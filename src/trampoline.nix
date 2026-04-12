# nix-effects trampoline: O(1) stack depth interpreter
#
# Uses builtins.genericClosure as a worklist-style trampoline.
# This is the key innovation: defunctionalize the recursive handler
# into an iterative loop via Nix's only built-in iterative primitive.
#
# Theory: Reynolds (1972) defunctionalization; Van Horn & Might (2010) store-allocated
# continuations + worklist iteration = bounded stack.
# Gibbons (2021) "CPS, Defunctionalization, Accumulations, and Associativity" —
# the hidden precondition is associativity of the operation being accumulated.
#
# After handling an effect, the continuation queue is processed inline via
# recursive applyQueue, keeping 1 genericClosure step per effect. For deep
# pure chains (>500 continuations), applyQueue falls back to a
# genericClosure-based qAppSlow for stack safety.
#
# Critical implementation detail: genericClosure only forces the `key` field
# (for deduplication). Handler state and continuation values would accumulate
# as thunk chains of depth N, blowing the stack when the final result is
# accessed. We break this chain by making `key` depend on `builtins.deepSeq`
# of the new state — since genericClosure forces `key`, this eagerly evaluates
# the state at each step. Validated: 1,000,000 operations in ~3 seconds.
{ lib, fx, api, ... }:

let
  queue = fx.queue;
  inherit (fx.comp) pure impure isPure;
  inherit (api) mk;

  # -- Queue application --
  #
  # Applies continuations left-to-right until hitting Impure or exhausting
  # the queue. Recursive with a depth limit of 500: beyond that, falls back
  # to genericClosure-based qAppSlow for stack safety. Processing the queue
  # inside the trampoline operator keeps 1 genericClosure step per effect.

  applyQueue = q: val: depth:
    let
      vl = queue.viewl q;
      result = vl.head val;
    in
      if vl.tail == null then result
      else if !(isPure result) then
        impure result.effect (queue.append result.queue vl.tail)
      else if depth >= 500 then
        # Deep pure chain: switch to genericClosure for stack safety.
        qAppSlow vl.tail result.value
      else
        applyQueue vl.tail (builtins.seq result.value result.value) (depth + 1);

  # genericClosure-based queue application for deep pure chains (>500
  # continuations). Iterates via genericClosure for stack safety.
  qAppSlow = q: val:
    let
      steps = builtins.genericClosure {
        startSet = [{ key = 0; _queue = q; _val = val; }];
        operator = state:
          let
            vl = queue.viewl state._queue;
            result = vl.head state._val;
          in
            if vl.tail != null && isPure result
            then [{ key = builtins.seq result.value (state.key + 1);
                    _queue = vl.tail; _val = result.value; }]
            else [];
      };
      last = lib.last steps;
      vl = queue.viewl last._queue;
      result = vl.head last._val;
    in
      if vl.tail == null then result
      else impure result.effect (queue.append result.queue vl.tail);

  # -- Interpreter --

  interpret = { comp, handlers, initialState }:
    let
      steps = builtins.genericClosure {
        startSet = [{
          key = 0;
          _comp = comp;
          _state = initialState;
        }];
        operator = step:
          if isPure step._comp then []
          else
            let
              eff = step._comp.effect;
              handler = handlers.${eff.name} or
                (throw "nix-effects: unhandled effect '${eff.name}'");
              result = handler {
                param = eff.param;
                state = step._state;
              };
              newState = if result ? state then result.state
                else throw "nix-effects: handler for '${eff.name}' must include 'state' in return value";
              # deepSeq newState in key: genericClosure forces key for dedup,
              # which forces newState, breaking the thunk chain.
              k = builtins.deepSeq newState (step.key + 1);
            in
              if result ? abort then
                [{ key = k; _comp = pure result.abort; _state = newState; }]
              else if result ? resume then
                let
                  q = step._comp.queue;
                  nextComp =
                    if q._variant == "Identity" then pure result.resume
                    else applyQueue q result.resume 0;
                in [{ key = k; _comp = nextComp; _state = newState; }]
              else
                throw "nix-effects: handler for '${eff.name}' must return { resume; state; } or { abort; state; }";
      };
      final = lib.last steps;
    in { value = final._comp.value; state = final._state; };

  run = mk {
    doc = ''
      Run a computation through the genericClosure trampoline.

      ```
      run : Computation a -> Handlers -> State -> { value : a, state : State }
      ```

      **Arguments:**
      - `comp` — the freer monad computation to interpret
      - `handlers` — `{ effectName = { param, state }: { resume | abort, state }; ... }`
      - `initialState` — starting state passed to handlers

      Handlers must return one of:

      ```
      { resume = value; state = newState; }  -- invoke continuation with value
      { abort  = value; state = newState; }  -- discard continuation, halt
      ```

      This is the defunctionalized encoding of Plotkin & Pretnar (2009):
      `resume` ≡ invoke continuation k(v), `abort` ≡ discard k.

      Stack depth: O(1) — constant regardless of computation length.
      Time: O(n) where n = number of effects in the computation.
    '';
    value = comp: handlers: initialState:
      assert (builtins.isAttrs comp && comp ? _tag)
        || throw "nix-effects: run expects a computation (Pure or Impure), got ${builtins.typeOf comp}";
      interpret { inherit comp handlers initialState; };
  };

  # -- Handler combinator --

  handle = mk {
    doc = ''
      Trampolined handler combinator with return clause.

      ```
      handle : { return?, handlers, state? } -> Computation a -> { value, state }
      ```

      Follows Kiselyov & Ishii's `handle_relay` pattern but trampolined
      via genericClosure for O(1) stack depth.

      **Arguments** (attrset):
      - `return` — `value -> state -> { value, state }`. How to transform the final Pure value. Default: identity.
      - `handlers` — `{ effectName = { param, state }: { resume | abort, state }; }`. Each must return `{ resume; state; }` or `{ abort; state; }`.
      - `state` — initial handler state. Default: null.
    '';
    value = {
      return ? (value: state: { inherit value state; }),
      handlers,
      state ? null,
    }: comp:
      assert (builtins.isAttrs comp && comp ? _tag)
        || throw "nix-effects: handle expects a computation (Pure or Impure), got ${builtins.typeOf comp}";
      let r = interpret { inherit comp handlers; initialState = state; };
      in return r.value r.state;
    tests = {
      "handle-with-default-return" = {
        expr =
          let
            send' = name: param:
              fx.comp.impure { inherit name param; } (fx.queue.singleton pure);
            comp = send' "double" 21;
            result = handle {
              handlers.double = { param, state }: { resume = param * 2; inherit state; };
            } comp;
          in result.value;
        expected = 42;
      };
      "handle-with-custom-return" = {
        expr =
          let
            comp = pure 21;
            result = handle {
              return = v: s: { value = v * 2; state = s; };
              handlers = {};
            } comp;
          in result.value;
        expected = 42;
      };
      "handle-abort-discards-continuation" = {
        expr =
          let
            send' = name: param:
              fx.comp.impure { inherit name param; } (fx.queue.singleton pure);
            kernelBind = comp: f:
              if isPure comp then f comp.value
              else fx.comp.impure comp.effect (fx.queue.snoc comp.queue f);
            comp = kernelBind (send' "fail" "boom") (_: send' "get" null);
            result = handle {
              handlers = {
                fail = { param, state }: { abort = { error = param; }; inherit state; };
                get = { param, state }: { resume = state; inherit state; };
              };
            } comp;
          in result.value;
        expected = { error = "boom"; };
      };
    };
  };

in mk {
  doc = "Trampolined interpreter using builtins.genericClosure for O(1) stack depth.";
  value = {
    inherit run handle;
  };
}

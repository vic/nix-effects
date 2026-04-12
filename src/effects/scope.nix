# nix-effects scope: Computation-scoped handlers via effect rotation
#
# Provides lexically-scoped handler installation without polluting
# user-visible state. Built on fx.rotate (Kyo-style handler rotation).
#
# scope.run    — run body with scoped handlers, hide scope state
# scope.runWith — run body with scoped handlers, expose scope state
# scope.local  — sugar: single handler scope
# scope.const  — sugar: single constant-handler scope
{ fx, api, ... }:

let
  inherit (api) mk;
  inherit (fx.kernel) pure bind send;
  rotate = fx.trampoline.rotate;
  handle = fx.trampoline.handle;

  run = mk {
    doc = ''
      Run a computation with scoped handlers. Effects matching `handlers`
      are handled inside the scope. Unknown effects rotate outward.
      The scope's internal state is hidden — caller sees only the body's value.

      ```
      scope.run : { handlers, state? } -> Computation a -> Computation a
      ```
    '';
    value = {
      handlers,
      state ? null,
    }:
      rotate {
        inherit handlers state;
        return = value: _state: value;
      };
    tests = {
      "scoped-handler-returns-value" = {
        expr =
          let
            comp = send "x" null;
            scoped = run {
              handlers.x = { state, ... }: { resume = 42; inherit state; };
            } comp;
            result = handle { handlers = {}; } scoped;
          in result.value;
        expected = 42;
      };
      "scope-hides-internal-state" = {
        expr =
          let
            comp = bind (send "inc" 1) (_: send "inc" 1);
            scoped = run {
              handlers.inc = { param, state }: { resume = null; state = state + param; };
              state = 0;
            } comp;
            result = handle { handlers = {}; } scoped;
          in result.value;
        expected = null;
      };
    };
  };

  runWith = mk {
    doc = ''
      Like scope.run but exposes the scope's final state alongside the value.

      ```
      scope.runWith : { handlers, state? } -> Computation a -> Computation { value, state }
      ```
    '';
    value = {
      handlers,
      state ? null,
    }: body:
      rotate {
        inherit handlers state;
      } body;
    tests = {
      "runWith-exposes-state" = {
        expr =
          let
            comp = bind (send "inc" 1) (_: send "inc" 1);
            scoped = runWith {
              handlers.inc = { param, state }: { resume = null; state = state + param; };
              state = 0;
            } comp;
            result = handle { handlers = {}; } scoped;
          in result.value.state;
        expected = 2;
      };
    };
  };

  local = mk {
    doc = ''
      Install a single named handler for a sub-computation.
      Sugar for scope.run with single handler.

      ```
      scope.local : string -> handler -> Computation a -> Computation a
      ```
    '';
    value = name: handler: run { handlers.${name} = handler; };
    tests = {
      "local-provides-value" = {
        expr =
          let
            comp = send "user" null;
            scoped = local "user" ({ state, ... }: { inherit state; resume = "alice"; }) comp;
            result = handle { handlers = {}; } scoped;
          in result.value;
        expected = "alice";
      };
      "local-different-values-per-scope" = {
        expr =
          let
            comp = send "user" null;
            a = local "user" ({ state, ... }: { inherit state; resume = "alice"; }) comp;
            b = local "user" ({ state, ... }: { inherit state; resume = "bob"; }) comp;
            combined = bind a (va:
              bind b (vb:
                pure { alice = va; bob = vb; }));
            result = handle { handlers = {}; } combined;
          in result.value;
        expected = { alice = "alice"; bob = "bob"; };
      };
    };
  };

  const = mk {
    doc = ''
      Install a single constant-value handler for a sub-computation.
      Sugar for scope.run with a  handler that always resumes
      with the given value.

      ```
      scope.const : string -> value -> Computation a -> Computation a
      ```
    '';
    value = name: resume:
      local name ({ state, ... }: { inherit state resume; });
    tests = {
      "provides-value" = {
        expr =
          let
            comp = send "user" null;
            scoped = const "user" "alice" comp;
            result = handle { handlers = {}; } scoped;
          in result.value;
        expected = "alice";
      };
      "different-values-per-scope" = {
        expr =
          let
            comp = send "user" null;
            a = const "user" "alice" comp;
            b = const "user" "bob" comp;
            combined = bind a (va:
              bind b (vb:
                pure { alice = va; bob = vb; }));
            result = handle { handlers = {}; } combined;
          in result.value;
        expected = { alice = "alice"; bob = "bob"; };
      };
    };
  };

in mk {
  doc = "Computation-scoped handlers via effect rotation.";
  value = { inherit run runWith local const; };
}

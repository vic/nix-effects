# nix-effects kernel: Freer monad operations with FTCQueue
#
# Monadic operations for the freer monad (Kiselyov & Ishii 2015).
# The Computation ADT (Pure/Impure) lives in comp.nix; this module
# builds send, bind, map, seq, pipe, and kleisli on top of it.
#
# The FTCQueue gives O(1) bind (snoc onto queue) instead of O(n)
# continuation composition. Left-nested bind chains are now O(n) total
# instead of O(n²).
{ fx, api, lib, ... }:

let
  queue = fx.queue;
  inherit (fx.comp) pure impure isPure;
  inherit (api) mk;

  # -- Derived operations --

  send = mk {
    doc = "Send an effect request. Returns the handler's response via continuation.";
    value = name: param:
      impure { inherit name param; } queue.identity;
    tests = {
      "creates-impure-with-effect" = {
        expr = (send "get" null).effect.name;
        expected = "get";
      };
      "queue-is-identity" = {
        expr = (send "get" null).queue._variant;
        expected = "Identity";
      };
    };
  };

  bind = mk {
    doc = ''
      Monadic bind: sequence two computations.

      ```
      bind comp f = case comp of
        Pure a       -> f a
        Impure e q   -> Impure e (snoc q f)
      ```

      O(1) per bind via FTCQueue snoc (Kiselyov & Ishii 2015, Section 3.1).
    '';
    value = comp: f:
      if isPure comp then f comp.value
      else if comp.queue._variant == "Identity" then impure comp.effect (queue.singleton f)
      else impure comp.effect (queue.snoc comp.queue f);
    tests = {
      "pure-bind-applies-f" = {
        expr = (bind (pure 21) (x: pure (x * 2))).value;
        expected = 42;
      };
      "impure-bind-preserves-effect" = {
        expr = (bind (send "get" null) (x: pure x)).effect.name;
        expected = "get";
      };
      "impure-bind-has-singleton-queue" = {
        expr =
          let
            comp = bind (send "get" null) (x: pure (x + 1));
          in comp.queue._variant;
        expected = "Leaf";
      };
    };
  };

  mapComp = mk {
    doc = "Map a function over the result of a computation (Functor instance).";
    value = f: comp: bind comp (x: pure (f x));
    tests = {
      "maps-pure" = {
        expr = (mapComp (x: x * 2) (pure 21)).value;
        expected = 42;
      };
    };
  };

  # -- Sequencing helpers --

  seq = mk {
    doc = "Sequence a list of computations, threading state via bind. Returns the last result.";
    value = comps:
      builtins.foldl'
        (acc: comp: bind acc (_: comp))
        (pure null)
        comps;
    tests = {
      "sequences-empty" = {
        expr = isPure (seq []);
        expected = true;
      };
    };
  };

  pipe = mk {
    doc = "Chain a computation through a list of Kleisli arrows, threading results via bind.";
    value = init: arrows:
      builtins.foldl'
        (acc: f: bind acc f)
        init
        arrows;
    tests = {
      "pipe-empty-returns-init" = {
        expr = (pipe (pure 42) []).value;
        expected = 42;
      };
      "pipe-single-arrow" = {
        expr = (pipe (pure 21) [(x: pure (x * 2))]).value;
        expected = 42;
      };
      "pipe-chains-results" = {
        expr = (pipe (pure 1) [
          (x: pure (x + 10))
          (x: pure (x * 3))
          (x: pure (x + 1))
        ]).value;
        expected = 34;  # (1 + 10) * 3 + 1
      };
      "pipe-threads-through-effects" = {
        expr = (pipe (send "get" null) [(x: pure (x + 1))]).effect.name;
        expected = "get";
      };
    };
  };

  kleisli = mk {
    doc = "Kleisli composition: compose two Kleisli arrows (a -> M b) and (b -> M c) into (a -> M c).";
    value = f: g: x: bind (f x) g;
    tests = {
      "kleisli-composes-pure" = {
        expr = (kleisli (x: pure (x + 1)) (x: pure (x * 2)) 10).value;
        expected = 22;  # (10 + 1) * 2
      };
      "kleisli-identity-left" = {
        expr = (kleisli pure (x: pure (x * 3)) 7).value;
        expected = 21;
      };
      "kleisli-identity-right" = {
        expr = (kleisli (x: pure (x * 3)) pure 7).value;
        expected = 21;
      };
      "kleisli-associative" = {
        expr =
          let
            f = x: pure (x + 1);
            g = x: pure (x * 2);
            h = x: pure (x - 3);
          in {
            lhs = (kleisli (kleisli f g) h 5).value;
            rhs = (kleisli f (kleisli g h) 5).value;
          };
        expected = {
          lhs = 9;  # ((5 + 1) * 2) - 3
          rhs = 9;
        };
      };
    };
  };

  bindAttrs = mk {
    doc = ''
    Like a bind-chain but operates over named attrset of required-effects.

    ```nix
    bindAttrs { foo = 99; bar = pure 22; baz = asks (env: env.baz); }
    ```

    Values that are non-effects become send params: `send "foo" 99`.

    Result has same attr-keys with corresponding effect result.

    See also: `bindFx`, `bindFn` for which this is the foundation.
    '';
    value = attrs:
      builtins.foldl'
      (prev: curr: bind prev (acc: bind curr.value (result: pure (acc // { ${curr.name} = result; }))))
      (pure {})
      (lib.mapAttrsToList (name: value:
        if builtins.elem (value._tag or null) ["Pure" "Impure"]
        then { inherit name value; }
        else { inherit name; value = send name value; }
      ) attrs);
    tests = {
      pure-passes-thru = {
        expr = (bindAttrs { foo = pure 22; }).value;
        expected.foo = 22;
      };
      impure-passes-thru = {
        expr = (bindAttrs { foo = (bind (pure 22) (x: pure (x + 1))); }).value;
        expected.foo = 23;
      };
      non-effect-is-send = {
        expr = let
          eff = bindAttrs { foo = 22; bar = pure 99; };
          result = fx.trampoline.run eff {
            foo = { param, state }: {
              resume = param * 2;
              state = state;
            };
          } null;
        in result.value;
        expected = {
          foo = 44;
          bar = 99;
        };
      };
    };
  };

  bindFx = mk {
    doc = ''
    Turns a Nix effectful function into an effect chain via bindAttrs.

    ```nix
    bindFx { bar = pure 22; } ({ foo, bar }: pure (foo * bar))
    ```

    The function sees bar as the result of `pure 22` and `foo` as the
    result of `send "foo" false` -- false comes directly from using 
    `lib.functionArgs f`, the handler can know if "foo" is optional in f.

    This works by using `bindAttrs` on the intersection of function args
    and attrs.
    '';
    value = attrs: f:
      bind (bindAttrs ((lib.functionArgs f) // attrs)) f;
    tests = {
      arg-in-attrs = {
        expr = (bindFx { x = pure 22; } ({ x }: pure (x * 2))).value;
        expected = 44;
      };
      arg-not-in-attrs-is-send = {
        expr = let
         eff = bindFx { } ({ foo }: pure (foo * 2));
         result = fx.trampoline.run eff {
          foo = { param, state }: {
            resume = 11;
            state = state;
          };
         } null;
        in result.value;
        expected = 22;
      };
    };
  };

  bindFn = mk {
    doc = ''
    Like bindFx but works on normal Nix functions and turns
    its result into a pure-effect.

    ```nix
    bindFn { bar = pure 22; } ({ foo, bar }: foo * bar)
    ```

    '';
    value = attrs: f: 
      bindFx attrs {
        __functionArgs = lib.functionArgs f;
        __functor = _: args: pure (f args);
      };
    tests = {
      arg-in-attrs = {
        expr = (bindFn { x = pure 22; } ({ x }: x * 2)).value;
        expected = 44;
      };
      arg-not-in-attrs-is-send = {
        expr = let
         eff = bindFn { } ({ foo }: foo * 2);
         result = fx.trampoline.run eff {
          foo = { param, state }: {
            resume = 11;
            state = state;
          };
         } null;
        in result.value;
        expected = 22;
      };
    };
  };

in mk {
  doc = "Freer monad kernel: Return/OpCall ADT with FTCQueue bind, send, map, seq, pipe, kleisli.";
  value = {
    inherit pure impure send bind;
    map = mapComp;
    inherit seq pipe kleisli;
    # Expose queue for advanced use (handler composition, adapt)
    inherit queue;
    inherit bindAttrs bindFx bindFn;
  };
}

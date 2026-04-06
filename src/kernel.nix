# nix-effects kernel: Freer monad ADT with FTCQueue
#
# Implements the freer monad from Kiselyov & Ishii (2015):
#   Computation a = Pure a | Impure (Effect x) (FTCQueue x a)
#
# Pure: computation finished with a value
# Impure: computation suspended at an effect, with a queue of continuations
#
# The FTCQueue gives O(1) bind (snoc onto queue) instead of O(n)
# continuation composition. Left-nested bind chains are now O(n) total
# instead of O(n²).
{ fx, api, ... }:

let
  queue = fx.queue;
  inherit (api) mk;

  # -- Core ADT --

  pure = mk {
    doc = "Lift a value into a pure computation (Return constructor).";
    value = value: { _tag = "Pure"; inherit value; };
    tests = {
      "creates-pure" = {
        expr = (pure 42)._tag;
        expected = "Pure";
      };
      "stores-value" = {
        expr = (pure 42).value;
        expected = 42;
      };
    };
  };

  impure = mk {
    doc = "Create a suspended computation (OpCall constructor). Takes an effect and a continuation queue.";
    value = effect: q: {
      _tag = "Impure";
      inherit effect;
      queue = q;
    };
    tests = {
      "creates-impure" = {
        expr = (impure { name = "test"; param = null; } (queue.singleton (x: pure x)))._tag;
        expected = "Impure";
      };
    };
  };

  # -- Derived operations --

  send = mk {
    doc = "Send an effect request. Returns the handler's response via continuation.";
    value = name: param: {
      _tag = "Impure";
      effect = { inherit name param; };
      queue = queue.singleton (value: { _tag = "Pure"; inherit value; });
    };
    tests = {
      "creates-impure-with-effect" = {
        expr = (send "get" null).effect.name;
        expected = "get";
      };
      "queue-applied-returns-pure" = {
        expr = (queue.qApp (send "get" null).queue 42)._tag;
        expected = "Pure";
      };
      "queue-applied-passes-value" = {
        expr = (queue.qApp (send "get" null).queue 42).value;
        expected = 42;
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
      if comp._tag == "Pure"
      then f comp.value
      else {
        _tag = "Impure";
        inherit (comp) effect;
        queue = queue.snoc comp.queue f;
      };
    tests = {
      "pure-bind-applies-f" = {
        expr = (bind (pure 21) (x: pure (x * 2))).value;
        expected = 42;
      };
      "impure-bind-preserves-effect" = {
        expr = (bind (send "get" null) (x: pure x)).effect.name;
        expected = "get";
      };
      "impure-bind-chains-via-queue" = {
        expr =
          let
            comp = bind (send "get" null) (x: pure (x + 1));
          in (queue.qApp comp.queue 10).value;
        expected = 11;
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
        expr = (seq [])._tag;
        expected = "Pure";
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

in mk {
  doc = "Freer monad kernel: Return/OpCall ADT with FTCQueue bind, send, map, seq, pipe, kleisli.";
  value = {
    inherit pure impure send bind;
    map = mapComp;
    inherit seq pipe kleisli;
    # Expose queue for advanced use (handler composition, adapt)
    inherit queue;
  };
}

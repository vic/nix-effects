{ fx, lib, ... }:

let
  inherit (fx.binds) bindAttrs;
in {
  scope = rec {
    do = steps: lib.foldl' (acc: step: bind acc step) (pure null) steps;

    letM = attrs: k: bind (bindAttrs attrs) k;

    inherit (fx.kernel) pure bind map seq pipe kleisli;
    inherit (fx.trampoline) run handle;
  };

  tests = {};
}

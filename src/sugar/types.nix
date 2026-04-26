{ fx, ... }:

let
  inherit (fx.types.refinement) refined;
  inherit (fx.types.primitives) Int String Bool Float Path Null Unit Any;

  sugared = t: t // {
    __functor = self: pred: sugared (refined "${self.name}?" self pred);
    __toString = self: self.name;
  };
in {
  scope = {
    types = {
      wrap = sugared;
      Int    = sugared Int;
      String = sugared String;
      Bool   = sugared Bool;
      Float  = sugared Float;
      Path   = sugared Path;
      Null   = sugared Null;
      Unit   = sugared Unit;
      Any    = sugared Any;
    };
  };

  tests = {};
}

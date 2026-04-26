{ fx, ... }:

{
  scope = {
    operators = { __div = fx.kernel.bind; };
  };

  tests = {};
}

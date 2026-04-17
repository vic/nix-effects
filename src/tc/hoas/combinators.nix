# HOAS node constructors — kernel-primitive types, compound-type sugar,
# binding forms (pi/sigma/lam/let), intros, literals, annotation/app/projection,
# descriptions, and the eliminator wrappers that compile via desc-ind adapters.
#
# The macro-derived prelude types (`nat`, `listOf`, `sum`) and their
# constructors/introduction forms (`zero`, `succ`, `nil`, `cons`, `inl`, `inr`)
# live in `datatype.nix` because they reference `NatDT`/`ListDT`/`SumDT` from
# the macro layer. Cross-part references go through `self.<name>`.
{ self, ... }:

let
  # HOAS variable markers. A marker stands for a bound variable at a specific
  # binding depth (level); `elaborate` converts it to `T.mkVar` with the
  # correct de Bruijn index.
  _hoasTag = "__nix-effects-hoas-marker__";
in {
  scope = {
    mkMarker = level: { _hoas = _hoasTag; inherit level; };
    isMarker = x: builtins.isAttrs x && x ? _hoas && x._hoas == _hoasTag;

    # Kernel-primitive types. `bool`, `unit`, `void` remain primitive because
    # descriptions use `bool` as the constructor-tag domain (natDesc = descArg
    # bool …) and `unit` as the base payload type; rebinding them to μ-forms
    # would be self-referential through `spineDesc`, `dispatchStep`,
    # `interpHoas`, `allHoas`. Lifted via Fin n once the indexed grammar
    # lifts the circularity.
    bool = { _htag = "bool"; };
    unit = { _htag = "unit"; };
    void = { _htag = "void"; };
    string = { _htag = "string"; };
    int_ = { _htag = "int"; };
    float_ = { _htag = "float"; };
    attrs = { _htag = "attrs"; };
    path = { _htag = "path"; };
    function_ = { _htag = "function"; };
    any = { _htag = "any"; };

    eq = type: lhs: rhs: { _htag = "eq"; inherit type lhs rhs; };
    u = level: { _htag = "U"; inherit level; };

    # Compound types (sugar for nested sigma/sum — carry structural info
    # for elaborateValue).
    # fields : [ { name; type; } ... ] — sorted by name
    record = fields: { _htag = "record"; inherit fields; };
    # maybe = Sum(inner, Unit) — null for Right/Unit, value for Left/inner.
    maybe = inner: { _htag = "maybe"; inherit inner; };
    # branches : [ { tag; type; } ... ] — sorted by tag
    variant = branches: { _htag = "variant"; inherit branches; };

    # Binding forms — take Nix lambda for the body.
    forall = name: domain: bodyFn:
      { _htag = "pi"; inherit name domain; body = bodyFn; };
    sigma = name: fst: sndFn:
      { _htag = "sigma"; inherit name fst; body = sndFn; };
    lam = name: domain: bodyFn:
      { _htag = "lam"; inherit name domain; body = bodyFn; };
    let_ = name: type: val: bodyFn:
      { _htag = "let"; inherit name type val; body = bodyFn; };

    # Intro forms and term combinators.
    true_ = { _htag = "true"; };
    false_ = { _htag = "false"; };
    tt = { _htag = "tt"; };
    pair = fst: snd: { _htag = "pair"; inherit fst snd; };
    refl = { _htag = "refl"; };

    stringLit = s: { _htag = "string-lit"; value = s; };
    intLit = n: { _htag = "int-lit"; value = n; };
    floatLit = f: { _htag = "float-lit"; value = f; };
    attrsLit = { _htag = "attrs-lit"; };
    pathLit = { _htag = "path-lit"; };
    fnLit = { _htag = "fn-lit"; };
    anyLit = { _htag = "any-lit"; };

    strEq = lhs: rhs: { _htag = "str-eq"; inherit lhs rhs; };
    opaqueLam = nixFn: piHoas:
      { _htag = "opaque-lam"; _fnBox = { _fn = nixFn; }; inherit nixFn piHoas; };
    absurd = type: term: { _htag = "absurd"; inherit type term; };
    ann = term: type: { _htag = "ann"; inherit term type; };
    app = fn: arg: { _htag = "app"; inherit fn arg; };
    fst_ = pair: { _htag = "fst"; inherit pair; };
    snd_ = pair: { _htag = "snd"; inherit pair; };

    # Eliminators. `ind`/`listElim`/`sumElim` wrap motive/base/step in
    # `let_`-bindings at their required types before the application spine,
    # making motive/step/base inferable (VAR via lookupType) and emitting a
    # `let_ P … let_ B … let_ S … <elim>` Tm shape. `boolElim` stays primitive —
    # kernel `bool-elim` is used internally by descriptions and adapters.
    ind = motive: base: step: scrut:
      let
        inherit (self) forall app let_ nat zero succ u NatDT;
        piMotiveTy = forall "_" nat (_: u 0);
      in
      let_ "P" piMotiveTy motive (P:
      let_ "B" (app P zero) base (B:
      let_ "S" (forall "k" nat (k:
                forall "_" (app P k) (_: app P (succ k)))) step (S:
        app (app (app (app NatDT.elim P) B) S) scrut)));

    boolElim = motive: onTrue: onFalse: scrut:
      { _htag = "bool-elim"; inherit motive onTrue onFalse scrut; };

    listElim = A: motive: onNil: onCons: scrut:
      let
        inherit (self) forall app let_ listOf nil cons u ListDT;
        piMotiveTy = forall "_" (listOf A) (_: u 0);
      in
      let_ "P" piMotiveTy motive (P:
      let_ "N" (app P (nil A)) onNil (N:
      let_ "C" (forall "h" A (hVar:
                forall "t" (listOf A) (tVar:
                forall "_" (app P tVar) (_:
                  app P (cons A hVar tVar))))) onCons (C:
        app (app (app (app (app ListDT.elim A) P) N) C) scrut)));

    sumElim = A: B: motive: onLeft: onRight: scrut:
      let
        inherit (self) forall app let_ sum inl inr u SumDT;
        piMotiveTy = forall "_" (sum A B) (_: u 0);
      in
      let_ "P" piMotiveTy motive (P:
      let_ "L" (forall "a" A (aVar: app P (inl A B aVar))) onLeft (L:
      let_ "R" (forall "b" B (bVar: app P (inr A B bVar))) onRight (R:
        app (app (app (app (app (app SumDT.elim A) B) P) L) R) scrut)));

    j = type: lhs: motive: base: rhs: eq_:
      { _htag = "j"; inherit type lhs motive base rhs; eq = eq_; };

    # Descriptions: types, constructors, and eliminators.
    desc = { _htag = "desc"; };
    mu = D: { _htag = "mu"; inherit D; };

    descRet = { _htag = "desc-ret"; };
    # descArg S (b: T b) — T is a Nix function, b binds a fresh variable.
    descArg = S: T: { _htag = "desc-arg"; inherit S; body = T; };
    descRec = D: { _htag = "desc-rec"; inherit D; };
    descPi = S: D: { _htag = "desc-pi"; inherit S D; };

    descCon = D: d: { _htag = "desc-con"; inherit D d; };
    descInd = D: motive: step: scrut:
      { _htag = "desc-ind"; inherit D motive step scrut; };
    descElim = motive: onRet: onArg: onRec: onPi: scrut:
      { _htag = "desc-elim"; inherit motive onRet onArg onRec onPi scrut; };
  };
  tests = {};
}

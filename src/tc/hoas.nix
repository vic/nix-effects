# Type-checking kernel: HOAS surface combinators
#
# Higher-Order Abstract Syntax layer using Nix lambdas for variable binding.
# Combinators produce an intermediate HOAS tree; `elaborate` compiles it
# to de Bruijn indexed Tm terms that the kernel can check/infer.
#
# HOAS markers: { _hoas = true; level = N; } — produced by binding
# combinators, compiled away by elaborate. No Nix lambdas leak into
# the kernel value domain.
#
# Spec reference: kernel-spec.md §2
{ fx, api, ... }:

let
  inherit (api) mk;
  T = fx.tc.term;
  E = fx.tc.eval;
  Q = fx.tc.quote;
  CH = fx.tc.check;

  # -- HOAS variable markers --
  # A marker is a lightweight attrset that stands for a bound variable
  # at a specific binding depth (level). elaborate converts these to
  # T.mkVar with the correct de Bruijn index.
  _hoasTag = "__nix-effects-hoas-marker__";
  mkMarker = level: { _hoas = _hoasTag; inherit level; };
  isMarker = x: builtins.isAttrs x && x ? _hoas && x._hoas == _hoasTag;

  # -- HOAS AST node constructors --
  # These build an intermediate tree that elaborate walks.

  # Types
  #
  # `nat`, `listOf`, `sum` forward to the macro-derived datatypes. `nat`
  # is `NatDT.T` directly — monomorphic `T` is a `"mu"` HOAS node
  # carrying `_dtypeMeta`. `listOf`/`sum` are spines of `app` over the
  # polymorphic `T`, keeping the parameter HOAS as a literal structural
  # slot. The un-reduced app form carries two pieces of information the
  # β-reduced `mu (listDesc A)` destroys: `_dtypeMeta` from the polyField
  # head (constructor + field names, shape classifier) and the parameter
  # HOAS with any surface sugar intact (`H.record`, `H.variant`,
  # `H.maybe`). elaborateValue/validateValue/extractInner all dispatch
  # on the app-spine directly and never round-trip through a kernel
  # value to recover the parameter.
  #
  # `bool`, `unit`, `void` stay as kernel primitives: descriptions use
  # `bool` as the constructor-tag domain (`natDesc = descArg bool …`) and
  # `unit` as the base payload type — both referenced from `spineDesc`,
  # `dispatchStep`, `interpHoas`, `allHoas`, and every eliminator adapter.
  # Rebinding them to μ-forms would be self-referential through
  # `spineDesc`. They are rebound via `Fin n` once the indexed grammar
  # lifts the circularity.
  nat = NatDT.T;
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
  listOf = A: app ListDT.T A;
  sum    = A: B: app (app SumDT.T A) B;
  eq = type: lhs: rhs: { _htag = "eq"; inherit type lhs rhs; };
  u = level: { _htag = "U"; inherit level; };

  # Compound types (sugar for nested sigma/sum — carry structural info for elaborateValue)
  # fields: [ { name; type; } ... ] — sorted by name
  record = fields: { _htag = "record"; inherit fields; };
  # maybe = Sum(inner, Unit) — null for Right/Unit, value for Left/inner
  maybe = inner: { _htag = "maybe"; inherit inner; };
  # branches: [ { tag; type; } ... ] — sorted by tag
  variant = branches: { _htag = "variant"; inherit branches; };

  # Binding types — take Nix lambda for the body
  forall = name: domain: bodyFn:
    { _htag = "pi"; inherit name domain; body = bodyFn; };

  sigma = name: fst: sndFn:
    { _htag = "sigma"; inherit name fst; body = sndFn; };

  # Terms
  lam = name: domain: bodyFn:
    { _htag = "lam"; inherit name domain; body = bodyFn; };

  let_ = name: type: val: bodyFn:
    { _htag = "let"; inherit name type val; body = bodyFn; };

  # Intro forms. `zero`/`succ`/`nil`/`cons`/`inl`/`inr` are delegated to the
  # macro-generated constructors so the Nix-level surface (`succ h`,
  # `cons A h t`, …) stays unchanged while the elaborated Tm flows through
  # the `dt-ctor-mono`/`dt-ctor-poly` chain-flatten path. `true_`/`false_`/
  # `tt` stay as kernel-primitive intros: they pair with kernel `bool`/`unit`,
  # which remain primitive (see the note above `nat`).
  zero = NatDT.zero;
  succ = h: app NatDT.succ h;
  true_ = { _htag = "true"; };
  false_ = { _htag = "false"; };
  tt = { _htag = "tt"; };
  nil = A: app ListDT.nil A;
  cons = A: h: t: app (app (app ListDT.cons A) h) t;
  pair = fst: snd: { _htag = "pair"; inherit fst snd; };
  inl = A: B: v: app (app (app SumDT.inl A) B) v;
  inr = A: B: v: app (app (app SumDT.inr A) B) v;
  refl = { _htag = "refl"; };
  stringLit = s: { _htag = "string-lit"; value = s; };
  intLit = n: { _htag = "int-lit"; value = n; };
  floatLit = f: { _htag = "float-lit"; value = f; };
  attrsLit = { _htag = "attrs-lit"; };
  pathLit = { _htag = "path-lit"; };
  fnLit = { _htag = "fn-lit"; };
  anyLit = { _htag = "any-lit"; };
  strEq = lhs: rhs: { _htag = "str-eq"; inherit lhs rhs; };
  opaqueLam = nixFn: piHoas: { _htag = "opaque-lam"; _fnBox = { _fn = nixFn; }; inherit nixFn piHoas; };
  absurd = type: term: { _htag = "absurd"; inherit type term; };
  ann = term: type: { _htag = "ann"; inherit term type; };
  app = fn: arg: { _htag = "app"; inherit fn arg; };
  fst_ = pair: { _htag = "fst"; inherit pair; };
  snd_ = pair: { _htag = "snd"; inherit pair; };

  # Eliminators. `ind`/`listElim`/`sumElim` delegate to the macro-generated
  # eliminators but wrap motive/base/step in `let_`-bindings at their
  # required types before the application spine. The let-wrapping makes
  # motive/step/base inferable (VAR via lookupType) and emits a
  # `let_ P ... let_ B ... let_ S ... <elim>` Tm shape. `boolElim` stays
  # primitive — kernel `bool-elim` is used internally by descriptions and
  # adapters, and a μ-form rebind would require migrating those sites.
  ind = motive: base: step: scrut:
    let piMotiveTy = forall "_" nat (_: u 0); in
    let_ "P" piMotiveTy motive (P:
    let_ "B" (app P zero) base (B:
    let_ "S" (forall "k" nat (k:
              forall "_" (app P k) (_: app P (succ k)))) step (S:
      app (app (app (app NatDT.elim P) B) S) scrut)));
  boolElim = motive: onTrue: onFalse: scrut:
    { _htag = "bool-elim"; inherit motive onTrue onFalse scrut; };
  listElim = A: motive: onNil: onCons: scrut:
    let piMotiveTy = forall "_" (listOf A) (_: u 0); in
    let_ "P" piMotiveTy motive (P:
    let_ "N" (app P (nil A)) onNil (N:
    let_ "C" (forall "h" A (hVar:
              forall "t" (listOf A) (tVar:
              forall "_" (app P tVar) (_:
                app P (cons A hVar tVar))))) onCons (C:
      app (app (app (app (app ListDT.elim A) P) N) C) scrut)));
  sumElim = A: B: motive: onLeft: onRight: scrut:
    let piMotiveTy = forall "_" (sum A B) (_: u 0); in
    let_ "P" piMotiveTy motive (P:
    let_ "L" (forall "a" A (aVar: app P (inl A B aVar))) onLeft (L:
    let_ "R" (forall "b" B (bVar: app P (inr A B bVar))) onRight (R:
      app (app (app (app (app (app SumDT.elim A) B) P) L) R) scrut)));
  j = type: lhs: motive: base: rhs: eq_:
    { _htag = "j"; inherit type lhs motive base rhs; eq = eq_; };

  # -- Descriptions (non-indexed) --
  # Types
  desc = { _htag = "desc"; };
  mu = D: { _htag = "mu"; inherit D; };

  # Desc constructors
  descRet = { _htag = "desc-ret"; };
  # descArg S (b: T b) — T is a Nix function, b binds a fresh variable
  descArg = S: T: { _htag = "desc-arg"; inherit S; body = T; };
  descRec = D: { _htag = "desc-rec"; inherit D; };
  descPi = S: D: { _htag = "desc-pi"; inherit S D; };

  # Fixpoint constructors and eliminators
  descCon = D: d: { _htag = "desc-con"; inherit D d; };
  descInd = D: motive: step: scrut:
    { _htag = "desc-ind"; inherit D motive step scrut; };
  descElim = motive: onRet: onArg: onRec: onPi: scrut:
    { _htag = "desc-elim"; inherit motive onRet onArg onRec onPi scrut; };

  # -- Macro-constructor chain flattening --
  #
  # The datatype macro emits fielded constructor terms as curried λ-cascades
  # wrapped in `ann`. A deeply-applied chain (e.g. a 5000-element cons list)
  # would elaborate to a 5000-deep `app`-tree Tm, which blows the C++ stack
  # on `infer`'s linear recursion (check.nix:338 → check.nix:311 per layer).
  # `tryFlattenCtorChain` peels spines whose head is tagged `dt-ctor-mono`
  # or `dt-ctor-poly` and emits a flat `desc-con` Tm — a single layer for
  # non-recursive ctors (sum's `inl`/`inr`), a `genericClosure`-walked
  # pyramid for the list/nat-style `recursive` shape.
  #
  # Chain-flatten precondition: one of two shapes per `ctorShape`:
  #   - "saturated": every field is `data`. Emits one flat `desc-con`.
  #   - "recursive": exactly one `rec` at the tail, every other field
  #     `data`. Aligns with the kernel's desc-con trampoline acceptance
  #     condition via `linearProfile` (eval.nix:376-403). Walks the chain
  #     along the rec tail.
  # Zero-field constructors (e.g. `nil`) never produce a `dt-ctor-mono`
  # node — `mkCtor` returns a plain `desc-con` HOAS with the tag-encoded
  # payload baked in. The poly-branch of `tryFlattenCtorChain` elaborates
  # that mono directly. Ctors outside either shape (tree's `node` with two
  # recs, dataD/piD-dependent fields) decline and the fallback
  # `ann (lam-cascade)` path handles the application normally.

  # List helpers — inline `take`/`drop` so this module does not need to
  # pull in nixpkgs `lib`.
  _listTake = n: xs:
    builtins.genList (i: builtins.elemAt xs i)
      (if n > builtins.length xs then builtins.length xs else n);
  _listDrop = n: xs:
    let len = builtins.length xs; in
    if n >= len then []
    else builtins.genList (i: builtins.elemAt xs (n + i)) (len - n);

  # Peel an app-spine: walk outward while the node is an HOAS `app`, returning
  # `{ head; args = [arg_inner, ..., arg_outer]; }`. Bounded by the ctor's
  # nParams + nFields per call site (3 for ListDT.cons) — no long recursion.
  peelAppSpine = node: args:
    if builtins.isAttrs node && node ? _htag && node._htag == "app"
    then peelAppSpine node.fn ([ node.arg ] ++ args)
    else { head = node; inherit args; };

  # Tm-level tag encoding: wrap `payloadTm` with the ctor's bool-tag prefix
  # committing at index i out of n constructors. Structurally mirrors the
  # HOAS `encodeTag` but operates on elaborated terms.
  encodeTagTm = i: n: payloadTm:
    if n == 1 then payloadTm
    else if i == 0 then T.mkPair T.mkTrue payloadTm
    else T.mkPair T.mkFalse (encodeTagTm (i - 1) (n - 1) payloadTm);

  # Classify a field list into a chain-flatten profile, or null if neither
  # shape applies.
  #   - "saturated": all fields are plain data (no rec). Emits a single
  #     flat `desc-con` whose payload is the right-nested pair of the data
  #     field Tms terminated with `tt`. No chain-walking.
  #   - "recursive": exactly one rec at the tail, every other field data.
  #     Walks a chain along the rec arg via `genericClosure` and emits a
  #     layered `desc-con` pyramid with a shared dTm across layers.
  # A trailing-rec ctor with zero data fields (e.g. `succ`, whose single
  # field is `rec`) is classified as "recursive" with `nData = 0`. A ctor
  # with zero fields is handled separately at the `tryFlattenCtorChain`
  # poly-branch via the `mono._htag == "desc-con"` short-circuit; both
  # profiles require `n >= 1` here.
  ctorShape = fields:
    let
      n = builtins.length fields;
      initsAllData = nInits:
        builtins.foldl'
          (ok: j: ok && (builtins.elemAt fields j).kind == "data")
          true
          (builtins.genList (x: x) nInits);
      allData = n >= 1 && initsAllData n;
      lastRec =
        n >= 1
        && (builtins.elemAt fields (n - 1)).kind == "rec"
        && initsAllData (n - 1);
    in
      if lastRec then { kind = "recursive"; }
      else if allData then { kind = "saturated"; }
      else null;

  # Attempt to recognise `h` (an `app` HOAS node) as the top of a saturated
  # macro-constructor application and emit a flat `desc-con` chain. Returns
  # a Tm on success, or null when the spine doesn't match a chain-flattenable
  # ctor (caller falls through to regular `app` elaboration).
  tryFlattenCtorChain = depth: h:
    let
      outer = peelAppSpine h [];
      head = outer.head;
      args = outer.args;
    in
      if !(builtins.isAttrs head && head ? _htag) then null
      else if head._htag == "dt-ctor-mono" then
        flattenCtor depth head null [] args
      else if head._htag == "dt-ctor-poly" then
        let nP = head.nParams; in
        if builtins.length args < nP then null
        else
          let
            paramArgs = _listTake nP args;
            fieldArgs = _listDrop nP args;
            mono = head.monoAt paramArgs;
          in
            if !(builtins.isAttrs mono) || !(mono ? _htag) then null
            # Fielded ctors: mono is a `dt-ctor-mono` node; pass to the
            # shape-classified flattener.
            else if mono._htag == "dt-ctor-mono"
            then flattenCtor depth mono head paramArgs fieldArgs
            # Zero-field ctors: `mkCtor` returns a plain `desc-con` HOAS
            # (no lam cascade, no tag). Elaborating it directly yields a
            # flat `desc-con` Tm with the parameter-instantiated D baked in.
            else if mono._htag == "desc-con"
                 && builtins.length fieldArgs == 0
            then elaborate depth mono
            else null
      else null;

  # Chain-flatten dispatcher. `polyHead` is non-null for poly chains (used
  # in the recursive branch to verify each successor layer uses the *same*
  # poly ctor with the *same* param args; structural `==` on HOAS param
  # args suffices because the test site passes the same references at
  # every layer).
  flattenCtor = depth: mono: polyHead: paramArgs: fieldArgs:
    let
      nFields = mono.nFields;
      shape = ctorShape mono.fields;
    in
    if builtins.length fieldArgs != nFields || shape == null then null
    else let
      dTm = elaborate depth mono.dHoas;
      ctorIdx = mono.ctorIndex;
      nCtors = mono.nCtors;
    in
    if shape.kind == "saturated" then
      # No recursion: build one payload from the data field Tms.
      #   descCon dTm (encodeTag i n (pair d_0 (pair d_1 (… (pair d_{n-1} tt) …))))
      let
        dataTms = map (a: elaborate depth a) fieldArgs;
        payload = builtins.foldl'
          (acc: j:
            let d = builtins.elemAt dataTms (nFields - 1 - j);
            in T.mkPair d acc)
          T.mkTt
          (builtins.genList (x: x) nFields);
      in T.mkDescCon dTm (encodeTagTm ctorIdx nCtors payload)
    else
      let
        recArg = builtins.elemAt fieldArgs (nFields - 1);
        nonRecArgs = _listTake (nFields - 1) fieldArgs;
        # Try to recognise a successor layer: peel an app spine and require
        # the head to be the same `mono` (mono chains) or the same
        # `polyHead` with matching paramArgs (poly chains).
        tryNext = node:
          let sp = peelAppSpine node []; in
          if !(builtins.isAttrs sp.head && sp.head ? _htag) then null
          else if polyHead == null then
            if sp.head != mono then null
            else if builtins.length sp.args != nFields then null
            else {
              nonRec = _listTake (nFields - 1) sp.args;
              recArg = builtins.elemAt sp.args (nFields - 1);
            }
          else
            if sp.head != polyHead then null
            else if builtins.length sp.args != polyHead.nParams + nFields then null
            else
              let pa = _listTake polyHead.nParams sp.args;
                  fa = _listDrop polyHead.nParams sp.args; in
              if pa != paramArgs then null
              else {
                nonRec = _listTake (nFields - 1) fa;
                recArg = builtins.elemAt fa (nFields - 1);
              };
        # Start the chain at the given layer. `genericClosure` walks along
        # `recArg` as long as each tail peels to a matching successor.
        startLayer = { inherit nonRecArgs recArg; };
        chain = builtins.genericClosure {
          startSet = [{ key = 0; val = startLayer; }];
          operator = item:
            let nxt = tryNext item.val.recArg; in
            if nxt == null then []
            else [{ key = item.key + 1;
                    val = { nonRecArgs = nxt.nonRec; recArg = nxt.recArg; }; }];
        };
        nLayers = builtins.length chain;
        innermost = (builtins.elemAt chain (nLayers - 1)).val;
        # Base: whatever the innermost layer's `recArg` points to (the
        # first non-chain-successor tail). Elaborated normally — may be
        # a zero-field ctor application, a neutral, or anything else.
        baseTm = elaborate depth innermost.recArg;
        # Build one layer's payload given elaborated non-rec field args and
        # a tail accumulator. Field args are prepended in declaration order,
        # the accumulator sits at the rec position, terminated with `tt`:
        #   encodeTag i n (pair f_0 (pair f_1 (… (pair acc tt) …))).
        buildLayer = nonRecTms: accTm:
          let
            innerMost = T.mkPair accTm T.mkTt;
            payloadInner = builtins.foldl'
              (acc: j:
                let f = builtins.elemAt nonRecTms (builtins.length nonRecTms - 1 - j);
                in T.mkPair f acc)
              innerMost
              (builtins.genList (x: x) (builtins.length nonRecTms));
          in T.mkDescCon dTm (encodeTagTm ctorIdx nCtors payloadInner);
      in
      # Fold inward-to-outward: step idx=0 wraps baseTm with the innermost
      # layer's non-rec args, step idx=1 with the next layer out, etc.
      builtins.foldl' (acc: idx:
        let
          layer = (builtins.elemAt chain (nLayers - 1 - idx)).val;
          nonRecTms = map (a: elaborate depth a) layer.nonRecArgs;
        in buildLayer nonRecTms acc
      ) baseTm (builtins.genList (x: x) nLayers);

  # -- Elaboration: HOAS tree → de Bruijn Tm --
  #
  # elaborate : Int → HoasTree → Tm
  # depth tracks the current binding depth. When we encounter a binding
  # combinator (pi, lam, sigma, let), we:
  #   1. Apply the stored Nix lambda to mkMarker(depth)
  #   2. Recursively elaborate the resulting body at depth+1
  #   3. Markers with level L become T.mkVar(depth - L - 1)
  elaborate = depth: h:
    # Marker → variable
    if isMarker h then
      T.mkVar (depth - h.level - 1)

    else if !(builtins.isAttrs h) || !(h ? _htag) then
      let
        desc =
          if builtins.isAttrs h
          then "attrset with keys: ${builtins.concatStringsSep ", " (builtins.attrNames h)}"
          else builtins.typeOf h;
      in throw "hoas.elaborate: not an HOAS node (${desc})"

    else let t = h._htag; in

    # -- Types --
    # `nat` is the description-based fixpoint `mu natDesc`. natDescTm is
    # pre-elaborated at module scope to avoid re-elaborating on every use.
    if t == "nat" then T.mkMu natDescTm
    else if t == "bool" then T.mkBool
    else if t == "unit" then T.mkUnit
    else if t == "void" then T.mkVoid
    else if t == "string" then T.mkString
    else if t == "int" then T.mkInt
    else if t == "float" then T.mkFloat
    else if t == "attrs" then T.mkAttrs
    else if t == "path" then T.mkPath
    else if t == "function" then T.mkFunction
    else if t == "any" then T.mkAny
    else if t == "U" then T.mkU h.level
    # `listOf elem` is the description-based fixpoint `mu (listDesc elem)`.
    else if t == "list" then T.mkMu (elaborate depth (listDesc h.elem))
    # `sum l r` is the description-based fixpoint `mu (sumDesc l r)`.
    else if t == "sum" then T.mkMu (elaborate depth (sumDesc h.left h.right))
    else if t == "eq" then
      T.mkEq (elaborate depth h.type) (elaborate depth h.lhs) (elaborate depth h.rhs)

    # -- Compound types (sugar for nested sigma/sum) --
    else if t == "record" then
      let
        fields = h.fields;
        n = builtins.length fields;
      in if n == 0 then T.mkUnit
         else if n == 1 then elaborate depth (builtins.head fields).type
         else
           # Build nested Sigma right-to-left: Σ(f1:T1).Σ(f2:T2)...Tn
           let lastType = elaborate depth (builtins.elemAt fields (n - 1)).type;
           in builtins.foldl' (acc: i:
             let field = builtins.elemAt fields (n - 2 - i); in
             T.mkSigma field.name (elaborate depth field.type) acc
           ) lastType (builtins.genList (x: x) (n - 1))

    else if t == "maybe" then
      # Sum(inner, Unit) — Left = value present, Right = null.
      # Delegates to the `sum` branch so the description-based representation
      # (μ(sumDesc l r)) is used uniformly with `inl`/`inr` values.
      elaborate depth (sum h.inner unit)

    else if t == "variant" then
      let
        branches = h.branches;
        n = builtins.length branches;
      in if n == 0 then T.mkVoid
         else if n == 1 then elaborate depth (builtins.head branches).type
         else
           # Build nested Sum right-to-left: Sum(T1, Sum(T2, ...Tn)).
           # Delegates to the `sum` branch so the nesting is in the description
           # representation, matching the inl/inr injection shape.
           let lastType = (builtins.elemAt branches (n - 1)).type;
           in elaborate depth (builtins.foldl' (acc: i:
             let branch = builtins.elemAt branches (n - 2 - i); in
             sum branch.type acc
           ) lastType (builtins.genList (x: x) (n - 1)))

    # -- Binding types and terms (trampolined for deep nesting) --
    else if t == "pi" || t == "sigma" || t == "lam" || t == "let" then
      let
        # Peel nested binding forms iteratively via genericClosure
        chain = builtins.genericClosure {
          startSet = [{ key = depth; val = h; }];
          operator = item:
            let node = item.val; in
            if builtins.isAttrs node && node ? _htag &&
               (let nt = node._htag; in nt == "pi" || nt == "sigma" || nt == "lam" || nt == "let")
            then
              let marker = mkMarker item.key; in
              [{ key = item.key + 1; val = node.body marker; }]
            else [];
        };
        n = builtins.length chain - 1;
        base = (builtins.elemAt chain n).val;
        baseElab = elaborate (depth + n) base;
      in
      builtins.foldl' (acc: i:
        let
          item = builtins.elemAt chain (n - 1 - i);
          node = item.val;
          d = item.key;
          nt = node._htag;
        in
        if nt == "pi" then T.mkPi node.name (elaborate d node.domain) acc
        else if nt == "sigma" then T.mkSigma node.name (elaborate d node.fst) acc
        else if nt == "lam" then T.mkLam node.name (elaborate d node.domain) acc
        else T.mkLet node.name (elaborate d node.type) (elaborate d node.val) acc
      ) baseElab (builtins.genList (x: x) n)

    # -- Non-binding terms --
    # `zero` = `descCon natDesc (pair true_ tt)` — tag true selects the
    # zero-constructor branch of natDesc, whose payload type is ⊤.
    else if t == "zero" then
      T.mkDescCon natDescTm (T.mkPair T.mkTrue T.mkTt)
    # `succ n` = `descCon natDesc (pair false_ (pair n tt))` — tag false
    # selects the succ-constructor branch, payload is the recursive arg
    # paired with ⊤. Trampolined for deep naturals (5000+).
    else if t == "succ" then
      let
        chain = builtins.genericClosure {
          startSet = [{ key = 0; val = h; }];
          operator = item:
            if builtins.isAttrs item.val && item.val ? _htag && item.val._htag == "succ"
            then [{ key = item.key + 1; val = item.val.pred; }]
            else [];
        };
        n = builtins.length chain - 1;
        base = (builtins.elemAt chain n).val;
      in builtins.foldl' (acc: _:
        T.mkDescCon natDescTm (T.mkPair T.mkFalse (T.mkPair acc T.mkTt))
      ) (elaborate depth base) (builtins.genList (x: x) n)
    else if t == "true" then T.mkTrue
    else if t == "false" then T.mkFalse
    else if t == "tt" then T.mkTt
    else if t == "refl" then T.mkRefl
    else if t == "string-lit" then T.mkStringLit h.value
    else if t == "int-lit" then T.mkIntLit h.value
    else if t == "float-lit" then T.mkFloatLit h.value
    else if t == "attrs-lit" then T.mkAttrsLit
    else if t == "path-lit" then T.mkPathLit
    else if t == "fn-lit" then T.mkFnLit
    else if t == "any-lit" then T.mkAnyLit
    # `nil elem` = `descCon (listDesc elem) (pair true tt)` — tag true
    # selects the nil-constructor branch, whose payload type is ⊤.
    else if t == "nil" then
      T.mkDescCon (elaborate depth (listDesc h.elem))
        (T.mkPair T.mkTrue T.mkTt)
    # `cons elem head tail` = `descCon (listDesc elem)
    #   (pair false (pair head (pair tail tt)))`. Trampolined for deep lists
    # (5000+ elements). The outer `listDesc elem` is elaborated ONCE for the
    # chain and the resulting D is shared across all emitted desc-cons; the
    # check/eval desc-con trampolines use reference identity on D to peel
    # homogeneous chains. The chain peel stops at the first tail that is
    # not a `cons` HOAS node (typically `nil`, which elaborates via its own
    # branch); that base is elaborated recursively with the outer depth.
    else if t == "cons" then
      let
        chain = builtins.genericClosure {
          startSet = [{ key = 0; val = h; }];
          operator = item:
            if builtins.isAttrs item.val && item.val ? _htag && item.val._htag == "cons"
            then [{ key = item.key + 1; val = item.val.tail; }]
            else [];
        };
        n = builtins.length chain - 1;
        base = (builtins.elemAt chain n).val;
        # All layers share the outer element type. Elaborate listDesc once.
        dTm = elaborate depth (listDesc h.elem);
      in builtins.foldl' (acc: i:
        let node = (builtins.elemAt chain (n - 1 - i)).val; in
        T.mkDescCon dTm
          (T.mkPair T.mkFalse
            (T.mkPair (elaborate depth node.head)
              (T.mkPair acc T.mkTt)))
      ) (elaborate depth base) (builtins.genList (x: x) n)
    else if t == "pair" then
      T.mkPair (elaborate depth h.fst) (elaborate depth h.snd)
    # `inl l r a` = `descCon (sumDesc l r) (pair true (pair a tt))` — tag true
    # selects the inl-constructor branch, whose payload type is Σ(a:l).⊤.
    else if t == "inl" then
      T.mkDescCon (elaborate depth (sumDesc h.left h.right))
        (T.mkPair T.mkTrue (T.mkPair (elaborate depth h.term) T.mkTt))
    # `inr l r b` = `descCon (sumDesc l r) (pair false (pair b tt))` — tag false
    # selects the inr-constructor branch, whose payload type is Σ(b:r).⊤.
    else if t == "inr" then
      T.mkDescCon (elaborate depth (sumDesc h.left h.right))
        (T.mkPair T.mkFalse (T.mkPair (elaborate depth h.term) T.mkTt))
    else if t == "opaque-lam" then
      T.mkOpaqueLam h._fnBox (elaborate depth h.piHoas)
    else if t == "str-eq" then
      T.mkStrEq (elaborate depth h.lhs) (elaborate depth h.rhs)
    else if t == "absurd" then
      T.mkAbsurd (elaborate depth h.type) (elaborate depth h.term)
    else if t == "ann" then
      T.mkAnn (elaborate depth h.term) (elaborate depth h.type)
    # Macro constructor fallback: elaborate as the annotated lam cascade.
    # Saturated chain applications are recognised in the `app` branch
    # below and emit flat `desc-con` Tms without touching this branch.
    else if t == "dt-ctor-mono" then elaborate depth h.fallback
    else if t == "dt-ctor-poly" then elaborate depth h.fallback
    # `app` tries flat-chain flattening for saturated macro-constructor
    # applications first (mirrors H.cons at hoas.nix:288-307). Non-chain
    # applications fall through to the regular `mkApp (elab fn) (elab arg)`.
    else if t == "app" then
      let flat = tryFlattenCtorChain depth h; in
      if flat != null then flat
      else T.mkApp (elaborate depth h.fn) (elaborate depth h.arg)
    else if t == "fst" then T.mkFst (elaborate depth h.pair)
    else if t == "snd" then T.mkSnd (elaborate depth h.pair)

    # -- Descriptions --
    else if t == "desc" then T.mkDesc
    else if t == "desc-ret" then T.mkDescRet
    else if t == "desc-arg" then
      let marker = mkMarker depth;
      in T.mkDescArg (elaborate depth h.S) (elaborate (depth + 1) (h.body marker))
    else if t == "desc-rec" then T.mkDescRec (elaborate depth h.D)
    else if t == "desc-pi" then
      T.mkDescPi (elaborate depth h.S) (elaborate depth h.D)
    else if t == "mu" then T.mkMu (elaborate depth h.D)
    else if t == "desc-con" then
      T.mkDescCon (elaborate depth h.D) (elaborate depth h.d)
    else if t == "desc-ind" then
      T.mkDescInd (elaborate depth h.D) (elaborate depth h.motive)
        (elaborate depth h.step) (elaborate depth h.scrut)
    else if t == "desc-elim" then
      T.mkDescElim (elaborate depth h.motive) (elaborate depth h.onRet)
        (elaborate depth h.onArg) (elaborate depth h.onRec)
        (elaborate depth h.onPi) (elaborate depth h.scrut)

    # -- Eliminators --
    # `ind motive base step scrut` elaborates to `descInd natDesc motive step' scrut`,
    # where step' adapts the (k, ih)→P(S k) protocol to descInd's
    # (d : ⟦natDesc⟧μ, ih : All natDesc natDesc P d) → P(con d) protocol.
    # The adapter dispatches on `fst d : Bool` via boolElim:
    #   b = true  (zero):  r : ⊤,           rih : ⊤           → `base`
    #   b = false (succ):  r : μnat × ⊤,    rih : P(fst r) × ⊤ → `step (fst r) (fst rih)`
    # Conv obligations: r ≡ tt (⊤-η) on the zero branch; r ≡ (fst r, tt) on
    # the succ branch (Σ-η + ⊤-η). Both rules live in conv.nix.
    else if t == "nat-elim" then
      let
        motive = h.motive;
        base = h.base;
        step = h.step;
        subDesc = b: boolElim (lam "_" bool (_: desc))
                              descRet
                              (descRec descRet)
                              b;
        natRecRet = descRec descRet;
        # Let-bind motive, base, step at their required types so their
        # occurrences in the adapter body are VARs (inferable via
        # lookupType — check.nix:271-272) rather than bare `lam`s (no
        # infer rule). Lambdas are checkable-only in this bidirectional
        # kernel; `let` is the canonical construct for making a checkable
        # value available at inferable positions (check rule at
        # check.nix:170-182). Types pinned by the desc-ind check rule
        # (check.nix:521-539) via the `ind` → `descInd` protocol
        # translation:
        #   P : nat → U(0)
        #   B : P zero
        #   S : Π(k:nat). P k → P (succ k)
        # Conv obligations on the adapter body (⊤-η on zero branch,
        # Σ-η + ⊤-η on succ branch) discharge via the conv.nix eta rules.
        piMotiveTy = forall "_" nat (_: u 0);
        body =
          let_ "P" piMotiveTy motive (P:
          let_ "B" (app P zero) base (base2:
          let_ "S" (forall "k" nat (k:
                    forall "_" (app P k) (_: app P (succ k)))) step (step2:
            descInd natDesc P
              (lam "d" (interpHoas natDesc (mu natDesc)) (d:
               lam "ih" (allHoas natDesc natDesc P d) (ih:
                 app (app
                   (boolElim
                      (lam "b" bool (b:
                         forall "r" (interpHoas (subDesc b) (mu natDesc)) (r:
                         forall "rih" (allHoas natDesc (subDesc b) P r) (_:
                           app P (descCon natDesc (pair b r))))))
                      (lam "r" unit (_:
                       lam "rih" unit (_: base2)))
                      (lam "r" (interpHoas natRecRet (mu natDesc)) (r:
                       lam "rih" (allHoas natDesc natRecRet P r) (rih:
                         app (app step2 (fst_ r)) (fst_ rih))))
                      (fst_ d))
                   (snd_ d))
                   ih)))
              h.scrut)));
      in elaborate depth body
    else if t == "bool-elim" then
      T.mkBoolElim (elaborate depth h.motive) (elaborate depth h.onTrue)
        (elaborate depth h.onFalse) (elaborate depth h.scrut)
    # `listElim elem motive onNil onCons scrut` elaborates to
    # `descInd (listDesc elem) motive step' scrut`, with an adapter that
    # dispatches on the constructor tag `fst d : Bool` via boolElim:
    #   b = true  (nil):  r : ⊤,                     rih : ⊤              → onNil
    #   b = false (cons): r : Σ(h:elem).(μlist × ⊤), rih : P(fst(snd r))×⊤ →
    #                         onCons (fst r) (fst (snd r)) (fst rih)
    # motive/onNil/onCons are let-bound at their required types so their
    # occurrences in the adapter body are VARs (inferable via lookupType)
    # rather than bare lambdas (no infer rule). Conv obligations on the
    # adapter body discharge via conv.nix's Σ-η and ⊤-η rules.
    else if t == "list-elim" then
      let
        elem = h.elem;
        motive = h.motive;
        onNil = h.onNil;
        onCons = h.onCons;
        listDescElem = listDesc elem;
        consRecRet = descArg elem (_: descRec descRet);
        subDesc = b: boolElim (lam "_" bool (_: desc))
                              descRet
                              consRecRet
                              b;
        piMotiveTy = forall "_" (listOf elem) (_: u 0);
        body =
          let_ "P" piMotiveTy motive (P:
          let_ "N" (app P (nil elem)) onNil (N:
          let_ "C" (forall "h" elem (hVar:
                    forall "t" (listOf elem) (tVar:
                    forall "_" (app P tVar) (_:
                      app P (cons elem hVar tVar))))) onCons (C:
            descInd listDescElem P
              (lam "d" (interpHoas listDescElem (mu listDescElem)) (d:
               lam "ih" (allHoas listDescElem listDescElem P d) (ih:
                 app (app
                   (boolElim
                      (lam "b" bool (b:
                         forall "r" (interpHoas (subDesc b) (mu listDescElem)) (r:
                         forall "rih" (allHoas listDescElem (subDesc b) P r) (_:
                           app P (descCon listDescElem (pair b r))))))
                      (lam "r" unit (_:
                       lam "rih" unit (_: N)))
                      (lam "r" (interpHoas consRecRet (mu listDescElem)) (r:
                       lam "rih" (allHoas listDescElem consRecRet P r) (rih:
                         app (app (app C (fst_ r)) (fst_ (snd_ r))) (fst_ rih))))
                      (fst_ d))
                   (snd_ d))
                   ih)))
              h.scrut)));
      in elaborate depth body
    # `sumElim left right motive onLeft onRight scrut` elaborates to
    # `descInd (sumDesc left right) motive step' scrut`, with an adapter that
    # dispatches on the constructor tag `fst d : Bool` via boolElim:
    #   b = true  (inl): r : Σ(a:left).⊤,  rih : ⊤ → onLeft  (fst r)
    #   b = false (inr): r : Σ(b:right).⊤, rih : ⊤ → onRight (fst r)
    # Sum is non-recursive, so rih : ⊤ in BOTH branches (no `fst_ rih`
    # to extract a recursive IH). motive/onLeft/onRight are let-bound at
    # their required types so their occurrences in the adapter body are VARs
    # (inferable via lookupType) rather than bare lambdas (no infer rule).
    # Conv obligations (Σ-η + ⊤-η on both branches) discharge via conv.nix.
    else if t == "sum-elim" then
      let
        left = h.left;
        right = h.right;
        motive = h.motive;
        onLeft = h.onLeft;
        onRight = h.onRight;
        sumDescLR = sumDesc left right;
        leftArm = descArg left (_: descRet);
        rightArm = descArg right (_: descRet);
        subDesc = b: boolElim (lam "_" bool (_: desc))
                              leftArm
                              rightArm
                              b;
        piMotiveTy = forall "_" (sum left right) (_: u 0);
        body =
          let_ "P" piMotiveTy motive (P:
          let_ "L" (forall "a" left (aVar: app P (inl left right aVar))) onLeft (L:
          let_ "R" (forall "b" right (bVar: app P (inr left right bVar))) onRight (R:
            descInd sumDescLR P
              (lam "d" (interpHoas sumDescLR (mu sumDescLR)) (d:
               lam "ih" (allHoas sumDescLR sumDescLR P d) (ih:
                 app (app
                   (boolElim
                      (lam "b" bool (b:
                         forall "r" (interpHoas (subDesc b) (mu sumDescLR)) (r:
                         forall "rih" (allHoas sumDescLR (subDesc b) P r) (_:
                           app P (descCon sumDescLR (pair b r))))))
                      (lam "r" (interpHoas leftArm (mu sumDescLR)) (r:
                       lam "rih" unit (_:
                         app L (fst_ r))))
                      (lam "r" (interpHoas rightArm (mu sumDescLR)) (r:
                       lam "rih" unit (_:
                         app R (fst_ r))))
                      (fst_ d))
                   (snd_ d))
                   ih)))
              h.scrut)));
      in elaborate depth body
    else if t == "j" then
      T.mkJ (elaborate depth h.type) (elaborate depth h.lhs)
        (elaborate depth h.motive) (elaborate depth h.base)
        (elaborate depth h.rhs) (elaborate depth h.eq)

    else throw "hoas.elaborate: unknown tag: ${t}";

  # -- Convenience: elaborate from depth 0 --
  elab = elaborate 0;

  # -- Convenience wrappers using the kernel checker --
  checkHoas = hoasTy: hoasTm:
    let
      ty = elab hoasTy;
      tm = elab hoasTm;
      vTy = E.eval [] ty;
    in CH.runCheck (CH.check CH.emptyCtx tm vTy);

  inferHoas = hoasTm:
    let tm = elab hoasTm;
    in CH.runCheck (CH.infer CH.emptyCtx tm);

  # -- Natural number literal helper --
  natLit = n:
    builtins.foldl' (acc: _: succ acc) zero (builtins.genList (x: x) n);

  # -- Description-level helpers: interpHoas / allHoas --
  #
  # These elaborate to `descElim` spines that compute the same values as
  # eval.nix's interpF / allTyF (traceable line-by-line against eval.nix
  # 213-322). Every HOAS binder below mirrors a named interpMotive /
  # interpOn* / mkAllMotive / allOn* in that file.
  #
  # Principled note on lam annotations: check.nix's check-lam (84-90)
  # discards the HOAS lam's domain annotation and uses the expected type's
  # domain when descending, so inner case annotations are for READABILITY
  # only. BUT the motive's annotations build paTy / peTy / ppTy in the
  # desc-elim check rule (check.nix:452-482), so the motive's d-annotation
  # MUST be the true type of d, not a lax U(0) as in eval.nix.
  #
  # eval.nix uses `term.mkU 0` for d in mkAllMotive; that's sound eval-side
  # because eval is not re-checked. HOAS cannot get away with that: when
  # allHoas's elaborated onArg runs through check, `fst_ d` fails unless
  # d's inferred type is a VSigma. The fix is confined to the motive.
  # Evaluation still matches allTyF: the motive body appears only in type
  # positions, never in the computed value.

  # interpHoas D X  ≡  ⟦D⟧(X)  as a closed kernel TERM.
  interpHoas = D: X:
    let
      # motive : λ(_:Desc). U(0) → U(0)
      motive = lam "_" desc (_: forall "_" (u 0) (_: u 0));
      # onRet  : λ(X:U(0)). ⊤
      onRet  = lam "X" (u 0) (_: unit);
      # onArg  : λ(S:U(0)) (T:S→Desc) (ih:Π(s:S).U→U) (X:U(0)). Σ(s:S). ih s X
      onArg  = lam "S" (u 0) (S:
               lam "T" (forall "_" S (_: desc)) (_:
               lam "ih" (forall "s" S (_: forall "_" (u 0) (_: u 0))) (ih:
               lam "X" (u 0) (X':
                 sigma "s" S (s: app (app ih s) X')))));
      # onRec  : λ(D:Desc) (ih:U→U) (X:U(0)). X × ih X
      onRec  = lam "D" desc (_:
               lam "ih" (forall "_" (u 0) (_: u 0)) (ih:
               lam "X" (u 0) (X':
                 sigma "_" X' (_: app ih X'))));
      # onPi   : λ(S:U(0)) (D:Desc) (ih:U→U) (X:U(0)). (S→X) × ih X
      onPi   = lam "S" (u 0) (S:
               lam "D" desc (_:
               lam "ih" (forall "_" (u 0) (_: u 0)) (ih:
               lam "X" (u 0) (X':
                 sigma "_" (forall "_" S (_: X')) (_: app ih X')))));
    in app (descElim motive onRet onArg onRec onPi D) X;

  # allHoas Douter Dsub P d ≡ All Douter Dsub P d — the inductive-hypothesis
  # TYPE for d : ⟦Dsub⟧(μDouter), where P : μDouter → U. The motive closes
  # over Douter; the four cases mention Douter only through P's domain.
  allHoas = Douter: Dsub: P: d:
    let
      # motive : λ(D:Desc). (μDouter → U) → ⟦D⟧(μDouter) → U
      # The inner d-domain MUST be interpHoas D (mu Douter) — see block
      # comment above. paTy / peTy / ppTy in the desc-elim check rule
      # reduce this to the concrete Σ / ×-shapes the case bodies expect.
      motive = lam "_" desc (Dm:
               forall "P" (forall "_" (mu Douter) (_: u 0)) (_:
               forall "d" (interpHoas Dm (mu Douter)) (_: u 0)));
      # onRet : λP. λ(d:⊤). ⊤
      onRet  = lam "P" (forall "_" (mu Douter) (_: u 0)) (_:
               lam "d" unit (_: unit));
      # onArg : λS T ihA P d. ihA (fst d) P (snd d)
      onArg  = lam "S" (u 0) (S:
               lam "T" (forall "_" S (_: desc)) (T:
               lam "ihA" (forall "s" S (s:
                          forall "P" (forall "_" (mu Douter) (_: u 0)) (_:
                          forall "d" (interpHoas (app T s) (mu Douter)) (_: u 0)))) (ihA:
               lam "P" (forall "_" (mu Douter) (_: u 0)) (P2:
               lam "d" (sigma "s" S (s: interpHoas (app T s) (mu Douter))) (d2:
                 app (app (app ihA (fst_ d2)) P2) (snd_ d2))))));
      # onRec : λD ihA P d. P (fst d) × ihA P (snd d)
      onRec  = lam "D" desc (D2:
               lam "ihA" (forall "P" (forall "_" (mu Douter) (_: u 0)) (_:
                          forall "d" (interpHoas D2 (mu Douter)) (_: u 0))) (ihA:
               lam "P" (forall "_" (mu Douter) (_: u 0)) (P2:
               lam "d" (sigma "_" (mu Douter) (_: interpHoas D2 (mu Douter))) (d2:
                 sigma "_" (app P2 (fst_ d2)) (_:
                   app (app ihA P2) (snd_ d2))))));
      # onPi : λS D ihA P d. (Π(s:S). P (fst d s)) × ihA P (snd d)
      onPi   = lam "S" (u 0) (S:
               lam "D" desc (D2:
               lam "ihA" (forall "P" (forall "_" (mu Douter) (_: u 0)) (_:
                          forall "d" (interpHoas D2 (mu Douter)) (_: u 0))) (ihA:
               lam "P" (forall "_" (mu Douter) (_: u 0)) (P2:
               lam "d" (sigma "_" (forall "_" S (_: mu Douter)) (_: interpHoas D2 (mu Douter))) (d2:
                 sigma "_"
                   (forall "s" S (s: app P2 (app (fst_ d2) s)))
                   (_: app (app ihA P2) (snd_ d2)))))));
    in app (app (descElim motive onRet onArg onRec onPi Dsub) P) d;

  # -- Description-based prelude types (using hardcoded Bool as tag domain) --
  # Bool remains a kernel primitive here because descriptions use it as the
  # constructor-tag domain (natDesc = descArg bool …), making a Bool rebind
  # via μBoolDesc self-referential. Bool is rebound via Fin 2 once the
  # indexed grammar lifts the circularity.

  # natDesc : Desc — tag true = zero (no recursion), tag false = succ (one rec arg)
  natDesc = descArg bool (b:
    boolElim (lam "_" bool (_: desc))
      descRet
      (descRec descRet)
      b);

  # listDesc elem : Desc — tag true = nil, tag false = cons (head : elem, tail : rec)
  listDesc = elem: descArg bool (b:
    boolElim (lam "_" bool (_: desc))
      descRet
      (descArg elem (_: descRec descRet))
      b);

  # sumDesc l r : Desc — tag true = inl (arg : l), tag false = inr (arg : r)
  sumDesc = l: r: descArg bool (b:
    boolElim (lam "_" bool (_: desc))
      (descArg l (_: descRet))
      (descArg r (_: descRet))
      b);

  # Pre-elaborated natDesc — used by the forthcoming nat/zero/succ/nat-elim
  # elaborate branches to avoid re-elaborating on every constructor.
  natDescTm = elab natDesc;

  # -- Datatype macro: declarative datatype signatures to DataSpec --
  #
  # A signature is a name and a non-empty ordered list of constructors;
  # each constructor has a name and an ordered list of field
  # specifications. The macro compiles a signature to a DataSpec record
  #   { name, cons, D, T, <conName_i>, elim, _dtypeMeta }
  # whose `D` is a closed description, `T = μ D`, each constructor name
  # binds a curried HOAS term, and `elim` is the generic eliminator.
  #
  # The macro is a pure Nix function from the signature attrset to an
  # attrset of HOAS terms; the kernel never learns about it.

  # Field specifications. Each is a tagged attrset; position in the
  # constructor's field list is the position in the constructor's
  # argument list and in the payload spine.
  _fieldMarker = "__nix-effects-datatype-field__";
  field    = name: type: { _fieldTag = _fieldMarker; kind = "data";  inherit name type; };
  fieldD   = name: tyFn: { _fieldTag = _fieldMarker; kind = "dataD"; inherit name; typeFn = tyFn; };
  recField = name:       { _fieldTag = _fieldMarker; kind = "rec";   inherit name; };
  piField  = name: S:    { _fieldTag = _fieldMarker; kind = "pi";    inherit name S; };
  piFieldD = name: SFn:  { _fieldTag = _fieldMarker; kind = "piD";   inherit name; SFn = SFn; };

  # Constructor specification.
  _conMarker = "__nix-effects-datatype-con__";
  con = name: fields: { _conTag = _conMarker; inherit name fields; };

  # conDesc prev fields : Hoas Desc
  # Compile a field list into a description spine. `prev` threads HOAS
  # markers for earlier `field`/`fieldD` bindings (the only field kinds
  # that bind a description-level variable via descArg); `rec`, `pi`,
  # `piD` do not extend `prev`.
  conDesc = prev: fields:
    if fields == [] then descRet
    else let
      f = builtins.head fields;
      rest = builtins.tail fields;
      k = f.kind;
    in
      if k == "data"  then descArg f.type         (v: conDesc (prev // { ${f.name} = v; }) rest)
      else if k == "dataD" then descArg (f.typeFn prev) (v: conDesc (prev // { ${f.name} = v; }) rest)
      else if k == "rec"   then descRec (conDesc prev rest)
      else if k == "pi"    then descPi f.S        (conDesc prev rest)
      else if k == "piD"   then descPi (f.SFn prev) (conDesc prev rest)
      else throw "datatype: unknown field kind '${k}'";

  # spineDesc descs : Hoas Desc
  # Combine per-constructor descriptions into a single description.
  # Uniform recursion: the singleton case IS the leaf (no outer tag);
  # n>=2 produces a right-associated Bool tag spine. Unrolls to the
  # familiar shapes — n=2 reduces to `descArg bool (b: boolElim _ D1 D2 b)`,
  # the same Bool-fold the prelude descriptions above use directly.
  spineDesc = descs:
    let n = builtins.length descs; in
    if n == 0 then throw "datatype: n=0 rejected (use H.void)"
    else if n == 1 then builtins.head descs
    else
      let
        D1 = builtins.elemAt descs 0;
        rest = builtins.tail descs;
      in descArg bool (b:
        boolElim (lam "_" bool (_: desc)) D1 (spineDesc rest) b);

  # payloadTuple xs : Hoas
  # Build a right-nested pair from an ordered list of HOAS terms.
  # Empty list is the unit `tt`.
  payloadTuple = xs:
    if xs == [] then tt
    else pair (builtins.head xs) (payloadTuple (builtins.tail xs));

  # encodeTag t n payload : Hoas
  # Wrap `payload` with the (n-1)-deep Bool tag prefix that commits at
  # position t (0-based) out of n total. Mirrors spineDesc structurally:
  # at every level a `false_` bit descends into the rest-spine, and the
  # commit at position t is `pair true_ payload`. n=1 has no prefix.
  encodeTag = t: n: payload:
    if n == 1 then payload
    else if t == 0 then pair true_ payload
    else pair false_ (encodeTag (t - 1) (n - 1) payload);

  # Build a monomorphic DataSpec from a non-empty list of ConSpecs.
  datatype = name: consList:
    let
      n = builtins.length consList;
      conNames = map (c: c.name) consList;

      # First duplicate constructor name (null if none).
      dupConName = let
        idxs = builtins.genList (x: x) n;
        step = acc: i:
          if acc != null then acc
          else let nm = builtins.elemAt conNames i;
                   seen = builtins.genList (j: builtins.elemAt conNames j) i;
               in if builtins.elem nm seen then nm else null;
        in builtins.foldl' step null idxs;

      conDescs = map (c: conDesc {} c.fields) consList;
      D = spineDesc conDescs;
      T = mu D;

      # Type of field f, given `prev` (markers for earlier data/dataD
      # fields). data/dataD bind a description-level variable visible to
      # later dependent forms; rec/pi/piD compile to descRec/descPi which
      # do not bind one (matching conDesc's marker-threading rule).
      fieldTyOf = f: prev:
        if      f.kind == "data"  then f.type
        else if f.kind == "dataD" then f.typeFn prev
        else if f.kind == "rec"   then T
        else if f.kind == "pi"    then forall "_" f.S (_: T)
        else if f.kind == "piD"   then forall "_" (f.SFn prev) (_: T)
        else throw "datatype '${name}': unknown field kind '${f.kind}'";

      extendsPrev = f: f.kind == "data" || f.kind == "dataD";
      isIHField = f: f.kind == "rec" || f.kind == "pi" || f.kind == "piD";

      # Π type of constructor `c`. Zero-field cons have implicit type T;
      # fielded cons produce a Π cascade over the field list terminating
      # in T. Same field-kind dispatch as the bare-lam cascade in mkCtor.
      ctorTyOf = c:
        if c.fields == [] then T
        else
          let
            tyGo = remaining: prev:
              if remaining == [] then T
              else
                let f = builtins.head remaining;
                    rest = builtins.tail remaining;
                in forall f.name (fieldTyOf f prev) (v:
                     tyGo rest
                       (if extendsPrev f then prev // { ${f.name} = v; } else prev));
          in tyGo c.fields {};

      # Build constructor term for the i-th constructor.
      # For zero-field cons, just `descCon D <tag-encoded tt>` — already a
      # complete checkable term. For fielded cons, build a curried lam
      # cascade emitting descCon over the payloadTuple of the args, and
      # wrap in `ann` against the constructor's full Π type so it stays
      # inferable when applied (same justification as the elim's ann).
      #
      # Fielded cons are additionally tagged `dt-ctor-mono` so `elaborate`
      # can recognise saturated applications in the `app` branch and emit a
      # flat `desc-con` Tm (mirroring the H.cons trampoline at
      # hoas.nix:288-307). Unsaturated or non-chain uses route through
      # `fallback` = `ann bareCtor ctorTyOf`, preserving the inferable
      # surface.
      mkCtor = i: c:
        if c.fields == []
        then descCon D (encodeTag i n (payloadTuple []))
        else
          let
            bareGo = remaining: prev: collected:
              if remaining == [] then
                descCon D (encodeTag i n (payloadTuple collected))
              else
                let f = builtins.head remaining;
                    rest = builtins.tail remaining;
                in lam f.name (fieldTyOf f prev) (v:
                     bareGo rest
                       (if extendsPrev f then prev // { ${f.name} = v; } else prev)
                       (collected ++ [v]));
            bareCtor = bareGo c.fields {} [];
            fallback = ann bareCtor (ctorTyOf c);
          in {
            _htag = "dt-ctor-mono";
            ctorIndex = i;
            nCtors = n;
            dHoas = D;
            nFields = builtins.length c.fields;
            fields = c.fields;
            inherit fallback;
          };

      ctorRecord = builtins.listToAttrs (builtins.genList (i:
        let c = builtins.elemAt consList i;
        in { name = c.name; value = mkCtor i c; }
      ) n);

      # Type of step_i. For zero-field constructors this is just `P C_i`.
      # For fielded constructors: Π over fields (in declaration order)
      # then Π over rec/pi IHs (in rec/pi-only declaration order),
      # terminating in P (C_i applied-to-fields).
      #
      # The terminal `app P (foldl' app C_i fieldMarkers)` requires C_i
      # to be inferable so the application chain types — hence mkCtor's
      # ann-wrapping for fielded cons.
      stepTyOf = P: i: c:
        if c.fields == [] then app P (mkCtor i c)
        else
          let
            ctor = mkCtor i c;

            # Π over IH binders, one per rec/pi/piD field. `markers` is
            # the field-marker list collected by `fieldGo` (in declaration
            # order); each entry carries the marker plus the `prev`
            # snapshot at binding time, used for piD's dependent SFn.
            ihGo = ihRemaining: markers:
              let
                applied = builtins.foldl' (acc: m: app acc m.marker)
                                          ctor
                                          markers;
              in
                if ihRemaining == [] then app P applied
                else
                  let f = builtins.head ihRemaining;
                      rest = builtins.tail ihRemaining;
                      m = builtins.head (builtins.filter
                            (x: x.name == f.name) markers);
                      ihTy =
                        if      f.kind == "rec" then app P m.marker
                        else if f.kind == "pi"  then
                          forall "s" f.S (s: app P (app m.marker s))
                        else
                          forall "s" (f.SFn m.prev) (s:
                            app P (app m.marker s));
                  in forall ("ih_" + f.name) ihTy (_: ihGo rest markers);

            # Π over fields, collecting markers + each field's `prev`
            # snapshot. After the last field, `ihGo` adds the IH binders.
            fieldGo = remaining: prev: collected:
              if remaining == [] then
                ihGo (builtins.filter isIHField c.fields) collected
              else
                let f = builtins.head remaining;
                    rest = builtins.tail remaining;
                in forall f.name (fieldTyOf f prev) (v:
                     fieldGo rest
                       (if extendsPrev f then prev // { ${f.name} = v; } else prev)
                       (collected ++ [{
                          inherit (f) name kind;
                          marker = v;
                          prev = prev;
                        }]));
          in fieldGo c.fields {} [];

      # Apply user-supplied step `s` to the projections of `payload` and
      # `payloadIH` per `c`'s field list.
      #
      # Field x_j (0-based) lives at fst (snd^j payload), where the
      # payload is a right-nested pair from payloadTuple — so fields in
      # declaration order line up with snd-descents.
      #
      # For payloadIH, only rec/pi/piD fields contribute a Σ component
      # (data/dataD's allHoas case is the identity on the tail). The
      # i-th rec/pi IH (0-based among rec/pi-only fields, in declaration
      # order) lives at fst (snd^i payloadIH).
      buildStepApply = s: c: payload: payloadIH:
        if c.fields == [] then s
        else
          let
            projAt = j: src:
              let go = idx: acc:
                if idx == 0 then fst_ acc
                else go (idx - 1) (snd_ acc);
              in go j src;
            fieldArgs = builtins.genList (j: projAt j payload)
                                         (builtins.length c.fields);
            ihCount = builtins.length (builtins.filter isIHField c.fields);
            ihArgs = builtins.genList (i: projAt i payloadIH) ihCount;
            withFields = builtins.foldl' (acc: a: app acc a) s fieldArgs;
            withIHs = builtins.foldl' (acc: a: app acc a) withFields ihArgs;
          in withIHs;

      # dispatchStep ctx descs steps cons payload payloadIH : Hoas
      # Walks the per-constructor descriptions in declaration order,
      # threading an outer-context wrapper `ctx` that reconstitutes the
      # full payload at each level (used in the boolElim motive so conv
      # discharges P(descCon D (ctx ...)) ≡ P(C_i ...) via Σ-η + ⊤-η).
      # n=1 (leaf) returns the user step applied to its projections;
      # n>=2 emits a boolElim that commits to constructor i on `true_`
      # and descends into the rest-spine on `false_`.
      dispatchStep = P: ctx: descs: steps: cons: payload: payloadIH:
        let n' = builtins.length descs; in
        if n' == 1 then
          buildStepApply (builtins.head steps) (builtins.head cons) payload payloadIH
        else
          let
            D1 = builtins.elemAt descs 0;
            s1 = builtins.head steps;
            c1 = builtins.head cons;
            restD = builtins.tail descs;
            restS = builtins.tail steps;
            restC = builtins.tail cons;
            restSpine = spineDesc restD;
            subDescAt = b:
              boolElim (lam "_" bool (_: desc)) D1 restSpine b;
            motive = lam "b" bool (b:
              forall "r" (interpHoas (subDescAt b) T) (r:
              forall "rih" (allHoas D (subDescAt b) P r) (_:
                app P (descCon D (ctx (pair b r))))));
            onTrue = lam "r" (interpHoas D1 T) (r:
                     lam "rih" (allHoas D D1 P r) (rih:
                       buildStepApply s1 c1 r rih));
            ctx' = local: ctx (pair false_ local);
            onFalse = lam "r" (interpHoas restSpine T) (r:
                      lam "rih" (allHoas D restSpine P r) (rih:
                        dispatchStep P ctx' restD restS restC r rih));
          in app (app
               (boolElim motive onTrue onFalse (fst_ payload))
               (snd_ payload))
               payloadIH;

      # Generic eliminator. The closed term is wrapped in `ann` against
      # its full Π type so it stays inferable when applied via `app` in
      # checked positions — the bidirectional kernel has no infer rule
      # for bare `lam`. `ann` is eval-transparent (eval discards it
      # before reduction), so nf-equivalence against the inline-adapter
      # spelling is preserved.
      motiveTy = forall "_" T (_: u 0);
      stepNames = builtins.genList (i: "step_${toString i}") n;

      # Wrap a body with `lam step_i (stepTyOf P i c)` for each
      # constructor in declaration order, then call `mkBody` with the
      # collected step markers.
      buildLamCascade = mkBody: P:
        let
          go = i: stepsAcc:
            if i == n then mkBody stepsAcc
            else
              let c = builtins.elemAt consList i; in
              lam (builtins.elemAt stepNames i) (stepTyOf P i c) (s:
                go (i + 1) (stepsAcc ++ [s]));
        in go 0 [];

      # Same cascade for the elim's Π type.
      buildPiCascade = mkBody: P:
        let
          go = i:
            if i == n then mkBody
            else
              let c = builtins.elemAt consList i; in
              forall (builtins.elemAt stepNames i) (stepTyOf P i c) (_:
                go (i + 1));
        in go 0;

      elimTy =
        forall "P" motiveTy (P:
        buildPiCascade
          (forall "scrut" T (scrut: app P scrut))
          P);

      elimBody =
        lam "P" motiveTy (P:
        buildLamCascade (steps:
          lam "scrut" T (scrut:
            descInd D P
              (lam "d" (interpHoas D T) (d:
               lam "ih" (allHoas D D P d) (ih:
                 dispatchStep P (x: x) conDescs steps consList d ih)))
              scrut))
          P);

      elim = ann elimBody elimTy;

      _dtypeMeta = {
        inherit name;
        cons = map (c: {
          name = c.name;
          fields = map (f: { name = f.name; kind = f.kind; }) c.fields;
        }) consList;
      };

      # Per-field polymorphic types, consumed by datatypeP to build the
      # outer `ann (λparams. monoField) (Π(params). monoFieldTy)` wrapping.
      # Zero-field cons have type T (not Π), just like fielded ctors with no
      # fields; ctorTyOf handles both cases.
      _tys = {
        D = desc;
        T = u 0;
        elim = elimTy;
      } // (builtins.listToAttrs (builtins.genList (i:
        let c = builtins.elemAt consList i; in
        { name = c.name; value = ctorTyOf c; }
      ) n));
    in
      if n == 0 then throw "datatype '${name}': n=0 rejected (use H.void)"
      else if dupConName != null then
        throw "datatype '${name}': duplicate constructor name '${dupConName}'"
      else (ctorRecord // {
        inherit name D elim _dtypeMeta _tys;
        # Attach `_dtypeMeta` to the exported `T` so the elaborate-layer
        # extract path can recover constructor + field names when
        # decomposing macro-generated VMu values. Internal uses of `T`
        # within this let-block (fieldTyOf, ctorTyOf, dispatchStep, etc.)
        # are unaffected — the HOAS elaborator only reads `_htag` and `D`
        # from a "mu" form; extra attrs are ignored.
        T = T // { inherit _dtypeMeta; };
        _cons = consList;
      });

  # Polymorphic datatype builder. Each output field f is the mono field
  # λ-abstracted over params, wrapped in `ann` against `Π(params). T_f`
  # where `T_f` is pulled from the mono spec's `_tys.<field>`. The outer
  # `ann` is what makes the curried constructor/eliminator inferable in
  # checked positions after the first parameter application; without it
  # `app <polyField> firstArg` would have a bare-λ head and fail synthesis.
  #
  # The probe call `mkCons dummyMarkers` is only used to extract
  # constructor names and metadata (via shallow attrs c.name / f.name /
  # f.kind). Each polymorphic field's closure re-runs `mkCons` with real
  # HOAS markers at elaborate-time, so field types and constructor bodies
  # are never resolved against the probe's dummy values.
  datatypeP = name: params: mkCons:
    let
      nParams = builtins.length params;
      monoOf = markers: datatype name (mkCons markers);
      # A parameter's `kind` is either a fixed Hoas (the common case,
      # e.g. `kind = u 0`) or a function from the list of previously-bound
      # parameter markers to a Hoas (e.g. for W-type's `P : S → U` where
      # `kind = ms: forall "_" (builtins.elemAt ms 0) (_: u 0)`). This is
      # the parameter-level analogue of `field` vs `fieldD` and `piField`
      # vs `piFieldD`: same "depends on prior bindings" pattern, applied
      # one scope outward.
      resolveKind = p: markers:
        if builtins.isFunction p.kind then p.kind markers else p.kind;
      overParams = mkBody:
        let go = i: markers:
          if i == nParams then mkBody markers
          else
            let p = builtins.elemAt params i; in
            lam p.name (resolveKind p markers) (m: go (i + 1) (markers ++ [m]));
        in go 0 [];
      paramPi = mkBodyTy:
        let go = i: markers:
          if i == nParams then mkBodyTy markers
          else
            let p = builtins.elemAt params i; in
            forall p.name (resolveKind p markers) (m: go (i + 1) (markers ++ [m]));
        in go 0 [];
      polyField = fieldName:
        ann (overParams (markers:
              builtins.getAttr fieldName (monoOf markers)))
            (paramPi (markers:
              builtins.getAttr fieldName (monoOf markers)._tys));
      # Poly constructor wrapper: tagged `dt-ctor-poly` HOAS node carrying
      # the nParams/monoAt hook that `elaborate`'s `app` branch uses to
      # recognise saturated chains and flatten them into a flat `desc-con`
      # Tm. Non-saturated/non-chain uses elaborate via `fallback` (the
      # regular ann + overParams wrapping) and behave identically to the
      # pre-flattening code. For zero-field constructors the fallback's
      # inner body is the plain `descCon D payload` HOAS; for fielded
      # constructors it is the dt-ctor-mono node's ann fallback.
      polyCtor = cName:
        ann (overParams (markers:
              let m = builtins.getAttr cName (monoOf markers); in
              if builtins.isAttrs m && m ? _htag && m._htag == "dt-ctor-mono"
              then m.fallback
              else m))
            (paramPi (markers:
              builtins.getAttr cName (monoOf markers)._tys));
      # Shallow probe: only c.name / f.name / f.kind are read. u 0 as a
      # dummy HOAS is structurally valid anywhere a type is expected;
      # field type expressions are never forced during the probe.
      dummyMarkers = map (_: u 0) params;
      probe = mkCons dummyMarkers;
      conNames = map (c: c.name) probe;
      # Eagerly validate shape (n=0, duplicate con names) at datatypeP time.
      _validate = builtins.seq (monoOf dummyMarkers).name null;
      # For each constructor name, expose a `dt-ctor-poly` tagged node
      # wrapping the polyCtor fallback. Keeps unsaturated uses identical
      # to the prior ann-lam cascade; enables the elaborate app-branch to
      # detect saturated chains and emit flat desc-con Tms for stack
      # safety on deep recursive values (5000+).
      mkPolyCtorNode = cName:
        let
          # Per-ctor shallow metadata from the probe: field count and the
          # field-kind list. Used for saturation + chain-shape checks.
          probeC = builtins.head (builtins.filter (c: c.name == cName) probe);
          nFields = builtins.length probeC.fields;
        in {
          _htag = "dt-ctor-poly";
          name = cName;
          inherit nParams;
          inherit nFields;
          fields = probeC.fields;
          # HOAS accessor: given a list of parameter HOAS args, produce the
          # mono constructor HOAS (a `dt-ctor-mono` tagged node for fielded
          # ctors, or a plain `descCon` HOAS for zero-field ctors).
          monoAt = paramArgs: builtins.getAttr cName (monoOf paramArgs);
          # Fallback for non-saturated / non-chain uses.
          fallback = polyCtor cName;
        };
      ctorRecord = builtins.listToAttrs (map (cName: {
        name = cName;
        value = mkPolyCtorNode cName;
      }) conNames);
      _dtypeMeta = {
        inherit name;
        cons = map (c: {
          name = c.name;
          fields = map (f: { name = f.name; kind = f.kind; }) c.fields;
        }) probe;
      };
    in builtins.seq _validate (ctorRecord // {
      inherit name params;
      D    = polyField "D";
      # `T` carries `_dtypeMeta` so the elaborate-layer extract path can
      # peel an `app L.T A1 .. An` spine to find the polymorphic head and
      # recover constructor + field names for macro-generated VMu values.
      T    = (polyField "T") // { inherit _dtypeMeta; };
      elim = polyField "elim";
      inherit _dtypeMeta;
      _cons = probe;
    });

  # Macro-derived prelude datatypes. The top-of-module `nat`, `listOf`,
  # `sum`, their introductions, and their eliminators forward to fields of
  # these specs; extract/reifyType detect the μ-shape match and route
  # decoding through the existing nat/list/sum branches so reifiy-shape
  # equivalence is preserved.
  NatDT = datatype "Nat" [
    (con "zero" [])
    (con "succ" [ (recField "pred") ])
  ];

  ListDT = datatypeP "List" [ { name = "A"; kind = u 0; } ] (ps:
    let A = builtins.elemAt ps 0; in [
      (con "nil"  [])
      (con "cons" [ (field "head" A) (recField "tail") ])
    ]);

  SumDT = datatypeP "Sum"
    [ { name = "A"; kind = u 0; } { name = "B"; kind = u 0; } ]
    (ps: let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
      (con "inl" [ (field "value" A) ])
      (con "inr" [ (field "value" B) ])
    ]);

in mk {
  doc = ''
    # fx.types.hoas — HOAS Surface Combinators

    Higher-Order Abstract Syntax layer that lets you write kernel terms
    using Nix lambdas for variable binding. The `elaborate` function
    compiles HOAS trees to de Bruijn indexed Tm terms.

    Spec reference: kernel-spec.md §2.

    ## Example

    ```nix
    # Π(A:U₀). A → A
    H.forall "A" (H.u 0) (A: H.forall "x" A (_: A))
    ```

    ## Type Combinators

    - `nat`, `bool`, `unit`, `void` — base types
    - `string`, `int_`, `float_`, `attrs`, `path`, `function_`, `any` — primitive types
    - `listOf : Hoas → Hoas` — List(elem)
    - `sum : Hoas → Hoas → Hoas` — Sum(left, right)
    - `eq : Hoas → Hoas → Hoas → Hoas` — Eq(type, lhs, rhs)
    - `u : Int → Hoas` — Universe at level
    - `forall : String → Hoas → (Hoas → Hoas) → Hoas` — Π-type (Nix lambda for body)
    - `sigma : String → Hoas → (Hoas → Hoas) → Hoas` — Σ-type

    ## Compound Types (Sugar)

    - `record : [{ name; type; }] → Hoas` — nested Sigma (sorted fields)
    - `maybe : Hoas → Hoas` — Sum(inner, Unit)
    - `variant : [{ tag; type; }] → Hoas` — nested Sum (sorted tags)

    ## Term Combinators

    - `lam : String → Hoas → (Hoas → Hoas) → Hoas` — λ-abstraction
    - `let_ : String → Hoas → Hoas → (Hoas → Hoas) → Hoas` — let binding
    - `zero`, `succ`, `true_`, `false_`, `tt`, `refl` — intro forms
    - `nil`, `cons`, `pair`, `inl`, `inr` — data constructors
    - `stringLit`, `intLit`, `floatLit`, `attrsLit`, `pathLit`, `fnLit`, `anyLit` — primitive literals
    - `absurd`, `ann`, `app`, `fst_`, `snd_` — elimination/annotation

    ## Eliminators

    - `ind` — NatElim(motive, base, step, scrut)
    - `boolElim` — BoolElim(motive, onTrue, onFalse, scrut)
    - `listElim` — ListElim(elem, motive, onNil, onCons, scrut)
    - `sumElim` — SumElim(left, right, motive, onLeft, onRight, scrut)
    - `j` — J(type, lhs, motive, base, rhs, eq)

    ## Elaboration

    - `elaborate : Int → Hoas → Tm` — compile at given depth
    - `elab : Hoas → Tm` — compile from depth 0

    ## Convenience

    - `checkHoas : Hoas → Hoas → Tm|Error` — elaborate type+term, type-check
    - `inferHoas : Hoas → { term; type; }|Error` — elaborate and infer
    - `natLit : Int → Hoas` — build S^n(zero)

    ## Stack Safety

    Binding chains (pi/lam/sigma/let), succ chains, and cons chains
    are elaborated iteratively via `genericClosure` — safe to 8000+ depth.
  '';
  value = {
    # Types
    inherit nat bool unit void string int_ float_ attrs path function_ any listOf sum eq u
      record maybe variant;
    # Binding
    inherit forall sigma lam let_;
    # Terms
    inherit zero succ true_ false_ tt nil cons pair inl inr refl
      stringLit intLit floatLit attrsLit pathLit fnLit anyLit
      opaqueLam strEq absurd ann app fst_ snd_;
    # Eliminators
    inherit ind boolElim listElim sumElim j;
    # Descriptions — types, constructors, eliminators
    inherit desc mu descRet descArg descRec descPi descCon descInd descElim;
    # Description-level helpers and prelude descriptions
    inherit interpHoas allHoas natDesc listDesc sumDesc natDescTm;
    # Datatype macro
    inherit field fieldD recField piField piFieldD con datatype datatypeP;
    # Elaboration
    inherit elaborate elab;
    # Convenience
    inherit checkHoas inferHoas natLit;
  };
  tests = {
    # ===== Combinator tests (elaborate produces correct Tm) =====

    # -- Type combinators --
    "elab-nat" = { expr = (elab nat).tag; expected = "mu"; };
    "elab-bool" = { expr = (elab bool).tag; expected = "bool"; };
    "elab-unit" = { expr = (elab unit).tag; expected = "unit"; };
    "elab-void" = { expr = (elab void).tag; expected = "void"; };
    "elab-U0" = { expr = (elab (u 0)).tag; expected = "U"; };
    "elab-U0-level" = { expr = (elab (u 0)).level; expected = 0; };
    "elab-list" = { expr = (elab (listOf nat)).tag; expected = "app"; };
    "elab-sum" = { expr = (elab (sum nat bool)).tag; expected = "app"; };
    "elab-eq" = { expr = (elab (eq nat zero zero)).tag; expected = "eq"; };

    # -- Binding type: forall --
    "elab-forall-tag" = {
      expr = (elab (forall "x" nat (_: nat))).tag;
      expected = "pi";
    };
    "elab-forall-domain" = {
      expr = (elab (forall "x" nat (_: nat))).domain.tag;
      expected = "mu";
    };
    "elab-forall-body-var" = {
      # forall "x" Nat (x: x) — body is Var(0)
      expr = (elab (forall "x" nat (x: x))).codomain.tag;
      expected = "var";
    };
    "elab-forall-body-idx" = {
      expr = (elab (forall "x" nat (x: x))).codomain.idx;
      expected = 0;
    };

    # -- Binding type: sigma --
    "elab-sigma-tag" = {
      expr = (elab (sigma "x" nat (_: bool))).tag;
      expected = "sigma";
    };

    # -- Binding terms: lam --
    "elab-lam-tag" = {
      expr = (elab (lam "x" nat (x: x))).tag;
      expected = "lam";
    };
    "elab-lam-body-idx" = {
      expr = (elab (lam "x" nat (x: x))).body.idx;
      expected = 0;
    };

    # -- let_ --
    "elab-let-tag" = {
      expr = (elab (let_ "x" nat zero (x: x))).tag;
      expected = "let";
    };

    # -- Non-binding terms --
    "elab-zero" = { expr = (elab zero).tag; expected = "desc-con"; };
    "elab-succ" = { expr = (elab (succ zero)).tag; expected = "desc-con"; };
    "elab-true" = { expr = (elab true_).tag; expected = "true"; };
    "elab-false" = { expr = (elab false_).tag; expected = "false"; };
    "elab-tt" = { expr = (elab tt).tag; expected = "tt"; };
    # nil elaborates to desc-con with inner tag "true" selecting the nil-constructor
    # branch; cons elaborates to desc-con with inner tag "false".
    "elab-nil" = {
      expr = let t = elab (nil nat); in "${t.tag}/${t.d.fst.tag}";
      expected = "desc-con/true";
    };
    "elab-cons" = {
      expr = let t = elab (cons nat zero (nil nat)); in "${t.tag}/${t.d.fst.tag}";
      expected = "desc-con/false";
    };
    "elab-pair" = { expr = (elab (pair zero true_)).tag; expected = "pair"; };
    # inl/inr elaborate to desc-con with inner tag "true"/"false" selecting
    # the inl/inr constructor branch of sumDesc.
    "elab-inl" = {
      expr = let t = elab (inl nat bool zero); in "${t.tag}/${t.d.fst.tag}";
      expected = "desc-con/true";
    };
    "elab-inr" = {
      expr = let t = elab (inr nat bool true_); in "${t.tag}/${t.d.fst.tag}";
      expected = "desc-con/false";
    };
    "elab-refl" = { expr = (elab refl).tag; expected = "refl"; };
    "elab-ann" = { expr = (elab (ann zero nat)).tag; expected = "ann"; };
    "elab-app" = { expr = (elab (app (lam "x" nat (x: x)) zero)).tag; expected = "app"; };
    "elab-absurd" = { expr = (elab (absurd nat (lam "x" void (x: x)))).tag; expected = "absurd"; };
    "elab-fst" = { expr = (elab (fst_ (pair zero true_))).tag; expected = "fst"; };
    "elab-snd" = { expr = (elab (snd_ (pair zero true_))).tag; expected = "snd"; };

    # -- Error path: non-serializable value doesn't crash toJSON --
    "elab-error-non-serializable" = {
      expr = (builtins.tryEval (elab (x: x))).success;
      expected = false;
    };

    # -- Sentinel hardening: {_hoas=true} is NOT a marker --
    "elab-reject-fake-marker" = {
      expr = (builtins.tryEval (elab { _hoas = true; level = 0; })).success;
      expected = false;
    };

    # -- Eliminators --
    # nat-elim surface combinator elaborates to nested let-bindings around a
    # desc-ind: `let P = motive in let B = base in let S = step in desc-ind …`.
    # The let-wrapping makes motive/step/base inferable (VAR via lookupType)
    # so the descInd check rule can type the body; see hoas.nix nat-elim adapter.
    "elab-nat-elim" = {
      expr = (elab (ind (lam "n" nat (_: nat)) zero
        (lam "k" nat (_: lam "ih" nat (ih: succ ih)))
        zero)).tag;
      expected = "let";
    };
    "elab-bool-elim" = {
      expr = (elab (boolElim (lam "b" bool (_: nat)) zero (succ zero) true_)).tag;
      expected = "bool-elim";
    };

    # -- Nested binding: de Bruijn indices correct --
    "elab-nested-var-outer" = {
      # forall "A" U0 (A: forall "x" A (_: A))
      # Inner body uses A which is at depth 0 when bound, now at depth 2
      # So idx = 2 - 0 - 1 = 1
      expr = (elab (forall "A" (u 0) (a:
        forall "x" a (_: a)))).codomain.codomain.idx;
      expected = 1;
    };
    "elab-nested-var-inner" = {
      # forall "A" U0 (A: forall "x" A (x: x))
      # x is at depth 1, used at depth 2 → idx = 2 - 1 - 1 = 0
      expr = (elab (forall "A" (u 0) (_:
        forall "x" nat (x: x)))).codomain.codomain.idx;
      expected = 0;
    };

    # -- natLit helper --
    "natLit-0" = { expr = (elab (natLit 0)).tag; expected = "desc-con"; };
    "natLit-3" = { expr = (elab (natLit 3)).tag; expected = "desc-con"; };

    # -- Stack safety: deep succ chain elaboration --
    "elab-succ-5000" = {
      expr = let tm = elab (natLit 5000); in tm.tag;
      expected = "desc-con";
    };

    # -- Stack safety: deep nested Pi chain elaboration --
    "elab-pi-8000" = {
      expr = let
        deepPi = builtins.foldl' (acc: _:
          forall "_" nat (_: acc)
        ) nat (builtins.genList (x: x) 8000);
        tm = elab deepPi;
      in tm.tag;
      expected = "pi";
    };

    # -- Stack safety: deep nested Lam chain elaboration --
    "elab-lam-8000" = {
      expr = let
        deepLam = builtins.foldl' (acc: _:
          lam "_" nat (_: acc)
        ) zero (builtins.genList (x: x) 8000);
        tm = elab deepLam;
      in tm.tag;
      expected = "lam";
    };

    # -- Stack safety: deep cons chain elaboration --
    "elab-cons-5000" = {
      expr = let
        bigList = builtins.foldl' (acc: _:
          cons nat zero acc
        ) (nil nat) (builtins.genList (x: x) 5000);
        tm = elab bigList;
      in tm.tag;
      expected = "desc-con";
    };

    # ===== Kernel integration: type-check elaborated terms =====

    # Zero : Nat  (elaborates to desc-con natDesc (pair true tt))
    "check-zero" = {
      expr = let t = checkHoas nat zero; in "${t.tag}/${t.d.fst.tag}";
      expected = "desc-con/true";
    };

    # S(S(0)) : Nat  (outer layer is desc-con with tag=false; inner is s(0))
    "check-succ2" = {
      expr = let t = checkHoas nat (succ (succ zero)); in "${t.tag}/${t.d.fst.tag}";
      expected = "desc-con/false";
    };

    # True : Bool
    "check-true" = {
      expr = (checkHoas bool true_).tag;
      expected = "true";
    };

    # () : Unit
    "check-tt" = {
      expr = (checkHoas unit tt).tag;
      expected = "tt";
    };

    # nil Nat : List Nat  (desc-con (listDesc nat) (pair true tt))
    "check-nil" = {
      expr = let t = checkHoas (listOf nat) (nil nat); in "${t.tag}/${t.d.fst.tag}";
      expected = "desc-con/true";
    };

    # cons Nat 0 (nil Nat) : List Nat  (desc-con (listDesc nat) (pair false ...))
    "check-cons" = {
      expr = let t = checkHoas (listOf nat) (cons nat zero (nil nat)); in "${t.tag}/${t.d.fst.tag}";
      expected = "desc-con/false";
    };

    # inl Nat Bool 0 : Sum Nat Bool  (desc-con (sumDesc nat bool) (pair true ...))
    "check-inl" = {
      expr = let t = checkHoas (sum nat bool) (inl nat bool zero); in
        "${t.tag}/${t.d.fst.tag}";
      expected = "desc-con/true";
    };

    # pair(0, true) : Σ(x:Nat).Bool
    "check-pair" = {
      expr = (checkHoas (sigma "x" nat (_: bool)) (pair zero true_)).tag;
      expected = "pair";
    };

    # Refl : Eq(Nat, 0, 0)
    "check-refl" = {
      expr = (checkHoas (eq nat zero zero) refl).tag;
      expected = "refl";
    };

    # ===== Theorem tests =====

    # Polymorphic identity: λ(A:U₀). λ(x:A). x  :  Π(A:U₀). A → A
    "theorem-poly-id" = {
      expr = let
        ty = forall "A" (u 0) (a: forall "x" a (_: a));
        tm = lam "A" (u 0) (a: lam "x" a (x: x));
      in (checkHoas ty tm).tag;
      expected = "lam";
    };

    # 0 + 0 = 0 by computation: NatElim(_, 0, λk.λih.S(ih), 0) = 0, Refl
    "theorem-0-plus-0" = {
      expr = let
        addZero = ind (lam "n" nat (_: nat)) zero
          (lam "k" nat (_: lam "ih" nat (ih: succ ih))) zero;
        eqTy = eq nat addZero zero;
      in (checkHoas eqTy refl).tag;
      expected = "refl";
    };

    # n + 0 = n by induction:
    #   motive: λn. Eq(Nat, add(n,0), n)
    #   base: Refl  (add(0,0) = 0 by computation)
    #   step: λk. λih. cong succ ih  (where add(S(k),0) = S(add(k,0)))
    # cong f p = J(A, a, λb.λ_. Eq(B, f(a), f(b)), refl, b, p)
    # For our purposes, since add(S(k), 0) computes to S(add(k, 0)) by the
    # step of NatElim, and ih : add(k,0) = k, we need:
    #   S(add(k,0)) = S(k), which follows from congruence on ih.
    #
    # Actually, since add is defined by NatElim and NatElim on S(k) computes
    # the step, we get: add(S(k), 0) = S(add(k, 0)). Combined with ih : add(k,0) = k
    # we need S(add(k,0)) = S(k). The J eliminator can produce this.
    #
    # However, encoding cong via J in HOAS is complex. Let's use a simpler approach:
    # The checker normalizes both sides before comparing, so if add(n,0) reduces to n
    # for all n, we just need Refl. But NatElim doesn't reduce symbolically.
    # Instead, test a concrete case: n=3.
    "theorem-3-plus-0-eq-3" = {
      expr = let
        three = succ (succ (succ zero));
        add_n_0 = ind (lam "n" nat (_: nat)) zero
          (lam "k" nat (_: lam "ih" nat (ih: succ ih))) three;
        eqTy = eq nat add_n_0 three;
      in (checkHoas eqTy refl).tag;
      expected = "refl";
    };

    # Dependent pair: (0, Refl) : Σ(x:Nat). Eq(Nat, x, 0)
    "theorem-dep-pair" = {
      expr = let
        ty = sigma "x" nat (x: eq nat x zero);
        tm = pair zero refl;
      in (checkHoas ty tm).tag;
      expected = "pair";
    };

    # BoolElim type-checks: if true then 0 else 1 : Nat
    # `nat` is `mu natDesc`, so the inferred value tag is "VMu".
    "theorem-bool-elim" = {
      expr = let
        tm = boolElim (lam "b" bool (_: nat)) zero (succ zero) true_;
      in (inferHoas (ann tm nat)).type.tag;
      expected = "VMu";
    };

    # ===== Description-based prelude integration =====
    # End-to-end semantic checks that the μ-description rebind of Nat/List/Sum
    # computes the same values as the primitive representations under conv.

    # add(2, 3) = 5 on description-based Nat — exercises the rebound `ind`
    # adapter (let-bound P/B/S around descInd) plus Σ-η + ⊤-η in the step.
    "integration-desc-nat-add-2-3" = {
      expr = let
        two   = succ (succ zero);
        three = succ (succ (succ zero));
        five  = succ (succ (succ (succ (succ zero))));
        addTm = lam "m" nat (m: lam "n" nat (n:
                  ind (lam "_" nat (_: nat))
                      n
                      (lam "k" nat (_: lam "ih" nat (ih: succ ih)))
                      m));
        eqTy = eq nat (app (app addTm two) three) five;
      in (checkHoas eqTy refl).tag;
      expected = "refl";
    };

    # length [0, 0, 0] = 3 on description-based List — exercises the rebound
    # `listElim` adapter (let-bound P/N/C around descInd) on the cons chain.
    "integration-desc-list-length-3" = {
      expr = let
        zeros = cons nat zero (cons nat zero (cons nat zero (nil nat)));
        three = succ (succ (succ zero));
        lenTm = listElim nat (lam "_" (listOf nat) (_: nat))
                  zero
                  (lam "h" nat (_:
                   lam "t" (listOf nat) (_:
                   lam "ih" nat (ih: succ ih))))
                  zeros;
        eqTy = eq nat lenTm three;
      in (checkHoas eqTy refl).tag;
      expected = "refl";
    };

    # sumElim id id (inl Nat Nat 7) = 7 on description-based Sum — exercises
    # the rebound `sumElim` adapter (let-bound P/L/R around descInd) with a
    # constant motive Nat, where the trivial rih : ⊤ is discharged in both arms.
    "integration-desc-sum-elim-inl" = {
      expr = let
        seven = succ (succ (succ (succ (succ (succ (succ zero))))));
        scrut = inl nat nat seven;
        motiveNat = lam "_" (sum nat nat) (_: nat);
        idNat = lam "n" nat (n: n);
        result = sumElim nat nat motiveNat idNat idNat scrut;
        eqTy = eq nat result seven;
      in (checkHoas eqTy refl).tag;
      expected = "refl";
    };

    # sumElim id id (inr Nat Nat 4) = 4 — mirror test exercises the right arm.
    "integration-desc-sum-elim-inr" = {
      expr = let
        four = succ (succ (succ (succ zero)));
        scrut = inr nat nat four;
        motiveNat = lam "_" (sum nat nat) (_: nat);
        idNat = lam "n" nat (n: n);
        result = sumElim nat nat motiveNat idNat idNat scrut;
        eqTy = eq nat result four;
      in (checkHoas eqTy refl).tag;
      expected = "refl";
    };

    # W-type wellformedness: μ(wDesc Bool (b: if b then Unit else Void)) : U(0).
    # `wDesc A B = descArg A (a: descPi (B a) descRet)` — B is a Nix meta-level
    # function (A → U at the HOAS surface), applied at elaboration time. This
    # exercises the descPi case in the kernel's Desc check rule.
    "integration-desc-wtype-wellformed" = {
      expr = let
        wDesc = A: B: descArg A (a: descPi (B a) descRet);
        wBool = wDesc bool (a:
                  boolElim (lam "_" bool (_: u 0)) unit void a);
      in (checkHoas (u 0) (mu wBool)).tag;
      expected = "mu";
    };

    # ===== Roundtrip: elaborate → eval → quote → eval → quote =====

    "roundtrip-lam-id" = {
      expr = let
        tm = elab (lam "x" nat (x: x));
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };

    "roundtrip-forall" = {
      expr = let
        tm = elab (forall "A" (u 0) (a: forall "x" a (_: a)));
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };

    "roundtrip-sigma" = {
      expr = let
        tm = elab (sigma "x" nat (_: bool));
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };

    "roundtrip-nat-elim" = {
      expr = let
        tm = elab (ind (lam "n" nat (_: nat)) zero
          (lam "k" nat (_: lam "ih" nat (ih: succ ih)))
          (succ (succ zero)));
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };

    "roundtrip-natLit-5" = {
      expr = let tm = elab (natLit 5);
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };

    # Stress test — stack safety (B4)
    "natLit-5000" = {
      expr = (elab (natLit 5000)).tag;
      expected = "desc-con";
    };

    # ===== Primitive type elaboration =====

    "elab-string" = { expr = (elab string).tag; expected = "string"; };
    "elab-int" = { expr = (elab int_).tag; expected = "int"; };
    "elab-float" = { expr = (elab float_).tag; expected = "float"; };
    "elab-attrs" = { expr = (elab attrs).tag; expected = "attrs"; };
    "elab-path" = { expr = (elab path).tag; expected = "path"; };
    "elab-function" = { expr = (elab function_).tag; expected = "function"; };
    "elab-any" = { expr = (elab any).tag; expected = "any"; };

    # ===== Primitive literal elaboration =====

    "elab-string-lit" = { expr = (elab (stringLit "hi")).tag; expected = "string-lit"; };
    "elab-string-lit-value" = { expr = (elab (stringLit "hi")).value; expected = "hi"; };
    "elab-int-lit" = { expr = (elab (intLit 42)).tag; expected = "int-lit"; };
    "elab-int-lit-value" = { expr = (elab (intLit 42)).value; expected = 42; };
    "elab-float-lit" = { expr = (elab (floatLit 3.14)).tag; expected = "float-lit"; };
    "elab-float-lit-value" = { expr = (elab (floatLit 3.14)).value; expected = 3.14; };
    "elab-attrs-lit" = { expr = (elab attrsLit).tag; expected = "attrs-lit"; };
    "elab-path-lit" = { expr = (elab pathLit).tag; expected = "path-lit"; };
    "elab-fn-lit" = { expr = (elab fnLit).tag; expected = "fn-lit"; };
    "elab-any-lit" = { expr = (elab anyLit).tag; expected = "any-lit"; };

    # ===== Primitive kernel integration =====

    "check-string-lit" = {
      expr = (checkHoas string (stringLit "hello")).tag;
      expected = "string-lit";
    };
    "check-int-lit" = {
      expr = (checkHoas int_ (intLit 7)).tag;
      expected = "int-lit";
    };
    "check-float-lit" = {
      expr = (checkHoas float_ (floatLit 2.5)).tag;
      expected = "float-lit";
    };
    "check-attrs-lit" = {
      expr = (checkHoas attrs attrsLit).tag;
      expected = "attrs-lit";
    };
    "check-path-lit" = {
      expr = (checkHoas path pathLit).tag;
      expected = "path-lit";
    };
    "check-fn-lit" = {
      expr = (checkHoas function_ fnLit).tag;
      expected = "fn-lit";
    };
    "check-any-lit" = {
      expr = (checkHoas any anyLit).tag;
      expected = "any-lit";
    };

    # ===== Opaque lambda: trust boundary for Pi =====

    "elab-opaque-lam" = {
      expr = (elab (opaqueLam (x: x) (forall "x" nat (_: nat)))).tag;
      expected = "opaque-lam";
    };

    # Opaque lambda checks at matching Pi type
    "opaque-lam-checks-at-pi" = {
      expr = let
        piTy = forall "x" nat (_: nat);
      in (checkHoas piTy (opaqueLam (x: x) piTy)).tag;
      expected = "opaque-lam";
    };

    # Opaque lambda rejects domain mismatch
    "opaque-lam-rejects-domain-mismatch" = {
      expr = let
        targetPi = forall "x" nat (_: nat);
        annotPi = forall "x" bool (_: nat);
      in (checkHoas targetPi (opaqueLam (x: x) annotPi)) ? error;
      expected = true;
    };

    # Opaque lambda rejects non-Pi target type
    "opaque-lam-rejects-non-pi" = {
      expr = (checkHoas nat (opaqueLam (x: x) (forall "x" nat (_: nat)))) ? error;
      expected = true;
    };

    # Opaque lambda infers Pi type from annotation
    "opaque-lam-infers-pi-type" = {
      expr = let
        piTy = forall "x" nat (_: nat);
        result = inferHoas (ann (opaqueLam (x: x) piTy) piTy);
      in result.type.tag;
      expected = "VPi";
    };

    # Opaque lambda quote roundtrip: eval → quote → eval = same structure
    "opaque-lam-quote-roundtrip" = {
      expr = let
        H = { inherit nat forall opaqueLam elab; };
        piTy = H.forall "x" H.nat (_: H.nat);
        tm = H.elab (H.opaqueLam (x: x) piTy);
        Q' = fx.tc.quote;
      in Q'.nf [] (Q'.nf [] tm) == Q'.nf [] tm;
      expected = true;
    };

    # Conv: same Nix function → conv-equal
    "opaque-lam-conv-reflexive" = {
      expr = let
        f = x: x;
        piTy = forall "x" nat (_: nat);
        tm1 = elab (opaqueLam f piTy);
        tm2 = elab (opaqueLam f piTy);
        E' = fx.tc.eval;
        C' = fx.tc.conv;
        v1 = E'.eval [] tm1;
        v2 = E'.eval [] tm2;
      in C'.conv 0 v1 v2;
      expected = true;
    };

    # Conv: different Nix functions → not conv-equal
    "opaque-lam-conv-distinct" = {
      expr = let
        f = x: x;
        g = x: succ x;
        piTy = forall "x" nat (_: nat);
        tm1 = elab (opaqueLam f piTy);
        tm2 = elab (opaqueLam g piTy);
        E' = fx.tc.eval;
        C' = fx.tc.conv;
        v1 = E'.eval [] tm1;
        v2 = E'.eval [] tm2;
      in C'.conv 0 v1 v2;
      expected = false;
    };

    # ----- Description-level acceptance tests -----

    # Acceptance A1: direct descElim on descRet infers motive(descRet).
    # With motive λ_:Desc. U→U, the result type is a VPi.
    "desc-elim-direct-infer" = {
      expr = let
        motive = lam "_" desc (_: forall "_" (u 0) (_: u 0));
        onRet  = lam "X" (u 0) (_: unit);
        onArg  = lam "S" (u 0) (S:
                 lam "T" (forall "_" S (_: desc)) (_:
                 lam "ih" (forall "s" S (_: forall "_" (u 0) (_: u 0))) (ih:
                 lam "X" (u 0) (X':
                   sigma "s" S (s: app (app ih s) X')))));
        onRec  = lam "D" desc (_:
                 lam "ih" (forall "_" (u 0) (_: u 0)) (ih:
                 lam "X" (u 0) (X':
                   sigma "_" X' (_: app ih X'))));
        onPi   = lam "S" (u 0) (S:
                 lam "D" desc (_:
                 lam "ih" (forall "_" (u 0) (_: u 0)) (ih:
                 lam "X" (u 0) (X':
                   sigma "_" (forall "_" S (_: X')) (_: app ih X')))));
        tm = descElim motive onRet onArg onRec onPi descRet;
      in (inferHoas tm).type.tag;
      expected = "VPi";
    };

    # interpHoas ≡ interpF — compare nf of HOAS-elaborated term against the
    # quoted result of eval.nix's interp at the same D, X.

    # ⟦ret⟧(X) = ⊤, so interpHoas descRet nat ≡ Unit
    "interpHoas-matches-interpF-ret" = {
      expr = let
        lhsNf = Q.nf [] (elab (interpHoas descRet nat));
        dVal = E.eval [] (elab descRet);
        xVal = E.eval [] (elab nat);
        rhsNf = Q.quote 0 (E.interp dVal xVal);
      in lhsNf == rhsNf;
      expected = true;
    };

    # ⟦rec ret⟧(X) = X × ⊤
    "interpHoas-matches-interpF-rec-ret" = {
      expr = let
        D = descRec descRet;
        X = bool;
        lhsNf = Q.nf [] (elab (interpHoas D X));
        rhsNf = Q.quote 0 (E.interp (E.eval [] (elab D)) (E.eval [] (elab X)));
      in lhsNf == rhsNf;
      expected = true;
    };

    # ⟦arg bool (b: ret)⟧(X) = Σ(b:Bool). ⊤
    "interpHoas-matches-interpF-arg-bool" = {
      expr = let
        D = descArg bool (_: descRet);
        X = nat;
        lhsNf = Q.nf [] (elab (interpHoas D X));
        rhsNf = Q.quote 0 (E.interp (E.eval [] (elab D)) (E.eval [] (elab X)));
      in lhsNf == rhsNf;
      expected = true;
    };

    # ⟦pi bool ret⟧(X) = (Bool→X) × ⊤
    "interpHoas-matches-interpF-pi-bool" = {
      expr = let
        D = descPi bool descRet;
        X = nat;
        lhsNf = Q.nf [] (elab (interpHoas D X));
        rhsNf = Q.quote 0 (E.interp (E.eval [] (elab D)) (E.eval [] (elab X)));
      in lhsNf == rhsNf;
      expected = true;
    };

    # ⟦natDesc⟧(X) — exercises the boolElim inside the arg body
    "interpHoas-matches-interpF-natDesc" = {
      expr = let
        lhsNf = Q.nf [] (elab (interpHoas natDesc bool));
        rhsNf = Q.quote 0 (E.interp
          (E.eval [] (elab natDesc))
          (E.eval [] (elab bool)));
      in lhsNf == rhsNf;
      expected = true;
    };

    # allHoas ≡ allTy — also validates the motive's d-annotation fix:
    # without `d : interpHoas D (mu Douter)` in the motive, desc-elim's
    # paTy rule would reject onArg's `fst_ d` / `snd_ d` inside the body.

    # All natDesc descRet P tt = ⊤ (no recursive arg)
    "allHoas-matches-allTy-ret" = {
      expr = let
        pHoas = lam "_" (mu natDesc) (_: u 0);
        lhsNf = Q.nf [] (elab (allHoas natDesc descRet pHoas tt));
        douter = E.eval [] (elab natDesc);
        dsub = E.eval [] (elab descRet);
        pVal = E.eval [] (elab pHoas);
        dVal = E.eval [] (elab tt);
        rhsNf = Q.quote 0 (E.allTy douter dsub pVal dVal);
      in lhsNf == rhsNf;
      expected = true;
    };

    # All natDesc (rec ret) P (zero, tt) exercises onRec
    "allHoas-matches-allTy-rec-ret" = {
      expr = let
        pHoas = lam "_" (mu natDesc) (_: u 0);
        zeroH = descCon natDesc (pair true_ tt);
        dH = pair zeroH tt;
        D = descRec descRet;
        lhsNf = Q.nf [] (elab (allHoas natDesc D pHoas dH));
        douter = E.eval [] (elab natDesc);
        dsub = E.eval [] (elab D);
        pVal = E.eval [] (elab pHoas);
        dVal = E.eval [] (elab dH);
        rhsNf = Q.quote 0 (E.allTy douter dsub pVal dVal);
      in lhsNf == rhsNf;
      expected = true;
    };

    # All natDesc (arg bool (_: ret)) P (true_, tt) exercises onArg —
    # the case whose type-checking motivates the motive fix.
    "allHoas-matches-allTy-arg-bool-ret" = {
      expr = let
        pHoas = lam "_" (mu natDesc) (_: u 0);
        D = descArg bool (_: descRet);
        dH = pair true_ tt;
        lhsNf = Q.nf [] (elab (allHoas natDesc D pHoas dH));
        douter = E.eval [] (elab natDesc);
        dsub = E.eval [] (elab D);
        pVal = E.eval [] (elab pHoas);
        dVal = E.eval [] (elab dH);
        rhsNf = Q.quote 0 (E.allTy douter dsub pVal dVal);
      in lhsNf == rhsNf;
      expected = true;
    };

    # ===== Datatype macro =====
    # UnitDT: the n=1 degenerate case — singleton constructor with no
    # fields. D = descRet, T = μ descRet, tt = descCon D tt, elim P step
    # scrut reduces to step. Exercises the leaf dispatchStep with no
    # field or IH projection, and the n=1 no-tag encoding.

    "datatype-unit-spec-name" = {
      expr = (datatype "Unit" [ (con "tt" []) ]).name;
      expected = "Unit";
    };
    "datatype-unit-spec-meta" = {
      expr = (datatype "Unit" [ (con "tt" []) ])._dtypeMeta;
      expected = {
        name = "Unit";
        cons = [{ name = "tt"; fields = []; }];
      };
    };
    "datatype-unit-D-elab" = {
      expr = (elab (datatype "Unit" [ (con "tt" []) ]).D).tag;
      expected = "desc-ret";
    };
    "datatype-unit-T-elab" = {
      expr = (elab (datatype "Unit" [ (con "tt" []) ]).T).tag;
      expected = "mu";
    };
    "datatype-unit-tt-elab" = {
      expr = (elab (datatype "Unit" [ (con "tt" []) ]).tt).tag;
      expected = "desc-con";
    };
    "datatype-unit-T-check-U0" = {
      expr = (checkHoas (u 0) (datatype "Unit" [ (con "tt" []) ]).T).tag;
      expected = "mu";
    };
    "datatype-unit-tt-check-T" = {
      expr = let U = datatype "Unit" [ (con "tt" []) ];
             in (checkHoas U.T U.tt).tag;
      expected = "desc-con";
    };
    "datatype-unit-elim-reduces-to-step" = {
      # elim (λ_:T. ⊤) tt U.tt  ≡nf≡  tt
      # The motive is constantly ⊤, the step is `tt : ⊤`, the scrutinee
      # is U.tt. descInd on the single-constructor μ descRet reduces
      # straight to the step (no field projection, no IH).
      expr = let
        U = datatype "Unit" [ (con "tt" []) ];
        applied = app (app (app U.elim
          (lam "x" U.T (_: unit)))
          tt)
          U.tt;
      in Q.nf [] (elab applied) == Q.nf [] (elab tt);
      expected = true;
    };
    # The macro elim must be INFERABLE as a closed term — bare lam
    # cascades are checkable-only in the bidirectional kernel, so the
    # macro wraps the elim in `ann <body> <full-Π-type>`. This test fires
    # an applied elim through `checkHoas` to prove the chain of `app`s
    # type-checks; nf-equivalence (datatype-unit-elim-reduces-to-step)
    # bypasses checking and would silently mask a non-inferable elim.
    "datatype-unit-elim-checks" = {
      expr = let
        U = datatype "Unit" [ (con "tt" []) ];
        applied = app (app (app U.elim
          (lam "x" U.T (_: unit)))
          tt)
          U.tt;
      in (checkHoas unit applied).tag;
      expected = "app";
    };
    # Direct inference of the closed elim: confirms `ann` pins a Π type
    # the kernel can recover without reducing the body.
    "datatype-unit-elim-infers-pi" = {
      expr = let U = datatype "Unit" [ (con "tt" []) ];
             in (inferHoas U.elim).type.tag;
      expected = "VPi";
    };
    "datatype-rejects-n0" = {
      expr = (builtins.tryEval (datatype "Empty" [])).success;
      expected = false;
    };
    "datatype-rejects-duplicate-cons" = {
      expr = (builtins.tryEval
               (datatype "Dup" [ (con "a" []) (con "a" []) ])).success;
      expected = false;
    };

    # BoolDT: n=2 with both arms zero-field. Exercises:
    #   - spineDesc n>=2 (right-associated Bool tag spine).
    #   - encodeTag n>=2 (true_/false_ tag prefixes).
    #   - dispatchStep n>=2 branch case with leaf onTrue / onFalse,
    #     ctx threaded with `pair false_` for the second arm.
    "datatype-bool-spec-name" = {
      expr = (datatype "Bool" [ (con "true" []) (con "false" []) ]).name;
      expected = "Bool";
    };
    "datatype-bool-spec-meta" = {
      expr = (datatype "Bool" [ (con "true" []) (con "false" []) ])._dtypeMeta;
      expected = {
        name = "Bool";
        cons = [
          { name = "true";  fields = []; }
          { name = "false"; fields = []; }
        ];
      };
    };
    # D = descArg bool (b: boolElim _ descRet descRet b) — same Bool-fold
    # as natDesc, with both arms degenerate (descRet) instead of asymmetric
    # (descRet vs descRec descRet).
    "datatype-bool-D-elab" = {
      expr = (elab (datatype "Bool" [ (con "true" []) (con "false" []) ]).D).tag;
      expected = "desc-arg";
    };
    "datatype-bool-T-elab" = {
      expr = (elab (datatype "Bool" [ (con "true" []) (con "false" []) ]).T).tag;
      expected = "mu";
    };
    "datatype-bool-true-elab" = {
      expr = (elab (datatype "Bool" [ (con "true" []) (con "false" []) ]).true).tag;
      expected = "desc-con";
    };
    "datatype-bool-false-elab" = {
      expr = (elab (datatype "Bool" [ (con "true" []) (con "false" []) ]).false).tag;
      expected = "desc-con";
    };
    # Macro D matches the canonical bool-fold structure: descArg over the
    # `bool` kernel primitive, with a boolElim body selecting descRet for
    # both arms. Compared against a hand-written equivalent via nf to
    # absorb α-renaming.
    "datatype-bool-D-matches-handwritten" = {
      expr = let
        macroD = (datatype "Bool" [ (con "true" []) (con "false" []) ]).D;
        handD = descArg bool (b:
          boolElim (lam "_" bool (_: desc)) descRet descRet b);
      in Q.nf [] (elab macroD) == Q.nf [] (elab handD);
      expected = true;
    };
    "datatype-bool-true-payload-shape" = {
      # encodeTag 0 2 tt = pair true_ tt — verified via nf against a
      # hand-written descCon emission with the same payload.
      expr = let
        B = datatype "Bool" [ (con "true" []) (con "false" []) ];
        handTrue = descCon B.D (pair true_ tt);
      in Q.nf [] (elab B.true) == Q.nf [] (elab handTrue);
      expected = true;
    };
    "datatype-bool-false-payload-shape" = {
      # encodeTag 1 2 tt = pair false_ (encodeTag 0 1 tt) = pair false_ tt
      expr = let
        B = datatype "Bool" [ (con "true" []) (con "false" []) ];
        handFalse = descCon B.D (pair false_ tt);
      in Q.nf [] (elab B.false) == Q.nf [] (elab handFalse);
      expected = true;
    };
    "datatype-bool-T-check-U0" = {
      expr = (checkHoas (u 0) (datatype "Bool" [ (con "true" []) (con "false" []) ]).T).tag;
      expected = "mu";
    };
    "datatype-bool-true-check-T" = {
      expr = let B = datatype "Bool" [ (con "true" []) (con "false" []) ];
             in (checkHoas B.T B.true).tag;
      expected = "desc-con";
    };
    "datatype-bool-false-check-T" = {
      expr = let B = datatype "Bool" [ (con "true" []) (con "false" []) ];
             in (checkHoas B.T B.false).tag;
      expected = "desc-con";
    };
    # Closed elim is inferable as a Π type via the ann wrapper.
    "datatype-bool-elim-infers-pi" = {
      expr = let B = datatype "Bool" [ (con "true" []) (con "false" []) ];
             in (inferHoas B.elim).type.tag;
      expected = "VPi";
    };
    # Reduction on the true scrutinee selects step_true.
    # Motive: const ⊤. step_true = tt : ⊤. step_false = tt : ⊤.
    # elim P step_true step_false B.true ≡nf≡ tt.
    "datatype-bool-elim-reduces-true" = {
      expr = let
        B = datatype "Bool" [ (con "true" []) (con "false" []) ];
        applied = app (app (app (app B.elim
          (lam "_" B.T (_: unit)))
          tt)  # step_true
          tt)  # step_false
          B.true;
      in Q.nf [] (elab applied) == Q.nf [] (elab tt);
      expected = true;
    };
    # Reduction on the false scrutinee selects step_false.
    # Discriminating motive (P b = if b then ⊤ else ⊤ — both arms
    # collapse to ⊤ because we have no second monomorphic ground type
    # in scope at U0 to distinguish them, but the dispatch chain is still
    # exercised structurally and verified by separately checking that
    # the elim chains through a non-collapsing motive in the next test).
    "datatype-bool-elim-reduces-false" = {
      expr = let
        B = datatype "Bool" [ (con "true" []) (con "false" []) ];
        applied = app (app (app (app B.elim
          (lam "_" B.T (_: unit)))
          tt)
          tt)
          B.false;
      in Q.nf [] (elab applied) == Q.nf [] (elab tt);
      expected = true;
    };
    # Distinguishing motive: P b = T (the BoolDT type itself).
    # step_true = B.false, step_false = B.true (negation).
    # elim P (B.false) (B.true) B.true ≡nf≡ B.false.
    # elim P (B.false) (B.true) B.false ≡nf≡ B.true.
    # This proves the boolElim dispatch genuinely picks the correct arm
    # rather than collapsing both to a common normal form.
    "datatype-bool-elim-negates-true" = {
      expr = let
        B = datatype "Bool" [ (con "true" []) (con "false" []) ];
        neg = scrut: app (app (app (app B.elim
          (lam "_" B.T (_: B.T)))
          B.false)
          B.true)
          scrut;
      in Q.nf [] (elab (neg B.true)) == Q.nf [] (elab B.false);
      expected = true;
    };
    "datatype-bool-elim-negates-false" = {
      expr = let
        B = datatype "Bool" [ (con "true" []) (con "false" []) ];
        neg = scrut: app (app (app (app B.elim
          (lam "_" B.T (_: B.T)))
          B.false)
          B.true)
          scrut;
      in Q.nf [] (elab (neg B.false)) == Q.nf [] (elab B.true);
      expected = true;
    };
    # Applied negation chain through checkHoas: proves the entire
    # `app`-cascade is type-checkable (the elim's ann wrapper makes the
    # head of the chain inferable; each step's check rule then validates).
    "datatype-bool-elim-checks-applied" = {
      expr = let
        B = datatype "Bool" [ (con "true" []) (con "false" []) ];
        applied = app (app (app (app B.elim
          (lam "_" B.T (_: B.T)))
          B.false)
          B.true)
          B.true;
      in (checkHoas B.T applied).tag;
      expected = "app";
    };

    # NatDT: n=2 with one fielded constructor (succ takes a recField).
    # Exercises:
    #   - conDesc with recField (descRec extension).
    #   - mkCtor curried lam over fields, ann-wrapped against the
    #     constructor's Π type.
    #   - stepTyOf with fielded cons: Π over the field, then Π over the
    #     IH, terminating in P (succ pred).
    #   - buildStepApply with field projection (fst payload) and IH
    #     projection (fst payloadIH).
    #   - nf-equivalence against the inline natElim adapter (`ind` HOAS
    #     combinator at hoas.nix:362-410). Both eval-discard their type
    #     scaffolding (let_ vs ann) so the descInd reductions agree.
    "datatype-nat-spec-name" = {
      expr = (datatype "Nat" [
        (con "zero" [])
        (con "succ" [ (recField "pred") ])
      ]).name;
      expected = "Nat";
    };
    "datatype-nat-spec-meta" = {
      expr = (datatype "Nat" [
        (con "zero" [])
        (con "succ" [ (recField "pred") ])
      ])._dtypeMeta;
      expected = {
        name = "Nat";
        cons = [
          { name = "zero"; fields = []; }
          { name = "succ"; fields = [ { name = "pred"; kind = "rec"; } ]; }
        ];
      };
    };
    # Macro D matches the prelude `natDesc` exactly via nf.
    "datatype-nat-D-matches-natDesc" = {
      expr = let
        N = datatype "Nat" [
          (con "zero" [])
          (con "succ" [ (recField "pred") ])
        ];
      in Q.nf [] (elab N.D) == Q.nf [] (elab natDesc);
      expected = true;
    };
    "datatype-nat-T-elab" = {
      expr = (elab (datatype "Nat" [
        (con "zero" [])
        (con "succ" [ (recField "pred") ])
      ]).T).tag;
      expected = "mu";
    };
    "datatype-nat-T-check-U0" = {
      expr = let N = datatype "Nat" [
        (con "zero" [])
        (con "succ" [ (recField "pred") ])
      ]; in (checkHoas (u 0) N.T).tag;
      expected = "mu";
    };
    # Constructor zero: descCon D (pair true_ tt) — same payload shape as
    # the prelude `zero` HOAS combinator, just over the macro-built D.
    "datatype-nat-zero-payload" = {
      expr = let
        N = datatype "Nat" [
          (con "zero" [])
          (con "succ" [ (recField "pred") ])
        ];
        handZero = descCon N.D (pair true_ tt);
      in Q.nf [] (elab N.zero) == Q.nf [] (elab handZero);
      expected = true;
    };
    "datatype-nat-zero-checks" = {
      expr = let N = datatype "Nat" [
        (con "zero" [])
        (con "succ" [ (recField "pred") ])
      ]; in (checkHoas N.T N.zero).tag;
      expected = "desc-con";
    };
    # Constructor succ is fielded — the macro emits an ann-wrapped curried
    # lam, so its top-level _htag is "ann" until applied.
    "datatype-nat-succ-elab" = {
      expr = (elab (datatype "Nat" [
        (con "zero" [])
        (con "succ" [ (recField "pred") ])
      ]).succ).tag;
      expected = "ann";
    };
    "datatype-nat-succ-infers-pi" = {
      expr = let N = datatype "Nat" [
        (con "zero" [])
        (con "succ" [ (recField "pred") ])
      ]; in (inferHoas N.succ).type.tag;
      expected = "VPi";
    };
    # Applied succ: descCon D (pair false_ (pair pred tt)). After nf, the
    # ann wrapper and the lam β-reduce away, leaving the descCon term.
    "datatype-nat-succ-applied-payload" = {
      expr = let
        N = datatype "Nat" [
          (con "zero" [])
          (con "succ" [ (recField "pred") ])
        ];
        macroSucc = app N.succ N.zero;
        handSucc = descCon N.D (pair false_ (pair N.zero tt));
      in Q.nf [] (elab macroSucc) == Q.nf [] (elab handSucc);
      expected = true;
    };
    # Saturated macro-ctor application flattens at elab time to a flat
    # `desc-con` Tm (shared-dTm chain of length 1). The kernel checks it
    # against the type and returns the reconstructed desc-con term.
    "datatype-nat-succ-applied-checks" = {
      expr = let N = datatype "Nat" [
        (con "zero" [])
        (con "succ" [ (recField "pred") ])
      ]; in (checkHoas N.T (app N.succ N.zero)).tag;
      expected = "desc-con";
    };
    "datatype-nat-elim-infers-pi" = {
      expr = let N = datatype "Nat" [
        (con "zero" [])
        (con "succ" [ (recField "pred") ])
      ]; in (inferHoas N.elim).type.tag;
      expected = "VPi";
    };

    # nf-equivalence between the macro elim and the inline `ind` adapter
    # for representative (M, B, S, scrut) vectors. Both sides eval-discard
    # their type scaffolding (let_ vs ann), so any divergence after nf is
    # a genuine semantic regression in the macro.
    #
    # Motive M = (λ_:nat. nat). Base B = zero. Step varies per test.
    #
    # Scrutinee 1: zero. The descInd's onTrue branch fires; macro
    # buildStepApply returns step_zero (B), the adapter's onTrue
    # returns base.
    "datatype-nat-elim-nf-gate-zero" = {
      expr = let
        N = datatype "Nat" [
          (con "zero" [])
          (con "succ" [ (recField "pred") ])
        ];
        M = lam "_" nat (_: nat);
        B = zero;
        S = lam "k" nat (k: lam "ih" nat (ih: ih));
        scrut = zero;
        macroApplied = app (app (app (app N.elim M) B) S) scrut;
        adapterApplied = ind M B S scrut;
      in Q.nf [] (elab macroApplied) == Q.nf [] (elab adapterApplied);
      expected = true;
    };
    # Scrutinee 2: succ zero. Both onFalse branches fire; macro projects
    # (fst r, fst rih) and applies step_succ; the adapter emits the same
    # projection chain inline.
    "datatype-nat-elim-nf-gate-one" = {
      expr = let
        N = datatype "Nat" [
          (con "zero" [])
          (con "succ" [ (recField "pred") ])
        ];
        M = lam "_" nat (_: nat);
        B = zero;
        S = lam "k" nat (k: lam "ih" nat (ih: ih));
        scrut = succ zero;
        macroApplied = app (app (app (app N.elim M) B) S) scrut;
        adapterApplied = ind M B S scrut;
      in Q.nf [] (elab macroApplied) == Q.nf [] (elab adapterApplied);
      expected = true;
    };
    # Scrutinee 3: succ (succ zero). Two layers of trampoline; checks the
    # nested descInd reduction agrees.
    "datatype-nat-elim-nf-gate-two" = {
      expr = let
        N = datatype "Nat" [
          (con "zero" [])
          (con "succ" [ (recField "pred") ])
        ];
        M = lam "_" nat (_: nat);
        B = zero;
        S = lam "k" nat (k: lam "ih" nat (ih: succ ih));
        scrut = succ (succ zero);
        macroApplied = app (app (app (app N.elim M) B) S) scrut;
        adapterApplied = ind M B S scrut;
      in Q.nf [] (elab macroApplied) == Q.nf [] (elab adapterApplied);
      expected = true;
    };
    # Scrutinee 4: a fresh-variable neutral scrutinee. This is the
    # critical case — neutral scrutinees do NOT reduce, so both terms
    # must produce the SAME stuck normal form (descInd D motive stepF
    # neutral) modulo α. Distinguishes "macro and adapter happen to agree
    # on closed scrutinees" from "macro and adapter agree as terms".
    "datatype-nat-elim-nf-gate-neutral" = {
      expr = let
        N = datatype "Nat" [
          (con "zero" [])
          (con "succ" [ (recField "pred") ])
        ];
        M = lam "_" nat (_: nat);
        B = zero;
        S = lam "k" nat (k: lam "ih" nat (ih: succ ih));
        # Fresh-variable neutral: the elim is wrapped in an outer lam
        # that binds `n : nat`, then applied to that bound variable. nf
        # cannot reduce it since `n` is neutral.
        macroAtN = lam "n" nat (n:
          app (app (app (app N.elim M) B) S) n);
        adapterAtN = lam "n" nat (n: ind M B S n);
      in Q.nf [] (elab macroAtN) == Q.nf [] (elab adapterAtN);
      expected = true;
    };

    # End-to-end semantic test: addition on macro-Nat reduces correctly.
    # add(2, 3) = 5 via the macro elim and macro constructors, exercising
    # the IH projection through actual recursion rather than just nf
    # comparison against the inline adapter.
    "datatype-nat-elim-add-2-3" = {
      expr = let
        N = datatype "Nat" [
          (con "zero" [])
          (con "succ" [ (recField "pred") ])
        ];
        # add m n = elim (λ_. nat) n (λk.λih. succ ih) m
        # Recursing on m: zero case → n; succ k case → succ (add k n).
        add = m: n:
          app (app (app (app N.elim
            (lam "_" N.T (_: N.T)))
            n)
            (lam "k" N.T (k: lam "ih" N.T (ih: app N.succ ih))))
            m;
        two = app N.succ (app N.succ N.zero);
        three = app N.succ (app N.succ (app N.succ N.zero));
        five = app N.succ (app N.succ (app N.succ (app N.succ (app N.succ N.zero))));
      in Q.nf [] (elab (add two three)) == Q.nf [] (elab five);
      expected = true;
    };

    # ===== ListDT tests (datatypeP; parameter A; linear-recursive) =====

    # ListDT: 1-param polymorphic, 2 constructors. `cons` carries one data
    # field (head : A) and one recursive field (tail : List A) — this is
    # the profile linearProfile accepts as Just [A].
    "datatype-list-spec-name" = {
      expr = let
        L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "nil"  [])
            (con "cons" [ (field "head" A) (recField "tail") ])
          ]);
      in L.name;
      expected = "List";
    };
    "datatype-list-spec-params" = {
      expr = let
        L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "nil"  [])
            (con "cons" [ (field "head" A) (recField "tail") ])
          ]);
      in builtins.length L.params;
      expected = 1;
    };
    # Macro D applied to nat is nf-equivalent to the hand-written
    # `listDesc nat`. The polymorphic λA. mono.D fully applies to give
    # the per-instance description; nf normalizes through the
    # `app (ann (λA. ...) ty) nat` β-redex, the ann wrapper, and the
    # listDesc's Bool-fold scaffold.
    "datatype-list-D-matches-listDesc" = {
      expr = let
        L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "nil"  [])
            (con "cons" [ (field "head" A) (recField "tail") ])
          ]);
      in Q.nf [] (elab (app L.D nat)) == Q.nf [] (elab (listDesc nat));
      expected = true;
    };
    # Polymorphic T at A=nat elaborates to a μ value.
    "datatype-list-T-nat-elab" = {
      expr = let
        L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "nil"  [])
            (con "cons" [ (field "head" A) (recField "tail") ])
          ]);
      in (elab (app L.T nat)).tag;
      # app of a lambda-annotated type — elaborated as an app tree.
      # The outer elab tag is "app" (not yet β-reduced); eval reduces to VMu.
      expected = "app";
    };
    # `ListDT.nil nat` type-checks against `ListDT.T nat`.
    "datatype-list-nil-checks" = {
      expr = let
        L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "nil"  [])
            (con "cons" [ (field "head" A) (recField "tail") ])
          ]);
        result = checkHoas (app L.T nat) (app L.nil nat);
      in !(result ? error);
      expected = true;
    };
    # `ListDT.cons nat zero (ListDT.nil nat)` type-checks.
    "datatype-list-cons-one-checks" = {
      expr = let
        L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "nil"  [])
            (con "cons" [ (field "head" A) (recField "tail") ])
          ]);
        hoasVal = app (app (app L.cons nat) zero) (app L.nil nat);
        result = checkHoas (app L.T nat) hoasVal;
      in !(result ? error);
      expected = true;
    };
    # Polymorphic cons at A=nat infers to a Π over head, tail (curried).
    "datatype-list-cons-at-nat-infers-pi" = {
      expr = let
        L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "nil"  [])
            (con "cons" [ (field "head" A) (recField "tail") ])
          ]);
      in (inferHoas (app L.cons nat)).type.tag;
      expected = "VPi";
    };
    # nf-equivalence of the macro ListDT.elim against the inline
    # `listElim` adapter on the empty list. Motive (λ_. nat), onNil =
    # zero, onCons returns `succ head` to differentiate base from step.
    "datatype-list-elim-nf-gate-empty" = {
      expr = let
        L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "nil"  [])
            (con "cons" [ (field "head" A) (recField "tail") ])
          ]);
        M = lam "_" (app L.T nat) (_: nat);
        onNil = zero;
        onCons = lam "h" nat (h: lam "t" (app L.T nat) (t: lam "ih" nat (ih: succ h)));
        scrut = app L.nil nat;
        macroApplied = app (app (app (app (app L.elim nat) M) onNil) onCons) scrut;
        adapterApplied = listElim nat M onNil
          (lam "h" nat (h: lam "t" (listOf nat) (t: lam "ih" nat (ih: succ h))))
          (nil nat);
      in Q.nf [] (elab macroApplied) == Q.nf [] (elab adapterApplied);
      expected = true;
    };
    # nf-gate on a one-element list: cons zero nil. Both sides reduce to
    # `succ zero` after normalization.
    "datatype-list-elim-nf-gate-one" = {
      expr = let
        L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "nil"  [])
            (con "cons" [ (field "head" A) (recField "tail") ])
          ]);
        M = lam "_" (app L.T nat) (_: nat);
        onNil = zero;
        onCons = lam "h" nat (h: lam "t" (app L.T nat) (t: lam "ih" nat (ih: succ h)));
        scrut = app (app (app L.cons nat) zero) (app L.nil nat);
        macroApplied = app (app (app (app (app L.elim nat) M) onNil) onCons) scrut;
        adapterApplied = listElim nat M zero
          (lam "h" nat (h: lam "t" (listOf nat) (t: lam "ih" nat (ih: succ h))))
          (cons nat zero (nil nat));
      in Q.nf [] (elab macroApplied) == Q.nf [] (elab adapterApplied);
      expected = true;
    };
    # nf-gate on a fresh-variable neutral list scrutinee — pins the stuck
    # normal form equality under the macro vs the adapter.
    "datatype-list-elim-nf-gate-neutral" = {
      expr = let
        L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "nil"  [])
            (con "cons" [ (field "head" A) (recField "tail") ])
          ]);
        M = lam "_" (app L.T nat) (_: nat);
        macroAtL = lam "l" (app L.T nat) (l:
          app (app (app (app (app L.elim nat) M) zero)
            (lam "h" nat (h: lam "t" (app L.T nat) (t: lam "ih" nat (ih: succ h)))))
            l);
        adapterAtL = lam "l" (listOf nat) (l:
          listElim nat (lam "_" (listOf nat) (_: nat)) zero
            (lam "h" nat (h: lam "t" (listOf nat) (t: lam "ih" nat (ih: succ h))))
            l);
      in Q.nf [] (elab macroAtL) == Q.nf [] (elab adapterAtL);
      expected = true;
    };

    # Tree: non-linear recursive (node has two rec fields). The peel's
    # linearProfile on the false-branch description `descRec (descRec
    # descRet)` returns null; the check falls through to non-trampolined
    # descCon handling without crashing. A payload-shape classifier would
    # mis-read `pair false (pair LEFTREC (pair RIGHTREC tt))` as a list-
    # shape head+rec and crash on the null elemVal — description-shape
    # dispatch avoids that class of miscount.
    "peel-declines-tree-shape" = {
      expr = let
        Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "leaf" [ (field "value" A) ])
            (con "node" [ (recField "left") (recField "right") ])
          ]);
        leafZero = app (app Tree.leaf nat) zero;
        nodeLL = app (app (app Tree.node nat) leafZero) leafZero;
        result = checkHoas (app Tree.T nat) nodeLL;
      in !(result ? error);
      expected = true;
    };

    # ===== SumDT tests (datatypeP; two parameters; non-recursive) =====

    # SumDT: 2-param polymorphic, 2 constructors. Each constructor carries a
    # single data field and no recursive field — exercises the nParams=2
    # branch of datatypeP's parameter loop. chainShapeOk requires a final
    # rec field, so the chain-flattener declines on `inl`/`inr` and the
    # regular ann-lam cascade handles every application.
    "datatype-sum-spec-name" = {
      expr = let
        S = datatypeP "Sum"
          [ { name = "A"; kind = u 0; } { name = "B"; kind = u 0; } ]
          (ps: let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
            (con "inl" [ (field "value" A) ])
            (con "inr" [ (field "value" B) ])
          ]);
      in S.name;
      expected = "Sum";
    };
    "datatype-sum-spec-params" = {
      expr = let
        S = datatypeP "Sum"
          [ { name = "A"; kind = u 0; } { name = "B"; kind = u 0; } ]
          (ps: let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
            (con "inl" [ (field "value" A) ])
            (con "inr" [ (field "value" B) ])
          ]);
      in builtins.length S.params;
      expected = 2;
    };
    # Macro D applied to (nat, bool) is nf-equivalent to the hand-written
    # `sumDesc nat bool`. The polymorphic λA.λB. mono.D fully applies to
    # give the per-instance description; nf normalizes through the two
    # `app (ann (λ. ...) ty) _` β-redexes, the ann wrappers, and the
    # sumDesc Bool-fold scaffold.
    "datatype-sum-D-matches-sumDesc" = {
      expr = let
        S = datatypeP "Sum"
          [ { name = "A"; kind = u 0; } { name = "B"; kind = u 0; } ]
          (ps: let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
            (con "inl" [ (field "value" A) ])
            (con "inr" [ (field "value" B) ])
          ]);
      in Q.nf [] (elab (app (app S.D nat) bool))
         == Q.nf [] (elab (sumDesc nat bool));
      expected = true;
    };
    # Polymorphic T fully applied to (nat, bool) elaborates as an app tree
    # (the outer ann (λA.λB. ...) ty awaiting two β-reductions); eval
    # reduces it to VMu.
    "datatype-sum-T-applied-elab" = {
      expr = let
        S = datatypeP "Sum"
          [ { name = "A"; kind = u 0; } { name = "B"; kind = u 0; } ]
          (ps: let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
            (con "inl" [ (field "value" A) ])
            (con "inr" [ (field "value" B) ])
          ]);
      in (elab (app (app S.T nat) bool)).tag;
      expected = "app";
    };
    # `SumDT.inl nat bool zero` type-checks against `SumDT.T nat bool`.
    "datatype-sum-inl-checks" = {
      expr = let
        S = datatypeP "Sum"
          [ { name = "A"; kind = u 0; } { name = "B"; kind = u 0; } ]
          (ps: let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
            (con "inl" [ (field "value" A) ])
            (con "inr" [ (field "value" B) ])
          ]);
        hoasVal = app (app (app S.inl nat) bool) zero;
        result = checkHoas (app (app S.T nat) bool) hoasVal;
      in !(result ? error);
      expected = true;
    };
    # `SumDT.inr nat bool true_` type-checks against `SumDT.T nat bool`.
    "datatype-sum-inr-checks" = {
      expr = let
        S = datatypeP "Sum"
          [ { name = "A"; kind = u 0; } { name = "B"; kind = u 0; } ]
          (ps: let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
            (con "inl" [ (field "value" A) ])
            (con "inr" [ (field "value" B) ])
          ]);
        hoasVal = app (app (app S.inr nat) bool) true_;
        result = checkHoas (app (app S.T nat) bool) hoasVal;
      in !(result ? error);
      expected = true;
    };
    # Polymorphic inl partially applied to its two type parameters infers
    # to a Π over `value` — the curried single-data-field signature.
    "datatype-sum-inl-at-types-infers-pi" = {
      expr = let
        S = datatypeP "Sum"
          [ { name = "A"; kind = u 0; } { name = "B"; kind = u 0; } ]
          (ps: let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
            (con "inl" [ (field "value" A) ])
            (con "inr" [ (field "value" B) ])
          ]);
      in (inferHoas (app (app S.inl nat) bool)).type.tag;
      expected = "VPi";
    };
    # nf-equivalence of the macro SumDT.elim against the inline `sumElim`
    # adapter on an `inl` scrutinee. Motive picks `nat` (constant), onLeft
    # is identity on Nat, onRight is the Bool→Nat true↦zero false↦zero
    # constant — both sides reduce to `zero` on `inl nat bool zero`.
    "datatype-sum-elim-nf-gate-inl" = {
      expr = let
        S = datatypeP "Sum"
          [ { name = "A"; kind = u 0; } { name = "B"; kind = u 0; } ]
          (ps: let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
            (con "inl" [ (field "value" A) ])
            (con "inr" [ (field "value" B) ])
          ]);
        M = lam "_" (app (app S.T nat) bool) (_: nat);
        onLeft  = lam "a" nat  (a: a);
        onRight = lam "b" bool (_: zero);
        scrut = app (app (app S.inl nat) bool) zero;
        macroApplied =
          app (app (app (app (app (app S.elim nat) bool) M) onLeft) onRight) scrut;
        adapterApplied =
          sumElim nat bool M onLeft onRight (inl nat bool zero);
      in Q.nf [] (elab macroApplied) == Q.nf [] (elab adapterApplied);
      expected = true;
    };
    # nf-equivalence on an `inr` scrutinee. Same motive/cases; this
    # exercises the false-branch of the descInd boolElim dispatch.
    "datatype-sum-elim-nf-gate-inr" = {
      expr = let
        S = datatypeP "Sum"
          [ { name = "A"; kind = u 0; } { name = "B"; kind = u 0; } ]
          (ps: let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
            (con "inl" [ (field "value" A) ])
            (con "inr" [ (field "value" B) ])
          ]);
        M = lam "_" (app (app S.T nat) bool) (_: nat);
        onLeft  = lam "a" nat  (a: a);
        onRight = lam "b" bool (_: zero);
        scrut = app (app (app S.inr nat) bool) true_;
        macroApplied =
          app (app (app (app (app (app S.elim nat) bool) M) onLeft) onRight) scrut;
        adapterApplied =
          sumElim nat bool M onLeft onRight (inr nat bool true_);
      in Q.nf [] (elab macroApplied) == Q.nf [] (elab adapterApplied);
      expected = true;
    };
    # nf-gate on a fresh-variable neutral Sum scrutinee — pins the stuck
    # normal form equality under the macro vs the adapter.
    "datatype-sum-elim-nf-gate-neutral" = {
      expr = let
        S = datatypeP "Sum"
          [ { name = "A"; kind = u 0; } { name = "B"; kind = u 0; } ]
          (ps: let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
            (con "inl" [ (field "value" A) ])
            (con "inr" [ (field "value" B) ])
          ]);
        M = lam "_" (app (app S.T nat) bool) (_: nat);
        onLeft  = lam "a" nat  (a: a);
        onRight = lam "b" bool (_: zero);
        macroAtS = lam "s" (app (app S.T nat) bool) (s:
          app (app (app (app (app (app S.elim nat) bool) M) onLeft) onRight) s);
        adapterAtS = lam "s" (sum nat bool) (s:
          sumElim nat bool (lam "_" (sum nat bool) (_: nat))
            onLeft onRight s);
      in Q.nf [] (elab macroAtS) == Q.nf [] (elab adapterAtS);
      expected = true;
    };

    # ===== TreeDT tests (datatypeP; one parameter; non-linear recursion) =====

    # TreeDT is a non-prelude user-defined datatype with two constructors:
    # `leaf` carries one data field, `node` carries two recursive fields.
    # `node`'s shape `descRec (descRec descRet)` falls outside linearProfile's
    # acceptance (no terminal data spine), so the chain-flattener declines
    # and the regular ann-lam cascade handles every application. The
    # eliminator's dispatchStep projects two recursive IHs at positions 0
    # and 1 of payloadIH (one per rec field, in declaration order).
    "datatype-tree-spec-name" = {
      expr = let
        Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "leaf" [ (field "value" A) ])
            (con "node" [ (recField "left") (recField "right") ])
          ]);
      in Tree.name;
      expected = "Tree";
    };
    "datatype-tree-spec-params" = {
      expr = let
        Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "leaf" [ (field "value" A) ])
            (con "node" [ (recField "left") (recField "right") ])
          ]);
      in builtins.length Tree.params;
      expected = 1;
    };
    "datatype-tree-spec-cons" = {
      expr = let
        Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "leaf" [ (field "value" A) ])
            (con "node" [ (recField "left") (recField "right") ])
          ]);
      in builtins.length Tree._dtypeMeta.cons;
      expected = 2;
    };
    # Polymorphic T at A=nat elaborates as an app tree (ann-wrapped λA. ...
    # awaiting β); eval reduces to VMu.
    "datatype-tree-T-at-nat-elab" = {
      expr = let
        Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "leaf" [ (field "value" A) ])
            (con "node" [ (recField "left") (recField "right") ])
          ]);
      in (elab (app Tree.T nat)).tag;
      expected = "app";
    };
    # `Tree.leaf nat zero` type-checks against `Tree.T nat`.
    "datatype-tree-leaf-checks" = {
      expr = let
        Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "leaf" [ (field "value" A) ])
            (con "node" [ (recField "left") (recField "right") ])
          ]);
        leafZero = app (app Tree.leaf nat) zero;
        result = checkHoas (app Tree.T nat) leafZero;
      in !(result ? error);
      expected = true;
    };
    # `Tree.node nat (leaf 0) (leaf 0)` type-checks against `Tree.T nat`.
    # Exercises the two-rec-fields fallback path: the chain-flatten precondition
    # rejects (chainShapeOk requires the last field to be `rec` and all earlier
    # fields to be `data`), so the application elaborates through the regular
    # ann-lam cascade. The kernel's desc-con peel then sees a `descRec
    # (descRec descRet)` description, linearProfile returns null, and the peel
    # declines without mis-reading the payload.
    "datatype-tree-node-of-leaves-checks" = {
      expr = let
        Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "leaf" [ (field "value" A) ])
            (con "node" [ (recField "left") (recField "right") ])
          ]);
        leafZero = app (app Tree.leaf nat) zero;
        nodeLL = app (app (app Tree.node nat) leafZero) leafZero;
        result = checkHoas (app Tree.T nat) nodeLL;
      in !(result ? error);
      expected = true;
    };
    # Polymorphic leaf at A=nat infers to a Π over `value : nat`.
    "datatype-tree-leaf-at-nat-infers-pi" = {
      expr = let
        Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "leaf" [ (field "value" A) ])
            (con "node" [ (recField "left") (recField "right") ])
          ]);
      in (inferHoas (app Tree.leaf nat)).type.tag;
      expected = "VPi";
    };
    # Polymorphic elim at A=nat infers to a Π (over the motive P).
    "datatype-tree-elim-at-nat-infers-pi" = {
      expr = let
        Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "leaf" [ (field "value" A) ])
            (con "node" [ (recField "left") (recField "right") ])
          ]);
      in (inferHoas (app Tree.elim nat)).type.tag;
      expected = "VPi";
    };
    # End-to-end semantic test: count leaves of a 2-leaf tree.
    # leafCount = elim with motive (λ_. nat),
    #   step_leaf  = λ_. succ zero
    #   step_node  = λl r il ir. add il ir
    # `node (leaf 0) (leaf 0)` reduces via descInd to `add 1 1 = 2`. The
    # equality `leafCount tree ≡ succ (succ zero)` holds by reduction; refl
    # type-checks against it.
    "datatype-tree-elim-leaf-count-2" = {
      expr = let
        Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "leaf" [ (field "value" A) ])
            (con "node" [ (recField "left") (recField "right") ])
          ]);
        Tnat = app Tree.T nat;
        leafZero = app (app Tree.leaf nat) zero;
        nodeLL = app (app (app Tree.node nat) leafZero) leafZero;
        addTm = lam "m" nat (m: lam "n" nat (n:
                  ind (lam "_" nat (_: nat))
                      n
                      (lam "k" nat (_: lam "ih" nat (ih: succ ih)))
                      m));
        M = lam "_" Tnat (_: nat);
        sLeaf = lam "v" nat (_: succ zero);
        sNode = lam "l" Tnat (_:
                lam "r" Tnat (_:
                lam "il" nat (il:
                lam "ir" nat (ir: app (app addTm il) ir))));
        countTm = app (app (app (app (app Tree.elim nat) M) sLeaf) sNode) nodeLL;
        two = succ (succ zero);
        eqTy = eq nat countTm two;
      in (checkHoas eqTy refl).tag;
      expected = "refl";
    };

    # ===== W-type tests (datatypeP; dependent parameter kinds) =====

    # W is parameterised by S (shapes : U) and P (positions : S → U). The
    # second parameter's KIND depends on the first — `P : S → U` cannot be
    # expressed with a fixed Hoas kind, so `datatypeP` accepts `kind` as
    # either a Hoas (fixed) OR a function `markers → Hoas` (dependent on
    # previously-bound parameter markers). This mirrors the existing
    # `field`/`fieldD` and `piField`/`piFieldD` dependency pattern at the
    # parameter level.
    #
    # The single ctor `sup` carries one data field (s : S) and one
    # dependent pi field (f : (P s) → W S P), exercising piFieldD's
    # `prev`-threaded type construction. chainShapeOk requires last.kind ==
    # "rec"; sup's last field is "piD", so the chain-flattener declines and
    # the regular ann-lam cascade handles every application.
    "datatype-w-spec-name" = {
      expr = let
        W = datatypeP "W"
          [ { name = "S"; kind = u 0; }
            { name = "P"; kind = ms: forall "_" (builtins.elemAt ms 0) (_: u 0); } ]
          (ps: let S = builtins.elemAt ps 0; P = builtins.elemAt ps 1; in [
            (con "sup" [ (field "s" S) (piFieldD "f" (prev: app P prev.s)) ])
          ]);
      in W.name;
      expected = "W";
    };
    "datatype-w-spec-params" = {
      expr = let
        W = datatypeP "W"
          [ { name = "S"; kind = u 0; }
            { name = "P"; kind = ms: forall "_" (builtins.elemAt ms 0) (_: u 0); } ]
          (ps: let S = builtins.elemAt ps 0; P = builtins.elemAt ps 1; in [
            (con "sup" [ (field "s" S) (piFieldD "f" (prev: app P prev.s)) ])
          ]);
      in builtins.length W.params;
      expected = 2;
    };
    # W's macro D fully applied to (bool, λs.boolElim _ unit void s) is
    # nf-equivalent to the hand-written `descArg bool (s: descPi (boolP s)
    # descRet)` from the integration-desc-wtype-wellformed test. Pins
    # the D-emission shape against the canonical W-type description.
    "datatype-w-D-matches-wDesc" = {
      expr = let
        W = datatypeP "W"
          [ { name = "S"; kind = u 0; }
            { name = "P"; kind = ms: forall "_" (builtins.elemAt ms 0) (_: u 0); } ]
          (ps: let S = builtins.elemAt ps 0; P = builtins.elemAt ps 1; in [
            (con "sup" [ (field "s" S) (piFieldD "f" (prev: app P prev.s)) ])
          ]);
        boolP = lam "s" bool (s:
                  boolElim (lam "_" bool (_: u 0)) unit void s);
        macroD = app (app W.D bool) boolP;
        manualD = descArg bool (s:
                    descPi (app boolP s) descRet);
      in Q.nf [] (elab macroD) == Q.nf [] (elab manualD);
      expected = true;
    };
    # `W.T bool boolP` reduces to `μ wBoolDesc` and inhabits `U(0)`,
    # matching the `integration-desc-wtype-wellformed` shape test.
    "datatype-w-T-wellformed" = {
      expr = let
        W = datatypeP "W"
          [ { name = "S"; kind = u 0; }
            { name = "P"; kind = ms: forall "_" (builtins.elemAt ms 0) (_: u 0); } ]
          (ps: let S = builtins.elemAt ps 0; P = builtins.elemAt ps 1; in [
            (con "sup" [ (field "s" S) (piFieldD "f" (prev: app P prev.s)) ])
          ]);
        boolP = lam "s" bool (s:
                  boolElim (lam "_" bool (_: u 0)) unit void s);
        Tw = app (app W.T bool) boolP;
        result = checkHoas (u 0) Tw;
      in !(result ? error);
      expected = true;
    };
    # Polymorphic `sup` partially applied to its two type parameters
    # infers to a Π over `s : bool` (the head of the curried field
    # signature). Validates that datatypeP's poly-ctor wrapper composes
    # the two `ann (λS λP. ...)` outer layers without losing inferability.
    "datatype-w-sup-at-types-infers-pi" = {
      expr = let
        W = datatypeP "W"
          [ { name = "S"; kind = u 0; }
            { name = "P"; kind = ms: forall "_" (builtins.elemAt ms 0) (_: u 0); } ]
          (ps: let S = builtins.elemAt ps 0; P = builtins.elemAt ps 1; in [
            (con "sup" [ (field "s" S) (piFieldD "f" (prev: app P prev.s)) ])
          ]);
        boolP = lam "s" bool (s:
                  boolElim (lam "_" bool (_: u 0)) unit void s);
      in (inferHoas (app (app W.sup bool) boolP)).type.tag;
      expected = "VPi";
    };
    # End-to-end ctor application: `sup false_ (λx:void. absurd Tw x)` is
    # a vacuous-position W value (P false_ = void, so f's domain is empty
    # and absurd discharges the body). Type-checks against `Tw = W bool
    # boolP`. Exercises piFieldD's dependent type-construction and the
    # absurd-on-void elimination through the macro's ctor type.
    "datatype-w-sup-vacuous-checks" = {
      expr = let
        W = datatypeP "W"
          [ { name = "S"; kind = u 0; }
            { name = "P"; kind = ms: forall "_" (builtins.elemAt ms 0) (_: u 0); } ]
          (ps: let S = builtins.elemAt ps 0; P = builtins.elemAt ps 1; in [
            (con "sup" [ (field "s" S) (piFieldD "f" (prev: app P prev.s)) ])
          ]);
        boolP = lam "s" bool (s:
                  boolElim (lam "_" bool (_: u 0)) unit void s);
        Tw = app (app W.T bool) boolP;
        vacuous = lam "x" void (x: absurd Tw x);
        sup0 = app (app (app (app W.sup bool) boolP) false_) vacuous;
        result = checkHoas Tw sup0;
      in !(result ? error);
      expected = true;
    };
  };
}

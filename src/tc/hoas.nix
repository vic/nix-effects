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
  nat = { _htag = "nat"; };
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
  listOf = elem: { _htag = "list"; inherit elem; };
  sum = left: right: { _htag = "sum"; inherit left right; };
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

  zero = { _htag = "zero"; };
  succ = pred: { _htag = "succ"; inherit pred; };
  true_ = { _htag = "true"; };
  false_ = { _htag = "false"; };
  tt = { _htag = "tt"; };
  nil = elem: { _htag = "nil"; inherit elem; };
  cons = elem: head: tail: { _htag = "cons"; inherit elem head tail; };
  pair = fst: snd: { _htag = "pair"; inherit fst snd; };
  inl = left: right: term: { _htag = "inl"; inherit left right term; };
  inr = left: right: term: { _htag = "inr"; inherit left right term; };
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

  # Eliminators
  ind = motive: base: step: scrut:
    { _htag = "nat-elim"; inherit motive base step scrut; };
  boolElim = motive: onTrue: onFalse: scrut:
    { _htag = "bool-elim"; inherit motive onTrue onFalse scrut; };
  listElim = elem: motive: onNil: onCons: scrut:
    { _htag = "list-elim"; inherit elem motive onNil onCons scrut; };
  sumElim = left: right: motive: onLeft: onRight: scrut:
    { _htag = "sum-elim"; inherit left right motive onLeft onRight scrut; };
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
    else if t == "app" then
      T.mkApp (elaborate depth h.fn) (elaborate depth h.arg)
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
    "elab-list" = { expr = (elab (listOf nat)).tag; expected = "mu"; };
    "elab-sum" = { expr = (elab (sum nat bool)).tag; expected = "mu"; };
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
  };
}

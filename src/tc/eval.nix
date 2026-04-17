# Type-checking kernel: Evaluator (eval)
#
# eval : Env -> Tm -> Val
# Interprets a term in an environment of values, producing a value.
# Pure function — zero effect system imports.
#
# Trampolines vNatElim and vListElim via builtins.genericClosure
# to guarantee O(1) stack depth on large inductive values.
#
# Fuel mechanism (§9): each eval call decrements fuel. Throws
# "normalization budget exceeded" on exhaustion. Default 10M.
#
# Spec reference: kernel-spec.md §4, §9
{ fx, api, ... }:

let
  inherit (api) mk;
  term = fx.tc.term;
  val = fx.tc.value;
  inherit (val) mkClosure freshVar
    vLam vPi vSigma vPair vNat vZero vSucc
    vBool vTrue vFalse vList vNil vCons
    vUnit vTt vVoid vSum vInl vInr vEq vRefl vU vNe
    vDesc vDescRet vDescArg vDescRec vDescPi vMu vDescCon
    vString vInt vFloat vAttrs vPath vFunction vAny
    vStringLit vIntLit vFloatLit vAttrsLit vPathLit vFnLit vAnyLit
    eApp eFst eSnd eNatElim eBoolElim eListElim eAbsurd eSumElim eJ eStrEq eDescInd eDescElim;

  defaultFuel = 10000000;

  # -- Fuel-threaded internals --

  instantiateF = fuel: cl: arg: evalF fuel ([ arg ] ++ cl.env) cl.body;

  vAppF = fuel: fn: arg:
    if fn.tag == "VLam" then instantiateF fuel fn.closure arg
    else if fn.tag == "VNe" then vNe fn.level (fn.spine ++ [ (eApp arg) ])
    else throw "tc: vApp on non-function (tag=${fn.tag})";

  vFst = p:
    if p.tag == "VPair" then p.fst
    else if p.tag == "VNe" then vNe p.level (p.spine ++ [ eFst ])
    else throw "tc: vFst on non-pair (tag=${p.tag})";

  vSnd = p:
    if p.tag == "VPair" then p.snd
    else if p.tag == "VNe" then vNe p.level (p.spine ++ [ eSnd ])
    else throw "tc: vSnd on non-pair (tag=${p.tag})";

  # vNatElim — trampolined via genericClosure for large naturals.
  vNatElimF = fuel: motive: base: step: scrut:
    if scrut.tag == "VZero" then base
    else if scrut.tag == "VNe" then
      vNe scrut.level (scrut.spine ++ [ (eNatElim motive base step) ])
    else if scrut.tag == "VSucc" then
      let
        chain = builtins.genericClosure {
          startSet = [{ key = 0; val = scrut; }];
          operator = item:
            if item.val.tag == "VSucc"
            then [{ key = item.key + 1; val = item.val.pred; }]
            else [];
        };
        last = builtins.elemAt chain (builtins.length chain - 1);
        baseResult = vNatElimF fuel motive base step last.val;
        n = builtins.length chain - 1;
        # Thread fuel through fold: each step application decrements fuel
        result = builtins.foldl' (state: i:
          if state.fuel <= 0 then throw "normalization budget exceeded"
          else let
            item = builtins.elemAt chain (n - i);
            predVal = item.val.pred;
            f = state.fuel;
            applied = vAppF f (vAppF f step predVal) state.acc;
          in { acc = applied; fuel = f - 1; }
        ) { acc = baseResult; inherit fuel; } (builtins.genList (i: i + 1) n);
      in result.acc
    else throw "tc: vNatElim on non-nat (tag=${scrut.tag})";

  vBoolElim = motive: onTrue: onFalse: scrut:
    if scrut.tag == "VTrue" then onTrue
    else if scrut.tag == "VFalse" then onFalse
    else if scrut.tag == "VNe" then
      vNe scrut.level (scrut.spine ++ [ (eBoolElim motive onTrue onFalse) ])
    else throw "tc: vBoolElim on non-bool (tag=${scrut.tag})";

  # vStrEq — string equality primitive.
  # Both VStringLit → VTrue/VFalse. Neutral arg → extend its spine.
  # StrEq is symmetric, so we canonicalize neutral-first for the spine.
  vStrEq = lhs: rhs:
    if lhs.tag == "VStringLit" && rhs.tag == "VStringLit" then
      if lhs.value == rhs.value then vTrue else vFalse
    else if lhs.tag == "VNe" then
      vNe lhs.level (lhs.spine ++ [ (eStrEq rhs) ])
    else if rhs.tag == "VNe" then
      vNe rhs.level (rhs.spine ++ [ (eStrEq lhs) ])
    else throw "tc: vStrEq on non-string (tags=${lhs.tag}, ${rhs.tag})";

  # vListElim — trampolined like vNatElim for large lists.
  vListElimF = fuel: elemTy: motive: onNil: onCons: scrut:
    if scrut.tag == "VNil" then onNil
    else if scrut.tag == "VNe" then
      vNe scrut.level (scrut.spine ++ [ (eListElim elemTy motive onNil onCons) ])
    else if scrut.tag == "VCons" then
      let
        chain = builtins.genericClosure {
          startSet = [{ key = 0; val = scrut; }];
          operator = item:
            if item.val.tag == "VCons"
            then [{ key = item.key + 1; val = item.val.tail; }]
            else [];
        };
        last = builtins.elemAt chain (builtins.length chain - 1);
        baseResult = vListElimF fuel elemTy motive onNil onCons last.val;
        n = builtins.length chain - 1;
        # Thread fuel through fold: each step application decrements fuel
        result = builtins.foldl' (state: i:
          if state.fuel <= 0 then throw "normalization budget exceeded"
          else let
            item = builtins.elemAt chain (n - i);
            h = item.val.head;
            t = item.val.tail;
            f = state.fuel;
            applied = vAppF f (vAppF f (vAppF f onCons h) t) state.acc;
          in { acc = applied; fuel = f - 1; }
        ) { acc = baseResult; inherit fuel; } (builtins.genList (i: i + 1) n);
      in result.acc
    else throw "tc: vListElim on non-list (tag=${scrut.tag})";

  vAbsurd = type: scrut:
    if scrut.tag == "VNe" then
      vNe scrut.level (scrut.spine ++ [ (eAbsurd type) ])
    else throw "tc: vAbsurd on non-neutral (tag=${scrut.tag})";

  vSumElimF = fuel: left: right: motive: onLeft: onRight: scrut:
    if scrut.tag == "VInl" then vAppF fuel onLeft scrut.val
    else if scrut.tag == "VInr" then vAppF fuel onRight scrut.val
    else if scrut.tag == "VNe" then
      vNe scrut.level (scrut.spine ++ [ (eSumElim left right motive onLeft onRight) ])
    else throw "tc: vSumElim on non-sum (tag=${scrut.tag})";

  # J computation: J(A, a, P, pr, b, refl) = pr.
  # When eq=VRefl, the checker has verified b≡a, so `rhs` is unused.
  # When eq is neutral, `rhs` is preserved in the EJ spine frame for quotation.
  vJ = type: lhs: motive: base: rhs: eq:
    if eq.tag == "VRefl" then base
    else if eq.tag == "VNe" then
      vNe eq.level (eq.spine ++ [ (eJ type lhs motive base rhs) ])
    else throw "tc: vJ on non-eq (tag=${eq.tag})";

  # vDescInd — generic eliminator for description-based inductive types.
  # ind D P step (con d) = step d (everywhere D P (ind D P step) d)
  vDescIndF = fuel: D: motive: step: scrut:
    if fuel <= 0 then throw "normalization budget exceeded"
    else if scrut.tag == "VNe" then
      vNe scrut.level (scrut.spine ++ [ (eDescInd D motive step) ])
    else if scrut.tag == "VDescCon" then
      let
        f = fuel - 1;
        d = scrut.d;
        # Build ih as a VLam: λx. ind D motive step x
        # Closure env = [step, motive, D]; under x: Var 0=x, 1=step, 2=motive, 3=D
        ihVal = vLam "x" (vMu D)
          (mkClosure [step motive D]
            (term.mkDescInd (term.mkVar 3) (term.mkVar 2) (term.mkVar 1) (term.mkVar 0)));
        evResult = everywhereF f D D motive ihVal d;
      in vAppF f (vAppF f step d) evResult
    else throw "tc: vDescInd on non-mu (tag=${scrut.tag})";

  # vDescElim — induction principle for Desc (4 cases: ret, arg, rec, pi).
  # descElim P pr pa pe pp D : P D
  vDescElimF = fuel: motive: onRet: onArg: onRec: onPi: scrut:
    if fuel <= 0 then throw "normalization budget exceeded"
    else let f = fuel - 1; in

    if scrut.tag == "VDescRet" then onRet

    else if scrut.tag == "VDescArg" then
      let
        S = scrut.S;
        Tcl = scrut.T;
        tLam = vLam "_" S Tcl;
        # Higher-order IH: λ(s:S). descElim motive onRet onArg onRec onPi (T s)
        # Closure env: [tLam, motive, onRet, onArg, onRec, onPi]
        # When instantiated with s: env = [s, tLam, motive, onRet, onArg, onRec, onPi]
        # s=0, tLam=1, motive=2, onRet=3, onArg=4, onRec=5, onPi=6
        ihClosure = mkClosure [ tLam motive onRet onArg onRec onPi ]
          (term.mkDescElim (term.mkVar 2) (term.mkVar 3) (term.mkVar 4)
                           (term.mkVar 5) (term.mkVar 6)
                           (term.mkApp (term.mkVar 1) (term.mkVar 0)));
        ihLam = vLam "_" S ihClosure;
      in
        vAppF f (vAppF f (vAppF f onArg S) tLam) ihLam

    else if scrut.tag == "VDescRec" then
      let
        D = scrut.D;
        ihVal = vDescElimF f motive onRet onArg onRec onPi D;
      in vAppF f (vAppF f onRec D) ihVal

    else if scrut.tag == "VDescPi" then
      let
        S = scrut.S;
        D = scrut.D;
        ihVal = vDescElimF f motive onRet onArg onRec onPi D;
      in vAppF f (vAppF f (vAppF f onPi S) D) ihVal

    else if scrut.tag == "VNe" then
      vNe scrut.level (scrut.spine ++ [ (eDescElim motive onRet onArg onRec onPi) ])

    else throw "tc: vDescElim on non-desc (tag=${scrut.tag})";

  # -- Pre-built interp motive and cases (static, built once at module load) --

  # interpMotive : λ(D:Desc). U(0) → U(0)
  interpMotive = vLam "_" vDesc
    (mkClosure [] (term.mkPi "_" (term.mkU 0) (term.mkU 0)));

  # interpOnRet : λ(X:U(0)). Unit
  interpOnRet = vLam "X" (vU 0) (mkClosure [] term.mkUnit);

  # interpOnArg : λ(S:U(0)). λ(T:S→Desc). λ(ih:Π(s:S).U→U). λ(X:U(0)). Σ(s:S). ih s X
  # Under λS.λT.λih.λX: env = [X, ih, T, S]
  # Under sigma binder s: env = [s, X, ih, T, S]
  interpOnArg = vLam "S" (vU 0)
    (mkClosure []
      (term.mkLam "T" (term.mkPi "_" (term.mkVar 0) term.mkDesc)
        (term.mkLam "ih" (term.mkPi "s" (term.mkVar 1)
                           (term.mkPi "_" (term.mkU 0) (term.mkU 0)))
          (term.mkLam "X" (term.mkU 0)
            (term.mkSigma "s" (term.mkVar 3)
              (term.mkApp (term.mkApp (term.mkVar 2) (term.mkVar 0))
                          (term.mkVar 1)))))));

  # interpOnRec : λ(D:Desc). λ(ih:U→U). λ(X:U(0)). X × ih X
  # Under λD.λih.λX: env = [X, ih, D]
  # Under sigma binder: env = [_, X, ih, D]
  interpOnRec = vLam "D" vDesc
    (mkClosure []
      (term.mkLam "ih" (term.mkPi "_" (term.mkU 0) (term.mkU 0))
        (term.mkLam "X" (term.mkU 0)
          (term.mkSigma "_" (term.mkVar 0)
            (term.mkApp (term.mkVar 2) (term.mkVar 1))))));

  # interpOnPi : λ(S:U(0)). λ(D:Desc). λ(ih:U→U). λ(X:U(0)). (S→X) × ih X
  # Under λS.λD.λih.λX: env = [X, ih, D, S]
  # Pi codomain (under _): env = [_, X, ih, D, S], mkVar 1 → X
  # Sigma body (under _): env = [_, X, ih, D, S]
  interpOnPi = vLam "S" (vU 0)
    (mkClosure []
      (term.mkLam "D" term.mkDesc
        (term.mkLam "ih" (term.mkPi "_" (term.mkU 0) (term.mkU 0))
          (term.mkLam "X" (term.mkU 0)
            (term.mkSigma "_" (term.mkPi "_" (term.mkVar 3) (term.mkVar 1))
              (term.mkApp (term.mkVar 2) (term.mkVar 1)))))));

  # interp D X — interpretation of description D at family X
  interpF = fuel: D: X:
    let result = vDescElimF fuel interpMotive interpOnRet interpOnArg interpOnRec interpOnPi D;
    in vAppF fuel result X;

  # idx D d — extract target index (trivial for Phase 1, I = ⊤)
  idxF = fuel: D: d: vTt;

  # -- All type computation: All D P d (derived from descElim) --
  # Cases are D'-independent module-level constants. Only the motive closes over D'.

  # allOnRet : λP. λd. Unit  (no recursive args → trivial IH)
  allOnRet = vLam "P" (vU 0) (mkClosure []
    (term.mkLam "d" term.mkUnit term.mkUnit));

  # allOnArg : λS. λT. λihA. λP. λd. ihA (fst d) P (snd d)
  # Under λS.λT.λihA.λP.λd: env = [d, P, ihA, T, S]
  allOnArg = vLam "S" (vU 0) (mkClosure []
    (term.mkLam "T" term.mkDesc
      (term.mkLam "ihA" term.mkDesc
        (term.mkLam "P" (term.mkU 0)
          (term.mkLam "d" (term.mkU 0)
            (term.mkApp
              (term.mkApp
                (term.mkApp (term.mkVar 2) (term.mkFst (term.mkVar 0)))
                (term.mkVar 1))
              (term.mkSnd (term.mkVar 0))))))));

  # allOnRec : λD. λihA. λP. λd. P(fst d) × ihA P (snd d)
  # Under λD.λihA.λP.λd: env = [d, P, ihA, D]
  # Sigma body (under _): env = [_, d, P, ihA, D]
  allOnRec = vLam "D" vDesc (mkClosure []
    (term.mkLam "ihA" term.mkDesc
      (term.mkLam "P" (term.mkU 0)
        (term.mkLam "d" (term.mkU 0)
          (term.mkSigma "_"
            (term.mkApp (term.mkVar 1) (term.mkFst (term.mkVar 0)))
            (term.mkApp
              (term.mkApp (term.mkVar 3) (term.mkVar 2))
              (term.mkSnd (term.mkVar 1))))))));

  # allOnPi : λS. λD. λihA. λP. λd. (Π(s:S). P(fst d s)) × ihA P (snd d)
  # Under λS.λD.λihA.λP.λd: env = [d, P, ihA, D, S]
  # Pi body (under s): env = [s, d, P, ihA, D, S]
  # Sigma body (under _): env = [_, d, P, ihA, D, S]
  allOnPi = vLam "S" (vU 0) (mkClosure []
    (term.mkLam "D" term.mkDesc
      (term.mkLam "ihA" term.mkDesc
        (term.mkLam "P" (term.mkU 0)
          (term.mkLam "d" (term.mkU 0)
            (term.mkSigma "_"
              (term.mkPi "s" (term.mkVar 4)
                (term.mkApp (term.mkVar 2)
                  (term.mkApp (term.mkFst (term.mkVar 1)) (term.mkVar 0))))
              (term.mkApp
                (term.mkApp (term.mkVar 3) (term.mkVar 2))
                (term.mkSnd (term.mkVar 1)))))))));

  # Term-level counterparts of interpMotive / interpOn*. Required so we can
  # embed a kernel-level `interp Dm μD'` expression inside mkAllMotive's body
  # (see below). The term structures below match the value definitions at
  # interpMotive / interpOnRet / interpOnArg / interpOnRec / interpOnPi;
  # eval on these terms produces the same values up to α-β.
  interpMotiveTm = term.mkLam "_" term.mkDesc
    (term.mkPi "_" (term.mkU 0) (term.mkU 0));

  interpOnRetTm = term.mkLam "X" (term.mkU 0) term.mkUnit;

  interpOnArgTm = term.mkLam "S" (term.mkU 0)
    (term.mkLam "T" (term.mkPi "_" (term.mkVar 0) term.mkDesc)
      (term.mkLam "ih" (term.mkPi "s" (term.mkVar 1)
                         (term.mkPi "_" (term.mkU 0) (term.mkU 0)))
        (term.mkLam "X" (term.mkU 0)
          (term.mkSigma "s" (term.mkVar 3)
            (term.mkApp (term.mkApp (term.mkVar 2) (term.mkVar 0))
                        (term.mkVar 1))))));

  interpOnRecTm = term.mkLam "D" term.mkDesc
    (term.mkLam "ih" (term.mkPi "_" (term.mkU 0) (term.mkU 0))
      (term.mkLam "X" (term.mkU 0)
        (term.mkSigma "_" (term.mkVar 0)
          (term.mkApp (term.mkVar 2) (term.mkVar 1)))));

  interpOnPiTm = term.mkLam "S" (term.mkU 0)
    (term.mkLam "D" term.mkDesc
      (term.mkLam "ih" (term.mkPi "_" (term.mkU 0) (term.mkU 0))
        (term.mkLam "X" (term.mkU 0)
          (term.mkSigma "_" (term.mkPi "_" (term.mkVar 3) (term.mkVar 1))
            (term.mkApp (term.mkVar 2) (term.mkVar 1))))));

  # interpTm Dtm Xtm : a kernel term that evaluates to `interp Dm X`.
  # Structurally equal to the term emitted by `interpHoas` in hoas.nix, so
  # when the outer Desc is stuck (neutral), the motive produced by
  # `mkAllMotive` below is conv-equal to the motive produced by `allHoas`.
  interpTm = Dtm: Xtm: term.mkApp
    (term.mkDescElim interpMotiveTm interpOnRetTm
      interpOnArgTm interpOnRecTm interpOnPiTm Dtm)
    Xtm;

  # Motive for All (inductive-hypothesis type):
  #   λ(Dm:Desc). Π(P : μD' → U). Π(d : ⟦Dm⟧(μD')). U
  # Matches hoas.nix's `allHoas` motive. Under stuck Dsub the motive is
  # preserved inside a neutral `desc-elim`, so value-level allTy and
  # HOAS-level allHoas must carry the same motive for conv to succeed.
  # Env layout in the closure:
  #   After vLam applied with Dm:  [Dm, vMu D']  -> Var(0)=Dm, Var(1)=μD'
  #   Under outer Pi "P" codomain: [P, Dm, vMu D'] -> Var(1)=Dm, Var(2)=μD'
  mkAllMotive = D': vLam "_" vDesc
    (mkClosure [ (vMu D') ]
      (term.mkPi "P"
        (term.mkPi "_" (term.mkVar 1) (term.mkU 0))
        (term.mkPi "d"
          (interpTm (term.mkVar 1) (term.mkVar 2))
          (term.mkU 0))));

  allTyF = fuel: D': D: P: d:
    let result = vDescElimF fuel (mkAllMotive D') allOnRet allOnArg allOnRec allOnPi D;
    in vAppF fuel (vAppF fuel result P) d;

  # linearProfile D — recognise the "linear recursive" description shape
  # that the desc-con trampoline decomposes layer-by-layer. Returns either
  # null (non-linear; trampoline declines) or [{ S = VDesc; }]_{i=1..n},
  # the list of data-field types preceding the single rec tail, iff
  # D = descArg S_1 (_. descArg S_2 (_. … descRec descRet)) for some n ≥ 0.
  #
  # Nat's succ-branch description `descRec descRet` has profile `[]`;
  # List's cons-branch `descArg elem (_. descRec descRet)` has profile
  # `[{ S = elem; }]`; Tree's `descRec (descRec descRet)` has profile `null`
  # (the inner descRec's body is descRec, not descRet).
  #
  # Closures under VDescArg are instantiated at V.vTt as a dummy. Linear
  # macro-emitted datatypes have constant-in-their-argument closures, so
  # the instantiation is faithful. Dependent shapes either terminate with
  # a non-linear tail (null result) or carry dependent S types — users of
  # the profile treat S as the expected type for that field position, which
  # is correct iff the closure is constant.
  linearProfileF = fuel: D:
    let
      go = node: acc:
        if node.tag == "VDescArg" then
          let subD = instantiateF fuel node.T vTt; in
          go subD (acc ++ [{ S = node.S; }])
        else if node.tag == "VDescRec" then
          if node.D.tag == "VDescRet" then acc
          else null
        else null;
    in go D [];

  # -- everywhere computation: everywhere D P ih d (derived from descElim) --
  # Maps the induction function over recursive positions in the data.

  # evOnRet : λP. λih. λd. tt
  evOnRet = vLam "P" (vU 0) (mkClosure []
    (term.mkLam "ih" (term.mkU 0)
      (term.mkLam "d" term.mkUnit term.mkTt)));

  # evOnArg : λS. λT. λihE. λP. λih. λd. ihE (fst d) P ih (snd d)
  # Under λS.λT.λihE.λP.λih.λd: env = [d, ih, P, ihE, T, S]
  evOnArg = vLam "S" (vU 0) (mkClosure []
    (term.mkLam "T" term.mkDesc
      (term.mkLam "ihE" term.mkDesc
        (term.mkLam "P" (term.mkU 0)
          (term.mkLam "ih" (term.mkU 0)
            (term.mkLam "d" (term.mkU 0)
              (term.mkApp
                (term.mkApp
                  (term.mkApp
                    (term.mkApp (term.mkVar 3) (term.mkFst (term.mkVar 0)))
                    (term.mkVar 2))
                  (term.mkVar 1))
                (term.mkSnd (term.mkVar 0)))))))));

  # evOnRec : λD. λihE. λP. λih. λd. (ih (fst d), ihE P ih (snd d))
  # Under λD.λihE.λP.λih.λd: env = [d, ih, P, ihE, D]
  evOnRec = vLam "D" vDesc (mkClosure []
    (term.mkLam "ihE" term.mkDesc
      (term.mkLam "P" (term.mkU 0)
        (term.mkLam "ih" (term.mkU 0)
          (term.mkLam "d" (term.mkU 0)
            (term.mkPair
              (term.mkApp (term.mkVar 1) (term.mkFst (term.mkVar 0)))
              (term.mkApp
                (term.mkApp
                  (term.mkApp (term.mkVar 3) (term.mkVar 2))
                  (term.mkVar 1))
                (term.mkSnd (term.mkVar 0)))))))));

  # evOnPi : λS. λD. λihE. λP. λih. λd. (λs. ih (fst d s), ihE P ih (snd d))
  # Under λS.λD.λihE.λP.λih.λd: env = [d, ih, P, ihE, D, S]
  # Lambda body (under s): env = [s, d, ih, P, ihE, D, S]
  evOnPi = vLam "S" (vU 0) (mkClosure []
    (term.mkLam "D" term.mkDesc
      (term.mkLam "ihE" term.mkDesc
        (term.mkLam "P" (term.mkU 0)
          (term.mkLam "ih" (term.mkU 0)
            (term.mkLam "d" (term.mkU 0)
              (term.mkPair
                (term.mkLam "s" (term.mkVar 5)
                  (term.mkApp (term.mkVar 2)
                    (term.mkApp (term.mkFst (term.mkVar 1)) (term.mkVar 0))))
                (term.mkApp
                  (term.mkApp
                    (term.mkApp (term.mkVar 3) (term.mkVar 2))
                    (term.mkVar 1))
                  (term.mkSnd (term.mkVar 0))))))))));

  mkEvMotive = D': vLam "_" vDesc
    (mkClosure [vMu D']
      (term.mkPi "P" (term.mkPi "_" (term.mkVar 0) (term.mkU 0))
        (term.mkPi "ih" (term.mkPi "_" (term.mkVar 1) (term.mkU 0))
          (term.mkPi "d" (term.mkU 0) (term.mkU 0)))));

  everywhereF = fuel: D': D: P: ih: d:
    let result = vDescElimF fuel (mkEvMotive D') evOnRet evOnArg evOnRec evOnPi D;
    in vAppF fuel (vAppF fuel (vAppF fuel result P) ih) d;

  # -- Main evaluator with fuel (§9) --
  evalF = fuel: env: tm:
    if fuel <= 0 then throw "normalization budget exceeded"
    else let t = tm.tag; f = fuel - 1; ev = evalF f env; in
    # Variables and binding
    if t == "var" then builtins.elemAt env tm.idx
    else if t == "let" then evalF f ([ (ev tm.val) ] ++ env) tm.body
    else if t == "ann" then ev tm.term

    # Functions
    else if t == "pi" then vPi tm.name (ev tm.domain) (mkClosure env tm.codomain)
    else if t == "lam" then vLam tm.name (ev tm.domain) (mkClosure env tm.body)
    else if t == "app" then vAppF f (ev tm.fn) (ev tm.arg)

    # Pairs
    else if t == "sigma" then vSigma tm.name (ev tm.fst) (mkClosure env tm.snd)
    else if t == "pair" then vPair (ev tm.fst) (ev tm.snd)
    else if t == "fst" then vFst (ev tm.pair)
    else if t == "snd" then vSnd (ev tm.pair)

    # Natural numbers
    else if t == "nat" then vNat
    else if t == "zero" then vZero
    # succ — trampolined for deep naturals (S^5000+)
    else if t == "succ" then
      let
        chain = builtins.genericClosure {
          startSet = [{ key = 0; val = tm; }];
          operator = item:
            if item.val.tag == "succ"
            then [{ key = item.key + 1; val = item.val.pred; }]
            else [];
        };
        n = builtins.length chain - 1;
        base = (builtins.elemAt chain n).val;
      in if n > f then throw "normalization budget exceeded"
      else builtins.foldl' (acc: _: vSucc acc)
        (evalF (f - n) env base)
        (builtins.genList (x: x) n)
    else if t == "nat-elim" then
      vNatElimF f (ev tm.motive) (ev tm.base) (ev tm.step) (ev tm.scrut)

    # Booleans
    else if t == "bool" then vBool
    else if t == "true" then vTrue
    else if t == "false" then vFalse
    else if t == "bool-elim" then
      vBoolElim (ev tm.motive) (ev tm.onTrue) (ev tm.onFalse) (ev tm.scrut)

    # Lists
    else if t == "list" then vList (ev tm.elem)
    else if t == "nil" then vNil (ev tm.elem)
    # cons — trampolined for deep lists (5000+ elements)
    # Fuel: deduct n for chain length, thread remaining through fold (§9.5)
    else if t == "cons" then
      let
        chain = builtins.genericClosure {
          startSet = [{ key = 0; val = tm; }];
          operator = item:
            if item.val.tag == "cons"
            then [{ key = item.key + 1; val = item.val.tail; }]
            else [];
        };
        n = builtins.length chain - 1;
        base = (builtins.elemAt chain n).val;
      in if n > f then throw "normalization budget exceeded"
      else let
        result = builtins.foldl' (state: i:
          if state.fuel <= 0 then throw "normalization budget exceeded"
          else let
            node = (builtins.elemAt chain (n - 1 - i)).val;
            ef = evalF state.fuel env;
          in { acc = vCons (ef node.elem) (ef node.head) state.acc; fuel = state.fuel - 1; }
        ) { acc = evalF (f - n) env base; fuel = f - n; } (builtins.genList (x: x) n);
      in result.acc
    else if t == "list-elim" then
      vListElimF f (ev tm.elem) (ev tm.motive) (ev tm.nil) (ev tm.cons) (ev tm.scrut)

    # Unit
    else if t == "unit" then vUnit
    else if t == "tt" then vTt

    # Void
    else if t == "void" then vVoid
    else if t == "absurd" then vAbsurd (ev tm.type) (ev tm.term)

    # Sum
    else if t == "sum" then vSum (ev tm.left) (ev tm.right)
    else if t == "inl" then vInl (ev tm.left) (ev tm.right) (ev tm.term)
    else if t == "inr" then vInr (ev tm.left) (ev tm.right) (ev tm.term)
    else if t == "sum-elim" then
      vSumElimF f (ev tm.left) (ev tm.right) (ev tm.motive)
        (ev tm.onLeft) (ev tm.onRight) (ev tm.scrut)

    # Identity
    else if t == "eq" then vEq (ev tm.type) (ev tm.lhs) (ev tm.rhs)
    else if t == "refl" then vRefl
    else if t == "j" then
      vJ (ev tm.type) (ev tm.lhs) (ev tm.motive)
        (ev tm.base) (ev tm.rhs) (ev tm.eq)

    # Descriptions (non-indexed, I = ⊤)
    else if t == "desc" then vDesc
    else if t == "desc-ret" then vDescRet
    else if t == "desc-arg" then vDescArg (ev tm.S) (mkClosure env tm.T)
    else if t == "desc-rec" then vDescRec (ev tm.D)
    else if t == "desc-pi" then vDescPi (ev tm.S) (ev tm.D)
    else if t == "mu" then vMu (ev tm.D)
    # desc-con — trampolined for deep recursive chains (5000+).
    # Peels a homogeneous desc-con chain along its recursive position.
    # The outer D's false-branch shape drives decomposition: iff
    # `linearProfile subFalse` is a list of n data-field types, each
    # layer's payload is `pair false (pair f_1 (... (pair REC tt) ...))`
    # with n heads and a rec tail. Non-linear shapes (tree, mutual
    # recursion) fall through to per-layer evaluation.
    #
    # D-sharing across layers: fast path is structural equality of the
    # D subterm (holds when elaborate emits a shared dTm per chain, and
    # when β-reducing macro-generated constructors under a shared param
    # env); fallback is conv-equality of the evaluated D against the
    # outer dVal.
    else if t == "desc-con" then
      let
        dVal = ev tm.D;
        subFalse =
          if dVal.tag != "VDescArg" then null
          else instantiateF f dVal.T vFalse;
        profile = if subFalse == null then null else linearProfileF f subFalse;
        nFields = if profile == null then 0 else builtins.length profile;
        depth = builtins.length env;
        sameD = d2Tm:
          if d2Tm == tm.D then true
          else fx.tc.conv.conv depth (evalF f env d2Tm) dVal;
        walkPayload = payload:
          if payload.tag != "pair" then null
          else if payload.fst.tag != "false" then null
          else
            let
              collect = i: p: acc:
                if i == nFields then
                  if p.tag != "pair" then null
                  else if p.snd.tag != "tt" then null
                  else if p.fst.tag != "desc-con" then null
                  else { heads = acc; tail = p.fst; }
                else
                  if p.tag != "pair" then null
                  else collect (i + 1) p.snd (acc ++ [p.fst]);
            in collect 0 payload.snd [];
        peel = node:
          if profile == null then null
          else if node.tag != "desc-con" then null
          else if !(sameD node.D) then null
          else walkPayload node.d;
        # Integer key is sufficient for dedup. `peel` is O(1) field
        # inspection into the already-concrete `tm`; no deferred work
        # accumulates on `val`, so the trampoline.nix deepSeq defense is
        # unnecessary and would add O(N²) cost through repeated traversal.
        chain = builtins.genericClosure {
          startSet = [{ key = 0; val = tm; }];
          operator = item:
            let peeled = peel item.val; in
            if peeled == null then []
            else [{ key = item.key + 1; val = peeled.tail; }];
        };
        n = builtins.length chain - 1;
        base = (builtins.elemAt chain n).val;
      in if n > f then throw "normalization budget exceeded"
      else let
        baseVal = vDescCon dVal (evalF (f - n) env base.d);
      in builtins.foldl' (acc: i:
        let
          layer = (builtins.elemAt chain (n - 1 - i)).val;
          peeled = peel layer;
          heads = peeled.heads;
          headVals = map (h: evalF (f - n + i) env h) heads;
          buildInner = hs: innerTail:
            if hs == [] then innerTail
            else vPair (builtins.head hs) (buildInner (builtins.tail hs) innerTail);
        in vDescCon dVal
             (vPair vFalse (buildInner headVals (vPair acc vTt)))
      ) baseVal (builtins.genList (x: x) n)
    else if t == "desc-ind" then
      vDescIndF f (ev tm.D) (ev tm.motive) (ev tm.step) (ev tm.scrut)
    else if t == "desc-elim" then
      vDescElimF f (ev tm.motive) (ev tm.onRet) (ev tm.onArg)
        (ev tm.onRec) (ev tm.onPi) (ev tm.scrut)

    # Universes
    else if t == "U" then vU tm.level

    # Axiomatized primitives
    else if t == "string" then vString
    else if t == "int" then vInt
    else if t == "float" then vFloat
    else if t == "attrs" then vAttrs
    else if t == "path" then vPath
    else if t == "function" then vFunction
    else if t == "any" then vAny

    # String operations
    else if t == "str-eq" then vStrEq (ev tm.lhs) (ev tm.rhs)

    # Primitive literals
    else if t == "string-lit" then vStringLit tm.value
    else if t == "int-lit" then vIntLit tm.value
    else if t == "float-lit" then vFloatLit tm.value
    else if t == "attrs-lit" then vAttrsLit
    else if t == "path-lit" then vPathLit
    else if t == "fn-lit" then vFnLit
    else if t == "any-lit" then vAnyLit

    # Opaque lambda: axiomatized value — not callable in kernel
    else if t == "opaque-lam" then val.vOpaqueLam tm._fnBox (ev tm.piTy)

    else throw "tc: eval unknown tag '${t}'";

  # -- Public API (default fuel) --
  eval = evalF defaultFuel;
  instantiate = instantiateF defaultFuel;
  vApp = vAppF defaultFuel;
  vNatElim = vNatElimF defaultFuel;
  vListElim = vListElimF defaultFuel;
  vSumElim = vSumElimF defaultFuel;
  vDescInd = vDescIndF defaultFuel;
  vDescElim = vDescElimF defaultFuel;
  interp = interpF defaultFuel;
  idx = idxF defaultFuel;
  allTy = allTyF defaultFuel;
  linearProfile = linearProfileF defaultFuel;

in mk {
  doc = ''
    # fx.tc.eval — Evaluator

    Pure evaluator: interprets kernel terms in an environment of
    values. Zero effect system imports — part of the trusted computing
    base (TCB).

    Spec reference: kernel-spec.md §4, §9.

    ## Core Functions

    - `eval : Env → Tm → Val` — evaluate with default fuel (10M steps)
    - `evalF : Int → Env → Tm → Val` — evaluate with explicit fuel budget
    - `instantiate : Closure → Val → Val` — apply a closure to an argument

    ## Elimination Helpers

    - `vApp : Val → Val → Val` — apply a function value (beta-reduces VLam, extends spine for VNe)
    - `vFst`, `vSnd` — pair projections
    - `vNatElim`, `vBoolElim`, `vListElim` — inductive eliminators
    - `vAbsurd` — ex falso (only on neutrals)
    - `vSumElim` — sum elimination
    - `vJ` — identity elimination (computes to base on VRefl)

    ## Trampolining (§11.3)

    `vNatElim`, `vListElim`, `succ` chains, and `cons` chains use
    `builtins.genericClosure` to flatten recursive structures iteratively,
    guaranteeing O(1) stack depth on inputs like S^10000(0) or cons^5000.

    ## Fuel Mechanism (§9)

    Each `evalF` call decrements a fuel counter. When fuel reaches 0,
    evaluation throws `"normalization budget exceeded"`. This bounds
    total work and prevents unbounded computation in the Nix evaluator.
    Default budget: 10,000,000 steps.
  '';
  value = {
    inherit eval evalF instantiate;
    inherit vApp vFst vSnd vNatElim vBoolElim vListElim vAbsurd vSumElim vJ vDescInd;
    inherit vDescElim interp idx allTy linearProfile;
  };
  tests = let
    T = fx.tc.term;

    # Helper: build S^n(0) as a term
    succN = n: if n == 0 then T.mkZero else T.mkSucc (succN (n - 1));

    # Identity function: λ(x:Nat). x
    idTm = T.mkLam "x" T.mkNat (T.mkVar 0);

    # Application: (λx.x) 0
    appIdZero = T.mkApp idTm T.mkZero;
  in {
    # -- Variable lookup --
    "eval-var-0" = { expr = (eval [ vZero vTrue ] (T.mkVar 0)).tag; expected = "VZero"; };
    "eval-var-1" = { expr = (eval [ vZero vTrue ] (T.mkVar 1)).tag; expected = "VTrue"; };

    # -- Let binding --
    "eval-let" = {
      expr = (eval [] (T.mkLet "x" T.mkNat T.mkZero (T.mkVar 0))).tag;
      expected = "VZero";
    };

    # -- Annotation erasure --
    "eval-ann" = {
      expr = (eval [] (T.mkAnn T.mkZero T.mkNat)).tag;
      expected = "VZero";
    };

    # -- Functions --
    "eval-lam" = { expr = (eval [] idTm).tag; expected = "VLam"; };
    "eval-pi" = { expr = (eval [] (T.mkPi "x" T.mkNat T.mkNat)).tag; expected = "VPi"; };
    "eval-app-beta" = {
      # (λx.x) 0 = 0
      expr = (eval [] appIdZero).tag;
      expected = "VZero";
    };
    "eval-app-stuck" = {
      # x 0 where x is a neutral at level 0
      expr = (eval [ (freshVar 0) ] (T.mkApp (T.mkVar 0) T.mkZero)).tag;
      expected = "VNe";
    };

    # -- Pairs --
    "eval-sigma" = { expr = (eval [] (T.mkSigma "x" T.mkNat T.mkBool)).tag; expected = "VSigma"; };
    "eval-pair" = { expr = (eval [] (T.mkPair T.mkZero T.mkTrue)).tag; expected = "VPair"; };
    "eval-fst" = {
      expr = (eval [] (T.mkFst (T.mkPair T.mkZero T.mkTrue))).tag;
      expected = "VZero";
    };
    "eval-snd" = {
      expr = (eval [] (T.mkSnd (T.mkPair T.mkZero T.mkTrue))).tag;
      expected = "VTrue";
    };
    "eval-fst-stuck" = {
      expr = (eval [ (freshVar 0) ] (T.mkFst (T.mkVar 0))).tag;
      expected = "VNe";
    };

    # -- Natural numbers --
    "eval-nat" = { expr = (eval [] T.mkNat).tag; expected = "VNat"; };
    "eval-zero" = { expr = (eval [] T.mkZero).tag; expected = "VZero"; };
    "eval-succ" = { expr = (eval [] (T.mkSucc T.mkZero)).tag; expected = "VSucc"; };
    "eval-succ-3" = {
      expr = (eval [] (succN 3)).pred.pred.pred.tag;
      expected = "VZero";
    };

    # NatElim: base case
    "eval-nat-elim-zero" = {
      expr = (eval [ vNat vZero (freshVar 2) ]
        (T.mkNatElim (T.mkVar 0) (T.mkVar 1) (T.mkVar 2) T.mkZero)).tag;
      expected = "VZero";
    };

    # NatElim: step case S(0)
    "eval-nat-elim-succ1" = {
      expr =
        let
          stepTm = T.mkLam "k" T.mkNat (T.mkLam "ih" T.mkNat (T.mkSucc (T.mkVar 0)));
          r = eval [] (T.mkNatElim (T.mkLam "n" T.mkNat (T.mkU 0)) T.mkZero stepTm (T.mkSucc T.mkZero));
        in r.tag;
      expected = "VSucc";
    };

    # NatElim: stuck on neutral
    "eval-nat-elim-stuck" = {
      expr = (eval [ (freshVar 0) vNat vZero (freshVar 3) ]
        (T.mkNatElim (T.mkVar 1) (T.mkVar 2) (T.mkVar 3) (T.mkVar 0))).tag;
      expected = "VNe";
    };

    # -- Booleans --
    "eval-bool" = { expr = (eval [] T.mkBool).tag; expected = "VBool"; };
    "eval-true" = { expr = (eval [] T.mkTrue).tag; expected = "VTrue"; };
    "eval-false" = { expr = (eval [] T.mkFalse).tag; expected = "VFalse"; };
    "eval-bool-elim-true" = {
      expr = (eval [] (T.mkBoolElim (T.mkLam "b" T.mkBool T.mkNat)
        T.mkZero (T.mkSucc T.mkZero) T.mkTrue)).tag;
      expected = "VZero";
    };
    "eval-bool-elim-false" = {
      expr = (eval [] (T.mkBoolElim (T.mkLam "b" T.mkBool T.mkNat)
        T.mkZero (T.mkSucc T.mkZero) T.mkFalse)).tag;
      expected = "VSucc";
    };

    # -- Lists --
    "eval-list" = { expr = (eval [] (T.mkList T.mkNat)).tag; expected = "VList"; };
    "eval-nil" = { expr = (eval [] (T.mkNil T.mkNat)).tag; expected = "VNil"; };
    "eval-cons" = { expr = (eval [] (T.mkCons T.mkNat T.mkZero (T.mkNil T.mkNat))).tag; expected = "VCons"; };
    "eval-list-elim-nil" = {
      expr = (eval [] (T.mkListElim T.mkNat
        (T.mkLam "l" (T.mkList T.mkNat) T.mkNat)
        T.mkZero
        (T.mkLam "h" T.mkNat (T.mkLam "t" (T.mkList T.mkNat) (T.mkLam "ih" T.mkNat (T.mkSucc (T.mkVar 0)))))
        (T.mkNil T.mkNat))).tag;
      expected = "VZero";
    };

    # -- Unit --
    "eval-unit" = { expr = (eval [] T.mkUnit).tag; expected = "VUnit"; };
    "eval-tt" = { expr = (eval [] T.mkTt).tag; expected = "VTt"; };

    # -- Void --
    "eval-void" = { expr = (eval [] T.mkVoid).tag; expected = "VVoid"; };
    "eval-absurd-stuck" = {
      expr = (eval [ (freshVar 0) ] (T.mkAbsurd T.mkNat (T.mkVar 0))).tag;
      expected = "VNe";
    };

    # -- Sum --
    "eval-sum" = { expr = (eval [] (T.mkSum T.mkNat T.mkBool)).tag; expected = "VSum"; };
    "eval-inl" = { expr = (eval [] (T.mkInl T.mkNat T.mkBool T.mkZero)).tag; expected = "VInl"; };
    "eval-inr" = { expr = (eval [] (T.mkInr T.mkNat T.mkBool T.mkTrue)).tag; expected = "VInr"; };
    "eval-sum-elim-inl" = {
      expr = (eval [] (T.mkSumElim T.mkNat T.mkBool
        (T.mkLam "s" (T.mkSum T.mkNat T.mkBool) T.mkNat)
        (T.mkLam "x" T.mkNat (T.mkVar 0))
        (T.mkLam "y" T.mkBool T.mkZero)
        (T.mkInl T.mkNat T.mkBool (T.mkSucc T.mkZero)))).tag;
      expected = "VSucc";
    };
    "eval-sum-elim-inr" = {
      expr = (eval [] (T.mkSumElim T.mkNat T.mkBool
        (T.mkLam "s" (T.mkSum T.mkNat T.mkBool) T.mkNat)
        (T.mkLam "x" T.mkNat (T.mkVar 0))
        (T.mkLam "y" T.mkBool T.mkZero)
        (T.mkInr T.mkNat T.mkBool T.mkTrue))).tag;
      expected = "VZero";
    };

    # -- Identity --
    "eval-eq" = { expr = (eval [] (T.mkEq T.mkNat T.mkZero T.mkZero)).tag; expected = "VEq"; };
    "eval-refl" = { expr = (eval [] T.mkRefl).tag; expected = "VRefl"; };
    "eval-j-refl" = {
      # J(Nat, 0, P, base, 0, refl) = base
      expr = (eval [ vNat vZero (freshVar 2) vZero vZero ]
        (T.mkJ T.mkNat T.mkZero (T.mkVar 2) (T.mkVar 3) T.mkZero T.mkRefl)).tag;
      expected = "VZero";
    };
    "eval-j-stuck" = {
      expr = (eval [ (freshVar 0) ] (T.mkJ T.mkNat T.mkZero
        (T.mkLam "y" T.mkNat (T.mkLam "e" (T.mkEq T.mkNat T.mkZero (T.mkVar 0)) (T.mkU 0)))
        (T.mkU 0) T.mkZero (T.mkVar 0))).tag;
      expected = "VNe";
    };

    # -- Universes --
    "eval-U0" = { expr = (eval [] (T.mkU 0)).tag; expected = "VU"; };
    "eval-U0-level" = { expr = (eval [] (T.mkU 0)).level; expected = 0; };
    "eval-U1-level" = { expr = (eval [] (T.mkU 1)).level; expected = 1; };

    # -- Axiomatized primitives --
    "eval-string" = { expr = (eval [] T.mkString).tag; expected = "VString"; };
    "eval-int" = { expr = (eval [] T.mkInt).tag; expected = "VInt"; };
    "eval-float" = { expr = (eval [] T.mkFloat).tag; expected = "VFloat"; };
    "eval-attrs" = { expr = (eval [] T.mkAttrs).tag; expected = "VAttrs"; };
    "eval-path" = { expr = (eval [] T.mkPath).tag; expected = "VPath"; };
    "eval-function" = { expr = (eval [] T.mkFunction).tag; expected = "VFunction"; };
    "eval-any" = { expr = (eval [] T.mkAny).tag; expected = "VAny"; };
    "eval-string-lit" = { expr = (eval [] (T.mkStringLit "hello")).tag; expected = "VStringLit"; };
    "eval-string-lit-value" = { expr = (eval [] (T.mkStringLit "hello")).value; expected = "hello"; };
    "eval-int-lit" = { expr = (eval [] (T.mkIntLit 42)).tag; expected = "VIntLit"; };
    "eval-int-lit-value" = { expr = (eval [] (T.mkIntLit 42)).value; expected = 42; };
    "eval-float-lit" = { expr = (eval [] (T.mkFloatLit 3.14)).tag; expected = "VFloatLit"; };
    "eval-float-lit-value" = { expr = (eval [] (T.mkFloatLit 3.14)).value; expected = 3.14; };
    "eval-attrs-lit" = { expr = (eval [] T.mkAttrsLit).tag; expected = "VAttrsLit"; };
    "eval-path-lit" = { expr = (eval [] T.mkPathLit).tag; expected = "VPathLit"; };
    "eval-fn-lit" = { expr = (eval [] T.mkFnLit).tag; expected = "VFnLit"; };
    "eval-any-lit" = { expr = (eval [] T.mkAnyLit).tag; expected = "VAnyLit"; };

    # -- Closure instantiation --
    "instantiate-identity" = {
      expr = (instantiate (mkClosure [] (T.mkVar 0)) vZero).tag;
      expected = "VZero";
    };
    "instantiate-const" = {
      expr = (instantiate (mkClosure [ vTrue ] (T.mkVar 1)) vZero).tag;
      expected = "VTrue";
    };

    # -- Fuel mechanism (§9) --
    "fuel-exhaustion" = {
      # Low fuel on a term requiring many eval steps → throws
      expr = (builtins.tryEval (builtins.deepSeq
        (evalF 10 [] (T.mkNatElim
          (T.mkLam "n" T.mkNat T.mkNat)
          T.mkZero
          (T.mkLam "k" T.mkNat (T.mkLam "ih" T.mkNat (T.mkSucc (T.mkVar 0))))
          (succN 100)))
        true)).success;
      expected = false;
    };
    "fuel-sufficient" = {
      # Default fuel handles moderate terms fine
      expr = (eval [] (T.mkNatElim
        (T.mkLam "n" T.mkNat T.mkNat)
        T.mkZero
        (T.mkLam "k" T.mkNat (T.mkLam "ih" T.mkNat (T.mkSucc (T.mkVar 0))))
        (succN 100))).tag;
      expected = "VSucc";
    };

    # Fuel threading: NatElim with fuel=100 on S^200(0) must exhaust.
    # Before fix, each fold step got full fuel budget; now fuel decrements per step.
    "fuel-threading-nat-elim" = {
      expr = (builtins.tryEval (builtins.deepSeq
        (evalF 100 [] (T.mkNatElim
          (T.mkLam "n" T.mkNat T.mkNat)
          T.mkZero
          (T.mkLam "k" T.mkNat (T.mkLam "ih" T.mkNat (T.mkSucc (T.mkVar 0))))
          (succN 200)))
        true)).success;
      expected = false;
    };
    # Fuel threading: ListElim with fuel=100 on 200-element list must exhaust.
    "fuel-threading-list-elim" = {
      expr = let
        mkList = n: builtins.foldl' (acc: _: T.mkCons T.mkNat T.mkZero acc)
          (T.mkNil T.mkNat) (builtins.genList (x: x) n);
      in (builtins.tryEval (builtins.deepSeq
        (evalF 100 [] (T.mkListElim T.mkNat
          (T.mkLam "l" (T.mkList T.mkNat) T.mkNat)
          T.mkZero
          (T.mkLam "h" T.mkNat (T.mkLam "t" (T.mkList T.mkNat)
            (T.mkLam "ih" T.mkNat (T.mkSucc (T.mkVar 0)))))
          (mkList 200)))
        true)).success;
      expected = false;
    };

    # Fuel threading: Cons eval with fuel=100 on 200-element cons chain must exhaust.
    # Before fix, each fold step got full fuel budget; now fuel deducts chain length.
    "fuel-threading-cons-eval" = {
      expr = let
        mkList = n: builtins.foldl' (acc: _: T.mkCons T.mkNat T.mkZero acc)
          (T.mkNil T.mkNat) (builtins.genList (x: x) n);
      in (builtins.tryEval (builtins.deepSeq
        (evalF 100 [] (mkList 200))
        true)).success;
      expected = false;
    };
    # Cons eval with sufficient fuel succeeds
    "fuel-sufficient-cons-eval" = {
      expr = let
        mkList = n: builtins.foldl' (acc: _: T.mkCons T.mkNat T.mkZero acc)
          (T.mkNil T.mkNat) (builtins.genList (x: x) n);
      in (eval [] (mkList 50)).tag;
      expected = "VCons";
    };

    # -- Descriptions --
    "eval-desc" = { expr = (eval [] T.mkDesc).tag; expected = "VDesc"; };
    "eval-desc-ret" = { expr = (eval [] T.mkDescRet).tag; expected = "VDescRet"; };
    "eval-desc-arg" = {
      expr = (eval [] (T.mkDescArg T.mkBool T.mkDescRet)).tag;
      expected = "VDescArg";
    };
    "eval-desc-rec" = {
      expr = (eval [] (T.mkDescRec T.mkDescRet)).tag;
      expected = "VDescRec";
    };
    "eval-desc-pi" = {
      expr = (eval [] (T.mkDescPi T.mkBool T.mkDescRet)).tag;
      expected = "VDescPi";
    };
    "eval-desc-pi-S" = {
      expr = (eval [] (T.mkDescPi T.mkBool T.mkDescRet)).S.tag;
      expected = "VBool";
    };
    "eval-desc-pi-D" = {
      expr = (eval [] (T.mkDescPi T.mkBool T.mkDescRet)).D.tag;
      expected = "VDescRet";
    };
    "eval-mu" = {
      expr = (eval [] (T.mkMu T.mkDescRet)).tag;
      expected = "VMu";
    };
    "eval-desc-con" = {
      expr = (eval [] (T.mkDescCon T.mkDescRet T.mkTt)).tag;
      expected = "VDescCon";
    };
    "eval-desc-ind-stuck" = {
      # desc-ind on a neutral scrutinee produces VNe
      expr = (eval [ (freshVar 0) ] (T.mkDescInd T.mkDescRet
        (T.mkVar 0) (T.mkVar 0) (T.mkVar 0))).tag;
      expected = "VNe";
    };

    # -- descElim --
    "eval-desc-elim-ret" = {
      # descElim on VDescRet returns onRet
      expr = (eval [] (T.mkDescElim
        (T.mkLam "_" T.mkDesc (T.mkU 0))
        T.mkUnit T.mkUnit T.mkUnit T.mkUnit T.mkDescRet)).tag;
      expected = "VUnit";
    };
    "eval-desc-elim-stuck" = {
      # descElim on a neutral scrutinee produces VNe with EDescElim frame
      expr = (eval [ (freshVar 0) ] (T.mkDescElim
        T.mkUnit T.mkUnit T.mkUnit T.mkUnit T.mkUnit (T.mkVar 0))).tag;
      expected = "VNe";
    };

    # -- interp --
    "interp-ret" = {
      # ⟦ret⟧(Nat) = Unit
      expr = (interpF defaultFuel vDescRet vNat).tag;
      expected = "VUnit";
    };
    "interp-rec-ret" = {
      # ⟦rec ret⟧(Nat) = Nat × Unit = Σ("_", Nat, Unit)
      expr = (interpF defaultFuel (vDescRec vDescRet) vNat).tag;
      expected = "VSigma";
    };
    "interp-rec-ret-fst" = {
      # first component is Nat (= X)
      expr = (interpF defaultFuel (vDescRec vDescRet) vNat).fst.tag;
      expected = "VNat";
    };
    "interp-pi-ret" = {
      # ⟦pi Bool ret⟧(Nat) = (Bool→Nat) × Unit
      expr = (interpF defaultFuel (vDescPi vBool vDescRet) vNat).tag;
      expected = "VSigma";
    };
    "interp-pi-ret-fst" = {
      # first component is Bool→Nat = VPi
      expr = (interpF defaultFuel (vDescPi vBool vDescRet) vNat).fst.tag;
      expected = "VPi";
    };
    "interp-pi-ret-fst-domain" = {
      # Pi domain is Bool
      expr = (interpF defaultFuel (vDescPi vBool vDescRet) vNat).fst.domain.tag;
      expected = "VBool";
    };
    "interp-arg-ret" = {
      # ⟦arg Bool (λ_.ret)⟧(Nat) = Σ(s:Bool). Unit
      expr = (interpF defaultFuel (vDescArg vBool (mkClosure [] T.mkDescRet)) vNat).tag;
      expected = "VSigma";
    };
    "interp-arg-ret-fst" = {
      # first component is Bool (= S)
      expr = (interpF defaultFuel (vDescArg vBool (mkClosure [] T.mkDescRet)) vNat).fst.tag;
      expected = "VBool";
    };
    "idx-trivial" = {
      # idx always returns vTt in Phase 1 (I = ⊤)
      expr = (idxF defaultFuel vDescRet vTt).tag;
      expected = "VTt";
    };

    # -- allTy --
    "allTy-ret" = {
      # All ret P d = Unit
      expr = (allTyF defaultFuel vDescRet vDescRet vNat vTt).tag;
      expected = "VUnit";
    };
    "allTy-rec-ret" = {
      # All (rec ret) P (x, tt) = P(x) × Unit
      expr = (allTyF defaultFuel vDescRet (vDescRec vDescRet) vNat
        (vPair vZero vTt)).tag;
      expected = "VSigma";
    };

    # -- ind computation --
    "eval-desc-ind-ret-con" = {
      # ind ret (λ_.Nat) (λd ih. 0) (con tt) = 0
      expr = let
        D = T.mkDescRet;
        P = T.mkLam "_" (T.mkMu D) T.mkNat;
        step = T.mkLam "d" T.mkUnit (T.mkLam "ih" T.mkUnit T.mkZero);
        scrut = T.mkDescCon D T.mkTt;
      in (eval [] (T.mkDescInd D P step scrut)).tag;
      expected = "VZero";
    };
    "eval-desc-ind-arg-con" = {
      # D = arg Bool (λ_.ret), ind D P step (con (false, tt)) = step (false,tt) tt
      expr = let
        D = T.mkDescArg T.mkBool T.mkDescRet;
        P = T.mkLam "_" (T.mkMu D) T.mkNat;
        step = T.mkLam "d" (T.mkU 0) (T.mkLam "ih" T.mkUnit T.mkZero);
        scrut = T.mkDescCon D (T.mkPair T.mkFalse T.mkTt);
      in (eval [] (T.mkDescInd D P step scrut)).tag;
      expected = "VZero";
    };

    # -- §11.3 Stress tests (eval level) --

    # S^10000(0) evaluates to VSucc chain (trampoline not needed for eval,
    # but confirms eval handles deep Succ terms via lazy wrapping)
    "stress-eval-10000" = {
      expr = let
        bigNat = builtins.foldl' (acc: _: T.mkSucc acc)
          T.mkZero (builtins.genList (x: x) 10000);
      in (eval [] bigNat).tag;
      expected = "VSucc";
    };

    # NatElim on S^1000(0) — trampoline stress (spec §11.3)
    "stress-nat-elim-1000" = {
      expr = let
        nat1000 = builtins.foldl' (acc: _: T.mkSucc acc)
          T.mkZero (builtins.genList (x: x) 1000);
        step = T.mkLam "k" T.mkNat (T.mkLam "ih" T.mkNat (T.mkSucc (T.mkVar 0)));
        r = eval [] (T.mkNatElim (T.mkLam "n" T.mkNat T.mkNat) T.mkZero step nat1000);
      in r.tag;
      expected = "VSucc";
    };

    # -- Linear profile classifier (feeds the desc-con trampoline peel) --
    # Nat's succ-branch description: descRec descRet → Just [] (0 data fields).
    "linearProfile-nat-shape" = {
      expr = let
        D = eval [] (T.mkDescRec T.mkDescRet);
      in linearProfile D;
      expected = [];
    };
    # List's cons-branch description: descArg nat (_. descRec descRet) → Just [nat].
    "linearProfile-list-shape-length" = {
      expr = let
        D = eval [] (T.mkDescArg T.mkNat (T.mkDescRec T.mkDescRet));
      in builtins.length (linearProfile D);
      expected = 1;
    };
    "linearProfile-list-shape-S" = {
      expr = let
        D = eval [] (T.mkDescArg T.mkNat (T.mkDescRec T.mkDescRet));
        profile = linearProfile D;
      in (builtins.elemAt profile 0).S.tag;
      expected = "VNat";
    };
    # Tree's node-branch description: descRec (descRec descRet) → null.
    # The inner descRec's body is descRec (not descRet), violating the
    # linear-recursion shape; peel declines, falls through.
    "linearProfile-tree-shape-declines" = {
      expr = let
        D = eval [] (T.mkDescRec (T.mkDescRec T.mkDescRet));
      in linearProfile D;
      expected = null;
    };
    # descRet directly (no rec) — also non-linear for trampoline purposes
    # (there's no recursion to peel).
    "linearProfile-ret-declines" = {
      expr = linearProfile (eval [] T.mkDescRet);
      expected = null;
    };
  };
}

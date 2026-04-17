# Inline tests for the HOAS surface: combinator-level elaboration shape
# checks, kernel-integration checks through `checkHoas`/`inferHoas`,
# theorem proofs, description-level semantic equivalence, datatype macro
# coverage (UnitDT / BoolDT / NatDT / ListDT / SumDT / TreeDT / W-type),
# and deep-stack / neutral-scrutinee stress tests.
{ self, fx, ... }:

let
  E = fx.tc.eval;
  Q = fx.tc.quote;

  inherit (self)
    nat bool unit void string int_ float_ attrs path function_ any
    listOf sum eq u
    forall sigma lam let_
    zero succ true_ false_ tt nil cons pair inl inr refl
    stringLit intLit floatLit attrsLit pathLit fnLit anyLit
    opaqueLam absurd ann app fst_ snd_
    ind boolElim listElim sumElim
    desc mu descRet descArg descRec descPi descCon descElim
    interpHoas allHoas natDesc listDesc sumDesc
    field recField piFieldD con datatype datatypeP
    elab checkHoas inferHoas natLit;
in {
  scope = {};
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
    # nil elaborates to desc-con with inner tag "true" selecting the
    # nil-constructor branch; cons elaborates to desc-con with inner tag
    # "false".
    "elab-nil" = {
      expr = let t = elab (nil nat); in "${t.tag}/${t.d.fst.tag}";
      expected = "desc-con/true";
    };
    "elab-cons" = {
      expr = let t = elab (cons nat zero (nil nat)); in "${t.tag}/${t.d.fst.tag}";
      expected = "desc-con/false";
    };
    "elab-pair" = { expr = (elab (pair zero true_)).tag; expected = "pair"; };
    # inl/inr elaborate to desc-con with inner tag "true"/"false"
    # selecting the inl/inr constructor branch of sumDesc.
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
    # nat-elim surface combinator elaborates to nested let-bindings around
    # a desc-ind: `let P = motive in let B = base in let S = step in
    # desc-ind …`. The let-wrapping makes motive/step/base inferable (VAR
    # via lookupType) so the descInd check rule can type the body.
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
    # Actually, since add is defined by NatElim and NatElim on S(k)
    # computes the step, we get: add(S(k), 0) = S(add(k, 0)). Combined
    # with ih : add(k,0) = k we need S(add(k,0)) = S(k). The J eliminator
    # can produce this.
    #
    # However, encoding cong via J in HOAS is complex. Let's use a
    # simpler approach: the checker normalizes both sides before
    # comparing, so if add(n,0) reduces to n for all n, we just need
    # Refl. But NatElim doesn't reduce symbolically. Instead, test a
    # concrete case: n=3.
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
    # End-to-end semantic checks that the μ-description rebind of
    # Nat/List/Sum computes the same values as the primitive
    # representations under conv.

    # add(2, 3) = 5 on description-based Nat — exercises the rebound
    # `ind` adapter (let-bound P/B/S around descInd) plus Σ-η + ⊤-η in
    # the step.
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

    # length [0, 0, 0] = 3 on description-based List — exercises the
    # rebound `listElim` adapter (let-bound P/N/C around descInd) on the
    # cons chain.
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

    # sumElim id id (inl Nat Nat 7) = 7 on description-based Sum —
    # exercises the rebound `sumElim` adapter (let-bound P/L/R around
    # descInd) with a constant motive Nat, where the trivial rih : ⊤ is
    # discharged in both arms.
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

    # sumElim id id (inr Nat Nat 4) = 4 — mirror test exercises the
    # right arm.
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
    # `wDesc A B = descArg A (a: descPi (B a) descRet)` — B is a Nix
    # meta-level function (A → U at the HOAS surface), applied at
    # elaboration time. This exercises the descPi case in the kernel's
    # Desc check rule.
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

    # interpHoas ≡ interpF — compare nf of HOAS-elaborated term against
    # the quoted result of eval.nix's interp at the same D, X.

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
    # macro wraps the elim in `ann <body> <full-Π-type>`. This test
    # fires an applied elim through `checkHoas` to prove the chain of
    # `app`s type-checks; nf-equivalence
    # (datatype-unit-elim-reduces-to-step) bypasses checking and would
    # silently mask a non-inferable elim.
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
    # D = descArg bool (b: boolElim _ descRet descRet b) — same
    # Bool-fold as natDesc, with both arms degenerate (descRet) instead
    # of asymmetric (descRet vs descRec descRet).
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
    # Macro D matches the canonical bool-fold structure: descArg over
    # the `bool` kernel primitive, with a boolElim body selecting
    # descRet for both arms. Compared against a hand-written equivalent
    # via nf to absorb α-renaming.
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
    # in scope at U0 to distinguish them, but the dispatch chain is
    # still exercised structurally and verified by separately checking
    # that the elim chains through a non-collapsing motive in the next
    # test).
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
    # head of the chain inferable; each step's check rule then
    # validates).
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
    #   - nf-equivalence against the inline natElim adapter. Both
    #     eval-discard their type scaffolding (let_ vs ann) so the
    #     descInd reductions agree.
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
    # Constructor zero: descCon D (pair true_ tt) — same payload shape
    # as the prelude `zero` HOAS combinator, just over the macro-built
    # D.
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
    # Constructor succ is fielded — the macro emits an ann-wrapped
    # curried lam, so its top-level _htag is "ann" until applied.
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
    # Applied succ: descCon D (pair false_ (pair pred tt)). After nf,
    # the ann wrapper and the lam β-reduce away, leaving the descCon
    # term.
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
    # `desc-con` Tm (shared-dTm chain of length 1). The kernel checks
    # it against the type and returns the reconstructed desc-con term.
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
    # for representative (M, B, S, scrut) vectors. Both sides
    # eval-discard their type scaffolding (let_ vs ann), so any
    # divergence after nf is a genuine semantic regression in the
    # macro.
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
    # Scrutinee 2: succ zero. Both onFalse branches fire; macro
    # projects (fst r, fst rih) and applies step_succ; the adapter
    # emits the same projection chain inline.
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
    # Scrutinee 3: succ (succ zero). Two layers of trampoline; checks
    # the nested descInd reduction agrees.
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
    # neutral) modulo α. Distinguishes "macro and adapter happen to
    # agree on closed scrutinees" from "macro and adapter agree as
    # terms".
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

    # End-to-end semantic test: addition on macro-Nat reduces
    # correctly. add(2, 3) = 5 via the macro elim and macro
    # constructors, exercising the IH projection through actual
    # recursion rather than just nf comparison against the inline
    # adapter.
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

    # ListDT: 1-param polymorphic, 2 constructors. `cons` carries one
    # data field (head : A) and one recursive field (tail : List A) —
    # this is the profile linearProfile accepts as Just [A].
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
      # The outer elab tag is "app" (not yet β-reduced); eval reduces
      # to VMu.
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
    # nf-gate on a one-element list: cons zero nil. Both sides reduce
    # to `succ zero` after normalization.
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
    # nf-gate on a fresh-variable neutral list scrutinee — pins the
    # stuck normal form equality under the macro vs the adapter.
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
    # descCon handling without crashing. A payload-shape classifier
    # would mis-read `pair false (pair LEFTREC (pair RIGHTREC tt))` as
    # a list-shape head+rec and crash on the null elemVal —
    # description-shape dispatch avoids that class of miscount.
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

    # SumDT: 2-param polymorphic, 2 constructors. Each constructor
    # carries a single data field and no recursive field — exercises
    # the nParams=2 branch of datatypeP's parameter loop. chainShapeOk
    # requires a final rec field, so the chain-flattener declines on
    # `inl`/`inr` and the regular ann-lam cascade handles every
    # application.
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
    # Macro D applied to (nat, bool) is nf-equivalent to the
    # hand-written `sumDesc nat bool`. The polymorphic λA.λB. mono.D
    # fully applies to give the per-instance description; nf normalizes
    # through the two `app (ann (λ. ...) ty) _` β-redexes, the ann
    # wrappers, and the sumDesc Bool-fold scaffold.
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
    # Polymorphic T fully applied to (nat, bool) elaborates as an app
    # tree (the outer ann (λA.λB. ...) ty awaiting two β-reductions);
    # eval reduces it to VMu.
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
    # Polymorphic inl partially applied to its two type parameters
    # infers to a Π over `value` — the curried single-data-field
    # signature.
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
    # nf-equivalence of the macro SumDT.elim against the inline
    # `sumElim` adapter on an `inl` scrutinee. Motive picks `nat`
    # (constant), onLeft is identity on Nat, onRight is the Bool→Nat
    # true↦zero false↦zero constant — both sides reduce to `zero` on
    # `inl nat bool zero`.
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
    # nf-gate on a fresh-variable neutral Sum scrutinee — pins the
    # stuck normal form equality under the macro vs the adapter.
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

    # TreeDT is a non-prelude user-defined datatype with two
    # constructors: `leaf` carries one data field, `node` carries two
    # recursive fields. `node`'s shape `descRec (descRec descRet)`
    # falls outside linearProfile's acceptance (no terminal data
    # spine), so the chain-flattener declines and the regular ann-lam
    # cascade handles every application. The eliminator's dispatchStep
    # projects two recursive IHs at positions 0 and 1 of payloadIH
    # (one per rec field, in declaration order).
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
    # Polymorphic T at A=nat elaborates as an app tree (ann-wrapped λA.
    # ... awaiting β); eval reduces to VMu.
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
    # Exercises the two-rec-fields fallback path: the chain-flatten
    # precondition rejects (chainShapeOk requires the last field to be
    # `rec` and all earlier fields to be `data`), so the application
    # elaborates through the regular ann-lam cascade. The kernel's
    # desc-con peel then sees a `descRec (descRec descRet)` description,
    # linearProfile returns null, and the peel declines without
    # mis-reading the payload.
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
    # `node (leaf 0) (leaf 0)` reduces via descInd to `add 1 1 = 2`.
    # The equality `leafCount tree ≡ succ (succ zero)` holds by
    # reduction; refl type-checks against it.
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

    # W is parameterised by S (shapes : U) and P (positions : S → U).
    # The second parameter's KIND depends on the first — `P : S → U`
    # cannot be expressed with a fixed Hoas kind, so `datatypeP`
    # accepts `kind` as either a Hoas (fixed) OR a function
    # `markers → Hoas` (dependent on previously-bound parameter
    # markers). This mirrors the existing `field`/`fieldD` and
    # `piField`/`piFieldD` dependency pattern at the parameter level.
    #
    # The single ctor `sup` carries one data field (s : S) and one
    # dependent pi field (f : (P s) → W S P), exercising piFieldD's
    # `prev`-threaded type construction. chainShapeOk requires
    # last.kind == "rec"; sup's last field is "piD", so the
    # chain-flattener declines and the regular ann-lam cascade handles
    # every application.
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
    # nf-equivalent to the hand-written `descArg bool (s: descPi
    # (boolP s) descRet)` from the integration-desc-wtype-wellformed
    # test. Pins the D-emission shape against the canonical W-type
    # description.
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
    # the two `ann (λS λP. ...)` outer layers without losing
    # inferability.
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
    # End-to-end ctor application: `sup false_ (λx:void. absurd Tw x)`
    # is a vacuous-position W value (P false_ = void, so f's domain is
    # empty and absurd discharges the body). Type-checks against `Tw =
    # W bool boolP`. Exercises piFieldD's dependent type-construction
    # and the absurd-on-void elimination through the macro's ctor type.
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

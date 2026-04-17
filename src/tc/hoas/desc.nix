# Description-level helpers (interpHoas / allHoas) and prelude descriptions
# (natDesc / listDesc / sumDesc), plus the pre-elaborated natDescTm used by
# the elaborate layer's zero/succ/ind branches to avoid re-elaborating
# natDesc on every constructor.
#
# interpHoas and allHoas elaborate to `descElim` spines that compute the
# same values as eval.nix's interpF / allTyF (traceable line-by-line
# against eval.nix 213-322). Every HOAS binder below mirrors a named
# interpMotive / interpOn* / mkAllMotive / allOn* in that file.
#
# Principled note on lam annotations: check.nix's check-lam discards the
# HOAS lam's domain annotation and uses the expected type's domain when
# descending, so inner case annotations are for READABILITY only. BUT the
# motive's annotations build paTy / peTy / ppTy in the desc-elim check
# rule, so the motive's d-annotation MUST be the true type of d, not a
# lax U(0) as in eval.nix.
#
# eval.nix uses `term.mkU 0` for d in mkAllMotive; that's sound eval-side
# because eval is not re-checked. HOAS cannot get away with that: when
# allHoas's elaborated onArg runs through check, `fst_ d` fails unless
# d's inferred type is a VSigma. The fix is confined to the motive.
# Evaluation still matches allTyF: the motive body appears only in type
# positions, never in the computed value.
{ self, ... }:

{
  scope = {
    # natDesc : Desc — tag true = zero (no recursion), tag false = succ
    # (one rec arg).
    natDesc =
      let inherit (self) descArg bool boolElim lam desc descRet descRec; in
      descArg bool (b:
        boolElim (lam "_" bool (_: desc)) descRet (descRec descRet) b);

    # listDesc elem : Desc — tag true = nil, tag false = cons
    # (head : elem, tail : rec).
    listDesc = elem:
      let inherit (self) descArg bool boolElim lam desc descRet descRec; in
      descArg bool (b:
        boolElim (lam "_" bool (_: desc))
          descRet
          (descArg elem (_: descRec descRet))
          b);

    # sumDesc l r : Desc — tag true = inl (arg : l), tag false = inr (arg : r).
    sumDesc = l: r:
      let inherit (self) descArg bool boolElim lam desc descRet; in
      descArg bool (b:
        boolElim (lam "_" bool (_: desc))
          (descArg l (_: descRet))
          (descArg r (_: descRet))
          b);

    # Pre-elaborated natDesc — used by the zero/succ/nat-elim elaborate
    # branches to avoid re-elaborating on every constructor.
    natDescTm = self.elab self.natDesc;

    # interpHoas D X  ≡  ⟦D⟧(X)  as a closed kernel TERM.
    interpHoas = D: X:
      let
        inherit (self) lam desc u forall unit sigma app descElim;
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
        inherit (self) lam desc mu forall u unit sigma app descElim fst_ snd_
                        interpHoas;
        # motive : λ(D:Desc). (μDouter → U) → ⟦D⟧(μDouter) → U
        # The inner d-domain MUST be interpHoas D (mu Douter). paTy / peTy /
        # ppTy in the desc-elim check rule reduce this to the concrete Σ /
        # ×-shapes the case bodies expect.
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
  };
  tests = {};
}

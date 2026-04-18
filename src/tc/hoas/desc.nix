# Description-level helpers (interpHoas / allHoas) and prelude descriptions
# (natDesc / listDesc / sumDesc), plus the pre-elaborated natDescTm used by
# the elaborate layer's zero/succ/ind branches to avoid re-elaborating
# natDesc on every constructor.
#
# interpHoas and allHoas elaborate to `descElim` spines that compute the
# same values as eval/desc.nix's interpF / allTyF. Every HOAS binder here
# mirrors a named interpMotive / interpOn* / mkAllMotive / allOn* in
# eval/desc.nix; conv between stuck `desc-elim` frames on the two sides
# relies on that structural match.
#
# Principled note on lam annotations: check.nix's check-lam discards the
# HOAS lam's domain annotation and uses the expected type's domain when
# descending, so inner case annotations are for READABILITY only. The
# motive's annotations, by contrast, build paTy / peTy / ppTy in the
# desc-elim check rule, so the motive's annotations MUST be the true
# types (eval/desc.nix's closed Tms use U(0) placeholders for the same
# binders because eval is not re-checked; HOAS cannot).
#
# The macro-derived prelude descriptions live at the I=⊤ slice:
# `desc`/`descRet`/`descRec`/`descPi` are the ⊤-slice aliases from
# combinators.nix. `mu`/`descCon`/`descInd` carry explicit indices; at
# I=⊤, call sites write `self.tt` at the index position.
{ self, ... }:

{
  scope = {
    # natDesc : Desc ⊤ — tag true = zero (no recursion), tag false = succ
    # (one rec arg).
    natDesc =
      let inherit (self) descArg bool boolElim lam desc descRet descRec; in
      descArg bool (b:
        boolElim (lam "_" bool (_: desc)) descRet (descRec descRet) b);

    # listDesc elem : Desc ⊤ — tag true = nil, tag false = cons
    # (head : elem, tail : rec).
    listDesc = elem:
      let inherit (self) descArg bool boolElim lam desc descRet descRec; in
      descArg bool (b:
        boolElim (lam "_" bool (_: desc))
          descRet
          (descArg elem (_: descRec descRet))
          b);

    # sumDesc l r : Desc ⊤ — tag true = inl (arg : l), tag false = inr (arg : r).
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

    # interpHoas I D X i  ≡  ⟦D⟧(X) i  as a closed kernel TERM.
    #   I : U(0)       the index type
    #   D : Desc I     the description
    #   X : I → U(0)   family of recursive positions
    #   i : I          target index
    # Mirrors eval/desc.nix's interpF structurally — each binder below
    # lines up with a named closure in that file.
    interpHoas = I: D: X: i:
      let
        inherit (self) lam forall descI descElim sigma app eq u;
        descII = descI I;
        iToU = forall "_" I (_: u 0);
        # motive : λ(_:Desc I). (I → U) → I → U
        motive = lam "_" descII (_:
                 forall "_" iToU (_:
                 forall "_" I (_: u 0)));
        # onRet : λ(j:I). λ(X:I→U). λ(i:I). Eq I j i
        onRet  = lam "j" I (j:
                 lam "X" iToU (_:
                 lam "i" I (i':
                   eq I j i')));
        # onArg : λ(S:U). λ(T:S→Desc I). λ(ih:Π(s:S).(I→U)→I→U). λ(X:I→U). λ(i:I).
        #           Σ(s:S). ih s X i
        onArg  = lam "S" (u 0) (S:
                 lam "T" (forall "_" S (_: descII)) (_:
                 lam "ih" (forall "s" S (_:
                            forall "_" iToU (_: forall "_" I (_: u 0)))) (ih:
                 lam "X" iToU (X':
                 lam "i" I (i':
                   sigma "s" S (s: app (app (app ih s) X') i'))))));
        # onRec : λ(j:I). λ(D:Desc I). λ(ih:(I→U)→I→U). λ(X:I→U). λ(i:I).
        #           Σ(_:X j). ih X i
        onRec  = lam "j" I (j:
                 lam "D" descII (_:
                 lam "ih" (forall "_" iToU (_: forall "_" I (_: u 0))) (ih:
                 lam "X" iToU (X':
                 lam "i" I (i':
                   sigma "_" (app X' j) (_: app (app ih X') i'))))));
        # onPi : λ(S:U). λ(f:S→I). λ(D:Desc I). λ(ih:(I→U)→I→U). λ(X:I→U). λ(i:I).
        #          Σ(_:Π(s:S). X(f s)). ih X i
        onPi   = lam "S" (u 0) (S:
                 lam "f" (forall "_" S (_: I)) (f:
                 lam "D" descII (_:
                 lam "ih" (forall "_" iToU (_: forall "_" I (_: u 0))) (ih:
                 lam "X" iToU (X':
                 lam "i" I (i':
                   sigma "_" (forall "s" S (s: app X' (app f s)))
                             (_: app (app ih X') i')))))));
      in app (app (descElim motive onRet onArg onRec onPi D) X) i;

    # allHoas I Douter Dsub P i d ≡ All Douter Dsub P i d — the
    # inductive-hypothesis TYPE for d : ⟦Dsub⟧(μ Douter) i, where
    # P : (i:I) → μ Douter i → U. The motive closes over Douter (and I);
    # the four cases mention Douter only through P's domain shape.
    allHoas = I: Douter: Dsub: P: i: d:
      let
        inherit (self) lam forall descI descElim sigma app fst_ snd_
                        u unit mu interpHoas;
        descII = descI I;
        # muFam : λi. μ Douter i — the family fed to interpHoas as X.
        muFam = lam "_i" I (iArg: mu Douter iArg);
        pTy = forall "i" I (iArg: forall "_" (mu Douter iArg) (_: u 0));
        # motive : λ(D:Desc I).
        #   Π(P:(i:I) → μ Douter i → U). Π(i:I). Π(d:⟦D⟧(μ Douter) i). U
        motive = lam "_" descII (Dm:
                 forall "P" pTy (_:
                 forall "i" I (iArg:
                 forall "d" (interpHoas I Dm muFam iArg) (_: u 0))));
        # onRet : λj λP λi λd. Unit
        onRet  = lam "j" I (_:
                 lam "P" pTy (_:
                 lam "i" I (_:
                 lam "d" unit (_: unit))));
        # onArg : λS λT λihA λP λi λd. ihA (fst d) P i (snd d)
        onArg  = lam "S" (u 0) (S:
                 lam "T" (forall "_" S (_: descII)) (T:
                 lam "ihA" (forall "s" S (s:
                            forall "P" pTy (_:
                            forall "i" I (iArg:
                            forall "d" (interpHoas I (app T s) muFam iArg) (_: u 0))))) (ihA:
                 lam "P" pTy (P2:
                 lam "i" I (iArg:
                 lam "d" (sigma "s" S (s: interpHoas I (app T s) muFam iArg)) (d2:
                   app (app (app (app ihA (fst_ d2)) P2) iArg) (snd_ d2)))))));
        # onRec : λj λD λihA λP λi λd. Σ(_: P j (fst d)). ihA P i (snd d)
        onRec  = lam "j" I (j:
                 lam "D" descII (D2:
                 lam "ihA" (forall "P" pTy (_:
                            forall "i" I (iArg:
                            forall "d" (interpHoas I D2 muFam iArg) (_: u 0)))) (ihA:
                 lam "P" pTy (P2:
                 lam "i" I (iArg:
                 lam "d" (sigma "_" (mu Douter j) (_: interpHoas I D2 muFam iArg)) (d2:
                   sigma "_" (app (app P2 j) (fst_ d2)) (_:
                     app (app (app ihA P2) iArg) (snd_ d2))))))));
        # onPi : λS λf λD λihA λP λi λd.
        #          Σ(_: Π(s:S). P (f s) (fst d s)). ihA P i (snd d)
        onPi   = lam "S" (u 0) (S:
                 lam "f" (forall "_" S (_: I)) (f:
                 lam "D" descII (D2:
                 lam "ihA" (forall "P" pTy (_:
                            forall "i" I (iArg:
                            forall "d" (interpHoas I D2 muFam iArg) (_: u 0)))) (ihA:
                 lam "P" pTy (P2:
                 lam "i" I (iArg:
                 lam "d" (sigma "_" (forall "s" S (s: mu Douter (app f s)))
                                    (_: interpHoas I D2 muFam iArg)) (d2:
                   sigma "_"
                     (forall "s" S (s:
                       app (app P2 (app f s)) (app (fst_ d2) s)))
                     (_: app (app (app ihA P2) iArg) (snd_ d2)))))))));
      in app (app (app (descElim motive onRet onArg onRec onPi Dsub) P) i) d;
  };
}

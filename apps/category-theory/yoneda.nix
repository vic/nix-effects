# Yoneda's lemma (type-theoretic).
#
# For A : U, a : A, B : A → U, the space of sections
# Π(x:A). Eq(A,a,x) → B(x) is equivalent to B(a).
#
# This is Yoneda's lemma viewed through the types-as-groupoids lens:
# every natural transformation from the representable presheaf y(a)
# to B is determined by its value at (a, refl).
#
#   yonedaEval : (Π(x:A). Eq(A,a,x) → B(x)) → B(a)
#   yonedaLift : B(a) → Π(x:A). Eq(A,a,x) → B(x)
#   evalLift   : Π(b:B(a)). eval(lift(b)) = b           (free by computation)
#   liftEval   : Π(α). Π(x). Π(p). lift(eval(α),x,p) = α(x,p)  (by path induction)
{ prelude }:

let
  inherit (prelude) verify U0 Eq Refl J Pi lam app;

  # B : A → U₀  (a type family over A)
  TyFam = A: Pi "_" A (_: U0);

  # Π(x:A). Eq(A,a,x) → B(x)  (sections of B along paths from a)
  SectionTy = A: a: B: Pi "x" A (x: Pi "_" (Eq A a x) (_: app B x));

  # J motive for lift: λy.λ_.B(y)
  liftMotive = A: a: B:
    lam "y" A (y: lam "_" (Eq A a y) (_: app B y));

in rec {

  # -- eval: apply the section at the universal element (a, refl) --

  yonedaEvalTy = Pi "A" U0 (A: Pi "a" A (a: Pi "B" (TyFam A) (B:
    Pi "_" (SectionTy A a B) (alpha:
      app B a))));

  yonedaEvalImpl = lam "A" U0 (A: lam "a" A (a: lam "B" (TyFam A) (B:
    lam "alpha" (SectionTy A a B) (alpha:
      app (app alpha a) Refl))));

  yonedaEval = verify yonedaEvalTy yonedaEvalImpl;

  # -- lift: transport along the path using J --

  yonedaLiftTy = Pi "A" U0 (A: Pi "a" A (a: Pi "B" (TyFam A) (B:
    Pi "b" (app B a) (b:
      SectionTy A a B))));

  yonedaLiftImpl = lam "A" U0 (A: lam "a" A (a: lam "B" (TyFam A) (B:
    lam "b" (app B a) (b:
      lam "x" A (x: lam "p" (Eq A a x) (p:
        J A a (liftMotive A a B) b x p))))));

  yonedaLift = verify yonedaLiftTy yonedaLiftImpl;

  # -- evalLift: eval(lift(b)) = b — free by computation --
  #
  # Unfolding: eval(lift(b)) = lift(b)(a,refl) = J(A,a,M,b,a,refl) = b.
  # J reduces on refl, so the proof is Refl.

  evalLiftTy = Pi "A" U0 (A: Pi "a" A (a: Pi "B" (TyFam A) (B:
    Pi "b" (app B a) (b:
      Eq (app B a)
        (J A a (liftMotive A a B) b a Refl)
        b))));

  evalLiftImpl = lam "A" U0 (A: lam "a" A (a: lam "B" (TyFam A) (B:
    lam "b" (app B a) (b:
      Refl))));

  evalLift = verify evalLiftTy evalLiftImpl;

  # -- liftEval: lift(eval(α),x,p) = α(x,p) — by path induction --
  #
  # Expanded: J(A,a,λy.λ_.B(y), α(a,refl), x, p) = α(x,p).
  # By J on p. At the base case (x=a, p=refl), both sides reduce to α(a,refl).

  liftEvalTy = Pi "A" U0 (A: Pi "a" A (a: Pi "B" (TyFam A) (B:
    Pi "alpha" (SectionTy A a B) (alpha:
      Pi "x" A (x: Pi "p" (Eq A a x) (p:
        Eq (app B x)
          (J A a (liftMotive A a B) (app (app alpha a) Refl) x p)
          (app (app alpha x) p)))))));

  liftEvalImpl = lam "A" U0 (A: lam "a" A (a: lam "B" (TyFam A) (B:
    lam "alpha" (SectionTy A a B) (alpha:
      lam "x" A (x: lam "p" (Eq A a x) (p:
        J A a
          (lam "y" A (y: lam "q" (Eq A a y) (q:
            Eq (app B y)
              (J A a (liftMotive A a B) (app (app alpha a) Refl) y q)
              (app (app alpha y) q))))
          Refl x p))))));

  liftEval = verify liftEvalTy liftEvalImpl;
}

import TranslatedDepthSeven.MonicAdjoinRootSurjection
import TranslatedDepthSeven.MonicAdjoinRootTowerRank
import Mathlib.LinearAlgebra.Charpoly.Basic

/-!
# Characteristic-polynomial equations for triangular presentations

Let `A` be finite free over `R`.  Every selected coordinate `x : A` is
annihilated by the characteristic polynomial of multiplication by `x`.
After any previously constructed `R`-algebra presentation `B →ₐ[R] A`, the
same polynomial can be mapped from `R[X]` to `B[X]`.  Adjoining one root then
extends the range by exactly `x`, and the equation remains monic of degree
`finrank R A`.

Thus, for explicit algebra generators `x₁, ..., xₙ`, literal repetition of
the theorem `range_adjoinRoot_lmulCharpoly_liftAlgHom` gives a surjection from
an iterated monic `AdjoinRoot` tower onto `A`.  Together with
`monicAdjoinRootTowerBasis`, this is the static algebraic core of the
triangular-presentation argument.  It does not provide coefficient-height
bounds for the multiplication matrices; that is a separate effective
problem.
-/

namespace TranslatedDepthSeven

noncomputable section

open Polynomial

universe u v w

variable {R : Type u} {A : Type v}
  [CommRing R] [CommRing A] [Algebra R A]
  [Module.Free R A] [Module.Finite R A]

/-- Cayley--Hamilton for multiplication by an element, pulled back from the
endomorphism ring to the algebra itself. -/
theorem aeval_lmul_charpoly_eq_zero (x : A) :
    Polynomial.aeval x ((Algebra.lmul R A x).charpoly) = 0 := by
  apply Algebra.lmul_injective (R := R)
  simpa [Polynomial.aeval_def] using
    (Algebra.lmul R A x).aeval_self_charpoly

/-- The characteristic polynomial of multiplication by `x` is monic. -/
theorem lmul_charpoly_monic (x : A) :
    (Algebra.lmul R A x).charpoly.Monic :=
  (Algebra.lmul R A x).charpoly_monic

/-- Its degree is the rank of the finite free coordinate algebra. -/
theorem lmul_charpoly_natDegree
    [Nontrivial R] [StrongRankCondition R] (x : A) :
    (Algebra.lmul R A x).charpoly.natDegree = Module.finrank R A :=
  (Algebra.lmul R A x).charpoly_natDegree

variable {B : Type w} [CommRing B] [Algebra R B]

/-- A characteristic-polynomial relation remains a relation after mapping
its coefficients into an arbitrary previously constructed `R`-algebra. -/
theorem eval₂_map_lmul_charpoly_eq_zero
    (phi : B →ₐ[R] A) (x : A) :
    (((Algebra.lmul R A x).charpoly).map (algebraMap R B)).eval₂ phi x = 0 := by
  simpa [Polynomial.eval₂_map, Polynomial.aeval_def] using
    (aeval_lmul_charpoly_eq_zero (R := R) x)

/-- The mapped characteristic polynomial used for the next triangular step
is still monic. -/
theorem map_lmul_charpoly_monic (x : A) :
    (((Algebra.lmul R A x).charpoly).map (algebraMap R B)).Monic :=
  (lmul_charpoly_monic (R := R) x).map (algebraMap R B)

/-- Mapping the coefficients into a nontrivial previous stage does not alter
the degree of the monic characteristic polynomial. -/
theorem map_lmul_charpoly_natDegree
    [Nontrivial R] [StrongRankCondition R] [Nontrivial B] (x : A) :
    (((Algebra.lmul R A x).charpoly).map
      (algebraMap R B)).natDegree = Module.finrank R A := by
  rw [(lmul_charpoly_monic (R := R) x).natDegree_map,
    lmul_charpoly_natDegree (R := R) x]

/-- One canonical characteristic-polynomial `AdjoinRoot` step enlarges the
old presentation range by exactly the selected coordinate. -/
theorem range_adjoinRoot_lmulCharpoly_liftAlgHom
    (phi : B →ₐ[R] A) (x : A) :
    (AdjoinRoot.liftAlgHom
      (((Algebra.lmul R A x).charpoly).map (algebraMap R B))
      phi x (eval₂_map_lmul_charpoly_eq_zero phi x)).range =
      phi.range ⊔ Algebra.adjoin R ({x} : Set A) :=
  range_adjoinRoot_liftAlgHom_eq_sup _ phi x _

/-- If adjoining the selected coordinate generates the target together with
the old range, the canonical characteristic-polynomial step is surjective. -/
theorem adjoinRoot_lmulCharpoly_liftAlgHom_surjective
    (phi : B →ₐ[R] A) (x : A)
    (hgen : phi.range ⊔ Algebra.adjoin R ({x} : Set A) = ⊤) :
    Function.Surjective
      (AdjoinRoot.liftAlgHom
        (((Algebra.lmul R A x).charpoly).map (algebraMap R B))
        phi x (eval₂_map_lmul_charpoly_eq_zero phi x)) := by
  rw [← AlgHom.range_eq_top,
    range_adjoinRoot_lmulCharpoly_liftAlgHom phi x]
  exact hgen

end

end TranslatedDepthSeven

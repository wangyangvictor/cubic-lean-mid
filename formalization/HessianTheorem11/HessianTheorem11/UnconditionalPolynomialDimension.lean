import HessianTheorem11.UnconditionalCutHeight
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.KrullDimension.Field

/-! The exact dimension of affine polynomial rings over Qbar, proved
from the variable ideal, Krull height, and successive variable quotients.
This does not use mathlib's unproved polynomial-dimension placeholder. -/
noncomputable section
namespace HessianTheorem11.UnconditionalPolynomialDimension
open MvPolynomial Ideal UnconditionalCutHeight

theorem origin_ideal_eq_span_variables {n : ℕ} :
    vanishingIdeal GeometricField ({0} : Set (GeometricPoint n)) =
      Ideal.span (Set.range (X : Fin n → GeometricPolynomial n)) := by
  ext P
  rw [← Set.image_univ, mem_ideal_span_X_image]
  constructor
  · intro h m hm
    have hc : P.coeff 0 = 0 := by
      have h0 := h 0 (Set.mem_singleton 0)
      change eval 0 P = 0 at h0
      simpa only [eval_zero, constantCoeff] using h0
    have hmn : m ≠ 0 := by
      intro he
      subst m
      exact (mem_support_iff.mp hm) hc
    obtain ⟨i, hi⟩ := DFunLike.ne_iff.mp hmn
    exact ⟨i, Set.mem_univ i, hi⟩
  · intro h
    intro x hx
    have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
    subst x
    change eval 0 P = 0
    rw [eval_zero]
    change P.coeff 0 = 0
    by_contra hc
    obtain ⟨i, _, hi⟩ := h 0 (mem_support_iff.mpr hc)
    exact hi rfl

theorem polynomial_dimension_le (n : ℕ) :
    ringKrullDim (GeometricPolynomial n) ≤ (n : Dimension) := by
  classical
  let m := vanishingIdeal GeometricField ({0} : Set (GeometricPoint n))
  let s : Finset (GeometricPolynomial n) := Finset.univ.image X
  have he : Ideal.span (s : Set (GeometricPolynomial n)) = m := by
    change Ideal.span (s : Set (GeometricPolynomial n)) = vanishingIdeal GeometricField {0}
    rw [origin_ideal_eq_span_variables]
    simp [s]
  have hmin : m ∈ (Ideal.span (s : Set (GeometricPolynomial n))).minimalPrimes := by
    rw [he]
    simp only [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff]
  have hh := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin
  have hcard : s.card ≤ n := (Finset.card_image_le).trans (by simp)
  rw [← polynomial_maximal_height m]
  exact_mod_cast hh.trans (show (s.card : ℕ∞) ≤ n by exact_mod_cast hcard)

theorem polynomial_dimension_ge (n : ℕ) :
    (n : Dimension) ≤ ringKrullDim (GeometricPolynomial n) := by
  induction n with
  | zero => exact ringKrullDim_nonneg_of_nontrivial
  | succ n ih =>
    let f : GeometricPolynomial (n+1) →ₐ[GeometricField] GeometricPolynomial n :=
      aeval (Fin.cases 0 X)
    have hf : Function.Surjective f := by
      intro P
      refine ⟨rename Fin.succ P, ?_⟩
      simp only [f, aeval_rename, Function.comp_def, Fin.cases_succ, aeval_X_left, AlgHom.id_apply]
    have hx : (X (0 : Fin (n+1)) : GeometricPolynomial (n+1)) ≠ 0 := X_ne_zero _
    have hz : f (X 0) = 0 := by simp [f]
    have h := ringKrullDim_succ_le_of_surjective f.toRingHom hf
      (mem_nonZeroDivisors_of_ne_zero hx) hz
    calc
      ((n+1 : ℕ) : Dimension) = (n : Dimension) + 1 := by simp
      _ ≤ ringKrullDim (GeometricPolynomial n) + 1 := by gcongr
      _ ≤ ringKrullDim (GeometricPolynomial (n+1)) := h

theorem polynomial_dimension (n : ℕ) :
    ringKrullDim (GeometricPolynomial n) = (n : Dimension) :=
  le_antisymm (polynomial_dimension_le n) (polynomial_dimension_ge n)

theorem normalization_dimension {n : ℕ} (A : Type*) [CommRing A]
    [IsDomain A] [IsNoetherianRing A] [Algebra GeometricField A]
    (g : GeometricPolynomial n →ₐ[GeometricField] A)
    (hginj : Function.Injective g) (hgint : g.IsIntegral) :
    ringKrullDim A = (n : Dimension) :=
  (normalization_dimension_eq A g hginj hgint).trans (polynomial_dimension n)

end HessianTheorem11.UnconditionalPolynomialDimension

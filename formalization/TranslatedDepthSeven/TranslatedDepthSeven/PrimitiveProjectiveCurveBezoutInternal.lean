import TranslatedDepthSeven.RationalProjectiveCurveFirstChartBezoutInternal
import TranslatedDepthSeven.PrimitiveRationalVectorHeight
import TranslatedDepthSeven.HomogeneousCone

/-! Rational points in a projective chart, and the two primitive integral
representatives of each point. All cardinal bounds use the proved Hilbert
function version of Bezout. -/
namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 2000000

 theorem rationalPoint_mem_firstChartReducedIdeal {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) (x : Fin (N + 1) → ℚ)
    (hx0 : x 0 = 1) (hx : x ∈ affineIdealZeroLocus I) :
    x ∈ affineIdealZeroLocus (rationalFirstAffineChartReducedIdeal I) := by
  rw [mem_affineIdealZeroLocus_iff_le_ker_aeval]
  apply (RingHom.ker_isPrime (MvPolynomial.eval x)).radical_le_iff.mpr
  apply sup_le
  · exact (mem_affineIdealZeroLocus_iff_le_ker_aeval I x).mp hx
  · rw [Ideal.span_le]
    rintro f (rfl : f = X 0 - C 1)
    change MvPolynomial.aeval x (X 0 - C 1) = 0
    simp [hx0]

/-- The first-chart bound applies to rational, not just integral, normalized
coordinates. -/
theorem card_rationalFirstChartPoints_le_of_span {N D : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (S : Finset (Fin (N + 1) → ℚ))
    (hzero : ∀ x ∈ S, x ∈ affineIdealZeroLocus I)
    (hchart : ∀ x ∈ S, x 0 = 1)
    (v : Fin D → (MvPolynomial (Fin (N + 1)) ℚ ⧸
      rationalFirstAffineChartReducedIdeal I))
    (hv : Submodule.span ℚ (Set.range v) = ⊤) : S.card ≤ D := by
  classical
  let A := MvPolynomial (Fin (N + 1)) ℚ ⧸ rationalFirstAffineChartReducedIdeal I
  let f : {x // x ∈ S} → (A →ₐ[ℚ] ℚ) := fun x ↦
    affineIdealPointToQuotientAlgHom (rationalFirstAffineChartReducedIdeal I)
      ⟨x.1, rationalPoint_mem_firstChartReducedIdeal I x.1
        (hchart x.1 x.2) (hzero x.1 x.2)⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun t : {z // z ∈ affineIdealZeroLocus
        (rationalFirstAffineChartReducedIdeal I)} ↦ t.1)
      ((affineIdealZeroLocusEquivQuotientAlgHom
        (rationalFirstAffineChartReducedIdeal I)).injective h)
  letI : Module.Finite ℚ A := Module.finite_def.mpr <|
    Submodule.fg_iff_exists_fin_generating_family.mpr ⟨D, v, hv⟩
  calc
    S.card = Nat.card {x // x ∈ S} := by simp
    _ ≤ Nat.card (A →ₐ[ℚ] ℚ) := Nat.card_le_card_of_injective f hf
    _ ≤ Module.finrank ℚ A := card_algHom_le_finrank ℚ A ℚ
    _ ≤ D := by simpa [A] using finrank_le_of_span_eq_top hv

/-- Normalization of an integral vector in the rational first chart. -/
def primitiveFirstChartNormalize {N : ℕ} (x : Fin (N + 1) → ℤ) :
    Fin (N + 1) → ℚ := fun i ↦ (x i : ℚ) / (x 0 : ℚ)

 theorem primitiveFirstChartNormalize_eq_implies_sign {N : ℕ}
    (x y : Fin (N + 1) → ℤ) (hx : IsPrimitiveIntVector x)
    (hy : IsPrimitiveIntVector y) (hx0 : x 0 ≠ 0) (hy0 : y 0 ≠ 0)
    (h : primitiveFirstChartNormalize x = primitiveFirstChartNormalize y) :
    y = x ∨ y = -x := by
  have hx0Q : (x 0 : ℚ) ≠ 0 := by exact_mod_cast hx0
  have hy0Q : (y 0 : ℚ) ≠ 0 := by exact_mod_cast hy0
  let q : ℚ := (y 0 : ℚ) / (x 0 : ℚ)
  have hq : q ≠ 0 := div_ne_zero hy0Q hx0Q
  have hscale : ∀ i, (y i : ℚ) = q * (x i : ℚ) := by
    intro i
    have hi := congrFun h i
    dsimp [primitiveFirstChartNormalize] at hi
    dsimp [q]
    apply (div_eq_div_iff hx0Q hy0Q).mp at hi
    field_simp
    nlinarith [hi]
  rcases primitive_proportional_scalar_eq_one_or_neg_one q x y hq hx hy hscale with h1 | hn
  · left
    ext i
    have hi := hscale i
    simp only [h1, one_mul] at hi
    exact_mod_cast hi
  · right
    ext i
    have hi := hscale i
    simp only [hn, neg_one_mul] at hi
    exact_mod_cast hi

/-- There are at most two primitive integral representatives of each
normalized rational first-chart point. -/
theorem card_primitive_le_two_mul_firstChart_image {N : ℕ}
    (S : Finset (Fin (N + 1) → ℤ))
    (hprimitive : ∀ x ∈ S, IsPrimitiveIntVector x)
    (hchart : ∀ x ∈ S, x 0 ≠ 0) :
    S.card ≤ 2 * (S.image primitiveFirstChartNormalize).card := by
  classical
  apply Finset.card_le_mul_card_image
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  have hsub : S.filter (fun y ↦ primitiveFirstChartNormalize y =
      primitiveFirstChartNormalize x) ⊆ {x, -x} := by
    intro y hy
    obtain ⟨hy, heq⟩ := Finset.mem_filter.mp hy
    rcases primitiveFirstChartNormalize_eq_implies_sign x y
      (hprimitive x hx) (hprimitive y hy) (hchart x hx) (hchart y hy) heq.symm with h | h
    · simp [h]
    · simp [h]
  apply (Finset.card_le_card hsub).trans
  have h := Finset.card_pair_eq_one_or_two (a := x) (b := -x)
  omega

/-- A proper degree-k equation leaves at most 2dk primitive vectors in a
fixed rational chart. -/
theorem card_primitiveFirstChart_curve_auxiliary_le {N d k : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) (hI : I.IsPrime)
    (hIhom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hdegree : HasProjectiveDimensionDegree I 1 d)
    (G : MvPolynomial (Fin (N + 1)) ℚ) (hGhom : G.IsHomogeneous k) (hGI : G ∉ I)
    (S : Finset (Fin (N + 1) → ℤ))
    (hprimitive : ∀ x ∈ S, IsPrimitiveIntVector x)
    (hchart : ∀ x ∈ S, x 0 ≠ 0)
    (hzero : ∀ x ∈ S, (fun i ↦ (x i : ℚ)) ∈ affineIdealZeroLocus I)
    (hGzero : ∀ x ∈ S, eval (fun i ↦ (x i : ℚ)) G = 0) :
    S.card ≤ 2 * (d * k) := by
  classical
  obtain ⟨v, hv⟩ := rationalProjectiveCurveAuxiliaryFirstChartBezout_internal
    N d k I G hI hIhom hdegree hGhom hGI
  apply (card_primitive_le_two_mul_firstChart_image S hprimitive hchart).trans
  apply Nat.mul_le_mul_left 2
  apply card_rationalFirstChartPoints_le_of_span (I ⊔ Ideal.span {G})
    (S.image primitiveFirstChartNormalize) _ _ v hv
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [mem_affineIdealZeroLocus_iff_le_ker_aeval]
    apply sup_le
    · have hs := smul_mem_affineIdealZeroLocus_of_isHomogeneous I hIhom
        (hzero x hx) ((x 0 : ℚ)⁻¹)
      apply (mem_affineIdealZeroLocus_iff_le_ker_aeval I _).mp
      simpa [primitiveFirstChartNormalize, div_eq_mul_inv, mul_comm] using hs
    · rw [Ideal.span_le]
      intro f hf
      have hfG : f = G := Set.mem_singleton_iff.mp hf
      subst f
      change eval (primitiveFirstChartNormalize x) G = 0
      have hs := eval_smul_of_isHomogeneous G (fun i ↦ (x i : ℚ))
        ((x 0 : ℚ)⁻¹) k hGhom
      simpa [primitiveFirstChartNormalize, div_eq_mul_inv, mul_comm, hGzero x hx] using hs
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    simp only [primitiveFirstChartNormalize]
    exact div_self (by exact_mod_cast hchart x hx)

end
end TranslatedDepthSeven

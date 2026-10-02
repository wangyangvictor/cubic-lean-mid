import CubicTenVariables.CubicJacobianSectionReduction
import CubicTenVariables.HomogeneousPrincipalOpen

/-! # Slicing a fixed cubic with an arbitrary finite-degree certificate

The degree of the supplied certificate may depend on the fixed equation.
The large-field estimate needs only q > 2D and has the same constant 15.
An integer certificate remains nonzero outside finitely many characteristics;
one additional factorial makes every remaining finite field large enough.
No certificate existence or smooth-section theorem is assumed globally.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace CubicTenVariables.CubicFixedFamilySlicing
open MvPolynomial Literature ProjectiveFourierIdentity
open ProjectiveLinearSectionVariance ProjectivePolynomialSectionVariance
open ProjectiveLinearSectionCoordinates SmoothCubicProjectivePointCount
open CubicSlicingNumerics CubicSmoothSectionReduction CubicJacobianSectionReduction

variable {K : Type} [Field K] [Fintype K]

/-- The actual projective slicing bound for any supplied certificate degree. -/
theorem projective_bound (weil : SmoothCubicWeil)
    (F : MvPolynomial (Fin 10) K) (hFne : F ≠ 0) (hF : F.IsHomogeneous 3)
    (D : ℕ) (Δ : MvPolynomial (Fin 50) K) (hΔ : Δ ≠ 0)
    (hdegree : Δ.totalDegree ≤ D) (hq : 2 * D < Nat.card K)
    (hsections : SmoothThreefoldSections F Δ) :
    |(Nat.card (zeroPoints F) : ℝ) - projectiveMainTerm (Fintype.card K) 8| ≤
      15 * (Fintype.card K : ℝ) ^ ((13 : ℝ) / 2) := by
  obtain ⟨γ, hγ, hvariance⟩ := exists_polynomial_nonvanishing_section
    (n := 10) (k := 5) (D := D) (by decide) (polynomialPoints F) Δ hΔ hdegree hq
  simp only [card_polynomialPoints, sectionCount_polynomialPoints] at hvariance
  rw [show Nat.card K = Fintype.card K from Nat.card_eq_fintype_card] at hvariance
  obtain ⟨e, hGne, hGsmooth⟩ := hsections γ hγ
  have hG := sectionPolynomial_isHomogeneous F hF γ e
  have hcount := projective_error_sq weil 3 (by decide) (by decide)
    (sectionPolynomial F γ e) hGne hG hGsmooth
  rw [projective_sectionPolynomial_card F hF (by decide) γ e] at hcount
  have hq2 : (2 : ℝ) ≤ Fintype.card K := by
    have h : 2 ≤ Fintype.card K := Fintype.one_lt_card
    exact_mod_cast h
  exact projective_slicing_bound hq2 (Nat.cast_nonneg _)
    (ten_variable_crude_bound F hFne hF) hvariance hcount

/-- The literal affine-cone error, with no uniform bound on certificate degree. -/
theorem affine_bound (weil : SmoothCubicWeil)
    (F : MvPolynomial (Fin 10) K) (hFne : F ≠ 0) (hF : F.IsHomogeneous 3)
    (D : ℕ) (Δ : MvPolynomial (Fin 50) K) (hΔ : Δ ≠ 0)
    (hdegree : Δ.totalDegree ≤ D) (hq : 2 * D < Nat.card K)
    (hsections : SmoothThreefoldSections F Δ) :
    |(affineZeroCount F : ℝ) - (Fintype.card K : ℝ) ^ 9| ≤
      15 * ((Fintype.card K : ℝ) - 1) *
        (Fintype.card K : ℝ) ^ ((13 : ℝ) / 2) := by
  have h := projective_bound weil F hFne hF D Δ hΔ hdegree hq hsections
  have hq1 : (1 : ℝ) ≤ Fintype.card K := by
    exact_mod_cast (show 1 ≤ Fintype.card K from Fintype.card_pos)
  have hcone := cone_error 8 (real_affine_cone_card F hF (by decide))
  rw [hcone, abs_mul, abs_of_nonneg (sub_nonneg.mpr hq1)]
  calc
    _ ≤ ((Fintype.card K : ℝ) - 1) *
        (15 * (Fintype.card K : ℝ) ^ ((13 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hq1)
    _ = _ := by ring

/-- A certificate for the ranks of the literal section Jacobian suffices;
the coordinate restriction and its smoothness are constructed internally. -/
theorem affine_bound_of_jacobian_certificate (weil : SmoothCubicWeil)
    (F : MvPolynomial (Fin 10) K) (hFne : F ≠ 0) (hF : F.IsHomogeneous 3)
    (D : ℕ) (Δ : MvPolynomial (Fin 50) K) (hΔ : Δ ≠ 0)
    (hdegree : Δ.totalDegree ≤ D) (hq : 2 * D < Nat.card K)
    (hcertificate : ∀ γ : Fin 5 → Fin 10 → K,
      eval (normalTupleCoordinates γ) Δ ≠ 0 → GoodJacobianTuple F γ) :
    |(affineZeroCount F : ℝ) - (Fintype.card K : ℝ) ^ 9| ≤
      15 * ((Fintype.card K : ℝ) - 1) *
        (Fintype.card K : ℝ) ^ ((13 : ℝ) / 2) := by
  apply affine_bound weil F hFne hF D Δ hΔ hdegree hq
  intro γ hγ
  exact smooth_threefold_coordinates F γ (hcertificate γ hγ)

/-- For finite-field counting only the field-rational parameter tuples
need to be certified, even when the certificate coefficients are geometric. -/
theorem affine_bound_of_geometric_jacobian_certificate (weil : SmoothCubicWeil)
    (F : MvPolynomial (Fin 10) K) (hFne : F ≠ 0) (hF : F.IsHomogeneous 3)
    (D : ℕ) (P : MvPolynomial (Fin 50) (AlgebraicClosure K)) (hP : P ≠ 0)
    (hdegree : P.totalDegree ≤ D) (hq : 2 * D < Nat.card K)
    (hcertificate : ∀ γ : Fin 5 → Fin 10 → K,
      eval (algebraMap K (AlgebraicClosure K) ∘ normalTupleCoordinates γ) P ≠ 0 →
        GoodJacobianTuple F γ) :
    |(affineZeroCount F : ℝ) - (Fintype.card K : ℝ) ^ 9| ≤
      15 * ((Fintype.card K : ℝ) - 1) *
        (Fintype.card K : ℝ) ^ ((13 : ℝ) / 2) := by
  obtain ⟨Δ, hΔ, hdegreeΔ, hnonvanishing⟩ :=
    PolynomialCertificateDescent.exists_nonzero_polynomial_certificate (K := K) P hP
  apply affine_bound_of_jacobian_certificate weil F hFne hF D Δ hΔ
    (hdegreeΔ.trans hdegree) hq
  intro γ hγ
  exact hcertificate γ (hnonvanishing (normalTupleCoordinates γ) hγ)

/-- A single integer coefficient preserves nonzeroness of a fixed integer
polynomial over every field of every remaining characteristic. -/
theorem exists_integer_certificate_nonzero_specialization {σ : Type*}
    (Δ : MvPolynomial σ ℤ) (hΔ : Δ ≠ 0) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ p : ℕ, ¬ p ∣ A →
      ∀ (E : Type*) [Field E] [CharP E p],
        map (Int.castRingHom E) Δ ≠ 0 ∧
        (map (Int.castRingHom E) Δ).totalDegree ≤ Δ.totalDegree := by
  classical
  obtain ⟨m, hm⟩ := Finsupp.support_nonempty_iff.mpr hΔ
  have hc : coeff m Δ ≠ 0 := mem_support_iff.mp hm
  refine ⟨(coeff m Δ).natAbs, Int.natAbs_pos.mpr hc, ?_⟩
  intro p hp E _ _
  have hcast : ((coeff m Δ : ℤ) : E) ≠ 0 := by
    intro hz
    have hd := (CharP.intCast_eq_zero_iff E p _).mp hz
    exact hp (by simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd)
  refine ⟨?_, ?_⟩
  · intro hz
    have h := congrArg (coeff m) hz
    exact hcast (by simpa only [coeff_map, Int.coe_castRingHom, coeff_zero] using h)
  · exact Finset.sup_mono (support_map_subset (Int.castRingHom E) Δ)

/-- A fixed integer Jacobian certificate yields the ambient count outside
one exceptional integer chosen before the prime and every finite extension.
The certificate's degree and exceptional integer may depend on F. -/
theorem exists_good_prime_affine_bound (weil : SmoothCubicWeil)
    (F : MvPolynomial (Fin 10) ℤ) (hFne : F ≠ 0) (hF : F.IsHomogeneous 3)
    (Δ : MvPolynomial (Fin 50) ℤ) (hΔ : Δ ≠ 0)
    (N : ℕ) (hN : 1 ≤ N)
    (hcertificate : ∀ p : ℕ, p.Prime → ¬ p ∣ N →
      ∀ (E : Type) [Field E] [Fintype E] [CharP E p]
        (γ : Fin 5 → Fin 10 → E),
      eval (normalTupleCoordinates γ) (map (Int.castRingHom E) Δ) ≠ 0 →
        GoodJacobianTuple (map (Int.castRingHom E) F) γ) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ A →
      ∀ (E : Type) [Field E] [Fintype E] [CharP E p],
        |(affineZeroCount (map (Int.castRingHom E) F) : ℝ) -
            (Fintype.card E : ℝ) ^ 9| ≤
          15 * ((Fintype.card E : ℝ) - 1) *
            (Fintype.card E : ℝ) ^ ((13 : ℝ) / 2) := by
  obtain ⟨B, hB, hgoodΔ⟩ := exists_integer_certificate_nonzero_specialization Δ hΔ
  obtain ⟨C, hC, hgoodF⟩ := exists_integer_certificate_nonzero_specialization F hFne
  let A := N * B * C * (2 * Δ.totalDegree).factorial
  refine ⟨A, Nat.one_le_iff_ne_zero.mpr (by
    dsimp [A]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by omega) (by omega)) (by omega))
      (Nat.factorial_ne_zero _)), ?_⟩
  intro p hp hpA E _ _ _
  letI : Fact p.Prime := ⟨hp⟩
  have hpN : ¬ p ∣ N := fun h ↦ hpA (dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h B) C) _)
  have hpB : ¬ p ∣ B := fun h ↦ hpA (dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h N) C) _)
  have hpC : ¬ p ∣ C := fun h ↦ hpA (dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_right h (N * B)) _)
  have hpf : ¬ p ∣ (2 * Δ.totalDegree).factorial := fun h ↦ hpA
    (dvd_mul_of_dvd_right h (N * B * C))
  obtain ⟨hΔE, hdegree⟩ := hgoodΔ p hpB E
  have hq : 2 * Δ.totalDegree < Nat.card E := by
    rw [Nat.card_eq_fintype_card]
    exact HomogeneousPrincipalOpen.cutoff_lt_card _ p hpf E
  exact affine_bound_of_jacobian_certificate weil _ (hgoodF p hpC E).1 (hF.map _)
    Δ.totalDegree _ hΔE hdegree hq (hcertificate p hp hpN E)

end CubicTenVariables.CubicFixedFamilySlicing

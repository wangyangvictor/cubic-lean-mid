import CubicTenVariables.CubicSurfaceFrameCertificate
import CubicTenVariables.CubicNonconicalHyperplaneCertificate
import CubicTenVariables.FrameRestrictionIrreducibility

/-! A geometric-integrality certificate in the coordinates of one actual
hyperplane normal. An integral characteristic-zero specialization supplies
a good normal in the first affine chart. Proved cubic irreducibility
openness then gives a polynomial over the original coefficient ring.
Nonvanishing preserves the literal canonical kernel restriction over every
target field. No finite-field selection or uniform degree bound is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace CubicTenVariables.CubicIntegralHyperplaneNormalCertificate
open MvPolynomial Literature HessianTheorem11.PolynomialRestriction
open CubicNonconicalHyperplaneCertificate

private theorem exists_eval_ne_zero {k : Type*} [Field k] [Infinite k] {σ : Type*}
    (P : MvPolynomial σ k) (hP : P ≠ 0) : ∃ x, eval x P ≠ 0 := by
  by_contra! h
  apply hP
  apply MvPolynomial.funext
  intro x
  simpa only [map_zero] using h x

/-- A nonempty full-frame polynomial open meets a literal normal chart,
with the first normal coefficient nonzero. This is over an infinite field;
it makes no assertion of a point over a finite field. -/
theorem exists_good_normal_chart
    {k : Type*} [Field k] [Infinite k] {n : ℕ}
    (Δ : MvPolynomial (Fin (n+1) × Fin n) k) (hΔ : Δ ≠ 0) :
    ∃ (u : Fin (n+1) → k) (M : Matrix (Fin n) (Fin n) k), u 0 ≠ 0 ∧
      eval (fun ij => GenericHyperplaneFrameOpen.chartFrame u M ij.1 ij.2) Δ ≠ 0 := by
  classical
  let P := GenericHyperplaneFrameOpen.pullback Δ
  have hP : P ≠ 0 := GenericHyperplaneFrameOpen.pullback_ne_zero Δ hΔ
  obtain ⟨a, ha⟩ := MvPolynomial.exists_coeff_ne_zero hP
  obtain ⟨u, hu⟩ := exists_eval_ne_zero (X 0 * coeff a P)
    (mul_ne_zero (X_ne_zero (0 : Fin (n+1))) ha)
  have hu' : u 0 ≠ 0 ∧ eval u (coeff a P) ≠ 0 := by
    simpa only [map_mul, eval_X, mul_ne_zero_iff] using hu
  have hPu : map (eval u) P ≠ 0 := by
    intro hz
    exact hu'.2 (by simpa only [coeff_map, coeff_zero] using congrArg (coeff a) hz)
  obtain ⟨m, hm⟩ := exists_eval_ne_zero (map (eval u) P) hPu
  let M : Matrix (Fin n) (Fin n) k := fun i j => m (i,j)
  refine ⟨u, M, hu'.1, ?_⟩
  have he := GenericHyperplaneFrameOpen.eval_pullback (eval u) M Δ
  have hc : (eval u : MvPolynomial (Fin (n+1)) k →+* k).comp C = RingHom.id k := by
    ext c
    simp
  rw [hc] at he
  have huX : (fun i => eval u (X i)) = u := by funext i; simp
  rw [huX] at he
  rw [eval_map] at hm
  exact fun hz => hm (he.trans hz)

/-- A characteristic-zero integral cubic specialization produces an honest
nonzero polynomial in one normal. All good later fibers use the displayed
canonical frame, whose range is exactly the kernel of that normal. -/
theorem exists_nonzero_certificate
    {R Ω : Type*} [CommRing R] [Field Ω] [CharZero Ω] [IsAlgClosed Ω]
    (r : ℕ) (ρ : R →+* Ω) (F : MvPolynomial (Fin (r+4)) R)
    (hF : F.IsHomogeneous 3) (hirr : Irreducible (map ρ F)) :
    ∃ Δ : MvPolynomial (Fin (r+4)) R, map ρ Δ ≠ 0 ∧
      ∀ (K : Type*) [Field K] (τ : R →+* K) (u : Fin (r+4) → K),
        eval₂Hom τ u Δ ≠ 0 →
          Function.Injective (frame u).mulVec ∧
          LinearMap.range (frame u).mulVecLin =
            LinearMap.ker (GenericHyperplaneFrameKernel.normal u) ∧
          (restrict (frame u) (map τ F)).IsHomogeneous 3 ∧
          (restrict (frame u) (map τ F)).totalDegree = 3 ∧
          GeometricallyIntegralForm (restrict (frame u) (map τ F)) := by
  classical
  obtain ⟨δ, hδ, hgood⟩ := CubicSurfaceFrameCertificate.exists_nonzero_hyperplane_certificate
    r ρ F hF hirr
  obtain ⟨u, M, hu, hM⟩ := exists_good_normal_chart (map ρ δ) hδ
  let B := GenericHyperplaneFrameOpen.chartFrame u M
  have hδB : eval₂Hom ρ (fun ij => B ij.1 ij.2) δ ≠ 0 := by
    simpa only [eval_map] using hM
  obtain ⟨hB, hBhom, _, hBI⟩ := hgood Ω ρ B hδB
  have hBirr : Irreducible (restrict B (map ρ F)) := by
    have hh := CubicSurfaceFrameCertificate.irreducible_of_geometricallyIntegral_specialization
      (RingHom.id Ω) Function.injective_id (restrict B (map ρ F)) hBhom
      (RingHom.id Ω) (by simpa only [map_id] using hBI)
    simpa only [map_id] using hh
  have hBcol (j : Fin (r+3)) : ∑ i, u i * B i j = 0 := by
    change ∑ i, u i * GenericHyperplaneFrameOpen.chartFrame u M i j = 0
    rw [Fin.sum_univ_succ]
    simp only [GenericHyperplaneFrameOpen.chartFrame, Fin.cons_zero, Fin.cons_succ]
    rw [mul_neg, Finset.mul_sum]
    have he : (∑ i, u i.succ * (u 0 * M i j)) = ∑ i, u 0 * (u i.succ * M i j) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he, neg_add_cancel]
  have hframeI : Irreducible (restrict (frame u) (map ρ F)) :=
    FrameRestrictionIrreducibility.irreducible_of_same_range (frame u) B
      (frame_injective u hu) hB
      ((frame_range u hu).trans
        (GenericHyperplaneFrameKernel.range_eq_ker u hu B hB hBcol).symm)
      (map ρ F) hBirr
  let ψ : MvPolynomial (Fin (r+4)) R →+* Ω := eval₂Hom ρ u
  have hψ : Irreducible (map ψ (family F)) := by
    rw [show ψ = eval₂Hom ρ u from rfl, specialize_family]
    exact hframeI
  obtain ⟨s, hs, hS⟩ := CubicIrreducibilityOpen.exists_geometrically_integral_principal_open
    ψ (family F) (family_homogeneous F hF) hψ
  refine ⟨X 0 * s, ?_, ?_⟩
  · have hnonzero : ψ (X 0 * s) ≠ 0 := by
      simpa only [map_mul, ψ, eval₂Hom_X'] using mul_ne_zero hu hs
    intro hz
    exact hnonzero (by
      change eval₂Hom ρ u (X 0 * s) = 0
      simpa only [eval_map, map_zero] using congrArg (eval u) hz)
  · intro K _ τ v hv
    have hh : v 0 ≠ 0 ∧ eval₂Hom τ v s ≠ 0 := by
      simpa only [map_mul, eval₂Hom_X', mul_ne_zero_iff] using hv
    have hcert := hS K (eval₂Hom τ v) hh.2
    rw [specialize_family] at hcert
    exact ⟨frame_injective v hh.1, frame_range v hh.1,
      homogeneous_restrict _ _ (hF.map τ), hcert⟩

end CubicTenVariables.CubicIntegralHyperplaneNormalCertificate

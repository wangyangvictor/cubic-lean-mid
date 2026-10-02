import CubicTenVariables.CubicGradientScaling
import CubicTenVariables.PadicPrimitive
import CubicTenVariables.PadicUnitOrbit
import CubicTenVariables.RationalHessianMinor

/-!
# Actual cubic geometry preserved on an integral unit orbit

Unit scaling preserves the p-adic norms of a cubic's selected first partial
and actual Hessian minor, the exact Hessian rank, and a selected integral
coordinate being a unit. Consequently the proved geometric properties of
a supplied congruence coset hold on its entire literal unit orbit. No zero
assertion is made for the coset or the orbit.
-/

noncomputable section
namespace CubicTenVariables.UnitOrbitGeometry

open MvPolynomial HessianTheorem11 RationalHessianMinor

/-- A selected size-r minor of the actual cubic Hessian scales by the r-th
power. The rows and columns are independent choices. -/
theorem eval₂_hessianMinor_smul
    {R S : Type*} [CommRing R] [CommRing S] {n r : ℕ}
    (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous 3) (f : R →+* S)
    (rows cols : Fin r → Fin n) (x : Fin n → S) (a : S) :
    eval₂ f (a • x) (hessianMinor F rows cols) =
      a ^ r * eval₂ f x (hessianMinor F rows cols) := by
  rw [eval₂_hessianMinor, eval₂_hessianMinor, hessian_smul (hF.map f)]
  change (a • (hessian (map f F) x).submatrix rows cols).det = _
  rw [Matrix.det_smul, Fintype.card_fin]

variable (p : ℕ) [Fact p.Prime]

/-- An integral unit has field norm exactly one. -/
theorem norm_coe_unit (u : ℤ_[p]ˣ) : ‖((u : ℤ_[p]) : ℚ_[p])‖ = 1 :=
  PadicInt.norm_units u

/-- Coercing an actual integral scalar multiple gives the same field
scalar multiple, coordinate by coordinate. -/
theorem coe_unit_smul {n : ℕ} (u : ℤ_[p]ˣ) (z : Fin n → ℤ_[p]) :
    (fun k => (((u : ℤ_[p]) • z) k : ℚ_[p])) =
      ((u : ℤ_[p]) : ℚ_[p]) • (fun k => (z k : ℚ_[p])) := rfl

/-- Unit scaling preserves the exact field norm of a selected formal
first partial of the actual integer cubic. -/
theorem norm_partial_unit_smul {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (i : Fin n) (u : ℤ_[p]ˣ) (z : Fin n → ℤ_[p]) :
    ‖eval₂ (Int.castRingHom ℚ_[p])
      (fun k => (((u : ℤ_[p]) • z) k : ℚ_[p])) (pderiv i F)‖ =
      ‖eval₂ (Int.castRingHom ℚ_[p]) (fun k => (z k : ℚ_[p])) (pderiv i F)‖ := by
  rw [coe_unit_smul, CubicGradientScaling.eval₂_partial_smul F hF,
    norm_mul, norm_pow, norm_coe_unit, one_pow, one_mul]

/-- Unit scaling preserves the exact field norm of a selected actual
Hessian minor, including a minor with different row and column selections. -/
theorem norm_minor_unit_smul {n r : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (rows cols : Fin r → Fin n) (u : ℤ_[p]ˣ) (z : Fin n → ℤ_[p]) :
    ‖eval₂ (Int.castRingHom ℚ_[p])
      (fun k => (((u : ℤ_[p]) • z) k : ℚ_[p])) (hessianMinor F rows cols)‖ =
      ‖eval₂ (Int.castRingHom ℚ_[p]) (fun k => (z k : ℚ_[p]))
        (hessianMinor F rows cols)‖ := by
  rw [coe_unit_smul, eval₂_hessianMinor_smul F hF,
    norm_mul, norm_pow, norm_coe_unit, one_pow, one_mul]

/-- Unit scaling preserves the exact actual Hessian rank. -/
theorem hessian_rank_unit_smul {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (u : ℤ_[p]ˣ) (z : Fin n → ℤ_[p]) :
    (hessian (map (Int.castRingHom ℚ_[p]) F)
      (fun k => (((u : ℤ_[p]) • z) k : ℚ_[p]))).rank =
      (hessian (map (Int.castRingHom ℚ_[p]) F) (fun k => (z k : ℚ_[p]))).rank := by
  rw [coe_unit_smul]
  apply PadicPrimitive.hessian_rank_smul_eq _ (hF.map _)
  apply norm_ne_zero_iff.mp
  rw [norm_coe_unit]
  exact one_ne_zero

/-- A specified integral unit coordinate stays a unit under domain unit scaling. -/
theorem isUnit_coordinate_unit_smul {n : ℕ}
    (u : ℤ_[p]ˣ) (z : Fin n → ℤ_[p]) (j : Fin n) (hj : IsUnit (z j)) :
    IsUnit (((u : ℤ_[p]) • z) j) :=
  u.isUnit.mul hj

set_option maxHeartbeats 800000 in
/-- Transfer the literal coset geometry to the whole literal unit orbit.
The exact norm reference remains the original center, and no assertion
that the surrounding points solve the cubic is added. -/
theorem coset_geometry_to_unitOrbit {n r : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (i j : Fin n) (rows cols : Fin r → Fin n)
    (ξ : Fin n → ℤ_[p]) (M R : ℕ)
    (hcoset : ∀ t : Fin n → ℤ_[p],
      let η := ξ + (p : ℤ_[p]) ^ M • t
      IsUnit (η j) ∧
      ‖eval₂ (Int.castRingHom ℚ_[p]) (fun k => (η k : ℚ_[p])) (pderiv i F)‖ =
        ‖eval₂ (Int.castRingHom ℚ_[p]) (fun k => (ξ k : ℚ_[p])) (pderiv i F)‖ ∧
      ‖eval₂ (Int.castRingHom ℚ_[p]) (fun k => (η k : ℚ_[p]))
        (hessianMinor F rows cols)‖ =
        ‖eval₂ (Int.castRingHom ℚ_[p]) (fun k => (ξ k : ℚ_[p]))
          (hessianMinor F rows cols)‖ ∧
      eval₂ (Int.castRingHom ℚ_[p]) (fun k => (η k : ℚ_[p])) (pderiv i F) ≠ 0 ∧
      eval₂ (Int.castRingHom ℚ_[p]) (fun k => (η k : ℚ_[p]))
        (hessianMinor F rows cols) ≠ 0 ∧
      R ≤ (hessian (map (Int.castRingHom ℚ_[p]) F) (fun k => (η k : ℚ_[p]))).rank) :
    ∀ η ∈ PadicUnitOrbit.unitOrbit p ξ M,
      IsUnit (η j) ∧
      ‖eval₂ (Int.castRingHom ℚ_[p]) (fun k => (η k : ℚ_[p])) (pderiv i F)‖ =
        ‖eval₂ (Int.castRingHom ℚ_[p]) (fun k => (ξ k : ℚ_[p])) (pderiv i F)‖ ∧
      ‖eval₂ (Int.castRingHom ℚ_[p]) (fun k => (η k : ℚ_[p]))
        (hessianMinor F rows cols)‖ =
        ‖eval₂ (Int.castRingHom ℚ_[p]) (fun k => (ξ k : ℚ_[p]))
          (hessianMinor F rows cols)‖ ∧
      eval₂ (Int.castRingHom ℚ_[p]) (fun k => (η k : ℚ_[p])) (pderiv i F) ≠ 0 ∧
      eval₂ (Int.castRingHom ℚ_[p]) (fun k => (η k : ℚ_[p]))
        (hessianMinor F rows cols) ≠ 0 ∧
      R ≤ (hessian (map (Int.castRingHom ℚ_[p]) F) (fun k => (η k : ℚ_[p]))).rank := by
  rintro η ⟨u, z, ⟨t, rfl⟩, rfl⟩
  obtain ⟨hj, hp, hd, hpne, hdne, hr⟩ := hcoset t
  refine ⟨isUnit_coordinate_unit_smul p u _ j hj,
    (norm_partial_unit_smul p F hF i u _).trans hp,
    (norm_minor_unit_smul p F hF rows cols u _).trans hd, ?_, ?_, ?_⟩
  · apply norm_ne_zero_iff.mp
    rw [norm_partial_unit_smul p F hF]
    exact norm_ne_zero_iff.mpr hpne
  · apply norm_ne_zero_iff.mp
    rw [norm_minor_unit_smul p F hF]
    exact norm_ne_zero_iff.mpr hdne
  · rw [hessian_rank_unit_smul p F hF]
    exact hr

end CubicTenVariables.UnitOrbitGeometry

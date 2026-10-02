import CubicTenVariables.IntegralHighRankLocalization
import CubicTenVariables.UnitGradientFibers
import CubicTenVariables.UnitOrbitGeometry

/-!
# Actual local data for an anisotropic ten-variable integer cubic

This record exposes every local geometric property and finite gradient
count on the literal unit orbit. Its existence theorem, proved below,
retains Pleasants only for initial p-adic solubility. The record is not
an axiom or a typeclass instance. The analytic complete-sum estimate and
positive local zero density are separate subsequent proof obligations.
-/

noncomputable section
namespace CubicTenVariables

open MvPolynomial HessianTheorem11 RationalHessianMinor
open IntegralGradientFibers LocalCongruenceFibers GradientTotalCount PadicUnitOrbit

attribute [local instance] Classical.propDecidable

structure PrimeLocalizationData (p : ℕ) [Fact p.Prime]
    (F : MvPolynomial (Fin 10) ℤ) where
  center : Fin 10 → ℤ_[p]
  partialIndex : Fin 10
  unitIndex : Fin 10
  minorSize : ℕ
  rows : Fin minorSize → Fin 10
  cols : Fin minorSize → Fin 10
  modulusExponent : ℕ
  lossExponent : ℕ
  unit_coordinate : center unitIndex = 1
  center_zero : eval₂ (Int.castRingHom ℚ_[p]) (fun k => (center k : ℚ_[p])) F = 0
  partial_ne_zero : eval₂ (Int.castRingHom ℚ_[p]) (fun k => (center k : ℚ_[p]))
    (pderiv partialIndex F) ≠ 0
  minorSize_ge_eight : 8 ≤ minorSize
  minorSize_eq_rank : minorSize =
    (hessian (map (Int.castRingHom ℚ_[p]) F) (fun k => (center k : ℚ_[p]))).rank
  modulus_positive : 1 ≤ modulusExponent
  minor_ne_zero : eval₂ (Int.castRingHom ℚ_[p]) (fun k => (center k : ℚ_[p]))
    (hessianMinor F rows cols) ≠ 0
  orbit_geometry : ∀ η ∈ unitOrbit p center modulusExponent,
    IsUnit (η unitIndex) ∧
    ‖eval₂ (Int.castRingHom ℚ_[p]) (fun k => (η k : ℚ_[p])) (pderiv partialIndex F)‖ =
      ‖eval₂ (Int.castRingHom ℚ_[p]) (fun k => (center k : ℚ_[p])) (pderiv partialIndex F)‖ ∧
    ‖eval₂ (Int.castRingHom ℚ_[p]) (fun k => (η k : ℚ_[p])) (hessianMinor F rows cols)‖ =
      ‖eval₂ (Int.castRingHom ℚ_[p]) (fun k => (center k : ℚ_[p])) (hessianMinor F rows cols)‖ ∧
    eval₂ (Int.castRingHom ℚ_[p]) (fun k => (η k : ℚ_[p])) (pderiv partialIndex F) ≠ 0 ∧
    eval₂ (Int.castRingHom ℚ_[p]) (fun k => (η k : ℚ_[p])) (hessianMinor F rows cols) ≠ 0 ∧
    8 ≤ (hessian (map (Int.castRingHom ℚ_[p]) F) (fun k => (η k : ℚ_[p]))).rank
  selected_fiber_bound : ∀ (s : ℕ) (u : (ZMod (p ^ s))ˣ)
    (b : Untouched cols → ZMod (p ^ s)) (c : Fin minorSize → ZMod (p ^ s)),
    Nat.card (unitModularFiber p F rows cols s (unitOrbit p center modulusExponent) u b c) ≤
      p ^ (modulusExponent + lossExponent * minorSize)
  full_gradient_bound : ∀ (s : ℕ) (u : (ZMod (p ^ s))ˣ) (c : Fin 10 → ZMod (p ^ s)),
    Nat.card (gradientFiber p F id s (unitOrbit p center modulusExponent) u c) ≤
      p ^ (modulusExponent + lossExponent * minorSize + s * (10 - minorSize))

namespace PrimeLocalizationData

variable {p : ℕ} [Fact p.Prime] {F : MvPolynomial (Fin 10) ℤ}

theorem center_ne_zero (D : PrimeLocalizationData p F) : D.center ≠ 0 := by
  intro h
  have hj := D.unit_coordinate
  rw [h, Pi.zero_apply] at hj
  exact zero_ne_one hj

theorem cols_injective (D : PrimeLocalizationData p F) : Function.Injective D.cols := by
  have hd := D.minor_ne_zero
  rw [eval₂_hessianMinor] at hd
  exact SelectedGradientCoordinates.cols_injective_of_submatrix_det_ne_zero _ _ _ hd

theorem minorSize_le_ten (D : PrimeLocalizationData p F) : D.minorSize ≤ 10 := by
  simpa using Fintype.card_le_of_injective D.cols D.cols_injective

theorem unit_invariant (D : PrimeLocalizationData p F) (u : ℤ_[p]ˣ) :
    (fun z => (u : ℤ_[p]) • z) '' unitOrbit p D.center D.modulusExponent =
      unitOrbit p D.center D.modulusExponent :=
  unit_smul_unitOrbit p D.center D.modulusExponent u

end PrimeLocalizationData

set_option maxHeartbeats 1200000 in
/-- Existence of the full actual local data, conditional only on the explicitly
displayed Pleasants theorem for initial local solubility. -/
theorem nonempty_primeLocalizationData
    (pleasants : Literature.Pleasants1971Theorem2Qp)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (p : ℕ) [Fact p.Prime] : Nonempty (PrimeLocalizationData p F) := by
  obtain ⟨ξ, i, j, r, rows, cols, M, A, hj, hzero, hi, hr, hrank, hM,
      hminor, hnorms, hcount⟩ :=
    IntegralHighRankLocalization.exists_integral_high_rank_localization pleasants F hF hA p
  have hdet : ((hessian (map (Int.castRingHom ℚ_[p]) F)
      (fun k => (ξ k : ℚ_[p]))).submatrix rows cols).det ≠ 0 := by
    rwa [← eval₂_hessianMinor]
  have hcols := SelectedGradientCoordinates.cols_injective_of_submatrix_det_ne_zero
    _ rows cols hdet
  have horbitCount : ∀ (s : ℕ) (u : (ZMod (p ^ s))ˣ)
      (b : Untouched cols → ZMod (p ^ s)) (c : Fin r → ZMod (p ^ s)),
      Nat.card (unitModularFiber p F rows cols s (unitOrbit p ξ M) u b c) ≤
        p ^ (M + A * r) := by
    intro s u b c
    simpa only [pow_add] using
      UnitGradientFibers.card_unitOrbit_fiber_le_of_coset_bound p F hF rows cols ξ M
        (p ^ (A * r)) hcount s u b c
  refine ⟨{
    center := ξ
    partialIndex := i
    unitIndex := j
    minorSize := r
    rows := rows
    cols := cols
    modulusExponent := M
    lossExponent := A
    unit_coordinate := hj
    center_zero := hzero
    partial_ne_zero := hi
    minorSize_ge_eight := hr
    minorSize_eq_rank := hrank
    modulus_positive := hM
    minor_ne_zero := hminor
    orbit_geometry := UnitOrbitGeometry.coset_geometry_to_unitOrbit p F hF i j
      rows cols ξ M 8 hnorms
    selected_fiber_bound := horbitCount
    full_gradient_bound := ?_
  }⟩
  intro s u c
  simpa only [pow_add] using card_full_gradientFiber_le p F rows cols hcols s
    (unitOrbit p ξ M) u c (p ^ (M + A * r))
    (fun b => horbitCount s u b (fun a => c (rows a)))

end CubicTenVariables

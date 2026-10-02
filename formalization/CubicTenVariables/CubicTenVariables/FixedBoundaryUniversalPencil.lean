import CubicTenVariables.FixedBoundaryPencilUniformity
import CubicTenVariables.CubicFactorCharts

/-! A literal finite universal coefficient family with prescribed boundary.
Its coefficient ring is a polynomial ring over the integers. The correction
`U - lift(boundary U) + b*lift(k)` makes the boundary identity exact while
retaining every homogeneous equation having boundary `b*k`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 600000
noncomputable section

namespace CubicTenVariables.FixedBoundaryUniversalPencil

open MvPolynomial TranslatedDepthSeven
open HessianTheorem11.PolynomialRestriction
open FixedLeadingFormIntegralShear FixedBoundaryPencilUniformity

def boundaryHom (R : Type*) [CommRing R] :
    MvPolynomial (Fin 4) R →+* MvPolynomial (Fin 3) R :=
  (aeval (linearForms (pencilFrame (0 : R)))).toRingHom

theorem boundaryHom_eq_restrict {R : Type*} [CommRing R]
    (F : MvPolynomial (Fin 4) R) :
    boundaryHom R F = restrict (pencilFrame (0 : R)) F := rfl

theorem boundaryHom_rename {R : Type*} [CommRing R]
    (f : MvPolynomial (Fin 3) R) :
    boundaryHom R (rename Fin.succ f) = f := by
  change aeval (linearForms (pencilFrame (0 : R))) (rename Fin.succ f) = f
  rw [aeval_rename]
  have he : (linearForms (pencilFrame (0 : R))) ∘ Fin.succ =
      (X : Fin 3 → MvPolynomial (Fin 3) R) := by
    funext i
    simp [linearForms, pencilFrame, graphFrame, Matrix.one_apply]
  rw [he, aeval_X_left_apply]

theorem map_boundaryHom {R K : Type*} [CommRing R] [CommRing K]
    (ρ : R →+* K) (F : MvPolynomial (Fin 4) R) :
    map ρ (boundaryHom R F) = boundaryHom K (map ρ F) := by
  rw [boundaryHom_eq_restrict, boundaryHom_eq_restrict, map_restrict,
    map_pencilFrame, map_zero]

abbrev CoefficientIndex (d : ℕ) := Option (CubicFactorCharts.Monomial 4 d)

abbrev CoefficientRing (d : ℕ) := MvPolynomial (CoefficientIndex d) ℤ

def genericHomogeneous (d : ℕ) : MvPolynomial (Fin 4) (CoefficientRing d) :=
  homogeneousComponent d
    (CubicFactorCharts.polynomial (fun m : CubicFactorCharts.Monomial 4 d =>
      X (some m)))

theorem genericHomogeneous_isHomogeneous (d : ℕ) :
    (genericHomogeneous d).IsHomogeneous d :=
  homogeneousComponent_isHomogeneous _ _

def coefficientSpecialization {K : Type*} [CommRing K] {d : ℕ}
    (F : MvPolynomial (Fin 4) K) (b : K) : CoefficientRing d →+* K :=
  eval₂Hom (Int.castRingHom K) (fun i => match i with
    | none => b
    | some m => coeff m.val F)

@[simp] theorem coefficientSpecialization_scalar {K : Type*} [CommRing K] {d : ℕ}
    (F : MvPolynomial (Fin 4) K) (b : K) :
    coefficientSpecialization (d := d) F b (X none) = b := by
  simp [coefficientSpecialization]

theorem specialize_genericHomogeneous {K : Type*} [CommRing K] {d : ℕ}
    (F : MvPolynomial (Fin 4) K) (b : K) (hF : F.IsHomogeneous d) :
    map (coefficientSpecialization (d := d) F b) (genericHomogeneous d) = F := by
  classical
  ext a
  rw [coeff_map]
  change coefficientSpecialization F b
    (coeff a (homogeneousComponent d
      (CubicFactorCharts.polynomial (fun m : CubicFactorCharts.Monomial 4 d =>
        X (some m))))) = coeff a F
  rw [coeff_homogeneousComponent]
  by_cases ha : a.degree = d
  · rw [if_pos ha, CubicFactorCharts.coeff_polynomial _ ⟨a, ha.le⟩]
    simp [coefficientSpecialization]
  · rw [if_neg ha, map_zero, hF.coeff_eq_zero ha]

def universal (d : ℕ) (k : MvPolynomial (Fin 3) ℤ) :
    MvPolynomial (Fin 4) (CoefficientRing d) :=
  genericHomogeneous d - rename Fin.succ (boundaryHom _ (genericHomogeneous d)) +
    C (X none) * rename Fin.succ (map (Int.castRingHom (CoefficientRing d)) k)

theorem universal_isHomogeneous {d : ℕ} (k : MvPolynomial (Fin 3) ℤ)
    (hk : k.IsHomogeneous d) : (universal d k).IsHomogeneous d := by
  apply IsHomogeneous.add
  · exact (genericHomogeneous_isHomogeneous d).sub
      (homogeneous_restrict _ _ (genericHomogeneous_isHomogeneous d)).rename_isHomogeneous
  · simpa only [zero_add] using (isHomogeneous_C (Fin 4)
      (X (none : CoefficientIndex d))).mul
      (hk.map (Int.castRingHom (CoefficientRing d))).rename_isHomogeneous

theorem universal_boundary (d : ℕ) (k : MvPolynomial (Fin 3) ℤ) :
    restrict (pencilFrame (0 : CoefficientRing d)) (universal d k) =
      C (X none) * map (Int.castRingHom (CoefficientRing d)) k := by
  change boundaryHom _ (universal d k) = _
  have hC : boundaryHom (CoefficientRing d) (C (X none)) = C (X none) := by
    simp [boundaryHom]
  simp only [universal, map_add, map_sub, map_mul, boundaryHom_rename, hC,
    sub_self, zero_add]

theorem specialize_universal {K : Type*} [CommRing K] {d : ℕ}
    (k : MvPolynomial (Fin 3) ℤ) (F : MvPolynomial (Fin 4) K) (b : K)
    (hF : F.IsHomogeneous d)
    (hboundary : restrict (pencilFrame (0 : K)) F =
      C b * map (Int.castRingHom K) k) :
    map (coefficientSpecialization (d := d) F b) (universal d k) = F := by
  let ρ := coefficientSpecialization (d := d) F b
  have hρ : ρ.comp (Int.castRingHom (CoefficientRing d)) = Int.castRingHom K :=
    RingHom.ext_int _ _
  change map ρ (universal d k) = F
  rw [universal, map_add, map_sub, map_mul, map_C, map_rename, map_boundaryHom,
    specialize_genericHomogeneous F b hF]
  rw [map_rename, map_map, hρ]
  have hρscalar : ρ (X none) = b := coefficientSpecialization_scalar F b
  rw [hρscalar]
  change F - rename Fin.succ (restrict (pencilFrame (0 : K)) F) +
    C b * rename Fin.succ (map (Int.castRingHom K) k) = F
  rw [hboundary, map_mul, rename_C]
  ring

/-- One integer and one degree bound precede the entire homogeneous family
over every good-characteristic field. The varying scalar and all remaining
coefficients are specialized only after these constants have been chosen. -/
theorem exists_uniform_certificate
    (integralityOpen : Literature.HomogeneousHypersurfaceIntegralityOpen)
    {d : ℕ} (hd : 1 ≤ d)
    (k : MvPolynomial (Fin 3) ℤ) (hk : k.IsHomogeneous d)
    (hirr : Published.IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k)) :
    ∃ N : ℕ, 0 < N ∧ ∃ D : ℕ,
      ∀ (K : Type) [Field K] (F : MvPolynomial (Fin 4) K) (b : K),
        F.IsHomogeneous d →
        restrict (pencilFrame (0 : K)) F = C b * map (Int.castRingHom K) k →
        (N : K) ≠ 0 → b ≠ 0 →
        ∃ Δ : MvPolynomial (Fin 1) K, Δ ≠ 0 ∧ Δ.totalDegree ≤ D ∧
          ∀ t : Fin 1 → K, eval t Δ ≠ 0 →
            (restrict (pencilFrame (t 0)) F).totalDegree = d ∧
            IsDomain (MvPolynomial (Fin 3) (AlgebraicClosure K) ⧸
              Ideal.span {map (algebraMap K (AlgebraicClosure K))
                (restrict (pencilFrame (t 0)) F)}) := by
  obtain ⟨N, hN, D, hcert⟩ := exists_uniform_pencil_certificate
    integralityOpen hd k hk hirr (universal d k) (universal_isHomogeneous k hk)
    (X none) (universal_boundary d k)
  refine ⟨N, hN, D, ?_⟩
  intro K _ F b hF hboundary hNK hb
  have hb' : coefficientSpecialization (d := d) F b (X none) ≠ 0 := by
    simpa using hb
  obtain ⟨Δ, hΔ, hdeg, hgood⟩ := hcert K (coefficientSpecialization F b) hNK hb'
  refine ⟨Δ, hΔ, hdeg, ?_⟩
  intro t ht
  have hh := hgood t ht
  rw [specialize_universal k F b hF hboundary] at hh
  exact hh

end CubicTenVariables.FixedBoundaryUniversalPencil

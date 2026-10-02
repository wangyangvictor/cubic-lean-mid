import CubicTenVariables.TenMicrolocalIncidence
import CubicTenVariables.PolynomialDivisorBound

/-! Bounds outside the actual integral equations of the microlocal depth
loci. The numerical depth is computed from the geometric fiber; no depth
bound or trace estimate is added as a hypothesis. In particular j=0 is
included. The only certificate used below is the already assembled
TenMicrolocalIncidence.Conclusion. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.MicrolocalOffDepthBound

open MvPolynomial HessianTheorem11
open BihomogeneousIncidenceFamily ProjectiveMicrolocalModels
open ProjectiveFourierIdentity

/-- Failure of the next positive-dimensional depth condition bounds the
actual truncated depth, including the empty-fiber case. -/
theorem depth_le_of_not_succ_le {m n : ℕ} {ι : Type*}
    (f : ι → MvPolynomial (Fin n) (MvPolynomial (Fin m) ℤ))
    (K : Type*) [Field K] (v : Fin m → K) (j : ℕ)
    (h : ¬ ((j+1 : ℕ) : Dimension) ≤
      IntegralGeometricFiberDepth.geometricFiberDimension f K v) :
    ProjectiveMicrolocalNumericalDepth.depth f K v ≤ j := by
  by_contra hneg
  have hs : ((j+1 : ℕ) : Dimension) ≤
      (ProjectiveMicrolocalNumericalDepth.depth f K v : Dimension) := by
    exact_mod_cast (show j+1 ≤ ProjectiveMicrolocalNumericalDepth.depth f K v by omega)
  rw [ProjectiveMicrolocalNumericalDepth.depth_eq_max] at hs
  rcases le_max_iff.mp hs with hs | hs
  · exact h hs
  · have hz : j+1 ≤ 0 := by exact_mod_cast hs
    omega

/-- Actual finite-field Fourier bound off the next depth locus. -/
theorem fourier_bound {t : ℕ} {F : MvPolynomial (Fin 10) ℤ}
    {f : Fin t → Polynomial 10 10} {N B : ℕ}
    (h : TenMicrolocalIncidence.Conclusion F f N B)
    (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ N)
    (K : Type) [Field K] [Fintype K] [CharP K p]
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) (v : Fin 10 → K) (hv : v ≠ 0)
    (j : ℕ) (hoff : ¬ ((j+1 : ℕ) : Dimension) ≤
      IntegralGeometricFiberDepth.geometricFiberDimension f K v) :
    ‖normalizedFourierSum ψ (map (Int.castRingHom K) F) v‖ ≤
      (1+2*(B : ℝ)) * (Fintype.card K : ℝ)^((9+(j : ℝ))/2) := by
  apply (h.fourier_bound p hp K ψ hψ v hv).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast (show 1 ≤ Fintype.card K from Fintype.card_pos)
  · have hd : (ProjectiveMicrolocalNumericalDepth.depth f K v : ℝ) ≤ (j : ℝ) :=
      Nat.cast_le.mpr (depth_le_of_not_succ_le f K v j hoff)
    linarith

/-- Actual prime-modulus complete sum off the next depth locus. -/
theorem prime_bound {t : ℕ} {F : MvPolynomial (Fin 10) ℤ}
    {f : Fin t → Polynomial 10 10} {N B : ℕ}
    (h : TenMicrolocalIncidence.Conclusion F f N B)
    (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ N)
    (v : Fin 10 → ℤ) (hv : (fun i => (v i : ZMod p)) ≠ 0)
    (j : ℕ) (hoff : ¬ ((j+1 : ℕ) : Dimension) ≤
      IntegralGeometricFiberDepth.geometricFiberDimension f (ZMod p)
        (fun i => (v i : ZMod p))) :
    ‖completeCubicSum F p v‖ ≤
      (1+2*(B : ℝ)) * (p : ℝ)^((11+(j : ℝ))/2) := by
  apply (h.prime_bound p hp v hv).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast (Fact.out : p.Prime).one_lt.le
  · have hd : (ProjectiveMicrolocalNumericalDepth.depth f (ZMod p)
        (fun i => (v i : ZMod p)) : ℝ) ≤ (j : ℝ) :=
      Nat.cast_le.mpr (depth_le_of_not_succ_le f (ZMod p) _ j hoff)
    linarith

/-- Choose the actual fixed homogeneous integer equations once, before
all primes, fields, characters and frequencies. Their reduction is the
exact geometric depth locus, and being outside their common zeros gives
the stated sharper bounds. -/
theorem exists_off_depth_equations {t : ℕ} {F : MvPolynomial (Fin 10) ℤ}
    {f : Fin t → Polynomial 10 10} {N B : ℕ}
    (h : TenMicrolocalIncidence.Conclusion F f N B) (j : ℕ) (hj : j ≤ 8) :
    ∃ (u : ℕ) (G : Fin u → MvPolynomial (Fin 10) ℤ) (d : Fin u → ℕ),
      (∀ i, (G i).IsHomogeneous (d i)) ∧
      IntegralModelDimension.geometricIdeal G = vanishingIdeal GeometricField
        (ProjectiveMicrolocalDepth.depth f (j+1)) ∧
      (∀ v : GeometricPoint 10, (∀ i, eval₂ (Int.castRingHom GeometricField) v (G i) = 0) ↔
        v ∈ ProjectiveMicrolocalDepth.depth f (j+1)) ∧
      ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ N →
        (∀ (K : Type) [Field K] [Fintype K] [CharP K p],
          (∀ v : Fin 10 → K, (∀ i, eval₂ (Int.castRingHom K) v (G i) = 0) ↔
            ((j+1 : ℕ) : Dimension) ≤ IntegralGeometricFiberDepth.geometricFiberDimension f K v) ∧
          ∀ (ψ : AddChar K ℂ), ψ ≠ 1 → ∀ (v : Fin 10 → K), v ≠ 0 →
            (∃ i, eval₂ (Int.castRingHom K) v (G i) ≠ 0) →
            ‖normalizedFourierSum ψ (map (Int.castRingHom K) F) v‖ ≤
              (1+2*(B : ℝ)) * (Fintype.card K : ℝ)^((9+(j : ℝ))/2)) ∧
        (∀ (v : Fin 10 → ℤ), (fun i => (v i : ZMod p)) ≠ 0 →
          (∃ i, eval₂ (Int.castRingHom (ZMod p)) (fun k => (v k : ZMod p)) (G i) ≠ 0) →
          ‖completeCubicSum F p v‖ ≤
            (1+2*(B : ℝ)) * (p : ℝ)^((11+(j : ℝ))/2)) := by
  obtain ⟨u,G,d,hd,hI,hgeo,hgood⟩ := h.depth_models ⟨j,by omega⟩
  refine ⟨u,G,d,hd,hI,hgeo,?_⟩
  intro p _ hp
  constructor
  · intro K _ _ _
    have he := (hgood p Fact.out hp K).1
    refine ⟨he,?_⟩
    intro ψ hψ v hv hoff
    apply fourier_bound h p hp K ψ hψ v hv j
    intro hdim
    obtain ⟨i,hi⟩ := hoff
    exact hi ((he v).mpr hdim i)
  · intro v hv hoff
    apply prime_bound h p hp v hv j
    intro hdim
    obtain ⟨i,hi⟩ := hoff
    exact hi (((hgood p Fact.out hp (ZMod p)).1 _).mpr hdim i)

end CubicTenVariables.MicrolocalOffDepthBound

import CubicTenVariables.ConductorNonzeroCoarse
import CubicTenVariables.ConductorCoarseWeightedSum
import CubicTenVariables.ConductorFixedFrequency

/-! The coarse actual cube-free pair sum at every nonzero integer
frequency. A nonzero coordinate supplies a positive exceptional integer;
its divisor count is absorbed by the actual frequency height. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ConductorNonzeroAverage
open MvPolynomial HessianTheorem11 ProjectiveMicrolocalData
open BihomogeneousIncidenceFamily ConductorFixedFrequency
open scoped BigOperators

theorem coordinate_natAbs_le_height (v : Fin 10 → ℤ) (i : Fin 10) :
    ((v i).natAbs : ℝ) ≤ frequencyHeight v := by
  have h := norm_le_pi_norm (fun j => (v j : ℝ)) i
  rw [Real.norm_eq_abs] at h
  have he : ((v i).natAbs : ℝ) = |(v i : ℝ)| := by
    simpa only [Int.cast_natCast,Int.cast_abs] using
      congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs (v i))
  rw [he]
  dsimp [frequencyHeight]
  linarith

/-- The data and the local constant are fixed before epsilon; the final
constant is uniform over the nonzero frequency and every finite modulus
pair family. No generic-frequency or radical restriction occurs. -/
theorem of_data
    (spread : CubicPrincipalOpenUniform.Uniform)
    (cubicWeil : Literature.SmoothCubicWeil)
    (ampl : Literature.CubicSurfacePointCountAmplification)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    {t : ℕ} (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (f : Fin t → Polynomial 10 10) (N B : ℕ) (hN : 1 ≤ N)
    (hgeo : Geometry F f) (hData : TenMicrolocalIncidence.Conclusion F f N B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ v : Fin 10 → ℤ, v ≠ 0 →
      ∀ D : ℝ, 1 ≤ D → ∀ Q : Finset (ℕ × ℕ),
      (∀ x ∈ Q, 1 ≤ x.1 ∧ 1 ≤ x.2 ∧ Squarefree x.1 ∧ Squarefree x.2 ∧
        x.1.Coprime x.2 ∧ (x.1 : ℝ)*(x.2 : ℝ)^2 ≤ 2*D) →
      (∑ x ∈ Q, ‖completeCubicSum F (x.1*x.2^2) v‖) ≤
        M*(D*frequencyHeight v)^ε*D^9 := by
  classical
  obtain ⟨C,hC,hpoint⟩ := ConductorNonzeroCoarse.of_data
    spread cubicWeil ampl pointcount F hF hAn f N B hN hgeo hData
  obtain ⟨M,hM,hbound⟩ := ConductorCoarseWeightedSum.exists_bound C hC ε hε
  refine ⟨M,hM,?_⟩
  intro v hv D hD Q hQ
  have hcoord : ∃ i : Fin 10, v i ≠ 0 := by
    by_contra! hz
    exact hv (funext hz)
  obtain ⟨i,hi⟩ := hcoord
  have hH : 1 ≤ frequencyHeight v := by
    dsimp [frequencyHeight]
    linarith [norm_nonneg (fun j => (v j : ℝ))]
  obtain ⟨hc,hpointv⟩ := hpoint v i hi
  calc
    _ ≤ ∑ x ∈ Q, C^(x.1.primeFactors.card+x.2.primeFactors.card)*
        (x.1 : ℝ)^8*(x.2 : ℝ)^17*(x.1.gcd (v i).natAbs : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      exact hpointv x.1 x.2 (hQ x hx).2.2.1 (hQ x hx).2.2.2.1
        (hQ x hx).2.2.2.2.1
    _ ≤ _ := hbound D (frequencyHeight v) hD hH (v i).natAbs hc
      (coordinate_natAbs_le_height v i) Q
      (fun x hx => ⟨(hQ x hx).1,(hQ x hx).2.1,(hQ x hx).2.2.2.2.2⟩)

/-- The listed literature hypotheses and proved prime-field count interface
construct the geometry and actual pair sum. No arithmetic average or
application-specific incidence conclusion is supplied. -/
theorem exists_bound
    (microlocal : Literature.ProjectiveMicrolocalCertificate)
    (spread : CubicPrincipalOpenUniform.Uniform)
    (cubicWeil : Literature.SmoothCubicWeil)
    (ampl : Literature.CubicSurfacePointCountAmplification)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ v : Fin 10 → ℤ, v ≠ 0 →
      ∀ D : ℝ, 1 ≤ D → ∀ Q : Finset (ℕ × ℕ),
      (∀ x ∈ Q, 1 ≤ x.1 ∧ 1 ≤ x.2 ∧ Squarefree x.1 ∧ Squarefree x.2 ∧
        x.1.Coprime x.2 ∧ (x.1 : ℝ)*(x.2 : ℝ)^2 ≤ 2*D) →
      (∑ x ∈ Q, ‖completeCubicSum F (x.1*x.2^2) v‖) ≤
        M*(D*frequencyHeight v)^ε*D^9 := by
  obtain ⟨t,f,N,B,hN,_hB,hgeo,hData⟩ := TenMicrolocalIncidenceData.exists_data
    microlocal F hF hAn
  exact of_data spread cubicWeil ampl pointcount F hF hAn f N B hN hgeo hData ε hε

end CubicTenVariables.ConductorNonzeroAverage

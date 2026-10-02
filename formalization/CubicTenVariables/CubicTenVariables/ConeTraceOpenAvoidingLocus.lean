import CubicTenVariables.HomogeneousClosedLocusAvoidance
import CubicTenVariables.FiniteHomogeneousConeTraceBounds
import CubicTenVariables.PrincipalOpenConeTopology

/-! A positive homogeneous principal trace open avoiding an actual closed
locus. The separator, open equation and common prime exclusion are all
constructed. The existing cone-trace hypotheses and proved integrality inputs remain explicit. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ConeTraceOpenAvoidingLocus
open MvPolynomial HessianTheorem11 ProjectiveFourierIdentity
open TranslatedDepthSeven FiniteFieldTraceCharacter PolynomialExponentialFamily
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every field refers to the same actual integer equation h and the same
exceptional integer N. The topology is that of the literal prime spectrum. -/
structure Conclusion {t u : ℕ} (F : ParameterPolynomial 10)
    (G : Fin t → ParameterPolynomial 10) (H : Fin u → ParameterPolynomial 10)
    (r w : ℕ) (h : ParameterPolynomial 10) (j N C : ℕ) : Prop where
  positive_degree : 0 < j
  homogeneous : h.IsHomogeneous j
  not_mem : map (Int.castRingHom ℚ) h ∉ baseIdeal G
  mem_excluded : map (Int.castRingHom ℚ) h ∈ baseIdeal H
  modulus_pos : 1 ≤ N
  constant_pos : 1 ≤ C
  residual_homogeneous :
    (ConePrincipalOpen.residualIdeal (baseIdeal G) (map (Int.castRingHom ℚ) h)).IsHomogeneous
      (homogeneousSubmodule (Fin 10) ℚ)
  residual_dimension : ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸
    ConePrincipalOpen.residualIdeal (baseIdeal G) (map (Int.castRingHom ℚ) h)) ≤
      (r : WithBot ℕ∞)
  residual_proper : PrimeSpectrum.zeroLocus
    (ConePrincipalOpen.residualIdeal (baseIdeal G) (map (Int.castRingHom ℚ) h) :
      Set (MvPolynomial (Fin 10) ℚ)) ⊂
        PrimeSpectrum.zeroLocus (baseIdeal G : Set (MvPolynomial (Fin 10) ℚ))
  open_nonempty :
    (PrincipalOpenConeTopology.locus (baseIdeal G) (map (Int.castRingHom ℚ) h)).Nonempty
  open_dense : closure (PrincipalOpenConeTopology.locus (baseIdeal G)
    (map (Int.castRingHom ℚ) h)) =
      PrimeSpectrum.zeroLocus (baseIdeal G : Set (MvPolynomial (Fin 10) ℚ))
  open_relative : IsOpen {x : PrimeSpectrum.zeroLocus
    (baseIdeal G : Set (MvPolynomial (Fin 10) ℚ)) |
      x.val ∈ PrincipalOpenConeTopology.locus (baseIdeal G) (map (Int.castRingHom ℚ) h)}
  avoidance : ∀ p : ℕ, ¬ p ∣ N →
    ∀ (K : Type*) [Field K] [CharP K p] (v : Fin 10 → K),
      eval v (map (Int.castRingHom K) h) ≠ 0 →
        ¬ (∀ a, eval v (map (Int.castRingHom K) (H a)) = 0)
  fourier_bound : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ N →
    ∀ (ψ : AddChar (ZMod p) ℂ), ψ ≠ 1 →
    ∀ (K : Type) [Field K] [Fintype K] [CharP K p] (v : Fin 10 → K),
      v ∈ parameterPoints G h K →
        ‖normalizedFourierSum (primeTraceCharacter p K ψ)
          (map (Int.castRingHom K) F) v‖ ≤
            (C : ℝ) * (Fintype.card K : ℝ)^((w : ℝ)/2)
  complete_sum_bound : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ N →
    ∀ v : Fin 10 → ℤ,
      (fun a => (v a : ZMod p)) ∈ parameterPoints G h (ZMod p) →
        ‖completeCubicSum F p v‖ ≤ (C : ℝ)*(p : ℝ)^((w : ℝ)/2+1)

/-- The same principal open is dense, avoids the given homogeneous closed
locus, and supports both literal trace estimates. No open or separator is
supplied as an assumption. -/
theorem exists_bound
    (degreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (weil : Literature.AffinePlaneCubicWeil)
    (dichotomy : Literature.ProperHyperplaneWeightDichotomy)
    (F : ParameterPolynomial 10) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    {t u : ℕ} (G : Fin t → ParameterPolynomial 10)
    (H : Fin u → ParameterPolynomial 10) (r d w : ℕ)
    (hprime : (baseIdeal G).IsPrime)
    (hgeometric : ((baseIdeal G).map
      (MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime)
    (hhom : (baseIdeal G).IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ))
    (hdegree : Published.HasProjectiveDimensionDegree (baseIdeal G) r d)
    (hsmall : r+d ≤ 8) (hweight : r+1+w+1 = 18)
    (hH : (baseIdeal H).IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ))
    (hnot : ¬ baseIdeal H ≤ baseIdeal G) :
    ∃ (h : ParameterPolynomial 10) (j N C : ℕ), Conclusion F G H r w h j N C := by
  obtain ⟨Q,e,D,hQ,hQH,hQI,hD,hreduce⟩ :=
    HomogeneousClosedLocusAvoidance.exists_equation_good_reduction
      (baseIdeal G) H hH hnot
  obtain ⟨hs,js,N,C,hdata,hN,hC,hfourier,hcomplete⟩ :=
    FiniteHomogeneousConeTraceBounds.exists_bounds_avoiding
      degreeSpan smooth spread weil dichotomy F hF hAn
      (fun _ : Fin 1 => t) (fun _ => G) (fun _ => r) (fun _ => d) (fun _ => w)
      (fun _ => hprime) (fun _ => hgeometric) (fun _ => hhom)
      (fun _ => hdegree) (fun _ => hsmall) (fun _ => hweight)
      (fun _ => Q) (fun _ => e) (fun _ => hQ) (fun _ => hQI)
  obtain ⟨hj,hh,hI,hQdiv,hresHom,hresDim,hresProper⟩ := hdata 0
  have hHmem : map (Int.castRingHom ℚ) (hs 0) ∈ baseIdeal H := by
    obtain ⟨a,ha⟩ := hQdiv
    rw [ha,map_mul]
    exact (baseIdeal H).mul_mem_right _ hQH
  have goodN (p : ℕ) (hp : ¬ p ∣ N*D) : ¬ p ∣ N :=
    fun h => hp (dvd_mul_of_dvd_left h D)
  have goodD (p : ℕ) (hp : ¬ p ∣ N*D) : ¬ p ∣ D :=
    fun h => hp (dvd_mul_of_dvd_right h N)
  refine ⟨hs 0,js 0,N*D,C,⟨hj,hh,hI,hHmem,
    one_le_mul_of_one_le_of_one_le hN hD,hC,hresHom,hresDim,hresProper,
    PrincipalOpenConeTopology.locus_nonempty _ hprime _ hI,
    PrincipalOpenConeTopology.closure_locus _ hprime _ hI,
    PrincipalOpenConeTopology.isOpen_relative _ _,?_,?_,?_⟩⟩
  · intro p hp K _ _ v hv hHv
    exact HomogeneousConeTraceRestriction.eval_ne_zero_of_dvd Q (hs 0) hQdiv K v hv
      (hreduce p (goodD p hp) K v hHv)
  · intro p _ hp ψ hψ K _ _ _ v hv
    exact hfourier p (goodN p hp) ψ hψ K 0 v hv
  · intro p _ hp v hv
    exact hcomplete p (goodN p hp) 0 v hv

end CubicTenVariables.ConeTraceOpenAvoidingLocus

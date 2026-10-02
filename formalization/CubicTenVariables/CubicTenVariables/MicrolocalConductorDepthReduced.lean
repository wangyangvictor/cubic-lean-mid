import CubicTenVariables.NumericalPrimeDepth
import CubicTenVariables.PrimePointwiseBoundsFromSurfacesReduced
import CubicTenVariables.PrimeSquarePointwiseBounds
import CubicTenVariables.MicrolocalRationalPartition
import CubicTenVariables.MicrolocalSquareRationalPartition
import CubicTenVariables.MicrolocalConductorDepth

/-! One constant for the actual numerical prime and prime-square depths,
the two rational partitions, and their exceptional integer certificates.
Large numerical depths imply membership in geometric congruence supports
(with the origin adjoined). Equality of numerical depths at frequencies
congruent modulo p is neither asserted nor needed. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.MicrolocalConductorDepthReduced
open MvPolynomial HessianTheorem11 TranslatedDepthSeven
open ProjectiveMicrolocalData NumericalPrimeDepth

/-- Reuse the established depth-certificate structure; only its prime
pointwise-bound constructor changes. -/
abbrev Conclusion {t : ℕ} (F : MvPolynomial (Fin 10) ℤ)
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (T : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1))
    (N : ℕ) (C : ℝ) (D : ℕ) (h : CoarseBounds F C) : Prop :=
  MicrolocalConductorDepth.Conclusion F f T N C D h

/-- Enlarge constants before taking least numerical depths. The Q data
are constructed from the same incidence already used for P. -/
theorem of_partition
    (spread : CubicPrincipalOpenUniform.Uniform)
    (cubicWeil : Literature.SmoothCubicWeil)
    (isolated : CubicSurfacePointCountReduced.IsolatedConjugateCubicSurfacePointCount)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    {t : ℕ} (F : MvPolynomial (Fin 10) ℤ) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10) (N B : ℕ)
    (T : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1))
    (hP : MicrolocalRationalPartition.Conclusion F f N B T) :
    MicrolocalSquareRationalPartition.Conclusion F f N B ∧
    ∃ (C : ℝ) (D : ℕ) (h : CoarseBounds F C), Conclusion F f T N C D h := by
  classical
  have hQ := MicrolocalSquareRationalPartition.of_data pointcount F hhom hAn f N B
    hP.modulus_pos hP.betti_pos hP.geometry hP.incidence
  obtain ⟨A,hA,hprime⟩ := PrimePointwiseBoundsFromSurfacesReduced.exists_uniform_bound spread isolated cubicWeil F hhom hAn
  obtain ⟨Cs,hCs,hsquare,hlocal⟩ := PrimeSquarePointwiseBounds.of_data pointcount
    F hhom hAn f N B hP.modulus_pos hP.geometry hP.incidence
  obtain ⟨CP,DP,hCP,hpcert⟩ := hP.certificates
  obtain ⟨CQ,DQ,hCQ,hqcert⟩ := hQ.certificates
  let C : ℝ := A+Cs+CP+CQ+(1+2*(B : ℝ))
  let D : ℕ := DP+DQ
  have hB0 : 0 ≤ (B : ℝ) := Nat.cast_nonneg B
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hAC : A ≤ C := by dsimp [C]; linarith
  have hCsC : Cs ≤ C := by dsimp [C]; linarith
  have hCPC : CP ≤ C := by dsimp [C]; linarith
  have hCQC : CQ ≤ C := by dsimp [C]; linarith
  have hBC : 1+2*(B : ℝ) ≤ C := by dsimp [C]; linarith
  have h : CoarseBounds F C := by
    refine ⟨hC,?_,?_⟩
    · intro p hp v
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
      have hb : ‖completeCubicSum F p v‖ ≤ A*(p : ℝ)^((17 : ℝ)/2) := by
        by_cases hv : (fun i => (v i : ZMod p)) = 0
        · exact (hprime p hp.out v).1 hv
        · apply ((hprime p hp.out v).2 hv).trans
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num)
      exact hb.trans (mul_le_mul_of_nonneg_right hAC (by positivity))
    · intro p _ v
      exact (hsquare p v).trans (mul_le_mul_of_nonneg_right hCsC (by positivity))
  refine ⟨hQ,C,D,h,?_,?_,?_⟩
  · intro j v hv
    obtain ⟨Δ,hΔ,hheight,hcert⟩ := hpcert j v hv
    refine ⟨Δ,hΔ,?_,prime_certificate h v Δ j.val CP hCPC hcert⟩
    intro H hH hvH
    exact (hheight H hH hvH).trans
      (mul_le_mul hCPC (pow_le_pow_right₀ hH (by dsimp [D]; omega))
        (by positivity) (by linarith))
  · intro j v hv
    obtain ⟨Δ,hΔ,hheight,hcert⟩ := hqcert j v hv
    refine ⟨Δ,hΔ,?_,square_certificate h v Δ j.val CQ hCQC hcert⟩
    intro H hH hvH
    exact (hheight H hH hvH).trans
      (mul_le_mul hCQC (pow_le_pow_right₀ hH (by dsimp [D]; omega))
        (by positivity) (by linarith))
  · intro p hp hpN v j hj hdepth
    by_cases hv : (fun i => (v i : ZMod p)) = 0
    · exact Or.inl hv
    right
    obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    by_contra hoff
    rcases hdepth with he | hs
    · have hb := MicrolocalOffDepthBound.prime_bound hP.incidence p hpN v hv r hoff
      have hd := (primeDepth_le_iff h p v r).mpr
        (hb.trans (mul_le_mul_of_nonneg_right hBC (by positivity)))
      omega
    · have hb := hlocal p v hv r hoff
      have hd := (squareDepth_le_iff h p v r).mpr
        (hb.trans (mul_le_mul_of_nonneg_right hCsC (by positivity)))
      omega

/-- All common data are produced from the named general premises; no
partition, sum estimate, depth divisibility, or support implication is an
unproved application input. This is preparation for the conductor averages,
not a proof of those averages. -/
theorem exists_data
    (microlocal : Literature.ProjectiveMicrolocalCertificate)
    (degreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (weil : Literature.AffinePlaneCubicWeil)
    (dichotomy : Literature.ProperHyperplaneWeightDichotomy)
    (salberger : Published.Salberger2023Theorem04)
    (integrality : CubicPrincipalOpenUniform.Uniform)
    (cubicWeil : Literature.SmoothCubicWeil)
    (isolated : CubicSurfacePointCountReduced.IsolatedConjugateCubicSurfacePointCount)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    (F : MvPolynomial (Fin 10) ℤ) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ (t : ℕ) (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10) (N B : ℕ)
      (T : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)),
      MicrolocalRationalPartition.Conclusion F f N B T ∧
      MicrolocalSquareRationalPartition.Conclusion F f N B ∧
      ∃ (C : ℝ) (D : ℕ) (h : CoarseBounds F C), Conclusion F f T N C D h := by
  obtain ⟨t,f,N,B,T,hP⟩ := MicrolocalRationalPartition.exists_partition microlocal
    degreeSpan smooth spread weil dichotomy salberger F hhom hAn
  exact ⟨t,f,N,B,T,hP,of_partition integrality cubicWeil isolated pointcount F hhom hAn f N B T hP⟩

end CubicTenVariables.MicrolocalConductorDepthReduced

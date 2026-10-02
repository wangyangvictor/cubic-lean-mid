import CubicTenVariables.ConeTraceOpenAvoidingLocus
import CubicTenVariables.HomogeneousPrimeDegree
import CubicTenVariables.ConeComponentProgressionCount

/-! Construct a principal-open promotion for each actual cone component.
A zero equation disables components which are too small, have large degree,
or lie in the next depth locus. Every remaining component receives an
actual positive homogeneous trace open, with a smaller-dimensional residual.
The existing cone-trace hypotheses and proved integrality inputs are used. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.MicrolocalPromotionChoice
open MvPolynomial HessianTheorem11 ProjectiveFourierIdentity
open TranslatedDepthSeven FiniteFieldTraceCharacter PolynomialExponentialFamily
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Explicit component alternatives. Degree is the actual Hilbert degree. -/
def Cases {t u : ℕ} (G : Fin t → ParameterPolynomial 10)
    (H : Fin u → ParameterPolynomial 10) (j : ℕ) (h : ParameterPolynomial 10) : Prop :=
  ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸ baseIdeal G) ≤ ((8-j : ℕ) : WithBot ℕ∞) ∨
  (∃ d, Published.HasProjectiveDimensionDegree (baseIdeal G) (8-j) d ∧ j < d) ∨
  baseIdeal H ≤ baseIdeal G ∨
  ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸
    ConePrincipalOpen.residualIdeal (baseIdeal G) (map (Int.castRingHom ℚ) h)) ≤
      ((8-j : ℕ) : WithBot ℕ∞)

structure Choice {t u : ℕ} (F : ParameterPolynomial 10)
    (G : Fin t → ParameterPolynomial 10) (H : Fin u → ParameterPolynomial 10)
    (j : ℕ) (h : ParameterPolynomial 10) (e N C : ℕ) : Prop where
  positive_degree : 0 < e
  homogeneous : h.IsHomogeneous e
  mem_excluded : map (Int.castRingHom ℚ) h ∈ baseIdeal H
  modulus_pos : 1 ≤ N
  constant_pos : 1 ≤ C
  cases : Cases G H j h
  fourier_bound : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ N →
    ∀ (ψ : AddChar (ZMod p) ℂ), ψ ≠ 1 →
    ∀ (K : Type) [Field K] [Fintype K] [CharP K p] (v : Fin 10 → K),
      v ∈ parameterPoints G h K →
        ‖normalizedFourierSum (primeTraceCharacter p K ψ)
          (map (Int.castRingHom K) F) v‖ ≤
            (C : ℝ) * (Fintype.card K : ℝ)^(((8+j : ℕ) : ℝ)/2)
  complete_sum_bound : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ N →
    ∀ v : Fin 10 → ℤ,
      (fun a => (v a : ZMod p)) ∈ parameterPoints G h (ZMod p) →
        ‖completeCubicSum F p v‖ ≤ (C : ℝ)*(p : ℝ)^(((8+j : ℕ) : ℝ)/2+1)

private theorem zero_choice {t u : ℕ} (F : ParameterPolynomial 10)
    (G : Fin t → ParameterPolynomial 10) (H : Fin u → ParameterPolynomial 10)
    (j : ℕ) (hc : Cases G H j 0) : Choice F G H j 0 1 1 1 := by
  refine ⟨by decide, by simpa using (MvPolynomial.isHomogeneous_zero (Fin 10) ℤ 1), by simp, le_rfl, le_rfl, hc, ?_, ?_⟩
  · intro p _ hp ψ hψ K _ _ _ v hv
    have hn := ((mem_parameterPoints G 0 K v).mp hv).2
    simp at hn
  · intro p _ hp v hv
    have hn := ((mem_parameterPoints G 0 (ZMod p) _).mp hv).2
    simp at hn

/-- Actual promotion equations are chosen, including disabled components;
no Hilbert degree, low-degree classification or open is assumed. -/
theorem exists_choice
    (degreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (weil : Literature.AffinePlaneCubicWeil)
    (dichotomy : Literature.ProperHyperplaneWeightDichotomy)
    (F : ParameterPolynomial 10) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    {t u : ℕ} (G : Fin t → ParameterPolynomial 10)
    (H : Fin u → ParameterPolynomial 10) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ 4)
    (hprime : (baseIdeal G).IsPrime)
    (hgeometric : ((baseIdeal G).map
      (MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime)
    (hhom : (baseIdeal G).IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ))
    (hdim : ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸ baseIdeal G) ≤
      ((9-j : ℕ) : WithBot ℕ∞))
    (hH : (baseIdeal H).IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ)) :
    ∃ (h : ParameterPolynomial 10) (e N C : ℕ), Choice F G H j h e N C := by
  classical
  by_cases hlow : ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸ baseIdeal G) ≤
      ((8-j : ℕ) : WithBot ℕ∞)
  · exact ⟨0,1,1,1,zero_choice F G H j (Or.inl hlow)⟩
  have heqdim : ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸ baseIdeal G) =
      (((8-j)+1 : ℕ) : WithBot ℕ∞) := by
    apply le_antisymm
    · simpa only [show 8-j+1 = 9-j by omega] using hdim
    · have hlt := lt_of_not_ge hlow
      simpa only [Nat.cast_add,Nat.cast_one] using WithBot.add_one_le_iff.mpr hlt
  obtain ⟨d,hd,hdegree⟩ := HomogeneousPrimeDegree.exists_degree (baseIdeal G) hprime hhom heqdim
  by_cases hlarge : j < d
  · exact ⟨0,1,1,1,zero_choice F G H j (Or.inr (Or.inl ⟨d,hdegree,hlarge⟩))⟩
  by_cases hcontained : baseIdeal H ≤ baseIdeal G
  · exact ⟨0,1,1,1,zero_choice F G H j (Or.inr (Or.inr (Or.inl hcontained)))⟩
  obtain ⟨h,e,N,C,hdata⟩ := ConeTraceOpenAvoidingLocus.exists_bound.{0}
    degreeSpan smooth spread weil dichotomy F hF hAn G H (8-j) d (8+j)
    hprime hgeometric hhom hdegree (by omega) (by omega) hH hcontained
  exact ⟨h,e,N,C,⟨hdata.positive_degree,hdata.homogeneous,hdata.mem_excluded,
    hdata.modulus_pos,hdata.constant_pos,Or.inr (Or.inr (Or.inr hdata.residual_dimension)),
    hdata.fourier_bound,hdata.complete_sum_bound⟩⟩

/-- At the two high counting levels these actual alternatives have exactly
the lower-dimensional/high-degree/residual form needed by the finite cover. -/
theorem cases_for_high_levels {t u : ℕ} {F : ParameterPolynomial 10}
    {G : Fin t → ParameterPolynomial 10} {H : Fin u → ParameterPolynomial 10}
    {j e N C : ℕ} {h : ParameterPolynomial 10} (hc : Choice F G H j h e N C)
    (hj : j = 3 ∨ j = 4) (hprime : (baseIdeal G).IsPrime)
    (hgeom : GeometricallyPrimeMvPolynomialIdeal (baseIdeal G))
    (hhom : (baseIdeal G).IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ)) :
    ConeComponentProgressionCount.ComponentCondition (8-j) (baseIdeal G) ∨
    baseIdeal H ≤ baseIdeal G ∨
    (0 < e ∧ h.IsHomogeneous e ∧
      ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸
        ConePrincipalOpen.residualIdeal (baseIdeal G) (map (Int.castRingHom ℚ) h)) ≤
          ((8-j : ℕ) : WithBot ℕ∞)) := by
  rcases hc.cases with hlow | ⟨d,hdegree,hd⟩ | hcontained | hres
  · exact Or.inl ⟨hprime.ne_top,hhom,Or.inl hlow⟩
  · exact Or.inl ⟨hprime.ne_top,hhom,Or.inr ⟨d,hprime,hgeom,hdegree,by omega⟩⟩
  · exact Or.inr (Or.inl hcontained)
  · exact Or.inr (Or.inr ⟨hc.positive_degree,hc.homogeneous,hres⟩)

end CubicTenVariables.MicrolocalPromotionChoice

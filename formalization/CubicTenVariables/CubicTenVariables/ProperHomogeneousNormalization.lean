import TranslatedDepthSeven.HomogeneousLinearNormalizationBoxCount

/-!
# Linear normalization of proper homogeneous ideals

The homogeneous elimination argument needs a nonzero quotient, not a domain.
This generalization retains the existing normalization datum with actual
homogeneous degree-one forms, an injective map and a finite module extension.
No radicality, primeness or geometric input is assumed.
-/

noncomputable section
namespace CubicTenVariables.ProperHomogeneousNormalization
open MvPolynomial TranslatedDepthSeven

universe u v
variable {K : Type u} [Field K]

local instance {σ : Type v} :
    GradedAlgebra (MvPolynomial.homogeneousSubmodule σ K) :=
  MvPolynomial.gradedAlgebra

/-- Every proper homogeneous ideal over an infinite field has a finite
injective normalization represented by actual linear homogeneous forms. -/
theorem exists_homogeneousLinearNormalizationData
    [Infinite K] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (hproper : I ≠ ⊤)
    (hhom : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) K)) :
    Nonempty (HomogeneousLinearNormalizationData I) := by
  induction n with
  | zero =>
      have hbot : I = ⊥ :=
        ideal_eq_bot_of_isEmpty I hproper
      subst I
      exact ⟨homogeneousLinearNormalizationDataBot 0⟩
  | succ n ih =>
      by_cases hbot : I = ⊥
      · subst I
        exact ⟨homogeneousLinearNormalizationDataBot (n + 1)⟩
      · let e : Fin (n + 1) ≃ Option (Fin n) := _root_.finSuccEquiv n
        let T : MvPolynomial (Fin (n + 1)) K ≃ₐ[K]
            MvPolynomial (Option (Fin n)) K :=
          MvPolynomial.renameEquiv K e
        let J : Ideal (MvPolynomial (Option (Fin n)) K) := I.map T
        have hJhom : J.IsHomogeneous
            (MvPolynomial.homogeneousSubmodule (Option (Fin n)) K) := by
          simpa [J, T] using map_renameEquiv_isHomogeneous e I hhom
        have hJne : J ≠ ⊥ := by
          dsimp only [J, T]
          exact (Ideal.map_eq_bot_iff_of_injective
            (MvPolynomial.renameEquiv K e).injective).not.mpr hbot
        have hJproper : J ≠ ⊤ := by
          intro htop
          apply hproper
          calc
            I = J.comap T := (Ideal.comap_map_of_bijective T T.bijective).symm
            _ = ⊤ := by rw [htop, Ideal.comap_top]
        obtain ⟨f, d, hfJ, hfhom, hfne⟩ :=
          exists_nonzero_isHomogeneous_mem_of_isHomogeneous_ne_bot
            J hJhom hJne
        obtain ⟨c, hcfinite, -⟩ :=
          exists_finite_homogeneousLinearEliminationHom
            J f d hfJ hfhom hfne
        let h : MvPolynomial (Fin n) K →ₐ[K]
            (MvPolynomial (Option (Fin n)) K ⧸ J) :=
          homogeneousLinearEliminationHom c J
        let l : Fin n → MvPolynomial (Option (Fin n)) K :=
          homogeneousLinearEliminationForm c
        have hh : h = (Ideal.Quotient.mkₐ K J).comp (aeval l) := by
          apply MvPolynomial.algHom_ext
          intro i
          simp [h, l, homogeneousLinearEliminationHom_X,
            homogeneousLinearEliminationForm]
        have hhfinite : h.Finite := by
          simpa [h] using hcfinite
        let P : Ideal (MvPolynomial (Fin n) K) := RingHom.ker h
        have hPhom : P.IsHomogeneous
            (MvPolynomial.homogeneousSubmodule (Fin n) K) := by
          simpa [P, h] using
            kernel_homogeneousLinearEliminationHom_isHomogeneous
              c J hJhom
        letI : Nontrivial (MvPolynomial (Option (Fin n)) K ⧸ J) :=
          Ideal.Quotient.nontrivial_iff.mpr hJproper
        have hPproper : P ≠ ⊤ := RingHom.ker_ne_top h
        obtain ⟨D⟩ := ih P hPproper hPhom
        have hl : ∀ i, (l i).IsHomogeneous 1 := by
          intro i
          exact homogeneousLinearEliminationForm_isHomogeneous c i
        let DJ : HomogeneousLinearNormalizationData J :=
          { parameterCount := D.parameterCount
            forms := fun i ↦ aeval l (D.forms i)
            forms_isHomogeneous := fun i ↦ by
              simpa using (D.forms_isHomogeneous i).aeval l hl
            injective := by
              rw [← kerLift_comp_normalizationHom J l h hh
                D.parameterCount D.forms]
              exact (Ideal.kerLiftAlg_injective h).comp D.injective
            finite := by
              rw [← kerLift_comp_normalizationHom J l h hh
                D.parameterCount D.forms]
              exact AlgHom.Finite.comp
                (kerLiftAlg_finite_of_finite h hhfinite) D.finite }
        exact ⟨DJ.renameEquiv e I⟩

/-- The parameter count of any such normalization is bounded by an upper
bound for the dimension of the actual quotient, even for nonreduced rings. -/
theorem parameterCount_le {σ : Type v} (I : Ideal (MvPolynomial σ K))
    (D : HomogeneousLinearNormalizationData I) (r : ℕ)
    (hdim : ringKrullDim (MvPolynomial σ K ⧸ I) ≤ (r : WithBot ℕ∞)) :
    D.parameterCount ≤ r := by
  letI : Nontrivial (MvPolynomial σ K ⧸ I) := D.hom_injective.nontrivial
  apply Nat.le_of_lt_succ
  apply normalization_parameter_lt_of_ringKrullDim_lt_nat
    D.hom D.hom_injective D.hom_finite.to_isIntegral
  exact lt_of_le_of_lt hdim (by exact_mod_cast Nat.lt_succ_self r)

/-- Proper homogeneous ideals admit literal linear normalization with at
most the stated quotient-dimension bound many parameters. -/
theorem exists_homogeneousLinearNormalizationData_parameterCount_le
    [Infinite K] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (hproper : I ≠ ⊤)
    (hhom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (r : ℕ)
    (hdim : ringKrullDim (MvPolynomial (Fin n) K ⧸ I) ≤ (r : WithBot ℕ∞)) :
    ∃ D : HomogeneousLinearNormalizationData I, D.parameterCount ≤ r := by
  obtain ⟨D⟩ := exists_homogeneousLinearNormalizationData n I hproper hhom
  exact ⟨D, parameterCount_le I D r hdim⟩

end CubicTenVariables.ProperHomogeneousNormalization

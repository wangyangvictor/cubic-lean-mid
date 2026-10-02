import TranslatedDepthSeven.HomogeneousHypersurfaceHilbertBoundInternal
import TranslatedDepthSeven.BoundedFirstChartHilbertInternal

/-!
# A proper form cuts a projective curve in length at most its degree product

This proves the exact rational first-chart input from the manuscript's
Hilbert-function definition.  The proof uses injective multiplication by
the form, rank-nullity, and dehomogenization.  No Bezout theorem, component
decomposition, generic projection, or point-count estimate is an input.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

/-- A bound for homogeneous quotient pieces bounds the size of a spanning
family of the reduced first-chart coordinate algebra.  This works for an
arbitrary ideal, including a nonreduced or empty section. -/
theorem exists_rationalFirstChart_spanningFamily_of_eventual_bounded_hilbert
    {N d : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (k₀ : ℕ)
    (hbounded : ∀ k ≥ k₀,
      Module.finrank ℚ (quotientHomogeneousComponent ℚ (Fin (N + 1)) I k) ≤ d) :
    ∃ v : Fin d → (MvPolynomial (Fin (N + 1)) ℚ ⧸
        rationalFirstAffineChartReducedIdeal I),
      Submodule.span ℚ (Set.range v) = ⊤ := by
  let R := MvPolynomial (Fin (N + 1)) ℚ
  let J₀ := rationalFirstAffineChartReducedIdeal I
  have hI_le : I ≤ J₀ := le_trans le_sup_left Ideal.le_radical
  have hXone : X (0 : Fin (N + 1)) - C (1 : ℚ) ∈ J₀ := by
    apply Ideal.le_radical
    exact (show Ideal.span ({X (0 : Fin (N + 1)) - C (1 : ℚ)} : Set R) ≤
      I ⊔ Ideal.span ({X (0 : Fin (N + 1)) - C (1 : ℚ)} : Set R)
      from le_sup_right) (Ideal.subset_span (Set.mem_singleton _))
  let e : R ≃ₐ[ℚ] MvPolynomial (Option (Fin N)) ℚ :=
    MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv N)
  let J := I.map e
  let C₀ := J.map multivariateDehomogenization.toRingHom
  have hAffBound : ∀ k ≥ k₀,
      Module.finrank ℚ (affineHilbertFiltration ℚ N C₀ k) ≤ d := by
    intro k hk
    calc
      Module.finrank ℚ (affineHilbertFiltration ℚ N C₀ k) ≤
          Module.finrank ℚ (quotientHomogeneousComponent ℚ (Option (Fin N)) J k) :=
        finrank_affine_dehomogenization_le_projective J
      _ = Module.finrank ℚ (quotientHomogeneousComponent ℚ (Fin (N + 1)) I k) :=
        (finrank_quotientHomogeneousComponent_map_renameEquiv
          ℚ (_root_.finSuccEquiv N) I k).symm
      _ ≤ d := hbounded k hk
  obtain ⟨v, hv⟩ :=
    exists_affineQuotient_spanningFamily_of_eventual_bounded_hilbert C₀ k₀ hAffBound
  let B := R ⧸ J₀
  let mk : R →ₐ[ℚ] B := Ideal.Quotient.mkₐ ℚ J₀
  let phi : MvPolynomial (Fin N) ℚ →ₐ[ℚ] B :=
    MvPolynomial.aeval fun i ↦ mk (X i.succ)
  have hmkX : mk (X (0 : Fin (N + 1))) = 1 := by
    have hz : mk (X (0 : Fin (N + 1)) - C (1 : ℚ)) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 hXone
    simpa only [map_sub, map_one, MvPolynomial.C_1, sub_eq_zero] using hz
  have hcomposition :
      phi.comp (multivariateDehomogenization.comp e.toAlgHom) = mk := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · change phi (multivariateDehomogenization
        (MvPolynomial.rename (_root_.finSuccEquiv N) (X (0 : Fin (N + 1))))) =
        mk (X (0 : Fin (N + 1)))
      rw [MvPolynomial.rename_X, _root_.finSuccEquiv_zero,
        multivariateDehomogenization_X_none, map_one, hmkX]
    · change phi (multivariateDehomogenization
        (MvPolynomial.rename (_root_.finSuccEquiv N) (X j.succ))) = mk (X j.succ)
      rw [MvPolynomial.rename_X, _root_.finSuccEquiv_succ]
      simp [phi, multivariateDehomogenization]
  have hphi : ∀ f : R,
      phi (multivariateDehomogenization (e f)) = mk f := by
    intro f
    exact DFunLike.congr_fun hcomposition f
  have hCker : C₀ ≤ RingHom.ker phi.toRingHom := by
    intro g hg
    obtain ⟨f, hfJ, hfg⟩ :=
      (Ideal.mem_map_iff_of_surjective multivariateDehomogenization.toRingHom
        (multivariateDehomogenization_surjective (K := ℚ) N)).1 hg
    obtain ⟨f₀, hf₀I, hf₀⟩ :=
      (Ideal.mem_map_iff_of_surjective e e.surjective).1 hfJ
    subst f
    rw [← hfg]
    change phi (multivariateDehomogenization (e f₀)) = 0
    rw [hphi]
    exact (Ideal.Quotient.eq_zero_iff_mem).2 (hI_le hf₀I)
  let psi : (MvPolynomial (Fin N) ℚ ⧸ C₀) →ₐ[ℚ] B :=
    Ideal.Quotient.liftₐ C₀ phi (fun f hf ↦ hCker hf)
  have hpsi : Function.Surjective psi := by
    intro x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨Ideal.Quotient.mk C₀ (multivariateDehomogenization (e f)), ?_⟩
    exact hphi f
  exact exists_spanningFamily_of_surjective_linearMap psi.toLinearMap hpsi v hv

/-- The Hilbert function of a proper hypersurface section of an integral
projective curve is eventually at most the product of the two degrees. -/
theorem eventual_finrank_projectiveCurve_hypersurface_le
    {N d k : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime) (hdegree : HasProjectiveDimensionDegree I 1 d)
    (G : MvPolynomial (Fin (N + 1)) ℚ)
    (hGhom : G.IsHomogeneous k) (hGI : G ∉ I) :
    ∃ k₀ : ℕ, ∀ m ≥ k₀,
      Module.finrank ℚ (quotientHomogeneousComponent ℚ (Fin (N + 1))
        (I ⊔ Ideal.span ({G} : Set _)) m) ≤ d * k := by
  obtain ⟨_hdim, _hdpos, P, hPdegree, hPlc, k₀, hPeventual⟩ := hdegree
  have hcoeff : P.coeff 1 = (d : ℚ) := by
    simpa only [Polynomial.leadingCoeff, hPdegree, Nat.factorial_one,
      Nat.cast_one, div_one] using hPlc
  have hlinear : P = Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C (P.coeff 0) := by
    simpa only [hcoeff] using P.eq_X_add_C_of_natDegree_le_one hPdegree.le
  refine ⟨k₀ + k, ?_⟩
  intro m hm
  have hkm : k ≤ m := by omega
  have hdiff : k₀ ≤ m - k := by omega
  have hmk : k + (m - k) = m := by omega
  have hsection := finrank_homogeneous_hypersurface_section_add_le I hI G hGhom hGI (m - k)
  rw [hmk] at hsection
  have hsmall := hPeventual (m - k) hdiff
  have hlarge := hPeventual m (by omega)
  have hsectionQ :
      (Module.finrank ℚ (quotientHomogeneousComponent ℚ (Fin (N + 1))
        (I ⊔ Ideal.span ({G} : Set _)) m) : ℚ) +
      P.eval ((m - k : ℕ) : ℚ) ≤ P.eval (m : ℚ) := by
    rw [← hsmall, ← hlarge]
    exact_mod_cast hsection
  rw [hlinear] at hsectionQ
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] at hsectionQ
  have hmkQ : (k : ℚ) + ((m - k : ℕ) : ℚ) = (m : ℚ) := by
    exact_mod_cast hmk
  have hfinal :
      (Module.finrank ℚ (quotientHomogeneousComponent ℚ (Fin (N + 1))
        (I ⊔ Ideal.span ({G} : Set _)) m) : ℚ) ≤ (d : ℚ) * (k : ℚ) := by
    nlinarith
  exact_mod_cast hfinal

/-- Internal discharge of the literal rational first-chart Bezout input.
The case of a degree-zero auxiliary form is included in the same argument. -/
theorem rationalProjectiveCurveAuxiliaryFirstChartBezout_internal :
    StandardAG.RationalProjectiveCurveAuxiliaryFirstChartBezout := by
  intro N d k I G hI _hIhom hdegree hGhom hGI
  obtain ⟨k₀, hbounded⟩ :=
    eventual_finrank_projectiveCurve_hypersurface_le I hI hdegree G hGhom hGI
  exact exists_rationalFirstChart_spanningFamily_of_eventual_bounded_hilbert
    (I ⊔ Ideal.span ({G} : Set _)) k₀ hbounded

end

end TranslatedDepthSeven

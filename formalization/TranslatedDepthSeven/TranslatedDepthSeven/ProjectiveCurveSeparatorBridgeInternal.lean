import TranslatedDepthSeven.HomogeneousHypersurfaceHilbertBoundInternal
import TranslatedDepthSeven.BoundedFirstChartHilbertInternal

/-!
# Proper curve sections over an arbitrary field

The rational first-chart proof is repeated over a generic field in this
independent file, so checked rational sources need not change.  The final
bridge states its actual separating form explicitly; it does not assert
that a separator of bounded degree has already been constructed.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

universe u
variable {K : Type u} [Field K]

/-- A bound for homogeneous quotient pieces bounds the size of a spanning
family of the reduced first-chart coordinate algebra.  This works for an
arbitrary ideal, including a nonreduced or empty section. -/
theorem exists_firstChart_spanningFamily_of_eventual_bounded_hilbert_over
    {N d : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (k₀ : ℕ)
    (hbounded : ∀ k ≥ k₀,
      Module.finrank K (quotientHomogeneousComponent K (Fin (N + 1)) I k) ≤ d) :
    ∃ v : Fin d → (MvPolynomial (Fin (N + 1)) K ⧸
        (I ⊔ Ideal.span ({X 0 - C 1} : Set (MvPolynomial (Fin (N + 1)) K))).radical),
      Submodule.span K (Set.range v) = ⊤ := by
  let R := MvPolynomial (Fin (N + 1)) K
  let J₀ := (I ⊔ Ideal.span ({X 0 - C 1} : Set (MvPolynomial (Fin (N + 1)) K))).radical
  have hI_le : I ≤ J₀ := le_trans le_sup_left Ideal.le_radical
  have hXone : X (0 : Fin (N + 1)) - C (1 : K) ∈ J₀ := by
    apply Ideal.le_radical
    exact (show Ideal.span ({X (0 : Fin (N + 1)) - C (1 : K)} : Set R) ≤
      I ⊔ Ideal.span ({X (0 : Fin (N + 1)) - C (1 : K)} : Set R)
      from le_sup_right) (Ideal.subset_span (Set.mem_singleton _))
  let e : R ≃ₐ[K] MvPolynomial (Option (Fin N)) K :=
    MvPolynomial.renameEquiv K (_root_.finSuccEquiv N)
  let J := I.map e
  let C₀ := J.map multivariateDehomogenization.toRingHom
  have hAffBound : ∀ k ≥ k₀,
      Module.finrank K (affineHilbertFiltration K N C₀ k) ≤ d := by
    intro k hk
    calc
      Module.finrank K (affineHilbertFiltration K N C₀ k) ≤
          Module.finrank K (quotientHomogeneousComponent K (Option (Fin N)) J k) :=
        finrank_affine_dehomogenization_le_projective J
      _ = Module.finrank K (quotientHomogeneousComponent K (Fin (N + 1)) I k) :=
        (finrank_quotientHomogeneousComponent_map_renameEquiv
          K (_root_.finSuccEquiv N) I k).symm
      _ ≤ d := hbounded k hk
  obtain ⟨v, hv⟩ :=
    exists_affineQuotient_spanningFamily_of_eventual_bounded_hilbert C₀ k₀ hAffBound
  let B := R ⧸ J₀
  let mk : R →ₐ[K] B := Ideal.Quotient.mkₐ K J₀
  let phi : MvPolynomial (Fin N) K →ₐ[K] B :=
    MvPolynomial.aeval fun i ↦ mk (X i.succ)
  have hmkX : mk (X (0 : Fin (N + 1))) = 1 := by
    have hz : mk (X (0 : Fin (N + 1)) - C (1 : K)) = 0 :=
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
        (multivariateDehomogenization_surjective (K := K) N)).1 hg
    obtain ⟨f₀, hf₀I, hf₀⟩ :=
      (Ideal.mem_map_iff_of_surjective e e.surjective).1 hfJ
    subst f
    rw [← hfg]
    change phi (multivariateDehomogenization (e f₀)) = 0
    rw [hphi]
    exact (Ideal.Quotient.eq_zero_iff_mem).2 (hI_le hf₀I)
  let psi : (MvPolynomial (Fin N) K ⧸ C₀) →ₐ[K] B :=
    Ideal.Quotient.liftₐ C₀ phi (fun f hf ↦ hCker hf)
  have hpsi : Function.Surjective psi := by
    intro x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨Ideal.Quotient.mk C₀ (multivariateDehomogenization (e f)), ?_⟩
    exact hphi f
  exact exists_spanningFamily_of_surjective_linearMap psi.toLinearMap hpsi v hv

/-- The Hilbert function of a proper hypersurface section of an integral
projective curve is eventually at most the product of the two degrees. -/
theorem eventual_finrank_projectiveCurve_hypersurface_le_over
    {N d k : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hI : I.IsPrime) (hdegree : HasProjectiveDimensionDegree I 1 d)
    (G : MvPolynomial (Fin (N + 1)) K)
    (hGhom : G.IsHomogeneous k) (hGI : G ∉ I) :
    ∃ k₀ : ℕ, ∀ m ≥ k₀,
      Module.finrank K (quotientHomogeneousComponent K (Fin (N + 1))
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
      (Module.finrank K (quotientHomogeneousComponent K (Fin (N + 1))
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
      (Module.finrank K (quotientHomogeneousComponent K (Fin (N + 1))
        (I ⊔ Ideal.span ({G} : Set _)) m) : ℚ) ≤ (d : ℚ) * (k : ℚ) := by
    nlinarith
  exact_mod_cast hfinal


/-- A displayed form in `Q` but outside the prime curve `P` bounds their
reduced first-chart intersection.  The only degree requirement is printed
explicitly as `k ≤ e`; no bounded separator is assumed implicitly. -/
theorem exists_firstChart_curveIntersection_spanningFamily_of_separator
    {N d e k : ℕ} (P Q : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hP : P.IsPrime) (hdegree : HasProjectiveDimensionDegree P 1 d)
    (G : MvPolynomial (Fin (N + 1)) K)
    (hGhom : G.IsHomogeneous k) (hGP : G ∉ P) (hGQ : G ∈ Q)
    (hke : k ≤ e) :
    ∃ v : Fin (d * e) →
        (MvPolynomial (Fin (N + 1)) K ⧸
          ((P ⊔ Q) ⊔ Ideal.span ({X 0 - C 1} : Set _)).radical),
      Submodule.span K (Set.range v) = ⊤ := by
  let J := P ⊔ Ideal.span ({G} : Set (MvPolynomial (Fin (N + 1)) K))
  let A := (J ⊔ Ideal.span
    ({X 0 - C 1} : Set (MvPolynomial (Fin (N + 1)) K))).radical
  let B := ((P ⊔ Q) ⊔ Ideal.span
    ({X 0 - C 1} : Set (MvPolynomial (Fin (N + 1)) K))).radical
  obtain ⟨k₀, hbounded⟩ :=
    eventual_finrank_projectiveCurve_hypersurface_le_over P hP hdegree G hGhom hGP
  obtain ⟨v, hv⟩ :=
    exists_firstChart_spanningFamily_of_eventual_bounded_hilbert_over J k₀ hbounded
  have hAB : A ≤ B := by
    apply Ideal.radical_mono
    apply sup_le_sup_right
    apply sup_le_sup_left
    exact Ideal.span_le.2 (by simpa using hGQ)
  let f := Ideal.Quotient.factorₐ K hAB
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hAB
  obtain ⟨w, hw⟩ := exists_spanningFamily_of_surjective_linearMap f.toLinearMap hf v hv
  exact exists_spanningFamily_of_spanningFamily_le (Nat.mul_le_mul_left d hke) w hw

/-- Without any degree bound, homogeneity extracts a separating homogeneous
component from an actual element of the ideal difference. -/
theorem exists_homogeneous_form_mem_not_mem_of_not_le
    {σ : Type*} [Finite σ]
    (P Q : Ideal (MvPolynomial σ K))
    (hQ : Q.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (hnotle : ¬ Q ≤ P) :
    ∃ (k : ℕ) (G : MvPolynomial σ K),
      G.IsHomogeneous k ∧ G ∈ Q ∧ G ∉ P := by
  classical
  obtain ⟨f, hfQ, hfP⟩ := Set.not_subset.1 hnotle
  have hex : ∃ k ∈ Finset.range (f.totalDegree + 1),
      homogeneousComponent k f ∉ P := by
    by_contra h
    push_neg at h
    apply hfP
    rw [← f.sum_homogeneousComponent]
    exact Ideal.sum_mem P h
  obtain ⟨k, _hk, hfkP⟩ := hex
  refine ⟨k, homogeneousComponent k f, homogeneousComponent_isHomogeneous k f, ?_, hfkP⟩
  have h := hQ k hfQ
  change (MvPolynomial.decomposition.decompose' f k : MvPolynomial σ K) ∈ Q at h
  simpa only [MvPolynomial.decomposition.decompose'_apply] using h

end

end TranslatedDepthSeven


import TranslatedDepthSeven.ProjectiveAffineChartBridge
import TranslatedDepthSeven.IsolatedVertexQuotientVertexCell

/-!
# The degree bound for the first chart of a projective zero-fold

The only input is the displayed projective Hilbert function.  On a nonempty
prime standard chart its cumulative affine Hilbert function agrees with the
projective one.  When that function is eventually the constant `d`, the
finite-dimensional filtration stabilizes and spans the entire coordinate
algebra.  Mapping onto the reduced chart cannot increase its number of
generators.  No zero-dimensional degree or point-counting theorem is assumed.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

universe u

variable {K : Type u} [Field K]

/-- An eventually constant cumulative Hilbert function supplies a spanning
family of that size for the whole affine coordinate algebra. -/
theorem exists_affineQuotient_spanningFamily_of_eventual_constant_hilbert
    {N d : ℕ} (I : Ideal (MvPolynomial (Fin N) K))
    (k₀ : ℕ)
    (hconstant : ∀ k ≥ k₀,
      Module.finrank K (affineHilbertFiltration K N I k) = d) :
    ∃ v : Fin d → (MvPolynomial (Fin N) K ⧸ I),
      Submodule.span K (Set.range v) = ⊤ := by
  let F := affineHilbertFiltration K N I
  have hmono : Monotone F := by
    intro a b hab
    apply Submodule.map_mono
    intro f hf
    exact (MvPolynomial.mem_restrictTotalDegree _ _ _).2
      (((MvPolynomial.mem_restrictTotalDegree _ _ _).1 hf).trans hab)
  have hstable : ∀ k ≥ k₀, F k₀ = F k := by
    intro k hk
    apply Submodule.eq_of_le_of_finrank_eq (hmono hk)
    exact (hconstant k₀ le_rfl).trans (hconstant k hk).symm
  have htop : F k₀ = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hmem : Ideal.Quotient.mk I f ∈ F (max k₀ f.totalDegree) := by
      exact Submodule.mem_map.2 ⟨f,
        (MvPolynomial.mem_restrictTotalDegree _ _ _).2 (le_max_right _ _), rfl⟩
    rw [← hstable _ (le_max_left _ _)] at hmem
    exact hmem
  letI : Module.Free K (F k₀) := Module.Free.of_divisionRing K (F k₀)
  let b := Module.finBasisOfFinrankEq K (F k₀) (hconstant k₀ le_rfl)
  refine ⟨fun i ↦ (b i : MvPolynomial (Fin N) K ⧸ I), ?_⟩
  have hspan := congrArg (Submodule.map (F k₀).subtype) b.span_eq
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at hspan
  simpa only [← Set.range_comp, Function.comp_def, htop] using hspan

/-- A surjective linear map transports a displayed finite spanning family.
This also applies when its codomain is the zero algebra. -/
theorem exists_spanningFamily_of_surjective_linearMap
    {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {d : ℕ}
    (f : V →ₗ[K] W) (hf : Function.Surjective f)
    (v : Fin d → V) (hv : Submodule.span K (Set.range v) = ⊤) :
    ∃ w : Fin d → W, Submodule.span K (Set.range w) = ⊤ := by
  refine ⟨f ∘ v, ?_⟩
  have hspan := congrArg (Submodule.map f) hv
  rw [Submodule.map_span, Submodule.map_top,
    LinearMap.range_eq_top.2 hf] at hspan
  simpa only [← Set.range_comp] using hspan

/-- Internal proof of the precise zero-fold chart input used for the
isolated-vertex elementary records. -/
theorem qbarIntegralProjectiveZerofoldFirstChartDegree_internal :
    StandardAG.QbarIntegralProjectiveZerofoldFirstChartDegree := by
  intro N d P hPprime hPhomogeneous hPdegree
  classical
  let R := MvPolynomial (Fin (N + 1)) Qbar
  let J₀ := qbarFirstAffineChartReducedIdeal P
  have hP_le : P ≤ J₀ :=
    le_trans le_sup_left Ideal.le_radical
  have hXone : X (0 : Fin (N + 1)) - C (1 : Qbar) ∈ J₀ := by
    apply Ideal.le_radical
    exact (show Ideal.span ({X (0 : Fin (N + 1)) - C (1 : Qbar)} : Set R) ≤
      P ⊔ Ideal.span ({X (0 : Fin (N + 1)) - C (1 : Qbar)} : Set R)
      from le_sup_right) (Ideal.subset_span (Set.mem_singleton _))
  by_cases hPX : X (0 : Fin (N + 1)) ∈ P
  · have hJtop : J₀ = ⊤ := by
      apply (Ideal.eq_top_iff_one J₀).2
      have h := J₀.sub_mem (hP_le hPX) hXone
      simpa using h
    change ∃ v : Fin d → (R ⧸ J₀),
      Submodule.span Qbar (Set.range v) = ⊤
    rw [hJtop]
    exact ⟨fun _ ↦ 0, Subsingleton.elim _ _⟩
  · let e : R ≃ₐ[Qbar] MvPolynomial (Option (Fin N)) Qbar :=
      MvPolynomial.renameEquiv Qbar (_root_.finSuccEquiv N)
    let J := P.map e
    let C₀ := J.map multivariateDehomogenization.toRingHom
    have hJhomogeneous : J.IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Option (Fin N)) Qbar) := by
      simpa only [J, e] using
        map_renameEquiv_isHomogeneous (_root_.finSuccEquiv N) P hPhomogeneous
    have hJprime : J.IsPrime := by
      letI : P.IsPrime := hPprime
      dsimp only [J, e]
      infer_instance
    have hJX : X (none : Option (Fin N)) ∉ J := by
      intro hmem
      obtain ⟨f, hf, hfeq⟩ :=
        (Ideal.mem_map_iff_of_surjective e e.surjective).1 hmem
      have hfX : f = X (0 : Fin (N + 1)) := by
        apply e.injective
        rw [hfeq]
        change X (none : Option (Fin N)) =
          MvPolynomial.rename (_root_.finSuccEquiv N) (X (0 : Fin (N + 1)))
        rw [MvPolynomial.rename_X, _root_.finSuccEquiv_zero]
      exact hPX (hfX ▸ hf)
    obtain ⟨_hdim, _hdpos, Hpoly, hHdegree, hHlc, k₀, hHeventual⟩ := hPdegree
    have hHconstant : Hpoly = Polynomial.C (d : ℚ) := by
      have h := Polynomial.eq_C_of_natDegree_eq_zero hHdegree
      have hcoeff : Hpoly.coeff 0 = (d : ℚ) := by
        simpa only [Polynomial.leadingCoeff, hHdegree, Nat.factorial_zero,
          Nat.cast_one, div_one] using hHlc
      simpa only [hcoeff] using h
    have hconstant : ∀ k ≥ k₀,
        Module.finrank Qbar (affineHilbertFiltration Qbar N C₀ k) = d := by
      intro k hk
      have hdim := hHeventual k hk
      rw [hHconstant, Polynomial.eval_C] at hdim
      have hrename :
          Module.finrank Qbar (projectiveHilbertPiece Qbar N P k) =
            Module.finrank Qbar
              (quotientHomogeneousComponent Qbar (Option (Fin N)) J k) := by
        exact finrank_quotientHomogeneousComponent_map_renameEquiv
          Qbar (_root_.finSuccEquiv N) P k
      have hchart := finrank_projective_eq_affine_dehomogenization
        J hJhomogeneous hJprime hJX (k := k)
      rw [hrename, hchart] at hdim
      exact_mod_cast hdim
    obtain ⟨v, hv⟩ :=
      exists_affineQuotient_spanningFamily_of_eventual_constant_hilbert C₀ k₀ hconstant
    let B := R ⧸ J₀
    let mk : R →ₐ[Qbar] B := Ideal.Quotient.mkₐ Qbar J₀
    let phi : MvPolynomial (Fin N) Qbar →ₐ[Qbar] B :=
      MvPolynomial.aeval fun i ↦ mk (X i.succ)
    have hmkX : mk (X (0 : Fin (N + 1))) = 1 := by
      have hz : mk (X (0 : Fin (N + 1)) - C (1 : Qbar)) = 0 :=
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
          (multivariateDehomogenization_surjective (K := Qbar) N)).1 hg
      obtain ⟨f₀, hf₀P, hf₀⟩ :=
        (Ideal.mem_map_iff_of_surjective e e.surjective).1 hfJ
      subst f
      rw [← hfg]
      change phi (multivariateDehomogenization (e f₀)) = 0
      rw [hphi]
      exact (Ideal.Quotient.eq_zero_iff_mem).2 (hP_le hf₀P)
    let psi : (MvPolynomial (Fin N) Qbar ⧸ C₀) →ₐ[Qbar] B :=
      Ideal.Quotient.liftₐ C₀ phi (fun f hf ↦ hCker hf)
    have hpsi : Function.Surjective psi := by
      intro x
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨Ideal.Quotient.mk C₀
        (multivariateDehomogenization (e f)), ?_⟩
      exact hphi f
    exact exists_spanningFamily_of_surjective_linearMap psi.toLinearMap hpsi v hv

end

end TranslatedDepthSeven

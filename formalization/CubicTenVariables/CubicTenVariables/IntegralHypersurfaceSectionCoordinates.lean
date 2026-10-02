import CubicTenVariables.IntegralHypersurfaceSectionElimination
import HessianTheorem11.FewerVariables
import HessianTheorem11.RationalIrreducibility
import TranslatedDepthSeven.ProjectiveBertiniGenericSectionConstruction

/-! Literal coordinate frames for the integral section supplied as a prime
all-coordinate saturation. The linear equation is normalized and eliminated;
no primality of the substituted equation is assumed. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open scoped BigOperators
namespace CubicTenVariables.IntegralHypersurfaceSectionCoordinates
open MvPolynomial HessianTheorem11 PolynomialRestriction TranslatedDepthSeven
open IntegralHypersurfaceSectionElimination

variable {K σ : Type*} [Field K]

/-- Normalize a nonzero coefficient of an actual homogeneous linear form. -/
theorem exists_monic_equation [Fintype σ]
    (L : MvPolynomial (Option σ) K) (hL : L.IsHomogeneous 1)
    (hc : coeff (Finsupp.single none 1) L ≠ 0) :
    ∃ l : MvPolynomial σ K, l.IsHomogeneous 1 ∧
      Ideal.span ({L} : Set _) =
        Ideal.span ({X none - rename some l} : Set _) := by
  classical
  let c := coeff (Finsupp.single none 1) L
  let t : MvPolynomial σ K :=
    ∑ i, C (coeff (Finsupp.single (some i) 1) L) * X i
  let l : MvPolynomial σ K := C (-c⁻¹) * t
  have ht : t.IsHomogeneous 1 := by
    apply IsHomogeneous.sum
    intro i _
    exact isHomogeneous_C_mul_X _ _
  have hl : l.IsHomogeneous 1 := by
    simpa only [zero_add] using (isHomogeneous_C σ (-c⁻¹)).mul ht
  have hc0 : coeff 0 L = 0 := hL.coeff_eq_zero (by simp)
  have hLexp : L = C c * X none + rename some t := by
    rw [eq_affine_linear_of_totalDegree_le_one L hL.totalDegree_le]
    simp only [hc0, map_zero, zero_add, Fintype.sum_option, t,
      map_sum, map_mul, rename_C, rename_X, c]
  have he : L = C c * (X none - rename some l) := by
    rw [hLexp]
    simp only [l, map_mul, rename_C]
    have hh : C c * C (-c⁻¹) = (-1 : MvPolynomial (Option σ) K) := by
      rw [← map_mul]
      simp [c, hc]
    rw [mul_sub, ← mul_assoc, hh]
    ring
  refine ⟨l, hl, ?_⟩
  rw [he]
  exact Ideal.span_singleton_mul_left_unit ((isUnit_iff_ne_zero.mpr hc).map C) _

/-- A cubic irreducible equation cannot vanish identically after eliminating
a single homogeneous linear coordinate. -/
theorem elimination_ne_zero_of_irreducible [Fintype σ]
    (F : MvPolynomial (Option σ) K) (hF : F.IsHomogeneous 3) (hI : Irreducible F)
    (l : MvPolynomial σ K) (hl : l.IsHomogeneous 1) :
    optionLinearEliminationAlgHom l F ≠ 0 := by
  classical
  let L : MvPolynomial (Option σ) K := X none - rename some l
  have hLhom : L.IsHomogeneous 1 := (isHomogeneous_X K none).sub hl.rename_isHomogeneous
  have hLcoeff : coeff (Finsupp.single none 1) L = 1 := by
    simp only [L, coeff_sub, coeff_X]
    rw [coeff_rename_eq_zero some l _ (by
      intro d hd
      have hh := congrArg (fun m : Option σ →₀ ℕ ↦ m none) hd
      change (d.mapDomain some) none = (Finsupp.single none 1) none at hh
      rw [Finsupp.mapDomain_notin_range d none (by simp), Finsupp.single_eq_same] at hh
      exact (zero_ne_one hh).elim)]
    ring
  have hLne : L ≠ 0 := by intro h; simp [h] at hLcoeff
  have hLdeg : L.totalDegree = 1 := hLhom.totalDegree hLne
  have hLunit : ¬ IsUnit L := by
    intro h
    have hh := (isUnit_iff_totalDegree_of_isReduced.mp h).2
    omega
  intro hzero
  have hmem : F ∈ RingHom.ker (optionLinearEliminationAlgHom l) := hzero
  rw [ker_optionLinearEliminationAlgHom] at hmem
  have hdiv : L ∣ F := Ideal.mem_span_singleton.mp hmem
  have ha : Associated F L := (hI.dvd_iff.mp hdiv).resolve_left hLunit
  have hdeg := totalDegree_le_of_dvd_of_isDomain ha.dvd hLne
  rw [hF.totalDegree hI.ne_zero, hLdeg] at hdeg
  omega

/-- The normalized substitution is an actual injective linear frame. -/
theorem exists_frame_for_elimination {n : ℕ}
    (e : Fin (n+1) ≃ Option (Fin n))
    (l : MvPolynomial (Fin n) K) (hl : l.IsHomogeneous 1) :
    ∃ B : Matrix (Fin (n+1)) (Fin n) K,
      Function.Injective B.mulVec ∧
      ∀ F : MvPolynomial (Fin (n+1)) K,
        restrict B F = optionLinearEliminationAlgHom l (renameEquiv K e F) := by
  classical
  let forms : Fin (n+1) → MvPolynomial (Fin n) K :=
    fun i ↦ optionLinearEliminationAlgHom l (X (e i))
  have hforms (i : Fin (n+1)) : (forms i).IsHomogeneous 1 := by
    dsimp only [forms]
    cases he : e i with
    | none => simpa only [he, optionLinearEliminationAlgHom_X_none] using hl
    | some j => simpa only [he, optionLinearEliminationAlgHom_X_some] using isHomogeneous_X K j
  let B := linearFormCoefficientMatrix forms
  have hlinear : linearForms B = forms := funext (linearForms_linearFormCoefficientMatrix forms hforms)
  have hcoord (y : Fin n → K) (j : Fin n) : B.mulVec y (e.symm (some j)) = y j := by
    rw [← eval_linearForms, hlinear]
    simp only [forms, Equiv.apply_symm_apply, optionLinearEliminationAlgHom_X_some, eval_X]
  refine ⟨B, ?_, ?_⟩
  · intro y z heq
    funext j
    simpa only [hcoord] using congrFun heq (e.symm (some j))
  · intro F
    change aeval (linearForms B) F = _
    rw [hlinear]
    have he : aeval forms = (optionLinearEliminationAlgHom l).comp (renameEquiv K e).toAlgHom := by
      ext i
      simp only [aeval_X, AlgHom.comp_apply, AlgEquiv.coe_algHom, renameEquiv_apply, rename_X]
      rfl
    exact AlgHom.congr_fun he F

/-- An actual injective coordinate restriction has a prime defining ideal
whenever the ambient hypersurface-plus-linear-equation has the prime
coordinate saturation delivered by projective Bertini. -/
theorem exists_integral_frame_of_prime_saturation {n : ℕ} (hn : 2 ≤ n)
    (F L : MvPolynomial (Fin (n+1)) K)
    (hF : F.IsHomogeneous 3) (hI : Irreducible F)
    (hL : L.IsHomogeneous 1) (hLne : L ≠ 0)
    (J : Ideal (MvPolynomial (Fin (n+1)) K)) (hJ : J.IsPrime)
    (hle : Ideal.span ({F} : Set _) ⊔ Ideal.span ({L} : Set _) ≤ J)
    (hsat : ∀ P ∈ J, ∀ i : Fin (n+1), ∃ a : ℕ,
      X i ^ a * P ∈ Ideal.span ({F} : Set _) ⊔ Ideal.span ({L} : Set _)) :
    ∃ B : Matrix (Fin (n+1)) (Fin n) K,
      Function.Injective B.mulVec ∧ restrict B F ≠ 0 ∧
      (restrict B F).IsHomogeneous 3 ∧
      IsDomain (MvPolynomial (Fin n) K ⧸ Ideal.span ({restrict B F} : Set _)) := by
  classical
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨i, hi⟩ := exists_linear_coefficient_ne_zero_of_totalDegree_one L (hL.totalDegree hLne)
  let e : Fin (n+1) ≃ Option (Fin n) := (Equiv.swap i 0).trans (_root_.finSuccEquiv n)
  have hei : e i = none := by simp [e]
  let E := renameEquiv K e
  let Fo := E F
  let Lo := E L
  let Jo := J.map E
  have hLo : Lo.IsHomogeneous 1 := hL.rename_isHomogeneous
  have hcoeff : coeff (Finsupp.single none 1) Lo ≠ 0 := by
    have hh := coeff_rename_mapDomain e e.injective L (Finsupp.single i 1)
    have hhne : coeff ((Finsupp.single i 1).mapDomain e) (rename e L) ≠ 0 := by
      rw [hh]
      exact hi
    simpa only [Lo, E, renameEquiv_apply, Finsupp.mapDomain_single, hei] using hhne
  obtain ⟨l, hl, hspan⟩ := exists_monic_equation Lo hLo hcoeff
  have hT : (Ideal.span ({F} : Set _) ⊔ Ideal.span ({L} : Set _)).map E =
      Ideal.span ({Fo} : Set _) ⊔ Ideal.span ({X none - rename some l} : Set _) := by
    rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
    exact congrArg (Ideal.span ({Fo} : Set _) ⊔ ·) hspan
  have hle' : Ideal.span ({Fo} : Set _) ⊔ Ideal.span ({X none - rename some l} : Set _) ≤ Jo := by
    rw [← hT]
    exact Ideal.map_mono hle
  have hsat' : ∀ P ∈ Jo, ∀ o : Option (Fin n), ∃ a : ℕ,
      X o ^ a * P ∈ Ideal.span ({Fo} : Set _) ⊔ Ideal.span ({X none - rename some l} : Set _) := by
    intro P hP o
    obtain ⟨a, ha⟩ := bertini_coordinate_saturation_map_renameEquiv e
      (Ideal.span ({F} : Set _) ⊔ Ideal.span ({L} : Set _)) J hsat P hP o
    exact ⟨a, hT ▸ ha⟩
  letI : J.IsPrime := hJ
  have hJo : Jo.IsPrime := by dsimp only [Jo]; infer_instance
  have hd := eliminated_quotient_isDomain Fo l Jo hJo hle' hsat'
  have hFo : Fo.IsHomogeneous 3 := hF.rename_isHomogeneous
  have hFoI : Irreducible Fo := hI.map E.toMulEquiv
  obtain ⟨B, hB, hBF⟩ := exists_frame_for_elimination e l hl
  refine ⟨B, hB, ?_, homogeneous_restrict B F hF, ?_⟩
  · rw [hBF]
    exact elimination_ne_zero_of_irreducible Fo hFo hFoI l hl
  · rw [hBF]
    exact hd

end CubicTenVariables.IntegralHypersurfaceSectionCoordinates

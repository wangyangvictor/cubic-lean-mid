import TranslatedDepthSeven.HilbertAffineChange
import TranslatedDepthSeven.HomogeneousLinearElimination
import TranslatedDepthSeven.MultivariateHomogenization
import TranslatedDepthSeven.ProjectiveConeIdealStructure

/-!
# Hilbert polynomial of a projective cone

Adjoining one unused homogeneous coordinate turns the degree-`k` quotient
piece into the cumulative degree-at-most-`k` filtration of the original
homogeneous quotient.  Consequently the projective Hilbert polynomial gains
one degree and retains its multiplicity.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators
open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1000000

universe u v w

/-- Exponents of degree at most `k` acquire the missing exponent in the new
vertex coordinate and thereby become exponents of degree exactly `k`. -/
def finExponentLEEquivOptionDegree (n k : ℕ) :
    {d : Fin n →₀ ℕ // d.sum (fun _ e ↦ e) ≤ k} ≃
      {m : Option (Fin n) →₀ ℕ // m.degree = k} where
  toFun d := ⟨d.1.optionElim (k - d.1.sum fun _ e ↦ e), by
    have hsum : d.1.sum (fun _ e ↦ e) = d.1.degree := by
      simp [Finsupp.sum_fintype, Finsupp.degree_eq_sum]
    have hd : d.1.degree ≤ k := by simpa [hsum] using d.2
    rw [finsupp_degree_option]
    simp only [Finsupp.optionElim_apply_none, Finsupp.some_optionElim]
    rw [hsum]
    omega⟩
  invFun m := ⟨m.1.some, by
    have hmdegree : m.1.degree = k := m.2
    have hm : m.1.some.degree ≤ k := by
      rw [finsupp_degree_option] at hmdegree
      omega
    change m.1.some.degree ≤ k
    exact hm⟩
  left_inv d := by
    apply Subtype.ext
    ext i
    simp
  right_inv m := by
    apply Subtype.ext
    apply finsupp_eq_of_some_eq_of_degree_eq
    · rw [m.2]
      rw [finsupp_degree_option]
      simp only [Finsupp.optionElim_apply_none, Finsupp.some_optionElim]
      have hsum : m.1.some.sum (fun _ e ↦ e) = m.1.some.degree := by
        simp [Finsupp.sum_fintype, Finsupp.degree_eq_sum]
      rw [hsum]
      have hmdegree : m.1.degree = k := m.2
      rw [finsupp_degree_option] at hmdegree
      omega
    · ext i
      simp

/-- The source and target polynomial spaces of degree-`k` homogenization
have equal finite dimension. -/
theorem finrank_restrictTotalDegree_eq_homogeneousOption
    (K : Type u) [Field K] (n k : ℕ) :
    Module.finrank K (MvPolynomial.restrictTotalDegree (Fin n) K k) =
      Module.finrank K
        (MvPolynomial.homogeneousSubmodule (Option (Fin n)) K k) := by
  let bSource := MvPolynomial.basisRestrictSupport K
    {d : Fin n →₀ ℕ | d.sum (fun _ e ↦ e) ≤ k}
  let bTargetSupported := MvPolynomial.basisRestrictSupport K
    {m : Option (Fin n) →₀ ℕ | m.degree = k}
  let eTarget :
      MvPolynomial.restrictSupport K
          {m : Option (Fin n) →₀ ℕ | m.degree = k} ≃ₗ[K]
        MvPolynomial.homogeneousSubmodule (Option (Fin n)) K k :=
    LinearEquiv.ofEq _ _
      (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported
        (Option (Fin n)) K k).symm
  let bTarget := bTargetSupported.map eTarget
  let e : MvPolynomial.restrictTotalDegree (Fin n) K k ≃ₗ[K]
      MvPolynomial.homogeneousSubmodule (Option (Fin n)) K k :=
    bSource.equiv bTarget (finExponentLEEquivOptionDegree n k)
  exact e.finrank_eq

/-- Homogenization at a fixed target degree, restricted to the appropriate
finite-dimensional source and target spaces. -/
def degreeHomogenizationLinearMap
    (K : Type u) [Field K] (n k : ℕ) :
    MvPolynomial.restrictTotalDegree (Fin n) K k →ₗ[K]
      MvPolynomial.homogeneousSubmodule (Option (Fin n)) K k where
  toFun f := ⟨multivariateHomogenization f.1 k,
    multivariateHomogenization_isHomogeneous f.1 k⟩
  map_add' f g := by
    apply Subtype.ext
    change multivariateHomogenization (f.1 + g.1) k =
      multivariateHomogenization f.1 k + multivariateHomogenization g.1 k
    simp [multivariateHomogenization, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    apply Subtype.ext
    change multivariateHomogenization (c • f.1) k =
      c • multivariateHomogenization f.1 k
    simp [multivariateHomogenization, Finset.smul_sum]

/-- Fixed-degree homogenization is injective. -/
theorem degreeHomogenizationLinearMap_injective
    (K : Type u) [Field K] (n k : ℕ) :
    Function.Injective (degreeHomogenizationLinearMap K n k) := by
  intro f g hfg
  apply Subtype.ext
  have h := congrArg
    (multivariateDehomogenization (R := K) (σ := Fin n))
    (congrArg Subtype.val hfg)
  change multivariateDehomogenization
      (multivariateHomogenization f.1 k) =
    multivariateDehomogenization (multivariateHomogenization g.1 k) at h
  rw [multivariateDehomogenization_homogenization f.1 k
      ((MvPolynomial.mem_restrictTotalDegree (Fin n) k f.1).1 f.2),
    multivariateDehomogenization_homogenization g.1 k
      ((MvPolynomial.mem_restrictTotalDegree (Fin n) k g.1).1 g.2)] at h
  exact h

/-- Fixed-degree homogenization is a linear equivalence. -/
def degreeHomogenizationLinearEquiv
    (K : Type u) [Field K] (n k : ℕ) :
    MvPolynomial.restrictTotalDegree (Fin n) K k ≃ₗ[K]
      MvPolynomial.homogeneousSubmodule (Option (Fin n)) K k :=
  LinearEquiv.ofBijective (degreeHomogenizationLinearMap K n k)
    ⟨degreeHomogenizationLinearMap_injective K n k,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (finrank_restrictTotalDegree_eq_homogeneousOption K n k)).mp
          (degreeHomogenizationLinearMap_injective K n k)⟩

@[simp]
theorem degreeHomogenizationLinearEquiv_apply
    (K : Type u) [Field K] (n k : ℕ)
    (f : MvPolynomial.restrictTotalDegree (Fin n) K k) :
    (degreeHomogenizationLinearEquiv K n k f).1 =
      multivariateHomogenization f.1 k :=
  rfl

/-- Dehomogenizing the extended ideal lands back in the original ideal. -/
theorem projectiveConeIdealExtension_le_comap_dehomogenization
    (K : Type u) [Field K] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K)) :
    projectiveConeIdealExtension I ≤
      Ideal.comap multivariateDehomogenization I := by
  rw [projectiveConeIdealExtension, Ideal.map_le_iff_le_comap]
  intro f hf
  change multivariateDehomogenization (rename some f) ∈ I
  simpa using hf

/-- For a homogeneous ideal, fixed-degree homogenization belongs to the
extended cone ideal exactly when the original polynomial belongs to the
original ideal. -/
theorem multivariateHomogenization_mem_projectiveConeIdealExtension_iff
    (K : Type u) [Field K] (n k : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (f : MvPolynomial (Fin n) K) (hdegree : f.totalDegree ≤ k) :
    multivariateHomogenization f k ∈ projectiveConeIdealExtension I ↔
      f ∈ I := by
  constructor
  · intro hf
    have hdehom :=
      projectiveConeIdealExtension_le_comap_dehomogenization K n I hf
    change multivariateDehomogenization
      (multivariateHomogenization f k) ∈ I at hdehom
    rwa [multivariateDehomogenization_homogenization f k hdegree] at hdehom
  · intro hf
    rw [multivariateHomogenization]
    apply Ideal.sum_mem
    intro j hj
    apply Ideal.mul_mem_left
    apply Ideal.mem_map_of_mem (MvPolynomial.rename some)
    have hjmem := hI j hf
    change (MvPolynomial.decomposition.decompose' f j :
      MvPolynomial (Fin n) K) ∈ I at hjmem
    simpa only [MvPolynomial.decomposition.decompose'_apply] using hjmem

/-- The quotient map from the degree-at-most-`k` affine polynomial space to
its image filtration. -/
def affineHilbertFiltrationMap
    (K : Type u) [Field K] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K)) (k : ℕ) :
    MvPolynomial.restrictTotalDegree (Fin n) K k →ₗ[K]
      Published.affineHilbertFiltration K n I k :=
  (((Ideal.Quotient.mkₐ K I).toLinearMap.comp
      (MvPolynomial.restrictTotalDegree (Fin n) K k).subtype).codRestrict
    (Published.affineHilbertFiltration K n I k) fun f ↦
      Submodule.mem_map.mpr ⟨f, f.2, rfl⟩)

@[simp]
theorem coe_affineHilbertFiltrationMap
    (K : Type u) [Field K] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K)) (k : ℕ)
    (f : MvPolynomial.restrictTotalDegree (Fin n) K k) :
    (affineHilbertFiltrationMap K n I k f :
      MvPolynomial (Fin n) K ⧸ I) = Ideal.Quotient.mk I f.1 :=
  rfl

theorem affineHilbertFiltrationMap_surjective
    (K : Type u) [Field K] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K)) (k : ℕ) :
    Function.Surjective (affineHilbertFiltrationMap K n I k) := by
  intro x
  obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.mp x.2
  refine ⟨⟨f, hf⟩, ?_⟩
  apply Subtype.ext
  exact hfx

@[simp]
theorem mem_ker_affineHilbertFiltrationMap_iff
    (K : Type u) [Field K] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K)) (k : ℕ)
    (f : MvPolynomial.restrictTotalDegree (Fin n) K k) :
    f ∈ LinearMap.ker (affineHilbertFiltrationMap K n I k) ↔ f.1 ∈ I := by
  rw [LinearMap.mem_ker]
  apply Iff.trans Subtype.ext_iff
  change Ideal.Quotient.mk I f.1 = 0 ↔ f.1 ∈ I
  exact Ideal.Quotient.eq_zero_iff_mem

theorem quotientHomogeneousComponentMap_surjective
    (K : Type u) [Field K] (n k : ℕ)
    (I : Ideal (MvPolynomial (Option (Fin n)) K)) :
    Function.Surjective
      (quotientHomogeneousComponentMap K (Option (Fin n)) I k) := by
  intro x
  obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.mp x.2
  refine ⟨⟨f, hf⟩, ?_⟩
  apply Subtype.ext
  exact hfx

@[simp]
theorem mem_ker_quotientHomogeneousComponentMap_iff
    (K : Type u) [Field K] (n k : ℕ)
    (I : Ideal (MvPolynomial (Option (Fin n)) K))
    (f : MvPolynomial.homogeneousSubmodule (Option (Fin n)) K k) :
    f ∈ LinearMap.ker
      (quotientHomogeneousComponentMap K (Option (Fin n)) I k) ↔ f.1 ∈ I := by
  rw [LinearMap.mem_ker]
  apply Iff.trans Subtype.ext_iff
  change Ideal.Quotient.mk I f.1 = 0 ↔ f.1 ∈ I
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The degree-`k` Hilbert function of the cone is the cumulative
degree-at-most-`k` Hilbert function of the original homogeneous quotient. -/
theorem finrank_projectiveCone_homogeneousComponent_eq_affineHilbertFiltration
    (K : Type u) [Field K] (n k : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) K)) :
    Module.finrank K
        (quotientHomogeneousComponent K (Option (Fin n))
          (projectiveConeIdealExtension I) k) =
      Module.finrank K (Published.affineHilbertFiltration K n I k) := by
  let e := degreeHomogenizationLinearEquiv K n k
  let qAff := affineHilbertFiltrationMap K n I k
  let qCone := quotientHomogeneousComponentMap K (Option (Fin n))
    (projectiveConeIdealExtension I) k
  have hker : Submodule.map e.toLinearMap (LinearMap.ker qAff) =
      LinearMap.ker qCone := by
    ext g
    constructor
    · rintro ⟨f, hf, hfg⟩
      rw [mem_ker_quotientHomogeneousComponentMap_iff]
      rw [← hfg]
      change multivariateHomogenization f.1 k ∈
        projectiveConeIdealExtension I
      apply (multivariateHomogenization_mem_projectiveConeIdealExtension_iff
        K n k I hI f.1
          ((MvPolynomial.mem_restrictTotalDegree (Fin n) k f.1).1 f.2)).2
      exact (mem_ker_affineHilbertFiltrationMap_iff K n I k f).1 hf
    · intro hg
      refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
      change e.symm g ∈ LinearMap.ker
        (affineHilbertFiltrationMap K n I k)
      rw [mem_ker_affineHilbertFiltrationMap_iff]
      apply (multivariateHomogenization_mem_projectiveConeIdealExtension_iff
        K n k I hI (e.symm g).1
          ((MvPolynomial.mem_restrictTotalDegree (Fin n) k (e.symm g).1).1
            (e.symm g).2)).1
      change (e (e.symm g)).1 ∈ projectiveConeIdealExtension I
      rw [e.apply_symm_apply]
      exact (mem_ker_quotientHomogeneousComponentMap_iff K n k
        (projectiveConeIdealExtension I) g).1 hg
  have hkerFinrank : Module.finrank K (LinearMap.ker qAff) =
      Module.finrank K (LinearMap.ker qCone) :=
    ((e.submoduleMap (LinearMap.ker qAff)).trans
      (LinearEquiv.ofEq _ _ hker)).finrank_eq
  have hAff := LinearMap.finrank_range_add_finrank_ker qAff
  have hCone := LinearMap.finrank_range_add_finrank_ker qCone
  rw [LinearMap.range_eq_top.mpr
      (affineHilbertFiltrationMap_surjective K n I k)] at hAff
  rw [LinearMap.range_eq_top.mpr
      (quotientHomogeneousComponentMap_surjective K n k
        (projectiveConeIdealExtension I))] at hCone
  simp at hAff hCone
  have hdomain := e.finrank_eq
  omega

/-! ## Reindexing the cone by consecutive homogeneous coordinates -/

/-- The quotient equivalence induced by a bijective renaming of variables. -/
def renameQuotientAlgEquiv
    (K : Type u) [Field K] { σ : Type v } { τ : Type w }
    (e : σ ≃ τ) (I : Ideal (MvPolynomial σ K)) :
    (MvPolynomial σ K ⧸ I) ≃ₐ[K]
      (MvPolynomial τ K ⧸ I.map (MvPolynomial.renameEquiv K e)) :=
  Ideal.quotientEquivAlg I _ (MvPolynomial.renameEquiv K e) rfl

/-- A variable renaming carries each homogeneous quotient piece onto the
corresponding homogeneous quotient piece of the renamed ideal. -/
theorem quotientHomogeneousComponent_map_renameEquiv
    (K : Type u) [Field K] { σ : Type v } { τ : Type w }
    (e : σ ≃ τ) (I : Ideal (MvPolynomial σ K)) (k : ℕ) :
    (quotientHomogeneousComponent K σ I k).map
        (renameQuotientAlgEquiv K e I).toLinearMap =
      quotientHomogeneousComponent K τ
        (I.map (MvPolynomial.renameEquiv K e)) k := by
  ext z
  constructor
  · rintro ⟨x, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨MvPolynomial.renameEquiv K e f, ?_, ?_⟩
    · simpa only [MvPolynomial.renameEquiv_apply] using
        hf.rename_isHomogeneous
    · exact Ideal.quotientEquivAlg_mk _ (MvPolynomial.renameEquiv K e)
        rfl f
  · rintro ⟨g, hg, rfl⟩
    let f : MvPolynomial σ K := (MvPolynomial.renameEquiv K e).symm g
    refine ⟨Ideal.Quotient.mk I f, ?_, ?_⟩
    · refine ⟨f, ?_, rfl⟩
      have hf : (MvPolynomial.rename e.symm g).IsHomogeneous k :=
        hg.rename_isHomogeneous
      simpa [f, MvPolynomial.renameEquiv_symm,
        MvPolynomial.renameEquiv_apply] using hf
    · change renameQuotientAlgEquiv K e I (Ideal.Quotient.mk I f) =
        Ideal.Quotient.mk (I.map (MvPolynomial.renameEquiv K e)) g
      rw [show g = MvPolynomial.renameEquiv K e f by simp [f]]
      exact Ideal.quotientEquivAlg_mk _ (MvPolynomial.renameEquiv K e)
        rfl f

/-- Bijective renaming leaves the dimension of every homogeneous quotient
piece unchanged. -/
theorem finrank_quotientHomogeneousComponent_map_renameEquiv
    (K : Type u) [Field K] { σ : Type v } { τ : Type w }
    [Finite σ] [Finite τ]
    (e : σ ≃ τ) (I : Ideal (MvPolynomial σ K)) (k : ℕ) :
    Module.finrank K (quotientHomogeneousComponent K σ I k) =
      Module.finrank K (quotientHomogeneousComponent K τ
        (I.map (MvPolynomial.renameEquiv K e)) k) := by
  rw [← quotientHomogeneousComponent_map_renameEquiv K e I k]
  exact (LinearEquiv.finrank_map_eq
    (renameQuotientAlgEquiv K e I).toLinearEquiv
      (quotientHomogeneousComponent K σ I k)).symm

/-- The cone ideal with its homogeneous coordinates reindexed consecutively. -/
def projectiveConeFinIdeal
    (K : Type u) [Field K] (N : ℕ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) :
    Ideal (MvPolynomial (Fin ((N + 1) + 1)) K) :=
  (projectiveConeIdealExtension I).map
    (MvPolynomial.renameEquiv K (_root_.finSuccEquiv (N + 1)).symm)

/-- In consecutive coordinates, the cone's degree-`k` projective Hilbert
piece is still the original cone's cumulative affine filtration. -/
theorem finrank_projectiveHilbertPiece_projectiveConeFinIdeal
    (K : Type u) [Field K] (N k : ℕ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)) :
    Module.finrank K
        (Published.projectiveHilbertPiece K (N + 1)
          (projectiveConeFinIdeal K N I) k) =
      Module.finrank K
        (Published.affineHilbertFiltration K (N + 1) I k) := by
  change Module.finrank K
      (quotientHomogeneousComponent K (Fin ((N + 1) + 1))
        (projectiveConeFinIdeal K N I) k) = _
  unfold projectiveConeFinIdeal
  rw [← finrank_quotientHomogeneousComponent_map_renameEquiv K
    (_root_.finSuccEquiv (N + 1)).symm
    (projectiveConeIdealExtension I) k]
  exact finrank_projectiveCone_homogeneousComponent_eq_affineHilbertFiltration
    K (N + 1) k I hI

/-- Reindexing the polynomial extension of a prime ideal remains prime. -/
theorem projectiveConeFinIdeal_isPrime
    (K : Type u) [Field K] (N : ℕ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) (hprime : I.IsPrime) :
    (projectiveConeFinIdeal K N I).IsPrime := by
  unfold projectiveConeFinIdeal
  letI : (projectiveConeIdealExtension I).IsPrime :=
    projectiveConeIdealExtension_isPrime I hprime
  exact Ideal.map_isPrime_of_equiv
    (MvPolynomial.renameEquiv K (_root_.finSuccEquiv (N + 1)).symm)

/-- The part of the projective cone dimension-and-degree statement which is
independent of the unavailable general polynomial-ring Krull-dimension
formula: the exact eventual Hilbert polynomial has degree `r+1` and the same
degree `d`. -/
theorem projectiveConeFinIdeal_hilbertPolynomial
    (K : Type u) [Field K] (N r d : ℕ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (hprime : I.IsPrime)
    (hproj : Published.HasProjectiveDimensionDegree I r d) :
    0 < d ∧
      ∃ P : Polynomial ℚ,
        P.natDegree = r + 1 ∧
        P.leadingCoeff = (d : ℚ) / (r + 1).factorial ∧
        ∃ k₀ : ℕ, ∀ k ≥ k₀,
          (Module.finrank K
            (Published.projectiveHilbertPiece K (N + 1)
              (projectiveConeFinIdeal K N I) k) : ℚ) =
            P.eval (k : ℚ) := by
  rcases Published.hasAffineDimensionDegree_of_homogeneous_hasProjectiveDimensionDegree
    I hI hprime r d hproj with
      ⟨_hprime, _hdim, hd, P, hPdegree, hPlc, k₀, hPeventual⟩
  refine ⟨hd, P, hPdegree, hPlc, k₀, ?_⟩
  intro k hk
  rw [finrank_projectiveHilbertPiece_projectiveConeFinIdeal K N k I hI]
  exact hPeventual k hk

/-- Projective dimension and degree pass to the cone once the single missing
Krull-dimension equality for polynomial extension is supplied explicitly.
All Hilbert-function and degree assertions are proved internally above. -/
theorem hasProjectiveDimensionDegree_projectiveConeFinIdeal_of_ringKrullDim
    (K : Type u) [Field K] (N r d : ℕ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (hprime : I.IsPrime)
    (hproj : Published.HasProjectiveDimensionDegree I r d)
    (hConeKrull :
      ringKrullDim
        (MvPolynomial (Fin ((N + 1) + 1)) K ⧸
          projectiveConeFinIdeal K N I) = (r + 1) + 1) :
    Published.HasProjectiveDimensionDegree
      (projectiveConeFinIdeal K N I) (r + 1) d := by
  rcases projectiveConeFinIdeal_hilbertPolynomial K N r d I hI hprime hproj with
    ⟨hd, P, hPdegree, hPlc, k₀, hPeventual⟩
  exact ⟨hConeKrull, hd, P, hPdegree, hPlc, k₀, hPeventual⟩

end

end TranslatedDepthSeven

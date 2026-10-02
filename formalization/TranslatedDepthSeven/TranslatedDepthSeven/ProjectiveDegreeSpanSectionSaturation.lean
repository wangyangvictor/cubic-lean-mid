import TranslatedDepthSeven.ProjectiveDegreeSpanSectionAlgebra
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Saturation cannot add a new linear equation to an integral section

The key argument is finite-dimensional. If the degree-zero fraction `F/L`
preserves a nonzero homogeneous piece of an integral coordinate ring, its
multiplication endomorphism has an eigenvalue over the algebraically closed
coefficient field. Cancellation then shows that `F/L` is that scalar.
There is no cohomology input.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 300000

theorem projectiveSection_scalar_of_finite_mul_stable
    {K E : Type*} [Field K] [IsAlgClosed K] [Field E] [Algebra K E]
    (V : Submodule K E) [Module.Finite K V] [Nontrivial V]
    (u : E) (hu : ∀ x ∈ V, u * x ∈ V) :
    ∃ c : K, u = algebraMap K E c := by
  let T : V →ₗ[K] V :=
    ((LinearMap.mulLeft K u).comp V.subtype).codRestrict V (fun x ↦ hu x x.2)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hmul : u * v.1 = algebraMap K E c * v.1 := by
    have heq := congrArg Subtype.val hv.apply_eq_smul
    simpa only [T, LinearMap.codRestrict_apply, LinearMap.comp_apply,
      Submodule.subtype_apply, LinearMap.mulLeft_apply, Submodule.coe_smul_of_tower,
      Algebra.smul_def] using heq
  have hvne : v.1 ≠ 0 := by
    intro h
    exact hv.2 (Subtype.ext h)
  exact ⟨c, mul_right_cancel₀ hvne hmul⟩

/-- A degree-zero rational function that preserves one nonzero homogeneous
piece is a scalar. The displayed polynomial congruences are precisely the
condition that multiplication by `F/L` preserves that piece. -/
theorem projectiveSection_linear_relation_of_stable_piece
    {K σ : Type*} [Field K] [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (hI : I.IsPrime)
    (L F : MvPolynomial σ K) (hL : L ∉ I) (n : ℕ)
    (hne : ∃ p : MvPolynomial σ K, p.IsHomogeneous n ∧ p ∉ I)
    (hstable : ∀ p : MvPolynomial σ K, p.IsHomogeneous n →
      ∃ q : MvPolynomial σ K, q.IsHomogeneous n ∧ F * p - L * q ∈ I) :
    ∃ c : K, F - C c * L ∈ I := by
  letI : I.IsPrime := hI
  let A := MvPolynomial σ K ⧸ I
  let E := FractionRing A
  let φ : MvPolynomial σ K →ₐ[K] E :=
    (IsScalarTower.toAlgHom K A E).comp (Ideal.Quotient.mkₐ K I)
  let H := quotientHomogeneousComponent K σ I n
  let V : Submodule K E := H.map (IsScalarTower.toAlgHom K A E).toLinearMap
  have hinj : Function.Injective (algebraMap A E) := IsFractionRing.injective A E
  have hφzero (p : MvPolynomial σ K) : φ p = 0 ↔ p ∈ I := by
    change algebraMap A E (Ideal.Quotient.mk I p) = 0 ↔ p ∈ I
    rw [map_eq_zero_iff _ hinj, Ideal.Quotient.eq_zero_iff_mem]
  letI : Module.Finite K V := Module.Finite.map _ _
  have hVne : V ≠ ⊥ := by
    obtain ⟨p, hp, hpI⟩ := hne
    intro hV
    have hpmem : φ p ∈ V :=
      Submodule.mem_map.mpr ⟨Ideal.Quotient.mk I p,
        Submodule.mem_map.mpr ⟨p, hp, rfl⟩, rfl⟩
    rw [hV] at hpmem
    exact hpI ((hφzero p).mp hpmem)
  letI : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hVne
  have hLne : φ L ≠ 0 := fun h ↦ hL ((hφzero L).mp h)
  have hVstable : ∀ x ∈ V, (φ F / φ L) * x ∈ V := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨p, hp, hpa⟩ := Submodule.mem_map.mp ha
    rw [← hpa]
    obtain ⟨q, hq, hpq⟩ := hstable p hp
    have heq : φ F * φ p = φ L * φ q := by
      have hz := (hφzero (F * p - L * q)).mpr hpq
      simpa only [map_sub, map_mul, sub_eq_zero] using hz
    have hfrac : (φ F / φ L) * φ p = φ q := by
      apply (mul_right_cancel₀ hLne)
      calc
        (φ F / φ L * φ p) * φ L = (φ F / φ L * φ L) * φ p := by ring
        _ = φ F * φ p := by rw [div_mul_cancel₀ _ hLne]
        _ = φ q * φ L := heq.trans (mul_comm _ _)
    change (φ F / φ L) * φ p ∈ V
    rw [hfrac]
    exact Submodule.mem_map.mpr ⟨Ideal.Quotient.mk I q,
      Submodule.mem_map.mpr ⟨q, hq, rfl⟩, rfl⟩
  obtain ⟨c, hc⟩ := projectiveSection_scalar_of_finite_mul_stable V (φ F / φ L) hVstable
  refine ⟨c, (hφzero _).mp ?_⟩
  have hφC : φ (C c) = algebraMap K E c := φ.commutes c
  rw [map_sub, map_mul, hφC]
  exact sub_eq_zero.mpr ((div_eq_iff hLne).mp hc)

/-- Membership in a hyperplane section after multiplication by every form
of one degree cannot create a new linear relation. -/
theorem projectiveSection_linear_relation_of_piece_annihilation
    {K σ : Type*} [Field K] [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (hI : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule σ K))
    (L F : MvPolynomial σ K) (hLhom : L.IsHomogeneous 1)
    (hFhom : F.IsHomogeneous 1) (hL : L ∉ I) (n : ℕ)
    (hne : ∃ p : MvPolynomial σ K, p.IsHomogeneous n ∧ p ∉ I)
    (hann : ∀ p : MvPolynomial σ K, p.IsHomogeneous n →
      F * p ∈ I ⊔ Ideal.span ({L} : Set _)) :
    F ∈ I ⊔ Ideal.span ({L} : Set _) := by
  obtain ⟨c, hc⟩ := projectiveSection_linear_relation_of_stable_piece
    I hI L F hL n hne (by
      intro p hp
      obtain ⟨a, b, hb, hab⟩ := Ideal.mem_span_singleton_sup.mp
        (show F * p ∈ Ideal.span ({L} : Set _) ⊔ I by
          simpa only [sup_comm] using hann p hp)
      let q := homogeneousComponent n a
      have hb' : homogeneousComponent (n + 1) b ∈ I := by
        have hh := hhom (n + 1) hb
        change (MvPolynomial.decomposition.decompose' b (n + 1) : MvPolynomial σ K) ∈ I at hh
        simpa only [MvPolynomial.decomposition.decompose'_apply] using hh
      have hcomponent : homogeneousComponent (n + 1) (a * L) = q * L := by
        have hh := DirectSum.coe_decompose_mul_add_of_right_mem
          (homogeneousSubmodule σ K) (a := a) (i := n) hLhom
        change (MvPolynomial.decomposition.decompose' (a * L) (n + 1) : MvPolynomial σ K) =
          (MvPolynomial.decomposition.decompose' a n : MvPolynomial σ K) * L at hh
        simpa only [MvPolynomial.decomposition.decompose'_apply] using hh
      have hFp : (F * p).IsHomogeneous (n + 1) := by
        simpa only [Nat.add_comm] using hFhom.mul hp
      have heq : q * L + homogeneousComponent (n + 1) b = F * p := by
        have hh := congrArg (homogeneousComponent (n + 1)) hab
        simpa only [map_add, hcomponent, homogeneousComponent_of_mem hFp, if_true] using hh
      refine ⟨q, homogeneousComponent_isHomogeneous n a, ?_⟩
      have hz : F * p - L * q = homogeneousComponent (n + 1) b := by
        rw [← heq]
        ring
      rw [hz]
      exact hb')
  have hcJ : F - C c * L ∈ I ⊔ Ideal.span ({L} : Set _) :=
    (show I ≤ I ⊔ Ideal.span ({L} : Set _) from le_sup_left) hc
  have hcL : C c * L ∈ I ⊔ Ideal.span ({L} : Set _) :=
    (show Ideal.span ({L} : Set _) ≤ I ⊔ Ideal.span ({L} : Set _) from le_sup_right)
      (Ideal.mem_span_singleton'.mpr ⟨C c, rfl⟩)
  simpa only [sub_add_cancel] using Ideal.add_mem _ hcJ hcL

/-- The literal coordinate-chart saturation statement in degree one.
If each coordinate has a power killing `F` modulo the section ideal,
then the linear form `F` already belongs to that section ideal. -/
theorem projectiveSection_no_new_linear_equation_after_saturation
    {K σ : Type*} [Field K] [IsAlgClosed K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (hI : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule σ K))
    (L F : MvPolynomial σ K) (hLhom : L.IsHomogeneous 1)
    (hFhom : F.IsHomogeneous 1) (hL : L ∉ I)
    (hsat : ∀ i : σ, ∃ k : ℕ, X i ^ k * F ∈ I ⊔ Ideal.span ({L} : Set _)) :
    F ∈ I ⊔ Ideal.span ({L} : Set _) := by
  classical
  choose k hk using hsat
  let n := (∑ i, k i) + 1
  apply projectiveSection_linear_relation_of_piece_annihilation I hI hhom
    L F hLhom hFhom hL n
  · exact ⟨L ^ n, by simpa only [one_mul] using hLhom.pow n,
      fun h ↦ hL (hI.mem_of_pow_mem n h)⟩
  · intro p hp
    rw [p.as_sum, Finset.mul_sum]
    apply Ideal.sum_mem
    intro m hm
    have hmd : m.degree = n := by
      simpa only [Finsupp.degree_eq_weight_one] using hp (mem_support_iff.mp hm)
    have hex : ∃ i : σ, k i ≤ m i := by
      by_contra h
      push_neg at h
      have hsum : (∑ i, m i) ≤ ∑ i, k i :=
        Finset.sum_le_sum (fun i _ ↦ (h i).le)
      rw [← Finsupp.degree_eq_sum, hmd] at hsum
      dsimp only [n] at hsum
      omega
    obtain ⟨i, hi⟩ := hex
    have hdiv : (X i ^ k i : MvPolynomial σ K) ∣ monomial m (p.coeff m) := by
      rw [X_pow_eq_monomial, monomial_dvd_monomial]
      exact ⟨Or.inr (Finsupp.single_le_iff.mpr hi), one_dvd _⟩
    obtain ⟨q, hq⟩ := hdiv
    rw [hq]
    have heq : F * (X i ^ k i * q) = q * (X i ^ k i * F) := by ring
    rw [heq]
    exact Ideal.mul_mem_left _ q (hk i)

/-- Any coordinate-chart saturation of the literal section has exactly the
same linear equations. No primality assumption on the saturated section
is used in this conclusion. -/
theorem projectiveSection_saturation_degreeOnePart_eq
    {K : Type*} [Field K] [IsAlgClosed K] {N : ℕ}
    (I J : Ideal (MvPolynomial (Fin (N + 1)) K)) (hI : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (L : MvPolynomial (Fin (N + 1)) K)
    (hLhom : L.IsHomogeneous 1) (hL : L ∉ I)
    (hle : I ⊔ Ideal.span ({L} : Set _) ≤ J)
    (hsat : ∀ F ∈ J, ∀ i : Fin (N + 1),
      ∃ k : ℕ, X i ^ k * F ∈ I ⊔ Ideal.span ({L} : Set _)) :
    StandardAG.degreeOnePartInIdeal J =
      StandardAG.degreeOnePartInIdeal (I ⊔ Ideal.span ({L} : Set _)) := by
  ext F
  constructor
  · intro hF
    exact ⟨projectiveSection_no_new_linear_equation_after_saturation
      I hI hhom L F hLhom hF.2 hL (hsat F hF.1), hF.2⟩
  · intro hF
    exact ⟨hle hF.1, hF.2⟩

/-- The exact drop in linear span survives saturation. -/
theorem projectiveSection_saturation_hilbertOne_add_one
    {K : Type*} [Field K] [IsAlgClosed K] {N : ℕ}
    (I J : Ideal (MvPolynomial (Fin (N + 1)) K)) (hI : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (L : MvPolynomial (Fin (N + 1)) K)
    (hLhom : L.IsHomogeneous 1) (hL : L ∉ I)
    (hle : I ⊔ Ideal.span ({L} : Set _) ≤ J)
    (hsat : ∀ F ∈ J, ∀ i : Fin (N + 1),
      ∃ k : ℕ, X i ^ k * F ∈ I ⊔ Ideal.span ({L} : Set _)) :
    Module.finrank K (projectiveHilbertPiece K N J 1) + 1 =
      Module.finrank K (projectiveHilbertPiece K N I 1) := by
  have hpart := projectiveSection_saturation_degreeOnePart_eq
    I J hI hhom L hLhom hL hle hsat
  have hJsum := finrank_degreeOnePart_add_quotientHomogeneousComponent_eq J
  have hSsum := finrank_degreeOnePart_add_quotientHomogeneousComponent_eq
    (I ⊔ Ideal.span ({L} : Set _))
  rw [hpart] at hJsum
  have hdrop := projectiveSection_hilbertOne_add_one I hI hhom L hLhom hL
  change Module.finrank K (quotientHomogeneousComponent K (Fin (N + 1)) J 1) + 1 =
    Module.finrank K (quotientHomogeneousComponent K (Fin (N + 1)) I 1)
  omega

end

end TranslatedDepthSeven

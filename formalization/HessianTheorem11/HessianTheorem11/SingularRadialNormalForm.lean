import HessianTheorem11.SingularRadialEquality
import HessianTheorem11.LocalCubicNormalForm

/-! Actual quadratic coefficient forms in the singular radial weight-zero
limit. The normal form is constructed from support filters and derivatives. -/
noncomputable section
namespace HessianTheorem11.SingularRadialNormalForm
open MvPolynomial Module NonzeroLimitTransport SingularRadialEquality
open scoped BigOperators

variable {K : Type*} [Field K] {n : ℕ}

/-- The three possible exponent distributions of a weight-zero cubic. -/
theorem exponent_distribution (radial : Fin n) (IT IL : Finset (Fin n))
    (hr : radial ∈ IT) (hnest : IT ⊆ IL) (d : Fin n →₀ ℕ)
    (hd : d.degree = 3) (hw : monomialWeight (singularRadialWeight radial IT IL) d = 0) :
    (d radial = 1 ∧ (∑ i ∈ IT, d i) = 1 ∧ (∑ i ∈ IL, d i) = 1 ∧
      (∑ i ∈ ILᶜ, d i) = 2) ∨
    (d radial = 0 ∧ (∑ i ∈ IT, d i) = 2 ∧ (∑ i ∈ IL, d i) = 2 ∧
      (∑ i ∈ ILᶜ, d i) = 1) ∨
    (d radial = 0 ∧ (∑ i ∈ IT, d i) = 0 ∧ (∑ i ∈ IL, d i) = 3 ∧
      (∑ i ∈ ILᶜ, d i) = 0) := by
  classical
  have hrad : d radial ≤ ∑ i ∈ IT, d i := Finset.single_le_sum (by intros; omega) hr
  have hTL : (∑ i ∈ IT, d i) ≤ ∑ i ∈ IL, d i :=
    Finset.sum_le_sum_of_subset_of_nonneg hnest (by intros; omega)
  have hLD : (∑ i ∈ IL, d i) ≤ 3 := by
    rw [← hd, Finsupp.degree_eq_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; omega)
  have hC := Finset.sum_compl_add_sum IL (fun i => d i)
  rw [← Finsupp.degree_eq_sum, hd] at hC
  rw [monomialWeight_singularRadialWeight, hd] at hw
  omega

/-- Filter by an arbitrary decidable condition on actual exponents. -/
def exponentPart (P : MvPolynomial (Fin n) K) (condition : (Fin n →₀ ℕ) → Prop) :
    MvPolynomial (Fin n) K := by classical exact Finsupp.filter condition P

@[simp] theorem coeff_exponentPart (P : MvPolynomial (Fin n) K)
    (condition : (Fin n →₀ ℕ) → Prop) [DecidablePred condition] (d : Fin n →₀ ℕ) :
    coeff d (exponentPart P condition) = if condition d then coeff d P else 0 := by
  classical
  by_cases h : condition d <;> simp [exponentPart, coeff, h]

theorem exponentPart_homogeneous {P : MvPolynomial (Fin n) K} {k : ℕ}
    (hP : P.IsHomogeneous k) (condition : (Fin n →₀ ℕ) → Prop) :
    (exponentPart P condition).IsHomogeneous k := by
  classical
  intro d hd
  apply hP
  intro hz
  exact hd (by simp [hz])

theorem mem_support_exponentPart (P : MvPolynomial (Fin n) K)
    (condition : (Fin n →₀ ℕ) → Prop) (d : Fin n →₀ ℕ) :
    d ∈ (exponentPart P condition).support ↔ d ∈ P.support ∧ condition d := by
  classical
  exact Finset.mem_filter

def radialPart (P : MvPolynomial (Fin n) K) (radial : Fin n) :=
  exponentPart P (fun d => d radial = 1)

def normalPart (P : MvPolynomial (Fin n) K) (radial : Fin n) (IL : Finset (Fin n)) :=
  exponentPart P (fun d => d radial = 0 ∧ (∑ i ∈ ILᶜ, d i) = 1)

def complementaryPart (P : MvPolynomial (Fin n) K) (radial : Fin n) (IL : Finset (Fin n)) :=
  exponentPart P (fun d => d radial = 0 ∧ (∑ i ∈ ILᶜ, d i) = 0)

theorem equals_three_parts (P : MvPolynomial (Fin n) K) (hP : P.IsHomogeneous 3)
    (radial : Fin n) (IT IL : Finset (Fin n)) (hr : radial ∈ IT) (hnest : IT ⊆ IL)
    (hw : ∀ d ∈ P.support, monomialWeight (singularRadialWeight radial IT IL) d = 0) :
    P = radialPart P radial + normalPart P radial IL + complementaryPart P radial IL := by
  classical
  ext d
  by_cases hd : coeff d P = 0
  · simp [radialPart, normalPart, complementaryPart, hd]
  have hdeg : d.degree = 3 := by rw [Finsupp.degree_eq_weight_one]; exact hP hd
  obtain h | h | h := exponent_distribution radial IT IL hr hnest d hdeg
    (hw d (Finsupp.mem_support_iff.mpr hd))
  all_goals simp only [radialPart, normalPart, complementaryPart, coeff_add, coeff_exponentPart, h.1, h.2.2.2]
  all_goals norm_num

/-- Euler identity in an arbitrary chosen block of variables. -/
theorem block_euler (P : MvPolynomial (Fin n) K) (S : Finset (Fin n)) (k : ℕ)
    (hP : ∀ d ∈ P.support, (∑ i ∈ S, d i) = k) :
    ∑ i ∈ S, X i * pderiv i P = k • P := by
  classical
  have h : P.IsWeightedHomogeneous (fun i => if i ∈ S then 1 else 0) k := by
    intro d hd
    have hsum := hP d (Finsupp.mem_support_iff.mpr hd)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype] <;> try { intros; simp }
    simpa [mul_ite, ← Finset.sum_filter] using hsum
  have he := h.sum_weight_X_mul_pderiv
  simpa [ite_smul, ← Finset.sum_filter] using he

/-- The radial and normal coefficient quadrics are actual derivatives of
the corresponding filtered polynomials. -/
def normalQuadratic (P : MvPolynomial (Fin n) K) (radial : Fin n) :=
  pderiv radial (radialPart P radial)

def normalMapComponent (P : MvPolynomial (Fin n) K) (radial : Fin n)
    (IL : Finset (Fin n)) (i : Fin n) := pderiv i (normalPart P radial IL)

theorem exact_normal_form (P : MvPolynomial (Fin n) K) (hP : P.IsHomogeneous 3)
    (radial : Fin n) (IT IL : Finset (Fin n)) (hr : radial ∈ IT) (hnest : IT ⊆ IL)
    (hw : ∀ d ∈ P.support, monomialWeight (singularRadialWeight radial IT IL) d = 0) :
    P = X radial * normalQuadratic P radial +
      (∑ i ∈ ILᶜ, X i * normalMapComponent P radial IL i) + complementaryPart P radial IL := by
  classical
  have hR : X radial * pderiv radial (radialPart P radial) = radialPart P radial := by
    have h := block_euler (radialPart P radial) {radial} 1 (by
      intro d hd
      have hm := (mem_support_exponentPart P (fun d => d radial = 1) d).mp hd
      simpa using hm.2)
    simpa using h
  have hD : (∑ i ∈ ILᶜ, X i * pderiv i (normalPart P radial IL)) = normalPart P radial IL := by
    have h := block_euler (normalPart P radial IL) ILᶜ 1 (by
      intro d hd
      exact ((mem_support_exponentPart P _ d).mp hd).2.2)
    simpa using h
  rw [normalQuadratic, show (∑ i ∈ ILᶜ, X i * normalMapComponent P radial IL i) =
    ∑ i ∈ ILᶜ, X i * pderiv i (normalPart P radial IL) from rfl, hR, hD]
  exact equals_three_parts P hP radial IT IL hr hnest hw

theorem normalQuadratic_homogeneous {P : MvPolynomial (Fin n) K} (hP : P.IsHomogeneous 3)
    (radial : Fin n) : (normalQuadratic P radial).IsHomogeneous 2 :=
  (exponentPart_homogeneous hP _).pderiv

theorem normalMapComponent_homogeneous {P : MvPolynomial (Fin n) K} (hP : P.IsHomogeneous 3)
    (radial : Fin n) (IL : Finset (Fin n)) (i : Fin n) :
    (normalMapComponent P radial IL i).IsHomogeneous 2 :=
  (exponentPart_homogeneous hP _).pderiv

/-- Every support exponent of an actual derivative comes from a support
exponent of the original polynomial, with one occurrence removed. -/
theorem derivative_support_preimage (P : MvPolynomial (Fin n) K) (i : Fin n)
    (d : Fin n →₀ ℕ) (hd : d ∈ (pderiv i P).support) :
    ∃ e ∈ P.support, e i ≠ 0 ∧ d = e - Finsupp.single i 1 := by
  classical
  have he : pderiv i P = ∑ e ∈ P.support, pderiv i (monomial e (coeff e P)) := by
    conv_lhs => rw [← P.support_sum_monomial_coeff]
    exact map_sum (pderiv i) _ _
  rw [he] at hd
  obtain ⟨e, he, hed⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  rw [pderiv_monomial] at hed
  have hi : e i ≠ 0 := by
    intro hz
    simp [hz] at hed
  exact ⟨e, he, hi, Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hed)⟩

theorem derivative_vars_subset (P : MvPolynomial (Fin n) K) (i : Fin n)
    (S : Finset (Fin n))
    (hP : ∀ e ∈ P.support, e i ≠ 0 → (e - Finsupp.single i 1).support ⊆ S) :
    (pderiv i P).vars ⊆ S := by
  intro j hj
  obtain ⟨d, hd, hjd⟩ := (MvPolynomial.mem_vars j).mp hj
  obtain ⟨e, he, hi, rfl⟩ := derivative_support_preimage P i d hd
  exact hP e he hi hjd

theorem sum_eq_coordinate_forces_zero (S : Finset (Fin n)) (d : Fin n →₀ ℕ)
    (i j : Fin n) (hi : i ∈ S) (hj : j ∈ S) (hji : j ≠ i)
    (hs : (∑ k ∈ S, d k) = d i) : d j = 0 := by
  classical
  have he := Finset.sum_erase_add S (fun k => d k) hi
  dsimp only at he
  have hz : ∑ k ∈ S.erase i, d k = 0 := by omega
  exact Finset.sum_eq_zero_iff.mp hz j (Finset.mem_erase.mpr ⟨hji,hj⟩)

/-- Removing the unique occurrence in a block removes that block entirely. -/
theorem derivative_exponent_support_avoids_block (S : Finset (Fin n))
    (d : Fin n →₀ ℕ) (i : Fin n) (hi : i ∈ S)
    (hs : (∑ j ∈ S, d j) = 1) (hdi : d i ≠ 0) :
    (d - Finsupp.single i 1).support ⊆ Sᶜ := by
  classical
  have hle : d i ≤ 1 := hs ▸ Finset.single_le_sum (by intros; omega) hi
  have heq : d i = 1 := by omega
  intro j hj
  apply Finset.mem_compl.mpr
  intro hjS
  have hval : (d - Finsupp.single i 1 : Fin n →₀ ℕ) j = 0 := by
    by_cases hji : j = i
    · subst j; simp [Finsupp.tsub_apply, heq]
    · have hdj := sum_eq_coordinate_forces_zero S d i j hi hjS hji (hs.trans heq.symm)
      simp [Finsupp.tsub_apply, hdj]
  exact Finsupp.mem_support_iff.mp hj hval

/-- The radial quadratic genuinely depends only on the normal variables. -/
theorem normalQuadratic_vars (P : MvPolynomial (Fin n) K) (hP : P.IsHomogeneous 3)
    (radial : Fin n) (IT IL : Finset (Fin n)) (hr : radial ∈ IT) (hnest : IT ⊆ IL)
    (hw : ∀ d ∈ P.support, monomialWeight (singularRadialWeight radial IT IL) d = 0) :
    (normalQuadratic P radial).vars ⊆ ILᶜ := by
  apply derivative_vars_subset
  intro e he hei
  have hm := (mem_support_exponentPart P (fun e => e radial = 1) e).mp he
  have hdeg : e.degree = 3 := by
    rw [Finsupp.degree_eq_weight_one]
    exact hP (Finsupp.mem_support_iff.mp hm.1)
  have hc := exponent_distribution radial IT IL hr hnest e hdeg (hw e hm.1)
  have hL : (∑ i ∈ IL, e i) = 1 := by rcases hc with h|h|h <;> omega
  exact derivative_exponent_support_avoids_block IL e radial (hnest hr) hL hei

/-- Each normal-map quadratic genuinely depends only on the nonradial
variables of the tangent space. -/
theorem normalMapComponent_vars (P : MvPolynomial (Fin n) K) (hP : P.IsHomogeneous 3)
    (radial : Fin n) (IT IL : Finset (Fin n)) (hr : radial ∈ IT) (hnest : IT ⊆ IL)
    (hw : ∀ d ∈ P.support, monomialWeight (singularRadialWeight radial IT IL) d = 0)
    (i : Fin n) (hi : i ∈ ILᶜ) :
    (normalMapComponent P radial IL i).vars ⊆ IT.erase radial := by
  classical
  apply derivative_vars_subset
  intro e he hei
  have hm := (mem_support_exponentPart P _ e).mp he
  have hdeg : e.degree = 3 := by
    rw [Finsupp.degree_eq_weight_one]
    exact hP (Finsupp.mem_support_iff.mp hm.1)
  have hc := exponent_distribution radial IT IL hr hnest e hdeg (hw e hm.1)
  have hT : (∑ j ∈ IT, e j) = 2 := by rcases hc with h|h|h <;> omega
  have hL : (∑ j ∈ IL, e j) = 2 := by rcases hc with h|h|h <;> omega
  have hC : ∑ j ∈ IL \ IT, e j = 0 := by
    have h := Finset.sum_sdiff (f := fun j => e j) hnest
    dsimp only at h
    omega
  have havoid := derivative_exponent_support_avoids_block ILᶜ e i hi hm.2.2 hei
  intro j hj
  have hjL : j ∈ IL := by simpa using havoid hj
  have hej : e j ≠ 0 := by
    intro hz
    apply Finsupp.mem_support_iff.mp hj
    simp [Finsupp.tsub_apply, hz]
  have hjT : j ∈ IT := by
    by_contra h
    exact hej (Finset.sum_eq_zero_iff.mp hC j (Finset.mem_sdiff.mpr ⟨hjL,h⟩))
  have hjr : j ≠ radial := by
    intro h
    subst j
    exact hej hm.2.1
  exact Finset.mem_erase.mpr ⟨hjr,hjT⟩

/-- The complementary cubic depends only on the complementary block. -/
theorem complementaryPart_vars (P : MvPolynomial (Fin n) K) (hP : P.IsHomogeneous 3)
    (radial : Fin n) (IT IL : Finset (Fin n)) (hr : radial ∈ IT) (hnest : IT ⊆ IL)
    (hw : ∀ d ∈ P.support, monomialWeight (singularRadialWeight radial IT IL) d = 0) :
    (complementaryPart P radial IL).vars ⊆ (IT ∪ ILᶜ)ᶜ := by
  classical
  intro j hj
  obtain ⟨e, he, hje⟩ := (MvPolynomial.mem_vars j).mp hj
  have hm := (mem_support_exponentPart P _ e).mp he
  have hdeg : e.degree = 3 := by
    rw [Finsupp.degree_eq_weight_one]
    exact hP (Finsupp.mem_support_iff.mp hm.1)
  have hc := exponent_distribution radial IT IL hr hnest e hdeg (hw e hm.1)
  have hT : (∑ i ∈ IT, e i) = 0 := by rcases hc with h|h|h <;> omega
  have hjT : j ∉ IT := by
    intro h
    exact Finsupp.mem_support_iff.mp hje (Finset.sum_eq_zero_iff.mp hT j h)
  have hjL : j ∈ IL := by
    by_contra h
    exact Finsupp.mem_support_iff.mp hje
      (Finset.sum_eq_zero_iff.mp hm.2.2 j (Finset.mem_compl.mpr h))
  simp [hjT,hjL]

/-- Differentiating the constructed normal form in the radial coordinate
recovers exactly its normal quadratic. -/
theorem radial_partial_eq_normalQuadratic (P : MvPolynomial (Fin n) K) (hP : P.IsHomogeneous 3)
    (radial : Fin n) (IT IL : Finset (Fin n)) (hr : radial ∈ IT) (hnest : IT ⊆ IL)
    (hw : ∀ d ∈ P.support, monomialWeight (singularRadialWeight radial IT IL) d = 0) :
    pderiv radial P = normalQuadratic P radial := by
  classical
  have hq : pderiv radial (normalQuadratic P radial) = 0 :=
    pderiv_eq_zero_of_notMem_vars (by
      intro h
      exact Finset.mem_compl.mp (normalQuadratic_vars P hP radial IT IL hr hnest hw h) (hnest hr))
  have hp (i : Fin n) (hi : i ∈ ILᶜ) : pderiv radial (normalMapComponent P radial IL i) = 0 :=
    pderiv_eq_zero_of_notMem_vars (by
      intro h
      exact Finset.notMem_erase radial IT
        (normalMapComponent_vars P hP radial IT IL hr hnest hw i hi h))
  have hK : pderiv radial (complementaryPart P radial IL) = 0 :=
    pderiv_eq_zero_of_notMem_vars (by
      intro h
      exact Finset.mem_compl.mp (complementaryPart_vars P hP radial IT IL hr hnest hw h)
        (Finset.mem_union_left _ hr))
  conv_lhs => rw [exact_normal_form P hP radial IT IL hr hnest hw]
  simp only [map_add, map_sum, pderiv_mul, pderiv_X_self, one_mul, hq, mul_zero,
    add_zero, hK]
  have hs : (∑ i ∈ ILᶜ, ((pderiv radial (X i)) * normalMapComponent P radial IL i +
      X i * pderiv radial (normalMapComponent P radial IL i))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hir : i ≠ radial := by
      intro h
      subst i
      exact Finset.mem_compl.mp hi (hnest hr)
    simp [pderiv_X_of_ne hir, hp i hi]
  rw [hs, add_zero]

/-- The Hessian at a coordinate vector is the constant Hessian of the
corresponding first derivative of a cubic. -/
theorem hessian_at_radial (P : MvPolynomial (Fin n) K) (hP : P.IsHomogeneous 3)
    (radial : Fin n) :
    hessian P (Pi.single radial 1) = LocalCubicNormalForm.quadraticMatrix (pderiv radial P) := by
  classical
  apply Matrix.ext
  intro i j
  have he := eval_homogeneous_one (hessian_entry_homogeneous_one hP i j) (Pi.single radial 1)
  have hp : pderiv j (pderiv i (pderiv radial P)) =
      pderiv radial (pderiv j (pderiv i P)) := by
    rw [partials_commute P i radial, partials_commute (pderiv i P) j radial]
  simpa [hessian, hessianPolynomial, LocalCubicNormalForm.quadraticMatrix, hp, Pi.single_apply] using he

theorem normalQuadratic_hessian (P : MvPolynomial (Fin n) K) (hP : P.IsHomogeneous 3)
    (radial : Fin n) (IT IL : Finset (Fin n)) (hr : radial ∈ IT) (hnest : IT ⊆ IL)
    (hw : ∀ d ∈ P.support, monomialWeight (singularRadialWeight radial IT IL) d = 0) :
    LocalCubicNormalForm.quadraticMatrix (normalQuadratic P radial) =
      hessian P (Pi.single radial 1) := by
  rw [hessian_at_radial P hP radial, radial_partial_eq_normalQuadratic P hP radial IT IL hr hnest hw]

/-- Equality in the singular radial bound has `3r-3` active coordinates.
The identity is stated without truncated subtraction. -/
theorem equality_dimensions_general (r : ℕ) (radial : Fin n) (IT IL : Finset (Fin n))
    (hnest : IT ⊆ IL) (hT : IT.card + 3 = 2*r) (hL : IL.card + r = n) :
    (IT ∪ ILᶜ).card + 3 = 3*r ∧
      (∑ i, singularRadialWeight radial IT IL i) = 0 := by
  classical
  have hd : Disjoint IT ILᶜ := Finset.disjoint_left.mpr (by
    intro i hi hni
    exact Finset.mem_compl.mp hni (hnest hi))
  have hLc := Finset.card_compl IL
  simp only [Fintype.card_fin] at hLc
  constructor
  · rw [Finset.card_union_of_disjoint hd]
    omega
  · rw [sum_singularRadialWeight]
    omega

/-- Actual singular radial transport fixes the radial coordinate. -/
theorem upperUnipotent_fixes_radial (radial : Fin n) (IT IL : Finset (Fin n))
    (hr : radial ∈ IT) (hnest : IT ⊆ IL)
    (U : Matrix (Fin n) (Fin n) K)
    (hU : WeightUpperUnipotent (singularRadialWeight radial IT IL) U) :
    U.mulVec (Pi.single radial 1) = Pi.single radial 1 := by
  apply hU.fixes_minimum_column
  intro i
  rw [singularRadialWeight_radial hr hnest]
  by_cases hir : i = radial
  · subst i
    rw [singularRadialWeight_radial hr hnest]
  · have h := singularRadialWeight_lower (IT := IT) (IL := IL) hir
    omega

/-- Actual unipotent transport preserves the normal quadratic rank because
it fixes the radial point and the Hessian changes by an invertible congruence. -/
theorem normalQuadratic_rank_of_transport
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (x : GeometricPoint n) (T : Submodule GeometricField (GeometricPoint n))
    (A : AdaptedFlagBasis T (LinearMap.ker (hessian F x).mulVecLin) x)
    (U : Matrix (Fin n) (Fin n) GeometricField) (hUdet : U.det = 1)
    (hU : WeightUpperUnipotent (singularRadialWeight A.radial A.tangentIndices A.kernelIndices) U)
    (he : zeroWeightPart (PolynomialRestriction.restrict (HessianTheorem11.basisMatrix A.basis) F)
        (singularRadialWeight A.radial A.tangentIndices A.kernelIndices) =
      PolynomialRestriction.restrict U
        (PolynomialRestriction.restrict (HessianTheorem11.basisMatrix A.basis) F)) :
    (LocalCubicNormalForm.quadraticMatrix (normalQuadratic
      (zeroWeightPart (PolynomialRestriction.restrict (HessianTheorem11.basisMatrix A.basis) F)
        (singularRadialWeight A.radial A.tangentIndices A.kernelIndices)) A.radial)).rank =
      (hessian F x).rank := by
  let P := PolynomialRestriction.restrict (HessianTheorem11.basisMatrix A.basis) F
  let w := singularRadialWeight A.radial A.tangentIndices A.kernelIndices
  have hPh : P.IsHomogeneous 3 := PolynomialRestriction.homogeneous_restrict _ _ hF
  rw [normalQuadratic_hessian (zeroWeightPart P w) (zeroWeightPart_homogeneous hPh w)
    A.radial A.tangentIndices A.kernelIndices A.radial_mem A.indices_nested (zeroWeightPart_weights P w)]
  rw [he]
  have hUy := upperUnipotent_fixes_radial A.radial A.tangentIndices A.kernelIndices
    A.radial_mem A.indices_nested U hU
  have h1 := BasisHessianTransport.hessian_rank_restrict
    (matrixBasis U (injective_of_det_one U hUdet)) P (Pi.single A.radial 1)
  simp only [matrixBasis_matrix] at h1
  change (hessian (PolynomialRestriction.restrict U P) (Pi.single A.radial 1)).rank =
    (hessian P (U.mulVec (Pi.single A.radial 1))).rank at h1
  rw [h1, hUy]
  have h2 := BasisHessianTransport.hessian_rank_restrict A.basis F (Pi.single A.radial 1)
  change (hessian P (Pi.single A.radial 1)).rank =
    (hessian F ((HessianTheorem11.basisMatrix A.basis).mulVec (Pi.single A.radial 1))).rank at h2
  have hAy : (HessianTheorem11.basisMatrix A.basis).mulVec (Pi.single A.radial 1) = x := by
    rw [Matrix.mulVec_single_one]
    exact A.radial_eq
  rw [h2, hAy]

/-- Equality data with arbitrary rank, in actual adapted coordinates. The
quadratic and normal-map polynomials are obtained by the definitions above. -/
structure EqualityData (r : ℕ) (F : GeometricPolynomial n) (x : GeometricPoint n)
    (T : Submodule GeometricField (GeometricPoint n)) where
  flag : AdaptedFlagBasis T (LinearMap.ker (hessian F x).mulVecLin) x
  active_card : (flag.tangentIndices ∪ flag.kernelIndicesᶜ).card + 3 = 3*r
  weight_sum : ∑ i, singularRadialWeight flag.radial flag.tangentIndices flag.kernelIndices i = 0
  nonnegative : HasNonnegativeWeights
    (PolynomialRestriction.restrict (HessianTheorem11.basisMatrix flag.basis) F)
    (singularRadialWeight flag.radial flag.tangentIndices flag.kernelIndices)
  transport : ∃ U : Matrix (Fin n) (Fin n) GeometricField,
    U.det = 1 ∧ WeightUpperUnipotent
      (singularRadialWeight flag.radial flag.tangentIndices flag.kernelIndices) U ∧
    zeroWeightPart (PolynomialRestriction.restrict (HessianTheorem11.basisMatrix flag.basis) F)
      (singularRadialWeight flag.radial flag.tangentIndices flag.kernelIndices) =
      PolynomialRestriction.restrict U
        (PolynomialRestriction.restrict (HessianTheorem11.basisMatrix flag.basis) F)
  normal_rank : (LocalCubicNormalForm.quadraticMatrix (normalQuadratic
    (zeroWeightPart (PolynomialRestriction.restrict (HessianTheorem11.basisMatrix flag.basis) F)
      (singularRadialWeight flag.radial flag.tangentIndices flag.kernelIndices)) flag.radial)).rank = r
  limit_irreducible : Irreducible (zeroWeightPart
    (PolynomialRestriction.restrict (HessianTheorem11.basisMatrix flag.basis) F)
    (singularRadialWeight flag.radial flag.tangentIndices flag.kernelIndices))
  limit_hessianDeterminant_ne_zero : hessianDeterminantPolynomial (zeroWeightPart
    (PolynomialRestriction.restrict (HessianTheorem11.basisMatrix flag.basis) F)
    (singularRadialWeight flag.radial flag.tangentIndices flag.kernelIndices)) ≠ 0

theorem nonempty_equalityData
    (boundary : RationalRelativeBoundaryInput) (bigCell : TextbookOrbitBigCellInput)
    (F : AnisotropicCubic n) (hn : 0 < n) (r : ℕ)
    (hirred : Irreducible (geometricPolynomial F.polynomial))
    (hdet : hessianDeterminantPolynomial (geometricPolynomial F.polynomial) ≠ 0)
    (x : GeometricPoint n) (hx : x ≠ 0)
    (T : Submodule GeometricField (GeometricPoint n)) (hxT : x ∈ T)
    (hTL : T ≤ LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin)
    (htensor : ∀ t ∈ T,
      ∀ u ∈ LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin,
      polarization (geometricPolynomial F.polynomial) t u v = 0)
    (hT : finrank GeometricField T + 3 = 2*r)
    (hR : (hessian (geometricPolynomial F.polynomial) x).rank = r) :
    Nonempty (EqualityData r (geometricPolynomial F.polynomial) x T) := by
  let P := geometricPolynomial F.polynomial
  let A := adaptedFlagBasis T (LinearMap.ker (hessian P x).mulVecLin) hTL x hx hxT
  have hcardT : A.tangentIndices.card + 3 = 2*r := by rw [A.tangent_card]; exact hT
  have hcardL : A.kernelIndices.card + r = n := by
    rw [A.kernel_card]
    have h := (hessian P x).mulVecLin.finrank_range_add_finrank_ker
    change (hessian P x).rank + finrank GeometricField (LinearMap.ker (hessian P x).mulVecLin) =
      finrank GeometricField (GeometricPoint n) at h
    rw [hR] at h
    simpa [add_comm] using h
  obtain ⟨hcard, hsum⟩ := equality_dimensions_general r A.radial A.tangentIndices A.kernelIndices
    A.indices_nested hcardT hcardL
  have hhom := geometric_homogeneous F.homogeneous
  have hnonneg := nonnegative_in_adapted_flag P hhom x T A htensor
  obtain ⟨U,hUdet,hU,he⟩ := anisotropic_zeroWeightPart_transport boundary bigCell F hn
    (HessianTheorem11.basisMatrix A.basis) (basisMatrix_injective A.basis) _ hsum hnonneg
  have hq := normalQuadratic_rank_of_transport P hhom x T A U hUdet hU he
  obtain ⟨hi, hd⟩ := zeroWeightPart_irreducible_and_hessianDeterminant_ne_zero
    boundary bigCell F hn hirred hdet (HessianTheorem11.basisMatrix A.basis)
    (basisMatrix_injective A.basis) _ hsum hnonneg
  exact ⟨⟨A,hcard,hsum,hnonneg,⟨U,hUdet,hU,he⟩,hq.trans hR,hi,hd⟩⟩

/-- A polynomial supported on a block comes from that block's actual
polynomial ring, preserving homogeneous degree. -/
theorem exists_block_polynomial (P : MvPolynomial (Fin n) K) {k : ℕ}
    (hP : P.IsHomogeneous k) (S : Finset (Fin n)) (hvars : P.vars ⊆ S) :
    ∃ Q : MvPolynomial S K, Q.IsHomogeneous k ∧ rename (fun i : S => (i : Fin n)) Q = P := by
  obtain ⟨Q,hQ⟩ := exists_rename_eq_of_vars_subset_range P (fun i : S => (i : Fin n))
    Subtype.val_injective (by intro i hi; exact ⟨⟨i,hvars hi⟩,rfl⟩)
  refine ⟨Q,?_,hQ⟩
  apply (MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff Subtype.val_injective).mp
  rwa [hQ]

/-- The exact singular normal form with its quadrics and complementary
cubic in separate, actual coordinate polynomial rings. -/
theorem exists_typed_normal_form (P : MvPolynomial (Fin n) K) (hP : P.IsHomogeneous 3)
    (radial : Fin n) (IT IL : Finset (Fin n)) (hr : radial ∈ IT) (hnest : IT ⊆ IL)
    (hw : ∀ d ∈ P.support, monomialWeight (singularRadialWeight radial IT IL) d = 0) :
    ∃ q : MvPolynomial (↑ILᶜ : Type) K,
    ∃ p : (↑ILᶜ : Type) → MvPolynomial (↑(IT.erase radial) : Type) K,
    ∃ R : MvPolynomial (↑((IT ∪ ILᶜ)ᶜ) : Type) K,
      q.IsHomogeneous 2 ∧ (∀ i, (p i).IsHomogeneous 2) ∧ R.IsHomogeneous 3 ∧
      rename (fun i : (↑ILᶜ : Type) => (i : Fin n)) q = normalQuadratic P radial ∧
      (∀ i, rename (fun j : (↑(IT.erase radial) : Type) => (j : Fin n)) (p i) =
        normalMapComponent P radial IL i) ∧
      P = X radial * rename (fun i : (↑ILᶜ : Type) => (i : Fin n)) q +
        (∑ i : (↑ILᶜ : Type), X (i : Fin n) *
          rename (fun j : (↑(IT.erase radial) : Type) => (j : Fin n)) (p i)) +
        rename (fun i : (↑((IT ∪ ILᶜ)ᶜ) : Type) => (i : Fin n)) R := by
  classical
  obtain ⟨q,hq,hqe⟩ := exists_block_polynomial (normalQuadratic P radial)
    (normalQuadratic_homogeneous hP radial) ILᶜ (normalQuadratic_vars P hP radial IT IL hr hnest hw)
  have hp : ∀ i : (↑ILᶜ : Type), ∃ Q : MvPolynomial (↑(IT.erase radial) : Type) K,
      Q.IsHomogeneous 2 ∧ rename (fun j : (↑(IT.erase radial) : Type) => (j : Fin n)) Q =
        normalMapComponent P radial IL i := by
    intro i
    exact exists_block_polynomial (normalMapComponent P radial IL i)
      (normalMapComponent_homogeneous hP radial IL i) _
      (normalMapComponent_vars P hP radial IT IL hr hnest hw i i.property)
  choose p hp hpe using hp
  obtain ⟨R,hR,hRe⟩ := exists_block_polynomial (complementaryPart P radial IL)
    (exponentPart_homogeneous hP _) _ (complementaryPart_vars P hP radial IT IL hr hnest hw)
  refine ⟨q,p,R,hq,hp,hR,hqe,hpe,?_⟩
  simp_rw [hqe,hpe,hRe]
  rw [Finset.sum_coe_sort ILᶜ (fun i => X i * normalMapComponent P radial IL i)]
  exact exact_normal_form P hP radial IT IL hr hnest hw

/-- The weight-zero polynomial attached to equality data. -/
def EqualityData.limit {r : ℕ} {F : GeometricPolynomial n} {x : GeometricPoint n}
    {T : Submodule GeometricField (GeometricPoint n)} (D : EqualityData r F x T) :
    GeometricPolynomial n :=
  zeroWeightPart (PolynomialRestriction.restrict (HessianTheorem11.basisMatrix D.flag.basis) F)
    (singularRadialWeight D.flag.radial D.flag.tangentIndices D.flag.kernelIndices)

theorem EqualityData.limit_homogeneous {r : ℕ} {F : GeometricPolynomial n}
    (hF : F.IsHomogeneous 3) {x : GeometricPoint n}
    {T : Submodule GeometricField (GeometricPoint n)} (D : EqualityData r F x T) :
    D.limit.IsHomogeneous 3 :=
  zeroWeightPart_homogeneous (PolynomialRestriction.homogeneous_restrict _ _ hF) _

theorem EqualityData.twelve_active_of_rank_five {F : GeometricPolynomial n} {x : GeometricPoint n}
    {T : Submodule GeometricField (GeometricPoint n)} (D : EqualityData 5 F x T) :
    (D.flag.tangentIndices ∪ D.flag.kernelIndicesᶜ).card = 12 := by
  have h := D.active_card
  omega

end HessianTheorem11.SingularRadialNormalForm

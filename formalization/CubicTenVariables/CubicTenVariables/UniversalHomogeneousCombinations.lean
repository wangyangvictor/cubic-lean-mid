import CubicTenVariables.HomogeneousFamilyDeterminant

/-! Universal homogeneous combinations and their square coefficient determinant.
Every literal common-degree certificate is an evaluation of these universal
coefficients. A nonzero evaluated determinant proves finiteness of the actual
specialized equation quotient. No dimension-locus or spreading conclusion is
assumed or asserted here. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.UniversalHomogeneousCombinations
open MvPolynomial HomogeneousMacaulayCertificates HomogeneousFamilyDeterminant
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

variable {n N : ℕ} {ι : Type*} [Fintype ι]
local instance (n d : ℕ) : Fintype (monomialIndices n d) := Fintype.ofFinite _
local instance (n d : ℕ) : DecidableEq (monomialIndices n d) := Classical.decEq _

/-- There are finitely many coefficients in the displayed homogeneous forms. -/
abbrev CoefficientVariable (n N : ℕ) (e : ι → ℕ) :=
  monomialIndices n N × (Σ j : ι, monomialIndices n (N - e j))

/-- One homogeneous coefficient in a universal degree-`N` row combination.
Generators with degree above `N` have zero coefficients. -/
def coefficientForm (R : Type*) [CommRing R] (e : ι → ℕ)
    (s : monomialIndices n N) (j : ι) :
    MvPolynomial (Fin n) (MvPolynomial (CoefficientVariable n N e) R) :=
  if e j ≤ N then
    ∑ t : monomialIndices n (N - e j), monomial t.val (X (s, ⟨j, t⟩))
  else 0

omit [Fintype ι] in
theorem coefficientForm_homogeneous (R : Type*) [CommRing R] (e : ι → ℕ)
    (s : monomialIndices n N) (j : ι) :
    (coefficientForm R e s j).IsHomogeneous (N - e j) := by
  classical
  unfold coefficientForm
  split
  · exact (homogeneousSubmodule _ _ _).sum_mem
      (fun t _ => isHomogeneous_monomial _ t.property)
  · exact isHomogeneous_zero _ _ _

omit [Fintype ι] in
theorem coefficientForm_eq_zero (R : Type*) [CommRing R] (e : ι → ℕ)
    (s : monomialIndices n N) (j : ι) (h : N < e j) :
    coefficientForm R e s j = 0 := by
  simp [coefficientForm, Nat.not_le.mpr h]

/-- Reconstruction from all coefficients in one homogeneous degree. -/
theorem sum_monomial_coeff_of_homogeneous {K : Type*} [CommRing K] {d : ℕ}
    (P : MvPolynomial (Fin n) K) (hP : P.IsHomogeneous d) :
    (∑ t : monomialIndices n d, monomial t.val (coeff t.val P)) = P := by
  classical
  ext u
  rw [coeff_sum]
  by_cases hu : u.degree = d
  · let t : monomialIndices n d := ⟨u, hu⟩
    rw [Finset.sum_eq_single t]
    · simp [t]
    · intro b _ hbt
      have hbu : b.val ≠ u := fun h => hbt (Subtype.ext h)
      simp [coeff_monomial, hbu]
    · simp
  · have hz : ∀ t : monomialIndices n d, coeff u (monomial t.val (coeff t.val P)) = 0 := by
      intro t
      have htu : t.val ≠ u := fun h => hu (h ▸ t.property)
      simp [coeff_monomial, htu]
    simp only [hz, Finset.sum_const_zero, hP.coeff_eq_zero hu]

omit [Fintype ι] in
/-- Every possible homogeneous coefficient family is one evaluation of the
universal coefficient forms, for any coefficient-ring specialization. -/
theorem coefficientForm_realizes {R K : Type*} [CommRing R] [CommRing K]
    (ρ : R →+* K) (e : ι → ℕ)
    (c : monomialIndices n N → ι → MvPolynomial (Fin n) K)
    (hc : ∀ s j, (c s j).IsHomogeneous (N - e j))
    (hz : ∀ s j, N < e j → c s j = 0) :
    ∃ a : CoefficientVariable n N e → K,
      ∀ s j, map (eval₂Hom ρ a) (coefficientForm R e s j) = c s j := by
  classical
  refine ⟨fun v => coeff v.2.2.val (c v.1 v.2.1), ?_⟩
  intro s j
  by_cases hj : e j ≤ N
  · simpa [coefficientForm, hj] using
      sum_monomial_coeff_of_homogeneous (c s j) (hc s j)
  · simp [coefficientForm, hj, hz s j (Nat.lt_of_not_ge hj)]

/-- The actual rows are universal combinations of the given equations. -/
def rows {R : Type*} [CommRing R] (f : ι → MvPolynomial (Fin n) R)
    (e : ι → ℕ) (s : monomialIndices n N) :
    MvPolynomial (Fin n) (MvPolynomial (CoefficientVariable n N e) R) :=
  ∑ j, coefficientForm R e s j * map C (f j)

theorem rows_homogeneous {R : Type*} [CommRing R]
    (f : ι → MvPolynomial (Fin n) R) (e : ι → ℕ)
    (hf : ∀ j, (f j).IsHomogeneous (e j)) (s : monomialIndices n N) :
    (rows f e s).IsHomogeneous N := by
  classical
  apply (homogeneousSubmodule _ _ N).sum_mem
  intro j _
  by_cases hj : e j ≤ N
  · simpa only [Nat.sub_add_cancel hj] using
      (coefficientForm_homogeneous R e s j).mul ((hf j).map C)
  · simp only [coefficientForm_eq_zero R e s j (Nat.lt_of_not_ge hj), zero_mul]
    exact isHomogeneous_zero _ _ _

@[simp] theorem rows_map {R K : Type*} [CommRing R] [CommRing K]
    (ρ : R →+* K) (f : ι → MvPolynomial (Fin n) R) (e : ι → ℕ)
    (a : CoefficientVariable n N e → K) (s : monomialIndices n N) :
    map (eval₂Hom ρ a) (rows f e s) =
      ∑ j, map (eval₂Hom ρ a) (coefficientForm R e s j) * map ρ (f j) := by
  have hcomp : (eval₂Hom ρ a).comp (C : R →+* MvPolynomial (CoefficientVariable n N e) R) = ρ := by
    ext r
    simp
  simp [rows, map_map, hcomp]

/-- A single square determinant in the universal coefficient variables. -/
def determinant {R : Type*} [CommRing R]
    (f : ι → MvPolynomial (Fin n) R) (e : ι → ℕ) (N : ℕ) :
    MvPolynomial (CoefficientVariable n N e) R :=
  (coefficientMatrix (rows (N := N) f e)).det

/-- Literal common-degree identities evaluate the universal matrix to the
identity, so its determinant evaluates to exactly one. -/
theorem exists_determinant_eq_one {R K : Type*} [CommRing R] [CommRing K]
    (ρ : R →+* K) (f : ι → MvPolynomial (Fin n) R) (e : ι → ℕ)
    (c : monomialIndices n N → ι → MvPolynomial (Fin n) K)
    (hc : ∀ s j, (c s j).IsHomogeneous (N - e j))
    (hz : ∀ s j, N < e j → c s j = 0)
    (hcert : ∀ s, monomial s.val 1 = ∑ j, c s j * map ρ (f j)) :
    ∃ a : CoefficientVariable n N e → K, eval₂Hom ρ a (determinant f e N) = 1 := by
  classical
  obtain ⟨a, ha⟩ := coefficientForm_realizes ρ e c hc hz
  have hrows (s : monomialIndices n N) :
      map (eval₂Hom ρ a) (rows f e s) = monomial s.val 1 := by
    rw [rows_map]
    simpa only [ha] using (hcert s).symm
  have hmatrix : (coefficientMatrix (rows (N := N) f e)).map (eval₂Hom ρ a) = 1 := by
    ext i j
    change eval₂Hom ρ a (coeff j.val (rows f e i)) = _
    rw [← coeff_map, hrows]
    simp only [coeff_monomial, Matrix.one_apply]
    by_cases hij : i = j
    · subst j
      simp
    · have hval : i.val ≠ j.val := fun h => hij (Subtype.ext h)
      simp [hij, hval]
  refine ⟨a, ?_⟩
  rw [determinant, RingHom.map_det]
  change ((coefficientMatrix (rows (N := N) f e)).map (eval₂Hom ρ a)).det = 1
  rw [hmatrix, Matrix.det_one]

/-- Nonvanishing of the actual universal determinant proves finiteness of
the specialized equation quotient. -/
theorem finite_quotient_of_determinant_ne_zero {R K : Type*} [CommRing R] [Field K]
    (ρ : R →+* K) (f : ι → MvPolynomial (Fin n) R) (e : ι → ℕ)
    (hf : ∀ j, (f j).IsHomogeneous (e j)) (hN : 0 < N)
    (a : CoefficientVariable n N e → K)
    (hdet : eval₂Hom ρ a (determinant f e N) ≠ 0) :
    Module.Finite K (MvPolynomial (Fin n) K ⧸
      Ideal.span (Set.range (fun j => map ρ (f j)))) := by
  classical
  let G := fun s : monomialIndices n N => map (eval₂Hom ρ a) (rows f e s)
  have hG : ∀ s, (G s).IsHomogeneous N :=
    fun s => (rows_homogeneous f e hf s).map (eval₂Hom ρ a)
  have hmatrix : (coefficientMatrix (rows (N := N) f e)).map (eval₂Hom ρ a) =
      coefficientMatrix G := by
    ext i j
    simp only [coefficientMatrix, Matrix.map_apply, G, coeff_map]
  have hdetG : (coefficientMatrix G).det ≠ 0 := by
    rw [determinant, RingHom.map_det] at hdet
    change ((coefficientMatrix (rows (N := N) f e)).map (eval₂Hom ρ a)).det ≠ 0 at hdet
    rwa [hmatrix] at hdet
  have hle : Ideal.span (Set.range G) ≤
      Ideal.span (Set.range (fun j => map ρ (f j))) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨s, rfl⟩
    change map (eval₂Hom ρ a) (rows f e s) ∈ _
    rw [rows_map]
    exact Ideal.sum_mem _ (fun j _ =>
      Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩))
  apply TotalDegreePowerSpan.finite_quotient _ (fun _ => N) (fun _ => 0)
  · intro i
    simp only [sub_zero, X_pow_eq_monomial]
    exact hle (monomial_mem_of_det_ne_zero G hG hdetG
      ⟨Finsupp.single i N, Finsupp.degree_single i N⟩)
  · intro i
    simpa only [totalDegree_zero] using hN

/-- A finite homogeneous equation quotient has one of these universal
positive-degree determinants nonzero (indeed, equal to one) at some assignment. -/
theorem exists_determinant_of_finite_quotient {R K : Type*} [CommRing R] [Field K]
    (ρ : R →+* K) (f : ι → MvPolynomial (Fin n) R) (e : ι → ℕ)
    (hf : ∀ j, (f j).IsHomogeneous (e j))
    [Module.Finite K (MvPolynomial (Fin n) K ⧸
      Ideal.span (Set.range (fun j => map ρ (f j))))] :
    ∃ N : ℕ, 0 < N ∧ ∃ a : CoefficientVariable n N e → K,
      eval₂Hom ρ a (determinant f e N) = 1 := by
  obtain ⟨N, hN, c, hcert, hc, hz⟩ := exists_common_degree_certificates
    (fun j => map ρ (f j)) e (fun j => (hf j).map ρ)
  exact ⟨N, hN, exists_determinant_eq_one ρ f e c hc hz hcert⟩

end CubicTenVariables.UniversalHomogeneousCombinations

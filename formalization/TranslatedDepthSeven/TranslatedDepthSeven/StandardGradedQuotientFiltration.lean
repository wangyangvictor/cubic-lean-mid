import TranslatedDepthSeven.GradedRankSandwich
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.Order.Interval.Finset.Nat

/-!
# The cumulative filtration on a homogeneous polynomial quotient

For a polynomial quotient `K[x_i] / I`, its degree-at-most-`n` part is
defined without requiring a graded-ring instance on the quotient: it is the
image of the polynomials of total degree at most `n`.  This file records the
elementary properties of that concrete filtration.

The cumulative formulation is the one useful for the generic-rank argument.
It is insensitive to whether a denominator is homogeneous: multiplying by a
polynomial of degree `c` merely shifts the filtration by `c`.
-/

namespace TranslatedDepthSeven

noncomputable section

universe u v

open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Substitution of degree-one forms commutes with homogeneous projection.
This elementary identity is kept local to the filtration argument so that
the latter does not depend on the elimination construction. -/
private theorem homogeneousComponent_aeval_degreeOne'
    {K : Type u} [Field K] {σ : Type v} {τ : Type*}
    (l : σ → MvPolynomial τ K)
    (hl : ∀ i, (l i).IsHomogeneous 1)
    (p : MvPolynomial σ K) (k : ℕ) :
    MvPolynomial.homogeneousComponent k (MvPolynomial.aeval l p) =
      MvPolynomial.aeval l (MvPolynomial.homogeneousComponent k p) := by
  classical
  conv_lhs =>
    rw [← p.sum_homogeneousComponent]
    simp only [map_sum]
  by_cases hk : k ∈ Finset.range (p.totalDegree + 1)
  · rw [Finset.sum_eq_single k]
    · have hh : (MvPolynomial.aeval l
          (MvPolynomial.homogeneousComponent k p)).IsHomogeneous k := by
        simpa using
          (MvPolynomial.homogeneousComponent_isHomogeneous k p).aeval l hl
      rw [MvPolynomial.homogeneousComponent_of_mem hh]
      simp
    · intro j hj hjk
      have hh : (MvPolynomial.aeval l
          (MvPolynomial.homogeneousComponent j p)).IsHomogeneous j := by
        simpa using
          (MvPolynomial.homogeneousComponent_isHomogeneous j p).aeval l hl
      rw [MvPolynomial.homogeneousComponent_of_mem hh]
      simp [Ne.symm hjk]
    · exact fun h ↦ (h hk).elim
  · have hpk : MvPolynomial.homogeneousComponent k p = 0 := by
      apply MvPolynomial.homogeneousComponent_eq_zero
      simpa only [Finset.mem_range, Nat.lt_add_one_iff, not_le] using hk
    rw [hpk, map_zero]
    apply Finset.sum_eq_zero
    intro j hj
    have hjk : j ≠ k := by
      intro h
      exact hk (h ▸ hj)
    have hh : (MvPolynomial.aeval l
        (MvPolynomial.homogeneousComponent j p)).IsHomogeneous j := by
      simpa using
        (MvPolynomial.homogeneousComponent_isHomogeneous j p).aeval l hl
    rw [MvPolynomial.homogeneousComponent_of_mem hh]
    simp [Ne.symm hjk]

/-- Over a domain, multiplying each member of a linearly independent family
by a nonzero scalar preserves linear independence. -/
theorem linearIndependent_smul_of_ne_zero
    {R : Type u} {M : Type v}
    [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M]
    {ι : Type*} {x : ι → M} (hx : LinearIndependent R x)
    (a : ι → R) (ha : ∀ i, a i ≠ 0) :
    LinearIndependent R (fun i ↦ a i • x i) := by
  rw [linearIndependent_iff'] at hx ⊢
  intro s g hsum i hi
  have hsum' : ∑ j ∈ s, (g j * a j) • x j = 0 := by
    simpa only [mul_smul] using hsum
  exact (mul_eq_zero.mp (hx s (fun j ↦ g j * a j) hsum' i hi)).resolve_right (ha i)

/-- The image in a polynomial quotient of the polynomials of total degree at
most `n`.  No quotient grading is used in this definition. -/
def quotientTotalDegreeFiltration
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    Submodule K (MvPolynomial σ K ⧸ I) :=
  (MvPolynomial.restrictTotalDegree σ K n).map
    (Ideal.Quotient.mkₐ K I).toLinearMap

theorem mem_quotientTotalDegreeFiltration_iff
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K)) (n : ℕ)
    (x : MvPolynomial σ K ⧸ I) :
    x ∈ quotientTotalDegreeFiltration K σ I n ↔
      ∃ p : MvPolynomial σ K,
        p.totalDegree ≤ n ∧ Ideal.Quotient.mk I p = x := by
  rw [quotientTotalDegreeFiltration, Submodule.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (MvPolynomial.mem_restrictTotalDegree _ _ _).mp hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hp, rfl⟩

/-- The cumulative filtration is increasing. -/
theorem quotientTotalDegreeFiltration_mono
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K)) {m n : ℕ} (hmn : m ≤ n) :
    quotientTotalDegreeFiltration K σ I m ≤
      quotientTotalDegreeFiltration K σ I n := by
  intro x hx
  rw [mem_quotientTotalDegreeFiltration_iff] at hx ⊢
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨p, hp.trans hmn, rfl⟩

/-- Every class belongs to one member of the cumulative filtration. -/
theorem exists_mem_quotientTotalDegreeFiltration
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K))
    (x : MvPolynomial σ K ⧸ I) :
    ∃ n : ℕ, x ∈ quotientTotalDegreeFiltration K σ I n := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨p.totalDegree,
    (mem_quotientTotalDegreeFiltration_iff K σ I p.totalDegree _).mpr
      ⟨p, le_rfl, rfl⟩⟩

/-- Each cumulative piece of a quotient in finitely many variables is finite
dimensional. -/
instance quotientTotalDegreeFiltration_moduleFinite
    (K : Type u) [Field K] (σ : Type v) [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    Module.Finite K (quotientTotalDegreeFiltration K σ I n) :=
  Module.Finite.map _ _

/-- Multiplication respects the cumulative filtration. -/
theorem mul_mem_quotientTotalDegreeFiltration
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K)) {m n : ℕ}
    {x y : MvPolynomial σ K ⧸ I}
    (hx : x ∈ quotientTotalDegreeFiltration K σ I m)
    (hy : y ∈ quotientTotalDegreeFiltration K σ I n) :
    x * y ∈ quotientTotalDegreeFiltration K σ I (m + n) := by
  rw [mem_quotientTotalDegreeFiltration_iff] at hx hy ⊢
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hy
  refine ⟨p * q, (MvPolynomial.totalDegree_mul p q).trans ?_, ?_⟩
  · exact Nat.add_le_add hp hq
  · exact map_mul (Ideal.Quotient.mk I) p q

/-- Multiplication by a fixed polynomial of degree `c` shifts the cumulative
filtration by at most `c`.  This is the form in which arbitrary denominator
clearing is compatible with Hilbert-function estimates. -/
theorem smul_mk_mem_quotientTotalDegreeFiltration
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K))
    (d : MvPolynomial σ K) {n : ℕ}
    {x : MvPolynomial σ K ⧸ I}
    (hx : x ∈ quotientTotalDegreeFiltration K σ I n) :
    Ideal.Quotient.mk I d * x ∈
      quotientTotalDegreeFiltration K σ I (d.totalDegree + n) := by
  apply mul_mem_quotientTotalDegreeFiltration K σ I
  · rw [mem_quotientTotalDegreeFiltration_iff]
    exact ⟨d, le_rfl, rfl⟩
  · exact hx

/-- For three variables the cumulative piece of any quotient has dimension
at most `choose (n+3) 3`. -/
theorem finrank_quotientTotalDegreeFiltration_finThree_le
    (K : Type u) [Field K]
    (I : Ideal (MvPolynomial (Fin 3) K)) (n : ℕ) :
    Module.finrank K (quotientTotalDegreeFiltration K (Fin 3) I n) ≤
      (n + 3).choose 3 := by
  calc
    Module.finrank K (quotientTotalDegreeFiltration K (Fin 3) I n) ≤
        Module.finrank K (MvPolynomial.restrictTotalDegree (Fin 3) K n) :=
      Submodule.finrank_map_le _ _
    _ = (n + 3).choose 3 :=
      finrank_mvPolynomial_finThree_restrictTotalDegree K n

/-! ## The homogeneous pieces of a homogeneous quotient -/

/-- The degree-`n` piece of a quotient by a homogeneous ideal, defined as the
image of the degree-`n` homogeneous polynomials. -/
def quotientHomogeneousComponent
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    Submodule K (MvPolynomial σ K ⧸ I) :=
  (MvPolynomial.homogeneousSubmodule σ K n).map
    (Ideal.Quotient.mkₐ K I).toLinearMap

instance homogeneousSubmodule_moduleFinite
    (K : Type u) [Field K] (σ : Type v) [Finite σ] (n : ℕ) :
    Module.Finite K (MvPolynomial.homogeneousSubmodule σ K n) := by
  let hle : MvPolynomial.homogeneousSubmodule σ K n ≤
      MvPolynomial.restrictTotalDegree σ K n := fun p hp ↦
    (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
      (MvPolynomial.IsHomogeneous.totalDegree_le hp)
  exact Module.Finite.of_injective (Submodule.inclusion hle)
    (Submodule.inclusion_injective hle)

instance quotientHomogeneousComponent_moduleFinite
    (K : Type u) [Field K] (σ : Type v) [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    Module.Finite K (quotientHomogeneousComponent K σ I n) :=
  Module.Finite.map _ _

/-- The quotient map restricted to one homogeneous piece. -/
def quotientHomogeneousComponentMap
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    MvPolynomial.homogeneousSubmodule σ K n →ₗ[K]
      quotientHomogeneousComponent K σ I n :=
  (((Ideal.Quotient.mkₐ K I).toLinearMap.comp
      (MvPolynomial.homogeneousSubmodule σ K n).subtype).codRestrict
    (quotientHomogeneousComponent K σ I n) fun p ↦
      Submodule.mem_map.mpr ⟨p, p.2, rfl⟩)

@[simp]
theorem coe_quotientHomogeneousComponentMap
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K)) (n : ℕ)
    (p : MvPolynomial.homogeneousSubmodule σ K n) :
    (quotientHomogeneousComponentMap K σ I n p :
        MvPolynomial σ K ⧸ I) = Ideal.Quotient.mk I p :=
  rfl

/-- Decompose a polynomial into homogeneous pieces and map each piece to the
quotient. -/
def polynomialDecomposeToQuotient
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K)) :
    MvPolynomial σ K →ₗ[K]
      DirectSum ℕ (fun n ↦ quotientHomogeneousComponent K σ I n) :=
  (DirectSum.lmap fun n ↦ quotientHomogeneousComponentMap K σ I n) ∘ₗ
    (DirectSum.decomposeLinearEquiv
      (MvPolynomial.homogeneousSubmodule σ K)).toLinearMap

@[simp]
theorem polynomialDecomposeToQuotient_apply_apply
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K))
    (p : MvPolynomial σ K) (n : ℕ) :
    ((polynomialDecomposeToQuotient K σ I p) n :
        MvPolynomial σ K ⧸ I) =
      Ideal.Quotient.mk I (MvPolynomial.homogeneousComponent n p) := by
  simp only [polynomialDecomposeToQuotient,
    LinearEquiv.coe_coe, DirectSum.lmap_apply,
    quotientHomogeneousComponentMap, LinearMap.codRestrict_apply,
    LinearMap.comp_apply]
  exact congrArg (Ideal.Quotient.mk I)
    (MvPolynomial.decomposition.decompose'_apply p n)

/-- A homogeneous ideal is contained in the kernel of the componentwise
quotient decomposition. -/
theorem le_ker_polynomialDecomposeToQuotient
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) :
    I.restrictScalars K ≤
      LinearMap.ker (polynomialDecomposeToQuotient K σ I) := by
  intro p hp
  rw [LinearMap.mem_ker]
  apply DirectSum.ext
  intro n
  apply Subtype.ext
  rw [polynomialDecomposeToQuotient_apply_apply]
  change Ideal.Quotient.mk I (MvPolynomial.homogeneousComponent n p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  rw [← MvPolynomial.decomposition.decompose'_apply p n]
  exact hI n hp

/-- The homogeneous decomposition descends to a quotient by a homogeneous
ideal. -/
def quotientDecomposeLinearMap
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) :
    (MvPolynomial σ K ⧸ I) →ₗ[K]
      DirectSum ℕ (fun n ↦ quotientHomogeneousComponent K σ I n) :=
  I.restrictScalars K |>.liftQ
    (polynomialDecomposeToQuotient K σ I)
    (le_ker_polynomialDecomposeToQuotient K σ I hI)

@[simp]
theorem quotientDecomposeLinearMap_mk_apply
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (p : MvPolynomial σ K) (n : ℕ) :
    ((quotientDecomposeLinearMap K σ I hI (Ideal.Quotient.mk I p)) n :
        MvPolynomial σ K ⧸ I) =
      Ideal.Quotient.mk I (MvPolynomial.homogeneousComponent n p) := by
  change ((polynomialDecomposeToQuotient K σ I p) n :
      MvPolynomial σ K ⧸ I) = _
  exact polynomialDecomposeToQuotient_apply_apply K σ I p n

/-- Recombining the componentwise quotient decomposition gives the ordinary
quotient map. -/
theorem coeLinearMap_comp_polynomialDecomposeToQuotient
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K)) :
    DirectSum.coeLinearMap
        (fun n ↦ quotientHomogeneousComponent K σ I n) ∘ₗ
      polynomialDecomposeToQuotient K σ I =
        (Ideal.Quotient.mkₐ K I).toLinearMap := by
  let H := MvPolynomial.homogeneousSubmodule σ K
  let Q := fun n ↦ quotientHomogeneousComponent K σ I n
  let f := fun n ↦ quotientHomogeneousComponentMap K σ I n
  have hmiddle :
      DirectSum.coeLinearMap Q ∘ₗ DirectSum.lmap f =
        (Ideal.Quotient.mkₐ K I).toLinearMap ∘ₗ
          DirectSum.coeLinearMap H := by
    apply DirectSum.linearMap_ext
    intro n
    apply LinearMap.ext
    intro p
    simp [H, Q, f, quotientHomogeneousComponentMap,
      DirectSum.lof_eq_of]
  rw [polynomialDecomposeToQuotient]
  rw [← LinearMap.comp_assoc, hmiddle, LinearMap.comp_assoc]
  apply LinearMap.ext
  intro p
  simp only [LinearMap.comp_apply]
  change (Ideal.Quotient.mkₐ K I).toLinearMap
      ((DirectSum.decomposeLinearEquiv H).symm
        (DirectSum.decomposeLinearEquiv H p)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The descended decomposition is a right inverse to recombination. -/
theorem coeLinearMap_comp_quotientDecomposeLinearMap
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) :
    DirectSum.coeLinearMap
        (fun n ↦ quotientHomogeneousComponent K σ I n) ∘ₗ
      quotientDecomposeLinearMap K σ I hI = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change DirectSum.coeLinearMap
      (fun n ↦ quotientHomogeneousComponent K σ I n)
      (polynomialDecomposeToQuotient K σ I p) =
        Ideal.Quotient.mk I p
  exact DFunLike.congr_fun
    (coeLinearMap_comp_polynomialDecomposeToQuotient K σ I) p

/-- On every homogeneous summand, decomposing after recombination is the
identity. -/
theorem quotientDecomposeLinearMap_comp_coeLinearMap
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) :
    quotientDecomposeLinearMap K σ I hI ∘ₗ
      DirectSum.coeLinearMap
        (fun n ↦ quotientHomogeneousComponent K σ I n) = LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro x
  obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
  have hx : x = quotientHomogeneousComponentMap K σ I n ⟨p, hp⟩ := by
    apply Subtype.ext
    exact hpx.symm
  subst x
  simp only [LinearMap.comp_apply, DirectSum.lof_eq_of,
    DirectSum.coeLinearMap_of, coe_quotientHomogeneousComponentMap]
  apply DirectSum.ext
  intro m
  apply Subtype.ext
  rw [quotientDecomposeLinearMap_mk_apply]
  rw [MvPolynomial.homogeneousComponent_of_mem hp]
  by_cases hmn : m = n
  · subst m
    simp
  · simp only [hmn, if_false, map_zero, LinearMap.id_apply]
    rw [DirectSum.coe_of_apply]
    simp [Ne.symm hmn]

/-- The images of the homogeneous polynomial pieces form an internal direct
sum in a quotient by a homogeneous ideal.  This supplies the quotient grading
that is not currently packaged as an instance in Mathlib. -/
theorem quotientHomogeneousComponent_isInternal
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) :
    DirectSum.IsInternal
      (fun n ↦ quotientHomogeneousComponent K σ I n) := by
  refine ⟨?_, ?_⟩
  · exact Function.LeftInverse.injective <|
      DFunLike.congr_fun
        (quotientDecomposeLinearMap_comp_coeLinearMap K σ I hI)
  · exact Function.RightInverse.surjective <|
      DFunLike.congr_fun
        (coeLinearMap_comp_quotientDecomposeLinearMap K σ I hI)

/-! ## Cumulative pieces as finite sums of homogeneous pieces -/

/-- Polynomials of degree at most `n` are exactly the sum of their homogeneous
pieces in degrees at most `n`. -/
theorem restrictTotalDegree_eq_iSup_homogeneousSubmodule
    (K : Type u) [Field K] (σ : Type v) (n : ℕ) :
    MvPolynomial.restrictTotalDegree σ K n =
      ⨆ k : {k : ℕ // k ≤ n},
        MvPolynomial.homogeneousSubmodule σ K k.1 := by
  apply le_antisymm
  · intro p hp
    rw [← MvPolynomial.sum_homogeneousComponent p]
    apply Submodule.sum_mem
    intro k hk
    apply le_iSup (fun j : {j : ℕ // j ≤ n} ↦
      MvPolynomial.homogeneousSubmodule σ K j.1)
      ⟨k, (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)).trans
        ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp hp)⟩
    exact MvPolynomial.homogeneousComponent_mem k p
  · refine iSup_le fun k p hp ↦
      (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr ?_
    exact (MvPolynomial.IsHomogeneous.totalDegree_le hp).trans k.2

/-- In a homogeneous quotient, the concrete cumulative filtration is the
finite sum of the quotient's homogeneous pieces. -/
theorem quotientTotalDegreeFiltration_eq_iSup_homogeneousComponent
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    quotientTotalDegreeFiltration K σ I n =
      ⨆ k : {k : ℕ // k ≤ n},
        quotientHomogeneousComponent K σ I k.1 := by
  rw [quotientTotalDegreeFiltration,
    restrictTotalDegree_eq_iSup_homogeneousSubmodule,
    Submodule.map_iSup]
  rfl

/-- A homogeneous piece of degree `n` lies in cumulative degree at most
`n`. -/
theorem quotientHomogeneousComponent_le_filtration
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    quotientHomogeneousComponent K σ I n ≤
      quotientTotalDegreeFiltration K σ I n := by
  rw [quotientTotalDegreeFiltration_eq_iSup_homogeneousComponent]
  exact le_iSup
    (fun j : {j : ℕ // j ≤ n} ↦ quotientHomogeneousComponent K σ I j.1)
    ⟨n, le_rfl⟩

/-- The homogeneous pieces in a homogeneous polynomial quotient are
multiplicative. -/
theorem quotientHomogeneousComponent_gradedMonoid
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K)) :
    SetLike.GradedMonoid
      (fun n ↦ quotientHomogeneousComponent K σ I n) where
  one_mem := by
    apply Submodule.mem_map.mpr
    exact ⟨1, MvPolynomial.isHomogeneous_one σ K,
      map_one (Ideal.Quotient.mk I)⟩
  mul_mem i j x y hx hy := by
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hy
    apply Submodule.mem_map.mpr
    exact ⟨p * q, MvPolynomial.IsHomogeneous.mul hp hq,
      map_mul (Ideal.Quotient.mk I) p q⟩

/-- The standard grading on a homogeneous polynomial quotient, constructed
from the concrete homogeneous pieces. -/
noncomputable def quotientGradedAlgebra
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) :
    GradedAlgebra (fun n ↦ quotientHomogeneousComponent K σ I n) :=
  { quotientHomogeneousComponent_gradedMonoid K σ I with
    decompose' := quotientDecomposeLinearMap K σ I hI
    left_inv := DFunLike.congr_fun
      (coeLinearMap_comp_quotientDecomposeLinearMap K σ I hI)
    right_inv := DFunLike.congr_fun
      (quotientDecomposeLinearMap_comp_coeLinearMap K σ I hI) }

/-- The cumulative Hilbert function is the sum of the dimensions of the
individual homogeneous pieces.  This is proved directly from the quotient
decomposition rather than assumed as a graded-quotient interface. -/
theorem finrank_quotientTotalDegreeFiltration_eq_sum_homogeneousComponent
    (K : Type u) [Field K] (σ : Type v) [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (n : ℕ) :
    Module.finrank K (quotientTotalDegreeFiltration K σ I n) =
      ∑ k : Set.Iic n,
        Module.finrank K (quotientHomogeneousComponent K σ I k.1) := by
  let Q := fun k ↦ quotientHomogeneousComponent K σ I k
  let s : Set ℕ := Set.Iic n
  let P : Submodule K (MvPolynomial σ K ⧸ I) := ⨆ k ∈ s, Q k
  let C : s → Submodule K P := fun k ↦ (Q k.1).comap P.subtype
  have hfull : DirectSum.IsInternal Q :=
    quotientHomogeneousComponent_isInternal K σ I hI
  have hind : iSupIndep (fun k : s ↦ Q k.1) :=
    hfull.submodule_iSupIndep.comp Subtype.val_injective
  have hInternal : DirectSum.IsInternal C := by
    exact DirectSum.isInternal_biSup_submodule_of_iSupIndep s hind
  letI : ∀ k : s, Module.Finite K (C k) := fun k ↦
    Module.Finite.equiv
      (Submodule.comapSubtypeEquivOfLe
        (show Q k.1 ≤ P from le_biSup Q k.2)).symm
  let e : (DirectSum s fun k ↦ C k) ≃ₗ[K] P :=
    LinearEquiv.ofBijective (DirectSum.coeLinearMap C) hInternal
  have hP : quotientTotalDegreeFiltration K σ I n = P := by
    rw [quotientTotalDegreeFiltration_eq_iSup_homogeneousComponent]
    simp only [P, s, Q, Set.mem_Iic, iSup_subtype]
  calc
    Module.finrank K (quotientTotalDegreeFiltration K σ I n) =
        Module.finrank K P := by rw [hP]
    _ = Module.finrank K (DirectSum s fun k ↦ C k) := e.finrank_eq.symm
    _ = ∑ k : s, Module.finrank K (C k) :=
      Module.finrank_directSum K (fun k : s ↦ C k)
    _ = ∑ k : Set.Iic n,
          Module.finrank K (quotientHomogeneousComponent K σ I k.1) := by
      apply Finset.sum_congr rfl
      intro k _
      exact (Submodule.comapSubtypeEquivOfLe
        (show Q k.1 ≤ P from le_biSup Q k.2)).finrank_eq

/-! ## A concrete linear normalization -/

/-- The algebra map from a three-variable polynomial ring obtained by
substituting three displayed ambient forms and then passing to the quotient. -/
def linearNormalizationHom
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K))
    (ell : Fin 3 → MvPolynomial σ K) :
    MvPolynomial (Fin 3) K →ₐ[K] (MvPolynomial σ K ⧸ I) :=
  (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval ell)

@[simp]
theorem linearNormalizationHom_apply
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K))
    (ell : Fin 3 → MvPolynomial σ K)
    (p : MvPolynomial (Fin 3) K) :
    linearNormalizationHom K σ I ell p =
      Ideal.Quotient.mk I (MvPolynomial.aeval ell p) :=
  rfl

/-- Substitution by degree-one forms preserves every homogeneous degree. -/
theorem linearNormalizationHom_mem_homogeneousComponent
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K))
    (ell : Fin 3 → MvPolynomial σ K)
    (hell : ∀ i, (ell i).IsHomogeneous 1)
    {n : ℕ} {p : MvPolynomial (Fin 3) K}
    (hp : p.IsHomogeneous n) :
    linearNormalizationHom K σ I ell p ∈
      quotientHomogeneousComponent K σ I n := by
  apply Submodule.mem_map.mpr
  refine ⟨MvPolynomial.aeval ell p, ?_, rfl⟩
  simpa only [one_mul] using hp.aeval ell hell

/-- Homogeneous projection commutes with the concrete linear normalization. -/
theorem quotientDecomposeLinearMap_linearNormalizationHom_apply
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (ell : Fin 3 → MvPolynomial σ K)
    (hell : ∀ i, (ell i).IsHomogeneous 1)
    (p : MvPolynomial (Fin 3) K) (n : ℕ) :
    ((quotientDecomposeLinearMap K σ I hI
        (linearNormalizationHom K σ I ell p)) n :
      MvPolynomial σ K ⧸ I) =
        linearNormalizationHom K σ I ell
          (MvPolynomial.homogeneousComponent n p) := by
  rw [linearNormalizationHom_apply,
    quotientDecomposeLinearMap_mk_apply,
    homogeneousComponent_aeval_degreeOne' ell hell]
  rfl

/-- If the right factor has degree `E`, then the degree-`k+E` part of its
product with a normalized polynomial is obtained from the degree-`k` part of
that polynomial. -/
theorem quotientDecomposeLinearMap_linearNormalizationHom_mul_apply
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (ell : Fin 3 → MvPolynomial σ K)
    (hell : ∀ i, (ell i).IsHomogeneous 1)
    (p : MvPolynomial (Fin 3) K) {E : ℕ}
    {x : MvPolynomial σ K ⧸ I}
    (hx : x ∈ quotientHomogeneousComponent K σ I E) (k : ℕ) :
    ((quotientDecomposeLinearMap K σ I hI
        (linearNormalizationHom K σ I ell p * x)) (k + E) :
      MvPolynomial σ K ⧸ I) =
        linearNormalizationHom K σ I ell
          (MvPolynomial.homogeneousComponent k p) * x := by
  let Q := fun n ↦ quotientHomogeneousComponent K σ I n
  letI : GradedAlgebra Q := quotientGradedAlgebra K σ I hI
  change ((DirectSum.decompose Q
      (linearNormalizationHom K σ I ell p * x) (k + E) : Q (k + E)) :
        MvPolynomial σ K ⧸ I) = _
  rw [DirectSum.coe_decompose_mul_add_of_right_mem Q hx]
  change ((quotientDecomposeLinearMap K σ I hI
      (linearNormalizationHom K σ I ell p)) k :
        MvPolynomial σ K ⧸ I) * x = _
  rw [quotientDecomposeLinearMap_linearNormalizationHom_apply
    K σ I hI ell hell]

/-- Every homogeneous component strictly above the cumulative filtration
index vanishes. -/
theorem quotientDecomposeLinearMap_eq_zero_of_mem_filtration
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    {n r : ℕ} {x : MvPolynomial σ K ⧸ I}
    (hx : x ∈ quotientTotalDegreeFiltration K σ I n) (hnr : n < r) :
    ((quotientDecomposeLinearMap K σ I hI x) r :
      MvPolynomial σ K ⧸ I) = 0 := by
  rw [mem_quotientTotalDegreeFiltration_iff] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  rw [quotientDecomposeLinearMap_mk_apply]
  rw [MvPolynomial.homogeneousComponent_eq_zero r p (hp.trans_lt hnr), map_zero]

/-- **Equal-degree strictness.**  Suppose homogeneous vectors of one common
degree are independent over the normalized polynomial ring.  If a linear
combination lies in cumulative degree at most `N`, then every coefficient
already has degree at most `N`.  This deliberately weak (unshifted) form is
enough for the Hilbert-function squeeze and avoids any cancellation issue. -/
theorem equalDegree_coefficients_mem_restrictTotalDegree
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (ell : Fin 3 → MvPolynomial σ K)
    (hell : ∀ i, (ell i).IsHomogeneous 1)
    {δ E N : ℕ}
    (x : Fin δ → MvPolynomial σ K ⧸ I)
    (hxHom : ∀ i, x i ∈ quotientHomogeneousComponent K σ I E)
    (hxLI :
      let B := MvPolynomial (Fin 3) K
      let A := MvPolynomial σ K ⧸ I
      let g := linearNormalizationHom K σ I ell
      letI : Algebra B A := g.toRingHom.toAlgebra
      LinearIndependent B x)
    (b : Fin δ → MvPolynomial (Fin 3) K)
    (hsum :
      ∑ i, linearNormalizationHom K σ I ell (b i) * x i ∈
        quotientTotalDegreeFiltration K σ I N) :
    ∀ i, b i ∈ MvPolynomial.restrictTotalDegree (Fin 3) K N := by
  let B := MvPolynomial (Fin 3) K
  let A := MvPolynomial σ K ⧸ I
  let g := linearNormalizationHom K σ I ell
  letI : Algebra B A := g.toRingHom.toAlgebra
  have hcomponent (k : ℕ) (hNk : N < k) :
      ∀ i, MvPolynomial.homogeneousComponent k (b i) = 0 := by
    have hzero := quotientDecomposeLinearMap_eq_zero_of_mem_filtration
      K σ I hI hsum (hNk.trans_le (Nat.le_add_right k E))
    rw [map_sum] at hzero
    rw [DFinsupp.finset_sum_apply] at hzero
    change (quotientHomogeneousComponent K σ I (k + E)).subtype
      (∑ a, (quotientDecomposeLinearMap K σ I hI
        (g (b a) * x a)) (k + E)) = 0 at hzero
    rw [map_sum] at hzero
    have hzero' :
        ∑ i, g (MvPolynomial.homogeneousComponent k (b i)) * x i = 0 := by
      calc
        ∑ i, g (MvPolynomial.homogeneousComponent k (b i)) * x i =
            ∑ i, ((quotientDecomposeLinearMap K σ I hI
              (g (b i) * x i)) (k + E) : A) := by
              apply Finset.sum_congr rfl
              intro i _
              exact (quotientDecomposeLinearMap_linearNormalizationHom_mul_apply
                K σ I hI ell hell (b i) (hxHom i) k).symm
        _ = 0 := hzero
    have hrelation :
        ∑ i, MvPolynomial.homogeneousComponent k (b i) • x i = 0 := by
      simpa only [Algebra.smul_def] using hzero'
    exact Fintype.linearIndependent_iff.mp hxLI _ hrelation
  intro i
  rw [restrictTotalDegree_eq_iSup_homogeneousSubmodule]
  rw [← MvPolynomial.sum_homogeneousComponent (b i)]
  apply Submodule.sum_mem
  intro k hk
  by_cases hkN : k ≤ N
  · apply le_iSup
      (fun j : {j : ℕ // j ≤ N} ↦
        MvPolynomial.homogeneousSubmodule (Fin 3) K j.1)
      ⟨k, hkN⟩
    exact MvPolynomial.homogeneousComponent_mem k (b i)
  · rw [hcomponent k (lt_of_not_ge hkN) i]
    exact Submodule.zero_mem _

/-- Consequently the concrete linear normalization preserves the cumulative
degree filtration. -/
theorem linearNormalizationHom_mem_quotientTotalDegreeFiltration
    (K : Type u) [Field K] (σ : Type v)
    (I : Ideal (MvPolynomial σ K))
    (ell : Fin 3 → MvPolynomial σ K)
    (hell : ∀ i, (ell i).IsHomogeneous 1)
    {n : ℕ} {p : MvPolynomial (Fin 3) K}
    (hp : p.totalDegree ≤ n) :
    linearNormalizationHom K σ I ell p ∈
      quotientTotalDegreeFiltration K σ I n := by
  rw [quotientTotalDegreeFiltration_eq_iSup_homogeneousComponent]
  rw [← MvPolynomial.sum_homogeneousComponent p, map_sum]
  apply Submodule.sum_mem
  intro k hk
  apply le_iSup
      (fun j : {j : ℕ // j ≤ n} ↦
        quotientHomogeneousComponent K σ I j.1)
      ⟨k, (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)).trans hp⟩
  exact linearNormalizationHom_mem_homogeneousComponent
    K σ I ell hell (MvPolynomial.homogeneousComponent_mem k p)

/-- The free equal-degree lattice gives the lower half of the concrete
Hilbert-function squeeze. -/
theorem equalDegree_genericRank_lower_binomial
    (K : Type u) [Field K] (σ : Type v) [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (ell : Fin 3 → MvPolynomial σ K)
    (hell : ∀ i, (ell i).IsHomogeneous 1)
    {δ E : ℕ}
    (x : Fin δ → MvPolynomial σ K ⧸ I)
    (hxHom : ∀ i, x i ∈ quotientHomogeneousComponent K σ I E)
    (hxLI :
      let B := MvPolynomial (Fin 3) K
      let A := MvPolynomial σ K ⧸ I
      let g := linearNormalizationHom K σ I ell
      letI : Algebra B A := g.toRingHom.toAlgebra
      LinearIndependent B x)
    (n : ℕ) :
    δ * (n + 3).choose 3 ≤
      Module.finrank K
        (quotientTotalDegreeFiltration K σ I (n + E)) := by
  let B := MvPolynomial (Fin 3) K
  let A := MvPolynomial σ K ⧸ I
  let g := linearNormalizationHom K σ I ell
  let P := MvPolynomial.restrictTotalDegree (Fin 3) K n
  let F := quotientTotalDegreeFiltration K σ I (n + E)
  letI : Algebra B A := g.toRingHom.toAlgebra
  let L : (Fin δ → P) →ₗ[K] F :=
    { toFun := fun b ↦ ⟨∑ i, g (b i) * x i, by
        apply Submodule.sum_mem
        intro i _
        apply mul_mem_quotientTotalDegreeFiltration K σ I
        · apply linearNormalizationHom_mem_quotientTotalDegreeFiltration
            K σ I ell hell
          have hb := (b i).2
          change (b i : B) ∈
            MvPolynomial.restrictTotalDegree (Fin 3) K n at hb
          exact (MvPolynomial.mem_restrictTotalDegree
            (Fin 3) n (b i : B)).mp hb
        · exact quotientHomogeneousComponent_le_filtration K σ I E (hxHom i)⟩
      map_add' := by
        intro b c
        apply Subtype.ext
        change ∑ i, g ((b i : B) + (c i : B)) * x i =
          (∑ i, g (b i) * x i) + ∑ i, g (c i) * x i
        simp only [map_add, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a b
        apply Subtype.ext
        change ∑ i, g (a • (b i : B)) * x i =
          a • ∑ i, g (b i) * x i
        simp only [map_smul, smul_mul_assoc, Finset.smul_sum] }
  have hLinj : Function.Injective L := by
    intro b c hbc
    have hsum : ∑ i, g (b i) * x i = ∑ i, g (c i) * x i := by
      exact congrArg Subtype.val hbc
    have hrelation : ∑ i, ((b i : B) - (c i : B)) • x i = 0 := by
      change ∑ i, g ((b i : B) - (c i : B)) * x i = 0
      simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr hsum
    have hcoeff := Fintype.linearIndependent_iff.mp hxLI _ hrelation
    funext i
    apply Subtype.ext
    exact sub_eq_zero.mp (hcoeff i)
  have hfin := L.finrank_le_finrank_of_injective hLinj
  rw [Module.finrank_pi_fintype K] at hfin
  dsimp only [P, F] at hfin
  simpa [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    finrank_mvPolynomial_finThree_restrictTotalDegree K n] using hfin

/-- Clearing the quotient into the free equal-degree lattice gives the upper
half of the concrete Hilbert-function squeeze. -/
theorem equalDegree_genericRank_upper_binomial
    (K : Type u) [Field K] (σ : Type v) [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (hprime : I.IsPrime)
    (ell : Fin 3 → MvPolynomial σ K)
    (hell : ∀ i, (ell i).IsHomogeneous 1)
    (hinjective : Function.Injective (linearNormalizationHom K σ I ell))
    {δ E : ℕ}
    (x : Fin δ → MvPolynomial σ K ⧸ I)
    (hxHom : ∀ i, x i ∈ quotientHomogeneousComponent K σ I E)
    (hxLI :
      let B := MvPolynomial (Fin 3) K
      let A := MvPolynomial σ K ⧸ I
      let g := linearNormalizationHom K σ I ell
      letI : Algebra B A := g.toRingHom.toAlgebra
      LinearIndependent B x)
    (d : MvPolynomial (Fin 3) K) (hd : d ≠ 0)
    (hclear :
      let B := MvPolynomial (Fin 3) K
      let A := MvPolynomial σ K ⧸ I
      let g := linearNormalizationHom K σ I ell
      letI : Algebra B A := g.toRingHom.toAlgebra
      ∀ a : A, d • a ∈ Submodule.span B (Set.range x))
    (n : ℕ) :
    Module.finrank K (quotientTotalDegreeFiltration K σ I n) ≤
      δ * (n + d.totalDegree + 3).choose 3 := by
  let B := MvPolynomial (Fin 3) K
  let A := MvPolynomial σ K ⧸ I
  let g := linearNormalizationHom K σ I ell
  let F := quotientTotalDegreeFiltration K σ I n
  let c := d.totalDegree + n
  let P := MvPolynomial.restrictTotalDegree (Fin 3) K c
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : IsDomain A :=
    (Ideal.Quotient.isDomain_iff_prime (I := I)).mpr hprime
  let S := Submodule.span B (Set.range x)
  let D : F →ₗ[K] S :=
    { toFun := fun a ↦ ⟨d • (a : A), by
          change d • (a : A) ∈ Submodule.span B (Set.range x)
          exact hclear (a : A)⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        simp only [Submodule.coe_add, smul_add]
      map_smul' := by
        intro a b
        apply Subtype.ext
        change g d * (a • (b : A)) = a • (g d * (b : A))
        simp only [Algebra.smul_def]
        ring }
  let R : S →ₗ[K] (Fin δ → B) :=
    ((Finsupp.linearEquivFunOnFinite B B (Fin δ)).toLinearMap.restrictScalars K).comp
      (hxLI.repr.restrictScalars K)
  let C : F →ₗ[K] (Fin δ → B) := R.comp D
  have hC_mem (a : F) (i : Fin δ) : C a i ∈ P := by
    have hrecomb₀ := hxLI.linearCombination_repr (D a)
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_fintype _ _ (by simp)] at hrecomb₀
    have hrecomb : ∑ i, g (C a i) * x i = (D a : A) := by
      simpa only [C, R, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
        LinearEquiv.coe_coe, Finsupp.linearEquivFunOnFinite_apply,
        Algebra.smul_def] using hrecomb₀
    have hDa : (D a : A) ∈ quotientTotalDegreeFiltration K σ I c := by
      apply mul_mem_quotientTotalDegreeFiltration K σ I
      · apply linearNormalizationHom_mem_quotientTotalDegreeFiltration
          K σ I ell hell
        exact le_rfl
      · exact a.2
    have hsum : ∑ i, g (C a i) * x i ∈
        quotientTotalDegreeFiltration K σ I c := by
      rw [hrecomb]
      exact hDa
    have hc := equalDegree_coefficients_mem_restrictTotalDegree
      K σ I hI ell hell x hxHom hxLI (C a) hsum i
    exact hc
  let U : F →ₗ[K] (Fin δ → P) :=
    { toFun := fun a i ↦ ⟨C a i, hC_mem a i⟩
      map_add' := by
        intro a b
        funext i
        apply Subtype.ext
        exact congrFun (C.map_add a b) i
      map_smul' := by
        intro a b
        funext i
        apply Subtype.ext
        exact congrFun (C.map_smul a b) i }
  have hDinj : Function.Injective D := by
    intro a b hab
    apply Subtype.ext
    apply mul_left_cancel₀ (hinjective.ne hd)
    exact congrArg Subtype.val hab
  have hRinj : Function.Injective R := by
    intro y z hyz
    apply (LinearMap.ker_eq_bot.mp hxLI.repr_ker)
    apply (Finsupp.linearEquivFunOnFinite B B (Fin δ)).injective
    exact hyz
  have hUinj : Function.Injective U := by
    intro a b hab
    apply hDinj
    apply hRinj
    apply funext
    intro i
    exact congrArg Subtype.val (congrFun hab i)
  have hfin := U.finrank_le_finrank_of_injective hUinj
  rw [Module.finrank_pi_fintype K] at hfin
  dsimp only [F, P, c] at hfin
  simpa [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    finrank_mvPolynomial_finThree_restrictTotalDegree K
      (d.totalDegree + n), Nat.add_comm n d.totalDegree,
    Nat.add_assoc] using hfin

/-- A module-finite degree-one normalization admits a finite homogeneous
spanning family.  This is obtained concretely: lift ordinary module
generators to polynomials and take their finitely many homogeneous pieces. -/
theorem exists_homogeneous_generators_of_finite_linearNormalization
    (K : Type u) [Field K] (σ : Type v) [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (ell : Fin 3 → MvPolynomial σ K)
    (hfinite : (linearNormalizationHom K σ I ell).Finite) :
    let B := MvPolynomial (Fin 3) K
    let A := MvPolynomial σ K ⧸ I
    let g := linearNormalizationHom K σ I ell
    letI : Algebra B A := g.toRingHom.toAlgebra
    ∃ N : ℕ, ∃ t : Fin N → A, ∃ degree : Fin N → ℕ,
      (∀ i, t i ∈ quotientHomogeneousComponent K σ I (degree i)) ∧
      Submodule.span B (Set.range t) = ⊤ := by
  dsimp only
  let B := MvPolynomial (Fin 3) K
  let A := MvPolynomial σ K ⧸ I
  let g := linearNormalizationHom K σ I ell
  letI : Algebra B A := g.toRingHom.toAlgebra
  haveI : Module.Finite B A := hfinite
  obtain ⟨M, s, hs⟩ := Module.Finite.exists_fin (R := B) (M := A)
  choose p hp using fun i : Fin M ↦ Ideal.Quotient.mk_surjective (s i)
  let D : ℕ := Finset.univ.sup fun i : Fin M ↦ (p i).totalDegree
  let ι := Fin M × Fin (D + 1)
  let t₀ : ι → A := fun ik ↦
    Ideal.Quotient.mk I (MvPolynomial.homogeneousComponent ik.2.1 (p ik.1))
  let degree₀ : ι → ℕ := fun ik ↦ ik.2.1
  have ht₀Hom (ik : ι) :
      t₀ ik ∈ quotientHomogeneousComponent K σ I (degree₀ ik) := by
    apply Submodule.mem_map.mpr
    exact ⟨MvPolynomial.homogeneousComponent ik.2.1 (p ik.1),
      MvPolynomial.homogeneousComponent_mem ik.2.1 (p ik.1), rfl⟩
  have ht₀Span : Submodule.span B (Set.range t₀) = ⊤ := by
    apply top_unique
    rw [← hs, Submodule.span_le]
    rintro a ⟨i, rfl⟩
    rw [← hp i, ← MvPolynomial.sum_homogeneousComponent (p i), map_sum]
    apply Submodule.sum_mem
    intro k hk
    apply Submodule.subset_span
    have hiD : (p i).totalDegree ≤ D := by
      exact Finset.le_sup (f := fun j : Fin M ↦ (p j).totalDegree)
        (Finset.mem_univ i)
    let k' : Fin (D + 1) := ⟨k,
      Nat.lt_succ_iff.mpr
        ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)).trans hiD)⟩
    exact ⟨(i, k'), rfl⟩
  let e := Fintype.equivFin ι
  let t : Fin (Fintype.card ι) → A := fun i ↦ t₀ (e.symm i)
  let degree : Fin (Fintype.card ι) → ℕ := fun i ↦ degree₀ (e.symm i)
  refine ⟨Fintype.card ι, t, degree, ?_, ?_⟩
  · intro i
    exact ht₀Hom (e.symm i)
  · have hrange : Set.range t = Set.range t₀ := by
      apply Set.ext
      intro a
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e.symm i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨e i, by simp only [t, Equiv.symm_apply_apply]⟩
    rw [hrange]
    exact ht₀Span

/-! ## A homogeneous generic-rank lattice -/

/-- Starting from homogeneous module generators, the generic-rank lattice may
be chosen with all basis vectors in one common degree.  A further nonzero
scalar still sends the whole quotient into this equal-degree lattice. -/
theorem exists_equalDegree_genericRank_lattice_sandwich
    (K : Type u) [Field K] (σ : Type v) [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (ell : Fin 3 → MvPolynomial σ K)
    (hell : ∀ i, (ell i).IsHomogeneous 1)
    (hfinite : (linearNormalizationHom K σ I ell).Finite) :
    let B := MvPolynomial (Fin 3) K
    let A := MvPolynomial σ K ⧸ I
    let g := linearNormalizationHom K σ I ell
    letI : Algebra B A := g.toRingHom.toAlgebra
    ∀ {N : ℕ} (t : Fin N → A) (degree : Fin N → ℕ),
      (∀ i, t i ∈ quotientHomogeneousComponent K σ I (degree i)) →
      Submodule.span B (Set.range t) = ⊤ →
      let δ := Module.finrank (FractionRing B)
        (LocalizedModule (nonZeroDivisors B) A)
      ∃ E : ℕ, ∃ d : B, ∃ x : Fin δ → A,
        d ≠ 0 ∧
        LinearIndependent B x ∧
        (∀ i, x i ∈ quotientHomogeneousComponent K σ I E) ∧
        (∀ a : A, d • a ∈ Submodule.span B (Set.range x)) := by
  dsimp only
  let B := MvPolynomial (Fin 3) K
  let A := MvPolynomial σ K ⧸ I
  let g := linearNormalizationHom K σ I ell
  letI : Algebra B A := g.toRingHom.toAlgebra
  haveI : Module.Finite B A := by
    exact hfinite
  intro N t degree htHom htSpan
  obtain ⟨e, _heInjective, heLI, _heLIK, _heSpanK,
      d, hd, hclear⟩ :=
    exists_genericRank_subfamily_lattice_sandwich t htSpan
  let δ := Module.finrank (FractionRing B)
    (LocalizedModule (nonZeroDivisors B) A)
  let E : ℕ := Finset.univ.sup fun i : Fin δ ↦ degree (e i)
  let q : Fin δ → B := fun i ↦
    MvPolynomial.X 0 ^ (E - degree (e i))
  let x : Fin δ → A := fun i ↦ q i • t (e i)
  have hdegree_le (i : Fin δ) : degree (e i) ≤ E := by
    exact Finset.le_sup (f := fun j : Fin δ ↦ degree (e j))
      (Finset.mem_univ i)
  have hq_ne (i : Fin δ) : q i ≠ 0 := by
    exact pow_ne_zero _ (MvPolynomial.X_ne_zero (R := K) (0 : Fin 3))
  have hxLI : LinearIndependent B x := by
    exact linearIndependent_smul_of_ne_zero heLI q hq_ne
  have hxHom (i : Fin δ) :
      x i ∈ quotientHomogeneousComponent K σ I E := by
    rw [show x i = g (q i) * t (e i) by
      simp only [x, Algebra.smul_def]
      rfl]
    have hqHom : (q i).IsHomogeneous (E - degree (e i)) := by
      exact MvPolynomial.isHomogeneous_X_pow 0 (E - degree (e i))
    have hgq := linearNormalizationHom_mem_homogeneousComponent
      K σ I ell hell hqHom
    have hmul :=
      (quotientHomogeneousComponent_gradedMonoid K σ I).mul_mem
        hgq (htHom (e i))
    simpa only [Nat.sub_add_cancel (hdegree_le i)] using hmul
  let X0E : B := MvPolynomial.X 0 ^ E
  have hX0E_ne : X0E ≠ 0 := by
    exact pow_ne_zero _ (MvPolynomial.X_ne_zero (R := K) (0 : Fin 3))
  have hX0E_generator (i : Fin δ) :
      X0E • t (e i) ∈ Submodule.span B (Set.range x) := by
    have heq : X0E • t (e i) =
        (MvPolynomial.X (R := K) (0 : Fin 3) ^ degree (e i)) • x i := by
      simp only [x, q, smul_smul, ← pow_add]
      rw [show degree (e i) + (E - degree (e i)) = E by
        have := hdegree_le i
        omega]
    rw [heq]
    exact (Submodule.span B (Set.range x)).smul_mem _
      (Submodule.subset_span ⟨i, rfl⟩)
  have hX0E_span (a : A)
      (ha : a ∈ Submodule.span B (Set.range fun i ↦ t (e i))) :
      X0E • a ∈ Submodule.span B (Set.range x) := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
    · rintro y ⟨i, rfl⟩
      exact hX0E_generator i
    · simp
    · intro y z _ _ hy hz
      simpa only [smul_add] using
        (Submodule.span B (Set.range x)).add_mem hy hz
    · intro b y _ hy
      rw [smul_smul, mul_comm X0E b, ← smul_smul]
      exact (Submodule.span B (Set.range x)).smul_mem b hy
  refine ⟨E, d * X0E, x, mul_ne_zero hd hX0E_ne, hxLI, hxHom, ?_⟩
  intro a
  simpa only [smul_smul, mul_comm X0E d] using
    hX0E_span (d • a) (hclear a)

/-- **Concrete generic-rank/Hilbert-function bridge in three parameters.**
For a homogeneous prime quotient which is finite and injective over three
displayed degree-one parameters, the cumulative Hilbert function is squeezed
between `δ` copies of the three-variable polynomial count, up to fixed shifts.
Here `δ` is literally the dimension after passage to the fraction field; no
abstract multiplicity or projective-degree interface occurs in the statement.

The homogeneous spanning family is the only finite presentation data used by
the proof. -/
theorem exists_genericRank_shifted_binomial_squeeze
    (K : Type u) [Field K] (σ : Type v) [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (hprime : I.IsPrime)
    (ell : Fin 3 → MvPolynomial σ K)
    (hell : ∀ i, (ell i).IsHomogeneous 1)
    (hfinite : (linearNormalizationHom K σ I ell).Finite)
    (hinjective : Function.Injective (linearNormalizationHom K σ I ell)) :
    let B := MvPolynomial (Fin 3) K
    let A := MvPolynomial σ K ⧸ I
    let g := linearNormalizationHom K σ I ell
    letI : Algebra B A := g.toRingHom.toAlgebra
    ∀ {N : ℕ} (t : Fin N → A) (degree : Fin N → ℕ),
      (∀ i, t i ∈ quotientHomogeneousComponent K σ I (degree i)) →
      Submodule.span B (Set.range t) = ⊤ →
      let δ := Module.finrank (FractionRing B)
        (LocalizedModule (nonZeroDivisors B) A)
      ∃ E C : ℕ, ∀ n : ℕ,
        δ * (n + 3).choose 3 ≤
            Module.finrank K
              (quotientTotalDegreeFiltration K σ I (n + E)) ∧
          Module.finrank K (quotientTotalDegreeFiltration K σ I n) ≤
            δ * (n + C + 3).choose 3 := by
  dsimp only
  let B := MvPolynomial (Fin 3) K
  let A := MvPolynomial σ K ⧸ I
  let g := linearNormalizationHom K σ I ell
  letI : Algebra B A := g.toRingHom.toAlgebra
  intro N t degree htHom htSpan
  obtain ⟨E, d, x, hd, hxLI, hxHom, hclear⟩ :=
    exists_equalDegree_genericRank_lattice_sandwich
      K σ I ell hell hfinite t degree htHom htSpan
  refine ⟨E, d.totalDegree, fun n ↦ ⟨?_, ?_⟩⟩
  · exact equalDegree_genericRank_lower_binomial
      K σ I ell hell x hxHom hxLI n
  · exact equalDegree_genericRank_upper_binomial
      K σ I hI hprime ell hell hinjective x hxHom hxLI d hd hclear n

/-- Generator-free form of the bridge: module-finiteness itself supplies the
homogeneous spanning family used above. -/
theorem exists_genericRank_shifted_binomial_squeeze_of_finite
    (K : Type u) [Field K] (σ : Type v) [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (hprime : I.IsPrime)
    (ell : Fin 3 → MvPolynomial σ K)
    (hell : ∀ i, (ell i).IsHomogeneous 1)
    (hfinite : (linearNormalizationHom K σ I ell).Finite)
    (hinjective : Function.Injective (linearNormalizationHom K σ I ell)) :
    let B := MvPolynomial (Fin 3) K
    let A := MvPolynomial σ K ⧸ I
    let g := linearNormalizationHom K σ I ell
    letI : Algebra B A := g.toRingHom.toAlgebra
    let δ := Module.finrank (FractionRing B)
      (LocalizedModule (nonZeroDivisors B) A)
    ∃ E C : ℕ, ∀ n : ℕ,
      δ * (n + 3).choose 3 ≤
          Module.finrank K
            (quotientTotalDegreeFiltration K σ I (n + E)) ∧
        Module.finrank K (quotientTotalDegreeFiltration K σ I n) ≤
          δ * (n + C + 3).choose 3 := by
  dsimp only
  let B := MvPolynomial (Fin 3) K
  let A := MvPolynomial σ K ⧸ I
  let g := linearNormalizationHom K σ I ell
  letI : Algebra B A := g.toRingHom.toAlgebra
  obtain ⟨N, t, degree, htHom, htSpan⟩ :=
    exists_homogeneous_generators_of_finite_linearNormalization
      K σ I ell hfinite
  exact exists_genericRank_shifted_binomial_squeeze
    K σ I hI hprime ell hell hfinite hinjective t degree htHom htSpan

end

end TranslatedDepthSeven

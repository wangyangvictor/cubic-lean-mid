import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Tactic

/-!
# The projective automorphism extending an affine scalar change

The affine substitution `z ↦ y₀ + r z`, with `r ≠ 0`, is the affine chart of
the homogeneous linear automorphism

`(s,z) ↦ (s, s y₀ + r z)`.

This file constructs that automorphism literally and descends it to
projective space.  It supplies the projective-coordinate bridge needed when
an affine rescaling is compared with a projective closure.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped LinearAlgebra.Projectivization

universe u v

variable {K : Type u} {σ : Type v} [Field K]

/-- Homogeneous linear automorphism extending `z ↦ y₀+r z` on the affine
chart `s=1`.  The index `none` is the homogenizing coordinate and `some i`
is the `i`-th affine coordinate. -/
def homogeneousAffineLinearEquiv
    (y₀ : σ → K) (r : K) (hr : r ≠ 0) :
    (Option σ → K) ≃ₗ[K] (Option σ → K) where
  toFun v j :=
    match j with
    | none => v none
    | some i => y₀ i * v none + r * v (some i)
  invFun w j :=
    match j with
    | none => w none
    | some i => r⁻¹ * (w (some i) - y₀ i * w none)
  left_inv v := by
    funext j
    cases j with
    | none => rfl
    | some i =>
        dsimp
        field_simp [hr]
        ring
  right_inv w := by
    funext j
    cases j with
    | none => rfl
    | some i =>
        dsimp
        field_simp [hr]
        ring
  map_add' v w := by
    funext j
    cases j with
    | none => rfl
    | some i =>
        dsimp
        ring
  map_smul' a v := by
    funext j
    cases j with
    | none => rfl
    | some i =>
        dsimp
        ring

@[simp]
theorem homogeneousAffineLinearEquiv_apply_none
    (y₀ : σ → K) (r : K) (hr : r ≠ 0) (v : Option σ → K) :
    homogeneousAffineLinearEquiv y₀ r hr v none = v none :=
  rfl

@[simp]
theorem homogeneousAffineLinearEquiv_apply_some
    (y₀ : σ → K) (r : K) (hr : r ≠ 0) (v : Option σ → K) (i : σ) :
    homogeneousAffineLinearEquiv y₀ r hr v (some i) =
      y₀ i * v none + r * v (some i) :=
  rfl

/-- The affine chart `s=1` is carried to the literal affine substitution
`z ↦ y₀+r z`. -/
theorem homogeneousAffineLinearEquiv_affineChart
    (y₀ : σ → K) (r : K) (hr : r ≠ 0) (z : σ → K) :
    homogeneousAffineLinearEquiv y₀ r hr
        (fun j ↦ match j with | none => 1 | some i => z i) =
      (fun j ↦ match j with | none => 1 | some i => y₀ i + r * z i) := by
  funext j
  cases j <;> simp

/-- The homogeneous representative `[1:z]` of an affine point. -/
def affineChartVector (z : σ → K) : Option σ → K
  | none => 1
  | some i => z i

/-- The representative `[1:z]` is nonzero because its homogenizing
coordinate is one. -/
theorem affineChartVector_ne_zero (z : σ → K) : affineChartVector z ≠ 0 := by
  intro h
  have hcoord := congrFun h none
  change (1 : K) = 0 at hcoord
  exact one_ne_zero hcoord

/-- The standard affine-chart embedding into projective space. -/
def affineChartPoint (z : σ → K) : ℙ K (Option σ → K) :=
  Projectivization.mk K (affineChartVector z) (affineChartVector_ne_zero z)

/-- Equality of affine-chart projective points is literal equality of their
affine coordinates: the first coordinate fixes the projective scalar. -/
theorem affineChartPoint_injective :
    Function.Injective (affineChartPoint : (σ → K) → ℙ K (Option σ → K)) := by
  intro z w hzw
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff' K _ _
      (affineChartVector_ne_zero z) (affineChartVector_ne_zero w)).1 hzw
  have ha_one : a = 1 := by
    have hnone := congrFun ha none
    simpa [affineChartVector] using hnone
  funext i
  have hsome := congrFun ha (some i)
  simpa [affineChartVector, ha_one] using hsome.symm

/-- The standard affine chart, defined intrinsically as the projective
classes admitting a representative with nonzero homogenizing coordinate. -/
def standardAffineChart : Set (ℙ K (Option σ → K)) :=
  {P | ∃ (v : Option σ → K) (hv : v ≠ 0),
    P = Projectivization.mk K v hv ∧ v none ≠ 0}

/-- Every standard affine-chart point lies in the standard affine chart. -/
theorem affineChartPoint_mem_standardAffineChart (z : σ → K) :
    affineChartPoint z ∈ (standardAffineChart : Set (ℙ K (Option σ → K))) :=
  ⟨affineChartVector z, affineChartVector_ne_zero z, rfl, by
    simp [affineChartVector]⟩

/-- A projective point belongs to the standard affine chart exactly when it
has a (necessarily unique) representative of the form `[1:z]`. -/
theorem mem_standardAffineChart_iff_exists_affineChartPoint
    (P : ℙ K (Option σ → K)) :
    P ∈ (standardAffineChart : Set (ℙ K (Option σ → K))) ↔
      ∃ z : σ → K, P = affineChartPoint z := by
  constructor
  · rintro ⟨v, hv, rfl, hvnone⟩
    let z : σ → K := fun i ↦ (v none)⁻¹ * v (some i)
    refine ⟨z, ?_⟩
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
    refine ⟨v none, ?_⟩
    funext j
    cases j with
    | none => simp [affineChartVector]
    | some i =>
        simp only [Pi.smul_apply, smul_eq_mul, affineChartVector]
        dsimp [z]
        field_simp [hvnone]
  · rintro ⟨z, rfl⟩
    exact affineChartPoint_mem_standardAffineChart z

/-- The affine coordinate of a point in the standard chart is unique. -/
theorem existsUnique_affineChartPoint_of_mem_standardAffineChart
    {P : ℙ K (Option σ → K)}
    (hP : P ∈ (standardAffineChart : Set (ℙ K (Option σ → K)))) :
    ∃! z : σ → K, P = affineChartPoint z := by
  obtain ⟨z, hz⟩ :=
    (mem_standardAffineChart_iff_exists_affineChartPoint P).1 hP
  refine ⟨z, hz, ?_⟩
  intro w hw
  exact (affineChartPoint_injective (hz.symm.trans hw)).symm

/-- The hyperplane at infinity, defined by vanishing of the homogenizing
coordinate on a nonzero representative. -/
def projectiveHyperplaneAtInfinity : Set (ℙ K (Option σ → K)) :=
  {P | ∃ (v : Option σ → K) (hv : v ≠ 0),
    P = Projectivization.mk K v hv ∧ v none = 0}

/-- Membership in the hyperplane at infinity can be checked on any displayed
nonzero representative. -/
theorem mk_mem_projectiveHyperplaneAtInfinity_iff
    (v : Option σ → K) (hv : v ≠ 0) :
    Projectivization.mk K v hv ∈ projectiveHyperplaneAtInfinity ↔
      v none = 0 := by
  constructor
  · rintro ⟨w, hw, hvw, hwnone⟩
    obtain ⟨a, ha⟩ :=
      (Projectivization.mk_eq_mk_iff' K v w hv hw).1 hvw
    have hnone := congrFun ha none
    simpa [hwnone] using hnone.symm
  · intro hvnone
    exact ⟨v, hv, rfl, hvnone⟩

/-- The standard affine chart and the hyperplane at infinity are exact
complements. -/
theorem projectiveHyperplaneAtInfinity_eq_compl_standardAffineChart :
    (projectiveHyperplaneAtInfinity : Set (ℙ K (Option σ → K))) =
      (standardAffineChart : Set (ℙ K (Option σ → K)))ᶜ := by
  ext P
  induction P using Projectivization.ind with
  | h v hv =>
      rw [mk_mem_projectiveHyperplaneAtInfinity_iff]
      simp only [Set.mem_compl_iff]
      constructor
      · intro hvnone hchart
        obtain ⟨z, hz⟩ :=
          (mem_standardAffineChart_iff_exists_affineChartPoint _).1 hchart
        obtain ⟨a, ha⟩ :=
          (Projectivization.mk_eq_mk_iff' K v (affineChartVector z) hv
            (affineChartVector_ne_zero z)).1 hz
        have hnone := congrFun ha none
        have haone : a = v none := by
          simpa [affineChartVector] using hnone
        have ha_ne : a ≠ 0 := by
          intro ha0
          apply hv
          have := ha
          rw [ha0, zero_smul] at this
          exact this.symm
        exact ha_ne (haone.trans hvnone)
      · intro hnot
        by_contra hvnone
        apply hnot
        exact ⟨v, hv, rfl, hvnone⟩

/-- The induced map on projective space. -/
def projectiveAffineMap
    (y₀ : σ → K) (r : K) (hr : r ≠ 0) :
    ℙ K (Option σ → K) → ℙ K (Option σ → K) :=
  Projectivization.map (homogeneousAffineLinearEquiv y₀ r hr).toLinearMap
    (homogeneousAffineLinearEquiv y₀ r hr).injective

/-- The induced projective map is injective. -/
theorem projectiveAffineMap_injective
    (y₀ : σ → K) (r : K) (hr : r ≠ 0) :
    Function.Injective (projectiveAffineMap y₀ r hr) :=
  Projectivization.map_injective _
    (homogeneousAffineLinearEquiv y₀ r hr).injective

/-- The projective map on a displayed homogeneous representative is exactly
the class of the displayed homogeneous affine image. -/
theorem projectiveAffineMap_mk
    (y₀ : σ → K) (r : K) (hr : r ≠ 0)
    (v : Option σ → K) (hv : v ≠ 0) :
    projectiveAffineMap y₀ r hr (Projectivization.mk K v hv) =
      Projectivization.mk K
        (homogeneousAffineLinearEquiv y₀ r hr v)
        (by
          simpa using
            (homogeneousAffineLinearEquiv y₀ r hr).injective.ne hv) :=
  rfl

/-- On the standard affine chart the induced projective map is exactly
`z ↦ y₀+r z`, with no unspecified projective scalar. -/
theorem projectiveAffineMap_affineChartPoint
    (y₀ : σ → K) (r : K) (hr : r ≠ 0) (z : σ → K) :
    projectiveAffineMap y₀ r hr (affineChartPoint z) =
      affineChartPoint (fun i ↦ y₀ i + r * z i) := by
  unfold affineChartPoint
  rw [projectiveAffineMap_mk]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
  refine ⟨1, ?_⟩
  funext j
  cases j <;> simp [affineChartVector]

/-- The homogeneous affine automorphism acts on every vector with
homogenizing coordinate zero by the scalar `r`; hence it fixes its projective
class pointwise. -/
theorem projectiveAffineMap_mk_of_none_eq_zero
    (y₀ : σ → K) (r : K) (hr : r ≠ 0)
    (v : Option σ → K) (hv : v ≠ 0) (hvnone : v none = 0) :
    projectiveAffineMap y₀ r hr (Projectivization.mk K v hv) =
      Projectivization.mk K v hv := by
  rw [projectiveAffineMap_mk]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
  refine ⟨r, ?_⟩
  funext j
  cases j with
  | none => simp [hvnone]
  | some i => simp [hvnone]

/-- Consequently the projective automorphism fixes the entire hyperplane at
infinity pointwise, not merely setwise. -/
theorem projectiveAffineMap_fixed_on_hyperplaneAtInfinity
    (y₀ : σ → K) (r : K) (hr : r ≠ 0)
    {P : ℙ K (Option σ → K)}
    (hP : P ∈ (projectiveHyperplaneAtInfinity :
      Set (ℙ K (Option σ → K)))) :
    projectiveAffineMap y₀ r hr P = P := by
  rcases hP with ⟨v, hv, rfl, hvnone⟩
  exact projectiveAffineMap_mk_of_none_eq_zero y₀ r hr v hv hvnone

/-- The projective automorphism preserves the affine chart in both
directions. -/
theorem projectiveAffineMap_mem_standardAffineChart_iff
    (y₀ : σ → K) (r : K) (hr : r ≠ 0)
    (P : ℙ K (Option σ → K)) :
    projectiveAffineMap y₀ r hr P ∈ standardAffineChart ↔
      P ∈ standardAffineChart := by
  constructor
  · intro hP
    obtain ⟨w, hw⟩ :=
      (mem_standardAffineChart_iff_exists_affineChartPoint _).1 hP
    let z : σ → K := fun i ↦ r⁻¹ * (w i - y₀ i)
    have hzmap :
        projectiveAffineMap y₀ r hr (affineChartPoint z) =
          affineChartPoint w := by
      rw [projectiveAffineMap_affineChartPoint]
      apply congrArg affineChartPoint
      funext i
      dsimp [z]
      field_simp [hr]
      ring
    have hsource : P = affineChartPoint z :=
      projectiveAffineMap_injective y₀ r hr (hw.trans hzmap.symm)
    exact (mem_standardAffineChart_iff_exists_affineChartPoint P).2
      ⟨z, hsource⟩
  · intro hP
    obtain ⟨z, rfl⟩ :=
      (mem_standardAffineChart_iff_exists_affineChartPoint P).1 hP
    rw [projectiveAffineMap_affineChartPoint]
    exact affineChartPoint_mem_standardAffineChart _

/-- The induced projective map is bijective because it comes from a linear
equivalence. -/
theorem projectiveAffineMap_bijective
    (y₀ : σ → K) (r : K) (hr : r ≠ 0) :
    Function.Bijective (projectiveAffineMap y₀ r hr) := by
  constructor
  · exact projectiveAffineMap_injective y₀ r hr
  · intro x
    induction x using Projectivization.ind with
    | h v hv =>
      let w := (homogeneousAffineLinearEquiv y₀ r hr).symm v
      have hw : w ≠ 0 := by
        intro hzero
        apply hv
        have himage := congrArg (homogeneousAffineLinearEquiv y₀ r hr) hzero
        simpa [w] using himage
      refine ⟨Projectivization.mk K w hw, ?_⟩
      rw [projectiveAffineMap_mk]
      have himage : homogeneousAffineLinearEquiv y₀ r hr w = v :=
        (homogeneousAffineLinearEquiv y₀ r hr).apply_symm_apply v
      exact (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
        ⟨1, by simpa using himage.symm⟩

/-- The resulting literal projective equivalence. -/
def projectiveAffineEquiv
    (y₀ : σ → K) (r : K) (hr : r ≠ 0) :
    ℙ K (Option σ → K) ≃ ℙ K (Option σ → K) :=
  Equiv.ofBijective (projectiveAffineMap y₀ r hr)
    (projectiveAffineMap_bijective y₀ r hr)

end

end TranslatedDepthSeven

import HessianTheorem11.KernelQuadraticDominance
import Mathlib.LinearAlgebra.Projectivization.Basic

/-! Projective loci and their ordinary normalized affine charts. Dimensions
are the supremum of the actual reduced coordinate-ring dimensions of these
charts. The empty projective locus has dimension `⊥` (the paper uses -1).
The universal cone/projective dimension interface is supplied in the final
proofs by `ReducedProjectiveDimension.affineProjectiveDimensionInput`, using
the proved `UnconditionalGeneric.genericRankOpenInput`; it is not a remaining
external assumption. -/

noncomputable section
namespace HessianTheorem11.BibleProjectiveGeometry
open MvPolynomial Module Matrix PolynomialRestriction

def projectiveLocus {n : ℕ} (Z : Set (GeometricPoint n)) :
    Set (Projectivization GeometricField (GeometricPoint n)) :=
  {p | ∃ x ∈ Z, ∃ hx : x ≠ 0, Projectivization.mk GeometricField x hx = p}

def affineChart {n : ℕ} (Z : Set (GeometricPoint n)) (i : Fin n) :
    Set (GeometricPoint n) := {x | x ∈ Z ∧ x i = 1}

/-- The dimension computed on the standard finite affine cover of projective
space. Each chart is normalized by the actual equation `x i = 1`. -/
def projectiveDimension {n : ℕ} (Z : Set (GeometricPoint n)) : Dimension :=
  ⨆ i : Fin n, affineDimension (affineChart Z i)

theorem chart_ne_zero {n : ℕ} {Z : Set (GeometricPoint n)} {i : Fin n}
    {x : GeometricPoint n} (hx : x ∈ affineChart Z i) : x ≠ 0 := by
  intro h
  have hi := hx.2
  rw [h] at hi
  exact zero_ne_one hi

def chartPoint {n : ℕ} (Z : Set (GeometricPoint n)) (i : Fin n)
    (x : affineChart Z i) : Projectivization GeometricField (GeometricPoint n) :=
  Projectivization.mk GeometricField x.val (chart_ne_zero x.property)

theorem chartPoint_injective {n : ℕ} (Z : Set (GeometricPoint n)) (i : Fin n) :
    Function.Injective (chartPoint Z i) := by
  intro x y h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' GeometricField _ _ _ _).mp h
  have hai := congrFun ha i
  have ha1 : a = 1 := by
    simpa only [Pi.smul_apply, smul_eq_mul, x.property.2, y.property.2, mul_one] using hai
  apply Subtype.ext
  simpa [ha1] using ha.symm

/-- Every projective point of a cone occurs in one of these actual affine
charts, and normalization preserves its projective class. -/
theorem charts_cover {n : ℕ} (Z : Set (GeometricPoint n)) (hZ : IsAffineCone Z)
    (p : Projectivization GeometricField (GeometricPoint n)) (hp : p ∈ projectiveLocus Z) :
    ∃ i : Fin n, ∃ x : affineChart Z i, chartPoint Z i x = p := by
  obtain ⟨v, hv, hv0, rfl⟩ := hp
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv0 (funext h)
  let x := (v i)⁻¹ • v
  have hx : x ∈ affineChart Z i := by
    refine ⟨hZ _ v hv, ?_⟩
    simp [x, hi]
  refine ⟨i, ⟨x, hx⟩, ?_⟩
  exact (Projectivization.mk_eq_mk_iff' GeometricField _ _ _ _).mpr ⟨(v i)⁻¹, rfl⟩

theorem projectiveDimension_eq_bot_of_no_nonzero {n : ℕ}
    (Z : Set (GeometricPoint n)) (hZ : ∀ x ∈ Z, x = 0) :
    projectiveDimension Z = ⊥ := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro i
  have he : affineChart Z i = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact chart_ne_zero hx (hZ x hx.1)
  rw [he, affineDimension_empty]

/-- The standard dimension theorem for a nontrivial affine cone and its
projectivization, with dimension on the actual standard affine charts.
It follows from `D(x_i) ≅ (Z ∩ {x_i=1}) × G_m` and the finite chart cover.
This input is universal in the cone and has no polynomial degree or target. -/
structure AffineProjectiveDimensionInput : Prop where
  dimension_cone : ∀ {n : ℕ} (Z : Set (GeometricPoint n)),
    AlgebraicallyClosedSet Z → IsAffineCone Z →
    (∃ x ∈ Z, x ≠ 0) → affineDimension Z = projectiveDimension Z + 1

theorem dimension_le_of_add_one_le {a : Dimension} {b : ℕ}
    (h : a + 1 ≤ ((b + 1 : ℕ) : Dimension)) : a ≤ (b : Dimension) := by
  cases a with
  | none => exact bot_le
  | some a =>
    change ((a + 1 : ℕ∞) : Dimension) ≤ (((b : ℕ∞) + 1 : ℕ∞) : Dimension) at h
    have hh : a + 1 ≤ (b : ℕ∞) + 1 := WithBot.coe_le_coe.mp h
    exact WithBot.coe_le_coe.mpr ((ENat.add_le_add_iff_right (by simp)).mp hh)

theorem projectiveDimension_le (AP : AffineProjectiveDimensionInput)
    {n b : ℕ} (Z : Set (GeometricPoint n)) (hc : AlgebraicallyClosedSet Z)
    (hcone : IsAffineCone Z) (h : affineDimension Z ≤ ((b + 1 : ℕ) : Dimension)) :
    projectiveDimension Z ≤ (b : Dimension) := by
  by_cases hnonzero : ∃ x ∈ Z, x ≠ 0
  · apply dimension_le_of_add_one_le
    rwa [← AP.dimension_cone Z hc hcone hnonzero]
  · have hz : ∀ x ∈ Z, x = 0 := by simpa only [not_exists, not_and, not_not] using hnonzero
    rw [projectiveDimension_eq_bot_of_no_nonzero Z hz]
    exact bot_le

theorem add_one_injective : Function.Injective (fun a : Dimension => a + 1) := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      change (⊥ : Dimension) = ((b + 1 : ℕ∞) : Dimension) at h
      cases h
  | some a =>
    cases b with
    | none =>
      change ((a + 1 : ℕ∞) : Dimension) = ⊥ at h
      cases h
    | some b =>
      have he : a + (1 : ℕ∞) = b + 1 := WithBot.coe_inj.mp h
      exact congrArg (fun x : ℕ∞ => (x : Dimension))
        (ENat.add_left_injective_of_ne_top (by simp) he)

/-- Actual injective changes of linear coordinates preserve projective
dimension, as well as giving the induced projective embedding. -/
theorem projectiveDimension_linearMap_image (AP : AffineProjectiveDimensionInput)
    {m n : ℕ} (L : GeometricPoint m →ₗ[GeometricField] GeometricPoint n)
    (hL : Function.Injective L) (Z : Set (GeometricPoint m))
    (hc : AlgebraicallyClosedSet Z) (hcone : IsAffineCone Z) :
    projectiveDimension (L '' Z) = projectiveDimension Z := by
  have hcone' : IsAffineCone (L '' Z) := by
    rintro a _ ⟨x, hx, rfl⟩
    exact ⟨a • x, hcone a x hx, L.map_smul a x⟩
  by_cases hn : ∃ x ∈ Z, x ≠ 0
  · obtain ⟨x, hx, hx0⟩ := hn
    have hn' : ∃ y ∈ L '' Z, y ≠ 0 :=
      ⟨L x, ⟨x, hx, rfl⟩, by intro he; exact hx0 (hL (he.trans L.map_zero.symm))⟩
    apply add_one_injective
    change projectiveDimension (L '' Z) + 1 = projectiveDimension Z + 1
    rw [← AP.dimension_cone (L '' Z) (algebraicallyClosedSet_linearMap_image L hL hc)
      hcone' hn', ← AP.dimension_cone Z hc hcone ⟨x, hx, hx0⟩,
      affineDimension_linearMap_image L hL]
  · have hz : ∀ x ∈ Z, x = 0 := by simpa only [not_exists, not_and, not_not] using hn
    rw [projectiveDimension_eq_bot_of_no_nonzero Z hz]
    apply projectiveDimension_eq_bot_of_no_nonzero
    rintro y ⟨x, hx, rfl⟩
    rw [hz x hx, L.map_zero]

/-- Every codimension-one vector subspace has an actual injective frame
with exactly that range; hence quantifying over frames covers all geometric
projective hyperplanes. -/
theorem exists_hyperplane_frame {K : Type*} [Field K] {m : ℕ}
    (H : Submodule K (Fin (m + 1) → K))
    (hH : finrank K H = m) :
    ∃ B : Matrix (Fin (m + 1)) (Fin m) K,
      Function.Injective B.mulVec ∧ LinearMap.range B.mulVecLin = H := by
  let b : Basis (Fin m) K H :=
    (Module.finBasis K H).reindex (finCongr hH)
  let L := H.subtype.comp b.equivFun.symm.toLinearMap
  let B := LinearMap.toMatrix' L
  have hBL : B.mulVecLin = L := by
    apply LinearMap.ext
    intro z
    exact LinearMap.toMatrix'_mulVec L z
  refine ⟨B, ?_, ?_⟩
  · change Function.Injective B.mulVecLin
    rw [hBL]
    exact Subtype.val_injective.comp b.equivFun.symm.injective
  · rw [hBL]
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact (b.equivFun.symm z).property
    · intro hy
      refine ⟨b.equivFun ⟨y, hy⟩, ?_⟩
      simp [L]

theorem frame_range_dimension {K : Type*} [Field K] {m : ℕ}
    (B : Matrix (Fin (m + 1)) (Fin m) K) (hB : Function.Injective B.mulVec) :
    finrank K (LinearMap.range B.mulVecLin) = m := by
  rw [LinearMap.finrank_range_of_inj hB]
  simp

/-- The frame pullback has exactly the ambient cubic's zero set inside H. -/
theorem frame_hypersurface_image {m n : ℕ}
    (B : Matrix (Fin n) (Fin m) GeometricField) (F : GeometricPolynomial n) :
    B.mulVec '' polynomialHypersurface (restrict B F) =
      {x | x ∈ LinearMap.range B.mulVecLin ∧ eval x F = 0} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, rfl⟩, by simpa only [polynomialHypersurface, Set.mem_setOf_eq, eval_restrict] using hy⟩
  · rintro ⟨⟨y, rfl⟩, hy⟩
    exact ⟨y, by simpa only [polynomialHypersurface, Set.mem_setOf_eq, eval_restrict] using hy, rfl⟩

end HessianTheorem11.BibleProjectiveGeometry

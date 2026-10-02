import HessianTheorem11.Geometry
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!+# Dimension of reduced affine point sets

These results apply to `affineDimension` as actually defined in this project:
the Krull dimension of the polynomial ring modulo the full vanishing ideal.
Monotonicity, the dimension of a point, and finite-union assembly are proved
from the existing order-theoretic and ring-theoretic definitions.
-/

namespace HessianTheorem11

open MvPolynomial

noncomputable section

theorem affineDimension_mono {σ : Type*} {A B : Set (σ → GeometricField)}
    (contained : A ⊆ B) : affineDimension A ≤ affineDimension B := by
  exact ringKrullDim_le_of_surjective
    (Ideal.Quotient.factor (vanishingIdeal_anti_mono contained))
    (Ideal.Quotient.factor_surjective _)

theorem affineDimension_empty {σ : Type*} :
    affineDimension (∅ : Set (σ → GeometricField)) = ⊥ := by
  unfold affineDimension
  rw [vanishingIdeal_empty]
  exact ringKrullDim_eq_bot_of_subsingleton

theorem affineDimension_singleton {σ : Type*} (x : σ → GeometricField) :
    affineDimension ({x} : Set (σ → GeometricField)) = 0 := by
  letI := Ideal.Quotient.field (vanishingIdeal GeometricField ({x} : Set (σ → GeometricField)))
  exact ringKrullDim_eq_zero_of_field _

theorem affineDimension_origin {n : ℕ} :
    affineDimension ({0} : Set (GeometricPoint n)) = 0 :=
  affineDimension_singleton 0

theorem affineDimension_nonneg_of_nonempty {σ : Type*}
    {Z : Set (σ → GeometricField)} (nonempty : Z.Nonempty) :
    0 ≤ affineDimension Z := by
  obtain ⟨x, hx⟩ := nonempty
  have bound := affineDimension_mono (Set.singleton_subset_iff.mpr hx)
  rwa [affineDimension_singleton] at bound

/-- An increasing chain in a union of upper sets lies entirely in the upper
set containing its first term. -/
theorem krullDim_union_upperSets {α : Type*} [Preorder α]
    (A B : Set α) (upperA : IsUpperSet A) (upperB : IsUpperSet B) :
    Order.krullDim (A ∪ B : Set α) = max (Order.krullDim A) (Order.krullDim B) := by
  apply le_antisymm
  · apply iSup_le
    intro p
    rcases p.head.property with hA | hB
    · let q : LTSeries A :=
        { length := p.length
          toFun := fun i => ⟨(p i).1, upperA (p.head_le i) hA⟩
          step := fun i => p.step i }
      exact le_trans (le_iSup_of_le q le_rfl) (le_max_left _ _)
    · let q : LTSeries B :=
        { length := p.length
          toFun := fun i => ⟨(p i).1, upperB (p.head_le i) hB⟩
          step := fun i => p.step i }
      exact le_trans (le_iSup_of_le q le_rfl) (le_max_right _ _)
  · apply max_le
    · exact Order.krullDim_le_of_strictMono
        (fun a : A => (⟨a.1, Or.inl a.2⟩ : (A ∪ B : Set α))) (fun _ _ h => h)
    · exact Order.krullDim_le_of_strictMono
        (fun b : B => (⟨b.1, Or.inr b.2⟩ : (A ∪ B : Set α))) (fun _ _ h => h)

theorem quotient_inf_ringKrullDim {R : Type*} [CommRing R] (I J : Ideal R) :
    ringKrullDim (R ⧸ (I ⊓ J)) =
      max (ringKrullDim (R ⧸ I)) (ringKrullDim (R ⧸ J)) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient, ringKrullDim_quotient,
    PrimeSpectrum.zeroLocus_inf]
  apply krullDim_union_upperSets
  · intro a b hab ha
    exact fun f hf => hab (ha hf)
  · intro a b hab ha
    exact fun f hf => hab (ha hf)

theorem affineDimension_union {σ : Type*} (A B : Set (σ → GeometricField)) :
    affineDimension (A ∪ B) = max (affineDimension A) (affineDimension B) := by
  have hv : vanishingIdeal GeometricField (A ∪ B) =
      vanishingIdeal GeometricField A ⊓ vanishingIdeal GeometricField B := by
    ext f
    simp only [mem_vanishingIdeal_iff, Ideal.mem_inf, Set.mem_union, or_imp, forall_and]
  unfold affineDimension
  rw [hv]
  exact quotient_inf_ringKrullDim _ _

theorem affineDimension_finset_union {σ ι : Type*}
    (s : Finset ι) (Z : ι → Set (σ → GeometricField)) :
    affineDimension (⋃ i ∈ s, Z i) = s.sup (fun i => affineDimension (Z i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [affineDimension_empty]
  | @insert i s hi ih =>
      simp [affineDimension_union, ih]

theorem affineDimension_finset_union_le {σ ι : Type*}
    (s : Finset ι) (Z : ι → Set (σ → GeometricField)) {d : Dimension}
    (bound : ∀ i ∈ s, affineDimension (Z i) ≤ d) :
    affineDimension (⋃ i ∈ s, Z i) ≤ d := by
  rw [affineDimension_finset_union]
  exact Finset.sup_le bound

theorem affineDimension_fintype_union_le {σ ι : Type*} [Fintype ι]
    (Z : ι → Set (σ → GeometricField)) {d : Dimension}
    (bound : ∀ i, affineDimension (Z i) ≤ d) :
    affineDimension (⋃ i, Z i) ≤ d := by
  simpa using affineDimension_finset_union_le Finset.univ Z (fun i _ => bound i)

theorem affineDimension_finite_set_le_zero {σ : Type*}
    {Z : Set (σ → GeometricField)} (finite : Z.Finite) :
    affineDimension Z ≤ 0 := by
  classical
  have union_eq : (⋃ x ∈ finite.toFinset, ({x} : Set (σ → GeometricField))) = Z := by
    ext x
    simp
  rw [← union_eq]
  apply affineDimension_finset_union_le
  intro x _
  exact (affineDimension_singleton x).le

theorem affineDimension_finite_set {σ : Type*}
    {Z : Set (σ → GeometricField)} (finite : Z.Finite) (nonempty : Z.Nonempty) :
    affineDimension Z = 0 :=
  le_antisymm (affineDimension_finite_set_le_zero finite)
    (affineDimension_nonneg_of_nonempty nonempty)

end

end HessianTheorem11

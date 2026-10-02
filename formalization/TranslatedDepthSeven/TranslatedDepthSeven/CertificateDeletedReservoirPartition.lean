import TranslatedDepthSeven.ManuscriptModulusReservoir
import TranslatedDepthSeven.StaticComparison
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Static comparison after pointwise deletion of certificate primes

For each point, delete from one fixed prime pool the primes dividing either
of two displayed integer certificates.  The resulting fixed-cardinality
reservoir has its own connected one-exchange graph.  This file applies the
connected-label trichotomy on that literal graph and then regards its moduli
as members of the original reservoir.

The final cardinal inequality is the exact point-dependent version needed
in the translated depth-seven argument.  Its three terms are indexed by one
ambient modulus, one ambient directed edge, and one nonempty label which is
constant on all moduli surviving at the point.  There is no path selection,
ordering, or stopping construction.
-/

namespace TranslatedDepthSeven

noncomputable section

open SimpleGraph

universe u v

variable {Point : Type u} {Label : Type v}

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Membership of an ambient reservoir modulus in the subreservoir obtained
by deleting the prime divisors of two integer certificates. -/
def survivesTwoCertificates {P : Finset ℕ} {k : ℕ}
    (q : ReservoirModulus P k) (D₁ D₂ : ℤ) : Prop :=
  Nat.Coprime q.1 D₁.natAbs ∧ Nat.Coprime q.1 D₂.natAbs

/-- The literal inclusion of a two-certificate subreservoir into the fixed
ambient reservoir. -/
def certificateAllowedTwoModulusEmbedding
    {P : Finset ℕ} {k : ℕ} (hP : ∀ p ∈ P, p.Prime) (D₁ D₂ : ℤ) :
    ReservoirModulus (certificateAllowedPrimesTwo P D₁ D₂) k ↪
      ReservoirModulus P k where
  toFun q := ⟨q.1,
    ((mem_certificateAllowedTwo_modulusReservoir_iff hP D₁ D₂).mp
      q.2).1⟩
  inj' q r hqr := by
    apply Subtype.ext
    exact congrArg (fun s : ReservoirModulus P k ↦ s.1) hqr

@[simp]
theorem certificateAllowedTwoModulusEmbedding_val
    {P : Finset ℕ} {k : ℕ} (hP : ∀ p ∈ P, p.Prime) (D₁ D₂ : ℤ)
    (q : ReservoirModulus (certificateAllowedPrimesTwo P D₁ D₂) k) :
    (certificateAllowedTwoModulusEmbedding hP D₁ D₂ q).1 = q.1 := rfl

@[simp]
theorem certificateAllowedTwoModulusEmbedding_survives
    {P : Finset ℕ} {k : ℕ} (hP : ∀ p ∈ P, p.Prime) (D₁ D₂ : ℤ)
    (q : ReservoirModulus (certificateAllowedPrimesTwo P D₁ D₂) k) :
    survivesTwoCertificates
      (certificateAllowedTwoModulusEmbedding hP D₁ D₂ q) D₁ D₂ := by
  exact ((mem_certificateAllowedTwo_modulusReservoir_iff hP D₁ D₂).mp
    q.2).2

/-- Every ambient reservoir modulus avoiding the two certificates comes
from a unique modulus in the deleted-prime reservoir. -/
theorem exists_unique_certificateAllowedTwo_preimage
    {P : Finset ℕ} {k : ℕ} (hP : ∀ p ∈ P, p.Prime) (D₁ D₂ : ℤ)
    (q : ReservoirModulus P k) :
    survivesTwoCertificates q D₁ D₂ →
      ∃! r : ReservoirModulus (certificateAllowedPrimesTwo P D₁ D₂) k,
        certificateAllowedTwoModulusEmbedding hP D₁ D₂ r = q := by
  intro hq
  let r : ReservoirModulus (certificateAllowedPrimesTwo P D₁ D₂) k :=
    ⟨q.1, (mem_certificateAllowedTwo_modulusReservoir_iff hP D₁ D₂).mpr
      ⟨q.2, hq⟩⟩
  refine ⟨r, Subtype.ext rfl, ?_⟩
  intro r' hr'
  apply Subtype.ext
  change r'.1 = q.1
  exact congrArg (fun s : ReservoirModulus P k ↦ s.1) hr'

/-- One-exchange adjacency is preserved when a deleted-prime reservoir is
included in the ambient reservoir. -/
theorem certificateAllowedTwoModulusEmbedding_adj
    {P : Finset ℕ} {k : ℕ} (hP : ∀ p ∈ P, p.Prime) (D₁ D₂ : ℤ)
    {q r : ReservoirModulus (certificateAllowedPrimesTwo P D₁ D₂) k}
    (hqr : (modulusReservoirGraph
      (certificateAllowedPrimesTwo P D₁ D₂) k
      (fun p hp ↦ hP p (Finset.mem_filter.mp hp).1)).Adj q r) :
    (modulusReservoirGraph P k hP).Adj
      (certificateAllowedTwoModulusEmbedding hP D₁ D₂ q)
      (certificateAllowedTwoModulusEmbedding hP D₁ D₂ r) := hqr

/-- Pointwise connected-label trichotomy after deleting the prime divisors
of two certificates.  All three alternatives are expressed on the original
fixed reservoir. -/
theorem certificateDeleted_reservoir_label_trichotomy
    {P : Finset ℕ} {k : ℕ} (hP : ∀ p ∈ P, p.Prime)
    (D₁ D₂ : ℤ) (label : ReservoirModulus P k → Option Label)
    (hconnected : (modulusReservoirGraph
      (certificateAllowedPrimesTwo P D₁ D₂) k
      (fun p hp ↦ hP p (Finset.mem_filter.mp hp).1)).Connected) :
    (∃ q : ReservoirModulus P k,
        survivesTwoCertificates q D₁ D₂ ∧ label q = none) ∨
      (∃ q r : ReservoirModulus P k,
        survivesTwoCertificates q D₁ D₂ ∧
        survivesTwoCertificates r D₁ D₂ ∧
        (modulusReservoirGraph P k hP).Adj q r ∧ label q ≠ label r) ∨
      ∃ b : Label, ∀ q : ReservoirModulus P k,
        survivesTwoCertificates q D₁ D₂ → label q = some b := by
  let hAllowedPrime : ∀ p ∈ certificateAllowedPrimesTwo P D₁ D₂,
      p.Prime := fun p hp ↦ hP p (Finset.mem_filter.mp hp).1
  let inclusion :
      ReservoirModulus (certificateAllowedPrimesTwo P D₁ D₂) k ↪
        ReservoirModulus P k :=
    certificateAllowedTwoModulusEmbedding (k := k) hP D₁ D₂
  let restrictedLabel :
      ReservoirModulus (certificateAllowedPrimesTwo P D₁ D₂) k →
        Option Label := fun q ↦ label (inclusion q)
  rcases StaticComparison.connected_option_labels hconnected restrictedLabel with
    ⟨q, hq⟩ | ⟨q, r, hqr, hne⟩ | ⟨b, hb⟩
  · left
    exact ⟨inclusion q,
      certificateAllowedTwoModulusEmbedding_survives hP D₁ D₂ q, hq⟩
  · right
    left
    exact ⟨inclusion q, inclusion r,
      certificateAllowedTwoModulusEmbedding_survives hP D₁ D₂ q,
      certificateAllowedTwoModulusEmbedding_survives hP D₁ D₂ r,
      certificateAllowedTwoModulusEmbedding_adj hP D₁ D₂ hqr, hne⟩
  · right
    right
    refine ⟨b, ?_⟩
    intro q hq
    obtain ⟨r, hr, _hrUnique⟩ :=
      exists_unique_certificateAllowedTwo_preimage hP D₁ D₂ q hq
    rw [← hr]
    exact hb r

/-- Strengthened form in which the edge alternative records that both
endpoint labels are nonempty.  If either endpoint label is empty, the point
is put in the first alternative instead. -/
theorem certificateDeleted_reservoir_label_trichotomy_nonempty_edge
    {P : Finset ℕ} {k : ℕ} (hP : ∀ p ∈ P, p.Prime)
    (D₁ D₂ : ℤ) (label : ReservoirModulus P k → Option Label)
    (hconnected : (modulusReservoirGraph
      (certificateAllowedPrimesTwo P D₁ D₂) k
      (fun p hp ↦ hP p (Finset.mem_filter.mp hp).1)).Connected) :
    (∃ q : ReservoirModulus P k,
        survivesTwoCertificates q D₁ D₂ ∧ label q = none) ∨
      (∃ q r : ReservoirModulus P k,
        survivesTwoCertificates q D₁ D₂ ∧
        survivesTwoCertificates r D₁ D₂ ∧
        (modulusReservoirGraph P k hP).Adj q r ∧
        label q ≠ label r ∧ label q ≠ none ∧ label r ≠ none) ∨
      ∃ b : Label, ∀ q : ReservoirModulus P k,
        survivesTwoCertificates q D₁ D₂ → label q = some b := by
  rcases certificateDeleted_reservoir_label_trichotomy
      hP D₁ D₂ label hconnected with
    hvertex | hedge | hpersistent
  · exact Or.inl hvertex
  · rcases hedge with ⟨q, r, hq, hr, hqr, hne⟩
    by_cases hqnone : label q = none
    · exact Or.inl ⟨q, hq, hqnone⟩
    by_cases hrnone : label r = none
    · exact Or.inl ⟨r, hr, hrnone⟩
    · exact Or.inr (Or.inl ⟨q, r, hq, hr, hqr, hne,
        hqnone, hrnone⟩)
  · exact Or.inr (Or.inr hpersistent)

/-- The labels which actually occur at a point and at an ambient modulus
surviving its two certificates. -/
def occurringCertificateDeletedLabels
    [DecidableEq Point] [DecidableEq Label]
    {P : Finset ℕ} {k : ℕ}
    (X : Finset Point) (D₁ D₂ : Point → ℤ)
    (label : Point → ReservoirModulus P k → Option Label) :
    Finset (Option Label) := by
  classical
  exact X.biUnion fun x ↦
    (Finset.univ.filter fun q : ReservoirModulus P k ↦
      survivesTwoCertificates q (D₁ x) (D₂ x)).image (label x)

@[simp]
theorem mem_occurringCertificateDeletedLabels_iff
    [DecidableEq Point] [DecidableEq Label]
    {P : Finset ℕ} {k : ℕ}
    (X : Finset Point) (D₁ D₂ : Point → ℤ)
    (label : Point → ReservoirModulus P k → Option Label)
    (o : Option Label) :
    o ∈ occurringCertificateDeletedLabels X D₁ D₂ label ↔
      ∃ x ∈ X, ∃ q : ReservoirModulus P k,
        survivesTwoCertificates q (D₁ x) (D₂ x) ∧ label x q = o := by
  classical
  simp [occurringCertificateDeletedLabels]

/-- Cardinal form of the pointwise two-certificate reservoir trichotomy.

The edge sum is deliberately over directed ambient pairs; only pairs which
survive both pointwise deletions and are genuinely adjacent contribute. -/
theorem card_le_sum_certificateDeleted_reservoir
    [DecidableEq Point] [DecidableEq Label]
    {P : Finset ℕ} {k : ℕ} (hP : ∀ p ∈ P, p.Prime)
    (X : Finset Point) (D₁ D₂ : Point → ℤ)
    (label : Point → ReservoirModulus P k → Option Label)
    (hconnected : ∀ x ∈ X,
      (modulusReservoirGraph
        (certificateAllowedPrimesTwo P (D₁ x) (D₂ x)) k
        (fun p hp ↦ hP p (Finset.mem_filter.mp hp).1)).Connected) :
    X.card ≤
      (∑ q : ReservoirModulus P k,
        (X.filter fun x ↦
          survivesTwoCertificates q (D₁ x) (D₂ x) ∧
            label x q = none).card) +
      (∑ q : ReservoirModulus P k, ∑ r : ReservoirModulus P k,
        (X.filter fun x ↦
          survivesTwoCertificates q (D₁ x) (D₂ x) ∧
          survivesTwoCertificates r (D₁ x) (D₂ x) ∧
          (modulusReservoirGraph P k hP).Adj q r ∧
            label x q ≠ label x r).card) +
      (∑ o ∈ occurringCertificateDeletedLabels X D₁ D₂ label,
        (X.filter fun x ↦
          o ≠ none ∧ ∀ q : ReservoirModulus P k,
            survivesTwoCertificates q (D₁ x) (D₂ x) →
              label x q = o).card) := by
  classical
  let vertexUnion : Finset Point :=
    Finset.univ.biUnion fun q : ReservoirModulus P k ↦
      X.filter fun x ↦
        survivesTwoCertificates q (D₁ x) (D₂ x) ∧ label x q = none
  let edgeUnion : Finset Point :=
    Finset.univ.biUnion fun q : ReservoirModulus P k ↦
      Finset.univ.biUnion fun r : ReservoirModulus P k ↦
        X.filter fun x ↦
          survivesTwoCertificates q (D₁ x) (D₂ x) ∧
          survivesTwoCertificates r (D₁ x) (D₂ x) ∧
          (modulusReservoirGraph P k hP).Adj q r ∧ label x q ≠ label x r
  let persistentUnion : Finset Point :=
    (occurringCertificateDeletedLabels X D₁ D₂ label).biUnion fun o ↦
      X.filter fun x ↦
        o ≠ none ∧ ∀ q : ReservoirModulus P k,
          survivesTwoCertificates q (D₁ x) (D₂ x) → label x q = o
  have hcover : X ⊆ vertexUnion ∪ edgeUnion ∪ persistentUnion := by
    intro x hx
    rcases certificateDeleted_reservoir_label_trichotomy
        hP (D₁ x) (D₂ x) (label x) (hconnected x hx) with
      ⟨q, hqSurvives, hqLabel⟩ |
      ⟨q, r, hqSurvives, hrSurvives, hqr, hne⟩ |
      ⟨b, hb⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr
        ⟨q, Finset.mem_univ q, Finset.mem_filter.mpr
          ⟨hx, hqSurvives, hqLabel⟩⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr
        ⟨q, Finset.mem_univ q, Finset.mem_biUnion.mpr
          ⟨r, Finset.mem_univ r, Finset.mem_filter.mpr
            ⟨hx, hqSurvives, hrSurvives, hqr, hne⟩⟩⟩
    · apply Finset.mem_union_right
      have hnonempty := (hconnected x hx).nonempty
      let r := Classical.choice hnonempty
      let q := certificateAllowedTwoModulusEmbedding hP (D₁ x) (D₂ x) r
      have hqSurvives : survivesTwoCertificates q (D₁ x) (D₂ x) :=
        certificateAllowedTwoModulusEmbedding_survives
          hP (D₁ x) (D₂ x) r
      have hoccurs : some b ∈
          occurringCertificateDeletedLabels X D₁ D₂ label := by
        exact (mem_occurringCertificateDeletedLabels_iff
          X D₁ D₂ label (some b)).2
          ⟨x, hx, q, hqSurvives, hb q hqSurvives⟩
      exact Finset.mem_biUnion.mpr
        ⟨some b, hoccurs, Finset.mem_filter.mpr
          ⟨hx, Option.some_ne_none b, hb⟩⟩
  have hvertex : vertexUnion.card ≤
      ∑ q : ReservoirModulus P k,
        (X.filter fun x ↦
          survivesTwoCertificates q (D₁ x) (D₂ x) ∧
            label x q = none).card := Finset.card_biUnion_le
  have hedge : edgeUnion.card ≤
      ∑ q : ReservoirModulus P k, ∑ r : ReservoirModulus P k,
        (X.filter fun x ↦
          survivesTwoCertificates q (D₁ x) (D₂ x) ∧
          survivesTwoCertificates r (D₁ x) (D₂ x) ∧
          (modulusReservoirGraph P k hP).Adj q r ∧
            label x q ≠ label x r).card := by
    refine Finset.card_biUnion_le.trans ?_
    apply Finset.sum_le_sum
    intro q _hq
    exact Finset.card_biUnion_le
  have hpersistent : persistentUnion.card ≤
      ∑ o ∈ occurringCertificateDeletedLabels X D₁ D₂ label,
        (X.filter fun x ↦
          o ≠ none ∧ ∀ q : ReservoirModulus P k,
            survivesTwoCertificates q (D₁ x) (D₂ x) →
              label x q = o).card := Finset.card_biUnion_le
  calc
    X.card ≤ (vertexUnion ∪ edgeUnion ∪ persistentUnion).card :=
      Finset.card_le_card hcover
    _ ≤ (vertexUnion ∪ edgeUnion).card + persistentUnion.card :=
      Finset.card_union_le _ _
    _ ≤ (vertexUnion.card + edgeUnion.card) + persistentUnion.card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add hvertex hedge) hpersistent

/-- Cardinal partition with the stronger edge class in which both endpoint
labels are nonempty. -/
theorem card_le_sum_certificateDeleted_reservoir_nonemptyEdges
    [DecidableEq Point] [DecidableEq Label]
    {P : Finset ℕ} {k : ℕ} (hP : ∀ p ∈ P, p.Prime)
    (X : Finset Point) (D₁ D₂ : Point → ℤ)
    (label : Point → ReservoirModulus P k → Option Label)
    (hconnected : ∀ x ∈ X,
      (modulusReservoirGraph
        (certificateAllowedPrimesTwo P (D₁ x) (D₂ x)) k
        (fun p hp ↦ hP p (Finset.mem_filter.mp hp).1)).Connected) :
    X.card ≤
      (∑ q : ReservoirModulus P k,
        (X.filter fun x ↦
          survivesTwoCertificates q (D₁ x) (D₂ x) ∧
            label x q = none).card) +
      (∑ q : ReservoirModulus P k, ∑ r : ReservoirModulus P k,
        (X.filter fun x ↦
          survivesTwoCertificates q (D₁ x) (D₂ x) ∧
          survivesTwoCertificates r (D₁ x) (D₂ x) ∧
          (modulusReservoirGraph P k hP).Adj q r ∧
          label x q ≠ label x r ∧
          label x q ≠ none ∧ label x r ≠ none).card) +
      (∑ o ∈ occurringCertificateDeletedLabels X D₁ D₂ label,
        (X.filter fun x ↦
          o ≠ none ∧ ∀ q : ReservoirModulus P k,
            survivesTwoCertificates q (D₁ x) (D₂ x) →
              label x q = o).card) := by
  classical
  let vertexUnion : Finset Point :=
    Finset.univ.biUnion fun q : ReservoirModulus P k ↦
      X.filter fun x ↦
        survivesTwoCertificates q (D₁ x) (D₂ x) ∧ label x q = none
  let edgeUnion : Finset Point :=
    Finset.univ.biUnion fun q : ReservoirModulus P k ↦
      Finset.univ.biUnion fun r : ReservoirModulus P k ↦
        X.filter fun x ↦
          survivesTwoCertificates q (D₁ x) (D₂ x) ∧
          survivesTwoCertificates r (D₁ x) (D₂ x) ∧
          (modulusReservoirGraph P k hP).Adj q r ∧
          label x q ≠ label x r ∧
          label x q ≠ none ∧ label x r ≠ none
  let persistentUnion : Finset Point :=
    (occurringCertificateDeletedLabels X D₁ D₂ label).biUnion fun o ↦
      X.filter fun x ↦
        o ≠ none ∧ ∀ q : ReservoirModulus P k,
          survivesTwoCertificates q (D₁ x) (D₂ x) → label x q = o
  have hcover : X ⊆ vertexUnion ∪ edgeUnion ∪ persistentUnion := by
    intro x hx
    rcases certificateDeleted_reservoir_label_trichotomy_nonempty_edge
        hP (D₁ x) (D₂ x) (label x) (hconnected x hx) with
      ⟨q, hqSurvives, hqLabel⟩ |
      ⟨q, r, hqSurvives, hrSurvives, hqr, hne, hqne, hrne⟩ |
      ⟨b, hb⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr
        ⟨q, Finset.mem_univ q, Finset.mem_filter.mpr
          ⟨hx, hqSurvives, hqLabel⟩⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr
        ⟨q, Finset.mem_univ q, Finset.mem_biUnion.mpr
          ⟨r, Finset.mem_univ r, Finset.mem_filter.mpr
            ⟨hx, hqSurvives, hrSurvives, hqr, hne, hqne, hrne⟩⟩⟩
    · apply Finset.mem_union_right
      have hnonempty := (hconnected x hx).nonempty
      let r := Classical.choice hnonempty
      let q := certificateAllowedTwoModulusEmbedding hP (D₁ x) (D₂ x) r
      have hqSurvives : survivesTwoCertificates q (D₁ x) (D₂ x) :=
        certificateAllowedTwoModulusEmbedding_survives
          hP (D₁ x) (D₂ x) r
      have hoccurs : some b ∈
          occurringCertificateDeletedLabels X D₁ D₂ label := by
        exact (mem_occurringCertificateDeletedLabels_iff
          X D₁ D₂ label (some b)).2
          ⟨x, hx, q, hqSurvives, hb q hqSurvives⟩
      exact Finset.mem_biUnion.mpr
        ⟨some b, hoccurs, Finset.mem_filter.mpr
          ⟨hx, Option.some_ne_none b, hb⟩⟩
  have hvertex : vertexUnion.card ≤
      ∑ q : ReservoirModulus P k,
        (X.filter fun x ↦
          survivesTwoCertificates q (D₁ x) (D₂ x) ∧
            label x q = none).card := Finset.card_biUnion_le
  have hedge : edgeUnion.card ≤
      ∑ q : ReservoirModulus P k, ∑ r : ReservoirModulus P k,
        (X.filter fun x ↦
          survivesTwoCertificates q (D₁ x) (D₂ x) ∧
          survivesTwoCertificates r (D₁ x) (D₂ x) ∧
          (modulusReservoirGraph P k hP).Adj q r ∧
          label x q ≠ label x r ∧
          label x q ≠ none ∧ label x r ≠ none).card := by
    refine Finset.card_biUnion_le.trans ?_
    apply Finset.sum_le_sum
    intro q _hq
    exact Finset.card_biUnion_le
  have hpersistent : persistentUnion.card ≤
      ∑ o ∈ occurringCertificateDeletedLabels X D₁ D₂ label,
        (X.filter fun x ↦
          o ≠ none ∧ ∀ q : ReservoirModulus P k,
            survivesTwoCertificates q (D₁ x) (D₂ x) →
              label x q = o).card := Finset.card_biUnion_le
  calc
    X.card ≤ (vertexUnion ∪ edgeUnion ∪ persistentUnion).card :=
      Finset.card_le_card hcover
    _ ≤ (vertexUnion ∪ edgeUnion).card + persistentUnion.card :=
      Finset.card_union_le _ _
    _ ≤ (vertexUnion.card + edgeUnion.card) + persistentUnion.card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add hvertex hedge) hpersistent

/-- The preceding partition with connectedness discharged by the exact
two-certificate clause of the manuscript reservoir theorem. -/
theorem card_le_sum_certificateDeleted_reservoir_of_twoCertificateSurvival
    [DecidableEq Point] [DecidableEq Label]
    {P : Finset ℕ} {k : ℕ} (hP : ∀ p ∈ P, p.Prime)
    (H A : ℝ)
    (hsurvival : ∀ D₁ D₂ : ℤ, D₁ ≠ 0 → D₂ ≠ 0 →
      (D₁.natAbs : ℝ) ≤ H ^ A → (D₂.natAbs : ℝ) ≤ H ^ A →
      Nonempty (ReservoirModulus
        (certificateAllowedPrimesTwo P D₁ D₂) k) ∧
      (modulusReservoirGraph
        (certificateAllowedPrimesTwo P D₁ D₂) k
        (fun p hp ↦ hP p (Finset.mem_filter.mp hp).1)).Connected)
    (X : Finset Point) (D₁ D₂ : Point → ℤ)
    (label : Point → ReservoirModulus P k → Option Label)
    (hD₁ne : ∀ x ∈ X, D₁ x ≠ 0)
    (hD₂ne : ∀ x ∈ X, D₂ x ≠ 0)
    (hD₁size : ∀ x ∈ X, ((D₁ x).natAbs : ℝ) ≤ H ^ A)
    (hD₂size : ∀ x ∈ X, ((D₂ x).natAbs : ℝ) ≤ H ^ A) :
    X.card ≤
      (∑ q : ReservoirModulus P k,
        (X.filter fun x ↦
          survivesTwoCertificates q (D₁ x) (D₂ x) ∧
            label x q = none).card) +
      (∑ q : ReservoirModulus P k, ∑ r : ReservoirModulus P k,
        (X.filter fun x ↦
          survivesTwoCertificates q (D₁ x) (D₂ x) ∧
          survivesTwoCertificates r (D₁ x) (D₂ x) ∧
          (modulusReservoirGraph P k hP).Adj q r ∧
            label x q ≠ label x r).card) +
      (∑ o ∈ occurringCertificateDeletedLabels X D₁ D₂ label,
        (X.filter fun x ↦
          o ≠ none ∧ ∀ q : ReservoirModulus P k,
            survivesTwoCertificates q (D₁ x) (D₂ x) →
              label x q = o).card) := by
  apply card_le_sum_certificateDeleted_reservoir hP X D₁ D₂ label
  intro x hx
  exact (hsurvival (D₁ x) (D₂ x)
    (hD₁ne x hx) (hD₂ne x hx)
    (hD₁size x hx) (hD₂size x hx)).2

end

end TranslatedDepthSeven

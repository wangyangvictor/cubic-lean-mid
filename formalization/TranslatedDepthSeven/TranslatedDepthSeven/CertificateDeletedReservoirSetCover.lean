import TranslatedDepthSeven.CertificateDeletedReservoirPartition

/-!
# The literal certificate-deleted reservoir cover

The cardinal partition in `CertificateDeletedReservoirPartition` is obtained
from a pointwise trichotomy.  This file exports the set inclusion before the
three unions are replaced by sums of cardinalities.  Retaining this inclusion
is necessary when equal degree-one curves occur in several record cells.
-/

namespace TranslatedDepthSeven

noncomputable section

open SimpleGraph

universe u v

variable {Point : Type u} {Label : Type v}

local instance certificateDeletedReservoirSetCoverPropDecidable
    (p : Prop) : Decidable p := Classical.propDecidable p

/-- Literal vertex--nonempty-edge--persistent cover supplied by the
certificate-deleted connected-label trichotomy. -/
theorem subset_union_certificateDeleted_reservoir_nonemptyEdges
    [DecidableEq Point] [DecidableEq Label]
    {P : Finset ℕ} {k : ℕ} (hP : ∀ p ∈ P, p.Prime)
    (X : Finset Point) (D₁ D₂ : Point → ℤ)
    (label : Point → ReservoirModulus P k → Option Label)
    (hconnected : ∀ x ∈ X,
      (modulusReservoirGraph
        (certificateAllowedPrimesTwo P (D₁ x) (D₂ x)) k
        (fun p hp ↦ hP p (Finset.mem_filter.mp hp).1)).Connected) :
    X ⊆
      ((Finset.univ : Finset (ReservoirModulus P k)).biUnion fun q ↦
        X.filter fun x ↦
          survivesTwoCertificates q (D₁ x) (D₂ x) ∧
            label x q = none) ∪
      (((Finset.univ : Finset (ReservoirModulus P k)).biUnion fun q ↦
        (Finset.univ : Finset (ReservoirModulus P k)).biUnion fun r ↦
          X.filter fun x ↦
            survivesTwoCertificates q (D₁ x) (D₂ x) ∧
            survivesTwoCertificates r (D₁ x) (D₂ x) ∧
            (modulusReservoirGraph P k hP).Adj q r ∧
            label x q ≠ label x r ∧
            label x q ≠ none ∧ label x r ≠ none) ∪
        ((occurringCertificateDeletedLabels X D₁ D₂ label).biUnion fun o ↦
          X.filter fun x ↦
            o ≠ none ∧ ∀ q : ReservoirModulus P k,
              survivesTwoCertificates q (D₁ x) (D₂ x) →
                label x q = o)) := by
  classical
  intro x hx
  rcases certificateDeleted_reservoir_label_trichotomy_nonempty_edge
      hP (D₁ x) (D₂ x) (label x) (hconnected x hx) with
    ⟨q, hqSurvives, hqLabel⟩ |
    ⟨q, r, hqSurvives, hrSurvives, hqr, hne, hqne, hrne⟩ |
    ⟨b, hb⟩
  · apply Finset.mem_union_left
    exact Finset.mem_biUnion.mpr
      ⟨q, Finset.mem_univ q, Finset.mem_filter.mpr
        ⟨hx, hqSurvives, hqLabel⟩⟩
  · apply Finset.mem_union_right
    apply Finset.mem_union_left
    exact Finset.mem_biUnion.mpr
      ⟨q, Finset.mem_univ q, Finset.mem_biUnion.mpr
        ⟨r, Finset.mem_univ r, Finset.mem_filter.mpr
          ⟨hx, hqSurvives, hrSurvives, hqr, hne, hqne, hrne⟩⟩⟩
  · apply Finset.mem_union_right
    apply Finset.mem_union_right
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

end

end TranslatedDepthSeven

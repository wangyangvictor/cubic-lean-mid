import TranslatedDepthSeven.CertificateDeletedReservoirPartition
import TranslatedDepthSeven.FiniteEquationComponentLabel

/-!
# Component comparison on certificate-deleted reservoirs

This is the polynomial specialization of the static two-certificate
reservoir partition.  At a point `x` and an ambient reservoir modulus `q`,
one has a literal finite equation family and labels `x` by one of the actual
minimal primes through its displayed coordinate vector.  Only moduli avoiding
the two certificates attached to `x` enter the comparison.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

universe u v w

variable {Point : Type u} {K : Type v} {σ : Type w}
variable [Field K] [Fintype σ]

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The finite set of component labels which actually occurs at a point and
at a modulus surviving its two certificate deletions. -/
def occurringCertificateDeletedEquationComponents
    [DecidableEq Point]
    {P : Finset ℕ} {k : ℕ}
    (X : Finset Point) (D₁ D₂ : Point → ℤ)
    (equations : Point → ReservoirModulus P k →
      Finset (MvPolynomial σ K))
    (coordinate : Point → σ → K) :
    Finset (Option (Ideal (MvPolynomial σ K))) :=
  occurringCertificateDeletedLabels X D₁ D₂ fun x q ↦
    selectedFiniteEquationComponent (equations x q) (coordinate x)

/-- Exact cardinal partition for point-dependent finite equation families
on the connected reservoir obtained after deleting two certificate sets.

The first sum contains points off the displayed locus at one surviving
modulus.  The second contains unequal selected minimal primes on a surviving
ambient edge.  In the last sum one nonempty ideal is selected at every
surviving modulus. -/
theorem card_le_sum_certificateDeleted_equationComponents
    [DecidableEq Point]
    {P : Finset ℕ} {k : ℕ} (hP : ∀ p ∈ P, p.Prime)
    (X : Finset Point) (D₁ D₂ : Point → ℤ)
    (equations : Point → ReservoirModulus P k →
      Finset (MvPolynomial σ K))
    (coordinate : Point → σ → K)
    (hconnected : ∀ x ∈ X,
      (modulusReservoirGraph
        (certificateAllowedPrimesTwo P (D₁ x) (D₂ x)) k
        (fun p hp ↦ hP p (Finset.mem_filter.mp hp).1)).Connected) :
    X.card ≤
      (∑ q : ReservoirModulus P k,
        (X.filter fun x ↦
          survivesTwoCertificates q (D₁ x) (D₂ x) ∧
          coordinate x ∉ finiteAffineCommonZeroLocus (equations x q)).card) +
      (∑ q : ReservoirModulus P k, ∑ r : ReservoirModulus P k,
        (X.filter fun x ↦
          survivesTwoCertificates q (D₁ x) (D₂ x) ∧
          survivesTwoCertificates r (D₁ x) (D₂ x) ∧
          (modulusReservoirGraph P k hP).Adj q r ∧
          selectedFiniteEquationComponent (equations x q) (coordinate x) ≠
            selectedFiniteEquationComponent (equations x r)
              (coordinate x)).card) +
      (∑ o ∈ occurringCertificateDeletedEquationComponents
          X D₁ D₂ equations coordinate,
        (X.filter fun x ↦
          o ≠ none ∧ ∀ q : ReservoirModulus P k,
            survivesTwoCertificates q (D₁ x) (D₂ x) →
            selectedFiniteEquationComponent (equations x q)
              (coordinate x) = o).card) := by
  let label : Point → ReservoirModulus P k →
      Option (Ideal (MvPolynomial σ K)) := fun x q ↦
    selectedFiniteEquationComponent (equations x q) (coordinate x)
  have h := card_le_sum_certificateDeleted_reservoir
    hP X D₁ D₂ label hconnected
  simpa only [label, occurringCertificateDeletedEquationComponents,
    selectedFiniteEquationComponent_eq_none_iff] using h

/-- The same component partition with connectedness discharged by the
two-certificate survival clause of the manuscript reservoir. -/
theorem card_le_sum_certificateDeleted_equationComponents_of_survival
    [DecidableEq Point]
    {P : Finset ℕ} {k : ℕ} (hP : ∀ p ∈ P, p.Prime)
    (H A : ℝ)
    (hsurvival : ∀ E₁ E₂ : ℤ, E₁ ≠ 0 → E₂ ≠ 0 →
      (E₁.natAbs : ℝ) ≤ H ^ A → (E₂.natAbs : ℝ) ≤ H ^ A →
      Nonempty (ReservoirModulus
        (certificateAllowedPrimesTwo P E₁ E₂) k) ∧
      (modulusReservoirGraph
        (certificateAllowedPrimesTwo P E₁ E₂) k
        (fun p hp ↦ hP p (Finset.mem_filter.mp hp).1)).Connected)
    (X : Finset Point) (D₁ D₂ : Point → ℤ)
    (equations : Point → ReservoirModulus P k →
      Finset (MvPolynomial σ K))
    (coordinate : Point → σ → K)
    (hD₁ne : ∀ x ∈ X, D₁ x ≠ 0)
    (hD₂ne : ∀ x ∈ X, D₂ x ≠ 0)
    (hD₁size : ∀ x ∈ X, ((D₁ x).natAbs : ℝ) ≤ H ^ A)
    (hD₂size : ∀ x ∈ X, ((D₂ x).natAbs : ℝ) ≤ H ^ A) :
    X.card ≤
      (∑ q : ReservoirModulus P k,
        (X.filter fun x ↦
          survivesTwoCertificates q (D₁ x) (D₂ x) ∧
          coordinate x ∉ finiteAffineCommonZeroLocus (equations x q)).card) +
      (∑ q : ReservoirModulus P k, ∑ r : ReservoirModulus P k,
        (X.filter fun x ↦
          survivesTwoCertificates q (D₁ x) (D₂ x) ∧
          survivesTwoCertificates r (D₁ x) (D₂ x) ∧
          (modulusReservoirGraph P k hP).Adj q r ∧
          selectedFiniteEquationComponent (equations x q) (coordinate x) ≠
            selectedFiniteEquationComponent (equations x r)
              (coordinate x)).card) +
      (∑ o ∈ occurringCertificateDeletedEquationComponents
          X D₁ D₂ equations coordinate,
        (X.filter fun x ↦
          o ≠ none ∧ ∀ q : ReservoirModulus P k,
            survivesTwoCertificates q (D₁ x) (D₂ x) →
            selectedFiniteEquationComponent (equations x q)
              (coordinate x) = o).card) := by
  apply card_le_sum_certificateDeleted_equationComponents
    hP X D₁ D₂ equations coordinate
  intro x hx
  exact (hsurvival (D₁ x) (D₂ x)
    (hD₁ne x hx) (hD₂ne x hx)
    (hD₁size x hx) (hD₂size x hx)).2

/-- At a point in the edge class, the two nonempty selected labels are
distinct actual minimal-prime components and the coordinate vector lies on
the zero locus of their ideal supremum. -/
theorem exists_distinct_components_and_mem_sup_of_certificateDeleted_edge
    [DecidableEq Point]
    {P : Finset ℕ} {k : ℕ} (hP : ∀ p ∈ P, p.Prime)
    (X : Finset Point) (D₁ D₂ : Point → ℤ)
    (equations : Point → ReservoirModulus P k →
      Finset (MvPolynomial σ K))
    (coordinate : Point → σ → K)
    {q r : ReservoirModulus P k} {x : Point}
    (_hx : x ∈ X)
    (_hq : survivesTwoCertificates q (D₁ x) (D₂ x))
    (_hr : survivesTwoCertificates r (D₁ x) (D₂ x))
    (_hqr : (modulusReservoirGraph P k hP).Adj q r)
    (hne : selectedFiniteEquationComponent (equations x q) (coordinate x) ≠
      selectedFiniteEquationComponent (equations x r) (coordinate x))
    (hzq : coordinate x ∈ finiteAffineCommonZeroLocus (equations x q))
    (hzr : coordinate x ∈ finiteAffineCommonZeroLocus (equations x r)) :
    ∃ Qq Qr : Ideal (MvPolynomial σ K),
      Qq ≠ Qr ∧
      selectedFiniteEquationComponent (equations x q) (coordinate x) =
        some Qq ∧
      selectedFiniteEquationComponent (equations x r) (coordinate x) =
        some Qr ∧
      coordinate x ∈ affineIdealZeroLocus (Qq ⊔ Qr) := by
  have hqNone : selectedFiniteEquationComponent
      (equations x q) (coordinate x) ≠ none := by
    intro hnone
    exact ((selectedFiniteEquationComponent_eq_none_iff
      (equations x q) (coordinate x)).mp hnone) hzq
  have hrNone : selectedFiniteEquationComponent
      (equations x r) (coordinate x) ≠ none := by
    intro hnone
    exact ((selectedFiniteEquationComponent_eq_none_iff
      (equations x r) (coordinate x)).mp hnone) hzr
  obtain ⟨Qq, hQq⟩ := Option.ne_none_iff_exists'.1 hqNone
  obtain ⟨Qr, hQr⟩ := Option.ne_none_iff_exists'.1 hrNone
  have hQne : Qq ≠ Qr := by
    intro hEq
    apply hne
    rw [hQq, hQr, hEq]
  exact ⟨Qq, Qr, hQne, hQq, hQr,
    mem_affineIdealZeroLocus_sup_of_two_selected_components
      (equations x q) (equations x r) (coordinate x) hQq hQr⟩

end

end TranslatedDepthSeven

import CubicTenVariables.HighDegreeConeFixedLeadingCount
import CubicTenVariables.ConeComponentProgressionCount

/-!
# Finite cone-component counts from fixed leading equations

The geometric component condition, actual point sets and low-dimensional
bound are reused unchanged. The high-degree branch uses the fixed-leading
hypersurface family through its proved finite projection. No Salberger
premise is used. The supplied geometric cover is still explicit; this file
does not assert construction of a promoted partition.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.ConeComponentFixedLeadingCount

open MvPolynomial TranslatedDepthSeven Published
open FixedLeadingHypersurfaceCountInduction ConeComponentProgressionCount
attribute [local instance] MvPolynomial.gradedAlgebra Classical.propDecidable

/-- The family of fixed-leading estimates needed by all high-degree cone
components. Its constants may depend on the fixed leading equation. -/
def HighDegreeFixedLeadingCounts : Prop :=
  ∀ n d : ℕ, 3 ≤ n → 4 ≤ d → ∀ ε : ℝ, 0 < ε →
    FixedRationalLeadingHypersurfaceBounds n d ε

private theorem card_le_sum_filters {n t : ℕ} (S : Finset (Fin n → ℤ))
    (I : Fin t → Ideal (MvPolynomial (Fin n) ℚ))
    (hcover : ∀ x ∈ S, ∃ k, (fun i => (x i : ℚ)) ∈ affineIdealZeroLocus (I k)) :
    S.card ≤ ∑ k, (S.filter fun x => (fun i => (x i : ℚ)) ∈ affineIdealZeroLocus (I k)).card := by
  classical
  let A : Fin t → Finset (Fin n → ℤ) := fun k =>
    S.filter fun x => (fun i => (x i : ℚ)) ∈ affineIdealZeroLocus (I k)
  change S.card ≤ ∑ k, (A k).card
  have hsub : S ⊆ Finset.univ.biUnion A := by
    intro x hx
    obtain ⟨k,hk⟩ := hcover x hx
    exact Finset.mem_biUnion.mpr ⟨k,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hx,hk⟩⟩
  have hsum : (Finset.univ.biUnion A).card ≤ ∑ k, (A k).card :=
    Finset.card_biUnion_le
  exact (Finset.card_le_card hsub).trans hsum

private theorem component_bound
    (hcounts : HighDegreeFixedLeadingCounts) {N r : ℕ} (hr : 1 ≤ r) (hrN : r < N)
    (I : Ideal (MvPolynomial (Fin (N+1)) ℚ)) (hI : ComponentCondition r I)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (S : Finset (Fin (N+1) → ℤ))
      (u : Fin (N+1) → ℝ) (L : ℝ), 0 ≤ L →
      ∀ (m : ℕ), 0 < m → ∀ b : Fin (N+1) → ℤ,
      (∀ x ∈ S, ∀ i, |(x i : ℝ)-u i| ≤ L) →
      (∀ x ∈ S, ∀ i, (m : ℤ) ∣ x i-b i) →
      (∀ x ∈ S, (fun i => (x i : ℚ)) ∈ affineIdealZeroLocus I) →
      (S.card : ℝ) ≤ C*(2+‖u‖+L+(m : ℝ))^ε*(1+L/(m : ℝ))^r := by
  rcases hI with ⟨hproper,hhom,hlow | ⟨d,hprime,hgeom,hdim,hd⟩⟩
  · obtain ⟨C,hC,hcount⟩ := HomogeneousProgressionBoxCount.exists_bound I hproper hhom r hlow
    refine ⟨C,hC,?_⟩
    intro S u L hL m hm b hbox hres hzero
    have hH : 1 ≤ 2+‖u‖+L+(m : ℝ) := by linarith [norm_nonneg u,(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hp := Real.one_le_rpow hH hε.le
    calc
      (S.card : ℝ) ≤ C*(1+L/(m : ℝ))^r := hcount S u L hL m hm b hbox hres hzero
      _ ≤ C*(2+‖u‖+L+(m : ℝ))^ε*(1+L/(m : ℝ))^r := by
        gcongr
        exact le_mul_of_one_le_right (zero_le_one.trans hC) hp
  · exact HighDegreeConeFixedLeadingCount.exists_source_bound
      (hcounts (r + 2) d (by omega) hd ε hε) hr hrN I hprime hgeom hhom hdim hd hε

/-- All high-degree and lower-dimensional components are summed with a
single constant chosen before the rational subset and the varying box data. -/
theorem exists_mixed_bound
    (hcounts : HighDegreeFixedLeadingCounts) {N r t : ℕ} (hr : 1 ≤ r) (hrN : r < N)
    (I : Fin t → Ideal (MvPolynomial (Fin (N+1)) ℚ))
    (hI : ∀ k, ComponentCondition r (I k)) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : Set (Fin (N+1) → ℚ),
      (∀ x ∈ P, ∃ k, x ∈ affineIdealZeroLocus (I k)) →
      ∀ (u : Fin (N+1) → ℝ) (L : ℝ), 0 ≤ L →
      ∀ (m : ℕ), 0 < m → ∀ b : Fin (N+1) → ℤ,
      ((points P u L m b).card : ℝ) ≤
        C*(2+‖u‖+L+(m : ℝ))^ε*(1+L/(m : ℝ))^r := by
  classical
  choose C hC hcount using fun k => component_bound hcounts hr hrN (I k) (hI k) ε hε
  refine ⟨1+∑ k, C k,?_,?_⟩
  · have hs : 0 ≤ ∑ k, C k := Finset.sum_nonneg fun k _ => (zero_le_one.trans (hC k))
    linarith
  intro P hcover u L hL m hm b
  let S := points P u L m b
  have hs (x) (hx : x ∈ S) := (mem_points P u L m b x).mp hx
  have hcards := card_le_sum_filters S I (fun x hx => hcover _ (hs x hx).2.2)
  have hnonneg : 0 ≤ (2+‖u‖+L+(m : ℝ))^ε*(1+L/(m : ℝ))^r := by positivity
  calc
    (S.card : ℝ) ≤ ∑ k, ((S.filter fun x =>
        (fun i => (x i : ℚ)) ∈ affineIdealZeroLocus (I k)).card : ℝ) := by exact_mod_cast hcards
    _ ≤ ∑ k, C k*(2+‖u‖+L+(m : ℝ))^ε*(1+L/(m : ℝ))^r := by
      apply Finset.sum_le_sum
      intro k _
      apply hcount k _ u L hL m hm b
      · intro x hx; exact (hs x (Finset.mem_filter.mp hx).1).1
      · intro x hx; exact (hs x (Finset.mem_filter.mp hx).1).2.1
      · intro x hx; exact (Finset.mem_filter.mp hx).2
    _ = (∑ k, C k)*((2+‖u‖+L+(m : ℝ))^ε*(1+L/(m : ℝ))^r) := by
      simp only [mul_assoc,Finset.sum_mul]
    _ ≤ (1+∑ k, C k)*((2+‖u‖+L+(m : ℝ))^ε*(1+L/(m : ℝ))^r) :=
      mul_le_mul_of_nonneg_right (by linarith) hnonneg
    _ = _ := by ring

/-- Exactly the retained n=10 exponents for j=3,4. This is a counting
application to a supplied geometric cover, not construction of that cover. -/
theorem exists_high_level_bound
    (hcounts : HighDegreeFixedLeadingCounts) (j : ℕ) (hj : j=3 ∨ j=4) {t : ℕ}
    (I : Fin t → Ideal (MvPolynomial (Fin 10) ℚ))
    (hI : ∀ k, ComponentCondition (8-j) (I k)) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : Set (Fin 10 → ℚ),
      (∀ x ∈ P, ∃ k, x ∈ affineIdealZeroLocus (I k)) →
      ∀ (u : Fin 10 → ℝ) (L : ℝ), 0 ≤ L →
      ∀ (m : ℕ), 0 < m → ∀ b : Fin 10 → ℤ,
      ((points P u L m b).card : ℝ) ≤
        C*(2+‖u‖+L+(m : ℝ))^ε*(1+L/(m : ℝ))^(8-j) :=
  exists_mixed_bound hcounts (by omega) (by omega) I hI ε hε


end CubicTenVariables.ConeComponentFixedLeadingCount

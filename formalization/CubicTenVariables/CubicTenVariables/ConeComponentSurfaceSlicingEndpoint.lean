import CubicTenVariables.ConeComponentProgressionCount
import CubicTenVariables.FixedConeSurfaceSlicingReduction

/-!
# Mixed cone-component counts from explicit surface slices

This file replaces the Salberger branch of
`ConeComponentProgressionCount` by the explicit fixed-family slicing
reduction.  It deliberately keeps the existing `ComponentCondition`, so the
geometric cover consumed downstream does not have to be restated.

For an actual high-degree witness, the additional datum is a literal
`RationalSurfaceSlicingCertificate` together with the uniform determinant
estimate for its good surface fibres.  Lower-dimensional components continue
to use `HomogeneousProgressionBoxCount` and require no slicing datum.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace CubicTenVariables.ConeComponentSurfaceSlicingEndpoint

open MvPolynomial TranslatedDepthSeven Published
open ConeComponentProgressionCount
open FixedConeSurfaceSlicingReduction

attribute [local instance] MvPolynomial.gradedAlgebra Classical.propDecidable

/-- The exact replacement datum for the high-degree alternative of the
existing `ComponentCondition`.  The quantifiers over the displayed
high-degree witness make this proposition vacuous for a component which has
only the low-dimensional alternative.

No high-dimensional point-count statement occurs here: the returned object
is a rational matrix, discriminant, exceptional ideal, literal good fibre
ideals and their geometry, followed by the uniform estimate on those
three-dimensional affine fibre ideals. -/
def HighComponentSurfaceSlicingData {N : ℕ} (r : ℕ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) : Prop :=
  ∀ d : ℕ,
    I.IsPrime →
    GeometricallyPrimeMvPolynomialIdeal I →
    HasProjectiveDimensionDegree I r d →
    4 ≤ d →
    ∃ cert : RationalSurfaceSlicingCertificate (r := r) (d := d) I,
      GoodSurfaceFibreProgressionEstimate I cert

/-- A single component satisfying the existing geometric condition has the
required translated progression count once its genuine high-degree branch
has explicit surface-slicing data. -/
private theorem component_bound_of_surfaceSlicing
    {N r : ℕ} (hr : 2 ≤ r)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : ComponentCondition r I)
    (slicing : HighComponentSurfaceSlicingData r I)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (S : Finset (Fin (N + 1) → ℤ))
      (u : Fin (N + 1) → ℝ) (L : ℝ), 0 ≤ L →
    ∀ (m : ℕ), 0 < m → ∀ b : Fin (N + 1) → ℤ,
      (∀ x ∈ S, ∀ i, |(x i : ℝ) - u i| ≤ L) →
      (∀ x ∈ S, ∀ i, (m : ℤ) ∣ x i - b i) →
      (∀ x ∈ S,
        (fun i ↦ (x i : ℚ)) ∈ affineIdealZeroLocus I) →
      (S.card : ℝ) ≤
        C * (2 + ‖u‖ + L + (m : ℝ)) ^ ε *
          (1 + L / (m : ℝ)) ^ r := by
  rcases hI with
    ⟨hproper, hhom, hlow | ⟨d, hprime, hgeom, hdim, hd⟩⟩
  · obtain ⟨C, hC, hcount⟩ :=
      HomogeneousProgressionBoxCount.exists_bound
        I hproper hhom r hlow
    refine ⟨C, hC, ?_⟩
    intro S u L hL m hm b hbox hres hzero
    have hW : 1 ≤ 2 + ‖u‖ + L + (m : ℝ) := by
      have hunorm : 0 ≤ ‖u‖ := norm_nonneg u
      have hmnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hWε : 1 ≤ (2 + ‖u‖ + L + (m : ℝ)) ^ ε :=
      Real.one_le_rpow hW hε.le
    have hbase : 0 ≤ (1 + L / (m : ℝ)) ^ r := by positivity
    calc
      (S.card : ℝ) ≤ C * (1 + L / (m : ℝ)) ^ r :=
        hcount S u L hL m hm b hbox hres hzero
      _ ≤ C * (2 + ‖u‖ + L + (m : ℝ)) ^ ε *
          (1 + L / (m : ℝ)) ^ r := by
        have hCnonneg : 0 ≤ C := zero_le_one.trans hC
        calc
          C * (1 + L / (m : ℝ)) ^ r =
              (C * (1 + L / (m : ℝ)) ^ r) * 1 := by ring
          _ ≤ (C * (1 + L / (m : ℝ)) ^ r) *
              (2 + ‖u‖ + L + (m : ℝ)) ^ ε :=
            mul_le_mul_of_nonneg_left hWε (mul_nonneg hCnonneg hbase)
          _ = C * (2 + ‖u‖ + L + (m : ℝ)) ^ ε *
              (1 + L / (m : ℝ)) ^ r := by ring
  · obtain ⟨cert, surface⟩ := slicing d hprime hgeom hdim hd
    exact exists_source_bound_of_surfaceSlicing
      hr I cert surface ε hε

/-- Elementary union bound for a finite cover, repeated here because the
corresponding helper in `ConeComponentProgressionCount` is intentionally
private. -/
private theorem card_le_sum_component_filters
    {n t : ℕ} (S : Finset (Fin n → ℤ))
    (I : Fin t → Ideal (MvPolynomial (Fin n) ℚ))
    (hcover : ∀ x ∈ S, ∃ k,
      (fun i ↦ (x i : ℚ)) ∈ affineIdealZeroLocus (I k)) :
    S.card ≤ ∑ k,
      (S.filter fun x ↦
        (fun i ↦ (x i : ℚ)) ∈ affineIdealZeroLocus (I k)).card := by
  classical
  let A : Fin t → Finset (Fin n → ℤ) := fun k ↦
    S.filter fun x ↦
      (fun i ↦ (x i : ℚ)) ∈ affineIdealZeroLocus (I k)
  change S.card ≤ ∑ k, (A k).card
  have hsub : S ⊆ Finset.univ.biUnion A := by
    intro x hx
    obtain ⟨k, hk⟩ := hcover x hx
    exact Finset.mem_biUnion.mpr
      ⟨k, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hx, hk⟩⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

/-- The mixed finite-component endpoint with no Salberger premise.  Each
component retains the old `ComponentCondition`; only an actual high-degree
witness invokes its corresponding surface-slicing datum. -/
theorem exists_mixed_bound_of_surfaceSlicing
    {N r t : ℕ} (hr : 2 ≤ r)
    (I : Fin t → Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : ∀ k, ComponentCondition r (I k))
    (slicing : ∀ k, HighComponentSurfaceSlicingData r (I k))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ P : Set (Fin (N + 1) → ℚ),
      (∀ x ∈ P, ∃ k, x ∈ affineIdealZeroLocus (I k)) →
    ∀ (u : Fin (N + 1) → ℝ) (L : ℝ), 0 ≤ L →
    ∀ (m : ℕ), 0 < m → ∀ b : Fin (N + 1) → ℤ,
      ((points P u L m b).card : ℝ) ≤
        C * (2 + ‖u‖ + L + (m : ℝ)) ^ ε *
          (1 + L / (m : ℝ)) ^ r := by
  classical
  choose C hC hcount using fun k ↦
    component_bound_of_surfaceSlicing
      hr (I k) (hI k) (slicing k) ε hε
  refine ⟨1 + ∑ k, C k, ?_, ?_⟩
  · have hs : 0 ≤ ∑ k, C k :=
      Finset.sum_nonneg fun k _ ↦ zero_le_one.trans (hC k)
    linarith
  intro P hcover u L hL m hm b
  let S := points P u L m b
  have hs (x) (hx : x ∈ S) := (mem_points P u L m b x).mp hx
  have hcards := card_le_sum_component_filters S I
    (fun x hx ↦ hcover _ (hs x hx).2.2)
  have hnonneg :
      0 ≤ (2 + ‖u‖ + L + (m : ℝ)) ^ ε *
        (1 + L / (m : ℝ)) ^ r := by positivity
  calc
    (S.card : ℝ) ≤ ∑ k,
        ((S.filter fun x ↦
          (fun i ↦ (x i : ℚ)) ∈ affineIdealZeroLocus (I k)).card : ℝ) := by
      exact_mod_cast hcards
    _ ≤ ∑ k, C k * (2 + ‖u‖ + L + (m : ℝ)) ^ ε *
        (1 + L / (m : ℝ)) ^ r := by
      apply Finset.sum_le_sum
      intro k _
      apply hcount k _ u L hL m hm b
      · intro x hx i
        exact (hs x (Finset.mem_filter.mp hx).1).1 i
      · intro x hx i
        exact (hs x (Finset.mem_filter.mp hx).1).2.1 i
      · intro x hx
        exact (Finset.mem_filter.mp hx).2
    _ = (∑ k, C k) *
        ((2 + ‖u‖ + L + (m : ℝ)) ^ ε *
          (1 + L / (m : ℝ)) ^ r) := by
      simp only [mul_assoc, Finset.sum_mul]
    _ ≤ (1 + ∑ k, C k) *
        ((2 + ‖u‖ + L + (m : ℝ)) ^ ε *
          (1 + L / (m : ℝ)) ^ r) :=
      mul_le_mul_of_nonneg_right (by linarith) hnonneg
    _ = _ := by ring

/-- The exact n=10 high-level consumer for `j=3,4`, with the former
`Salberger2023Theorem04` argument replaced componentwise by explicit rational
surface slicing. -/
theorem exists_n10_high_level_bound_of_surfaceSlicing
    (j : ℕ) (hj : j = 3 ∨ j = 4) {t : ℕ}
    (I : Fin t → Ideal (MvPolynomial (Fin 10) ℚ))
    (hI : ∀ k, ComponentCondition (8 - j) (I k))
    (slicing : ∀ k, HighComponentSurfaceSlicingData (8 - j) (I k))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ P : Set (Fin 10 → ℚ),
      (∀ x ∈ P, ∃ k, x ∈ affineIdealZeroLocus (I k)) →
    ∀ (u : Fin 10 → ℝ) (L : ℝ), 0 ≤ L →
    ∀ (m : ℕ), 0 < m → ∀ b : Fin 10 → ℤ,
      ((points P u L m b).card : ℝ) ≤
        C * (2 + ‖u‖ + L + (m : ℝ)) ^ ε *
          (1 + L / (m : ℝ)) ^ (8 - j) :=
  exists_mixed_bound_of_surfaceSlicing
    (by omega) I hI slicing ε hε

end CubicTenVariables.ConeComponentSurfaceSlicingEndpoint

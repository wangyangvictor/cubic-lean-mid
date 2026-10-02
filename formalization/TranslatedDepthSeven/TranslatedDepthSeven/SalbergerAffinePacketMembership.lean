import TranslatedDepthSeven.PublishedCountingApplications

/-!
# Affine packet points in Salberger's `S₁`

Salberger's Corollary 3.7 is stated for the affine-chart set `S₁`: its
integral representatives are literally `(1,z₁,...,z_N)`.  This file proves
the elementary membership bridge for exactly those representatives.  The
projective specialization is still allowed its intrinsic unit twist.
-/

namespace TranslatedDepthSeven

noncomputable section

open Published

/-- The literal integral representative `(1,z₁,...,z_N)` of an affine
integral point. -/
def integralAffineChartVector {N : ℕ} (z : IntVector N) :
    Fin (N + 1) → ℤ :=
  Fin.cases 1 z

@[simp]
theorem integralAffineChartVector_zero {N : ℕ} (z : IntVector N) :
    integralAffineChartVector z 0 = 1 := rfl

@[simp]
theorem integralAffineChartVector_succ {N : ℕ} (z : IntVector N)
    (i : Fin N) :
    integralAffineChartVector z i.succ = z i := rfl

/-- If the affine coordinates of `z` reduce to the standard affine
coordinates of `P`, then `(1,z)` specializes projectively to `P`. -/
theorem affineChartVector_specializesToProjectivePoint
    {N p : ℕ} (hp : p.Prime)
    (P : Fin (N + 1) → ZMod p) (hP0 : P 0 ≠ 0)
    (z : IntVector N)
    (hz : ∀ i : Fin N,
      (z i : ZMod p) = (P 0)⁻¹ * P i.succ) :
    SpecializesToProjectivePoint (integralAffineChartVector z) P := by
  letI : Fact p.Prime := ⟨hp⟩
  let u : (ZMod p)ˣ := (Units.mk0 (P 0) hP0)⁻¹
  refine ⟨u, ?_⟩
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [integralAffineChartVector, u, hP0]
  · simpa [integralAffineChartVector, u] using hz j

/-- A bounded integral affine point, lying on `I` after homogenization and
having the prescribed affine reductions, belongs to the exact set `S₁`
used in Salberger's Corollary 3.7. -/
theorem integralAffineChartVector_mem_InSalbergerSOne
    {N : ℕ} {index : Type*} [Fintype index]
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) (B : ℝ)
    (hB : 1 ≤ B)
    (prime : index → ℕ) (hprime : ∀ j, (prime j).Prime)
    (point : ∀ j, Fin (N + 1) → ZMod (prime j))
    (hpoint0 : ∀ j, point j 0 ≠ 0)
    (z : IntVector N)
    (hbox : ∀ i, |(z i : ℝ)| ≤ B)
    (hzero : ∀ f ∈ I,
      MvPolynomial.eval
        (fun i ↦ (integralAffineChartVector z i : ℚ)) f = 0)
    (hreduction : ∀ j i,
      (z i : ZMod (prime j)) =
        (point j 0)⁻¹ * point j i.succ) :
    InSalbergerSOne I B prime point (integralAffineChartVector z) := by
  refine ⟨rfl, ?_, hzero, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa using hB
    · simpa using hbox j
  · intro j
    exact affineChartVector_specializesToProjectivePoint
      (hprime j) (point j) (hpoint0 j) z (hreduction j)

/-- Exact finite-packet application of Salberger 2007, Corollary 3.7 in
its multiplicity-one case.  All geometry and all local hypotheses remain
visible; this theorem only proves that the literal representatives `(1,z)`
belong to the source set `S₁` and then invokes the published result. -/
theorem salberger2007_auxiliaryForm_for_integralAffinePacket
    (hSalberger : Salberger2007Corollary37)
    {N d r : ℕ} {ε : ℝ} (hε : 0 < ε)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hr : 1 ≤ r)
    (hI : IsReducedEquidimensionalProjectiveScheme I r d)
    (hinfinity : InfinityHyperplaneMeetsProperly I)
    {B : ℝ} (hB : 1 ≤ B)
    {index : Type} [Fintype index]
    (prime : index → ℕ)
    (hprime : ∀ i, (prime i).Prime)
    (hinjective : Function.Injective prime)
    (point : ∀ i, Fin (N + 1) → ZMod (prime i))
    (hchart : ∀ i, point i 0 ≠ 0)
    (hmultiplicity : ∀ i,
      HasHilbertSamuelMultiplicityAt (hprime i)
        (projectiveSpecialFiberIdeal I) (point i) r 1)
    (hproduct :
      B ^ (1 + ε) ≤
        ∏ i, (prime i : ℝ) ^
          (((d : ℝ) / (1 : ℝ)) ^ ((r : ℝ)⁻¹)))
    (points : Finset (IntVector N))
    (hbox : ∀ z ∈ points, ∀ i, |(z i : ℝ)| ≤ B)
    (hzero : ∀ z ∈ points, ∀ f ∈ I,
      MvPolynomial.eval
        (fun i ↦ (integralAffineChartVector z i : ℚ)) f = 0)
    (hreduction : ∀ z ∈ points, ∀ j i,
      (z i : ZMod (prime j)) =
        (point j 0)⁻¹ * point j i.succ) :
    ∃ K : ℕ,
      ∃ (k : ℕ) (G : MvPolynomial (Fin (N + 1)) ℚ),
        k ≤ K ∧ G.IsHomogeneous k ∧ G ∉ I ∧
          ∀ z ∈ points,
            MvPolynomial.eval
              (fun i ↦ (integralAffineChartVector z i : ℚ)) G = 0 := by
  obtain ⟨K, k, G, hk, hGhom, hGnot, hGvanish⟩ :=
    salberger2007_corollary37_multiplicityOne
      hSalberger hε I hr hI hinfinity hB prime hprime hinjective point
        hchart hmultiplicity hproduct
  refine ⟨K, k, G, hk, hGhom, hGnot, ?_⟩
  intro z hz
  apply hGvanish (integralAffineChartVector z)
  exact integralAffineChartVector_mem_InSalbergerSOne
    I B hB prime hprime point hchart z (hbox z hz) (hzero z hz)
      (hreduction z hz)

end

end TranslatedDepthSeven

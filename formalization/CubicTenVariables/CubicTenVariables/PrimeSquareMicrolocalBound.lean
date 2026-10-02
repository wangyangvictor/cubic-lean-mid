import CubicTenVariables.PrimeSquareStationaryBound
import CubicTenVariables.FixedFamilyPrimeFieldPointCount
import CubicTenVariables.MicrolocalOffDepthBound

/-! The literal stationary points lie in the same closed Gauss graph used
by the microlocal incidence. The elementary first-lift bound and the fixed
prime-field family point count therefore give the actual
prime-square estimate, uniformly in the frequency and its depth. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.PrimeSquareMicrolocalBound
open MvPolynomial HessianTheorem11
open BihomogeneousIncidenceFamily ProjectiveMicrolocalData
open PrimeSquareStationaryBound

theorem gradient_at_zero {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (K : Type*) [Field K] :
    ProjectiveMicrolocalData.gradient F K 0 = 0 := by
  funext i
  change eval₂ (Int.castRingHom K) 0 (pderiv i F) = 0
  rw [eval₂_zero_apply]
  have hz : constantCoeff (pderiv i F) = 0 :=
    hF.pderiv.coeff_eq_zero (by norm_num)
  rw [hz, map_zero]

/-- Actual stationary points give actual graph points with normal scalar
minus the stationary scalar. No algebraic-closure or density shortcut is
used, and the zero point is excluded by the nonzero gradient. -/
theorem gaussPoints_subset_closure {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (K : Type*) [Field K] [Fintype K]
    (v : Fin n → K) (hv : v ≠ 0) :
    (gaussPoints F K v : Set (Fin n → K)) ⊆ gaussFiberClosure F K v := by
  intro y hy
  obtain ⟨hFy,b,hb,he⟩ := (mem_gaussPoints F K v y).mp hy
  have hg : ProjectiveMicrolocalData.gradient F K y ≠ 0 :=
    gradient_ne_zero_of_mem F K v hv (b,y)
      ((mem_stationaryPairs F K v (b,y)).mpr ⟨hb,hFy,he⟩)
  have hy0 : y ≠ 0 := by
    intro hz
    apply hg
    rw [hz,gradient_at_zero F hF K]
  have hgraph : Sum.elim v y ∈ gaussGraph F K := by
    refine ⟨hy0,hFy,hg,-b,neg_ne_zero.mpr hb,?_⟩
    funext i
    change v i = (-b) * eval₂ (Int.castRingHom K) y (pderiv i F)
    rw [neg_mul,he i,neg_neg]
  exact mem_zeroLocus_iff.mpr (fun P hP => mem_vanishingIdeal_iff.mp hP _ hgraph)

/-- A literal subset of the displayed incidence fiber. -/
theorem gaussPoints_subset_incidence {n t : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (f : Fin t → Polynomial n n)
    (K : Type*) [Field K] [Fintype K] (h : IncidenceAndGauss F f K)
    (v : Fin n → K) (hv : v ≠ 0) :
    (gaussPoints F K v : Set (Fin n → K)) ⊆ fiber f K v :=
  (gaussPoints_subset_closure F hF K v hv).trans (h.gauss v)

/-- One constant precedes the prime, frequency and dimension threshold.
The counting argument uses the fixed prime-field family count interface;
the Gauss containment must concern this very same polynomial family. -/
theorem exists_bound (lit : FixedFamilyPrimeFieldPointCount.Uniform)
    {n t : ℕ} (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (f : Fin t → Polynomial n n) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime],
      IncidenceAndGauss F f (ZMod p) → ∀ v : Fin n → ℤ,
      (fun i => (v i : ZMod p)) ≠ 0 → ∀ j : ℕ,
      IntegralGeometricFiberDepth.geometricFiberDimension f (ZMod p)
        (fun i => (v i : ZMod p)) ≤ (j : Dimension) →
      ‖completeCubicSum F (p^2) v‖ ≤ C * (p : ℝ)^(n+1+j) := by
  classical
  obtain ⟨C,hC,hcount⟩ := FixedFamilyPrimeFieldPointCount.exists_filter_bound lit f
  refine ⟨C,by exact_mod_cast hC,?_⟩
  intro p _ hi v hv j hd
  have hc := hcount p (fun i => (v i : ZMod p)) j hd
  have hsub : gaussPoints F (ZMod p) (fun i => (v i : ZMod p)) ⊆
      Finset.univ.filter (fun y => ∀ i, value (f i) (fun a => (v a : ZMod p)) y = 0) := by
    intro y hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      gaussPoints_subset_incidence F hF f (ZMod p) hi _ hv hy⟩
  have hn : ((gaussPoints F (ZMod p) (fun i => (v i : ZMod p))).card : ℝ) ≤
      (C : ℝ)*(p : ℝ)^j := by
    have hh : (gaussPoints F (ZMod p) (fun i => (v i : ZMod p))).card ≤ C*p^j := by
      exact (Finset.card_le_card hsub).trans hc
    exact_mod_cast hh
  calc
    ‖completeCubicSum F (p^2) v‖ ≤ (p : ℝ)^(n+1) *
        ((gaussPoints F (ZMod p) (fun i => (v i : ZMod p))).card : ℝ) :=
      norm_completeCubicSum_le_gaussPoints F hF p v hv
    _ ≤ (p : ℝ)^(n+1)*((C : ℝ)*(p : ℝ)^j) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = (C : ℝ)*(p : ℝ)^(n+1+j) := by rw [pow_add]; ring

/-- For the shared ten-variable incidence, avoidance of the next depth
locus implies the actual p^(11+j) bound. Empty fibers are included. -/
theorem exists_off_depth_bound (lit : FixedFamilyPrimeFieldPointCount.Uniform)
    {t : ℕ} {F : MvPolynomial (Fin 10) ℤ} (hF : F.IsHomogeneous 3)
    {f : Fin t → Polynomial 10 10} {N B : ℕ}
    (h : TenMicrolocalIncidence.Conclusion F f N B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ N →
      ∀ v : Fin 10 → ℤ, (fun i => (v i : ZMod p)) ≠ 0 → ∀ j : ℕ,
      ¬ ((j+1 : ℕ) : Dimension) ≤
        IntegralGeometricFiberDepth.geometricFiberDimension f (ZMod p)
          (fun i => (v i : ZMod p)) →
      ‖completeCubicSum F (p^2) v‖ ≤ C * (p : ℝ)^(11+j) := by
  obtain ⟨C,hC,hbound⟩ := exists_bound lit F hF f
  refine ⟨C,hC,?_⟩
  intro p _ hp v hv j hoff
  apply hbound p (h.good_incidence p hp (ZMod p)) v hv j
  exact (ProjectiveMicrolocalNumericalDepth.geometricFiberDimension_le_depth f (ZMod p) _).trans
    (by exact_mod_cast MicrolocalOffDepthBound.depth_le_of_not_succ_le f (ZMod p) _ j hoff)

end CubicTenVariables.PrimeSquareMicrolocalBound

import CubicTenVariables.ComplementSieveTuple
import CubicTenVariables.ComplementProgressionCounts
import CubicTenVariables.StratifiedCompositeSieveAllScales

/-! The actual merged-depth tuple image satisfies the full-scale stratified
sieve on each literal complement piece. Original modulus pairs with the same
merged factors and frequency are counted once. The excluded-prime and
progression coprimality conditions remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ComplementMergedSieve
open MvPolynomial HessianTheorem11 NumericalPrimeDepth NumericalDepthAllocation
open OriginAdjoinedDepthModels ComplementSieveTuple StratifiedSieveData
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev Sample := (ℕ × ℕ) × (Fin 10 → ℤ)
variable {t N B : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
  {tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)}
  {C : ℝ} {d : ℕ} {h : CoarseBounds F C}

/-- The actual full tail of merged factors, retaining the integer frequency. -/
def mergedTuple (h : CoarseBounds F C) (i : Fin 5) (x : Sample) :
    (Fin (5-i.val) → ℕ) × (Fin 10 → ℤ) :=
  (fun k => mergedPart h x.1.1 x.1.2 x.2 (i.val+k.val+2),x.2)

/-- Literal restrictions on original modulus/frequency samples. There is
no count, congruence estimate or periodicity hypothesis in this domain. -/
structure InBlock (F : MvPolynomial (Fin 10) ℤ)
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1))
    (N : ℕ) (h : CoarseBounds F C) (i : Fin 5) (R : Fin (5-i.val) → ℝ)
    (u : Fin 10 → ℝ) (L : ℝ) (m : ℕ) (v₀ : Fin 10 → ℤ) (x : Sample) : Prop where
  squarefree_left : Squarefree x.1.1
  squarefree_right : Squarefree x.1.2
  coprime : x.1.1.Coprime x.1.2
  good_primes : (x.1.1*x.1.2^2).Coprime N
  progression_coprime : m.Coprime (x.1.1*x.1.2^2)
  piece : (fun k => (x.2 k : ℚ)) ∈ ComplementFrequencyPieces.piece F f tables i
  box : ∀ k, |(x.2 k : ℝ)-u k| ≤ L
  progression : ∀ k, (m : ℤ) ∣ x.2 k-v₀ k
  dyadic : ∀ k, R k ≤ ((mergedTuple h i x).1 k : ℝ) ∧
    ((mergedTuple h i x).1 k : ℝ) ≤ 2*R k

/-- The dimension sequence for the selected full tail is the actual
origin-adjoined depth profile 8,7,6,4,3. -/
def dimensionProfile (i : Fin 5) (k : Fin (5-i.val)) : ℕ :=
  MicrolocalDepthSupportCount.profile (tailIndex i k)

/-- One constant precedes the piece, all scales and all original samples.
The bound is on the image of the actual merged tuple map, not on arbitrary
choices of independent residue conditions. -/
theorem exists_bound
    (hP : MicrolocalRationalPartition.Conclusion F f N B tables)
    (hhom : F.IsHomogeneous 3) (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C d h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (i : Fin 5) (R : Fin (5-i.val) → ℝ), (∀ k, 1 ≤ R k) →
      ∀ (u : Fin 10 → ℝ) (L : ℝ), 1 ≤ L → ∀ (m : ℕ), 0 < m →
      ∀ (v₀ : Fin 10 → ℤ) (E : Finset Sample),
      (∀ x ∈ E, InBlock F f tables N h i R u L m v₀ x) →
      ((E.image (mergedTuple h i)).card : ℝ) ≤
        K*(L*(∏ k, R k)+‖u‖)^ε*
          StratifiedSieveData.profile (dimensionProfile i) R (L/(m : ℝ))
            (ComplementProgressionCounts.profile i : ℝ) := by
  classical
  let M := Classical.choice (OriginAdjoinedDepthModels.exists_models
    hP.geometry hhom hAn hP.incidence)
  have hbound (i : Fin 5) := StratifiedCompositeSieveAllScales.exists_bound
    (fun k : Fin (5-i.val) => (M (tailIndex i k)).count) (dimensionProfile i)
    (fun k => (M (tailIndex i k)).equations)
    (fun k => (M (tailIndex i k)).proper)
    (fun k => (M (tailIndex i k)).ideal_homogeneous)
    (fun k => (M (tailIndex i k)).dimension)
    {v | (fun k => (v k : ℚ)) ∈ ComplementFrequencyPieces.piece F f tables i}
    (ComplementProgressionCounts.profile i : ℝ) (Nat.cast_nonneg _)
    (ComplementProgressionCounts.progressionHypothesis hP i) ε hε
  choose K hK hcount using hbound
  let K₀ : ℝ := 1+∑ i, K i
  have hK0 : 1 ≤ K₀ := by
    have hs := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) =>
      zero_le_one.trans (hK i))
    dsimp [K₀]
    linarith
  have hle (i : Fin 5) : K i ≤ K₀ := by
    have hs := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 5))) =>
      zero_le_one.trans (hK j)) (Finset.mem_univ i)
    dsimp [K₀]
    linarith
  refine ⟨K₀,hK0,?_⟩
  intro i R hR u L hL m hm v₀ E hE
  have hv : ∀ p ∈ E.image (mergedTuple h i),
      ValidTuple (fun k => (M (tailIndex i k)).count)
        (fun k => (M (tailIndex i k)).equations)
        {v | (fun k => (v k : ℚ)) ∈ ComplementFrequencyPieces.piece F f tables i}
        u L m v₀ R p := by
    intro p hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    have hh := hE x hx
    exact tail_validTuple hc M i x.1.1 x.1.2 hh.squarefree_left hh.squarefree_right
      hh.coprime hh.good_primes m hh.progression_coprime u L v₀ x.2 R
      hh.piece hh.box hh.progression hh.dyadic
  have hfirst := hcount i R hR u L hL m hm v₀ (E.image (mergedTuple h i)) hv
  apply hfirst.trans
  have hp0 := StratifiedSieveProfileRestriction.profile_nonneg (dimensionProfile i) R
    (fun k => zero_le_one.trans (hR k)) (L/(m : ℝ))
    (ComplementProgressionCounts.profile i : ℝ) (by positivity)
  apply mul_le_mul_of_nonneg_right _ hp0
  have hprod : 0 ≤ ∏ k, R k := Finset.prod_nonneg
    (fun k _ => zero_le_one.trans (hR k))
  exact mul_le_mul_of_nonneg_right (hle i) (Real.rpow_nonneg
    (add_nonneg (mul_nonneg (zero_le_one.trans hL) hprod) (norm_nonneg u)) _)

end CubicTenVariables.ComplementMergedSieve

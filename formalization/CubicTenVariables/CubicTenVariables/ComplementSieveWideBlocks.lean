import CubicTenVariables.ComplementSieveProfileMono

/-! The actual merged-depth sieve on wide dyadic blocks [R,4R]. Each
coordinate is covered by [R,2R] and [2R,4R], and at most 32 ordinary
blocks suffice. The original profile and base-scale height are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.ComplementSieveWideBlocks
open MvPolynomial HessianTheorem11 NumericalPrimeDepth ComplementMergedSieve
open StratifiedSieveData
open scoped BigOperators
variable {t N B : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
  {tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)}
  {C : ℝ} {d : ℕ} {h : CoarseBounds F C}

/-- Every original domain condition is kept; only the dyadic upper
endpoint changes from 2R to 4R. -/
structure InWideBlock (F : MvPolynomial (Fin 10) ℤ)
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
    ((mergedTuple h i x).1 k : ℝ) ≤ 4*R k

/-- A binary choice of the lower or upper ordinary dyadic block. -/
def scale {s : ℕ} (R : Fin s → ℝ) (β : Fin s → Bool) (k : Fin s) : ℝ :=
  if β k then 2*R k else R k

private theorem scale_bounds {s : ℕ} (R : Fin s → ℝ) (hR : ∀ k, 1 ≤ R k)
    (β : Fin s → Bool) (k : Fin s) :
    R k ≤ scale R β k ∧ scale R β k ≤ 2*R k := by
  unfold scale
  cases β k <;> simp only [Bool.false_eq_true,if_false,if_true] <;> constructor <;> linarith [hR k]

private theorem exists_choice {s : ℕ} (R : Fin s → ℝ) (q : Fin s → ℕ)
    (hq : ∀ k, R k ≤ (q k : ℝ) ∧ (q k : ℝ) ≤ 4*R k) :
    ∃ β : Fin s → Bool, ∀ k, scale R β k ≤ (q k : ℝ) ∧ (q k : ℝ) ≤ 2*scale R β k := by
  classical
  refine ⟨fun k => decide (2*R k < (q k : ℝ)),?_⟩
  intro k
  by_cases hk : 2*R k < (q k : ℝ)
  · simp only [scale,hk,decide_true,if_true]
    constructor <;> linarith [(hq k).2]
  · simp only [scale,hk,decide_false,Bool.false_eq_true,if_false]
    exact ⟨(hq k).1,le_of_not_gt hk⟩

private theorem height_le (i : Fin 5) (R : Fin (5-i.val) → ℝ) (hR : ∀ k, 1 ≤ R k)
    (β : Fin (5-i.val) → Bool) (u : Fin 10 → ℝ) (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε) :
    (L*(∏ k, scale R β k)+‖u‖)^ε ≤ (32 : ℝ)^ε*(L*(∏ k, R k)+‖u‖)^ε := by
  have hR0 (k) : 0 ≤ R k := zero_le_one.trans (hR k)
  have hS0 (k) : 0 ≤ scale R β k := (hR0 k).trans (scale_bounds R hR β k).1
  have hp0 : 0 ≤ ∏ k, R k := Finset.prod_nonneg (fun k _ => hR0 k)
  have hs0 : 0 ≤ ∏ k, scale R β k := Finset.prod_nonneg (fun k _ => hS0 k)
  have hpow : (2 : ℝ)^(5-i.val) ≤ 32 := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le 5 i.val)
    norm_num at hh ⊢
    exact hh
  have hp : (∏ k, scale R β k) ≤ 32*(∏ k, R k) := by
    calc
      _ ≤ ∏ k, 2*R k := Finset.prod_le_prod (fun k _ => hS0 k)
        (fun k _ => (scale_bounds R hR β k).2)
      _ = (2 : ℝ)^(5-i.val)*(∏ k, R k) := by rw [Finset.prod_mul_distrib]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hpow hp0
  have hbase : L*(∏ k, scale R β k)+‖u‖ ≤ 32*(L*(∏ k, R k)+‖u‖) := by
    have hh := mul_le_mul_of_nonneg_left hp hL
    nlinarith [norm_nonneg u]
  calc
    _ ≤ (32*(L*(∏ k, R k)+‖u‖))^ε := Real.rpow_le_rpow (by positivity) hbase hε
    _ = _ := Real.mul_rpow (by norm_num) (by positivity)

/-- The wide-block count has no supplied counting or sieve premise.
One constant precedes the piece, base scales, box, progression, and original
samples, and the image retains the actual integer-frequency merged tuple. -/
theorem exists_bound
    (hP : MicrolocalRationalPartition.Conclusion F f N B tables)
    (hhom : F.IsHomogeneous 3) (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C d h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (i : Fin 5) (R : Fin (5-i.val) → ℝ), (∀ k, 1 ≤ R k) →
      ∀ (u : Fin 10 → ℝ) (L : ℝ), 1 ≤ L → ∀ (m : ℕ), 0 < m →
      ∀ (v₀ : Fin 10 → ℤ) (E : Finset Sample),
      (∀ x ∈ E, InWideBlock F f tables N h i R u L m v₀ x) →
      ((E.image (mergedTuple h i)).card : ℝ) ≤
        K*(L*(∏ k, R k)+‖u‖)^ε*
          profile (dimensionProfile i) R (1+L/(m : ℝ))
            (ComplementProgressionCounts.profile i : ℝ) := by
  classical
  obtain ⟨K₀,hK₀,hcount⟩ := ComplementMergedSieve.exists_bound hP hhom hAn hc ε hε
  let K : ℝ := 32*K₀*(32 : ℝ)^ε
  have hK : 1 ≤ K := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by norm_num) hK₀) (Real.one_le_rpow (by norm_num) hε.le)
  refine ⟨K,hK,?_⟩
  intro i R hR u L hL m hm v₀ E hE
  let Eβ (β : Fin (5-i.val) → Bool) : Finset Sample := E.filter (fun x =>
    ∀ k, scale R β k ≤ ((mergedTuple h i x).1 k : ℝ) ∧
      ((mergedTuple h i x).1 k : ℝ) ≤ 2*scale R β k)
  let P : ℝ := profile (dimensionProfile i) R (1+L/(m : ℝ))
    (ComplementProgressionCounts.profile i : ℝ)
  let H : ℝ := (L*(∏ k, R k)+‖u‖)^ε
  have hT : 0 ≤ L/(m : ℝ) := by positivity
  have hP0 : 0 ≤ P := StratifiedSieveProfileRestriction.profile_nonneg _ _
    (fun k => zero_le_one.trans (hR k)) _ _ (by positivity)
  have hprod0 : 0 ≤ ∏ k, R k := Finset.prod_nonneg (fun k _ => zero_le_one.trans (hR k))
  have hH0 : 0 ≤ H := Real.rpow_nonneg (by positivity) _
  have hb (β : Fin (5-i.val) → Bool) :
      (((Eβ β).image (mergedTuple h i)).card : ℝ) ≤ K₀*(32 : ℝ)^ε*H*P := by
    have hR' (k) : 1 ≤ scale R β k := (hR k).trans (scale_bounds R hR β k).1
    have hv : ∀ x ∈ Eβ β, InBlock F f tables N h i (scale R β) u L m v₀ x := by
      intro x hx
      obtain ⟨hx,hdy⟩ := Finset.mem_filter.mp hx
      have hh := hE x hx
      exact ⟨hh.squarefree_left,hh.squarefree_right,hh.coprime,hh.good_primes,
        hh.progression_coprime,hh.piece,hh.box,hh.progression,hdy⟩
    have hh := hcount i (scale R β) hR' u L hL m hm v₀ (Eβ β) hv
    have hheight := height_le i R hR β u L ε (zero_le_one.trans hL) hε.le
    have hprofile := ComplementSieveProfileMono.complement_profile_le i R (scale R β)
      hR (fun k => (scale_bounds R hR β k).1) (L/(m : ℝ)) hT
    have hp0 := StratifiedSieveProfileRestriction.profile_nonneg (dimensionProfile i) (scale R β)
      (fun k => zero_le_one.trans (hR' k)) (L/(m : ℝ))
      (ComplementProgressionCounts.profile i : ℝ) hT
    calc
      _ ≤ _ := hh
      _ ≤ K₀*((32 : ℝ)^ε*H)*P := mul_le_mul
        (mul_le_mul_of_nonneg_left hheight (zero_le_one.trans hK₀)) hprofile hp0 (by positivity)
      _ = _ := by ring
  have hcover : E.image (mergedTuple h i) ⊆
      Finset.univ.biUnion (fun β : Fin (5-i.val) → Bool => (Eβ β).image (mergedTuple h i)) := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨β,hβ⟩ := exists_choice R (mergedTuple h i x).1 (hE x hx).dyadic
    exact Finset.mem_biUnion.mpr ⟨β,Finset.mem_univ _,Finset.mem_image_of_mem _
      (Finset.mem_filter.mpr ⟨hx,hβ⟩)⟩
  have hcard : ((E.image (mergedTuple h i)).card : ℝ) ≤
      ∑ β : Fin (5-i.val) → Bool, (((Eβ β).image (mergedTuple h i)).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hchoices : (Fintype.card (Fin (5-i.val) → Bool) : ℝ) ≤ 32 := by
    have hh : Fintype.card (Fin (5-i.val) → Bool) ≤ 32 := by
      simpa only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] using
        (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (Nat.sub_le 5 i.val))
    exact_mod_cast hh
  calc
    _ ≤ ∑ β : Fin (5-i.val) → Bool, (((Eβ β).image (mergedTuple h i)).card : ℝ) := hcard
    _ ≤ ∑ _β : Fin (5-i.val) → Bool, K₀*(32 : ℝ)^ε*H*P := Finset.sum_le_sum (fun β _ => hb β)
    _ = (Fintype.card (Fin (5-i.val) → Bool) : ℝ)*(K₀*(32 : ℝ)^ε*H*P) := by simp
    _ ≤ 32*(K₀*(32 : ℝ)^ε*H*P) := mul_le_mul_of_nonneg_right hchoices (by positivity)
    _ = _ := by dsimp [K,H,P]; ring

end CubicTenVariables.ComplementSieveWideBlocks

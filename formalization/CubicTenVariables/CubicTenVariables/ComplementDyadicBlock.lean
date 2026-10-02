import CubicTenVariables.ComplementAllocationWeightedBlock
import CubicTenVariables.ComplementAllocationFibers
import CubicTenVariables.ComplementSieveWideBlocks
import CubicTenVariables.ComplementSieveProfileBridge
import CubicTenVariables.ConductorPositiveMeanNumerics

/-! The actual sum of complete cubic sums in a dyadic high-depth block.
The hypotheses below describe original modulus/frequency samples only.
All allocation, multiplicity and sieve estimates are proved internally. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.ComplementDyadicBlock
open MvPolynomial HessianTheorem11 NumericalPrimeDepth NumericalDepthAllocation
open ComplementAllocationSamples ComplementDeepWeights
open scoped BigOperators

variable {t N Betti : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
  {tables : ∀ k : Fin 4, MicrolocalPromotionTable.Table F f (k.val+1)}
  {C : ℝ} {d : ℕ} {h : CoarseBounds F C}

structure InBlock (F : MvPolynomial (Fin 10) ℤ)
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (tables : ∀ k : Fin 4, MicrolocalPromotionTable.Table F f (k.val+1))
    (N : ℕ) (h : CoarseBounds F C) (i : Fin 5) (D : ℝ) (A B : ℕ → ℝ)
    (u : Fin 10 → ℝ) (L : ℝ) (m : ℕ) (v₀ : Fin 10 → ℤ) (x : Sample) : Prop where
  squarefree_left : Squarefree x.1.1
  squarefree_right : Squarefree x.1.2
  coprime : x.1.1.Coprime x.1.2
  size : (x.1.1 : ℝ)*(x.1.2 : ℝ)^2 ≤ 2*D
  good_primes : (x.1.1*x.1.2^2).Coprime N
  progression_coprime : m.Coprime (x.1.1*x.1.2^2)
  piece : (fun k => (x.2 k : ℚ)) ∈ ComplementFrequencyPieces.piece F f tables i
  box : ∀ k, |(x.2 k : ℝ)-u k| ≤ L
  progression : ∀ k, (m : ℤ) ∣ x.2 k-v₀ k
  prime_dyadic : ∀ j ∈ Finset.Icc (i.val+2) 6,
    A j ≤ (primePart h x.1.1 x.2 j : ℝ) ∧ (primePart h x.1.1 x.2 j : ℝ) ≤ 2*A j
  square_dyadic : ∀ j ∈ Finset.Icc (i.val+2) 6,
    B j ≤ (squarePart h x.1.2 x.2 j : ℝ) ∧ (squarePart h x.1.2 x.2 j : ℝ) ≤ 2*B j
  open_cutoff : i.val=0 → 1+L/(m : ℝ) < (NumericalConductorRadical.R22 h x.1.1 x.1.2 x.2 : ℝ)

private theorem loss_le (D H Ξ ε : ℝ) (hD : 1 ≤ D) (hH : 1 ≤ H)
    (hΞ : 0 ≤ Ξ) (hsize : Ξ ≤ 2*(D*H)) (hε : 0 < ε) :
    (D*H)^(ε/3)*D^(ε/3)*Ξ^(ε/3) ≤ (2 : ℝ)^(ε/3)*(D*H)^ε := by
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hDH : 0 < D*H := mul_pos hD0 hH0
  have hd : D ≤ D*H := by nlinarith
  calc
    _ ≤ (D*H)^(ε/3)*(D*H)^(ε/3)*(2*(D*H))^(ε/3) := by
      gcongr
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hDH.le]
      calc
        _ = (2 : ℝ)^(ε/3)*(((D*H)^(ε/3)*(D*H)^(ε/3))*(D*H)^(ε/3)) := by ring
        _ = _ := by rw [← Real.rpow_add hDH,← Real.rpow_add hDH]; congr 2; ring

/-- A full arithmetic dyadic-block bound, with the original finite sum
on the left. The constant precedes every modulus and spatial parameter. -/
theorem exists_bound
    (hP : MicrolocalRationalPartition.Conclusion F f N Betti tables)
    (hhom : F.IsHomogeneous 3) (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C d h)
    (i : Fin 5) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ D : ℝ, 1 ≤ D → ∀ A B : ℕ → ℝ,
      (∀ j ∈ Finset.Icc (i.val+2) 6, 1 ≤ A j) →
      (∀ j ∈ Finset.Icc (i.val+2) 6, 1 ≤ B j) →
      ∀ (u : Fin 10 → ℝ) (L : ℝ), 1 ≤ L → ∀ m : ℕ, 0 < m →
      ∀ (v₀ : Fin 10 → ℤ) (E : Finset Sample),
      (∀ x ∈ E, InBlock F f tables N h i D A B u L m v₀ x) →
      (∑ x ∈ E, ‖completeCubicSum F (x.1.1*x.1.2^2) x.2‖) ≤
        M*(D*(2+‖u‖+L+(m : ℝ)))^ε*D^((59 : ℝ)/6)*
          ((1+L/(m : ℝ))/D^((1 : ℝ)/3)+((1+L/(m : ℝ))/D^((1 : ℝ)/3))^9) := by
  classical
  have he : 0 < ε/3 := by linarith
  obtain ⟨M₀,hM₀,hweight⟩ := ComplementAllocationWeightedBlock.exists_bound hhom hc i (ε/3) he
  obtain ⟨Kₐ,hKₐ,halloc⟩ := ComplementAllocationFibers.exists_bound h i (ε/3) he
  obtain ⟨Kₛ,hKₛ,hsieve⟩ := ComplementSieveWideBlocks.exists_bound hP hhom hAn hc (ε/3) he
  let M : ℝ := max 1 (M₀*Kₐ*Kₛ*(2 : ℝ)^(ε/3)*6192)
  refine ⟨M,le_max_left _ _,?_⟩
  intro D hD A B hA hB u L hL m hm v₀ E hE
  let H : ℝ := 2+‖u‖+L+(m : ℝ)
  let T : ℝ := 1+L/(m : ℝ)
  let R : Fin (5-i.val) → ℝ := fun k =>
    A (ComplementSieveProfileBridge.depth i k)*B (ComplementSieveProfileBridge.depth i k)
  let Ξ : ℝ := L*(∏ k, R k)+‖u‖
  have hH : 1 ≤ H := by dsimp [H]; have := norm_nonneg u; have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
  have hT : 1 ≤ T := by
    dsimp [T]
    exact le_add_of_nonneg_right (by positivity)
  have hR (k) : 1 ≤ R k := one_le_mul_of_one_le_of_one_le
    (hA _ (ComplementSieveProfileBridge.depth_mem i k))
    (hB _ (ComplementSieveProfileBridge.depth_mem i k))
  have hprod : 0 ≤ ∏ k, R k := Finset.prod_nonneg fun k _ => zero_le_one.trans (hR k)
  have hΞ : 0 ≤ Ξ := by dsimp [Ξ]; positivity
  have hW : 0 ≤ weight (i.val+2) A B := Finset.prod_nonneg fun j hj =>
    mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (hA j hj)) _)
      (Real.rpow_nonneg (zero_le_one.trans (hB j hj)) _)
  by_cases hne : E.Nonempty
  · obtain ⟨x₀,hx₀⟩ := hne
    have hx := hE x₀ hx₀
    have hmod : modulus (i.val+2) A B ≤ 2*D := by
      have hscale := ComplementDyadicWeight.modulus_le (i.val+2)
        (primePart h x₀.1.1 x₀.2) (squarePart h x₀.1.2 x₀.2) A B
        (fun j hj => zero_le_one.trans (hA j hj)) (fun j hj => zero_le_one.trans (hB j hj))
        (fun j hj => (hx.prime_dyadic j hj).1) (fun j hj => (hx.square_dyadic j hj).1)
      have hd : ((deepModulus h x₀.1.1 x₀.1.2 x₀.2 (i.val+2) : ℕ) : ℝ) ≤
          (x₀.1.1 : ℝ)*(x₀.1.2 : ℝ)^2 := by
        exact_mod_cast deepModulus_le h x₀.1.1 x₀.1.2
          (Nat.pos_of_ne_zero hx.squarefree_left.ne_zero) (Nat.pos_of_ne_zero hx.squarefree_right.ne_zero)
          x₀.2 (i.val+2)
      exact hscale.trans (hd.trans hx.size)
    have hPQ : (∏ k, R k) ≤ modulus (i.val+2) A B := by
      rw [show (∏ k, R k) = ∏ j ∈ Finset.Icc (i.val+2) 6, A j*B j from
        ComplementSieveProfileBridge.merged_product_eq i A B]
      apply Finset.prod_le_prod (fun j hj => mul_nonneg
        (zero_le_one.trans (hA j hj)) (zero_le_one.trans (hB j hj)))
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (hA j hj))
      nlinarith [hB j hj]
    have hheight : Ξ ≤ 2*(D*H) := by
      have hh := mul_le_mul_of_nonneg_left (hPQ.trans hmod) (zero_le_one.trans hL)
      have hu := norm_nonneg u
      have hm0 := (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
      dsimp [Ξ,H]
      nlinarith
    have hcut : i.val+2=2 → T ≤ 4^5*(∏ j ∈ Finset.Icc 2 6, A j*B j) := by
      intro hi
      have hi0 : i.val=0 := by omega
      have hr := hx.open_cutoff hi0
      rw [R22_eq_product] at hr
      have hrad : T < ∏ j ∈ Finset.Icc 2 6,
          (primePart h x₀.1.1 x₀.2 j : ℝ)*(squarePart h x₀.1.2 x₀.2 j : ℝ) := by
        simpa only [Nat.cast_prod,Nat.cast_mul,mergedPart] using hr
      exact dyadic_cutoff (primePart h x₀.1.1 x₀.2) (squarePart h x₀.1.2 x₀.2) A B T
        (fun j hj => (hx.prime_dyadic j (by simpa only [hi] using hj)).2)
        (fun j hj => (hx.square_dyadic j (by simpa only [hi] using hj)).2) hrad
    have hw := hweight D H hD hH A B hA hB E (fun x hx => by
      have hh := hE x hx
      refine ⟨hh.squarefree_left,hh.squarefree_right,hh.coprime,hh.size,hh.piece,?_,
        (fun j hj => (hh.prime_dyadic j hj).2),(fun j hj => (hh.square_dyadic j hj).2)⟩
      intro k
      have hhgt := ConductorPositiveMeanNumerics.height_le u L (zero_le_one.trans hL) m x.2 hh.box
      have hn := norm_le_pi_norm (fun k => (x.2 k : ℝ)) k
      simp only [Real.norm_eq_abs] at hn
      dsimp [ConductorFixedFrequency.frequencyHeight] at hhgt
      dsimp [H]
      linarith)
    have ha := halloc D hD E (fun x hx =>
      ⟨(hE x hx).squarefree_left,(hE x hx).squarefree_right,(hE x hx).coprime,(hE x hx).size⟩)
    have hs := hsieve i R hR u L hL m hm v₀ E (fun x hx => by
      have hh := hE x hx
      refine ⟨hh.squarefree_left,hh.squarefree_right,hh.coprime,hh.good_primes,
        hh.progression_coprime,hh.piece,hh.box,hh.progression,?_⟩
      intro k
      let j := ComplementSieveProfileBridge.depth i k
      have hj := ComplementSieveProfileBridge.depth_mem i k
      have ha := hh.prime_dyadic j hj
      have hb := hh.square_dyadic j hj
      change A j*B j ≤ ((primePart h x.1.1 x.2 j*squarePart h x.1.2 x.2 j : ℕ) : ℝ) ∧
        ((primePart h x.1.1 x.2 j*squarePart h x.1.2 x.2 j : ℕ) : ℝ) ≤ 4*(A j*B j)
      rw [Nat.cast_mul]
      constructor
      · exact mul_le_mul ha.1 hb.1 (zero_le_one.trans (hB j hj)) (Nat.cast_nonneg _)
      · have ht := mul_le_mul ha.2 hb.2 (Nat.cast_nonneg _) (by linarith [hA j hj])
        nlinarith)
    have hpEq := ComplementSieveProfileBridge.profile_eq i A B T hA hB
    change _ ≤ Kₛ*Ξ^(ε/3)*StratifiedSieveData.profile _ R T _ at hs
    rw [hpEq] at hs
    have hp0 : 0 ≤ ComplementDeepProfile.profile (i.val+2) A B T := by
      rw [← hpEq]
      exact StratifiedSieveProfileRestriction.profile_nonneg _ R
        (fun k => zero_le_one.trans (hR k)) T _ (zero_le_one.trans hT)
    have hnum := ComplementDeepProfile.weighted_profile_final_le (i.val+2) (by omega)
      (by omega) A B D T hD hT hA hB hmod hcut
    have hexp : (11+((i.val+2 : ℕ) : ℝ))/2 = (13+(i.val : ℝ))/2 := by push_cast; ring
    rw [hexp] at hnum
    have hloss := loss_le D H Ξ ε hD hH hΞ hheight hε
    have hM0 := zero_le_one.trans hM₀
    have hKa0 := zero_le_one.trans hKₐ
    have hKs0 := zero_le_one.trans hKₛ
    have hD0 : 0 < D := zero_lt_one.trans_le hD
    have hH0 : 0 < H := zero_lt_one.trans_le hH
    calc
      _ ≤ M₀*(D*H)^(ε/3)*D^((13+(i.val : ℝ))/2)*weight (i.val+2) A B*
          (Kₐ*D^(ε/3)*(Kₛ*Ξ^(ε/3)*ComplementDeepProfile.profile (i.val+2) A B T)) := by
        apply hw.trans
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact ha.trans (mul_le_mul_of_nonneg_left hs (by positivity))
      _ = (M₀*Kₐ*Kₛ)*((D*H)^(ε/3)*D^(ε/3)*Ξ^(ε/3))*
          (D^((13+(i.val : ℝ))/2)*weight (i.val+2) A B*ComplementDeepProfile.profile (i.val+2) A B T) := by ring
      _ ≤ (M₀*Kₐ*Kₛ)*((2 : ℝ)^(ε/3)*(D*H)^ε)*
          (6192*D^((59 : ℝ)/6)*(T/D^((1 : ℝ)/3)+(T/D^((1 : ℝ)/3))^9)) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hloss (by positivity)) hnum (by positivity) (by positivity)
      _ = (M₀*Kₐ*Kₛ*(2 : ℝ)^(ε/3)*6192)*(D*H)^ε*D^((59 : ℝ)/6)*
          (T/D^((1 : ℝ)/3)+(T/D^((1 : ℝ)/3))^9) := by ring
      _ ≤ _ := by
        change _ ≤ M*(D*H)^ε*D^((59 : ℝ)/6)*(T/D^((1 : ℝ)/3)+(T/D^((1 : ℝ)/3))^9)
        gcongr
        exact le_max_right _ _
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty]
    have hM : 0 ≤ M := zero_le_one.trans (le_max_left _ _)
    have hD0 : 0 < D := zero_lt_one.trans_le hD
    have hH0 : 0 < H := zero_lt_one.trans_le hH
    have hT0 : 0 < T := zero_lt_one.trans_le hT
    change 0 ≤ M*(D*H)^ε*D^((59 : ℝ)/6)*(T/D^((1 : ℝ)/3)+(T/D^((1 : ℝ)/3))^9)
    positivity

end CubicTenVariables.ComplementDyadicBlock

import CubicTenVariables.ComplementDyadicBlock
import CubicTenVariables.ComplementDyadicScales

/-! Summation over every actual dyadic allocation block on one literal
complement piece. No restriction on high-depth sizes is supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.ComplementPieceAverage
open MvPolynomial HessianTheorem11 NumericalPrimeDepth NumericalDepthAllocation
open ComplementAllocationSamples
open scoped BigOperators

variable {t N Betti : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
  {tables : ∀ k : Fin 4, MicrolocalPromotionTable.Table F f (k.val+1)}
  {C : ℝ} {d : ℕ} {h : CoarseBounds F C}

structure InPiece (F : MvPolynomial (Fin 10) ℤ)
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (tables : ∀ k : Fin 4, MicrolocalPromotionTable.Table F f (k.val+1))
    (N : ℕ) (h : CoarseBounds F C) (i : Fin 5) (D : ℝ)
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
  open_cutoff : i.val=0 → 1+L/(m : ℝ) < (NumericalConductorRadical.R22 h x.1.1 x.1.2 x.2 : ℝ)

private def slot (i : Fin 5) (j : ℕ) (hj : j ∈ Finset.Icc (i.val+2) 6) : Fin (5-i.val) :=
  ⟨j-(i.val+2),by have hi := i.isLt; have hji := Finset.mem_Icc.mp hj; omega⟩

private theorem depth_slot (i : Fin 5) (j : ℕ) (hj : j ∈ Finset.Icc (i.val+2) 6) :
    i.val+(slot i j hj).val+2=j := by
  dsimp [slot]
  have hji := Finset.mem_Icc.mp hj
  omega

/-- Extend a finite array of dyadic indices by unit scales off its tail. -/
def scales (i : Fin 5) (a : Fin (5-i.val) → ℕ) (j : ℕ) : ℝ :=
  if hj : j ∈ Finset.Icc (i.val+2) 6 then (2 : ℝ)^(a (slot i j hj)) else 1

theorem one_le_scales (i : Fin 5) (a : Fin (5-i.val) → ℕ) (j : ℕ) : 1 ≤ scales i a j := by
  unfold scales
  split_ifs
  · exact one_le_pow₀ (by norm_num)
  · exact le_rfl

/-- The canonical two dyadic indices at every actual high-depth factor. -/
def tag (h : CoarseBounds F C) (i : Fin 5) (x : Sample) :
    (Fin (5-i.val) → ℕ) × (Fin (5-i.val) → ℕ) :=
  (fun k => Nat.log 2 (primePart h x.1.1 x.2 (i.val+k.val+2)),
    fun k => Nat.log 2 (squarePart h x.1.2 x.2 (i.val+k.val+2)))

theorem tag_mem (h : CoarseBounds F C) (i : Fin 5) (D : ℝ) (x : Sample)
    (ha : Squarefree x.1.1) (hb : Squarefree x.1.2)
    (hsize : (x.1.1 : ℝ)*(x.1.2 : ℝ)^2 ≤ 2*D) :
    tag h i x ∈ ComplementDyadicScales.pairArrays D i := by
  have ha0 := Nat.pos_of_ne_zero ha.ne_zero
  have hb0 := Nat.pos_of_ne_zero hb.ne_zero
  apply ComplementDyadicScales.canonical_pair_mem
  · intro k
    have hp := Nat.le_of_dvd ha0 (parts_dvd h x.1.1 x.1.2 x.2 (i.val+k.val+2)).1
    have hm : x.1.1 ≤ x.1.1*x.1.2^2 := Nat.le_mul_of_pos_right _ (by positivity)
    have hr : (primePart h x.1.1 x.2 (i.val+k.val+2) : ℝ) ≤
        (x.1.1 : ℝ)*(x.1.2 : ℝ)^2 := by exact_mod_cast hp.trans hm
    exact hr.trans hsize
  · intro k
    have hp := Nat.le_of_dvd hb0 (parts_dvd h x.1.1 x.1.2 x.2 (i.val+k.val+2)).2
    have hm : x.1.2 ≤ x.1.1*x.1.2^2 :=
      (by nlinarith : x.1.2 ≤ x.1.2^2).trans (Nat.le_mul_of_pos_left _ ha0)
    have hr : (squarePart h x.1.2 x.2 (i.val+k.val+2) : ℝ) ≤
        (x.1.1 : ℝ)*(x.1.2 : ℝ)^2 := by exact_mod_cast hp.trans hm
    exact hr.trans hsize

theorem tag_dyadic (h : CoarseBounds F C) (i : Fin 5) (x : Sample)
    (j : ℕ) (hj : j ∈ Finset.Icc (i.val+2) 6) :
    (scales i (tag h i x).1 j ≤ (primePart h x.1.1 x.2 j : ℝ) ∧
      (primePart h x.1.1 x.2 j : ℝ) ≤ 2*scales i (tag h i x).1 j) ∧
    (scales i (tag h i x).2 j ≤ (squarePart h x.1.2 x.2 j : ℝ) ∧
      (squarePart h x.1.2 x.2 j : ℝ) ≤ 2*scales i (tag h i x).2 j) := by
  simp only [scales,dif_pos hj,tag,depth_slot]
  have ha := ComplementDyadicScales.canonical_scale_bounds _ (parts_pos h x.1.1 x.1.2 x.2 j).1
  have hb := ComplementDyadicScales.canonical_scale_bounds _ (parts_pos h x.1.1 x.1.2 x.2 j).2
  exact ⟨⟨ha.2.1,ha.2.2.le⟩,⟨hb.2.1,hb.2.2.le⟩⟩

/-- The complete mean on one complementary piece, summed over every
original pair and frequency in an arbitrary finite family. -/
theorem exists_bound
    (hP : MicrolocalRationalPartition.Conclusion F f N Betti tables)
    (hhom : F.IsHomogeneous 3) (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C d h)
    (i : Fin 5) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ D : ℝ, 1 ≤ D →
      ∀ (u : Fin 10 → ℝ) (L : ℝ), 1 ≤ L → ∀ m : ℕ, 0 < m →
      ∀ (v₀ : Fin 10 → ℤ) (E : Finset Sample),
      (∀ x ∈ E, InPiece F f tables N h i D u L m v₀ x) →
      (∑ x ∈ E, ‖completeCubicSum F (x.1.1*x.1.2^2) x.2‖) ≤
        M*(D*(2+‖u‖+L+(m : ℝ)))^ε*D^((59 : ℝ)/6)*
          ((1+L/(m : ℝ))/D^((1 : ℝ)/3)+((1+L/(m : ℝ))/D^((1 : ℝ)/3))^9) := by
  classical
  obtain ⟨M₀,hM₀,hblock⟩ := ComplementDyadicBlock.exists_bound hP hhom hAn hc i (ε/2) (by linarith)
  obtain ⟨K,hK,hcard⟩ := ComplementDyadicScales.exists_pair_count_bound (ε/2) (by linarith)
  refine ⟨M₀*K,one_le_mul_of_one_le_of_one_le hM₀ hK,?_⟩
  intro D hD u L hL m hm v₀ E hE
  let H : ℝ := 2+‖u‖+L+(m : ℝ)
  let T : ℝ := 1+L/(m : ℝ)
  let P : ℝ := D^((59 : ℝ)/6)*(T/D^((1 : ℝ)/3)+(T/D^((1 : ℝ)/3))^9)
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hH : 1 ≤ H := by dsimp [H]; have := norm_nonneg u; have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hT0 : 0 < T := by dsimp [T]; positivity
  have hP0 : 0 ≤ P := by dsimp [P]; positivity
  have hM0 := zero_le_one.trans hM₀
  have hK0 := zero_le_one.trans hK
  let tags := ComplementDyadicScales.pairArrays D i
  let fiber (z : (Fin (5-i.val) → ℕ) × (Fin (5-i.val) → ℕ)) := E.filter (fun x => tag h i x=z)
  have hmaps : (↑E : Set Sample).MapsTo (tag h i) tags := fun x hx =>
    tag_mem h i D x (hE x hx).squarefree_left (hE x hx).squarefree_right (hE x hx).size
  have hfiber (z) (_hz : z ∈ tags) :
      (∑ x ∈ fiber z, ‖completeCubicSum F (x.1.1*x.1.2^2) x.2‖) ≤ M₀*(D*H)^(ε/2)*P := by
    have hb := hblock D hD (scales i z.1) (scales i z.2)
      (fun j _ => one_le_scales i z.1 j) (fun j _ => one_le_scales i z.2 j)
      u L hL m hm v₀ (fiber z) (fun x hx => by
        obtain ⟨hx,htag⟩ := Finset.mem_filter.mp hx
        have hh := hE x hx
        refine ⟨hh.squarefree_left,hh.squarefree_right,hh.coprime,hh.size,hh.good_primes,
          hh.progression_coprime,hh.piece,hh.box,hh.progression,?_,?_,hh.open_cutoff⟩
        · intro j hj
          simpa only [htag] using (tag_dyadic h i x j hj).1
        · intro j hj
          simpa only [htag] using (tag_dyadic h i x j hj).2)
    convert hb using 1 <;> dsimp [P,H,T] <;> ring
  have hloss : D^(ε/2)*(D*H)^(ε/2) ≤ (D*H)^ε := by
    calc
      _ ≤ (D*H)^(ε/2)*(D*H)^(ε/2) := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hD0.le (by nlinarith) (by linarith)) (by positivity)
      _ = _ := by rw [← Real.rpow_add (mul_pos hD0 hH0)]; congr 1; ring
  calc
    _ = ∑ z ∈ tags, ∑ x ∈ fiber z, ‖completeCubicSum F (x.1.1*x.1.2^2) x.2‖ :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ _z ∈ tags, M₀*(D*H)^(ε/2)*P := Finset.sum_le_sum hfiber
    _ = (tags.card : ℝ)*(M₀*(D*H)^(ε/2)*P) := by simp
    _ ≤ (K*D^(ε/2))*(M₀*(D*H)^(ε/2)*P) :=
      mul_le_mul_of_nonneg_right (hcard D hD i) (by positivity)
    _ = (M₀*K)*(D^(ε/2)*(D*H)^(ε/2))*P := by ring
    _ ≤ (M₀*K)*(D*H)^ε*P := by gcongr
    _ = _ := by dsimp [P,H,T]; ring

end CubicTenVariables.ComplementPieceAverage

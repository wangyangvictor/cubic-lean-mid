import CubicTenVariables.ComplementAllocationSamples
import CubicTenVariables.ComplementDyadicWeight

/-! Summing actual complete sums in a fixed dyadic high-allocation block.
The fibers are indexed by their exact high factors and original frequency;
all low modulus factors are summed using the proved allocation estimate. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ComplementAllocationWeightedBlock
open MvPolynomial NumericalPrimeDepth NumericalDepthAllocation ComplementAllocationSamples
open scoped BigOperators

variable {t N : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
  {tables : ∀ k : Fin 4, MicrolocalPromotionTable.Table F f (k.val+1)}
  {C : ℝ} {d : ℕ} {h : CoarseBounds F C}

/-- Only pointwise domain restrictions: the sum estimate is a conclusion. -/
structure InBlock (F : MvPolynomial (Fin 10) ℤ)
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (tables : ∀ k : Fin 4, MicrolocalPromotionTable.Table F f (k.val+1))
    (h : CoarseBounds F C) (i : Fin 5) (D H : ℝ) (A B : ℕ → ℝ) (x : Sample) : Prop where
  squarefree_left : Squarefree x.1.1
  squarefree_right : Squarefree x.1.2
  coprime : x.1.1.Coprime x.1.2
  size : (x.1.1 : ℝ)*(x.1.2 : ℝ)^2 ≤ 2*D
  piece : (fun k => (x.2 k : ℚ)) ∈ ComplementFrequencyPieces.piece F f tables i
  height : ∀ k, |(x.2 k : ℝ)| ≤ H
  prime_upper : ∀ j ∈ Finset.Icc (i.val+2) 6, (primePart h x.1.1 x.2 j : ℝ) ≤ 2*A j
  square_upper : ∀ j ∈ Finset.Icc (i.val+2) 6, (squarePart h x.1.2 x.2 j : ℝ) ≤ 2*B j

private theorem parts_eq (i : Fin 5) (x y : Sample)
    (he : allocationTuple h i x = allocationTuple h i y)
    (j : ℕ) (hj : j ∈ Finset.Icc (i.val+2) 6) :
    primePart h x.1.1 x.2 j = primePart h y.1.1 y.2 j ∧
      squarePart h x.1.2 x.2 j = squarePart h y.1.2 y.2 j := by
  have hji := Finset.mem_Icc.mp hj
  let k : Fin (5-i.val) := ⟨j-(i.val+2),by have hi := i.isLt; omega⟩
  have hk : i.val+k.val+2=j := by dsimp [k]; omega
  have ha := congrArg (fun z : Allocation i => z.1.1 k) he
  have hb := congrArg (fun z : Allocation i => z.1.2 k) he
  change primePart h x.1.1 x.2 (i.val+k.val+2) =
    primePart h y.1.1 y.2 (i.val+k.val+2) at ha
  change squarePart h x.1.2 x.2 (i.val+k.val+2) =
    squarePart h y.1.2 y.2 (i.val+k.val+2) at hb
  rw [hk] at ha hb
  exact ⟨ha,hb⟩

/-- A single constant precedes the scale functions, all frequencies and
the arbitrary finite family of original modulus/frequency samples. -/
theorem exists_bound (hF : F.IsHomogeneous 3)
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C d h)
    (i : Fin 5) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ D H : ℝ, 1 ≤ D → 1 ≤ H →
      ∀ A B : ℕ → ℝ,
      (∀ j ∈ Finset.Icc (i.val+2) 6, 1 ≤ A j) →
      (∀ j ∈ Finset.Icc (i.val+2) 6, 1 ≤ B j) →
      ∀ E : Finset Sample, (∀ x ∈ E, InBlock F f tables h i D H A B x) →
      (∑ x ∈ E, ‖completeCubicSum F (x.1.1*x.1.2^2) x.2‖) ≤
        M*(D*H)^ε*D^((13+(i.val : ℝ))/2)*ComplementDeepWeights.weight (i.val+2) A B*
          ((E.image (allocationTuple h i)).card : ℝ) := by
  classical
  obtain ⟨M₀,hM₀,hbound⟩ := ComplementAllocationBound.exists_bound hF hc i ε hε
  refine ⟨M₀*(2 : ℝ)^30,by norm_num; linarith,?_⟩
  intro D H hD hH A B hA hB E hE
  let Z := E.image (allocationTuple h i)
  let fiber (z : Allocation i) := E.filter (fun x => allocationTuple h i x=z)
  let V : ℝ := (M₀*(2 : ℝ)^30)*(D*H)^ε*D^((13+(i.val : ℝ))/2)*
    ComplementDeepWeights.weight (i.val+2) A B
  have hfiber (z : Allocation i) (hz : z ∈ Z) :
      (∑ x ∈ fiber z, ‖completeCubicSum F (x.1.1*x.1.2^2) x.2‖) ≤ V := by
    obtain ⟨x₀,hx₀,rfl⟩ := Finset.mem_image.mp hz
    let Q := (fiber (allocationTuple h i x₀)).image Prod.fst
    have hfreq (x : Sample) (hx : x ∈ fiber (allocationTuple h i x₀)) : x.2=x₀.2 :=
      congrArg (fun z : Allocation i => z.2) (Finset.mem_filter.mp hx).2
    have hQ : ∀ a ∈ Q, Squarefree a.1 ∧ Squarefree a.2 ∧ a.1.Coprime a.2 ∧
        (a.1 : ℝ)*(a.2 : ℝ)^2 ≤ 2*D ∧
        ∀ j ∈ Finset.Icc (i.val+2) 6,
          primePart h a.1 x₀.2 j = primePart h x₀.1.1 x₀.2 j ∧
          squarePart h a.2 x₀.2 j = squarePart h x₀.1.2 x₀.2 j := by
      intro a ha
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
      have hh := hE x (Finset.mem_filter.mp hx).1
      refine ⟨hh.squarefree_left,hh.squarefree_right,hh.coprime,hh.size,?_⟩
      intro j hj
      have hp := parts_eq i x x₀ (Finset.mem_filter.mp hx).2 j hj
      simpa only [hfreq x hx] using hp
    have hinj : Set.InjOn (Prod.fst : Sample → ℕ × ℕ)
        (↑(fiber (allocationTuple h i x₀)) : Set Sample) := by
      intro x hx y hy he
      exact Prod.ext he ((hfreq x hx).trans (hfreq y hy).symm)
    have hsum : (∑ a ∈ Q, ‖completeCubicSum F (a.1*a.2^2) x₀.2‖) =
        ∑ x ∈ fiber (allocationTuple h i x₀), ‖completeCubicSum F (x.1.1*x.1.2^2) x.2‖ := by
      rw [show (∑ a ∈ Q, ‖completeCubicSum F (a.1*a.2^2) x₀.2‖) =
          ∑ x ∈ fiber (allocationTuple h i x₀), ‖completeCubicSum F (x.1.1*x.1.2^2) x₀.2‖ from
        Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro x hx
      rw [hfreq x hx]
    have hxdata := hE x₀ hx₀
    have hs := hbound x₀.2 hxdata.piece D H hD hH hxdata.height
      (primePart h x₀.1.1 x₀.2) (squarePart h x₀.1.2 x₀.2) Q hQ
    have hw := ComplementDyadicWeight.weight_le (i.val+2) (by omega)
      (primePart h x₀.1.1 x₀.2) (squarePart h x₀.1.2 x₀.2)
      A B hA hB hxdata.prime_upper hxdata.square_upper
    rw [hsum] at hs
    apply hs.trans
    calc
      _ ≤ M₀*(D*H)^ε*D^((13+(i.val : ℝ))/2)*
          ((2 : ℝ)^30*ComplementDeepWeights.weight (i.val+2) A B) :=
        mul_le_mul_of_nonneg_left hw (by
          have hD0 := zero_le_one.trans hD
          have hH0 := zero_le_one.trans hH
          have hM0 := zero_le_one.trans hM₀
          positivity)
      _ = V := by dsimp [V]; ring
  calc
    _ = ∑ z ∈ Z, ∑ x ∈ fiber z, ‖completeCubicSum F (x.1.1*x.1.2^2) x.2‖ := by
      symm
      exact Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem _ hx) _
    _ ≤ ∑ z ∈ Z, V := Finset.sum_le_sum hfiber
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, V, Z]; ring

end CubicTenVariables.ComplementAllocationWeightedBlock

import CubicTenVariables.PrimePowerScalarFibers
import CubicTenVariables.MatrixSmithResidualRank
import CubicTenVariables.PrimePowerKernelProfile
import CubicTenVariables.PrimeFieldKernelRank
import CubicTenVariables.SmoothResidueLifting

/-! Exact one-digit kernel counts for an arbitrary perturbation of an
integral diagonal matrix. The residual matrix is affine in the perturbation;
all primes, zero entries and empty old or tail blocks are included. -/

noncomputable section
set_option maxHeartbeats 800000
namespace CubicTenVariables.DiagonalSmithOneDigitKernel
open scoped BigOperators
open PrimePowerKernelProfile

variable {n : ℕ}

abbrev tailIndices (p m : ℕ) (d : Fin n → ℤ) :=
  MatrixSmithResidualRank.tailIndices p m d

abbrev oldIndices (p m : ℕ) (d : Fin n → ℤ) :=
  MatrixSmithResidualRank.oldIndices p m d

/-- Reduction to the actual prime-field residue. -/
def toPrime (p m : ℕ) : ZMod (p^(m+1)) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by omega)) (ZMod p)

/-- The shared residual tail matrix. -/
abbrev residualMatrix (p m : ℕ) (d : Fin n → ℤ)
    (E : Matrix (Fin n) (Fin n) ℤ) :=
  MatrixSmithResidualRank.residualMatrix p m d E

/-- The integer matrix whose literal residue kernel is counted. -/
def perturbedMatrix (p m : ℕ) (d : Fin n → ℤ)
    (E : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.diagonal d + (p:ℤ)^m • E

@[simp] theorem toPrime_intCast (p m : ℕ) (a : ℤ) :
    toPrime p m (a : ZMod (p^(m+1))) = (a : ZMod p) := by
  exact map_intCast _ _

/-- Multiplication by the last-digit step tests exactly the prime residue. -/
theorem step_mul_eq_zero_iff (p m : ℕ) [NeZero p] (z : ZMod (p^(m+1))) :
    (p : ZMod (p^(m+1)))^m*z = 0 ↔ toPrime p m z = 0 := by
  obtain ⟨a,rfl⟩ := ZMod.intCast_surjective z
  simpa only [Int.cast_mul, Int.cast_natCast, Nat.cast_pow, Int.cast_pow, toPrime_intCast]
    using SmoothResidueLifting.step_mul_cast_eq_zero_iff p m a

/-- The literal matrix equation, expanded one row at a time. -/
theorem mulVec_apply (p m : ℕ) (d : Fin n → ℤ)
    (E : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ZMod (p^(m+1))) (i : Fin n) :
    ((perturbedMatrix p m d E).map (Int.castRingHom (ZMod (p^(m+1))))).mulVec x i =
      (d i : ZMod (p^(m+1)))*x i + (p : ZMod (p^(m+1)))^m *
        ∑ j, (E i j : ZMod (p^(m+1)))*x j := by
  classical
  change (∑ j, (((Matrix.diagonal d) i j + (p:ℤ)^m * E i j : ℤ) :
    ZMod (p^(m+1))) * x j) = _
  simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
    add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  congr 1
  simp [Matrix.diagonal]

/-- The residual matrix multiplication is the reduction of its integral
quotient expression on the tail. -/
theorem residual_mulVec_apply (p m : ℕ) (d : Fin n → ℤ)
    (E : Matrix (Fin n) (Fin n) ℤ)
    (x : tailIndices p m d → ZMod (p^(m+1))) (i : tailIndices p m d) :
    (residualMatrix p m d E).mulVec (fun j => toPrime p m (x j)) i =
      toPrime p m (((d i / (p:ℤ)^m : ℤ) : ZMod (p^(m+1))) * x i +
        ∑ j : tailIndices p m d, (E i j : ZMod (p^(m+1)))*x j) := by
  classical
  dsimp only [residualMatrix, MatrixSmithResidualRank.residualMatrix]
  rw [Matrix.add_mulVec, Pi.add_apply, Matrix.mulVec_diagonal]
  simp [Matrix.mulVec, dotProduct]

/-- Old columns make no contribution at the next precision once their
coordinates reduce to zero modulo p. -/
theorem step_sum_eq_tail (p m : ℕ) [NeZero p] (d : Fin n → ℤ)
    (E : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ZMod (p^(m+1)))
    (hx : ∀ i : oldIndices p m d, toPrime p m (x i) = 0) (i : Fin n) :
    (p : ZMod (p^(m+1)))^m * (∑ j, (E i j : ZMod (p^(m+1)))*x j) =
      (p : ZMod (p^(m+1)))^m *
        ∑ j : tailIndices p m d, (E i j : ZMod (p^(m+1)))*x j := by
  classical
  have hzero : ∀ j : oldIndices p m d,
      (p : ZMod (p^(m+1)))^m * ((E i j : ZMod (p^(m+1)))*x j) = 0 := by
    intro j
    apply (step_mul_eq_zero_iff p m _).mpr
    rw [map_mul, hx j, mul_zero]
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun j : Fin n => (p:ℤ)^m ∣ d j)
    (fun j : Fin n => (E i j : ZMod (p^(m+1)))*x j)
  rw [← hs, mul_add]
  have hz : (p : ZMod (p^(m+1)))^m *
      (∑ j : oldIndices p m d, (E i j : ZMod (p^(m+1)))*x j) = 0 := by
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero (fun j _ => hzero j)
  rw [hz, add_zero]

/-- Counting a preimage by all its actual fibers. -/
theorem card_preimage_eq_mul {α β : Type*} [Finite α] [Fintype β]
    (f : α → β) (P : β → Prop) (C : ℕ)
    (hc : ∀ b, P b → Nat.card {a : α // f a = b} = C) :
    Nat.card {a : α // P (f a)} = C * Nat.card {b : β // P b} := by
  classical
  let e : {a : α // P (f a)} ≃
      (Σ b : {b : β // P b}, {a : α // f a = b.1}) :=
    { toFun := fun a => ⟨⟨f a.1, a.2⟩, ⟨a.1,rfl⟩⟩
      invFun := fun b => ⟨b.2.1, by rw [b.2.2]; exact b.1.2⟩
      left_inv := fun a => rfl
      right_inv := by
        rintro ⟨⟨b,hb⟩,⟨a,ha⟩⟩
        dsimp at ha
        subst b
        rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  simp only [hc _ (Subtype.property _), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Nat.card_eq_fintype_card, mul_comm, Nat.cast_id]

/-- Every prime residue has precisely p^m lifts at precision m+1. -/
theorem card_toPrime_fiber (p m : ℕ) [Fact p.Prime] (b : ZMod p) :
    Nat.card {x : ZMod (p^(m+1)) // toPrime p m x = b} = p^m := by
  have h := PrimePowerFibers.card_fiber_mul_card_of_surjective
    (toPrime p m).toAddMonoidHom
    (ZMod.castHom_surjective (dvd_pow_self p (by omega))) b
  rw [Nat.card_zmod, Nat.card_zmod] at h
  apply Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos
  simpa only [pow_succ] using h

/-- The same exact lifting count for any finite tail index type. -/
theorem card_vector_toPrime_fiber {ι : Type*} [Fintype ι]
    (p m : ℕ) [Fact p.Prime] (b : ι → ZMod p) :
    Nat.card {x : ι → ZMod (p^(m+1)) // (fun i => toPrime p m (x i)) = b} =
      p^(m*Fintype.card ι) := by
  classical
  calc
    _ = Nat.card {x : ι → ZMod (p^(m+1)) // ∀ i, toPrime p m (x i) = b i} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x => funext_iff)
    _ = _ := by
      rw [Nat.card_congr (Equiv.subtypePiEquivPi
        (p := fun i z => toPrime p m z = b i)), Nat.card_pi]
      simp only [card_toPrime_fiber, Finset.prod_const, Finset.card_univ, ← pow_mul]

/-- Higher tail digits contribute a fixed factor independently of the
actual prime-field matrix and its kernel. -/
theorem card_lifted_kernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p m : ℕ) [Fact p.Prime] (G : Matrix ι ι (ZMod p)) :
    Nat.card {x : ι → ZMod (p^(m+1)) //
      G.mulVec (fun i => toPrime p m (x i)) = 0} =
      p^(m*Fintype.card ι) * Nat.card {y : ι → ZMod p // G.mulVec y = 0} := by
  classical
  exact card_preimage_eq_mul (α := ι → ZMod (p^(m+1))) (β := ι → ZMod p)
    (fun x i => toPrime p m (x i)) (fun y => G.mulVec y = 0)
    (p^(m*Fintype.card ι)) (fun b _ => card_vector_toPrime_fiber p m b)

/-- Every old coordinate of an actual kernel vector vanishes modulo p. -/
theorem old_reduction_eq_zero (p m : ℕ) [Fact p.Prime] (d : Fin n → ℤ)
    (E : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ZMod (p^(m+1)))
    (hx : ((perturbedMatrix p m d E).map
      (Int.castRingHom (ZMod (p^(m+1))))).mulVec x = 0)
    (i : oldIndices p m d) : toPrime p m (x i) = 0 := by
  have hi := congrFun hx i.val
  rw [mulVec_apply] at hi
  simp only [Pi.zero_apply] at hi
  have he : (d i : ZMod (p^(m+1)))*x i =
      (p : ZMod (p^(m+1)))^m * (-(∑ j, (E i j : ZMod (p^(m+1)))*x j)) := by
    linear_combination hi
  exact PrimePowerScalarFibers.reduction_eq_zero_of_scalar_eq
    p m Fact.out (d i) i.property (x i) _ he

/-- For tail rows, the whole matrix equation is exactly the residual
prime-field equation, once old coordinates have zero prime residue. -/
theorem tail_row_eq_zero_iff (p m : ℕ) [Fact p.Prime] (d : Fin n → ℤ)
    (E : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ZMod (p^(m+1)))
    (hx : ∀ i : oldIndices p m d, toPrime p m (x i) = 0)
    (i : tailIndices p m d) :
    ((perturbedMatrix p m d E).map
      (Int.castRingHom (ZMod (p^(m+1))))).mulVec x i = 0 ↔
      (residualMatrix p m d E).mulVec (fun j => toPrime p m (x j)) i = 0 := by
  have hd : (d i : ZMod (p^(m+1))) = (p : ZMod (p^(m+1)))^m *
      ((d i / (p:ℤ)^m : ℤ) : ZMod (p^(m+1))) := by
    have hi := Int.mul_ediv_cancel' i.property
    simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast] using
      congrArg (fun z : ℤ => (z : ZMod (p^(m+1)))) hi.symm
  rw [mulVec_apply, step_sum_eq_tail p m d E x hx i, hd,
    mul_assoc, ← mul_add, step_mul_eq_zero_iff, residual_mulVec_apply]

/-- Exact independent old scalar equations and the residual tail kernel. -/
theorem kernel_iff (p m : ℕ) [Fact p.Prime] (d : Fin n → ℤ)
    (E : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ZMod (p^(m+1))) :
    ((perturbedMatrix p m d E).map
      (Int.castRingHom (ZMod (p^(m+1))))).mulVec x = 0 ↔
      (∀ i : oldIndices p m d, (d i : ZMod (p^(m+1)))*x i =
        (p : ZMod (p^(m+1)))^m *
          (-(∑ j : tailIndices p m d, (E i j : ZMod (p^(m+1)))*x j))) ∧
      (residualMatrix p m d E).mulVec (fun j => toPrime p m (x j)) = 0 := by
  classical
  constructor
  · intro hx
    have hold := old_reduction_eq_zero p m d E x hx
    constructor
    · intro i
      have hi := congrFun hx i.val
      rw [mulVec_apply, step_sum_eq_tail p m d E x hold i] at hi
      simp only [Pi.zero_apply] at hi
      linear_combination hi
    · funext i
      exact (tail_row_eq_zero_iff p m d E x hold i).mp (congrFun hx i.val)
  · rintro ⟨hold,htail⟩
    have hz : ∀ i : oldIndices p m d, toPrime p m (x i) = 0 := by
      intro i
      exact PrimePowerScalarFibers.reduction_eq_zero_of_scalar_eq
        p m Fact.out (d i) i.property (x i) _ (hold i)
    funext i
    by_cases hi : (p:ℤ)^m ∣ d i
    · exact (tail_row_eq_zero_iff p m d E x hz ⟨i,hi⟩).mpr (congrFun htail ⟨i,hi⟩)
    · rw [mulVec_apply, step_sum_eq_tail p m d E x hz i]
      simp only [Pi.zero_apply]
      have he := hold ⟨i,hi⟩
      dsimp only at he
      linear_combination he

/-- Exact product decomposition when the second-coordinate condition
has a fixed cardinality on every admissible first coordinate. -/
theorem card_pair_subtype {α β : Type*} [Fintype α] [Finite β]
    (P : α → Prop) (Q : α → β → Prop) (C : ℕ)
    (hc : ∀ a, P a → Nat.card {b : β // Q a b} = C) :
    Nat.card {z : α × β // P z.1 ∧ Q z.1 z.2} = C * Nat.card {a : α // P a} := by
  classical
  let e : {z : α × β // P z.1 ∧ Q z.1 z.2} ≃
      (Σ a : {a : α // P a}, {b : β // Q a.1 b}) :=
    { toFun := fun z => ⟨⟨z.1.1,z.2.1⟩,⟨z.1.2,z.2.2⟩⟩
      invFun := fun z => ⟨⟨z.1.1,z.2.1⟩,z.1.2,z.2.2⟩
      left_inv := fun z => rfl
      right_inv := fun z => rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  simp only [hc _ (Subtype.property _), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Nat.card_eq_fintype_card, mul_comm, Nat.cast_id]

/-- Each fixed tail leaves independent solvable equations at the old pivots. -/
theorem card_old_solutions (p m : ℕ) [Fact p.Prime] (d : Fin n → ℤ)
    (E : Matrix (Fin n) (Fin n) ℤ) (v : tailIndices p m d → ZMod (p^(m+1))) :
    Nat.card {u : oldIndices p m d → ZMod (p^(m+1)) //
      ∀ i : oldIndices p m d, (d i : ZMod (p^(m+1)))*u i = (p : ZMod (p^(m+1)))^m *
        (-(∑ j : tailIndices p m d, (E i j : ZMod (p^(m+1)))*v j))} =
      p^(∑ i : oldIndices p m d, truncatedValuation p m (d i)) := by
  classical
  rw [Nat.card_congr (Equiv.subtypePiEquivPi
    (p := fun (i : oldIndices p m d) z => (d i : ZMod (p^(m+1)))*z = (p : ZMod (p^(m+1)))^m *
      (-(∑ j : tailIndices p m d, (E i j : ZMod (p^(m+1)))*v j)))), Nat.card_pi]
  trans ∏ i : oldIndices p m d, p^(truncatedValuation p m (d i))
  · apply Finset.prod_congr rfl
    intro i _
    exact PrimePowerScalarFibers.card_scalar_fiber p m Fact.out (d i) i.property _
  · exact Finset.prod_pow_eq_pow_sum Finset.univ _ p

/-- The exact literal one-digit kernel formula. The level zero boundary is
also valid; at that level there are no old pivots. -/
theorem card_kernel_eq (p m : ℕ) [Fact p.Prime] (d : Fin n → ℤ)
    (E : Matrix (Fin n) (Fin n) ℤ) :
    Nat.card {x : Fin n → ZMod (p^(m+1)) //
      ((Matrix.diagonal d + (p:ℤ)^m • E).map
        (Int.castRingHom (ZMod (p^(m+1))))).mulVec x = 0} =
      p^((∑ i : oldIndices p m d, truncatedValuation p m (d i)) +
          m*Fintype.card (tailIndices p m d)) *
        Nat.card {y : tailIndices p m d → ZMod p //
          (residualMatrix p m d E).mulVec y = 0} := by
  classical
  let P : (tailIndices p m d → ZMod (p^(m+1))) → Prop :=
    fun v => (residualMatrix p m d E).mulVec (fun j => toPrime p m (v j)) = 0
  let Q : (tailIndices p m d → ZMod (p^(m+1))) →
      (oldIndices p m d → ZMod (p^(m+1))) → Prop :=
    fun v u => ∀ i : oldIndices p m d, (d i : ZMod (p^(m+1)))*u i = (p : ZMod (p^(m+1)))^m *
      (-(∑ j : tailIndices p m d, (E i j : ZMod (p^(m+1)))*v j))
  let e := Equiv.piEquivPiSubtypeProd (fun i : Fin n => (p:ℤ)^m ∣ d i)
    (fun _ => ZMod (p^(m+1)))
  have he : ∀ x : Fin n → ZMod (p^(m+1)),
      ((Matrix.diagonal d + (p:ℤ)^m • E).map
        (Int.castRingHom (ZMod (p^(m+1))))).mulVec x = 0 ↔ P (e x).1 ∧ Q (e x).1 (e x).2 := by
    intro x
    exact (kernel_iff p m d E x).trans and_comm
  calc
    _ = Nat.card {z : (tailIndices p m d → ZMod (p^(m+1))) ×
        (oldIndices p m d → ZMod (p^(m+1))) // P z.1 ∧ Q z.1 z.2} :=
      Nat.card_congr (e.subtypeEquiv he)
    _ = p^(∑ i : oldIndices p m d, truncatedValuation p m (d i)) *
        Nat.card {v : tailIndices p m d → ZMod (p^(m+1)) // P v} :=
      card_pair_subtype P Q _ (fun v _ => card_old_solutions p m d E v)
    _ = _ := by
      dsimp only [P]
      rw [card_lifted_kernel, ← mul_assoc, ← pow_add]

/-- Rank-nullity for the actual residual tail, on its literal subtype index. -/
theorem card_residual_kernel (p m : ℕ) [Fact p.Prime] (d : Fin n → ℤ)
    (E : Matrix (Fin n) (Fin n) ℤ) :
    Nat.card {y : tailIndices p m d → ZMod p //
      (residualMatrix p m d E).mulVec y = 0} =
        p^(Fintype.card (tailIndices p m d) - (residualMatrix p m d E).rank) := by
  classical
  let G := residualMatrix p m d E
  change Nat.card (LinearMap.ker G.mulVecLin) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  congr 1
  have h := G.mulVecLin.finrank_range_add_finrank_ker
  have h' : G.rank + Module.finrank (ZMod p) (LinearMap.ker G.mulVecLin) =
      Fintype.card (tailIndices p m d) := by
    simpa only [Matrix.rank, Module.finrank_pi] using h
  change Module.finrank (ZMod p) (LinearMap.ker G.mulVecLin) =
    Fintype.card (tailIndices p m d) - G.rank
  omega

/-- The equivalent exact formula with the residual rank exposed. -/
theorem card_kernel_eq_pow (p m : ℕ) [Fact p.Prime] (d : Fin n → ℤ)
    (E : Matrix (Fin n) (Fin n) ℤ) :
    Nat.card {x : Fin n → ZMod (p^(m+1)) //
      ((Matrix.diagonal d + (p:ℤ)^m • E).map
        (Int.castRingHom (ZMod (p^(m+1))))).mulVec x = 0} =
      p^((∑ i : oldIndices p m d, truncatedValuation p m (d i)) +
        m*Fintype.card (tailIndices p m d)) *
      p^(Fintype.card (tailIndices p m d) - (residualMatrix p m d E).rank) := by
  rw [card_kernel_eq, card_residual_kernel]

/-- The old diagonal kernel is exactly the common prefactor in the next
one-digit count. -/
theorem card_diagonal_eq_prefactor (p m : ℕ) [Fact p.Prime] (d : Fin n → ℤ) :
    Nat.card {x : Fin n → ZMod (p^m) //
      ((Matrix.diagonal d).map (Int.castRingHom (ZMod (p^m)))).mulVec x = 0} =
      p^((∑ i : oldIndices p m d, truncatedValuation p m (d i)) +
        m*Fintype.card (tailIndices p m d)) := by
  classical
  have ht (i : tailIndices p m d) : truncatedValuation p m (d i) = m := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
    change p^(truncatedValuation p m (d i)) = p^m
    rw [← gcd_primePower p m Fact.out]
    apply Nat.gcd_eq_right
    apply Int.natCast_dvd.mp
    simpa only [Nat.cast_pow] using i.property
  rw [card_diagonal_primePower p m Fact.out]
  congr 1
  have h := Fintype.sum_subtype_add_sum_subtype
    (fun i : Fin n => (p:ℤ)^m ∣ d i) (fun i => truncatedValuation p m (d i))
  have he : (∑ i : tailIndices p m d, truncatedValuation p m (d i)) =
      m*Fintype.card (tailIndices p m d) := by
    simp only [ht, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm, Nat.cast_id]
  calc
    _ = (∑ i : tailIndices p m d, truncatedValuation p m (d i)) +
        (∑ i : oldIndices p m d, truncatedValuation p m (d i)) := h.symm
    _ = _ := by rw [he, Nat.add_comm]

/-- The exact growth formula with the literal old-level diagonal kernel. -/
theorem card_kernel_eq_diagonal_mul (p m : ℕ) [Fact p.Prime] (d : Fin n → ℤ)
    (E : Matrix (Fin n) (Fin n) ℤ) :
    Nat.card {x : Fin n → ZMod (p^(m+1)) //
      ((Matrix.diagonal d + (p:ℤ)^m • E).map
        (Int.castRingHom (ZMod (p^(m+1))))).mulVec x = 0} =
      Nat.card {x : Fin n → ZMod (p^m) //
        ((Matrix.diagonal d).map (Int.castRingHom (ZMod (p^m)))).mulVec x = 0} *
      p^(Fintype.card (tailIndices p m d) - (residualMatrix p m d E).rank) := by
  rw [card_kernel_eq_pow, card_diagonal_eq_prefactor]

/-- The retained block has the complementary number of coordinates. -/
theorem tail_card_eq_sub_old (p m : ℕ) (d : Fin n → ℤ) :
    Fintype.card (tailIndices p m d) = n - Fintype.card (oldIndices p m d) := by
  classical
  have h : Fintype.card (tailIndices p m d) + Fintype.card (oldIndices p m d) = n := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using
      Fintype.card_congr (Equiv.sumCompl (fun i : Fin n => (p:ℤ)^m ∣ d i))
  omega

end CubicTenVariables.DiagonalSmithOneDigitKernel

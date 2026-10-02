import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.BigOperators

/-!
# Literal scalar and diagonal kernels modulo a positive integer

Multiplication by an integer `d` on `ZMod q` has exactly
`Nat.gcd d.natAbs q` zeros. Coordinatewise decomposition then counts the
actual kernel of a diagonal matrix as the product of these gcds.

For a diagonal entry equal to a residue unit times `p^j`, at modulus `p^t`,
the scalar count is `p^(min j t)`; the diagonal count is the corresponding
power with the exponents summed. Primality is unnecessary for these last
identities: any positive base works. Zero entries, saturated exponents,
modulus one, and empty coordinate sets are included. No Smith normal form
existence, geometric estimate, or literature proposition is assumed.
-/

noncomputable section
namespace CubicTenVariables.ModularKernelCardinality

open scoped BigOperators

/-- The actual scalar multiplication kernel, first for a natural coefficient. -/
theorem card_scalar_kernel_nat (q d : ℕ) [NeZero q] :
    Nat.card {x : ZMod q // (d : ZMod q) * x = 0} = Nat.gcd d q := by
  simpa only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, nsmul_eq_mul,
    Nat.card_zmod, Nat.gcd_comm] using
    IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod q) d

/-- Signed coefficients give the gcd of their absolute value with the modulus. -/
theorem card_scalar_kernel_int (q : ℕ) [NeZero q] (d : ℤ) :
    Nat.card {x : ZMod q // (d : ZMod q) * x = 0} = Nat.gcd d.natAbs q := by
  calc
    _ = Nat.card {x : ZMod q // (d.natAbs : ZMod q) * x = 0} := by
      apply Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
      simpa only [nsmul_eq_mul, zsmul_eq_mul] using
        (natAbs_nsmul_eq_zero (n := d) (a := x)).symm
    _ = _ := card_scalar_kernel_nat q d.natAbs

/-- A residue-unit factor does not change the literal multiplication kernel. -/
theorem card_scalar_kernel_mul_unit (q : ℕ) [NeZero q]
    (d : ZMod q) (u : (ZMod q)ˣ) :
    Nat.card {x : ZMod q // (d * (u : ZMod q)) * x = 0} =
      Nat.card {x : ZMod q // d * x = 0} := by
  apply Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [mul_right_comm, u.mul_left_eq_zero]

/-- Saturation at the modulus exponent is automatic, including `t = 0`. -/
theorem card_scalar_primePower_kernel (p j t : ℕ) [NeZero p] :
    Nat.card {x : ZMod (p ^ t) // (p : ZMod (p ^ t)) ^ j * x = 0} =
      p ^ min j t := by
  have h := card_scalar_kernel_nat (p ^ t) (p ^ j)
  rw [Nat.cast_pow] at h
  rw [h]
  rcases le_total j t with hjt | htj
  · rw [Nat.min_eq_left hjt, Nat.gcd_eq_left (pow_dvd_pow p hjt)]
  · rw [Nat.min_eq_right htj, Nat.gcd_eq_right (pow_dvd_pow p htj)]

/-- The same exact count with an arbitrary unit factor in the residue ring. -/
theorem card_scalar_primePower_unit_kernel (p j t : ℕ) [NeZero p]
    (u : (ZMod (p ^ t))ˣ) :
    Nat.card {x : ZMod (p ^ t) //
      ((p : ZMod (p ^ t)) ^ j * (u : ZMod (p ^ t))) * x = 0} =
      p ^ min j t := by
  rw [card_scalar_kernel_mul_unit, card_scalar_primePower_kernel]

/-- A zero coefficient contributes the whole residue ring to the kernel. -/
@[simp] theorem card_zero_scalar_kernel (q : ℕ) [NeZero q] :
    Nat.card {x : ZMod q // (0 : ZMod q) * x = 0} = q := by
  simp

/-- An actual diagonal matrix kernel is the product of its scalar kernels. -/
theorem card_diagonal_kernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ) [NeZero q] (d : ι → ZMod q) :
    Nat.card {x : ι → ZMod q // (Matrix.diagonal d).mulVec x = 0} =
      ∏ i, Nat.card {z : ZMod q // d i * z = 0} := by
  calc
    _ = Nat.card {x : ι → ZMod q // ∀ i, d i * x i = 0} := by
      apply Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
      simp only [funext_iff, Matrix.mulVec_diagonal, Pi.zero_apply]
    _ = _ := by
      rw [Nat.card_congr (Equiv.subtypePiEquivPi
        (p := fun (i : ι) (z : ZMod q) => d i * z = 0)), Nat.card_pi]

/-- The diagonal kernel formula for actual integer entries after reduction. -/
theorem card_diagonal_int_kernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ) [NeZero q] (d : ι → ℤ) :
    Nat.card {x : ι → ZMod q //
      (Matrix.diagonal (fun i => (d i : ZMod q))).mulVec x = 0} =
      ∏ i, Nat.gcd (d i).natAbs q := by
  rw [card_diagonal_kernel]
  simp only [card_scalar_kernel_int]

/-- The same formula with the integer matrix itself explicitly mapped. -/
theorem card_map_diagonal_int_kernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ) [NeZero q] (d : ι → ℤ) :
    Nat.card {x : ι → ZMod q //
      ((Matrix.diagonal d).map (Int.castRingHom (ZMod q))).mulVec x = 0} =
      ∏ i, Nat.gcd (d i).natAbs q := by
  simpa only [Matrix.diagonal_map (map_zero (Int.castRingHom (ZMod q)))] using
    card_diagonal_int_kernel q d

/-- Explicit power/unit diagonal entries give the sum of truncated exponents.
Exponents at least `t` are allowed and represent zero entries modulo `p^t`. -/
theorem card_diagonal_primePower_unit_kernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p t : ℕ) [NeZero p] (j : ι → ℕ) (u : ι → (ZMod (p ^ t))ˣ) :
    Nat.card {x : ι → ZMod (p ^ t) //
      (Matrix.diagonal (fun i => (p : ZMod (p ^ t)) ^ j i * (u i : ZMod (p ^ t)))).mulVec x = 0} =
      p ^ (∑ i, min (j i) t) := by
  rw [card_diagonal_kernel]
  simp only [card_scalar_primePower_unit_kernel]
  exact Finset.prod_pow_eq_pow_sum Finset.univ _ p

end CubicTenVariables.ModularKernelCardinality

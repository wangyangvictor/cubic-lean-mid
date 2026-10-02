import CubicTenVariables.PrimeSumAdapter
import CubicTenVariables.WeightedCounting
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

/-! Exact decomposition of the integer-coordinate lattice into canonical
residue representatives and quotient vectors. All regrouping statements
retain genuine convergence hypotheses; no Poisson identity is assumed. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.IntegerLatticeResidues
open MvPolynomial
open scoped BigOperators

/-- Canonical integer representatives of one vector residue class. -/
def representative {n ℓ : ℕ} (b : Fin n → Fin ℓ) : Fin n → ℤ :=
  fun i => ((b i).val : ℤ)

/-- The full affine lattice in one residue class. -/
def assemble {n ℓ : ℕ} (b : Fin n → Fin ℓ) (m : Fin n → ℤ) : Fin n → ℤ :=
  fun i => representative b i + (ℓ : ℤ)*m i

/-- Euclidean division in every coordinate, including negative integers. -/
def equiv (n ℓ : ℕ) (hℓ : 0 < ℓ) :
    (Fin n → ℤ) ≃ (Fin n → Fin ℓ) × (Fin n → ℤ) := by
  letI : NeZero ℓ := ⟨hℓ.ne'⟩
  exact {
    toFun := fun x => (fun i => (Int.divModEquiv ℓ (x i)).2,
      fun i => (Int.divModEquiv ℓ (x i)).1)
    invFun := fun p i => (Int.divModEquiv ℓ).symm (p.2 i,p.1 i)
    left_inv := by
      intro x
      funext i
      exact (Int.divModEquiv ℓ).symm_apply_apply (x i)
    right_inv := by
      intro p
      apply Prod.ext
      · funext i
        exact congrArg Prod.snd ((Int.divModEquiv ℓ).apply_symm_apply (p.2 i,p.1 i))
      · funext i
        exact congrArg Prod.fst ((Int.divModEquiv ℓ).apply_symm_apply (p.2 i,p.1 i)) }

@[simp] theorem equiv_symm_apply (n ℓ : ℕ) (hℓ : 0 < ℓ)
    (b : Fin n → Fin ℓ) (m : Fin n → ℤ) :
    (equiv n ℓ hℓ).symm (b,m) = assemble b m := by
  funext i
  dsimp [equiv,assemble,representative,Int.divModEquiv]
  ring

@[simp] theorem equiv_symm_apply_pair (n ℓ : ℕ) (hℓ : 0 < ℓ)
    (p : (Fin n → Fin ℓ) × (Fin n → ℤ)) :
    (equiv n ℓ hℓ).symm p = assemble p.1 p.2 :=
  equiv_symm_apply n ℓ hℓ p.1 p.2

/-- Literal reconstruction, without a nonnegative-coordinate restriction. -/
theorem reconstruct (n ℓ : ℕ) (hℓ : 0 < ℓ) (x : Fin n → ℤ) :
    assemble ((equiv n ℓ hℓ x).1) ((equiv n ℓ hℓ x).2) = x := by
  rw [← equiv_symm_apply]
  exact (equiv n ℓ hℓ).symm_apply_apply x

@[simp] theorem equiv_assemble (n ℓ : ℕ) (hℓ : 0 < ℓ)
    (b : Fin n → Fin ℓ) (m : Fin n → ℤ) :
    equiv n ℓ hℓ (assemble b m) = (b,m) := by
  rw [← equiv_symm_apply]
  exact (equiv n ℓ hℓ).apply_symm_apply (b,m)

/-- Progression representatives agree modulo every divisor of the spacing. -/
theorem integerResidue_assemble {n ℓ : ℕ} (q : ℕ) (hq : q ∣ ℓ)
    (b : Fin n → Fin ℓ) (m : Fin n → ℤ) :
    integerResidue q (assemble b m) = integerResidue q (representative b) := by
  have hz : (ℓ : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff ℓ q).mpr hq
  ext i
  simp [integerResidue,assemble,hz]

/-- Polynomial evaluation is compatible with the same divisor reduction. -/
theorem eval_assemble_cast {n ℓ : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (q : ℕ) (hq : q ∣ ℓ) (b : Fin n → Fin ℓ) (m : Fin n → ℤ) :
    (eval (assemble b m) F : ZMod q) = (eval (representative b) F : ZMod q) := by
  have he := integerResidue_assemble q hq b m
  change (Int.castRingHom (ZMod q)) (eval (assemble b m) F) =
    (Int.castRingHom (ZMod q)) (eval (representative b) F)
  rw [MvPolynomial.map_eval, MvPolynomial.map_eval]
  change eval (integerResidue q (assemble b m)) (map (Int.castRingHom (ZMod q)) F) =
    eval (integerResidue q (representative b)) (map (Int.castRingHom (ZMod q)) F)
  rw [he]

/-- The polynomial character stays at modulus q, even when the lattice
spacing is a larger multiple of q. -/
theorem character_assemble {n ℓ : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (q : ℕ) (hq : 0 < q) (hqℓ : q ∣ ℓ) (a : ℤ)
    (b : Fin n → Fin ℓ) (m : Fin n → ℤ) :
    residueExponential q (a*eval (assemble b m) F) =
      residueExponential q (a*eval (representative b) F) := by
  letI : NeZero q := ⟨hq.ne'⟩
  rw [PrimeSumAdapter.residueExponential_eq_stdAddChar,
    PrimeSumAdapter.residueExponential_eq_stdAddChar]
  simp only [Int.cast_mul,eval_assemble_cast F q hqℓ b m]

section Sums
variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

/-- Reindexing a convergent full-lattice sum by its actual residue and quotient. -/
theorem hasSum_iff (n ℓ : ℕ) (hℓ : 0 < ℓ) (h : (Fin n → ℤ) → E) (s : E) :
    HasSum h s ↔ HasSum (fun p : (Fin n → Fin ℓ) × (Fin n → ℤ) =>
      h (assemble p.1 p.2)) s := by
  simpa only [Function.comp_def,equiv_symm_apply_pair] using
    ((equiv n ℓ hℓ).symm.hasSum_iff (f := h) (a := s)).symm

theorem summable_iff (n ℓ : ℕ) (hℓ : 0 < ℓ) (h : (Fin n → ℤ) → E) :
    Summable h ↔ Summable (fun p : (Fin n → Fin ℓ) × (Fin n → ℤ) =>
      h (assemble p.1 p.2)) := by
  exact exists_congr fun s => hasSum_iff n ℓ hℓ h s

/-- Each individual residue-lattice series converges. -/
theorem summable_residue (n ℓ : ℕ) (hℓ : 0 < ℓ) (h : (Fin n → ℤ) → E)
    (hh : Summable h) (b : Fin n → Fin ℓ) :
    Summable (fun m : Fin n → ℤ => h (assemble b m)) :=
  ((summable_iff n ℓ hℓ h).mp hh).prod_factor b

/-- Exact finite-residue / infinite-quotient regrouping. -/
theorem tsum_eq_sum_tsum (n ℓ : ℕ) (hℓ : 0 < ℓ) (h : (Fin n → ℤ) → E)
    (hh : Summable h) :
    (∑' x : Fin n → ℤ, h x) =
      ∑ b : Fin n → Fin ℓ, ∑' m : Fin n → ℤ, h (assemble b m) := by
  have hs := (summable_iff n ℓ hℓ h).mp hh
  calc
    _ = ∑' p : (Fin n → Fin ℓ) × (Fin n → ℤ), h (assemble p.1 p.2) := by
      simpa only [equiv_symm_apply_pair] using ((equiv n ℓ hℓ).symm.tsum_eq h).symm
    _ = _ := by rw [hs.tsum_prod,tsum_fintype]

/-- A HasSum formulation for the original lattice with the explicit
finite sum of its convergent residue-lattice sums. -/
theorem hasSum_sum_tsum (n ℓ : ℕ) (hℓ : 0 < ℓ) (h : (Fin n → ℤ) → E)
    (hh : Summable h) :
    HasSum h (∑ b : Fin n → Fin ℓ, ∑' m : Fin n → ℤ, h (assemble b m)) := by
  rw [← tsum_eq_sum_tsum n ℓ hℓ h hh]
  exact hh.hasSum

/-- Finite support is enough; no absolute-convergence premise is then needed. -/
theorem finiteSupport_hasSum (n ℓ : ℕ) (hℓ : 0 < ℓ) (h : (Fin n → ℤ) → E)
    (hh : (Function.support h).Finite) :
    HasSum h (∑ b : Fin n → Fin ℓ, ∑' m : Fin n → ℤ, h (assemble b m)) :=
  hasSum_sum_tsum n ℓ hℓ h (summable_of_finite_support hh)

/-- Absolute summability is preserved by exact residue regrouping. -/
theorem norm_tsum_eq_sum_tsum (n ℓ : ℕ) (hℓ : 0 < ℓ) (h : (Fin n → ℤ) → E)
    (hh : Summable (fun x => ‖h x‖)) :
    (∑' x : Fin n → ℤ, ‖h x‖) =
      ∑ b : Fin n → Fin ℓ, ∑' m : Fin n → ℤ, ‖h (assemble b m)‖ :=
  tsum_eq_sum_tsum n ℓ hℓ (fun x => ‖h x‖) hh

end Sums

section Numerators
variable {E : Type*} [AddCommMonoid E]

/-- The interval 1,...,q and canonical representatives differ only at the
endpoints, so endpoint equality suffices for the exact finite sum adapter. -/
theorem sum_Icc_eq_sum_fin (q : ℕ) (hq : 0 < q) (f : ℕ → E) (hf : f q = f 0) :
    (∑ a ∈ Finset.Icc 1 q, f a) = ∑ a : Fin q, f a.val := by
  have hq1 : 1 ≤ q := hq
  have hsplit := Finset.sum_Ico_consecutive f (by omega : 0 ≤ 1) hq1
  have he : f 0 + ∑ a ∈ Finset.Ico 1 q, f a = ∑ a ∈ Finset.range q, f a := by
    simpa only [Nat.Ico_zero_eq_range,Finset.range_one,Finset.sum_singleton] using hsplit
  rw [← Finset.add_sum_Ico_eq_sum_Icc hq1,hf,he]
  exact (Fin.sum_univ_eq_sum_range f q).symm

/-- The coprimality filters agree at the exchanged endpoints, including q=1. -/
theorem sum_Icc_coprime_eq_sum_fin (q : ℕ) (hq : 0 < q) (f : ℕ → E)
    (hf : f q = f 0) :
    (∑ a ∈ Finset.Icc 1 q, if Nat.Coprime a q then f a else 0) =
      ∑ a : Fin q, if Nat.Coprime a.val q then f a.val else 0 := by
  apply sum_Icc_eq_sum_fin q hq
  simp only [Nat.coprime_self,Nat.coprime_zero_left,hf]

/-- q-periodicity supplies the numerator adapter without choosing new
residue representatives or omitting the modulus-one unit. -/
theorem sum_Icc_coprime_eq_sum_fin_of_periodic (q : ℕ) (hq : 0 < q) (f : ℕ → E)
    (hf : Function.Periodic f q) :
    (∑ a ∈ Finset.Icc 1 q, if Nat.Coprime a q then f a else 0) =
      ∑ a : Fin q, if Nat.Coprime a.val q then f a.val else 0 :=
  sum_Icc_coprime_eq_sum_fin q hq f (by simpa only [zero_add] using hf 0)

end Numerators
end CubicTenVariables.IntegerLatticeResidues

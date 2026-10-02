import CubicTenVariables.StratifiedSieveNumerics
import CubicTenVariables.DyadicPowerSum
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Int.Basic

/-! Prefix, pivot and tail of literal modulus tuples. Inactive coordinates
are 1, so the finite ambient index type need not be changed. -/
noncomputable section
namespace CubicTenVariables.StratifiedModuli
open scoped BigOperators

variable {s : ℕ}

def prefixModuli {α : Type*} [One α] (j : Fin s) (q : Fin s → α) (i : Fin s) : α :=
  if i < j then q i else 1

def tail {α : Type*} [One α] (j : Fin s) (q : Fin s → α) (i : Fin s) : α :=
  if j < i then q i else 1

def tailScales (j : Fin s) (R : Fin s → ℝ) : Fin s → ℝ := tail j R

def split (j : Fin s) (q : Fin s → ℕ) : (Fin s → ℕ) × ℕ × (Fin s → ℕ) :=
  (prefixModuli j q,q j,tail j q)

theorem reconstruct {α : Type*} [One α] (j : Fin s) (q q' : Fin s → α)
    (hp : prefixModuli j q=prefixModuli j q') (hm : q j=q' j) (ht : tail j q=tail j q') : q=q' := by
  funext i
  rcases lt_trichotomy i j with hi|rfl|hi
  · simpa only [prefixModuli,if_pos hi] using congrFun hp i
  · exact hm
  · simpa only [tail,if_pos hi] using congrFun ht i

theorem split_injective (j : Fin s) : Function.Injective (split j) := by
  intro q q' h
  exact reconstruct j q q' (congrArg Prod.fst h)
    (congrArg (fun x => x.2.1) h) (congrArg (fun x => x.2.2) h)

theorem card_image_split (j : Fin s) (T : Finset (Fin s → ℕ)) :
    (T.image (split j)).card=T.card := Finset.card_image_of_injective _ (split_injective j)

/-- For fixed tail and pivot modulus, the prefixModuli uniquely identifies a tuple. -/
theorem card_eq_card_prefix_image (j : Fin s) (T : Finset (Fin s → ℕ))
    (t : Fin s → ℕ) (b : ℕ) (ht : ∀ q ∈ T, tail j q=t) (hm : ∀ q ∈ T, q j=b) :
    T.card=(T.image (prefixModuli j)).card := by
  classical
  symm
  apply Finset.card_image_iff.mpr
  intro q hq q' hq' hp
  exact reconstruct j q q' hp ((hm q hq).trans (hm q' hq').symm)
    ((ht q hq).trans (ht q' hq').symm)

theorem prefix_dvd (j : Fin s) (q : Fin s → ℕ) (i : Fin s) : prefixModuli j q i ∣ q i := by
  unfold prefixModuli
  split_ifs
  · exact dvd_rfl
  · exact one_dvd _

theorem tail_dvd (j : Fin s) (q : Fin s → ℕ) (i : Fin s) : tail j q i ∣ q i := by
  unfold tail
  split_ifs
  · exact dvd_rfl
  · exact one_dvd _

theorem prefix_squarefree (j : Fin s) (q : Fin s → ℕ)
    (hq : ∀ i, Squarefree (q i)) : ∀ i, Squarefree (prefixModuli j q i) := by
  intro i
  unfold prefixModuli
  split_ifs
  · exact hq i
  · exact squarefree_one

theorem tail_squarefree (j : Fin s) (q : Fin s → ℕ)
    (hq : ∀ i, Squarefree (q i)) : ∀ i, Squarefree (tail j q i) := by
  intro i
  unfold tail
  split_ifs
  · exact hq i
  · exact squarefree_one

theorem prefix_coprime_modulus (j : Fin s) (q : Fin s → ℕ) (m : ℕ)
    (hq : ∀ i, (q i).Coprime m) : ∀ i, (prefixModuli j q i).Coprime m := by
  intro i
  exact (hq i).of_dvd_left (prefix_dvd j q i)

theorem tail_coprime_modulus (j : Fin s) (q : Fin s → ℕ) (m : ℕ)
    (hq : ∀ i, (q i).Coprime m) : ∀ i, (tail j q i).Coprime m := by
  intro i
  exact (hq i).of_dvd_left (tail_dvd j q i)

theorem prefix_pairwise_coprime (j : Fin s) (q : Fin s → ℕ)
    (hq : Pairwise (fun i k => (q i).Coprime (q k))) :
    Pairwise (fun i k => (prefixModuli j q i).Coprime (prefixModuli j q k)) := by
  intro i k hik
  exact ((hq hik).of_dvd_left (prefix_dvd j q i)).of_dvd_right (prefix_dvd j q k)

theorem tail_pairwise_coprime (j : Fin s) (q : Fin s → ℕ)
    (hq : Pairwise (fun i k => (q i).Coprime (q k))) :
    Pairwise (fun i k => (tail j q i).Coprime (tail j q k)) := by
  intro i k hik
  exact ((hq hik).of_dvd_left (tail_dvd j q i)).of_dvd_right (tail_dvd j q k)

/-- Every individual integral congruence survives after replacing inactive
moduli by 1. -/
theorem tail_equation_dvd (j : Fin s) (q : Fin s → ℕ) (a : Fin s → ℤ)
    (ha : ∀ i, (q i : ℤ) ∣ a i) : ∀ i, ((tail j q i : ℕ) : ℤ) ∣ a i := by
  intro i
  exact (Int.natCast_dvd_natCast.mpr (tail_dvd j q i)).trans (ha i)

theorem prefix_equation_dvd (j : Fin s) (q : Fin s → ℕ) (a : Fin s → ℤ)
    (ha : ∀ i, (q i : ℤ) ∣ a i) : ∀ i, ((prefixModuli j q i : ℕ) : ℤ) ∣ a i := by
  intro i
  exact (Int.natCast_dvd_natCast.mpr (prefix_dvd j q i)).trans (ha i)

theorem tailScales_product (j : Fin s) (R : Fin s → ℝ) :
    (∏ i, tailScales j R i)=StratifiedSieveNumerics.tailProduct R j := rfl

theorem tailScales_one_le (j : Fin s) (R : Fin s → ℝ) (hR : ∀ i, 1 ≤ R i) :
    ∀ i, 1 ≤ tailScales j R i := by
  intro i
  unfold tailScales tail
  split_ifs
  · exact hR i
  · exact le_rfl

theorem tail_dyadic (j : Fin s) (R : Fin s → ℝ) (q : Fin s → ℕ)
    (hq : ∀ i, R i ≤ (q i : ℝ) ∧ (q i : ℝ) ≤ 2*R i) :
    ∀ i, tailScales j R i ≤ ((tail j q i : ℕ) : ℝ) ∧
      ((tail j q i : ℕ) : ℝ) ≤ 2*tailScales j R i := by
  intro i
  unfold tailScales tail
  split_ifs
  · exact hq i
  · norm_num

theorem prefix_dyadic (j : Fin s) (R : Fin s → ℝ) (q : Fin s → ℕ)
    (hq : ∀ i, R i ≤ (q i : ℝ) ∧ (q i : ℝ) ≤ 2*R i) :
    ∀ i, prefixModuli j R i ≤ ((prefixModuli j q i : ℕ) : ℝ) ∧
      ((prefixModuli j q i : ℕ) : ℝ) ≤ 2*prefixModuli j R i := by
  intro i
  unfold prefixModuli
  split_ifs
  · exact hq i
  · norm_num

/-- Actual tail products lie between the scale product and its dyadic
upper bound; the harmless power 2^s also covers inactive coordinates. -/
theorem tail_product_bounds (j : Fin s) (R : Fin s → ℝ) (hR : ∀ i, 1 ≤ R i)
    (q : Fin s → ℕ) (hq : ∀ i, R i ≤ (q i : ℝ) ∧ (q i : ℝ) ≤ 2*R i) :
    StratifiedSieveNumerics.tailProduct R j ≤ (∏ i, ((tail j q i : ℕ) : ℝ)) ∧
      (∏ i, ((tail j q i : ℕ) : ℝ)) ≤ (2 : ℝ)^s*StratifiedSieveNumerics.tailProduct R j := by
  have he := tail_dyadic j R q hq
  constructor
  · rw [← tailScales_product]
    exact Finset.prod_le_prod (fun i _ => zero_le_one.trans (tailScales_one_le j R hR i))
      (fun i _ => (he i).1)
  · calc
      _ ≤ ∏ i, 2*tailScales j R i :=
        Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => (he i).2)
      _ = _ := by simp only [Finset.prod_mul_distrib, tailScales_product, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem coprime_pivot_tail (j : Fin s) (q : Fin s → ℕ)
    (hq : Pairwise (fun i k => (q i).Coprime (q k))) :
    ∀ i, (q j).Coprime (tail j q i) := by
  intro i
  unfold tail
  split_ifs with hi
  · exact hq (ne_of_lt hi)
  · exact Nat.coprime_one_right _

theorem tailScale_product_le_all (j : Fin s) (R : Fin s → ℝ)
    (hR : ∀ i, 1 ≤ R i) : (∏ i, tailScales j R i) ≤ ∏ i, R i := by
  apply Finset.prod_le_prod
  · intro i _
    exact zero_le_one.trans (tailScales_one_le j R hR i)
  · intro i _
    simp only [tailScales, tail]
    split_ifs
    · exact le_rfl
    · exact hR i

theorem scale_le_product (R : Fin s → ℝ) (hR : ∀ i, 1 ≤ R i) (j : Fin s) :
    R j ≤ ∏ i, R i := by
  classical
  calc
    R j = ∏ i : Fin s, if i = j then R j else 1 := by simp
    _ ≤ ∏ i, R i := by
      apply Finset.prod_le_prod
      · intro i _
        split_ifs
        · exact zero_le_one.trans (hR j)
        · exact zero_le_one
      · intro i _
        split_ifs with hi
        · subst i
          exact le_rfl
        · exact hR i

theorem tailScales_rpow_product (j : Fin s) (R e : Fin s → ℝ) :
    (∏ i, (tailScales j R i) ^ e i) =
      ∏ i, if j < i then (R i) ^ e i else 1 := by
  apply Finset.prod_congr rfl
  intro i _
  simp only [tailScales, tail]
  split_ifs <;> simp

end CubicTenVariables.StratifiedModuli

import CubicTenVariables.IntegralEquationCounts
import CubicTenVariables.ResidueBoxCount
import Mathlib.RingTheory.Coprime.Lemmas

/-! Grouping actual integral points by simultaneous modular equation data.
Coprimality is used only to identify the combined progression modulus. -/
noncomputable section
namespace CubicTenVariables.SimultaneousResidueCount
open MvPolynomial IntegralEquationCounts
open scoped BigOperators
variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The actual reductions at the selected moduli, without constructing a
separate CRT representative. -/
def residues (q : ι → ℕ) (x : Fin n → ℤ) : ∀ i, Fin n → ZMod (q i) :=
  fun i j => (x j : ZMod (q i))

theorem cast_eq_iff_dvd (q : ℕ) (a b : ℤ) :
    (a : ZMod q)=(b : ZMod q) ↔ (q : ℤ) ∣ a-b := by
  rw [← sub_eq_zero,← Int.cast_sub,ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- Simultaneous equal residues give the product progression. -/
theorem product_dvd (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (m : ℕ) (hm : ∀ i, m.Coprime (q i)) (a b : ℤ)
    (hbase : (m : ℤ) ∣ a-b) (hq : ∀ i, (a : ZMod (q i))=(b : ZMod (q i))) :
    ((m*∏ i, q i : ℕ) : ℤ) ∣ a-b := by
  have hp : (∏ i, (q i : ℤ)) ∣ a-b :=
    Fintype.prod_dvd_of_coprime (fun i j hij => (hcop hij).isCoprime)
      (fun i => (cast_eq_iff_dvd (q i) a b).mp (hq i))
  have hc : IsCoprime (m : ℤ) (∏ i, (q i : ℤ)) :=
    IsCoprime.prod_right (fun i _ => (hm i).isCoprime)
  simpa only [Nat.cast_mul,Nat.cast_prod] using hc.mul_dvd hbase hp

/-- The number of occurring residue tuples is at most the product of the
literal common-zero counts. Compatibility with the fixed progression may
reduce this number, so no CRT surjectivity is needed. -/
theorem card_residue_image_le (t : ι → ℕ)
    (G : ∀ i, Fin (t i) → MvPolynomial (Fin n) ℤ)
    (q : ι → ℕ) [∀ i, NeZero (q i)] (S : Finset (Fin n → ℤ))
    (hzero : ∀ x ∈ S, ∀ i j, (q i : ℤ) ∣ eval x (G i j)) :
    (S.image (residues q)).card ≤ ∏ i, zeroCount (G i) (q i) := by
  classical
  let Z (i : ι) : Finset (Fin n → ZMod (q i)) :=
    Finset.univ.filter fun x => ∀ j, eval₂ (Int.castRingHom (ZMod (q i))) x (G i j)=0
  have hZ (i : ι) : (Z i).card=zeroCount (G i) (q i) := by
    simp only [Z,zeroCount,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have hsub : S.image (residues q) ⊆ Fintype.piFinset Z := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro j
    change eval₂ (Int.castRingHom (ZMod (q i))) (fun k => (x k : ZMod (q i))) (G i j)=0
    calc
      _ = (eval x (G i j) : ZMod (q i)) :=
        (eval₂_comp (Int.castRingHom (ZMod (q i))) x (G i j)).symm
      _ = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hzero x hx i j)
  calc
    _ ≤ (Fintype.piFinset Z).card := Finset.card_le_card hsub
    _ = ∏ i, zeroCount (G i) (q i) := by rw [Fintype.card_piFinset]; simp only [hZ]

/-- The source progression hypothesis, stated for every finite subset of U.
It is an explicit hypothesis of the stratified sieve, not a literature input. -/
def ProgressionBound (U : Set (Fin n → ℤ)) (α ε A : ℝ) : Prop :=
  ∀ (u : Fin n → ℝ) (L : ℝ), 1 ≤ L → ∀ (m : ℕ), 0 < m →
    ∀ (b : Fin n → ℤ) (S : Finset (Fin n → ℤ)),
    (∀ x ∈ S, x ∈ U) → (∀ x ∈ S, ∀ i, |(x i : ℝ)-u i| ≤ L) →
    (∀ x ∈ S, ∀ i, (m : ℤ) ∣ x i-b i) →
    (S.card : ℝ) ≤ A*(L+‖u‖)^ε*(1+L/(m : ℝ))^α

/-- The progression hypothesis applied after grouping by actual equation
residues. The combined modulus includes the original progression modulus. -/
theorem card_le_of_progression (t : ι → ℕ)
    (G : ∀ i, Fin (t i) → MvPolynomial (Fin n) ℤ)
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (m : ℕ) (hm : 0 < m) (hmq : ∀ i, m.Coprime (q i))
    (U : Set (Fin n → ℤ)) (α ε A : ℝ) (hA : 0 ≤ A)
    (hU : ProgressionBound U α ε A)
    (u : Fin n → ℝ) (L : ℝ) (hL : 1 ≤ L)
    (b : Fin n → ℤ) (S : Finset (Fin n → ℤ))
    (hmem : ∀ x ∈ S, x ∈ U)
    (hbox : ∀ x ∈ S, ∀ i, |(x i : ℝ)-u i| ≤ L)
    (hres : ∀ x ∈ S, ∀ i, (m : ℤ) ∣ x i-b i)
    (hzero : ∀ x ∈ S, ∀ i j, (q i : ℤ) ∣ eval x (G i j)) :
    (S.card : ℝ) ≤ A*(L+‖u‖)^ε*(1+L/(m*∏ i, q i : ℕ))^α*
      ((∏ i, zeroCount (G i) (q i) : ℕ) : ℝ) := by
  classical
  let M := m*∏ i, q i
  have hM : 0 < M := Nat.mul_pos hm (Finset.prod_pos fun i _ => NeZero.pos (q i))
  let B : ℝ := A*(L+‖u‖)^ε*(1+L/(M : ℝ))^α
  have hB : 0 ≤ B := by
    apply mul_nonneg (mul_nonneg hA (Real.rpow_nonneg (by linarith [norm_nonneg u]) _))
    exact Real.rpow_nonneg (by positivity) _
  have hfiber (y) (hy : y ∈ S.image (residues q)) :
      ((S.filter fun x => residues q x=y).card : ℝ) ≤ B := by
    obtain ⟨z,hz,hzy⟩ := Finset.mem_image.mp hy
    apply hU u L hL M hM z _
    · intro x hx
      exact hmem x (Finset.mem_filter.mp hx).1
    · intro x hx
      exact hbox x (Finset.mem_filter.mp hx).1
    · intro x hx j
      have he := (Finset.mem_filter.mp hx).2.trans hzy.symm
      exact product_dvd q hcop m hmq (x j) (z j)
        (by simpa only [sub_sub_sub_cancel_right] using
          dvd_sub (hres x (Finset.mem_filter.mp hx).1 j) (hres z hz j))
        (fun i => congrFun (congrFun he i) j)
  calc
    (S.card : ℝ) = ∑ y ∈ S.image (residues q), ((S.filter fun x => residues q x=y).card : ℝ) := by
      rw [Finset.card_eq_sum_card_image (residues q) S,Nat.cast_sum]
    _ ≤ ∑ _y ∈ S.image (residues q), B := Finset.sum_le_sum hfiber
    _ = B*((S.image (residues q)).card : ℝ) := by simp [mul_comm]
    _ ≤ B*((∏ i, zeroCount (G i) (q i) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast card_residue_image_le t G q S hzero) hB

end CubicTenVariables.SimultaneousResidueCount

import CubicTenVariables.TerminalCubicCRT
import CubicTenVariables.FlexibleLiftingSmith
import CubicTenVariables.SmithProfileMassBound
import CubicTenVariables.PolynomialRootProductCRT

/-! Exact finite CRT factorization of terminal maxima, with the same global
coefficient in every local factor. -/

noncomputable section
namespace CubicTenVariables.TerminalProfileProduct
open MvPolynomial HessianTheorem11 TerminalCubicSum SecondLiftSum FlexibleLifting
open scoped BigOperators

private instance prodNeZero {ι : Type*} (s : Finset ι) (q : ι → ℕ)
    [∀ i, NeZero (q i)] : NeZero (∏ i ∈ s, q i) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (q i))⟩

/-- Modulus one contributes one, including in zero variables. -/
@[simp] theorem terminalMax_one {n : ℕ}
    (F : MvPolynomial (Fin n) (ZMod 1)) (A : ZMod 1) (y : Fin n → ZMod 1) :
    terminalMax 1 F A y = 1 := by
  obtain ⟨u, ell, h⟩ := terminalMax_attained 1 F A y
  rw [h]
  have hz (z : Fin n → ZMod 1) : terminalPhase F A ell (u : ZMod 1) y z = 0 :=
    Subsingleton.elim _ _
  simp [terminalSum, hz]

/-- The empty prime family has one root and terminal value one. -/
@[simp] theorem zeroFiberTerminalTotal_one {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) : zeroFiberTerminalTotal F 1 1 = 1 := by
  classical
  simp [zeroFiberTerminalTotal, residueTerminalMax]

/-- Transport only the modulus, without changing any integer data. -/
theorem terminalMax_modulus_congr {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (A : ℤ) (y : Fin n → ℤ) (M N : ℕ) [NeZero M] [NeZero N] (h : M = N) :
    terminalMax M (map (Int.castRingHom (ZMod M)) F) (A : ZMod M)
      (fun j => (y j : ZMod M)) =
    terminalMax N (map (Int.castRingHom (ZMod N)) F) (A : ZMod N)
      (fun j => (y j : ZMod N)) := by
  subst N
  rfl

/-- The integer coefficient and center are unchanged in every CRT factor. -/
theorem terminalMax_prod {ι : Type*} {n : ℕ} (s : Finset ι) (q : ι → ℕ)
    [∀ i, NeZero (q i)]
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (q i).Coprime (q j))
    (F : MvPolynomial (Fin n) ℤ) (A : ℤ) (y : Fin n → ℤ) :
    terminalMax (∏ i ∈ s, q i)
      (map (Int.castRingHom (ZMod (∏ i ∈ s, q i))) F)
      (A : ZMod (∏ i ∈ s, q i)) (fun j => (y j : ZMod (∏ i ∈ s, q i))) =
      ∏ i ∈ s, terminalMax (q i) (map (Int.castRingHom (ZMod (q i))) F)
        (A : ZMod (q i)) (fun j => (y j : ZMod (q i))) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hcop' : ∀ k ∈ s, ∀ j ∈ s, k ≠ j → (q k).Coprime (q j) :=
      fun k hk j hj hkj => hcop k (Finset.mem_insert_of_mem hk)
        j (Finset.mem_insert_of_mem hj) hkj
    have hc : (q i).Coprime (∏ j ∈ s, q j) := Nat.Coprime.prod_right
      (fun j hj => hcop i (Finset.mem_insert_self i s) j
        (Finset.mem_insert_of_mem hj) (by intro he; subst j; exact hi hj))
    calc
      _ = terminalMax (q i * ∏ j ∈ s, q j)
          (map (Int.castRingHom (ZMod (q i * ∏ j ∈ s, q j))) F)
          (A : ZMod (q i * ∏ j ∈ s, q j))
          (fun j => (y j : ZMod (q i * ∏ j ∈ s, q j))) :=
        terminalMax_modulus_congr F A y _ _ (Finset.prod_insert hi)
      _ = _ := by
        rw [TerminalCubicCRT.terminalMax_crt hc, ih hcop', Finset.prod_insert hi]

/-- A local terminal factor is bounded by the canonical residue profile.
The coefficient is the global A, not the local prime power. -/
theorem terminalMax_le_actualProfile
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (p : ℕ) [Fact p.Prime] (a t : ℕ) (A : ℕ) (y : Fin 10 → ℤ)
    (hA : p^a ∣ A) (hcase : t ≤ a ∨ p ≠ 2) :
    terminalMax (p^t) (map (Int.castRingHom (ZMod (p^t))) F)
      (A : ZMod (p^t)) (fun i => (y i : ZMod (p^t))) ≤
      (p : ℝ)^(((10*t : ℕ) : ℝ) -
        (SmithProfileNumerics.penalty
          (SmithProfileMassBound.actualProfile F p a (fun i => (y i : ZMod (p^a)))) t : ℝ)) := by
  obtain ⟨U,V,d,hD⟩ := MatrixSmithExistence.exists_integer_diagonalization (hessian F y)
  rw [SmithProfileMassBound.actualProfile_eq_ofDiagonal F p Fact.out a y U V d hD]
  have hA' : ((p^a : ℕ) : ℤ) ∣ (A : ℤ) := by exact_mod_cast hA
  simpa only [Int.cast_natCast] using
    TerminalSmithBound.terminalMax_ten_le_profile_penalty
      F hF y U V d hD p Fact.out a t hcase (A : ℤ) hA'

/-- CRT followed by the actual local profile bounds. -/
theorem terminalMax_le_prod_profiles {ι : Type*} [Fintype ι]
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hp : Function.Injective p)
    (a t : ι → ℕ) (A : ℕ) (y : Fin 10 → ℤ)
    (hA : ∀ i, p i ^ a i ∣ A) (hcase : ∀ i, t i ≤ a i ∨ p i ≠ 2) :
    terminalMax (∏ i, p i ^ t i)
      (map (Int.castRingHom (ZMod (∏ i, p i ^ t i))) F)
      (A : ZMod (∏ i, p i ^ t i)) (fun j => (y j : ZMod (∏ i, p i ^ t i))) ≤
      ∏ i, (p i : ℝ)^(((10*t i : ℕ) : ℝ) -
        (SmithProfileNumerics.penalty
          (SmithProfileMassBound.actualProfile F (p i) (a i)
            (fun j => (y j : ZMod (p i ^ a i)))) (t i) : ℝ)) := by
  classical
  have hc : ∀ i ∈ (Finset.univ : Finset ι), ∀ j ∈ Finset.univ,
      i ≠ j → (p i ^ t i).Coprime (p j ^ t j) :=
    fun i _ j _ hij => Nat.coprime_pow_primes _ _ Fact.out Fact.out (fun h => hij (hp h))
  have he := terminalMax_prod Finset.univ (fun i => p i ^ t i) hc F (A : ℤ) y
  simp only [Int.cast_natCast] at he
  rw [he]
  apply Finset.prod_le_prod
  · intro i _
    exact terminalMax_nonneg _ _ _ _
  · intro i _
    simpa only [Int.cast_natCast] using terminalMax_le_actualProfile F hF
      (p i) (a i) (t i) A y (hA i) (hcase i)

/-- The literal composite zero-fiber total is bounded by the product of
actual local weighted root masses. The prime labels are distinct; both
moduli use this same finite family, permitting zero exponents and the
empty family. No anisotropy or literature hypothesis is needed. -/
theorem zeroFiberTerminalTotal_le_prod_profileMass {ι : Type*} [Fintype ι]
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hp : Function.Injective p)
    (a t : ι → ℕ) (hcase : ∀ i, t i ≤ a i ∨ p i ≠ 2) :
    zeroFiberTerminalTotal F (∏ i, p i ^ a i) (∏ i, p i ^ t i) ≤
      ∏ i, SmithProfileMassBound.profileMass F (p i) (a i) (t i) := by
  classical
  let w (i : ι) (z : Fin 10 → ZMod (p i ^ a i)) : ℝ :=
    (p i : ℝ)^(((10*t i : ℕ) : ℝ) -
      (SmithProfileNumerics.penalty
        (SmithProfileMassBound.actualProfile F (p i) (a i) z) (t i) : ℝ))
  have hc : Pairwise fun i j => (p i ^ a i).Coprime (p j ^ a j) :=
    fun i j hij => Nat.coprime_pow_primes _ _ Fact.out Fact.out (fun h => hij (hp h))
  calc
    _ ≤ ∑ y : Fin 10 → Fin (∏ i, p i ^ a i),
        if (((∏ i, p i ^ a i : ℕ) : ℤ) ∣ eval (integerVector y) F) then
          ∏ i, w i (fun j => ((y j).val : ZMod (p i ^ a i))) else 0 := by
      unfold zeroFiberTerminalTotal
      apply Finset.sum_le_sum
      intro y _
      split_ifs
      · have hdiv : ∀ i, p i ^ a i ∣ ∏ j, p j ^ a j :=
          fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
        simpa only [residueTerminalMax, integerVector, Int.cast_natCast, w] using
          terminalMax_le_prod_profiles F hF p hp a t (∏ i, p i ^ a i)
            (integerVector y) hdiv hcase
      · rfl
    _ = _ := by
      simpa only [SmithProfileMassBound.profileMass, w] using
        PolynomialRootProductCRT.sum_roots_fin_product (fun i => p i ^ a i) hc F w

end CubicTenVariables.TerminalProfileProduct


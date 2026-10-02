import CubicTenVariables.SimultaneousResidueCount
import CubicTenVariables.TranslatedGeometricSievePairs

/-! One translated geometric sieve after grouping by the residues at a
coprime family of other moduli. The selected sieve modulus is still summed. -/
noncomputable section
namespace CubicTenVariables.SievedResidueCount
open MvPolynomial IntegralEquationCounts IntegralLinearNormalization
open SimultaneousResidueCount TranslatedGeometricSievePairs
open scoped BigOperators
variable {n s r : ℕ}

theorem exists_bound {J : Ideal (MvPolynomial (Fin n) ℤ)} (D : Certificate J r)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c K : ℝ, 1 ≤ c ∧ 1 ≤ K ∧
      ∀ (t : Fin s → ℕ) (G : ∀ i, Fin (t i) → MvPolynomial (Fin n) ℤ)
        (q : Fin s → ℕ) [∀ i, NeZero (q i)],
      Pairwise (fun i j => (q i).Coprime (q j)) →
      ∀ (m : ℕ), 0 < m → (∀ i, m.Coprime (q i)) →
      ∀ (u : Fin n → ℝ) (L : ℝ), 1 ≤ L →
      ∀ (b : Fin n → ℤ) (R : ℝ), c*(1+L/(m*∏ i, q i : ℕ)) ≤ R →
      ∀ E : Finset (ℕ × (Fin n → ℤ)),
      (∀ p ∈ E, ValidPair J u L m b R p) →
      (∀ p ∈ E, ∀ i, p.1.Coprime (q i)) →
      (∀ p ∈ E, ∀ i j, (q i : ℤ) ∣ eval p.2 (G i j)) →
      (E.card : ℝ) ≤ K*(L*R+‖u‖)^ε*(1+L/(m*∏ i, q i : ℕ))^(r+1)*
        ((∏ i, zeroCount (G i) (q i) : ℕ) : ℝ) := by
  classical
  obtain ⟨c,K,hc,hK,hbound⟩ := exists_pair_bound_of_certificate D ε hε
  refine ⟨c,K,hc,hK,?_⟩
  intro t G q hq hcop m hm hmq u L hL b R hR E hE hcopE hzero
  let M := m*∏ i, q i
  have hM : 0 < M := Nat.mul_pos hm (Finset.prod_pos fun i _ => NeZero.pos (q i))
  let B : ℝ := K*(L*R+‖u‖)^ε*(1+L/(M : ℝ))^(r+1)
  let key (p : ℕ × (Fin n → ℤ)) := residues q p.2
  have hR0 : 0 ≤ R := by
    have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
    have hv : 0 ≤ L/(M : ℝ) := div_nonneg (by linarith) hMreal.le
    change c*(1+L/(M : ℝ)) ≤ R at hR
    nlinarith
  have hB : 0 ≤ B := by positivity
  have hfiber (y) (hy : y ∈ E.image key) :
      ((E.filter fun p => key p=y).card : ℝ) ≤ B := by
    obtain ⟨z,hz,hzy⟩ := Finset.mem_image.mp hy
    apply hbound u L hL M hM z.2 R hR
    intro p hp
    have hpE := (Finset.mem_filter.mp hp).1
    have hv := hE p hpE
    have he := (Finset.mem_filter.mp hp).2.trans hzy.symm
    refine ⟨hv.1,?_,hv.2.2.1,hv.2.2.2.1,hv.2.2.2.2.1,?_,hv.2.2.2.2.2.2⟩
    · exact hv.2.1.mul_right (Nat.Coprime.prod_right fun i _ => hcopE p hpE i)
    · intro j
      exact product_dvd q hcop m hmq (p.2 j) (z.2 j)
        (by simpa only [sub_sub_sub_cancel_right] using
          dvd_sub (hv.2.2.2.2.2.1 j) ((hE z hz).2.2.2.2.2.1 j))
        (fun i => congrFun (congrFun he i) j)
  have hcount : (E.image key).card ≤ ∏ i, zeroCount (G i) (q i) := by
    have he : (E.image Prod.snd).image (residues q)=E.image key := by
      rw [Finset.image_image]
      rfl
    rw [← he]
    apply card_residue_image_le t G q
    intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    exact hzero p hp
  calc
    (E.card : ℝ) = ∑ y ∈ E.image key, ((E.filter fun p => key p=y).card : ℝ) := by
      rw [Finset.card_eq_sum_card_image key E,Nat.cast_sum]
    _ ≤ ∑ _y ∈ E.image key, B := Finset.sum_le_sum hfiber
    _ = B*((E.image key).card : ℝ) := by simp [mul_comm]
    _ ≤ B*((∏ i, zeroCount (G i) (q i) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hcount) hB

end CubicTenVariables.SievedResidueCount

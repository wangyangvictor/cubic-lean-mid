import CubicTenVariables.StratifiedSieveData
import CubicTenVariables.StratifiedModuli
import CubicTenVariables.StratifiedPrefixElimination
import CubicTenVariables.SievedResidueCount
import CubicTenVariables.SquarefreeEquationCount

/-! The large-product sieve on one literal tail slice. All modulus tuple
multiplicity, modular point counts and progression regrouping are internal. -/
noncomputable section
namespace CubicTenVariables.StratifiedLargeSlice
open MvPolynomial IntegralLinearNormalization StratifiedSieveData StratifiedModuli
open scoped BigOperators
variable {n s : ℕ}

theorem exists_bound (t d : Fin s → ℕ)
    (G : ∀ i, Fin (t i) → MvPolynomial (Fin n) ℤ)
    (hproper : ∀ i, IntegralModelDimension.rationalIdeal (G i) ≠ ⊤)
    (hdim : ∀ i, ringKrullDim (MvPolynomial (Fin n) ℚ ⧸
      IntegralModelDimension.rationalIdeal (G i)) ≤ (d i : WithBot ℕ∞))
    (j : Fin s) (D : Certificate (ideal t G j) (d j)) (η : ℝ) (hη : 0 < η) :
    ∃ c K : ℝ, 1 ≤ c ∧ 1 ≤ K ∧ ∀ (R : Fin s → ℝ), (∀ i, 1 ≤ R i) →
      ∀ (U : Set (Fin n → ℤ)) (u : Fin n → ℝ) (L : ℝ), 1 ≤ L →
      ∀ (m : ℕ), 0 < m → ∀ (b : Fin n → ℤ) (a : Fin s → ℕ),
      c*(1+L/(m*∏ i, a i : ℕ)) ≤ R j →
      ∀ E : Finset ((Fin s → ℕ) × (Fin n → ℤ)),
      (∀ p ∈ E, ValidTuple t G U u L m b R p) →
      (∀ p ∈ E, tail j p.1=a) →
      (E.card : ℝ) ≤ K*(L+‖u‖)^η*(L*R j+‖u‖)^η*
        (1+L/(m*∏ i, a i : ℕ))^(d j+1)*∏ i, (a i : ℝ)^((d i : ℝ)+η) := by
  classical
  obtain ⟨B,hB,hprefix⟩ := StratifiedPrefixElimination.exists_uniform_bound (ideal t G) η hη
  obtain ⟨c,K,hc,hK,hsieve⟩ := SievedResidueCount.exists_bound (s := s) D η hη
  choose A hA hcount using fun i => SquarefreeEquationCount.exists_uniform_bound
    (d := d i) (G i) (hproper i) (hdim i) η hη
  have hprodA : 1 ≤ ∏ i, A i := by
    simpa using Finset.prod_le_prod (s := Finset.univ) (f := fun _i : Fin s => (1:ℝ))
      (fun _ _ => zero_le_one) (fun i _ => hA i)
  refine ⟨c,B*K*(∏ i, A i),hc,one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hB hK) hprodA,?_⟩
  intro R hR U u L hL m hm b a hthreshold E hE htail
  have hRj : 1 ≤ R j := hR j
  rcases E.eq_empty_or_nonempty with he | he
  · subst E
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity
  obtain ⟨z,hz⟩ := he
  have hza := htail z hz
  have ha : ∀ i, Squarefree (a i) := by
    rw [← hza]
    exact tail_squarefree j z.1 (hE z hz).squarefree
  letI (i : Fin s) : NeZero (a i) := ⟨(ha i).ne_zero⟩
  have hacop : Pairwise (fun i k => (a i).Coprime (a k)) := by
    rw [← hza]
    exact tail_pairwise_coprime j z.1 (hE z hz).coprime
  have hma : ∀ i, m.Coprime (a i) := by
    intro i
    rw [← hza]
    exact ((hE z hz).base_coprime i).of_dvd_right (tail_dvd j z.1 i)
  let P := E.image (fun p => (p.1 j,p.2))
  have hP : ∀ p ∈ P, TranslatedGeometricSievePairs.ValidPair (ideal t G j) u L m b (R j) p := by
    intro p hp
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hp
    have hv := hE w hw
    exact ⟨hv.squarefree j,(hv.base_coprime j).symm,(hv.dyadic j).1,(hv.dyadic j).2,
      hv.box,hv.progression,hv.outside j,hv.equations j⟩
  have hPivotCoprime : ∀ p ∈ P, ∀ i, p.1.Coprime (a i) := by
    intro p hp i
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hp
    rw [← htail w hw]
    exact coprime_pivot_tail j w.1 (hE w hw).coprime i
  have hPzero : ∀ p ∈ P, ∀ i k, (a i : ℤ) ∣ eval p.2 (G i k) := by
    intro p hp i k
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hp
    rw [← htail w hw]
    exact (Int.natCast_dvd_natCast.mpr (tail_dvd j w.1 i)).trans
      ((hE w hw).generator_equations i k)
  have hpivot := hsieve t G a hacop m hm hma u L hL b (R j) hthreshold P hP hPivotCoprime hPzero
  have hePrefix := hprefix j u L hL E (fun p hp => (hE p hp).box)
    (fun p hp => (hE p hp).outside)
    (fun p hp i => Nat.pos_of_ne_zero ((hE p hp).squarefree i).ne_zero)
    (fun p hp => (hE p hp).equations)
  have hzcount : ((∏ i, IntegralEquationCounts.zeroCount (G i) (a i) : ℕ) : ℝ) ≤
      (∏ i, A i)*(∏ i, (a i : ℝ)^((d i : ℝ)+η)) := by
    rw [Nat.cast_prod,← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => hcount i (a i) (ha i))
  have hn : 0 ≤ K*(L*R j+‖u‖)^η*(1+L/(m*∏ i, a i : ℕ))^(d j+1) := by
    positivity
  have hfinal := hpivot.trans (mul_le_mul_of_nonneg_left hzcount hn)
  calc
    (E.card : ℝ) ≤ B*(L+‖u‖)^η*(P.card : ℝ) := hePrefix
    _ ≤ B*(L+‖u‖)^η*(K*(L*R j+‖u‖)^η*(1+L/(m*∏ i, a i : ℕ))^(d j+1)*
        ((∏ i, A i)*(∏ i, (a i : ℝ)^((d i : ℝ)+η)))) :=
      mul_le_mul_of_nonneg_left hfinal (by positivity)
    _ = _ := by ring

end CubicTenVariables.StratifiedLargeSlice

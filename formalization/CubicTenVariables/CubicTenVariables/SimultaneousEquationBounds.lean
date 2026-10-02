import CubicTenVariables.SimultaneousResidueCount
import CubicTenVariables.SquarefreeEquationCount

/-! Uniform squarefree equation counts inserted into the simultaneous
progression count. All geometric constants precede the moduli. -/
noncomputable section
namespace CubicTenVariables.SimultaneousEquationBounds
open MvPolynomial IntegralEquationCounts SimultaneousResidueCount
open scoped BigOperators
variable {n s : ℕ}

theorem exists_bound (t d : Fin s → ℕ)
    (G : ∀ i, Fin (t i) → MvPolynomial (Fin n) ℤ)
    (hproper : ∀ i, IntegralModelDimension.rationalIdeal (G i) ≠ ⊤)
    (hdim : ∀ i, ringKrullDim (MvPolynomial (Fin n) ℚ ⧸
      IntegralModelDimension.rationalIdeal (G i)) ≤ (d i : WithBot ℕ∞))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (q : Fin s → ℕ),
      (∀ i, Squarefree (q i)) →
      Pairwise (fun i j => (q i).Coprime (q j)) →
      ∀ (m : ℕ), 0 < m → (∀ i, m.Coprime (q i)) →
      ∀ (U : Set (Fin n → ℤ)) (α η A : ℝ), 0 ≤ A → ProgressionBound U α η A →
      ∀ (u : Fin n → ℝ) (L : ℝ), 1 ≤ L →
      ∀ (b : Fin n → ℤ) (S : Finset (Fin n → ℤ)),
      (∀ x ∈ S, x ∈ U) → (∀ x ∈ S, ∀ i, |(x i : ℝ)-u i| ≤ L) →
      (∀ x ∈ S, ∀ i, (m : ℤ) ∣ x i-b i) →
      (∀ x ∈ S, ∀ i j, (q i : ℤ) ∣ eval x (G i j)) →
      (S.card : ℝ) ≤ A*B*(L+‖u‖)^η*(1+L/(m*∏ i, q i : ℕ))^α*
        ∏ i, (q i : ℝ)^((d i : ℝ)+δ) := by
  classical
  choose K hK hcount using fun i => SquarefreeEquationCount.exists_uniform_bound
    (d := d i) (G i) (hproper i) (hdim i) δ hδ
  have hK0 (i) : 0 ≤ K i := zero_le_one.trans (hK i)
  have hprod : 1 ≤ ∏ i, K i := by
    simpa using Finset.prod_le_prod (s := Finset.univ)
      (f := fun _i : Fin s => (1 : ℝ)) (fun _ _ => zero_le_one) (fun i _ => hK i)
  refine ⟨∏ i, K i,hprod,?_⟩
  intro q hq hcop m hm hmq U α η A hA hU u L hL b S hmem hbox hres hzero
  letI (i : Fin s) : NeZero (q i) := ⟨(hq i).ne_zero⟩
  have h := card_le_of_progression t G q hcop m hm hmq U α η A hA hU u L hL b S
    hmem hbox hres hzero
  have hz : ((∏ i, zeroCount (G i) (q i) : ℕ) : ℝ) ≤
      (∏ i, K i)*(∏ i, (q i : ℝ)^((d i : ℝ)+δ)) := by
    rw [Nat.cast_prod,← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => hcount i (q i) (hq i))
  have hM : 0 ≤ A*(L+‖u‖)^η*(1+L/(m*∏ i, q i : ℕ))^α := by positivity
  exact h.trans (by
    have he := mul_le_mul_of_nonneg_left hz hM
    convert he using 1
    ring)

/-- Summing actual modulus-tuples retains the literal product modulus in
its progression factor. The tuple set may impose further restrictions. -/
theorem exists_tuple_bound (t d : Fin s → ℕ)
    (G : ∀ i, Fin (t i) → MvPolynomial (Fin n) ℤ)
    (hproper : ∀ i, IntegralModelDimension.rationalIdeal (G i) ≠ ⊤)
    (hdim : ∀ i, ringKrullDim (MvPolynomial (Fin n) ℚ ⧸
      IntegralModelDimension.rationalIdeal (G i)) ≤ (d i : WithBot ℕ∞))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (m : ℕ), 0 < m →
      ∀ (U : Set (Fin n → ℤ)) (α η A : ℝ), 0 ≤ A → ProgressionBound U α η A →
      ∀ (u : Fin n → ℝ) (L : ℝ), 1 ≤ L → ∀ (b : Fin n → ℤ)
        (E : Finset ((Fin s → ℕ) × (Fin n → ℤ))),
      (∀ p ∈ E, ∀ i, Squarefree (p.1 i)) →
      (∀ p ∈ E, Pairwise (fun i j => (p.1 i).Coprime (p.1 j))) →
      (∀ p ∈ E, ∀ i, m.Coprime (p.1 i)) →
      (∀ p ∈ E, p.2 ∈ U) → (∀ p ∈ E, ∀ i, |(p.2 i : ℝ)-u i| ≤ L) →
      (∀ p ∈ E, ∀ i, (m : ℤ) ∣ p.2 i-b i) →
      (∀ p ∈ E, ∀ i j, (p.1 i : ℤ) ∣ eval p.2 (G i j)) →
      (E.card : ℝ) ≤ A*B*(L+‖u‖)^η*∑ q ∈ E.image Prod.fst,
        (1+L/(m*∏ i, q i : ℕ))^α*(∏ i, (q i : ℝ)^((d i : ℝ)+δ)) := by
  classical
  obtain ⟨B,hB,hbound⟩ := exists_bound t d G hproper hdim δ hδ
  refine ⟨B,hB,?_⟩
  intro m hm U α η A hA hU u L hL b E hsquare hcop hmq hmem hbox hres hzero
  have hfiber (q) (hq : q ∈ E.image Prod.fst) :
      ((E.filter fun p => p.1=q).card : ℝ) ≤
        A*B*(L+‖u‖)^η*((1+L/(m*∏ i, q i : ℕ))^α*
          (∏ i, (q i : ℝ)^((d i : ℝ)+δ))) := by
    obtain ⟨z,hz,hzq⟩ := Finset.mem_image.mp hq
    let T := E.filter fun p => p.1=q
    have hinj : Set.InjOn Prod.snd (T : Set ((Fin s → ℕ) × (Fin n → ℤ))) := by
      intro p hp w hw he
      exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hw).2.symm) he
    have heq : (T.image Prod.snd).card=T.card := Finset.card_image_of_injOn hinj
    have hqS : ∀ i, Squarefree (q i) := by simpa only [← hzq] using hsquare z hz
    have hqC : Pairwise (fun i j => (q i).Coprime (q j)) := by
      simpa only [← hzq] using hcop z hz
    have hqm : ∀ i, m.Coprime (q i) := by simpa only [← hzq] using hmq z hz
    have he := hbound q hqS hqC m hm hqm U α η A hA hU u L hL b
      (T.image Prod.snd) (by
        intro x hx
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
        exact hmem p (Finset.mem_filter.mp hp).1) (by
        intro x hx
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
        exact hbox p (Finset.mem_filter.mp hp).1) (by
        intro x hx
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
        exact hres p (Finset.mem_filter.mp hp).1) (by
        intro x hx
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
        have hpq := (Finset.mem_filter.mp hp).2
        simpa only [hpq] using hzero p (Finset.mem_filter.mp hp).1)
    rw [heq] at he
    simpa only [mul_assoc] using he
  calc
    (E.card : ℝ) = ∑ q ∈ E.image Prod.fst, ((E.filter fun p => p.1=q).card : ℝ) := by
      rw [Finset.card_eq_sum_card_image Prod.fst E,Nat.cast_sum]
    _ ≤ ∑ q ∈ E.image Prod.fst, A*B*(L+‖u‖)^η*
        ((1+L/(m*∏ i, q i : ℕ))^α*(∏ i, (q i : ℝ)^((d i : ℝ)+δ))) :=
      Finset.sum_le_sum hfiber
    _ = _ := by rw [Finset.mul_sum]

end CubicTenVariables.SimultaneousEquationBounds

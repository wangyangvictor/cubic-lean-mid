import CubicTenVariables.TranslatedGeometricSieve
import CubicTenVariables.GeometricSievePairCount

/-! The actual squarefree modulus--point pair count outside the original
integral zero locus. The constants precede all box and progression data. -/
noncomputable section
namespace CubicTenVariables.TranslatedGeometricSievePairs
open MvPolynomial IntegralLinearNormalization TranslatedGeometricSieve
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- Literal data of a pair appearing in the source sieve. -/
def ValidPair (J : Ideal (MvPolynomial (Fin n) ℤ)) (u : Fin n → ℝ)
    (L : ℝ) (m : ℕ) (b : Fin n → ℤ) (S0 : ℝ) (p : ℕ × (Fin n → ℤ)) : Prop :=
  Squarefree p.1 ∧ p.1.Coprime m ∧ S0 ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ 2*S0 ∧
    (∀ i, |(p.2 i : ℝ)-u i| ≤ L) ∧ (∀ i, (m : ℤ) ∣ p.2 i-b i) ∧
    (∃ f ∈ J, eval p.2 f ≠ 0) ∧ ∀ f ∈ J, (p.1 : ℤ) ∣ eval p.2 f

theorem exists_pair_bound_of_certificate
    {J : Ideal (MvPolynomial (Fin n) ℤ)} {r : ℕ} (D : Certificate J r)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c K : ℝ, 1 ≤ c ∧ 1 ≤ K ∧
      ∀ (u : Fin n → ℝ) (L : ℝ), 1 ≤ L → ∀ (m : ℕ), 0 < m →
      ∀ (b : Fin n → ℤ) (S0 : ℝ), c*(1+L/(m : ℝ)) ≤ S0 →
      ∀ E : Finset (ℕ × (Fin n → ℤ)),
      (∀ p ∈ E, ValidPair J u L m b S0 p) →
      (E.card : ℝ) ≤ K*(L*S0+‖u‖)^ε*(1+L/(m : ℝ))^(r+1) := by
  classical
  obtain ⟨c,K,hc,hK,hbound⟩ := exists_admissible_bound_of_certificate D (ε/2) (by positivity)
  obtain ⟨C,hC,hdivisor⟩ := GeometricSievePairCount.exists_uniform_bound J (ε/2) (by positivity)
  refine ⟨c,C*K,hc,one_le_mul_of_one_le_of_one_le hC hK,?_⟩
  intro u L hL m hm b S0 hS0 E hE
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hratio : 0 ≤ L/(m : ℝ) := div_nonneg (by linarith) hmR.le
  have hS01 : 1 ≤ S0 := by nlinarith
  have hp0 (p) (hp : p ∈ E) : 0 < p.1 := by
    have he : (0 : ℝ) < (p.1 : ℝ) := lt_of_lt_of_le (by linarith) (hE p hp).2.2.1
    exact_mod_cast he
  have hpoints := hbound u L hL m hm b S0 hS0 (E.image Prod.snd) (by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    exact (hE p hp).2.2.2.2.1) (by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    exact (hE p hp).2.2.2.2.2.1) (by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    have hv := hE p hp
    exact ⟨p.1,hv.1,hv.2.1,hv.2.2.1,hv.2.2.2.1,hv.2.2.2.2.2.2.2⟩)
  have hpairs := hdivisor u L hL E hp0
    (fun p hp => (hE p hp).2.2.2.2.1)
    (fun p hp => (hE p hp).2.2.2.2.2.2.1)
    (fun p hp => (hE p hp).2.2.2.2.2.2.2)
  have hH : 0 < L*S0+‖u‖ := by nlinarith [norm_nonneg u]
  have hscale : (L+‖u‖)^(ε/2) ≤ (L*S0+‖u‖)^(ε/2) :=
    Real.rpow_le_rpow (by linarith [norm_nonneg u]) (by nlinarith) (by positivity)
  have hpower : (L*S0+‖u‖)^(ε/2)*(L*S0+‖u‖)^(ε/2)=(L*S0+‖u‖)^ε := by
    rw [← Real.rpow_add hH]
    congr 1
    ring
  calc
    (E.card : ℝ) ≤ C*(L+‖u‖)^(ε/2)*((E.image Prod.snd).card : ℝ) := hpairs
    _ ≤ C*(L*S0+‖u‖)^(ε/2)*(K*(L*S0+‖u‖)^(ε/2)*
        (1+L/(m : ℝ))^(r+1)) := by
      apply mul_le_mul _ hpoints (Nat.cast_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left hscale (by linarith)
    _ = (C*K)*(L*S0+‖u‖)^ε*(1+L/(m : ℝ))^(r+1) := by
      rw [← hpower]
      ring

/-- The complete modulus--point sieve on a fixed proper homogeneous model. -/
theorem exists_pair_bound (J : Ideal (MvPolynomial (Fin n) ℤ))
    (hproper : rationalIdeal J ≠ ⊤)
    (hhom : (rationalIdeal J).IsHomogeneous (homogeneousSubmodule (Fin n) ℚ))
    (r : ℕ) (hdim : ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ rationalIdeal J) ≤
      (r : WithBot ℕ∞)) (ε : ℝ) (hε : 0 < ε) :
    ∃ c K : ℝ, 1 ≤ c ∧ 1 ≤ K ∧
      ∀ (u : Fin n → ℝ) (L : ℝ), 1 ≤ L → ∀ (m : ℕ), 0 < m →
      ∀ (b : Fin n → ℤ) (S0 : ℝ), c*(1+L/(m : ℝ)) ≤ S0 →
      ∀ E : Finset (ℕ × (Fin n → ℤ)),
      (∀ p ∈ E, ValidPair J u L m b S0 p) →
      (E.card : ℝ) ≤ K*(L*S0+‖u‖)^ε*(1+L/(m : ℝ))^(r+1) := by
  obtain ⟨D⟩ := exists_certificate J hproper hhom r hdim
  exact exists_pair_bound_of_certificate D ε hε

/-- Finite enumeration of exactly the source pairs. -/
def pairs (J : Ideal (MvPolynomial (Fin n) ℤ)) (u : Fin n → ℝ)
    (L : ℝ) (m : ℕ) (b : Fin n → ℤ) (S0 : ℝ) : Finset (ℕ × (Fin n → ℤ)) := by
  classical
  exact ((Finset.range (⌊2*S0⌋₊+1)).product (TranslatedIntegerBoxes.box u L)).filter
    (ValidPair J u L m b S0)

theorem mem_pairs (J : Ideal (MvPolynomial (Fin n) ℤ)) (u : Fin n → ℝ)
    (L : ℝ) (m : ℕ) (b : Fin n → ℤ) (S0 : ℝ) (p : ℕ × (Fin n → ℤ)) :
    p ∈ pairs J u L m b S0 ↔ ValidPair J u L m b S0 p := by
  classical
  constructor
  · intro hp
    exact (Finset.mem_filter.mp hp).2
  · intro hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,hp⟩
    · exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.le_floor hp.2.2.2.1))
    · exact (TranslatedIntegerBoxes.mem_box u L p.2).mpr hp.2.2.2.2.1

/-- Literal cardinality of the complete finite source pair set. -/
theorem exists_source_bound (J : Ideal (MvPolynomial (Fin n) ℤ))
    (hproper : rationalIdeal J ≠ ⊤)
    (hhom : (rationalIdeal J).IsHomogeneous (homogeneousSubmodule (Fin n) ℚ))
    (r : ℕ) (hdim : ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ rationalIdeal J) ≤
      (r : WithBot ℕ∞)) (ε : ℝ) (hε : 0 < ε) :
    ∃ c K : ℝ, 1 ≤ c ∧ 1 ≤ K ∧
      ∀ (u : Fin n → ℝ) (L : ℝ), 1 ≤ L → ∀ (m : ℕ), 0 < m →
      ∀ (b : Fin n → ℤ) (S0 : ℝ), c*(1+L/(m : ℝ)) ≤ S0 →
      ((pairs J u L m b S0).card : ℝ) ≤
        K*(L*S0+‖u‖)^ε*(1+L/(m : ℝ))^(r+1) := by
  obtain ⟨c,K,hc,hK,hbound⟩ := exists_pair_bound J hproper hhom r hdim ε hε
  exact ⟨c,K,hc,hK,fun u L hL m hm b S0 hS0 =>
    hbound u L hL m hm b S0 hS0 _ (fun p hp => (mem_pairs J u L m b S0 p).mp hp)⟩

end CubicTenVariables.TranslatedGeometricSievePairs

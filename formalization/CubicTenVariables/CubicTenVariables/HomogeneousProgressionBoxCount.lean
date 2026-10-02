import CubicTenVariables.ProperHomogeneousNormalization
import CubicTenVariables.ResidueBoxCount

/-! Uniform counts in real-centered boxes and arbitrary integral progressions
for fixed proper homogeneous ideals. Recentring is proved explicitly; the
constant precedes the center, radius, progression and finite point set. -/
noncomputable section
namespace CubicTenVariables.HomogeneousProgressionBoxCount
open MvPolynomial TranslatedDepthSeven
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Recentring an actual progression at any one of its points produces a
bounded displacement set, without requiring an integral box center. -/
theorem displacement_bound {n : ℕ} (S : Finset (Fin n → ℤ))
    (u : Fin n → ℝ) (L : ℝ) (m : ℕ) (hm : 0 < m)
    (x₀ : Fin n → ℤ) (hx₀ : x₀ ∈ S)
    (hbox : ∀ x ∈ S, ∀ i, |(x i : ℝ)-u i| ≤ L)
    (hres : ∀ x ∈ S, ∀ i, (m : ℤ) ∣ x i-x₀ i) :
    let q := fun (x : Fin n → ℤ) i => (x i-x₀ i)/(m : ℤ)
    (∀ x ∈ S, integralAffineMap x₀ (q x) m=x) ∧
    Set.InjOn q (S : Set (Fin n → ℤ)) ∧
    ∀ x ∈ S, ∀ i, (q x i).natAbs ≤ ⌈2*L/(m : ℝ)⌉₊+1 := by
  dsimp only
  let q := fun (x : Fin n → ℤ) i => (x i-x₀ i)/(m : ℤ)
  have hmul (x) (hx : x ∈ S) (i) : q x i*(m : ℤ)=x i-x₀ i :=
    Int.ediv_mul_cancel (hres x hx i)
  have he (x) (hx : x ∈ S) : integralAffineMap x₀ (q x) m=x := by
    funext i
    dsimp [integralAffineMap]
    rw [mul_comm (m : ℤ),hmul x hx i]
    ring
  refine ⟨he,?_,?_⟩
  · intro x hx y hy hxy
    change q x=q y at hxy
    exact (he x hx).symm.trans ((congrArg (fun z => integralAffineMap x₀ z m) hxy).trans (he y hy))
  · intro x hx i
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    have hm' : (q x i : ℝ)*(m : ℝ)=(x i : ℝ)-(x₀ i : ℝ) := by
      exact_mod_cast hmul x hx i
    have hd : |(x i : ℝ)-(x₀ i : ℝ)| ≤ 2*L :=
      (abs_sub_le (x i : ℝ) (u i) (x₀ i : ℝ)).trans (by
        rw [abs_sub_comm (u i)]
        linarith [hbox x hx i,hbox x₀ hx₀ i])
    have hq : |(q x i : ℝ)| ≤ 2*L/(m : ℝ) := by
      apply (le_div_iff₀ hmR).mpr
      rw [←abs_of_pos hmR,←abs_mul,hm']
      exact hd
    have hceil := hq.trans (Nat.le_ceil (2*L/(m : ℝ)))
    have hnat : (q x i).natAbs ≤ ⌈2*L/(m : ℝ)⌉₊ := by
      apply (Nat.cast_le (α := ℤ)).mp
      simpa only [Int.natCast_natAbs] using
        (show |q x i| ≤ (⌈2*L/(m : ℝ)⌉₊ : ℤ) by exact_mod_cast hceil)
    exact hnat.trans (Nat.le_succ _)

/-- Any supplied homogeneous linear normalization gives the source box
bound, with a constant independent of all translations and progressions. -/
theorem exists_bound_of_normalization {n d : ℕ}
    {I : Ideal (MvPolynomial (Fin n) ℚ)}
    (D : HomogeneousLinearNormalizationData I) (hd : D.parameterCount ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (S : Finset (Fin n → ℤ)) (u : Fin n → ℝ)
      (L : ℝ), 0 ≤ L → ∀ (m : ℕ), 0 < m → ∀ (b : Fin n → ℤ),
      (∀ x ∈ S, ∀ i, |(x i : ℝ)-u i| ≤ L) →
      (∀ x ∈ S, ∀ i, (m : ℤ) ∣ x i-b i) →
      (∀ x ∈ S, (fun i => (x i : ℚ)) ∈ affineIdealZeroLocus I) →
      (S.card : ℝ) ≤ C*(1+L/(m : ℝ))^d := by
  classical
  obtain ⟨K,hK⟩ := exists_card_le_mul_power_of_parameterCount_le D hd
  let C : ℝ := 1+(K : ℝ)*2^d
  have hC : 1 ≤ C := by
    have h : 0 ≤ (K : ℝ)*2^d := by positivity
    dsimp [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro S u L hL m hm b hbox hres hzero
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hbase : 0 ≤ 1+L/(m : ℝ) := by positivity
  by_cases hS : S.Nonempty
  · obtain ⟨x₀,hx₀⟩ := hS
    let q := fun (x : Fin n → ℤ) i => (x i-x₀ i)/(m : ℤ)
    have hres₀ : ∀ x ∈ S, ∀ i, (m : ℤ) ∣ x i-x₀ i := by
      intro x hx i
      convert dvd_sub (hres x hx i) (hres x₀ hx₀ i) using 1
      ring
    obtain ⟨he,hinj,hq⟩ := displacement_bound S u L m hm x₀ hx₀ hbox hres₀
    let T : ℕ := ⌈2*L/(m : ℝ)⌉₊+1
    have hb (z) (hz : z ∈ S.image q) (i) : (z i).natAbs ≤ T := by
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      exact hq x hx i
    have hz (z) (hz : z ∈ S.image q) :
        (fun i => (integralAffineMap x₀ z m i : ℚ)) ∈ affineIdealZeroLocus I := by
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      rw [he x hx]
      exact hzero x hx
    have hc := hK (S.image q) x₀ m T hm (by omega) hb hz
    have himage : (S.image q).card=S.card := Finset.card_image_iff.mpr hinj
    rw [himage] at hc
    have hT : (T : ℝ) ≤ 2*(1+L/(m : ℝ)) := by
      have ht : (⌈2*L/(m : ℝ)⌉₊ : ℝ) ≤ 2*L/(m : ℝ)+1 :=
        (Nat.ceil_lt_add_one (div_nonneg (by positivity) hmR.le)).le
      dsimp [T]
      push_cast
      have he : 2*L/(m : ℝ)=2*(L/(m : ℝ)) := by ring
      rw [he] at ht ⊢
      linarith
    calc
      (S.card : ℝ)  ≤  (K : ℝ)*(T : ℝ)^d := by exact_mod_cast hc
      _  ≤  (K : ℝ)*(2*(1+L/(m : ℝ)))^d :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hT d) (Nat.cast_nonneg _)
      _ = ((K : ℝ)*2^d)*(1+L/(m : ℝ))^d := by rw [mul_pow]; ring
      _  ≤  C*(1+L/(m : ℝ))^d :=
        mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (pow_nonneg hbase _)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS,Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg (zero_le_one.trans hC) (pow_nonneg hbase _)

/-- The normalization itself is supplied by the proved general theorem;
only properness, homogeneity and the actual quotient-dimension bound remain. -/
theorem exists_bound {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ))
    (hproper : I ≠ ⊤)
    (hhom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℚ))
    (d : ℕ) (hdim : ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ I) ≤ (d : WithBot ℕ∞)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (S : Finset (Fin n → ℤ)) (u : Fin n → ℝ)
      (L : ℝ), 0 ≤ L → ∀ (m : ℕ), 0 < m → ∀ (b : Fin n → ℤ),
      (∀ x ∈ S, ∀ i, |(x i : ℝ)-u i| ≤ L) →
      (∀ x ∈ S, ∀ i, (m : ℤ) ∣ x i-b i) →
      (∀ x ∈ S, (fun i => (x i : ℚ)) ∈ affineIdealZeroLocus I) →
      (S.card : ℝ) ≤ C*(1+L/(m : ℝ))^d := by
  obtain ⟨D,hD⟩ := ProperHomogeneousNormalization.exists_homogeneousLinearNormalizationData_parameterCount_le
    n I hproper hhom d hdim
  exact exists_bound_of_normalization D hD

end CubicTenVariables.HomogeneousProgressionBoxCount

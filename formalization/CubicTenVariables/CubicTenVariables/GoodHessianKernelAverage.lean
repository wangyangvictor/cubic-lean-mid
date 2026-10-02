import CubicTenVariables.DavenportCount
import CubicTenVariables.SmithKernelFormula
import CubicTenVariables.HessianMinorBoxBound
import CubicTenVariables.ModularMinorKernelBound
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! An epsilon-free average of the actual modular Hessian kernel over an
integer box. The constant is uniform in the modulus and box radius. -/

noncomputable section
namespace CubicTenVariables.GoodHessianKernelAverage
open MvPolynomial HessianTheorem11
open scoped BigOperators

/-- The actual kernel of the integral Hessian reduced modulo `m`. -/
def kernelCard (F : MvPolynomial (Fin 10) ℤ) (m : ℕ) (x : Fin 10 → ℤ) : ℕ :=
  Nat.card {z : Fin 10 → ZMod m //
    ((hessian F x).map (Int.castRingHom (ZMod m))).mulVec z = 0}

/-- One rank stratum has the correct fifth-power envelope. -/
theorem rank_envelope (C m B : ℝ) (hC : 1 ≤ C) (hm : 0 ≤ m) (hB : 0 ≤ B)
    (j : ℕ) (hj : j ≤ 10) :
    B^j * Real.sqrt (C * m^(10-j) * B^j) ≤ C * (m+B^3)^5 := by
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hs : 0 ≤ m+B^3 := by positivity
  have hmS : m ≤ m+B^3 := le_add_of_nonneg_right (by positivity)
  have hBS : B^3 ≤ m+B^3 := le_add_of_nonneg_left hm
  have hp : m^(10-j) * (B^3)^j ≤ (m+B^3)^10 := by
    calc
      _ ≤ (m+B^3)^(10-j) * (m+B^3)^j :=
        mul_le_mul (pow_le_pow_left₀ hm hmS _) (pow_le_pow_left₀ (by positivity) hBS _)
          (by positivity) (by positivity)
      _ = _ := by rw [← pow_add, Nat.sub_add_cancel hj]
  have hsqrt : (Real.sqrt (C * m^(10-j) * B^j))^2 = C * m^(10-j) * B^j :=
    Real.sq_sqrt (by positivity)
  have hp' : m^(10-j) * B^(3*j) ≤ (m+B^3)^10 := by simpa [pow_mul] using hp
  have heq : (B^j * Real.sqrt (C * m^(10-j) * B^j))^2 =
      C * (m^(10-j) * B^(3*j)) := by
    rw [mul_pow, hsqrt]
    simp only [pow_mul]
    ring
  have hC2 : C ≤ C^2 := by nlinarith
  have hprod := mul_le_mul hp' hC2 hC0 (by positivity : 0 ≤ (m+B^3)^10)
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [heq, mul_pow]
  simpa only [← pow_mul, Nat.reduceMul, mul_comm] using hprod

/-- Finite rank summation; its premises will be discharged by the literal
minor and Davenport bounds in the final endpoint. -/
private theorem sum_sqrt_le_of_rank_bounds
    (F : MvPolynomial (Fin 10) ℤ) (m B C : ℕ) (hC : 1 ≤ C)
    (K : ℕ → ℕ)
    (hcount : ∀ j ≤ 10, hessianRankCount F B j ≤ K j * B^j)
    (hkernel : ∀ x ∈ integerBox 10 B,
      kernelCard F m x ≤ C * m^(10-integerHessianRank F x) * B^(integerHessianRank F x)) :
    (∑ x ∈ integerBox 10 B, Real.sqrt (kernelCard F m x : ℝ)) ≤
      ((∑ j ∈ Finset.range 11, K j) * C : ℕ) * ((m:ℝ)+(B:ℝ)^3)^5 := by
  classical
  have hrank (x : Fin 10 → ℤ) : integerHessianRank F x ≤ 10 := by
    simpa [integerHessianRank] using
      Matrix.rank_le_card_width (hessian (map (Int.castRingHom ℚ) F)
        (fun i => (x i : ℚ)))
  rw [← Finset.sum_fiberwise_of_maps_to (s := integerBox 10 B)
    (t := Finset.range 11) (g := integerHessianRank F)
    (fun x _ => Finset.mem_range.mpr (by have := hrank x; omega))]
  have hstratum (j : ℕ) (hj : j ∈ Finset.range 11) :
      (∑ x ∈ (integerBox 10 B).filter (fun x => integerHessianRank F x = j),
        Real.sqrt (kernelCard F m x : ℝ)) ≤
      (K j : ℝ) * C * ((m:ℝ)+(B:ℝ)^3)^5 := by
    have hj10 : j ≤ 10 := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hpoint (x : Fin 10 → ℤ)
        (hx : x ∈ (integerBox 10 B).filter (fun x => integerHessianRank F x = j)) :
        Real.sqrt (kernelCard F m x : ℝ) ≤
          Real.sqrt ((C:ℝ) * (m:ℝ)^(10-j) * (B:ℝ)^j) := by
      apply Real.sqrt_le_sqrt
      have hh := hkernel x (Finset.mem_filter.mp hx).1
      rw [(Finset.mem_filter.mp hx).2] at hh
      exact_mod_cast hh
    calc
      _ ≤ (hessianRankCount F B j : ℝ) *
          Real.sqrt ((C:ℝ) * (m:ℝ)^(10-j) * (B:ℝ)^j) := by
        simpa [hessianRankCount, nsmul_eq_mul] using
          Finset.sum_le_card_nsmul _ _ _ hpoint
      _ ≤ ((K j:ℝ) * (B:ℝ)^j) *
          Real.sqrt ((C:ℝ) * (m:ℝ)^(10-j) * (B:ℝ)^j) := by
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        exact_mod_cast hcount j hj10
      _ = (K j:ℝ) * ((B:ℝ)^j *
          Real.sqrt ((C:ℝ) * (m:ℝ)^(10-j) * (B:ℝ)^j)) := by ring
      _ ≤ (K j:ℝ) * ((C:ℝ) * ((m:ℝ)+(B:ℝ)^3)^5) := by
        exact mul_le_mul_of_nonneg_left
          (rank_envelope C m B (by exact_mod_cast hC) (by positivity) (by positivity) j hj10)
          (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ j ∈ Finset.range 11, (K j:ℝ) * C * ((m:ℝ)+(B:ℝ)^3)^5 :=
      Finset.sum_le_sum hstratum
    _ = _ := by simp only [Nat.cast_mul, Nat.cast_sum, Finset.sum_mul]

/-- An integer-radius average with one constant before the modulus and radius.
All rank counts and actual modular kernels are supplied by proved theorems. -/
theorem exists_integer_box_bound
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hzero : ¬ HasIntegerZero F) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (m B : ℕ), 0 < m → 1 ≤ B →
      (∑ x ∈ integerBox 10 B, Real.sqrt (kernelCard F m x : ℝ)) ≤
        A * ((m:ℝ)+(B:ℝ)^3)^5 := by
  classical
  obtain ⟨C,hC,hminor⟩ := HessianMinorBoxBound.exists_uniform_rank_minor_bound_in_integerBox F hF
  choose K hK using fun j : ℕ => hessianRankCount_le_of_no_integer_zero F hF hzero j
  refine ⟨(1 + (∑ j ∈ Finset.range 11, K j) * C : ℕ), by exact_mod_cast Nat.le_add_right 1 _, ?_⟩
  intro m B hm hB
  letI : NeZero m := ⟨hm.ne'⟩
  have hk (x : Fin 10 → ℤ) (hx : x ∈ integerBox 10 B) :
      kernelCard F m x ≤ C * m^(10-integerHessianRank F x) * B^(integerHessianRank F x) := by
    obtain ⟨rows,cols,hd,hdB⟩ := hminor B hB x hx (integerHessianRank F x) rfl
    calc
      _ ≤ m^(10-integerHessianRank F x) * ((hessian F x).submatrix rows cols).det.natAbs :=
        ModularMinorKernelBound.natCard_kernel_le_minor (hessian F x) rows cols hd m
      _ ≤ m^(10-integerHessianRank F x) * (C * B^(integerHessianRank F x)) :=
        Nat.mul_le_mul_left _ hdB
      _ = _ := by ring
  apply (sum_sqrt_le_of_rank_bounds F m B C hC K (fun j _ => hK j B hB) hk).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hle : (∑ j ∈ Finset.range 11, K j) * C ≤ 1 + (∑ j ∈ Finset.range 11, K j) * C := by omega
  exact_mod_cast hle

/-- The actual closed real-radius box, represented as a finite set. -/
def realBox (R : ℝ) : Finset (Fin 10 → ℤ) := integerBox 10 ⌊R⌋₊

@[simp] theorem mem_realBox {R : ℝ} (hR : 0 ≤ R) {x : Fin 10 → ℤ} :
    x ∈ realBox R ↔ ∀ i, |(x i : ℝ)| ≤ R := by
  rw [realBox, mem_integerBox]
  constructor
  · intro hx i
    have hi : |(x i : ℝ)| ≤ (⌊R⌋₊ : ℝ) := by exact_mod_cast hx i
    exact hi.trans (Nat.floor_le hR)
  · intro hx i
    have hi : (x i).natAbs ≤ ⌊R⌋₊ := by
      apply Nat.le_floor
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hx i
    have hi' : ((x i).natAbs : ℤ) ≤ (⌊R⌋₊ : ℤ) := by exact_mod_cast hi
    simpa only [Int.natCast_natAbs] using hi'

/-- Epsilon-free average over the literal real-radius integer box. -/
theorem exists_real_box_bound
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (m : ℕ), 0 < m → ∀ (R : ℝ), 1 ≤ R →
      (∑ x ∈ realBox R, Real.sqrt (kernelCard F m x : ℝ)) ≤
        A * ((m:ℝ)+R^3)^5 := by
  have hzero : ¬ HasIntegerZero F := by
    intro hz
    obtain ⟨x,hx,hFx⟩ := hasRationalZero_of_hasIntegerZero hz
    exact hx (hA x hFx)
  obtain ⟨A,hA1,hbound⟩ := exists_integer_box_bound F hF hzero
  refine ⟨A,hA1,?_⟩
  intro m hm R hR
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  apply (hbound m ⌊R⌋₊ hm ((Nat.one_le_floor_iff R).mpr hR)).trans
  apply mul_le_mul_of_nonneg_left _ (le_trans (by norm_num) hA1)
  have hpow : (⌊R⌋₊ : ℝ)^3 ≤ R^3 :=
    pow_le_pow_left₀ (by positivity) (Nat.floor_le hR0) 3
  exact pow_le_pow_left₀ (by positivity) (by linarith :
    (m:ℝ)+(⌊R⌋₊:ℝ)^3 ≤ (m:ℝ)+R^3) 5

/-- The manuscript's good-kernel average, with its epsilon factor removed.
The only hypotheses concern the actual cubic and rational anisotropy. -/
theorem exists_uniform_bound
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (m : ℕ), 0 < m → ∀ (R : ℝ), 1 ≤ R →
      (∑ x ∈ realBox R, Real.sqrt (kernelCard F m x : ℝ)) ≤
        A * (m:ℝ)^5 * (1+R^3/(m:ℝ))^5 := by
  obtain ⟨A,hA1,hbound⟩ := exists_real_box_bound F hF hA
  refine ⟨A,hA1,?_⟩
  intro m hm R hR
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have heq : A * (m:ℝ)^5 * (1+R^3/(m:ℝ))^5 = A * ((m:ℝ)+R^3)^5 := by
    rw [mul_assoc, ← mul_pow]
    congr 2
    field_simp
  rw [heq]
  exact hbound m hm R hR

end CubicTenVariables.GoodHessianKernelAverage

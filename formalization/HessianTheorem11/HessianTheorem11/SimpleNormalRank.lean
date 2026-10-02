import HessianTheorem11.NormalPencil
import HessianTheorem11.SchurSecondOrder
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Inverse

/-! A simple determinant divisor forces the first normal matrix to be
nonsingular. The proof factors actual matrix power series by X and cancels
the common determinant factor before taking constant coefficients. -/

noncomputable section
namespace HessianTheorem11.SimpleNormalRank
open Matrix PowerSeries SchurSecondOrder

variable {K : Type*} [Field K]

theorem matrixCoeff_one_X_smul {ι κ : Type*}
    (M : Matrix ι κ (PowerSeries K)) :
    matrixCoeff 1 ((PowerSeries.X : PowerSeries K) • M) = matrixCoeff 0 M := by
  ext i j
  simp [matrixCoeff, PowerSeries.coeff_one_mul, PowerSeries.coeff_zero_eq_constantCoeff]

theorem first_matrix_nonsingular_of_simple_factor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι (PowerSeries K)) (f d k : PowerSeries K)
    (hS : matrixCoeff 0 S = 0)
    (hf0 : constantCoeff f = 0) (hf1 : PowerSeries.coeff 1 f ≠ 0)
    (hd : constantCoeff d ≠ 0)
    (hdet : k * S.det = f ^ Fintype.card ι * d) :
    (matrixCoeff 1 S).det ≠ 0 := by
  have hzero : S.map constantCoeff = 0 := by
    ext i j
    have hi := congrArg (fun A : Matrix ι ι K => A i j) hS
    simpa [matrixCoeff, PowerSeries.coeff_zero_eq_constantCoeff] using hi
  obtain ⟨T, hT⟩ := NormalPencil.exists_scalar_factor_of_residue_zero
    (constantCoeff : PowerSeries K →+* K) PowerSeries.X
    (fun _ => PowerSeries.X_dvd_iff.symm) S hzero
  obtain ⟨u, hu⟩ := PowerSeries.X_dvd_iff.mpr hf0
  have hu0 : constantCoeff u = PowerSeries.coeff 1 f := by
    rw [hu]
    simp [PowerSeries.coeff_one_mul]
  have hT0 : matrixCoeff 1 S = T.map constantCoeff := by
    rw [hT, matrixCoeff_one_X_smul]
    ext i j
    exact PowerSeries.coeff_zero_eq_constantCoeff_apply _
  have hc : k * T.det = u ^ Fintype.card ι * d := by
    apply mul_left_cancel₀ (pow_ne_zero _ (PowerSeries.X_ne_zero (R := K)))
    calc
      PowerSeries.X ^ Fintype.card ι * (k * T.det) = k * S.det := by
        rw [hT, Matrix.det_smul]
        ring
      _ = f ^ Fintype.card ι * d := hdet
      _ = PowerSeries.X ^ Fintype.card ι * (u ^ Fintype.card ι * d) := by
        rw [hu, mul_pow]
        ring
  have hc0 := congrArg (constantCoeff : PowerSeries K →+* K) hc
  simp only [map_mul, map_pow, RingHom.map_det, hu0] at hc0
  change constantCoeff k * (T.map constantCoeff).det =
    PowerSeries.coeff 1 f ^ Fintype.card ι * constantCoeff d at hc0
  rw [hT0]
  intro hz
  rw [hz, mul_zero] at hc0
  exact (mul_ne_zero (pow_ne_zero _ hf1) hd) hc0.symm

theorem first_schur_coefficient
    {ι κ : Type*} [Fintype κ]
    (A : Matrix ι ι (PowerSeries K)) (C : Matrix ι κ (PowerSeries K))
    (D : Matrix κ ι (PowerSeries K)) (J : Matrix κ κ (PowerSeries K))
    (hC : matrixCoeff 0 C = 0) (hD : matrixCoeff 0 D = 0) :
    matrixCoeff 1 (A - C * J * D) = matrixCoeff 1 A := by
  rw [matrixCoeff_sub, matrixCoeff_mul_one, matrixCoeff_mul_zero, hC, hD]
  simp

/-- The simple-divisor obstruction for an actual block matrix. The zero
and first coefficients are the only normal-line data needed. -/
theorem first_normal_nonsingular_of_simple_divisor
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι (PowerSeries K)) (C : Matrix ι κ (PowerSeries K))
    (D : Matrix κ ι (PowerSeries K)) (N : Matrix κ κ (PowerSeries K))
    [Invertible N] (f d : PowerSeries K)
    (hA : matrixCoeff 0 A = 0) (hC : matrixCoeff 0 C = 0)
    (hD : matrixCoeff 0 D = 0)
    (hf0 : constantCoeff f = 0) (hf1 : PowerSeries.coeff 1 f ≠ 0)
    (hd : constantCoeff d ≠ 0)
    (hdet : (Matrix.fromBlocks A C D N).det = f ^ Fintype.card ι * d) :
    (matrixCoeff 1 A).det ≠ 0 := by
  have hs0 : matrixCoeff 0 (A - C * ⅟N * D) = 0 := by
    rw [matrixCoeff_sub, matrixCoeff_mul_zero, matrixCoeff_mul_zero, hA, hC]
    simp
  rw [Matrix.det_fromBlocks₂₂] at hdet
  have h := first_matrix_nonsingular_of_simple_factor
    (A - C * ⅟N * D) f d N.det hs0 hf0 hf1 hd hdet
  rwa [first_schur_coefficient A C D (⅟N) hC hD] at h

/-- A transverse defining equation and a nonvanishing residual factor
have exactly the prescribed order on the formal line. -/
theorem power_X_divisor_bound (f d : PowerSeries K) (h k : ℕ)
    (hf0 : constantCoeff f = 0) (hf1 : PowerSeries.coeff 1 f ≠ 0)
    (hd : constantCoeff d ≠ 0)
    (hdiv : (PowerSeries.X : PowerSeries K) ^ k ∣ f ^ h * d) : k ≤ h := by
  by_contra hk
  have hkh : h < k := by omega
  have hz := PowerSeries.X_pow_dvd_iff.mp hdiv h hkh
  obtain ⟨u, hu⟩ := PowerSeries.X_dvd_iff.mpr hf0
  have hu0 : constantCoeff u = PowerSeries.coeff 1 f := by
    rw [hu]
    simp
  have he : f ^ h * d = PowerSeries.X ^ h * (u ^ h * d) := by
    rw [hu, mul_pow]
    ring
  rw [he] at hz
  have hz' : constantCoeff (u ^ h * d) = 0 := by
    have hc : PowerSeries.coeff h (PowerSeries.X ^ h * (u ^ h * d)) =
        constantCoeff (u ^ h * d) := by
      simpa only [Nat.add_zero, Nat.zero_add, PowerSeries.coeff_zero_eq_constantCoeff_apply] using
        PowerSeries.coeff_X_pow_mul (u ^ h * d) h 0
    rwa [hc] at hz
  rw [map_mul, map_pow, hu0] at hz'
  exact (mul_ne_zero (pow_ne_zero _ hf1) hd) hz'

/-- The first-normal rank estimate on a transverse formal line. This
avoids introducing a separate abstract first-normal-rank certificate. -/
theorem first_normal_rank_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι (PowerSeries K)) (f d k : PowerSeries K) (h : ℕ)
    (hS : matrixCoeff 0 S = 0)
    (hf0 : constantCoeff f = 0) (hf1 : PowerSeries.coeff 1 f ≠ 0)
    (hd : constantCoeff d ≠ 0)
    (hdet : k * S.det = f ^ h * d) :
    2 * Fintype.card ι ≤ h + (matrixCoeff 1 S).rank := by
  have hzero : S.map constantCoeff = 0 := by
    ext i j
    have hi := congrArg (fun A : Matrix ι ι K => A i j) hS
    simpa [matrixCoeff, PowerSeries.coeff_zero_eq_constantCoeff] using hi
  obtain ⟨T, hT⟩ := NormalPencil.exists_scalar_factor_of_residue_zero
    (constantCoeff : PowerSeries K →+* K) PowerSeries.X
    (fun _ => PowerSeries.X_dvd_iff.symm) S hzero
  have hT0 : matrixCoeff 1 S = T.map constantCoeff := by
    rw [hT, matrixCoeff_one_X_smul]
    ext i j
    exact PowerSeries.coeff_zero_eq_constantCoeff_apply _
  have hdiv := NormalPencil.first_normal_pow_dvd_det
    (constantCoeff : PowerSeries K →+* K)
    (fun a => ⟨PowerSeries.C a, by simp⟩) PowerSeries.X
    (fun _ => PowerSeries.X_dvd_iff.symm) T
  rw [← hT] at hdiv
  have hddiv := dvd_mul_of_dvd_right hdiv k
  rw [hdet] at hddiv
  have hb := power_X_divisor_bound f d h _ hf0 hf1 hd hddiv
  have hr : (T.map constantCoeff).rank ≤ Fintype.card ι := Matrix.rank_le_card_width _
  rw [hT0]
  change 2 * Fintype.card ι - (T.map constantCoeff).rank ≤ h at hb
  omega

theorem first_normal_block_rank_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι (PowerSeries K)) (C : Matrix ι κ (PowerSeries K))
    (D : Matrix κ ι (PowerSeries K)) (N : Matrix κ κ (PowerSeries K))
    [Invertible N] (f d : PowerSeries K) (h : ℕ)
    (hA : matrixCoeff 0 A = 0) (hC : matrixCoeff 0 C = 0)
    (hD : matrixCoeff 0 D = 0)
    (hf0 : constantCoeff f = 0) (hf1 : PowerSeries.coeff 1 f ≠ 0)
    (hd : constantCoeff d ≠ 0)
    (hdet : (Matrix.fromBlocks A C D N).det = f ^ h * d) :
    2 * Fintype.card ι ≤ h + (matrixCoeff 1 A).rank := by
  have hs0 : matrixCoeff 0 (A - C * ⅟N * D) = 0 := by
    rw [matrixCoeff_sub, matrixCoeff_mul_zero, matrixCoeff_mul_zero, hA, hC]
    simp
  rw [Matrix.det_fromBlocks₂₂] at hdet
  have hb := first_normal_rank_bound (A - C * ⅟N * D) f d N.det h hs0 hf0 hf1 hd hdet
  rwa [first_schur_coefficient A C D (⅟N) hC hD] at hb

end HessianTheorem11.SimpleNormalRank

import CubicTenVariables.PadicPrimitiveCompactness
import CubicTenVariables.CubicGradientScaling
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-! A nonarchimedean determinant estimate turns the supplied cubic descent
certificates at levels n*k into primitive approximate zeros.  Matrix and
integral-polynomial descent certificates are constructed elsewhere; no local
solubility assertion is assumed here. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PadicCubicDescentColumns
open MvPolynomial Matrix Filter Topology
open scoped BigOperators

/-- The ultrametric determinant bound has no factorial loss. -/
theorem norm_det_le_pow {K : Type*} [NormedField K] [IsUltrametricDist K]
    {n : ℕ} (T : Matrix (Fin n) (Fin n) K) {M : ℝ} (hM : 0 ≤ M)
    (hT : ∀ i j, ‖T i j‖ ≤ M) : ‖T.det‖ ≤ M^n := by
  classical
  rw [Matrix.det_apply]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hM n)
  intro σ _
  rw [norm_units_zsmul, norm_prod]
  simpa using Finset.prod_le_prod (fun i (_ : i ∈ Finset.univ) => norm_nonneg (T (σ i) i))
    (fun i (_ : i ∈ Finset.univ) => hT (σ i) i)

/-- A maximal entry supplies a column normalization and the lower bound
forced by the determinant. -/
theorem exists_maximal_entry {K : Type*} [NormedField K] [IsUltrametricDist K]
    {n : ℕ} (hn : 0 < n) (T : Matrix (Fin n) (Fin n) K)
    {a : ℝ} (ha : 0 < a) (hdet : a^n ≤ ‖T.det‖) :
    ∃ i j, T i j ≠ 0 ∧ a ≤ ‖T i j‖ ∧ ∀ l m, ‖T l m‖ ≤ ‖T i j‖ := by
  classical
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨ij,_,hij⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
    (fun ij => ‖T ij.1 ij.2‖) Finset.univ_nonempty
  have hmax (i j) : ‖T i j‖ ≤ ‖T ij.1 ij.2‖ := hij (i,j) (Finset.mem_univ _)
  have hpow := hdet.trans (norm_det_le_pow T (norm_nonneg _) hmax)
  have hlarge : a ≤ ‖T ij.1 ij.2‖ :=
    le_of_pow_le_pow_left₀ (by omega : n ≠ 0) (norm_nonneg _) hpow
  exact ⟨ij.1,ij.2,norm_pos_iff.mp (ha.trans_le hlarge),hlarge,hmax⟩

variable {p n : ℕ} [Fact p.Prime]

/-- Normalizing a maximal column in the level n*k descent matrix gives an
integral vector with a coordinate exactly one and the required cubic decay. -/
theorem exists_normalized_vector (F : MvPolynomial (Fin n) ℚ_[p])
    (hF : F.IsHomogeneous 3) (hn : 9 < n) (k : ℕ)
    (T : Matrix (Fin n) (Fin n) ℚ_[p])
    (hdet : ‖(p : ℚ_[p])‖^(3*n*k) ≤ ‖T.det‖)
    (hcol : ∀ j, ‖eval (fun i => T i j) F‖ ≤ ‖(p : ℚ_[p])‖^(n*k)) :
    ∃ x : Fin n → ℤ_[p], (∃ i, x i=1) ∧
      ‖eval (fun i => (x i : ℚ_[p])) F‖ ≤ ‖(p : ℚ_[p])‖^((n-9)*k) := by
  classical
  let b : ℝ := ‖(p : ℚ_[p])‖
  have hb : 0 < b := by
    dsimp [b]
    rw [Padic.norm_p]
    exact inv_pos.mpr (by exact_mod_cast (Fact.out : p.Prime).pos)
  have hd : (b^(3*k))^n ≤ ‖T.det‖ := by
    rw [← pow_mul]
    convert hdet using 1
    congr 1
    ring
  obtain ⟨i,j,ha,hlower,hmax⟩ := exists_maximal_entry (by omega) T (pow_pos hb _) hd
  let a := T i j
  have hnorm : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hint (l) : ‖a⁻¹*T l j‖ ≤ 1 := by
    rw [norm_mul,norm_inv]
    calc
      ‖a‖⁻¹*‖T l j‖ ≤ ‖a‖⁻¹*‖a‖ := mul_le_mul_of_nonneg_left (hmax l j)
        (inv_nonneg.mpr (norm_nonneg _))
      _ = 1 := inv_mul_cancel₀ hnorm.ne'
  let x : Fin n → ℤ_[p] := fun l => ⟨a⁻¹*T l j,hint l⟩
  refine ⟨x,⟨i,?_⟩,?_⟩
  · apply Subtype.ext
    exact inv_mul_cancel₀ ha
  · have heval : eval (fun l => (x l : ℚ_[p])) F = a⁻¹^3*eval (fun l => T l j) F := by
      exact CubicGradientScaling.homogeneous_eval₂_smul F hF (RingHom.id _) _ _
    rw [heval,norm_mul,norm_pow,norm_inv]
    have hscale : b^(n*k)=b^((n-9)*k)*(b^(3*k))^3 := by
      rw [← pow_mul,← pow_add]
      congr 1
      calc
        n*k = ((n-9)+9)*k := by rw [Nat.sub_add_cancel (by omega : 9 ≤ n)]
        _ = (n-9)*k+(3*k)*3 := by ring
    have hnum : ‖eval (fun l => T l j) F‖ ≤ b^((n-9)*k)*‖a‖^3 :=
      (hcol j).trans (hscale ▸ mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (le_of_lt (pow_pos hb _)) hlower 3) (pow_nonneg hb.le _))
    have hh := (div_le_iff₀ (pow_pos hnorm 3)).mpr hnum
    simpa only [div_eq_mul_inv,inv_pow,mul_comm] using hh

/-- Supplied descent certificates at the subsequence n*k produce one
primitive integral sequence whose actual cubic values converge to zero. -/
theorem exists_approximate_zeros (F : MvPolynomial (Fin n) ℚ_[p])
    (hF : F.IsHomogeneous 3) (hn : 9 < n)
    (hT : ∀ k : ℕ, ∃ T : Matrix (Fin n) (Fin n) ℚ_[p],
      ‖(p : ℚ_[p])‖^(3*n*k) ≤ ‖T.det‖ ∧
      ∀ j, ‖eval (fun i => T i j) F‖ ≤ ‖(p : ℚ_[p])‖^(n*k)) :
    ∃ x : ℕ → (Fin n → ℤ_[p]), (∀ k, ∃ i, x k i=1) ∧
      Tendsto (fun k => eval (fun i => (x k i : ℚ_[p])) F) atTop (𝓝 0) := by
  classical
  have hx (k : ℕ) : ∃ x : Fin n → ℤ_[p], (∃ i, x i=1) ∧
      ‖eval (fun i => (x i : ℚ_[p])) F‖ ≤ ‖(p : ℚ_[p])‖^((n-9)*k) := by
    obtain ⟨T,hd,hc⟩ := hT k
    exact exists_normalized_vector F hF hn k T hd hc
  choose x hx hxbound using hx
  refine ⟨x,hx,?_⟩
  have hb0 : 0 ≤ ‖(p : ℚ_[p])‖^(n-9) := pow_nonneg (norm_nonneg _) _
  have hb1 : ‖(p : ℚ_[p])‖^(n-9) < 1 :=
    pow_lt_one₀ (norm_nonneg _) Padic.norm_p_lt_one (by omega)
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hb0 hb1
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) hxbound
  simpa only [← pow_mul] using ht

/-- Compactness closes the determinant/column certificates to an actual
nonzero p-adic zero. No local-solubility literature premise is used. -/
theorem exists_zero_of_certificates (F : MvPolynomial (Fin n) ℚ_[p])
    (hF : F.IsHomogeneous 3) (hn : 9 < n)
    (hT : ∀ k : ℕ, ∃ T : Matrix (Fin n) (Fin n) ℚ_[p],
      ‖(p : ℚ_[p])‖^(3*n*k) ≤ ‖T.det‖ ∧
      ∀ j, ‖eval (fun i => T i j) F‖ ≤ ‖(p : ℚ_[p])‖^(n*k)) :
    ∃ y : Fin n → ℚ_[p], (∀ i, ‖y i‖≤1) ∧ (∃ i, y i=1) ∧ y≠0 ∧ eval y F=0 := by
  obtain ⟨x,hx,ht⟩ := exists_approximate_zeros F hF hn hT
  exact PadicPrimitiveCompactness.exists_zero_of_tendsto F x hx ht

end CubicTenVariables.PadicCubicDescentColumns

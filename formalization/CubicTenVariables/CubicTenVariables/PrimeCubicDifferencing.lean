import CubicTenVariables.TranslatedHessianRankCount
import CubicTenVariables.PrimeFieldKernelRank
import CubicTenVariables.CubicDifferenceCorrelation
import CubicTenVariables.FiniteShiftDifferencing
import CubicTenVariables.PrimeSumAdapter
import CubicTenVariables.IntegerAnisotropy

/-! Full prime-field differencing from the proved geometric Hessian-rank
table. The resulting exponent is sufficient for the ordinary prime series;
it does not assert the sharper Hooley--Katz estimate used elsewhere. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.PrimeCubicDifferencing
open MvPolynomial HessianTheorem11 HessianKernelCRT
open TranslatedHessianLeadingGeometry
open scoped BigOperators

/-- The worst rank in the proved ten-variable table is seven. -/
theorem rank_exponent_le (r : ℕ) (hr : r ≤ 10) :
    (tauNat r : ℝ) + ((10-r : ℕ) : ℝ)/2 ≤ 21/2 := by
  interval_cases r <;> norm_num [tauNat]

/-- An actual full-field average of the square root of the Hessian kernel.
One constant precedes every prime, including the small primes. -/
theorem exists_kernel_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hzero : ¬ HasIntegerZero F) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (p : ℕ) [Fact p.Prime],
      (∑ h : Fin 10 → ZMod p, Real.sqrt (hessianKernelCard F p h : ℝ)) ≤
        A*(p : ℝ)^(21/2 : ℝ) := by
  classical
  obtain ⟨C,hC,hcount⟩ := TranslatedHessianRankCount.exists_uniform_bound F hF
    (anisotropicCubicOfNoIntegerZero F hF hzero).anisotropic
  refine ⟨11*C, by exact_mod_cast (by omega : 1 ≤ 11*C), ?_⟩
  intro p hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  let rank : (Fin 10 → ZMod p) → ℕ := fun h =>
    (hessian (map (Int.castRingHom (ZMod p)) F) h).rank
  have hrank (h : Fin 10 → ZMod p) : rank h ≤ 10 := by
    simpa only [Fintype.card_fin] using Matrix.rank_le_card_width
      (hessian (map (Int.castRingHom (ZMod p)) F) h)
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
    (t := Finset.range 11) (g := rank)
    (fun h _ => Finset.mem_range.mpr (by have := hrank h; omega))]
  have hstratum (r : ℕ) (hr : r ∈ Finset.range 11) :
      (∑ h ∈ Finset.univ.filter (fun h => rank h=r),
        Real.sqrt (hessianKernelCard F p h : ℝ)) ≤
          (C : ℝ)*(p : ℝ)^(21/2 : ℝ) := by
    have hr10 : r ≤ 10 := by have := Finset.mem_range.mp hr; omega
    have hcard : (Finset.univ.filter (fun h : Fin 10 → ZMod p => rank h=r)).card ≤
        C*p^(tauNat r) := by
      have hc := hcount p hp.out 0 r
      have he : (Finset.univ.filter (fun h : Fin 10 → ZMod p => rank h=r)).card =
          Nat.card {h : Fin 10 → ZMod p // rank h=r} := by
        simp only [Nat.card_eq_fintype_card,Fintype.card_subtype]
      rw [he]
      have hs : Nat.card {h : Fin 10 → ZMod p // rank h=r} ≤
          Nat.card {h : Fin 10 → ZMod p // rank h ≤ r} :=
        Set.ncard_le_ncard (fun _ hh => hh.le)
      apply hs.trans
      simpa only [TranslatedHessianRankCount.count,zero_add] using hc
    have heq (h : Fin 10 → ZMod p) (hh : h ∈ Finset.univ.filter (fun h => rank h=r)) :
        Real.sqrt (hessianKernelCard F p h : ℝ) = (p : ℝ)^(((10-r : ℕ) : ℝ)/2) := by
      rw [PrimeFieldKernelRank.hessianKernelCard_eq_pow]
      change Real.sqrt ((p^(10-rank h) : ℕ) : ℝ) = _
      rw [(Finset.mem_filter.mp hh).2, Nat.cast_pow, Real.sqrt_eq_rpow,
        ← Real.rpow_natCast_mul hp0.le]
      congr 1
      ring
    calc
      _ = ((Finset.univ.filter (fun h : Fin 10 → ZMod p => rank h=r)).card : ℝ) *
          (p : ℝ)^(((10-r : ℕ) : ℝ)/2) := by
        rw [Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((C : ℝ)*(p : ℝ)^(tauNat r)) * (p : ℝ)^(((10-r : ℕ) : ℝ)/2) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Real.rpow_nonneg hp0.le _)
      _ = (C : ℝ)*(p : ℝ)^((tauNat r : ℝ)+((10-r : ℕ) : ℝ)/2) := by
        rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hp0]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hp1 (rank_exponent_le r hr10)) (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ _r ∈ Finset.range 11, (C : ℝ)*(p : ℝ)^(21/2 : ℝ) :=
      Finset.sum_le_sum hstratum
    _ = _ := by simp; ring

private theorem norm_correlation_le {p : ℕ} [Fact p.Prime]
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (a : (ZMod p)ˣ) (h : Fin 10 → ZMod p) :
    ‖∑ x : Fin 10 → ZMod p,
      ZMod.stdAddChar ((a : ZMod p)*eval₂ (Int.castRingHom (ZMod p)) (x+h) F) *
      starRingEnd ℂ (ZMod.stdAddChar ((a : ZMod p)*eval₂ (Int.castRingHom (ZMod p)) x F))‖ ≤
      (p : ℝ)^5 * Real.sqrt (hessianKernelCard F p h : ℝ) := by
  have he (u v : ZMod p) : ZMod.stdAddChar u * starRingEnd ℂ (ZMod.stdAddChar v) =
      ZMod.stdAddChar (u-v) := by
    calc
      _ = (ZMod.stdAddChar (u-v)*ZMod.stdAddChar v)*starRingEnd ℂ (ZMod.stdAddChar v) := by
        rw [← AddChar.map_add_eq_mul, sub_add_cancel]
      _ = _ := by rw [mul_assoc, QuadraticGaussBound.stdAddChar_mul_conj, mul_one]
  simp_rw [he, ← mul_sub, eval₂_eq_eval_map]
  have hs := CubicDifferenceCorrelation.norm_sum_sq_le
    (map (Int.castRingHom (ZMod p)) F) (hF.map _) a h
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    _ ≤ (p : ℝ)^10*(hessianKernelCard F p h : ℝ) := hs
    _ = ((p : ℝ)^5 * Real.sqrt (hessianKernelCard F p h : ℝ))^2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      ring

/-- Actual scalar cubic sums over every prime field, with no point-count
literature premise. -/
theorem exists_unit_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hzero : ¬ HasIntegerZero F) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (p : ℕ) [Fact p.Prime] (a : (ZMod p)ˣ),
      ‖∑ x : Fin 10 → ZMod p,
        ZMod.stdAddChar ((a : ZMod p)*eval₂ (Int.castRingHom (ZMod p)) x F)‖ ≤
          A*(p : ℝ)^(31/4 : ℝ) := by
  classical
  obtain ⟨A,hA,hkernel⟩ := exists_kernel_bound F hF hzero
  refine ⟨A,hA,?_⟩
  intro p hp a
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  let f : (Fin 10 → ZMod p) → ℂ := fun x =>
    ZMod.stdAddChar ((a : ZMod p)*eval₂ (Int.castRingHom (ZMod p)) x F)
  let M : (Fin 10 → ZMod p) → ℝ := fun h =>
    (p : ℝ)^5*Real.sqrt (hessianKernelCard F p h : ℝ)
  have hs := FiniteShiftDifferencing.norm_sum_sq_le_of_difference_majorant
    f (AddMonoidHom.id _) Finset.univ Finset.univ (Finset.univ_nonempty) M
    (fun h _ => by dsimp [M]; positivity)
    (fun _ _ _ _ => Finset.mem_univ _)
    (fun h _ => norm_correlation_le F hF a h)
  have hs' : ‖∑ x, f x‖^2 ≤ ∑ h, M h := by
    simp only [Finset.card_univ] at hs
    have hc : (0 : ℝ)<Fintype.card (Fin 10 → ZMod p) := by positivity
    nlinarith
  have hsq : ‖∑ x, f x‖^2 ≤ A*(p : ℝ)^(31/2 : ℝ) := by
    calc
      _ ≤ ∑ h, M h := hs'
      _ = (p : ℝ)^5*∑ h, Real.sqrt (hessianKernelCard F p h : ℝ) := by
        simp only [M, Finset.mul_sum]
      _ ≤ (p : ℝ)^5*(A*(p : ℝ)^(21/2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hkernel p) (by positivity)
      _ = A*((p : ℝ)^(5 : ℝ)*(p : ℝ)^(21/2 : ℝ)) := by norm_num; ring
      _ = _ := by
        rw [← Real.rpow_add hp0]
        norm_num
  change ‖∑ x, f x‖ ≤ _
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have hAA : A ≤ A^2 := by nlinarith
  calc
    _ ≤ A*(p : ℝ)^(31/2 : ℝ) := hsq
    _ ≤ A^2*(p : ℝ)^(31/2 : ℝ) :=
      mul_le_mul_of_nonneg_right hAA (Real.rpow_nonneg hp0.le _)
    _ = (A*(p : ℝ)^(31/4 : ℝ))^2 := by
      rw [mul_pow, ← Real.rpow_mul_natCast hp0.le]
      norm_num

/-- The literal sum over all primitive scalar coefficients and residue
vectors has exponent `35/4`; both its normalization and all primes are explicit. -/
theorem exists_complete_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hzero : ¬ HasIntegerZero F) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ p : ℕ, p.Prime →
      ‖completeCubicSum F p 0‖ ≤ A*(p : ℝ)^(35/4 : ℝ) := by
  classical
  obtain ⟨A,hA,hbound⟩ := exists_unit_bound F hF hzero
  refine ⟨A,hA,?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : (0 : ℝ)<p := by exact_mod_cast hp.pos
  have hscalar (a : Fin p) (ha : Nat.Coprime a.val p) :
      ‖∑ x : Fin 10 → Fin p, residueExponential p (completeSumPhase F a x 0)‖ ≤
        A*(p : ℝ)^(31/4 : ℝ) := by
    obtain ⟨u,hu⟩ := (ZMod.isUnit_iff_coprime a.val p).mpr ha
    have heq : (∑ x : Fin 10 → Fin p, residueExponential p (completeSumPhase F a x 0)) =
        ∑ x : Fin 10 → ZMod p,
          ZMod.stdAddChar ((u : ZMod p)*eval₂ (Int.castRingHom (ZMod p)) x F) := by
      apply Fintype.sum_equiv (PrimeSumAdapter.vectorResidueEquiv p 10) _ _
      intro x
      rw [PrimeSumAdapter.residueExponential_completeSumPhase, hu]
      simp only [Pi.zero_apply,Int.cast_zero,dotProduct,zero_mul,Finset.sum_const_zero,
        add_zero,PrimeSumAdapter.vectorResidueEquiv_apply,eval₂_eq_eval_map]
    rw [heq]
    exact hbound p u
  calc
    _ ≤ ∑ a : Fin p, ‖if Nat.Coprime a.val p then
        ∑ x : Fin 10 → Fin p, residueExponential p (completeSumPhase F a x 0) else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _a : Fin p, A*(p : ℝ)^(31/4 : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      split_ifs with ha
      · exact hscalar a ha
      · simp only [norm_zero]; positivity
    _ = A*(p : ℝ)^(35/4 : ℝ) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      calc
        _ = A*((p : ℝ)^(1 : ℝ)*(p : ℝ)^(31/4 : ℝ)) := by rw [Real.rpow_one]; ring
        _ = _ := by rw [← Real.rpow_add hp0]; norm_num

end CubicTenVariables.PrimeCubicDifferencing

import CubicTenVariables.PrimeCubicDifferencing
import CubicTenVariables.UnconditionalTenRootBound
import CubicTenVariables.PrimePowerMultiplicativeSummability
import CubicTenVariables.OrdinarySeriesMultiplicativity
import CubicTenVariables.OrdinarySeriesPositivity
import CubicTenVariables.OrdinaryLocalFactorPositivity
import CubicTenVariables.PleasantsProved

/-! Absolute convergence and positivity of the ordinary singular series
in the actual ten-variable anisotropic contradiction branch. Prime-field
differencing gives decay p^(-5/4); the higher prime powers, local existence,
local density and Euler product are all proved internally. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.OrdinarySeriesUnconditional
open MvPolynomial

/-- One constant bounds every actual prime coefficient, including bad primes. -/
theorem exists_prime_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hzero : ¬ HasIntegerZero F) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p : ℕ, p.Prime →
      ‖singularSeriesTerm F p‖ ≤ C*(p : ℝ)^(-(5 : ℝ)/4) := by
  obtain ⟨C,hC,hbound⟩ := PrimeCubicDifferencing.exists_complete_bound F hF hzero
  refine ⟨C,hC,?_⟩
  intro p hp
  have h := PrimePowerSeriesConvergence.normalized_bound F hp.pos (hbound p hp)
  norm_num at h ⊢
  exact h

theorem summable_primes (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hzero : ¬ HasIntegerZero F) :
    Summable (fun p : Nat.Primes => ‖singularSeriesTerm F p.val‖) := by
  obtain ⟨C,_,hC⟩ := exists_prime_bound F hF hzero
  have hmajor : Summable (fun p : Nat.Primes => (p.val : ℝ)^(-(5 : ℝ)/4)) :=
    (Real.summable_nat_rpow.mpr (by norm_num)).comp_injective Subtype.val_injective
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => hC p.val p.property) (hmajor.mul_left C)

/-- Every positive prime-power exponent, jointly in the prime and exponent. -/
theorem summable_prime_powers (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hzero : ¬ HasIntegerZero F) :
    Summable (fun pk : Nat.Primes × ℕ =>
      ‖singularSeriesTerm F (pk.1.val^(pk.2+1))‖) := by
  have hprime := summable_primes F hF hzero
  have hhigh := (summable_prod_of_nonneg (fun pk : Nat.Primes × ℕ =>
    norm_nonneg (singularSeriesTerm F (pk.1.val^(pk.2+2))))).mp
      (UnconditionalTenRootBound.summable_higher_prime_powers F hF hzero)
  have hlocal (p : Nat.Primes) :
      Summable (fun k : ℕ => ‖singularSeriesTerm F (p.val^(k+1))‖) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.add_assoc,Nat.reduceAdd] using hhigh.1 p
  apply (summable_prod_of_nonneg (fun pk : Nat.Primes × ℕ =>
    norm_nonneg (singularSeriesTerm F (pk.1.val^(pk.2+1))))).mpr
  refine ⟨hlocal,?_⟩
  apply (hprime.add hhigh.2).congr
  intro p
  rw [(hlocal p).tsum_eq_zero_add]
  simp only [Nat.zero_add,pow_one,Nat.add_assoc,Nat.reduceAdd]

/-- Absolute convergence of the actual ordinary series over every modulus. -/
theorem summable_norm (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hzero : ¬ HasIntegerZero F) :
    Summable (fun q : ℕ => ‖singularSeriesTerm F q‖) :=
  PrimePowerMultiplicativeSummability.summable_norm
    (singularSeriesTerm F) (singularSeriesTerm_zero F) (singularSeriesTerm_one F)
    (fun {a b} hab => OrdinarySeriesMultiplicativity.mul F a b hab)
    (summable_prime_powers F hF hzero)

theorem summable (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hzero : ¬ HasIntegerZero F) :
    Summable (singularSeriesTerm F) := (summable_norm F hF hzero).of_norm

/-- Supplied actual local data give the same positive ordinary series. -/
theorem of_local_data (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hzero : ¬ HasIntegerZero F)
    (data : ∀ (p : ℕ) [Fact p.Prime], Nonempty (PrimeLocalizationData p F)) :
    SingularSeriesAbsolutelyConvergent F ∧ Literature.PositiveRealSingularSeries F := by
  have hconv := summable_norm F hF hzero
  refine ⟨hconv,OrdinarySeriesPositivity.of_localFactors F (by decide) hconv
    (summable_prime_powers F hF hzero) ?_⟩
  intro p
  letI : Fact p.val.Prime := ⟨p.property⟩
  obtain ⟨D⟩ := data p.val
  exact OrdinaryLocalFactorPositivity.localFactor_re_pos D hconv

/-- No point-count, local-solubility, convergence or positivity input is
supplied: only the actual homogeneous cubic and absence of an integer zero. -/
theorem of_cubic (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hzero : ¬ HasIntegerZero F) :
    SingularSeriesAbsolutelyConvergent F ∧ Literature.PositiveRealSingularSeries F := by
  apply of_local_data F hF hzero
  intro p _
  exact nonempty_primeLocalizationData PleasantsProved.proved F hF
    (anisotropicCubicOfNoIntegerZero F hF hzero).anisotropic p

end CubicTenVariables.OrdinarySeriesUnconditional

import CubicTenVariables.PolynomialMatrixRankSpreading
import CubicTenVariables.ProjectiveLinearSectionJacobian
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Parameter differentiation for a literal generic linear section.
The polynomial differential basis survives localization and the separable
algebraic closure. Its dual gives actual partial derivations of the generic
coefficient field; no differential or transversality assertion is assumed. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators TensorProduct

namespace CubicTenVariables.GenericNormalDerivations
open MvPolynomial

abbrev ParameterRing (k : Type*) [Field k] (m n : ℕ) :=
  MvPolynomial (Fin (m * n)) k

abbrev GenericField (k : Type*) [Field k] (m n : ℕ) :=
  AlgebraicClosure (FractionRing (ParameterRing k m n))

def parameterMap (k : Type*) [Field k] (m n : ℕ) :
    ParameterRing k m n →+* GenericField k m n := algebraMap _ _

def genericNormal (k : Type*) [Field k] (m n : ℕ) :
    Matrix (Fin m) (Fin n) (GenericField k m n) :=
  fun r c ↦ parameterMap k m n (X (finProdFinEquiv (r, c)))

private theorem generic_formallyEtale (k : Type*) [Field k] [CharZero k] (m n : ℕ) :
    Algebra.FormallyEtale (ParameterRing k m n) (GenericField k m n) := by
  let B := ParameterRing k m n
  let L := FractionRing B
  let E := AlgebraicClosure L
  letI : Algebra.FormallyEtale B L :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors B)
  letI : Algebra.FormallyEtale L E := Algebra.FormallyEtale.of_isSeparable L E
  exact Algebra.FormallyEtale.comp B L E

/-- The literal generic parameters give a differential basis even after
passing to the algebraic closure of their fraction field. -/
def parameterDifferentialBasis (k : Type*) [Field k] [CharZero k] (m n : ℕ) :
    Module.Basis (Fin (m * n)) (GenericField k m n)
      (KaehlerDifferential k (GenericField k m n)) := by
  letI := generic_formallyEtale k m n
  exact ((KaehlerDifferential.mvPolynomialBasis k (Fin (m * n))).baseChange
    (GenericField k m n)).map
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k
        (ParameterRing k m n) (GenericField k m n))

theorem parameterDifferentialBasis_repr_D
    (k : Type*) [Field k] [CharZero k] (m n : ℕ)
    (f : ParameterRing k m n) (i : Fin (m * n)) :
    (parameterDifferentialBasis k m n).repr
      (KaehlerDifferential.D k (GenericField k m n) (parameterMap k m n f)) i =
      parameterMap k m n (pderiv i f) := by
  classical
  letI := generic_formallyEtale k m n
  simp only [parameterDifferentialBasis, parameterMap, Module.Basis.map_repr,
    LinearEquiv.trans_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    Module.Basis.baseChange_repr_tmul,
    KaehlerDifferential.mvPolynomialBasis_repr_apply, Algebra.smul_def, mul_one]

def parameterPartial (k : Type*) [Field k] [CharZero k] (m n : ℕ)
    (i : Fin (m * n)) : Derivation k (GenericField k m n) (GenericField k m n) :=
  ((parameterDifferentialBasis k m n).coord i).compDer
    (KaehlerDifferential.D k (GenericField k m n))

theorem parameterPartial_parameterMap
    (k : Type*) [Field k] [CharZero k] (m n : ℕ)
    (i : Fin (m * n)) (f : ParameterRing k m n) :
    parameterPartial k m n i (parameterMap k m n f) =
      parameterMap k m n (pderiv i f) :=
  parameterDifferentialBasis_repr_D k m n f i

theorem parameterPartial_genericNormal
    (k : Type*) [Field k] [CharZero k] (m n : ℕ)
    (a r : Fin m) (b c : Fin n) :
    parameterPartial k m n (finProdFinEquiv (a, b)) (genericNormal k m n r c) =
      if a = r ∧ b = c then 1 else 0 := by
  classical
  rw [genericNormal, parameterPartial_parameterMap]
  simp [pderiv_X, Pi.single_apply, eq_comm]

/-- Chain rule for evaluation at coordinates in an arbitrary field extension. -/
theorem derivation_aeval {k E σ : Type*} [Field k] [Field E] [Algebra k E]
    [Fintype σ] (D : Derivation k E E) (x : σ → E) (F : MvPolynomial σ k) :
    D (aeval x F) = ∑ i, aeval x (pderiv i F) * D (x i) := by
  classical
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add F G hF hG => simp [hF, hG, add_mul, Finset.sum_add_distrib]
  | mul_X F j hF =>
    simp only [map_mul, aeval_X, Derivation.leibniz, map_add,
      smul_eq_mul, hF]
    simp only [pderiv_X, Pi.single_apply, apply_ite, map_one, map_zero]
    simp only [add_mul, Finset.sum_add_distrib]
    simp [Finset.mul_sum, mul_comm, mul_left_comm]

/-- In a relation between the gradient and the generic normal rows, all
normal-row coefficients vanish at every nonzero common zero. -/
theorem generic_normal_relation_coefficients_eq_zero
    {k : Type*} [Field k] [CharZero k] {m n : ℕ}
    (F : MvPolynomial (Fin n) k) (x : Fin n → GenericField k m n)
    (hx : x ≠ 0) (hF : aeval x F = 0)
    (hγ : (genericNormal k m n).mulVec x = 0)
    (a₀ : GenericField k m n) (a : Fin m → GenericField k m n)
    (ha : ∀ c, a₀ * aeval x (pderiv c F) +
      ∑ r, a r * genericNormal k m n r c = 0) : a = 0 := by
  classical
  obtain ⟨b, hb⟩ : ∃ b, x b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  ext j
  let D := parameterPartial k m n (finProdFinEquiv (j, b))
  have hDF : ∑ c, aeval x (pderiv c F) * D (x c) = 0 := by
    rw [← derivation_aeval, hF, map_zero]
  have hDγ (r : Fin m) :
      (∑ c, genericNormal k m n r c * D (x c)) =
        -(if j = r then x b else 0) := by
    have hrow : ∑ c, genericNormal k m n r c * x c = 0 :=
      congrFun hγ r
    have hd := congrArg D hrow
    simp only [map_sum, Derivation.leibniz, smul_eq_mul, map_zero,
      Finset.sum_add_distrib, D, parameterPartial_genericNormal] at hd
    by_cases hjr : j = r
    · simpa [hjr, D] using eq_neg_of_add_eq_zero_left hd
    · simpa [hjr, D] using eq_neg_of_add_eq_zero_left hd
  have hcombine : a₀ * (∑ c, aeval x (pderiv c F) * D (x c)) +
      ∑ r, a r * (∑ c, genericNormal k m n r c * D (x c)) = 0 := by
    calc
      _ = (∑ c, a₀ * aeval x (pderiv c F) * D (x c)) +
          ∑ r, ∑ c, a r * genericNormal k m n r c * D (x c) := by
        simp only [Finset.mul_sum, mul_assoc]
      _ = (∑ c, a₀ * aeval x (pderiv c F) * D (x c)) +
          ∑ c, ∑ r, a r * genericNormal k m n r c * D (x c) := by
        rw [Finset.sum_comm]
      _ = ∑ c, (a₀ * aeval x (pderiv c F) +
          ∑ r, a r * genericNormal k m n r c) * D (x c) := by
        simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
      _ = 0 := by simp only [ha, zero_mul, Finset.sum_const_zero]
  have hprod : a j * x b = 0 := by
    simpa [hDF, hDγ, mul_ite, Finset.sum_neg_distrib] using hcombine
  exact (mul_eq_zero.mp hprod).resolve_right hb

/-- The generic section is smooth at every common zero where the original
hypersurface is smooth. This is a theorem about the literal augmented matrix. -/
theorem generic_augmented_rank_of_gradient_ne_zero
    {k : Type*} [Field k] [CharZero k] {m n : ℕ}
    (F : MvPolynomial (Fin n) k) (x : Fin n → GenericField k m n)
    (hx : x ≠ 0) (hF : aeval x F = 0)
    (hγ : (genericNormal k m n).mulVec x = 0)
    (hgrad : ∃ i, aeval x (pderiv i F) ≠ 0) :
    (ProjectiveLinearSectionJacobian.augmentedSectionJacobian
      (map (algebraMap k (GenericField k m n)) F) (genericNormal k m n) x).rank =
        m + 1 := by
  classical
  suffices h : (ProjectiveLinearSectionJacobian.augmentedSectionJacobian
      (map (algebraMap k (GenericField k m n)) F) (genericNormal k m n) x).rank =
        Fintype.card (Fin (m + 1)) by
    simpa only [Fintype.card_fin] using h
  apply (PolynomialMatrixRankSpreading.fullRowRank_iff_no_row_relation _).mpr
  intro a ha
  have hrel (c : Fin n) : a 0 * aeval x (pderiv c F) +
      ∑ r : Fin m, a r.succ * genericNormal k m n r c = 0 := by
    simpa [ProjectiveLinearSectionJacobian.augmentedSectionJacobian,
      Fin.sum_univ_succ, pderiv_map, eval_map, aeval_def] using ha c
  have hnormal : (fun r : Fin m ↦ a r.succ) = 0 :=
    generic_normal_relation_coefficients_eq_zero F x hx hF hγ (a 0) _ hrel
  obtain ⟨i, hi⟩ := hgrad
  have hzero : a 0 = 0 := by
    have hh := hrel i
    simp only [show ∀ r : Fin m, a r.succ = 0 from fun r ↦ congrFun hnormal r,
      zero_mul, Finset.sum_const_zero, add_zero] at hh
    exact (mul_eq_zero.mp hh).resolve_right hi
  ext r
  exact Fin.cases hzero (fun j ↦ congrFun hnormal j) r

/-- A critical point of the actual generic section is singular on the
original hypersurface. No smoothness assumption on that hypersurface is used. -/
theorem generic_critical_implies_original_singular
    {k : Type*} [Field k] [CharZero k] {m n : ℕ}
    (F : MvPolynomial (Fin n) k) (x : Fin n → GenericField k m n)
    (hx : x ≠ 0) (hF : aeval x F = 0)
    (hγ : (genericNormal k m n).mulVec x = 0)
    (hcritical : (ProjectiveLinearSectionJacobian.augmentedSectionJacobian
      (map (algebraMap k (GenericField k m n)) F) (genericNormal k m n) x).rank ≠
        m + 1) : ∀ i, aeval x (pderiv i F) = 0 := by
  intro i
  by_contra hi
  exact hcritical (generic_augmented_rank_of_gradient_ne_zero F x hx hF hγ ⟨i, hi⟩)

end CubicTenVariables.GenericNormalDerivations

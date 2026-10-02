import CubicTenVariables.Targets
import HessianTheorem11.PolarizationExpansion
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Separable

/-! Nonzero nonsingular real points of anisotropic rational cubics. The
argument uses a literal binary rational restriction, irreducibility and
separability of its univariate cubic, and the proved real-polynomial root
criterion. No local-solubility theorem is assumed. -/
noncomputable section
namespace CubicTenVariables.RealPlace
open MvPolynomial HessianTheorem11

/-- Actual substitution on the affine line v+t u, with rational coefficients. -/
def linePolynomial {n : ℕ} (F : RationalPolynomial n) (u v : Fin n → ℚ) :
    Polynomial ℚ :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (v i) + Polynomial.X * Polynomial.C (u i)) F

theorem linePolynomial_eval₂ {n : ℕ} (F : RationalPolynomial n)
    (u v : Fin n → ℚ) {K : Type*} [Field K] (f : ℚ →+* K) (t : K) :
    (linePolynomial F u v).eval₂ f t =
      MvPolynomial.eval₂ f (fun i => f (v i) + t * f (u i)) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [linePolynomial]
  | add P Q hP hQ => simp [linePolynomial] at hP hQ ⊢; rw [hP, hQ]
  | mul_X P i hP => simp [linePolynomial] at hP ⊢; rw [hP]; ring

/-- Formal differentiation of the line substitution is the actual
ambient gradient paired with its rational direction, over any extension. -/
theorem linePolynomial_derivative_eval₂ {n : ℕ} (F : RationalPolynomial n)
    (u v : Fin n → ℚ) {K : Type*} [Field K] (f : ℚ →+* K) (t : K) :
    (linePolynomial F u v).derivative.eval₂ f t =
      ∑ i, MvPolynomial.eval₂ f (fun j => f (v j) + t * f (u j)) (pderiv i F) * f (u i) := by
  classical
  induction F using MvPolynomial.induction_on with
  | C c => simp [linePolynomial]
  | add P Q hP hQ =>
      simp only [linePolynomial, map_add,
        Polynomial.eval₂_add, hP, hQ, MvPolynomial.eval₂_add,
        add_mul, Finset.sum_add_distrib] at *
  | mul_X P k hP =>
      have hp := linePolynomial_eval₂ P u v f t
      simp only [linePolynomial, map_mul, MvPolynomial.eval₂Hom_X'] at *
      rw [Polynomial.derivative_mul, Polynomial.eval₂_add, Polynomial.eval₂_mul,
        Polynomial.eval₂_mul, hP, hp]
      simp only [Polynomial.derivative_add, Polynomial.derivative_C,
        Polynomial.derivative_mul, Polynomial.derivative_X, zero_add, one_mul,
        mul_zero, add_zero, Polynomial.eval₂_add, Polynomial.eval₂_mul,
        Polynomial.eval₂_C, Polynomial.eval₂_X, pderiv_mul, pderiv_X,
        MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
        add_mul, Finset.sum_add_distrib]
      simp only [Pi.single_apply, apply_ite, MvPolynomial.eval₂_one,
        MvPolynomial.eval₂_zero, mul_one, mul_zero, zero_mul,
        ite_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The actual line restriction has this explicit rational cubic expression. -/
theorem linePolynomial_cubic {n : ℕ} (F : RationalPolynomial n)
    (hF : F.IsHomogeneous 3) (u v : Fin n → ℚ) :
    linePolynomial F u v =
      Polynomial.C (eval u F) * Polynomial.X ^ 3 +
      Polynomial.C ((1/2 : ℚ) * polarization F v u u) * Polynomial.X ^ 2 +
      Polynomial.C ((1/2 : ℚ) * polarization F v v u) * Polynomial.X +
      Polynomial.C (eval v F) := by
  apply Polynomial.funext
  intro t
  have he := linePolynomial_eval₂ F u v (RingHom.id ℚ) t
  simp only [Polynomial.eval₂_id, RingHom.id_apply, MvPolynomial.eval₂_id] at he
  rw [he]
  have hvec : (fun i => v i + t * u i) = v + t • u := rfl
  rw [hvec, eval_cubic_add hF]
  simp only [eval_cubic_eq_polarization hF, polarization_smul_first,
    polarization_smul_second, polarization_smul_third hF, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring

theorem linePolynomial_natDegree {n : ℕ} (F : RationalPolynomial n)
    (hF : F.IsHomogeneous 3) (u v : Fin n → ℚ) (hu : eval u F ≠ 0) :
    (linePolynomial F u v).natDegree = 3 := by
  rw [linePolynomial_cubic F hF u v]
  compute_degree!

/-- Every real polynomial of degree three has an actual real root. The
proof uses mathlib's proved degree bound for irreducible real polynomials. -/
theorem exists_real_root_of_natDegree_three (P : Polynomial ℝ) (hP : P.natDegree = 3) :
    ∃ t : ℝ, P.eval t = 0 := by
  by_contra hn
  have hnot : ∀ t, ¬ P.IsRoot t := by simpa only [not_exists, Polynomial.IsRoot] using hn
  have hi := Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (p := P) (by simp [hP]) hnot
  have hb := hi.natDegree_le_two
  omega

/-- An anisotropic rational cubic in at least two variables has a nonzero
real zero at which the actual formal gradient is nonzero. -/
theorem exists_nonsingular_real_zero {n : ℕ} (F : AnisotropicCubic n) (hn : 2 ≤ n) :
    ∃ x : Fin n → ℝ, x ≠ 0 ∧
      eval x (map (algebraMap ℚ ℝ) F.polynomial) = 0 ∧
      gradient (map (algebraMap ℚ ℝ) F.polynomial) x ≠ 0 := by
  classical
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  let u : Fin n → ℚ := Pi.single i 1
  let v : Fin n → ℚ := Pi.single j 1
  have hu : u ≠ 0 := by intro h; have he := congrFun h i; simp [u] at he
  have hlead := anisotropic_eval_ne_zero F.anisotropic hu
  let P := linePolynomial F.polynomial u v
  have hd : P.natDegree = 3 := linePolynomial_natDegree F.polynomial F.homogeneous u v hlead
  have hnoroot : ∀ t : ℚ, ¬ P.IsRoot t := by
    intro t ht
    have hvect : (fun k => v k + t * u k) ≠ 0 := by
      intro h
      have he := congrFun h j
      simp [u, v, Ne.symm hij] at he
    apply hvect
    apply F.anisotropic
    have he := linePolynomial_eval₂ F.polynomial u v (RingHom.id ℚ) t
    simpa only [Polynomial.eval₂_id, RingHom.id_apply, MvPolynomial.eval₂_id] using he.symm.trans ht
  have hi : Irreducible P := Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (by simp [hd]) hnoroot
  obtain ⟨t, ht⟩ := exists_real_root_of_natDegree_three (P.map (algebraMap ℚ ℝ))
    (by rw [Polynomial.natDegree_map]; exact hd)
  have ht' : P.eval₂ (algebraMap ℚ ℝ) t = 0 := by simpa using ht
  have hderiv := hi.separable.eval₂_derivative_ne_zero (algebraMap ℚ ℝ) ht'
  let x : Fin n → ℝ := fun k => algebraMap ℚ ℝ (v k) + t * algebraMap ℚ ℝ (u k)
  have hx : x ≠ 0 := by
    intro h
    have he := congrFun h j
    simp [x, u, v, Ne.symm hij] at he
  refine ⟨x, hx, ?_, ?_⟩
  · rw [← MvPolynomial.eval₂_eq_eval_map]
    exact (linePolynomial_eval₂ F.polynomial u v (algebraMap ℚ ℝ) t).symm.trans ht'
  · intro hgrad
    apply hderiv
    rw [show P = linePolynomial F.polynomial u v from rfl,
      linePolynomial_derivative_eval₂]
    apply Finset.sum_eq_zero
    intro k _
    have he := congrFun hgrad k
    change eval x (pderiv k (map (algebraMap ℚ ℝ) F.polynomial)) = 0 at he
    rw [pderiv_map, ← MvPolynomial.eval₂_eq_eval_map] at he
    exact mul_eq_zero_of_left he _

end CubicTenVariables.RealPlace

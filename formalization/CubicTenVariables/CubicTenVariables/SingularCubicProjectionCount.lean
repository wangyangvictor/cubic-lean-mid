import CubicTenVariables.SingularCubicFiberCount
import CubicTenVariables.SingularCubicLinearFibers
import CubicTenVariables.ReducedVertexBaseChange
import CubicTenVariables.CoprimeCommonZeroCount

/-! Literal singular-point projection for a nonconical cubic. The quadratic
coefficient in the constructed chart is nonzero; its ordinary zero count is
bounded by Schwartz--Zippel. The common-zero estimate is kept explicit until
the coprime-intersection argument supplies it. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.SingularCubicProjectionCount
open MvPolynomial HessianTheorem11 CubicSingularQuotient
open SingularCubicLinearFibers SingularCubicFiberCount

variable {K : Type*} [Field K] {n : ℕ}

theorem translation_of_section_quadratic_zero
    (F : MvPolynomial (Fin (n+1)) K) (hF : F.IsHomogeneous 3)
    (z : Fin (n+1) → K) (hzero : eval z F=0) (hsing : gradient F z=0)
    (i : Fin (n+1)) (hi : z i ≠ 0)
    (hQ : zeroSection i (quadraticPolynomial F z)=0) :
    ReducedCubicVertex.TranslationDirection F z := by
  intro x t
  let u := chartEquiv z i hi x
  have hx : x=i.insertNth 0 u.1+u.2 • z :=
    ((chartEquiv z i hi).symm_apply_apply x).symm
  have hq : eval (i.insertNth 0 u.1) (quadraticPolynomial F z)=0 := by
    rw [← eval_section,hQ,map_zero]
  rw [hx,show (i.insertNth 0 u.1+u.2 • z)+t • z=
      i.insertNth 0 u.1+(u.2+t) • z by rw [add_smul,add_assoc]]
  rw [eval_singular_line F hF z hzero hsing,
    eval_singular_line F hF z hzero hsing,hq]
  simp

theorem hessian_kernel_trivial_of_geometricallyNonconical
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (hNC : Literature.GeometricallyNonconicalCubic F)
    (z : Fin n → K) (hz : hessian F z=0) : z=0 := by
  have hbar := (Literature.geometricallyNonconicalCubic_iff_hessian F hF h2 h3).mp hNC
  have hb : hessian (map (algebraMap K (AlgebraicClosure K)) F)
      (fun j => algebraMap K (AlgebraicClosure K) (z j))=0 := by
    rw [ReducedVertexBaseChange.hessian_map_point F hF,hz]
    ext i j
    simp
  have he := hbar _ hb
  funext j
  exact (algebraMap K (AlgebraicClosure K)).injective
    (by simpa only [Pi.zero_apply,map_zero] using congrFun he j)

/-- Nonconicality rules out a zero quadratic coefficient at the chosen
singular point. This uses actual polynomial vanishing in the finite chart. -/
theorem section_quadratic_ne_zero
    (F : MvPolynomial (Fin (n+1)) K) (hF : F.IsHomogeneous 3)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (hNC : Literature.GeometricallyNonconicalCubic F)
    (z : Fin (n+1) → K) (hzero : eval z F=0) (hsing : gradient F z=0)
    (i : Fin (n+1)) (hi : z i ≠ 0) :
    zeroSection i (quadraticPolynomial F z) ≠ 0 := by
  intro hQ
  have ht := translation_of_section_quadratic_zero F hF z hzero hsing i hi hQ
  have hh := ReducedCubicVertex.hessian_zero_of_translation F hF h2 z ht
  have hz := hessian_kernel_trivial_of_geometricallyNonconical F hF h2 h3 hNC z hh
  exact hi (by rw [hz]; rfl)

/-- The actual affine point-count error, with all coordinate changes and
the individual quadratic point bound discharged internally. -/
theorem bound_of_common_zero_bound [Fintype K]
    (hn : 2 ≤ n) (F : MvPolynomial (Fin (n+1)) K) (hF : F.IsHomogeneous 3)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (hNC : Literature.GeometricallyNonconicalCubic F)
    (z : Fin (n+1) → K) (hzero : eval z F=0) (hsing : gradient F z=0)
    (i : Fin (n+1)) (hi : z i ≠ 0)
    (A : ℝ) (hI : (Nat.card {y : Fin n → K //
      eval y (zeroSection i (quadraticPolynomial F z))=0 ∧ eval y (zeroSection i F)=0} : ℝ) ≤
        A*(Fintype.card K : ℝ)^(n-2)) :
    |(Literature.affineZeroCount F : ℝ)-(Fintype.card K : ℝ)^n| ≤
      (A+2)*(Fintype.card K : ℝ)^(n-1) := by
  apply abs_projection_error_le hn F
    (zeroSection i (quadraticPolynomial F z)) (zeroSection i F)
    (section_quadratic_ne_zero F hF h2 h3 hNC z hzero hsing i hi)
    (homogeneous_section i _ (homogeneous_quadraticPolynomial F hF z)).totalDegree_le
    (chartEquiv z i hi) _ A hI
  intro x
  have h := eval_chart F hF z hzero hsing i hi (chartEquiv z i hi x)
  simpa only [Equiv.symm_apply_apply] using h

/-- Uniform bound for the literal cubic, once relative primality of the
two constructed section polynomials is supplied. The constant is chosen
before the prime, coefficients, singular point, and coordinate chart. -/
theorem exists_prime_bound_of_coprime (n : ℕ) (hn : 2 ≤ n) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (p : ℕ) [Fact p.Prime]
      (F : MvPolynomial (Fin (n+1)) (ZMod p)), F.IsHomogeneous 3 →
      (2 : ZMod p) ≠ 0 → (3 : ZMod p) ≠ 0 →
      Literature.GeometricallyNonconicalCubic F →
      ∀ (z : Fin (n+1) → ZMod p), eval z F=0 → gradient F z=0 →
      ∀ (i : Fin (n+1)), z i ≠ 0 →
      IsRelPrime (zeroSection i (quadraticPolynomial F z)) (zeroSection i F) →
      |(Literature.affineZeroCount F : ℝ)-(p : ℝ)^n| ≤
        B*((p : ℝ)-1)*(p : ℝ)^(n-2) := by
  obtain ⟨A,hA,hcount⟩ := CoprimeCommonZeroCount.exists_quadratic_cubic_prime_bound n hn
  have hB : 1 ≤ 2*((A : ℝ)+2) := by
    have ha : (0 : ℝ) ≤ A := by positivity
    linarith
  refine ⟨2*((A : ℝ)+2),hB,?_⟩
  intro p hp F hF h2 h3 hNC z hzero hsing i hi hcop
  have hI := hcount p (zeroSection i (quadraticPolynomial F z)) (zeroSection i F)
    (section_quadratic_ne_zero F hF h2 h3 hNC z hzero hsing i hi)
    (homogeneous_section i _ (homogeneous_quadraticPolynomial F hF z)).totalDegree_le
    (homogeneous_section i F hF).totalDegree_le hcop
  have hI' : (Nat.card {y : Fin n → ZMod p //
      eval y (zeroSection i (quadraticPolynomial F z))=0 ∧ eval y (zeroSection i F)=0} : ℝ) ≤
      (A : ℝ)*(Fintype.card (ZMod p) : ℝ)^(n-2) := by
    simpa only [ZMod.card] using (show
      (Nat.card {y : Fin n → ZMod p //
        eval y (zeroSection i (quadraticPolynomial F z))=0 ∧ eval y (zeroSection i F)=0} : ℝ) ≤
      (A : ℝ)*(p : ℝ)^(n-2) by exact_mod_cast hI)
  have hb := bound_of_common_zero_bound hn F hF h2 h3 hNC z hzero hsing i hi A hI'
  simp only [ZMod.card] at hb
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
  have hpow : (p : ℝ)^(n-1)=(p : ℝ)*(p : ℝ)^(n-2) := by
    rw [← pow_succ']
    congr 1
    omega
  apply hb.trans
  rw [hpow]
  calc
    _ = ((A : ℝ)+2)*(p : ℝ)*(p : ℝ)^(n-2) := by ring
    _ ≤ ((A : ℝ)+2)*(2*((p : ℝ)-1))*(p : ℝ)^(n-2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (by positivity)
    _ = _ := by ring

end CubicTenVariables.SingularCubicProjectionCount

import CubicTenVariables.EssentialVariables
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Explicit p-adic specialization of Pleasants's local-zero theorem

P. A. B. Pleasants, *Forms over p-adic fields*, Acta Arithmetica 18 (1971),
289–296, Theorem 2 on printed p. 295; DOI 10.4064/aa-18-1-289-296.
Primary scan: https://matwbn.icm.edu.pl/ksiazki/aa/aa18/aa18131.pdf .
The cached primary renders `source/literature/Pleasants1971/pages-290-291.png`
and `pages-294-295.png` were visually rechecked for this interface.

On p. 290, the order of a form is the smallest number of explicit variables
after an invertible linear coordinate change over its coefficient field.
The valued field is complete, discretely nonarchimedean, with finite residue
field. Theorem 2 asserts a nonsingular zero for a cubic of order at least
ten. There is no restriction on residue characteristic or residue-field
cardinality, so its Q_p specialization includes p = 2 and p = 3.

`LinearOrderAtLeast r F` below uses an explicit sufficient condition for the
published order bound: F is not a polynomial in any list of fewer than r
actual linear forms. Indeed an invertible change leaving only m variables
expresses F in the m corresponding coordinate forms of that change (or its
inverse). Such a representation is among the matrices A and polynomials G
quantified below. Thus the condition rules out published order < r; this
does not rely on an independently supplied numerical order invariant.
Allowing arbitrary G makes the written premise at least as strong as the
required exclusion of homogeneous cubic representations.

The literature proposition is quantified over arbitrary homogeneous cubics
over Q_p, independently of rational anisotropy. It is an explicit argument,
not an axiom, instance, or inhabitant. The later application proves its
essential-variable premise using `EssentialVariables`. The original local-existence interface is now proved internally by
`CubicTenVariables.PleasantsProved.proved`; the adapters below retain their
explicit proposition argument for reuse.

No integrality, primitivity, symmetric-tensor convention, or multiplication
by six is required: coefficients and zeros lie in Q_p. Nonsingularity is
literal nonvanishing of a formal first partial. The included nonzero-vector
condition follows also from homogeneity of degree three, whose first
partials vanish at the origin. No local density or singular-series
positivity theorem is asserted here.
-/

noncomputable section
namespace CubicTenVariables.Literature
open MvPolynomial HessianTheorem11

/-- A concrete sufficient condition for variable-order at least `r`: there
is no literal polynomial pullback along fewer than `r` linear forms. -/
def LinearOrderAtLeast {K : Type*} [Field K] {n : ℕ}
    (r : ℕ) (F : MvPolynomial (Fin n) K) : Prop :=
  ∀ (m : ℕ), m < r → ∀ (A : Matrix (Fin m) (Fin n) K)
    (G : MvPolynomial (Fin m) K),
    F ≠ aeval (fun i => ∑ j, C (A i j) * X j) G

/-- Every actual displayed linear-form representation satisfies the stated
variable lower bound. In particular this applies to coordinate-change
representations occurring in the published definition of order. -/
theorem variables_le_of_linearOrderAtLeast {K : Type*} [Field K] {r m n : ℕ}
    {F : MvPolynomial (Fin n) K} (hF : LinearOrderAtLeast r F)
    (A : Matrix (Fin m) (Fin n) K) (G : MvPolynomial (Fin m) K)
    (hFG : F = aeval (fun i => ∑ j, C (A i j) * X j) G) : r ≤ m := by
  by_contra hrm
  exact hF m (Nat.lt_of_not_ge hrm) A G hFG

/-- The scalar extension of a rational anisotropic cubic satisfies the
literal essential-variable condition, with no geometric premise. -/
theorem linearOrderAtLeast_baseChange {K : Type*} [Field K] [Algebra ℚ K]
    {n : ℕ} (F : AnisotropicCubic n) (r : ℕ) (hr : r ≤ n) :
    LinearOrderAtLeast r (map (algebraMap ℚ K) F.polynomial) := by
  intro m hm A G
  exact EssentialVariables.not_baseChange_eq_aeval_linearForms_of_lt
    F.polynomial F.homogeneous F.anisotropic (lt_of_lt_of_le hm hr) A G

/-- Pleasants 1971, Theorem 2, specialized to Q_p and the explicitly
displayed sufficient order condition. The original proposition is retained
verbatim and is inhabited by `CubicTenVariables.PleasantsProved.proved`.
The conditional adapters below continue to accept it explicitly. -/
def Pleasants1971Theorem2Qp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (F : MvPolynomial (Fin n) ℚ_[p]),
    F.IsHomogeneous 3 → LinearOrderAtLeast 10 F →
    ∃ x : Fin n → ℚ_[p], x ≠ 0 ∧ eval x F = 0 ∧
      ∃ i : Fin n, eval x (pderiv i F) ≠ 0

/-- Conditional local application. Essentiality after scalar extension is
proved; existence of the p-adic zero is precisely the literature argument. -/
theorem padic_nonsingular_zero_of_pleasants
    (pleasants : Pleasants1971Theorem2Qp) {n : ℕ} (F : AnisotropicCubic n)
    (hn : 10 ≤ n) (p : ℕ) [Fact p.Prime] :
    ∃ x : Fin n → ℚ_[p], x ≠ 0 ∧
      eval x (map (algebraMap ℚ ℚ_[p]) F.polynomial) = 0 ∧
      ∃ i : Fin n, eval x (pderiv i (map (algebraMap ℚ ℚ_[p]) F.polynomial)) ≠ 0 :=
  pleasants p n _ (F.homogeneous.map _) (linearOrderAtLeast_baseChange F 10 hn)

/-- The same conditional conclusion in literal coefficient-extension
evaluation, matching the local geometry API. -/
theorem padic_eval₂_nonsingular_zero_of_pleasants
    (pleasants : Pleasants1971Theorem2Qp) {n : ℕ} (F : AnisotropicCubic n)
    (hn : 10 ≤ n) (p : ℕ) [Fact p.Prime] :
    ∃ x : Fin n → ℚ_[p], x ≠ 0 ∧
      eval₂ (algebraMap ℚ ℚ_[p]) x F.polynomial = 0 ∧
      ∃ i : Fin n, eval₂ (algebraMap ℚ ℚ_[p]) x (pderiv i F.polynomial) ≠ 0 := by
  obtain ⟨x, hx, hzero, i, hi⟩ := padic_nonsingular_zero_of_pleasants pleasants F hn p
  exact ⟨x, hx, by simpa only [eval_map] using hzero,
    i, by simpa only [pderiv_map, eval_map] using hi⟩

end CubicTenVariables.Literature

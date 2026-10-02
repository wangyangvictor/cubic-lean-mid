import CubicTenVariables.FiniteFieldTraceCharacter
import CubicTenVariables.ProjectiveFourierIdentity
import Mathlib.FieldTheory.Finite.GaloisField

/-! Literal polynomial exponential-sum families. The parameter variables
are coefficient variables and the summation variables are outer variables.
No sheaf predicate, weight theorem or trace dichotomy is hidden in these
definitions. The cubic Fourier family is identified with its actual sum. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.PolynomialExponentialFamily
open MvPolynomial Matrix
open scoped BigOperators Classical

abbrev ParameterPolynomial (n : ℕ) := MvPolynomial (Fin n) ℤ
abbrev FamilyPolynomial (n m : ℕ) := MvPolynomial (Fin m) (ParameterPolynomial n)

/-- The rational base ideal of the specified integral equations. -/
abbrev baseIdeal {n t : ℕ} (G : Fin t → ParameterPolynomial n) :=
  Ideal.span (Set.range (fun i => map (Int.castRingHom ℚ) (G i)))

/-- Evaluation of the parameter coefficients, retaining the summation variables. -/
def specialize {n m : ℕ} (P : FamilyPolynomial n m)
    {K : Type*} [CommRing K] (y : Fin n → K) : MvPolynomial (Fin m) K :=
  map (eval₂Hom (Int.castRingHom K) y) P

/-- The actual principal-open parameter points over a finite field. -/
def parameterPoints {n t : ℕ} (G : Fin t → ParameterPolynomial n)
    (g : ParameterPolynomial n) (K : Type*) [Field K] [Fintype K] : Finset (Fin n → K) :=
  Finset.univ.filter fun y =>
    (∀ i, eval y (map (Int.castRingHom K) (G i)) = 0) ∧
      eval y (map (Int.castRingHom K) g) ≠ 0

theorem mem_parameterPoints {n t : ℕ} (G : Fin t → ParameterPolynomial n)
    (g : ParameterPolynomial n) (K : Type*) [Field K] [Fintype K] (y : Fin n → K) :
    y ∈ parameterPoints G g K ↔
      (∀ i, eval y (map (Int.castRingHom K) (G i)) = 0) ∧
        eval y (map (Int.castRingHom K) g) ≠ 0 := by
  simp [parameterPoints]

/-- Requiring a coordinate as a factor removes the zero frequency in
every characteristic, with no additional exceptional prime. -/
theorem parameterPoint_ne_zero_of_coordinate_dvd {n t : ℕ}
    (G : Fin t → ParameterPolynomial n) (g : ParameterPolynomial n)
    (i : Fin n) (hg : X i ∣ g) {K : Type*} [Field K] [Fintype K]
    (y : Fin n → K) (hy : y ∈ parameterPoints G g K) : y ≠ 0 := by
  intro hzero
  obtain ⟨q, rfl⟩ := hg
  have h := ((mem_parameterPoints G (X i * q) K y).mp hy).2
  subst y
  simp at h

/-- An exponential sum on the literal polynomial fiber. -/
def fiberSum {n m s : ℕ} (H : Fin s → FamilyPolynomial n m)
    (P : FamilyPolynomial n m) {K : Type*} [Field K] [Fintype K]
    (ψ : AddChar K ℂ) (y : Fin n → K) : ℂ :=
  ∑ x : Fin m → K,
    if ∀ i, eval x (specialize (H i) y) = 0
    then ψ (eval x (specialize P y)) else 0

/-- A field of cardinality p^a for a≥1. The harmless a=0 field is
defined too; no assertion that it has cardinality one is made. -/
abbrev Extension (p : ℕ) [Fact p.Prime] (a : ℕ) := GaloisField p a

instance extensionFintype (p : ℕ) [Fact p.Prime] (a : ℕ) : Fintype (Extension p a) :=
  Fintype.ofFinite _

theorem extension_card (p : ℕ) [Fact p.Prime] (a : ℕ) (ha : 1 ≤ a) :
    Fintype.card (Extension p a) = p^a := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card p a (by omega)

/-- A hypersurface equation independent of the parameter. -/
def hypersurface {n : ℕ} (F : ParameterPolynomial n) : Fin 1 → FamilyPolynomial n n :=
  fun _ => map C F

/-- The actual bilinear Fourier phase x·y. -/
def fourierPhase (n : ℕ) : FamilyPolynomial n n :=
  ∑ i : Fin n, C (X i) * X i

theorem specialize_hypersurface {n : ℕ} (F : ParameterPolynomial n)
    {K : Type*} [CommRing K] (y : Fin n → K) (i : Fin 1) :
    specialize (hypersurface F i) y = map (Int.castRingHom K) F := by
  unfold specialize hypersurface
  rw [MvPolynomial.map_map]
  have hm : (eval₂Hom (Int.castRingHom K) y).comp C = Int.castRingHom K := by
    ext z
    simp only [RingHom.comp_apply, eval₂Hom_C]
  rw [hm]

theorem eval_fourierPhase {n : ℕ} {K : Type*} [CommRing K]
    (y x : Fin n → K) : eval x (specialize (fourierPhase n) y) = dotProduct y x := by
  simp [specialize, fourierPhase, dotProduct, eval_mul]

/-- The generic family really is the cubic Fourier sum on the zero
fiber, with the same trace-extension character as the moment theorem. -/
theorem fiberSum_hypersurface {n : ℕ} (F : ParameterPolynomial n)
    {K : Type*} [Field K] [Fintype K] (ψ : AddChar K ℂ) (y : Fin n → K) :
    fiberSum (hypersurface F) (fourierPhase n) ψ y =
      ∑ x : Fin n → K, if eval x (map (Int.castRingHom K) F) = 0
        then ψ (dotProduct y x) else 0 := by
  simp [fiberSum, specialize_hypersurface, eval_fourierPhase]

theorem fiberSum_eq_normalized {n : ℕ} (F : ParameterPolynomial n)
    {K : Type*} [Field K] [Fintype K] (ψ : AddChar K ℂ)
    (y : Fin n → K) (hy : y ≠ 0) :
    fiberSum (hypersurface F) (fourierPhase n) ψ y =
      ProjectiveFourierIdentity.normalizedFourierSum ψ (map (Int.castRingHom K) F) y := by
  rw [fiberSum_hypersurface]
  simp [ProjectiveFourierIdentity.normalizedFourierSum, FiniteFieldFourier.zeroFiberSum,
    hy, Finset.sum_filter]

end CubicTenVariables.PolynomialExponentialFamily

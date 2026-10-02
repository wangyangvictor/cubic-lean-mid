import CubicTenVariables.BinarySliceCounting
import CubicTenVariables.AffinePolynomialSlice
import HessianTheorem11.RationalIrreducibility
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.Ideal

/-! Literal selected-coordinate binary families and their elementary algebra.
The complementary variables are parameters; no fiber integrality is assumed. -/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace CubicTenVariables.BinarySliceGeometry
open MvPolynomial HessianTheorem11
open BinarySliceCounting

/-- The actual polynomial on a binary affine slice. -/
def slice {n : ℕ} {R : Type*} [CommRing R] (e : Fin 2 ↪ Fin n)
    (F : MvPolynomial (Fin n) R) (w : Complement e → R) : MvPolynomial (Fin 2) R :=
  aeval (combine e X (fun i => C (w i))) F

@[simp] theorem eval_slice {n : ℕ} {R : Type*} [CommRing R]
    (e : Fin 2 ↪ Fin n) (F : MvPolynomial (Fin n) R)
    (w : Complement e → R) (z : Fin 2 → R) :
    eval z (slice e F w) = eval (combine e z w) F := by
  change aeval z (aeval _ F) = aeval _ F
  rw [comp_aeval_apply]
  have hv : (fun i => aeval z (combine e X (fun i => C (w i)) i)) = combine e z w := by
    funext i
    cases h : (indexEquiv e).symm i <;> simp [combine, h]
  rw [hv]

theorem totalDegree_slice_le {n : ℕ} {R : Type*} [CommRing R]
    (e : Fin 2 ↪ Fin n) (F : MvPolynomial (Fin n) R) (w : Complement e → R) :
    (slice e F w).totalDegree ≤ F.totalDegree := by
  apply TranslatedDepthSeven.totalDegree_aeval_le_of_totalDegree_le_one
  intro i
  cases h : (indexEquiv e).symm i
  · simpa only [combine, h, Sum.elim_inl] using (isHomogeneous_X (R := R) _).totalDegree_le
  · simp [combine, h]

/-- Splitting the selected and parameter variables is an actual ring equivalence. -/
def familyEquiv {n : ℕ} (R : Type*) [CommRing R] (e : Fin 2 ↪ Fin n) :
    MvPolynomial (Fin n) R ≃+*
      MvPolynomial (Fin 2) (MvPolynomial (Complement e) R) :=
  (renameEquiv R (indexEquiv e).symm).toRingEquiv.trans
    (sumRingEquiv R (Fin 2) (Complement e))

/-- The original polynomial, with the complementary coordinates regarded
as coefficient parameters. -/
def family {n : ℕ} {R : Type*} [CommRing R] (e : Fin 2 ↪ Fin n)
    (F : MvPolynomial (Fin n) R) :
    MvPolynomial (Fin 2) (MvPolynomial (Complement e) R) := familyEquiv R e F

@[simp] theorem family_C {n : ℕ} {R : Type*} [CommRing R]
    (e : Fin 2 ↪ Fin n) (a : R) : family e (C a) = C (C a) := by
  simp [family, familyEquiv, sumRingEquiv, mvPolynomialEquivMvPolynomial]

@[simp] theorem family_X {n : ℕ} {R : Type*} [CommRing R]
    (e : Fin 2 ↪ Fin n) (i : Fin n) :
    family e (X i : MvPolynomial (Fin n) R) =
      combine e X (fun j => C (X j)) i := by
  cases h : (indexEquiv e).symm i <;>
    simp [family, familyEquiv, sumRingEquiv, mvPolynomialEquivMvPolynomial, combine, h]

/-- Specializing the parameter polynomial gives exactly the actual binary slice. -/
theorem specialize_family {n : ℕ} {R K : Type*} [CommRing R] [CommRing K]
    (e : Fin 2 ↪ Fin n) (f : R →+* K) (F : MvPolynomial (Fin n) R)
    (w : Complement e → K) :
    map (eval₂Hom f w) (family e F) = slice e (map f F) w := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [slice]
  | add p q hp hq => simp only [family, map_add] at hp hq ⊢; simp [slice, hp, hq]
  | mul_X p i hp =>
    have hX : map (eval₂Hom f w) (family e (X i)) =
        combine e X (fun j => C (w j)) i := by
      rw [family_X]
      cases h : (indexEquiv e).symm i <;> simp [combine, h]
    change map (eval₂Hom f w) (familyEquiv R e (p * X i)) = _
    rw [map_mul, map_mul]
    change map (eval₂Hom f w) (family e p) * _ = _
    rw [hp]
    change slice e (map f p) w * map (eval₂Hom f w) (family e (X i)) = _
    rw [hX]
    simp [slice]

/-- Injectivity of the coordinate inclusion is retained at the polynomial
level: the homogeneous binary restriction is the parameter-zero slice. -/
theorem homogeneous_slice_zero {n : ℕ} {R : Type*} [CommRing R]
    (e : Fin 2 ↪ Fin n) (F : MvPolynomial (Fin n) R) {d : ℕ}
    (hF : F.IsHomogeneous d) : (slice e F 0).IsHomogeneous d := by
  unfold slice
  simpa only [one_mul] using hF.aeval (combine e (X : Fin 2 → MvPolynomial (Fin 2) R) (fun i => C ((0 : Complement e → R) i))) (show ∀ i, (combine e (X : Fin 2 → MvPolynomial (Fin 2) R) (fun i => C ((0 : Complement e → R) i)) i).IsHomogeneous 1 from by
   intro i
   cases h : (indexEquiv e).symm i <;>
     simp only [combine, h, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, C_0]
   · exact isHomogeneous_X (R := R) _
   · exact isHomogeneous_zero _ _ _)

/-- Rational anisotropy passes to the actual selected binary leading form. -/
theorem anisotropic_slice_zero {n : ℕ} (e : Fin 2 ↪ Fin n)
    (F : MvPolynomial (Fin n) ℚ) (hF : Anisotropic F) :
    Anisotropic (slice e F 0) := by
  intro z hz
  have he := hF (combine e z 0) (by simpa using hz)
  funext j
  simpa using congrFun he (e j)

/-- The binary leading cubic is irreducible over Q, with no geometric
irreducibility assertion about a binary form. -/
theorem irreducible_slice_zero {n : ℕ} (e : Fin 2 ↪ Fin n)
    (F : MvPolynomial (Fin n) ℚ) (hF : F.IsHomogeneous 3) (hA : Anisotropic F) :
    Irreducible (slice e F 0) :=
  anisotropic_cubic_irreducible
    ⟨slice e F 0, homogeneous_slice_zero e F hF, anisotropic_slice_zero e F hA⟩
    (by norm_num)

end CubicTenVariables.BinarySliceGeometry

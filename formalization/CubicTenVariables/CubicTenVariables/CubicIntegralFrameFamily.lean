import CubicTenVariables.IntegralCubicBertiniFrame
import CubicTenVariables.ReducedHyperplaneIntegrality

/-! Literal full-frame parameters for the integral nine-to-five-variable
section. This module transports the proved extension-field section into an
actual specialization of one polynomial family. It does not infer generic
integrality or a finite-field certificate from that specialization. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CubicIntegralFrameFamily
open MvPolynomial HessianTheorem11.PolynomialRestriction
open ReducedHyperplaneIntegrality
universe u

/-- The existing integer universal frame, with coefficients extended to R. -/
def frame (R : Type*) [CommRing R] (n m : ℕ) :
    Matrix (Fin n) (Fin m) (MvPolynomial (Parameters n m) R) :=
  (universalFrame (n := n) (m := m)).map (map (Int.castRingHom R))

/-- The literal restriction to the universal full frame. -/
def polynomial {R : Type*} [CommRing R] {n m : ℕ}
    (F : MvPolynomial (Fin n) R) :
    MvPolynomial (Fin m) (MvPolynomial (Parameters n m) R) :=
  restrict (frame R n m) (map C F)

@[simp] theorem frame_apply {R : Type*} [CommRing R] {n m : ℕ}
    (i : Fin n) (j : Fin m) : frame R n m i j = X (i,j) := by
  simp only [frame, Matrix.map_apply, universalFrame, map_X]

/-- Every matrix over every coefficient specialization is an actual fiber. -/
theorem specialize {R K : Type*} [CommRing R] [CommRing K] {n m : ℕ}
    (F : MvPolynomial (Fin n) R) (ρ : R →+* K)
    (B : Matrix (Fin n) (Fin m) K) :
    map (eval₂Hom ρ (fun ij => B ij.1 ij.2)) (polynomial (m := m) F) =
      restrict B (map ρ F) := by
  have hc : (eval₂Hom ρ (fun ij : Parameters n m => B ij.1 ij.2)).comp
      (C : R →+* MvPolynomial (Parameters n m) R) = ρ := by
    ext a
    exact eval₂Hom_C _ _ _
  rw [polynomial, map_restrict, map_map, hc]
  congr 1
  ext i j
  simp only [Matrix.map_apply, frame_apply, eval₂Hom_X']

theorem homogeneous {R : Type*} [CommRing R] {n m d : ℕ}
    (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous d) :
    (polynomial (m := m) F).IsHomogeneous d :=
  homogeneous_restrict _ _ (hF.map _)

/-- A genuine integral specialization of the full-frame family, obtained
by composing four internally proved generic hyperplane sections. -/
theorem exists_integral_specialization
    {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (F : MvPolynomial (Fin 9) K) (hF : F.IsHomogeneous 3)
    (hirr : Irreducible F) :
    ∃ (L : Type u) (hL : Field L),
      letI : Field L := hL
      ∃ (ρ : K →+* L), IsAlgClosed L ∧
        ∃ B : Matrix (Fin 9) (Fin 5) L,
          Function.Injective B.mulVec ∧
          Irreducible (map (eval₂Hom ρ (fun ij => B ij.1 ij.2))
            (polynomial (m := 5) F)) := by
  obtain ⟨L, hL, hdata⟩ := IntegralCubicBertiniFrame.exists_nine_to_five_integral_frame F hF hirr
  letI : Field L := hL
  obtain ⟨hA, hdata⟩ := hdata
  letI : Algebra K L := hA
  obtain ⟨hclosed, B, hB, _, hI⟩ := hdata
  refine ⟨L, hL, algebraMap K L, hclosed, B, hB, ?_⟩
  rwa [specialize]

/-- In particular the actual full-frame polynomial is not zero. This uses
the displayed integral fiber, without asserting that generic fibers are integral. -/
theorem polynomial_ne_zero
    {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (F : MvPolynomial (Fin 9) K) (hF : F.IsHomogeneous 3)
    (hirr : Irreducible F) : polynomial (m := 5) F ≠ 0 := by
  obtain ⟨L, hL, hdata⟩ := exists_integral_specialization F hF hirr
  letI : Field L := hL
  obtain ⟨ρ, _, B, _, hI⟩ := hdata
  intro he
  exact hI.ne_zero (by rw [he, map_zero])

end CubicTenVariables.CubicIntegralFrameFamily

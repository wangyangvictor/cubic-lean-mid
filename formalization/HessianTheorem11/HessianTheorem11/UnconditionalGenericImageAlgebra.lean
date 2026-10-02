import HessianTheorem11.UnconditionalGenericDominantDerivation
import HessianTheorem11.UnconditionalGenericJacobianDerivation

/-! Coordinate rings and derivations of the actual image of a polynomial map. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 160000
namespace HessianTheorem11.UnconditionalGeneric
open MvPolynomial Module ReducedTangentRank

section Coordinates
variable {m : ℕ} (J : Ideal (GeometricPolynomial m)) (F : Type*) [Field F]
  [Algebra GeometricField F] [Algebra (affineCoordinateRing J) F]
  [IsScalarTower GeometricField (affineCoordinateRing J) F]

def coordinateDerivationValues :
    Derivation GeometricField (affineCoordinateRing J) F →ₗ[F] (Fin m → F) where
  toFun D i := D (Ideal.Quotient.mk J (X i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coordinateDerivationValues_injective :
    Function.Injective (coordinateDerivationValues J F) := by
  intro D E he
  letI : Algebra (GeometricPolynomial m) F :=
    ((algebraMap (affineCoordinateRing J) F).comp (Ideal.Quotient.mk J)).toAlgebra
  letI : IsScalarTower (GeometricPolynomial m) (affineCoordinateRing J) F :=
    IsScalarTower.of_algebraMap_eq (R := GeometricPolynomial m)
      (S := affineCoordinateRing J) (A := F) (fun _ => rfl)
  letI : IsScalarTower GeometricField (GeometricPolynomial m) F :=
    IsScalarTower.to₁₂₄ GeometricField (GeometricPolynomial m) (affineCoordinateRing J) F
  have h : D.compAlgebraMap (GeometricPolynomial m) = E.compAlgebraMap (GeometricPolynomial m) := by
    apply MvPolynomial.derivation_ext
    intro i
    exact congrFun he i
  apply Derivation.ext
  intro x
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact Derivation.congr_fun h p

end Coordinates

section Image
variable {n m : ℕ} (I : Ideal (GeometricPolynomial n))
    (P : Fin m → GeometricPolynomial n)

abbrev polynomialImageIdeal : Ideal (GeometricPolynomial m) :=
  I.comap (aeval P).toRingHom

def polynomialImageCoordinateMap :
    affineCoordinateRing (polynomialImageIdeal I P) →ₐ[GeometricField] affineCoordinateRing I :=
  Ideal.quotientMapₐ I (aeval P) le_rfl

theorem polynomialImageCoordinateMap_injective :
    Function.Injective (polynomialImageCoordinateMap I P) :=
  Ideal.quotientMap_injective

@[simp] theorem polynomialImageCoordinateMap_X (i : Fin m) :
    polynomialImageCoordinateMap I P (Ideal.Quotient.mk (polynomialImageIdeal I P) (X i)) =
      Ideal.Quotient.mk I (P i) := by
  simp [polynomialImageCoordinateMap]

end Image

section Rank
variable {K : Type*} [Field K]

theorem rank_stacked {n c m : ℕ}
    (A : Matrix (Fin c) (Fin n) K) (B : Matrix (Fin m) (Fin n) K) :
    (stackMatrix A B).rank = A.rank +
      finrank K (LinearMap.range (B.mulVecLin.domRestrict (LinearMap.ker A.mulVecLin))) := by
  let S := LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin
  have hs : LinearMap.ker (stackMatrix A B).mulVecLin = S := by
    ext v
    change (stackMatrix A B).mulVec v = 0 ↔ A.mulVec v = 0 ∧ B.mulVec v = 0
    rw [stackMatrix_mulVec]
    exact ⟨fun h => ⟨congrArg (fun f => f ∘ Sum.inl) h,
      congrArg (fun f => f ∘ Sum.inr) h⟩,
      fun ⟨ha,hb⟩ => by rw [ha,hb]; ext (i|i) <;> rfl⟩
  have hk : LinearMap.ker (B.mulVecLin.domRestrict (LinearMap.ker A.mulVecLin)) =
      S.comap (LinearMap.ker A.mulVecLin).subtype := by
    ext v
    simp [S]
  have h1 := (stackMatrix A B).mulVecLin.finrank_range_add_finrank_ker
  have h2 := (B.mulVecLin.domRestrict (LinearMap.ker A.mulVecLin)).finrank_range_add_finrank_ker
  rw [hs] at h1
  rw [hk, (Submodule.comapSubtypeEquivOfLe (show S ≤ LinearMap.ker A.mulVecLin from inf_le_left)).finrank_eq] at h2
  have h3 := A.mulVecLin.finrank_range_add_finrank_ker
  change (stackMatrix A B).rank + finrank K S = _ at h1
  change A.rank + finrank K (LinearMap.ker A.mulVecLin) = _ at h3
  simp only [Module.finrank_pi_fintype,Module.finrank_self,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at h1 h3
  omega

end Rank

end HessianTheorem11.UnconditionalGeneric

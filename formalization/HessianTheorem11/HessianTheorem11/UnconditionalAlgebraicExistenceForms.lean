import HessianTheorem11.UnconditionalAlgebraicExistenceMatrix
import HessianTheorem11.PolynomialRestriction

/-! Polynomial equations in the coefficients of an actual linearly
transformed form can be specialized from arbitrary extension-field matrices
to base-field matrices. No homogeneity or finite equation-set hypothesis is
needed. -/
noncomputable section
namespace HessianTheorem11.UnconditionalAlgebraicExistence
open MvPolynomial PolynomialRestriction
variable {K E : Type*} [Field K] [IsAlgClosed K] [Field E] [Algebra K E] {n : ℕ}

def universalRestriction (F : MvPolynomial (Fin n) K) :
    MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) K) :=
  restrict (fun i j : Fin n => (X (i,j) : MvPolynomial (Fin n × Fin n) K)) (map C F)

def restrictionCoefficient (F : MvPolynomial (Fin n) K) (e : Fin n →₀ ℕ) :
    MvPolynomial (Fin n × Fin n) K := coeff e (universalRestriction F)

theorem map_universalRestriction (F : MvPolynomial (Fin n) K)
    (A : Matrix (Fin n) (Fin n) E) :
    map (aeval (matrixPoint A) : MvPolynomial (Fin n × Fin n) K →ₐ[K] E).toRingHom
        (universalRestriction F) = restrict A (map (algebraMap K E) F) := by
  rw [universalRestriction,map_restrict,MvPolynomial.map_map]
  have hm : Matrix.map (fun i j : Fin n => (X (i,j) : MvPolynomial (Fin n × Fin n) K))
      (aeval (matrixPoint A) : MvPolynomial (Fin n × Fin n) K →ₐ[K] E).toRingHom = A := by
    ext i j
    simp [matrixPoint]
  have hc : (aeval (matrixPoint A) : MvPolynomial (Fin n × Fin n) K →ₐ[K] E).toRingHom.comp C =
      algebraMap K E := by ext c; simp
  rw [hm,hc]

theorem aeval_restrictionCoefficient (F : MvPolynomial (Fin n) K)
    (A : Matrix (Fin n) (Fin n) E) (e : Fin n →₀ ℕ) :
    aeval (matrixPoint A) (restrictionCoefficient F e) =
      coeff e (restrict A (map (algebraMap K E) F)) := by
  change (aeval (matrixPoint A) : MvPolynomial (Fin n × Fin n) K →ₐ[K] E).toRingHom
    (coeff e (universalRestriction F)) = _
  rw [← coeff_map,map_universalRestriction]

def restrictionEquation (F : MvPolynomial (Fin n) K)
    (p : MvPolynomial (Fin n →₀ ℕ) K) : MvPolynomial (Fin n × Fin n) K :=
  aeval (restrictionCoefficient F) p

theorem aeval_restrictionEquation (F : MvPolynomial (Fin n) K)
    (A : Matrix (Fin n) (Fin n) E) (p : MvPolynomial (Fin n →₀ ℕ) K) :
    aeval (matrixPoint A) (restrictionEquation F p) =
      aeval (fun e => coeff e (restrict A (map (algebraMap K E) F))) p := by
  rw [restrictionEquation,MvPolynomial.comp_aeval_apply]
  have he : (fun e => aeval (matrixPoint A) (restrictionCoefficient F e)) =
      (fun e => coeff e (restrict A (map (algebraMap K E) F))) :=
    funext (aeval_restrictionCoefficient F A)
  rw [he]

theorem eval_restrictionEquation (F : MvPolynomial (Fin n) K)
    (A : Matrix (Fin n) (Fin n) K) (p : MvPolynomial (Fin n →₀ ℕ) K) :
    eval (matrixPoint A) (restrictionEquation F p) =
      eval (fun e => coeff e (restrict A F)) p := by
  simpa only [Algebra.algebraMap_self,MvPolynomial.map_id] using aeval_restrictionEquation F A p

/-- Actual SL coordinate changes satisfying arbitrary coefficient target
equations and finitely many nonzero coefficient tests descend to K. The
coefficient equations may in particular encode any desired support zeros. -/
theorem exists_specialLinear_restriction
    (F : MvPolynomial (Fin n) K)
    (Q : Set (MvPolynomial (Fin n →₀ ℕ) K)) (S : Finset (MvPolynomial (Fin n →₀ ℕ) K))
    (A : Matrix (Fin n) (Fin n) E) (hA : A.det = 1)
    (hQ : ∀ p ∈ Q, aeval (fun e => coeff e (restrict A (map (algebraMap K E) F))) p = 0)
    (hS : ∀ p ∈ S, aeval (fun e => coeff e (restrict A (map (algebraMap K E) F))) p ≠ 0) :
    ∃ B : Matrix (Fin n) (Fin n) K, B.det = 1 ∧
      (∀ p ∈ Q, eval (fun e => coeff e (restrict B F)) p = 0) ∧
      (∀ p ∈ S, eval (fun e => coeff e (restrict B F)) p ≠ 0) := by
  classical
  obtain ⟨B,hB,hQB,hSB⟩ := exists_specialLinear_matrix
    (restrictionEquation F '' Q) (S.image (restrictionEquation F)) A hA
    (by rintro _ ⟨p,hp,rfl⟩; rw [aeval_restrictionEquation]; exact hQ p hp)
    (by intro q hq; obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
        rw [aeval_restrictionEquation]; exact hS p hp)
  refine ⟨B,hB,?_,?_⟩
  · intro p hp
    rw [← eval_restrictionEquation]
    exact hQB _ ⟨p,hp,rfl⟩
  · intro p hp
    rw [← eval_restrictionEquation]
    exact hSB _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩)

theorem exists_invertible_restriction
    (F : MvPolynomial (Fin n) K)
    (Q : Set (MvPolynomial (Fin n →₀ ℕ) K)) (S : Finset (MvPolynomial (Fin n →₀ ℕ) K))
    (A : Matrix (Fin n) (Fin n) E) (hA : A.det ≠ 0)
    (hQ : ∀ p ∈ Q, aeval (fun e => coeff e (restrict A (map (algebraMap K E) F))) p = 0)
    (hS : ∀ p ∈ S, aeval (fun e => coeff e (restrict A (map (algebraMap K E) F))) p ≠ 0) :
    ∃ B : Matrix (Fin n) (Fin n) K, IsUnit B ∧
      (∀ p ∈ Q, eval (fun e => coeff e (restrict B F)) p = 0) ∧
      (∀ p ∈ S, eval (fun e => coeff e (restrict B F)) p ≠ 0) := by
  classical
  obtain ⟨B,hB,hQB,hSB⟩ := exists_invertible_matrix
    (restrictionEquation F '' Q) (S.image (restrictionEquation F)) A hA
    (by rintro _ ⟨p,hp,rfl⟩; rw [aeval_restrictionEquation]; exact hQ p hp)
    (by intro q hq; obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
        rw [aeval_restrictionEquation]; exact hS p hp)
  refine ⟨B,hB,?_,?_⟩
  · intro p hp
    rw [← eval_restrictionEquation]
    exact hQB _ ⟨p,hp,rfl⟩
  · intro p hp
    rw [← eval_restrictionEquation]
    exact hSB _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩)

end HessianTheorem11.UnconditionalAlgebraicExistence

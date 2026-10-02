import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic

/-!
# Tensor products of domains over an algebraically closed field

The finite-type factor has a rational specialization avoiding any prescribed
nonzero element, by the Jacobson property and Zariski's lemma.  A basis of
the other factor then allows simultaneous specialization of two nonzero
tensors to nonzero elements of a domain.  This is the algebraic-closure
argument needed for the remaining coefficient-field primality comparison.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct

universe u v w

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {A : Type v} [CommRing A] [IsDomain A] [Algebra K A]
variable {B : Type w} [CommRing B] [IsDomain B] [Algebra K B]

/-- A nonzero element of a finite-type domain over an algebraically closed
field survives in some rational specialization. -/
theorem exists_algHom_to_algebraicallyClosedField_ne_zero
    [Algebra.FiniteType K B] (x : B) (hx : x ≠ 0) :
    ∃ φ : B →ₐ[K] K, φ x ≠ 0 := by
  classical
  letI : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := K)
  have hnot : x ∉ (⊥ : Ideal B).jacobson := by
    rw [← Ideal.radical_eq_jacobson, Ideal.radical_bot_of_noZeroDivisors]
    simpa using hx
  obtain ⟨m, hm, hxm⟩ : ∃ m : Ideal B, m.IsMaximal ∧ x ∉ m := by
    by_contra! h
    apply hnot
    exact Ideal.mem_sInf.mpr fun m hm ↦ h m hm.2
  letI : m.IsMaximal := hm
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  letI : Module.Finite K (B ⧸ m) :=
    finite_of_finite_type_of_isJacobsonRing K (B ⧸ m)
  let φ : (B ⧸ m) →ₐ[K] K := IsAlgClosed.lift
  refine ⟨φ.comp (Ideal.Quotient.mkₐ K m), ?_⟩
  intro hzero
  apply hxm
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply φ.injective
  simpa only [map_zero] using hzero

/-- Specialization of the first tensor factor, followed by multiplication
in the second. -/
def tensorSpecialization (φ : B →ₐ[K] K) : (B ⊗[K] A) →ₐ[K] A :=
  Algebra.TensorProduct.lift ((Algebra.ofId K A).comp φ)
    (AlgHom.id K A) (fun _ _ ↦ Commute.all _ _)

theorem tensorSpecialization_tmul (φ : B →ₐ[K] K) (x : B) (y : A) :
    tensorSpecialization (A := A) φ (x ⊗ₜ[K] y) = φ x • y := by
  simp [tensorSpecialization, Algebra.smul_def]

/-- Coordinates of a specialized tensor are the specialized coordinates in
the scalar-extended basis. -/
theorem basis_repr_tensorSpecialization {ι : Type*}
    (b : Module.Basis ι K A) (φ : B →ₐ[K] K)
    (z : B ⊗[K] A) (i : ι) :
    b.repr (tensorSpecialization φ z) i =
      φ ((b.baseChange B).repr z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      rw [tensorSpecialization_tmul]
      simp [mul_comm]
  | add x y hx hy => simp [hx, hy]

/-- If one factor is finite type, two domains over an algebraically closed
field have a domain as their tensor product.  No geometric proposition is
assumed. -/
theorem tensorProduct_isDomain_of_algebraicallyClosed_of_finiteType
    [Algebra.FiniteType K B] : IsDomain (B ⊗[K] A) := by
  classical
  letI : Nontrivial (B ⊗[K] A) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain
      K B A (algebraMap K B).injective (algebraMap K A).injective
  let b := Module.Free.chooseBasis K A
  haveI : NoZeroDivisors (B ⊗[K] A) := by
    constructor
    intro x y hxy
    by_cases hx : x = 0
    · exact Or.inl hx
    by_cases hy : y = 0
    · exact Or.inr hy
    obtain ⟨i, hi⟩ : ∃ i, (b.baseChange B).repr x i ≠ 0 := by
      by_contra! h
      apply hx
      apply (b.baseChange B).repr.injective
      ext i
      simpa using h i
    obtain ⟨j, hj⟩ : ∃ j, (b.baseChange B).repr y j ≠ 0 := by
      by_contra! h
      apply hy
      apply (b.baseChange B).repr.injective
      ext j
      simpa using h j
    obtain ⟨φ, hφ⟩ := exists_algHom_to_algebraicallyClosedField_ne_zero (K := K)
      ((b.baseChange B).repr x i * (b.baseChange B).repr y j)
        (mul_ne_zero hi hj)
    rw [map_mul] at hφ
    have hximage : tensorSpecialization (A := A) φ x ≠ 0 := by
      intro hz
      apply (mul_ne_zero_iff.mp hφ).1
      rw [← basis_repr_tensorSpecialization b φ x i, hz]
      simp
    have hyimage : tensorSpecialization (A := A) φ y ≠ 0 := by
      intro hz
      apply (mul_ne_zero_iff.mp hφ).2
      rw [← basis_repr_tensorSpecialization b φ y j, hz]
      simp
    exfalso
    apply mul_ne_zero hximage hyimage
    rw [← map_mul, hxy, map_zero]
  exact {}

end

end TranslatedDepthSeven

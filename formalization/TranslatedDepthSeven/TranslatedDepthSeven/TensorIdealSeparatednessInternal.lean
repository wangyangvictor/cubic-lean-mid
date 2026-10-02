import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Filtration

/-!
# Separation of extended ideals under a field extension

A basis of the extending field gives coefficient maps on the tensor product.
Membership in an extended ideal forces each coefficient into the original
ideal.  Consequently an arbitrary separated family of ideals remains
separated after extending the coefficient field.  No finite-dimensionality
or geometric reducedness is required.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct

variable {K L A C : Type*} [Field K] [CommRing L] [Algebra K L]
  [CommRing A] [Algebra K A] [CommRing C] [Algebra K C]

def tensorFieldCoefficient {ι : Type*} (b : Module.Basis ι K L)
    (i : ι) (z : L ⊗[K] A) : A :=
  (b.baseChange A).repr ((TensorProduct.comm K L A) z) i

@[simp]
theorem tensorFieldCoefficient_tmul {ι : Type*} (b : Module.Basis ι K L)
    (i : ι) (l : L) (a : A) :
    tensorFieldCoefficient b i (l ⊗ₜ[K] a) = (b.repr l i) • a := by
  simp [tensorFieldCoefficient]

@[simp]
theorem tensorFieldCoefficient_zero {ι : Type*} (b : Module.Basis ι K L)
    (i : ι) : tensorFieldCoefficient b i (0 : L ⊗[K] A) = 0 := by
  simp [tensorFieldCoefficient]

@[simp]
theorem tensorFieldCoefficient_add {ι : Type*} (b : Module.Basis ι K L)
    (i : ι) (x y : L ⊗[K] A) :
    tensorFieldCoefficient b i (x + y) =
      tensorFieldCoefficient b i x + tensorFieldCoefficient b i y := by
  simp [tensorFieldCoefficient]

theorem tensorFieldCoefficient_map {ι : Type*} (b : Module.Basis ι K L)
    (i : ι) (g : A →ₐ[K] C) (z : L ⊗[K] A) :
    tensorFieldCoefficient b i
        (Algebra.TensorProduct.map (AlgHom.id K L) g z) =
      g (tensorFieldCoefficient b i z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul l a => simp
  | add x y hx hy => simp [hx, hy]

theorem eq_zero_of_tensorFieldCoefficient_eq_zero {ι : Type*}
    (b : Module.Basis ι K L) (z : L ⊗[K] A)
    (hz : ∀ i, tensorFieldCoefficient b i z = 0) : z = 0 := by
  apply (TensorProduct.comm K L A).injective
  apply (b.baseChange A).repr.injective
  ext i
  simpa [tensorFieldCoefficient] using hz i

theorem tensorFieldCoefficient_mem_of_mem_map {ι : Type*}
    (b : Module.Basis ι K L) (J : Ideal A) (z : L ⊗[K] A)
    (hz : z ∈ J.map
      (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A))
    (i : ι) : tensorFieldCoefficient b i z ∈ J := by
  let q := Ideal.Quotient.mkₐ K J
  have hker := Algebra.TensorProduct.lTensor_ker (A := L) q
    Ideal.Quotient.mk_surjective
  have hqker : RingHom.ker q = J := Ideal.mk_ker
  rw [hqker] at hker
  have hzero : Algebra.TensorProduct.map (AlgHom.id K L) q z = 0 := by
    change z ∈ RingHom.ker (Algebra.TensorProduct.map (AlgHom.id K L) q)
    rw [hker]
    exact hz
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q (tensorFieldCoefficient b i z) = 0
  rw [← tensorFieldCoefficient_map b i q z, hzero]
  simp

theorem iInf_map_includeRight_eq_bot_of_iInf_eq_bot
    {κ : Sort*} (J : κ → Ideal A) (hJ : (⨅ i, J i) = ⊥) :
    (⨅ i, (J i).map
      (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)) = ⊥ := by
  classical
  apply le_antisymm _ bot_le
  intro z hz
  change z = 0
  apply eq_zero_of_tensorFieldCoefficient_eq_zero (Module.Free.chooseBasis K L)
  intro b
  have hmem : tensorFieldCoefficient (Module.Free.chooseBasis K L) b z ∈
      ⨅ i, J i := by
    simp only [Submodule.mem_iInf]
    intro i
    have hzi : z ∈ (J i).map
        (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) :=
      (show (⨅ i, (J i).map
        (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)) ≤
        (J i).map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)
        from iInf_le _ i) hz
    exact tensorFieldCoefficient_mem_of_mem_map _ (J i) z hzi b
  simpa [hJ] using hmem

theorem iInf_map_powers_includeRight_eq_bot
    [IsNoetherianRing A] [IsDomain A] (J : Ideal A) (hJ : J ≠ ⊤) :
    (⨅ n : ℕ, (J.map
      (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)) ^ n) = ⊥ := by
  simp_rw [← Ideal.map_pow]
  exact iInf_map_includeRight_eq_bot_of_iInf_eq_bot (fun n : ℕ ↦ J ^ n)
    (Ideal.iInf_pow_eq_bot_of_isDomain J hJ)

end

end TranslatedDepthSeven

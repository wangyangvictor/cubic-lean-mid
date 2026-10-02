import Mathlib
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.LinearAlgebra.Dimension.Free

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1000000

universe u v w

variable {K : Type u} {L : Type v} {σ : Type w}
  [Field K] [Field L] [Algebra K L]

noncomputable local instance polynomialCoefficientAlgebra :
    Algebra (MvPolynomial σ K) (MvPolynomial σ L) :=
  MvPolynomial.algebraMvPolynomial

noncomputable def polynomialCoefficientTensorLinearEquiv :
    MvPolynomial σ L ≃ₗ[MvPolynomial σ K]
      ((MvPolynomial σ K) ⊗[K] L) := by
  let eAlg : ((MvPolynomial σ K) ⊗[K] L) ≃ₐ[K]
      MvPolynomial σ L :=
    (Algebra.TensorProduct.comm K (MvPolynomial σ K) L).trans
      ((MvPolynomial.algebraTensorAlgEquiv K L (σ := σ)).restrictScalars K)
  exact
    { eAlg.symm.toEquiv with
      map_add' := eAlg.symm.map_add
      map_smul' := by
        intro a b
        simp [eAlg, Algebra.smul_def]
        change (algebraMap (MvPolynomial σ K)
          ((MvPolynomial σ K) ⊗[K] L)) a *
            (Algebra.TensorProduct.comm K (MvPolynomial σ K) L).symm
              ((MvPolynomial.algebraTensorAlgEquiv K L
                (σ := σ)).symm b) = _
        exact (Algebra.smul_def a _).symm }

noncomputable instance polynomialCoefficient_faithfullyFlat :
    Module.FaithfullyFlat (MvPolynomial σ K) (MvPolynomial σ L) := by
  letI : Module.Free K L := Module.Free.of_divisionRing K L
  letI : Module.FaithfullyFlat K L := inferInstance
  letI : Module.FaithfullyFlat (MvPolynomial σ K)
      ((MvPolynomial σ K) ⊗[K] L) := inferInstance
  exact Module.FaithfullyFlat.of_linearEquiv
    (MvPolynomial σ K) ((MvPolynomial σ K) ⊗[K] L)
      (polynomialCoefficientTensorLinearEquiv (K := K) (L := L) (σ := σ))

theorem polynomialCoefficient_comap_map_eq
    (I : Ideal (MvPolynomial σ K)) :
    (I.map (MvPolynomial.map (algebraMap K L))).comap
        (MvPolynomial.map (algebraMap K L)) = I := by
  simpa only [MvPolynomial.algebraMap_apply] using
    (Ideal.comap_map_eq_self_of_faithfullyFlat I)

end

end TranslatedDepthSeven

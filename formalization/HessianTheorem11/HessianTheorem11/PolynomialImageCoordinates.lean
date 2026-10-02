import HessianTheorem11.LinearEmbeddingGeometry
import HessianTheorem11.KernelGradientSpan

/-! Compress an actual polynomial map to independent coordinates on the
linear span of its values. The compression and reconstruction are actual
linear maps, with polynomial identities and equal image dimensions. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Module Matrix
variable {n m d k : ℕ}

/-- Apply a linear map to a tuple of actual coordinate polynomials. -/
def linearCombinePolynomials
    (L : GeometricPoint m →ₗ[GeometricField] GeometricPoint d)
    (P : Fin m → GeometricPolynomial n) : Fin d → GeometricPolynomial n :=
  fun j => ∑ i, C (L ((Pi.basisFun GeometricField (Fin m)) i) j) * P i

@[simp] theorem polynomialMap_linearCombinePolynomials
    (L : GeometricPoint m →ₗ[GeometricField] GeometricPoint d)
    (P : Fin m → GeometricPolynomial n) (x : GeometricPoint n) :
    polynomialMap (linearCombinePolynomials L P) x = L (polynomialMap P x) := by
  ext j
  have h := congrFun (polynomialMap_linearCoordinatePolynomials L (polynomialMap P x)) j
  simpa only [polynomialMap, linearCombinePolynomials, linearCoordinatePolynomials,
    map_sum, map_mul, eval_C, eval_X] using h

theorem linearCombinePolynomials_homogeneous
    (L : GeometricPoint m →ₗ[GeometricField] GeometricPoint d)
    (P : Fin m → GeometricPolynomial n) (hP : ∀ i, (P i).IsHomogeneous k) :
    ∀ j, (linearCombinePolynomials L P j).IsHomogeneous k := by
  intro j
  apply IsHomogeneous.sum
  intro i _
  exact (hP i).C_mul _

theorem linearIndependent_of_polynomial_image_span_top
    (P : Fin d → GeometricPolynomial n)
    (hspan : Submodule.span GeometricField (polynomialMap P '' Set.univ) = ⊤) :
    LinearIndependent GeometricField P := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  let f : GeometricPoint d →ₗ[GeometricField] GeometricField :=
    (dotProductBilin GeometricField GeometricField) c
  have hf : Submodule.span GeometricField (polynomialMap P '' Set.univ) ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, _, rfl⟩
    have he := congrArg (eval x) hc
    change dotProduct c (polynomialMap P x) = 0
    simpa only [map_sum, MvPolynomial.smul_eq_C_mul, map_mul, eval_C,
      map_zero, dotProduct, polynomialMap] using he
  rw [hspan] at hf
  have hh := hf (Submodule.mem_top : Pi.single j 1 ∈ (⊤ : Submodule GeometricField (GeometricPoint d)))
  change dotProduct c (Pi.single j 1) = 0 at hh
  simpa using hh

structure PolynomialImageCoordinates (P : Fin m → GeometricPolynomial n) (d : ℕ) where
  tuple : Fin d → GeometricPolynomial n
  embedding : GeometricPoint d →ₗ[GeometricField] GeometricPoint m
  projection : GeometricPoint m →ₗ[GeometricField] GeometricPoint d
  leftInverse : projection.comp embedding = LinearMap.id
  tuple_eq : tuple = linearCombinePolynomials projection P
  reconstruct : P = linearCombinePolynomials embedding tuple
  independent : LinearIndependent GeometricField tuple

namespace PolynomialImageCoordinates

theorem embedding_injective {P : Fin m → GeometricPolynomial n}
    (D : PolynomialImageCoordinates P d) : Function.Injective D.embedding := by
  intro u v h
  have hh := congrArg D.projection h
  simpa only [← LinearMap.comp_apply, D.leftInverse, LinearMap.id_apply] using hh

theorem reconstruct_value {P : Fin m → GeometricPolynomial n}
    (D : PolynomialImageCoordinates P d) (x : GeometricPoint n) :
    D.embedding (polynomialMap D.tuple x) = polynomialMap P x := by
  conv_rhs => rw [D.reconstruct]
  rw [polynomialMap_linearCombinePolynomials]

theorem tuple_value {P : Fin m → GeometricPolynomial n}
    (D : PolynomialImageCoordinates P d) (x : GeometricPoint n) :
    polynomialMap D.tuple x = D.projection (polynomialMap P x) := by
  rw [D.tuple_eq, polynomialMap_linearCombinePolynomials]

theorem homogeneous {P : Fin m → GeometricPolynomial n}
    (D : PolynomialImageCoordinates P d) (hP : ∀ i, (P i).IsHomogeneous k) :
    ∀ j, (D.tuple j).IsHomogeneous k := by
  rw [D.tuple_eq]
  exact linearCombinePolynomials_homogeneous D.projection P hP

theorem image_eq {P : Fin m → GeometricPolynomial n}
    (D : PolynomialImageCoordinates P d) (Z : Set (GeometricPoint n)) :
    polynomialMap P '' Z = D.embedding '' (polynomialMap D.tuple '' Z) := by
  rw [Set.image_image]
  congr 1
  funext x
  exact (D.reconstruct_value x).symm

theorem image_dimension {P : Fin m → GeometricPolynomial n}
    (D : PolynomialImageCoordinates P d) (Z : Set (GeometricPoint n)) :
    affineDimension (polynomialMap D.tuple '' Z) = affineDimension (polynomialMap P '' Z) := by
  rw [D.image_eq, affineDimension_linearMap_image D.embedding D.embedding_injective]

end PolynomialImageCoordinates

theorem exists_polynomialImageCoordinates
    (P : Fin m → GeometricPolynomial n)
    (hdim : finrank GeometricField (Submodule.span GeometricField
      (polynomialMap P '' Set.univ)) = d) : Nonempty (PolynomialImageCoordinates P d) := by
  classical
  let S := Submodule.span GeometricField (polynomialMap P '' Set.univ)
  let e : GeometricPoint d ≃ₗ[GeometricField] S := LinearEquiv.ofFinrankEq _ _ (by
    simpa using hdim.symm)
  let L : GeometricPoint d →ₗ[GeometricField] GeometricPoint m := S.subtype.comp e.toLinearMap
  have hL : Function.Injective L := S.subtype_injective.comp e.injective
  obtain ⟨R, hR⟩ := L.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hL)
  let Q := linearCombinePolynomials R P
  have hLP (x : GeometricPoint n) : L (polynomialMap Q x) = polynomialMap P x := by
    have hv : polynomialMap P x ∈ S := Submodule.subset_span ⟨x, Set.mem_univ _, rfl⟩
    let v : S := ⟨polynomialMap P x, hv⟩
    have hLv : L (e.symm v) = polynomialMap P x := by
      change ((e (e.symm v) : S) : GeometricPoint m) = _
      rw [e.apply_symm_apply]
    rw [show Q = _ from rfl, polynomialMap_linearCombinePolynomials, ← hLv]
    have heR : R (L (e.symm v)) = e.symm v := LinearMap.congr_fun hR _
    rw [heR]
  have hrec : P = linearCombinePolynomials L Q := by
    funext j
    apply MvPolynomial.funext
    intro x
    exact (congrFun ((polynomialMap_linearCombinePolynomials L Q x).trans (hLP x)) j).symm
  have hRS : S.map R = ⊤ := by
    apply top_unique
    intro v _
    refine ⟨L v, ?_, LinearMap.congr_fun hR v⟩
    exact (e v).property
  have hspan : Submodule.span GeometricField (polynomialMap Q '' Set.univ) = ⊤ := by
    have him : polynomialMap Q '' Set.univ = R '' (polynomialMap P '' Set.univ) := by
      rw [Set.image_image]
      congr 1
      funext x
      exact polynomialMap_linearCombinePolynomials R P x
    rw [him, Submodule.span_image]
    exact hRS
  exact ⟨⟨Q, L, R, hR, rfl, hrec, linearIndependent_of_polynomial_image_span_top Q hspan⟩⟩

end HessianTheorem11

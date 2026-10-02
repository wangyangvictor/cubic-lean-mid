import CubicTenVariables.BinarySliceExceptional
import CubicTenVariables.CubicGenericIntegralityUniform
import CubicTenVariables.SmoothInfinityGeometricIntegralityProved

/-! The actual binary-slice exceptional polynomial, with both geometric
integrality inputs discharged. The intermediate endpoints retain only the
proved cubic interface for downstream parameter replacement. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.BinarySliceExceptionalProved
open MvPolynomial HessianTheorem11 BinarySliceCounting Literature BinarySliceGeometry
open GeometricGenericParameterEmbedding

/-- The parameter-family equation at the literal geometric generic
parameter is exactly the algebraic-closure extension of the generic slice. -/
theorem map_family_coefficientHom {n : ℕ} (e : Fin 2 ↪ Fin n)
    (F : MvPolynomial (Fin n) ℤ) :
    map (coefficientHom (Complement e)) (family e F) =
      map (algebraMap (GeometricParameterField (Complement e))
        (AlgebraicClosure (GeometricParameterField (Complement e)))) (genericSlice e F) := by
  rw [coefficientHom, specialize_family, genericSlice_eq_slice, map_slice,
    MvPolynomial.map_map]
  have hc : (algebraMap (GeometricParameterField (Complement e))
      (AlgebraicClosure (GeometricParameterField (Complement e)))).comp
      (Int.castRingHom (GeometricParameterField (Complement e))) =
      Int.castRingHom (AlgebraicClosure (GeometricParameterField (Complement e))) :=
    RingHom.ext_int _ _
  simp only [hc]
  rfl

/-- The exact algebraically closed field endpoint using the internally
proved cubic open interface. No smooth-infinity input is supplied. -/
theorem exists_exceptional_polynomial_of_uniform
    (spread : CubicGenericIntegralityUniform.Uniform) {n : ℕ} (hn : 4 ≤ n)
    (e : Fin 2 ↪ Fin n) (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ g : MvPolynomial (Complement e) ℤ, g ≠ 0 ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (w : Complement e → K),
        eval₂ (Int.castRingHom K) w g ≠ 0 →
        IsDomain (MvPolynomial (Fin 2) K ⧸
          Ideal.span {slice e (map (Int.castRingHom K) F) w}) := by
  have hdegree : (map (coefficientHom (Complement e)) (family e F)).totalDegree = 3 := by
    rw [map_family_coefficientHom,
      PolynomialDegreePrincipalOpen.totalDegree_map_of_injective _
        (algebraMap (GeometricParameterField (Complement e))
          (AlgebraicClosure (GeometricParameterField (Complement e)))).injective]
    exact genericSlice_totalDegree e F hF hA
  have hdomain : IsDomain (MvPolynomial (Fin 2)
      (AlgebraicClosure (GeometricParameterField (Complement e))) ⧸
      Ideal.span {map (coefficientHom (Complement e)) (family e F)}) := by
    rw [map_family_coefficientHom]
    exact genericSlice_geometricallyIntegral SmoothInfinityGeometricIntegralityProved.proved
      hn e F hF hA
  obtain ⟨g, hg, hgood⟩ := spread (Complement e) 2 (family e F) hdegree hdomain
  refine ⟨g, hg, ?_⟩
  intro K _ _ w hw
  have hh := hgood K w hw
  rw [BinarySliceGeometry.specialize_family] at hh
  exact hh

/-- The corresponding algebraic-closure quotient endpoint over every
field, using the same integral exceptional polynomial. -/
theorem exists_exceptional_polynomial_for_fields_of_uniform
    (spread : CubicGenericIntegralityUniform.Uniform) {n : ℕ} (hn : 4 ≤ n)
    (e : Fin 2 ↪ Fin n) (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ g : MvPolynomial (Complement e) ℤ, g ≠ 0 ∧
      ∀ (K : Type) [Field K] (w : Complement e → K),
        eval₂ (Int.castRingHom K) w g ≠ 0 →
        IsDomain (MvPolynomial (Fin 2) (AlgebraicClosure K) ⧸
          Ideal.span {map (algebraMap K (AlgebraicClosure K))
            (slice e (map (Int.castRingHom K) F) w)}) := by
  obtain ⟨g, hg, hgood⟩ := exists_exceptional_polynomial_of_uniform spread hn e F hF hA
  refine ⟨g, hg, ?_⟩
  intro K _ w hw
  let a := algebraMap K (AlgebraicClosure K)
  have hc : a.comp (Int.castRingHom K) = Int.castRingHom (AlgebraicClosure K) :=
    RingHom.ext_int _ _
  have he : eval₂ (Int.castRingHom (AlgebraicClosure K)) (fun i => a (w i)) g =
      a (eval₂ (Int.castRingHom K) w g) := by
    simpa only [hc] using (map_eval₂Hom (Int.castRingHom K) w a g).symm
  have hh := hgood (AlgebraicClosure K) (fun i => a (w i))
    (by rw [he]; exact (map_ne_zero a).mpr hw)
  rw [map_slice, MvPolynomial.map_map, hc]
  exact hh

/-- A nonzero integer exceptional polynomial for the actual binary
slices, uniform over all algebraically closed fields, with no literature premise. -/
theorem exists_exceptional_polynomial {n : ℕ} (hn : 4 ≤ n)
    (e : Fin 2 ↪ Fin n) (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ g : MvPolynomial (Complement e) ℤ, g ≠ 0 ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (w : Complement e → K),
        eval₂ (Int.castRingHom K) w g ≠ 0 →
        IsDomain (MvPolynomial (Fin 2) K ⧸
          Ideal.span {slice e (map (Int.castRingHom K) F) w}) :=
  exists_exceptional_polynomial_of_uniform CubicGenericIntegralityUniform.proved hn e F hF hA

/-- The exact geometric-integrality format needed by the finite-field
curve estimate, with no smoothness or spreading proposition supplied as input. -/
theorem exists_exceptional_polynomial_for_fields {n : ℕ} (hn : 4 ≤ n)
    (e : Fin 2 ↪ Fin n) (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ g : MvPolynomial (Complement e) ℤ, g ≠ 0 ∧
      ∀ (K : Type) [Field K] (w : Complement e → K),
        eval₂ (Int.castRingHom K) w g ≠ 0 →
        IsDomain (MvPolynomial (Fin 2) (AlgebraicClosure K) ⧸
          Ideal.span {map (algebraMap K (AlgebraicClosure K))
            (slice e (map (Int.castRingHom K) F) w)}) :=
  exists_exceptional_polynomial_for_fields_of_uniform
    CubicGenericIntegralityUniform.proved hn e F hF hA

end CubicTenVariables.BinarySliceExceptionalProved

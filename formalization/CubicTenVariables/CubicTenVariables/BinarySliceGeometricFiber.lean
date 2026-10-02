import CubicTenVariables.BinarySliceGeometry
import CubicTenVariables.Literature.GenericFiberGeometricIntegrality

/-! Exact coefficient-field and fiber-ideal identifications for the binary
family. The open-locus theorem here retains its explicit, generic geometric
integrality hypothesis; the anisotropic-cubic application discharges it. -/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace CubicTenVariables.BinarySliceGeometry
open MvPolynomial HessianTheorem11 BinarySliceCounting Literature

/-- The actual generic binary equation over Qbar(parameters). -/
def genericSlice {n : ℕ} (e : Fin 2 ↪ Fin n) (F : MvPolynomial (Fin n) ℤ) :
    MvPolynomial (Fin 2) (GeometricParameterField (Complement e)) :=
  map (algebraMap (MvPolynomial (Complement e) GeometricField)
    (GeometricParameterField (Complement e)))
    (family e (map (Int.castRingHom GeometricField) F))

/-- Coefficient change commutes with the actual slice substitution. -/
theorem map_slice {n : ℕ} {R K : Type*} [CommRing R] [CommRing K]
    (e : Fin 2 ↪ Fin n) (f : R →+* K) (F : MvPolynomial (Fin n) R)
    (w : Complement e → R) :
    map f (slice e F w) = slice e (map f F) (fun i => f (w i)) := by
  unfold slice
  change map f (eval₂ C _ F) = eval₂ C _ (map f F)
  rw [map_eval₂]
  congr 1
  funext i
  cases h : (indexEquiv e).symm i <;> simp [combine, h]

/-- The quotient used by the generic open theorem is the principal quotient
of the literal specialized binary equation. -/
theorem family_ideal {n : ℕ} {K : Type*} [CommRing K]
    (e : Fin 2 ↪ Fin n) (F : MvPolynomial (Fin n) ℤ) (w : Complement e → K) :
    integralityFiberIdeal (fun _ : Unit => family e F) K w =
      Ideal.span {slice e (map (Int.castRingHom K) F) w} := by
  simp only [integralityFiberIdeal, specialize_family, Set.range_const]

/-- Generic specialization of the parameter polynomials is their canonical
embedding into their fraction field. -/
theorem genericSlice_eq_slice {n : ℕ} (e : Fin 2 ↪ Fin n)
    (F : MvPolynomial (Fin n) ℤ) :
    genericSlice e F =
      slice e (map (Int.castRingHom (GeometricParameterField (Complement e))) F)
        (fun i => algebraMap (MvPolynomial (Complement e) GeometricField)
          (GeometricParameterField (Complement e)) (X i)) := by
  let K := GeometricParameterField (Complement e)
  let t : Complement e → K := fun i => algebraMap (MvPolynomial (Complement e) GeometricField) K (X i)
  have he : eval₂Hom (algebraMap GeometricField K) t =
      algebraMap (MvPolynomial (Complement e) GeometricField) K := by
    ext a <;> simp [t, IsScalarTower.algebraMap_eq GeometricField
      (MvPolynomial (Complement e) GeometricField) K]
  have h := specialize_family e (algebraMap GeometricField K)
    (map (Int.castRingHom GeometricField) F) t
  rw [he, MvPolynomial.map_map] at h
  have hc : (algebraMap GeometricField K).comp (Int.castRingHom GeometricField) =
      Int.castRingHom K := RingHom.ext_int _ _
  simpa only [genericSlice, hc] using h

/-- The displayed generic fiber ideal is exactly the base change of the
actual generic binary equation to an algebraic closure. -/
theorem geometric_generic_fiber_ideal {n : ℕ} (e : Fin 2 ↪ Fin n)
    (F : MvPolynomial (Fin n) ℤ) :
    integralityFiberIdeal (fun _ : Unit => family e F)
      (AlgebraicClosure (GeometricParameterField (Complement e)))
      (geometricGenericParameter (Complement e)) =
    Ideal.span {map (algebraMap (GeometricParameterField (Complement e))
      (AlgebraicClosure (GeometricParameterField (Complement e)))) (genericSlice e F)} := by
  rw [family_ideal, genericSlice_eq_slice, map_slice, MvPolynomial.map_map]
  have hc : (algebraMap (GeometricParameterField (Complement e))
      (AlgebraicClosure (GeometricParameterField (Complement e)))).comp
      (Int.castRingHom (GeometricParameterField (Complement e))) =
      Int.castRingHom (AlgebraicClosure (GeometricParameterField (Complement e))) :=
    RingHom.ext_int _ _
  simp only [hc]
  rfl

/-- One genuine nonzero integer parameter polynomial controls every good
fiber, provided the actual generic binary curve is geometrically integral.
No cubic-specific exceptional-polynomial assertion is supplied as input. -/
theorem exists_exceptional_polynomial_of_generic
    (spread : GenericFiberGeometricIntegralityOpen) {n : ℕ}
    (e : Fin 2 ↪ Fin n) (F : MvPolynomial (Fin n) ℤ)
    (hgeneric : IsDomain (MvPolynomial (Fin 2)
      (AlgebraicClosure (GeometricParameterField (Complement e))) ⧸
      Ideal.span {map (algebraMap (GeometricParameterField (Complement e))
        (AlgebraicClosure (GeometricParameterField (Complement e)))) (genericSlice e F)})) :
    ∃ g : MvPolynomial (Complement e) ℤ, g ≠ 0 ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (w : Complement e → K),
        eval₂ (Int.castRingHom K) w g ≠ 0 →
        IsDomain (MvPolynomial (Fin 2) K ⧸
          Ideal.span {slice e (map (Int.castRingHom K) F) w}) := by
  obtain ⟨g, hg, hgood⟩ := spread (Complement e) (Fin 2) Unit
    (fun _ => family e F) (by rw [geometric_generic_fiber_ideal]; exact hgeneric)
  refine ⟨g, hg, ?_⟩
  intro K _ _ w hw
  have hh := hgood K w hw
  rw [family_ideal] at hh
  exact hh

/-- The same nonzero integer exceptional polynomial works over every field,
with geometric integrality expressed by its actual algebraic-closure quotient. -/
theorem exists_exceptional_polynomial_for_fields_of_generic
    (spread : GenericFiberGeometricIntegralityOpen) {n : ℕ}
    (e : Fin 2 ↪ Fin n) (F : MvPolynomial (Fin n) ℤ)
    (hgeneric : IsDomain (MvPolynomial (Fin 2)
      (AlgebraicClosure (GeometricParameterField (Complement e))) ⧸
      Ideal.span {map (algebraMap (GeometricParameterField (Complement e))
        (AlgebraicClosure (GeometricParameterField (Complement e)))) (genericSlice e F)})) :
    ∃ g : MvPolynomial (Complement e) ℤ, g ≠ 0 ∧
      ∀ (K : Type) [Field K] (w : Complement e → K),
        eval₂ (Int.castRingHom K) w g ≠ 0 →
        IsDomain (MvPolynomial (Fin 2) (AlgebraicClosure K) ⧸
          Ideal.span {map (algebraMap K (AlgebraicClosure K))
            (slice e (map (Int.castRingHom K) F) w)}) := by
  obtain ⟨g, hg, hgood⟩ := exists_exceptional_polynomial_of_generic spread e F hgeneric
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

end CubicTenVariables.BinarySliceGeometry

import CubicTenVariables.BinarySliceGenericGeometry
import CubicTenVariables.BinaryInfinitySmoothPoint

/-! The exceptional polynomial for the actual binary slices of an
anisotropic integral cubic. The generic curve's integrality, degree and
smooth infinity point are proved. Only the two explicitly cited general
geometric-integrality propositions are passed as literature inputs. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.BinarySliceGeometry
open MvPolynomial HessianTheorem11 BinarySliceCounting Literature

/-- The actual binary leading form has a simple nonzero zero over Qbar. -/
theorem geometric_slice_zero_simple_point {n : ℕ} (e : Fin 2 ↪ Fin n)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ x : Fin 2 → GeometricField, x ≠ 0 ∧
      eval x (slice e (map (Int.castRingHom GeometricField) F) 0) = 0 ∧
      ∃ i, eval x (pderiv i (slice e (map (Int.castRingHom GeometricField) F) 0)) ≠ 0 := by
  have hp := BinaryInfinitySmoothPoint.exists_simple_binary_zero (K := GeometricField)
    (slice e (map (Int.castRingHom ℚ) F) 0)
    (homogeneous_slice_zero e _ (hF.map _))
    (anisotropic_slice_zero e _ hA)
  have hm := map_slice e (algebraMap ℚ GeometricField) (map (Int.castRingHom ℚ) F) 0
  have hc : (algebraMap ℚ GeometricField).comp (Int.castRingHom ℚ) =
      Int.castRingHom GeometricField := RingHom.ext_int _ _
  rw [MvPolynomial.map_map, hc] at hm
  simp only [Pi.zero_apply, map_zero] at hm
  rw [hm] at hp
  exact hp

/-- The top homogeneous part of the actual generic equation has an actual
simple nonzero rational point over Qbar(parameters). -/
theorem genericSlice_infinity_simple_point {n : ℕ} (e : Fin 2 ↪ Fin n)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ x : Fin 2 → GeometricParameterField (Complement e), x ≠ 0 ∧
      eval x (homogeneousComponent 3 (genericSlice e F)) = 0 ∧
      ∃ i, eval x (pderiv i (homogeneousComponent 3 (genericSlice e F))) ≠ 0 := by
  rw [genericSlice_top e F hF]
  exact exists_simple_zero_map (algebraMap GeometricField
    (GeometricParameterField (Complement e))) _ (geometric_slice_zero_simple_point e F hF hA)

/-- The actual generic binary curve is geometrically integral. The only
literature input is the general smooth-rational-point-at-infinity criterion;
its actual equation, domain, degree and smooth-point hypotheses are proved. -/
theorem genericSlice_geometricallyIntegral
    (smooth : SmoothInfinityGeometricIntegrality) {n : ℕ} (hn : 4 ≤ n)
    (e : Fin 2 ↪ Fin n) (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    IsDomain (MvPolynomial (Fin 2)
      (AlgebraicClosure (GeometricParameterField (Complement e))) ⧸
      Ideal.span {map (algebraMap (GeometricParameterField (Complement e))
        (AlgebraicClosure (GeometricParameterField (Complement e)))) (genericSlice e F)}) :=
  smooth (GeometricParameterField (Complement e)) 2 3 (genericSlice e F) (by norm_num)
    (genericSlice_totalDegree e F hF hA) (genericSlice_isDomain hn e F hF hA)
    (genericSlice_infinity_simple_point e F hF hA)

/-- A nonzero integer exceptional polynomial for the actual selected
binary slices, uniform over every algebraically closed residue field.
No generic-fiber or exceptional-polynomial hypothesis remains. -/
theorem exists_exceptional_polynomial
    (smooth : SmoothInfinityGeometricIntegrality)
    (spread : GenericFiberGeometricIntegralityOpen) {n : ℕ} (hn : 4 ≤ n)
    (e : Fin 2 ↪ Fin n) (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ g : MvPolynomial (Complement e) ℤ, g ≠ 0 ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (w : Complement e → K),
        eval₂ (Int.castRingHom K) w g ≠ 0 →
        IsDomain (MvPolynomial (Fin 2) K ⧸
          Ideal.span {slice e (map (Int.castRingHom K) F) w}) :=
  exists_exceptional_polynomial_of_generic spread e F
    (genericSlice_geometricallyIntegral smooth hn e F hF hA)

/-- The same exceptional polynomial in the exact algebraic-closure quotient
format used by the finite-field curve estimate, including all field extensions. -/
theorem exists_exceptional_polynomial_for_fields
    (smooth : SmoothInfinityGeometricIntegrality)
    (spread : GenericFiberGeometricIntegralityOpen) {n : ℕ} (hn : 4 ≤ n)
    (e : Fin 2 ↪ Fin n) (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ g : MvPolynomial (Complement e) ℤ, g ≠ 0 ∧
      ∀ (K : Type) [Field K] (w : Complement e → K),
        eval₂ (Int.castRingHom K) w g ≠ 0 →
        IsDomain (MvPolynomial (Fin 2) (AlgebraicClosure K) ⧸
          Ideal.span {map (algebraMap K (AlgebraicClosure K))
            (slice e (map (Int.castRingHom K) F) w)}) :=
  exists_exceptional_polynomial_for_fields_of_generic spread e F
    (genericSlice_geometricallyIntegral smooth hn e F hF hA)

end CubicTenVariables.BinarySliceGeometry

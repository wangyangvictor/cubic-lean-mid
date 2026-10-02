import CubicTenVariables.BinarySliceGeometricFiber
import CubicTenVariables.GenericBinarySliceIntegral
import CubicTenVariables.BinarySliceLeadingCoefficient
import HessianTheorem11.UnconditionalCubicIrreducibility

/-! The actual generic binary curve is integral by proved anisotropic-cubic
absolute irreducibility and coefficient localization. Geometric integrality
will additionally use its actual smooth point at infinity. -/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace CubicTenVariables.BinarySliceGeometry
open MvPolynomial HessianTheorem11 BinarySliceCounting Literature

/-- Coefficient maps do not increase total degree. -/
theorem totalDegree_map_le {σ R K : Type*} [CommRing R] [CommRing K]
    (f : R →+* K) (F : MvPolynomial σ R) : (map f F).totalDegree ≤ F.totalDegree := by
  exact Finset.sup_mono (support_map_subset _ _)

/-- The actual rational binary leading form remains nonzero over Qbar. -/
theorem geometric_slice_zero_ne_zero {n : ℕ} (e : Fin 2 ↪ Fin n)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    slice e (map (Int.castRingHom GeometricField) F) 0 ≠ 0 := by
  have hbin := (irreducible_slice_zero e (map (Int.castRingHom ℚ) F) (hF.map _) hA).ne_zero
  have hh := map_slice e (algebraMap ℚ GeometricField) (map (Int.castRingHom ℚ) F) 0
  have hc : (algebraMap ℚ GeometricField).comp (Int.castRingHom ℚ) =
      Int.castRingHom GeometricField := RingHom.ext_int _ _
  rw [MvPolynomial.map_map, hc] at hh
  simp only [Pi.zero_apply, map_zero] at hh
  change map (algebraMap ℚ GeometricField) (slice e (map (Int.castRingHom ℚ) F) 0) =
    slice e (map (Int.castRingHom GeometricField) F) 0 at hh
  rw [← hh]
  exact fun hz => hbin ((map_injective _ (algebraMap ℚ GeometricField).injective)
    (by simpa only [map_zero] using hz))

/-- The generic family has positive degree in its two retained variables;
coefficient localization therefore cannot turn its equation into a unit. -/
theorem geometric_family_degree_pos {n : ℕ} (e : Fin 2 ↪ Fin n)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    0 < (family e (map (Int.castRingHom GeometricField) F)).totalDegree := by
  have hs := specialize_family e (RingHom.id GeometricField)
    (map (Int.castRingHom GeometricField) F) (0 : Complement e → GeometricField)
  simp only [MvPolynomial.map_id] at hs
  have hd := totalDegree_map_le (eval₂Hom (RingHom.id GeometricField) 0)
    (family e (map (Int.castRingHom GeometricField) F))
  rw [hs, (homogeneous_slice_zero e _ (hF.map _)).totalDegree
    (geometric_slice_zero_ne_zero e F hF hA)] at hd
  omega

/-- Absolute irreducibility of the full original cubic is a proved theorem,
not a new literature premise. -/
theorem geometric_ambient_irreducible {n : ℕ} (hn : 4 ≤ n)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    Irreducible (map (Int.castRingHom GeometricField) F) := by
  let A : AnisotropicCubic n := ⟨map (Int.castRingHom ℚ) F, hF.map _, hA⟩
  have hi := UnconditionalIrreducibility.anisotropic_geometric_irreducible A hn
  have hc : (algebraMap ℚ GeometricField).comp (Int.castRingHom ℚ) =
      Int.castRingHom GeometricField := RingHom.ext_int _ _
  simpa only [geometricPolynomial, A, MvPolynomial.map_map, hc] using hi

/-- The literal generic curve over Qbar(parameters) is integral. -/
theorem genericSlice_isDomain {n : ℕ} (hn : 4 ≤ n) (e : Fin 2 ↪ Fin n)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    IsDomain (MvPolynomial (Fin 2) (GeometricParameterField (Complement e)) ⧸
      Ideal.span {genericSlice e F}) :=
  GenericBinarySliceIntegral.isDomain_generic_family e
    (map (Int.castRingHom GeometricField) F) (geometric_ambient_irreducible hn F hF hA)
    (geometric_family_degree_pos e F hF hA)

/-- The complete cubic homogeneous part is unchanged by generic
specialization: it is the base change of the actual binary leading form. -/
theorem genericSlice_top {n : ℕ} (e : Fin 2 ↪ Fin n)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3) :
    homogeneousComponent 3 (genericSlice e F) =
      map (algebraMap GeometricField (GeometricParameterField (Complement e)))
        (slice e (map (Int.castRingHom GeometricField) F) 0) := by
  rw [genericSlice_eq_slice]
  have ht := BinarySliceLeadingCoefficient.homogeneousComponent_slice e
    (map (Int.castRingHom (GeometricParameterField (Complement e))) F)
    (fun i => algebraMap (MvPolynomial (Complement e) GeometricField)
      (GeometricParameterField (Complement e)) (X i)) (hF.map _)
  have ht' : homogeneousComponent 3 (slice e
      (map (Int.castRingHom (GeometricParameterField (Complement e))) F)
      (fun i => algebraMap (MvPolynomial (Complement e) GeometricField)
        (GeometricParameterField (Complement e)) (X i))) =
      slice e (map (Int.castRingHom (GeometricParameterField (Complement e))) F) 0 := by
    simpa only [slice, Pi.zero_apply, C_0] using ht
  rw [ht', map_slice, MvPolynomial.map_map]
  have hc : (algebraMap GeometricField (GeometricParameterField (Complement e))).comp
      (Int.castRingHom GeometricField) =
      Int.castRingHom (GeometricParameterField (Complement e)) := RingHom.ext_int _ _
  simp only [hc, Pi.zero_apply, map_zero]
  rfl

/-- In particular the actual generic binary equation has degree exactly three. -/
theorem genericSlice_totalDegree {n : ℕ} (e : Fin 2 ↪ Fin n)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    (genericSlice e F).totalDegree = 3 := by
  have hu : (genericSlice e F).totalDegree ≤ 3 := by
    rw [genericSlice_eq_slice]
    exact (totalDegree_slice_le _ _ _).trans (hF.map _).totalDegree_le
  have hn : homogeneousComponent 3 (genericSlice e F) ≠ 0 := by
    rw [genericSlice_top e F hF]
    intro hz
    apply geometric_slice_zero_ne_zero e F hF hA
    exact (map_injective _ (algebraMap GeometricField
      (GeometricParameterField (Complement e))).injective) (by simpa only [map_zero] using hz)
  apply le_antisymm hu
  by_contra hl
  exact hn (homogeneousComponent_eq_zero _ _ (by omega))

/-- An actual simple nonzero zero remains simple under any field embedding. -/
theorem exists_simple_zero_map {K L : Type*} [Field K] [Field L] {n : ℕ}
    (f : K →+* L) (H : MvPolynomial (Fin n) K)
    (h : ∃ x : Fin n → K, x ≠ 0 ∧ eval x H = 0 ∧
      ∃ i, eval x (pderiv i H) ≠ 0) :
    ∃ y : Fin n → L, y ≠ 0 ∧ eval y (map f H) = 0 ∧
      ∃ i, eval y (pderiv i (map f H)) ≠ 0 := by
  obtain ⟨x, hx, hH, i, hi⟩ := h
  have he (A : MvPolynomial (Fin n) K) :
      eval (fun j => f (x j)) (map f A) = f (eval x A) := by
    rw [eval_map]
    simpa only [RingHom.comp_id] using (map_eval₂Hom (RingHom.id K) x f A).symm
  refine ⟨fun j => f (x j), ?_, ?_, i, ?_⟩
  · intro hz
    apply hx
    funext j
    apply f.injective
    simpa only [Pi.zero_apply, map_zero] using congrFun hz j
  · rw [he, hH, map_zero]
  · rw [pderiv_map, he]
    exact (map_ne_zero f).mpr hi

end CubicTenVariables.BinarySliceGeometry

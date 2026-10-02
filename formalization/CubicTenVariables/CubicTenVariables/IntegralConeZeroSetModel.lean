import CubicTenVariables.GaloisClosedConeIntegralModel
import CubicTenVariables.IntegerZeroSetSpreading

/-! A finite integral equation family defining a geometric cone has a reduced
homogeneous integral model with the same field-valued zeros outside finitely
many characteristics. Closedness and Galois stability are proved from the
literal raw equations; only their conical zero-set property is required. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.IntegralConeZeroSetModel
open MvPolynomial HessianTheorem11 RationalComponentDescent

variable {n r : ℕ}

/-- The actual geometric common zeros of a finite integer equation family. -/
def zeroSet (H : Fin r → MvPolynomial (Fin n) ℤ) : Set (GeometricPoint n) :=
  {v | ∀ i, eval₂Hom (Int.castRingHom GeometricField) v (H i) = 0}

theorem zeroSet_eq_zeroLocus (H : Fin r → MvPolynomial (Fin n) ℤ) :
    zeroSet H = zeroLocus GeometricField
      (Ideal.span (Set.range (fun i => map (Int.castRingHom GeometricField) (H i)))) := by
  ext v
  rw [zeroLocus_span]
  change (∀ i, eval₂Hom (Int.castRingHom GeometricField) v (H i) = 0) ↔
    ∀ P ∈ Set.range (fun i => map (Int.castRingHom GeometricField) (H i)), eval v P = 0
  simp only [Set.forall_mem_range, eval_map]
  rfl

theorem zeroSet_closed (H : Fin r → MvPolynomial (Fin n) ℤ) :
    AlgebraicallyClosedSet (zeroSet H) := by
  rw [zeroSet_eq_zeroLocus]
  exact algebraicallyClosedSet_zeroLocus _

/-- Integer coefficients are fixed by every rational Galois automorphism. -/
theorem zeroSet_galois_stable (H : Fin r → MvPolynomial (Fin n) ℤ)
    (σ : GeometricField ≃ₐ[ℚ] GeometricField) (v : GeometricPoint n)
    (hv : v ∈ zeroSet H) : galoisPoint σ v ∈ zeroSet H := by
  intro i
  have hc : σ.toRingHom.comp (Int.castRingHom GeometricField) =
      Int.castRingHom GeometricField := RingHom.ext_int _ _
  have he := map_eval₂Hom (Int.castRingHom GeometricField) v σ.toRingHom (H i)
  rw [hv i, map_zero, hc] at he
  exact he.symm

/-- The homogeneous reduced model and exceptional integer precede every
characteristic, field and point. The rational locus is never substituted
for the actual geometric common zero set. -/
theorem exists_model (H : Fin r → MvPolynomial (Fin n) ℤ)
    (hcone : IsAffineCone (zeroSet H)) :
    ∃ (u : ℕ) (G : Fin u → MvPolynomial (Fin n) ℤ)
      (d : Fin u → ℕ) (D : ℕ),
      (∀ i, (G i).IsHomogeneous (d i)) ∧ 1 ≤ D ∧
      Ideal.span (Set.range (fun i => map (Int.castRingHom GeometricField) (G i))) =
        vanishingIdeal GeometricField (zeroSet H) ∧
      (∀ v : GeometricPoint n,
        (∀ i, eval₂Hom (Int.castRingHom GeometricField) v (H i) = 0) ↔
          ∀ i, eval₂Hom (Int.castRingHom GeometricField) v (G i) = 0) ∧
      ∀ p : ℕ, ¬ p ∣ D → ∀ (K : Type*) [Field K] [CharP K p] (v : Fin n → K),
        (∀ i, eval₂Hom (Int.castRingHom K) v (H i) = 0) ↔
          ∀ i, eval₂Hom (Int.castRingHom K) v (G i) = 0 := by
  obtain ⟨u, G, d, hd, _, hG, hzero⟩ :=
    GaloisClosedConeIntegralModel.exists_homogeneous_model (zeroSet H)
      (zeroSet_closed H) hcone (zeroSet_galois_stable H)
  have hgeneric : ∀ v : GeometricPoint n,
      (∀ i, eval₂Hom (Int.castRingHom GeometricField) v (H i) = 0) ↔
        ∀ i, eval₂Hom (Int.castRingHom GeometricField) v (G i) = 0 := hzero
  obtain ⟨D, hD, hgood⟩ := IntegerZeroSetSpreading.exists_good_characteristic_equivalence
    H G hgeneric
  exact ⟨u, G, d, D, hd, hD, hG, hgeneric, hgood⟩

end CubicTenVariables.IntegralConeZeroSetModel

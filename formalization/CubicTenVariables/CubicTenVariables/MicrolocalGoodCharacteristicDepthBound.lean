import CubicTenVariables.MicrolocalUniversalDepthBound
import CubicTenVariables.MicrolocalOffDepthBound
import CubicTenVariables.DegreeSpanReduction

/-! Transfer the actual depth-seven origin containment to every good
characteristic for the same incidence family. Exact reduced model ideals
allow coordinate-ideal membership to descend from the algebraic closure;
one fixed denominator then works for all fields and all frequencies.
No new literature or point-counting premise is used. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.MicrolocalGoodCharacteristicDepthBound
open MvPolynomial HessianTheorem11
open BihomogeneousIncidenceFamily ProjectiveMicrolocalData
open IntegralModelDimension

attribute [local instance] MvPolynomial.algebraMvPolynomial

private theorem coordinate_mem_rationalIdeal {n u : ℕ}
    (G : Fin u → MvPolynomial (Fin n) ℤ) (Z : Set (GeometricPoint n))
    (hmodel : geometricIdeal G = vanishingIdeal GeometricField Z)
    (hzero : Z ⊆ {0}) (i : Fin n) :
    map (Int.castRingHom ℚ) (X i : MvPolynomial (Fin n) ℤ) ∈ rationalIdeal G := by
  have hcontract :
      ((rationalIdeal G).map (map (algebraMap ℚ GeometricField))).comap
        (map (algebraMap ℚ GeometricField)) = rationalIdeal G :=
    Ideal.comap_map_eq_self_of_faithfullyFlat (rationalIdeal G)
  rw [← hcontract]
  change map (algebraMap ℚ GeometricField)
    (map (Int.castRingHom ℚ) (X i : MvPolynomial (Fin n) ℤ)) ∈
      (rationalIdeal G).map (map (algebraMap ℚ GeometricField))
  rw [map_X, map_X, map_rationalIdeal, hmodel]
  intro x hx
  have hx0 : x = 0 := Set.mem_singleton_iff.mp (hzero hx)
  simp only [hx0, aeval_X, Pi.zero_apply]

/-- Exact geometric origin containment of a fixed reduced model gives one
positive integer before every field and point; no finite-field hypothesis
is needed for this algebraic reduction. -/
theorem exists_model_origin_reduction {n u : ℕ}
    (G : Fin u → MvPolynomial (Fin n) ℤ) (Z : Set (GeometricPoint n))
    (hmodel : geometricIdeal G = vanishingIdeal GeometricField Z)
    (hzero : Z ⊆ {0}) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, ¬ p ∣ D →
      ∀ (K : Type*) [Field K] [CharP K p] (v : Fin n → K),
        (∀ i, eval₂ (Int.castRingHom K) v (G i) = 0) → v = 0 := by
  obtain ⟨D,hD,hgood⟩ := DegreeSpanReduction.exists_uniform_family_reduction
    G (fun i : Fin n => (X i : MvPolynomial (Fin n) ℤ))
    (coordinate_mem_rationalIdeal G Z hmodel hzero)
  refine ⟨D,hD,?_⟩
  intro p hp K _ _ v hv
  have h := hgood p hp K v (by simpa only [← eval₂_eq_eval_map] using hv)
  funext i
  simpa only [map_X, eval_X, Pi.zero_apply] using h i

/-- The same incidence model has geometric fiber dimension at most six at
all nonzero frequencies outside one fixed enlarged prime exclusion. The
excluded integer is chosen before the prime, its extensions and v. -/
theorem exists_bound {t : ℕ} {F : MvPolynomial (Fin 10) ℤ}
    {f : Fin t → Polynomial 10 10} {N B : ℕ}
    (hGeometry : Geometry F f) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (h : TenMicrolocalIncidence.Conclusion F f N B) (hN : 1 ≤ N) :
    ∃ D : ℕ, 1 ≤ D ∧ N ∣ D ∧ ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ D →
      ∀ (K : Type) [Field K] [CharP K p] (v : Fin 10 → K), v ≠ 0 →
        IntegralGeometricFiberDepth.geometricFiberDimension f K v ≤ (6 : Dimension) := by
  obtain ⟨u,G,d,hd,hmodel,hpoints,hgood⟩ := h.depth_models (⟨6,by omega⟩ : Fin 9)
  have hmodel7 : geometricIdeal G =
      vanishingIdeal GeometricField (ProjectiveMicrolocalDepth.depth f 7) := hmodel
  obtain ⟨E,hE,hzero⟩ := exists_model_origin_reduction G
    (ProjectiveMicrolocalDepth.depth f 7) hmodel7
    (MicrolocalUniversalDepthBound.depth_seven_subset_origin hGeometry hhom hAn)
  refine ⟨N*E,by nlinarith,dvd_mul_right N E,?_⟩
  intro p hp hpNE K _ _ v hv
  have hpN : ¬ p ∣ N := fun hdiv => hpNE (hdiv.trans (dvd_mul_right N E))
  have hpE : ¬ p ∣ E := fun hdiv => hpNE (hdiv.trans (dvd_mul_left E N))
  have hoff : ¬ (7 : Dimension) ≤
      IntegralGeometricFiberDepth.geometricFiberDimension f K v := by
    intro hdepth
    have heq : ∀ i, eval₂ (Int.castRingHom K) v (G i) = 0 :=
      ((hgood p hp.out hpN K).1 v).mpr hdepth
    exact hv (hzero p hpE K v heq)
  have hnat := MicrolocalOffDepthBound.depth_le_of_not_succ_le f K v 6 hoff
  apply (ProjectiveMicrolocalNumericalDepth.geometricFiberDimension_le_depth f K v).trans
  exact_mod_cast hnat

end CubicTenVariables.MicrolocalGoodCharacteristicDepthBound

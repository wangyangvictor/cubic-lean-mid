import CubicTenVariables.GaloisStableSubspacePoint
import CubicTenVariables.CubicSingularLinearSpaces
import CubicTenVariables.Literature.FiniteFieldPointCounts
import Mathlib.FieldTheory.Perfect

/-! A geometric singular plane of an integral cubic threefold descends to
a nonzero base-field singular point. Uniqueness of the plane is proved by
the cubic secant argument, and its Galois invariance is then derived from
the actual singular equations. No rationality of the plane is assumed. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CubicSingularPlanePoint
open MvPolynomial HessianTheorem11 Literature Module

variable {K : Type*} [Field K]

theorem eval_map_galois {n : ℕ}
    (F : MvPolynomial (Fin n) K)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (x : Fin n → AlgebraicClosure K) :
    eval (fun i => σ (x i)) (map (algebraMap K (AlgebraicClosure K)) F) =
      σ (eval x (map (algebraMap K (AlgebraicClosure K)) F)) := by
  have hc : σ.toRingHom.comp (algebraMap K (AlgebraicClosure K)) =
      algebraMap K (AlgebraicClosure K) := by
    ext a
    exact σ.commutes a
  simp only [eval_map]
  rw [show σ (eval₂ (algebraMap K (AlgebraicClosure K)) x F) =
      σ.toRingHom (eval₂ (algebraMap K (AlgebraicClosure K)) x F) from rfl,
    eval₂_comp_left, hc]
  rfl

/-- The actual geometric singular equations are stable under every
base-field automorphism of the algebraic closure. -/
theorem singularCone_galois {n : ℕ}
    (F : MvPolynomial (Fin n) K)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (x : Fin n → AlgebraicClosure K) (hx : x ∈ geometricSingularCone F) :
    (fun i => σ (x i)) ∈ geometricSingularCone F := by
  constructor
  · rw [eval_map_galois, hx.1, map_zero]
  · intro i
    rw [pderiv_map, eval_map_galois]
    have hi := hx.2 i
    rw [pderiv_map] at hi
    rw [hi, map_zero]

theorem base_point_singular_iff {n : ℕ}
    (F : MvPolynomial (Fin n) K) (z : Fin n → K) :
    (fun i => algebraMap K (AlgebraicClosure K) (z i)) ∈ geometricSingularCone F ↔
      eval z F = 0 ∧ gradient F z = 0 := by
  change (eval ((algebraMap K (AlgebraicClosure K)) ∘ z)
      (map (algebraMap K (AlgebraicClosure K)) F) = 0 ∧
      ∀ i, eval ((algebraMap K (AlgebraicClosure K)) ∘ z)
        (pderiv i (map (algebraMap K (AlgebraicClosure K)) F)) = 0) ↔ _
  simp only [pderiv_map, eval_map, ← eval₂_comp, map_eq_zero,
    funext_iff, HessianTheorem11.gradient, Pi.zero_apply]

/-- If the full geometric singular cone is a positive-dimensional linear
space, it has a nonzero base-field point over every perfect field. -/
theorem exists_point_of_linear_singularCone [PerfectField K] {n : ℕ}
    (F : MvPolynomial (Fin n) K)
    (T : Submodule (AlgebraicClosure K) (Fin n → AlgebraicClosure K))
    (hdim : 0 < finrank (AlgebraicClosure K) T)
    (hT : (T : Set (Fin n → AlgebraicClosure K)) = geometricSingularCone F) :
    ∃ z : Fin n → K, z ≠ 0 ∧ eval z F = 0 ∧ gradient F z = 0 := by
  letI : IsGalois K (AlgebraicClosure K) := ⟨⟩
  obtain ⟨z,hz,hmem⟩ := GaloisStableSubspacePoint.exists_nonzero_base_point T hdim (by
    intro σ x hx
    change x ∈ (T : Set _) at hx
    change (fun i => σ (x i)) ∈ (T : Set _)
    rw [hT] at hx ⊢
    exact singularCone_galois F σ x hx)
  exact ⟨z,hz,(base_point_singular_iff F z).mp (hT ▸ hmem)⟩

/-- A supplied geometric singular plane is automatically the full singular
cone, hence descends. The plane need not be defined over the base field. -/
theorem exists_point_of_singular_plane [PerfectField K]
    (F : MvPolynomial (Fin 5) K) (hF : F.IsHomogeneous 3)
    (hI : GeometricallyIntegralForm F)
    (T : Submodule (AlgebraicClosure K) (Fin 5 → AlgebraicClosure K))
    (hdim : finrank (AlgebraicClosure K) T = 3)
    (hT : ∀ x ∈ T, x ∈ geometricSingularCone F) :
    ∃ z : Fin 5 → K, z ≠ 0 ∧ eval z F = 0 ∧ gradient F z = 0 := by
  let G := map (algebraMap K (AlgebraicClosure K)) F
  have hG : G.IsHomogeneous 3 := hF.map _
  have hGne : G ≠ 0 := by
    intro hz
    apply hI.1
    apply map_injective (algebraMap K (AlgebraicClosure K))
      (algebraMap K (AlgebraicClosure K)).injective
    simpa only [map_zero] using hz
  have hirr : Irreducible G :=
    ((Ideal.span_singleton_prime hGne).mp ((Ideal.Quotient.isDomain_iff_prime _).mp hI.2)).irreducible
  have hT' : ∀ x ∈ T, eval x G = 0 ∧ gradient G x = 0 := by
    intro x hx
    exact ⟨(hT x hx).1, funext (hT x hx).2⟩
  apply exists_point_of_linear_singularCone F T (by omega)
  ext x
  constructor
  · exact hT x
  · intro hx
    exact CubicSingularLinearSpaces.singular_point_mem_singular_plane G hG hirr T hdim hT'
      x hx.1 (funext hx.2)

end CubicTenVariables.CubicSingularPlanePoint

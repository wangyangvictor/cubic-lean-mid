import CubicTenVariables.FiniteFieldCubicSingularPointCount
import CubicTenVariables.ReducedVertexBaseChange
import CubicTenVariables.SmoothCubicProjectivePointCount
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.MvPolynomial.Equiv

/-! A literal finite extension on which a geometrically singular cubic
surface satisfies the proved projection estimate over every further finite
extension. The constant precedes the base field and surface. There is no
trace, weight, amplification or descent-of-counts premise here. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CubicSurfacePotentialGoodness
open MvPolynomial Literature HessianTheorem11 ReducedCubicVertex

/-- Geometric integrality is preserved by finite coefficient extensions. -/
theorem integral_map_finite {K L : Type} [Field K] [Field L] [Finite L]
    {n : ℕ} (ρ : K →+* L) (F : MvPolynomial (Fin n) K)
    (hI : GeometricallyIntegralForm F) : GeometricallyIntegralForm (map ρ F) := by
  letI : Algebra K L := ρ.toAlgebra
  letI : IsAlgClosure K (AlgebraicClosure L) :=
    IsAlgClosure.ofAlgebraic K L (AlgebraicClosure L)
  let e := IsAlgClosure.equiv K (AlgebraicClosure K) (AlgebraicClosure L)
  have hne : map (algebraMap K (AlgebraicClosure K)) F ≠ 0 :=
    fun h => hI.1 ((map_injective _ (algebraMap K (AlgebraicClosure K)).injective)
      (by simpa only [map_zero] using h))
  have hirr : Irreducible (map (algebraMap K (AlgebraicClosure K)) F) :=
    ((Ideal.span_singleton_prime hne).mp
      ((Ideal.Quotient.isDomain_iff_prime _).mp hI.2)).irreducible
  have he : e.toRingHom.comp (algebraMap K (AlgebraicClosure K)) =
      (algebraMap L (AlgebraicClosure L)).comp ρ := by
    ext x
    exact (e.commutes x).trans (IsScalarTower.algebraMap_apply K L (AlgebraicClosure L) x)
  have hirr' := (MulEquiv.irreducible_iff
    (mapEquiv (Fin n) e.toRingEquiv)).mpr hirr
  change Irreducible (map e.toRingHom (map (algebraMap K (AlgebraicClosure K)) F)) at hirr'
  rw [map_map, he, ← map_map] at hirr'
  refine ⟨fun h => hI.1 ((map_injective ρ ρ.injective)
    (by simpa only [map_zero] using h)), ?_⟩
  exact (Ideal.Quotient.isDomain_iff_prime _).mpr
    ((Ideal.span_singleton_prime hirr'.ne_zero).mpr hirr'.prime)

/-- The actual Hessian-kernel criterion preserves geometric nonconicality
under arbitrary field extension; characteristics two and three are excluded. -/
theorem nonconical_map {K L : Type} [Field K] [Field L] {n : ℕ}
    (ρ : K →+* L) (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (hNC : GeometricallyNonconicalCubic F) :
    GeometricallyNonconicalCubic (map ρ F) := by
  letI : Algebra K L := ρ.toAlgebra
  have hbot : affineVertex F hF = ⊥ := by
    apply (ReducedVertexBaseChange.affineVertex_baseChange_eq_bot_iff
      (L := AlgebraicClosure K) F hF).mp
    apply bot_unique
    intro v hv
    exact (geometricallyNonconicalCubic_iff_hessian F hF h2 h3).mp hNC v hv
  have hbotL : affineVertex (map ρ F) (hF.map ρ) = ⊥ :=
    (ReducedVertexBaseChange.affineVertex_baseChange_eq_bot_iff (L := L) F hF).mpr hbot
  have hbotA := (ReducedVertexBaseChange.affineVertex_baseChange_eq_bot_iff
    (L := AlgebraicClosure L) (map ρ F) (hF.map ρ)).mpr hbotL
  have h2L : (2 : L) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero ρ).mpr h2
  have h3L : (3 : L) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero ρ).mpr h3
  apply (geometricallyNonconicalCubic_iff_hessian _ (hF.map ρ) h2L h3L).mpr
  intro v hv
  have hm : v ∈ affineVertex (map (algebraMap L (AlgebraicClosure L)) (map ρ F))
      ((hF.map ρ).map _) := hv
  rw [hbotA] at hm
  exact hm

private theorem eval_map_coordinates {K L : Type} [Field K] [Field L]
    {n : ℕ} (ρ : K →+* L) (F : MvPolynomial (Fin n) K) (x : Fin n → K) :
    eval (fun i => ρ (x i)) (map ρ F) = ρ (eval x F) := by
  simpa only [eval_map, Function.comp_def] using (eval₂_comp ρ x F).symm

/-- All coordinates of a geometric singular point lie in one actual finite
intermediate field of the chosen algebraic closure. -/
theorem exists_finite_singular_point {K : Type} [Field K] [Finite K] {n : ℕ}
    (F : MvPolynomial (Fin n) K)
    (hs : ∃ x : Fin n → AlgebraicClosure K, x ≠ 0 ∧ x ∈ geometricSingularCone F) :
    ∃ E : IntermediateField K (AlgebraicClosure K), FiniteDimensional K E ∧ Finite E ∧
      ∃ z : Fin n → E, z ≠ 0 ∧ eval z (map (algebraMap K E) F) = 0 ∧
        gradient (map (algebraMap K E) F) z = 0 := by
  classical
  obtain ⟨x, hx, hz, hgrad⟩ := hs
  let E := IntermediateField.adjoin K (Set.range x)
  letI : FiniteDimensional K E :=
    IntermediateField.finiteDimensional_adjoin (fun y _ => Algebra.IsIntegral.isIntegral y)
  letI : Finite E := Module.finite_of_finite K
  let z : Fin n → E := fun i => ⟨x i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  have hmap : (algebraMap E (AlgebraicClosure K)).comp (algebraMap K E) =
      algebraMap K (AlgebraicClosure K) := by ext a; rfl
  have heval (P : MvPolynomial (Fin n) K) :
      (algebraMap E (AlgebraicClosure K)) (eval z (map (algebraMap K E) P)) =
        eval x (map (algebraMap K (AlgebraicClosure K)) P) := by
    rw [← eval_map_coordinates (algebraMap E (AlgebraicClosure K)), map_map, hmap]
    rfl
  refine ⟨E, inferInstance, inferInstance, z, ?_, ?_, ?_⟩
  · intro h
    apply hx
    funext i
    exact congrArg (fun a : E => (a : AlgebraicClosure K)) (congrFun h i)
  · apply (algebraMap E (AlgebraicClosure K)).injective
    simpa only [heval, map_zero] using hz
  · funext i
    apply (algebraMap E (AlgebraicClosure K)).injective
    simpa only [HessianTheorem11.gradient, pderiv_map, heval, Pi.zero_apply, map_zero] using hgrad i

/-- The actual potential-goodness estimate, without any descent assertion.
One absolute B works for every cubic surface. After adjoining a geometric
singular point, it holds over every further finite extension (every embedding
of that intermediate field), for the literal coefficient extension of F. -/
theorem exists_uniform_potential_bound :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (K : Type) [Field K] [Fintype K]
      (F : MvPolynomial (Fin 4) K), F.IsHomogeneous 3 →
      (2 : K) ≠ 0 → (3 : K) ≠ 0 → GeometricallyIntegralForm F →
      GeometricallyNonconicalCubic F →
      (∃ x : Fin 4 → AlgebraicClosure K, x ≠ 0 ∧ x ∈ geometricSingularCone F) →
      ∃ E : IntermediateField K (AlgebraicClosure K), FiniteDimensional K E ∧ Finite E ∧
        ∀ (L : Type) [Field L] [Fintype L] (τ : E →+* L),
          |(affineZeroCount (map (τ.comp (algebraMap K E)) F) : ℝ) -
            (Fintype.card L : ℝ)^3| ≤
          B * ((Fintype.card L : ℝ)-1) * (Fintype.card L : ℝ) := by
  obtain ⟨B, hB, hbound⟩ := FiniteFieldCubicSingularPointCount.exists_bound 3 (by decide)
  refine ⟨B, hB, ?_⟩
  intro K _ _ F hF h2 h3 hI hNC hs
  obtain ⟨E, hE, hfin, z, hz, hzero, hgrad⟩ := exists_finite_singular_point F hs
  refine ⟨E, hE, hfin, ?_⟩
  intro L _ _ τ
  let ρ := τ.comp (algebraMap K E)
  have h2L : (2 : L) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero ρ).mpr h2
  have h3L : (3 : L) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero ρ).mpr h3
  suffices hsL : ∃ w : Fin 4 → L, w ≠ 0 ∧ eval w (map ρ F) = 0 ∧
      gradient (map ρ F) w = 0 by
    simpa only [Nat.reduceSub, pow_one] using
      hbound L (map ρ F) (hF.map ρ) h2L h3L
        (integral_map_finite ρ F hI) (nonconical_map ρ F hF h2 h3 hNC) hsL
  refine ⟨fun i => τ (z i), ?_, ?_, ?_⟩
  · intro h
    apply hz
    funext i
    apply τ.injective
    simpa only [Pi.zero_apply, map_zero] using congrFun h i
  · change eval _ (map (τ.comp (algebraMap K E)) F) = 0
    rw [← map_map, eval_map_coordinates, hzero, map_zero]
  · funext i
    change eval _ (pderiv i (map (τ.comp (algebraMap K E)) F)) = 0
    rw [← map_map, pderiv_map, eval_map_coordinates]
    simpa only [HessianTheorem11.gradient, Pi.zero_apply, map_zero] using congrArg τ (congrFun hgrad i)

/-- The same potential-goodness statement for literal projective points,
with one absolute constant and error at most B*q over every further field. -/
theorem exists_uniform_projective_potential_bound :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (K : Type) [Field K] [Fintype K]
      (F : MvPolynomial (Fin 4) K), F.IsHomogeneous 3 →
      (2 : K) ≠ 0 → (3 : K) ≠ 0 → GeometricallyIntegralForm F →
      GeometricallyNonconicalCubic F →
      (∃ x : Fin 4 → AlgebraicClosure K, x ≠ 0 ∧ x ∈ geometricSingularCone F) →
      ∃ E : IntermediateField K (AlgebraicClosure K), FiniteDimensional K E ∧ Finite E ∧
        ∀ (L : Type) [Field L] [Fintype L] (τ : E →+* L),
          |(Nat.card (ProjectiveFourierIdentity.zeroPoints
              (map (τ.comp (algebraMap K E)) F)) : ℝ) -
            ((Fintype.card L : ℝ)^2 + (Fintype.card L : ℝ) + 1)| ≤
          B * (Fintype.card L : ℝ) := by
  obtain ⟨B, hB, h⟩ := exists_uniform_potential_bound
  refine ⟨B, hB, ?_⟩
  intro K _ _ F hF h2 h3 hI hNC hs
  obtain ⟨E, hE, hfin, hcount⟩ := h K F hF h2 h3 hI hNC hs
  refine ⟨E, hE, hfin, ?_⟩
  intro L _ _ τ
  have hb := hcount L τ
  let G := map (τ.comp (algebraMap K E)) F
  let q : ℝ := Fintype.card L
  have hq : 0 < q - 1 := by
    have hh : (1 : ℝ) < Fintype.card L := by
      exact_mod_cast (Fintype.one_lt_card (α := L))
    dsimp only [q]
    linarith
  have hc := SmoothCubicProjectivePointCount.real_affine_cone_card G (hF.map _) (by decide)
  have he : (affineZeroCount G : ℝ) - q^3 =
      (q-1) * ((Nat.card (ProjectiveFourierIdentity.zeroPoints G) : ℝ) - (q^2+q+1)) := by
    change (affineZeroCount G : ℝ) =
      1 + (q-1) * (Nat.card (ProjectiveFourierIdentity.zeroPoints G) : ℝ) at hc
    rw [hc]
    ring
  change |(affineZeroCount G : ℝ) - q^3| ≤ B*(q-1)*q at hb
  rw [he, abs_mul, abs_of_pos hq] at hb
  apply le_of_mul_le_mul_left (a := q-1) ?_ hq
  calc
    (q-1) * |(Nat.card (ProjectiveFourierIdentity.zeroPoints G) : ℝ) - (q^2+q+1)| ≤
        B*(q-1)*q := hb
    _ = (q-1) * (B*q) := by ring

end CubicTenVariables.CubicSurfacePotentialGoodness

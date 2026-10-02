import CubicTenVariables.HypersurfaceIntegralFrameCertificate
import CubicTenVariables.GenericHyperplaneFrameOpen
import CubicTenVariables.ReducedConeCoordinates
import CubicTenVariables.IntegralFirstCoordinateShear
import TranslatedDepthSeven.FieldPolynomialNatGridInternal

/-!
# An integral slicing shear for one fixed leading form

The internally proved Bertini theorem supplies a good full frame.  The
explicit geometric-integrality openness premise moves that frame to the
graph chart and then selects integer graph coefficients.  No bound uniform
in the degree or in the leading form is asserted or needed here.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
noncomputable section

namespace CubicTenVariables.FixedLeadingFormIntegralShear

open MvPolynomial TranslatedDepthSeven
open HessianTheorem11.PolynomialRestriction
open HessianTheorem11.PolynomialWeightTransport
open scoped Matrix BigOperators

/-- The graph `x₀ = ∑ aᵢ xᵢ₊₁`, with the remaining coordinates unchanged. -/
def graphFrame {R : Type*} [CommRing R] {n : ℕ}
    (a : Fin n → R) : Matrix (Fin (n + 1)) (Fin n) R :=
  Fin.cons a (1 : Matrix (Fin n) (Fin n) R)

theorem graphFrame_mul {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin n) K)
    (M : Matrix (Fin n) (Fin n) K) (a : Fin n → K)
    (htail : ∀ i j, M i j = A i.succ j)
    (ha : M.vecMul a = A 0) : graphFrame a * M = A := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · exact congrFun ha j
  · simpa [graphFrame, Matrix.mul_apply, Matrix.one_apply] using htail i j

theorem graphFrame_mulVec {R : Type*} [CommRing R] {n : ℕ}
    (a x : Fin n → R) :
    (graphFrame a).mulVec x = Fin.cases (∑ i, a i * x i) x := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;>
    simp [graphFrame, Matrix.mulVec, dotProduct, Matrix.one_apply]

/-- Restriction to the graph is precisely the coordinate-zero section of
the shear, with the sign of its coefficients unchanged. -/
theorem restrict_graphFrame_eq_shear_slice {n : ℕ}
    (a : Fin n → ℚ) (H : MvPolynomial (Fin (n + 1)) ℚ) :
    restrict (graphFrame a) H = rationalSpecializeFirstCoordinate 0
      (firstCoordinateShearPolynomialEquiv a H) := by
  apply MvPolynomial.funext
  intro x
  rw [eval_restrict, eval_rationalSpecializeFirstCoordinate,
    eval_firstCoordinateShearPolynomialEquiv, graphFrame_mulVec]
  apply congrArg (fun y : Fin (n + 1) → ℚ => eval y H)
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [firstCoordinateShear]

private theorem exists_eval_ne_zero {σ : Type*}
    (P : MvPolynomial σ ℚ) (hP : P ≠ 0) :
    ∃ x, eval x P ≠ 0 := by
  by_contra! h
  apply hP
  apply MvPolynomial.funext
  intro x
  simpa only [map_zero] using h x

/-- A full-frame integrality certificate meets the graph chart. -/
theorem exists_rational_good_graph
    (integralityOpen : Literature.HomogeneousHypersurfaceIntegralityOpen)
    {d : ℕ} (hd : 2 ≤ d)
    (H : MvPolynomial (Fin 4) ℚ) (hhom : H.IsHomogeneous d)
    (hirr : Published.IsAbsolutelyIrreducible H) :
    ∃ a : Fin 3 → ℚ,
      restrict (graphFrame a) H ≠ 0 ∧
      IsDomain (MvPolynomial (Fin 3) (AlgebraicClosure ℚ) ⧸
        Ideal.span {map (algebraMap ℚ (AlgebraicClosure ℚ))
          (restrict (graphFrame a) H)}) := by
  classical
  let Ω := AlgebraicClosure ℚ
  obtain ⟨L, hL, hdata⟩ :=
    IntegralHypersurfaceBertiniFrame.exists_integral_surface_hyperplane_frame_nonzero
      hd (map (algebraMap ℚ Ω) H) (hhom.map _) hirr
  letI : Field L := hL
  obtain ⟨hA, hdata⟩ := hdata
  letI : Algebra Ω L := hA
  obtain ⟨hclosed, B, hB, hBne, _hBhom, hBdomain⟩ := hdata
  letI : IsAlgClosed L := hclosed
  let ρ : ℚ →+* L := (algebraMap Ω L).comp (algebraMap ℚ Ω)
  have hmap : map ρ H = map (algebraMap Ω L) (map (algebraMap ℚ Ω) H) := by
    rw [map_map]
  obtain ⟨Δ, hΔB, hgood⟩ :=
    HypersurfaceIntegralFrameCertificate.exists_nonzero_certificate_of_good_frame
      integralityOpen (by omega : 1 ≤ d) ρ H hhom B hB
      (by rw [hmap]; exact hBne) (by rw [hmap]; exact hBdomain)
  have hΔ : Δ ≠ 0 := fun hz => hΔB (by rw [hz, map_zero])
  let D : MvPolynomial (Fin 4 × Fin 3) ℚ :=
    Matrix.det (fun i j : Fin 3 => X (i.succ, j))
  have hD : D ≠ 0 := GenericHyperplaneFrameOpen.lowerMinor_ne_zero
  obtain ⟨b, hb⟩ := exists_eval_ne_zero (Δ * D) (mul_ne_zero hΔ hD)
  have hb' : eval b Δ ≠ 0 ∧ eval b D ≠ 0 :=
    mul_ne_zero_iff.mp (by simpa only [map_mul] using hb)
  let A : Matrix (Fin 4) (Fin 3) ℚ := fun i j => b (i, j)
  let M : Matrix (Fin 3) (Fin 3) ℚ := fun i j => A i.succ j
  have hM : M.det ≠ 0 := by
    have he : eval b D = M.det := by
      dsimp only [D]
      rw [RingHom.map_det]
      congr 1
      ext i j
      simp [M, A]
    exact he ▸ hb'.2
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  obtain ⟨a, ha⟩ := Matrix.vecMul_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det M).mpr hunit) (A 0)
  have hframe : graphFrame a * M = A := graphFrame_mul A M a (fun _ _ => rfl) ha
  have hgoodA := hgood ℚ (RingHom.id ℚ) A hb'.1
  rw [MvPolynomial.map_id] at hgoodA
  have hAne : restrict A H ≠ 0 := by
    intro hz
    have he := hgoodA.2.2.1
    rw [hz, totalDegree_zero] at he
    omega
  have hfactor : restrict A H = restrict M (restrict (graphFrame a) H) := by
    rw [restrict_restrict, hframe]
  refine ⟨a, ?_, ?_⟩
  · intro hz
    apply hAne
    rw [hfactor, hz]
    exact map_zero (aeval (linearForms M))
  · exact ReducedConeCoordinates.quotient_domain_baseChange_of_factor
      (restrict A H) (restrict (graphFrame a) H) M M⁻¹
      (Matrix.mul_nonsing_inv M hunit) hfactor hgoodA.2.2.2

/-- The literal polynomial family parametrizing all graph hyperplanes. -/
def graphFamily {n : ℕ} (H : MvPolynomial (Fin (n + 1)) ℚ) :
    MvPolynomial (Fin n) (MvPolynomial (Fin n) ℚ) :=
  restrict (graphFrame (fun i => X i)) (map C H)

theorem specialize_graphFamily {K : Type*} [CommRing K] {n : ℕ}
    (ρ : ℚ →+* K) (a : Fin n → K)
    (H : MvPolynomial (Fin (n + 1)) ℚ) :
    map (eval₂Hom ρ a) (graphFamily H) = restrict (graphFrame a) (map ρ H) := by
  have hc : (eval₂Hom ρ a).comp (C : ℚ →+* MvPolynomial (Fin n) ℚ) = ρ := by
    ext r
    simp
  rw [graphFamily, map_restrict, map_map, hc]
  congr 1
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [graphFrame, Matrix.map_apply]
  · by_cases hij : i = j <;>
      simp [graphFrame, Matrix.map_apply, Matrix.one_apply, hij]

/-- For one fixed rational absolutely irreducible homogeneous form in four
variables, an integral shear has an absolutely irreducible plane section.
The only explicit literature premise is fixed-degree integrality openness. -/
theorem exists_integral_shear_absIrreducible
    (integralityOpen : Literature.HomogeneousHypersurfaceIntegralityOpen)
    {d : ℕ} (hd : 2 ≤ d)
    (H : MvPolynomial (Fin 4) ℚ) (hhom : H.IsHomogeneous d)
    (hirr : Published.IsAbsolutelyIrreducible H) :
    ∃ a : Fin 3 → ℤ,
      Published.IsAbsolutelyIrreducible
        (rationalSpecializeFirstCoordinate 0
          (firstCoordinateShearPolynomialEquiv (fun i => (a i : ℚ)) H)) := by
  classical
  obtain ⟨a, hane, hadomain⟩ := exists_rational_good_graph integralityOpen hd H hhom hirr
  let Ω := AlgebraicClosure ℚ
  let ρ : MvPolynomial (Fin 3) ℚ →+* Ω :=
    eval₂Hom (algebraMap ℚ Ω) (fun i => algebraMap ℚ Ω (a i))
  have hspecial : map ρ (graphFamily H) =
      map (algebraMap ℚ Ω) (restrict (graphFrame a) H) := by
    rw [specialize_graphFamily, map_restrict]
    congr 1
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;>
      simp [graphFrame, Matrix.map_apply, Matrix.one_apply]
  have hne : map ρ (graphFamily H) ≠ 0 := by
    rw [hspecial]
    exact fun hz => hane ((map_injective _ (algebraMap ℚ Ω).injective)
      (by simpa only [map_zero] using hz))
  obtain ⟨s, hs, hopen⟩ := integralityOpen (MvPolynomial (Fin 3) ℚ) Ω 3 d
    (by omega : 1 ≤ d) ρ (graphFamily H)
    (homogeneous_restrict _ _ (hhom.map C)) hne (by rw [hspecial]; exact hadomain)
  have hsne : s ≠ 0 := fun hz => hs (by rw [hz, map_zero])
  obtain ⟨z, _hzbound, hz⟩ := exists_nonzero_eval_on_boundedNatGrid_over_field
    s hsne (le_refl s.totalDegree)
  let b : Fin 3 → ℤ := fun i => z i
  have hb : eval (fun i => (b i : ℚ)) s ≠ 0 := by
    simpa only [b, Int.cast_natCast] using hz
  have hgood := hopen ℚ (eval (fun i => (b i : ℚ))) hb
  have heval : map (eval (fun i => (b i : ℚ))) (graphFamily H) =
      restrict (graphFrame (fun i => (b i : ℚ))) H := by
    simpa only [map_id] using specialize_graphFamily (RingHom.id ℚ)
      (fun i => (b i : ℚ)) H
  rw [heval] at hgood
  have hgne : restrict (graphFrame (fun i => (b i : ℚ))) H ≠ 0 := by
    intro hz
    rw [hz, totalDegree_zero] at hgood
    omega
  have hgeone : map (algebraMap ℚ Ω)
      (restrict (graphFrame (fun i => (b i : ℚ))) H) ≠ 0 := by
    exact fun hz => hgne ((map_injective _ (algebraMap ℚ Ω).injective)
      (by simpa only [map_zero] using hz))
  refine ⟨b, ?_⟩
  rw [← restrict_graphFrame_eq_shear_slice]
  exact ((Ideal.span_singleton_prime hgeone).mp
    ((Ideal.Quotient.isDomain_iff_prime _).mp hgood.2)).irreducible

end CubicTenVariables.FixedLeadingFormIntegralShear

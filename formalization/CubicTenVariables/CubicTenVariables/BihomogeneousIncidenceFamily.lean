import CubicTenVariables.FiniteIncidenceDepth
import CubicTenVariables.Literature.FiberDimensionSpreading
import CubicTenVariables.CubicGradientScaling

/-! Literal integral two-block equations for the microlocal incidence.
Homogeneity in the parameter block is imposed on the actual coefficients,
and homogeneity in the fiber block on the outer polynomial. These properties
survive every coefficient specialization, including bad characteristic.
This file constructs no singular support and assumes no literature result. -/

noncomputable section
namespace CubicTenVariables.BihomogeneousIncidenceFamily
open MvPolynomial HessianTheorem11
open TerminalFiberCoordinates FiniteIncidenceDepth
open scoped BigOperators

abbrev Polynomial (m n : ℕ) := MvPolynomial (Fin n) (MvPolynomial (Fin m) ℤ)

/-- Literal evaluation: inner variables are normals and outer variables points. -/
def value {m n : ℕ} (P : Polynomial m n) {K : Type*} [CommRing K]
    (v : Fin m → K) (x : Fin n → K) : K :=
  eval₂ (eval₂Hom (Int.castRingHom K) v) x P

def fiber {m n : ℕ} {ι : Type*} (f : ι → Polynomial m n)
    (K : Type*) [CommRing K] (v : Fin m → K) : Set (Fin n → K) :=
  {x | ∀ i, value (f i) v x = 0}

theorem fiber_eq_zeroLocus {m n : ℕ} {ι : Type*} (f : ι → Polynomial m n)
    (K : Type*) [Field K] (v : Fin m → K) :
    fiber f K v = zeroLocus K (Literature.integralFamilyFiberIdeal f K v) := by
  ext x
  rw [Literature.integralFamilyFiberIdeal, zeroLocus_span]
  change (∀ i, value (f i) v x = 0) ↔
    ∀ P ∈ Set.range (fun i => map (eval₂Hom (Int.castRingHom K) v) (f i)), eval x P = 0
  simp only [Set.forall_mem_range, value, eval_map]

theorem value_smul_parameter {m n d : ℕ} (P : Polynomial m n)
    (hP : ∀ s, (coeff s P).IsHomogeneous d)
    {K : Type*} [CommRing K] (v : Fin m → K) (x : Fin n → K) (a : K) :
    value P (a • v) x = a^d * value P v x := by
  classical
  simp only [value, eval₂_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  change eval₂ (Int.castRingHom K) (a • v) (coeff s P) * _ = _
  rw [CubicGradientScaling.homogeneous_eval₂_smul _ (hP s)]
  change a^d * eval₂ (Int.castRingHom K) v (coeff s P) * _ =
    a^d * (eval₂ (Int.castRingHom K) v (coeff s P) * _)
  ring

theorem value_smul_point {m n d : ℕ} (P : Polynomial m n)
    (hP : P.IsHomogeneous d) {K : Type*} [CommRing K]
    (v : Fin m → K) (x : Fin n → K) (a : K) :
    value P v (a • x) = a^d * value P v x :=
  CubicGradientScaling.homogeneous_eval₂_smul P hP _ x a

theorem fiber_subset_smul_parameter {m n : ℕ} {ι : Type*}
    (f : ι → Polynomial m n) (d : ι → ℕ)
    (hf : ∀ i s, (coeff s (f i)).IsHomogeneous (d i))
    {K : Type*} [CommRing K] (v : Fin m → K) (a : K) :
    fiber f K v ⊆ fiber f K (a • v) := by
  intro x hx i
  rw [value_smul_parameter _ (hf i), hx i, mul_zero]

theorem fiber_smul_parameter_eq {m n : ℕ} {ι : Type*}
    (f : ι → Polynomial m n) (d : ι → ℕ)
    (hf : ∀ i s, (coeff s (f i)).IsHomogeneous (d i))
    {K : Type*} [Field K] (v : Fin m → K) (a : K) (ha : a ≠ 0) :
    fiber f K (a • v) = fiber f K v := by
  apply Set.Subset.antisymm
  · have h := fiber_subset_smul_parameter f d hf (a • v) a⁻¹
    simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using h
  · exact fiber_subset_smul_parameter f d hf v a

theorem fiber_stable_smul_point {m n : ℕ} {ι : Type*}
    (f : ι → Polynomial m n) (d : ι → ℕ)
    (hf : ∀ i, (f i).IsHomogeneous (d i))
    {K : Type*} [CommRing K] (v : Fin m → K) (a : K)
    (x : Fin n → K) (hx : x ∈ fiber f K v) : a • x ∈ fiber f K v := by
  intro i
  rw [value_smul_point _ (hf i), hx i, mul_zero]

theorem origin_mem_fiber {m n : ℕ} {ι : Type*}
    (f : ι → Polynomial m n) (d : ι → ℕ)
    (hf : ∀ i, (f i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    {K : Type*} [CommRing K] (v : Fin m → K) : (0 : Fin n → K) ∈ fiber f K v := by
  intro i
  have h := value_smul_point (f i) (hf i) v (0 : Fin n → K) (0 : K)
  simpa only [zero_smul, zero_pow (hd i).ne', zero_mul] using h

/-- Same actual equations, now over the fixed algebraic closure of Q. -/
def geometricEquations {m n : ℕ} {ι : Type*} (f : ι → Polynomial m n) :
    ι → MvPolynomial (Fin n) (GeometricPolynomial m) :=
  fun i => map (map (Int.castRingHom GeometricField)) (f i)

theorem fiber_eq_geometric_fiber {m n : ℕ} {ι : Type*}
    (f : ι → Polynomial m n) (v : GeometricPoint m) :
    fiber f GeometricField v = HomogeneousFamilyBadLocus.fiber (geometricEquations f) v := by
  ext x
  simp only [fiber, value, HomogeneousFamilyBadLocus.fiber,
    HomogeneousFamilyBadLocus.specialized, geometricEquations, Set.mem_setOf_eq]
  apply forall_congr'
  intro i
  have he : (eval v).comp (map (Int.castRingHom GeometricField)) =
      eval₂Hom (Int.castRingHom GeometricField) v := by
    apply RingHom.ext
    intro P
    exact eval_map (Int.castRingHom GeometricField) v P
  rw [map_map, he, eval_map]

/-- Actual incidence in the existing (point,normal) coordinates. -/
def geometricIncidence {n : ℕ} {ι : Type*} (f : ι → Polynomial n n) :
    Set (GeometricPoint (n+n)) :=
  {y | polynomialMap (pointProjection n) y ∈
    fiber f GeometricField (polynomialMap (normalProjection n) y)}

theorem pointFiber_geometricIncidence {n : ℕ} {ι : Type*}
    (f : ι → Polynomial n n) (v : GeometricPoint n) :
    pointFiber (geometricIncidence f) v = fiber f GeometricField v := by
  ext x
  simp only [pointFiber, geometricIncidence, Set.mem_setOf_eq,
    pointProjection_section, normalProjection_section]

theorem depth_closed {n : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → Polynomial n n) (d : ι → ℕ)
    (hf : ∀ i, (f i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i) (t : ℕ) :
    AlgebraicallyClosedSet
      (FiberJumpDimension.largeFiberParameters (normalProjection n) (geometricIncidence f) (t+1)) := by
  apply depth_closed_of_equations (geometricIncidence f) (geometricEquations f) d
    (fun i => (hf i).map _) hd
  intro v
  rw [pointFiber_geometricIncidence, fiber_eq_geometric_fiber]

theorem depth_cone {n : ℕ} {ι : Type*}
    (f : ι → Polynomial n n) (d : ι → ℕ)
    (hf : ∀ i s, (coeff s (f i)).IsHomogeneous (d i)) (j : ℕ) :
    IsAffineCone
      (FiberJumpDimension.largeFiberParameters (normalProjection n) (geometricIncidence f) j) := by
  apply depth_isAffineCone
  intro v a
  rw [pointFiber_geometricIncidence, pointFiber_geometricIncidence]
  exact fiber_subset_smul_parameter f d hf v a

end CubicTenVariables.BihomogeneousIncidenceFamily

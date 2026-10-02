import CubicTenVariables.FixedIntegralSurfaceSection
import CubicTenVariables.FrameRestrictionIrreducibility
import CubicTenVariables.PlaneCubicSingularGeometry
import CubicTenVariables.Literature.HomogeneousHypersurfaceIntegralityOpen
import HessianTheorem11.MatrixRankMinors
import Mathlib.LinearAlgebra.CrossProduct

/-!
# A fixed integral pencil through a geometrically integral surface section

This file turns the fixed integral Bertini frame into a form adapted to the
affine chart `X 0 != 0`.  The first column retains its nonzero zeroth
coordinate, while the other two columns have zeroth coordinate zero.  The
change of the three plane coordinates has determinant `A 0 0 ^ 2`; hence it
preserves the actual plane and its geometric integrality in every field in
which that integer is nonzero.

The remaining construction of the parallel affine pencil will adjoin a
third spatial direction to the two direction columns produced here.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace CubicTenVariables.FixedIntegralSurfacePencil

open MvPolynomial Literature HessianTheorem11
open HessianTheorem11.PolynomialRestriction
open CubicTenVariables.FrameRestrictionIrreducibility
open scoped Matrix

/-- The triangular plane-coordinate change which kills the zeroth entries
of columns one and two. -/
def chartChange {R : Type*} [CommRing R]
    (A : Matrix (Fin 4) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j =>
    if i = 0 then
      if j = 0 then 1 else -A 0 j
    else if i = j then A 0 0 else 0

/-- The same projective plane in coordinates adapted to the affine chart. -/
def chartFrame {R : Type*} [CommRing R]
    (A : Matrix (Fin 4) (Fin 3) R) : Matrix (Fin 4) (Fin 3) R :=
  A * chartChange A

@[simp] theorem map_chartChange {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A : Matrix (Fin 4) (Fin 3) R) :
    (chartChange A).map f = chartChange (A.map f) := by
  ext i j
  simp only [Matrix.map_apply, chartChange]
  split_ifs <;> simp_all

@[simp] theorem map_chartFrame {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A : Matrix (Fin 4) (Fin 3) R) :
    (chartFrame A).map f = chartFrame (A.map f) := by
  rw [chartFrame, Matrix.map_mul, map_chartChange]
  rfl

@[simp] theorem chartChange_det {R : Type*} [CommRing R]
    (A : Matrix (Fin 4) (Fin 3) R) :
    (chartChange A).det = (A 0 0) ^ 2 := by
  rw [Matrix.det_fin_three]
  simp [chartChange]
  ring

@[simp] theorem chartFrame_zero_zero {R : Type*} [CommRing R]
    (A : Matrix (Fin 4) (Fin 3) R) : chartFrame A 0 0 = A 0 0 := by
  simp [chartFrame, Matrix.mul_apply, chartChange, Fin.sum_univ_succ]

@[simp] theorem chartFrame_zero_one {R : Type*} [CommRing R]
    (A : Matrix (Fin 4) (Fin 3) R) : chartFrame A 0 1 = 0 := by
  simp [chartFrame, Matrix.mul_apply, chartChange, Fin.sum_univ_succ]
  ring

@[simp] theorem chartFrame_zero_two {R : Type*} [CommRing R]
    (A : Matrix (Fin 4) (Fin 3) R) : chartFrame A 0 2 = 0 := by
  simp [chartFrame, Matrix.mul_apply, chartChange, Fin.sum_univ_succ]
  ring

theorem chartChange_injective {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 3) K) (ha : A 0 0 ≠ 0) :
    Function.Injective (chartChange A).mulVec := by
  apply Matrix.mulVec_injective_iff_isUnit.mpr
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [chartChange_det]
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero 2 ha)

theorem chartFrame_injective {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 3) K) (hA : Function.Injective A.mulVec)
    (ha : A 0 0 ≠ 0) : Function.Injective (chartFrame A).mulVec := by
  intro x y hxy
  apply chartChange_injective A ha
  apply hA
  simpa only [chartFrame, Matrix.mulVec_mulVec] using hxy

theorem chartFrame_range {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 3) K) (ha : A 0 0 ≠ 0) :
    LinearMap.range (chartFrame A).mulVecLin = LinearMap.range A.mulVecLin := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    refine ⟨(chartChange A).mulVec x, ?_⟩
    change A.mulVec ((chartChange A).mulVec x) = (chartFrame A).mulVec x
    rw [chartFrame, Matrix.mulVec_mulVec]
  · rintro _ ⟨x, rfl⟩
    have hs : Function.Surjective (chartChange A).mulVec :=
      Matrix.mulVec_surjective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr
          (isUnit_iff_ne_zero.mpr (by simp [ha])))
    obtain ⟨y, hy⟩ := hs x
    refine ⟨y, ?_⟩
    change (chartFrame A).mulVec y = A.mulVec x
    rw [chartFrame, ← Matrix.mulVec_mulVec, hy]

theorem chartFrame_domain {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 3) K) (hA : Function.Injective A.mulVec)
    (ha : A 0 0 ≠ 0) (F : MvPolynomial (Fin 4) K)
    (hdegree : 2 ≤ (restrict A F).totalDegree)
    (hdom : IsDomain (MvPolynomial (Fin 3) (AlgebraicClosure K) ⧸
      Ideal.span {map (algebraMap K (AlgebraicClosure K)) (restrict A F)})) :
    IsDomain (MvPolynomial (Fin 3) (AlgebraicClosure K) ⧸
      Ideal.span {map (algebraMap K (AlgebraicClosure K))
        (restrict (chartFrame A) F)}) := by
  let L := AlgebraicClosure K
  let Abar : Matrix (Fin 4) (Fin 3) L := A.map (algebraMap K L)
  let Cbar : Matrix (Fin 4) (Fin 3) L := (chartFrame A).map (algebraMap K L)
  have ha' : (Abar 0 0) ≠ 0 := by
    exact (map_ne_zero (algebraMap K L)).mpr ha
  have hAbar : Function.Injective Abar.mulVec := by
    exact ReducedVertexBaseChange.map_frame_injective A hA
  have hCbar : Function.Injective Cbar.mulVec := by
    have he : Cbar = chartFrame Abar := by
      exact map_chartFrame (algebraMap K L) A
    rw [he]
    exact chartFrame_injective Abar hAbar ha'
  have hrange : LinearMap.range Cbar.mulVecLin =
      LinearMap.range Abar.mulVecLin := by
    have he : Cbar = chartFrame Abar := by
      exact map_chartFrame (algebraMap K L) A
    rw [he]
    exact chartFrame_range Abar ha'
  have hmapA : map (algebraMap K L) (restrict A F) =
      restrict Abar (map (algebraMap K L) F) := by
    exact map_restrict (algebraMap K L) A F
  have hmapC : map (algebraMap K L) (restrict (chartFrame A) F) =
      restrict Cbar (map (algebraMap K L) F) := by
    exact map_restrict (algebraMap K L) (chartFrame A) F
  have hAne : map (algebraMap K L) (restrict A F) ≠ 0 := by
    intro hz
    have hz0 : restrict A F = 0 :=
      (map_injective _ (algebraMap K L).injective) (by simpa using hz)
    rw [hz0, totalDegree_zero] at hdegree
    omega
  have hprime := (Ideal.Quotient.isDomain_iff_prime _).mp hdom
  have hirrA : Irreducible (restrict Abar (map (algebraMap K L) F)) := by
    rw [← hmapA]
    exact ((Ideal.span_singleton_prime hAne).mp hprime).irreducible
  have hirrC : Irreducible (restrict Cbar (map (algebraMap K L) F)) :=
    irreducible_of_same_range Cbar Abar hCbar hAbar hrange _ hirrA
  apply (Ideal.Quotient.isDomain_iff_prime _).mpr
  rw [hmapC]
  exact (Ideal.span_singleton_prime hirrC.ne_zero).mpr hirrC.prime

/-- The two spatial direction columns of a chart-adapted projective frame. -/
def spatialDirections {R : Type*} [CommRing R]
    (C : Matrix (Fin 4) (Fin 3) R) : Matrix (Fin 3) (Fin 2) R :=
  fun i j => C i.succ j.succ

/-- Insert a zero zeroth coordinate before two plane coordinates. -/
def directionLift {R : Type*} [Zero R] (x : Fin 2 → R) : Fin 3 → R :=
  Fin.cases 0 x

theorem mulVec_directionLift {K : Type*} [Field K]
    (C : Matrix (Fin 4) (Fin 3) K) (hC1 : C 0 1 = 0) (hC2 : C 0 2 = 0)
    (x : Fin 2 → K) :
    C.mulVec (directionLift x) =
      Fin.cases 0 ((spatialDirections C).mulVec x) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Matrix.mulVec, dotProduct, directionLift,
      Fin.sum_univ_succ, hC1, hC2]
  · simp [Matrix.mulVec, dotProduct, directionLift, spatialDirections,
      Fin.sum_univ_succ]

theorem spatialDirections_injective {K : Type*} [Field K]
    (C : Matrix (Fin 4) (Fin 3) K) (hC : Function.Injective C.mulVec)
    (hC1 : C 0 1 = 0) (hC2 : C 0 2 = 0) :
    Function.Injective (spatialDirections C).mulVec := by
  intro x y hxy
  have hlift : directionLift x = directionLift y := by
    apply hC
    rw [mulVec_directionLift C hC1 hC2, mulVec_directionLift C hC1 hC2, hxy]
  funext i
  exact congrFun hlift i.succ

/-- The integral third direction is the cross product of the two fixed
spatial directions. -/
def pencilDirection (C : Matrix (Fin 4) (Fin 3) ℤ) : Fin 3 → ℤ :=
  (fun i => spatialDirections C i 0) ⨯₃
    (fun i => spatialDirections C i 1)

/-- The three spatial directions of the affine pencil. -/
def spatialPencilMatrix (C : Matrix (Fin 4) (Fin 3) ℤ) :
    Matrix (Fin 3) (Fin 3) ℤ :=
  fun i j => ![spatialDirections C i 0, spatialDirections C i 1,
    pencilDirection C i] j

theorem spatialPencilMatrix_det_ne_zero
    (C : Matrix (Fin 4) (Fin 3) ℤ)
    (hC : Function.Injective (C.map (Int.castRingHom ℚ)).mulVec)
    (hC1 : C 0 1 = 0) (hC2 : C 0 2 = 0) :
    (spatialPencilMatrix C).det ≠ 0 := by
  have hC1q : (C.map (Int.castRingHom ℚ)) 0 1 = 0 := by simp [hC1]
  have hC2q : (C.map (Int.castRingHom ℚ)) 0 2 = 0 := by simp [hC2]
  have hdir := spatialDirections_injective (C.map (Int.castRingHom ℚ)) hC hC1q hC2q
  have hlin : LinearIndependent ℚ
      ![(fun i => ((spatialDirections C i 0 : ℤ) : ℚ)),
        (fun i => ((spatialDirections C i 1 : ℤ) : ℚ))] := by
    have hh := Matrix.mulVec_injective_iff.mp hdir
    have he : (spatialDirections (C.map (Int.castRingHom ℚ))).col =
        ![(fun i => ((spatialDirections C i 0 : ℤ) : ℚ)),
          (fun i => ((spatialDirections C i 1 : ℤ) : ℚ))] := by
      ext i j
      fin_cases i <;> simp [spatialDirections]
    exact he ▸ hh
  have hcross : ((fun i => ((spatialDirections C i 0 : ℤ) : ℚ)) ⨯₃
      (fun i => ((spatialDirections C i 1 : ℤ) : ℚ))) ≠ 0 :=
    (crossProduct_ne_zero_iff_linearIndependent.mpr hlin)
  intro hdet
  let u : Fin 3 → ℚ := fun i => ((spatialDirections C i 0 : ℤ) : ℚ)
  let v : Fin 3 → ℚ := fun i => ((spatialDirections C i 1 : ℤ) : ℚ)
  let w : Fin 3 → ℚ := u ⨯₃ v
  have hw : w ≠ 0 := by simpa only [u, v, w] using hcross
  let U : Matrix (Fin 3) (Fin 3) ℚ := fun i j => ![u i, v i, w i] j
  have hUmap : (spatialPencilMatrix C).map (Int.castRingHom ℚ) = U := by
    ext i j
    fin_cases j <;> fin_cases i <;>
      simp [spatialPencilMatrix, pencilDirection, U, u, v, w,
        cross_apply, spatialDirections] <;> ring
  have hUdet : U.det = 0 := by
    rw [← hUmap]
    calc
      ((spatialPencilMatrix C).map (Int.castRingHom ℚ)).det =
          (Int.castRingHom ℚ) (spatialPencilMatrix C).det := by
            simpa using ((Int.castRingHom ℚ).map_det
              (spatialPencilMatrix C)).symm
      _ = 0 := by rw [hdet, map_zero]
  have hUt : U.transpose = ![u, v, w] := by
    ext i j
    fin_cases i <;> simp [U]
  have htriple : u ⬝ᵥ v ⨯₃ w = 0 := by
    rw [triple_product_eq_det, ← hUt, Matrix.det_transpose, hUdet]
  have hself : w ⬝ᵥ w = 0 := by
    calc
      w ⬝ᵥ w = w ⬝ᵥ u ⨯₃ v := by rfl
      _ = u ⬝ᵥ v ⨯₃ w := triple_product_permutation w u v
      _ = 0 := htriple
  exact hw (dotProduct_self_eq_zero.mp hself)

/-- The projective plane in the pencil at parameter `t`.  Only its first
column moves; at `t = 0` it is the fixed chart-adapted Bertini frame. -/
def pencilFrame {K : Type*} [CommRing K]
    (C : Matrix (Fin 4) (Fin 3) ℤ) (t : K) : Matrix (Fin 4) (Fin 3) K :=
  fun i j => Fin.cases
    ((C 0 j : K))
    (fun r => if j = 0 then (C r.succ 0 : K) + t * (pencilDirection C r : K)
      else (C r.succ j : K)) i

@[simp] theorem pencilFrame_zero {K : Type*} [CommRing K]
    (C : Matrix (Fin 4) (Fin 3) ℤ) :
    pencilFrame C (0 : K) = C.map (Int.castRingHom K) := by
  ext i j
  refine Fin.cases ?_ (fun r => ?_) i
  · simp [pencilFrame]
  · by_cases hj : j = 0
    · subst j
      simp [pencilFrame]
    · simp [pencilFrame, hj]

/-- The plane frame at every parameter is injective whenever the fixed
affine spatial change of coordinates remains invertible. -/
theorem pencilFrame_injective
    {K : Type*} [Field K]
    (C : Matrix (Fin 4) (Fin 3) ℤ)
    (hC00 : (C 0 0 : K) ≠ 0) (hC01 : C 0 1 = 0) (hC02 : C 0 2 = 0)
    (hdet : ((spatialPencilMatrix C).det : K) ≠ 0) (t : K) :
    Function.Injective (pencilFrame C t).mulVec := by
  let U : Matrix (Fin 3) (Fin 3) K :=
    (spatialPencilMatrix C).map (Int.castRingHom K)
  have hUdet : U.det ≠ 0 := by
    have hm := (Int.castRingHom K).map_det (spatialPencilMatrix C)
    change (Int.castRingHom K) (spatialPencilMatrix C).det = U.det at hm
    exact fun hz => hdet (hm.trans hz)
  have hU : Function.Injective U.mulVec := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr
    exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hUdet)
  intro x y hxy
  let z : Fin 3 → K := x - y
  have hz : (pencilFrame C t).mulVec z = 0 := by
    dsimp only [z]
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have hz0 : z 0 = 0 := by
    have h := congrFun hz 0
    simp [pencilFrame, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      hC01, hC02] at h
    exact h.resolve_left hC00
  let q : Fin 3 → K := ![z 1, z 2, 0]
  have hq : U.mulVec q = 0 := by
    ext r
    have hr := congrFun hz r.succ
    fin_cases r <;> simpa [U, q, spatialPencilMatrix, spatialDirections, pencilDirection,
        pencilFrame, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
        cross_apply, hz0, Fin.cases_succ] using hr
  have hq0 : q = 0 := hU (by simpa using hq)
  have hz1 : z 1 = 0 := congrFun hq0 0
  have hz2 : z 2 = 0 := congrFun hq0 1
  have hzero : z = 0 := by
    funext i
    fin_cases i <;> assumption
  exact sub_eq_zero.mp hzero

/-- The same pencil as one literal homogeneous polynomial family over
`Z[T]`. -/
def projectivePencilFrame (C : Matrix (Fin 4) (Fin 3) ℤ) :
    Matrix (Fin 4) (Fin 3) (MvPolynomial (Fin 1) ℤ) :=
  fun i j => Fin.cases
    (MvPolynomial.C (C 0 j))
    (fun r => if j = 0 then MvPolynomial.C (C r.succ 0) +
        X 0 * MvPolynomial.C (pencilDirection C r)
      else MvPolynomial.C (C r.succ j)) i

def projectivePencilPolynomial
    (F : MvPolynomial (Fin 4) ℤ) (C : Matrix (Fin 4) (Fin 3) ℤ) :
    MvPolynomial (Fin 3) (MvPolynomial (Fin 1) ℤ) :=
  restrict (projectivePencilFrame C) (map MvPolynomial.C F)

theorem projectivePencilPolynomial_homogeneous
    {d : ℕ} (F : MvPolynomial (Fin 4) ℤ) (hF : F.IsHomogeneous d)
    (C : Matrix (Fin 4) (Fin 3) ℤ) :
    (projectivePencilPolynomial F C).IsHomogeneous d :=
  homogeneous_restrict _ _ (hF.map MvPolynomial.C)

theorem eval_projectivePencilFrame
    {K : Type*} [CommRing K] (C : Matrix (Fin 4) (Fin 3) ℤ)
    (t : K) :
    (projectivePencilFrame C).map
      (eval₂Hom (Int.castRingHom K) (fun _ : Fin 1 => t)) =
      pencilFrame C t := by
  ext i j
  refine Fin.cases ?_ (fun r => ?_) i
  · change eval₂ (Int.castRingHom K) (fun _ : Fin 1 => t)
      (MvPolynomial.C (C 0 j)) = (C 0 j : K)
    exact eval₂_C _ _ _
  · by_cases hj : j = 0
    · subst j
      change eval₂ (Int.castRingHom K) (fun _ : Fin 1 => t)
        (MvPolynomial.C (C r.succ 0) + X 0 *
          MvPolynomial.C (pencilDirection C r)) =
        (C r.succ 0 : K) + t * (pencilDirection C r : K)
      simp only [eval₂_add, eval₂_C, eval₂_mul, eval₂_X]
      rfl
    · simp only [Matrix.map_apply, projectivePencilFrame, pencilFrame,
        Fin.cases_succ, hj, if_false]
      change eval₂ (Int.castRingHom K) (fun _ : Fin 1 => t)
        (MvPolynomial.C (C r.succ j)) = (C r.succ j : K)
      exact eval₂_C _ _ _

theorem specialize_projectivePencilPolynomial
    {K : Type*} [CommRing K]
    (F : MvPolynomial (Fin 4) ℤ) (C : Matrix (Fin 4) (Fin 3) ℤ)
    (t : K) :
    map (eval₂Hom (Int.castRingHom K) (fun _ : Fin 1 => t))
        (projectivePencilPolynomial F C) =
      restrict (pencilFrame C t) (map (Int.castRingHom K) F) := by
  rw [projectivePencilPolynomial, map_restrict,
    eval_projectivePencilFrame, MvPolynomial.map_map]
  have hc : (eval₂Hom (Int.castRingHom K) (fun _ : Fin 1 => t)).comp
      (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 1) ℤ) = Int.castRingHom K := by
    ext a
    exact eval₂Hom_C _ _ _
  rw [hc]

/-- A fixed absolutely integral projective surface admits one actual integral
parallel pencil.  One nonzero integer controls both the affine-coordinate
determinant and a nonzero exceptional parameter polynomial.  Outside the
zeros of that polynomial, the literal projective plane equation has degree
`d` and geometrically integral principal quotient.

The only standard AG input is `HomogeneousHypersurfaceIntegralityOpen`;
Bertini and all coordinate constructions used here are proved in the
imported modules. -/
theorem exists_fixed_integral_surface_pencil_certificate
    (integralityOpen : HomogeneousHypersurfaceIntegralityOpen)
    {d : ℕ} (hd : 2 ≤ d)
    (F : MvPolynomial (Fin 4) ℤ) (hF0 : F ≠ 0)
    (hF : F.IsHomogeneous d)
    (hgeom : IsDomain (MvPolynomial (Fin 4) GeometricField ⧸
      Ideal.span {map (Int.castRingHom GeometricField) F})) :
    ∃ (C : Matrix (Fin 4) (Fin 3) ℤ) (N : ℤ)
        (g : MvPolynomial (Fin 1) ℤ),
      C 0 0 ≠ 0 ∧ C 0 1 = 0 ∧ C 0 2 = 0 ∧
      eval (fun _ : Fin 1 => (0 : ℤ)) g ≠ 0 ∧ N ≠ 0 ∧
      ∀ (K : Type) [Field K], (N : K) ≠ 0 →
        (C 0 0 : K) ≠ 0 ∧
        ((spatialPencilMatrix C).det : K) ≠ 0 ∧
        (map (Int.castRingHom K) F).totalDegree = d ∧
        IsDomain (MvPolynomial (Fin 4) (AlgebraicClosure K) ⧸
          Ideal.span {map (algebraMap K (AlgebraicClosure K))
            (map (Int.castRingHom K) F)}) ∧
        map (Int.castRingHom K) g ≠ 0 ∧
        ∀ t : K, eval (fun _ : Fin 1 => t) (map (Int.castRingHom K) g) ≠ 0 →
          (restrict (pencilFrame C t) (map (Int.castRingHom K) F)).IsHomogeneous d ∧
          (restrict (pencilFrame C t)
            (map (Int.castRingHom K) F)).totalDegree = d ∧
          IsDomain (MvPolynomial (Fin 3) (AlgebraicClosure K) ⧸
            Ideal.span {map (algebraMap K (AlgebraicClosure K))
              (restrict (pencilFrame C t) (map (Int.castRingHom K) F))}) := by
  obtain ⟨A, N₀, hA00, hN₀, hgood⟩ :=
    FixedIntegralSurfaceSection.exists_fixed_integral_surface_section
      integralityOpen hd F hF0 hF hgeom
  let C₀ : Matrix (Fin 4) (Fin 3) ℤ := chartFrame A
  have hC00 : C₀ 0 0 ≠ 0 := by simpa [C₀] using hA00
  have hC01 : C₀ 0 1 = 0 := by simp [C₀]
  have hC02 : C₀ 0 2 = 0 := by simp [C₀]
  have hNQ : (N₀ : ℚ) ≠ 0 := by exact_mod_cast hN₀
  obtain ⟨hA00Q, hAQ, _hhomAQ, hdegAQ, hdomAQ⟩ := hgood ℚ hNQ
  let AQ : Matrix (Fin 4) (Fin 3) ℚ := A.map (Int.castRingHom ℚ)
  let FQ : MvPolynomial (Fin 4) ℚ := map (Int.castRingHom ℚ) F
  have hrestrictAQ : restrict AQ FQ =
      map (Int.castRingHom ℚ) (restrict A F) := by
    exact (map_restrict (Int.castRingHom ℚ) A F).symm
  have hCdomQ : IsDomain (MvPolynomial (Fin 3) (AlgebraicClosure ℚ) ⧸
      Ideal.span {map (algebraMap ℚ (AlgebraicClosure ℚ))
        (restrict (chartFrame AQ) FQ)}) := by
    apply chartFrame_domain AQ hAQ hA00Q FQ
    · rw [hrestrictAQ]
      exact hd.trans_eq hdegAQ.symm
    · rw [hrestrictAQ]
      exact hdomAQ
  have hCQ : Function.Injective (C₀.map (Int.castRingHom ℚ)).mulVec := by
    have he : C₀.map (Int.castRingHom ℚ) = chartFrame AQ := by
      simpa [C₀, AQ] using map_chartFrame (Int.castRingHom ℚ) A
    rw [he]
    exact chartFrame_injective AQ hAQ hA00Q
  have hdet : (spatialPencilMatrix C₀).det ≠ 0 :=
    spatialPencilMatrix_det_ne_zero C₀ hCQ hC01 hC02
  obtain ⟨sF, hsFgeom, hsFopen⟩ := integralityOpen
    ℤ GeometricField 4 d (by omega) (Int.castRingHom GeometricField)
    F hF (by
      intro hz
      exact hF0 ((map_injective (Int.castRingHom GeometricField)
        Int.cast_injective) (by simpa only [map_zero] using hz))) hgeom
  have hsF : sF ≠ 0 := by
    intro hs
    exact hsFgeom (by rw [hs, map_zero])
  let Ω := AlgebraicClosure ℚ
  let ρ : MvPolynomial (Fin 1) ℤ →+* Ω :=
    eval₂Hom (Int.castRingHom Ω) (fun _ => 0)
  let P := projectivePencilPolynomial F C₀
  have hP : P.IsHomogeneous d :=
    projectivePencilPolynomial_homogeneous F hF C₀
  have hPspecialized : map ρ P =
      map (algebraMap ℚ Ω) (restrict (chartFrame AQ) FQ) := by
    have hs := specialize_projectivePencilPolynomial F C₀ (0 : Ω)
    have hmapC : C₀.map (Int.castRingHom Ω) =
        (chartFrame AQ).map (algebraMap ℚ Ω) := by
      calc
        C₀.map (Int.castRingHom Ω) =
            chartFrame (A.map (Int.castRingHom Ω)) := by
              simpa [C₀] using map_chartFrame (Int.castRingHom Ω) A
        _ = chartFrame (AQ.map (algebraMap ℚ Ω)) := by
              congr 1
        _ = (chartFrame AQ).map (algebraMap ℚ Ω) := by
              exact (map_chartFrame (algebraMap ℚ Ω) AQ).symm
    have hmapF : map (Int.castRingHom Ω) F =
        map (algebraMap ℚ Ω) FQ := by
      dsimp only [FQ]
      rw [MvPolynomial.map_map]
      exact congrArg (fun f : ℤ →+* Ω => map f F) (RingHom.ext_int _ _)
    rw [show map ρ P = restrict (pencilFrame C₀ (0 : Ω))
        (map (Int.castRingHom Ω) F) by simpa [ρ, P] using hs]
    rw [pencilFrame_zero, hmapC, hmapF]
    rw [← map_restrict]
  have hCneQ : restrict (chartFrame AQ) FQ ≠ 0 := by
    intro hz
    have hs : Function.Surjective (chartChange AQ).mulVec :=
      Matrix.mulVec_surjective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr
          (isUnit_iff_ne_zero.mpr (by
            rw [chartChange_det]
            exact pow_ne_zero 2 hA00Q)))
    have hAzero : restrict AQ FQ = 0 := by
      apply MvPolynomial.funext
      intro x
      obtain ⟨y, hy⟩ := hs x
      have heval := congrArg (MvPolynomial.eval y) hz
      rw [eval_restrict, map_zero] at heval
      rw [eval_restrict, map_zero]
      simpa only [chartFrame, ← Matrix.mulVec_mulVec, hy] using heval
    rw [hrestrictAQ] at hAzero
    rw [hAzero, totalDegree_zero] at hdegAQ
    omega
  have hPne : map ρ P ≠ 0 := by
    rw [hPspecialized]
    exact fun hz => hCneQ ((map_injective (algebraMap ℚ Ω)
      (algebraMap ℚ Ω).injective) (by simpa only [map_zero] using hz))
  have hPdom : IsDomain (MvPolynomial (Fin 3) Ω ⧸
      Ideal.span {map ρ P}) := by
    rw [hPspecialized]
    exact hCdomQ
  obtain ⟨g, hgρ, hgopen⟩ := integralityOpen
    (MvPolynomial (Fin 1) ℤ) Ω 3 d (by omega) ρ P hP hPne hPdom
  have hg0 : eval (fun _ : Fin 1 => (0 : ℤ)) g ≠ 0 := by
    intro hz
    apply hgρ
    change eval₂ (Int.castRingHom Ω) (fun _ : Fin 1 => 0) g = 0
    rw [eval₂_eq_eval_map]
    have hm := map_eval (Int.castRingHom Ω) (fun _ : Fin 1 => (0 : ℤ)) g
    have hzero : (Int.castRingHom Ω) ∘ (fun _ : Fin 1 => (0 : ℤ)) =
        (fun _ : Fin 1 => (0 : Ω)) := by funext i; simp
    rw [hzero] at hm
    simpa only [hz, map_zero] using hm.symm
  let N : ℤ := N₀ * (spatialPencilMatrix C₀).det *
    eval (fun _ : Fin 1 => (0 : ℤ)) g * sF
  have hN : N ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hN₀ hdet) hg0) hsF
  refine ⟨C₀, N, g, hC00, hC01, hC02, hg0, hN, ?_⟩
  intro K _ hNK
  have hprod : ((N₀ : K) * ((spatialPencilMatrix C₀).det : K) *
      ((eval (fun _ : Fin 1 => (0 : ℤ)) g : ℤ) : K)) * (sF : K) ≠ 0 := by
    simpa [N, Int.cast_mul] using hNK
  have hsplit := mul_ne_zero_iff.mp hprod
  have hsplit' := mul_ne_zero_iff.mp hsplit.1
  have hsplit'' := mul_ne_zero_iff.mp hsplit'.1
  have hN₀K : (N₀ : K) ≠ 0 := hsplit''.1
  have hdetK : ((spatialPencilMatrix C₀).det : K) ≠ 0 := hsplit''.2
  have hg0K : ((eval (fun _ : Fin 1 => (0 : ℤ)) g : ℤ) : K) ≠ 0 := hsplit'.2
  have hsFK : (sF : K) ≠ 0 := hsplit.2
  obtain ⟨hA00K, _hAK, _hhomAK, _hdegAK, _hdomAK⟩ := hgood K hN₀K
  have hgK : map (Int.castRingHom K) g ≠ 0 := by
    intro hz
    apply hg0K
    have hm := map_eval (Int.castRingHom K) (fun _ : Fin 1 => (0 : ℤ)) g
    have hzero : (Int.castRingHom K) ∘ (fun _ : Fin 1 => (0 : ℤ)) =
        (fun _ : Fin 1 => (0 : K)) := by funext i; simp
    rw [hzero, hz] at hm
    simpa only [map_zero] using hm
  have hambK := hsFopen K (Int.castRingHom K) hsFK
  refine ⟨?_, hdetK, hambK.1, hambK.2, hgK, ?_⟩
  · simpa [C₀] using hA00K
  · intro t hgt
    let τ : MvPolynomial (Fin 1) ℤ →+* K :=
      eval₂Hom (Int.castRingHom K) (fun _ => t)
    have hτg : τ g ≠ 0 := by
      change eval₂ (Int.castRingHom K) (fun _ : Fin 1 => t) g ≠ 0
      rw [eval₂_eq_eval_map]
      exact hgt
    have hopen := hgopen K τ hτg
    have hs := specialize_projectivePencilPolynomial F C₀ t
    have heq : map τ P =
        restrict (pencilFrame C₀ t) (map (Int.castRingHom K) F) := by
      simpa [τ, P] using hs
    rw [heq] at hopen
    exact ⟨homogeneous_restrict _ _ (hF.map _), hopen⟩

end CubicTenVariables.FixedIntegralSurfacePencil

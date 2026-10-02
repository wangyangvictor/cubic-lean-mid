import CubicTenVariables.Literature.BoundedDegreeAffinePointCount
import CubicTenVariables.IntegralGeometricFiberDepth
import CubicTenVariables.BihomogeneousIncidenceFamily

/-! The generic bounded-degree affine estimate specializes to the literal
fibers of one fixed integral polynomial family. Specialization cannot
increase the outer degree, and its geometric equation ideal is exactly
the existing geometric-fiber ideal. Constants precede all fields, parameters
and dimension thresholds. Homogeneity and good-prime assumptions are not
needed; the only literature premise is the displayed general point bound. -/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace CubicTenVariables.FixedFamilyFiberPointCount
open MvPolynomial Literature BihomogeneousIncidenceFamily
open scoped BigOperators Classical

/-- A positive degree cap depending only on the original equations. -/
def degreeBound {m n t : ℕ} (f : Fin t → Polynomial m n) : ℕ :=
  1 + ∑ i, (f i).totalDegree

theorem degreeBound_pos {m n t : ℕ} (f : Fin t → Polynomial m n) :
    1 ≤ degreeBound f := by unfold degreeBound; omega

/-- This cap is valid for every coefficient specialization, including
specializations in which an equation becomes zero or constant. -/
theorem specialized_degree_le {m n t : ℕ} (f : Fin t → Polynomial m n)
    (K : Type*) [CommRing K] (v : Fin m → K) (i : Fin t) :
    (map (eval₂Hom (Int.castRingHom K) v) (f i)).totalDegree ≤ degreeBound f := by
  classical
  have hm : (map (eval₂Hom (Int.castRingHom K) v) (f i)).totalDegree ≤
      (f i).totalDegree := Finset.sup_mono (support_map_subset _ _)
  have hs : (f i).totalDegree ≤ ∑ a, (f a).totalDegree :=
    Finset.single_le_sum (fun a _ => Nat.zero_le (f a).totalDegree) (Finset.mem_univ i)
  dsimp [degreeBound]
  omega

/-- Specialize first and then extend the field, or specialize directly
over the algebraic closure: the literal quotient dimensions agree. -/
theorem geometric_dimension_specialize {m n t : ℕ} (f : Fin t → Polynomial m n)
    (K : Type*) [Field K] (v : Fin m → K) :
    geometricEquationDimension (fun i => map (eval₂Hom (Int.castRingHom K) v) (f i)) =
      IntegralGeometricFiberDepth.geometricFiberDimension f K v := by
  have hc : (algebraMap K (AlgebraicClosure K)).comp (Int.castRingHom K) =
      Int.castRingHom (AlgebraicClosure K) := RingHom.ext_int _ _
  have hf : (fun i => map (algebraMap K (AlgebraicClosure K))
      (map (eval₂Hom (Int.castRingHom K) v) (f i))) =
      (fun i => map (eval₂Hom (Int.castRingHom (AlgebraicClosure K))
        (fun a => algebraMap K (AlgebraicClosure K) (v a))) (f i)) := by
    funext i
    rw [MvPolynomial.map_map,MvPolynomial.comp_eval₂Hom,hc]
  change ringKrullDim (_ ⧸ Ideal.span (Set.range _)) =
    ringKrullDim (_ ⧸ Ideal.span (Set.range _))
  rw [hf]

/-- Uniform bound for the actual nested-equation fibers. No dimension or
counting assertion about the fixed family is assumed: only the dimension
of the particular specialized geometric fiber bounds its exponent. -/
theorem exists_bound (lit : BoundedDegreeAffinePointCount) {m n t : ℕ}
    (f : Fin t → Polynomial m n) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (K : Type) [Field K] [Fintype K]
      (v : Fin m → K) (j : ℕ),
      IntegralGeometricFiberDepth.geometricFiberDimension f K v ≤ (j : WithBot ℕ∞) →
      Nat.card {x : Fin n → K // ∀ i, value (f i) v x = 0} ≤ C * (Fintype.card K)^j := by
  obtain ⟨C,hC,hbound⟩ := lit n t (degreeBound f) (degreeBound_pos f)
  refine ⟨C,hC,?_⟩
  intro K _ _ v j hdim
  have hd : geometricEquationDimension (fun i => map (eval₂Hom (Int.castRingHom K) v) (f i)) ≤
      (j : WithBot ℕ∞) := by
    rw [geometric_dimension_specialize]
    exact hdim
  simpa only [value,eval_map] using hbound K
    (fun i => map (eval₂Hom (Int.castRingHom K) v) (f i))
    (specialized_degree_le f K v) j hd

/-- The same estimate for the actual set-valued incidence fiber, which is
the representation used by the microlocal geometry. -/
theorem exists_fiber_bound (lit : BoundedDegreeAffinePointCount) {m n t : ℕ}
    (f : Fin t → Polynomial m n) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (K : Type) [Field K] [Fintype K]
      (v : Fin m → K) (j : ℕ),
      IntegralGeometricFiberDepth.geometricFiberDimension f K v ≤ (j : WithBot ℕ∞) →
      Nat.card (fiber f K v) ≤ C * (Fintype.card K)^j :=
  exists_bound lit f

/-- Finite-set form of the same count, without any unspecified model. -/
theorem exists_filter_bound (lit : BoundedDegreeAffinePointCount) {m n t : ℕ}
    (f : Fin t → Polynomial m n) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (K : Type) [Field K] [Fintype K]
      (v : Fin m → K) (j : ℕ),
      IntegralGeometricFiberDepth.geometricFiberDimension f K v ≤ (j : WithBot ℕ∞) →
      (Finset.univ.filter (fun x : Fin n → K => ∀ i, value (f i) v x = 0)).card ≤
        C * (Fintype.card K)^j := by
  classical
  obtain ⟨C,hC,hbound⟩ := exists_bound lit f
  refine ⟨C,hC,?_⟩
  intro K _ _ v j hdim
  simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype] using hbound K v j hdim

end CubicTenVariables.FixedFamilyFiberPointCount

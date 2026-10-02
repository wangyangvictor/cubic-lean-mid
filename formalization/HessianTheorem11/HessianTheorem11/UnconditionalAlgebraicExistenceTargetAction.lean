import HessianTheorem11.UnconditionalAlgebraicExistenceTarget
import HessianTheorem11.UnconditionalAlgebraicExistenceForms

/-! The finite coefficient action is an actual polynomial family.
Consequently closed invariant homogeneous targets remain invariant over
arbitrary extension fields, by the proved polynomial-implication theorem. -/
noncomputable section
namespace HessianTheorem11.UnconditionalAlgebraicExistence
open MvPolynomial PolynomialRestriction ReducedRelative UnconditionalOrbitIdeal
variable {K E : Type*} [Field K] [IsAlgClosed K] [Field E] [Algebra K E] {n : ℕ}

def coefficientActionTuple (d : ℕ) :
    DegreeIndex n d → MvPolynomial ((Fin n × Fin n) ⊕ DegreeIndex n d) K :=
  fun e => ∑ m : DegreeIndex n d,
    rename Sum.inl (restrictionCoefficient (monomial m.val (1 : K)) e.val) * X (Sum.inr m)

theorem actionValue_coefficientActionTuple (d : ℕ)
    (A : Matrix (Fin n) (Fin n) E) (x : DegreeIndex n d → E) :
    actionValue (coefficientActionTuple (K := K) d) (matrixPoint A) x =
      (finiteCoefficientMatrix (d := d) A).mulVec x := by
  classical
  ext e
  simp only [actionValue,coefficientActionTuple,map_sum,map_mul,aeval_rename,aeval_X,
    Sum.elim_inr,Sum.elim_comp_inl,aeval_restrictionCoefficient,map_monomial,map_one]
  rfl

theorem actionValue_coefficientVector (d : ℕ)
    (A : Matrix (Fin n) (Fin n) E) (H : MvPolynomial (Fin n) E)
    (hH : H.IsHomogeneous d) :
    actionValue (coefficientActionTuple (K := K) d) (matrixPoint A) (coefficientVector H) =
      coefficientVector (d := d) (restrict A H) := by
  rw [actionValue_coefficientActionTuple,coefficientVector_restrict A H hH]

def specialLinearParameterIdeal : Ideal (MvPolynomial (Fin n × Fin n) K) :=
  Ideal.span {matrixDetPolynomial - 1}

theorem matrixPoint_mem_specialLinearParameter (A : Matrix (Fin n) (Fin n) E)
    (hA : A.det = 1) :
    matrixPoint A ∈ zeroLocus E (specialLinearParameterIdeal (K := K)) := by
  simp only [specialLinearParameterIdeal,zeroLocus_span,Set.mem_singleton_iff,
    forall_eq,Set.mem_setOf_eq,map_sub,aeval_matrixDetPolynomial,map_one,hA,sub_self]

theorem det_eq_one_of_specialLinearParameter (u : (Fin n × Fin n) → E)
    (hu : u ∈ zeroLocus E (specialLinearParameterIdeal (K := K))) :
    Matrix.det (fun i j : Fin n => u (i,j)) = 1 := by
  let A : Matrix (Fin n) (Fin n) E := fun i j => u (i,j)
  have he : matrixPoint A = u := by ext ⟨i,j⟩; rfl
  have h := hu (matrixDetPolynomial - 1) (Ideal.subset_span (Set.mem_singleton _))
  change aeval u (matrixDetPolynomial - 1) = 0 at h
  rw [← he,map_sub,aeval_matrixDetPolynomial,map_one,sub_eq_zero] at h
  exact h

/-- Literal invariance of the extended target, for arbitrary extension
fields, follows from base-field closedness and pointwise SL invariance. -/
theorem extendedTarget_slInvariant (d : ℕ) (S : Set (MvPolynomial (Fin n) K))
    (hclosed : coefficientClosed S) (hhom : ∀ H ∈ S, H.IsHomogeneous d)
    (hinv : slInvariant S) : slInvariant (extendedTarget (E := E) d S) := by
  classical
  let I := vanishingIdeal K (finiteTarget (d := d) S)
  let J := specialLinearParameterIdeal (K := K) (n := n)
  let P := coefficientActionTuple (K := K) (n := n) d
  have hbase : ∀ u ∈ zeroLocus K J, ∀ x ∈ zeroLocus K I,
      actionValue P u x ∈ zeroLocus K I := by
    intro u hu x hx
    let A : Matrix (Fin n) (Fin n) K := fun i j => u (i,j)
    have hAu : matrixPoint A = u := by ext ⟨i,j⟩; rfl
    have hA : A.det = 1 := det_eq_one_of_specialLinearParameter u hu
    change x ∈ zeroLocus K (vanishingIdeal K (finiteTarget (d := d) S)) at hx
    rw [finiteTarget_zeroLocus S hclosed hhom] at hx
    obtain ⟨H,hH,rfl⟩ := hx
    rw [← hAu]
    change actionValue (coefficientActionTuple (K := K) d) (matrixPoint A)
      (coefficientVector H) ∈ zeroLocus K (vanishingIdeal K (finiteTarget (d := d) S))
    rw [actionValue_coefficientVector d A H (hhom H hH),finiteTarget_zeroLocus S hclosed hhom]
    exact ⟨restrict A H,hinv A hA H hH,rfl⟩
  intro A hA H hH
  refine ⟨homogeneous_restrict A H hH.1,?_⟩
  rw [← actionValue_coefficientVector (K := K) d A H hH.1]
  exact invariant_zero_locus_baseChange J I P hbase (matrixPoint A)
    (matrixPoint_mem_specialLinearParameter A hA) (coefficientVector H) hH.2

end HessianTheorem11.UnconditionalAlgebraicExistence

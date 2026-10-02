import HessianTheorem11.UnconditionalOrbitIdeal

/-! A literal finite coefficient representation of homogeneous forms and
of the equations of a closed invariant target. -/
noncomputable section
namespace HessianTheorem11.UnconditionalOrbitIdeal
open MvPolynomial PolynomialRestriction ReducedOrbitCoordinates ReducedRelative
variable {K : Type*} [Field K] {n d : ℕ}

abbrev DegreeIndex (n d : ℕ) := {e : Fin n →₀ ℕ // e ∈ degreeMonomials n d}

def coefficientVector (F : MvPolynomial (Fin n) K) : DegreeIndex n d → K :=
  fun e => coeff e.val F

def decode (x : DegreeIndex n d → K) : MvPolynomial (Fin n) K :=
  ∑ e, monomial e.val (x e)

theorem decode_homogeneous (x : DegreeIndex n d → K) : (decode x).IsHomogeneous d := by
  classical
  apply IsHomogeneous.sum
  intro e _
  apply isHomogeneous_monomial
  exact (Finset.mem_finsuppAntidiag'.mp e.property).1

@[simp] theorem coefficientVector_decode (x : DegreeIndex n d → K) :
    coefficientVector (d := d) (decode x) = x := by
  classical
  funext e
  letI : Nonempty (DegreeIndex n d) := ⟨e⟩
  change coeff e.val (∑ m : DegreeIndex n d, monomial m.val (x m)) = x e
  rw [coeff_sum,Finset.sum_eq_single e]
  · simp
  · intro m _ hme
    have hm : m.val ≠ e.val := fun h => hme (Subtype.ext h)
    simp [coeff_monomial,hm]
  · simp

theorem decode_coefficientVector (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d) :
    decode (coefficientVector (d := d) F) = F := by
  calc
    _ = ∑ e ∈ degreeMonomials n d, monomial e (coeff e F) := by
      exact Finset.sum_attach (degreeMonomials n d) (fun e => monomial e (coeff e F))
    _ = F := (homogeneous_fixed_sum F hF).symm

theorem coeff_zero_outside_degree (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous d) (e : Fin n →₀ ℕ) (he : e ∉ degreeMonomials n d) :
    coeff e F = 0 := by
  by_contra hc
  apply he
  apply Finset.mem_finsuppAntidiag'.mpr
  refine ⟨?_,Finset.subset_univ _⟩
  simpa [Finsupp.weight_apply,smul_eq_mul] using hF hc

def finiteCoefficientMatrix (B : Matrix (Fin n) (Fin n) K) :
    Matrix (DegreeIndex n d) (DegreeIndex n d) K :=
  fun e m => coeff e.val (restrict B (monomial m.val 1))

theorem coefficientVector_restrict (B : Matrix (Fin n) (Fin n) K)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d) :
    coefficientVector (d := d) (restrict B F) =
      (finiteCoefficientMatrix (d := d) B).mulVec (coefficientVector F) := by
  funext e
  have h := eval_coefficientRestriction B F hF e.val
  simp only [coefficientRestriction,map_sum,map_mul,eval_C,eval_X] at h
  change coeff e.val (restrict B F) = _
  rw [← h]
  change (∑ m ∈ degreeMonomials n d,
    coeff e.val (restrict B (monomial m 1)) * coeff m F) =
    ∑ m : DegreeIndex n d, coeff e.val (restrict B (monomial m.val 1)) * coeff m.val F
  exact (Finset.sum_attach _ _).symm

def finiteTarget (S : Set (MvPolynomial (Fin n) K)) : Set (DegreeIndex n d → K) :=
  coefficientVector '' S

theorem finiteTarget_invariant (S : Set (MvPolynomial (Fin n) K))
    (hS : slInvariant S) (hhom : ∀ F ∈ S, F.IsHomogeneous d)
    (B : Matrix (Fin n) (Fin n) K) (hB : B.det = 1) :
    ∀ x ∈ finiteTarget (d := d) S, (finiteCoefficientMatrix B).mulVec x ∈ finiteTarget S := by
  rintro _ ⟨F,hF,rfl⟩
  rw [← coefficientVector_restrict B F (hhom F hF)]
  exact ⟨restrict B F,hS B hB F hF,rfl⟩

def finiteEquation (P : MvPolynomial (Fin n →₀ ℕ) K) : MvPolynomial (DegreeIndex n d) K :=
  aeval (fun e => if he : e ∈ degreeMonomials n d then X ⟨e,he⟩ else 0) P

theorem eval_finiteEquation (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (P : MvPolynomial (Fin n →₀ ℕ) K) :
    eval (coefficientVector (d := d) F) (finiteEquation (d := d) P) =
      eval (fun e => coeff e F) P := by
  change aeval (coefficientVector (d := d) F)
    (aeval (fun e => if he : e ∈ degreeMonomials n d then
      (X ⟨e,he⟩ : MvPolynomial (DegreeIndex n d) K) else 0) P) =
    aeval (fun e => coeff e F) P
  rw [MvPolynomial.comp_aeval_apply]
  have heq : (fun e : Fin n →₀ ℕ => aeval (coefficientVector (d := d) F)
      (if he : e ∈ degreeMonomials n d then
        (X ⟨e,he⟩ : MvPolynomial (DegreeIndex n d) K) else 0)) =
      (fun e => coeff e F) := by
    funext e
    by_cases he : e ∈ degreeMonomials n d
    · simp [he,coefficientVector]
    · simp [he,coeff_zero_outside_degree F hF e he]
  rw [heq]

/-- A closed target avoiding F supplies an actual nonzero evaluation
functional on some finite-dimensional bounded-degree target-ideal piece. -/
theorem exists_finite_target_evaluation
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (hclosed : coefficientClosed S)
    (hhom : ∀ G ∈ S, G.IsHomogeneous d) (hnot : F ∉ S) :
    ∃ N : ℕ, boundedEvaluation (finiteTarget (d := d) S) N (coefficientVector F) ≠ 0 := by
  have hex : ∃ P : MvPolynomial (Fin n →₀ ℕ) K,
      coefficientVanishing S P ∧ eval (fun e => coeff e F) P ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hnot (hclosed F hn)
  obtain ⟨P,hP,hPF⟩ := hex
  apply exists_nonzero_boundedEvaluation
  refine ⟨finiteEquation P,?_,?_⟩
  · rintro _ ⟨G,hG,rfl⟩
    rw [eval_finiteEquation G (hhom G hG)]
    exact hP G hG
  · rw [eval_finiteEquation F hF]
    exact hPF

theorem finiteTarget_zeroLocus (S : Set (MvPolynomial (Fin n) K))
    (hclosed : coefficientClosed S) (hhom : ∀ G ∈ S, G.IsHomogeneous d) :
    zeroLocus K (vanishingIdeal K (finiteTarget (d := d) S)) = finiteTarget (d := d) S := by
  apply le_antisymm
  · intro x hx
    refine ⟨decode x,?_,coefficientVector_decode x⟩
    apply hclosed
    intro P hP
    have hvan : ∀ y ∈ finiteTarget (d := d) S, eval y (finiteEquation (d := d) P) = 0 := by
      rintro _ ⟨G,hG,rfl⟩
      rw [eval_finiteEquation G (hhom G hG)]
      exact hP G hG
    have h := hx (finiteEquation P) hvan
    change eval x (finiteEquation P) = 0 at h
    rw [← coefficientVector_decode x] at h
    change eval (coefficientVector (decode x)) (finiteEquation P) = 0 at h
    rw [eval_finiteEquation (decode x) (decode_homogeneous x)] at h
    exact h
  · intro x hx P hP
    exact hP x hx

end HessianTheorem11.UnconditionalOrbitIdeal

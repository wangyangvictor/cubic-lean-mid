import HessianTheorem11.UnconditionalAlgebraicExistence

/-! Base-change stability of actual polynomial implications and actions.
Pointwise invariance over an algebraically closed field implies invariance
of the actual base-changed zero locus over every field extension. -/
noncomputable section
namespace HessianTheorem11.UnconditionalAlgebraicExistence
open MvPolynomial Ideal
variable {K E : Type*} [Field K] [IsAlgClosed K] [Field E] [Algebra K E]

/-- A polynomial consequence of arbitrary equations over K remains a
consequence over every extension field. -/
theorem equation_of_equations {σ : Type*} [Finite σ]
    (Q : Set (MvPolynomial σ K)) (p : MvPolynomial σ K)
    (h : ∀ y : σ → K, (∀ q ∈ Q, eval y q = 0) → eval y p = 0)
    (x : σ → E) (hx : ∀ q ∈ Q, aeval x q = 0) : aeval x p = 0 := by
  classical
  by_contra hn
  obtain ⟨y,hy,hpy⟩ := exists_equations_inequations Q {p} x hx (by
    intro q hq
    simpa only [Finset.mem_singleton.mp hq] using hn)
  exact hpy p (Finset.mem_singleton_self p) (h y hy)

/-- The actual polynomial tuple evaluated on a parameter and source point. -/
def actionValue {μ σ τ : Type*}
    (P : τ → MvPolynomial (μ ⊕ σ) K) (u : μ → E) (x : σ → E) : τ → E :=
  fun j => aeval (Sum.elim u x) (P j)

theorem aeval_actionEquation {μ σ τ : Type*}
    (P : τ → MvPolynomial (μ ⊕ σ) K) (u : μ → E) (x : σ → E)
    (q : MvPolynomial τ K) :
    aeval (Sum.elim u x) (aeval P q) = aeval (actionValue P u x) q := by
  exact MvPolynomial.comp_aeval_apply (f := P) (aeval (Sum.elim u x)) q

/-- Any polynomial family mapping parameter/source zero loci into a
target zero locus on K-points has the same property over every extension
field. Ideals may have arbitrarily many equations. -/
theorem polynomial_zero_locus_mapsTo {μ σ τ : Type*} [Finite μ] [Finite σ]
    (J : Ideal (MvPolynomial μ K)) (I : Ideal (MvPolynomial σ K))
    (H : Ideal (MvPolynomial τ K)) (P : τ → MvPolynomial (μ ⊕ σ) K)
    (hP : ∀ u ∈ zeroLocus K J, ∀ x ∈ zeroLocus K I,
      actionValue P u x ∈ zeroLocus K H)
    (u : μ → E) (hu : u ∈ zeroLocus E J)
    (x : σ → E) (hx : x ∈ zeroLocus E I) :
    actionValue P u x ∈ zeroLocus E H := by
  intro q hq
  rw [← aeval_actionEquation]
  let Q : Set (MvPolynomial (μ ⊕ σ) K) :=
    rename Sum.inl '' (J : Set (MvPolynomial μ K)) ∪
      rename Sum.inr '' (I : Set (MvPolynomial σ K))
  apply equation_of_equations Q (aeval P q) ?_ (Sum.elim u x) ?_
  · intro y hy
    have hu' : y ∘ Sum.inl ∈ zeroLocus K J := by
      intro p hp
      have he := hy (rename Sum.inl p) (Or.inl ⟨p,hp,rfl⟩)
      simpa only [eval_rename] using he
    have hx' : y ∘ Sum.inr ∈ zeroLocus K I := by
      intro p hp
      have he := hy (rename Sum.inr p) (Or.inr ⟨p,hp,rfl⟩)
      simpa only [eval_rename] using he
    have hh := hP (y ∘ Sum.inl) hu' (y ∘ Sum.inr) hx' q hq
    have he : Sum.elim (y ∘ Sum.inl) (y ∘ Sum.inr) = y := by ext (a|a) <;> rfl
    have ht := aeval_actionEquation P (y ∘ Sum.inl) (y ∘ Sum.inr) q
    rw [he] at ht
    exact ht.trans hh
  · intro p hp
    rcases hp with ⟨p,hp,rfl⟩ | ⟨p,hp,rfl⟩
    · rw [aeval_rename]
      exact hu p hp
    · rw [aeval_rename]
      exact hx p hp

/-- In particular, actual invariance on algebraically closed base-field
points implies invariance after arbitrary field extension. This is an
instance of polynomial implication, with no stable-ideal representation
hypothesis over general algebras. -/
theorem invariant_zero_locus_baseChange {μ σ : Type*} [Finite μ] [Finite σ]
    (J : Ideal (MvPolynomial μ K)) (I : Ideal (MvPolynomial σ K))
    (P : σ → MvPolynomial (μ ⊕ σ) K)
    (hP : ∀ u ∈ zeroLocus K J, ∀ x ∈ zeroLocus K I,
      actionValue P u x ∈ zeroLocus K I)
    (u : μ → E) (hu : u ∈ zeroLocus E J)
    (x : σ → E) (hx : x ∈ zeroLocus E I) :
    actionValue P u x ∈ zeroLocus E I :=
  polynomial_zero_locus_mapsTo J I I P hP u hu x hx

end HessianTheorem11.UnconditionalAlgebraicExistence

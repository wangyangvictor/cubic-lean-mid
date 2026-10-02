import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Tactic

/-! Polynomial realizability descends from an arbitrary field extension of
an algebraically closed field. There may be infinitely many equations; only
the family of nonvanishing conditions must be finite. -/
noncomputable section
namespace HessianTheorem11.UnconditionalAlgebraicExistence
open MvPolynomial Ideal
variable {K E : Type*} [Field K] [IsAlgClosed K] [Field E] [Algebra K E]
  {σ : Type*} [Finite σ]

/-- A point over any extension has a base-field point satisfying every
polynomial equation that vanishes at the original point. -/
theorem exists_specialization (x : σ → E) :
    ∃ y : σ → K, ∀ p : MvPolynomial σ K, aeval x p = 0 → eval y p = 0 := by
  let I := RingHom.ker (aeval x : MvPolynomial σ K →ₐ[K] E).toRingHom
  have hi : I.IsPrime := RingHom.ker_isPrime _
  obtain ⟨M,hM,hIM⟩ := I.exists_le_maximal hi.ne_top
  obtain ⟨y,hy⟩ := (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton).mp hM
  refine ⟨y,?_⟩
  intro p hp
  have hm : p ∈ M := hIM hp
  rw [hy] at hm
  exact (mem_vanishingIdeal_singleton_iff y p).mp hm

/-- Arbitrary equations and finitely many inequations descend from any
field extension. An extra reciprocal coordinate retains all inequations. -/
theorem exists_equations_inequations
    (Q : Set (MvPolynomial σ K)) (S : Finset (MvPolynomial σ K)) (x : σ → E)
    (hQ : ∀ p ∈ Q, aeval x p = 0) (hS : ∀ p ∈ S, aeval x p ≠ 0) :
    ∃ y : σ → K, (∀ p ∈ Q, eval y p = 0) ∧ (∀ p ∈ S, eval y p ≠ 0) := by
  classical
  let q : MvPolynomial σ K := ∏ p ∈ S, p
  have hq : aeval x q ≠ 0 := by
    simpa only [q,map_prod] using Finset.prod_ne_zero_iff.mpr hS
  let x' : (σ ⊕ Unit) → E := Sum.elim x (fun _ => (aeval x q)⁻¹)
  obtain ⟨y',hy'⟩ := exists_specialization (K := K) x'
  let y : σ → K := y' ∘ Sum.inl
  have hrename (p : MvPolynomial σ K) : aeval x' (rename Sum.inl p) = aeval x p := by
    rw [aeval_rename]
    rfl
  have hzero : eval y' (rename Sum.inl q * X (Sum.inr ()) - 1) = 0 := by
    apply hy'
    rw [map_sub,map_mul,hrename,map_one,aeval_X]
    change aeval x q * (aeval x q)⁻¹ - 1 = 0
    rw [mul_inv_cancel₀ hq,sub_self]
  have heq : eval y q * y' (Sum.inr ()) = 1 := by
    simpa only [map_sub,map_mul,eval_rename,eval_X,map_one,sub_eq_zero] using hzero
  have hyq : eval y q ≠ 0 := by
    intro hz
    rw [hz,zero_mul] at heq
    exact zero_ne_one heq
  refine ⟨y,?_,?_⟩
  · intro p hp
    have h := hy' (rename Sum.inl p) (by rw [hrename]; exact hQ p hp)
    simpa only [eval_rename] using h
  · have hsprod : (∏ p ∈ S, eval y p) ≠ 0 := by
      simpa only [q,map_prod] using hyq
    exact Finset.prod_ne_zero_iff.mp hsprod

/-- The same statement using explicit evaluation into the extension. -/
theorem exists_eval₂_equations_inequations
    (Q : Set (MvPolynomial σ K)) (S : Finset (MvPolynomial σ K)) (x : σ → E)
    (hQ : ∀ p ∈ Q, eval₂ (algebraMap K E) x p = 0)
    (hS : ∀ p ∈ S, eval₂ (algebraMap K E) x p ≠ 0) :
    ∃ y : σ → K, (∀ p ∈ Q, eval y p = 0) ∧ (∀ p ∈ S, eval y p ≠ 0) :=
  exists_equations_inequations Q S x hQ hS

end HessianTheorem11.UnconditionalAlgebraicExistence

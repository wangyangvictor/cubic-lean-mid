import CubicTenVariables.PolynomialDivisorBound
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int

/-! Elementary multiplicity of positive moduli at integer points outside a
fixed ideal's actual zero set. Finite defining equations are constructed from
Noetherianity; no geometric sieve or point-count estimate is assumed. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.GeometricSievePairCount
open MvPolynomial
open scoped BigOperators

/-- Actual finite generators of the original integral ideal. -/
theorem exists_finite_generators {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℤ)) :
    ∃ t : ℕ, ∃ P : Fin t → MvPolynomial (Fin n) ℤ,
      Ideal.span (Set.range P)=J := by
  classical
  obtain ⟨S,hS⟩ := IsNoetherian.noetherian J
  let P : Fin (Fintype.card S) → MvPolynomial (Fin n) ℤ :=
    fun i => ((Fintype.equivFin S).symm i).val
  refine ⟨Fintype.card S,P,?_⟩
  have hrange : Set.range P=(S : Set (MvPolynomial (Fin n) ℤ)) := by
    ext f
    constructor
    · rintro ⟨i,rfl⟩
      exact ((Fintype.equivFin S).symm i).property
    · intro hf
      refine ⟨(Fintype.equivFin S) ⟨f,hf⟩,?_⟩
      simp [P]
  rw [hrange]
  exact hS

/-- A point outside the ideal's zero set has a nonzero value among any
actual generating family. There is no rational-point or closure replacement. -/
theorem exists_nonzero_generator {n t : ℕ}
    (J : Ideal (MvPolynomial (Fin n) ℤ)) (P : Fin t → MvPolynomial (Fin n) ℤ)
    (hP : Ideal.span (Set.range P)=J) (x : Fin n → ℤ)
    (hx : ∃ f∈J,eval x f≠0) : ∃j,eval x (P j)≠0 := by
  by_contra! hz
  have hJ : J≤RingHom.ker (eval x) := by
    rw [←hP]
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact hz j
  obtain ⟨f,hf,hne⟩ := hx
  exact hne (hJ hf)

/-- One constant precedes every real center, radius and finite pair set.
Every positive q dividing every ideal value is counted, with no squarefree
or coprimality restriction. Points on the actual integer zero set are excluded
because their modulus fibers need not be finite uniformly. -/
theorem exists_uniform_bound {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℤ))
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,1≤C ∧ ∀u : Fin n → ℝ,∀L : ℝ,1≤L →
      ∀E : Finset (ℕ × (Fin n → ℤ)),
      (∀a∈E,0<a.1) →
      (∀a∈E,∀i,|(a.2 i : ℝ)-u i|≤L) →
      (∀a∈E,∃f∈J,eval a.2 f≠0) →
      (∀a∈E,∀f∈J,(a.1 : ℤ)∣eval a.2 f) →
      (E.card : ℝ)≤C*(L+‖u‖)^ε*((E.image Prod.snd).card : ℝ) := by
  classical
  obtain ⟨t,P,hP⟩ := exists_finite_generators J
  obtain ⟨C,hC,hbound⟩ :=
    PolynomialDivisorBound.exists_family_translated_box_divisor_bound P ε hε
  refine ⟨C,hC,?_⟩
  intro u L hL E hpos hbox hout hdiv
  have hfiber (x : Fin n → ℤ) (hx : x∈E.image Prod.snd) :
      ((E.filter fun a => a.2=x).card : ℝ)≤C*(L+‖u‖)^ε := by
    obtain ⟨a,ha,hax⟩ := Finset.mem_image.mp hx
    let T := E.filter fun a => a.2=x
    let Q := T.image Prod.fst
    have hinj : Set.InjOn Prod.fst (T : Set (ℕ × (Fin n → ℤ))) := by
      intro a ha b hb he
      apply Prod.ext he
      exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
    have hcard : Q.card=T.card := Finset.card_image_iff.mpr hinj
    change (T.card : ℝ)≤_
    rw [←hcard]
    apply hbound u L hL x
    · intro i
      rw [←hax]
      exact hbox a ha i
    · apply exists_nonzero_generator J P hP x
      rw [←hax]
      exact hout a ha
    · intro q hq
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hq
      have hbE := (Finset.mem_filter.mp hb).1
      have hbx := (Finset.mem_filter.mp hb).2
      refine ⟨hpos b hbE,?_⟩
      intro j
      rw [←hbx]
      apply hdiv b hbE
      rw [←hP]
      exact Ideal.subset_span (Set.mem_range_self j)
  calc
    (E.card : ℝ) = ∑x∈E.image Prod.snd,((E.filter fun a => a.2=x).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image Prod.snd E
    _ ≤ ∑_x∈E.image Prod.snd,C*(L+‖u‖)^ε := Finset.sum_le_sum hfiber
    _ = _ := by simp [mul_comm]

end CubicTenVariables.GeometricSievePairCount

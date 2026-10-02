import TranslatedDepthSeven.FiniteIntegralMonicRelationInternal
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Algebra.Polynomial.Roots

/-!
# Cardinality of a fibre of a finite integral algebra

A finite set of distinct points over an infinite field can be separated
by one algebra element. Its monic equation over a normal base remains
monic under specialization, so the number of points is at most the generic
module rank. This counts distinct points, not the length of the fibre, and
does not assume flatness or smoothness of the fibre.
-/

namespace TranslatedDepthSeven

noncomputable section
open scoped nonZeroDivisors
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

universe u

/-- A single element distinguishes any given finite collection of
distinct algebra homomorphisms into an infinite coefficient field. -/
theorem exists_element_injective_on_finite_algHoms
    {K A : Type u} [Field K] [Infinite K] [CommRing A] [Algebra K A]
    (S : Finset (A →ₐ[K] K)) :
    ∃ a : A, Set.InjOn (fun f : A →ₐ[K] K ↦ f a) (↑S : Set (A →ₐ[K] K)) := by
  classical
  let pairs := {p : S × S // p.1 ≠ p.2}
  let difference : pairs → Module.Dual K A := fun p ↦
    p.val.1.val.toLinearMap - p.val.2.val.toLinearMap
  have hnonzero : ∀ p, ∃ a, difference p a ≠ 0 := by
    intro p
    by_contra h
    push_neg at h
    apply p.property
    apply Subtype.ext
    ext a
    have ha := h a
    exact sub_eq_zero.mp ha
  obtain ⟨a, ha⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists difference hnonzero
  refine ⟨a, ?_⟩
  intro f hf g hg heq
  by_contra hfg
  let p : pairs := ⟨(⟨f, hf⟩, ⟨g, hg⟩), fun h ↦ hfg (congrArg Subtype.val h)⟩
  exact ha p (sub_eq_zero.mpr heq)

/-- Distinct field-valued points over one specialization of a finite
normal-base extension of domains number at most its generic module rank.
No claim about scheme-theoretic fibre length is made. -/
theorem finite_fibre_card_le_localized_rank
    {K B A : Type u} [Field K] [Infinite K]
    [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [CommRing A] [IsDomain A] [Algebra B A] [Algebra K A]
    [FaithfulSMul B A] [Module.Finite B A]
    (specialization : B →+* K) (S : Finset (A →ₐ[K] K))
    (hS : ∀ f ∈ S, ∀ b : B, f (algebraMap B A b) = specialization b) :
    S.card ≤ Module.finrank (FractionRing B)
      (LocalizedModule (nonZeroDivisors B) A) := by
  classical
  obtain ⟨a, hseparates⟩ := exists_element_injective_on_finite_algHoms S
  obtain ⟨p, hmonic, hdegree, hzero⟩ :=
    exists_monic_annihilator_natDegree_le_localized_rank (B := B) a
  let q := p.map specialization
  have hqne : q ≠ 0 := Polynomial.map_monic_ne_zero hmonic
  have hroots : ∀ f ∈ S, q.eval (f a) = 0 := by
    intro f hf
    have hcomp : f.toRingHom.comp (algebraMap B A) = specialization := by
      ext b
      exact hS f hf b
    have h := congrArg f hzero
    have heval := Polynomial.hom_eval₂ p (algebraMap B A) f.toRingHom a
    rw [hcomp] at heval
    have hz : p.eval₂ specialization (f a) = 0 :=
      heval.symm.trans (by simpa only [map_zero] using h)
    simpa only [q, ← Polynomial.eval₂_eq_eval_map] using hz
  have hcard : S.card ≤ q.natDegree := by
    by_contra h
    have hsmall : q.natDegree < Fintype.card S := by simpa using (Nat.lt_of_not_ge h)
    have hinj : Function.Injective (fun f : S ↦ f.val a) := by
      intro f g hfg
      exact Subtype.ext (hseparates f.property g.property hfg)
    exact hqne (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero q hinj
      (fun f ↦ hroots f.val f.property) hsmall)
  exact hcard.trans ((Polynomial.natDegree_map_le).trans hdegree)

end
end TranslatedDepthSeven

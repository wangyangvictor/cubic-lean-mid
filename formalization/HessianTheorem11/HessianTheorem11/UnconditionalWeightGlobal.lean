import HessianTheorem11.UnconditionalWeightSpeed
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Data.Fintype.Lattice

/-! Only finitely many monomial supports occur in a fixed homogeneous
representation. Selecting the best of their proved integer optima gives a
global maximizing frame, without an optimal-one-parameter-subgroup input. -/
noncomputable section
namespace HessianTheorem11.UnconditionalWeightOptimization
open MvPolynomial RationalDescent PolynomialRestriction PolynomialWeightTransport
variable {K : Type*} [Field K] {n d : ℕ}

theorem restrict_nonzero (F : MvPolynomial (Fin n) K) (hF : F ≠ 0)
    (B : Matrix (Fin n) (Fin n) K) (hB : Function.Injective B.mulVec) :
    restrict B F ≠ 0 := by
  intro hz
  apply hF
  have hh : restrict (frameTransition B 1 hB) (restrict B F) = 0 := by
    rw [hz]
    exact map_zero (aeval (linearForms (frameTransition B 1 hB)))
  rwa [restrict_restrict, matrix_mul_frameTransition, restrict_one] at hh

def positiveSupports (F : MvPolynomial (Fin n) K) : Set (Finset (Fin n →₀ ℕ)) :=
  {S | ∃ B : Matrix (Fin n) (Fin n) K, Function.Injective B.mulVec ∧
      (restrict B F).support = S ∧ (feasible S).Nonempty}

theorem positiveSupports_finite (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d) :
    (positiveSupports F).Finite := by
  classical
  apply (Finset.powerset (Finset.univ.finsuppAntidiag d)).finite_toSet.subset
  rintro S ⟨B,hB,rfl,hne⟩
  apply Finset.mem_powerset.mpr
  intro e he
  apply Finset.mem_finsuppAntidiag'.mpr
  refine ⟨?_,Finset.subset_univ _⟩
  simpa [Finsupp.weight_apply,smul_eq_mul] using
    homogeneous_restrict B F hF (Finsupp.mem_support_iff.mp he)

def MaximizingFrame (F : MvPolynomial (Fin n) K) (f : WeightFrame K n) : Prop :=
  f.Positive F ∧ ∀ g : WeightFrame K n, g.instability F ≤ f.instability F

/-- Global normalized instability has an actual integral maximizing frame.
Primitivity is unnecessary for the later Galois comparison, which retains
the identical weight list. -/
theorem exists_maximizing_frame (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous d) (hne : F ≠ 0)
    (hunstable : ∃ f : WeightFrame K n, f.Positive F) :
    ∃ f : WeightFrame K n, MaximizingFrame F f := by
  classical
  let Supports := {S // S ∈ positiveSupports F}
  letI : Finite Supports := (positiveSupports_finite F hF).to_subtype
  have hSupports : Nonempty Supports := by
    obtain ⟨f,hf⟩ := hunstable
    exact ⟨⟨(restrict f.matrix F).support, f.matrix,f.injective,rfl,
      ⟨_,feasible_of_positive _ f.weight f.sum_zero hf⟩⟩⟩
  letI : Nonempty Supports := hSupports
  have hnonempty (S : Supports) : S.val.Nonempty := by
    obtain ⟨B,hB,hS,hfeas⟩ := S.property
    rw [← hS]
    exact support_nonempty.mpr (restrict_nonzero F hne B hB)
  have hfeasible (S : Supports) : (feasible S.val).Nonempty := by
    obtain ⟨B,hB,hS,hfeas⟩ := S.property
    exact hfeas
  choose z hz using (fun S : Supports =>
    exists_fixed_support_maximizer S.val (hnonempty S) (hfeasible S))
  obtain ⟨S,hSmax⟩ := Finite.exists_max (fun S : Supports => finiteSpeed S.val (z S))
  obtain ⟨B,hB,hBS,_⟩ := S.property
  let f : WeightFrame K n := ⟨B,hB,z S,(hz S).1⟩
  have hf : f.Positive F := by
    change ∀ e ∈ (restrict B F).support, 0 < monomialWeight (z S) e
    rw [hBS]
    exact (hz S).2.1
  have hfspeed : f.instability F = finiteSpeed S.val (z S) := by
    rw [instability_eq_finiteSpeed]
    change finiteSpeed (restrict B F).support (z S) = _
    rw [hBS]
  refine ⟨f,hf,?_⟩
  intro g
  by_cases hg : g.Positive F
  · let T : Supports := ⟨(restrict g.matrix F).support,
      g.matrix,g.injective,rfl,⟨_,feasible_of_positive _ g.weight g.sum_zero hg⟩⟩
    rw [hfspeed,instability_eq_finiteSpeed]
    exact ((hz T).2.2.2 g.weight g.sum_zero).trans (hSmax T)
  · have hgmin : finiteMinimum (restrict g.matrix F).support g.weight ≤ 0 := by
      change ¬ (∀ e ∈ (restrict g.matrix F).support, 0 < monomialWeight g.weight e) at hg
      push_neg at hg
      obtain ⟨e,he,hweight⟩ := hg
      exact (finiteMinimum_le g.weight he).trans hweight
    have hgzero : g.instability F ≤ 0 := by
      rw [instability_eq_finiteSpeed]
      exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hgmin) (norm_nonneg _)
    exact hgzero.trans (by rw [hfspeed]; exact (hz S).2.2.1.le)

theorem maximizing_conjugate (F : MvPolynomial (Fin n) K)
    (f : WeightFrame K n) (σ : K ≃+* K) (hf : MaximizingFrame F f) :
    MaximizingFrame (map σ.toRingHom F) (f.conjugate σ) := by
  refine ⟨(f.positive_conjugate_iff σ F).mpr hf.1,?_⟩
  intro g
  have h := hf.2 (g.conjugate σ.symm)
  rw [← (g.conjugate σ.symm).instability_conjugate σ F] at h
  rw [g.conjugate_symm σ] at h
  rwa [f.instability_conjugate σ F]

end HessianTheorem11.UnconditionalWeightOptimization

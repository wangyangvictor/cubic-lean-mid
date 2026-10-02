import HessianTheorem11.UnconditionalAlgebraicExistenceForms
import HessianTheorem11.ReducedRelativeGeometry

/-! A diagonal limit satisfying the original target equations descends
from an arbitrary extension field to the algebraically closed base. The
integral weight is held fixed, and admissibility is preserved exactly. -/
noncomputable section
namespace HessianTheorem11.UnconditionalWeightLimitDescent
open MvPolynomial PolynomialRestriction PolynomialWeightTransport NonzeroLimitTransport
  ReducedRelative UnconditionalAlgebraicExistence
variable {K E : Type*} [Field K] [IsAlgClosed K] [Field E] [Algebra K E] {n : ℕ}

def zeroWeightEquation (w : Fin n → ℤ) (q : MvPolynomial (Fin n →₀ ℕ) K) :
    MvPolynomial (Fin n →₀ ℕ) K :=
  aeval (fun e => if monomialWeight w e = 0 then X e else 0) q

theorem aeval_zeroWeightEquation (w : Fin n → ℤ)
    (q : MvPolynomial (Fin n →₀ ℕ) K) (H : MvPolynomial (Fin n) E) :
    aeval (fun e => coeff e H) (zeroWeightEquation w q) =
      aeval (fun e => coeff e (zeroWeightPart H w)) q := by
  rw [zeroWeightEquation,MvPolynomial.comp_aeval_apply]
  have he : (fun e => aeval (fun e => coeff e H)
      (if monomialWeight w e = 0 then (X e : MvPolynomial (Fin n →₀ ℕ) K) else 0)) =
      (fun e => coeff e (zeroWeightPart H w)) := by
    funext e
    by_cases h : monomialWeight w e = 0 <;> simp [h]
  rw [he]

theorem eval_zeroWeightEquation (w : Fin n → ℤ)
    (q : MvPolynomial (Fin n →₀ ℕ) K) (H : MvPolynomial (Fin n) K) :
    eval (fun e => coeff e H) (zeroWeightEquation w q) =
      eval (fun e => coeff e (zeroWeightPart H w)) q :=
  aeval_zeroWeightEquation w q H

/-- Descend the actual SL frame producing an admissible diagonal limit
in a coefficient-closed base-field target. -/
theorem exists_base_weight_limit (F : MvPolynomial (Fin n) K)
    (S : Set (MvPolynomial (Fin n) K)) (hS : coefficientClosed S)
    (w : Fin n → ℤ) (A : Matrix (Fin n) (Fin n) E) (hA : A.det = 1)
    (hW : HasNonnegativeWeights (restrict A (map (algebraMap K E) F)) w)
    (hT : ∀ q : MvPolynomial (Fin n →₀ ℕ) K, coefficientVanishing S q →
      aeval (fun e => coeff e (zeroWeightPart
        (restrict A (map (algebraMap K E) F)) w)) q = 0) :
    ∃ B : Matrix (Fin n) (Fin n) K, B.det = 1 ∧
      HasNonnegativeWeights (restrict B F) w ∧ zeroWeightPart (restrict B F) w ∈ S := by
  classical
  let Q : Set (MvPolynomial (Fin n →₀ ℕ) K) := {p |
    (∃ e, monomialWeight w e < 0 ∧ p = X e) ∨
    ∃ q, coefficientVanishing S q ∧ p = zeroWeightEquation w q}
  have hQ : ∀ p ∈ Q,
      aeval (fun e => coeff e (restrict A (map (algebraMap K E) F))) p = 0 := by
    intro p hp
    rcases hp with ⟨e,he,rfl⟩ | ⟨q,hq,rfl⟩
    · simp only [aeval_X]
      by_contra hc
      exact (not_le_of_gt he) (hW e (mem_support_iff.mpr hc))
    · rw [aeval_zeroWeightEquation]
      exact hT q hq
  obtain ⟨B,hB,hBQ,_⟩ := exists_specialLinear_restriction F Q ∅ A hA hQ (by simp)
  refine ⟨B,hB,?_,?_⟩
  · intro e he
    by_contra hw
    have hz := hBQ (X e) (Or.inl ⟨e,lt_of_not_ge hw,rfl⟩)
    exact (mem_support_iff.mp he) (by simpa only [eval_X] using hz)
  · apply hS
    intro q hq
    rw [← eval_zeroWeightEquation]
    exact hBQ _ (Or.inr ⟨q,hq,rfl⟩)

end HessianTheorem11.UnconditionalWeightLimitDescent

import HessianTheorem11.TangentHessianRank
import HessianTheorem11.GenericRankBridge

/-! Extending the rank bound across the vertex of the actual quadratic
normal map. This uses the same universal open-minor input as the generic
Hessian rank, together with polynomial-domain and Nullstellensatz lemmas. -/

noncomputable section
namespace HessianTheorem11.TangentHessianRank
open MvPolynomial Matrix Module

/-- A polynomial map to a nondegenerate quadratic cone has Jacobian rank
strictly smaller than the target dimension at every point, including
points sent to the vertex. The zero map is handled separately. -/
theorem rank_polynomialJacobian_lt_everywhere
    (MR : GenericMatrixRankInput) {s r : ℕ} (hr : 0 < r)
    (Q : Matrix (Fin r) (Fin r) GeometricField) (hQ : Q.IsSymm) (hdet : Q.det ≠ 0)
    (p : Fin r → GeometricPolynomial s) (hp : quadraticRelation Q p = 0)
    (x : GeometricPoint s) : (polynomialJacobian p x).rank < r := by
  classical
  by_cases hp0 : p = 0
  · have hj : polynomialJacobian p x = 0 := by
      ext i j
      simp [polynomialJacobian, hp0]
    simpa only [hj, Matrix.rank_zero] using hr
  · obtain ⟨i, hi⟩ : ∃ i, p i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hp0 (funext h)
    let I : Ideal (GeometricPolynomial s) := ⊥
    let M : Matrix (Fin r) (Fin s) (GeometricPolynomial s) :=
      fun i j => pderiv j (p i)
    letI : I.IsPrime := Ideal.bot_prime
    obtain ⟨q, hq, hopen⟩ := MR.principal_open I M
    have hq0 : q ≠ 0 := by simpa only [I, Ideal.mem_bot] using hq
    have hprod : q * p i ∉ I := by
      simpa only [I, Ideal.mem_bot] using mul_ne_zero hq0 hi
    obtain ⟨y, hy, hye⟩ := exists_zeroLocus_eval_ne_zero I (q * p i) hprod
    have hyq : eval y q ≠ 0 := by
      intro he
      exact hye (by rw [map_mul, he, zero_mul])
    have hyp : (fun j => eval y (p j)) ≠ 0 := by
      intro he
      have hei : eval y (p i) = 0 := congrFun he i
      exact hye (by rw [map_mul, hei, mul_zero])
    have hg : genericMatrixRank I M < r := by
      rw [← hopen y hy hyq]
      simpa only [Fintype.card_fin] using rank_polynomialJacobian_lt Q hQ hdet p hp y hyp
    have hxI : x ∈ zeroLocus GeometricField I := by
      intro P hP
      have hP0 : P = 0 := hP
      simp [hP0]
    exact (MR.specialization_le I M x hxI).trans_lt hg

theorem tangent_hessian_rank_le_nine_everywhere
    (MR : GenericMatrixRankInput) {s : ℕ}
    (F : MvPolynomial (Fin s ⊕ Fin 5) GeometricField)
    (hF : tangentRestriction F = 0)
    (Q : Matrix (Fin 5) (Fin 5) GeometricField) (hQ : Q.IsSymm) (hdet : Q.det ≠ 0)
    (hp : quadraticRelation Q (normalGradient F) = 0)
    (x : GeometricPoint s) :
    (evaluatedHessian F (Sum.elim x (0 : Fin 5 → GeometricField))).rank ≤ 9 := by
  have h₁ := tangent_hessian_rank_le F hF x
  have h₂ := rank_polynomialJacobian_lt_everywhere MR (by norm_num : 0 < 5)
    Q hQ hdet (normalGradient F) hp x
  simp only [Fintype.card_fin] at h₁
  omega

end HessianTheorem11.TangentHessianRank

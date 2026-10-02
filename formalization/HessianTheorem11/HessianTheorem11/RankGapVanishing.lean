import HessianTheorem11.RankClosure

/-! A polynomial vanishes on an irreducible set if its nonvanishing would
force the rank of a larger matrix above the allowed bound. The proof uses
an ordinary generic-rank principal open and primality of the vanishing ideal. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial

theorem polynomial_vanishes_of_rank_gap
    (MR : GenericMatrixRankInput)
    {σ : Type} [Fintype σ] {a b c d : ℕ}
    (Z : Set (σ → GeometricField)) (hZ : GeometricallyIrreducible Z)
    (M : Matrix (Fin a) (Fin b) (MvPolynomial σ GeometricField))
    (A : Matrix (Fin c) (Fin d) (MvPolynomial σ GeometricField))
    (p : MvPolynomial σ GeometricField) (r : ℕ)
    (hbound : ∀ x ∈ Z, (M.map (eval x)).rank ≤ r)
    (hattained : ∃ x ∈ Z, r ≤ (A.map (eval x)).rank)
    (hgap : ∀ x ∈ Z, eval x p ≠ 0 →
      (A.map (eval x)).rank < (M.map (eval x)).rank) :
    ∀ x ∈ Z, eval x p = 0 := by
  let I := vanishingIdeal GeometricField Z
  letI : I.IsPrime := hZ
  obtain ⟨q, hq, hgeneric⟩ := MR.principal_open I A
  have hr : r ≤ genericMatrixRank I A := by
    obtain ⟨x, hx, hrx⟩ := hattained
    exact hrx.trans (MR.specialization_le I A x (subset_geometricClosure Z hx))
  have hpq : p * q ∈ I := by
    intro x hx
    change eval x (p * q) = 0
    rw [eval_mul]
    by_cases hxq : eval x q = 0
    · simp [hxq]
    · have hxp : eval x p = 0 := by
        by_contra hxp
        have hsmall := hgap x hx hxp
        have hlarge := hbound x hx
        have h := hgeneric x (subset_geometricClosure Z hx) hxq
        change (A.map (eval x)).rank = genericMatrixRank I A at h
        rw [h] at hsmall
        omega
      simp [hxp]
  have hp : p ∈ I := ((inferInstance : I.IsPrime).mem_or_mem hpq).resolve_right hq
  exact hp

end HessianTheorem11

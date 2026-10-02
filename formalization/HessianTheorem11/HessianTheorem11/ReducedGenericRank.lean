import HessianTheorem11.GenericRankBridge
import HessianTheorem11.MatrixRankMinors

/-! The former generic-matrix-rank input is proved from actual minors and
the injective map of a domain into its fraction field. No geometric theorem
is assumed here, and the polynomial matrix may be rectangular. -/

noncomputable section
namespace HessianTheorem11.ReducedGenericRank
open MvPolynomial Matrix MatrixRankMinors

theorem genericPointMap_eq_zero_iff {σ : Type*}
    (I : Ideal (MvPolynomial σ GeometricField)) [I.IsPrime]
    (p : MvPolynomial σ GeometricField) : genericPointMap I p = 0 ↔ p ∈ I := by
  change algebraMap (affineCoordinateRing I) (affineFunctionField I)
    (Ideal.Quotient.mk I p) = 0 ↔ p ∈ I
  rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

theorem specialization_le {σ : Type*} {a b : ℕ}
    (I : Ideal (MvPolynomial σ GeometricField)) [I.IsPrime]
    (M : Matrix (Fin a) (Fin b) (MvPolynomial σ GeometricField))
    (x : σ → GeometricField) (hx : x ∈ zeroLocus GeometricField I) :
    (evaluatedMatrix M x).rank ≤ genericMatrixRank I M := by
  by_contra h
  obtain ⟨rows, cols, hdet⟩ := exists_rank_minor (evaluatedMatrix M x)
  let p : MvPolynomial σ GeometricField := (M.submatrix rows cols).det
  have hsub := PolynomialSchurVanishing.rank_submatrix_le (genericMatrix I M) rows cols
  have hzero : ((genericMatrix I M).submatrix rows cols).det = 0 :=
    PolynomialSchurVanishing.det_eq_zero_of_rank_lt _
      (by simpa only [Fintype.card_fin] using hsub.trans_lt (lt_of_not_ge h))
  have hp : genericPointMap I p = 0 := by
    rw [show genericPointMap I p = genericPointMap I (M.submatrix rows cols).det by rfl,
      RingHom.map_det]
    exact hzero
  have he := hx p ((genericPointMap_eq_zero_iff I p).mp hp)
  change eval x p = 0 at he
  apply hdet
  rw [show eval x p = (eval x) (M.submatrix rows cols).det by rfl,
    RingHom.map_det] at he
  exact he

theorem principal_open {σ : Type*} {a b : ℕ}
    (I : Ideal (MvPolynomial σ GeometricField)) [I.IsPrime]
    (M : Matrix (Fin a) (Fin b) (MvPolynomial σ GeometricField)) :
    ∃ q : MvPolynomial σ GeometricField, q ∉ I ∧
      ∀ x ∈ zeroLocus GeometricField I, eval x q ≠ 0 →
        (evaluatedMatrix M x).rank = genericMatrixRank I M := by
  obtain ⟨rows, cols, hdet⟩ := exists_rank_minor (genericMatrix I M)
  let q : MvPolynomial σ GeometricField := (M.submatrix rows cols).det
  have hq : q ∉ I := by
    intro hq
    have hz := (genericPointMap_eq_zero_iff I q).mpr hq
    rw [show genericPointMap I q = genericPointMap I (M.submatrix rows cols).det by rfl,
      RingHom.map_det] at hz
    exact hdet hz
  refine ⟨q, hq, ?_⟩
  intro x hx hqx
  apply le_antisymm (specialization_le I M x hx)
  apply minor_size_le_rank (evaluatedMatrix M x) rows cols
  intro hz
  apply hqx
  rw [show eval x q = (eval x) (M.submatrix rows cols).det by rfl, RingHom.map_det]
  exact hz

/-- Fully proved replacement for the former textbook hypothesis MR. -/
def genericMatrixRankInput : GenericMatrixRankInput where
  specialization_le := specialization_le
  principal_open := principal_open

end HessianTheorem11.ReducedGenericRank

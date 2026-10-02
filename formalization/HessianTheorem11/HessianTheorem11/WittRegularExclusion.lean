import HessianTheorem11.WittQuadraticTuple
import HessianTheorem11.FourQuadricsRadical

/-! The actual reconstruction and exclusion of nondegenerate deficient
normal spans. The Witt subspace and polynomial tuple are genuine data. -/

noncomputable section
namespace HessianTheorem11.WittQuadraticTuple
open MvPolynomial Matrix Module WittSubspaceBasis
variable {K : Type*} [Field K] [CharZero K] {n m r k : ℕ}
variable {B : LinearMap.BilinForm K (Fin m → K)} {U : Submodule K (Fin m → K)}

def regularReconstructionMatrix (D : Data B U r 0 k) : Matrix (Fin m) (Fin r) K :=
  fun i j => D.basis (regularIndex j) i

theorem tuple_eq_combine_regular (D : Data B U r 0 k)
    (p : Fin m → MvPolynomial (Fin n) K) (hmem : ∀ x, value p x ∈ U) :
    p = combinePolynomials (regularReconstructionMatrix D) (regularTuple D p) := by
  funext i
  apply MvPolynomial.funext
  intro x
  have he := congrFun (value_expansion D p hmem x) i
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at he
  simpa only [combinePolynomials_apply, map_sum, map_mul, eval_C,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, regularReconstructionMatrix,
    mul_comm] using he

theorem regular_three_four_excluded [IsAlgClosed K]
    (D : Data B U r 0 k) (hB : B.IsSymm)
    (p : Fin m → MvPolynomial (Fin n) K)
    (hp : ∀ i, (p i).IsHomogeneous 2)
    (hspan : Submodule.span K (Set.range (value p)) = U)
    (hrel : ∀ x, B (value p x) (value p x) = 0)
    (hcommon : polynomialTupleDifferentialRadical p = ⊥)
    (hn : 5 ≤ n) (hr : r = 3 ∨ r = 4) : False := by
  have hmem : ∀ x, value p x ∈ U := fun x => hspan.le (Submodule.subset_span ⟨x,rfl⟩)
  exact tuple_not_three_four_nondegenerate_span p hcommon hn (regularTuple D p)
    (regularTuple_homogeneous D p hp) (regularTuple_independent D p hspan)
    (regularReconstructionMatrix D) (tuple_eq_combine_regular D p hmem)
    (regularGram D) (regularGram_symm D hB) D.regular_nonsingular
    (regular_relation D hB p hmem hrel) hr

end HessianTheorem11.WittQuadraticTuple

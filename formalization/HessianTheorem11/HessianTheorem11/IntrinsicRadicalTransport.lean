import HessianTheorem11.LocalCubicKernel
import HessianTheorem11.BasisHessianTransport
import HessianTheorem11.IntrinsicRadical

/-! Transport of the actual kernel-of-kernel radical through a basis change.
The local quadratic kernel is identified with the intrinsic submodule, rather
than supplied as a dimension or rank certificate. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Module LocalCubicNormalForm BasisHessianTransport

variable {n m q : ℕ}

theorem basis_congruence_mulVec_eq_zero_iff {ι : Type*} [Fintype ι]
    (b : Basis ι GeometricField (Fin n → GeometricField))
    (H : Matrix (Fin n) (Fin n) GeometricField) (v : ι → GeometricField) :
    ((BasisHessianTransport.basisMatrix b).transpose * H * BasisHessianTransport.basisMatrix b).mulVec v = 0 ↔
      H.mulVec ((BasisHessianTransport.basisMatrix b).mulVec v) = 0 := by
  classical
  let B := BasisHessianTransport.basisMatrix b
  let T := b.toMatrix (Pi.basisFun GeometricField (Fin n))
  have hBT : B * T = 1 := by
    rw [show B = (Pi.basisFun GeometricField (Fin n)).toMatrix b from
      BasisHessianTransport.basisMatrix_eq_toMatrix b]
    exact (Pi.basisFun GeometricField (Fin n)).toMatrix_mul_toMatrix_flip b
  have hTB : T.transpose * B.transpose = 1 := by
    rw [← Matrix.transpose_mul, hBT, Matrix.transpose_one]
  change (B.transpose * H * B).mulVec v = 0 ↔ H.mulVec (B.mulVec v) = 0
  constructor
  · intro hv
    have hz := congrArg (T.transpose.mulVec) hv
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at hz
    simpa only [← Matrix.mul_assoc, hTB, Matrix.one_mul, ← Matrix.mulVec_mulVec] using hz
  · intro hv
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

theorem localHessian_mulVec_zero_iff
    (D : Data (K := GeometricField) m q)
    (b : Basis (Coordinate m q) GeometricField (Fin n → GeometricField))
    (F : GeometricPolynomial n)
    (hD : PolynomialRestriction.restrict (BasisHessianTransport.basisMatrix b) F = polynomial D)
    (x v : Coordinate m q → GeometricField) :
    (localHessian D x).mulVec v = 0 ↔
      (hessian F (b.equivFun.symm x)).mulVec (b.equivFun.symm v) = 0 := by
  have he := BasisHessianTransport.hessian_restrict (BasisHessianTransport.basisMatrix b) F x
  rw [hD] at he
  change localHessian D x = _ at he
  rw [he, basis_congruence_mulVec_eq_zero_iff, BasisHessianTransport.basisMatrix_mulVec_eq,
    BasisHessianTransport.basisMatrix_mulVec_eq]

theorem mem_localIntrinsicRadical_transport_iff
    (D : Data (K := GeometricField) m q)
    (b : Basis (Coordinate m q) GeometricField (Fin n → GeometricField))
    (F : GeometricPolynomial n)
    (hD : PolynomialRestriction.restrict (BasisHessianTransport.basisMatrix b) F = polynomial D)
    (v : Coordinate m q → GeometricField) :
    v ∈ localIntrinsicRadical D ↔
      b.equivFun.symm v ∈ intrinsicRadical F (b.equivFun.symm (basePoint m q)) := by
  rw [mem_localIntrinsicRadical_iff, mem_intrinsicRadical_iff,
    localHessian_mulVec_zero_iff D b F hD]
  constructor
  · rintro ⟨hv, h⟩
    refine ⟨hv, ?_⟩
    intro u hu
    have hlocal : (localHessian D (basePoint m q)).mulVec (b.equivFun u) = 0 := by
      apply (localHessian_mulVec_zero_iff D b F hD _ _).mpr
      simpa only [LinearEquiv.symm_apply_apply] using hu
    have hr := (localHessian_mulVec_zero_iff D b F hD _ _).mp (h _ hlocal)
    simpa only [LinearEquiv.symm_apply_apply] using hr
  · rintro ⟨hv, h⟩
    refine ⟨hv, ?_⟩
    intro u hu
    apply (localHessian_mulVec_zero_iff D b F hD _ _).mpr
    exact h _ ((localHessian_mulVec_zero_iff D b F hD _ _).mp hu)

def localRadicalTransportEquiv
    (D : Data (K := GeometricField) m q)
    (b : Basis (Coordinate m q) GeometricField (Fin n → GeometricField))
    (F : GeometricPolynomial n)
    (hD : PolynomialRestriction.restrict (BasisHessianTransport.basisMatrix b) F = polynomial D) :
    localIntrinsicRadical D ≃ₗ[GeometricField]
      intrinsicRadical F (b.equivFun.symm (basePoint m q)) where
  toFun v := ⟨b.equivFun.symm v,
    (mem_localIntrinsicRadical_transport_iff D b F hD v).mp v.property⟩
  invFun v := ⟨b.equivFun v, by
    apply (mem_localIntrinsicRadical_transport_iff D b F hD _).mpr
    simpa only [LinearEquiv.symm_apply_apply] using v.property⟩
  left_inv v := by apply Subtype.ext; exact b.equivFun.apply_symm_apply v
  right_inv v := by apply Subtype.ext; exact b.equivFun.symm_apply_apply v
  map_add' v w := by apply Subtype.ext; exact b.equivFun.symm.map_add v w
  map_smul' c v := by apply Subtype.ext; exact b.equivFun.symm.map_smul c v

theorem finrank_intrinsicRadical_of_local
    (D : Data (K := GeometricField) m q)
    (b : Basis (Coordinate m q) GeometricField (Fin n → GeometricField))
    (F : GeometricPolynomial n)
    (hD : PolynomialRestriction.restrict (BasisHessianTransport.basisMatrix b) F = polynomial D)
    (hB0 : (quadraticMatrix D.Q0).det ≠ 0) :
    finrank GeometricField (intrinsicRadical F (b.equivFun.symm (basePoint m q))) =
      m - (quadraticMatrix D.QA).rank := by
  rw [← (localRadicalTransportEquiv D b F hD).finrank_eq]
  exact finrank_localIntrinsicRadical D hB0

theorem localHessian_rank_transport
    (D : Data (K := GeometricField) m q)
    (b : Basis (Coordinate m q) GeometricField (Fin n → GeometricField))
    (F : GeometricPolynomial n)
    (hD : PolynomialRestriction.restrict (BasisHessianTransport.basisMatrix b) F = polynomial D)
    (x : Coordinate m q → GeometricField) :
    (localHessian D x).rank = (hessian F (b.equivFun.symm x)).rank := by
  have he := BasisHessianTransport.hessian_rank_restrict b F x
  rw [hD, BasisHessianTransport.basisMatrix_mulVec_eq] at he
  exact he

/-- The rank-four conclusion for the actual intrinsic radical in the
original coordinates. The irreducibility and rank bound are hypotheses on
the original polynomial; both are transported through the actual basis. -/
theorem intrinsicRadical_rank_le_four_of_local
    (D : Data (K := GeometricField) m q)
    (b : Basis (Coordinate m q) GeometricField (Fin n → GeometricField))
    (F : GeometricPolynomial n)
    (hD : PolynomialRestriction.restrict (BasisHessianTransport.basisMatrix b) F = polynomial D)
    (FI : FormalImplicitFunctionInput GeometricField)
    (hirred : Irreducible F) (hB0 : (quadraticMatrix D.Q0).det ≠ 0)
    (hRank : ∀ x, eval x F = 0 → (hessian F x).rank ≤ q + 2)
    (hP : 1 ≤ (quadraticMatrix D.QA).rank) (hq : q ≤ 7)
    (v : GeometricPoint n)
    (hv : v ∈ intrinsicRadical F (b.equivFun.symm (basePoint m q))) :
    (hessian F v).rank ≤ 4 := by
  have hirredD : Irreducible (polynomial D) := by
    rw [← hD]
    exact BasisHessianTransport.restrict_irreducible b F hirred
  have hRankD : ∀ y : Coordinate m q → GeometricField,
      eval y (polynomial D) = 0 → ((polynomialHessian D).map (eval y)).rank ≤ q + 2 := by
    intro y hy
    change (localHessian D y).rank ≤ q + 2
    rw [localHessian_rank_transport D b F hD]
    apply hRank
    rw [← BasisHessianTransport.basisMatrix_mulVec_eq,
      ← PolynomialRestriction.eval_restrict, hD]
    exact hy
  let u := b.equivFun v
  have hu : u ∈ localIntrinsicRadical D := by
    apply (mem_localIntrinsicRadical_transport_iff D b F hD u).mpr
    simpa only [u, LinearEquiv.symm_apply_apply] using hv
  have huA : u = pureAPoint (u ∘ Sum.inl) :=
    (base_hessian_kernel_iff D hB0 u).mp ((mem_localIntrinsicRadical_iff D u).mp hu).1
  have hkernel : (quadraticMatrix D.QA).mulVec (u ∘ Sum.inl) = 0 := by
    apply (pureA_mem_localIntrinsicRadical_iff D hB0 _).mp
    rw [← huA]
    exact hu
  have hr := (pureA_radical_singular_rank_le_four D FI hirredD hB0 hRankD hP hq
    (u ∘ Sum.inl) hkernel).2
  have ht := localHessian_rank_transport D b F hD (pureAPoint (u ∘ Sum.inl))
  change (pureAHessian D (u ∘ Sum.inl)).rank = _ at ht
  rw [← huA] at ht
  have heu : b.equivFun.symm u = v := b.equivFun.symm_apply_apply v
  rw [heu] at ht
  rw [← ht]
  exact hr

end HessianTheorem11

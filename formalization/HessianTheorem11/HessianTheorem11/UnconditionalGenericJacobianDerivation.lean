import HessianTheorem11.UnconditionalGenericQuotient
import HessianTheorem11.UnconditionalGenericJacobian
import HessianTheorem11.UnconditionalGenericDimension

/-! The generic Jacobian kernel is the space of derivations of the actual
coordinate quotient with values in its fraction field. -/

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 160000
namespace HessianTheorem11.UnconditionalGeneric
open MvPolynomial Module ReducedTangentRank

section Polynomial
variable (K L : Type*) (σ : Type*) [CommRing K] [CommRing L]
  [Algebra K L] [Algebra (MvPolynomial σ K) L]
  [IsScalarTower K (MvPolynomial σ K) L]

/-- Values on the polynomial variables determine a derivation, and the
correspondence is linear over the entire target coefficient algebra. -/
def polynomialDerivationEquiv : (σ → L) ≃ₗ[L] Derivation K (MvPolynomial σ K) L where
  toFun := MvPolynomial.mkDerivation K
  invFun D := fun i => D (X i)
  left_inv v := by funext i; exact mkDerivation_X K v i
  right_inv D := MvPolynomial.derivation_ext (fun i => mkDerivation_X K _ i)
  map_add' v w := by apply MvPolynomial.derivation_ext; intro i; simp
  map_smul' a v := by apply MvPolynomial.derivation_ext; intro i; simp

@[simp] theorem polynomialDerivationEquiv_X (v : σ → L) (i : σ) :
    polynomialDerivationEquiv K L σ v (X i) = v i := mkDerivation_X K v i

theorem derivation_sum_apply {ι : Type*} (s : Finset ι)
    (D : ι → Derivation K (MvPolynomial σ K) L) (p : MvPolynomial σ K) :
    (∑i∈s,D i) p = ∑i∈s,D i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp only [Finset.sum_insert ha,Derivation.add_apply,ih]

/-- The polynomial derivation is exactly multiplication by the evaluated
Jacobian row; the evaluation is the given algebra map, not a chosen point. -/
theorem polynomialDerivation_apply [Fintype σ] (v : σ → L) (p : MvPolynomial σ K) :
    polynomialDerivationEquiv K L σ v p =
      ∑ i, algebraMap (MvPolynomial σ K) L (pderiv i p) * v i := by
  classical
  have he : polynomialDerivationEquiv K L σ v =
      ∑ i, v i • (Algebra.linearMap (MvPolynomial σ K) L).compDer (pderiv i) := by
    apply MvPolynomial.derivation_ext
    intro j
    simp [derivation_sum_apply, LinearMap.compDer, pderiv_X, Pi.single_apply]
  rw [he,derivation_sum_apply]
  change (∑ i, v i * algebraMap (MvPolynomial σ K) L (pderiv i p)) = _
  apply Finset.sum_congr rfl
  intro i _
  ring

end Polynomial

section GenericPoint
variable {n c : ℕ} (I : Ideal (GeometricPolynomial n)) [I.IsPrime]

@[simp] theorem genericPointMap_algebraMap (p : GeometricPolynomial n) :
    genericPointMap I p = algebraMap (GeometricPolynomial n) (affineFunctionField I) p := by
  rw [IsScalarTower.algebraMap_apply (GeometricPolynomial n) (affineCoordinateRing I)
    (affineFunctionField I)]
  rfl

/-- Checking a derivation on finite ideal generators is sufficient because
the whole ideal is zero in the target fraction field. -/
theorem annihilates_ideal_iff_generators
    (f : Fin c → GeometricPolynomial n)
    (hf : Submodule.span (GeometricPolynomial n) (Set.range f) = I)
    (D : Derivation GeometricField (GeometricPolynomial n) (affineFunctionField I)) :
    (∀p∈I,D p=0) ↔ ∀i,D (f i)=0 := by
  constructor
  · intro h i
    apply h
    rw [←hf]
    exact Submodule.subset_span ⟨i,rfl⟩
  · intro h p hp
    rw [←hf] at hp
    induction hp using Submodule.span_induction with
    | mem p hp => obtain ⟨i,rfl⟩ := hp; exact h i
    | zero => exact D.map_zero
    | add p q hp hq ihp ihq => exact (D.map_add p q).trans (by rw [ihp,ihq,add_zero])
    | smul a p hp ih =>
      change D (a*p)=0
      rw [D.leibniz,ih,smul_zero,zero_add]
      have hpI : p ∈ I := hf ▸ hp
      have he : algebraMap (GeometricPolynomial n) (affineFunctionField I) p = 0 := by
        rw [←genericPointMap_algebraMap I]
        exact (ReducedGenericRank.genericPointMap_eq_zero_iff I p).mpr hpI
      rw [Algebra.smul_def,he,zero_mul]

/-- Values on the coordinate variables identify the generic Jacobian
kernel with all ideal-annihilating derivations upstairs. -/
def genericJacobianAnnihilatorEquiv (f : Fin c → GeometricPolynomial n)
    (hf : Submodule.span (GeometricPolynomial n) (Set.range f) = I) :
    LinearMap.ker (genericMatrix I (jacobian f)).mulVecLin ≃ₗ[affineFunctionField I]
      annihilatingDerivations GeometricField (GeometricPolynomial n) (affineFunctionField I) I := by
  let E := polynomialDerivationEquiv GeometricField (affineFunctionField I) (Fin n)
  have he (v : Fin n → affineFunctionField I) (i : Fin c) :
      E v (f i) = ((genericMatrix I (jacobian f)).mulVec v) i := by
    rw [polynomialDerivation_apply]
    simp only [genericMatrix,jacobian,Matrix.mulVec,dotProduct,Matrix.map_apply,
      genericPointMap_algebraMap]
  have hv (v : Fin n → affineFunctionField I) :
      v ∈ LinearMap.ker (genericMatrix I (jacobian f)).mulVecLin ↔
        E v ∈ annihilatingDerivations GeometricField (GeometricPolynomial n) (affineFunctionField I) I := by
    change (genericMatrix I (jacobian f)).mulVec v=0 ↔ ∀p∈I,E v p=0
    rw [annihilates_ideal_iff_generators I f hf]
    simp only [he,funext_iff,Pi.zero_apply]
  exact E.submoduleMap (LinearMap.ker (genericMatrix I (jacobian f)).mulVecLin) |>.trans
    (LinearEquiv.ofEq _ _ (by
      ext D
      constructor
      · rintro ⟨v,hv',rfl⟩
        exact (hv v).mp hv'
      · intro hD
        exact ⟨E.symm D,(hv (E.symm D)).mpr (by simpa using hD),E.apply_symm_apply D⟩))

/-- The generic tangent vector space is the derivation space of the actual
coordinate quotient, as a vector space over its actual fraction field. -/
def genericJacobianDerivationEquiv (f : Fin c → GeometricPolynomial n)
    (hf : Submodule.span (GeometricPolynomial n) (Set.range f) = I) :
    LinearMap.ker (genericMatrix I (jacobian f)).mulVecLin ≃ₗ[affineFunctionField I]
      Derivation GeometricField (affineCoordinateRing I) (affineFunctionField I) :=
  (genericJacobianAnnihilatorEquiv I f hf).trans
    (quotientDerivationEquiv GeometricField (GeometricPolynomial n) (affineFunctionField I) I).symm

/-- The missing generic tangent dimension identity is now proved from the
actual Jacobian and the actual prime coordinate ideal. -/
theorem generic_jacobian_dimension (f : Fin c → GeometricPolynomial n)
    (hf : Submodule.span (GeometricPolynomial n) (Set.range f) = I) :
    ringKrullDim (affineCoordinateRing I) =
      ((n - genericMatrixRank I (jacobian f) : ℕ) : Dimension) := by
  have hd := krull_dimension_eq_derivation_finrank (affineCoordinateRing I)
  rw [←(genericJacobianDerivationEquiv I f hf).finrank_eq] at hd
  have he := (genericMatrix I (jacobian f)).mulVecLin.finrank_range_add_finrank_ker
  change genericMatrixRank I (jacobian f) +
    finrank (affineFunctionField I) (LinearMap.ker (genericMatrix I (jacobian f)).mulVecLin) = _ at he
  simp only [Module.finrank_pi_fintype,Module.finrank_self,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at he
  have hn : finrank (affineFunctionField I)
      (LinearMap.ker (genericMatrix I (jacobian f)).mulVecLin) = n - genericMatrixRank I (jacobian f) := by omega
  exact hd.trans (congrArg (fun d : ℕ => (d : Dimension)) hn)

end GenericPoint

end HessianTheorem11.UnconditionalGeneric

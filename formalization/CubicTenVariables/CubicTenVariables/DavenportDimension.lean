import CubicTenVariables.DavenportTangent
import HessianTheorem11.UnconditionalGenericJacobianDerivation
import TranslatedDepthSeven.FieldPolynomialKrullDimension
import TranslatedDepthSeven.PrimeAffineNoetherNormalization
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
Rational coordinate-ring dimension bounds for Hessian rank loci.
The argument uses actual vanishing ideals, their rational tangent spaces,
and prime coordinate rings. No closure/dimension package is assumed.
-/
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 300000
namespace CubicTenVariables.DavenportDimension
open MvPolynomial HessianTheorem11 Module
open HessianTheorem11.UnconditionalGeneric

abbrev coordinateRing {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ)) :=
  MvPolynomial (Fin n) ℚ ⧸ I
abbrev functionField {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ)) :=
  FractionRing (coordinateRing I)

def genericMap {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ)) :
    MvPolynomial (Fin n) ℚ →+* functionField I :=
  (algebraMap (coordinateRing I) (functionField I)).comp (Ideal.Quotient.mk I)

@[simp] theorem genericMap_eq_algebraMap {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℚ)) (p : MvPolynomial (Fin n) ℚ) :
    genericMap I p = algebraMap (MvPolynomial (Fin n) ℚ) (functionField I) p := by
  rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) ℚ)
    (coordinateRing I) (functionField I)]
  rfl

@[simp] theorem genericMap_eq_zero_iff {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℚ)) [I.IsPrime] (p : MvPolynomial (Fin n) ℚ) :
    genericMap I p = 0 ↔ p ∈ I := by
  change algebraMap (coordinateRing I) (functionField I) (Ideal.Quotient.mk I p) = 0 ↔ _
  rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

/-- The dimension/differential identity over the rational ground field,
using the proved field-case polynomial dimension theorem. -/
theorem dimension_eq_derivation_finrank (A : Type*) [CommRing A] [IsDomain A]
    [Algebra ℚ A] [Algebra.FiniteType ℚ A] :
    ringKrullDim A = (finrank (FractionRing A)
      (Derivation ℚ A (FractionRing A)) : WithBot ℕ∞) := by
  obtain ⟨d, g, hg, hint, ⟨b⟩⟩ := exists_normalization_differential_basis ℚ A
  letI : FiniteDimensional (FractionRing A)
      (KaehlerDifferential ℚ (FractionRing A)) := Module.Finite.of_basis b
  rw [derivation_finrank_eq_differential_finrank,
    finrank_eq_card_basis b, Fintype.card_fin]
  letI : Algebra (MvPolynomial (Fin d) ℚ) A := g.toAlgebra
  letI : Algebra.IsIntegral (MvPolynomial (Fin d) ℚ) A := ⟨hint⟩
  exact (TranslatedDepthSeven.ringKrullDim_eq_of_isIntegral_injective hg).trans
    (TranslatedDepthSeven.ringKrullDim_mvPolynomial_fin_eq_of_field ℚ d)

/-- A finite generating family presents all reduced rational tangent spaces. -/
theorem exists_tangent_equations {n : ℕ} (Z : Set (Fin n → ℚ)) :
    ∃ (c : ℕ) (f : Fin c → MvPolynomial (Fin n) ℚ),
      (∀ i, f i ∈ vanishingIdeal ℚ Z) ∧
      ∀ x ∈ Z, affineTangentSpace Z x =
        LinearMap.ker (Matrix.mulVecLin (fun i j => eval x (pderiv j (f i)))) := by
  obtain ⟨c, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (vanishingIdeal ℚ Z))
  have hmem (i) : f i ∈ vanishingIdeal ℚ Z := by
    rw [← hf]
    exact Submodule.subset_span ⟨i, rfl⟩
  refine ⟨c, f, hmem, ?_⟩
  intro x hx
  ext v
  constructor
  · intro hv
    apply LinearMap.mem_ker.mpr
    ext i
    simpa only [polynomialDifferential_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec, dotProduct, Pi.zero_apply] using
      mem_affineTangentSpace.mp hv (f i) (hmem i)
  · intro hv
    apply mem_affineTangentSpace.mpr
    intro p hp
    rw [← hf] at hp
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨i, rfl⟩ := hp
      simpa only [polynomialDifferential_apply, Matrix.mulVecLin_apply,
        Matrix.mulVec, dotProduct, Pi.zero_apply] using
        congrFun (LinearMap.mem_ker.mp hv) i
    | zero => simp [polynomialDifferential_apply]
    | add p q hp hq ihp ihq =>
      simpa only [polynomialDifferential_apply, map_add, Derivation.map_add,
        add_mul, Finset.sum_add_distrib, add_zero] using congrArg₂ (· + ·) ihp ihq
    | smul a p hp ih =>
      change polynomialDifferential (a * p) x v = 0
      have hpZ : p ∈ vanishingIdeal ℚ Z := hf ▸ hp
      have he : eval x p = 0 := hpZ x hx
      have hm : polynomialDifferential (a * p) x v =
          eval x p * polynomialDifferential a x v +
          eval x a * polynomialDifferential p x v := by
        simp only [polynomialDifferential_apply, Derivation.leibniz, smul_eq_mul,
          map_add, map_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
        rw [add_comm]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
      rw [hm, he, ih]
      ring

/-- Specialization cannot increase the rank of an actual polynomial matrix. -/
theorem specialization_rank_le {n a b : ℕ}
    (P : Ideal (MvPolynomial (Fin n) ℚ)) [P.IsPrime]
    (M : Matrix (Fin a) (Fin b) (MvPolynomial (Fin n) ℚ))
    (x : Fin n → ℚ) (hx : x ∈ zeroLocus ℚ P) :
    (M.map (eval x)).rank ≤ (M.map (genericMap P)).rank := by
  by_contra h
  obtain ⟨rows, cols, hdet⟩ := MatrixRankMinors.exists_rank_minor (M.map (eval x))
  let p := (M.submatrix rows cols).det
  have hsub := PolynomialSchurVanishing.rank_submatrix_le (M.map (genericMap P)) rows cols
  have hzero : ((M.map (genericMap P)).submatrix rows cols).det = 0 :=
    PolynomialSchurVanishing.det_eq_zero_of_rank_lt _
      (by simpa only [Fintype.card_fin] using hsub.trans_lt (lt_of_not_ge h))
  have hp : genericMap P p = 0 := by
    rw [show genericMap P p = genericMap P (M.submatrix rows cols).det from rfl,
      RingHom.map_det]
    exact hzero
  have he := hx p ((genericMap_eq_zero_iff P p).mp hp)
  change eval x p = 0 at he
  apply hdet
  rw [show eval x p = (eval x) (M.submatrix rows cols).det from rfl,
    RingHom.map_det] at he
  exact he

/-- Generic derivations inject into the kernel of any Jacobian formed from
polynomials in the prime ideal. -/
def derivationToJacobianKernel {n c : ℕ}
    (P : Ideal (MvPolynomial (Fin n) ℚ)) [P.IsPrime]
    (f : Fin c → MvPolynomial (Fin n) ℚ) (hf : ∀ i, f i ∈ P) :
    Derivation ℚ (coordinateRing P) (functionField P) →ₗ[functionField P]
      LinearMap.ker (Matrix.mulVecLin (fun i j => genericMap P (pderiv j (f i)))) where
  toFun D := ⟨fun i => D (Ideal.Quotient.mk P (X i)), by
    apply LinearMap.mem_ker.mpr
    ext i
    have he : polynomialDerivationEquiv ℚ (functionField P) (Fin n)
        (fun j => D (Ideal.Quotient.mk P (X j))) =
        D.compAlgebraMap (MvPolynomial (Fin n) ℚ) := by
      apply MvPolynomial.derivation_ext
      intro j
      simp only [polynomialDerivationEquiv_X, Derivation.compAlgebraMap_apply]
      rfl
    have hv := congrArg (fun d : Derivation ℚ (MvPolynomial (Fin n) ℚ)
      (functionField P) => d (f i)) he
    dsimp only at hv
    rw [polynomialDerivation_apply] at hv
    change (∑ j, algebraMap (MvPolynomial (Fin n) ℚ) (functionField P)
      (pderiv j (f i)) * D (Ideal.Quotient.mk P (X j))) =
      D (Ideal.Quotient.mk P (f i)) at hv
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hf i), map_zero] at hv
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      genericMap_eq_algebraMap, Pi.zero_apply] using hv⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem derivationToJacobianKernel_injective {n c : ℕ}
    (P : Ideal (MvPolynomial (Fin n) ℚ)) [P.IsPrime]
    (f : Fin c → MvPolynomial (Fin n) ℚ) (hf : ∀ i, f i ∈ P) :
    Function.Injective (derivationToJacobianKernel P f hf) := by
  intro D E h
  have hv := congrArg Subtype.val h
  have he : D.compAlgebraMap (MvPolynomial (Fin n) ℚ) =
      E.compAlgebraMap (MvPolynomial (Fin n) ℚ) := by
    apply MvPolynomial.derivation_ext
    intro i
    exact congrFun hv i
  apply Derivation.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact Derivation.congr_fun he p

/-- Each rational point on a prime component bounds that component's Krull
dimension by the reduced tangent dimension of the entire rational set. -/
theorem prime_dimension_le_tangent_finrank {n : ℕ}
    (Z : Set (Fin n → ℚ)) (P : Ideal (MvPolynomial (Fin n) ℚ)) [P.IsPrime]
    (hIP : vanishingIdeal ℚ Z ≤ P) (x : Fin n → ℚ)
    (hx : x ∈ Z) (hxP : x ∈ zeroLocus ℚ P) :
    ringKrullDim (coordinateRing P) ≤
      (finrank ℚ (affineTangentSpace Z x) : WithBot ℕ∞) := by
  obtain ⟨c, f, hf, hker⟩ := exists_tangent_equations Z
  let M : Matrix (Fin c) (Fin n) (MvPolynomial (Fin n) ℚ) := fun i j => pderiv j (f i)
  have hd := dimension_eq_derivation_finrank (coordinateRing P)
  have hi := LinearMap.finrank_le_finrank_of_injective
    (derivationToJacobianKernel_injective P f (fun i => hIP (hf i)))
  have hs := specialization_rank_le P M x hxP
  have hg := (M.map (genericMap P)).mulVecLin.finrank_range_add_finrank_ker
  have hxrank := (M.map (eval x)).mulVecLin.finrank_range_add_finrank_ker
  have hfnK : finrank (functionField P) (Fin n → functionField P) = n := by simp
  have hfnQ : finrank ℚ (Fin n → ℚ) = n := by simp
  rw [hfnK] at hg
  rw [hfnQ] at hxrank
  change (M.map (genericMap P)).rank +
    finrank (functionField P) (LinearMap.ker (M.map (genericMap P)).mulVecLin) = n at hg
  change (M.map (eval x)).rank +
    finrank ℚ (LinearMap.ker (M.map (eval x)).mulVecLin) = n at hxrank
  have he : affineTangentSpace Z x = LinearMap.ker (M.map (eval x)).mulVecLin := hker x hx
  rw [hd, he]
  exact_mod_cast (show finrank (functionField P)
      (Derivation ℚ (coordinateRing P) (functionField P)) ≤
      finrank ℚ (LinearMap.ker (M.map (eval x)).mulVecLin) by
    change finrank (functionField P)
      (Derivation ℚ (coordinateRing P) (functionField P)) ≤
      finrank (functionField P) (LinearMap.ker (M.map (genericMap P)).mulVecLin) at hi
    omega)

/-- Every minimal prime of the full vanishing ideal of a rational point set
has an actual point in that set. Finite prime separation proves this directly. -/
theorem exists_point_of_minimalPrime {n : ℕ}
    (Z : Set (Fin n → ℚ)) (P : Ideal (MvPolynomial (Fin n) ℚ))
    (hP : P ∈ (vanishingIdeal ℚ Z).minimalPrimes) :
    ∃ x ∈ Z, x ∈ zeroLocus ℚ P := by
  classical
  let I := vanishingIdeal ℚ Z
  letI : P.IsPrime := hP.1.1
  let s := I.finite_minimalPrimes_of_isNoetherianRing.toFinset.erase P
  have ha (Q : s) : ∃ a : MvPolynomial (Fin n) ℚ, a ∈ Q.val ∧ a ∉ P := by
    have hQ : Q.val ∈ I.minimalPrimes := by
      simpa only [Set.Finite.mem_toFinset] using (Finset.mem_erase.mp Q.property).2
    have hne : Q.val ≠ P := (Finset.mem_erase.mp Q.property).1
    have hnle : ¬ Q.val ≤ P := by
      intro hQP
      exact hne (le_antisymm hQP (hP.2 hQ.1 hQP))
    exact SetLike.not_le_iff_exists.mp hnle
  choose a haQ haP using ha
  let q : MvPolynomial (Fin n) ℚ := ∏ Q : s, a Q
  have hqP : q ∉ P := by
    intro h
    obtain ⟨Q, _, hQ⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact haP Q hQ
  by_contra h
  push_neg at h
  have hqI : q ∈ I := by
    intro x hx
    have hIx : I ≤ RingHom.ker (eval x) := fun f hf => hf x hx
    letI : (RingHom.ker (eval x : MvPolynomial (Fin n) ℚ →+* ℚ)).IsPrime :=
      RingHom.ker_isPrime _
    obtain ⟨Q, hQ, hQx⟩ := Ideal.exists_minimalPrimes_le hIx
    have hQP : Q ≠ P := by
      rintro rfl
      exact h x hx (fun f hf => hQx hf)
    have hQs : Q ∈ s := by
      simp only [s, Finset.mem_erase, Set.Finite.mem_toFinset]
      exact ⟨hQP, hQ⟩
    change eval x q = 0
    dsimp only [q]
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ (⟨Q, hQs⟩ : s))
      (hQx (haQ ⟨Q, hQs⟩))
  exact hqP (hP.1.2 hqI)

/-- Bounding the quotients at the minimal primes bounds the whole quotient.
Each chain of primes is contained above a minimal prime of its first member. -/
theorem quotient_dimension_le_of_minimalPrimes
    {R : Type*} [CommRing R] (I : Ideal R) (r : ℕ)
    (h : ∀ P ∈ I.minimalPrimes, ringKrullDim (R ⧸ P) ≤ (r : WithBot ℕ∞)) :
    ringKrullDim (R ⧸ I) ≤ (r : WithBot ℕ∞) := by
  rw [ringKrullDim_quotient, Order.krullDim]
  apply iSup_le
  intro l
  letI : l.head.val.asIdeal.IsPrime := l.head.val.isPrime
  obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le
    (show I ≤ l.head.val.asIdeal from l.head.property)
  let q : LTSeries (PrimeSpectrum.zeroLocus (R := R) P) :=
    { length := l.length
      toFun := fun i => ⟨(l i).val, hPle.trans (l.head_le i)⟩
      step := fun i => l.step i }
  have hlen : (l.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ P) := by
    rw [ringKrullDim_quotient]
    exact Order.LTSeries.length_le_krullDim q
  exact hlen.trans (h P hP)

/-- A pointwise bound on actual rational tangent spaces bounds the Krull
dimension of the full rational vanishing-ideal quotient. -/
theorem dimension_le_of_tangent_finrank_le {n r : ℕ}
    (Z : Set (Fin n → ℚ))
    (ht : ∀ x ∈ Z, finrank ℚ (affineTangentSpace Z x) ≤ r) :
    ringKrullDim (coordinateRing (vanishingIdeal ℚ Z)) ≤ (r : WithBot ℕ∞) := by
  apply quotient_dimension_le_of_minimalPrimes
  intro P hP
  letI : P.IsPrime := hP.1.1
  obtain ⟨x, hx, hxP⟩ := exists_point_of_minimalPrime Z P hP
  exact (prime_dimension_le_tangent_finrank Z P hP.1.2 x hx hxP).trans
    (by exact_mod_cast ht x hx)

/-- The rational closure of the rank-r Hessian locus of an anisotropic
rational cubic has actual coordinate-ring Krull dimension at most r. -/
theorem rank_locus_dimension_le {n r : ℕ} (F : AnisotropicCubic n) :
    ringKrullDim (MvPolynomial (Fin n) ℚ ⧸
      vanishingIdeal ℚ {x : Fin n → ℚ | (hessian F.polynomial x).rank = r}) ≤
      (r : WithBot ℕ∞) := by
  apply dimension_le_of_tangent_finrank_le
  intro x hx
  exact DavenportTangent.rank_locus_tangent_finrank_le F x hx

/-- The same dimension bound applies to each actual minimal prime component. -/
theorem rank_locus_minimalPrime_dimension_le {n r : ℕ} (F : AnisotropicCubic n)
    (P : Ideal (MvPolynomial (Fin n) ℚ))
    (hP : P ∈ (vanishingIdeal ℚ
      {x : Fin n → ℚ | (hessian F.polynomial x).rank = r}).minimalPrimes) :
    ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ P) ≤ (r : WithBot ℕ∞) := by
  exact (ringKrullDim_le_of_surjective (Ideal.Quotient.factor hP.1.2)
    (Ideal.Quotient.factor_surjective _)).trans (rank_locus_dimension_le F)

end CubicTenVariables.DavenportDimension

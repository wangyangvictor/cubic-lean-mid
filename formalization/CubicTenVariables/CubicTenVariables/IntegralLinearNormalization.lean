import CubicTenVariables.IntegralNormalizationCoordinates
import TranslatedDepthSeven.RationalLocalEquationIntegralization
import TranslatedDepthSeven.FractionFieldFiniteCoefficientClearing

/-! Integral linear normalization certificates for a fixed homogeneous cone.
Every displayed relation belongs to the original integral ideal, before any
prime is inverted. No geometric or arithmetic counting estimate is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
noncomputable section
namespace CubicTenVariables.IntegralLinearNormalization
open MvPolynomial TranslatedDepthSeven HessianTheorem11 PolynomialRestriction
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

variable {n s : ℕ}

/-- The original ideal after extension to rational coefficients. -/
def rationalIdeal (J : Ideal (MvPolynomial (Fin n) ℤ)) : Ideal (MvPolynomial (Fin n) ℚ) :=
  J.map (MvPolynomial.map (Int.castRingHom ℚ))

/-- The integral base coordinates, among the rows of an integral matrix. -/
def baseForms (A : Matrix (Fin n) (Fin n) ℤ) (β : Fin s ↪ Fin n) :
    Fin s → MvPolynomial (Fin n) ℤ := fun i => linearForms A (β i)

/-- The actual coordinate relation substituted in the original variables. -/
def relation (A : Matrix (Fin n) (Fin n) ℤ) (β : Fin s ↪ Fin n)
    (j : Fin n) (P : Polynomial (MvPolynomial (Fin s) ℤ)) : MvPolynomial (Fin n) ℤ :=
  P.eval₂ (aeval (baseForms A β)).toRingHom (linearForms A j)

/-- The rational normalization map uses these same integral rows. -/
def projectionHom (J : Ideal (MvPolynomial (Fin n) ℤ))
    (A : Matrix (Fin n) (Fin n) ℤ) (β : Fin s ↪ Fin n) :
    MvPolynomial (Fin s) ℚ →ₐ[ℚ] (MvPolynomial (Fin n) ℚ ⧸ rationalIdeal J) :=
  (Ideal.Quotient.mkₐ ℚ (rationalIdeal J)).comp
    (aeval (fun i => linearForms (A.map (Int.castRingHom ℚ)) (β i)))

def scaleHom (s : ℕ) (a : ℚ) : MvPolynomial (Fin s) ℚ →ₐ[ℚ] MvPolynomial (Fin s) ℚ :=
  aeval (fun i => C a * X i)

theorem scaleHom_surjective (s : ℕ) (a : ℚ) (ha : a ≠ 0) :
    Function.Surjective (scaleHom s a) := by
  have he : (scaleHom s a).comp (scaleHom s a⁻¹) = AlgHom.id ℚ _ := by
    ext i
    simp [scaleHom, ha]
  intro x
  exact ⟨scaleHom s a⁻¹ x, congrArg (fun f : MvPolynomial (Fin s) ℚ →ₐ[ℚ] _ => f x) he⟩

theorem scaleHom_injective (s : ℕ) (a : ℚ) (ha : a ≠ 0) :
    Function.Injective (scaleHom s a) := by
  have he : (scaleHom s a⁻¹).comp (scaleHom s a) = AlgHom.id ℚ _ := by
    ext i
    simp [scaleHom, ha]
  intro x y h
  have hh := congrArg (scaleHom s a⁻¹) h
  change ((scaleHom s a⁻¹).comp (scaleHom s a)) x =
    ((scaleHom s a⁻¹).comp (scaleHom s a)) y at hh
  simpa only [he, AlgHom.id_apply] using hh

/-- The integral matrix remains an actual finite injective normalization. -/
theorem exists_finite_projection (J : Ideal (MvPolynomial (Fin n) ℤ))
    (D : HomogeneousLinearNormalizationData (rationalIdeal J)) :
    ∃ (A : Matrix (Fin n) (Fin n) ℤ) (β : Fin D.parameterCount ↪ Fin n),
      (A.map (Int.castRingHom ℚ)).det ≠ 0 ∧
      Function.Injective (projectionHom J A β) ∧ (projectionHom J A β).Finite := by
  obtain ⟨A,β,L,hL,hdet,hforms⟩ :=
    IntegralNormalizationCoordinates.exists_integral_matrix (rationalIdeal J) D
  have hLQ : (L : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
  have he : projectionHom J A β = D.hom.comp (scaleHom D.parameterCount L) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [projectionHom,HomogeneousLinearNormalizationData.hom,scaleHom,
      AlgHom.comp_apply,aeval_X,map_mul,aeval_C]
    rw [hforms]
    simp
  refine ⟨A,β,hdet,?_,?_⟩
  · rw [he]
    exact D.hom_injective.comp (scaleHom_injective _ _ hLQ)
  · rw [he]
    exact AlgHom.Finite.comp D.hom_finite
      (AlgHom.Finite.of_surjective _ (scaleHom_surjective _ _ hLQ))

/-- The same integral coordinate maps commute with rational extension. -/
theorem map_linearForms (A : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) :
    MvPolynomial.map (Int.castRingHom ℚ) (linearForms A j) =
      linearForms (A.map (Int.castRingHom ℚ)) j := by
  simp [linearForms]

theorem map_relation (A : Matrix (Fin n) (Fin n) ℤ) (β : Fin s ↪ Fin n)
    (j : Fin n) (P : Polynomial (MvPolynomial (Fin s) ℤ)) :
    MvPolynomial.map (Int.castRingHom ℚ) (relation A β j P) =
      (P.map (MvPolynomial.map (Int.castRingHom ℚ))).eval₂
        (aeval (fun i => linearForms (A.map (Int.castRingHom ℚ)) (β i))).toRingHom
        (linearForms (A.map (Int.castRingHom ℚ)) j) := by
  let φ := MvPolynomial.map (Int.castRingHom ℚ) (σ := Fin n)
  let ψ := MvPolynomial.map (Int.castRingHom ℚ) (σ := Fin s)
  let g : MvPolynomial (Fin s) ℤ →+* MvPolynomial (Fin n) ℤ :=
    (aeval (baseForms A β)).toRingHom
  let gQ : MvPolynomial (Fin s) ℚ →+* MvPolynomial (Fin n) ℚ :=
    (aeval (fun i => linearForms (A.map (Int.castRingHom ℚ)) (β i))).toRingHom
  have hc : φ.comp g = gQ.comp ψ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [φ,ψ,g,gQ]
    · intro i
      simp [φ,ψ,g,gQ,baseForms,map_linearForms]
  change φ (P.eval₂ g _) = (P.map ψ).eval₂ gQ _
  rw [Polynomial.eval₂_map, ← hc]
  rw [← map_linearForms]
  exact Polynomial.hom_eval₂ P g φ _

/-- Clearing a nested polynomial gives a literal scalar multiple, with a
positive scalar independent of evaluation or modulus. -/
theorem exists_integral_polynomial (p : Polynomial (MvPolynomial (Fin s) ℚ)) :
    ∃ (P : Polynomial (MvPolynomial (Fin s) ℤ)) (L : ℕ), 0 < L ∧
      P.map (MvPolynomial.map (Int.castRingHom ℚ)) = Polynomial.C (C (L : ℚ)) * p := by
  let f := (MvPolynomial.optionEquivLeft ℚ (Fin s)).symm p
  refine ⟨MvPolynomial.optionEquivLeft ℤ (Fin s) (clearRationalMvPolynomial f),
    mvPolynomialRationalCommonDenominator f,mvPolynomialRationalCommonDenominator_pos f,?_⟩
  rw [map_optionEquivLeft,map_clearRationalMvPolynomial,map_mul]
  simp [f]

/-- Every transformed coordinate satisfies a positive-degree monic equation
in the selected base rows, in the actual rational quotient. -/
theorem exists_rational_relation (J : Ideal (MvPolynomial (Fin n) ℤ))
    (A : Matrix (Fin n) (Fin n) ℤ) (β : Fin s ↪ Fin n)
    (hf : (projectionHom J A β).Finite) (j : Fin n) :
    ∃ p : Polynomial (MvPolynomial (Fin s) ℚ), p.Monic ∧ 0 < p.natDegree ∧
      p.eval₂ (aeval (fun i => linearForms (A.map (Int.castRingHom ℚ)) (β i))).toRingHom
        (linearForms (A.map (Int.castRingHom ℚ)) j) ∈ rationalIdeal J := by
  let g := projectionHom J A β
  let w := linearForms (A.map (Int.castRingHom ℚ)) j
  obtain ⟨p,hp,hz⟩ := hf.to_isIntegral (Ideal.Quotient.mk (rationalIdeal J) w)
  let q := p * Polynomial.X
  have hq : q.Monic := hp.mul (Polynomial.monic_X)
  have hdeg : 0 < q.natDegree := by
    simp only [q, Polynomial.natDegree_mul hp.ne_zero Polynomial.X_ne_zero,
      Polynomial.natDegree_X]
    omega
  refine ⟨q,hq,hdeg,?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hzero : q.eval₂ g.toRingHom (Ideal.Quotient.mk (rationalIdeal J) w) = 0 := by
    simp only [q, g, Polynomial.eval₂_mul, hz, zero_mul]
  rw [← hzero]
  exact Polynomial.hom_eval₂ q _ (Ideal.Quotient.mk (rationalIdeal J)) w

/-- A rational relation becomes an original-ideal relation, with a positive
constant leading coefficient. No prime or modulus is excluded. -/
theorem exists_integral_relation (J : Ideal (MvPolynomial (Fin n) ℤ))
    (A : Matrix (Fin n) (Fin n) ℤ) (β : Fin s ↪ Fin n)
    (hf : (projectionHom J A β).Finite) (j : Fin n) :
    ∃ (P : Polynomial (MvPolynomial (Fin s) ℤ)) (c : ℕ),
      0 < c ∧ 0 < P.natDegree ∧ P.leadingCoeff = C (c : ℤ) ∧ relation A β j P ∈ J := by
  obtain ⟨p,hp,hpdeg,hmem⟩ := exists_rational_relation J A β hf j
  obtain ⟨P,L,hL,hP⟩ := exists_integral_polynomial p
  have hi : Function.Injective (MvPolynomial.map (Int.castRingHom ℚ) (σ := Fin s)) :=
    MvPolynomial.map_injective _ Int.cast_injective
  have hLC : (C (L : ℚ) : MvPolynomial (Fin s) ℚ) ≠ 0 := by
    exact C_ne_zero.mpr (by exact_mod_cast hL.ne')
  have hdeg : P.natDegree = p.natDegree := by
    rw [← Polynomial.natDegree_map_eq_of_injective hi P,hP,Polynomial.natDegree_C_mul hLC]
  have hlead : P.leadingCoeff = C (L : ℤ) := by
    apply hi
    have he := congrArg Polynomial.leadingCoeff hP
    rw [Polynomial.leadingCoeff_map_of_injective hi,Polynomial.leadingCoeff_mul,
      Polynomial.leadingCoeff_C,hp.leadingCoeff,mul_one] at he
    simpa only [MvPolynomial.map_C, Int.cast_natCast] using he
  have hmapmem : MvPolynomial.map (Int.castRingHom ℚ) (relation A β j P) ∈ rationalIdeal J := by
    rw [map_relation,hP,Polynomial.eval₂_mul,Polynomial.eval₂_C]
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C] using
      (rationalIdeal J).mul_mem_left (C (L : ℚ)) hmem
  obtain ⟨d,hd,hint⟩ := exists_nonzero_int_C_mul_mem_of_map_intCast_mem J (relation A β j P) hmapmem
  let R := Polynomial.C (C (d ^ 2)) * P
  have hdC : (C (d ^ 2) : MvPolynomial (Fin s) ℤ) ≠ 0 := C_ne_zero.mpr (pow_ne_zero _ hd)
  have hdpos : 0 < d.natAbs := Int.natAbs_pos.mpr hd
  refine ⟨R,d.natAbs^2 * L,Nat.mul_pos (pow_pos hdpos _) hL,?_,?_,?_⟩
  · simpa only [R,Polynomial.natDegree_C_mul hdC,hdeg] using hpdeg
  · simp only [R,Polynomial.leadingCoeff_mul,Polynomial.leadingCoeff_C,hlead,← C_mul]
    congr 1
    simp only [Nat.cast_mul, Nat.cast_pow, Int.natAbs_sq]
  · have hh := J.mul_mem_left (C d) hint
    simpa only [R,relation,Polynomial.eval₂_mul,Polynomial.eval₂_C,AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe,aeval_C,pow_two, map_mul,mul_assoc] using hh

/-- Fixed integral data sufficient for all translated squarefree-modulus
sieve applications. No equality with the enlarged relation locus is asserted. -/
structure Certificate (J : Ideal (MvPolynomial (Fin n) ℤ)) (r : ℕ) where
  parameterCount : ℕ
  parameterCount_le : parameterCount ≤ r
  ambient_le : parameterCount ≤ n
  matrix : Matrix (Fin n) (Fin n) ℤ
  base : Fin parameterCount ↪ Fin n
  determinant_ne_zero : (matrix.map (Int.castRingHom ℚ)).det ≠ 0
  projection_injective : Function.Injective (projectionHom J matrix base)
  projection_finite : (projectionHom J matrix base).Finite
  leading : ℕ
  leading_pos : 0 < leading
  degreeBound : ℕ
  degreeBound_pos : 0 < degreeBound
  polynomial : Fin n → Polynomial (MvPolynomial (Fin parameterCount) ℤ)
  degree_pos : ∀ j, 0 < (polynomial j).natDegree
  degree_le : ∀ j, (polynomial j).natDegree ≤ degreeBound
  leadingCoeff_eq : ∀ j, (polynomial j).leadingCoeff = C (leading : ℤ)
  relation_mem : ∀ j, relation matrix base j (polynomial j) ∈ J

/-- The original proper homogeneous rational cone yields an integral square
coordinate matrix and certificates in its original integral ideal. -/
theorem exists_certificate (J : Ideal (MvPolynomial (Fin n) ℤ))
    (hproper : rationalIdeal J ≠ ⊤)
    (hhom : (rationalIdeal J).IsHomogeneous (homogeneousSubmodule (Fin n) ℚ))
    (r : ℕ) (hdim : ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ rationalIdeal J) ≤
      (r : WithBot ℕ∞)) : Nonempty (Certificate J r) := by
  classical
  obtain ⟨D,hD⟩ := ProperHomogeneousNormalization.exists_homogeneousLinearNormalizationData_parameterCount_le
    n (rationalIdeal J) hproper hhom r hdim
  obtain ⟨A,β,hdet,hinj,hfinite⟩ := exists_finite_projection J D
  choose P c hc hdeg hlead hmem using exists_integral_relation J A β hfinite
  let C₀ := ∏ j, c j
  let b (j : Fin n) := ∏ i ∈ Finset.univ.erase j, c i
  have hb (j : Fin n) : 0 < b j := Finset.prod_pos (fun i _ => hc i)
  have hbc (j : Fin n) : b j * c j = C₀ := by
    exact Finset.prod_erase_mul Finset.univ (fun i => c i) (Finset.mem_univ j)
  let R (j : Fin n) := Polynomial.C (C (b j : ℤ)) * P j
  have hRdeg (j : Fin n) : (R j).natDegree = (P j).natDegree := by
    apply Polynomial.natDegree_C_mul
    exact C_ne_zero.mpr (by exact_mod_cast (hb j).ne')
  refine ⟨{
    parameterCount := D.parameterCount
    parameterCount_le := hD
    ambient_le := by simpa using Fintype.card_le_of_injective β β.injective
    matrix := A
    base := β
    determinant_ne_zero := hdet
    projection_injective := hinj
    projection_finite := hfinite
    leading := C₀
    leading_pos := Finset.prod_pos (fun i _ => hc i)
    degreeBound := max 1 (Finset.univ.sup fun j => (P j).natDegree)
    degreeBound_pos := lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)
    polynomial := R
    degree_pos := fun j => by rw [hRdeg]; exact hdeg j
    degree_le := fun j => by rw [hRdeg]; exact (Finset.le_sup (f := fun j => (P j).natDegree)
      (Finset.mem_univ j)).trans (le_max_right _ _)
    leadingCoeff_eq := ?_
    relation_mem := ?_ }⟩
  · intro j
    simp only [R,Polynomial.leadingCoeff_mul,Polynomial.leadingCoeff_C,hlead,← C_mul]
    congr 1
    exact_mod_cast hbc j
  · intro j
    simpa only [R,relation,Polynomial.eval₂_mul,Polynomial.eval₂_C,AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe,aeval_C] using J.mul_mem_left (C (b j : ℤ)) (hmem j)

/-- Evaluation of the original relation is exactly evaluation of the
univariate polynomial on the transformed base and distinguished coordinate. -/
theorem eval₂_relation {K : Type*} [CommRing K]
    (A : Matrix (Fin n) (Fin n) ℤ) (β : Fin s ↪ Fin n) (j : Fin n)
    (P : Polynomial (MvPolynomial (Fin s) ℤ)) (x : Fin n → K) :
    eval₂ (Int.castRingHom K) x (relation A β j P) =
      P.eval₂ (eval₂Hom (Int.castRingHom K)
        (fun i => (A.map (Int.castRingHom K)).mulVec x (β i)))
        ((A.map (Int.castRingHom K)).mulVec x j) := by
  let φ : MvPolynomial (Fin n) ℤ →+* K := eval₂Hom (Int.castRingHom K) x
  let g : MvPolynomial (Fin s) ℤ →+* MvPolynomial (Fin n) ℤ :=
    (aeval (baseForms A β)).toRingHom
  have hform (i : Fin n) : φ (linearForms A i) = (A.map (Int.castRingHom K)).mulVec x i := by
    simp only [φ,linearForms,map_sum,map_mul,eval₂Hom_C,eval₂Hom_X',
      Matrix.mulVec,dotProduct,Matrix.map_apply]
  have hc : φ.comp g = eval₂Hom (Int.castRingHom K)
      (fun i => (A.map (Int.castRingHom K)).mulVec x (β i)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [φ,g]
    · intro i
      change φ (aeval (baseForms A β) (X i)) = _
      rw [aeval_X]
      change φ (linearForms A (β i)) = _
      rw [hform]
      simp
  change φ (P.eval₂ g _) = _
  rw [← hc, ← hform j]
  exact Polynomial.hom_eval₂ P g φ _

/-- The same certificate works over every commutative coefficient ring.
In particular this includes ZMod q for every q, with no good-prime condition. -/
theorem Certificate.specializes {J : Ideal (MvPolynomial (Fin n) ℤ)} {r : ℕ}
    (D : Certificate J r) {K : Type*} [CommRing K] (x : Fin n → K)
    (hx : ∀ f ∈ J, eval₂ (Int.castRingHom K) x f = 0) (j : Fin n) :
    (D.polynomial j).eval₂ (eval₂Hom (Int.castRingHom K)
      (fun i => (D.matrix.map (Int.castRingHom K)).mulVec x (D.base i)))
      ((D.matrix.map (Int.castRingHom K)).mulVec x j) = 0 := by
  rw [← eval₂_relation]
  exact hx _ (D.relation_mem j)

/-- The displayed integral matrix is injective on the full integer lattice;
no coprimality with its determinant is needed. -/
theorem Certificate.matrix_injective {J : Ideal (MvPolynomial (Fin n) ℤ)} {r : ℕ}
    (D : Certificate J r) : Function.Injective D.matrix.mulVec := by
  have hi : Function.Injective (D.matrix.map (Int.castRingHom ℚ)).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr D.determinant_ne_zero))
  intro x y hxy
  have he : (D.matrix.map (Int.castRingHom ℚ)).mulVec (fun i => (x i : ℚ)) =
      (D.matrix.map (Int.castRingHom ℚ)).mulVec (fun i => (y i : ℚ)) := by
    ext i
    have h := congrArg (Int.castRingHom ℚ) (congrFun hxy i)
    simpa only [Matrix.mulVec,dotProduct,map_sum,map_mul,Matrix.map_apply] using h
  have he' := hi he
  ext i
  exact Int.cast_injective (congrFun he' i)

/-- The integral projection also exposes the already-proved uniform finite
fiber/translated-box APIs through their original normalization data type. -/
def Certificate.normalizationData {J : Ideal (MvPolynomial (Fin n) ℤ)} {r : ℕ}
    (D : Certificate J r) : HomogeneousLinearNormalizationData (rationalIdeal J) where
  parameterCount := D.parameterCount
  forms := fun i => linearForms (D.matrix.map (Int.castRingHom ℚ)) (D.base i)
  forms_isHomogeneous := fun _ => homogeneous_linearForms _ _
  injective := D.projection_injective
  finite := D.projection_finite

end CubicTenVariables.IntegralLinearNormalization

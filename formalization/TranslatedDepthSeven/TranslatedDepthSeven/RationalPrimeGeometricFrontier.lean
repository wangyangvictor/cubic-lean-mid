import TranslatedDepthSeven.QbarCoefficientExtension
import TranslatedDepthSeven.QbarInvariantIdealDescent
import TranslatedDepthSeven.CoefficientExtensionHomogeneousIdeal
import TranslatedDepthSeven.HomogeneousMinimalComponents
import TranslatedDepthSeven.FiniteComponentFrontier
import TranslatedDepthSeven.GaloisInvariantComponentPointDescent
import TranslatedDepthSeven.HomogeneousLinearNormalizationBoxCount

/-!
# A rational frontier for geometrically reducible prime ideals

Let `Q` be a prime homogeneous ideal over `ℚ`.  If its coefficient
extension to `Qbar` is reducible, every rational point of `Q` lies on one
fixed, explicitly defined, homogeneous rational ideal strictly containing
`Q`.  The construction takes the sum of all Galois conjugates of each
geometric minimal component, contracts those orbit ideals to `ℚ`, and then
intersects the finitely many contractions.

This is the ideal-level replacement for a point-dependent choice of a
conjugate component.  In particular, every minimal prime of the resulting
rational ideal has strictly smaller quotient Krull dimension than `Q`.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {σ : Type u}

private abbrev coeffMap : MvPolynomial σ ℚ →+* MvPolynomial σ Qbar :=
  MvPolynomial.map (algebraMap ℚ Qbar)

/-- Applying two coefficient automorphisms successively applies their
composition. -/
theorem conjugatePolynomial_trans
    (g h : Qbar ≃ₐ[ℚ] Qbar) (f : MvPolynomial σ Qbar) :
    conjugatePolynomial h (conjugatePolynomial g f) =
      conjugatePolynomial (g.trans h) f := by
  ext m
  simp only [conjugatePolynomial_apply, MvPolynomial.coeff_map]
  rfl

/-- Ideal conjugation has the same composition law. -/
theorem conjugateIdeal_trans
    (g h : Qbar ≃ₐ[ℚ] Qbar) (P : Ideal (MvPolynomial σ Qbar)) :
    conjugateIdeal h (conjugateIdeal g P) =
      conjugateIdeal (g.trans h) P := by
  rw [conjugateIdeal, conjugateIdeal, conjugateIdeal, Ideal.map_map]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [RingHom.comp_apply, conjugatePolynomial_apply]
  · intro i
    simp [RingHom.comp_apply, conjugatePolynomial_apply]

/-- The sum of the complete coefficientwise Galois orbit of `P`. -/
def galoisOrbitSupIdeal (P : Ideal (MvPolynomial σ Qbar)) :
    Ideal (MvPolynomial σ Qbar) :=
  ⨆ g : Qbar ≃ₐ[ℚ] Qbar, conjugateIdeal g P

@[simp]
theorem conjugateIdeal_refl (P : Ideal (MvPolynomial σ Qbar)) :
    conjugateIdeal (AlgEquiv.refl : Qbar ≃ₐ[ℚ] Qbar) P = P := by
  have hmap : (conjugatePolynomial
      (AlgEquiv.refl : Qbar ≃ₐ[ℚ] Qbar)).toRingHom =
      RingHom.id (MvPolynomial σ Qbar) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [conjugatePolynomial_apply]
    · intro i
      simp [conjugatePolynomial_apply]
  rw [conjugateIdeal, hmap, Ideal.map_id]

theorem le_galoisOrbitSupIdeal (P : Ideal (MvPolynomial σ Qbar)) :
    P ≤ galoisOrbitSupIdeal P := by
  have hle := le_iSup
    (fun g : Qbar ≃ₐ[ℚ] Qbar ↦ conjugateIdeal g P)
      (AlgEquiv.refl : Qbar ≃ₐ[ℚ] Qbar)
  simpa only [conjugateIdeal_refl, galoisOrbitSupIdeal] using hle

/-- The complete orbit sum is invariant under every coefficient
automorphism. -/
theorem conjugateIdeal_galoisOrbitSupIdeal
    (h : Qbar ≃ₐ[ℚ] Qbar) (P : Ideal (MvPolynomial σ Qbar)) :
    conjugateIdeal h (galoisOrbitSupIdeal P) =
      galoisOrbitSupIdeal P := by
  rw [conjugateIdeal, galoisOrbitSupIdeal, Ideal.map_iSup]
  change (⨆ g, conjugateIdeal h (conjugateIdeal g P)) = _
  simp_rw [conjugateIdeal_trans]
  apply le_antisymm
  · apply iSup_le
    intro g
    exact le_iSup (fun k : Qbar ≃ₐ[ℚ] Qbar ↦ conjugateIdeal k P)
      (g.trans h)
  · apply iSup_le
    intro g
    have hle := le_iSup
      (fun k : Qbar ≃ₐ[ℚ] Qbar ↦ conjugateIdeal (k.trans h) P)
      (g.trans h.symm)
    have heq : (g.trans h.symm).trans h = g := by
      ext x
      exact h.apply_symm_apply (g x)
    rw [heq] at hle
    exact hle

/-- The rational contraction of the complete Galois-orbit sum. -/
def rationalOrbitIdeal (P : Ideal (MvPolynomial σ Qbar)) :
    Ideal (MvPolynomial σ ℚ) :=
  (galoisOrbitSupIdeal P).comap coeffMap

/-- Extending the rational orbit ideal back to `Qbar` recovers the orbit
sum exactly. -/
theorem map_rationalOrbitIdeal_eq
    [Fintype σ]
    (P : Ideal (MvPolynomial σ Qbar)) :
    (rationalOrbitIdeal P).map coeffMap = galoisOrbitSupIdeal P := by
  exact map_rationalContraction_eq_of_galoisInvariant _
    (fun g ↦ conjugateIdeal_galoisOrbitSupIdeal g P)

/-- Homogeneity is preserved by taking the complete orbit sum. -/
theorem galoisOrbitSupIdeal_isHomogeneous
    (P : Ideal (MvPolynomial σ Qbar))
    (hP : P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ Qbar)) :
    (galoisOrbitSupIdeal P).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ Qbar) := by
  apply Ideal.IsHomogeneous.iSup
  intro g
  exact isHomogeneous_map_mvPolynomialMap g.toRingHom P hP

/-- The rational orbit ideal is homogeneous whenever the chosen geometric
component is homogeneous. -/
theorem rationalOrbitIdeal_isHomogeneous
    [Fintype σ]
    (P : Ideal (MvPolynomial σ Qbar))
    (hP : P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ Qbar)) :
    (rationalOrbitIdeal P).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ ℚ) := by
  exact rationalContraction_isHomogeneous _
    (galoisOrbitSupIdeal_isHomogeneous P hP)

/-- A rational point on `P` lies on the rational contraction of the sum of
all conjugates of `P`. -/
theorem rationalPoint_mem_rationalOrbitIdeal
    (P : Ideal (MvPolynomial σ Qbar)) (x : σ → ℚ)
    (hx : P ≤ RingHom.ker (MvPolynomial.eval
      (fun i ↦ algebraMap ℚ Qbar (x i)))) :
    x ∈ affineIdealZeroLocus (rationalOrbitIdeal P) := by
  rw [mem_affineIdealZeroLocus_iff]
  intro f hf
  have horbitKernel : galoisOrbitSupIdeal P ≤
      RingHom.ker (MvPolynomial.eval
        (fun i ↦ algebraMap ℚ Qbar (x i))) := by
    apply iSup_le
    intro g
    exact conjugateIdeal_le_rationalEvaluationKernel g P x hx
  have hmap : coeffMap f ∈ galoisOrbitSupIdeal P := hf
  have hzeroQbar : MvPolynomial.eval
      (fun i ↦ algebraMap ℚ Qbar (x i)) (coeffMap f) = 0 :=
    RingHom.mem_ker.mp (horbitKernel hmap)
  rw [eval_coefficientExtension_at_rationalPoint] at hzeroQbar
  exact (map_eq_zero_iff (algebraMap ℚ Qbar)
    (FaithfulSMul.algebraMap_injective ℚ Qbar)).mp hzeroQbar

/-! ## The finite rational frontier -/

/-- Literal coefficient extension of a rational ideal to `Qbar`. -/
def qbarCoefficientExtensionIdeal
    (Q : Ideal (MvPolynomial σ ℚ)) :
    Ideal (MvPolynomial σ Qbar) :=
  Q.map coeffMap

/-- The finite intersection of the rational orbit ideals belonging to all
geometric minimal components. -/
def rationalGeometricFrontierIdeal
    [Fintype σ]
    (Q : Ideal (MvPolynomial σ ℚ)) :
    Ideal (MvPolynomial σ ℚ) :=
  (finiteMinimalPrimes (qbarCoefficientExtensionIdeal Q)).inf
    rationalOrbitIdeal

/-- The coefficient extension of a homogeneous rational ideal is
homogeneous. -/
theorem qbarCoefficientExtensionIdeal_isHomogeneous
    (Q : Ideal (MvPolynomial σ ℚ))
    (hQ : Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ ℚ)) :
    (qbarCoefficientExtensionIdeal Q).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ Qbar) := by
  exact isHomogeneous_map_mvPolynomialMap
    (algebraMap ℚ Qbar) Q hQ

/-- A geometric minimal component of a homogeneous coefficient extension
is homogeneous. -/
theorem qbarMinimalComponent_isHomogeneous
    [Fintype σ]
    (Q : Ideal (MvPolynomial σ ℚ))
    (hQ : Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ ℚ))
    (P : Ideal (MvPolynomial σ Qbar))
    (hP : P ∈ finiteMinimalPrimes
      (qbarCoefficientExtensionIdeal Q)) :
    P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ Qbar) := by
  apply isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous
    (qbarCoefficientExtensionIdeal_isHomogeneous Q hQ)
  exact (mem_finiteMinimalPrimes_iff _ _).mp hP

/-- The frontier contains the original rational ideal: this direction uses
only that every minimal component contains the coefficient extension. -/
theorem le_rationalOrbitIdeal_of_mem_qbarMinimalPrimes
    [Fintype σ]
    (Q : Ideal (MvPolynomial σ ℚ))
    (P : Ideal (MvPolynomial σ Qbar))
    (hP : P ∈ finiteMinimalPrimes
      (qbarCoefficientExtensionIdeal Q)) :
    Q ≤ rationalOrbitIdeal P := by
  change Q ≤ (galoisOrbitSupIdeal P).comap coeffMap
  rw [← Ideal.map_le_iff_le_comap]
  exact (le_of_mem_finiteMinimalPrimes hP).trans
    (le_galoisOrbitSupIdeal P)

/-- If the coefficient extension is reducible, the rational orbit ideal of
each geometric minimal component strictly contains the original prime. -/
theorem lt_rationalOrbitIdeal_of_mem_qbarMinimalPrimes
    [Fintype σ]
    (Q : Ideal (MvPolynomial σ ℚ))
    (hnotPrime : ¬ (qbarCoefficientExtensionIdeal Q).IsPrime)
    (P : Ideal (MvPolynomial σ Qbar))
    (hP : P ∈ finiteMinimalPrimes
      (qbarCoefficientExtensionIdeal Q)) :
    Q < rationalOrbitIdeal P := by
  have hle := le_rationalOrbitIdeal_of_mem_qbarMinimalPrimes Q P hP
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hExtOrbit : qbarCoefficientExtensionIdeal Q =
      galoisOrbitSupIdeal P := by
    calc
      qbarCoefficientExtensionIdeal Q =
          (rationalOrbitIdeal P).map coeffMap := by
            change Q.map coeffMap = _
            rw [heq]
      _ = galoisOrbitSupIdeal P := map_rationalOrbitIdeal_eq P
  have hExtP : qbarCoefficientExtensionIdeal Q ≤ P :=
    le_of_mem_finiteMinimalPrimes hP
  have hPExt : P ≤ qbarCoefficientExtensionIdeal Q :=
    (le_galoisOrbitSupIdeal P).trans_eq hExtOrbit.symm
  have hPEq : P = qbarCoefficientExtensionIdeal Q :=
    le_antisymm hPExt hExtP
  have hPprime : P.IsPrime := isPrime_of_mem_finiteMinimalPrimes hP
  apply hnotPrime
  rwa [← hPEq]

private theorem prime_lt_inf_two
    {R : Type*} [CommRing R]
    (Q I J : Ideal R) (hQ : Q.IsPrime)
    (hQI : Q < I) (hQJ : Q < J) :
    Q < I ⊓ J := by
  rcases SetLike.lt_iff_le_and_exists.mp hQI with
    ⟨hQIle, x, hxI, hxQ⟩
  rcases SetLike.lt_iff_le_and_exists.mp hQJ with
    ⟨hQJle, y, hyJ, hyQ⟩
  refine SetLike.lt_iff_le_and_exists.mpr
    ⟨le_inf hQIle hQJle, x * y, ?_, ?_⟩
  · exact ⟨I.mul_mem_right y hxI, J.mul_mem_left x hyJ⟩
  · intro hxy
    exact (hQ.mem_or_mem hxy).elim hxQ hyQ

private theorem prime_lt_finset_inf
    {R α : Type*} [CommRing R] [DecidableEq α]
    (Q : Ideal R) (hQ : Q.IsPrime)
    (s : Finset α) (I : α → Ideal R)
    (hQI : ∀ a ∈ s, Q < I a) :
    Q < s.inf I := by
  induction s using Finset.induction_on with
  | empty =>
      exact lt_top_iff_ne_top.mpr hQ.ne_top
  | @insert a s ha ih =>
      rw [Finset.inf_insert]
      apply prime_lt_inf_two Q (I a) (s.inf I) hQ
      · exact hQI a (Finset.mem_insert_self a s)
      · apply ih
        intro b hb
        exact hQI b (Finset.mem_insert_of_mem hb)

/-- In the reducible case the single rational frontier ideal strictly
contains the original rational prime. -/
theorem lt_rationalGeometricFrontierIdeal
    [Fintype σ]
    (Q : Ideal (MvPolynomial σ ℚ)) (hQprime : Q.IsPrime)
    (hnotPrime : ¬ (qbarCoefficientExtensionIdeal Q).IsPrime) :
    Q < rationalGeometricFrontierIdeal Q := by
  classical
  unfold rationalGeometricFrontierIdeal
  apply prime_lt_finset_inf Q hQprime _ _
  intro P hP
  exact lt_rationalOrbitIdeal_of_mem_qbarMinimalPrimes
    Q hnotPrime P hP

private theorem mvPolynomial_finset_inf_isHomogeneous
    {K α τ : Type*} [Field K] [DecidableEq α]
    (s : Finset α) (I : α → Ideal (MvPolynomial τ K))
    (hI : ∀ a ∈ s, (I a).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule τ K)) :
    (s.inf I).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule τ K) := by
  induction s using Finset.induction_on with
  | empty =>
      simpa using Ideal.IsHomogeneous.top
        (MvPolynomial.homogeneousSubmodule τ K)
  | @insert a s ha ih =>
      rw [Finset.inf_insert]
      apply Ideal.IsHomogeneous.inf
      · exact hI a (Finset.mem_insert_self a s)
      · apply ih
        intro b hb
        exact hI b (Finset.mem_insert_of_mem hb)

/-- The single rational frontier ideal is homogeneous. -/
theorem rationalGeometricFrontierIdeal_isHomogeneous
    [Fintype σ]
    (Q : Ideal (MvPolynomial σ ℚ))
    (hQ : Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ ℚ)) :
    (rationalGeometricFrontierIdeal Q).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ ℚ) := by
  classical
  unfold rationalGeometricFrontierIdeal
  apply mvPolynomial_finset_inf_isHomogeneous
    (finiteMinimalPrimes (qbarCoefficientExtensionIdeal Q))
    (fun P ↦ rationalOrbitIdeal P)
  intro P hP
  exact rationalOrbitIdeal_isHomogeneous P
    (qbarMinimalComponent_isHomogeneous Q hQ P hP)

/-- Every rational zero of `Q` is a zero of the single rational frontier
ideal. -/
theorem rationalZero_mem_rationalGeometricFrontierIdeal
    [Fintype σ]
    (Q : Ideal (MvPolynomial σ ℚ)) (x : σ → ℚ)
    (hx : x ∈ affineIdealZeroLocus Q) :
    x ∈ affineIdealZeroLocus (rationalGeometricFrontierIdeal Q) := by
  classical
  let T : Ideal (MvPolynomial σ Qbar) :=
    RingHom.ker (MvPolynomial.eval
      (fun i ↦ algebraMap ℚ Qbar (x i)))
  letI : T.IsPrime := RingHom.ker_isPrime _
  have hxExt : (fun i ↦ algebraMap ℚ Qbar (x i)) ∈
      affineIdealZeroLocus (qbarCoefficientExtensionIdeal Q) :=
    (rational_zero_of_ideal_iff_qbar_zero_of_extension
      Q (qbarCoefficientExtensionIdeal Q) rfl x).mp hx
  have hExtT : qbarCoefficientExtensionIdeal Q ≤ T := by
    rw [mem_affineIdealZeroLocus_iff] at hxExt
    exact hxExt
  obtain ⟨P, hP, hPT⟩ := exists_finiteMinimalPrime_le hExtT
  have hxP : x ∈ affineIdealZeroLocus (rationalOrbitIdeal P) :=
    rationalPoint_mem_rationalOrbitIdeal P x hPT
  rw [mem_affineIdealZeroLocus_iff] at hxP ⊢
  have hfrontierP : rationalGeometricFrontierIdeal Q ≤
      rationalOrbitIdeal P := by
    unfold rationalGeometricFrontierIdeal
    exact Finset.inf_le (f := fun R ↦ rationalOrbitIdeal R) hP
  intro f hf
  exact hxP f (hfrontierP hf)

/-- Every irreducible component of the rational frontier has strictly
smaller quotient Krull dimension than the original prime. -/
theorem rationalGeometricFrontierMinimalPrime_dimension_lt
    [Fintype σ]
    (Q : Ideal (MvPolynomial σ ℚ)) (hQprime : Q.IsPrime)
    (hnotPrime : ¬ (qbarCoefficientExtensionIdeal Q).IsPrime)
    {s : ℕ}
    (hQdim : ringKrullDim (MvPolynomial σ ℚ ⧸ Q) = s)
    (R : Ideal (MvPolynomial σ ℚ))
    (hR : R ∈ finiteMinimalPrimes
      (rationalGeometricFrontierIdeal Q)) :
    ringKrullDim (MvPolynomial σ ℚ ⧸ R) < s := by
  letI : Q.IsPrime := hQprime
  letI : R.IsPrime := isPrime_of_mem_finiteMinimalPrimes hR
  have hQR : Q < R :=
    (lt_rationalGeometricFrontierIdeal Q hQprime hnotPrime).trans_le
      (le_of_mem_finiteMinimalPrimes hR)
  have hfinite : ringKrullDim (MvPolynomial σ ℚ ⧸ Q) < ⊤ := by
    rw [hQdim]
    change (↑(s : ℕ∞) : WithBot ℕ∞) < ↑(⊤ : ℕ∞)
    exact WithBot.coe_lt_coe.mpr (ENat.coe_lt_top s)
  have hdrop := ringKrullDim_quotient_lt_of_prime_lt Q R hQR hfinite
  rwa [hQdim] at hdrop

/-- Exact rational-prime dichotomy.  In the non-geometrically-prime case,
one fixed homogeneous rational ideal contains all rational points and all
of its actual minimal components have smaller dimension. -/
theorem qbarPrime_or_exists_homogeneous_rationalFrontier
    [Fintype σ]
    (Q : Ideal (MvPolynomial σ ℚ)) (hQprime : Q.IsPrime)
    (hQhomogeneous : Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ ℚ))
    {s : ℕ}
    (hQdim : ringKrullDim (MvPolynomial σ ℚ ⧸ Q) = s) :
    (qbarCoefficientExtensionIdeal Q).IsPrime ∨
      ∃ J : Ideal (MvPolynomial σ ℚ),
        J = rationalGeometricFrontierIdeal Q ∧
        Q < J ∧
        J.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule σ ℚ) ∧
        (∀ x : σ → ℚ,
          x ∈ affineIdealZeroLocus Q →
          x ∈ affineIdealZeroLocus J) ∧
        ∀ R ∈ finiteMinimalPrimes J,
          ringKrullDim (MvPolynomial σ ℚ ⧸ R) < s := by
  classical
  by_cases hgeom : (qbarCoefficientExtensionIdeal Q).IsPrime
  · exact Or.inl hgeom
  · right
    refine ⟨rationalGeometricFrontierIdeal Q, rfl,
      lt_rationalGeometricFrontierIdeal Q hQprime hgeom,
      rationalGeometricFrontierIdeal_isHomogeneous Q hQhomogeneous,
      ?_, ?_⟩
    · intro x hx
      exact rationalZero_mem_rationalGeometricFrontierIdeal Q x hx
    · intro R hR
      exact rationalGeometricFrontierMinimalPrime_dimension_lt
        Q hQprime hgeom hQdim R hR

/-! ## The dimension-five counting consequence -/

/-- If a homogeneous rational prime cone of dimension five is not
geometrically prime, its integral points in every translated and rescaled
box satisfy the elementary `O(T^4)` bound.  The proof uses the explicit
rational frontier above and homogeneous linear normalization of each of its
actual minimal components. -/
theorem exists_card_le_mul_fourthPower_of_qbarExtension_notPrime
    {N : ℕ}
    (Q : Ideal (MvPolynomial (Fin N) ℚ)) (hQprime : Q.IsPrime)
    (hQhomogeneous : Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin N) ℚ))
    (hQdim : ringKrullDim (MvPolynomial (Fin N) ℚ ⧸ Q) = 5)
    (hnotPrime : ¬ (qbarCoefficientExtensionIdeal Q).IsPrime) :
    ∃ K : ℕ, ∀ (points : Finset (IntVector N))
      (x₀ : IntVector N) (m T : ℕ), 0 < m → 1 ≤ T →
      (∀ z ∈ points, ∀ i, (z i).natAbs ≤ T) →
      (∀ z ∈ points,
        (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
          affineIdealZeroLocus Q) →
      points.card ≤ K * T ^ 4 := by
  classical
  let J := rationalGeometricFrontierIdeal Q
  let components := finiteMinimalPrimes J
  let Component := {R : Ideal (MvPolynomial (Fin N) ℚ) // R ∈ components}
  have hJhomogeneous : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin N) ℚ) :=
    rationalGeometricFrontierIdeal_isHomogeneous Q hQhomogeneous
  have hEach : ∀ R : Component, ∃ K : ℕ,
      ∀ (points : Finset (IntVector N))
        (x₀ : IntVector N) (m T : ℕ), 0 < m → 1 ≤ T →
        (∀ z ∈ points, ∀ i, (z i).natAbs ≤ T) →
        (∀ z ∈ points,
          (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
            affineIdealZeroLocus R.1) →
        points.card ≤ K * T ^ 4 := by
    intro R
    have hR : R.1 ∈ finiteMinimalPrimes J := R.2
    have hRprime : R.1.IsPrime := isPrime_of_mem_finiteMinimalPrimes hR
    letI : R.1.IsPrime := hRprime
    have hRhomogeneous : R.1.IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin N) ℚ) := by
      apply isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous hJhomogeneous
      exact (mem_finiteMinimalPrimes_iff J R.1).mp hR
    obtain ⟨D⟩ := exists_homogeneousLinearNormalizationData N R.1
      hRprime hRhomogeneous
    have hRdim : ringKrullDim (MvPolynomial (Fin N) ℚ ⧸ R.1) < 5 :=
      rationalGeometricFrontierMinimalPrime_dimension_lt
        Q hQprime hnotPrime hQdim R.1 hR
    have hparameterlt : D.parameterCount < 5 :=
      normalization_parameter_lt_of_ringKrullDim_lt_nat
        D.hom D.hom_injective D.hom_finite.to_isIntegral hRdim
    exact exists_card_le_mul_power_of_parameterCount_le D (by omega)
  choose componentConstant hcomponentConstant using hEach
  let K : ℕ := ∑ R : Component, componentConstant R
  refine ⟨K, ?_⟩
  intro points x₀ m T hm hT hbox hzero
  let componentPoints := fun R : Component ↦
    points.filter fun z ↦
      (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
        affineIdealZeroLocus R.1
  have hcover : points ⊆ Finset.univ.biUnion componentPoints := by
    intro z hz
    let x : Fin N → ℚ :=
      fun i ↦ (integralAffineMap x₀ z m i : ℚ)
    have hxQ : x ∈ affineIdealZeroLocus Q := hzero z hz
    have hxJ : x ∈ affineIdealZeroLocus J :=
      rationalZero_mem_rationalGeometricFrontierIdeal Q x hxQ
    let Tzero : Ideal (MvPolynomial (Fin N) ℚ) :=
      RingHom.ker (MvPolynomial.eval x)
    letI : Tzero.IsPrime := RingHom.ker_isPrime _
    have hJT : J ≤ Tzero := by
      rw [mem_affineIdealZeroLocus_iff] at hxJ
      exact hxJ
    obtain ⟨R, hR, hRT⟩ := exists_finiteMinimalPrime_le hJT
    apply Finset.mem_biUnion.mpr
    refine ⟨⟨R, hR⟩, Finset.mem_univ _, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨hz, fun f hf ↦ RingHom.mem_ker.mp (hRT hf)⟩
  have hcardCover : points.card ≤
      ∑ R : Component, (componentPoints R).card := by
    calc
      points.card ≤ (Finset.univ.biUnion componentPoints).card :=
        Finset.card_le_card hcover
      _ ≤ ∑ R ∈ (Finset.univ : Finset Component),
          (componentPoints R).card := Finset.card_biUnion_le
      _ = ∑ R : Component, (componentPoints R).card := by simp
  have hcomponent : ∀ R : Component,
      (componentPoints R).card ≤ componentConstant R * T ^ 4 := by
    intro R
    apply hcomponentConstant R (componentPoints R) x₀ m T hm hT
    · intro z hz i
      exact hbox z (Finset.mem_filter.mp hz).1 i
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
  calc
    points.card ≤ ∑ R : Component, (componentPoints R).card := hcardCover
    _ ≤ ∑ R : Component, componentConstant R * T ^ 4 := by
      exact Finset.sum_le_sum fun R _ ↦ hcomponent R
    _ = K * T ^ 4 := by
      simp only [K, Finset.sum_mul]

end

end TranslatedDepthSeven

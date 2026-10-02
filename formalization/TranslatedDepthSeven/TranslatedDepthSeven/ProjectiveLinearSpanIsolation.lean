import TranslatedDepthSeven.DepthSevenRankSevenPacketAssembly
import TranslatedDepthSeven.FiniteComponentFrontier
import TranslatedDepthSeven.JacobianExceptionalDegreeSplit
import TranslatedDepthSeven.ProjectiveHilbertCoefficientExtension

/-!
# Literal rational linear-span isolation

This file contains the linear-algebra and component-extraction part of the
low-degree projective-fourfold argument.  It deliberately uses matrices,
generated ideals, actual minimal primes, and the Hilbert-function predicate
from `PublishedCountingTheorems`; no geometric counting interface is
introduced.

The classical degree--span inequality

`dim Span(V) ≤ dim(V) + deg(V) - 1`

is not presently available in Mathlib.  Everything after the two independent
rational linear equations supplied by that inequality is proved below.  In
particular, the finite-height assertion is an elementary consequence of the
fact that the Jacobian-exceptional component list is fixed and finite.
-/

namespace TranslatedDepthSeven

noncomputable section

open Matrix MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

local instance projectiveLinearSpanIsolationClassicalDecidablePred
    {A : Type*} (q : A → Prop) : DecidablePred q := Classical.decPred q

/-- The homogeneous linear polynomial with the displayed coefficient
vector. -/
def rationalLinearPolynomial {N : ℕ} :
    (Fin N → ℚ) →ₗ[ℚ] MvPolynomial (Fin N) ℚ where
  toFun a := ∑ j, MvPolynomial.C (a j) * MvPolynomial.X j
  map_add' a b := by
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' q a := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, map_mul]
    rw [MvPolynomial.smul_eq_C_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [mul_assoc]

/-- Coefficient vectors of rational hyperplanes containing the projective
zero locus of `Q`.  Membership is the literal ideal-membership condition on
the associated degree-one polynomial. -/
def rationalLinearFormsInIdeal {N : ℕ}
    (Q : Ideal (MvPolynomial (Fin N) ℚ)) : Submodule ℚ (Fin N → ℚ) where
  carrier := {a | rationalLinearPolynomial a ∈ Q}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simpa using Q.add_mem ha hb
  smul_mem' := by
    intro q a ha
    change rationalLinearPolynomial (q • a) ∈ Q
    change rationalLinearPolynomial a ∈ Q at ha
    rw [map_smul]
    simpa [MvPolynomial.smul_eq_C_mul] using
      Q.mul_mem_left (MvPolynomial.C q) ha

@[simp]
theorem mem_rationalLinearFormsInIdeal_iff {N : ℕ}
    (Q : Ideal (MvPolynomial (Fin N) ℚ)) (a : Fin N → ℚ) :
    a ∈ rationalLinearFormsInIdeal Q ↔ rationalLinearPolynomial a ∈ Q :=
  Iff.rfl

/-- The matrix whose rows are the displayed rational linear forms. -/
def rationalLinearFormMatrix {c N : ℕ} (v : Fin c → Fin N → ℚ) :
    Matrix (Fin c) (Fin N) ℚ :=
  fun i j ↦ v i j

@[simp]
theorem rationalLinearFormMatrix_row {c N : ℕ}
    (v : Fin c → Fin N → ℚ) (i : Fin c) :
    (rationalLinearFormMatrix v).row i = v i :=
  rfl

/-- Independent displayed linear forms give a full-row-rank matrix. -/
theorem rationalLinearFormMatrix_rank_eq {c N : ℕ}
    (v : Fin c → Fin N → ℚ) (hv : LinearIndependent ℚ v) :
    (rationalLinearFormMatrix v).rank = c := by
  simpa using hv.rank_matrix

theorem rationalMatrixRowLinearPolynomial_rationalLinearFormMatrix
    {c N : ℕ} (v : Fin c → Fin N → ℚ) (i : Fin c) :
    rationalMatrixRowLinearPolynomial (rationalLinearFormMatrix v) i =
      rationalLinearPolynomial (v i) := by
  rfl

/-- Two-dimensionality of the literal space of linear equations produces
two independent rational rows, hence a codimension-two rational projective
linear space containing the zero locus. -/
theorem exists_twoRow_rationalLinearFormMatrix_of_two_le_finrank
    {N : ℕ} (Q : Ideal (MvPolynomial (Fin N) ℚ))
    (hlin : 2 ≤ Module.finrank ℚ (rationalLinearFormsInIdeal Q)) :
    ∃ v : Fin 2 → Fin N → ℚ,
      LinearIndependent ℚ v ∧
      (rationalLinearFormMatrix v).rank = 2 ∧
      ∀ i, rationalMatrixRowLinearPolynomial
        (rationalLinearFormMatrix v) i ∈ Q := by
  obtain ⟨u, hu⟩ := exists_linearIndependent_of_le_finrank hlin
  let v : Fin 2 → Fin N → ℚ := fun i ↦ (u i).1
  have hv : LinearIndependent ℚ v := by
    exact hu.map' (rationalLinearFormsInIdeal Q).subtype
      (Submodule.ker_subtype (rationalLinearFormsInIdeal Q))
  refine ⟨v, hv, rationalLinearFormMatrix_rank_eq v hv, ?_⟩
  intro i
  rw [rationalMatrixRowLinearPolynomial_rationalLinearFormMatrix]
  exact (u i).2

/-- If every displayed row polynomial belongs to `Q`, the complete row
ideal belongs to `Q`. -/
theorem finiteEquationIdeal_rowLinear_le_of_rows_mem
    {c N : ℕ} (v : Fin c → Fin N → ℚ)
    (Q : Ideal (MvPolynomial (Fin N) ℚ))
    (hvQ : ∀ i, rationalMatrixRowLinearPolynomial
      (rationalLinearFormMatrix v) i ∈ Q) :
    finiteEquationIdeal
        (rationalMatrixRowLinearEquationFamily
          (rationalLinearFormMatrix v)) ≤ Q := by
  rw [finiteEquationIdeal]
  apply Ideal.span_le.mpr
  intro f hf
  rw [Finset.mem_coe, rationalMatrixRowLinearEquationFamily,
    Finset.mem_image] at hf
  obtain ⟨i, _hi, rfl⟩ := hf
  exact hvQ i

/-- Every rational zero of an ideal containing the row equations lies in
the literal matrix kernel. -/
theorem mulVec_rationalLinearFormMatrix_eq_zero_of_zeroLocus
    {c N : ℕ} (v : Fin c → Fin N → ℚ)
    (Q : Ideal (MvPolynomial (Fin N) ℚ))
    (hvQ : ∀ i, rationalMatrixRowLinearPolynomial
      (rationalLinearFormMatrix v) i ∈ Q)
    {x : Fin N → ℚ} (hx : x ∈ affineIdealZeroLocus Q) :
    Matrix.mulVec (rationalLinearFormMatrix v) x = 0 := by
  funext i
  have hrow := hx
    (rationalMatrixRowLinearPolynomial (rationalLinearFormMatrix v) i)
    (hvQ i)
  simpa [eval_rationalMatrixRowLinearPolynomial] using hrow

/-- The geometric section ideal is literally the coefficient extension of
the rational section ideal. -/
theorem geometricLinearSectionIdeal_eq_map_rationalLinearSectionIdeal
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    {c : ℕ} (A : Matrix (Fin c) (Fin 13) ℚ) :
    finiteEquationIdeal
        (geometricLinearSectionEquationFinset equations A) =
      (finiteEquationIdeal
        (rationalLinearSectionEquationFinset equations A)).map
          (MvPolynomial.map (algebraMap ℚ Qbar)) := by
  classical
  rw [geometricLinearSectionEquationFinset]
  unfold finiteEquationIdeal
  rw [Ideal.map_span, Finset.coe_image]

/-- The coefficient-extended original equation ideal is contained in every
literal geometric linear-section ideal. -/
theorem geometricOriginalIdeal_le_geometricLinearSectionIdeal
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    {c : ℕ} (A : Matrix (Fin c) (Fin 13) ℚ) :
    (finiteEquationIdeal (rationalizedEquationFinset equations)).map
        (MvPolynomial.map (algebraMap ℚ Qbar)) ≤
      finiteEquationIdeal
        (geometricLinearSectionEquationFinset equations A) := by
  rw [geometricLinearSectionIdeal_eq_map_rationalLinearSectionIdeal]
  apply Ideal.map_mono
  rw [rationalLinearSectionEquationFinset,
    finiteEquationIdeal_union_rowLinearEquationFamily]
  exact le_sup_left

/-- Ideal-theoretic containment of the original equations and the row
equations in a rational ideal survives coefficient extension. -/
theorem geometricLinearSectionIdeal_le_of_rational_containment
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    {c : ℕ} (A : Matrix (Fin c) (Fin 13) ℚ)
    (Q : Ideal (MvPolynomial (Fin 13) ℚ))
    (R : Ideal (MvPolynomial (Fin 13) Qbar))
    (hIQ : finiteEquationIdeal (rationalizedEquationFinset equations) ≤ Q)
    (hAQ : finiteEquationIdeal
      (rationalMatrixRowLinearEquationFamily A) ≤ Q)
    (hQR : Q.map (MvPolynomial.map (algebraMap ℚ Qbar)) ≤ R) :
    finiteEquationIdeal
        (geometricLinearSectionEquationFinset equations A) ≤ R := by
  rw [geometricLinearSectionIdeal_eq_map_rationalLinearSectionIdeal]
  apply (Ideal.map_mono ?_).trans hQR
  rw [rationalLinearSectionEquationFinset,
    finiteEquationIdeal_union_rowLinearEquationFamily]
  exact sup_le hIQ hAQ

/-- If a geometric prime contains the complete section ideal, an actual
minimal component of that section lies below it.  A nonzero rational
projective point on the prime lies on the chosen component, so the component
survives projectivization. -/
theorem exists_projectiveSectionComponent_le_geometricPrime_through_point
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    {c : ℕ} (A : Matrix (Fin c) (Fin 13) ℚ)
    (R : Ideal (MvPolynomial (Fin 13) Qbar))
    (hRprime : R.IsPrime)
    (hsectionR : finiteEquationIdeal
      (geometricLinearSectionEquationFinset equations A) ≤ R)
    (x : Projectivization ℚ (Fin 13 → ℚ))
    (hxR : ProjectivePointVanishesOnGeometricIdeal R x) :
    ∃ P : Ideal (MvPolynomial (Fin 13) Qbar),
      IsProjectiveSectionComponent equations A P ∧
      P ≤ R ∧ ProjectivePointVanishesOnGeometricIdeal P x := by
  classical
  letI : R.IsPrime := hRprime
  obtain ⟨P, hPminimal, hPR⟩ :=
    exists_finiteMinimalPrime_le hsectionR
  have hxP : ProjectivePointVanishesOnGeometricIdeal P x := by
    intro f hf
    exact hxR f (hPR hf)
  have hirrelevant : ¬ geometricIrrelevantCoordinateIdeal 13 ≤ P := by
    intro hirr
    apply x.rep_nonzero
    funext i
    have hXi : MvPolynomial.X i ∈ P := by
      apply hirr
      apply Ideal.subset_span
      exact Set.mem_range_self i
    have heval := hxP (MvPolynomial.X i) hXi
    have hmap : algebraMap ℚ Qbar (x.rep i) = 0 := by
      simpa [ProjectivePointVanishesOnGeometricIdeal] using heval
    exact (map_eq_zero_iff (algebraMap ℚ Qbar)
      (FaithfulSMul.algebraMap_injective ℚ Qbar)).mp hmap
  refine ⟨P, ⟨?_, hirrelevant⟩, hPR, hxP⟩
  simpa [finiteEquationMinimalPrimes] using hPminimal

/-- A homogeneous-coordinate ideal which vanishes at a genuine projective
point cannot contain every coordinate. -/
theorem geometricIrrelevantCoordinateIdeal_not_le_of_projectivePoint
    (P : Ideal (MvPolynomial (Fin 13) Qbar))
    (x : Projectivization ℚ (Fin 13 → ℚ))
    (hxP : ProjectivePointVanishesOnGeometricIdeal P x) :
    ¬ geometricIrrelevantCoordinateIdeal 13 ≤ P := by
  intro hirr
  apply x.rep_nonzero
  funext i
  have hXi : MvPolynomial.X i ∈ P := by
    apply hirr
    apply Ideal.subset_span
    exact Set.mem_range_self i
  have heval := hxP (MvPolynomial.X i) hXi
  have hmap : algebraMap ℚ Qbar (x.rep i) = 0 := by
    simpa [ProjectivePointVanishesOnGeometricIdeal] using heval
  exact (map_eq_zero_iff (algebraMap ℚ Qbar)
    (FaithfulSMul.algebraMap_injective ℚ Qbar)).mp hmap

/-- On a fixed finite component list, any pointwise choice of rational
linear spaces has one uniform (finite) Plücker-height bound. -/
theorem exists_uniform_rationalProjectiveLinearHeight_of_finite
    {α : Type*} (components : Finset α)
    (hspace : ∀ Q ∈ components,
      ∃ c : ℕ, 1 ≤ c ∧ c ≤ 3 ∧
        ∃ A : Matrix (Fin c) (Fin 13) ℚ, A.rank = c) :
    ∃ C : ℕ, ∀ Q ∈ components,
      ∃ c : ℕ, 1 ≤ c ∧ c ≤ 3 ∧
        ∃ A : Matrix (Fin c) (Fin 13) ℚ,
          A.rank = c ∧ rationalProjectiveLinearHeight A ≤ C := by
  classical
  have hspace' : ∀ Q : {Q // Q ∈ components},
      ∃ c : ℕ, 1 ≤ c ∧ c ≤ 3 ∧
        ∃ A : Matrix (Fin c) (Fin 13) ℚ, A.rank = c := by
    intro Q
    exact hspace Q.1 Q.2
  choose c hc1 hc3 A hArank using hspace'
  let C : ℕ := components.attach.sup fun Q ↦
    rationalProjectiveLinearHeight (A Q)
  refine ⟨C, ?_⟩
  intro Q hQ
  let Q' : {R // R ∈ components} := ⟨Q, hQ⟩
  refine ⟨c Q', hc1 Q', hc3 Q', A Q', hArank Q', ?_⟩
  exact Finset.le_sup (s := components.attach) (f := fun R ↦
    rationalProjectiveLinearHeight (A R)) (Finset.mem_attach components Q')

/-- Uniform-height codimension-two spaces for a finite list, obtained
directly from the literal two-dimensional spaces of linear equations. -/
theorem exists_uniform_twoRow_linearSpan_of_finite
    {α : Type*} (components : Finset α)
    (ideal : α → Ideal (MvPolynomial (Fin 13) ℚ))
    (hlin : ∀ Q ∈ components,
      2 ≤ Module.finrank ℚ (rationalLinearFormsInIdeal (ideal Q))) :
    ∃ C : ℕ, ∀ Q ∈ components,
      ∃ v : Fin 2 → Fin 13 → ℚ,
        LinearIndependent ℚ v ∧
        (rationalLinearFormMatrix v).rank = 2 ∧
        (∀ i, rationalMatrixRowLinearPolynomial
          (rationalLinearFormMatrix v) i ∈ ideal Q) ∧
        rationalProjectiveLinearHeight (rationalLinearFormMatrix v) ≤ C := by
  classical
  have hchoice : ∀ Q : {Q // Q ∈ components},
      ∃ v : Fin 2 → Fin 13 → ℚ,
        LinearIndependent ℚ v ∧
        (rationalLinearFormMatrix v).rank = 2 ∧
        ∀ i, rationalMatrixRowLinearPolynomial
          (rationalLinearFormMatrix v) i ∈ ideal Q.1 := by
    intro Q
    exact exists_twoRow_rationalLinearFormMatrix_of_two_le_finrank
      (ideal Q.1) (hlin Q.1 Q.2)
  choose v hv hvrank hvrows using hchoice
  let C : ℕ := components.attach.sup fun Q ↦
    rationalProjectiveLinearHeight (rationalLinearFormMatrix (v Q))
  refine ⟨C, ?_⟩
  intro Q hQ
  let Q' : {R // R ∈ components} := ⟨Q, hQ⟩
  refine ⟨v Q', hv Q', hvrank Q', hvrows Q', ?_⟩
  exact Finset.le_sup (s := components.attach) (f := fun R ↦
    rationalProjectiveLinearHeight (rationalLinearFormMatrix (v R)))
      (Finset.mem_attach components Q')

/-- Outside the concrete exceptional locus, a component through a
codimension-two section has projective dimension at most three. -/
theorem codimensionTwo_component_dimension_le_three_of_not_exceptional
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (heightBound : ℕ)
    (A : Matrix (Fin 2) (Fin 13) ℚ) (hArank : A.rank = 2)
    (hAheight : rationalProjectiveLinearHeight A ≤ heightBound)
    (P : Ideal (MvPolynomial (Fin 13) Qbar))
    (hcomponent : IsProjectiveSectionComponent equations A P)
    (x : Projectivization ℚ (Fin 13 → ℚ))
    (hxP : ProjectivePointVanishesOnGeometricIdeal P x)
    (hnot : ¬ MemDepthSevenExceptionalLocus equations heightBound x)
    {r d : ℕ} (hP : HasGeometricProjectiveDimensionDegree P r d) :
    r ≤ 3 := by
  by_contra hr
  apply hnot
  refine ⟨2, by omega, by omega, A, hArank, hAheight, P,
    hcomponent, ?_, hxP⟩
  exact Or.inl ⟨by omega, by omega, Or.inl ⟨r, d, hP, by omega⟩⟩

/-- A minimal component of a section lying below a projective fourfold has
projective dimension at least four, whenever the two literal Hilbert
dimension--degree certificates are available. -/
theorem projectiveDimension_ge_four_of_sectionComponent_le_fourfold
    (P R : Ideal (MvPolynomial (Fin 13) Qbar))
    (hPprime : P.IsPrime) (hRprime : R.IsPrime) (hPR : P ≤ R)
    {r e d : ℕ}
    (hP : HasGeometricProjectiveDimensionDegree P r e)
    (hR : HasGeometricProjectiveDimensionDegree R 4 d) :
    4 ≤ r := by
  letI : P.IsPrime := hPprime
  letI : R.IsPrime := hRprime
  rcases eq_or_lt_of_le hPR with hEq | hlt
  · subst R
    have hdim : (r + 1 : WithBot ℕ∞) = (4 + 1 : WithBot ℕ∞) := by
      exact hP.1.symm.trans hR.1
    have hr : r + 1 = 4 + 1 := by exact_mod_cast hdim
    omega
  · have hfinite : ringKrullDim
        (MvPolynomial (Fin 13) Qbar ⧸ P) < ⊤ := by
      rw [hP.1]
      change (↑((r + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) < ↑(⊤ : ℕ∞)
      exact WithBot.coe_lt_coe.mpr (ENat.coe_lt_top (r + 1))
    have hdrop := ringKrullDim_quotient_lt_of_prime_lt P R hlt hfinite
    rw [hP.1, hR.1] at hdrop
    have hr : 4 + 1 < r + 1 := by exact_mod_cast hdrop
    omega

/-- Let `I` be the prime affine cone over a projective fivefold and `R` the
prime affine cone over a projective fourfold contained in it.  If a section
ideal `J` lies between `I` and `R`, then either the section adds no equation
to `I`, or `R` itself is a minimal prime of `J`.

This elementary dimension argument is useful because it avoids invoking
Hilbert--Serre for an arbitrary intermediate minimal prime. -/
theorem fivefold_fourfold_section_dichotomy
    (I J R : Ideal (MvPolynomial (Fin 13) Qbar))
    (hIprime : I.IsPrime) (hRprime : R.IsPrime)
    (hIJ : I ≤ J) (hJR : J ≤ R)
    (hIdim : ringKrullDim
      (MvPolynomial (Fin 13) Qbar ⧸ I) = 6)
    (hRdim : ringKrullDim
      (MvPolynomial (Fin 13) Qbar ⧸ R) = 5) :
    J ≤ I ∨ R ∈ finiteMinimalPrimes J := by
  by_cases hJI : J ≤ I
  · exact Or.inl hJI
  · right
    letI : I.IsPrime := hIprime
    letI : R.IsPrime := hRprime
    obtain ⟨P, hPminimal, hPR⟩ := exists_finiteMinimalPrime_le hJR
    have hPprime : P.IsPrime := isPrime_of_mem_finiteMinimalPrimes hPminimal
    letI : P.IsPrime := hPprime
    have hJP : J ≤ P := le_of_mem_finiteMinimalPrimes hPminimal
    have hIP : I ≤ P := hIJ.trans hJP
    have hIPstrict : I < P := by
      apply lt_of_le_not_ge hIP
      intro hPI
      exact hJI (hJP.trans hPI)
    have hIfinite : ringKrullDim
        (MvPolynomial (Fin 13) Qbar ⧸ I) < ⊤ := by
      rw [hIdim]
      change (↑(6 : ℕ∞) : WithBot ℕ∞) < ↑(⊤ : ℕ∞)
      exact WithBot.coe_lt_coe.mpr (ENat.coe_lt_top 6)
    have hPdimLt : ringKrullDim
        (MvPolynomial (Fin 13) Qbar ⧸ P) < 6 := by
      have hdrop := ringKrullDim_quotient_lt_of_prime_lt
        I P hIPstrict hIfinite
      simpa only [hIdim] using hdrop
    have hPdimLe : ringKrullDim
        (MvPolynomial (Fin 13) Qbar ⧸ P) ≤ 5 := by
      exact WithBot.lt_add_one_iff.mp hPdimLt
    rcases eq_or_lt_of_le hPR with hEq | hPRstrict
    · simpa only [hEq] using hPminimal
    ·
      have hfiveTop : (5 : WithBot ℕ∞) < ⊤ := by
        change (↑(5 : ℕ∞) : WithBot ℕ∞) < ↑(⊤ : ℕ∞)
        exact WithBot.coe_lt_coe.mpr (ENat.coe_lt_top 5)
      have hPfinite : ringKrullDim
          (MvPolynomial (Fin 13) Qbar ⧸ P) < ⊤ :=
        hPdimLe.trans_lt hfiveTop
      have hdrop := ringKrullDim_quotient_lt_of_prime_lt
        P R hPRstrict hPfinite
      rw [hRdim] at hdrop
      exact ((not_lt_of_ge hPdimLe) hdrop).elim

/-- Complete codimension-two endpoint for a geometric fourfold between the
original fivefold and a rational linear section.  Only the Hilbert
certificate of the original rational fivefold and that of the fourfold are
used.  No Hilbert--Serre certificate for an auxiliary section component is
needed: `fivefold_fourfold_section_dichotomy` says that the relevant actual
component is either the coefficient-extended original ideal or `R` itself.
-/
theorem memDepthSevenExceptionalLocus_of_codimensionTwo_fourfold_section
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (heightBound : ℕ)
    (A : Matrix (Fin 2) (Fin 13) ℚ)
    (hArank : A.rank = 2)
    (hAheight : rationalProjectiveLinearHeight A ≤ heightBound)
    {D : ℕ}
    (hOriginal : Published.HasProjectiveDimensionDegree
      (finiteEquationIdeal (rationalizedEquationFinset equations)) 5 D)
    (hGeometricallyPrime : GeometricallyPrimeMvPolynomialIdeal
      (finiteEquationIdeal (rationalizedEquationFinset equations)))
    (R : Ideal (MvPolynomial (Fin 13) Qbar))
    (hRprime : R.IsPrime)
    (hsectionR : finiteEquationIdeal
      (geometricLinearSectionEquationFinset equations A) ≤ R)
    {d : ℕ} (hR : HasGeometricProjectiveDimensionDegree R 4 d)
    (x : Projectivization ℚ (Fin 13 → ℚ))
    (hxR : ProjectivePointVanishesOnGeometricIdeal R x) :
    MemDepthSevenExceptionalLocus equations heightBound x := by
  let I₀ : Ideal (MvPolynomial (Fin 13) ℚ) :=
    finiteEquationIdeal (rationalizedEquationFinset equations)
  let Ibar : Ideal (MvPolynomial (Fin 13) Qbar) :=
    I₀.map (MvPolynomial.map (algebraMap ℚ Qbar))
  let J : Ideal (MvPolynomial (Fin 13) Qbar) :=
    finiteEquationIdeal (geometricLinearSectionEquationFinset equations A)
  have hIbarPrime : Ibar.IsPrime := by
    exact hGeometricallyPrime Qbar
  have hIbar : HasGeometricProjectiveDimensionDegree Ibar 5 D := by
    exact qbarHasProjectiveDimensionDegree_of_rational
      I₀ hOriginal hIbarPrime
  have hIJ : Ibar ≤ J := by
    exact geometricOriginalIdeal_le_geometricLinearSectionIdeal equations A
  have hIR : Ibar ≤ R := hIJ.trans hsectionR
  have hxIbar : ProjectivePointVanishesOnGeometricIdeal Ibar x := by
    intro f hf
    exact hxR f (hIR hf)
  have hchoice : J ≤ Ibar ∨ R ∈ finiteMinimalPrimes J := by
    apply fivefold_fourfold_section_dichotomy Ibar J R
      hIbarPrime hRprime hIJ hsectionR
    · simpa only [Nat.reduceAdd] using hIbar.1
    · simpa only [Nat.reduceAdd] using hR.1
  rcases hchoice with hJI | hRminimal
  · have hEq : J = Ibar := le_antisymm hJI hIJ
    have hIminimal : Ibar ∈ finiteMinimalPrimes J := by
      rw [hEq, mem_finiteMinimalPrimes_iff,
        Ideal.minimalPrimes_eq_subsingleton_self]
      exact Set.mem_singleton Ibar
    have hcomponent : IsProjectiveSectionComponent equations A Ibar := by
      refine ⟨?_, geometricIrrelevantCoordinateIdeal_not_le_of_projectivePoint
        Ibar x hxIbar⟩
      simpa only [finiteEquationMinimalPrimes, J] using hIminimal
    refine ⟨2, by omega, by omega, A, hArank, hAheight, Ibar,
      hcomponent, ?_, hxIbar⟩
    exact isDepthSevenExceptionalComponent_of_dimension_gt_expected
      (c := 2) (r := 5) (d := D) (by omega) (by omega) hIbar (by omega)
  · have hcomponent : IsProjectiveSectionComponent equations A R := by
      refine ⟨?_, geometricIrrelevantCoordinateIdeal_not_le_of_projectivePoint
        R x hxR⟩
      simpa only [finiteEquationMinimalPrimes, J] using hRminimal
    refine ⟨2, by omega, by omega, A, hArank, hAheight, R,
      hcomponent, ?_, hxR⟩
    exact isDepthSevenExceptionalComponent_of_dimension_gt_expected
      (c := 2) (r := 4) (d := d) (by omega) (by omega) hR (by omega)

/-- A rational point on an actual geometric fourfold contained in a
bounded-height rational codimension-two section is necessarily in the
concrete exceptional locus.  The section component `P` is literal and its
containment in the fourfold is stated as the ideal inclusion `P ≤ R`.
-/
theorem memDepthSevenExceptionalLocus_of_codimensionTwo_fourfold_containment
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (heightBound : ℕ)
    (A : Matrix (Fin 2) (Fin 13) ℚ)
    (hArank : A.rank = 2)
    (hAheight : rationalProjectiveLinearHeight A ≤ heightBound)
    (P R : Ideal (MvPolynomial (Fin 13) Qbar))
    (hcomponent : IsProjectiveSectionComponent equations A P)
    (hPprime : P.IsPrime) (hRprime : R.IsPrime) (hPR : P ≤ R)
    {r e d : ℕ}
    (hP : HasGeometricProjectiveDimensionDegree P r e)
    (hR : HasGeometricProjectiveDimensionDegree R 4 d)
    (x : Projectivization ℚ (Fin 13 → ℚ))
    (hxR : ProjectivePointVanishesOnGeometricIdeal R x) :
    MemDepthSevenExceptionalLocus equations heightBound x := by
  have hxP : ProjectivePointVanishesOnGeometricIdeal P x := by
    intro f hf
    exact hxR f (hPR hf)
  refine ⟨2, by omega, by omega, A, hArank, hAheight, P,
    hcomponent, ?_, hxP⟩
  exact isDepthSevenExceptionalComponent_of_dimension_gt_expected
    (c := 2) (r := r) (d := e) (by omega) (by omega) hP
      (by
        have := projectiveDimension_ge_four_of_sectionComponent_le_fourfold
          P R hPprime hRprime hPR hP hR
        omega)

/-- Exact endpoint of the low-degree linear-span argument in the absence of
a general Hilbert--Serre theorem in Mathlib: a nonexceptional point on the
fourfold would force an actual projective section component through that
point to have no `HasProjectiveDimensionDegree` certificate at all.  Thus
Hilbert--Serre existence for this literal homogeneous minimal prime closes
the branch immediately. -/
theorem exists_uncertified_sectionComponent_of_nonexceptional_fourfold_point
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (heightBound : ℕ)
    (A : Matrix (Fin 2) (Fin 13) ℚ)
    (hArank : A.rank = 2)
    (hAheight : rationalProjectiveLinearHeight A ≤ heightBound)
    (R : Ideal (MvPolynomial (Fin 13) Qbar))
    (hRprime : R.IsPrime)
    (hsectionR : finiteEquationIdeal
      (geometricLinearSectionEquationFinset equations A) ≤ R)
    {d : ℕ} (hR : HasGeometricProjectiveDimensionDegree R 4 d)
    (x : Projectivization ℚ (Fin 13 → ℚ))
    (hxR : ProjectivePointVanishesOnGeometricIdeal R x)
    (hnot : ¬ MemDepthSevenExceptionalLocus equations heightBound x) :
    ∃ P : Ideal (MvPolynomial (Fin 13) Qbar),
      IsProjectiveSectionComponent equations A P ∧
      P ≤ R ∧ ProjectivePointVanishesOnGeometricIdeal P x ∧
      ¬ ∃ r e : ℕ, HasGeometricProjectiveDimensionDegree P r e := by
  obtain ⟨P, hcomponent, hPR, hxP⟩ :=
    exists_projectiveSectionComponent_le_geometricPrime_through_point
      equations A R hRprime hsectionR x hxR
  refine ⟨P, hcomponent, hPR, hxP, ?_⟩
  rintro ⟨r, e, hP⟩
  apply hnot
  exact memDepthSevenExceptionalLocus_of_codimensionTwo_fourfold_containment
    equations heightBound A hArank hAheight P R
      hcomponent (projectiveSectionComponent_isPrime equations A hcomponent)
      hRprime hPR hP hR x hxR

end

end TranslatedDepthSeven

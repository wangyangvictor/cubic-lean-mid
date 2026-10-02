import TranslatedDepthSeven.TruncatedPolynomialJets
import TranslatedDepthSeven.RelativePersistentMultiplicityCertificate

/-!
# The universal family of bounded-degree integral polynomial tuples

For fixed numbers `N`, `R`, and `D`, this file constructs one literal
relative family whose parameters are precisely the coefficients of an
`R`-tuple of polynomials in `N` variables of total degree at most `D`.

Every such tuple is recovered exactly by one integral specialization.  The
largest natural absolute value of the canonical parameter vector is exactly
the largest coefficient height of the tuple.  Thus any qualitative relative
spreading theorem may be applied once to this universal family, rather than
separately to polynomial families arising from different packet parameters.

There is no algebraic-geometric existence assertion in this file.  All
results are finite sums, coefficient extraction, and elementary height
comparisons.
-/

namespace TranslatedDepthSeven

noncomputable section

open Finset MvPolynomial

/-- Exponent vectors of total degree at most `D` in `N` variables. -/
def BoundedDegreeMonomial (N D : ℕ) :=
  {m : Fin N →₀ ℕ // Finsupp.degree m ≤ D}

/-- The bounded monomials form a finite type.  The instance is obtained by
adding one slack coordinate and applying stars and bars. -/
noncomputable instance boundedDegreeMonomialFintype (N D : ℕ) :
    Fintype (BoundedDegreeMonomial N D) :=
  Fintype.ofEquiv (Sym (Fin (N + 1)) D)
    (((finExponentLEEquivFinSuccSum N D).trans
      (Sym.equivNatSumOfFintype (Fin (N + 1)) D).symm).symm)

/-- One parameter coordinate for every polynomial and every bounded-degree
monomial. -/
abbrev UniversalCoefficientIndex (N R D : ℕ) :=
  Fin R × BoundedDegreeMonomial N D

/-- The number of coefficient parameters in the universal family. -/
def universalCoefficientParameterCount (N R D : ℕ) : ℕ :=
  Fintype.card (UniversalCoefficientIndex N R D)

/-- The coefficient space has the expected stars-and-bars dimension. -/
theorem universalCoefficientParameterCount_eq (N R D : ℕ) :
    universalCoefficientParameterCount N R D =
      R * (D + N).choose N := by
  unfold universalCoefficientParameterCount UniversalCoefficientIndex
  rw [Fintype.card_prod, Fintype.card_fin]
  congr 1
  rw [← Nat.card_eq_fintype_card]
  exact natCard_finExponent_totalDegree_le N D

/-- A fixed enumeration of the coefficient coordinates by a finite ordinal.
This is the only reason the relative-family parameter type is written as a
`Fin` rather than as the more descriptive product type above. -/
noncomputable def universalCoefficientIndexEquivFin (N R D : ℕ) :
    UniversalCoefficientIndex N R D ≃
      Fin (universalCoefficientParameterCount N R D) :=
  Fintype.equivFin (UniversalCoefficientIndex N R D)

/-- The `r`-th member of the universal integral relative family. -/
def universalBoundedDegreeIntegralPolynomial
    (N R D : ℕ) (r : Fin R) :
    RelativeIntegralAffinePolynomial
      (universalCoefficientParameterCount N R D) N :=
  ∑ m : BoundedDegreeMonomial N D,
    MvPolynomial.monomial m.1
      (MvPolynomial.X (universalCoefficientIndexEquivFin N R D (r, m)))

/-- The canonical parameter vector attached to an integral polynomial
tuple: its `(r,m)` coordinate is literally the coefficient of `m` in the
`r`-th polynomial. -/
def boundedDegreeCoefficientParameter
    {N R D : ℕ} (f : Fin R → MvPolynomial (Fin N) ℤ) :
    Fin (universalCoefficientParameterCount N R D) → ℤ :=
  fun j ↦
    let rm := (universalCoefficientIndexEquivFin N R D).symm j
    (f rm.1).coeff rm.2.1

@[simp]
theorem boundedDegreeCoefficientParameter_apply_index
    {N R D : ℕ} (f : Fin R → MvPolynomial (Fin N) ℤ)
    (r : Fin R) (m : BoundedDegreeMonomial N D) :
    boundedDegreeCoefficientParameter f
        (universalCoefficientIndexEquivFin N R D (r, m)) =
      (f r).coeff m.1 := by
  simp [boundedDegreeCoefficientParameter]

/-- An arbitrary integral parameter vector specializes the universal family
to the corresponding bounded-degree coefficient table. -/
theorem specialize_universalBoundedDegreeIntegralPolynomial_eq_parameter_sum
    {N R D : ℕ}
    (u : Fin (universalCoefficientParameterCount N R D) → ℤ)
    (r : Fin R) :
    specializeRelativeIntegralAffinePolynomial u
        (universalBoundedDegreeIntegralPolynomial N R D r) =
      ∑ m : BoundedDegreeMonomial N D,
        MvPolynomial.monomial m.1
          (u (universalCoefficientIndexEquivFin N R D (r, m))) := by
  classical
  simp [universalBoundedDegreeIntegralPolynomial,
    specializeRelativeIntegralAffinePolynomial]

/-- Coefficient extraction from the universal family recovers the selected
parameter coordinate exactly. -/
theorem coeff_specialize_universalBoundedDegreeIntegralPolynomial
    {N R D : ℕ}
    (u : Fin (universalCoefficientParameterCount N R D) → ℤ)
    (r : Fin R) (m : BoundedDegreeMonomial N D) :
    (specializeRelativeIntegralAffinePolynomial u
        (universalBoundedDegreeIntegralPolynomial N R D r)).coeff m.1 =
      u (universalCoefficientIndexEquivFin N R D (r, m)) := by
  classical
  rw [specialize_universalBoundedDegreeIntegralPolynomial_eq_parameter_sum]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single m]
  · simp
  · intro c _hc hcm
    have hne : c.1 ≠ m.1 := by
      intro h
      apply hcm
      exact Subtype.ext h
    simp [hne]
  · simp

/-- Hence the coefficient-vector construction is a left inverse to
specialization of the universal family; there are no redundant parameter
coordinates. -/
theorem boundedDegreeCoefficientParameter_specializedUniversal
    {N R D : ℕ}
    (u : Fin (universalCoefficientParameterCount N R D) → ℤ) :
    boundedDegreeCoefficientParameter (D := D)
        (fun r ↦ specializeRelativeIntegralAffinePolynomial u
          (universalBoundedDegreeIntegralPolynomial N R D r)) = u := by
  funext j
  let rm := (universalCoefficientIndexEquivFin N R D).symm j
  calc
    boundedDegreeCoefficientParameter (D := D)
          (fun r ↦ specializeRelativeIntegralAffinePolynomial u
            (universalBoundedDegreeIntegralPolynomial N R D r)) j =
        boundedDegreeCoefficientParameter (D := D)
          (fun r ↦ specializeRelativeIntegralAffinePolynomial u
            (universalBoundedDegreeIntegralPolynomial N R D r))
          (universalCoefficientIndexEquivFin N R D rm) := by
            rw [(universalCoefficientIndexEquivFin N R D).apply_symm_apply j]
    _ = (specializeRelativeIntegralAffinePolynomial u
          (universalBoundedDegreeIntegralPolynomial N R D rm.1)).coeff
            rm.2.1 := by
          exact boundedDegreeCoefficientParameter_apply_index _ _ _
    _ = u (universalCoefficientIndexEquivFin N R D rm) :=
      coeff_specialize_universalBoundedDegreeIntegralPolynomial u rm.1 rm.2
    _ = u j := by
      rw [(universalCoefficientIndexEquivFin N R D).apply_symm_apply j]

/-- Specializing the universal family at the coefficient vector produces
the finite sum of all bounded-degree monomials with their prescribed
coefficients. -/
theorem specialize_universalBoundedDegreeIntegralPolynomial_eq_sum
    {N R D : ℕ} (f : Fin R → MvPolynomial (Fin N) ℤ) (r : Fin R) :
    specializeRelativeIntegralAffinePolynomial
        (boundedDegreeCoefficientParameter f)
        (universalBoundedDegreeIntegralPolynomial N R D r) =
      ∑ m : BoundedDegreeMonomial N D,
        MvPolynomial.monomial m.1 ((f r).coeff m.1) := by
  classical
  simp [universalBoundedDegreeIntegralPolynomial,
    specializeRelativeIntegralAffinePolynomial]

/-- Every integral `R`-tuple of total degree at most `D` is exactly one
specialization of the fixed universal family. -/
theorem specialize_universalBoundedDegreeIntegralPolynomial
    {N R D : ℕ} (f : Fin R → MvPolynomial (Fin N) ℤ)
    (hdegree : ∀ r, (f r).totalDegree ≤ D) (r : Fin R) :
    specializeRelativeIntegralAffinePolynomial
        (boundedDegreeCoefficientParameter f)
        (universalBoundedDegreeIntegralPolynomial N R D r) =
      f r := by
  classical
  rw [specialize_universalBoundedDegreeIntegralPolynomial_eq_sum]
  ext m
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  by_cases hbounded : Finsupp.degree m ≤ D
  · let b : BoundedDegreeMonomial N D := ⟨m, hbounded⟩
    rw [Finset.sum_eq_single b]
    · simp [b]
    · intro c _hc hcb
      have hcm : c.1 ≠ m := by
        intro h
        apply hcb
        exact Subtype.ext h
      simp [hcm]
    · simp
  · have hnotmem : m ∉ (f r).support := by
      intro hm
      apply hbounded
      simpa [Finsupp.degree_eq_sum, Finsupp.sum_fintype] using
        (MvPolynomial.le_totalDegree hm).trans (hdegree r)
    have hcoeff : (f r).coeff m = 0 :=
      MvPolynomial.notMem_support_iff.mp hnotmem
    rw [hcoeff]
    apply Finset.sum_eq_zero
    intro b _hb
    have hbm : b.1 ≠ m := by
      intro h
      apply hbounded
      simpa [h] using b.2
    simp [hbm]

/-- Sup norm of an integral parameter vector. -/
def integralParameterNatAbsMax {M : ℕ} (u : Fin M → ℤ) : ℕ :=
  Finset.univ.sup fun j ↦ (u j).natAbs

/-- The coefficient height computed over all monomials of degree at most
`D`.  For a tuple of degree at most `D`, this agrees with the ordinary
support-based coefficient height below. -/
def boundedDegreeTupleCoefficientHeight
    {N R : ℕ} (D : ℕ) (f : Fin R → MvPolynomial (Fin N) ℤ) : ℕ :=
  Finset.univ.sup fun rm : UniversalCoefficientIndex N R D ↦
    ((f rm.1).coeff rm.2.1).natAbs

/-- The ordinary largest coefficient height of an integral polynomial
tuple. -/
def integralPolynomialTupleCoefficientHeight
    {N R : ℕ} (f : Fin R → MvPolynomial (Fin N) ℤ) : ℕ :=
  Finset.univ.sup fun r ↦ mvPolynomialCoefficientNatAbsMax (f r)

/-- The canonical parameter vector has exactly the bounded-degree
coefficient height. -/
theorem integralParameterNatAbsMax_boundedDegreeCoefficientParameter
    {N R D : ℕ} (f : Fin R → MvPolynomial (Fin N) ℤ) :
    integralParameterNatAbsMax
        (boundedDegreeCoefficientParameter (D := D) f) =
      boundedDegreeTupleCoefficientHeight D f := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro j _hj
    let rm := (universalCoefficientIndexEquivFin N R D).symm j
    have h := Finset.le_sup
      (s := (Finset.univ : Finset (UniversalCoefficientIndex N R D)))
      (f := fun z ↦ ((f z.1).coeff z.2.1).natAbs)
      (Finset.mem_univ rm)
    simpa [integralParameterNatAbsMax, boundedDegreeTupleCoefficientHeight,
      boundedDegreeCoefficientParameter, rm] using h
  · apply Finset.sup_le
    intro rm _hrm
    rcases rm with ⟨r, m⟩
    have h := Finset.le_sup
      (s := Finset.univ)
      (f := fun j : Fin (universalCoefficientParameterCount N R D) ↦
        (boundedDegreeCoefficientParameter (D := D) f j).natAbs)
      (Finset.mem_univ (universalCoefficientIndexEquivFin N R D (r, m)))
    simp only [boundedDegreeCoefficientParameter_apply_index] at h
    simpa [integralParameterNatAbsMax] using h

/-- Every bounded-degree coefficient occurs in the ordinary support-based
tuple height.  Coefficients outside the support are zero. -/
theorem boundedDegreeTupleCoefficientHeight_le
    {N R D : ℕ} (f : Fin R → MvPolynomial (Fin N) ℤ) :
    boundedDegreeTupleCoefficientHeight D f ≤
      integralPolynomialTupleCoefficientHeight f := by
  classical
  apply Finset.sup_le
  intro rm _hrm
  have hcoefficient : ((f rm.1).coeff rm.2.1).natAbs ≤
      mvPolynomialCoefficientNatAbsMax (f rm.1) := by
    by_cases hm : rm.2.1 ∈ (f rm.1).support
    · exact coeff_natAbs_le_mvPolynomialCoefficientNatAbsMax (f rm.1) hm
    · rw [MvPolynomial.notMem_support_iff.mp hm]
      exact Nat.zero_le _
  exact hcoefficient.trans
    (Finset.le_sup (s := Finset.univ)
      (f := fun r ↦ mvPolynomialCoefficientNatAbsMax (f r))
      (Finset.mem_univ rm.1))

/-- For a tuple of degree at most `D`, every supported coefficient occurs
among the bounded-degree parameter coordinates. -/
theorem integralPolynomialTupleCoefficientHeight_le_boundedDegree
    {N R D : ℕ} (f : Fin R → MvPolynomial (Fin N) ℤ)
    (hdegree : ∀ r, (f r).totalDegree ≤ D) :
    integralPolynomialTupleCoefficientHeight f ≤
      boundedDegreeTupleCoefficientHeight D f := by
  classical
  apply Finset.sup_le
  intro r _hr
  unfold mvPolynomialCoefficientNatAbsMax
  apply Finset.sup_le
  intro m hm
  have hmdegree : Finsupp.degree m ≤ D := by
    simpa [Finsupp.degree_eq_sum, Finsupp.sum_fintype] using
      (MvPolynomial.le_totalDegree hm).trans (hdegree r)
  let b : BoundedDegreeMonomial N D := ⟨m, hmdegree⟩
  have h := Finset.le_sup
    (s := (Finset.univ : Finset (UniversalCoefficientIndex N R D)))
    (f := fun rm ↦ ((f rm.1).coeff rm.2.1).natAbs)
    (Finset.mem_univ (r, b))
  simpa [boundedDegreeTupleCoefficientHeight, b] using h

/-- Consequently the canonical universal-family parameter norm is exactly
the ordinary largest coefficient height. -/
theorem integralParameterNatAbsMax_boundedDegreeCoefficientParameter_eq
    {N R D : ℕ} (f : Fin R → MvPolynomial (Fin N) ℤ)
    (hdegree : ∀ r, (f r).totalDegree ≤ D) :
    integralParameterNatAbsMax
        (boundedDegreeCoefficientParameter (D := D) f) =
      integralPolynomialTupleCoefficientHeight f := by
  rw [integralParameterNatAbsMax_boundedDegreeCoefficientParameter]
  exact le_antisymm (boundedDegreeTupleCoefficientHeight_le f)
    (integralPolynomialTupleCoefficientHeight_le_boundedDegree f hdegree)

/-- Pack exact specialization and exact height control into one reusable
statement.  This theorem is the elementary bridge needed before invoking a
separate relative spreading result. -/
theorem exists_universalBoundedDegreeIntegralPolynomial_specialization
    {N R D : ℕ} (f : Fin R → MvPolynomial (Fin N) ℤ)
    (hdegree : ∀ r, (f r).totalDegree ≤ D) :
    ∃ u : Fin (universalCoefficientParameterCount N R D) → ℤ,
      (∀ r,
        specializeRelativeIntegralAffinePolynomial u
            (universalBoundedDegreeIntegralPolynomial N R D r) = f r) ∧
      integralParameterNatAbsMax u =
        integralPolynomialTupleCoefficientHeight f := by
  refine ⟨boundedDegreeCoefficientParameter (D := D) f, ?_, ?_⟩
  · exact fun r ↦
      specialize_universalBoundedDegreeIntegralPolynomial f hdegree r
  · exact
      integralParameterNatAbsMax_boundedDegreeCoefficientParameter_eq
        f hdegree

end

end TranslatedDepthSeven

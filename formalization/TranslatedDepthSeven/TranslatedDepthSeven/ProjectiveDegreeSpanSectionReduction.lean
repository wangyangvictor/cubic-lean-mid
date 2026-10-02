import TranslatedDepthSeven.ProjectiveDegreeSpanSectionSaturation
import TranslatedDepthSeven.FiniteEquationComponentDimensionInternal
import TranslatedDepthSeven.ProperHomogeneousHypersurfaceComponentDegreeInternal

/-!
# The degree--span inequality reduced to integral Bertini sections

The only geometric existence input is that an integral projective variety
of dimension at least two has a nonempty integral hyperplane section over
an algebraically closed field of characteristic zero. It is stated below
using the literal homogeneous ideals and coordinate-chart saturation.

The input contains no degree bound, Hilbert polynomial, span inequality,
or assertion about linear relations. All these numerical consequences are
proved here using the checked curve case, Krull's height theorem, the
affine altitude formula, the Hilbert-function comparison, and the preceding
finite-dimensional proof that saturation adds no linear equations.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

/-- The ideal-coordinate form of existence of an integral Bertini
hyperplane section. The section ideal is allowed to require saturation.

Reference: J.-P. Jouanolou, *Théorèmes de Bertini et applications*,
Théorème I.6.10; see also O. Benoist, *Le théorème de Bertini en famille*,
Bull. Soc. Math. France 139 (2011), 555--569, Théorème 1.1 with `e = 1`.
Geometric integrality, rather than only irreducibility, is required. -/
def ProjectiveIntegralHyperplaneSectionExists
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] : Prop :=
  ∀ (N r : ℕ) (I : Ideal (MvPolynomial (Fin (N + 1)) K)),
    2 ≤ r → I.IsPrime →
    I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K) →
    ringKrullDim (MvPolynomial (Fin (N + 1)) K ⧸ I) = r + 1 →
    ∃ (L : MvPolynomial (Fin (N + 1)) K)
      (J : Ideal (MvPolynomial (Fin (N + 1)) K)),
      L.IsHomogeneous 1 ∧ L ∉ I ∧ J.IsPrime ∧
      J.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K) ∧
      (∃ i : Fin (N + 1), X i ∉ J) ∧
      I ⊔ Ideal.span ({L} : Set _) ≤ J ∧
      ∀ F ∈ J, ∀ i : Fin (N + 1),
        ∃ k : ℕ, X i ^ k * F ∈ I ⊔ Ideal.span ({L} : Set _)

theorem projectiveSection_saturatedPrime_isMinimal
    {K : Type*} [Field K] {N : ℕ}
    (I J : Ideal (MvPolynomial (Fin (N + 1)) K))
    (L : MvPolynomial (Fin (N + 1)) K) (hJ : J.IsPrime)
    (hchart : ∃ i : Fin (N + 1), X i ∉ J)
    (hle : I ⊔ Ideal.span ({L} : Set _) ≤ J)
    (hsat : ∀ F ∈ J, ∀ i : Fin (N + 1),
      ∃ k : ℕ, X i ^ k * F ∈ I ⊔ Ideal.span ({L} : Set _)) :
    J ∈ (I ⊔ Ideal.span ({L} : Set _)).minimalPrimes := by
  obtain ⟨i, hi⟩ := hchart
  refine ⟨⟨hJ, hle⟩, ?_⟩
  intro P hP hPJ F hF
  obtain ⟨k, hk⟩ := hsat F hF i
  have hprod := hP.2 hk
  exact (hP.1.mem_or_mem hprod).resolve_left
    (fun hp ↦ hi (hPJ (hP.1.mem_of_pow_mem k hp)))

/-- Expected dimension and the sufficient degree upper bound for a prime
chart-saturation of a proper hyperplane section. -/
theorem projectiveSection_saturatedPrime_dimension_degree
    {K : Type*} [Field K] [CharZero K] {N r d : ℕ}
    (I J : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hI : I.IsPrime)
    (hdegree : HasProjectiveDimensionDegree I (r + 1) d)
    (L : MvPolynomial (Fin (N + 1)) K)
    (hLhom : L.IsHomogeneous 1) (hL : L ∉ I)
    (hJ : J.IsPrime)
    (hJhom : J.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hchart : ∃ i : Fin (N + 1), X i ∉ J)
    (hle : I ⊔ Ideal.span ({L} : Set _) ≤ J)
    (hsat : ∀ F ∈ J, ∀ i : Fin (N + 1),
      ∃ k : ℕ, X i ^ k * F ∈ I ⊔ Ideal.span ({L} : Set _)) :
    ∃ e : ℕ, e ≤ d ∧ HasProjectiveDimensionDegree J r e := by
  classical
  let R := MvPolynomial (Fin (N + 1)) K
  letI : I.IsPrime := hI
  letI : J.IsPrime := hJ
  have hminimal := projectiveSection_saturatedPrime_isMinimal I J L hJ hchart hle hsat
  have hIdim : ringKrullDim (R ⧸ I) = ((r + 2 : ℕ) : WithBot ℕ∞) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat, add_assoc, one_add_one_eq_two] using hdegree.1
  obtain ⟨s, hs, hslow⟩ := finiteEquation_minimalComponent_dimension_lower
    K R I J {L} (by simpa only [Finset.coe_singleton] using hminimal) hIdim
  have hlt : I < J := by
    apply lt_of_le_not_ge (le_sup_left.trans hle)
    intro hJI
    exact hL (hJI (hle (Ideal.subset_span (Set.mem_singleton L) |>
      (show Ideal.span ({L} : Set _) ≤ I ⊔ Ideal.span ({L} : Set _) from le_sup_right))))
  have hfinite : ringKrullDim (R ⧸ I) < ⊤ := by
    rw [hIdim]
    exact WithBot.coe_lt_coe.mpr (ENat.coe_lt_top _)
  have hupper := ringKrullDim_quotient_lt_of_prime_lt I J hlt hfinite
  rw [hs, hIdim] at hupper
  have hsup : s < r + 2 := by exact_mod_cast hupper
  have hseq : s = r + 1 := by
    simp only [Finset.card_singleton] at hslow
    omega
  have hJdim : ringKrullDim (R ⧸ J) = r + 1 := by
    rw [hs, hseq]
    push_cast
    rfl
  have hirr : ¬ projectiveIrrelevantIdeal K N ≤ J := by
    obtain ⟨i, hi⟩ := hchart
    intro h
    exact hi (h (Ideal.subset_span ⟨i, rfl⟩))
  obtain ⟨t, e, Q, hcert⟩ := projectiveHilbertDegreeCertification_internal K
    N J hJ hJhom hirr
  have htr : t = r := by
    have hh : t + 1 = r + 1 := by exact_mod_cast hcert.1.symm.trans hJdim
    omega
  subst t
  have hJdegree := hcert.toPublished
  have hmass := sum_projectiveDegrees_proper_homogeneous_hypersurface_le
    I hI hdegree L hLhom hL (fun _ : Fin 1 ↦ J) (fun _ : Fin 1 ↦ e)
    (fun _ _ _ ↦ Subsingleton.elim _ _) (fun _ ↦ hJ) (fun _ ↦ hJhom)
    (fun _ ↦ hJdegree) (fun _ ↦ hle)
  refine ⟨e, ?_, hJdegree⟩
  simpa only [Fin.sum_univ_one, Nat.mul_one] using hmass

/-- The zero-dimensional starting case needs only the constant Hilbert
polynomial and injectivity of multiplication by a surviving coordinate. -/
theorem projectiveSection_zerofold_hilbertOne_le_degree
    {K : Type*} [Field K] {N d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) (hI : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hdegree : HasProjectiveDimensionDegree I 0 d) :
    Module.finrank K (projectiveHilbertPiece K N I 1) ≤ d := by
  obtain ⟨i, hi⟩ := exists_coordinate_not_mem_of_projectiveHilbertDimensionDegree I hdegree.toHilbert
  have hmono : Monotone (fun n ↦ Module.finrank K (projectiveHilbertPiece K N I n)) := by
    apply monotone_nat_of_le_succ
    intro n
    have h := projectiveSection_finrank_recurrence I hI hhom (X i) (isHomogeneous_X K i) hi n
    change _ + Module.finrank K (projectiveHilbertPiece K N I n) =
      Module.finrank K (projectiveHilbertPiece K N I (n + 1)) at h
    omega
  obtain ⟨_, hd, P, hPdeg, hPlc, n₀, hP⟩ := hdegree
  have hPc : P = Polynomial.C (d : ℚ) := by
    have hp := Polynomial.eq_C_of_natDegree_eq_zero hPdeg
    have hc : P.coeff 0 = (d : ℚ) := by
      simpa only [Polynomial.leadingCoeff, hPdeg, Nat.factorial_zero,
        Nat.cast_one, div_one] using hPlc
    simpa only [hc] using hp
  have hval := hP (n₀ + 1) (by omega)
  rw [hPc, Polynomial.eval_C] at hval
  have hv : Module.finrank K (projectiveHilbertPiece K N I (n₀ + 1)) = d := by exact_mod_cast hval
  rw [← hv]
  exact hmono (by omega)

/-- Every-dimensional degree--span over an algebraically closed field,
using only the displayed integral-section existence input. -/
theorem projectiveDegreeSpan_hilbertOne_of_integralHyperplaneSections
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (bertini : ProjectiveIntegralHyperplaneSectionExists K)
    {N r d : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hI : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hdegree : HasProjectiveDimensionDegree I r d) :
    Module.finrank K (projectiveHilbertPiece K N I 1) ≤ r + d := by
  induction r generalizing I d with
  | zero =>
    simpa only [Nat.zero_add] using projectiveSection_zerofold_hilbertOne_le_degree I hI hhom hdegree
  | succ r ih =>
    by_cases hr : r = 0
    · subst r
      have h := projectiveCurve_hilbertOne_le_degree_add_one I hI hhom hdegree
      simpa only [Nat.add_comm d 1] using h
    · obtain ⟨L, J, hLhom, hL, hJ, hJhom, hchart, hle, hsat⟩ :=
        bertini N (r + 1) I (by omega) hI hhom hdegree.1
      obtain ⟨e, hed, hJdegree⟩ := projectiveSection_saturatedPrime_dimension_degree
        I J hI hdegree L hLhom hL hJ hJhom hchart hle hsat
      have hnext := ih J hJ hJhom hJdegree
      have hdrop := projectiveSection_saturation_hilbertOne_add_one
        I J hI hhom L hLhom hL hle hsat
      omega

/-- The exact rational literature interface follows by scalar extension
to `Qbar`, integral hyperplane sections there, and descent of linear span. -/
theorem rationalProjectiveDegreeSpan_of_integralHyperplaneSections
    (bertini : ProjectiveIntegralHyperplaneSectionExists Qbar) :
    StandardAG.ProjectiveDegreeSpanInequality ℚ := by
  intro N r d I hI hgeometric hhom hdegree
  apply projectiveDegreeSpan_descends_coefficientExtension (L := Qbar)
  let Ibar := I.map (MvPolynomial.map (algebraMap ℚ Qbar))
  have hbound := projectiveDegreeSpan_hilbertOne_of_integralHyperplaneSections
    bertini Ibar hgeometric
    (isHomogeneous_map_mvPolynomialMap (algebraMap ℚ Qbar) I hhom)
    (qbarHasProjectiveDimensionDegree_of_rational I hdegree hgeometric)
  have hsum := finrank_degreeOnePart_add_quotientHomogeneousComponent_eq Ibar
  change Module.finrank Qbar
    (quotientHomogeneousComponent Qbar (Fin (N + 1)) Ibar 1) ≤ r + d at hbound
  change N + 1 ≤ Module.finrank Qbar (StandardAG.degreeOnePartInIdeal Ibar) + r + d
  omega

end

end TranslatedDepthSeven

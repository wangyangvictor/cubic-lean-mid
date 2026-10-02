import HessianTheorem11.CubicIrreducibility
import HessianTheorem11.NormalPencil
import HessianTheorem11.HessianDeterminant
import HessianTheorem11.GenericRankBridge
import HessianTheorem11.GeometricFactorization
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import Mathlib.Algebra.Prime.Lemmas

/-!
The corank of a matrix over the function field of a prime divisor contributes
that many powers of the divisor to its determinant. Localization, the residue
field, and denominator cancellation are actual mathlib constructions. The
cubic degree bound then follows from the proved Hessian determinant degree.
-/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Module

section PrimeLocalization
variable {R : Type*} [CommRing R]

/-- The residue map at a prime ideal, with the residue field identified with
the concrete fraction ring of the quotient. -/
def localToGenericResidue (P : Ideal R) [P.IsPrime] :
    Localization.AtPrime P →+* FractionRing (R ⧸ P) :=
  (FractionRing.algEquiv (R ⧸ P) P.ResidueField).symm.toRingHom.comp
    (IsLocalRing.residue (Localization.AtPrime P))

theorem localToGenericResidue_surjective (P : Ideal R) [P.IsPrime] :
    Function.Surjective (localToGenericResidue P) :=
  (FractionRing.algEquiv (R ⧸ P) P.ResidueField).symm.surjective.comp
    IsLocalRing.residue_surjective

@[simp] theorem localToGenericResidue_algebraMap (P : Ideal R) [P.IsPrime] (r : R) :
    localToGenericResidue P (algebraMap R (Localization.AtPrime P) r) =
      algebraMap (R ⧸ P) (FractionRing (R ⧸ P)) (Ideal.Quotient.mk P r) := by
  change (FractionRing.algEquiv (R ⧸ P) P.ResidueField).symm
    (algebraMap R P.ResidueField r) = _
  rw [← Ideal.algebraMap_quotient_residueField_mk]
  exact (FractionRing.algEquiv (R ⧸ P) P.ResidueField).symm.commutes _

theorem localToGenericResidue_kernel (f : R)
    [hP : (Ideal.span ({f} : Set R)).IsPrime] (y : Localization.AtPrime (Ideal.span ({f} : Set R))) :
    localToGenericResidue (Ideal.span ({f} : Set R)) y = 0 ↔
      algebraMap R (Localization.AtPrime (Ideal.span ({f} : Set R))) f ∣ y := by
  let P : Ideal R := Ideal.span {f}
  change (FractionRing.algEquiv (R ⧸ P) P.ResidueField).symm
    (IsLocalRing.residue (Localization.AtPrime P) y) = 0 ↔ _
  rw [map_eq_zero_iff _ (FractionRing.algEquiv (R ⧸ P) P.ResidueField).symm.injective,
    IsLocalRing.residue_eq_zero_iff,
    ← Localization.AtPrime.map_eq_maximalIdeal]
  simp [P, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]

variable [IsDomain R]

/-- A power of a prime element cannot acquire divisibility merely by
localizing away from that prime. The proof clears one actual denominator. -/
theorem prime_pow_dvd_of_localization_dvd
    (f g : R) (hf : Prime f) (m : ℕ)
    [hP : (Ideal.span ({f} : Set R)).IsPrime]
    (hdiv : (algebraMap R (Localization.AtPrime (Ideal.span ({f} : Set R))) f) ^ m ∣
      algebraMap R (Localization.AtPrime (Ideal.span ({f} : Set R))) g) : f ^ m ∣ g := by
  let P : Ideal R := Ideal.span {f}
  let S := Localization.AtPrime P
  change (algebraMap R S f) ^ m ∣ algebraMap R S g at hdiv
  obtain ⟨z, hz⟩ := hdiv
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj P.primeCompl z
  have hseq : g * (s : R) = f ^ m * a := by
    apply IsLocalization.injective S P.primeCompl_le_nonZeroDivisors
    rw [map_mul, hz, mul_assoc, hs, map_mul, map_pow]
  have hfs : ¬ f ∣ (s : R) := by
    intro h
    exact s.property (Ideal.mem_span_singleton.mpr h)
  exact hf.pow_dvd_of_dvd_mul_right m hfs ⟨a, hseq⟩

theorem prime_pow_localization_dvd_iff
    (f g : R) (hf : Prime f) (m : ℕ)
    [(Ideal.span ({f} : Set R)).IsPrime] :
    (algebraMap R (Localization.AtPrime (Ideal.span ({f} : Set R))) f) ^ m ∣
      algebraMap R (Localization.AtPrime (Ideal.span ({f} : Set R))) g ↔ f ^ m ∣ g := by
  constructor
  · exact prime_pow_dvd_of_localization_dvd f g hf m
  · intro h
    simpa only [map_pow] using
      map_dvd (algebraMap R (Localization.AtPrime (Ideal.span ({f} : Set R)))) h

/-- Localization at the prime divisor preserves its actual multiplicity. -/
theorem prime_localization_multiplicity_eq
    (f g : R) (hf : Prime f)
    [(Ideal.span ({f} : Set R)).IsPrime] :
    multiplicity
      (algebraMap R (Localization.AtPrime (Ideal.span ({f} : Set R))) f)
      (algebraMap R (Localization.AtPrime (Ideal.span ({f} : Set R))) g) =
        multiplicity f g := by
  apply multiplicity_eq_of_emultiplicity_eq
  apply emultiplicity_eq_emultiplicity_iff.mpr
  intro m
  exact prime_pow_localization_dvd_iff f g hf m

theorem prime_localization_finiteMultiplicity_iff
    (f g : R) (hf : Prime f)
    [(Ideal.span ({f} : Set R)).IsPrime] :
    FiniteMultiplicity
      (algebraMap R (Localization.AtPrime (Ideal.span ({f} : Set R))) f)
      (algebraMap R (Localization.AtPrime (Ideal.span ({f} : Set R))) g) ↔
        FiniteMultiplicity f g := by
  unfold FiniteMultiplicity
  simp only [prime_pow_localization_dvd_iff f g hf]

/-- Determinant divisibility by generic corank along an actual principal
prime divisor, over any integral domain. -/
theorem prime_pow_generic_corank_dvd_det
    (f : R) (hf : Prime f)
    [hP : (Ideal.span ({f} : Set R)).IsPrime]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) :
    f ^ (Fintype.card ι -
      (M.map ((algebraMap (R ⧸ Ideal.span ({f} : Set R))
        (FractionRing (R ⧸ Ideal.span ({f} : Set R)))).comp
          (Ideal.Quotient.mk (Ideal.span ({f} : Set R))))).rank) ∣ M.det := by
  let P : Ideal R := Ideal.span {f}
  let S := Localization.AtPrime P
  let φ := localToGenericResidue P
  let ιR := algebraMap R S
  let ψ : R →+* FractionRing (R ⧸ P) :=
    (algebraMap (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mk P)
  have hmatrix : φ.mapMatrix (M.map ιR) = M.map ψ := by
    ext i j
    exact localToGenericResidue_algebraMap P (M i j)
  have hdiv := NormalPencil.pow_corank_dvd_det φ (localToGenericResidue_surjective P)
    (ιR f) (localToGenericResidue_kernel f) (M.map ιR)
  have hdet : (M.map ιR).det = ιR M.det := (ιR.map_det M).symm
  rw [hmatrix, hdet] at hdiv
  exact prime_pow_dvd_of_localization_dvd f M.det hf _ hdiv

end PrimeLocalization

section Cubic

/-- The actual geometric cubic divides its Hessian determinant to at least
the generic corank. This is a specialization of the proved prime-divisor
matrix theorem; it assumes no determinant degree or corank inequality. -/
theorem geometric_cubic_pow_genericPoint_corank_dvd_hessianDeterminant
    {n : ℕ} (F : RationalPolynomial n)
    (hF : Irreducible (geometricPolynomial F)) :
    (geometricPolynomial F) ^ (n - genericPointHessianRank F) ∣
      hessianDeterminantPolynomial (geometricPolynomial F) := by
  letI : (Ideal.span ({geometricPolynomial F} : Set (GeometricPolynomial n))).IsPrime :=
    (Ideal.span_singleton_prime hF.ne_zero).mpr hF.prime
  have hdiv := prime_pow_generic_corank_dvd_det (geometricPolynomial F) hF.prime
    (hessianPolynomial (geometricPolynomial F))
  simpa only [Fintype.card_fin, genericPointHessianRank, genericPointHessian,
    genericMatrix, genericPointMap, cubicCoordinateIdeal, hessianDeterminantPolynomial]
    using hdiv

/-- The same divisibility expressed in the geometric-point supremum rank
used in the nine theorem targets. The sole additional input is the universal
open-minor theorem connecting the two actual ranks. -/
theorem geometric_cubic_pow_generic_corank_dvd_hessianDeterminant
    (AG : GenericMatrixRankInput) {n : ℕ} (F : RationalPolynomial n)
    (hF : Irreducible (geometricPolynomial F)) :
    (geometricPolynomial F) ^ (n - genericHessianRank F) ∣
      hessianDeterminantPolynomial (geometricPolynomial F) := by
  rw [genericHessianRank_eq_genericPointHessianRank AG F hF]
  exact geometric_cubic_pow_genericPoint_corank_dvd_hessianDeterminant F hF

/-- Degree bounds for an actual homogeneous polynomial divisor, with
nonzero dividend and divisor explicit. -/
theorem homogeneous_pow_degree_le_of_dvd
    {K σ : Type*} [CommRing K] [IsDomain K]
    {f g : MvPolynomial σ K} {d m N : ℕ}
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hgdegree : g.totalDegree ≤ N) (hdiv : f ^ m ∣ g) : d * m ≤ N := by
  have hpdegree := (hf.pow m).totalDegree (pow_ne_zero m hf0)
  have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hg0
  rw [hpdegree] at hle
  exact hle.trans hgdegree

/-- A nonzero homogeneous polynomial of positive degree has finite
multiplicity in every nonzero polynomial. This prevents any silent use of the
natural-valued multiplicity at infinite order. -/
theorem finiteMultiplicity_of_positive_homogeneous_divisor
    {K σ : Type*} [CommRing K] [IsDomain K]
    {f g : MvPolynomial σ K} {d : ℕ}
    (hf : f.IsHomogeneous d) (hd : 0 < d) (hf0 : f ≠ 0) (hg0 : g ≠ 0) :
    FiniteMultiplicity f g := by
  refine ⟨g.totalDegree, ?_⟩
  intro hdiv
  have hbound := homogeneous_pow_degree_le_of_dvd hf hf0 hg0 le_rfl hdiv
  nlinarith

theorem geometric_hessian_finiteMultiplicity
    (DT : DeterminantalTangentOver ℚ) {n : ℕ} (F : AnisotropicCubic n)
    (hF : Irreducible (geometricPolynomial F.polynomial)) :
    FiniteMultiplicity (geometricPolynomial F.polynomial)
      (hessianDeterminantPolynomial (geometricPolynomial F.polynomial)) :=
  finiteMultiplicity_of_positive_homogeneous_divisor
    (geometric_homogeneous F.homogeneous) (by norm_num) hF.ne_zero
    (geometric_hessianDeterminantPolynomial_ne_zero DT F)

/-- The actual finite divisor multiplicity has the degree bound needed in
the first-normal sieve. -/
theorem geometric_hessian_multiplicity_degree_bound
    (DT : DeterminantalTangentOver ℚ) {n : ℕ} (F : AnisotropicCubic n)
    (hF : Irreducible (geometricPolynomial F.polynomial)) :
    3 * multiplicity (geometricPolynomial F.polynomial)
      (hessianDeterminantPolynomial (geometricPolynomial F.polynomial)) ≤ n :=
  homogeneous_pow_degree_le_of_dvd
    (geometric_homogeneous F.homogeneous) hF.ne_zero
    (geometric_hessianDeterminantPolynomial_ne_zero DT F)
    (hessianDeterminantPolynomial_totalDegree_le (geometric_homogeneous F.homogeneous))
    (pow_multiplicity_dvd _ _)

theorem geometric_hessian_corank_le_multiplicity
    (AG : GenericMatrixRankInput) (DT : DeterminantalTangentOver ℚ)
    {n : ℕ} (F : AnisotropicCubic n)
    (hF : Irreducible (geometricPolynomial F.polynomial)) :
    n - genericHessianRank F.polynomial ≤ multiplicity (geometricPolynomial F.polynomial)
      (hessianDeterminantPolynomial (geometricPolynomial F.polynomial)) :=
  (geometric_hessian_finiteMultiplicity DT F hF).le_multiplicity_of_pow_dvd
    (geometric_cubic_pow_generic_corank_dvd_hessianDeterminant AG F.polynomial hF)

/-- Source Lemma 7.2: three times the actual generic Hessian corank is at
most the number of variables. The determinant nonvanishing used here is
proved from anisotropy, rather than supplied as an input. -/
theorem anisotropic_genericPoint_corank_degree_bound
    (DT : DeterminantalTangentOver ℚ) {n : ℕ} (F : AnisotropicCubic n)
    (hF : Irreducible (geometricPolynomial F.polynomial)) :
    3 * (n - genericPointHessianRank F.polynomial) ≤ n := by
  exact homogeneous_pow_degree_le_of_dvd
    (geometric_homogeneous F.homogeneous) hF.ne_zero
    (geometric_hessianDeterminantPolynomial_ne_zero DT F)
    (hessianDeterminantPolynomial_totalDegree_le (geometric_homogeneous F.homogeneous))
    (geometric_cubic_pow_genericPoint_corank_dvd_hessianDeterminant F.polynomial hF)

theorem anisotropic_generic_corank_degree_bound
    (AG : GenericMatrixRankInput) (DT : DeterminantalTangentOver ℚ)
    {n : ℕ} (F : AnisotropicCubic n)
    (hF : Irreducible (geometricPolynomial F.polynomial)) :
    3 * (n - genericHessianRank F.polynomial) ≤ n := by
  rw [genericHessianRank_eq_genericPointHessianRank AG F.polynomial hF]
  exact anisotropic_genericPoint_corank_degree_bound DT F hF

theorem anisotropic_generic_corank_le_third
    (AG : GenericMatrixRankInput) (DT : DeterminantalTangentOver ℚ)
    {n : ℕ} (F : AnisotropicCubic n)
    (hF : Irreducible (geometricPolynomial F.polynomial)) :
    n - genericHessianRank F.polynomial ≤ n / 3 := by
  have h := anisotropic_generic_corank_degree_bound AG DT F hF
  omega

/-- Internal use of the proved absolute-irreducibility lemma. The public
aggregate supplies `CI` from geometric semistability. -/
theorem anisotropic_generic_corank_le_third_of_textbook
    (CI : CubicGeometricIrreducibility)
    (AG : GenericMatrixRankInput) (DT : DeterminantalTangentOver ℚ)
    {n : ℕ} (F : AnisotropicCubic n) (hn : 4 ≤ n) :
    n - genericHessianRank F.polynomial ≤ n / 3 :=
  anisotropic_generic_corank_le_third AG DT F
    (CI F hn)

end Cubic

end HessianTheorem11

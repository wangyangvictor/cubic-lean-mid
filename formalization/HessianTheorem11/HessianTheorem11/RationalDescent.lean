import HessianTheorem11.FlagTransport

/-!
General optimal-weighted-flag descent, independent of cubics and Hessians.

The two named input structures below isolate textbook results: the existence
and uniqueness of the primitive optimal weighted flag (Dolgachev, Lectures on
Invariant Theory, Theorem 9.4), and ordinary Galois descent of finite flags.
Neither input mentions anisotropy or geometric semistability of a cubic.
The Galois-invariance argument, support invariance, and the assembly are proved.
See TEXTBOOK_INPUT_AUDIT.md for hypotheses and the distinction from ordinary
Hilbert--Mumford over an algebraically closed field.
-/

noncomputable section

namespace HessianTheorem11.RationalDescent

open MvPolynomial
open scoped BigOperators

/-- An actual invertible coordinate system and determinant-one integral
variable weights. Primitivity is specified separately below. -/
structure WeightFrame (K : Type*) [Field K] (n : ℕ) where
  matrix : Matrix (Fin n) (Fin n) K
  injective : Function.Injective matrix.mulVec
  weight : Fin n → ℤ
  sum_zero : ∑ i, weight i = 0

/-- An integral normalization of the ray of weights. -/
def WeightFrame.Primitive {K : Type*} [Field K] {n : ℕ}
    (f : WeightFrame K n) : Prop :=
  Finset.univ.gcd (fun i => (f.weight i).natAbs) = 1

/-- The increasing filtration of the actual vector space induced by a weighted
basis. This records every jump and its integer weight, not just an unweighted
parabolic flag. -/
def WeightFrame.flag {K : Type*} [Field K] {n : ℕ}
    (f : WeightFrame K n) : ℤ → Submodule K (Fin n → K) :=
  fun a => Submodule.span K
    {v | ∃ i, f.weight i ≤ a ∧ v = fun j => f.matrix j i}

def WeightFrame.Positive {K : Type*} [Field K] {n : ℕ}
    (f : WeightFrame K n) (F : MvPolynomial (Fin n) K) : Prop :=
  HasPositiveWeights (PolynomialRestriction.restrict f.matrix F) f.weight

/-- The empty polynomial is assigned minimum weight zero. Optimality is only
used for nonzero unstable forms, so this convention never affects the proof. -/
def minimumWeight {K : Type*} [Field K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (w : Fin n → ℤ) : ℤ :=
  if h : F.support.Nonempty then F.support.inf' h (monomialWeight w) else 0

/-- Normalized instability for the Euclidean Weyl-invariant norm of SL(n).
The primitive condition removes the remaining positive integral scaling. -/
def WeightFrame.instability {K : Type*} [Field K] {n : ℕ}
    (f : WeightFrame K n) (F : MvPolynomial (Fin n) K) : ℝ :=
  (minimumWeight (PolynomialRestriction.restrict f.matrix F) f.weight : ℝ) /
    Real.sqrt (∑ i, (f.weight i : ℝ) ^ 2)

def WeightFrame.Optimal {K : Type*} [Field K] {n : ℕ}
    (f : WeightFrame K n) (F : MvPolynomial (Fin n) K) : Prop :=
  f.Primitive ∧ f.Positive F ∧
    ∀ g : WeightFrame K n, g.instability F ≤ f.instability F

theorem injective_map_matrix_ringEquiv {K : Type*} [Field K] {n : ℕ}
    (σ : K ≃+* K) (B : Matrix (Fin n) (Fin n) K)
    (hB : Function.Injective B.mulVec) : Function.Injective (B.map σ).mulVec := by
  intro x y hxy
  have hpre : B.mulVec (fun i => σ.symm (x i)) =
      B.mulVec (fun i => σ.symm (y i)) := by
    funext i
    apply σ.injective
    simpa [Matrix.mulVec, dotProduct] using congrFun hxy i
  have h := hB hpre
  funext i
  have hi := congrArg σ (congrFun h i)
  simpa using hi

/-- Coefficientwise field conjugation changes the basis, retaining every
integral weight and its primitive normalization. -/
def WeightFrame.conjugate {K : Type*} [Field K] {n : ℕ}
    (f : WeightFrame K n) (σ : K ≃+* K) : WeightFrame K n where
  matrix := f.matrix.map σ
  injective := injective_map_matrix_ringEquiv σ f.matrix f.injective
  weight := f.weight
  sum_zero := f.sum_zero

@[simp] theorem WeightFrame.conjugate_weight {K : Type*} [Field K] {n : ℕ}
    (f : WeightFrame K n) (σ : K ≃+* K) : (f.conjugate σ).weight = f.weight := rfl

@[simp] theorem WeightFrame.conjugate_symm {K : Type*} [Field K] {n : ℕ}
    (f : WeightFrame K n) (σ : K ≃+* K) :
    (f.conjugate σ.symm).conjugate σ = f := by
  cases f
  simp [WeightFrame.conjugate, Matrix.map_map]
  ext i j
  exact σ.apply_symm_apply _

theorem minimumWeight_map {K L : Type*} [Field K] [Field L] {n : ℕ}
    (σ : K →+* L) (F : MvPolynomial (Fin n) K) (w : Fin n → ℤ) :
    minimumWeight (map σ F) w = minimumWeight F w := by
  unfold minimumWeight
  rw [MvPolynomial.support_map_of_injective F σ.injective]

theorem WeightFrame.positive_conjugate_iff {K : Type*} [Field K] {n : ℕ}
    (f : WeightFrame K n) (σ : K ≃+* K) (F : MvPolynomial (Fin n) K) :
    (f.conjugate σ).Positive (map σ.toRingHom F) ↔ f.Positive F := by
  unfold WeightFrame.Positive
  change HasPositiveWeights
    (PolynomialRestriction.restrict (f.matrix.map σ.toRingHom) (map σ.toRingHom F)) f.weight ↔ _
  rw [← PolynomialRestriction.map_restrict σ.toRingHom f.matrix F]
  unfold HasPositiveWeights
  rw [MvPolynomial.support_map_of_injective _ σ.injective]

theorem WeightFrame.instability_conjugate {K : Type*} [Field K] {n : ℕ}
    (f : WeightFrame K n) (σ : K ≃+* K) (F : MvPolynomial (Fin n) K) :
    (f.conjugate σ).instability (map σ.toRingHom F) = f.instability F := by
  unfold WeightFrame.instability
  change (minimumWeight
    (PolynomialRestriction.restrict (f.matrix.map σ.toRingHom) (map σ.toRingHom F))
      f.weight : ℝ) / _ = _
  rw [← PolynomialRestriction.map_restrict σ.toRingHom f.matrix F, minimumWeight_map]
  rfl

theorem WeightFrame.optimal_conjugate {K : Type*} [Field K] {n : ℕ}
    (f : WeightFrame K n) (σ : K ≃+* K) (F : MvPolynomial (Fin n) K)
    (hf : f.Optimal F) : (f.conjugate σ).Optimal (map σ.toRingHom F) := by
  refine ⟨hf.1, (f.positive_conjugate_iff σ F).mpr hf.2.1, ?_⟩
  intro g
  have h := hf.2.2 (g.conjugate σ.symm)
  rw [← (g.conjugate σ.symm).instability_conjugate σ F] at h
  rw [g.conjugate_symm σ] at h
  rwa [f.instability_conjugate σ F]

/-- Textbook optimal-weighted-flag theorem, universally quantified in the
number of variables, degree, and form. `unique_flag` is the primitive integral
version of uniqueness in the SL(n) flag complex, not uniqueness of a splitting.
There are no arithmetic or Hessian hypotheses in this input. -/
structure TextbookOptimalFlags (K : Type*) [Field K] [IsAlgClosed K]
    [CharZero K] : Prop where
  exists_optimal : ∀ {n d : ℕ} (F : MvPolynomial (Fin n) K),
    0 < d → F.IsHomogeneous d → F ≠ 0 →
    (∃ f : WeightFrame K n, f.Positive F) →
    ∃ f : WeightFrame K n, f.Optimal F
  unique_flag : ∀ {n d : ℕ} (F : MvPolynomial (Fin n) K),
    0 < d → F.IsHomogeneous d → F ≠ 0 →
    ∀ f g : WeightFrame K n, f.Optimal F → g.Optimal F → f.flag = g.flag

/-- Actual conjugation invariance of a weighted flag. -/
def WeightFrame.RationalFlag {n : ℕ} (f : WeightFrame GeometricField n) : Prop :=
  ∀ σ : GeometricField ≃ₐ[ℚ] GeometricField,
    (f.conjugate σ.toRingEquiv).flag = f.flag

theorem geometricPolynomial_galois_fixed {n : ℕ} (F : RationalPolynomial n)
    (σ : GeometricField ≃ₐ[ℚ] GeometricField) :
    map σ.toRingHom (geometricPolynomial F) = geometricPolynomial F := by
  ext d
  simp [geometricPolynomial, MvPolynomial.coeff_map]

/-- Uniqueness is used before descent. Galois conjugates preserve the exact
support, weights, norm, and optimality; hence they preserve the entire primitive
weighted flag. No averaging of cocharacters is performed. -/
theorem optimal_flag_galois_fixed
    (input : TextbookOptimalFlags GeometricField) {n d : ℕ}
    (F : RationalPolynomial n) (hd : 0 < d) (hF : F.IsHomogeneous d)
    (hne : F ≠ 0) (f : WeightFrame GeometricField n)
    (hf : f.Optimal (geometricPolynomial F)) : f.RationalFlag := by
  intro σ
  have hconj := f.optimal_conjugate σ.toRingEquiv (geometricPolynomial F) hf
  rw [show σ.toRingEquiv.toRingHom = σ.toRingHom from rfl,
    geometricPolynomial_galois_fixed F σ] at hconj
  have hgeom : geometricPolynomial F ≠ 0 := by
    intro hz
    apply hne
    apply MvPolynomial.map_injective (algebraMap ℚ GeometricField)
      (algebraMap ℚ GeometricField).injective
    simpa [geometricPolynomial] using hz
  exact input.unique_flag (geometricPolynomial F) hd (hF.map _)
    hgeom (f.conjugate σ.toRingEquiv) f hconj hf

/-- Ordinary rational descent of finite weighted flags. Its conclusion is a
rational splitting of the same actual vector-space filtration and the same
integer weights. No polynomial occurs in this input. -/
structure TextbookRationalFlagDescent : Prop where
  split : ∀ {n : ℕ} (f : WeightFrame GeometricField n), f.RationalFlag →
    ∃ g : WeightFrame ℚ n, g.weight = f.weight ∧
      (fun a => Submodule.span GeometricField
        {v | ∃ i, g.weight i ≤ a ∧
          v = fun j => algebraMap ℚ GeometricField (g.matrix j i)}) = f.flag

theorem positiveWeights_map_iff {K L : Type*} [Field K] [Field L] {n : ℕ}
    (φ : K →+* L) (F : MvPolynomial (Fin n) K) (w : Fin n → ℤ) :
    HasPositiveWeights (map φ F) w ↔ HasPositiveWeights F w := by
  unfold HasPositiveWeights
  rw [MvPolynomial.support_map_of_injective F φ.injective]

theorem geometricPolynomial_ne_zero {n : ℕ} (F : RationalPolynomial n)
    (hne : F ≠ 0) : geometricPolynomial F ≠ 0 := by
  intro hz
  apply hne
  apply MvPolynomial.map_injective (algebraMap ℚ GeometricField)
    (algebraMap ℚ GeometricField).injective
  simpa [geometricPolynomial] using hz

/-- Genuine rational zero-instability descent for every positive degree.
The proof passes through an actual canonical weighted flag and a rational
splitting, and uses proved polynomial support transport between splittings.
Both textbook inputs are independent of the form's degree and anisotropy. -/
theorem exists_rational_positive_frame
    (optimal : TextbookOptimalFlags GeometricField)
    (descent : TextbookRationalFlagDescent) {n d : ℕ}
    (F : RationalPolynomial n) (hd : 0 < d) (hF : F.IsHomogeneous d)
    (hne : F ≠ 0)
    (hunstable : ∃ f : WeightFrame GeometricField n,
      f.Positive (geometricPolynomial F)) :
    ∃ g : WeightFrame ℚ n, g.Primitive ∧ g.Positive F := by
  obtain ⟨f, hf⟩ := optimal.exists_optimal (geometricPolynomial F) hd
    (hF.map _) (geometricPolynomial_ne_zero F hne) hunstable
  have hfixed := optimal_flag_galois_fixed optimal F hd hF hne f hf
  obtain ⟨g, hweight, hflag⟩ := descent.split f hfixed
  have hflags : weightFlag f.matrix f.weight =
      weightFlag (g.matrix.map (algebraMap ℚ GeometricField)) f.weight := by
    have hh := hflag
    rw [hweight] at hh
    exact hh.symm
  have hpositive := positiveWeights_of_same_weightFlag (geometricPolynomial F)
    f.matrix (g.matrix.map (algebraMap ℚ GeometricField)) f.weight
    f.injective hflags hf.2.1
  rw [← hweight] at hpositive
  change HasPositiveWeights
    (PolynomialRestriction.restrict (g.matrix.map (algebraMap ℚ GeometricField))
      (map (algebraMap ℚ GeometricField) F)) g.weight at hpositive
  rw [← PolynomialRestriction.map_restrict] at hpositive
  have hgpositive := (positiveWeights_map_iff (algebraMap ℚ GeometricField)
    (PolynomialRestriction.restrict g.matrix F) g.weight).mp hpositive
  refine ⟨g, ?_, hgpositive⟩
  unfold WeightFrame.Primitive
  rw [hweight]
  exact hf.1

/-- General homogeneous-form semistability descends from the proved rational
positive-weight certificate theorem. This statement has no cubic hypotheses. -/
theorem geometric_weightSemistable_of_rational
    (optimal : TextbookOptimalFlags GeometricField)
    (descent : TextbookRationalFlagDescent) {n d : ℕ}
    (F : RationalPolynomial n) (hd : 0 < d) (hF : F.IsHomogeneous d)
    (hne : F ≠ 0) (hsemi : WeightSemistable F) :
    WeightSemistable (geometricPolynomial F) := by
  intro B hB w hsum hpositive
  let f : WeightFrame GeometricField n := ⟨B, hB, w, hsum⟩
  obtain ⟨g, _, hg⟩ := exists_rational_positive_frame optimal descent F hd hF hne
    ⟨f, hpositive⟩
  exact hsemi g.matrix g.injective g.weight g.sum_zero hg

/-- The anisotropy implication is proved after, and separately from, universal
rationality descent. No anisotropy-to-semistability statement is an input. -/
theorem anisotropic_geometric_weightSemistable
    (optimal : TextbookOptimalFlags GeometricField)
    (descent : TextbookRationalFlagDescent) {n : ℕ}
    (F : AnisotropicCubic n) (hn : 0 < n) :
    WeightSemistable (geometricPolynomial F.polynomial) := by
  exact geometric_weightSemistable_of_rational optimal descent F.polynomial
    (by norm_num) F.homogeneous (anisotropic_polynomial_ne_zero hn F)
    (rational_weightSemistable F hn)

end HessianTheorem11.RationalDescent

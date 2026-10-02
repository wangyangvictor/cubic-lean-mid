import TranslatedDepthSeven.RankSevenNodeSurfaceExhaustion
import TranslatedDepthSeven.StandardAlgebraicGeometry
import TranslatedDepthSeven.RelativePersistentMultiplicityCertificate

/-!
# The literal relative family of rank-seven source sections

The source surface equations depend on three finite collections of integral
parameters: the translation vector, the scalar dilation, and the four rows
of the Cramer section matrix.  This file places those parameters in one
fixed polynomial ring and proves that specialization gives exactly
`rankSevenSourceSectionEquationFinset`.

This is the application-specific step needed before invoking any general
relative algebraic geometry.  It contains no component construction,
smoothness assertion, height estimate, or point count.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

local instance rankSevenRelativeSourceSectionPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- Tags for the translation coordinates, the one dilation coordinate,
and the entries of the four-by-fourteen section matrix. -/
abbrev RankSevenSourceSectionParameter :=
  Fin 13 ⊕ (Fin 1 ⊕ (Fin 4 × Fin 14))

/-- The fixed number of parameters in the source-section family. -/
abbrev rankSevenSourceSectionParameterCount :=
  Fintype.card RankSevenSourceSectionParameter

/-- A fixed enumeration of the finite parameter tags. -/
def rankSevenSourceSectionParameterEquiv :
    RankSevenSourceSectionParameter ≃
      Fin rankSevenSourceSectionParameterCount :=
  Fintype.equivFin RankSevenSourceSectionParameter

/-- The coordinate polynomial attached to one parameter tag. -/
def rankSevenSourceSectionParameterPolynomial
    (u : RankSevenSourceSectionParameter) :
    MvPolynomial (Fin rankSevenSourceSectionParameterCount) ℚ :=
  MvPolynomial.X (rankSevenSourceSectionParameterEquiv u)

/-- The rational value of each parameter tag at the displayed integral
translation, dilation, and section matrix. -/
def rankSevenSourceSectionParameterValue
    (x₀ : IntVector 13) (m : ℕ)
    (A : Matrix (Fin 4) (Fin 14) ℤ) :
    RankSevenSourceSectionParameter → ℚ
  | Sum.inl i => (x₀ i : ℚ)
  | Sum.inr (Sum.inl _) => (m : ℚ)
  | Sum.inr (Sum.inr ij) => (A ij.1 ij.2 : ℚ)

/-- Integral parameter values underlying the preceding rational
specialization. -/
def rankSevenSourceSectionIntegralParameterValue
    (x₀ : IntVector 13) (m : ℕ)
    (A : Matrix (Fin 4) (Fin 14) ℤ) :
    RankSevenSourceSectionParameter → ℤ
  | Sum.inl i => x₀ i
  | Sum.inr (Sum.inl _) => (m : ℤ)
  | Sum.inr (Sum.inr ij) => A ij.1 ij.2

/-- Integral parameter values indexed by the fixed enumeration. -/
def rankSevenSourceSectionIntegralParameterVector
    (x₀ : IntVector 13) (m : ℕ)
    (A : Matrix (Fin 4) (Fin 14) ℤ) :
    Fin rankSevenSourceSectionParameterCount → ℤ :=
  fun i ↦ rankSevenSourceSectionIntegralParameterValue x₀ m A
    (rankSevenSourceSectionParameterEquiv.symm i)

@[simp]
theorem rankSevenSourceSectionParameterValue_eq_intCast
    (x₀ : IntVector 13) (m : ℕ)
    (A : Matrix (Fin 4) (Fin 14) ℤ)
    (u : RankSevenSourceSectionParameter) :
    rankSevenSourceSectionParameterValue x₀ m A u =
      (rankSevenSourceSectionIntegralParameterValue x₀ m A u : ℚ) := by
  rcases u with i | u
  · rfl
  · rcases u with j | ij
    · simp [rankSevenSourceSectionParameterValue,
        rankSevenSourceSectionIntegralParameterValue]
    · rfl

/-- The same specialization, indexed by the fixed finite enumeration. -/
def rankSevenSourceSectionParameterVector
    (x₀ : IntVector 13) (m : ℕ)
    (A : Matrix (Fin 4) (Fin 14) ℤ) :
    Fin rankSevenSourceSectionParameterCount → ℚ :=
  fun i ↦ rankSevenSourceSectionParameterValue x₀ m A
    (rankSevenSourceSectionParameterEquiv.symm i)

@[simp]
theorem eval_rankSevenSourceSectionParameterPolynomial
    (x₀ : IntVector 13) (m : ℕ)
    (A : Matrix (Fin 4) (Fin 14) ℤ)
    (u : RankSevenSourceSectionParameter) :
    MvPolynomial.eval (rankSevenSourceSectionParameterVector x₀ m A)
        (rankSevenSourceSectionParameterPolynomial u) =
      rankSevenSourceSectionParameterValue x₀ m A u := by
  simp [rankSevenSourceSectionParameterVector,
    rankSevenSourceSectionParameterPolynomial]

/-- Integral coordinate polynomial attached to one parameter tag. -/
def rankSevenSourceSectionIntegralParameterPolynomial
    (u : RankSevenSourceSectionParameter) :
    MvPolynomial (Fin rankSevenSourceSectionParameterCount) ℤ :=
  MvPolynomial.X (rankSevenSourceSectionParameterEquiv u)

/-- The integral relative pullback underlying
`rankSevenRelativeHomogeneousAffineChange`. -/
def rankSevenRelativeIntegralHomogeneousAffineChange :
    MvPolynomial (Option (Fin 13)) ℤ →+*
      RelativeIntegralAffinePolynomial
        rankSevenSourceSectionParameterCount 14 :=
  MvPolynomial.eval₂Hom (Int.castRingHom _)
    (fun j ↦
      match j with
      | none => MvPolynomial.X ((finSuccEquiv 13).symm none)
      | some i =>
          MvPolynomial.C
              (rankSevenSourceSectionIntegralParameterPolynomial
                (Sum.inl i)) *
              MvPolynomial.X ((finSuccEquiv 13).symm none) +
            MvPolynomial.C
              (rankSevenSourceSectionIntegralParameterPolynomial
                (Sum.inr (Sum.inl 0))) *
              MvPolynomial.X ((finSuccEquiv 13).symm (some i)))

/-- Integral relative transform of one original cone equation. -/
def rankSevenRelativeIntegralConeEquation
    (f : MvPolynomial (Fin 13) ℤ) :
    RelativeIntegralAffinePolynomial
      rankSevenSourceSectionParameterCount 14 :=
  rankSevenRelativeIntegralHomogeneousAffineChange
    (MvPolynomial.rename some f)

/-- Integral relative form of one section row. -/
def rankSevenRelativeIntegralSectionRow (i : Fin 4) :
    RelativeIntegralAffinePolynomial
      rankSevenSourceSectionParameterCount 14 :=
  ∑ j : Fin 14,
    MvPolynomial.C
        (rankSevenSourceSectionIntegralParameterPolynomial
          (Sum.inr (Sum.inr (i, j)))) *
      MvPolynomial.X j

/-- Coefficient extension of an integral relative polynomial to `ℚ`. -/
def rationalizeRankSevenRelativeIntegralPolynomial :
    RelativeIntegralAffinePolynomial
        rankSevenSourceSectionParameterCount 14 →+*
      StandardAG.RelativePolynomial
        rankSevenSourceSectionParameterCount 14 :=
  MvPolynomial.map (MvPolynomial.map (Int.castRingHom ℚ))

/-- The relative pullback `(s,y) ↦ (s,s*x₀+m*y)`, with all coefficients
retained as polynomials in the fixed parameter variables. -/
def rankSevenRelativeHomogeneousAffineChange :
    MvPolynomial (Option (Fin 13)) ℚ →+*
      StandardAG.RelativePolynomial
        rankSevenSourceSectionParameterCount 14 :=
  MvPolynomial.eval₂Hom (algebraMap ℚ _)
    (fun j ↦
      match j with
      | none => MvPolynomial.X ((finSuccEquiv 13).symm none)
      | some i =>
          MvPolynomial.C
              (rankSevenSourceSectionParameterPolynomial (Sum.inl i)) *
              MvPolynomial.X ((finSuccEquiv 13).symm none) +
            MvPolynomial.C
              (rankSevenSourceSectionParameterPolynomial
                (Sum.inr (Sum.inl 0))) *
              MvPolynomial.X ((finSuccEquiv 13).symm (some i)))

/-- One relative row equation for the four-by-fourteen section matrix. -/
def rankSevenRelativeSectionRow (i : Fin 4) :
    StandardAG.RelativePolynomial
      rankSevenSourceSectionParameterCount 14 :=
  ∑ j : Fin 14,
    MvPolynomial.C
        (rankSevenSourceSectionParameterPolynomial
          (Sum.inr (Sum.inr (i, j)))) *
      MvPolynomial.X j

/-- Rationalizing the integral relative cone equation gives the rational
relative equation used above. -/
theorem rationalize_rankSevenRelativeIntegralConeEquation
    (f : MvPolynomial (Fin 13) ℤ) :
    rationalizeRankSevenRelativeIntegralPolynomial
        (rankSevenRelativeIntegralConeEquation f) =
      rankSevenRelativeHomogeneousAffineChange
        (projectiveConeLiftEquation f) := by
  let lhs : MvPolynomial (Fin 13) ℤ →+*
      StandardAG.RelativePolynomial
        rankSevenSourceSectionParameterCount 14 :=
    rationalizeRankSevenRelativeIntegralPolynomial.comp
      (rankSevenRelativeIntegralHomogeneousAffineChange.comp
        (MvPolynomial.rename some).toRingHom)
  let rhs : MvPolynomial (Fin 13) ℤ →+*
      StandardAG.RelativePolynomial
        rankSevenSourceSectionParameterCount 14 :=
    rankSevenRelativeHomogeneousAffineChange.comp
      ((MvPolynomial.rename some).toRingHom.comp
        (MvPolynomial.map (Int.castRingHom ℚ)))
  have hrings : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [lhs, rhs, rationalizeRankSevenRelativeIntegralPolynomial,
        rankSevenRelativeIntegralHomogeneousAffineChange,
        rankSevenRelativeHomogeneousAffineChange]
    · intro i
      simp [lhs, rhs, rationalizeRankSevenRelativeIntegralPolynomial,
        rankSevenRelativeIntegralHomogeneousAffineChange,
        rankSevenRelativeHomogeneousAffineChange,
        rankSevenSourceSectionIntegralParameterPolynomial,
        rankSevenSourceSectionParameterPolynomial]
  simpa only [lhs, rhs, rankSevenRelativeIntegralConeEquation,
    projectiveConeLiftEquation] using RingHom.congr_fun hrings f

/-- Rationalizing an integral relative section row gives the rational row. -/
theorem rationalize_rankSevenRelativeIntegralSectionRow (i : Fin 4) :
    rationalizeRankSevenRelativeIntegralPolynomial
        (rankSevenRelativeIntegralSectionRow i) =
      rankSevenRelativeSectionRow i := by
  simp [rationalizeRankSevenRelativeIntegralPolynomial,
    rankSevenRelativeIntegralSectionRow, rankSevenRelativeSectionRow,
    rankSevenSourceSectionIntegralParameterPolynomial,
    rankSevenSourceSectionParameterPolynomial]

/-- Specialize the coefficients of a relative source-section polynomial. -/
def specializeRankSevenRelativeSourceSectionPolynomial
    (x₀ : IntVector 13) (m : ℕ)
    (A : Matrix (Fin 4) (Fin 14) ℤ) :
    StandardAG.RelativePolynomial
        rankSevenSourceSectionParameterCount 14 →+*
      MvPolynomial (Fin 14) ℚ :=
  MvPolynomial.map
    (MvPolynomial.eval (rankSevenSourceSectionParameterVector x₀ m A))

/-- Specialization commutes with extension of the integral coefficients to
`\mathbb Q`.  This is the coefficient-level bridge between the integral
relative family used for height estimates and the rational family used to
define the actual source surfaces. -/
theorem map_specializeRelativeIntegralAffinePolynomial_rankSeven
    (x₀ : IntVector 13) (m : ℕ)
    (A : Matrix (Fin 4) (Fin 14) ℤ)
    (f : RelativeIntegralAffinePolynomial
      rankSevenSourceSectionParameterCount 14) :
    MvPolynomial.map (Int.castRingHom ℚ)
        (specializeRelativeIntegralAffinePolynomial
          (rankSevenSourceSectionIntegralParameterVector x₀ m A) f) =
      specializeRankSevenRelativeSourceSectionPolynomial x₀ m A
        (rationalizeRankSevenRelativeIntegralPolynomial f) := by
  have hparameter :
      rankSevenSourceSectionParameterVector x₀ m A =
        fun i ↦
          (rankSevenSourceSectionIntegralParameterVector x₀ m A i : ℚ) := by
    funext i
    exact rankSevenSourceSectionParameterValue_eq_intCast x₀ m A
      (rankSevenSourceSectionParameterEquiv.symm i)
  have hcoeff :
      (Int.castRingHom ℚ).comp
          (MvPolynomial.eval
            (rankSevenSourceSectionIntegralParameterVector x₀ m A)) =
        (MvPolynomial.eval
            (rankSevenSourceSectionParameterVector x₀ m A)).comp
          (MvPolynomial.map (Int.castRingHom ℚ)) := by
    rw [hparameter]
    apply MvPolynomial.ringHom_ext
    · intro z
      simp
    · intro i
      simp
  simp only [specializeRelativeIntegralAffinePolynomial,
    specializeRankSevenRelativeSourceSectionPolynomial,
    rationalizeRankSevenRelativeIntegralPolynomial,
    MvPolynomial.map_map]
  rw [hcoeff]

/-- The relative affine-change polynomial specializes to the exact
homogeneous affine pullback and coordinate renaming used by the manuscript
source section. -/
theorem specialize_rankSevenRelativeHomogeneousAffineChange
    (x₀ : IntVector 13) (m : ℕ) (hm : 0 < m)
    (A : Matrix (Fin 4) (Fin 14) ℤ)
    (f : MvPolynomial (Option (Fin 13)) ℚ) :
    specializeRankSevenRelativeSourceSectionPolynomial x₀ m A
        (rankSevenRelativeHomogeneousAffineChange f) =
      MvPolynomial.rename (finSuccEquiv 13).symm
        (homogeneousAffinePolynomialChangeAlgEquiv
          (fun i ↦ (x₀ i : ℚ)) (m : ℚ) (by exact_mod_cast hm.ne')
          f) := by
  let lhs : MvPolynomial (Option (Fin 13)) ℚ →+*
      MvPolynomial (Fin 14) ℚ :=
    (specializeRankSevenRelativeSourceSectionPolynomial x₀ m A).comp
      rankSevenRelativeHomogeneousAffineChange
  let rhs : MvPolynomial (Option (Fin 13)) ℚ →+*
      MvPolynomial (Fin 14) ℚ :=
    (MvPolynomial.rename (finSuccEquiv 13).symm).toRingHom.comp
        (homogeneousAffinePolynomialChangeAlgEquiv
          (fun i ↦ (x₀ i : ℚ)) (m : ℚ)
            (by exact_mod_cast hm.ne')).toRingHom
  have hrings : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [lhs, rhs, rankSevenRelativeHomogeneousAffineChange,
        specializeRankSevenRelativeSourceSectionPolynomial]
    · intro j
      cases j with
      | none =>
          simp [lhs, rhs, rankSevenRelativeHomogeneousAffineChange,
            specializeRankSevenRelativeSourceSectionPolynomial,
            homogeneousAffinePolynomialChangeAlgEquiv,
            homogeneousAffinePolynomialChangeHom]
      | some i =>
          simp [lhs, rhs, rankSevenRelativeHomogeneousAffineChange,
            specializeRankSevenRelativeSourceSectionPolynomial,
            homogeneousAffinePolynomialChangeAlgEquiv,
            homogeneousAffinePolynomialChangeHom,
            rankSevenSourceSectionParameterValue]
  exact RingHom.congr_fun hrings f

/-- A relative section row specializes to the literal row linear
polynomial. -/
theorem specialize_rankSevenRelativeSectionRow
    (x₀ : IntVector 13) (m : ℕ)
    (A : Matrix (Fin 4) (Fin 14) ℤ) (i : Fin 4) :
    specializeRankSevenRelativeSourceSectionPolynomial x₀ m A
        (rankSevenRelativeSectionRow i) =
      rationalMatrixRowLinearPolynomial (A.map ((↑) : ℤ → ℚ)) i := by
  simp [rankSevenRelativeSectionRow,
    specializeRankSevenRelativeSourceSectionPolynomial,
    rationalMatrixRowLinearPolynomial,
    rankSevenSourceSectionParameterValue]

/-- The fixed relative equation family: transformed cone equations and the
four relative section rows. -/
def rankSevenRelativeSourceSectionEquationFinset
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) :
    Finset (StandardAG.RelativePolynomial
      rankSevenSourceSectionParameterCount 14) := by
  classical
  exact
    (projectiveConeLiftEquationFamily equations).image
        rankSevenRelativeHomogeneousAffineChange ∪
      (Finset.univ : Finset (Fin 4)).image rankSevenRelativeSectionRow

/-- The same fixed family before coefficient extension from `ℤ` to `ℚ`.
This is the family to which the elementary relative certificate-height
lemmas apply. -/
def rankSevenRelativeIntegralSourceSectionEquationFinset
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) :
    Finset (RelativeIntegralAffinePolynomial
      rankSevenSourceSectionParameterCount 14) := by
  classical
  exact
    equations.image rankSevenRelativeIntegralConeEquation ∪
      (Finset.univ : Finset (Fin 4)).image
        rankSevenRelativeIntegralSectionRow

/-- Coefficient extension of the integral relative family is exactly the
rational relative family. -/
theorem rationalize_rankSevenRelativeIntegralSourceSectionEquationFinset
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) :
    (rankSevenRelativeIntegralSourceSectionEquationFinset equations).image
        rationalizeRankSevenRelativeIntegralPolynomial =
      rankSevenRelativeSourceSectionEquationFinset equations := by
  classical
  ext g
  simp only [rankSevenRelativeIntegralSourceSectionEquationFinset,
    rankSevenRelativeSourceSectionEquationFinset, Finset.mem_image,
    Finset.mem_union, projectiveConeLiftEquationFamily]
  constructor
  · rintro ⟨h, (⟨f, hf, rfl⟩ | ⟨i, _hi, rfl⟩), rfl⟩
    · left
      exact ⟨projectiveConeLiftEquation f, ⟨f, hf, rfl⟩,
        rationalize_rankSevenRelativeIntegralConeEquation f |>.symm⟩
    · right
      exact ⟨i, Finset.mem_univ i,
        rationalize_rankSevenRelativeIntegralSectionRow i |>.symm⟩
  · rintro (⟨h, ⟨f, hf, rfl⟩, rfl⟩ | ⟨i, _hi, rfl⟩)
    · exact ⟨rankSevenRelativeIntegralConeEquation f,
        Or.inl ⟨f, hf, rfl⟩,
        rationalize_rankSevenRelativeIntegralConeEquation f⟩
    · exact ⟨rankSevenRelativeIntegralSectionRow i,
        Or.inr ⟨i, Finset.mem_univ i, rfl⟩,
        rationalize_rankSevenRelativeIntegralSectionRow i⟩

/-- Integral specialization of the fixed source-section family. -/
def specializeRankSevenRelativeIntegralSourceSectionEquationFinset
    (x₀ : IntVector 13) (m : ℕ)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (A : Matrix (Fin 4) (Fin 14) ℤ) :
    Finset (MvPolynomial (Fin 14) ℤ) :=
  (rankSevenRelativeIntegralSourceSectionEquationFinset equations).image
    (specializeRelativeIntegralAffinePolynomial
      (rankSevenSourceSectionIntegralParameterVector x₀ m A))

/-- Extending the specialized integral family to `\mathbb Q` gives exactly
the specialization of the rational relative family.  No fibre ideal or
component is inserted in this identity. -/
theorem map_specializeRankSevenRelativeIntegralSourceSectionEquationFinset
    (x₀ : IntVector 13) (m : ℕ)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (A : Matrix (Fin 4) (Fin 14) ℤ) :
    (specializeRankSevenRelativeIntegralSourceSectionEquationFinset
        x₀ m equations A).image
        (MvPolynomial.map (Int.castRingHom ℚ)) =
      (rankSevenRelativeSourceSectionEquationFinset equations).image
        (specializeRankSevenRelativeSourceSectionPolynomial x₀ m A) := by
  classical
  rw [specializeRankSevenRelativeIntegralSourceSectionEquationFinset,
    Finset.image_image]
  calc
    (rankSevenRelativeIntegralSourceSectionEquationFinset equations).image
        ((MvPolynomial.map (Int.castRingHom ℚ)) ∘
          specializeRelativeIntegralAffinePolynomial
            (rankSevenSourceSectionIntegralParameterVector x₀ m A)) =
      (rankSevenRelativeIntegralSourceSectionEquationFinset equations).image
        (specializeRankSevenRelativeSourceSectionPolynomial x₀ m A ∘
          rationalizeRankSevenRelativeIntegralPolynomial) := by
            apply Finset.image_congr
            intro f hf
            exact map_specializeRelativeIntegralAffinePolynomial_rankSeven
              x₀ m A f
    _ = ((rankSevenRelativeIntegralSourceSectionEquationFinset equations).image
          rationalizeRankSevenRelativeIntegralPolynomial).image
            (specializeRankSevenRelativeSourceSectionPolynomial x₀ m A) := by
              rw [Finset.image_image]
    _ = (rankSevenRelativeSourceSectionEquationFinset equations).image
          (specializeRankSevenRelativeSourceSectionPolynomial x₀ m A) := by
            rw [rationalize_rankSevenRelativeIntegralSourceSectionEquationFinset]

/-- Specializing the one fixed relative family gives, literally, the
source-section family selected for any actual packet. -/
theorem specialize_rankSevenRelativeSourceSectionEquationFinset
    (x₀ : IntVector 13) (m : ℕ) (hm : 0 < m)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (A : Matrix (Fin 4) (Fin 14) ℤ) :
    (rankSevenRelativeSourceSectionEquationFinset equations).image
        (specializeRankSevenRelativeSourceSectionPolynomial x₀ m A) =
      rankSevenSourceSectionEquationFinset x₀ m hm equations
        (A.map ((↑) : ℤ → ℚ)) := by
  classical
  ext g
  simp only [rankSevenRelativeSourceSectionEquationFinset,
    Finset.mem_image, Finset.mem_union,
    rankSevenSourceSectionEquationFinset,
    translatedProjectiveConeLiftEquationFamily,
    finiteFamilyHomogeneousAffineChange,
    rationalMatrixRowLinearEquationFamily]
  constructor
  · rintro ⟨h, (⟨f, hf, rfl⟩ | ⟨i, _hi, rfl⟩), rfl⟩
    · left
      refine ⟨homogeneousAffinePolynomialChangeAlgEquiv
        (fun i ↦ (x₀ i : ℚ)) (m : ℚ) (by exact_mod_cast hm.ne') f, ?_, ?_⟩
      · exact ⟨f, hf, rfl⟩
      · exact (specialize_rankSevenRelativeHomogeneousAffineChange
          x₀ m hm A f).symm
    · right
      exact ⟨i, Finset.mem_univ i,
        (specialize_rankSevenRelativeSectionRow x₀ m A i).symm⟩
  · rintro (⟨h, ⟨f, hf, rfl⟩, rfl⟩ | ⟨i, _hi, rfl⟩)
    · refine ⟨rankSevenRelativeHomogeneousAffineChange f, ?_, ?_⟩
      · left
        exact ⟨f, hf, rfl⟩
      · exact specialize_rankSevenRelativeHomogeneousAffineChange
          x₀ m hm A f
    · refine ⟨rankSevenRelativeSectionRow i, ?_, ?_⟩
      · right
        exact ⟨i, Finset.mem_univ i, rfl⟩
      · exact specialize_rankSevenRelativeSectionRow x₀ m A i

/-- The preceding family identity applied to the literal integral Cramer
matrix selected by an actual residue packet.  Thus every source section
which can occur in the persistent argument is a fibre of this one fixed
relative family. -/
theorem specialize_rankSevenRelativeSourceSectionEquationFinset_selected
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q : ReservoirModulus P k) (z : IntVector 13) :
    let A := selectedRankSevenPacketSectionMatrix p x₀ equations CF C q.1
      (integralResidueVector z : Fin 13 → ZMod q.1)
    (rankSevenRelativeSourceSectionEquationFinset equations).image
        (specializeRankSevenRelativeSourceSectionPolynomial x₀ p.m A) =
      rankSevenStaticSourceSectionEquations p x₀ equations CF C denominator
        P k hP hlower q z := by
  dsimp only
  simpa only [rankSevenStaticSourceSectionEquations,
    rankSevenSourceSectionEquationsAtResidue] using
      specialize_rankSevenRelativeSourceSectionEquationFinset
        x₀ p.m p.hm equations
          (selectedRankSevenPacketSectionMatrix p x₀ equations CF C q.1
            (integralResidueVector z : Fin 13 → ZMod q.1))

/-- The actual source-section equations in every selected packet are the
coefficient extension of a specialization of the single fixed integral
relative family.  This is the exact global-family endpoint needed by any
effective elimination or relative-chart theorem. -/
theorem map_specializeRankSevenRelativeIntegralSourceSectionEquationFinset_selected
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q : ReservoirModulus P k) (z : IntVector 13) :
    let A := selectedRankSevenPacketSectionMatrix p x₀ equations CF C q.1
      (integralResidueVector z : Fin 13 → ZMod q.1)
    (specializeRankSevenRelativeIntegralSourceSectionEquationFinset
        x₀ p.m equations A).image
        (MvPolynomial.map (Int.castRingHom ℚ)) =
      rankSevenStaticSourceSectionEquations p x₀ equations CF C denominator
        P k hP hlower q z := by
  dsimp only
  calc
    (specializeRankSevenRelativeIntegralSourceSectionEquationFinset
        x₀ p.m equations
          (selectedRankSevenPacketSectionMatrix p x₀ equations CF C q.1
            (integralResidueVector z : Fin 13 → ZMod q.1))).image
        (MvPolynomial.map (Int.castRingHom ℚ)) =
      (rankSevenRelativeSourceSectionEquationFinset equations).image
        (specializeRankSevenRelativeSourceSectionPolynomial x₀ p.m
          (selectedRankSevenPacketSectionMatrix p x₀ equations CF C q.1
            (integralResidueVector z : Fin 13 → ZMod q.1))) :=
      map_specializeRankSevenRelativeIntegralSourceSectionEquationFinset
        x₀ p.m equations
          (selectedRankSevenPacketSectionMatrix p x₀ equations CF C q.1
            (integralResidueVector z : Fin 13 → ZMod q.1))
    _ = rankSevenStaticSourceSectionEquations p x₀ equations CF C denominator
          P k hP hlower q z :=
      specialize_rankSevenRelativeSourceSectionEquationFinset_selected
        p x₀ equations CF C denominator P k hP hlower q z

/-- Every integral parameter in an actual occupied source section is
bounded by one fixed power of the manuscript height.  The exponent `39` is
chosen before any epsilon and is exactly the already-proved Cramer entry
exponent. -/
theorem selected_rankSevenSourceSectionIntegralParameterValue_natAbs_cast_le
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p equations CF)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q : ReservoirModulus P k) (z : IntVector 13)
    (hz : z ∈ rankSevenChartReservoirCell
      p x₀ equations CF C denominator q.1)
    (u : RankSevenSourceSectionParameter) :
    ((rankSevenSourceSectionIntegralParameterValue x₀ p.m
      (selectedRankSevenPacketSectionMatrix p x₀ equations CF C q.1
        (integralResidueVector z : Fin 13 → ZMod q.1)) u).natAbs : ℝ) ≤
      p.H ^ (39 : ℕ) := by
  have hHpow : p.H ≤ p.H ^ (39 : ℕ) := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ (p.one_le_T.trans p.T_le_H) (by norm_num : 1 ≤ 39))
  rcases u with i | u
  · have hcoord : ((x₀ i).natAbs : ℝ) ≤
        (depthSevenProjectionBaseHeight x₀ : ℝ) := by
      exact_mod_cast coordinate_le_depthSevenProjectionBaseHeight x₀ i
    exact hcoord.trans
      ((depthSevenProjectionBaseHeight_cast_le p equations CF hx₀).trans hHpow)
  · rcases u with j | ij
    · have hmH : (p.m : ℝ) ≤ p.H := by
        unfold Parameters.H
        nlinarith [p.hB, p.hL]
      simpa [rankSevenSourceSectionIntegralParameterValue] using
        hmH.trans hHpow
    · have hentry := selectedRankSevenPacketSectionMatrix_entry_le
        p x₀ equations CF C denominator P k hP hlower q z hz ij.1 ij.2
      have hentryReal :
          (((selectedRankSevenPacketSectionMatrix p x₀ equations CF C q.1
            (integralResidueVector z : Fin 13 → ZMod q.1))
              ij.1 ij.2).natAbs : ℝ) ≤
            (depthSevenPacketSectionEntryBound p : ℝ) := by
        exact_mod_cast hentry
      exact hentryReal.trans (depthSevenPacketSectionEntryBound_cast_le p)

/-- Natural-number form of the same parameter bound, ready for the fixed
polynomial evaluation lemmas. -/
theorem selected_rankSevenSourceSectionIntegralParameterVector_natAbs_le
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p equations CF)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q : ReservoirModulus P k) (z : IntVector 13)
    (hz : z ∈ rankSevenChartReservoirCell
      p x₀ equations CF C denominator q.1) :
    ∀ i,
      (rankSevenSourceSectionIntegralParameterVector x₀ p.m
        (selectedRankSevenPacketSectionMatrix p x₀ equations CF C q.1
          (integralResidueVector z : Fin 13 → ZMod q.1)) i).natAbs ≤
        ⌈p.H ^ (39 : ℕ)⌉₊ := by
  intro i
  have hreal :=
    selected_rankSevenSourceSectionIntegralParameterValue_natAbs_cast_le
      p x₀ equations CF hx₀ C denominator P k hP hlower q z hz
        (rankSevenSourceSectionParameterEquiv.symm i)
  have hceil := (Nat.le_ceil (p.H ^ (39 : ℕ)))
  exact_mod_cast (show
    ((rankSevenSourceSectionIntegralParameterVector x₀ p.m
      (selectedRankSevenPacketSectionMatrix p x₀ equations CF C q.1
        (integralResidueVector z : Fin 13 → ZMod q.1)) i).natAbs : ℝ) ≤
        (⌈p.H ^ (39 : ℕ)⌉₊ : ℝ) from
      (by
        simpa only [rankSevenSourceSectionIntegralParameterVector] using
          hreal.trans hceil))

end

end TranslatedDepthSeven

import TranslatedDepthSeven.EffectiveFixedRelativeCurveCover
import TranslatedDepthSeven.IsolatedVertexQuotientStaticPacketLabel
import TranslatedDepthSeven.RankSevenRelativeSourceSectionFamily
import TranslatedDepthSeven.RankSevenSourceSectionVertexInternal

/-!
# A fixed relative family for the isolated-vertex quotient curves

The quotient node depends on the twelve translated lower coordinates, one
nonzero scale, and the entries of the selected four-by-thirteen packet
plane.  This file puts those values into one fixed integral relative family
and proves that specialization gives exactly the literal translated cone
plus the four packet-plane rows.  It contains no component selection,
smoothness, certificate, or point-count conclusion.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

local instance isolatedVertexQuotientRelativeSourceSectionFamilyPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- Tags for the twelve translation coordinates, the scale, and the
four-by-thirteen packet-plane matrix. -/
abbrev IsolatedVertexQuotientSourceSectionParameter :=
  Fin 12 ⊕ (Fin 1 ⊕ (Fin 4 × Fin 13))

abbrev isolatedVertexQuotientSourceSectionParameterCount :=
  Fintype.card IsolatedVertexQuotientSourceSectionParameter

def isolatedVertexQuotientSourceSectionParameterEquiv :
    IsolatedVertexQuotientSourceSectionParameter ≃
      Fin isolatedVertexQuotientSourceSectionParameterCount :=
  Fintype.equivFin IsolatedVertexQuotientSourceSectionParameter

def isolatedVertexQuotientSourceSectionParameterPolynomial
    (u : IsolatedVertexQuotientSourceSectionParameter) :
    MvPolynomial (Fin isolatedVertexQuotientSourceSectionParameterCount) ℚ :=
  X (isolatedVertexQuotientSourceSectionParameterEquiv u)

def isolatedVertexQuotientSourceSectionIntegralParameterPolynomial
    (u : IsolatedVertexQuotientSourceSectionParameter) :
    MvPolynomial (Fin isolatedVertexQuotientSourceSectionParameterCount) ℤ :=
  X (isolatedVertexQuotientSourceSectionParameterEquiv u)

def isolatedVertexQuotientSourceSectionParameterValue
    (b : IntVector 12) (m : ℤ)
    (A : Matrix (Fin 4) (Fin 13) ℤ) :
    IsolatedVertexQuotientSourceSectionParameter → ℚ
  | Sum.inl i => (b i : ℚ)
  | Sum.inr (Sum.inl _) => (m : ℚ)
  | Sum.inr (Sum.inr ij) => (A ij.1 ij.2 : ℚ)

def isolatedVertexQuotientSourceSectionIntegralParameterValue
    (b : IntVector 12) (m : ℤ)
    (A : Matrix (Fin 4) (Fin 13) ℤ) :
    IsolatedVertexQuotientSourceSectionParameter → ℤ
  | Sum.inl i => b i
  | Sum.inr (Sum.inl _) => m
  | Sum.inr (Sum.inr ij) => A ij.1 ij.2

def isolatedVertexQuotientSourceSectionIntegralParameterVector
    (b : IntVector 12) (m : ℤ)
    (A : Matrix (Fin 4) (Fin 13) ℤ) :
    Fin isolatedVertexQuotientSourceSectionParameterCount → ℤ :=
  fun i ↦ isolatedVertexQuotientSourceSectionIntegralParameterValue b m A
    (isolatedVertexQuotientSourceSectionParameterEquiv.symm i)

def isolatedVertexQuotientSourceSectionParameterVector
    (b : IntVector 12) (m : ℤ)
    (A : Matrix (Fin 4) (Fin 13) ℤ) :
    Fin isolatedVertexQuotientSourceSectionParameterCount → ℚ :=
  fun i ↦ isolatedVertexQuotientSourceSectionParameterValue b m A
    (isolatedVertexQuotientSourceSectionParameterEquiv.symm i)

@[simp]
theorem isolatedVertexQuotientSourceSectionParameterValue_eq_intCast
    (b : IntVector 12) (m : ℤ)
    (A : Matrix (Fin 4) (Fin 13) ℤ)
    (u : IsolatedVertexQuotientSourceSectionParameter) :
    isolatedVertexQuotientSourceSectionParameterValue b m A u =
      (isolatedVertexQuotientSourceSectionIntegralParameterValue b m A u : ℚ) := by
  rcases u with i | u
  · rfl
  · rcases u with j | ij <;> rfl

@[simp]
theorem eval_isolatedVertexQuotientSourceSectionParameterPolynomial
    (b : IntVector 12) (m : ℤ)
    (A : Matrix (Fin 4) (Fin 13) ℤ)
    (u : IsolatedVertexQuotientSourceSectionParameter) :
    eval (isolatedVertexQuotientSourceSectionParameterVector b m A)
        (isolatedVertexQuotientSourceSectionParameterPolynomial u) =
      isolatedVertexQuotientSourceSectionParameterValue b m A u := by
  simp [isolatedVertexQuotientSourceSectionParameterVector,
    isolatedVertexQuotientSourceSectionParameterPolynomial]

/-- Integral relative homogeneous affine change in the quotient
coordinates. -/
def isolatedVertexQuotientRelativeIntegralHomogeneousAffineChange :
    MvPolynomial (Option (Fin 12)) ℤ →+*
      RelativeIntegralAffinePolynomial
        isolatedVertexQuotientSourceSectionParameterCount 13 :=
  eval₂Hom (Int.castRingHom _)
    (fun j ↦
      match j with
      | none => X ((finSuccEquiv 12).symm none)
      | some i =>
          C (isolatedVertexQuotientSourceSectionIntegralParameterPolynomial
              (Sum.inl i)) * X ((finSuccEquiv 12).symm none) +
            C (isolatedVertexQuotientSourceSectionIntegralParameterPolynomial
              (Sum.inr (Sum.inl 0))) *
              X ((finSuccEquiv 12).symm (some i)))

def isolatedVertexQuotientRelativeIntegralConeEquation
    (f : MvPolynomial (Fin 12) ℤ) :
    RelativeIntegralAffinePolynomial
      isolatedVertexQuotientSourceSectionParameterCount 13 :=
  isolatedVertexQuotientRelativeIntegralHomogeneousAffineChange
    (rename some f)

def isolatedVertexQuotientRelativeIntegralSectionRow (i : Fin 4) :
    RelativeIntegralAffinePolynomial
      isolatedVertexQuotientSourceSectionParameterCount 13 :=
  ∑ j : Fin 13,
    C (isolatedVertexQuotientSourceSectionIntegralParameterPolynomial
      (Sum.inr (Sum.inr (i, j)))) * X j

def rationalizeIsolatedVertexQuotientRelativeIntegralPolynomial :
    RelativeIntegralAffinePolynomial
        isolatedVertexQuotientSourceSectionParameterCount 13 →+*
      StandardAG.RelativePolynomial
        isolatedVertexQuotientSourceSectionParameterCount 13 :=
  map (map (Int.castRingHom ℚ))

def isolatedVertexQuotientRelativeHomogeneousAffineChange :
    MvPolynomial (Option (Fin 12)) ℚ →+*
      StandardAG.RelativePolynomial
        isolatedVertexQuotientSourceSectionParameterCount 13 :=
  eval₂Hom (algebraMap ℚ _)
    (fun j ↦
      match j with
      | none => X ((finSuccEquiv 12).symm none)
      | some i =>
          C (isolatedVertexQuotientSourceSectionParameterPolynomial
              (Sum.inl i)) * X ((finSuccEquiv 12).symm none) +
            C (isolatedVertexQuotientSourceSectionParameterPolynomial
              (Sum.inr (Sum.inl 0))) *
              X ((finSuccEquiv 12).symm (some i)))

def isolatedVertexQuotientRelativeSectionRow (i : Fin 4) :
    StandardAG.RelativePolynomial
      isolatedVertexQuotientSourceSectionParameterCount 13 :=
  ∑ j : Fin 13,
    C (isolatedVertexQuotientSourceSectionParameterPolynomial
      (Sum.inr (Sum.inr (i, j)))) * X j

theorem rationalize_isolatedVertexQuotientRelativeIntegralConeEquation
    (f : MvPolynomial (Fin 12) ℤ) :
    rationalizeIsolatedVertexQuotientRelativeIntegralPolynomial
        (isolatedVertexQuotientRelativeIntegralConeEquation f) =
      isolatedVertexQuotientRelativeHomogeneousAffineChange
        (projectiveConeLiftEquation f) := by
  let lhs : MvPolynomial (Fin 12) ℤ →+*
      StandardAG.RelativePolynomial
        isolatedVertexQuotientSourceSectionParameterCount 13 :=
    rationalizeIsolatedVertexQuotientRelativeIntegralPolynomial.comp
      (isolatedVertexQuotientRelativeIntegralHomogeneousAffineChange.comp
        (rename some).toRingHom)
  let rhs : MvPolynomial (Fin 12) ℤ →+*
      StandardAG.RelativePolynomial
        isolatedVertexQuotientSourceSectionParameterCount 13 :=
    isolatedVertexQuotientRelativeHomogeneousAffineChange.comp
      ((rename some).toRingHom.comp (map (Int.castRingHom ℚ)))
  have hrings : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [lhs, rhs,
        rationalizeIsolatedVertexQuotientRelativeIntegralPolynomial,
        isolatedVertexQuotientRelativeIntegralHomogeneousAffineChange,
        isolatedVertexQuotientRelativeHomogeneousAffineChange]
    · intro i
      simp [lhs, rhs,
        rationalizeIsolatedVertexQuotientRelativeIntegralPolynomial,
        isolatedVertexQuotientRelativeIntegralHomogeneousAffineChange,
        isolatedVertexQuotientRelativeHomogeneousAffineChange,
        isolatedVertexQuotientSourceSectionIntegralParameterPolynomial,
        isolatedVertexQuotientSourceSectionParameterPolynomial]
  simpa only [lhs, rhs,
    isolatedVertexQuotientRelativeIntegralConeEquation,
    projectiveConeLiftEquation] using RingHom.congr_fun hrings f

theorem rationalize_isolatedVertexQuotientRelativeIntegralSectionRow
    (i : Fin 4) :
    rationalizeIsolatedVertexQuotientRelativeIntegralPolynomial
        (isolatedVertexQuotientRelativeIntegralSectionRow i) =
      isolatedVertexQuotientRelativeSectionRow i := by
  simp [rationalizeIsolatedVertexQuotientRelativeIntegralPolynomial,
    isolatedVertexQuotientRelativeIntegralSectionRow,
    isolatedVertexQuotientRelativeSectionRow,
    isolatedVertexQuotientSourceSectionIntegralParameterPolynomial,
    isolatedVertexQuotientSourceSectionParameterPolynomial]

def specializeIsolatedVertexQuotientRelativeSourceSectionPolynomial
    (b : IntVector 12) (m : ℤ)
    (A : Matrix (Fin 4) (Fin 13) ℤ) :
    StandardAG.RelativePolynomial
        isolatedVertexQuotientSourceSectionParameterCount 13 →+*
      MvPolynomial (Fin 13) ℚ :=
  map (eval (isolatedVertexQuotientSourceSectionParameterVector b m A))

theorem map_specializeRelativeIntegralAffinePolynomial_isolatedVertexQuotient
    (b : IntVector 12) (m : ℤ)
    (A : Matrix (Fin 4) (Fin 13) ℤ)
    (f : RelativeIntegralAffinePolynomial
      isolatedVertexQuotientSourceSectionParameterCount 13) :
    map (Int.castRingHom ℚ)
        (specializeRelativeIntegralAffinePolynomial
          (isolatedVertexQuotientSourceSectionIntegralParameterVector b m A) f) =
      specializeIsolatedVertexQuotientRelativeSourceSectionPolynomial b m A
        (rationalizeIsolatedVertexQuotientRelativeIntegralPolynomial f) := by
  have hparameter :
      isolatedVertexQuotientSourceSectionParameterVector b m A =
        fun i ↦
          (isolatedVertexQuotientSourceSectionIntegralParameterVector
            b m A i : ℚ) := by
    funext i
    exact isolatedVertexQuotientSourceSectionParameterValue_eq_intCast
      b m A (isolatedVertexQuotientSourceSectionParameterEquiv.symm i)
  have hcoeff :
      (Int.castRingHom ℚ).comp
          (eval
            (isolatedVertexQuotientSourceSectionIntegralParameterVector
              b m A)) =
        (eval
            (isolatedVertexQuotientSourceSectionParameterVector b m A)).comp
          (map (Int.castRingHom ℚ)) := by
    rw [hparameter]
    apply MvPolynomial.ringHom_ext
    · intro z
      simp
    · intro i
      simp
  simp only [specializeRelativeIntegralAffinePolynomial,
    specializeIsolatedVertexQuotientRelativeSourceSectionPolynomial,
    rationalizeIsolatedVertexQuotientRelativeIntegralPolynomial,
    MvPolynomial.map_map]
  rw [hcoeff]

theorem specialize_isolatedVertexQuotientRelativeHomogeneousAffineChange
    (b : IntVector 12) (m : ℤ) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Fin 13) ℤ)
    (f : MvPolynomial (Option (Fin 12)) ℚ) :
    specializeIsolatedVertexQuotientRelativeSourceSectionPolynomial b m A
        (isolatedVertexQuotientRelativeHomogeneousAffineChange f) =
      rename (finSuccEquiv 12).symm
        (homogeneousAffinePolynomialChangeAlgEquiv
          (fun i ↦ (b i : ℚ)) (m : ℚ) (by exact_mod_cast hm) f) := by
  let lhs : MvPolynomial (Option (Fin 12)) ℚ →+*
      MvPolynomial (Fin 13) ℚ :=
    (specializeIsolatedVertexQuotientRelativeSourceSectionPolynomial
      b m A).comp isolatedVertexQuotientRelativeHomogeneousAffineChange
  let rhs : MvPolynomial (Option (Fin 12)) ℚ →+*
      MvPolynomial (Fin 13) ℚ :=
    (rename (finSuccEquiv 12).symm).toRingHom.comp
      (homogeneousAffinePolynomialChangeAlgEquiv
        (fun i ↦ (b i : ℚ)) (m : ℚ)
          (by exact_mod_cast hm)).toRingHom
  have hrings : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [lhs, rhs,
        isolatedVertexQuotientRelativeHomogeneousAffineChange,
        specializeIsolatedVertexQuotientRelativeSourceSectionPolynomial]
    · intro j
      cases j with
      | none =>
          simp [lhs, rhs,
            isolatedVertexQuotientRelativeHomogeneousAffineChange,
            specializeIsolatedVertexQuotientRelativeSourceSectionPolynomial,
            homogeneousAffinePolynomialChangeAlgEquiv,
            homogeneousAffinePolynomialChangeHom]
      | some i =>
          simp [lhs, rhs,
            isolatedVertexQuotientRelativeHomogeneousAffineChange,
            specializeIsolatedVertexQuotientRelativeSourceSectionPolynomial,
            homogeneousAffinePolynomialChangeAlgEquiv,
            homogeneousAffinePolynomialChangeHom,
            isolatedVertexQuotientSourceSectionParameterValue]
  exact RingHom.congr_fun hrings f

theorem specialize_isolatedVertexQuotientRelativeSectionRow
    (b : IntVector 12) (m : ℤ)
    (A : Matrix (Fin 4) (Fin 13) ℤ) (i : Fin 4) :
    specializeIsolatedVertexQuotientRelativeSourceSectionPolynomial b m A
        (isolatedVertexQuotientRelativeSectionRow i) =
      rationalMatrixRowLinearPolynomial (A.map ((↑) : ℤ → ℚ)) i := by
  simp [isolatedVertexQuotientRelativeSectionRow,
    specializeIsolatedVertexQuotientRelativeSourceSectionPolynomial,
    rationalMatrixRowLinearPolynomial,
    isolatedVertexQuotientSourceSectionParameterValue]

/-- The fixed integral relative quotient family. -/
def isolatedVertexQuotientRelativeIntegralSourceSectionEquationFinset
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ)) :
    Finset (RelativeIntegralAffinePolynomial
      isolatedVertexQuotientSourceSectionParameterCount 13) := by
  classical
  exact lowerEquations.image
      isolatedVertexQuotientRelativeIntegralConeEquation ∪
    (Finset.univ : Finset (Fin 4)).image
      isolatedVertexQuotientRelativeIntegralSectionRow

def isolatedVertexQuotientRelativeSourceSectionEquationFinset
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ)) :
    Finset (StandardAG.RelativePolynomial
      isolatedVertexQuotientSourceSectionParameterCount 13) := by
  classical
  exact (projectiveConeLiftEquationFamily lowerEquations).image
      isolatedVertexQuotientRelativeHomogeneousAffineChange ∪
    (Finset.univ : Finset (Fin 4)).image
      isolatedVertexQuotientRelativeSectionRow

theorem rationalize_isolatedVertexQuotientRelativeIntegralSourceSectionEquationFinset
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ)) :
    (isolatedVertexQuotientRelativeIntegralSourceSectionEquationFinset
      lowerEquations).image
        rationalizeIsolatedVertexQuotientRelativeIntegralPolynomial =
      isolatedVertexQuotientRelativeSourceSectionEquationFinset
        lowerEquations := by
  classical
  ext g
  simp only [isolatedVertexQuotientRelativeIntegralSourceSectionEquationFinset,
    isolatedVertexQuotientRelativeSourceSectionEquationFinset,
    Finset.mem_image, Finset.mem_union, projectiveConeLiftEquationFamily]
  constructor
  · rintro ⟨h, (⟨f, hf, rfl⟩ | ⟨i, _hi, rfl⟩), rfl⟩
    · left
      exact ⟨projectiveConeLiftEquation f, ⟨f, hf, rfl⟩,
        rationalize_isolatedVertexQuotientRelativeIntegralConeEquation f |>.symm⟩
    · right
      exact ⟨i, Finset.mem_univ i,
        rationalize_isolatedVertexQuotientRelativeIntegralSectionRow i |>.symm⟩
  · rintro (⟨h, ⟨f, hf, rfl⟩, rfl⟩ | ⟨i, _hi, rfl⟩)
    · exact ⟨isolatedVertexQuotientRelativeIntegralConeEquation f,
        Or.inl ⟨f, hf, rfl⟩,
        rationalize_isolatedVertexQuotientRelativeIntegralConeEquation f⟩
    · exact ⟨isolatedVertexQuotientRelativeIntegralSectionRow i,
        Or.inr ⟨i, Finset.mem_univ i, rfl⟩,
        rationalize_isolatedVertexQuotientRelativeIntegralSectionRow i⟩

/-- Literal rational equations of one translated quotient-node section. -/
def isolatedVertexQuotientSourceSectionEquationFinset
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (b : IntVector 12) (m : ℤ) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Fin 13) ℚ) :
    Finset (MvPolynomial (Fin 13) ℚ) := by
  classical
  exact (translatedProjectiveConeLiftEquationFamily
      (fun i ↦ (b i : ℚ)) (m : ℚ) (by exact_mod_cast hm)
        lowerEquations).image (rename (finSuccEquiv 12).symm) ∪
    rationalMatrixRowLinearEquationFamily A

theorem specialize_isolatedVertexQuotientRelativeSourceSectionEquationFinset
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (b : IntVector 12) (m : ℤ) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Fin 13) ℤ) :
    (isolatedVertexQuotientRelativeSourceSectionEquationFinset
      lowerEquations).image
        (specializeIsolatedVertexQuotientRelativeSourceSectionPolynomial
          b m A) =
      isolatedVertexQuotientSourceSectionEquationFinset lowerEquations
        b m hm (A.map ((↑) : ℤ → ℚ)) := by
  classical
  ext g
  simp only [isolatedVertexQuotientRelativeSourceSectionEquationFinset,
    isolatedVertexQuotientSourceSectionEquationFinset,
    Finset.mem_image, Finset.mem_union,
    translatedProjectiveConeLiftEquationFamily,
    finiteFamilyHomogeneousAffineChange,
    rationalMatrixRowLinearEquationFamily]
  constructor
  · rintro ⟨h, (⟨f, hf, rfl⟩ | ⟨i, _hi, rfl⟩), rfl⟩
    · left
      refine ⟨homogeneousAffinePolynomialChangeAlgEquiv
        (fun i ↦ (b i : ℚ)) (m : ℚ) (by exact_mod_cast hm) f, ?_, ?_⟩
      · exact ⟨f, hf, rfl⟩
      · exact (specialize_isolatedVertexQuotientRelativeHomogeneousAffineChange
          b m hm A f).symm
    · right
      exact ⟨i, Finset.mem_univ i,
        (specialize_isolatedVertexQuotientRelativeSectionRow b m A i).symm⟩
  · rintro (⟨h, ⟨f, hf, rfl⟩, rfl⟩ | ⟨i, _hi, rfl⟩)
    · refine ⟨isolatedVertexQuotientRelativeHomogeneousAffineChange f, ?_, ?_⟩
      · left
        exact ⟨f, hf, rfl⟩
      · exact specialize_isolatedVertexQuotientRelativeHomogeneousAffineChange
          b m hm A f
    · refine ⟨isolatedVertexQuotientRelativeSectionRow i, ?_, ?_⟩
      · right
        exact ⟨i, Finset.mem_univ i, rfl⟩
      · exact specialize_isolatedVertexQuotientRelativeSectionRow b m A i

/-- Rational coefficient extension of the specialized integral family is
the literal quotient-node equation family. -/
theorem rationalRelativeIntegralFibreEquationFinset_isolatedVertexQuotient
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (b : IntVector 12) (m : ℤ) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Fin 13) ℤ) :
    rationalRelativeIntegralFibreEquationFinset
        (isolatedVertexQuotientRelativeIntegralSourceSectionEquationFinset
          lowerEquations)
        (isolatedVertexQuotientSourceSectionIntegralParameterVector b m A) =
      isolatedVertexQuotientSourceSectionEquationFinset lowerEquations
        b m hm (A.map ((↑) : ℤ → ℚ)) := by
  classical
  rw [rationalRelativeIntegralFibreEquationFinset, Finset.image_image]
  calc
    (isolatedVertexQuotientRelativeIntegralSourceSectionEquationFinset
      lowerEquations).image
        ((map (Int.castRingHom ℚ)) ∘
          specializeRelativeIntegralAffinePolynomial
            (isolatedVertexQuotientSourceSectionIntegralParameterVector
              b m A)) =
      (isolatedVertexQuotientRelativeIntegralSourceSectionEquationFinset
        lowerEquations).image
        (specializeIsolatedVertexQuotientRelativeSourceSectionPolynomial
          b m A ∘
            rationalizeIsolatedVertexQuotientRelativeIntegralPolynomial) := by
      apply Finset.image_congr
      intro f hf
      exact map_specializeRelativeIntegralAffinePolynomial_isolatedVertexQuotient
        b m A f
    _ = ((isolatedVertexQuotientRelativeIntegralSourceSectionEquationFinset
          lowerEquations).image
          rationalizeIsolatedVertexQuotientRelativeIntegralPolynomial).image
        (specializeIsolatedVertexQuotientRelativeSourceSectionPolynomial
          b m A) := by rw [Finset.image_image]
    _ = (isolatedVertexQuotientRelativeSourceSectionEquationFinset
          lowerEquations).image
        (specializeIsolatedVertexQuotientRelativeSourceSectionPolynomial
          b m A) := by
      rw [rationalize_isolatedVertexQuotientRelativeIntegralSourceSectionEquationFinset]
    _ = _ :=
      specialize_isolatedVertexQuotientRelativeSourceSectionEquationFinset
        lowerEquations b m hm A

/-! ## Generated ideal of one rational fibre -/

/-- The literal rational equation family generates the rational
translated-cone-plus-packet-plane node ideal. -/
theorem finiteEquationIdeal_isolatedVertexQuotientSourceSection_eq_nodeIdeal
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (b : IntVector 12) (m : ℤ) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Fin 13) ℚ) :
    finiteEquationIdeal
        (isolatedVertexQuotientSourceSectionEquationFinset
          lowerEquations b m hm A) =
      isolatedVertexQuotientNodeIdeal
        (isolatedVertexLowerRationalIdeal lowerEquations)
        (fun i ↦ (b i : ℚ)) (m : ℚ) (by exact_mod_cast hm) A := by
  let bQ : Fin 12 → ℚ := fun i ↦ (b i : ℚ)
  let hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  let coneFamily := translatedProjectiveConeLiftEquationFamily
    bQ (m : ℚ) hmQ lowerEquations
  rw [isolatedVertexQuotientSourceSectionEquationFinset,
    isolatedVertexQuotientNodeIdeal,
    finiteEquationIdeal_union_rowLinearEquationFamily,
    finiteEquationIdeal_rationalMatrixRowLinearEquationFamily_eq]
  congr 1
  rw [finiteEquationIdeal_image_renameEquiv]
  change (finiteEquationIdeal coneFamily).map
      (MvPolynomial.renameEquiv ℚ (finSuccEquiv 12).symm) = _
  have hcone : finiteEquationIdeal coneFamily =
      translatedProjectiveConeIdeal bQ (m : ℚ) hmQ
        (isolatedVertexLowerRationalIdeal lowerEquations) := by
    change finiteEquationIdeal
        (finiteFamilyHomogeneousAffineChange bQ (m : ℚ) hmQ
          (projectiveConeLiftEquationFamily lowerEquations)) = _
    rw [projectiveConeLiftEquationFamily_eq_renameSome_rationalized]
    exact finiteEquationIdeal_translated_renameSomeEquationFinset
      bQ (m : ℚ) hmQ (rationalizedEquationFinset lowerEquations)
  rw [hcone]
  rfl

/-- Consequently, the exact rational fibre ideal of the fixed integral
relative family is the rational quotient-node ideal. -/
theorem finiteEquationIdeal_rationalRelativeIntegralFibre_isolatedVertexQuotient_eq_nodeIdeal
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (b : IntVector 12) (m : ℤ) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Fin 13) ℤ) :
    finiteEquationIdeal
      (rationalRelativeIntegralFibreEquationFinset
        (isolatedVertexQuotientRelativeIntegralSourceSectionEquationFinset
          lowerEquations)
        (isolatedVertexQuotientSourceSectionIntegralParameterVector b m A)) =
      isolatedVertexQuotientNodeIdeal
        (isolatedVertexLowerRationalIdeal lowerEquations)
        (fun i ↦ (b i : ℚ)) (m : ℚ) (by exact_mod_cast hm)
        (A.map ((↑) : ℤ → ℚ)) := by
  rw [rationalRelativeIntegralFibreEquationFinset_isolatedVertexQuotient
    lowerEquations b m hm A]
  exact finiteEquationIdeal_isolatedVertexQuotientSourceSection_eq_nodeIdeal
    lowerEquations b m hm (A.map ((↑) : ℤ → ℚ))

/-! ## Coefficient extension to the geometric quotient node -/

/-- Coefficient extension commutes with the homogeneous affine transform of
a projective cone ideal. -/
theorem map_translatedProjectiveConeIdeal_coefficients
    (E : Type*) [Field E] [Algebra ℚ E]
    {σ : Type*} (b : σ → ℚ) (m : ℚ) (hm : m ≠ 0)
    (I : Ideal (MvPolynomial σ ℚ)) :
    (translatedProjectiveConeIdeal b m hm I).map
        (MvPolynomial.map (algebraMap ℚ E)) =
      translatedProjectiveConeIdeal
        (fun i ↦ algebraMap ℚ E (b i)) (algebraMap ℚ E m)
        (by simpa using (FaithfulSMul.algebraMap_injective ℚ E).ne hm)
        (I.map (MvPolynomial.map (algebraMap ℚ E))) := by
  unfold translatedProjectiveConeIdeal
  rw [← map_projectiveConeIdealExtension_coefficients E I]
  change Ideal.map (MvPolynomial.map (algebraMap ℚ E))
      (Ideal.map
        (homogeneousAffinePolynomialChangeAlgEquiv b m hm).toRingEquiv.toRingHom
        (projectiveConeIdealExtension I)) =
    Ideal.map
      (homogeneousAffinePolynomialChangeAlgEquiv
        (fun i ↦ algebraMap ℚ E (b i)) (algebraMap ℚ E m)
        (by simpa using
          (FaithfulSMul.algebraMap_injective ℚ E).ne hm)).toRingEquiv.toRingHom
      (Ideal.map (MvPolynomial.map (algebraMap ℚ E))
        (projectiveConeIdealExtension I))
  rw [Ideal.map_map, Ideal.map_map]
  apply congrArg (fun φ : MvPolynomial (Option σ) ℚ →+*
      MvPolynomial (Option σ) E ↦
    (projectiveConeIdealExtension I).map φ)
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [homogeneousAffinePolynomialChangeAlgEquiv,
      homogeneousAffinePolynomialChangeHom]
  · intro j
    cases j <;>
      simp [homogeneousAffinePolynomialChangeAlgEquiv,
        homogeneousAffinePolynomialChangeHom]

/-- Coefficient extension commutes with the standard consecutive-coordinate
version of the translated quotient cone. -/
theorem map_isolatedVertexTranslatedConeFinIdeal_coefficients
    (E : Type*) [Field E] [Algebra ℚ E]
    (b : Fin 12 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (I : Ideal (MvPolynomial (Fin 12) ℚ)) :
    (isolatedVertexTranslatedConeFinIdeal b m hm I).map
        (MvPolynomial.map (algebraMap ℚ E)) =
      isolatedVertexTranslatedConeFinIdeal
        (fun i ↦ algebraMap ℚ E (b i)) (algebraMap ℚ E m)
        (by simpa using (FaithfulSMul.algebraMap_injective ℚ E).ne hm)
        (I.map (MvPolynomial.map (algebraMap ℚ E))) := by
  unfold isolatedVertexTranslatedConeFinIdeal
  rw [← map_translatedProjectiveConeIdeal_coefficients E b m hm I]
  change Ideal.map (MvPolynomial.map (algebraMap ℚ E))
      (Ideal.map
        (MvPolynomial.renameEquiv ℚ
          (finSuccEquiv 12).symm).toRingEquiv.toRingHom
        (translatedProjectiveConeIdeal b m hm I)) =
    Ideal.map
      (MvPolynomial.renameEquiv E
        (finSuccEquiv 12).symm).toRingEquiv.toRingHom
      (Ideal.map (MvPolynomial.map (algebraMap ℚ E))
        (translatedProjectiveConeIdeal b m hm I))
  rw [Ideal.map_map, Ideal.map_map]
  apply congrArg (fun φ : MvPolynomial (Option (Fin 12)) ℚ →+*
      MvPolynomial (Fin 13) E ↦
    (translatedProjectiveConeIdeal b m hm I).map φ)
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro j
    simp

/-- Coefficient extension commutes with the row-generated homogeneous
linear ideal. -/
theorem map_matrixRowLinearIdeal_coefficients
    (E : Type*) [Field E] [Algebra ℚ E]
    {c N : ℕ} (A : Matrix (Fin c) (Fin N) ℚ) :
    (matrixRowLinearIdeal A).map
        (MvPolynomial.map (algebraMap ℚ E)) =
      matrixRowLinearIdeal (A.map (algebraMap ℚ E)) := by
  unfold matrixRowLinearIdeal
  rw [Ideal.map_span]
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro ⟨g, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    simp [matrixRowLinearPolynomial]
  · rintro ⟨i, rfl⟩
    refine ⟨matrixRowLinearPolynomial A i, ⟨i, rfl⟩, ?_⟩
    simp [matrixRowLinearPolynomial]

/-- The rational quotient-node ideal extends to the literal geometric node
used by the static component label. -/
theorem map_rational_isolatedVertexQuotientNodeIdeal_qbar
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (b : IntVector 12) (m : ℤ) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Fin 13) ℤ) :
    (isolatedVertexQuotientNodeIdeal
      (isolatedVertexLowerRationalIdeal lowerEquations)
      (fun i ↦ (b i : ℚ)) (m : ℚ) (by exact_mod_cast hm)
      (A.map ((↑) : ℤ → ℚ))).map
        (MvPolynomial.map (algebraMap ℚ Qbar)) =
      isolatedVertexQuotientNodeIdeal
        (geometricIsolatedVertexLowerIdeal lowerEquations)
        (qbarIntVector b) (algebraMap ℚ Qbar (m : ℚ))
        (qbarIntCast_ne_zero hm) (qbarIntMatrix A) := by
  rw [isolatedVertexQuotientNodeIdeal, Ideal.map_sup,
    map_isolatedVertexTranslatedConeFinIdeal_coefficients,
    map_matrixRowLinearIdeal_coefficients]
  rfl

/-! ## Minimal-prime descent for an actual stable component -/

/-- A geometric minimal prime over a rational ideal contracts to a rational
minimal prime under the faithfully flat coefficient extension to `Qbar`. -/
theorem comap_qbar_minimalPrime_map_mem_minimalPrimes
    {N : ℕ} (J : Ideal (MvPolynomial (Fin N) ℚ))
    (Q : Ideal (MvPolynomial (Fin N) Qbar))
    (hQ : Q ∈
      (J.map (MvPolynomial.map (algebraMap ℚ Qbar))).minimalPrimes) :
    Q.comap (MvPolynomial.map (algebraMap ℚ Qbar)) ∈
      J.minimalPrimes := by
  let R := MvPolynomial (Fin N) ℚ
  let S := MvPolynomial (Fin N) Qbar
  let f : R →+* S := MvPolynomial.map (algebraMap ℚ Qbar)
  letI : Algebra R S := MvPolynomial.algebraMvPolynomial
  let P : Ideal R := Q.comap f
  have hQprime : Q.IsPrime := Ideal.minimalPrimes_isPrime hQ
  have hPprime : P.IsPrime := hQprime.comap f
  have hJP : J ≤ P := by
    rw [← Ideal.map_le_iff_le_comap]
    exact hQ.1.2
  refine ⟨⟨hPprime, hJP⟩, ?_⟩
  intro K hK hKP
  by_contra hne
  have hKneP : K ≠ P := fun hEq ↦ hne (by rw [hEq])
  have hKPstrict : K < P := lt_of_le_of_ne hKP hKneP
  letI : K.IsPrime := hK.1
  letI : P.IsPrime := hPprime
  letI : Q.IsPrime := hQprime
  letI : Q.LiesOver P := ⟨rfl⟩
  obtain ⟨Q', hQ'Q, hQ'prime, hQ'over⟩ :=
    Ideal.exists_ideal_lt_liesOver_of_lt (R := R) (S := S) Q hKPstrict
  have hJQ' : J.map f ≤ Q' := by
    rw [Ideal.map_le_iff_le_comap]
    have hover : Q'.comap f = K := by
      rw [hQ'over.over]
      rfl
    rw [hover]
    exact hK.2
  have hQQ' : Q ≤ Q' := hQ.2 ⟨hQ'prime, hJQ'⟩ hQ'Q.le
  exact hQ'Q.not_ge hQQ'

/-- For a stable geometric component, its fixed rational descent is a
minimal prime of the exact rational fibre whenever that fibre extends to
the geometric node. -/
theorem rationalDescent_mem_finiteMinimalPrimes_of_qbarNodeComponent
    {N : ℕ} (J : Ideal (MvPolynomial (Fin N) ℚ))
    (Q : Ideal (MvPolynomial (Fin N) Qbar))
    (I : Ideal (MvPolynomial (Fin N) ℚ))
    (hIQ : I.map (MvPolynomial.map (algebraMap ℚ Qbar)) = Q)
    (hQ : Q ∈
      (J.map (MvPolynomial.map (algebraMap ℚ Qbar))).minimalPrimes) :
    I ∈ finiteMinimalPrimes J := by
  apply (mem_finiteMinimalPrimes_iff J I).2
  have hcomap := comap_qbar_minimalPrime_map_mem_minimalPrimes J Q hQ
  have hIcomap :
      Q.comap (MvPolynomial.map (algebraMap ℚ Qbar)) = I := by
    rw [← hIQ]
    letI : Algebra (MvPolynomial (Fin N) ℚ)
        (MvPolynomial (Fin N) Qbar) := MvPolynomial.algebraMvPolynomial
    simpa only [MvPolynomial.algebraMap_apply] using
      (Ideal.comap_map_eq_self_of_faithfullyFlat I)
  rwa [hIcomap] at hcomap

end

end TranslatedDepthSeven

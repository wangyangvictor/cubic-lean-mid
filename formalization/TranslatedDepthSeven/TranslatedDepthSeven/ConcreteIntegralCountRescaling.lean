import TranslatedDepthSeven.AffineIntegralPointTransport
import TranslatedDepthSeven.ConcreteIntegralCount

/-!
# Exact rescaling of the concrete translated point set

This file applies the literal substitution `x = x₀ + m z` to
`translatedIntegralPointFinset`.  The normalized finite set retains the
original translated-box condition exactly.  Its ambient box
`|z_i| <= ceil (2T)` is used only to make the set finite and is proved to
contain every displacement; it is not substituted for the original box.
-/

namespace TranslatedDepthSeven

noncomputable section

open Finset

/-- Apply the literal integral affine substitution to every equation in a
finite family. -/
def integralAffineTransformEquationFinset {n : ℕ}
    (x₀ : IntVector n) (r : ℕ)
    (equations : Finset (MvPolynomial (Fin n) ℤ)) :
    Finset (MvPolynomial (Fin n) ℤ) := by
  classical
  exact equations.image (integralAffineTransform x₀ r)

/-- Apply the same substitution to every equation of every listed closed
piece. -/
def integralAffineTransformClosedPieces {n : ℕ}
    (x₀ : IntVector n) (r : ℕ)
    (closedPieces : Finset (Finset (MvPolynomial (Fin n) ℤ))) :
    Finset (Finset (MvPolynomial (Fin n) ℤ)) := by
  classical
  exact closedPieces.image
    (integralAffineTransformEquationFinset x₀ r)

/-- Evaluation of the transformed integral polynomial is exactly evaluation
of the original polynomial at `x₀ + r z`. -/
theorem eval_integralAffineTransform {n : ℕ}
    (x₀ z : IntVector n) (r : ℕ)
    (f : MvPolynomial (Fin n) ℤ) :
    MvPolynomial.eval z (integralAffineTransform x₀ r f) =
      MvPolynomial.eval (integralAffineMap x₀ z r) f := by
  simpa only [MvPolynomial.aeval_eq_eval] using
    (aeval_integralAffineTransform x₀ z r f)

/-- Simultaneous vanishing of the transformed family is equivalent to
simultaneous vanishing of the original family at the affine image. -/
theorem integralCommonZero_transform_iff {n : ℕ}
    (x₀ z : IntVector n) (r : ℕ)
    (equations : Finset (MvPolynomial (Fin n) ℤ)) :
    IntegralCommonZero
        (integralAffineTransformEquationFinset x₀ r equations) z ↔
      IntegralCommonZero equations (integralAffineMap x₀ z r) := by
  classical
  constructor
  · intro h f hf
    have hmem : integralAffineTransform x₀ r f ∈
        integralAffineTransformEquationFinset x₀ r equations := by
      exact Finset.mem_image.mpr ⟨f, hf, rfl⟩
    rw [← eval_integralAffineTransform x₀ z r f]
    exact h _ hmem
  · intro h g hg
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
    rw [eval_integralAffineTransform]
    exact h f hf

/-- Avoidance of all transformed closed pieces is equivalent to avoidance of
the original pieces at the affine image. -/
theorem avoidsIntegralClosedPieces_transform_iff {n : ℕ}
    (x₀ z : IntVector n) (r : ℕ)
    (closedPieces : Finset (Finset (MvPolynomial (Fin n) ℤ))) :
    AvoidsIntegralClosedPieces
        (integralAffineTransformClosedPieces x₀ r closedPieces) z ↔
      AvoidsIntegralClosedPieces closedPieces
        (integralAffineMap x₀ z r) := by
  classical
  constructor
  · intro h equations hequations
    have hmem : integralAffineTransformEquationFinset x₀ r equations ∈
        integralAffineTransformClosedPieces x₀ r closedPieces := by
      exact Finset.mem_image.mpr ⟨equations, hequations, rfl⟩
    obtain ⟨g, hg, hgne⟩ := h _ hmem
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
    refine ⟨f, hf, ?_⟩
    rwa [eval_integralAffineTransform] at hgne
  · intro h transformed htransformed
    obtain ⟨equations, hequations, rfl⟩ :=
      Finset.mem_image.mp htransformed
    obtain ⟨f, hf, hfne⟩ := h equations hequations
    refine ⟨integralAffineTransform x₀ r f, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨f, hf, rfl⟩
    · rwa [eval_integralAffineTransform]

/-- The literal normalized displacement set.  Besides the finite ambient
box, membership keeps the exact condition that `x₀ + m z` belongs to the
original translated box, and uses the literally transformed main and closed
piece equations. -/
def normalizedDisplacementFinset
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (closedPieces : Finset (Finset (MvPolynomial (Fin 13) ℤ))) :
    Finset (IntVector 13) := by
  classical
  exact (integerSupNormBox 13 ⌈2 * p.T⌉₊).filter fun z ↦
    p.InTranslatedBox
        (fun i ↦ (integralAffineMap x₀ z p.m i : ℝ)) ∧
      IntegralCommonZero
        (integralAffineTransformEquationFinset x₀ p.m equations) z ∧
      AvoidsIntegralClosedPieces
        (integralAffineTransformClosedPieces x₀ p.m closedPieces) z

/-- The `ceil(2T)` ambient box contains every exact displacement whose image
and base point both lie in the original translated box. -/
theorem mem_integerSupNormBox_of_affineMap_mem_translatedBox
    (p : Parameters) (x₀ z : IntVector 13)
    (hx₀ : p.InTranslatedBox (fun i ↦ (x₀ i : ℝ)))
    (hz : p.InTranslatedBox
      (fun i ↦ (integralAffineMap x₀ z p.m i : ℝ))) :
    z ∈ integerSupNormBox 13 ⌈2 * p.T⌉₊ := by
  rw [mem_integerSupNormBox_iff]
  intro i
  have hscale : ∀ j,
      integralAffineMap x₀ z p.m j = x₀ j + p.m * z j := by
    intro j
    rfl
  have hreal : |(z i : ℝ)| ≤ 2 * p.T :=
    p.integral_displacement_le_two_T hz hx₀ hscale i
  have hcast : ((z i).natAbs : ℝ) ≤ 2 * p.T := by
    simpa [Nat.cast_natAbs] using hreal
  exact_mod_cast hcast.trans (Nat.le_ceil (2 * p.T))

/-- Exact membership formula.  The ambient `ceil(2T)` box disappears from
the right-hand side because it follows from the retained translated-box
condition and the base-point hypothesis. -/
theorem mem_normalizedDisplacementFinset_iff
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (closedPieces : Finset (Finset (MvPolynomial (Fin 13) ℤ)))
    (hx₀ : p.InTranslatedBox (fun i ↦ (x₀ i : ℝ)))
    (z : IntVector 13) :
    z ∈ normalizedDisplacementFinset p x₀ equations closedPieces ↔
      p.InTranslatedBox
          (fun i ↦ (integralAffineMap x₀ z p.m i : ℝ)) ∧
        IntegralCommonZero
          (integralAffineTransformEquationFinset x₀ p.m equations) z ∧
        AvoidsIntegralClosedPieces
          (integralAffineTransformClosedPieces x₀ p.m closedPieces) z := by
  classical
  constructor
  · intro hz
    exact (Finset.mem_filter.mp hz).2
  · intro hz
    exact Finset.mem_filter.mpr
      ⟨mem_integerSupNormBox_of_affineMap_mem_translatedBox
        p x₀ z hx₀ hz.1, hz⟩

/-- Equivalent membership formula expressed entirely using the original
equations and original closed pieces evaluated at `x₀ + m z`. -/
theorem mem_normalizedDisplacementFinset_iff_original
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (closedPieces : Finset (Finset (MvPolynomial (Fin 13) ℤ)))
    (hx₀ : p.InTranslatedBox (fun i ↦ (x₀ i : ℝ)))
    (z : IntVector 13) :
    z ∈ normalizedDisplacementFinset p x₀ equations closedPieces ↔
      p.InTranslatedBox
          (fun i ↦ (integralAffineMap x₀ z p.m i : ℝ)) ∧
        IntegralCommonZero equations (integralAffineMap x₀ z p.m) ∧
        AvoidsIntegralClosedPieces closedPieces
          (integralAffineMap x₀ z p.m) := by
  rw [mem_normalizedDisplacementFinset_iff p x₀ equations closedPieces hx₀ z,
    integralCommonZero_transform_iff,
    avoidsIntegralClosedPieces_transform_iff]

/-- The affine image of a normalized displacement is a member of the
original concrete translated point set. -/
theorem integralAffineMap_mem_translatedIntegralPointFinset
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (closedPieces : Finset (Finset (MvPolynomial (Fin 13) ℤ)))
    (hx₀box : p.InTranslatedBox (fun i ↦ (x₀ i : ℝ)))
    (hx₀res : p.InResidueClass x₀)
    {z : IntVector 13}
    (hz : z ∈ normalizedDisplacementFinset p x₀ equations closedPieces) :
    integralAffineMap x₀ z p.m ∈
      translatedIntegralPointFinset p equations closedPieces := by
  rw [mem_translatedIntegralPointFinset_iff]
  have hz' := (mem_normalizedDisplacementFinset_iff_original
    p x₀ equations closedPieces hx₀box z).mp hz
  refine ⟨hz'.1, ?_, hz'.2.1, hz'.2.2⟩
  intro i
  exact (integralAffineMap_congruent x₀ z i).trans (hx₀res i)

/-- The explicit map from normalized displacements to the original concrete
point set. -/
def normalizedDisplacementToTranslatedPoint
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (closedPieces : Finset (Finset (MvPolynomial (Fin 13) ℤ)))
    (hx₀box : p.InTranslatedBox (fun i ↦ (x₀ i : ℝ)))
    (hx₀res : p.InResidueClass x₀) :
    {z // z ∈ normalizedDisplacementFinset p x₀ equations closedPieces} →
      {x // x ∈ translatedIntegralPointFinset p equations closedPieces} :=
  fun z ↦ ⟨integralAffineMap x₀ z.1 p.m,
    integralAffineMap_mem_translatedIntegralPointFinset
      p x₀ equations closedPieces hx₀box hx₀res z.2⟩

/-- The preceding explicit map is bijective.  Surjectivity uses the literal
congruence displacement of the given point; no enlargement of the exact
translated-box condition occurs. -/
theorem normalizedDisplacementToTranslatedPoint_bijective
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (closedPieces : Finset (Finset (MvPolynomial (Fin 13) ℤ)))
    (hx₀box : p.InTranslatedBox (fun i ↦ (x₀ i : ℝ)))
    (hx₀res : p.InResidueClass x₀) :
    Function.Bijective
      (normalizedDisplacementToTranslatedPoint
        p x₀ equations closedPieces hx₀box hx₀res) := by
  constructor
  · intro z z' hzz'
    apply Subtype.ext
    apply integralAffineMap_injective p.hm x₀
    exact congrArg Subtype.val hzz'
  · intro x
    have hx := (mem_translatedIntegralPointFinset_iff
      p equations closedPieces x.1).mp x.2
    have hcongr : IntVectorCongruent p.m x.1 x₀ := by
      intro i
      exact (hx.2.1 i).trans (hx₀res i).symm
    let xcongr : {y : IntVector 13 // IntVectorCongruent p.m y x₀} :=
      ⟨x.1, hcongr⟩
    let z : IntVector 13 := congruenceDisplacement x₀ xcongr
    have hmap : integralAffineMap x₀ z p.m = x.1 := by
      funext i
      exact (congruenceDisplacement_spec x₀ xcongr i).symm
    have hz : z ∈
        normalizedDisplacementFinset p x₀ equations closedPieces := by
      apply (mem_normalizedDisplacementFinset_iff_original
        p x₀ equations closedPieces hx₀box z).mpr
      simpa [hmap] using ⟨hx.1, hx.2.2.1, hx.2.2.2⟩
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    exact hmap

/-- Exact equivalence between the normalized displacement set and the
original concrete translated point set. -/
def normalizedDisplacementEquivTranslatedIntegralPoint
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (closedPieces : Finset (Finset (MvPolynomial (Fin 13) ℤ)))
    (hx₀box : p.InTranslatedBox (fun i ↦ (x₀ i : ℝ)))
    (hx₀res : p.InResidueClass x₀) :
    {z // z ∈ normalizedDisplacementFinset p x₀ equations closedPieces} ≃
      {x // x ∈ translatedIntegralPointFinset p equations closedPieces} :=
  Equiv.ofBijective
    (normalizedDisplacementToTranslatedPoint
      p x₀ equations closedPieces hx₀box hx₀res)
    (normalizedDisplacementToTranslatedPoint_bijective
      p x₀ equations closedPieces hx₀box hx₀res)

/-- Exact cardinality equality furnished by the preceding equivalence. -/
theorem card_normalizedDisplacementFinset_eq_translatedIntegralPointFinset
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (closedPieces : Finset (Finset (MvPolynomial (Fin 13) ℤ)))
    (hx₀box : p.InTranslatedBox (fun i ↦ (x₀ i : ℝ)))
    (hx₀res : p.InResidueClass x₀) :
    (normalizedDisplacementFinset p x₀ equations closedPieces).card =
      (translatedIntegralPointFinset p equations closedPieces).card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_congr
      (normalizedDisplacementEquivTranslatedIntegralPoint
        p x₀ equations closedPieces hx₀box hx₀res)

end

end TranslatedDepthSeven

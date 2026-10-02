import TranslatedDepthSeven.ConcreteExceptionalLocus
import TranslatedDepthSeven.ConcreteIntegralCountRescaling

/-!
# Exact normalization of the literal depth-seven target

The exceptional-locus condition is retained on the original projective
point.  The substitution `x = x₀ + m z` is an exact equivalence; the
`ceil (2T)` box is only a finite ambient container for the displacement.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- The literal normalized displacement set corresponding to
`depthSevenTranslatedPointFinset`. -/
def depthSevenNormalizedDisplacementFinset
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (CF : ℕ) : Finset (IntVector 13) := by
  classical
  exact (integerSupNormBox 13 ⌈2 * p.T⌉₊).filter fun z ↦
    let x := integralAffineMap x₀ z p.m
    p.InTranslatedBox (fun i ↦ (x i : ℝ)) ∧
      IntegralCommonZero equations x ∧
      ∃ hx : x ≠ 0,
        ¬ EquationFamilyDefinesLinearProjectiveSpace equations ∧
        ¬ MemDepthSevenExceptionalLocus equations
          ⌈p.H ^ CF⌉₊ (integralProjectiveClass x hx)

/-- Exact membership formula; the ambient displacement box follows from the
two translated-box conditions. -/
theorem mem_depthSevenNormalizedDisplacementFinset_iff
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (CF : ℕ)
    (hx₀box : p.InTranslatedBox (fun i ↦ (x₀ i : ℝ)))
    (z : IntVector 13) :
    z ∈ depthSevenNormalizedDisplacementFinset p x₀ equations CF ↔
      let x := integralAffineMap x₀ z p.m
      p.InTranslatedBox (fun i ↦ (x i : ℝ)) ∧
        IntegralCommonZero equations x ∧
        ∃ hx : x ≠ 0,
          ¬ EquationFamilyDefinesLinearProjectiveSpace equations ∧
          ¬ MemDepthSevenExceptionalLocus equations
            ⌈p.H ^ CF⌉₊ (integralProjectiveClass x hx) := by
  classical
  dsimp only
  constructor
  · exact fun hz ↦ (Finset.mem_filter.mp hz).2
  · intro hz
    exact Finset.mem_filter.mpr
      ⟨mem_integerSupNormBox_of_affineMap_mem_translatedBox
        p x₀ z hx₀box hz.1, hz⟩

/-- The affine image of a normalized displacement is a member of the
literal original target. -/
theorem integralAffineMap_mem_depthSevenTranslatedPointFinset
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (CF : ℕ)
    (hx₀box : p.InTranslatedBox (fun i ↦ (x₀ i : ℝ)))
    (hx₀res : p.InResidueClass x₀)
    {z : IntVector 13}
    (hz : z ∈ depthSevenNormalizedDisplacementFinset p x₀ equations CF) :
    integralAffineMap x₀ z p.m ∈
      depthSevenTranslatedPointFinset p equations CF := by
  rw [mem_depthSevenTranslatedPointFinset_iff]
  have hz' := (mem_depthSevenNormalizedDisplacementFinset_iff
    p x₀ equations CF hx₀box z).mp hz
  refine ⟨hz'.1, ?_, hz'.2.1, hz'.2.2⟩
  intro i
  exact (integralAffineMap_congruent x₀ z i).trans (hx₀res i)

/-- The explicit map from normalized displacements to original points. -/
def depthSevenNormalizedToTranslatedPoint
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (CF : ℕ)
    (hx₀box : p.InTranslatedBox (fun i ↦ (x₀ i : ℝ)))
    (hx₀res : p.InResidueClass x₀) :
    {z // z ∈ depthSevenNormalizedDisplacementFinset p x₀ equations CF} →
      {x // x ∈ depthSevenTranslatedPointFinset p equations CF} :=
  fun z ↦ ⟨integralAffineMap x₀ z.1 p.m,
    integralAffineMap_mem_depthSevenTranslatedPointFinset
      p x₀ equations CF hx₀box hx₀res z.2⟩

/-- The normalization map is bijective. -/
theorem depthSevenNormalizedToTranslatedPoint_bijective
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (CF : ℕ)
    (hx₀box : p.InTranslatedBox (fun i ↦ (x₀ i : ℝ)))
    (hx₀res : p.InResidueClass x₀) :
    Function.Bijective
      (depthSevenNormalizedToTranslatedPoint
        p x₀ equations CF hx₀box hx₀res) := by
  constructor
  · intro z z' hzz'
    apply Subtype.ext
    apply integralAffineMap_injective p.hm x₀
    exact congrArg Subtype.val hzz'
  · intro x
    have hx := (mem_depthSevenTranslatedPointFinset_iff
      p equations CF x.1).mp x.2
    have hcongr : IntVectorCongruent p.m x.1 x₀ := by
      intro i
      exact (hx.2.1 i).trans (hx₀res i).symm
    let xcongr : {y : IntVector 13 // IntVectorCongruent p.m y x₀} :=
      ⟨x.1, hcongr⟩
    let z : IntVector 13 := congruenceDisplacement x₀ xcongr
    have hmap : integralAffineMap x₀ z p.m = x.1 := by
      funext i
      exact (congruenceDisplacement_spec x₀ xcongr i).symm
    have hz : z ∈ depthSevenNormalizedDisplacementFinset
        p x₀ equations CF := by
      apply (mem_depthSevenNormalizedDisplacementFinset_iff
        p x₀ equations CF hx₀box z).mpr
      simpa only [hmap] using ⟨hx.1, hx.2.2.1, hx.2.2.2⟩
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    exact hmap

/-- Exact cardinality preservation under normalization. -/
theorem card_depthSevenNormalizedDisplacementFinset_eq_translated
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (CF : ℕ)
    (hx₀box : p.InTranslatedBox (fun i ↦ (x₀ i : ℝ)))
    (hx₀res : p.InResidueClass x₀) :
    (depthSevenNormalizedDisplacementFinset p x₀ equations CF).card =
      (depthSevenTranslatedPointFinset p equations CF).card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_congr
      (Equiv.ofBijective
        (depthSevenNormalizedToTranslatedPoint
          p x₀ equations CF hx₀box hx₀res)
        (depthSevenNormalizedToTranslatedPoint_bijective
          p x₀ equations CF hx₀box hx₀res))

end

end TranslatedDepthSeven

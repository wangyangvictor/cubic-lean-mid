import CubicTenVariables.RationalTerminalBound
import HessianTheorem11.ReducedProjectiveDimension

/-!
The literal section-singularity fiber is a closed affine cone. Its
normalized-chart projective dimension gives exactly the affine threshold
used in the rational terminal bound. The final statement uses nonzero
rational normals before taking geometric closure and adjoining the origin.

No closedness of the bad-normal parameter set, properness theorem, or
scheme-theoretic singular-fiber identification is asserted or assumed.
-/

noncomputable section
namespace CubicTenVariables.TerminalProjectiveDimension
open MvPolynomial HessianTheorem11 Matrix
open TerminalSectionIncidence BibleProjectiveGeometry RationalConeClosure

theorem sectionSingularFiber_closed {n : ℕ} (F : GeometricPolynomial n)
    (v : GeometricPoint n) : AlgebraicallyClosedSet (sectionSingularFiber F v) := by
  let P : (Fin n ⊕ Fin n) → GeometricPolynomial n := Sum.elim X (fun i => C (v i))
  have hc := ReducedDominantOpen.closed_preimage P (affineSectionSingularIncidence_closed F)
  have he : polynomialMap P ⁻¹'
      {z : (Fin n ⊕ Fin n) → GeometricField |
        ((fun i => z (Sum.inl i)), (fun i => z (Sum.inr i))) ∈
          affineSectionSingularIncidence F} = sectionSingularFiber F v := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, polynomialMap, P,
      Sum.elim_inl, Sum.elim_inr, eval_X, eval_C]
    rfl
  exact he ▸ hc

theorem sectionSingularFiber_isAffineCone {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) (v : GeometricPoint n) :
    IsAffineCone (sectionSingularFiber F v) := by
  rintro a x ⟨hzero, hpair, hmin⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [BibleLowRank.eval_cubic_smul F hF, hzero, mul_zero]
  · rw [dotProduct_smul, hpair, smul_zero]
  · intro i j
    change v i * eval (a • x) (pderiv j F) - v j * eval (a • x) (pderiv i F) = 0
    rw [SingularNormalEquations.eval_quadratic_smul _ hF.pderiv,
      SingularNormalEquations.eval_quadratic_smul _ hF.pderiv]
    have hh := hmin i j
    change v i * eval x (pderiv j F) - v j * eval x (pderiv i F) = 0 at hh
    linear_combination a ^ 2 * hh

theorem zero_mem_sectionSingularFiber {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) (v : GeometricPoint n) :
    (0 : GeometricPoint n) ∈ sectionSingularFiber F v := by
  refine ⟨eval_origin_of_positive_homogeneous hF (by norm_num), ?_, ?_⟩
  · simp
  · intro i j
    change v i * eval 0 (pderiv j F) - v j * eval 0 (pderiv i F) = 0
    rw [eval_origin_of_positive_homogeneous hF.pderiv (by norm_num),
      eval_origin_of_positive_homogeneous hF.pderiv (by norm_num)]
    ring

private theorem nat_succ_le_add_one_iff (t : ℕ) (D : Dimension) :
    ((t + 1 : ℕ) : Dimension) ≤ D + 1 ↔ (t : Dimension) ≤ D := by
  cases D with
  | none =>
    change (((t + 1 : ℕ) : ℕ∞) : Dimension) ≤ ⊥ + 1 ↔ ((t : ℕ∞) : Dimension) ≤ ⊥
    simp only [WithBot.bot_add, WithBot.not_coe_le_bot]
  | some D =>
    change (((t : ℕ∞) + 1 : ℕ∞) : Dimension) ≤ ((D + 1 : ℕ∞) : Dimension) ↔
      ((t : ℕ∞) : Dimension) ≤ (D : Dimension)
    simp only [WithBot.coe_le_coe, ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)]

/-- The exact lower threshold, including the origin-only and empty cones. -/
theorem nat_le_projectiveDimension_iff {n : ℕ} (Z : Set (GeometricPoint n))
    (hZ : AlgebraicallyClosedSet Z) (hcone : IsAffineCone Z) (t : ℕ) :
    (t : Dimension) ≤ projectiveDimension Z ↔
      ((t + 1 : ℕ) : Dimension) ≤ affineDimension Z := by
  by_cases hn : ∃ x ∈ Z, x ≠ 0
  · rw [ReducedProjectiveDimension.dimension_cone Unconditional.genericRankOpen Z hZ hcone hn]
    exact (nat_succ_le_add_one_iff t _).symm
  · have hz : ∀ x ∈ Z, x = 0 := by simpa only [not_exists, not_and, not_not] using hn
    have hd : affineDimension Z ≤ (0 : Dimension) := by
      calc
        affineDimension Z ≤ affineDimension ({0} : Set (GeometricPoint n)) :=
          affineDimension_mono (fun x hx => hz x hx)
        _ = 0 := affineDimension_origin
    rw [projectiveDimension_eq_bot_of_no_nonzero Z hz]
    have hnot : ¬ ((t + 1 : ℕ) : Dimension) ≤ affineDimension Z := by
      intro h
      have hh : t + 1 ≤ 0 := by exact_mod_cast h.trans hd
      omega
    constructor
    · intro h
      exact (WithBot.not_coe_le_bot _ h).elim
    · intro h
      exact (hnot h).elim

/-- The corresponding upper threshold, also valid for empty projectivization. -/
theorem projectiveDimension_le_nat_iff {n : ℕ} (Z : Set (GeometricPoint n))
    (hZ : AlgebraicallyClosedSet Z) (hcone : IsAffineCone Z) (t : ℕ) :
    projectiveDimension Z ≤ (t : Dimension) ↔
      affineDimension Z ≤ ((t + 1 : ℕ) : Dimension) := by
  constructor
  · intro h
    by_cases hn : ∃ x ∈ Z, x ≠ 0
    · rw [ReducedProjectiveDimension.dimension_cone Unconditional.genericRankOpen Z hZ hcone hn]
      simpa only [Nat.cast_add, Nat.cast_one, add_comm] using add_le_add_right h (1 : Dimension)
    · have hz : ∀ x ∈ Z, x = 0 := by simpa only [not_exists, not_and, not_not] using hn
      calc
        affineDimension Z ≤ affineDimension ({0} : Set (GeometricPoint n)) :=
          affineDimension_mono (fun x hx => hz x hx)
        _ = 0 := affineDimension_origin
        _ ≤ ((t + 1 : ℕ) : Dimension) := by exact_mod_cast Nat.zero_le (t+1)
  · exact projectiveDimension_le
      (ReducedProjectiveDimension.affineProjectiveDimensionInput Unconditional.genericRankOpen)
      Z hZ hcone

theorem sectionSingularFiber_projective_threshold {n : ℕ}
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3) (v : GeometricPoint n) (t : ℕ) :
    (t : Dimension) ≤ projectiveDimension (sectionSingularFiber F v) ↔
      ((t + 1 : ℕ) : Dimension) ≤ affineDimension (sectionSingularFiber F v) :=
  nat_le_projectiveDimension_iff _ (sectionSingularFiber_closed F v)
    (sectionSingularFiber_isAffineCone F hF v) t

/-- Bad normals defined by the actual standard normalized projective charts. -/
def projectiveBadNormals {n : ℕ} (F : GeometricPolynomial n) (t : ℕ) :
    Set (GeometricPoint n) :=
  {v | (t : Dimension) ≤ projectiveDimension (sectionSingularFiber F v)}

theorem projectiveBadNormals_eq_badNormals {n : ℕ}
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3) (t : ℕ) :
    projectiveBadNormals F t = TerminalBadNormals.badNormals F t := by
  ext v
  exact sectionSingularFiber_projective_threshold F hF v t

theorem projective_singular_dimension_iff {n : ℕ} (F : AnisotropicCubic n) (t : ℕ) :
    projectiveDimension (singularLocus F.polynomial) ≤ (t : Dimension) ↔
      singularDimension F.polynomial ≤ ((t + 1 : ℕ) : Dimension) :=
  projectiveDimension_le_nat_iff _
    (BibleHyperplanes.singularCone_closed (geometricPolynomial F.polynomial))
    (BibleHyperplanes.singularCone_cone _ (geometric_homogeneous F.homogeneous)) t

/-- The rational terminal bound with both the ambient range and bad fibers
stated using actual normalized-chart projective dimensions. -/
theorem rational_projectiveBadNormals_dimension_le {n t : ℕ}
    (F : AnisotropicCubic n) (ht : 1 ≤ t)
    (hsing : projectiveDimension (singularLocus F.polynomial) ≤ (t : Dimension)) :
    affineDimension (rationalConeClosure
      (projectiveBadNormals (geometricPolynomial F.polynomial) t)) ≤
        ((n - (3 * (t+2) + 1) / 2 : ℕ) : Dimension) := by
  rw [projectiveBadNormals_eq_badNormals _ (geometric_homogeneous F.homogeneous)]
  exact RationalTerminalBound.rational_badNormals_dimension_le F ht
    ((projective_singular_dimension_iff F t).mp hsing)

/-- The same bound with the source construction displayed literally:
nonzero rational normals, geometric closure, then the origin. -/
theorem rational_projective_terminal_dimension_le {n t : ℕ}
    (F : AnisotropicCubic n) (ht : 1 ≤ t)
    (hsing : projectiveDimension (singularLocus F.polynomial) ≤ (t : Dimension)) :
    affineDimension (geometricClosure (rationalEmbedding ''
      {q : Fin n → ℚ |
        (t : Dimension) ≤ projectiveDimension
          (sectionSingularFiber (geometricPolynomial F.polynomial) (rationalEmbedding q)) ∧
        q ≠ 0}) ∪ {0}) ≤ ((n - (3 * (t+2) + 1) / 2 : ℕ) : Dimension) := by
  have h := rational_projectiveBadNormals_dimension_le F ht hsing
  rw [rationalConeClosure_eq_nonzero_closure] at h
  exact h

end CubicTenVariables.TerminalProjectiveDimension

import CubicTenVariables.TerminalSectionIncidence
import Mathlib.RingTheory.KrullDimension.Basic

/-! The literal scalar-gradient Gauss closure lies in the displayed
section-singularity incidence over every field, including characteristics
two and three. The equation F=0 is retained. Coordinate-ring dimensions
and normalized-chart projective dimensions are monotone under this actual
containment; no affine/projective dimension-shift theorem is assumed. -/

noncomputable section
namespace CubicTenVariables.ReducedGaussSection
open MvPolynomial HessianTheorem11 Matrix TerminalSectionIncidence
open scoped BigOperators

variable {K : Type*} [Field K] {n : ℕ}

/-- The actual scalar-gradient image, with the cubic equation retained. -/
def scalarGradientImage (F : MvPolynomial (Fin n) K) :
    Set ((Fin n ⊕ Fin n) → K) :=
  {z | ∃ x : Fin n → K, eval x F=0 ∧ ∃ a : K,
    z=Sum.elim x (a • gradient F x)}

/-- Literal Zariski closure over the chosen field. In geometric applications
K is an algebraic closure of a prime field. -/
def graph (F : MvPolynomial (Fin n) K) : Set ((Fin n ⊕ Fin n) → K) :=
  zeroLocus K (vanishingIdeal K (scalarGradientImage F))

/-- The actual point fiber at a fixed normal, including the zero normal. -/
def fiber (F : MvPolynomial (Fin n) K) (v : Fin n → K) : Set (Fin n → K) :=
  {x | Sum.elim x v ∈ graph F}

theorem scalarGradientImage_subset_graph (F : MvPolynomial (Fin n) K) :
    scalarGradientImage F ⊆ graph F := zeroLocus_vanishingIdeal_le _

/-- Euler's identity is used only as x·gradient F=3F, with no division by 3. -/
theorem scalarGradient_mem_incidence (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (x : Fin n → K) (hx : eval x F=0) (a : K) :
    (x,a • gradient F x) ∈ affineSectionSingularIncidence F := by
  refine ⟨hx,?_,?_⟩
  · rw [smul_dotProduct, dotProduct_comm]
    change a * (∑ i, x i * gradient F x i)=0
    rw [euler_cubic hF, hx, mul_zero, mul_zero]
  · intro i j
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- Every displayed incidence polynomial vanishes on the generating image. -/
theorem incidenceEquation_mem_vanishingIdeal (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (e : IncidenceEquationIndex n) :
    incidenceEquation F e ∈ vanishingIdeal K (scalarGradientImage F) := by
  rintro z ⟨x,hx,a,rfl⟩
  exact (incidence_iff_equations F (Sum.elim x (a • gradient F x))).mp
    (scalarGradient_mem_incidence F hF x hx a) e

/-- Closing the image preserves all actual section-incidence equations. -/
theorem graph_subset_incidence (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) :
    graph F ⊆ {z | ((fun i => z (Sum.inl i)),(fun i => z (Sum.inr i))) ∈
      affineSectionSingularIncidence F} := by
  intro z hz
  apply (incidence_iff_equations F z).mpr
  intro e
  exact hz (incidenceEquation F e) (incidenceEquation_mem_vanishingIdeal F hF e)

/-- Literal Gauss-fiber containment, uniformly in the normal parameter. -/
theorem fiber_subset_section (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (v : Fin n → K) :
    fiber F v ⊆ sectionSingularFiber F v := by
  intro x hx
  change Sum.elim x v ∈ graph F at hx
  change (x,v) ∈ affineSectionSingularIncidence F
  have hz := graph_subset_incidence F hF (show Sum.elim x v ∈ graph F from hx)
  exact hz

/-- Dimension of the actual reduced coordinate ring of a field-valued set. -/
def coordinateDimension (Z : Set (Fin n → K)) : WithBot ℕ∞ :=
  ringKrullDim (MvPolynomial (Fin n) K ⧸ vanishingIdeal K Z)

theorem coordinateDimension_mono {A B : Set (Fin n → K)} (h : A ⊆ B) :
    coordinateDimension A ≤ coordinateDimension B :=
  ringKrullDim_le_of_surjective
    (Ideal.Quotient.factor (vanishingIdeal_anti_mono h))
    (Ideal.Quotient.factor_surjective _)

theorem fiber_dimension_le_section (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (v : Fin n → K) :
    coordinateDimension (fiber F v) ≤ coordinateDimension (sectionSingularFiber F v) :=
  coordinateDimension_mono (fiber_subset_section F hF v)

theorem affine_threshold_section (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (v : Fin n → K) (t : ℕ)
    (ht : (t : WithBot ℕ∞) ≤ coordinateDimension (fiber F v)) :
    (t : WithBot ℕ∞) ≤ coordinateDimension (sectionSingularFiber F v) :=
  ht.trans (fiber_dimension_le_section F hF v)

/-- The actual normalized affine projective chart, with no quotient model. -/
def normalizedChart (Z : Set (Fin n → K)) (i : Fin n) : Set (Fin n → K) :=
  {x | x ∈ Z ∧ x i=1}

/-- Projective dimension defined by the normalized charts. No affine +1
identity is included; in particular empty charts retain their true dimension. -/
def projectiveDimension (Z : Set (Fin n → K)) : WithBot ℕ∞ :=
  ⨆ i : Fin n, coordinateDimension (normalizedChart Z i)

theorem normalizedChart_mono {A B : Set (Fin n → K)} (h : A ⊆ B) (i : Fin n) :
    normalizedChart A i ⊆ normalizedChart B i := fun _ hx => ⟨h hx.1,hx.2⟩

theorem projectiveDimension_mono {A B : Set (Fin n → K)} (h : A ⊆ B) :
    projectiveDimension A ≤ projectiveDimension B :=
  iSup_mono (fun i => coordinateDimension_mono (normalizedChart_mono h i))

theorem normalized_fiber_dimension_le_section (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (v : Fin n → K) (i : Fin n) :
    coordinateDimension (normalizedChart (fiber F v) i) ≤
      coordinateDimension (normalizedChart (sectionSingularFiber F v) i) :=
  coordinateDimension_mono (normalizedChart_mono (fiber_subset_section F hF v) i)

theorem projective_fiber_dimension_le_section (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (v : Fin n → K) :
    projectiveDimension (fiber F v) ≤ projectiveDimension (sectionSingularFiber F v) :=
  projectiveDimension_mono (fiber_subset_section F hF v)

theorem projective_threshold_section (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (v : Fin n → K) (t : ℕ)
    (ht : (t : WithBot ℕ∞) ≤ projectiveDimension (fiber F v)) :
    (t : WithBot ℕ∞) ≤ projectiveDimension (sectionSingularFiber F v) :=
  ht.trans (projective_fiber_dimension_le_section F hF v)

end CubicTenVariables.ReducedGaussSection

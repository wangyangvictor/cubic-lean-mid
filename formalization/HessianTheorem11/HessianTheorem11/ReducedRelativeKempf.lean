import HessianTheorem11.ReducedRelativeOrder
import HessianTheorem11.ReducedFlagStabilizer
import HessianTheorem11.ReducedRationalBoundaryDescent

/-! Geometric relative Kempf optimality and its proved arithmetic consequence.
The external theorem contains neither rationality nor a Galois-fixed flag.
Its optimization uses the actual target ideal and the actual orbit curve.

Textbook scope: Dolgachev, Lectures on Invariant Theory (2003), §9.5 p.141,
describes the relative fastest-limit construction and its canonical parabolic.
The literal ideal-order formulation is Kempf's relative instability theorem;
unlike Theorem 9.4 on p.140, it concerns an arbitrary closed invariant target.
Ordinary local closedness of orbits remains separately explicit.
-/
noncomputable section
namespace HessianTheorem11.ReducedRelative
open MvPolynomial PolynomialRestriction PolynomialWeightTransport NonzeroLimitTransport
open RationalDescent ReducedFlagStabilizer
variable {K : Type*} [Field K] {n d : ℕ}

def relativeSpeed (d : ℕ) (F : MvPolynomial (Fin n) K)
    (S : Set (MvPolynomial (Fin n) K)) (f : WeightFrame K n) : ℝ :=
  (relativeOrder d F S f : ℝ) / Real.sqrt (∑ i, (f.weight i : ℝ)^2)

/-- Primitive admissible cocharacters maximizing the actual relative ideal
order, normalized by the Euclidean Weyl-invariant norm.  The positive-order
clause asserts genuine approach to the closed target, not merely an existing
limit somewhere in the orbit closure. -/
structure RelativeOptimal (d : ℕ) (F : MvPolynomial (Fin n) K)
    (S : Set (MvPolynomial (Fin n) K)) (f : WeightFrame K n) : Prop where
  primitive : f.Primitive
  nonzero : f.weight ≠ 0
  admissible : HasNonnegativeWeights (restrict f.matrix F) f.weight
  positive_order : 0 < relativeOrder d F S f
  maximal : ∀ g : WeightFrame K n, g.weight ≠ 0 →
    HasNonnegativeWeights (restrict g.matrix F) g.weight →
    relativeSpeed d F S g ≤ relativeSpeed d F S f

/-- Relative Kempf optimality over an algebraically closed field.  The
representation is the full space of degree-d forms; the target is any nonempty
closed invariant subset of the orbit closure avoiding the given point.
The canonical parabolic is the actual stabilizer of the weighted flag.

For the conventional left action g·F=F∘g⁻¹, our original-coordinate pullback
curve corresponds to the cocharacter B diag(t^(-w)) B⁻¹.  Its parabolic preserves
the increasing w-filtration, exactly `flagStabilizer` below. -/
structure RelativeKempfInput (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] : Prop where
  exists_optimal : ∀ {n d : ℕ} (F : MvPolynomial (Fin n) K), F.IsHomogeneous d →
    ∀ S : Set (MvPolynomial (Fin n) K), coefficientClosed S → slInvariant S →
    S.Nonempty → S ⊆ slOrbitClosure F → F ∉ S →
    ∃ f : WeightFrame K n, RelativeOptimal d F S f
  unique_parabolic : ∀ {n d : ℕ} (F : MvPolynomial (Fin n) K), F.IsHomogeneous d →
    ∀ S : Set (MvPolynomial (Fin n) K), coefficientClosed S → slInvariant S →
    S ⊆ slOrbitClosure F → F ∉ S → ∀ f g : WeightFrame K n,
    RelativeOptimal d F S f → RelativeOptimal d F S g →
    flagStabilizer f.matrix f.weight = flagStabilizer g.matrix g.weight

theorem admissible_conjugate_iff (σ : K ≃+* K) (F : MvPolynomial (Fin n) K)
    (f : WeightFrame K n) :
    HasNonnegativeWeights (restrict (f.conjugate σ).matrix (map σ.toRingHom F))
      (f.conjugate σ).weight ↔ HasNonnegativeWeights (restrict f.matrix F) f.weight := by
  change HasNonnegativeWeights (restrict (f.matrix.map σ.toRingHom) (map σ.toRingHom F))
    f.weight ↔ _
  rw [← map_restrict]
  unfold HasNonnegativeWeights
  rw [MvPolynomial.support_map_of_injective _ σ.injective]

theorem relativeSpeed_map [Infinite K] (σ : K ≃+* K)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (f : WeightFrame K n) :
    relativeSpeed d (map σ.toRingHom F) (conjugateSet σ S) (f.conjugate σ) =
      relativeSpeed d F S f := by
  unfold relativeSpeed
  rw [relativeOrder_map σ F hF]
  rfl

theorem RelativeOptimal.conjugate [Infinite K] (σ : K ≃+* K)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (f : WeightFrame K n)
    (hf : RelativeOptimal d F S f) :
    RelativeOptimal d (map σ.toRingHom F) (conjugateSet σ S) (f.conjugate σ) := by
  refine ⟨hf.primitive, hf.nonzero, (admissible_conjugate_iff σ F f).mpr hf.admissible,
    ?_, ?_⟩
  · rw [relativeOrder_map σ F hF]
    exact hf.positive_order
  · intro g hg hga
    have hadm := (admissible_conjugate_iff σ.symm (map σ.toRingHom F) g).mpr hga
    rw [map_symm_map] at hadm
    have h := hf.maximal (g.conjugate σ.symm) hg hadm
    have he := relativeSpeed_map σ F hF S (g.conjugate σ.symm)
    rw [WeightFrame.conjugate_symm] at he
    rw [relativeSpeed_map σ F hF, he]
    exact h

theorem conjugateSet_orbitBoundary (σ : K ≃+* K) (F : MvPolynomial (Fin n) K) :
    conjugateSet σ (orbitBoundary F) = orbitBoundary (map σ.toRingHom F) := by
  ext G
  constructor
  · rintro ⟨H,hH,rfl⟩
    exact (orbitBoundary_map_iff σ F H).mpr hH
  · intro hG
    refine ⟨map σ.symm.toRingHom G, ?_, map_map_symm σ G⟩
    have h := (orbitBoundary_map_iff σ.symm (map σ.toRingHom F) G).mpr hG
    rwa [map_symm_map] at h

/-- Canonical relative optimality yields the literal Galois-fixed weighted
flag.  Equality of parabolics is converted to equality of filtrations by
elementary transvections and equal dimensions; conjugation keeps each weight. -/
theorem boundary_optimal_rationalFlag (Kempf : RelativeKempfInput GeometricField)
    (OC : OrbitBoundaryClosedInput GeometricField) (F : RationalPolynomial n)
    (hF : F.IsHomogeneous d) (f : WeightFrame GeometricField n)
    (hf : RelativeOptimal d (geometricPolynomial F) (orbitBoundary (geometricPolynomial F)) f) :
    f.RationalFlag := by
  intro σ
  have hc := hf.conjugate σ.toRingEquiv (geometricPolynomial F) (hF.map _) _ f
  rw [conjugateSet_orbitBoundary,
    show σ.toRingEquiv.toRingHom = σ.toRingHom from rfl,
    geometricPolynomial_galois_fixed F σ] at hc
  have he := Kempf.unique_parabolic (geometricPolynomial F) (hF.map _)
    (orbitBoundary (geometricPolynomial F)) (OC.closed_boundary _ (hF.map _))
    (orbitBoundary_invariant _ (hF.map _)) (fun _ h => h.1) (self_notMem_orbitBoundary _)
    (f.conjugate σ.toRingEquiv) f hc hf
  exact weightFlag_eq_of_stabilizer_eq (f.conjugate σ.toRingEquiv).matrix f.matrix
    (f.conjugate σ.toRingEquiv).injective f.injective f.weight he

/-- The complete former arithmetic boundary interface, derived from the
geometric relative theorem, ordinary orbit local closedness, and proved
Galois/linear-algebra descent.  No arithmetic or invariant-flag input remains. -/
theorem rationalRelativeBoundaryInput
    (Kempf : RelativeKempfInput GeometricField)
    (OC : OrbitBoundaryClosedInput GeometricField) : RationalRelativeBoundaryInput where
  boundary F _ hF _ hclosed := by
    obtain ⟨f,hf⟩ := Kempf.exists_optimal (geometricPolynomial F) (hF.map _)
      (orbitBoundary (geometricPolynomial F)) (OC.closed_boundary _ (hF.map _))
      (orbitBoundary_invariant _ (hF.map _)) (orbitBoundary_nonempty _ hclosed)
      (fun _ h => h.1) (self_notMem_orbitBoundary _)
    exact ReducedRationalBoundary.rational_existing_limit_of_invariant_flag F f
      (boundary_optimal_rationalFlag Kempf OC F hF f hf) hf.nonzero hf.admissible

end HessianTheorem11.ReducedRelative

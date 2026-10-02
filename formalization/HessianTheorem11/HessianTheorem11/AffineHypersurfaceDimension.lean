import HessianTheorem11.AffineGeometry

/-! General textbook dimension inputs for arbitrary affine algebraic sets and
arbitrary irreducible hypersurfaces. All loci use their actual vanishing ideals.
The promotion from a dimension bound to equality of sets is proved below. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial

def polynomialHypersurface {n : ℕ} (P : GeometricPolynomial n) : Set (GeometricPoint n) :=
  {x | eval x P = 0}

theorem polynomialHypersurface_eq_zeroLocus {n : ℕ} (P : GeometricPolynomial n) :
    polynomialHypersurface P = zeroLocus GeometricField (Ideal.span {P}) := by
  ext x
  change eval x P = 0 ↔ ∀ p ∈ Ideal.span {P}, eval x p = 0
  constructor
  · intro h p hp
    have hle : Ideal.span {P} ≤ RingHom.ker (eval x) := by
      apply Ideal.span_le.mpr
      intro p hp
      have he : p = P := Set.mem_singleton_iff.mp hp
      subst p
      exact h
    exact hle hp
  · intro h
    exact h P (Ideal.subset_span (Set.mem_singleton P))

theorem polynomialHypersurface_closed {n : ℕ} (P : GeometricPolynomial n) :
    AlgebraicallyClosedSet (polynomialHypersurface P) := by
  rw [polynomialHypersurface_eq_zeroLocus]
  exact algebraicallyClosedSet_zeroLocus _

theorem polynomialHypersurface_irreducible {n : ℕ} (P : GeometricPolynomial n)
    (hP : Irreducible P) : GeometricallyIrreducible (polynomialHypersurface P) := by
  rw [polynomialHypersurface_eq_zeroLocus]
  let I : Ideal (GeometricPolynomial n) := Ideal.span {P}
  letI : I.IsPrime := (Ideal.span_singleton_prime hP.ne_zero).mpr hP.prime
  change (vanishingIdeal GeometricField (zeroLocus GeometricField I)).IsPrime
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus]
  infer_instance

/-- Dimension of an irreducible principal hypersurface, and the strict
dimension drop for a proper closed subset of any irreducible affine variety.
These statements have no cubic, Hessian, incidence, or numerical target. -/
structure AffineHypersurfaceDimensionInput : Prop where
  hypersurface : ∀ {n : ℕ} (P : GeometricPolynomial n), Irreducible P →
    affineDimension (polynomialHypersurface P) = ((n - 1 : ℕ) : Dimension)
  proper_closed : ∀ {n : ℕ} (A B : Set (GeometricPoint n)),
    AlgebraicallyClosedSet A → AlgebraicallyClosedSet B → GeometricallyIrreducible B →
    A ⊂ B → affineDimension A < affineDimension B

theorem equal_hypersurface_of_dimension_ge
    (AD : AffineHypersurfaceDimensionInput) {n : ℕ} (P : GeometricPolynomial n)
    (hP : Irreducible P) (Z : Set (GeometricPoint n))
    (hZ : AlgebraicallyClosedSet Z) (hsub : Z ⊆ polynomialHypersurface P)
    (hd : ((n - 1 : ℕ) : Dimension) ≤ affineDimension Z) :
    Z = polynomialHypersurface P := by
  by_contra hne
  have hproper : Z ⊂ polynomialHypersurface P :=
    Set.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
  have hlt := AD.proper_closed Z (polynomialHypersurface P) hZ
    (polynomialHypersurface_closed P) (polynomialHypersurface_irreducible P hP) hproper
  rw [AD.hypersurface P hP] at hlt
  exact (not_lt_of_ge hd) hlt

end HessianTheorem11

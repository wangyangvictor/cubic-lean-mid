import HessianTheorem11.ReducedZeroInstability

/-! Closed-orbit-only Kempf optimality, with proved arithmetic bridges.

This restricts the retained geometric optimization theorem to actual closed
orbits. It does not construct the old arbitrary-target RK input. Ordinary
existence/uniqueness of the closed orbit is a separate geometric input (CO).
Mumford--Fogarty, Geometric Invariant Theory, second enlarged edition (1982),
Appendix 2B pp.157--158 defines the literal pullback-ideal order divided by
cocharacter length and states uniqueness of its maximum in the flag complex.
Dolgachev, Lectures on Invariant Theory (2003), Corollary 6.1 p.94 gives the
unique closed orbit via the affine quotient; §9.5 pp.140--141 explains the
flag-complex parabolic and the closed-orbit version of this construction.
-/
noncomputable section
namespace HessianTheorem11.ReducedClosedOrbit
open MvPolynomial PolynomialRestriction PolynomialWeightTransport NonzeroLimitTransport
open RationalDescent ReducedRelative ReducedFlagStabilizer
variable {K : Type*} [Field K] {n d : ℕ}

/-- A closed orbit is an actual special-linear orbit closed in coefficient
coordinates. There is no rationality or chosen degeneration in this predicate. -/
def IsClosedOrbit (S : Set (MvPolynomial (Fin n) K)) : Prop :=
  coefficientClosed S ∧ ∃ G, S = slOrbit G

/-- Ordinary affine reductive orbit geometry: each orbit closure has a unique
closed orbit. This specializes the affine-quotient theorem only by choosing
the representation of degree-d forms. -/
structure ClosedOrbitInput (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] : Prop where
  unique_closed_orbit : ∀ {n d : ℕ} (F : MvPolynomial (Fin n) K), F.IsHomogeneous d →
    ∃! S : Set (MvPolynomial (Fin n) K), IsClosedOrbit S ∧ S ⊆ slOrbitClosure F

/-- Geometric Kempf optimality restricted to a single actual closed orbit.
The optimization and parabolic are precisely the already defined ideal order,
Euclidean cocharacter norm, and actual weighted-flag stabilizer. No arithmetic
or Galois-fixed conclusion is assumed. -/
structure ClosedOrbitKempfInput (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] : Prop where
  exists_optimal : ∀ {n d : ℕ} (F : MvPolynomial (Fin n) K), F.IsHomogeneous d →
    ∀ S : Set (MvPolynomial (Fin n) K), IsClosedOrbit S →
    S ⊆ slOrbitClosure F → F ∉ S → ∃ f : WeightFrame K n, RelativeOptimal d F S f
  unique_parabolic : ∀ {n d : ℕ} (F : MvPolynomial (Fin n) K), F.IsHomogeneous d →
    ∀ S : Set (MvPolynomial (Fin n) K), IsClosedOrbit S →
    S ⊆ slOrbitClosure F → F ∉ S → ∀ f g : WeightFrame K n,
    RelativeOptimal d F S f → RelativeOptimal d F S g →
    flagStabilizer f.matrix f.weight = flagStabilizer g.matrix g.weight

theorem coefficientClosed_conjugate (σ : K ≃+* K)
    (S : Set (MvPolynomial (Fin n) K)) (hS : coefficientClosed S) :
    coefficientClosed (conjugateSet σ S) := by
  intro G hG
  refine ⟨map σ.symm.toRingHom G, hS _ ?_, map_map_symm σ G⟩
  intro P hP
  apply σ.injective
  rw [map_zero, ← eval_coeff_map, map_map_symm]
  exact hG _ ((coefficientVanishing_conjugate_iff σ S P).mpr hP)

theorem conjugateSet_slOrbit (σ : K ≃+* K) (F : MvPolynomial (Fin n) K) :
    conjugateSet σ (slOrbit F) = slOrbit (map σ.toRingHom F) := by
  ext G
  constructor
  · rintro ⟨H,hH,rfl⟩
    exact slOrbit_map σ F H hH
  · intro hG
    refine ⟨map σ.symm.toRingHom G, ?_, map_map_symm σ G⟩
    simpa only [map_symm_map] using slOrbit_map σ.symm _ _ hG

theorem IsClosedOrbit.conjugate (σ : K ≃+* K)
    {S : Set (MvPolynomial (Fin n) K)} (hS : IsClosedOrbit S) :
    IsClosedOrbit (conjugateSet σ S) := by
  refine ⟨coefficientClosed_conjugate σ S hS.1, ?_⟩
  obtain ⟨G,rfl⟩ := hS.2
  exact ⟨map σ.toRingHom G, conjugateSet_slOrbit σ G⟩

theorem slOrbit_eq_of_mem {F G : MvPolynomial (Fin n) K} (hG : G ∈ slOrbit F) :
    slOrbit G = slOrbit F := by
  obtain ⟨A,hA,rfl⟩ := hG
  ext H
  constructor
  · rintro ⟨B,hB,rfl⟩
    exact ⟨A*B, by rw [Matrix.det_mul,hA,hB,one_mul], restrict_restrict A B F⟩
  · rintro ⟨B,hB,rfl⟩
    refine ⟨A⁻¹*B, ?_, ?_⟩
    · rw [Matrix.det_mul,Matrix.det_nonsing_inv,hA,Ring.inverse_one,hB,one_mul]
    · rw [restrict_restrict, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv A (hA ▸ isUnit_one), Matrix.one_mul]

theorem notMem_closedOrbit_of_not_closed {F : MvPolynomial (Fin n) K}
    (hF : ¬ ClosedSLOrbit F) {S : Set (MvPolynomial (Fin n) K)}
    (hS : IsClosedOrbit S) : F ∉ S := by
  intro hFS
  obtain ⟨G,hG⟩ := hS.2
  have he : slOrbit F = S := (slOrbit_eq_of_mem (hG ▸ hFS)).trans hG.symm
  apply hF
  intro H hH
  rw [he]
  apply hS.1 H
  intro P hP
  exact hH P (by simpa only [he] using hP)

/-- Uniqueness of the actual closed orbit proves its Galois invariance. No
rationality of an individual point of that orbit is asserted or needed. -/
theorem closedOrbit_galois_fixed (CO : ClosedOrbitInput GeometricField)
    (F : RationalPolynomial n) (hF : F.IsHomogeneous d)
    (S : Set (GeometricPolynomial n)) (hS : IsClosedOrbit S)
    (hsub : S ⊆ slOrbitClosure (geometricPolynomial F)) :
    ∀ σ : GeometricField ≃ₐ[ℚ] GeometricField, conjugateSet σ.toRingEquiv S = S := by
  obtain ⟨T,hT,hunique⟩ := CO.unique_closed_orbit (geometricPolynomial F) (hF.map _)
  have hST := hunique S ⟨hS,hsub⟩
  intro σ
  apply (hunique _ ?_).trans hST.symm
  refine ⟨hS.conjugate σ.toRingEquiv, ?_⟩
  rintro _ ⟨G,hG,rfl⟩
  have h := slOrbitClosure_map σ.toRingEquiv _ _ (hsub hG)
  rwa [show σ.toRingEquiv.toRingHom = σ.toRingHom from rfl,
    geometricPolynomial_galois_fixed F σ] at h

/-- Optimality for a Galois-stable closed orbit yields the literal rational
weighted flag by the proved conjugation and flag-stabilizer bridges. -/
theorem closedOrbit_optimal_rationalFlag (CK : ClosedOrbitKempfInput GeometricField)
    (F : RationalPolynomial n) (hF : F.IsHomogeneous d)
    (S : Set (GeometricPolynomial n)) (hS : IsClosedOrbit S)
    (hsub : S ⊆ slOrbitClosure (geometricPolynomial F))
    (hnot : geometricPolynomial F ∉ S)
    (hfixed : ∀ σ : GeometricField ≃ₐ[ℚ] GeometricField, conjugateSet σ.toRingEquiv S = S)
    (f : WeightFrame GeometricField n) (hf : RelativeOptimal d (geometricPolynomial F) S f) :
    f.RationalFlag := by
  intro σ
  have hc := hf.conjugate σ.toRingEquiv (geometricPolynomial F) (hF.map _) S f
  rw [hfixed σ, show σ.toRingEquiv.toRingHom = σ.toRingHom from rfl,
    geometricPolynomial_galois_fixed F σ] at hc
  have he := CK.unique_parabolic (geometricPolynomial F) (hF.map _) S hS hsub hnot
    (f.conjugate σ.toRingEquiv) f hc hf
  exact weightFlag_eq_of_stabilizer_eq (f.conjugate σ.toRingEquiv).matrix f.matrix
    (f.conjugate σ.toRingEquiv).injective f.injective f.weight he

/-- The old arithmetic boundary consequence uses closed-orbit optimality and
ordinary unique-closed-orbit geometry. It does not use or construct RK or OG. -/
theorem rationalRelativeBoundaryInput (CK : ClosedOrbitKempfInput GeometricField)
    (CO : ClosedOrbitInput GeometricField) : RationalRelativeBoundaryInput where
  boundary F _ hF _ hclosed := by
    obtain ⟨S,⟨hS,hsub⟩,_⟩ := CO.unique_closed_orbit (geometricPolynomial F) (hF.map _)
    have hnot := notMem_closedOrbit_of_not_closed hclosed hS
    obtain ⟨f,hf⟩ := CK.exists_optimal (geometricPolynomial F) (hF.map _) S hS hsub hnot
    exact ReducedRationalBoundary.rational_existing_limit_of_invariant_flag F f
      (closedOrbit_optimal_rationalFlag CK F hF S hS hsub hnot
        (closedOrbit_galois_fixed CO F hF S hS hsub) f hf) hf.nonzero hf.admissible

end HessianTheorem11.ReducedClosedOrbit

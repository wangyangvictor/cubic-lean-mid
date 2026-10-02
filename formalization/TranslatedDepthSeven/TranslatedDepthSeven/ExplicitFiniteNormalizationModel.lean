import TranslatedDepthSeven.MonicCoordinateModuleFinite

/-!
# A finite affine model from literal monic normalization relations

This file contains the model used after coefficient descent.  The input is
entirely explicit: equations `f`, polynomial functions `q` defining the
normalization coordinates, and monic polynomials `p` for the ambient
coordinates.  We adjoin the substituted relations

`p_i(q_1(x), ..., q_d(x); x_i)`

to the model ideal.  They therefore vanish identically in the quotient,
and the resulting normalization map is module-finite.  No assertion about
primality, reducedness, fibre dimension, or injectivity is used.
-/

namespace TranslatedDepthSeven

noncomputable section

open Polynomial

universe u

/-- Substitute the displayed normalization functions and one ambient
coordinate into its proposed monic relation. -/
def normalizationCoordinateRelation
    {S : Type u} [CommRing S] {N d : ℕ}
    (q : Fin d → MvPolynomial (Fin N) S)
    (p : Fin N → (MvPolynomial (Fin d) S)[X])
    (i : Fin N) : MvPolynomial (Fin N) S :=
  (p i).eval₂ (MvPolynomial.aeval q).toRingHom (MvPolynomial.X i)

/-- Substitution in a normalization relation commutes exactly with an
arbitrary coefficient homomorphism. -/
theorem map_normalizationCoordinateRelation
    {S T : Type u} [CommRing S] [CommRing T] {N d : ℕ}
    (phi : S →+* T)
    (q : Fin d → MvPolynomial (Fin N) S)
    (p : Fin N → (MvPolynomial (Fin d) S)[X]) (i : Fin N) :
    MvPolynomial.map phi (normalizationCoordinateRelation q p i) =
      normalizationCoordinateRelation
        (fun j ↦ MvPolynomial.map phi (q j))
        (fun j ↦ (p j).map (MvPolynomial.map phi)) i := by
  rw [normalizationCoordinateRelation, normalizationCoordinateRelation,
    Polynomial.hom_eval₂]
  rw [Polynomial.eval₂_map]
  congr 1
  · apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro j
      simp
  · simp

/-- The literal model ideal: the chosen component equations together with
all substituted monic coordinate relations. -/
def finiteNormalizationModelIdeal
    {S : Type u} [CommRing S] {N d r : ℕ}
    (f : Fin r → MvPolynomial (Fin N) S)
    (q : Fin d → MvPolynomial (Fin N) S)
    (p : Fin N → (MvPolynomial (Fin d) S)[X]) :
    Ideal (MvPolynomial (Fin N) S) :=
  Ideal.span
    (Set.range f ∪ Set.range (normalizationCoordinateRelation q p))

/-- Extending coefficients carries the literal finite-normalization model
ideal exactly to the model ideal obtained by extending the coefficients of
each displayed equation, normalization function, and monic relation. -/
theorem map_finiteNormalizationModelIdeal
    {S T : Type u} [CommRing S] [CommRing T] {N d r : ℕ}
    (phi : S →+* T)
    (f : Fin r → MvPolynomial (Fin N) S)
    (q : Fin d → MvPolynomial (Fin N) S)
    (p : Fin N → (MvPolynomial (Fin d) S)[X]) :
    Ideal.map (MvPolynomial.map phi)
        (finiteNormalizationModelIdeal f q p) =
      finiteNormalizationModelIdeal
        (fun i ↦ MvPolynomial.map phi (f i))
        (fun j ↦ MvPolynomial.map phi (q j))
        (fun i ↦ (p i).map (MvPolynomial.map phi)) := by
  classical
  rw [finiteNormalizationModelIdeal, finiteNormalizationModelIdeal,
    Ideal.map_span]
  congr 1
  ext g
  constructor
  · rintro ⟨h, hf | hr, rfl⟩
    · obtain ⟨i, rfl⟩ := hf
      exact Or.inl ⟨i, rfl⟩
    · obtain ⟨i, rfl⟩ := hr
      exact Or.inr ⟨i, (map_normalizationCoordinateRelation phi q p i).symm⟩
  · intro hg
    rcases hg with hf | hr
    · obtain ⟨i, rfl⟩ := hf
      exact ⟨f i, Or.inl ⟨i, rfl⟩, rfl⟩
    · obtain ⟨i, rfl⟩ := hr
      exact ⟨normalizationCoordinateRelation q p i,
        Or.inr ⟨i, rfl⟩, map_normalizationCoordinateRelation phi q p i⟩

theorem normalizationCoordinateRelation_mem_modelIdeal
    {S : Type u} [CommRing S] {N d r : ℕ}
    (f : Fin r → MvPolynomial (Fin N) S)
    (q : Fin d → MvPolynomial (Fin N) S)
    (p : Fin N → (MvPolynomial (Fin d) S)[X]) (i : Fin N) :
    normalizationCoordinateRelation q p i ∈
      finiteNormalizationModelIdeal f q p := by
  apply Ideal.subset_span
  exact Or.inr ⟨i, rfl⟩

/-- The algebra map defined by the displayed normalization functions. -/
def finiteNormalizationModelAlgHom
    {S : Type u} [CommRing S] {N d r : ℕ}
    (f : Fin r → MvPolynomial (Fin N) S)
    (q : Fin d → MvPolynomial (Fin N) S)
    (p : Fin N → (MvPolynomial (Fin d) S)[X]) :
    MvPolynomial (Fin d) S →ₐ[S]
      (MvPolynomial (Fin N) S ⧸ finiteNormalizationModelIdeal f q p) :=
  (Ideal.Quotient.mkₐ S (finiteNormalizationModelIdeal f q p)).comp
    (MvPolynomial.aeval q)

/-- The displayed monic relations make the explicit model finite over its
normalization polynomial algebra. -/
theorem finite_finiteNormalizationModelAlgHom
    {S : Type u} [CommRing S] {N d r : ℕ}
    (f : Fin r → MvPolynomial (Fin N) S)
    (q : Fin d → MvPolynomial (Fin N) S)
    (p : Fin N → (MvPolynomial (Fin d) S)[X])
    (hmonic : ∀ i, (p i).Monic) :
    (finiteNormalizationModelAlgHom f q p).Finite := by
  apply finite_affineQuotient_map_of_monic_coordinate_relations
    (finiteNormalizationModelIdeal f q p)
    (finiteNormalizationModelAlgHom f q p) p
  intro i
  refine ⟨hmonic i, ?_⟩
  have hmap :
      (Ideal.Quotient.mkₐ S (finiteNormalizationModelIdeal f q p))
          (normalizationCoordinateRelation q p i) =
        (p i).eval₂
          (finiteNormalizationModelAlgHom f q p).toRingHom
          (Ideal.Quotient.mk (finiteNormalizationModelIdeal f q p)
            (MvPolynomial.X i)) := by
    simpa only [normalizationCoordinateRelation,
      finiteNormalizationModelAlgHom, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_comp, RingHom.coe_comp, Function.comp_apply] using
      (Polynomial.hom_eval₂ (p i) (MvPolynomial.aeval q).toRingHom
        (Ideal.Quotient.mkₐ S
          (finiteNormalizationModelIdeal f q p)).toRingHom
        (MvPolynomial.X i))
  rw [← hmap]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (normalizationCoordinateRelation_mem_modelIdeal f q p i)

end

end TranslatedDepthSeven

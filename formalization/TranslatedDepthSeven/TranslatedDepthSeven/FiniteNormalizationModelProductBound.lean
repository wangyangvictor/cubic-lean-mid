import TranslatedDepthSeven.MonicCoordinateProductBound
import TranslatedDepthSeven.RelativeGenericComponentFiniteNormalization

/-!
# Quantitative fibres of the explicit finite-normalization model

The literal model `finiteNormalizationModelIdeal f q p` contains, for each
ambient coordinate, the substituted monic relation `p i`.  Consequently
the quotient is spanned over its normalization polynomial algebra by at
most

`∏ i, (p i).natDegree`

elements.  This file records all consequences needed after specialization:
module-finiteness, a uniform scalar-fibre rank bound, the corresponding
finite-field point bound, and a Krull-dimension upper bound.

The final two theorems apply these conclusions to any specialized ideal
which is literally equal to the specialized model ideal.  This is the form
used after the torsion-clearing theorem for a generic component closure.
Nothing here asserts that a special fibre is reduced, irreducible,
equidimensional, or flat.
-/

namespace TranslatedDepthSeven

noncomputable section

open Polynomial
open scoped TensorProduct

universe u v

set_option maxHeartbeats 2000000

/-- Each substituted normalization relation vanishes in the literal model
quotient. -/
theorem finiteNormalizationModel_coordinate_relation
    {S : Type u} [CommRing S] {N d r : ℕ}
    (f : Fin r → MvPolynomial (Fin N) S)
    (q : Fin d → MvPolynomial (Fin N) S)
    (p : Fin N → (MvPolynomial (Fin d) S)[X])
    (i : Fin N) :
    (p i).eval₂ (finiteNormalizationModelAlgHom f q p).toRingHom
        (Ideal.Quotient.mk (finiteNormalizationModelIdeal f q p)
          (MvPolynomial.X i)) = 0 := by
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

/-- The ambient affine coordinates generate the literal model quotient as
an algebra over the displayed normalization polynomial algebra. -/
theorem finiteNormalizationModel_coordinate_generate
    {S : Type u} [CommRing S] {N d r : ℕ}
    (f : Fin r → MvPolynomial (Fin N) S)
    (q : Fin d → MvPolynomial (Fin N) S)
    (p : Fin N → (MvPolynomial (Fin d) S)[X]) :
    let A := MvPolynomial (Fin N) S ⧸
      finiteNormalizationModelIdeal f q p
    let B := MvPolynomial (Fin d) S
    let g := finiteNormalizationModelAlgHom f q p
    letI : Algebra B A := g.toRingHom.toAlgebra
    Algebra.adjoin B
      (Set.range fun i ↦
        Ideal.Quotient.mk (finiteNormalizationModelIdeal f q p)
          (MvPolynomial.X i)) = ⊤ := by
  dsimp only
  let A := MvPolynomial (Fin N) S ⧸ finiteNormalizationModelIdeal f q p
  let B := MvPolynomial (Fin d) S
  let g := finiteNormalizationModelAlgHom f q p
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : IsScalarTower S B A :=
    IsScalarTower.of_algebraMap_eq fun s ↦ (g.commutes s).symm
  apply adjoin_eq_top_of_adjoin_eq_top_of_tower
    (R := S) (B := B) (A := A)
  exact adjoin_affineQuotient_coordinates_eq_top S
    (finiteNormalizationModelIdeal f q p)

/-- Every fibre of the displayed normalization map over an arbitrary field
point has vector-space dimension at most the product of the monic relation
degrees. -/
theorem finiteNormalizationModel_scalarFibre_finrank_le_prod
    (k : Type u) [Field k] {N d r : ℕ}
    (f : Fin r → MvPolynomial (Fin N) k)
    (q : Fin d → MvPolynomial (Fin N) k)
    (p : Fin N → (MvPolynomial (Fin d) k)[X])
    (hmonic : ∀ i, (p i).Monic)
    (phi : MvPolynomial (Fin d) k →ₐ[k] k) :
    Module.finrank k
        (ringHomScalarFibre (MvPolynomial (Fin d) k) k
          (MvPolynomial (Fin N) k ⧸ finiteNormalizationModelIdeal f q p)
          phi.toRingHom
          (finiteNormalizationModelAlgHom f q p).toRingHom) ≤
      ∏ i, (p i).natDegree := by
  exact finrank_ringHomScalarFibre_le_prod_natDegree
    (MvPolynomial (Fin d) k) k
    (MvPolynomial (Fin N) k ⧸ finiteNormalizationModelIdeal f q p)
    phi.toRingHom (finiteNormalizationModelAlgHom f q p).toRingHom
    (fun i ↦ Ideal.Quotient.mk (finiteNormalizationModelIdeal f q p)
      (MvPolynomial.X i)) p
    (finiteNormalizationModel_coordinate_generate f q p)
    (fun i ↦ ⟨hmonic i,
      finiteNormalizationModel_coordinate_relation f q p i⟩)

/-- Scheme-theoretic fibre-length version of
`finiteNormalizationModel_scalarFibre_finrank_le_prod`. -/
theorem finiteNormalizationModel_scalarFibre_length_le_prod
    (k : Type u) [Field k] {N d r : ℕ}
    (f : Fin r → MvPolynomial (Fin N) k)
    (q : Fin d → MvPolynomial (Fin N) k)
    (p : Fin N → (MvPolynomial (Fin d) k)[X])
    (hmonic : ∀ i, (p i).Monic)
    (phi : MvPolynomial (Fin d) k →ₐ[k] k) :
    Module.length k
        (ringHomScalarFibre (MvPolynomial (Fin d) k) k
          (MvPolynomial (Fin N) k ⧸ finiteNormalizationModelIdeal f q p)
          phi.toRingHom
          (finiteNormalizationModelAlgHom f q p).toRingHom) ≤
      (∏ i, (p i).natDegree : ℕ∞) := by
  exact length_ringHomScalarFibre_le_prod_natDegree
    (MvPolynomial (Fin d) k) k
    (MvPolynomial (Fin N) k ⧸ finiteNormalizationModelIdeal f q p)
    phi.toRingHom (finiteNormalizationModelAlgHom f q p).toRingHom
    (fun i ↦ Ideal.Quotient.mk (finiteNormalizationModelIdeal f q p)
      (MvPolynomial.X i)) p
    (finiteNormalizationModel_coordinate_generate f q p)
    (fun i ↦ ⟨hmonic i,
      finiteNormalizationModel_coordinate_relation f q p i⟩)

/-- Over a finite field, the literal model has at most the product of the
monic degrees times `(#k)^d` rational points. -/
theorem finiteNormalizationModel_points_le_prod_mul_pow
    (k : Type u) [Field k] [Finite k] {N d r : ℕ}
    (f : Fin r → MvPolynomial (Fin N) k)
    (q : Fin d → MvPolynomial (Fin N) k)
    (p : Fin N → (MvPolynomial (Fin d) k)[X])
    (hmonic : ∀ i, (p i).Monic) :
    Nat.card
        ((MvPolynomial (Fin N) k ⧸ finiteNormalizationModelIdeal f q p)
          →ₐ[k] k) ≤
      (∏ i, (p i).natDegree) * Nat.card k ^ d := by
  apply natCard_algHom_le_prod_natDegree_mul_pow k
    (MvPolynomial (Fin N) k ⧸ finiteNormalizationModelIdeal f q p) d
    (finiteNormalizationModelAlgHom f q p)
    (fun i ↦ Ideal.Quotient.mk (finiteNormalizationModelIdeal f q p)
      (MvPolynomial.X i)) p
    (finiteNormalizationModel_coordinate_generate f q p)
  intro i
  exact ⟨hmonic i,
    finiteNormalizationModel_coordinate_relation f q p i⟩

/-- Universal Krull-dimension consequence of the displayed finite map.
This remains only an upper bound because the normalization map need not be
injective after specialization. -/
theorem finiteNormalizationModel_ringKrullDim_le
    {S : Type u} [CommRing S] {N d r : ℕ}
    (f : Fin r → MvPolynomial (Fin N) S)
    (q : Fin d → MvPolynomial (Fin N) S)
    (p : Fin N → (MvPolynomial (Fin d) S)[X])
    (hmonic : ∀ i, (p i).Monic) :
    ringKrullDim
        (MvPolynomial (Fin N) S ⧸ finiteNormalizationModelIdeal f q p) ≤
      ringKrullDim (MvPolynomial (Fin d) S) := by
  let A := MvPolynomial (Fin N) S ⧸ finiteNormalizationModelIdeal f q p
  let B := MvPolynomial (Fin d) S
  let g := finiteNormalizationModelAlgHom f q p
  letI : Algebra B A := g.toRingHom.toAlgebra
  exact ringKrullDim_le_of_monic_generators
    (fun i ↦ Ideal.Quotient.mk (finiteNormalizationModelIdeal f q p)
      (MvPolynomial.X i)) p
    (finiteNormalizationModel_coordinate_generate f q p)
    (fun i ↦ ⟨hmonic i,
      finiteNormalizationModel_coordinate_relation f q p i⟩)

/-- A literal equality with the model ideal transfers the displayed finite
normalization, the Krull-dimension upper bound, and the uniform fibre-rank
bound to the other quotient.  This is useful for a canonical component
closure after its torsion discrepancy with the model has been cleared. -/
theorem ideal_eq_finiteNormalizationModel_quantitative
    (k : Type u) [Field k] {N d r : ℕ}
    (f : Fin r → MvPolynomial (Fin N) k)
    (q : Fin d → MvPolynomial (Fin N) k)
    (p : Fin N → (MvPolynomial (Fin d) k)[X])
    (hmonic : ∀ i, (p i).Monic)
    (I : Ideal (MvPolynomial (Fin N) k))
    (hI : I = finiteNormalizationModelIdeal f q p) :
    ∃ g : MvPolynomial (Fin d) k →ₐ[k]
        (MvPolynomial (Fin N) k ⧸ I),
      g.Finite ∧
      ringKrullDim (MvPolynomial (Fin N) k ⧸ I) ≤
        ringKrullDim (MvPolynomial (Fin d) k) ∧
      ∀ phi : MvPolynomial (Fin d) k →ₐ[k] k,
        Module.finrank k
            (ringHomScalarFibre (MvPolynomial (Fin d) k) k
              (MvPolynomial (Fin N) k ⧸ I)
              phi.toRingHom g.toRingHom) ≤
          ∏ i, (p i).natDegree ∧
        Module.length k
            (ringHomScalarFibre (MvPolynomial (Fin d) k) k
              (MvPolynomial (Fin N) k ⧸ I)
              phi.toRingHom g.toRingHom) ≤
          (∏ i, (p i).natDegree : ℕ∞) := by
  subst I
  refine ⟨finiteNormalizationModelAlgHom f q p,
    finite_finiteNormalizationModelAlgHom f q p hmonic,
    finiteNormalizationModel_ringKrullDim_le f q p hmonic, ?_⟩
  intro phi
  exact ⟨finiteNormalizationModel_scalarFibre_finrank_le_prod
      k f q p hmonic phi,
    finiteNormalizationModel_scalarFibre_length_le_prod
      k f q p hmonic phi⟩

/-- Finite-field point-count form of
`ideal_eq_finiteNormalizationModel_quantitative`. -/
theorem ideal_eq_finiteNormalizationModel_points_le_prod_mul_pow
    (k : Type u) [Field k] [Finite k] {N d r : ℕ}
    (f : Fin r → MvPolynomial (Fin N) k)
    (q : Fin d → MvPolynomial (Fin N) k)
    (p : Fin N → (MvPolynomial (Fin d) k)[X])
    (hmonic : ∀ i, (p i).Monic)
    (I : Ideal (MvPolynomial (Fin N) k))
    (hI : I = finiteNormalizationModelIdeal f q p) :
    Nat.card ((MvPolynomial (Fin N) k ⧸ I) →ₐ[k] k) ≤
      (∏ i, (p i).natDegree) * Nat.card k ^ d := by
  subst I
  exact finiteNormalizationModel_points_le_prod_mul_pow
    k f q p hmonic

/-- After an arbitrary specialization from a coefficient ring to a field,
literal equality of the specialized closure ideal with the specialized
model ideal gives a finite normalization with one fibre-rank bound measured
by the degrees of the original monic relations.  Monicity ensures that
those degrees do not drop under specialization. -/
theorem specialized_ideal_eq_finiteNormalizationModel_quantitative
    {S : Type u} [CommRing S]
    (k : Type v) [Field k] (rho : S →+* k)
    {N d r : ℕ}
    (f : Fin r → MvPolynomial (Fin N) S)
    (q : Fin d → MvPolynomial (Fin N) S)
    (p : Fin N → (MvPolynomial (Fin d) S)[X])
    (hmonic : ∀ i, (p i).Monic)
    (I : Ideal (MvPolynomial (Fin N) k))
    (hI : I = finiteNormalizationModelIdeal
      (fun i ↦ MvPolynomial.map rho (f i))
      (fun j ↦ MvPolynomial.map rho (q j))
      (fun i ↦ (p i).map (MvPolynomial.map rho))) :
    ∃ g : MvPolynomial (Fin d) k →ₐ[k]
        (MvPolynomial (Fin N) k ⧸ I),
      g.Finite ∧
      ringKrullDim (MvPolynomial (Fin N) k ⧸ I) ≤
        ringKrullDim (MvPolynomial (Fin d) k) ∧
      ∀ phi : MvPolynomial (Fin d) k →ₐ[k] k,
        Module.finrank k
            (ringHomScalarFibre (MvPolynomial (Fin d) k) k
              (MvPolynomial (Fin N) k ⧸ I)
              phi.toRingHom g.toRingHom) ≤
          ∏ i, (p i).natDegree ∧
        Module.length k
            (ringHomScalarFibre (MvPolynomial (Fin d) k) k
              (MvPolynomial (Fin N) k ⧸ I)
              phi.toRingHom g.toRingHom) ≤
          (∏ i, (p i).natDegree : ℕ∞) := by
  simpa only [fun i ↦ (hmonic i).natDegree_map (MvPolynomial.map rho)] using
    (ideal_eq_finiteNormalizationModel_quantitative k
      (fun i ↦ MvPolynomial.map rho (f i))
      (fun j ↦ MvPolynomial.map rho (q j))
      (fun i ↦ (p i).map (MvPolynomial.map rho))
      (fun i ↦ (hmonic i).map (MvPolynomial.map rho)) I hI)

/-- Finite-field point-count form of the specialized closure theorem. -/
theorem specialized_ideal_eq_finiteNormalizationModel_points_le
    {S : Type u} [CommRing S]
    (k : Type v) [Field k] [Finite k] (rho : S →+* k)
    {N d r : ℕ}
    (f : Fin r → MvPolynomial (Fin N) S)
    (q : Fin d → MvPolynomial (Fin N) S)
    (p : Fin N → (MvPolynomial (Fin d) S)[X])
    (hmonic : ∀ i, (p i).Monic)
    (I : Ideal (MvPolynomial (Fin N) k))
    (hI : I = finiteNormalizationModelIdeal
      (fun i ↦ MvPolynomial.map rho (f i))
      (fun j ↦ MvPolynomial.map rho (q j))
      (fun i ↦ (p i).map (MvPolynomial.map rho))) :
    Nat.card ((MvPolynomial (Fin N) k ⧸ I) →ₐ[k] k) ≤
      (∏ i, (p i).natDegree) * Nat.card k ^ d := by
  simpa only [fun i ↦ (hmonic i).natDegree_map (MvPolynomial.map rho)] using
    (ideal_eq_finiteNormalizationModel_points_le_prod_mul_pow k
      (fun i ↦ MvPolynomial.map rho (f i))
      (fun j ↦ MvPolynomial.map rho (q j))
      (fun i ↦ (p i).map (MvPolynomial.map rho))
      (fun i ↦ (hmonic i).map (MvPolynomial.map rho)) I hI)

end

end TranslatedDepthSeven

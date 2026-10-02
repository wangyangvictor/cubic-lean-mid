import TranslatedDepthSeven.ParameterCountSurface
import TranslatedDepthSeven.PrimeAffineNoetherNormalization
import TranslatedDepthSeven.VerticalFiniteNormalizationPackage
import TranslatedDepthSeven.PrincipalOpenReduction
import TranslatedDepthSeven.RestrictionFibreAlgHom
import TranslatedDepthSeven.SquarefreeResidueCount
import TranslatedDepthSeven.PublishedCountingTheorems
import TranslatedDepthSeven.ConcreteExceptionalLocus
import TranslatedDepthSeven.HomogeneousCone

/-!
# Fixed-cone residue counts from a vertical linear normalization

This file supplies the fixed geometric residue-count input used by the
depth-seven argument.  A projective fivefold has an affine cone of Krull
dimension six.  Homogeneous linear Noether normalization therefore supplies
at most six linear parameters.  After the finitely many coefficients and
monic coordinate relations have been spread over one principal open of
`Spec Z`, the resulting fixed model has `O(p^6)` points over every remaining
prime, with one constant chosen before the prime.  Exact Chinese
remaindering then gives `O(q^6)` up to the standard subpower factor.

The proof deliberately uses `parameterCount <= 6`, which is all the counting
argument needs.  Thus it does not appeal to the unavailable general identity
`dim k[X_1,...,X_s] = s` in the pinned Mathlib version.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct
open MvPolynomial Polynomial

universe u v w

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

/-- An algebra homomorphism from a polynomial algebra to an arbitrary
algebra is determined by the images of the variables. -/
def mvPolynomialAlgHomEquivOver
    (R : Type u) (K : Type v) (s : ℕ)
    [CommSemiring R] [CommSemiring K] [Algebra R K] :
    (MvPolynomial (Fin s) R →ₐ[R] K) ≃ (Fin s → K) where
  toFun f := fun i ↦ f (MvPolynomial.X i)
  invFun x := MvPolynomial.aeval x
  left_inv f := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  right_inv x := by
    funext i
    simp

/-- The polynomial algebra over `R` has exactly `(#K)^s` `R`-algebra
homomorphisms to a finite `R`-algebra `K`. -/
theorem natCard_mvPolynomial_algHom_over
    (R : Type u) (K : Type v) (s : ℕ)
    [CommSemiring R] [CommSemiring K] [Algebra R K] [Finite K] :
    Nat.card (MvPolynomial (Fin s) R →ₐ[R] K) = Nat.card K ^ s := by
  rw [Nat.card_congr (mvPolynomialAlgHomEquivOver R K s)]
  simp only [Nat.card_fun, Nat.card_fin]

/-- Common zeroes in an `R`-algebra `K` of an ideal over `R`. -/
def affineIdealZeroLocusOver
    {R : Type u} {K : Type v} {N : ℕ}
    [CommRing R] [CommRing K] [Algebra R K]
    (I : Ideal (MvPolynomial (Fin N) R)) : Set (Fin N → K) :=
  {x | ∀ f ∈ I, MvPolynomial.aeval x f = 0}

/-- The literal finite common-zero set when the target algebra is finite. -/
def affineIdealZeroFinsetOver
    {R : Type u} {K : Type v} {N : ℕ}
    [CommRing R] [CommRing K] [Algebra R K] [Finite K]
    (I : Ideal (MvPolynomial (Fin N) R)) : Finset (Fin N → K) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  exact Finset.univ.filter fun x ↦ x ∈ affineIdealZeroLocusOver I

@[simp]
theorem mem_affineIdealZeroFinsetOver_iff
    {R : Type u} {K : Type v} {N : ℕ}
    [CommRing R] [CommRing K] [Algebra R K] [Finite K]
    {I : Ideal (MvPolynomial (Fin N) R)} {x : Fin N → K} :
    x ∈ affineIdealZeroFinsetOver I ↔
      ∀ f ∈ I, MvPolynomial.aeval x f = 0 := by
  classical
  simp [affineIdealZeroFinsetOver, affineIdealZeroLocusOver]

/-- Evaluation at a common zero descends to the quotient coordinate ring. -/
noncomputable def affineIdealPointToQuotientAlgHomOver
    {R : Type u} {K : Type v} {N : ℕ}
    [CommRing R] [CommRing K] [Algebra R K]
    (I : Ideal (MvPolynomial (Fin N) R))
    (x : {x : Fin N → K // x ∈ affineIdealZeroLocusOver I}) :
    (MvPolynomial (Fin N) R ⧸ I) →ₐ[R] K :=
  Ideal.Quotient.liftₐ I (MvPolynomial.aeval x.1) <| by
    intro f hf
    exact x.2 f hf

/-- A quotient-algebra point gives the images of the ambient coordinates. -/
noncomputable def quotientAlgHomToAffineIdealPointOver
    {R : Type u} {K : Type v} {N : ℕ}
    [CommRing R] [CommRing K] [Algebra R K]
    (I : Ideal (MvPolynomial (Fin N) R))
    (φ : (MvPolynomial (Fin N) R ⧸ I) →ₐ[R] K) :
    {x : Fin N → K // x ∈ affineIdealZeroLocusOver I} := by
  let x : Fin N → K := fun i ↦ φ (Ideal.Quotient.mk I (MvPolynomial.X i))
  refine ⟨x, ?_⟩
  intro f hf
  have hcomp :
      φ.comp (Ideal.Quotient.mkₐ R I) = MvPolynomial.aeval x := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [x]
  rw [← hcomp]
  change φ (Ideal.Quotient.mk I f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]

/-- Common zeroes over an arbitrary target algebra are exactly algebra
homomorphisms from the quotient coordinate ring. -/
noncomputable def affineIdealZeroLocusEquivQuotientAlgHomOver
    {R : Type u} {K : Type v} {N : ℕ}
    [CommRing R] [CommRing K] [Algebra R K]
    (I : Ideal (MvPolynomial (Fin N) R)) :
    {x : Fin N → K // x ∈ affineIdealZeroLocusOver I} ≃
      ((MvPolynomial (Fin N) R ⧸ I) →ₐ[R] K) where
  toFun := affineIdealPointToQuotientAlgHomOver I
  invFun := quotientAlgHomToAffineIdealPointOver I
  left_inv x := by
    apply Subtype.ext
    funext i
    simp [affineIdealPointToQuotientAlgHomOver,
      quotientAlgHomToAffineIdealPointOver]
  right_inv φ := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp [affineIdealPointToQuotientAlgHomOver,
      quotientAlgHomToAffineIdealPointOver]

/-- The subtype of the literal finite zero set is the predicate subtype of
the same common-zero condition. -/
noncomputable def affineIdealZeroFinsetOverSubtypeEquiv
    {R : Type u} {K : Type v} {N : ℕ}
    [CommRing R] [CommRing K] [Algebra R K] [Finite K]
    (I : Ideal (MvPolynomial (Fin N) R)) :
    {x : Fin N → K // x ∈ affineIdealZeroFinsetOver (K := K) I} ≃
      {x : Fin N → K // x ∈ affineIdealZeroLocusOver (K := K) I} where
  toFun x := ⟨x.1, (mem_affineIdealZeroFinsetOver_iff.mp x.2)⟩
  invFun x := ⟨x.1, (mem_affineIdealZeroFinsetOver_iff.mpr x.2)⟩
  left_inv x := by rfl
  right_inv x := by rfl

/-- Cardinal form of the relative common-zero/quotient-point equivalence. -/
theorem card_affineIdealZeroFinsetOver_eq_natCard_quotientAlgHom
    {R : Type u} {K : Type v} {N : ℕ}
    [CommRing R] [CommRing K] [Algebra R K] [Finite K]
    (I : Ideal (MvPolynomial (Fin N) R)) :
    (affineIdealZeroFinsetOver (K := K) I).card =
      Nat.card ((MvPolynomial (Fin N) R ⧸ I) →ₐ[R] K) := by
  classical
  calc
    (affineIdealZeroFinsetOver (K := K) I).card =
        Nat.card {x // x ∈ affineIdealZeroFinsetOver (K := K) I} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = Nat.card {x : Fin N → K //
        x ∈ affineIdealZeroLocusOver (K := K) I} :=
      Nat.card_congr (affineIdealZeroFinsetOverSubtypeEquiv (K := K) I)
    _ = Nat.card ((MvPolynomial (Fin N) R ⧸ I) →ₐ[R] K) :=
      Nat.card_congr (affineIdealZeroLocusEquivQuotientAlgHomOver I)

/-- A finite normalization over a polynomial algebra on `s` variables has
at most `D (#K)^s` points over every finite field carrying the displayed
base-ring structure.  The same `D` works for all target fields and all base
points. -/
theorem exists_uniform_natCard_algHom_le_mul_pow_of_finite_normalization_over_base
    (R : Type u) (A : Type v) (s : ℕ)
    [CommRing R] [CommRing A] [Algebra R A]
    (g : MvPolynomial (Fin s) R →ₐ[R] A)
    (hfinite : g.Finite) :
    ∃ D : ℕ, 1 ≤ D ∧
      ∀ (K : Type w), ∀ [Field K] [Finite K] [Algebra R K],
        Nat.card (A →ₐ[R] K) ≤ D * Nat.card K ^ s := by
  let B := MvPolynomial (Fin s) R
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : Module.Finite B A := hfinite
  obtain ⟨D₀, t, ht⟩ := Module.Finite.exists_fin (R := B) (M := A)
  let D := max 1 D₀
  refine ⟨D, Nat.le_max_left 1 D₀, ?_⟩
  intro K _ _ _
  let restriction : (A →ₐ[R] K) → (B →ₐ[R] K) :=
    fun psi ↦ psi.comp g
  letI : Finite (B →ₐ[R] K) :=
    Finite.of_equiv (Fin s → K) (mvPolynomialAlgHomEquivOver R K s).symm
  have hfiniteTotal : (Set.univ : Set (A →ₐ[R] K)).Finite := by
    apply Set.Finite.of_finite_fibers restriction (Set.toFinite _)
    intro phi _hphi
    letI : Algebra B K := phi.toRingHom.toAlgebra
    letI : Module.Finite K (K ⊗[B] A) :=
      Module.Finite.base_change B K A
    letI : Finite ((K ⊗[B] A) →ₐ[K] K) := by infer_instance
    letI : Finite (A →ₐ[B] K) :=
      Finite.of_injective (baseChangeLiftAlgHom B K A)
        (baseChangeLiftAlgHom_injective B K A)
    letI : Finite {psi : A →ₐ[R] K // psi.comp g = phi} :=
      Finite.of_equiv (A →ₐ[B] K)
        (restrictionFibreAlgHomEquiv R B A K g phi).symm
    simpa [restriction, Set.finite_coe_iff] using
      (Set.finite_coe_iff.mp
        (inferInstance : Finite {psi : A →ₐ[R] K // psi.comp g = phi}))
  letI : Finite (A →ₐ[R] K) :=
    Finite.of_finite_univ hfiniteTotal
  letI : Fintype (A →ₐ[R] K) := Fintype.ofFinite _
  letI : Fintype (B →ₐ[R] K) := Fintype.ofFinite _
  letI : DecidableEq (A →ₐ[R] K) := Classical.decEq _
  letI : DecidableEq (B →ₐ[R] K) := Classical.decEq _
  have hfibre : ∀ phi : B →ₐ[R] K,
      (finiteMapFiber restriction Finset.univ phi).card ≤ D := by
    intro phi
    rw [finiteMapFiber, ← Fintype.card_subtype]
    have hD₀ : Nat.card {psi : A →ₐ[R] K // psi.comp g = phi} ≤ D₀ :=
      natCard_restrictionFibre_le_of_span_fin R B A K D₀ g phi t ht
    simpa only [Nat.card_eq_fintype_card] using
      hD₀.trans (Nat.le_max_right 1 D₀)
  calc
    Nat.card (A →ₐ[R] K) = Fintype.card (A →ₐ[R] K) :=
      Nat.card_eq_fintype_card
    _ ≤ D * Fintype.card (B →ₐ[R] K) := by
      simpa using card_finiteSet_le_of_map_fibers_le
        restriction (Finset.univ : Finset (A →ₐ[R] K)) hfibre
    _ = D * Nat.card K ^ s := by
      rw [← natCard_mvPolynomial_algHom_over R K s,
        Nat.card_eq_fintype_card]

/-- A homogeneous prime ideal whose projectivization has dimension five
admits a homogeneous linear normalization with at most six parameters. -/
theorem exists_homogeneousLinearNormalizationData_parameterCount_le_six
    (I : Ideal (MvPolynomial (Fin 13) ℚ)) (degree : ℕ)
    (hI : Published.IsIntegralProjectiveVariety (N := 12) I 5 degree) :
    ∃ D : HomogeneousLinearNormalizationData I,
      D.parameterCount ≤ 6 := by
  rcases hI with ⟨hhom, _hsaturated, hprime, hdimdegree⟩
  obtain ⟨D⟩ := exists_homogeneousLinearNormalizationData 13 I hprime hhom
  refine ⟨D, ?_⟩
  have hdim : ringKrullDim (MvPolynomial (Fin 13) ℚ ⧸ I) = 6 := by
    simpa using hdimdegree.1
  exact normalization_parameter_le_of_ringKrullDim_eq
    D.hom D.hom_injective D.hom_finite.to_isIntegral hdim

/-- The ambient coordinate classes satisfy monic equations over a finite
homogeneous linear normalization, and the corresponding substituted
relations belong to the original ideal. -/
theorem exists_monic_relations_for_homogeneousLinearNormalizationData
    (I : Ideal (MvPolynomial (Fin 13) ℚ))
    (D : HomogeneousLinearNormalizationData I) :
    ∃ p : Fin 13 → (MvPolynomial (Fin D.parameterCount) ℚ)[X],
      (∀ i, (p i).Monic) ∧
      ∀ i, normalizationCoordinateRelation D.forms p i ∈ I := by
  let B := MvPolynomial (Fin D.parameterCount) ℚ
  let A := MvPolynomial (Fin 13) ℚ ⧸ I
  let g : B →ₐ[ℚ] A := D.hom
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : Module.Finite B A := D.hom_finite
  letI : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  have hcoordinate : ∀ i : Fin 13,
      IsIntegral B (Ideal.Quotient.mk I (MvPolynomial.X i)) := by
    intro i
    exact Algebra.IsIntegral.isIntegral
      (Ideal.Quotient.mk I (MvPolynomial.X i))
  choose p hpmonic hpzero using hcoordinate
  refine ⟨p, hpmonic, ?_⟩
  intro i
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hmap :
      Ideal.Quotient.mk I (normalizationCoordinateRelation D.forms p i) =
        (p i).eval₂ g.toRingHom
          (Ideal.Quotient.mk I (MvPolynomial.X i)) := by
    simpa only [normalizationCoordinateRelation,
      HomogeneousLinearNormalizationData.hom, g,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_comp, RingHom.coe_comp,
      Function.comp_apply] using
      (Polynomial.hom_eval₂ (p i) (MvPolynomial.aeval D.forms).toRingHom
        (Ideal.Quotient.mkₐ ℚ I).toRingHom (MvPolynomial.X i))
  rw [hmap]
  exact hpzero i

/-- The literal zero set over `ZMod p` of an ideal defined over the
principal open `Z[1/Δ]`.  The hypotheses make reduction of every
coefficient well defined. -/
def principalOpenIdealZeroFinset
    (N : ℕ) (Δ : ℤ) (p : ℕ) (hp : p.Prime)
    (hpΔ : ¬ p ∣ Δ.natAbs)
    (I : Ideal (MvPolynomial (Fin N) (Localization.Away Δ))) :
    Finset (Fin N → ZMod p) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Algebra (Localization.Away Δ) (ZMod p) :=
    (awayIntToZMod Δ p hp hpΔ).toAlgebra
  exact affineIdealZeroFinsetOver I

/-- The complete finite-normalization data used for a fixed projective
fivefold.  This is data, not an assumed geometric proposition. -/
structure FixedFivefoldResidueModel
    {r : ℕ} (f : Fin r → MvPolynomial (Fin 13) ℚ) where
  parameterCount : ℕ
  parameterCount_le_six : parameterCount ≤ 6
  denominator : ℤ
  denominator_ne_zero : denominator ≠ 0
  equations : Fin r →
    MvPolynomial (Fin 13) (Localization.Away denominator)
  parameters : Fin parameterCount →
    MvPolynomial (Fin 13) (Localization.Away denominator)
  relations : Fin 13 →
    (MvPolynomial (Fin parameterCount)
      (Localization.Away denominator))[X]
  equations_map : ∀ i, MvPolynomial.map
    (awayToFractionRing (R := ℤ) (K := ℚ)
      denominator denominator_ne_zero) (equations i) = f i
  relations_monic : ∀ i, (relations i).Monic
  generic_model : Ideal.map
      (MvPolynomial.map
        (awayToFractionRing (R := ℤ) (K := ℚ)
          denominator denominator_ne_zero))
      (finiteNormalizationModelIdeal equations parameters relations) =
    Ideal.span (Set.range f)
  normalization_finite :
    (finiteNormalizationModelAlgHom equations parameters relations).Finite
  localConstant : ℕ
  one_le_localConstant : 1 ≤ localConstant
  local_bound : ∀ (p : ℕ) (hp : p.Prime)
      (hpden : ¬ p ∣ denominator.natAbs),
    (principalOpenIdealZeroFinset 13 denominator p hp hpden
      (finiteNormalizationModelIdeal equations parameters relations)).card ≤
        localConstant * p ^ 6

/-- A fixed integral model of a projective fivefold, obtained from a finite
rational equation family, has a finite homogeneous linear normalization over
one principal open.  Every remaining prime fibre has at most `C p^6`
points, with `C` independent of the prime.

All data preceding the final universal quantifier are chosen once from the
fixed rational equation family. -/
theorem exists_fixedFivefoldFiniteNormalizationModel_and_local_residue_bound
    {r degree : ℕ} (f : Fin r → MvPolynomial (Fin 13) ℚ)
    (hI : Published.IsIntegralProjectiveVariety (N := 12)
      (Ideal.span (Set.range f)) 5 degree) :
    ∃ s : ℕ, s ≤ 6 ∧
      ∃ (Δ : ℤ) (hΔ : Δ ≠ 0),
      ∃ f₀ : Fin r →
          MvPolynomial (Fin 13) (Localization.Away Δ),
      ∃ q₀ : Fin s →
          MvPolynomial (Fin 13) (Localization.Away Δ),
      ∃ p₀ : Fin 13 →
          (MvPolynomial (Fin s) (Localization.Away Δ))[X],
        (∀ i, MvPolynomial.map
          (awayToFractionRing (R := ℤ) (K := ℚ) Δ hΔ) (f₀ i) = f i) ∧
        (∀ i, (p₀ i).Monic) ∧
        Ideal.map
            (MvPolynomial.map
              (awayToFractionRing (R := ℤ) (K := ℚ) Δ hΔ))
            (finiteNormalizationModelIdeal f₀ q₀ p₀) =
          Ideal.span (Set.range f) ∧
        (finiteNormalizationModelAlgHom f₀ q₀ p₀).Finite ∧
        ∃ C : ℕ, 1 ≤ C ∧
          ∀ (p : ℕ) (hp : p.Prime) (hpΔ : ¬ p ∣ Δ.natAbs),
            (principalOpenIdealZeroFinset 13 Δ p hp hpΔ
              (finiteNormalizationModelIdeal f₀ q₀ p₀)).card ≤
                C * p ^ 6 := by
  obtain ⟨D, hs⟩ :=
    exists_homogeneousLinearNormalizationData_parameterCount_le_six
      (Ideal.span (Set.range f)) degree hI
  obtain ⟨p, hpmonic, hprelation⟩ :=
    exists_monic_relations_for_homogeneousLinearNormalizationData
      (Ideal.span (Set.range f)) D
  obtain ⟨Δ, hΔ, f₀, q₀, p₀, hf₀, _hq₀, hp₀monic, _hp₀map,
      hmodel, hfinite⟩ :=
    exists_vertical_finite_normalization_model
      (R := ℤ) (K := ℚ) f D.forms p hpmonic
      (Ideal.span (Set.range f)) rfl hprelation
  let S := Localization.Away Δ
  let A := MvPolynomial (Fin 13) S ⧸
    finiteNormalizationModelIdeal f₀ q₀ p₀
  let g : MvPolynomial (Fin D.parameterCount) S →ₐ[S] A :=
    finiteNormalizationModelAlgHom f₀ q₀ p₀
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_natCard_algHom_le_mul_pow_of_finite_normalization_over_base
      S A D.parameterCount g hfinite
  refine ⟨D.parameterCount, hs, Δ, hΔ, f₀, q₀, p₀,
    hf₀, hp₀monic, hmodel, hfinite, C, hC, ?_⟩
  · intro ℘ h℘ h℘Δ
    letI : NeZero ℘ := ⟨h℘.ne_zero⟩
    letI : Fact ℘.Prime := ⟨h℘⟩
    letI : Algebra S (ZMod ℘) :=
      (awayIntToZMod Δ ℘ h℘ h℘Δ).toAlgebra
    have hcount : Nat.card (A →ₐ[S] ZMod ℘) ≤
        C * Nat.card (ZMod ℘) ^ D.parameterCount :=
      hbound (ZMod ℘)
    calc
      (principalOpenIdealZeroFinset 13 Δ ℘ h℘ h℘Δ
          (finiteNormalizationModelIdeal f₀ q₀ p₀)).card =
          Nat.card (A →ₐ[S] ZMod ℘) := by
        simpa only [principalOpenIdealZeroFinset, S, A] using
          card_affineIdealZeroFinsetOver_eq_natCard_quotientAlgHom
            (K := ZMod ℘)
            (finiteNormalizationModelIdeal f₀ q₀ p₀)
      _ ≤ C * Nat.card (ZMod ℘) ^ D.parameterCount := hcount
      _ = C * ℘ ^ D.parameterCount := by simp
      _ ≤ C * ℘ ^ 6 := by
        exact Nat.mul_le_mul_left C (Nat.pow_le_pow_right h℘.one_le hs)

/-- Structured form of
`exists_fixedFivefoldFiniteNormalizationModel_and_local_residue_bound`. -/
theorem nonempty_fixedFivefoldResidueModel
    {r degree : ℕ} (f : Fin r → MvPolynomial (Fin 13) ℚ)
    (hI : Published.IsIntegralProjectiveVariety (N := 12)
      (Ideal.span (Set.range f)) 5 degree) :
    Nonempty (FixedFivefoldResidueModel f) := by
  obtain ⟨s, hs, Δ, hΔ, f₀, q₀, p₀, hf₀, hp₀, hmodel, hfinite,
      C, hC, hlocal⟩ :=
    exists_fixedFivefoldFiniteNormalizationModel_and_local_residue_bound
      f hI
  exact ⟨
    { parameterCount := s
      parameterCount_le_six := hs
      denominator := Δ
      denominator_ne_zero := hΔ
      equations := f₀
      parameters := q₀
      relations := p₀
      equations_map := hf₀
      relations_monic := hp₀
      generic_model := hmodel
      normalization_finite := hfinite
      localConstant := C
      one_le_localConstant := hC
      local_bound := hlocal }⟩

/-- Canonical finite indexing of a finite equation family. -/
noncomputable def indexedFinsetFamily {A : Type u} (S : Finset A) :
    Fin S.card → A :=
  fun i ↦ (S.equivFin.symm i).1

theorem range_indexedFinsetFamily {A : Type u}
    (S : Finset A) : Set.range (indexedFinsetFamily S) = (S : Set A) := by
  classical
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact (S.equivFin.symm i).2
  · intro hx
    let xS : S := ⟨x, hx⟩
    refine ⟨S.equivFin xS, ?_⟩
    change (S.equivFin.symm (S.equivFin xS)).1 = x
    rw [S.equivFin.symm_apply_apply]

theorem span_range_indexedFinsetFamily_eq_finiteEquationIdeal
    {K : Type u} {N : ℕ} [Field K]
    (S : Finset (MvPolynomial (Fin N) K)) :
    Ideal.span (Set.range (indexedFinsetFamily S)) =
      finiteEquationIdeal S := by
  classical
  rw [range_indexedFinsetFamily]
  rfl

/-- Finite-family endpoint matching the strict root's literal generated
ideal. -/
theorem nonempty_fixedFivefoldResidueModel_finiteEquationIdeal
    (equations : Finset (MvPolynomial (Fin 13) ℚ)) (degree : ℕ)
    (hI : Published.IsIntegralProjectiveVariety (N := 12)
      (finiteEquationIdeal equations) 5 degree) :
    Nonempty (FixedFivefoldResidueModel
      (indexedFinsetFamily equations)) := by
  apply nonempty_fixedFivefoldResidueModel
    (degree := degree) (indexedFinsetFamily equations)
  rw [span_range_indexedFinsetFamily_eq_finiteEquationIdeal]
  exact hI

/-- Every integral point annihilating the rational ideal of the fixed
fivefold reduces, at a prime away from the model denominator, to a point of
the principal-open finite model.  This is the bridge needed for occupied
residue classes; no assertion about all points of an arbitrary special fibre
is used. -/
theorem intCast_mem_principalOpenModel_of_mem_rationalIdeal
    {r : ℕ} {f : Fin r → MvPolynomial (Fin 13) ℚ}
    (M : FixedFivefoldResidueModel f)
    (x : Fin 13 → ℤ)
    (hx : ∀ g ∈ Ideal.span (Set.range f),
      MvPolynomial.eval (fun i ↦ (x i : ℚ)) g = 0)
    (p : ℕ) (hp : p.Prime)
    (hpden : ¬ p ∣ M.denominator.natAbs) :
    (fun i ↦ (x i : ZMod p)) ∈
      principalOpenIdealZeroFinset 13 M.denominator p hp hpden
        (finiteNormalizationModelIdeal
          M.equations M.parameters M.relations) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  let S := Localization.Away M.denominator
  let φQ : S →+* ℚ :=
    awayToFractionRing M.denominator M.denominator_ne_zero
  let φp : S →+* ZMod p :=
    awayIntToZMod M.denominator p hp hpden
  letI : Algebra S (ZMod p) := φp.toAlgebra
  change (fun i ↦ (x i : ZMod p)) ∈
    affineIdealZeroFinsetOver
      (finiteNormalizationModelIdeal
        M.equations M.parameters M.relations)
  rw [mem_affineIdealZeroFinsetOver_iff]
  intro g₀ hg₀
  have hQg₀ : MvPolynomial.map φQ g₀ ∈ Ideal.span (Set.range f) := by
    rw [← M.generic_model]
    exact Ideal.mem_map_of_mem _ hg₀
  have hQzero :
      MvPolynomial.eval (fun i ↦ (x i : ℚ))
        (MvPolynomial.map φQ g₀) = 0 :=
    hx _ hQg₀
  let xS : Fin 13 → S :=
    fun i ↦ algebraMap ℤ S (x i)
  have hxQcoord : φQ ∘ xS = fun i ↦ (x i : ℚ) := by
    funext i
    simpa only [xS, φQ, Function.comp_apply, S] using
      awayToFractionRing_algebraMap
        M.denominator M.denominator_ne_zero (x i)
  have hmapQ :
      φQ (MvPolynomial.eval xS g₀) =
        MvPolynomial.eval (fun i ↦ (x i : ℚ))
          (MvPolynomial.map φQ g₀) := by
    have heval := MvPolynomial.map_eval φQ xS g₀
    rw [hxQcoord] at heval
    exact heval
  have hSzero : MvPolynomial.eval xS g₀ = 0 := by
    apply (awayToFractionRing_injective (R := ℤ) (K := ℚ)
      M.denominator M.denominator_ne_zero)
    rw [hmapQ, hQzero, map_zero]
  change MvPolynomial.eval₂ φp (fun i ↦ (x i : ZMod p)) g₀ = 0
  have hspecialize :=
    (MvPolynomial.eval₂_comp φp xS g₀).symm
  have hxpcoord : φp ∘ xS = fun i ↦ (x i : ZMod p) := by
    funext i
    simpa only [xS, φp, Function.comp_apply, S] using
      awayIntToZMod_algebraMap M.denominator p hp hpden (x i)
  rw [hxpcoord, hSzero, map_zero] at hspecialize
  exact hspecialize

/-- Literal finite-equation specialization of the preceding bridge. -/
theorem intCast_mem_principalOpenModel_of_mem_integralEquationFinset
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (M : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (x : Fin 13 → ℤ)
    (hx : ∀ g ∈ equations, MvPolynomial.eval x g = 0)
    (p : ℕ) (hp : p.Prime)
    (hpden : ¬ p ∣ M.denominator.natAbs) :
    (fun i ↦ (x i : ZMod p)) ∈
      principalOpenIdealZeroFinset 13 M.denominator p hp hpden
        (finiteNormalizationModelIdeal
          M.equations M.parameters M.relations) := by
  refine intCast_mem_principalOpenModel_of_mem_rationalIdeal
    M x ?_ p hp hpden
  rw [span_range_indexedFinsetFamily_eq_finiteEquationIdeal]
  have hcommon : (fun i ↦ (x i : ℚ)) ∈
      finiteAffineCommonZeroLocus (rationalizedEquationFinset equations) := by
    intro q hq
    rw [rationalizedEquationFinset, Finset.mem_image] at hq
    obtain ⟨g, hg, rfl⟩ := hq
    rw [eval_map_intCast, hx g hg, Int.cast_zero]
  rw [← affineIdealZeroLocus_finiteEquationIdeal] at hcommon
  exact hcommon

/-- Reduction modulo `p` of the affine substitution `x = x₀ + m z`. -/
def zmodIntegralAffineMap {N : ℕ}
    (p m : ℕ) (x₀ : Fin N → ℤ) (z : Fin N → ZMod p) :
    Fin N → ZMod p :=
  fun i ↦ (x₀ i : ZMod p) + (m : ZMod p) * z i

/-- The reduced affine substitution is injective whenever `p` does not
divide its scale. -/
theorem zmodIntegralAffineMap_injective
    {N p m : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m)
    (x₀ : Fin N → ℤ) :
    Function.Injective (zmodIntegralAffineMap p m x₀) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  have hm : (m : ZMod p) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff m p).not.mpr hpm
  intro z w hzw
  funext i
  have hi := congrFun hzw i
  have hi' : (m : ZMod p) * z i = (m : ZMod p) * w i := by
    exact add_left_cancel hi
  exact mul_left_cancel₀ hm hi'

/-- Consequently any finite family of normalized residue vectors whose
affine images lie on the fixed principal-open model has cardinality bounded
by the model's full residue count. -/
theorem card_le_principalOpenModel_of_affine_image_mem
    {r : ℕ} {f : Fin r → MvPolynomial (Fin 13) ℚ}
    (M : FixedFivefoldResidueModel f)
    (p m : ℕ) (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hpden : ¬ p ∣ M.denominator.natAbs)
    (x₀ : Fin 13 → ℤ) (Y : Finset (Fin 13 → ZMod p))
    (himage : ∀ z ∈ Y,
      zmodIntegralAffineMap p m x₀ z ∈
        principalOpenIdealZeroFinset 13 M.denominator p hp hpden
          (finiteNormalizationModelIdeal
            M.equations M.parameters M.relations)) :
    Y.card ≤
      (principalOpenIdealZeroFinset 13 M.denominator p hp hpden
        (finiteNormalizationModelIdeal
          M.equations M.parameters M.relations)).card := by
  classical
  let φ := zmodIntegralAffineMap p m x₀
  have hφ : Function.Injective φ :=
    zmodIntegralAffineMap_injective hp hpm x₀
  have hsubset : Y.image φ ⊆
      principalOpenIdealZeroFinset 13 M.denominator p hp hpden
        (finiteNormalizationModelIdeal
          M.equations M.parameters M.relations) := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact himage z hz
  calc
    Y.card = (Y.image φ).card :=
      (Finset.card_image_iff.mpr hφ.injOn).symm
    _ ≤ (principalOpenIdealZeroFinset 13 M.denominator p hp hpden
        (finiteNormalizationModelIdeal
          M.equations M.parameters M.relations)).card :=
      Finset.card_le_card hsubset

/-- Exact square-free consequence for one fixed principal-open model. -/
theorem card_fixedPrincipalOpenModel_crt_le
    {s r : ℕ} {Δ : ℤ}
    (f₀ : Fin r → MvPolynomial (Fin 13) (Localization.Away Δ))
    (q₀ : Fin s → MvPolynomial (Fin 13) (Localization.Away Δ))
    (p₀ : Fin 13 → (MvPolynomial (Fin s) (Localization.Away Δ))[X])
    (C : ℕ) (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hgood : ∀ p ∈ P, ¬ p ∣ Δ.natAbs)
    (hlocal : ∀ (p : P),
      (principalOpenIdealZeroFinset 13 Δ (p : ℕ)
        (hprime p p.property) (hgood p p.property)
        (finiteNormalizationModelIdeal f₀ q₀ p₀)).card ≤
          C * (p : ℕ) ^ 6) :
    (crtGlobalResidues (fun p : P ↦ (p : ℕ))
      (primeSubtype_pairwise_coprime hprime)
      (primeSubtype_ne_zero hprime) 13
      (fun p ↦ principalOpenIdealZeroFinset 13 Δ (p : ℕ)
        (hprime p p.property) (hgood p p.property)
        (finiteNormalizationModelIdeal f₀ q₀ p₀))).card ≤
      C ^ P.card * (primeProduct P) ^ 6 := by
  exact card_squarefreePrime_crtGlobalResidues_le
    P hprime 13 6 C
      (fun p ↦ principalOpenIdealZeroFinset 13 Δ (p : ℕ)
        (hprime p p.property) (hgood p p.property)
        (finiteNormalizationModelIdeal f₀ q₀ p₀)) hlocal

/-- Reservoir-scale form: the fixed local factor is absorbed into `H^ε`,
leaving the dimension-six power of the square-free modulus. -/
theorem card_fixedPrincipalOpenModel_crt_cast_le_rpow_mul
    {M₀ ε H : ℝ} (hM₀ : 0 ≤ M₀) (hε : 0 < ε)
    {s r : ℕ} {Δ : ℤ}
    (f₀ : Fin r → MvPolynomial (Fin 13) (Localization.Away Δ))
    (q₀ : Fin s → MvPolynomial (Fin 13) (Localization.Away Δ))
    (p₀ : Fin 13 → (MvPolynomial (Fin s) (Localization.Away Δ))[X])
    (C : ℕ) (hC : 1 ≤ C)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hgood : ∀ p ∈ P, ¬ p ∣ Δ.natAbs)
    (hPcard : P.card ≤ reservoirDepth M₀ H)
    (hH : reservoirSubpowerThreshold M₀ (C : ℝ) ε ≤ H)
    (hlocal : ∀ (p : P),
      (principalOpenIdealZeroFinset 13 Δ (p : ℕ)
        (hprime p p.property) (hgood p p.property)
        (finiteNormalizationModelIdeal f₀ q₀ p₀)).card ≤
          C * (p : ℕ) ^ 6) :
    ((crtGlobalResidues (fun p : P ↦ (p : ℕ))
      (primeSubtype_pairwise_coprime hprime)
      (primeSubtype_ne_zero hprime) 13
      (fun p ↦ principalOpenIdealZeroFinset 13 Δ (p : ℕ)
        (hprime p p.property) (hgood p p.property)
        (finiteNormalizationModelIdeal f₀ q₀ p₀))).card : ℝ) ≤
      H ^ ε * (primeProduct P : ℝ) ^ 6 := by
  exact card_squarefreePrime_crtGlobalResidues_cast_le_rpow_mul
    hM₀ hε P hprime 13 6 C hC hPcard hH
      (fun p ↦ principalOpenIdealZeroFinset 13 Δ (p : ℕ)
        (hprime p p.property) (hgood p p.property)
        (finiteNormalizationModelIdeal f₀ q₀ p₀)) hlocal

end

end TranslatedDepthSeven

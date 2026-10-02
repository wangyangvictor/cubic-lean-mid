import TranslatedDepthSeven.GenericFunctionFieldDifferentials
import TranslatedDepthSeven.EquationFamilyTangentBaseChange
import TranslatedDepthSeven.DepthSevenJacobianExceptionalLocus
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# A displayed Jacobian minor on a prime sixfold in thirteen-space

This file proves the generic-rank assertion needed by the depth-seven
argument directly from a finite presentation.  It first identifies the row
span of the generic Jacobian with the conormal image.  Noether normalization
then computes its dimension.  Finally, elementary linear algebra selects a
literal `7 × 7` minor belonging to the original finite equation family.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct
open KaehlerDifferential

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

/-- Scalar extension carries a spanning family to a spanning family of the
base-changed module. -/
theorem span_one_tmul_eq_top_of_span_eq_top
    {R S M ι : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [Algebra R S]
    (v : ι → M) (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.span S
      (Set.range (fun i ↦ (1 : S) ⊗ₜ[R] v i)) = ⊤ := by
  have hbase :
      (Submodule.span R (Set.range v)).baseChange S =
        (⊤ : Submodule R M).baseChange S :=
    congrArg (fun p : Submodule R M ↦ p.baseChange S) hv
  rw [Submodule.baseChange_span, Submodule.baseChange_top] at hbase
  have himage :
      (TensorProduct.mk R S M 1) '' Set.range v =
        Set.range (fun i ↦ (1 : S) ⊗ₜ[R] v i) := by
    ext x
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨v i, ⟨i, rfl⟩, rfl⟩
  rwa [himage] at hbase

section GenericConormal

variable {R : Type*} [Field R] [CharZero R]
variable {A : Type*} [CommRing A] [IsDomain A] [Algebra R A]
variable {n s : ℕ} {ι : Type*}

/-- For a finite presentation of a normalized affine domain, the generic
Jacobian row span has dimension `n - s`. -/
theorem finrank_generic_gradient_span_eq
    (G : Algebra.Generators R A (Fin n))
    (F : ι → MvPolynomial (Fin n) R)
    (hF : Ideal.span (Set.range F) = G.ker)
    (normalization : MvPolynomial (Fin s) R →ₐ[R] A)
    (hnormalization : Function.Injective normalization)
    (hfinite : normalization.Finite) :
    Module.finrank (FractionRing A)
      (Submodule.span (FractionRing A) (Set.range fun i j ↦
        algebraMap A (FractionRing A)
          (MvPolynomial.aeval G.val (MvPolynomial.pderiv j (F i))))) =
      n - s := by
  let L := FractionRing A
  letI : Algebra (MvPolynomial (Fin n) R) A := G.algebra
  let P := G.toExtension
  let rel : ι → P.ker := fun i ↦
    ⟨F i, hF.le (Ideal.subset_span ⟨i, rfl⟩)⟩
  have hcot : Submodule.span A
      (Set.range (fun i ↦ Algebra.Extension.Cotangent.mk (rel i))) = ⊤ := by
    simpa only [P, rel] using
      (Algebra.Extension.Cotangent.span_eq_top_of_span_eq_ker
        (P := G.toExtension) F hF)
  have hcotL : Submodule.span L
      (Set.range (fun i ↦
        (1 : L) ⊗ₜ[A] Algebra.Extension.Cotangent.mk (rel i))) = ⊤ :=
    span_one_tmul_eq_top_of_span_eq_top _ hcot
  let fL := P.cotangentComplex.baseChange L
  let gL := P.toKaehler.baseChange L
  have hexact : Function.Exact fL gL := by
    simpa only [fL, gL, LinearMap.baseChange_eq_ltensor] using
      (lTensor_exact L P.exact_cotangentComplex_toKaehler
        P.toKaehler_surjective)
  have hsurj : Function.Surjective gL := by
    rw [show gL = P.toKaehler.baseChange L from rfl,
      LinearMap.baseChange_eq_ltensor]
    exact P.toKaehler.lTensor_surjective _ P.toKaehler_surjective
  have hambient : Module.finrank L (L ⊗[A] P.CotangentSpace) = n := by
    rw [Module.finrank_eq_card_basis
      (G.cotangentSpaceBasis.baseChange L), Fintype.card_fin]
  letI : Module.Finite L (L ⊗[A] P.CotangentSpace) :=
    Module.Finite.of_basis (G.cotangentSpaceBasis.baseChange L)
  letI : Algebra.FormallyEtale A L :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  let eAL : (L ⊗[A] (KaehlerDifferential R A)) ≃ₗ[L]
      KaehlerDifferential R L :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A L
  have htarget : Module.finrank L
      (L ⊗[A] (KaehlerDifferential R A)) = s := by
    calc
      Module.finrank L (L ⊗[A] (KaehlerDifferential R A)) =
          Module.finrank L (KaehlerDifferential R L) := eAL.finrank_eq
      _ = s := finrank_fractionRing_kaehler_eq_normalizationParameters
        normalization hnormalization hfinite
  have hrange : Module.finrank L (LinearMap.range fL) = n - s := by
    have hsum := LinearMap.finrank_range_add_finrank_ker gL
    rw [LinearMap.range_eq_top_of_surjective gL hsurj,
      finrank_top, htarget,
      hexact.linearMap_ker_eq, hambient] at hsum
    omega
  have himageSpan : Submodule.span L
      (Set.range (fun i ↦ fL
        ((1 : L) ⊗ₜ[A] Algebra.Extension.Cotangent.mk (rel i)))) =
      LinearMap.range fL := by
    rw [show Set.range (fun i ↦ fL
          ((1 : L) ⊗ₜ[A] Algebra.Extension.Cotangent.mk (rel i))) =
        fL '' Set.range (fun i ↦
          ((1 : L) ⊗ₜ[A] Algebra.Extension.Cotangent.mk (rel i))) by
      exact Set.range_comp (f := fun i ↦
        ((1 : L) ⊗ₜ[A] Algebra.Extension.Cotangent.mk (rel i)))
        (g := fL)]
    rw [← Submodule.map_span, hcotL, Submodule.map_top]
  let coordinates : (L ⊗[A] P.CotangentSpace) ≃ₗ[L] (Fin n → L) :=
    (G.cotangentSpaceBasis.baseChange L).repr.trans
      (Finsupp.linearEquivFunOnFinite L L (Fin n))
  let v : ι → Fin n → L := fun i ↦
    coordinates (fL
      ((1 : L) ⊗ₜ[A] Algebra.Extension.Cotangent.mk (rel i)))
  have hvspan : Submodule.span L (Set.range v) =
      (LinearMap.range fL).map coordinates.toLinearMap := by
    calc
      Submodule.span L (Set.range v) =
          (Submodule.span L (Set.range fun i ↦ fL
            ((1 : L) ⊗ₜ[A] Algebra.Extension.Cotangent.mk (rel i)))).map
              coordinates.toLinearMap := by
        rw [Submodule.map_span]
        congr 1
        ext z
        simp only [Set.mem_image, Set.mem_range]
        constructor
        · rintro ⟨i, rfl⟩
          exact ⟨fL ((1 : L) ⊗ₜ[A]
            Algebra.Extension.Cotangent.mk (rel i)), ⟨i, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
          exact ⟨i, rfl⟩
      _ = (LinearMap.range fL).map coordinates.toLinearMap := by
        rw [himageSpan]
  have hvfinrank : Module.finrank L
      (Submodule.span L (Set.range v)) = n - s := by
    rw [hvspan, LinearEquiv.finrank_map_eq coordinates, hrange]
  have hv : v = fun i j ↦
      algebraMap A L
        (MvPolynomial.aeval G.val (MvPolynomial.pderiv j (F i))) := by
    funext i j
    simp only [v, coordinates, LinearEquiv.trans_apply,
      Finsupp.linearEquivFunOnFinite_apply, fL,
      LinearMap.baseChange_tmul]
    rw [Algebra.Extension.cotangentComplex_mk,
      Module.Basis.baseChange_repr_tmul]
    simp only [rel]
    dsimp only [P, Algebra.Generators.toExtension_Ring]
    rw [G.cotangentSpaceBasis_repr_tmul, one_mul]
    simp [Algebra.smul_def]
  rwa [← hv]

end GenericConormal

section PrimeDimensionSix

variable {k : Type*} [Field k] [CharZero k]

/-- A prime affine sixfold in thirteen-space, presented by a finite family,
has a literal displayed `7 × 7` Jacobian determinant outside its prime
ideal. -/
theorem exists_depthSevenJacobianChart_determinant_notMem_of_prime_dimension_six
    (equations : Finset (MvPolynomial (Fin 13) k))
    (P : Ideal (MvPolynomial (Fin 13) k))
    (hprime : P.IsPrime)
    (hspan : Ideal.span (equations : Set (MvPolynomial (Fin 13) k)) = P)
    (hdim : ringKrullDim (MvPolynomial (Fin 13) k ⧸ P) = 6) :
    ∃ C : DepthSevenJacobianChartIndex equations, C.determinant ∉ P := by
  letI : P.IsPrime := hprime
  let A := MvPolynomial (Fin 13) k ⧸ P
  let q : MvPolynomial (Fin 13) k →ₐ[k] A := Ideal.Quotient.mkₐ k P
  let G : Algebra.Generators k A (Fin 13) :=
    Algebra.Generators.ofAlgHom q (Ideal.Quotient.mkₐ_surjective k P)
  let F : {f // f ∈ equations} → MvPolynomial (Fin 13) k :=
    fun f ↦ f.1
  have hGker : G.ker = P := by
    dsimp only [G]
    rw [Algebra.Generators.ker_ofAlgHom]
    exact Ideal.Quotient.mkₐ_ker k P
  have hF : Ideal.span (Set.range F) = G.ker := by
    rw [hGker, ← hspan]
    congr 1
    exact Subtype.range_coe_subtype
  obtain ⟨s, _hs13, normalization, hinjective, hfinite⟩ :=
    exists_finite_injective_normalization_of_primeAffine P
  have hsix : s ≤ 6 :=
    normalization_parameter_le_of_ringKrullDim_eq
      normalization hinjective hfinite.to_isIntegral hdim
  have hgrad := finrank_generic_gradient_span_eq
    G F hF normalization hinjective hfinite
  have hseven : 7 ≤ Module.finrank (FractionRing A)
      (Submodule.span (FractionRing A) (Set.range fun i j ↦
        algebraMap A (FractionRing A)
          (MvPolynomial.aeval G.val (MvPolynomial.pderiv j (F i))))) := by
    rw [hgrad]
    omega
  obtain ⟨rows, cols, hrows, hcols, hdet⟩ :=
    TangentBaseChange.exists_nonzero_minor_of_finrank_span_ge
      (v := fun i j ↦
        algebraMap A (FractionRing A)
          (MvPolynomial.aeval G.val (MvPolynomial.pderiv j (F i))))
      hseven
  let C : DepthSevenJacobianChartIndex equations :=
    ⟨rows, cols, hrows, hcols⟩
  refine ⟨C, ?_⟩
  intro hCP
  have hminorP : finiteEquationJacobianMinor equations rows cols ∈ P := by
    simpa only [C, DepthSevenJacobianChartIndex.determinant] using hCP
  have hGaeval : MvPolynomial.aeval G.val = q := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [G, q, Algebra.Generators.ofAlgHom]
  have hqzero : q (finiteEquationJacobianMinor equations rows cols) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hminorP
  apply hdet
  rw [hGaeval]
  let φ : MvPolynomial (Fin 13) k →+* FractionRing A :=
    (algebraMap A (FractionRing A)).comp q.toRingHom
  have hmatrix : Matrix.of (fun i j ↦
      algebraMap A (FractionRing A)
        (q (MvPolynomial.pderiv (cols j) (F (rows i))))) =
      φ.mapMatrix
        (finiteEquationJacobianMinorMatrix equations rows cols) := by
    rfl
  have hφzero : φ (finiteEquationJacobianMinor equations rows cols) = 0 := by
    dsimp only [φ]
    rw [RingHom.comp_apply]
    have hqzero' : q.toRingHom
        (finiteEquationJacobianMinor equations rows cols) = 0 := hqzero
    rw [hqzero', map_zero]
  rw [hmatrix, ← φ.map_det]
  simpa only [finiteEquationJacobianMinor] using hφzero

end PrimeDimensionSix

end

end TranslatedDepthSeven

import TranslatedDepthSeven.GenericFunctionFieldDifferentials
import TranslatedDepthSeven.GenericJacobianMinor
import TranslatedDepthSeven.LocalSmoothConormalEquationSelection
import TranslatedDepthSeven.LocalizedIdealEquality
import TranslatedDepthSeven.ExplicitDenominatorClearing
import TranslatedDepthSeven.PrimeStratumGenericIdealSpreading
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# A literal Jacobian chart at the generic point of a prime component

This file connects the generic differential-rank calculation with exact
generation of a prime ideal in its local ring.  The equations and coordinate
columns selected below are literal members of the supplied finite family.
The final principal-open statement is only an equality of localized ideals;
it makes no assertion about reducedness or equidimensionality of special
fibres.
-/

namespace TranslatedDepthSeven

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000

open scoped TensorProduct
open MvPolynomial KaehlerDifferential IsLocalRing

universe u

/-- The normalization-parameter differential-rank calculation for an
arbitrary chosen fraction field of the normalized affine domain.  This is
the type-flexible form needed for an ideal residue field. -/
theorem finrank_isFractionRing_kaehler_eq_normalizationParameters
    {k A L : Type u} [Field k] [CharZero k]
    [CommRing A] [IsDomain A] [Algebra k A]
    [Field L] [Algebra k L] [Algebra A L] [IsScalarTower k A L]
    [IsFractionRing A L] {s : ℕ}
    (g : MvPolynomial (Fin s) k →ₐ[k] A)
    (hg : Function.Injective g) (hf : g.Finite) :
    Module.finrank L Ω[L⁄k] = s := by
  let B := MvPolynomial (Fin s) k
  let K := FractionRing B
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : IsScalarTower k B A :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      simp [RingHom.algebraMap_toAlgebra]
  letI : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective B A).mpr hg
  letI : Module.Finite B A := hf
  letI : CharZero B := charZero_of_injective_algebraMap
    (FaithfulSMul.algebraMap_injective k B)
  letI : CharZero A := charZero_of_injective_algebraMap
    (FaithfulSMul.algebraMap_injective k A)
  letI : Algebra B L :=
    ((algebraMap A L).comp g.toRingHom).toAlgebra
  letI : IsScalarTower B A L :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      simp [RingHom.algebraMap_toAlgebra]
  letI : IsScalarTower k B L :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      rw [IsScalarTower.algebraMap_apply k A L,
        IsScalarTower.algebraMap_apply k B A]
      rfl
  letI : FaithfulSMul B L :=
    (faithfulSMul_iff_algebraMap_injective B L).mpr (by
      simpa only [RingHom.algebraMap_toAlgebra] using
        (IsFractionRing.injective A L).comp hg)
  letI : Algebra K L := FractionRing.liftAlgebra B L
  letI : IsScalarTower k K L :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      rw [IsScalarTower.algebraMap_apply k B L,
        IsScalarTower.algebraMap_apply k B K,
        IsScalarTower.algebraMap_apply B K L]
  letI : Module.Finite K L :=
    Module.Finite.of_isLocalization B A (nonZeroDivisors B)
  letI : CharZero K :=
    charZero_of_injective_algebraMap (IsFractionRing.injective B K)
  haveI : Algebra.IsSeparable K L := by infer_instance
  letI : Algebra.FormallyEtale B K :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors B)
  letI : Algebra.FormallyEtale K L :=
    Algebra.FormallyEtale.of_isSeparable K L
  let eBK : (K ⊗[B] Ω[B⁄k]) ≃ₗ[K] Ω[K⁄k] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k B K
  let eKL : (L ⊗[K] Ω[K⁄k]) ≃ₗ[L] Ω[L⁄k] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k K L
  calc
    Module.finrank L Ω[L⁄k] =
        Module.finrank L (L ⊗[K] Ω[K⁄k]) := eKL.finrank_eq.symm
    _ = Module.finrank K Ω[K⁄k] := Module.finrank_baseChange
    _ = Module.finrank K (K ⊗[B] Ω[B⁄k]) := eBK.finrank_eq.symm
    _ = Module.finrank B Ω[B⁄k] := Module.finrank_baseChange
    _ = s := by
      rw [Module.finrank_eq_card_basis
        (KaehlerDifferential.mvPolynomialBasis k (Fin s)),
        Fintype.card_fin]

/-- In characteristic zero, the chosen fraction field of a finite normalized
affine domain is formally smooth over the ground field. -/
theorem formallySmooth_isFractionRing_of_finite_normalization
    {k A L : Type u} [Field k] [CharZero k]
    [CommRing A] [IsDomain A] [Algebra k A]
    [Field L] [Algebra k L] [Algebra A L] [IsScalarTower k A L]
    [IsFractionRing A L] {s : ℕ}
    (g : MvPolynomial (Fin s) k →ₐ[k] A)
    (hg : Function.Injective g) (hf : g.Finite) :
    Algebra.FormallySmooth k L := by
  let B := MvPolynomial (Fin s) k
  let K := FractionRing B
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : IsScalarTower k B A :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      simp [RingHom.algebraMap_toAlgebra]
  letI : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective B A).mpr hg
  letI : Module.Finite B A := hf
  letI : CharZero B := charZero_of_injective_algebraMap
    (FaithfulSMul.algebraMap_injective k B)
  letI : CharZero A := charZero_of_injective_algebraMap
    (FaithfulSMul.algebraMap_injective k A)
  letI : Algebra B L :=
    ((algebraMap A L).comp g.toRingHom).toAlgebra
  letI : IsScalarTower B A L :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      simp [RingHom.algebraMap_toAlgebra]
  letI : IsScalarTower k B L :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      rw [IsScalarTower.algebraMap_apply k A L,
        IsScalarTower.algebraMap_apply k B A]
      rfl
  letI : FaithfulSMul B L :=
    (faithfulSMul_iff_algebraMap_injective B L).mpr (by
      simpa only [RingHom.algebraMap_toAlgebra] using
        (IsFractionRing.injective A L).comp hg)
  letI : Algebra K L := FractionRing.liftAlgebra B L
  letI : IsScalarTower k K L :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      rw [IsScalarTower.algebraMap_apply k B L,
        IsScalarTower.algebraMap_apply k B K,
        IsScalarTower.algebraMap_apply B K L]
  letI : Module.Finite K L :=
    Module.Finite.of_isLocalization B A (nonZeroDivisors B)
  letI : CharZero K :=
    charZero_of_injective_algebraMap (IsFractionRing.injective B K)
  haveI : Algebra.IsSeparable K L := by infer_instance
  letI : Algebra.FormallyEtale B K :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors B)
  letI : Algebra.FormallySmooth k K :=
    Algebra.FormallySmooth.comp k B K
  letI : Algebra.FormallyEtale K L :=
    Algebra.FormallyEtale.of_isSeparable K L
  exact Algebra.FormallySmooth.comp k K L

/-- The residue map of the polynomial local ring at a prime, regarded as an
algebra extension over the ground field. -/
noncomputable def genericPrimeLocalExtension
    {k : Type u} [Field k] {N : ℕ}
    (Q : Ideal (MvPolynomial (Fin N) k)) [Q.IsPrime] :
    Algebra.Extension k Q.ResidueField :=
  Algebra.Extension.ofSurjective
    (IsScalarTower.toAlgHom k (Localization.AtPrime Q) Q.ResidueField)
    IsLocalRing.residue_surjective

/-- The kernel of the generic-point local presentation is the extension of
the prime ideal to its local ring. -/
theorem genericPrimeLocalExtension_ker
    {k : Type u} [Field k] {N : ℕ}
    (Q : Ideal (MvPolynomial (Fin N) k)) [Q.IsPrime] :
    (genericPrimeLocalExtension Q).ker =
      Ideal.map
        (algebraMap (MvPolynomial (Fin N) k) (Localization.AtPrime Q)) Q := by
  change RingHom.ker
      (algebraMap (Localization.AtPrime Q) Q.ResidueField) = _
  rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue,
    Localization.AtPrime.map_eq_maximalIdeal]

/-- A finite generating family of a prime ideal gives the corresponding
finite generating family of the generic local kernel. -/
theorem genericPrimeLocalExtension_ker_eq_span_of_span_eq
    {k : Type u} [Field k] {N n : ℕ}
    (Q : Ideal (MvPolynomial (Fin N) k)) [Q.IsPrime]
    (F : Fin n → MvPolynomial (Fin N) k)
    (hF : Ideal.span (Set.range F) = Q) :
    Ideal.span (Set.range fun i ↦
      algebraMap (MvPolynomial (Fin N) k) (Localization.AtPrime Q) (F i)) =
      (genericPrimeLocalExtension Q).ker := by
  rw [genericPrimeLocalExtension_ker]
  calc
    Ideal.span (Set.range fun i ↦
        algebraMap (MvPolynomial (Fin N) k) (Localization.AtPrime Q) (F i)) =
        Ideal.map
          (algebraMap (MvPolynomial (Fin N) k) (Localization.AtPrime Q))
          (Ideal.span (Set.range F)) := by
      rw [Ideal.map_span]
      congr 1
      rw [← Set.range_comp]
      rfl
    _ = Ideal.map
          (algebraMap (MvPolynomial (Fin N) k) (Localization.AtPrime Q)) Q := by
      rw [hF]

/-- The `dX_i` basis after localizing the polynomial ring at an arbitrary
prime. -/
noncomputable def genericPrimePolynomialLocalKaehlerBasis
    {k : Type u} [Field k] {N : ℕ}
    (Q : Ideal (MvPolynomial (Fin N) k)) [Q.IsPrime] :
    Module.Basis (Fin N) (Localization.AtPrime Q)
      Ω[Localization.AtPrime Q⁄k] := by
  let R := MvPolynomial (Fin N) k
  let L := Localization.AtPrime Q
  letI : Algebra.FormallyEtale R L :=
    Algebra.FormallyEtale.of_isLocalization Q.primeCompl
  exact
    ((KaehlerDifferential.mvPolynomialBasis k (Fin N)).baseChange L).map
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R L)

@[simp]
theorem genericPrimePolynomialLocalKaehlerBasis_repr_D_algebraMap
    {k : Type u} [Field k] {N : ℕ}
    (Q : Ideal (MvPolynomial (Fin N) k)) [Q.IsPrime]
    (f : MvPolynomial (Fin N) k) (i : Fin N) :
    (genericPrimePolynomialLocalKaehlerBasis Q).repr
        (KaehlerDifferential.D k (Localization.AtPrime Q)
          (algebraMap (MvPolynomial (Fin N) k)
            (Localization.AtPrime Q) f)) i =
      algebraMap (MvPolynomial (Fin N) k) (Localization.AtPrime Q)
        (MvPolynomial.pderiv i f) := by
  classical
  let R := MvPolynomial (Fin N) k
  let L := Localization.AtPrime Q
  letI : Algebra.FormallyEtale R L :=
    Algebra.FormallyEtale.of_isLocalization Q.primeCompl
  simp only [genericPrimePolynomialLocalKaehlerBasis, Module.Basis.map_repr,
    LinearEquiv.trans_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    Module.Basis.baseChange_repr_tmul,
    KaehlerDifferential.mvPolynomialBasis_repr_apply, Algebra.smul_def,
    mul_one]

/-- Standard residual ambient coordinates for the generic-point local
presentation of a prime affine component. -/
noncomputable def genericPrimeResidualAmbientCoordinates
    {k : Type u} [Field k] {N : ℕ}
    (Q : Ideal (MvPolynomial (Fin N) k)) [Q.IsPrime] :
    let S := Q.ResidueField
    let P := genericPrimeLocalExtension Q
    (ResidueField S ⊗[S] P.CotangentSpace) ≃ₗ[ResidueField S]
      (Fin N → ResidueField S) := by
  let L := Localization.AtPrime Q
  let S := Q.ResidueField
  let P := genericPrimeLocalExtension Q
  let bL := genericPrimePolynomialLocalKaehlerBasis Q
  let bS : Module.Basis (Fin N) S P.CotangentSpace := bL.baseChange S
  let bκ : Module.Basis (Fin N) (ResidueField S)
      (ResidueField S ⊗[S] P.CotangentSpace) :=
    bS.baseChange (ResidueField S)
  exact bκ.repr ≪≫ₗ
    Finsupp.linearEquivFunOnFinite (ResidueField S) (ResidueField S) (Fin N)

/-- A literal equation in the prime ideal, viewed in the kernel of the
generic-point local presentation. -/
noncomputable def genericPrimeLocalKernelElement
    {k : Type u} [Field k] {N : ℕ}
    (Q : Ideal (MvPolynomial (Fin N) k)) [Q.IsPrime]
    (f : MvPolynomial (Fin N) k) (hf : f ∈ Q) :
    (genericPrimeLocalExtension Q).ker := by
  refine ⟨algebraMap (MvPolynomial (Fin N) k)
    (Localization.AtPrime Q) f, ?_⟩
  rw [genericPrimeLocalExtension_ker]
  exact Ideal.mem_map_of_mem _ hf

/-- In the standard residual ambient coordinates, the differential of a
literal prime equation is its ordinary gradient, mapped to the two residue
fields. -/
theorem genericPrimeResidualAmbientCoordinates_apply
    {k : Type u} [Field k] {N : ℕ}
    (Q : Ideal (MvPolynomial (Fin N) k)) [Q.IsPrime]
    (f : MvPolynomial (Fin N) k) (hf : f ∈ Q) (i : Fin N) :
    let S := Q.ResidueField
    let P := genericPrimeLocalExtension Q
    genericPrimeResidualAmbientCoordinates Q
        ((P.cotangentComplex.baseChange (ResidueField S))
          ((1 : ResidueField S) ⊗ₜ[S]
            Algebra.Extension.Cotangent.mk
              (genericPrimeLocalKernelElement Q f hf))) i =
      algebraMap S (ResidueField S)
        (algebraMap (Localization.AtPrime Q) S
          (algebraMap (MvPolynomial (Fin N) k)
            (Localization.AtPrime Q) (MvPolynomial.pderiv i f))) := by
  classical
  let L := Localization.AtPrime Q
  let S := Q.ResidueField
  let P := genericPrimeLocalExtension Q
  simp only [genericPrimeResidualAmbientCoordinates,
    LinearEquiv.trans_apply, Finsupp.linearEquivFunOnFinite_apply,
    LinearMap.baseChange_tmul,
    Algebra.Extension.cotangentComplex_mk,
    Module.Basis.baseChange_repr_tmul,
    Algebra.smul_def, mul_one,
    genericPrimeLocalKernelElement]
  apply congrArg (algebraMap S (ResidueField S))
  change
    ((genericPrimePolynomialLocalKaehlerBasis Q).baseChange S).repr
        ((1 : S) ⊗ₜ[L]
          KaehlerDifferential.D k L
            (algebraMap (MvPolynomial (Fin N) k) L f)) i =
      algebraMap L S
        (algebraMap (MvPolynomial (Fin N) k) L
          (MvPolynomial.pderiv i f))
  rw [Module.Basis.baseChange_repr_tmul]
  simp only [Algebra.smul_def, mul_one]
  rw [genericPrimePolynomialLocalKaehlerBasis_repr_D_algebraMap]

/-- At the generic point of a normalized prime component, an expected-size
subfamily of any displayed finite generating family has a nonzero residual
Jacobian minor and generates the exact local prime ideal. -/
theorem exists_genericPrime_selected_generators_and_residual_minor
    {k : Type u} [Field k] [CharZero k] {N n s : ℕ}
    (Q : Ideal (MvPolynomial (Fin N) k)) [Q.IsPrime]
    (F : Fin n → MvPolynomial (Fin N) k)
    (hF : Ideal.span (Set.range F) = Q)
    (normalization : MvPolynomial (Fin s) k →ₐ[k]
      (MvPolynomial (Fin N) k ⧸ Q))
    (hnormalization : Function.Injective normalization)
    (hfinite : normalization.Finite) :
    ∃ rows : Fin (N - s) → Fin n,
      ∃ cols : Fin (N - s) → Fin N,
        Function.Injective rows ∧ Function.Injective cols ∧
          Matrix.det (Matrix.of (fun i j ↦
            genericPrimeResidualAmbientCoordinates Q
              ((((genericPrimeLocalExtension Q).cotangentComplex.baseChange
                (ResidueField Q.ResidueField)))
                ((1 : ResidueField Q.ResidueField) ⊗ₜ[Q.ResidueField]
                  Algebra.Extension.Cotangent.mk
                    (genericPrimeLocalKernelElement Q (F (rows i))
                      (hF.le (Ideal.subset_span ⟨rows i, rfl⟩)))))
              (cols j))) ≠ 0 ∧
          Ideal.span (Set.range fun i ↦
            algebraMap (MvPolynomial (Fin N) k) (Localization.AtPrime Q)
              (F (rows i))) =
            Ideal.map
              (algebraMap (MvPolynomial (Fin N) k)
                (Localization.AtPrime Q)) Q := by
  classical
  let R := MvPolynomial (Fin N) k
  let A := R ⧸ Q
  let L := Localization.AtPrime Q
  let S := Q.ResidueField
  let P := genericPrimeLocalExtension Q
  letI : IsScalarTower k A S :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := A) (A := S)
      (fun x ↦ by rfl)
  let Flocal : Fin n → L := fun i ↦ algebraMap R L (F i)
  have hFlocal : Ideal.span (Set.range Flocal) = P.ker := by
    simpa only [R, L, P, Flocal] using
      genericPrimeLocalExtension_ker_eq_span_of_span_eq Q F hF
  have hker : P.ker.FG := by
    rw [← hFlocal]
    exact Submodule.fg_span (Set.finite_range Flocal)
  have hambient : Module.finrank (ResidueField S)
      (ResidueField S ⊗[S] P.CotangentSpace) = N := by
    simpa only [S, P, Module.finrank_pi, Fintype.card_fin] using
      (genericPrimeResidualAmbientCoordinates Q).finrank_eq
  have htarget0 : Module.finrank S Ω[S⁄k] = s := by
    exact finrank_isFractionRing_kaehler_eq_normalizationParameters
      normalization hnormalization hfinite
  have htarget : Module.finrank (ResidueField S)
      (ResidueField S ⊗[S] Ω[S⁄k]) = s := by
    rw [Module.finrank_baseChange]
    exact htarget0
  letI : IsLocalRing P.Ring := by
    change IsLocalRing L
    infer_instance
  letI : Algebra.FormallySmooth k P.Ring := by
    letI : Algebra.FormallySmooth R L :=
      Algebra.FormallySmooth.of_isLocalization Q.primeCompl
    change Algebra.FormallySmooth k L
    exact Algebra.FormallySmooth.comp k R L
  letI : Module.Free P.Ring Ω[P.Ring⁄k] := by
    change Module.Free L Ω[L⁄k]
    exact Module.Free.of_basis (genericPrimePolynomialLocalKaehlerBasis Q)
  letI : Module.Finite P.Ring Ω[P.Ring⁄k] := by
    change Module.Finite L Ω[L⁄k]
    exact Module.Finite.of_basis (genericPrimePolynomialLocalKaehlerBasis Q)
  letI : Algebra.FormallySmooth k S := by
    exact formallySmooth_isFractionRing_of_finite_normalization
      normalization hnormalization hfinite
  obtain ⟨rows, cols, hrows, hcols, hminor, hgenerate⟩ :=
    exists_selected_localKernel_generators_and_minor
      P hker hambient htarget Flocal hFlocal
        (genericPrimeResidualAmbientCoordinates Q)
  refine ⟨rows, cols, hrows, hcols, ?_, ?_⟩
  · simpa only [P, S, Flocal, genericPrimeLocalKernelElement] using hminor
  · rw [← genericPrimeLocalExtension_ker Q]
    simpa only [P, Flocal] using hgenerate

/-- Literal polynomial form of generic conormal selection.  The ordinary
selected Jacobian determinant avoids the prime, while the same selected
equations generate the prime after localization at its generic point. -/
theorem exists_genericPrime_selected_generators_and_literal_minor
    {k : Type u} [Field k] [CharZero k] {N n s : ℕ}
    (Q : Ideal (MvPolynomial (Fin N) k)) [Q.IsPrime]
    (F : Fin n → MvPolynomial (Fin N) k)
    (hF : Ideal.span (Set.range F) = Q)
    (normalization : MvPolynomial (Fin s) k →ₐ[k]
      (MvPolynomial (Fin N) k ⧸ Q))
    (hnormalization : Function.Injective normalization)
    (hfinite : normalization.Finite) :
    ∃ rows : Fin (N - s) → Fin n,
      ∃ cols : Fin (N - s) → Fin N,
        Function.Injective rows ∧ Function.Injective cols ∧
          selectedJacobianDeterminant (fun i ↦ F (rows i)) cols ∉ Q ∧
          Ideal.span (Set.range fun i ↦
            algebraMap (MvPolynomial (Fin N) k) (Localization.AtPrime Q)
              (F (rows i))) =
            Ideal.map
              (algebraMap (MvPolynomial (Fin N) k)
                (Localization.AtPrime Q)) Q := by
  classical
  obtain ⟨rows, cols, hrows, hcols, hminor, hgenerate⟩ :=
    exists_genericPrime_selected_generators_and_residual_minor
      Q F hF normalization hnormalization hfinite
  let R := MvPolynomial (Fin N) k
  let L := Localization.AtPrime Q
  let S := Q.ResidueField
  let κ := ResidueField S
  let P := genericPrimeLocalExtension Q
  let M : Matrix (Fin (N - s)) (Fin (N - s)) κ :=
    Matrix.of (fun i j ↦
      genericPrimeResidualAmbientCoordinates Q
        (((P.cotangentComplex.baseChange κ)
          ((1 : κ) ⊗ₜ[S]
            Algebra.Extension.Cotangent.mk
              (genericPrimeLocalKernelElement Q (F (rows i))
                (hF.le (Ideal.subset_span ⟨rows i, rfl⟩))))))
        (cols j))
  let B : Matrix (Fin (N - s)) (Fin (N - s)) κ :=
    Matrix.of (fun i j ↦
      algebraMap R κ (MvPolynomial.pderiv (cols j) (F (rows i))))
  let C : Matrix (Fin (N - s)) (Fin (N - s)) κ :=
    Matrix.of (fun i j ↦
      algebraMap R κ (MvPolynomial.pderiv (cols i) (F (rows j))))
  have hM : M.det ≠ 0 := by
    simpa only [M, P, S, κ] using hminor
  have hMB : M = B := by
    ext i j
    rw [show M i j =
        genericPrimeResidualAmbientCoordinates Q
          (((P.cotangentComplex.baseChange κ)
            ((1 : κ) ⊗ₜ[S]
              Algebra.Extension.Cotangent.mk
                (genericPrimeLocalKernelElement Q (F (rows i))
                  (hF.le (Ideal.subset_span ⟨rows i, rfl⟩))))))
          (cols j) from rfl,
      genericPrimeResidualAmbientCoordinates_apply]
    change algebraMap S κ
        (algebraMap L S
          (algebraMap R L
            (MvPolynomial.pderiv (cols j) (F (rows i))))) = _
    rw [← IsScalarTower.algebraMap_apply R L S,
      ← IsScalarTower.algebraMap_apply R S κ]
    rfl
  have hB : B.det ≠ 0 := by
    rw [← hMB]
    exact hM
  have hBC : B = C.transpose := by
    ext i j
    rfl
  have hC : C.det ≠ 0 := by
    rw [← Matrix.det_transpose C, ← hBC]
    exact hB
  refine ⟨rows, cols, hrows, hcols, ?_, hgenerate⟩
  intro hdetQ
  have hzeroS : algebraMap R S
      (selectedJacobianDeterminant (fun i ↦ F (rows i)) cols) = 0 := by
    exact Ideal.algebraMap_residueField_eq_zero.mpr hdetQ
  have hzeroκ : algebraMap R κ
      (selectedJacobianDeterminant (fun i ↦ F (rows i)) cols) = 0 := by
    rw [IsScalarTower.algebraMap_apply R S κ, hzeroS, map_zero]
  apply hC
  rw [selectedJacobianDeterminant,
    (algebraMap R κ).map_det] at hzeroκ
  simpa only [C, RingHom.mapMatrix_apply, Matrix.of_apply] using hzeroκ

/-- A single affine principal open on the component supports both the
selected nonzero Jacobian minor and exact ideal generation.  The divisibility
condition says literally that the selected determinant is inverted on this
open. -/
theorem exists_genericPrime_principalOpen_selectedJacobianChart
    {k : Type u} [Field k] [CharZero k] {N n s : ℕ}
    (Q : Ideal (MvPolynomial (Fin N) k)) [Q.IsPrime]
    (F : Fin n → MvPolynomial (Fin N) k)
    (hF : Ideal.span (Set.range F) = Q)
    (normalization : MvPolynomial (Fin s) k →ₐ[k]
      (MvPolynomial (Fin N) k ⧸ Q))
    (hnormalization : Function.Injective normalization)
    (hfinite : normalization.Finite) :
    ∃ rows : Fin (N - s) → Fin n,
      ∃ cols : Fin (N - s) → Fin N,
        ∃ u : MvPolynomial (Fin N) k,
          Function.Injective rows ∧ Function.Injective cols ∧
          u ∉ Q ∧
          selectedJacobianDeterminant (fun i ↦ F (rows i)) cols ∣ u ∧
          (∀ x ∈ Q, u * x ∈
            Ideal.span (Set.range fun i ↦ F (rows i))) ∧
          Ideal.map
              (algebraMap (MvPolynomial (Fin N) k) (Localization.Away u))
              (Ideal.span (Set.range fun i ↦ F (rows i))) =
            Ideal.map
              (algebraMap (MvPolynomial (Fin N) k) (Localization.Away u)) Q := by
  classical
  let R := MvPolynomial (Fin N) k
  obtain ⟨rows, cols, hrows, hcols, hdet, hlocal⟩ :=
    exists_genericPrime_selected_generators_and_literal_minor
      Q F hF normalization hnormalization hfinite
  let I : Ideal R := Ideal.span (Set.range fun i ↦ F (rows i))
  let D : R := selectedJacobianDeterminant (fun i ↦ F (rows i)) cols
  have hIQ : I ≤ Q := by
    rw [Ideal.span_le]
    rintro x ⟨i, rfl⟩
    exact hF.le (Ideal.subset_span ⟨rows i, rfl⟩)
  have hQfg : Q.FG := IsNoetherian.noetherian Q
  have hlocal' :
      Ideal.map (algebraMap R (Localization.AtPrime Q)) I =
        Ideal.map (algebraMap R (Localization.AtPrime Q)) Q := by
    calc
      Ideal.map (algebraMap R (Localization.AtPrime Q)) I =
          Ideal.span (Set.range fun i ↦
            algebraMap R (Localization.AtPrime Q) (F (rows i))) := by
        rw [show I = Ideal.span (Set.range fun i ↦ F (rows i)) from rfl,
          Ideal.map_span]
        congr 1
        rw [← Set.range_comp]
        rfl
      _ = Ideal.map (algebraMap R (Localization.AtPrime Q)) Q := by
        simpa only [R] using hlocal
  obtain ⟨h, hhQ, hclear, _haway⟩ :=
    exists_notMem_mul_mem_and_map_away_eq_of_map_atPrime_eq
      I Q Q hIQ hQfg hlocal'
  let u : R := D * h
  have huQ : u ∉ Q := by
    exact (inferInstance : Q.IsPrime).mul_notMem hdet hhQ
  have hDdvd : D ∣ u := ⟨h, rfl⟩
  have huclear : ∀ x ∈ Q, u * x ∈ I := by
    intro x hx
    change (D * h) * x ∈ I
    rw [mul_assoc]
    exact I.mul_mem_left D (hclear x hx)
  have huaway :
      Ideal.map (algebraMap R (Localization.Away u)) I =
        Ideal.map (algebraMap R (Localization.Away u)) Q :=
    map_away_eq_of_mul_mem I Q u hIQ huclear
  exact ⟨rows, cols, u, hrows, hcols, huQ, hDdvd, huclear, huaway⟩

/-- Clearing the finitely many coefficients of one fraction-field
polynomial can be expressed by a single nonzero scalar from the base
domain. -/
theorem exists_nonzero_base_multiple_mvPolynomial
    {B : Type u} {K : Type*} {σ : Type*}
    [CommRing B] [IsDomain B] [Field K] [Algebra B K]
    [IsFractionRing B K]
    (f : MvPolynomial σ K) :
    ∃ d : B, d ≠ 0 ∧ ∃ f₀ : MvPolynomial σ B,
      MvPolynomial.map (algebraMap B K) f₀ =
        MvPolynomial.C (algebraMap B K d) * f := by
  let R := MvPolynomial σ B
  let RK := MvPolynomial σ K
  let M : Submonoid R :=
    (nonZeroDivisors B).map (MvPolynomial.C (σ := σ))
  letI : Algebra R RK := MvPolynomial.algebraMvPolynomial
  obtain ⟨⟨f₀, m⟩, hm⟩ := IsLocalization.surj M f
  obtain ⟨d, hd, hdm⟩ := Submonoid.mem_map.mp m.property
  refine ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp hd, f₀, ?_⟩
  have hm' : f * algebraMap R RK (MvPolynomial.C d) =
      algebraMap R RK f₀ := by
    rw [← hdm] at hm
    exact hm
  have halgebraMap : algebraMap R RK =
      MvPolynomial.map (algebraMap B K) := by
    rfl
  have hm'' : f * MvPolynomial.C (algebraMap B K d) =
      MvPolynomial.map (algebraMap B K) f₀ := by
    rw [halgebraMap, MvPolynomial.map_C] at hm'
    exact hm'
  simpa only [mul_comm] using hm''.symm

/-- Relative generic-component chart over an integral parameter stratum.
The rows and columns are selected from the displayed base-ring family.  One
nonzero element of the parameter ring clears every generic ideal identity;
on the resulting affine principal open the selected equations and the
contracted generic component ideal are literally equal. -/
theorem exists_baseOpen_genericPrime_selectedJacobianChart
    {B : Type u} {K : Type*}
    [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Field K] [CharZero K] [Algebra B K] [IsFractionRing B K]
    {N n s : ℕ}
    (Q : Ideal (MvPolynomial (Fin N) K)) [Q.IsPrime]
    (F : Fin n → MvPolynomial (Fin N) B)
    (hF : Ideal.span (Set.range fun i ↦
      MvPolynomial.map (algebraMap B K) (F i)) = Q)
    (normalization : MvPolynomial (Fin s) K →ₐ[K]
      (MvPolynomial (Fin N) K ⧸ Q))
    (hnormalization : Function.Injective normalization)
    (hfinite : normalization.Finite) :
    let J := Q.comap (MvPolynomial.map (algebraMap B K))
    ∃ rows : Fin (N - s) → Fin n,
      ∃ cols : Fin (N - s) → Fin N,
        ∃ chart : MvPolynomial (Fin N) B,
          ∃ denominator : B,
            Function.Injective rows ∧ Function.Injective cols ∧
            denominator ≠ 0 ∧ chart ∉ J ∧
            selectedJacobianDeterminant (fun i ↦ F (rows i)) cols ∉ J ∧
            selectedJacobianDeterminant (fun i ↦ F (rows i)) cols ∣ chart ∧
            (∀ x ∈ J,
              MvPolynomial.C denominator * chart * x ∈
                Ideal.span (Set.range fun i ↦ F (rows i))) ∧
            Ideal.map
                (algebraMap (MvPolynomial (Fin N) B)
                  (Localization.Away
                    (MvPolynomial.C denominator * chart)))
                (Ideal.span (Set.range fun i ↦ F (rows i))) =
              Ideal.map
                (algebraMap (MvPolynomial (Fin N) B)
                  (Localization.Away
                    (MvPolynomial.C denominator * chart))) J := by
  classical
  let R := MvPolynomial (Fin N) B
  let RK := MvPolynomial (Fin N) K
  let φ : R →+* RK := MvPolynomial.map (algebraMap B K)
  let FK : Fin n → RK := fun i ↦ φ (F i)
  let J : Ideal R := Q.comap φ
  obtain ⟨rows, cols, uK, hrows, hcols, huQ, hDdvd,
      huClear, _huAway⟩ :=
    exists_genericPrime_principalOpen_selectedJacobianChart
      Q FK (by simpa only [FK, φ, RK] using hF)
        normalization hnormalization hfinite
  let DB : R := selectedJacobianDeterminant (fun i ↦ F (rows i)) cols
  let DK : RK := selectedJacobianDeterminant (fun i ↦ FK (rows i)) cols
  have hmapD : φ DB = DK := by
    simpa only [φ, DB, DK, FK] using
      map_selectedJacobianDeterminant (algebraMap B K)
        (fun i ↦ F (rows i)) cols
  obtain ⟨hK, huK⟩ := hDdvd
  have hDKQ : DK ∉ Q := by
    intro hDK
    apply huQ
    rw [huK]
    exact Q.mul_mem_right hK hDK
  obtain ⟨d, hd, hB, hmaphB⟩ :=
    exists_nonzero_base_multiple_mvPolynomial (B := B) (K := K) hK
  let chart : R := DB * hB
  have hmapChart : φ chart = MvPolynomial.C (algebraMap B K d) * uK := by
    rw [show φ chart = φ DB * φ hB by simp only [chart, map_mul],
      hmapD]
    have hmaphB' : φ hB = MvPolynomial.C (algebraMap B K d) * hK := by
      simpa only [φ] using hmaphB
    rw [hmaphB', huK]
    ring
  have hconstant_ne : algebraMap B K d ≠ 0 :=
    fractionRing_algebraMap_ne_zero hd
  have hconstantUnit : IsUnit
      (MvPolynomial.C (algebraMap B K d) : RK) :=
    (isUnit_iff_ne_zero.mpr hconstant_ne).map MvPolynomial.C
  have hchartJ : chart ∉ J := by
    intro hchart
    have hmapChartQ : φ chart ∈ Q := hchart
    rw [hmapChart] at hmapChartQ
    exact huQ ((Q.unit_mul_mem_iff_mem hconstantUnit).mp hmapChartQ)
  have hDBJ : DB ∉ J := by
    intro hDB
    exact hDKQ (hmapD ▸ hDB)
  have hDBdvd : DB ∣ chart := ⟨hB, rfl⟩
  let I : Ideal R := Ideal.span (Set.range fun i ↦ F (rows i))
  have hIJ : I ≤ J := by
    rw [Ideal.span_le]
    rintro x ⟨i, rfl⟩
    change φ (F (rows i)) ∈ Q
    exact hF.le (Ideal.subset_span ⟨rows i, rfl⟩)
  have hmapI : Ideal.map φ I =
      Ideal.span (Set.range fun i ↦ FK (rows i)) := by
    rw [show I = Ideal.span (Set.range fun i ↦ F (rows i)) from rfl,
      Ideal.map_span]
    congr 1
    rw [← Set.range_comp]
    rfl
  have hgeneric : ∀ x ∈ J,
      φ chart * φ x ∈ Ideal.map φ I := by
    intro x hx
    rw [hmapI, hmapChart, mul_assoc]
    exact (Ideal.span (Set.range fun i ↦ FK (rows i))).mul_mem_left
      (MvPolynomial.C (algebraMap B K d)) (huClear (φ x) hx)
  obtain ⟨denominator, hdenominator, hclear, haway⟩ :=
    exists_nonzero_base_clearing_for_generic_chart I J chart hIJ hgeneric
  exact ⟨rows, cols, chart, denominator, hrows, hcols, hdenominator,
    hchartJ, hDBJ, hDBdvd, hclear, haway⟩

end

end TranslatedDepthSeven

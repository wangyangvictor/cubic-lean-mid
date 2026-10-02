import TranslatedDepthSeven.CotangentKrullLowerBound
import Mathlib.RingTheory.Smooth.Local

/-!
# Differential fibres at rational points

At a local `k`-algebra whose residue field is identified with `k`, formal
smoothness identifies the residual Kaehler differential fibre with the
Zariski cotangent space.  Combining this with Krull's height theorem gives
the lower bound from Krull dimension to differential-fibre dimension.

This file does not assert the converse inequality.  In particular, it does
not smuggle in the absent general theorem that a smooth local algebra over a
field is regular of dimension equal to its cotangent dimension.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct
open KaehlerDifferential IsLocalRing

universe u v

private noncomputable def idealCotangentLinearEquivOfEq
    {R : Type u} [CommRing R] {I J : Ideal R} (h : I = J) :
    I.Cotangent ≃ₗ[R] J.Cotangent := by
  subst J
  exact LinearEquiv.refl R _

/-- At a formally smooth rational point, the residual module of Kaehler
differentials and the Zariski cotangent space have the same dimension.

The algebra equivalence is the precise rational-residue hypothesis. -/
theorem finrank_residueTensor_kaehler_eq_finrank_cotangentSpace_of_rationalResidue
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    [IsLocalRing S] [Algebra.FormallySmooth k S]
    (e : ResidueField S ≃ₐ[k] k) :
    Module.finrank (ResidueField S) (ResidueField S ⊗[S] Ω[S⁄k]) =
      Module.finrank (ResidueField S) (CotangentSpace S) := by
  let f : S →ₐ[k] ResidueField S := IsScalarTower.toAlgHom k S (ResidueField S)
  let P : Algebra.Extension.{v} k (ResidueField S) :=
    Algebra.Extension.ofSurjective f IsLocalRing.residue_surjective
  have hf : (f : S →+* ResidueField S) = IsLocalRing.residue S := by
    rfl
  have hker : P.ker = maximalIdeal S := by
    change RingHom.ker (f : S →+* ResidueField S) = maximalIdeal S
    rw [hf]
    exact IsLocalRing.ker_residue
  haveI : Algebra.FormallySmooth k (ResidueField S) :=
    Algebra.FormallySmooth.of_equiv e.symm
  haveI : Algebra.FormallyUnramified k (ResidueField S) :=
    Algebra.FormallyUnramified.of_equiv e.symm
  letI : Algebra.FormallySmooth k P.Ring :=
    show Algebra.FormallySmooth k S from inferInstance
  have hinj : Function.Injective P.cotangentComplex := by
    rw [P.cotangentComplex_injective_iff]
    infer_instance
  have hsurj : Function.Surjective P.cotangentComplex := by
    intro y
    exact (P.exact_cotangentComplex_toKaehler y).mp (Subsingleton.elim _ _)
  let E : P.Cotangent ≃ₗ[ResidueField S] P.CotangentSpace :=
    LinearEquiv.ofBijective P.cotangentComplex ⟨hinj, hsurj⟩
  letI : Module S P.ker.Cotangent := by
    change Module S (RingHom.ker (f : S →+* ResidueField S)).Cotangent
    infer_instance
  let eIdeal : P.ker.Cotangent ≃ₗ[S] CotangentSpace S :=
    idealCotangentLinearEquivOfEq hker
  let eCot : P.Cotangent ≃ₗ[ResidueField S] CotangentSpace S := {
    toFun := fun x ↦ eIdeal x.val
    invFun := fun x ↦ Algebra.Extension.Cotangent.of (eIdeal.symm x)
    left_inv := by
      intro x
      apply Algebra.Extension.Cotangent.ext
      simp
    right_inv := by
      intro x
      simp
    map_add' := by
      intro x y
      simp
    map_smul' := by
      intro r x
      obtain ⟨a, rfl⟩ :=
        (IsLocalRing.residue_surjective : Function.Surjective (residue S)) r
      change eIdeal ((algebraMap S (ResidueField S) a • x).val) =
        algebraMap S (ResidueField S) a • eIdeal x.val
      rw [IsScalarTower.algebraMap_smul (ResidueField S) a x,
        Algebra.Extension.Cotangent.val_smul', eIdeal.map_smul,
        IsScalarTower.algebraMap_smul (ResidueField S) a (eIdeal x.val)]
  }
  change Module.finrank (ResidueField S) P.CotangentSpace = _
  rw [← E.finrank_eq]
  exact eCot.finrank_eq

/-- At a rational point of a Noetherian formally smooth local algebra, the
Krull dimension is at most the dimension of the residual differential fibre.
This is the direction supplied by Krull's height theorem. -/
theorem ringKrullDim_le_finrank_residueTensor_kaehler_of_rationalResidue
    {k : Type u} (S : Type v) [Field k] [CommRing S] [Algebra k S]
    [IsLocalRing S] [IsNoetherianRing S] [Algebra.FormallySmooth k S]
    (e : ResidueField S ≃ₐ[k] k) :
    ringKrullDim S ≤
      (Module.finrank (ResidueField S)
        (ResidueField S ⊗[S] Ω[S⁄k]) : WithBot ℕ∞) := by
  rw [finrank_residueTensor_kaehler_eq_finrank_cotangentSpace_of_rationalResidue e]
  exact ringKrullDim_le_finrank_cotangentSpace S

/-- The exact smooth-local dimension conclusion once an upper bound for the
residual differential dimension is supplied.  At a rational point, the
opposite inequality is already `ringKrullDim_le_finrank_residueTensor_kaehler_of_rationalResidue`.

In the polynomial application, a full selected Jacobian minor can supply
`hupper`; thus one need not invoke a general regular-local-ring theorem. -/
theorem finrank_residueTensor_kaehler_eq_krullDim_of_rationalResidue_of_le
    {k : Type u} (S : Type v) [Field k] [CommRing S] [Algebra k S]
    [IsLocalRing S] [IsNoetherianRing S] [Algebra.FormallySmooth k S]
    (e : ResidueField S ≃ₐ[k] k) {s : ℕ}
    (hdim : ringKrullDim S = s)
    (hupper : Module.finrank (ResidueField S)
      (ResidueField S ⊗[S] Ω[S⁄k]) ≤ s) :
    Module.finrank (ResidueField S)
      (ResidueField S ⊗[S] Ω[S⁄k]) = s := by
  apply le_antisymm hupper
  have hlower :=
    ringKrullDim_le_finrank_residueTensor_kaehler_of_rationalResidue S e
  rw [hdim] at hlower
  exact_mod_cast hlower

end

end TranslatedDepthSeven

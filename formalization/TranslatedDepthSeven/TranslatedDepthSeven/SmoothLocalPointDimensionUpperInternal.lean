import TranslatedDepthSeven.ArbitraryLocalizationAugmentedJetsInternal
import TranslatedDepthSeven.SmoothLocalDimensionBridge

/-!
# The dimension upper bound on a localization of a standard-smooth algebra

Only finite jets are transported.  In particular, no finite-presentation
claim is made for a localization at an arbitrary prime ideal.
-/

namespace TranslatedDepthSeven

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

theorem localRationalPoint_ker_spanFinrank_eq_finrank_cotangent
    {K T : Type*} [Field K] [CommRing T] [Algebra K T]
    [IsLocalRing T] [IsNoetherianRing T] (x : T →ₐ[K] K) :
    (RingHom.ker x.toRingHom).spanFinrank =
      Module.finrank K (RingHom.ker x.toRingHom).Cotangent := by
  have hx : Function.Surjective x := fun a ↦ ⟨algebraMap K T a, by simp⟩
  let P : Algebra.Extension K K := Algebra.Extension.ofSurjective x hx
  letI : IsLocalRing P.Ring := show IsLocalRing T from inferInstance
  letI : IsNoetherianRing P.Ring := show IsNoetherianRing T from inferInstance
  let E : P.Cotangent ≃ₗ[K] P.ker.Cotangent := {
    toFun := Algebra.Extension.Cotangent.val
    invFun := Algebra.Extension.Cotangent.of
    left_inv y := Algebra.Extension.Cotangent.of_val y
    right_inv y := Algebra.Extension.Cotangent.val_of y
    map_add' _ _ := Algebra.Extension.Cotangent.val_add _ _
    map_smul' c y := Algebra.Extension.Cotangent.val_smul'' c y
  }
  exact (extension_ker_spanFinrank_eq_finrank_cotangent P).trans E.finrank_eq

theorem ringKrullDim_localization_le_of_standardSmooth_rationalPoint
    {K A T : Type*} [Field K] [CommRing A] [CommRing T]
    [Algebra K A] [Algebra A T] [Algebra K T] [IsScalarTower K A T]
    [IsLocalRing T] [IsNoetherianRing T]
    (S : Submonoid A) [IsLocalization S T]
    (x : T →ₐ[K] K) (r : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A] :
    ringKrullDim T ≤ (r : WithBot ℕ∞) := by
  have hx : Function.Surjective x := fun a ↦ ⟨algebraMap K T a, by simp⟩
  letI : Nontrivial T := hx.nontrivial
  let f := x.comp (IsScalarTower.toAlgHom K A T)
  let M := RingHom.ker x.toRingHom
  let E := arbitraryLocalizationAugmentedJetAlgEquiv S x 1
  letI : Module.Finite K (augmentedJet f 1) :=
    augmentedJet_moduleFinite_of_isStandardSmoothOfRelativeDimension f r 1
  letI : Module.Finite K (T ⧸ M ^ 2) :=
    Module.Finite.equiv E.toLinearEquiv
  let inclusion : M.Cotangent →ₗ[K] T ⧸ M ^ 2 :=
    M.cotangentToQuotientSquare.restrictScalars K
  have hinclusion : Function.Injective inclusion := by
    intro a b hab
    apply M.cotangentEquivIdeal.injective
    exact Subtype.ext hab
  letI : Module.Finite K M.Cotangent := Module.Finite.of_injective inclusion hinclusion
  have hjet : Module.finrank K (T ⧸ M ^ 2) = r + 1 := by
    calc
      _ = Module.finrank K (augmentedJet f 1) := E.toLinearEquiv.finrank_eq.symm
      _ = r + 1 := finrank_firstJet_eq_add_one_of_isStandardSmoothOfRelativeDimension f r
  have hcotr : Module.finrank K M.Cotangent = r := by
    have h := finrank_firstJet_eq_cotangent_add_one x
    change Module.finrank K (T ⧸ M ^ 2) = Module.finrank K M.Cotangent + 1 at h
    omega
  have hM : M = IsLocalRing.maximalIdeal T :=
    IsLocalRing.ker_eq_maximalIdeal x.toRingHom hx
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← hM]
  have hspan : M.spanFinrank = r :=
    (localRationalPoint_ker_spanFinrank_eq_finrank_cotangent x).trans hcotr
  rw [← hspan]
  exact WithBot.coe_le_coe.mpr (Ideal.height_le_spanFinrank M
    (RingHom.ker_isMaximal_of_surjective x.toRingHom hx).ne_top)

end

end TranslatedDepthSeven

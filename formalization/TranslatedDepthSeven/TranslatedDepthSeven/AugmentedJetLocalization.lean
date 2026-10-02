import TranslatedDepthSeven.StandardSmoothHigherJets
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Finite jets are unchanged on a principal neighbourhood of their point

If a rational point of `A` extends to `A[1/s]`, then `s` is a unit modulo
every power of the point ideal.  The universal property of localization
therefore identifies the finite jets before and after localization.  This
file constructs the two algebra maps and proves that they are inverse.
-/

namespace TranslatedDepthSeven

noncomputable section

universe u v w

variable {K : Type u} [Field K]
variable {A : Type v} {T : Type w}
variable [CommRing A] [CommRing T]
variable [Algebra K A] [Algebra A T] [Algebra K T]
variable [IsScalarTower K A T]

/-- An element which is nonzero under the augmentation becomes a unit in
every finite jet. -/
theorem isUnit_mk_augmentedJet_of_ne_zero
    (f : A →ₐ[K] K) (k : ℕ) (s : A) (hs : f s ≠ 0) :
    IsUnit (Ideal.Quotient.mk (RingHom.ker f.toRingHom ^ (k + 1)) s) := by
  let B := augmentedJet f k
  let q : A →ₐ[K] B :=
    Ideal.Quotient.mkₐ K (RingHom.ker f.toRingHom ^ (k + 1))
  let eB := augmentedJetEvaluation f k
  let n : B := q s - algebraMap K B (f s)
  have hnmem : n ∈ RingHom.ker eB.toRingHom := by
    change eB (q s - algebraMap K B (f s)) = 0
    rw [map_sub]
    rw [show eB (q s) = f s by rfl, eB.commutes]
    simp
  have hnil : IsNilpotent n := by
    refine ⟨k + 1, ?_⟩
    have hnPow : n ^ (k + 1) ∈
        RingHom.ker eB.toRingHom ^ (k + 1) :=
      Ideal.pow_mem_pow hnmem (k + 1)
    rw [pow_ker_augmentedJetEvaluation_eq_bot] at hnPow
    exact hnPow
  have hu : IsUnit (algebraMap K B (f s)) :=
    (isUnit_iff_ne_zero.mpr hs).map (algebraMap K B)
  have hsum : IsUnit (n + algebraMap K B (f s)) :=
    hnil.isUnit_add_right_of_commute hu (Commute.all _ _)
  change IsUnit (q s)
  simpa only [n, sub_add_cancel] using hsum

variable (s : A) [IsLocalization.Away s T]

omit [Algebra K A] [IsScalarTower K A T] in
private theorem localized_point_value_isUnit (x : T →ₐ[K] K) :
    IsUnit (x (algebraMap A T s)) :=
  (IsLocalization.Away.algebraMap_isUnit s).map x

/-- The rational point on a localization, restricted to the original
algebra. -/
abbrev localizationRestrictedPoint (x : T →ₐ[K] K) : A →ₐ[K] K :=
  x.comp (IsScalarTower.toAlgHom K A T)

/-- The quotient map from `A` to its finite jet sends the localization
element to a unit. -/
theorem isUnit_mk_localizationRestrictedPoint_jet
    (x : T →ₐ[K] K) (k : ℕ) :
    IsUnit (Ideal.Quotient.mk
      (RingHom.ker (localizationRestrictedPoint (A := A) x).toRingHom ^ (k + 1)) s) := by
  apply isUnit_mk_augmentedJet_of_ne_zero
  exact (localized_point_value_isUnit s x).ne_zero

/-- The localization maps back to every finite jet of the restricted
point, because the localization element is already a unit there. -/
noncomputable def localizationToAugmentedJet
    (x : T →ₐ[K] K) (k : ℕ) :
    T →ₐ[K] augmentedJet (localizationRestrictedPoint (A := A) x) k := by
  let q : A →ₐ[K] augmentedJet (localizationRestrictedPoint (A := A) x) k :=
    Ideal.Quotient.mkₐ K
      (RingHom.ker (localizationRestrictedPoint (A := A) x).toRingHom ^ (k + 1))
  have hmapUnits : ∀ y : Submonoid.powers s, IsUnit (q y) := by
    rintro ⟨y, n, rfl⟩
    change IsUnit (q (s ^ n))
    rw [map_pow]
    exact (isUnit_mk_localizationRestrictedPoint_jet s x k).pow n
  exact IsLocalization.liftAlgHom hmapUnits

/-- On `A`, the preceding localization lift is the original quotient map.
-/
theorem localizationToAugmentedJet_comp_algebraMap
    (x : T →ₐ[K] K) (k : ℕ) :
    (localizationToAugmentedJet s x k).comp
        (IsScalarTower.toAlgHom K A T) =
      Ideal.Quotient.mkₐ K
        (RingHom.ker (localizationRestrictedPoint (A := A) x).toRingHom ^ (k + 1)) := by
  apply AlgHom.ext
  intro a
  change localizationToAugmentedJet s x k (algebraMap A T a) =
    Ideal.Quotient.mk _ a
  unfold localizationToAugmentedJet
  rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

/-- The localization lift respects the two rational-point evaluations. -/
theorem comp_localizationToAugmentedJet_evaluation
    (x : T →ₐ[K] K) (k : ℕ) :
    (augmentedJetEvaluation (localizationRestrictedPoint (A := A) x) k).comp
        (localizationToAugmentedJet s x k) = x := by
  apply IsLocalization.algHom_ext (Submonoid.powers s)
  rw [AlgHom.comp_assoc]
  change (augmentedJetEvaluation (localizationRestrictedPoint (A := A) x) k).comp
      ((localizationToAugmentedJet s x k).comp
        (IsScalarTower.toAlgHom K A T)) =
    x.comp (IsScalarTower.toAlgHom K A T)
  rw [localizationToAugmentedJet_comp_algebraMap s x k]
  apply AlgHom.ext
  intro a
  change augmentedJetEvaluation (localizationRestrictedPoint (A := A) x) k
      (Ideal.Quotient.mk _ a) = x (algebraMap A T a)
  exact augmentedJetEvaluation_mk _ _ _

/-- The localization lift kills the required power of the localized point
ideal. -/
theorem localizationToAugmentedJet_pow_eq_zero
    (x : T →ₐ[K] K) (k : ℕ) (y : T)
    (hy : y ∈ RingHom.ker x.toRingHom ^ (k + 1)) :
    localizationToAugmentedJet s x k y = 0 := by
  let eA := augmentedJetEvaluation (localizationRestrictedPoint (A := A) x) k
  have hI : RingHom.ker x.toRingHom ≤
      (RingHom.ker eA.toRingHom).comap
        (localizationToAugmentedJet s x k) := by
    intro z hz
    change eA (localizationToAugmentedJet s x k z) = 0
    rw [← AlgHom.comp_apply, comp_localizationToAugmentedJet_evaluation]
    exact hz
  have hy' : localizationToAugmentedJet s x k y ∈
      RingHom.ker eA.toRingHom ^ (k + 1) :=
    ((Ideal.pow_right_mono hI (k + 1)).trans
      (Ideal.le_comap_pow (localizationToAugmentedJet s x k) (k + 1))) hy
  rw [pow_ker_augmentedJetEvaluation_eq_bot] at hy'
  exact hy'

/-- The inverse map from the localized jet to the original jet. -/
noncomputable def localizationAugmentedJetSection
    (x : T →ₐ[K] K) (k : ℕ) :
    augmentedJet x k →ₐ[K]
      augmentedJet (localizationRestrictedPoint (A := A) x) k :=
  Ideal.Quotient.liftₐ _ (localizationToAugmentedJet s x k)
    (localizationToAugmentedJet_pow_eq_zero s x k)

/-- The natural map from the original jet to the localized jet. -/
noncomputable def localizationAugmentedJetMap
    (x : T →ₐ[K] K) (k : ℕ) :
    augmentedJet (localizationRestrictedPoint (A := A) x) k →ₐ[K]
      augmentedJet x k :=
  augmentedJetMap (localizationRestrictedPoint (A := A) x) x
    (IsScalarTower.toAlgHom K A T) rfl k

@[simp]
theorem localizationAugmentedJetSection_mk
    (x : T →ₐ[K] K) (k : ℕ) (y : T) :
    localizationAugmentedJetSection s x k (Ideal.Quotient.mk _ y) =
      localizationToAugmentedJet s x k y :=
  rfl

@[simp]
theorem localizationAugmentedJetMap_mk
    (x : T →ₐ[K] K) (k : ℕ) (a : A) :
    localizationAugmentedJetMap (A := A) x k (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (algebraMap A T a) :=
  rfl

/-- First inverse identity for localization invariance of finite jets. -/
theorem localizationAugmentedJetSection_comp_map
    (x : T →ₐ[K] K) (k : ℕ) :
    (localizationAugmentedJetSection s x k).comp
        (localizationAugmentedJetMap (A := A) x k) = AlgHom.id K _ := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro a
  change localizationToAugmentedJet s x k (algebraMap A T a) =
    Ideal.Quotient.mk _ a
  exact AlgHom.congr_fun
    (localizationToAugmentedJet_comp_algebraMap s x k) a

/-- Second inverse identity for localization invariance of finite jets. -/
theorem localizationAugmentedJetMap_comp_section
    (x : T →ₐ[K] K) (k : ℕ) :
    (localizationAugmentedJetMap (A := A) x k).comp
        (localizationAugmentedJetSection s x k) = AlgHom.id K _ := by
  apply Ideal.Quotient.algHom_ext
  apply IsLocalization.algHom_ext (Submonoid.powers s)
  apply AlgHom.ext
  intro a
  change localizationAugmentedJetMap (A := A) x k
      (localizationToAugmentedJet s x k (algebraMap A T a)) =
    Ideal.Quotient.mk _ (algebraMap A T a)
  have hloc : localizationToAugmentedJet s x k (algebraMap A T a) =
      Ideal.Quotient.mk _ a :=
    AlgHom.congr_fun (localizationToAugmentedJet_comp_algebraMap s x k) a
  rw [hloc]
  rfl

/-- Algebra equivalence of the finite jets before and after principal
localization. -/
noncomputable def localizationAugmentedJetAlgEquiv
    (x : T →ₐ[K] K) (k : ℕ) :
    augmentedJet (localizationRestrictedPoint (A := A) x) k ≃ₐ[K]
      augmentedJet x k :=
  AlgEquiv.ofAlgHom (localizationAugmentedJetMap (A := A) x k)
    (localizationAugmentedJetSection s x k)
    (localizationAugmentedJetMap_comp_section s x k)
    (localizationAugmentedJetSection_comp_map s x k)

end

end TranslatedDepthSeven

import TranslatedDepthSeven.AugmentedJetLocalization

/-!
# Finite jets under an arbitrary localization

This is the same finite-jet argument as for principal localization, with
an arbitrary multiplicative set.  The rational point itself ensures that
every denominator is invertible on each of its finite jets.
-/

namespace TranslatedDepthSeven

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

noncomputable def arbitraryLocalizationAugmentedJetAlgEquiv
    {K A T : Type*} [Field K] [CommRing A] [CommRing T]
    [Algebra K A] [Algebra A T] [Algebra K T] [IsScalarTower K A T]
    (S : Submonoid A) [IsLocalization S T]
    (x : T →ₐ[K] K) (k : ℕ) :
    augmentedJet (x.comp (IsScalarTower.toAlgHom K A T)) k ≃ₐ[K]
      augmentedJet x k := by
  let b := IsScalarTower.toAlgHom K A T
  let f := x.comp b
  let q : A →ₐ[K] augmentedJet f k :=
    Ideal.Quotient.mkₐ K (RingHom.ker f.toRingHom ^ (k + 1))
  have hunits : ∀ s : S, IsUnit (q s) := by
    intro s
    apply isUnit_mk_augmentedJet_of_ne_zero f k s
    change x (algebraMap A T s) ≠ 0
    exact ((IsLocalization.map_units T s).map x).ne_zero
  let lift : T →ₐ[K] augmentedJet f k := IsLocalization.liftAlgHom hunits
  have hlift : lift.comp b = q := by
    apply AlgHom.ext
    intro a
    change (IsLocalization.liftAlgHom hunits) (algebraMap A T a) = q a
    rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
    rfl
  have heval : (augmentedJetEvaluation f k).comp lift = x := by
    apply IsLocalization.algHom_ext S
    change ((augmentedJetEvaluation f k).comp lift).comp b = x.comp b
    rw [AlgHom.comp_assoc, hlift]
    rfl
  have hkill (z : T) (hz : z ∈ RingHom.ker x.toRingHom ^ (k + 1)) :
      lift z = 0 := by
    have hbase : RingHom.ker x.toRingHom ≤
        (RingHom.ker (augmentedJetEvaluation f k).toRingHom).comap lift := by
      intro y hy
      change augmentedJetEvaluation f k (lift y) = 0
      rw [← AlgHom.comp_apply, heval]
      exact hy
    have hz' := ((Ideal.pow_right_mono hbase (k + 1)).trans
      (Ideal.le_comap_pow lift (k + 1))) hz
    change lift z ∈ RingHom.ker (augmentedJetEvaluation f k).toRingHom ^ (k + 1) at hz'
    rw [pow_ker_augmentedJetEvaluation_eq_bot] at hz'
    exact hz'
  let sectionMap : augmentedJet x k →ₐ[K] augmentedJet f k :=
    Ideal.Quotient.liftₐ _ lift hkill
  let forward : augmentedJet f k →ₐ[K] augmentedJet x k :=
    augmentedJetMap f x b rfl k
  have hleft : sectionMap.comp forward = AlgHom.id K _ := by
    apply Ideal.Quotient.algHom_ext
    apply AlgHom.ext
    intro a
    exact AlgHom.congr_fun hlift a
  have hright : forward.comp sectionMap = AlgHom.id K _ := by
    apply Ideal.Quotient.algHom_ext
    apply IsLocalization.algHom_ext S
    apply AlgHom.ext
    intro a
    change forward (lift (algebraMap A T a)) =
      Ideal.Quotient.mk _ (algebraMap A T a)
    rw [show lift (algebraMap A T a) = q a from AlgHom.congr_fun hlift a]
    rfl
  exact AlgEquiv.ofAlgHom forward sectionMap hright hleft

end

end TranslatedDepthSeven

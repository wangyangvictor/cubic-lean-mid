import TranslatedDepthSeven.ProjectiveDegreeTwoAlgebra

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial
open scoped nonZeroDivisors

set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 20000000

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Surjectivity of a homogeneous linear normalization bounds the degree-one
piece of the quotient by the number of normalization parameters. -/
theorem finrank_quotientHomogeneousComponent_one_le_parameterCount_of_surjective
    (K : Type*) [Field K]
    (I : Ideal (MvPolynomial (Fin 13) K))
    (hIhomogeneous :
      I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 13) K))
    (D : HomogeneousLinearNormalizationData I)
    (hsurjective : Function.Surjective D.hom) :
    Module.finrank K
      (quotientHomogeneousComponent K (Fin 13) I 1) ≤
        D.parameterCount := by
  let A := MvPolynomial (Fin 13) K ⧸ I
  let Q := quotientHomogeneousComponent K (Fin 13) I 1
  let B := MvPolynomial (Fin D.parameterCount) K
  let BH := MvPolynomial.homogeneousSubmodule
    (Fin D.parameterCount) K 1
  let bA : B →ₗ[K] A := D.hom.toLinearMap
  let S : Submodule K A := BH.map bA
  have hQS : Q ≤ S := by
    intro x hx
    obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp hx
    obtain ⟨b, hb⟩ := hsurjective x
    let b₁ := MvPolynomial.homogeneousComponent 1 b
    have hb₁ : D.hom b₁ = Ideal.Quotient.mk I p := by
      apply normalization_preimage_homogeneousComponent
        K I hIhomogeneous D p 1 hp b
      exact hb.trans hpx.symm
    apply Submodule.mem_map.mpr
    exact ⟨b₁, MvPolynomial.homogeneousComponent_isHomogeneous 1 b,
      hb₁.trans hpx⟩
  calc
    Module.finrank K Q ≤ Module.finrank K S := Submodule.finrank_mono hQS
    _ ≤ Module.finrank K BH := Submodule.finrank_map_le bA BH
    _ = (D.parameterCount + 1 - 1).choose 1 :=
      finrank_mvPolynomial_homogeneousSubmodule_fin K D.parameterCount 1
    _ = D.parameterCount := by simp

/-- In the quadratic case, the degree-one part of a homogeneous prime quotient
over an algebraically closed characteristic-zero field is at most one dimension
larger than the degree-one part of a homogeneous linear normalization. -/
theorem finrank_quotientHomogeneousComponent_one_le_succ_parameterCount_of_quadratic
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (I : Ideal (MvPolynomial (Fin 13) K))
    (hIprime : I.IsPrime)
    (hIhomogeneous :
      I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 13) K))
    (D : HomogeneousLinearNormalizationData I)
    (hdim :
      let B := MvPolynomial (Fin D.parameterCount) K
      let A := MvPolynomial (Fin 13) K ⧸ I
      letI : Algebra B A := D.hom.toRingHom.toAlgebra
      letI : FaithfulSMul B A :=
        (faithfulSMul_iff_algebraMap_injective B A).mpr D.hom_injective
      let L := FractionRing A
      letI : FaithfulSMul B L :=
        (faithfulSMul_iff_algebraMap_injective B L).mpr
          ((IsFractionRing.injective A L).comp D.hom_injective)
      letI : Algebra (FractionRing B) L := FractionRing.liftAlgebra B L
      Module.finrank (FractionRing B) L = 2) :
    Module.finrank K
      (quotientHomogeneousComponent K (Fin 13) I 1) ≤
        D.parameterCount + 1 := by
  dsimp only at hdim
  letI : I.IsPrime := hIprime
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin 13) K ⧸ I
  let L := FractionRing A
  let KF := FractionRing B
  let Q := quotientHomogeneousComponent K (Fin 13) I 1
  letI : IsDomain A := Ideal.Quotient.isDomain I
  letI : Algebra B A := D.hom.toRingHom.toAlgebra
  letI : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective B A).mpr D.hom_injective
  haveI : Module.Finite B A := D.hom_finite
  haveI : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  letI : FaithfulSMul B L :=
    (faithfulSMul_iff_algebraMap_injective B L).mpr
      ((IsFractionRing.injective A L).comp D.hom_injective)
  letI : Algebra KF L := FractionRing.liftAlgebra B L
  letI : IsScalarTower B KF L :=
    FractionRing.isScalarTower_liftAlgebra B L
  have hdim' : Module.finrank KF L = 2 := hdim
  haveI : FiniteDimensional KF L :=
    FiniteDimensional.of_finrank_pos (by omega : 0 < Module.finrank KF L)
  let qL : Q →ₗ[K] L :=
    (IsScalarTower.toAlgHom K A L).toLinearMap.comp Q.subtype
  let tr : L →ₗ[K] KF := (Algebra.trace KF L).restrictScalars K
  let T : Q →ₗ[K] KF := tr.comp qL
  let BH := MvPolynomial.homogeneousSubmodule
    (Fin D.parameterCount) K 1
  let bKF : B →ₗ[K] KF := (IsScalarTower.toAlgHom K B KF).toLinearMap
  let S : Submodule K KF := BH.map bKF
  have hTrange : LinearMap.range T ≤ S := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.property
    obtain ⟨t, htHom, ht⟩ := exists_homogeneous_trace_preimage
      K I hIprime hIhomogeneous D hdim' p hp
    apply Submodule.mem_map.mpr
    refine ⟨t, htHom, ?_⟩
    change algebraMap B KF t = T x
    rw [ht]
    change Algebra.trace KF L
      (algebraMap A L (Ideal.Quotient.mk I p)) =
        Algebra.trace KF L (algebraMap A L x)
    exact congrArg (fun z : A ↦ Algebra.trace KF L (algebraMap A L z)) hpx
  have hSfinrank : Module.finrank K S ≤ D.parameterCount := by
    calc
      Module.finrank K S ≤ Module.finrank K BH :=
        Submodule.finrank_map_le bKF BH
      _ = (D.parameterCount + 1 - 1).choose 1 :=
        finrank_mvPolynomial_homogeneousSubmodule_fin K D.parameterCount 1
      _ = D.parameterCount := by simp
  have hTrank : Module.finrank K (LinearMap.range T) ≤ D.parameterCount :=
    (Submodule.finrank_mono hTrange).trans hSfinrank
  have hkerRank : Module.finrank K (LinearMap.ker T) ≤ 1 := by
    by_cases hkerzero : LinearMap.ker T = ⊥
    · rw [hkerzero, finrank_bot]
      omega
    · obtain ⟨x, hxker, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hkerzero
      let x' : LinearMap.ker T := ⟨x, hxker⟩
      have hx'ne : x' ≠ 0 := by
        intro h
        exact hxne (congrArg Subtype.val h)
      apply finrank_le_one x'
      intro y'
      obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x'.1.property
      obtain ⟨q, hq, hqy⟩ := Submodule.mem_map.mp y'.1.property
      have hpxA : Ideal.Quotient.mk I p = (x'.1 : Q) := hpx
      have hqyA : Ideal.Quotient.mk I q = (y'.1 : Q) := hqy
      have hpnot : p ∉ I := by
        intro hpI
        apply hx'ne
        apply Subtype.ext
        apply Subtype.ext
        rw [← hpxA]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hpI
      have htracep : Algebra.trace KF L
          (algebraMap A L (Ideal.Quotient.mk I p)) = 0 := by
        have hxT := x'.property
        change T x'.1 = 0 at hxT
        change Algebra.trace KF L (algebraMap A L x'.1) = 0 at hxT
        rw [hpxA]
        exact hxT
      have htraceq : Algebra.trace KF L
          (algebraMap A L (Ideal.Quotient.mk I q)) = 0 := by
        have hyT := y'.property
        change T y'.1 = 0 at hyT
        change Algebra.trace KF L (algebraMap A L y'.1) = 0 at hyT
        rw [hqyA]
        exact hyT
      obtain ⟨c, hc⟩ := trace_zero_linear_classes_proportional
        K I hIprime hIhomogeneous D hdim' p q hp hq hpnot htracep htraceq
      refine ⟨c, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      change c • ((x'.1 : Q) : A) = ((y'.1 : Q) : A)
      rw [← hqyA, ← hpxA]
      exact hc.symm
  have hRankNullity := T.finrank_range_add_finrank_ker
  change Module.finrank K Q ≤ D.parameterCount + 1
  omega

/-- The preceding bounds combined with finite birational normality: generic
rank at most two gives at most one degree-one generator beyond a homogeneous
linear normalization. -/
theorem finrank_quotientHomogeneousComponent_one_le_succ_parameterCount_of_rank_le_two
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (I : Ideal (MvPolynomial (Fin 13) K))
    (hIprime : I.IsPrime)
    (hIhomogeneous :
      I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 13) K))
    (D : HomogeneousLinearNormalizationData I)
    (hdim_le :
      let B := MvPolynomial (Fin D.parameterCount) K
      let A := MvPolynomial (Fin 13) K ⧸ I
      letI : Algebra B A := D.hom.toRingHom.toAlgebra
      Module.finrank (FractionRing B)
        (LocalizedModule (nonZeroDivisors B) A) ≤ 2) :
    Module.finrank K
      (quotientHomogeneousComponent K (Fin 13) I 1) ≤
        D.parameterCount + 1 := by
  dsimp only at hdim_le
  letI : I.IsPrime := hIprime
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin 13) K ⧸ I
  letI : IsDomain A := Ideal.Quotient.isDomain I
  letI : Algebra B A := D.hom.toRingHom.toAlgebra
  letI : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective B A).mpr D.hom_injective
  haveI : Module.Finite B A := D.hom_finite
  have hdim_pos : 0 < Module.finrank (FractionRing B)
      (LocalizedModule (nonZeroDivisors B) A) := by
    let f := LocalizedModule.mkLinearMap (nonZeroDivisors B) A
    have hf : Function.Injective f := by
      apply (IsLocalizedModule.injective_iff_isRegular
        (S := nonZeroDivisors B) (f := f)).mpr
      intro c x y hxy
      change (c : B) • x = (c : B) • y at hxy
      rw [Algebra.smul_def, Algebra.smul_def] at hxy
      exact mul_left_cancel₀
        (map_ne_zero_of_mem_nonZeroDivisors
          (algebraMap B A) D.hom_injective c.property) hxy
    letI : Nontrivial (LocalizedModule (nonZeroDivisors B) A) :=
      hf.nontrivial
    exact Module.finrank_pos
  interval_cases hdim : Module.finrank (FractionRing B)
      (LocalizedModule (nonZeroDivisors B) A)
  · haveI : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
    have hsurj : Function.Surjective D.hom := by
      exact algebraMap_surjective_of_localized_finrank_eq_one
        D.hom_injective hdim
    exact (finrank_quotientHomogeneousComponent_one_le_parameterCount_of_surjective
      K I hIhomogeneous D hsurj).trans (Nat.le_add_right _ _)
  · letI : Algebra (FractionRing B) (FractionRing A) :=
      FractionRing.liftAlgebra B (FractionRing A)
    have hfrac : Module.finrank (FractionRing B) (FractionRing A) = 2 := by
      rw [← localizedModule_finrank_eq_fractionRing_finrank]
      exact hdim
    exact finrank_quotientHomogeneousComponent_one_le_succ_parameterCount_of_quadratic
      K I hIprime hIhomogeneous D hfrac

end

end TranslatedDepthSeven

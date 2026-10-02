import TranslatedDepthSeven.ProjectiveDegreeTwoAlgebraBookkeeping

/-! The quadratic homogeneous-normalization calculation in arbitrary finite
coordinate dimension. The proofs are adapted from the existing thirteen-variable
calculation; no degree-span result is assumed. This supplies the degree-two
case needed for the ten-variable terminal strata. -/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 20000000

noncomputable section
namespace CubicTenVariables.DegreeTwoNormalization
open MvPolynomial TranslatedDepthSeven
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.gradedAlgebra
variable {N : ℕ}

theorem not_associated_square_of_nonbase_linear_class
    (K : Type*) [Field K] [IsAlgClosed K]
    (I : Ideal (MvPolynomial (Fin N) K))
    (hIprime : I.IsPrime)
    (D : HomogeneousLinearNormalizationData I)
    (p : MvPolynomial (Fin N) K)
    (f r : MvPolynomial (Fin D.parameterCount) K)
    (hrelation : p ^ 2 - MvPolynomial.aeval D.forms f ∈ I)
    (hnobase : ∀ b : MvPolynomial (Fin D.parameterCount) K,
      p - MvPolynomial.aeval D.forms b ∉ I)
    (hassoc : Associated f (r ^ 2)) : False := by
  classical
  let B := MvPolynomial (Fin D.parameterCount) K
  obtain ⟨u, hu⟩ := hassoc
  obtain ⟨c, hcunit, huC⟩ :=
    (MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp u.isUnit)
  have hc : c ≠ 0 := by simpa using hcunit
  have hfc : f * MvPolynomial.C c = r ^ 2 := by
    simpa only [huC] using hu
  have hf : f = MvPolynomial.C c⁻¹ * r ^ 2 := by
    calc
      f = f * 1 := (mul_one f).symm
      _ = f * (MvPolynomial.C c * MvPolynomial.C c⁻¹) := by
        rw [← map_mul, mul_inv_cancel₀ hc, map_one]
      _ = (f * MvPolynomial.C c) * MvPolynomial.C c⁻¹ := by
        rw [mul_assoc]
      _ = r ^ 2 * MvPolynomial.C c⁻¹ := by rw [hfc]
      _ = MvPolynomial.C c⁻¹ * r ^ 2 := mul_comm _ _
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq c⁻¹
    (by norm_num : 0 < 2)
  let R := MvPolynomial.aeval D.forms r
  have hevalf : MvPolynomial.aeval D.forms f =
      MvPolynomial.C (s ^ 2) * R ^ 2 := by
    rw [hf, map_mul, map_pow, hs]
    simp [R]
  have hproduct :
      (p - MvPolynomial.C s * R) *
        (p + MvPolynomial.C s * R) ∈ I := by
    have hfactor :
      (p - MvPolynomial.C s * R) *
            (p + MvPolynomial.C s * R) =
          p ^ 2 - MvPolynomial.C (s ^ 2) * R ^ 2 := by
      rw [map_pow (MvPolynomial.C : K →+* MvPolynomial (Fin N) K)]
      ring
    rw [hfactor, ← hevalf]
    exact hrelation
  rcases hIprime.mem_or_mem hproduct with hminus | hplus
  · exact hnobase (MvPolynomial.C s * r) (by
      simpa [R] using hminus)
  · exact hnobase (-(MvPolynomial.C s * r)) (by
      simpa [R] using hplus)


theorem quadratic_relation_coefficients_homogeneous
    (K : Type*) [Field K]
    (I : Ideal (MvPolynomial (Fin N) K))
    (hIprime : I.IsPrime)
    (hIhomogeneous :
      I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin N) K))
    (D : HomogeneousLinearNormalizationData I)
    (p : MvPolynomial (Fin N) K) (hp : p.IsHomogeneous 1)
    (t n : MvPolynomial (Fin D.parameterCount) K)
    (hrelation : p ^ 2 - MvPolynomial.aeval D.forms t * p +
        MvPolynomial.aeval D.forms n ∈ I)
    (hnonbase :
      let B := MvPolynomial (Fin D.parameterCount) K
      let A := MvPolynomial (Fin N) K ⧸ I
      letI : Algebra B A := D.hom.toRingHom.toAlgebra
      ∀ a b : B, b ≠ 0 →
        algebraMap A (FractionRing A) (Ideal.Quotient.mk I p) ≠
          algebraMap A (FractionRing A) (D.hom a) /
            algebraMap A (FractionRing A) (D.hom b)) :
    t.IsHomogeneous 1 ∧ n.IsHomogeneous 2 := by
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin N) K ⧸ I
  letI : I.IsPrime := hIprime
  letI : IsDomain A := Ideal.Quotient.isDomain I
  letI : Algebra B A := D.hom.toRingHom.toAlgebra
  have hti : ∀ i : ℕ, i ≠ 1 →
      MvPolynomial.homogeneousComponent i t = 0 := by
    intro i hi
    let ti := MvPolynomial.homogeneousComponent i t
    let ni := MvPolynomial.homogeneousComponent (i + 1) n
    have hcomponent := hIhomogeneous (i + 1) hrelation
    rw [← DirectSum.Decomposition.decompose'_eq,
      MvPolynomial.decomposition.decompose'_apply] at hcomponent
    have hp2 : (p ^ 2).IsHomogeneous 2 := by
      simpa [pow_two] using hp.mul hp
    have hp2zero : MvPolynomial.homogeneousComponent (i + 1) (p ^ 2) = 0 := by
      rw [MvPolynomial.homogeneousComponent_of_mem hp2,
        if_neg (by omega)]
    have hmul : MvPolynomial.homogeneousComponent (i + 1)
        (MvPolynomial.aeval D.forms t * p) =
        MvPolynomial.aeval D.forms ti * p := by
      rw [homogeneousComponent_succ_mul_degreeOne _ _ hp i,
        homogeneousComponent_aeval_degreeOne D.forms
          D.forms_isHomogeneous]
    have hncomp : MvPolynomial.homogeneousComponent (i + 1)
        (MvPolynomial.aeval D.forms n) = MvPolynomial.aeval D.forms ni := by
      rw [homogeneousComponent_aeval_degreeOne D.forms
        D.forms_isHomogeneous]
    simp only [map_add, map_sub] at hcomponent
    rw [hp2zero, hmul, hncomp, zero_sub] at hcomponent
    by_contra htine
    have hqzero : Ideal.Quotient.mk I
        (-(MvPolynomial.aeval D.forms ti * p) +
          MvPolynomial.aeval D.forms ni) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hcomponent
    have hAeq : D.hom ti * Ideal.Quotient.mk I p = D.hom ni := by
      simp only [map_add, map_neg, map_mul] at hqzero
      change -(D.hom ti * Ideal.Quotient.mk I p) + D.hom ni = 0 at hqzero
      linear_combination -hqzero
    apply hnonbase ni ti htine
    have hden : algebraMap A (FractionRing A) (D.hom ti) ≠ 0 := by
      simpa only [map_zero] using
        (IsFractionRing.injective A (FractionRing A)).ne
          (D.hom_injective.ne htine)
    rw [eq_div_iff hden]
    simpa only [map_mul, mul_comm] using
      congrArg (algebraMap A (FractionRing A)) hAeq
  have htHom : t.IsHomogeneous 1 :=
    isHomogeneous_of_other_components_eq_zero t 1 hti
  have hnj : ∀ j : ℕ, j ≠ 2 →
      MvPolynomial.homogeneousComponent j n = 0 := by
    intro j hj
    have hcomponent := hIhomogeneous j hrelation
    rw [← DirectSum.Decomposition.decompose'_eq,
      MvPolynomial.decomposition.decompose'_apply] at hcomponent
    have hp2 : (p ^ 2).IsHomogeneous 2 := by
      simpa [pow_two] using hp.mul hp
    have hp2zero : MvPolynomial.homogeneousComponent j (p ^ 2) = 0 := by
      rw [MvPolynomial.homogeneousComponent_of_mem hp2,
        if_neg hj]
    have hmulzero : MvPolynomial.homogeneousComponent j
        (MvPolynomial.aeval D.forms t * p) = 0 := by
      rcases j with _ | k
      · exact homogeneousComponent_zero_mul_degreeOne _ _ hp
      · rw [homogeneousComponent_succ_mul_degreeOne _ _ hp k,
          homogeneousComponent_aeval_degreeOne D.forms
            D.forms_isHomogeneous]
        rw [hti k (by omega), map_zero, zero_mul]
    have hncomp : MvPolynomial.homogeneousComponent j
        (MvPolynomial.aeval D.forms n) =
        MvPolynomial.aeval D.forms
          (MvPolynomial.homogeneousComponent j n) :=
      homogeneousComponent_aeval_degreeOne D.forms
        D.forms_isHomogeneous n j
    simp only [map_add, map_sub] at hcomponent
    rw [hp2zero, hmulzero, hncomp, sub_zero, zero_add] at hcomponent
    apply D.hom_injective
    change Ideal.Quotient.mk I
      (MvPolynomial.aeval D.forms
        (MvPolynomial.homogeneousComponent j n)) =
      Ideal.Quotient.mk I (MvPolynomial.aeval D.forms 0)
    rw [map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hcomponent
  exact ⟨htHom, isHomogeneous_of_other_components_eq_zero n 2 hnj⟩


theorem exists_homogeneous_trace_preimage
    (K : Type*) [Field K]
    (I : Ideal (MvPolynomial (Fin N) K))
    (hIprime : I.IsPrime)
    (hIhomogeneous :
      I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin N) K))
    (D : HomogeneousLinearNormalizationData I)
    (hdim :
      let B := MvPolynomial (Fin D.parameterCount) K
      let A := MvPolynomial (Fin N) K ⧸ I
      letI : Algebra B A := D.hom.toRingHom.toAlgebra
      letI : FaithfulSMul B A :=
        (faithfulSMul_iff_algebraMap_injective B A).mpr D.hom_injective
      let L := FractionRing A
      letI : FaithfulSMul B L :=
        (faithfulSMul_iff_algebraMap_injective B L).mpr
          ((IsFractionRing.injective A L).comp D.hom_injective)
      letI : Algebra (FractionRing B) L := FractionRing.liftAlgebra B L
      Module.finrank (FractionRing B) L = 2)
    (p : MvPolynomial (Fin N) K) (hp : p.IsHomogeneous 1) :
    let B := MvPolynomial (Fin D.parameterCount) K
    let A := MvPolynomial (Fin N) K ⧸ I
    letI : Algebra B A := D.hom.toRingHom.toAlgebra
    letI : FaithfulSMul B A :=
      (faithfulSMul_iff_algebraMap_injective B A).mpr D.hom_injective
    let L := FractionRing A
    letI : FaithfulSMul B L :=
      (faithfulSMul_iff_algebraMap_injective B L).mpr
        ((IsFractionRing.injective A L).comp D.hom_injective)
    letI : Algebra (FractionRing B) L := FractionRing.liftAlgebra B L
    ∃ t : B, t.IsHomogeneous 1 ∧
      algebraMap B (FractionRing B) t =
        Algebra.trace (FractionRing B) L
          (algebraMap A L (Ideal.Quotient.mk I p)) := by
  dsimp only
  letI : I.IsPrime := hIprime
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin N) K ⧸ I
  let L := FractionRing A
  let KF := FractionRing B
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
  let xA : A := Ideal.Quotient.mk I p
  let x : L := algebraMap A L xA
  have hxIntegral : IsIntegral B x := by
    exact (Algebra.IsIntegral.isIntegral xA).map
      (IsScalarTower.toAlgHom B A L)
  by_cases hbase : ∃ k : KF, x = algebraMap KF L k
  · obtain ⟨k, hk⟩ := hbase
    have hkIntegral : IsIntegral B k := by
      rw [← isIntegral_algHom_iff
        (IsScalarTower.toAlgHom B KF L)
        (FaithfulSMul.algebraMap_injective KF L)]
      simpa only [hk] using hxIntegral
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hkIntegral
    have hxB : x = algebraMap B L b := by
      calc
        x = algebraMap KF L k := hk
        _ = algebraMap KF L (algebraMap B KF b) := by rw [hb]
        _ = algebraMap B L b :=
          (IsScalarTower.algebraMap_apply B KF L b).symm
    have hxA : xA = D.hom b := by
      apply IsFractionRing.injective A L
      change x = algebraMap B L b
      exact hxB
    let b₁ := MvPolynomial.homogeneousComponent 1 b
    have hb₁ : D.hom b₁ = xA :=
      normalization_preimage_homogeneousComponent
        K I hIhomogeneous D p 1 hp b hxA.symm
    let t : B := MvPolynomial.C (2 : K) * b₁
    refine ⟨t, ?_, ?_⟩
    · simpa only [zero_add] using
        (MvPolynomial.isHomogeneous_C (Fin D.parameterCount) (2 : K)).mul
          (MvPolynomial.homogeneousComponent_isHomogeneous 1 b)
    · have hxB₁ : x = algebraMap B L b₁ := by
        change algebraMap A L xA = _
        rw [← hb₁]
        exact IsScalarTower.algebraMap_apply B A L b₁
      change algebraMap B KF t = Algebra.trace KF L x
      rw [hxB₁, IsScalarTower.algebraMap_apply B KF L,
        Algebra.trace_algebraMap, hdim']
      have hc : (MvPolynomial.C (2 : K) : B) = 2 :=
        map_ofNat (MvPolynomial.C : K →+* B) 2
      simp only [t, map_mul, hc, map_ofNat, nsmul_eq_mul]
      norm_num
  · have hnonbase : ∀ a b : B, b ≠ 0 →
        x ≠ algebraMap A L (D.hom a) / algebraMap A L (D.hom b) := by
      intro a b _hb hab
      apply hbase
      refine ⟨algebraMap B KF a / algebraMap B KF b, ?_⟩
      rw [hab]
      change algebraMap B L a / algebraMap B L b =
        algebraMap KF L (algebraMap B KF a / algebraMap B KF b)
      rw [map_div₀ (algebraMap KF L : KF →+* L)]
      congr 1 <;> exact IsScalarTower.algebraMap_apply B KF L _
    have htrIntegral : IsIntegral B (Algebra.trace KF L x) :=
      Algebra.isIntegral_trace hxIntegral
    have hnormIntegral : IsIntegral B (Algebra.norm KF x) :=
      Algebra.isIntegral_norm KF hxIntegral
    obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.mp htrIntegral
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hnormIntegral
    have hrelation : p ^ 2 - MvPolynomial.aeval D.forms t * p +
        MvPolynomial.aeval D.forms n ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      apply IsFractionRing.injective A L
      simp only [map_add, map_sub, map_mul, map_pow, map_zero]
      change x ^ 2 - algebraMap A L (D.hom t) * x +
        algebraMap A L (D.hom n) = 0
      have hmap (b : B) : algebraMap A L (D.hom b) =
          algebraMap B L b := by
        rw [← show algebraMap B A b = D.hom b from rfl]
        exact (IsScalarTower.algebraMap_apply B A L b).symm
      rw [hmap t, hmap n]
      rw [IsScalarTower.algebraMap_apply B KF L,
        IsScalarTower.algebraMap_apply B KF L, ht, hn]
      exact quadratic_cayley_trace_norm hdim' x
    have hhom := quadratic_relation_coefficients_homogeneous
      K I hIprime hIhomogeneous D p hp t n hrelation hnonbase
    exact ⟨t, hhom.1, ht⟩


theorem exists_homogeneous_square_preimage_live
    (K : Type*) [Field K] [CharZero K]
    (I : Ideal (MvPolynomial (Fin N) K))
    (hIprime : I.IsPrime)
    (hIhomogeneous :
      I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin N) K))
    (D : HomogeneousLinearNormalizationData I)
    (hdim :
      let B := MvPolynomial (Fin D.parameterCount) K
      let A := MvPolynomial (Fin N) K ⧸ I
      letI : Algebra B A := D.hom.toRingHom.toAlgebra
      letI : FaithfulSMul B A :=
        (faithfulSMul_iff_algebraMap_injective B A).mpr D.hom_injective
      let L := FractionRing A
      letI : FaithfulSMul B L :=
        (faithfulSMul_iff_algebraMap_injective B L).mpr
          ((IsFractionRing.injective A L).comp D.hom_injective)
      letI : Algebra (FractionRing B) L := FractionRing.liftAlgebra B L
      Module.finrank (FractionRing B) L = 2)
    (p : MvPolynomial (Fin N) K) (hp : p.IsHomogeneous 1)
    (hpnot : p ∉ I)
    (htrace :
      let B := MvPolynomial (Fin D.parameterCount) K
      let A := MvPolynomial (Fin N) K ⧸ I
      letI : Algebra B A := D.hom.toRingHom.toAlgebra
      letI : FaithfulSMul B A :=
        (faithfulSMul_iff_algebraMap_injective B A).mpr D.hom_injective
      let L := FractionRing A
      letI : FaithfulSMul B L :=
        (faithfulSMul_iff_algebraMap_injective B L).mpr
          ((IsFractionRing.injective A L).comp D.hom_injective)
      letI : Algebra (FractionRing B) L := FractionRing.liftAlgebra B L
      Algebra.trace (FractionRing B) L
        (algebraMap A L (Ideal.Quotient.mk I p)) = 0) :
    let B := MvPolynomial (Fin D.parameterCount) K
    let A := MvPolynomial (Fin N) K ⧸ I
    letI : Algebra B A := D.hom.toRingHom.toAlgebra
    letI : FaithfulSMul B A :=
      (faithfulSMul_iff_algebraMap_injective B A).mpr D.hom_injective
    let L := FractionRing A
    letI : FaithfulSMul B L :=
      (faithfulSMul_iff_algebraMap_injective B L).mpr
        ((IsFractionRing.injective A L).comp D.hom_injective)
    letI : Algebra (FractionRing B) L := FractionRing.liftAlgebra B L
    ∃ f : B, f.IsHomogeneous 2 ∧
      p ^ 2 - MvPolynomial.aeval D.forms f ∈ I ∧
      algebraMap B L f =
        (algebraMap A L (Ideal.Quotient.mk I p)) ^ 2 := by
  dsimp only
  dsimp only at htrace
  letI : I.IsPrime := hIprime
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin N) K ⧸ I
  let L := FractionRing A
  let KF := FractionRing B
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
  let xA : A := Ideal.Quotient.mk I p
  let x : L := algebraMap A L xA
  have htrace' : Algebra.trace KF L x = 0 := by
    exact htrace
  have hxIntegral : IsIntegral B x := by
    exact (Algebra.IsIntegral.isIntegral xA).map
      (IsScalarTower.toAlgHom B A L)
  have hxne : x ≠ 0 := by
    intro hx
    apply hpnot
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply IsFractionRing.injective A L
    simpa only [map_zero] using hx
  have hxnonbase : ¬ ∃ k : KF, x = algebraMap KF L k := by
    rintro ⟨k, hk⟩
    have hkzero : k = 0 := by
      have hz := htrace'
      rw [hk, Algebra.trace_algebraMap, hdim'] at hz
      have hz' : (2 : KF) * k = 0 := by
        simpa only [nsmul_eq_mul] using hz
      exact (mul_eq_zero.mp hz').resolve_left (by norm_num)
    exact hxne (by rw [hk, hkzero, map_zero])
  have hnonbase : ∀ a b : B, b ≠ 0 →
      x ≠ algebraMap A L (D.hom a) / algebraMap A L (D.hom b) := by
    intro a b _hb hab
    apply hxnonbase
    refine ⟨algebraMap B KF a / algebraMap B KF b, ?_⟩
    rw [hab]
    change algebraMap B L a / algebraMap B L b =
      algebraMap KF L (algebraMap B KF a / algebraMap B KF b)
    rw [map_div₀ (algebraMap KF L : KF →+* L)]
    congr 1 <;> exact IsScalarTower.algebraMap_apply B KF L _
  have hnormIntegral : IsIntegral B (Algebra.norm KF x) :=
    Algebra.isIntegral_norm KF hxIntegral
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hnormIntegral
  have hrelation : p ^ 2 + MvPolynomial.aeval D.forms n ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply IsFractionRing.injective A L
    simp only [map_add, map_pow, map_zero]
    change x ^ 2 + algebraMap A L (D.hom n) = 0
    have hmap : algebraMap A L (D.hom n) = algebraMap B L n := by
      rw [← show algebraMap B A n = D.hom n from rfl]
      exact (IsScalarTower.algebraMap_apply B A L n).symm
    rw [hmap, IsScalarTower.algebraMap_apply B KF L, hn]
    have hCH := quadratic_cayley_trace_norm hdim' x
    rw [htrace', map_zero, zero_mul, sub_zero] at hCH
    exact hCH
  have hrelation' : p ^ 2 - MvPolynomial.aeval D.forms (0 : B) * p +
      MvPolynomial.aeval D.forms n ∈ I := by
    simpa using hrelation
  have hnHom : n.IsHomogeneous 2 :=
    (quadratic_relation_coefficients_homogeneous
      K I hIprime hIhomogeneous D p hp (0 : B) n hrelation' hnonbase).2
  refine ⟨-n, hnHom.neg, ?_, ?_⟩
  · simpa using hrelation
  · rw [map_neg]
    change -algebraMap B L n = x ^ 2
    rw [IsScalarTower.algebraMap_apply B KF L, hn]
    have hCH := quadratic_cayley_trace_norm hdim' x
    rw [htrace', map_zero, zero_mul, sub_zero] at hCH
    linear_combination -hCH


theorem trace_zero_linear_classes_proportional
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (I : Ideal (MvPolynomial (Fin N) K))
    (hIprime : I.IsPrime)
    (hIhomogeneous :
      I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin N) K))
    (D : HomogeneousLinearNormalizationData I)
    (hdim :
      let B := MvPolynomial (Fin D.parameterCount) K
      let A := MvPolynomial (Fin N) K ⧸ I
      letI : Algebra B A := D.hom.toRingHom.toAlgebra
      letI : FaithfulSMul B A :=
        (faithfulSMul_iff_algebraMap_injective B A).mpr D.hom_injective
      let L := FractionRing A
      letI : FaithfulSMul B L :=
        (faithfulSMul_iff_algebraMap_injective B L).mpr
          ((IsFractionRing.injective A L).comp D.hom_injective)
      letI : Algebra (FractionRing B) L := FractionRing.liftAlgebra B L
      Module.finrank (FractionRing B) L = 2)
    (p q : MvPolynomial (Fin N) K)
    (hp : p.IsHomogeneous 1) (hq : q.IsHomogeneous 1)
    (hpnot : p ∉ I)
    (htracep :
      let B := MvPolynomial (Fin D.parameterCount) K
      let A := MvPolynomial (Fin N) K ⧸ I
      letI : Algebra B A := D.hom.toRingHom.toAlgebra
      letI : FaithfulSMul B A :=
        (faithfulSMul_iff_algebraMap_injective B A).mpr D.hom_injective
      let L := FractionRing A
      letI : FaithfulSMul B L :=
        (faithfulSMul_iff_algebraMap_injective B L).mpr
          ((IsFractionRing.injective A L).comp D.hom_injective)
      letI : Algebra (FractionRing B) L := FractionRing.liftAlgebra B L
      Algebra.trace (FractionRing B) L
        (algebraMap A L (Ideal.Quotient.mk I p)) = 0)
    (htraceq :
      let B := MvPolynomial (Fin D.parameterCount) K
      let A := MvPolynomial (Fin N) K ⧸ I
      letI : Algebra B A := D.hom.toRingHom.toAlgebra
      letI : FaithfulSMul B A :=
        (faithfulSMul_iff_algebraMap_injective B A).mpr D.hom_injective
      let L := FractionRing A
      letI : FaithfulSMul B L :=
        (faithfulSMul_iff_algebraMap_injective B L).mpr
          ((IsFractionRing.injective A L).comp D.hom_injective)
      letI : Algebra (FractionRing B) L := FractionRing.liftAlgebra B L
      Algebra.trace (FractionRing B) L
        (algebraMap A L (Ideal.Quotient.mk I q)) = 0) :
    ∃ c : K, Ideal.Quotient.mk I q = c • Ideal.Quotient.mk I p := by
  dsimp only at htracep htraceq hdim
  letI : I.IsPrime := hIprime
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin N) K ⧸ I
  let L := FractionRing A
  let KF := FractionRing B
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
  let xA : A := Ideal.Quotient.mk I p
  let yA : A := Ideal.Quotient.mk I q
  let x : L := algebraMap A L xA
  let y : L := algebraMap A L yA
  have hxne : x ≠ 0 := by
    intro hx
    apply hpnot
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply IsFractionRing.injective A L
    simpa only [map_zero] using hx
  by_cases hqI : q ∈ I
  · refine ⟨0, ?_⟩
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hqI]
    simp
  have hyne : y ≠ 0 := by
    intro hy
    apply hqI
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply IsFractionRing.injective A L
    simpa only [map_zero] using hy
  obtain ⟨k, hykx⟩ := trace_zero_vectors_proportional_quadratic
    hdim' hxne htracep htraceq
  have hykx' : y = algebraMap KF L k * x := by
    change y = k • x at hykx
    simpa only [Algebra.smul_def] using hykx
  obtain ⟨f, hfHom, hfrelation, hfx⟩ :=
    exists_homogeneous_square_preimage_live K I hIprime hIhomogeneous
      D hdim' p hp hpnot htracep
  obtain ⟨g, hgHom, hgrelation, hgy⟩ :=
    exists_homogeneous_square_preimage_live K I hIprime hIhomogeneous
      D hdim' q hq hqI htraceq
  have hxIntegral : IsIntegral B x := by
    exact (Algebra.IsIntegral.isIntegral xA).map
      (IsScalarTower.toAlgHom B A L)
  have hyIntegral : IsIntegral B y := by
    exact (Algebra.IsIntegral.isIntegral yA).map
      (IsScalarTower.toAlgHom B A L)
  let z : KF := k * algebraMap B KF f
  have hmapz : algebraMap KF L z = x * y := by
    dsimp only [z]
    rw [map_mul, ← IsScalarTower.algebraMap_apply B KF L, hfx]
    rw [hykx']
    ring
  have hzIntegral : IsIntegral B z := by
    rw [← isIntegral_algHom_iff
      (IsScalarTower.toAlgHom B KF L)
      (FaithfulSMul.algebraMap_injective KF L)]
    change IsIntegral B (algebraMap KF L z)
    rw [hmapz]
    exact hxIntegral.mul hyIntegral
  obtain ⟨h₀, hh₀⟩ := IsIntegrallyClosed.isIntegral_iff.mp hzIntegral
  have hh₀L : algebraMap B L h₀ = x * y := by
    rw [IsScalarTower.algebraMap_apply B KF L, hh₀, hmapz]
  have hh₀A : D.hom h₀ = Ideal.Quotient.mk I (p * q) := by
    apply IsFractionRing.injective A L
    have hmap (b : B) : algebraMap A L (D.hom b) =
        algebraMap B L b := by
      rw [← show algebraMap B A b = D.hom b from rfl]
      exact (IsScalarTower.algebraMap_apply B A L b).symm
    rw [hmap, hh₀L]
    change x * y = algebraMap A L (xA * yA)
    rw [map_mul]
  let h := MvPolynomial.homogeneousComponent 2 h₀
  have hhA : D.hom h = Ideal.Quotient.mk I (p * q) := by
    exact normalization_preimage_homogeneousComponent K I hIhomogeneous
      D (p * q) 2 (hp.mul hq) h₀ hh₀A
  have hhHom : h.IsHomogeneous 2 :=
    MvPolynomial.homogeneousComponent_isHomogeneous 2 h₀
  have hhrelation : p * q - MvPolynomial.aeval D.forms h ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa [HomogeneousLinearNormalizationData.hom, map_sub] using
      sub_eq_zero.mpr hhA.symm
  have hhyx : algebraMap B L h = x * y := by
    have hmap (b : B) : algebraMap B L b =
        algebraMap A L (D.hom b) := by
      rw [← show algebraMap B A b = D.hom b from rfl]
      exact IsScalarTower.algebraMap_apply B A L b
    rw [hmap, hhA]
    change algebraMap A L (xA * yA) = x * y
    rw [map_mul]
  have hfne : f ≠ 0 := by
    intro hfzero
    rw [hfzero, map_zero] at hfx
    exact hxne (by
      have : x ^ 2 = 0 := hfx.symm
      have hxx : x * x = 0 := by simpa [pow_two] using this
      exact mul_self_eq_zero.mp hxx)
  have hhne : h ≠ 0 := by
    intro hhzero
    rw [hhzero, map_zero] at hhyx
    exact mul_ne_zero hxne hyne hhyx.symm
  have hfg : h ^ 2 = f * g := by
    apply (FaithfulSMul.algebraMap_injective B L)
    rw [map_pow, map_mul, hhyx, hfx, hgy]
    ring
  by_cases hdiv : f ∣ h
  · obtain ⟨ell, hell⟩ := hdiv
    have hellne : ell ≠ 0 := by
      intro hellzero
      rw [hellzero, mul_zero] at hell
      exact hhne hell
    have hdegf : f.totalDegree = 2 := hfHom.totalDegree hfne
    have hdegh : h.totalDegree = 2 := hhHom.totalDegree hhne
    have hdegmul := MvPolynomial.totalDegree_mul_of_isDomain hfne hellne
    rw [← hell, hdegh, hdegf] at hdegmul
    have hdegell : ell.totalDegree = 0 := by omega
    have hellC : ell = MvPolynomial.C (MvPolynomial.coeff 0 ell) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegell
    let c : K := MvPolynomial.coeff 0 ell
    have hCmap : algebraMap B L (MvPolynomial.C c) =
        algebraMap K L c := by
      calc
        algebraMap B L (MvPolynomial.C c) =
            algebraMap B L (algebraMap K B c) := by rfl
        _ = algebraMap K L c :=
          (IsScalarTower.algebraMap_apply K B L c).symm
    have hxy : x * y = x * (algebraMap K L c * x) := by
      rw [← hhyx, hell, map_mul, hfx, hellC]
      rw [hCmap]
      ring
    have hy : y = algebraMap K L c * x := mul_left_cancel₀ hxne hxy
    refine ⟨c, ?_⟩
    apply IsFractionRing.injective A L
    change y = algebraMap A L (c • xA)
    rw [Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply K A L c]
    exact hy
  · have hfdv : f ∣ h ^ 2 := ⟨g, hfg⟩
    obtain ⟨r, _hrIrr, hassoc⟩ :=
      associated_square_of_quadratic_dvd_square_not_dvd
        hfne hhne hfHom hfdv hdiv
    have hnobase : ∀ b : B,
        p - MvPolynomial.aeval D.forms b ∉ I := by
      intro b hb
      have hbq : Ideal.Quotient.mk I p = D.hom b := by
        have hz : Ideal.Quotient.mk I
            (p - MvPolynomial.aeval D.forms b) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr hb
        simp only [map_sub] at hz
        change Ideal.Quotient.mk I p - D.hom b = 0 at hz
        exact sub_eq_zero.mp hz
      have hxB : x = algebraMap B L b := by
        change algebraMap A L xA = algebraMap B L b
        rw [show xA = D.hom b from hbq]
        rw [← show algebraMap B A b = D.hom b from rfl]
        exact IsScalarTower.algebraMap_apply B A L b
      have hbKF : algebraMap B KF b = 0 := by
        have hz := htracep
        change Algebra.trace KF L x = 0 at hz
        rw [hxB, IsScalarTower.algebraMap_apply B KF L,
          Algebra.trace_algebraMap, hdim'] at hz
        have hz' : (2 : KF) * algebraMap B KF b = 0 := by
          simpa only [nsmul_eq_mul] using hz
        exact (mul_eq_zero.mp hz').resolve_left (by norm_num)
      have hbzero : b = 0 :=
        (FaithfulSMul.algebraMap_injective B KF)
          (by simpa only [map_zero] using hbKF)
      apply hpnot
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [hbq, hbzero, map_zero]
    exact (not_associated_square_of_nonbase_linear_class
      K I hIprime D p f r hfrelation hnobase hassoc).elim


theorem finrank_quotientHomogeneousComponent_one_le_parameterCount_of_surjective
    (K : Type*) [Field K]
    (I : Ideal (MvPolynomial (Fin N) K))
    (hIhomogeneous :
      I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin N) K))
    (D : HomogeneousLinearNormalizationData I)
    (hsurjective : Function.Surjective D.hom) :
    Module.finrank K
      (quotientHomogeneousComponent K (Fin N) I 1) ≤
        D.parameterCount := by
  let A := MvPolynomial (Fin N) K ⧸ I
  let Q := quotientHomogeneousComponent K (Fin N) I 1
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
    (I : Ideal (MvPolynomial (Fin N) K))
    (hIprime : I.IsPrime)
    (hIhomogeneous :
      I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin N) K))
    (D : HomogeneousLinearNormalizationData I)
    (hdim :
      let B := MvPolynomial (Fin D.parameterCount) K
      let A := MvPolynomial (Fin N) K ⧸ I
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
      (quotientHomogeneousComponent K (Fin N) I 1) ≤
        D.parameterCount + 1 := by
  dsimp only at hdim
  letI : I.IsPrime := hIprime
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin N) K ⧸ I
  let L := FractionRing A
  let KF := FractionRing B
  let Q := quotientHomogeneousComponent K (Fin N) I 1
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
    (I : Ideal (MvPolynomial (Fin N) K))
    (hIprime : I.IsPrime)
    (hIhomogeneous :
      I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin N) K))
    (D : HomogeneousLinearNormalizationData I)
    (hdim_le :
      let B := MvPolynomial (Fin D.parameterCount) K
      let A := MvPolynomial (Fin N) K ⧸ I
      letI : Algebra B A := D.hom.toRingHom.toAlgebra
      Module.finrank (FractionRing B)
        (LocalizedModule (nonZeroDivisors B) A) ≤ 2) :
    Module.finrank K
      (quotientHomogeneousComponent K (Fin N) I 1) ≤
        D.parameterCount + 1 := by
  dsimp only at hdim_le
  letI : I.IsPrime := hIprime
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin N) K ⧸ I
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


end CubicTenVariables.DegreeTwoNormalization

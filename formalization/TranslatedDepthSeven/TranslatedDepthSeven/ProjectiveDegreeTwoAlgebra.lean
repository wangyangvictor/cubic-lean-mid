import TranslatedDepthSeven.ProjectiveDegreeOneSpan
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 5000000

namespace TranslatedDepthSeven

open MvPolynomial
open UniqueFactorizationMonoid

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 5000000

noncomputable local instance mvPolynomialNormalizationMonoid
    {K : Type*} [Field K] {sigma : Type*} :
    NormalizationMonoid (MvPolynomial sigma K) := Classical.arbitrary _

theorem card_normalizedFactors_le_totalDegree
    {K : Type*} [Field K] {sigma : Type*} [Fintype sigma] [LinearOrder sigma]
    (f : MvPolynomial sigma K) (hf : f ≠ 0) :
    (normalizedFactors f).card ≤ f.totalDegree := by
  classical
  let s := normalizedFactors f
  have hsirreducible : ∀ p ∈ s, Irreducible p := by
    intro p hp
    exact irreducible_of_normalized_factor p hp
  have hsne : ∀ p ∈ s, p ≠ 0 := by
    intro p hp
    exact (hsirreducible p hp).ne_zero
  have hsdegree : ∀ p ∈ s, 0 < p.totalDegree := by
    intro p hp
    have hirr := hsirreducible p hp
    by_contra hnot
    have hzero : p.totalDegree = 0 := Nat.eq_zero_of_not_pos hnot
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hzero
    apply hirr.not_isUnit
    rw [hzero]
    have hcne : MvPolynomial.coeff 0 p ≠ 0 := by
      intro hc
      apply hirr.ne_zero
      rw [hzero, hc, map_zero]
    simpa using (isUnit_iff_ne_zero.mpr hcne)
  have hcardprodAux : ∀ t : Multiset (MvPolynomial sigma K),
      (∀ p ∈ t, p ≠ 0) → (∀ p ∈ t, 0 < p.totalDegree) →
      t.card ≤ t.prod.totalDegree := by
    intro t htne htdegree
    induction t using Multiset.induction_on with
    | empty => simp
    | @cons p t ih =>
        have hp : p ≠ 0 := htne p (Multiset.mem_cons_self p t)
        have htprod : t.prod ≠ 0 := by
          exact Multiset.prod_ne_zero fun h ↦
            htne 0 (Multiset.mem_cons_of_mem h) rfl
        rw [Multiset.card_cons, Multiset.prod_cons,
          MvPolynomial.totalDegree_mul_of_isDomain hp htprod]
        have hpdeg := htdegree p (Multiset.mem_cons_self p t)
        have ih' : t.card ≤ t.prod.totalDegree := by
          apply ih
          · intro q hq
            exact htne q (Multiset.mem_cons_of_mem hq)
          · intro q hq
            exact htdegree q (Multiset.mem_cons_of_mem hq)
        omega
  have hcardprod : s.card ≤ s.prod.totalDegree :=
    hcardprodAux s hsne hsdegree
  have hprod : s.prod = normalize f := prod_normalizedFactors_eq hf
  have hdegreeNormalize : (normalize f).totalDegree = f.totalDegree := by
    apply le_antisymm
    · exact MvPolynomial.totalDegree_le_of_dvd_of_isDomain
        (Associated.dvd (associated_normalize f).symm) hf
    · exact MvPolynomial.totalDegree_le_of_dvd_of_isDomain
        (Associated.dvd (associated_normalize f))
        (fun h ↦ hf (normalize_eq_zero.mp h))
  simpa only [s, hprod, hdegreeNormalize] using hcardprod

theorem associated_square_of_quadratic_dvd_square_not_dvd
    {K : Type*} [Field K] {sigma : Type*} [Fintype sigma] [LinearOrder sigma]
    {f g : MvPolynomial sigma K}
    (hf : f ≠ 0) (hg : g ≠ 0)
    (hfHom : f.IsHomogeneous 2)
    (hdiv : f ∣ g ^ 2) (hnotdiv : ¬ f ∣ g) :
    ∃ p : MvPolynomial sigma K, Irreducible p ∧ Associated f (p ^ 2) := by
  classical
  let F := normalizedFactors f
  let G := normalizedFactors g
  have hFcard : F.card ≤ 2 := by
    change (normalizedFactors f).card ≤ 2
    simpa only [hfHom.totalDegree hf] using
      (card_normalizedFactors_le_totalDegree f hf)
  have hFleTwoG : F ≤ 2 • G := by
    have := (dvd_iff_normalizedFactors_le_normalizedFactors hf
      (pow_ne_zero 2 hg)).mp hdiv
    simpa only [normalizedFactors_pow] using this
  have hFnotleG : ¬ F ≤ G := by
    intro h
    apply hnotdiv
    exact (dvd_iff_normalizedFactors_le_normalizedFactors hf hg).mpr h
  have hFne : F ≠ 0 := by
    intro h
    have hunit : IsUnit f :=
      (normalizedFactors_eq_zero_iff hf).mp h
    exact hnotdiv hunit.dvd
  have hFpos : 0 < F.card := Multiset.card_pos.mpr hFne
  have hFcardEq : F.card = 1 ∨ F.card = 2 := by omega
  rcases hFcardEq with hcard1 | hcard2
  · obtain ⟨p, hpF⟩ := Multiset.card_eq_one.mp hcard1
    have hpTwoG : p ∈ 2 • G := by
      rw [hpF] at hFleTwoG
      exact Multiset.subset_of_le hFleTwoG (by simp)
    have hpG : p ∈ G := by
      simpa using hpTwoG
    exfalso
    apply hFnotleG
    rw [hpF]
    exact Multiset.singleton_le.mpr hpG
  · obtain ⟨p, q, hpq⟩ := Multiset.card_eq_two.mp hcard2
    have hpcount : Multiset.count p F ≤ 2 * Multiset.count p G := by
      have := Multiset.le_iff_count.mp hFleTwoG p
      simpa using this
    have hqcount : Multiset.count q F ≤ 2 * Multiset.count q G := by
      have := Multiset.le_iff_count.mp hFleTwoG q
      simpa using this
    by_cases hpqeq : p = q
    · subst q
      have hpF : p ∈ normalizedFactors f := by
        change p ∈ F
        rw [hpq]
        simp
      have hpIrr : Irreducible p :=
        irreducible_of_normalized_factor p hpF
      refine ⟨p, ?_, ?_⟩
      · exact hpIrr
      · apply (associated_iff_normalizedFactors_eq_normalizedFactors
          hf (pow_ne_zero 2 hpIrr.ne_zero)).mpr
        change F = normalizedFactors (p ^ 2)
        rw [hpq, normalizedFactors_pow, normalizedFactors_irreducible hpIrr]
        rw [normalize_normalized_factor p hpF]
        simp [two_nsmul]
    · have hpG : p ∈ G := by
        rw [hpq] at hpcount
        have : 0 < Multiset.count p G := by
          simp [hpqeq] at hpcount
          omega
        exact Multiset.count_pos.mp this
      have hqG : q ∈ G := by
        rw [hpq] at hqcount
        have : 0 < Multiset.count q G := by
          simp [hpqeq] at hqcount
          omega
        exact Multiset.count_pos.mp this
      exfalso
      apply hFnotleG
      rw [hpq]
      rw [Multiset.le_iff_count]
      intro r
      by_cases hrp : r = p
      · subst r
        simpa [hpqeq] using (Multiset.count_pos.mpr hpG)
      · by_cases hrq : r = q
        · subst r
          simpa [hpqeq] using (Multiset.count_pos.mpr hqG)
        · simp [hrp, hrq]

theorem homogeneousComponent_zero_mul_degreeOne
    {K : Type*} [Field K] {sigma : Type*}
    (p q : MvPolynomial sigma K) (hq : q.IsHomogeneous 1) :
    MvPolynomial.homogeneousComponent 0 (p * q) = 0 := by
  classical
  conv_lhs =>
    rw [← p.sum_homogeneousComponent]
  rw [Finset.sum_mul, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have hprod :
      (MvPolynomial.homogeneousComponent i p * q).IsHomogeneous (i + 1) :=
    (MvPolynomial.homogeneousComponent_isHomogeneous i p).mul hq
  rw [MvPolynomial.homogeneousComponent_of_mem hprod]
  simp

theorem homogeneousComponent_succ_mul_degreeOne
    {K : Type*} [Field K] {sigma : Type*}
    (p q : MvPolynomial sigma K) (hq : q.IsHomogeneous 1) (k : ℕ) :
    MvPolynomial.homogeneousComponent (k + 1) (p * q) =
      MvPolynomial.homogeneousComponent k p * q := by
  classical
  conv_lhs =>
    rw [← p.sum_homogeneousComponent]
  rw [Finset.sum_mul, map_sum]
  by_cases hk : k ∈ Finset.range (p.totalDegree + 1)
  · rw [Finset.sum_eq_single k]
    · have hprod :
          (MvPolynomial.homogeneousComponent k p * q).IsHomogeneous (k + 1) :=
        (MvPolynomial.homogeneousComponent_isHomogeneous k p).mul hq
      rw [MvPolynomial.homogeneousComponent_of_mem hprod, if_pos rfl]
    · intro i hi hik
      have hprod :
          (MvPolynomial.homogeneousComponent i p * q).IsHomogeneous (i + 1) :=
        (MvPolynomial.homogeneousComponent_isHomogeneous i p).mul hq
      rw [MvPolynomial.homogeneousComponent_of_mem hprod,
        if_neg (by omega)]
    · exact fun h ↦ (h hk).elim
  · have hpk : MvPolynomial.homogeneousComponent k p = 0 := by
      apply MvPolynomial.homogeneousComponent_eq_zero
      simpa only [Finset.mem_range, Nat.lt_add_one_iff, not_le] using hk
    rw [hpk, zero_mul]
    apply Finset.sum_eq_zero
    intro i hi
    have hik : i ≠ k := by
      intro h
      exact hk (h ▸ hi)
    have hprod :
        (MvPolynomial.homogeneousComponent i p * q).IsHomogeneous (i + 1) :=
      (MvPolynomial.homogeneousComponent_isHomogeneous i p).mul hq
    rw [MvPolynomial.homogeneousComponent_of_mem hprod,
      if_neg (by omega)]

theorem eq_homogeneousComponent_of_other_components_eq_zero
    {K : Type*} [Field K] {sigma : Type*}
    (p : MvPolynomial sigma K) (d : ℕ)
    (hzero : ∀ i : ℕ, i ≠ d →
      MvPolynomial.homogeneousComponent i p = 0) :
    p = MvPolynomial.homogeneousComponent d p := by
  classical
  by_cases hd : d ∈ Finset.range (p.totalDegree + 1)
  · calc
      p = ∑ i ∈ Finset.range (p.totalDegree + 1),
          MvPolynomial.homogeneousComponent i p := p.sum_homogeneousComponent.symm
      _ = MvPolynomial.homogeneousComponent d p := by
        apply Finset.sum_eq_single d
        · intro i hi hid
          exact hzero i hid
        · exact fun h ↦ (h hd).elim
  · have hdc : MvPolynomial.homogeneousComponent d p = 0 := by
      apply MvPolynomial.homogeneousComponent_eq_zero
      simpa only [Finset.mem_range, Nat.lt_add_one_iff, not_le] using hd
    have hpzero : p = 0 := by
      calc
        p = ∑ i ∈ Finset.range (p.totalDegree + 1),
            MvPolynomial.homogeneousComponent i p := p.sum_homogeneousComponent.symm
        _ = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          exact hzero i (fun hid ↦ hd (hid ▸ hi))
    rw [hpzero, map_zero]

theorem isHomogeneous_of_other_components_eq_zero
    {K : Type*} [Field K] {sigma : Type*}
    (p : MvPolynomial sigma K) (d : ℕ)
    (hzero : ∀ i : ℕ, i ≠ d →
      MvPolynomial.homogeneousComponent i p = 0) :
    p.IsHomogeneous d := by
  rw [eq_homogeneousComponent_of_other_components_eq_zero p d hzero]
  exact MvPolynomial.homogeneousComponent_isHomogeneous d p

end
end TranslatedDepthSeven

namespace TranslatedDepthSeven

/-- The trace-zero subspace of a quadratic extension in characteristic zero
is one-dimensional. -/
theorem trace_zero_vectors_proportional_quadratic
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [CharZero K] [FiniteDimensional K L]
    (hdim : Module.finrank K L = 2)
    {x y : L} (hx : x ≠ 0)
    (htrx : Algebra.trace K L x = 0)
    (htry : Algebra.trace K L y = 0) :
    ∃ c : K, y = c • x := by
  let tr : L →ₗ[K] K := Algebra.trace K L
  have hsurj : Function.Surjective tr := Algebra.trace_surjective K L
  have hrange : LinearMap.range tr = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hkerdim : Module.finrank K (LinearMap.ker tr) = 1 := by
    have hrank := tr.finrank_range_add_finrank_ker
    rw [hrange, finrank_top, Module.finrank_self, hdim] at hrank
    omega
  let x' : LinearMap.ker tr := ⟨x, htrx⟩
  let y' : LinearMap.ker tr := ⟨y, htry⟩
  have hx' : x' ≠ 0 := by
    intro h
    apply hx
    exact congrArg Subtype.val h
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' x' hx').mp hkerdim y'
  refine ⟨c, ?_⟩
  exact congrArg Subtype.val hc.symm

end TranslatedDepthSeven

/-
namespace TranslatedDepthSeven

open scoped nonZeroDivisors

attribute [local instance] MvPolynomial.gradedAlgebra

/-- In generic degree two, a nonzero trace-zero linear class has square in
the normalization ring, represented there by a homogeneous quadratic. -/
theorem exists_homogeneous_square_preimage_dead
    (K : Type*) [Field K] [CharZero K]
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
      Module.finrank (FractionRing B) L = 2)
    (p : MvPolynomial (Fin 13) K) (hp : p.IsHomogeneous 1)
    (hpnot : p ∉ I)
    (htrace :
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
      Algebra.trace (FractionRing B) L
        (algebraMap A L (Ideal.Quotient.mk I p)) = 0) :
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
    ∃ f : B, f.IsHomogeneous 2 ∧
      p ^ 2 - MvPolynomial.aeval D.forms f ∈ I ∧
      algebraMap B L f =
        (algebraMap A L (Ideal.Quotient.mk I p)) ^ 2 := by
  dsimp only
  dsimp only at htrace
  letI : I.IsPrime := hIprime
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin 13) K ⧸ I
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
  have hxne : x ≠ 0 := by
    intro hx
    apply hpnot
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply IsFractionRing.injective A L
    simpa only [map_zero] using hx
  have hxnonbase : ¬ ∃ k : KF, x = algebraMap KF L k := by
    rintro ⟨k, hk⟩
    have hkzero : k = 0 := by
      have hz := htrace
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
    rw [htrace, map_zero, zero_mul, sub_zero] at hCH
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
    rw [htrace, map_zero, zero_mul, sub_zero] at hCH
    linear_combination -hCH

end TranslatedDepthSeven
-/

namespace TranslatedDepthSeven

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Over an algebraically closed coefficient field, a nonconstant
degree-one class in a prime homogeneous quotient cannot have square equal
to a square in the homogeneous normalization.  This is the elementary
factorization which rules out a constant quadratic extension. -/
theorem not_associated_square_of_nonbase_linear_class
    (K : Type*) [Field K] [IsAlgClosed K]
    (I : Ideal (MvPolynomial (Fin 13) K))
    (hIprime : I.IsPrime)
    (D : HomogeneousLinearNormalizationData I)
    (p : MvPolynomial (Fin 13) K)
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
      rw [map_pow (MvPolynomial.C : K →+* MvPolynomial (Fin 13) K)]
      ring
    rw [hfactor, ← hevalf]
    exact hrelation
  rcases hIprime.mem_or_mem hproduct with hminus | hplus
  · exact hnobase (MvPolynomial.C s * r) (by
      simpa [R] using hminus)
  · exact hnobase (-(MvPolynomial.C s * r)) (by
      simpa [R] using hplus)

end TranslatedDepthSeven

/-
namespace TranslatedDepthSeven

open scoped nonZeroDivisors

attribute [local instance] MvPolynomial.gradedAlgebra

/-- In a quadratic generic fibre, the trace of a degree-one class is again
a degree-one polynomial in the homogeneous normalization parameters. -/
set_option maxHeartbeats 5000000 in
theorem exists_homogeneous_trace_preimage
    (K : Type*) [Field K]
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
      Module.finrank (FractionRing B) L = 2)
    (p : MvPolynomial (Fin 13) K) (hp : p.IsHomogeneous 1) :
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
    ∃ t : B, t.IsHomogeneous 1 ∧
      algebraMap B (FractionRing B) t =
        Algebra.trace (FractionRing B) L
          (algebraMap A L (Ideal.Quotient.mk I p)) := by
  dsimp only
  letI : I.IsPrime := hIprime
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin 13) K ⧸ I
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
    have hb₁ : D.hom b₁ = xA := by
      exact normalization_preimage_homogeneousComponent
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
      rw [hxB₁, ← IsScalarTower.algebraMap_apply B KF L b₁,
        Algebra.trace_algebraMap, hdim']
      simp [t]
  · have hnonbase : ∀ a b : B, b ≠ 0 →
        x ≠ algebraMap A L (D.hom a) / algebraMap A L (D.hom b) := by
      intro a b _hb hab
      apply hbase
      refine ⟨algebraMap B KF a / algebraMap B KF b, ?_⟩
      rw [hab]
      change algebraMap B L a / algebraMap B L b =
        algebraMap KF L (algebraMap B KF a / algebraMap B KF b)
      rw [← IsScalarTower.algebraMap_apply B KF L a,
        ← IsScalarTower.algebraMap_apply B KF L b, map_div₀]
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
      simp only [map_add, map_sub, map_mul, map_pow,
        HomogeneousLinearNormalizationData.hom]
      change x ^ 2 - algebraMap B L t * x + algebraMap B L n = 0
      rw [IsScalarTower.algebraMap_apply B KF L,
        IsScalarTower.algebraMap_apply B KF L, ht, hn]
      exact quadratic_cayley_trace_norm hdim' x
    have hhom := quadratic_relation_coefficients_homogeneous
      K I hIprime hIhomogeneous D p hp t n hrelation hnonbase
    exact ⟨t, hhom.1, ht⟩

end TranslatedDepthSeven

namespace TranslatedDepthSeven

open scoped nonZeroDivisors

attribute [local instance] MvPolynomial.gradedAlgebra

/-- In generic degree two, a nonzero trace-zero linear class has square in
the normalization ring, represented there by a homogeneous quadratic. -/
theorem exists_homogeneous_square_preimage
    (K : Type*) [Field K] [CharZero K]
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
      Module.finrank (FractionRing B) L = 2)
    (p : MvPolynomial (Fin 13) K) (hp : p.IsHomogeneous 1)
    (hpnot : p ∉ I)
    (htrace :
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
      Algebra.trace (FractionRing B) L
        (algebraMap A L (Ideal.Quotient.mk I p)) = 0) :
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
    ∃ f : B, f.IsHomogeneous 2 ∧
      p ^ 2 - MvPolynomial.aeval D.forms f ∈ I ∧
      algebraMap B L f =
        (algebraMap A L (Ideal.Quotient.mk I p)) ^ 2 := by
  dsimp only
  letI : I.IsPrime := hIprime
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin 13) K ⧸ I
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
  have hxne : x ≠ 0 := by
    intro hx
    apply hpnot
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply IsFractionRing.injective A L
    exact hx
  have hxnonbase : ¬ ∃ k : KF, x = algebraMap KF L k := by
    rintro ⟨k, hk⟩
    have hkzero : k = 0 := by
      have hz := htrace
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
    rw [htrace, map_zero, zero_mul, sub_zero] at hCH
    exact hCH
  have hrelation' : p ^ 2 - MvPolynomial.aeval D.forms 0 * p +
      MvPolynomial.aeval D.forms n ∈ I := by
    simpa using hrelation
  have hnHom : n.IsHomogeneous 2 :=
    (quadratic_relation_coefficients_homogeneous
      K I hIprime hIhomogeneous D p hp 0 n hrelation' hnonbase).2
  refine ⟨-n, hnHom.neg, ?_, ?_⟩
  · simpa using hrelation
  · rw [map_neg, hn, htrace]
    have hCH := quadratic_cayley_trace_norm hdim' x
    rw [htrace, map_zero, zero_mul, sub_zero] at hCH
    linear_combination -hCH

end TranslatedDepthSeven
-/


namespace TranslatedDepthSeven

attribute [local instance] MvPolynomial.gradedAlgebra

theorem quadratic_relation_coefficients_homogeneous
    (K : Type*) [Field K]
    (I : Ideal (MvPolynomial (Fin 13) K))
    (hIprime : I.IsPrime)
    (hIhomogeneous :
      I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 13) K))
    (D : HomogeneousLinearNormalizationData I)
    (p : MvPolynomial (Fin 13) K) (hp : p.IsHomogeneous 1)
    (t n : MvPolynomial (Fin D.parameterCount) K)
    (hrelation : p ^ 2 - MvPolynomial.aeval D.forms t * p +
        MvPolynomial.aeval D.forms n ∈ I)
    (hnonbase :
      let B := MvPolynomial (Fin D.parameterCount) K
      let A := MvPolynomial (Fin 13) K ⧸ I
      letI : Algebra B A := D.hom.toRingHom.toAlgebra
      ∀ a b : B, b ≠ 0 →
        algebraMap A (FractionRing A) (Ideal.Quotient.mk I p) ≠
          algebraMap A (FractionRing A) (D.hom a) /
            algebraMap A (FractionRing A) (D.hom b)) :
    t.IsHomogeneous 1 ∧ n.IsHomogeneous 2 := by
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin 13) K ⧸ I
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

end TranslatedDepthSeven

namespace TranslatedDepthSeven

theorem normalization_genericRank_le_projectiveDegree_fourfold_field
    (K : Type*) [Field K]
    (I : Ideal (MvPolynomial (Fin 13) K))
    (D : HomogeneousLinearNormalizationData I)
    (hparameterCount : D.parameterCount = 5)
    {d : ℕ}
    (hprojective : Published.HasProjectiveDimensionDegree I 4 d) :
    let B := MvPolynomial (Fin D.parameterCount) K
    let A := MvPolynomial (Fin 13) K ⧸ I
    let g := D.hom
    letI : Algebra B A := g.toRingHom.toAlgebra
    Module.finrank (FractionRing B)
      (LocalizedModule (nonZeroDivisors B) A) ≤ d := by
  dsimp only
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin 13) K ⧸ I
  let g := D.hom
  letI : Algebra B A := g.toRingHom.toAlgebra
  obtain ⟨E, hlower⟩ :=
    exists_genericRank_lower_homogeneous_normalizationData
      K (Fin 13) I D (hparameterCount ▸ by omega)
  rcases hprojective with
    ⟨_hdimension, _hpositive, P, hPdegree, hPleading, k₀, hPeventual⟩
  apply multiplicity_le_of_shifted_homogeneousHilbert_lower
    P d (Module.finrank (FractionRing B)
      (LocalizedModule (nonZeroDivisors B) A)) E k₀ hPdegree hPleading
  intro n hn
  have hnE : k₀ ≤ n + E := hn.trans (Nat.le_add_right n E)
  have hvalue := hPeventual (n + E) hnE
  have hvalue' :
      (Module.finrank K
        (quotientHomogeneousComponent K (Fin 13) I (n + E)) : ℚ) =
          P.eval ((n + E : ℕ) : ℚ) := by
    simpa only [Published.projectiveHilbertPiece,
      quotientHomogeneousComponent] using hvalue
  have hlower' := hlower n
  have hchoose : (D.parameterCount + n - 1).choose n =
      (n + 4).choose 4 := by
    rw [hparameterCount, show 5 + n - 1 = n + 4 by omega]
    exact Nat.choose_symm (by omega : 4 ≤ n + 4)
  rw [hchoose] at hlower'
  have hlowerQ :
      ((Module.finrank (FractionRing B)
          (LocalizedModule (nonZeroDivisors B) A)) *
        (n + 4).choose 4 : ℕ) ≤
        (Module.finrank K
          (quotientHomogeneousComponent K (Fin 13) I (n + E)) : ℚ) := by
    exact_mod_cast hlower'
  rw [hvalue'] at hlowerQ
  exact hlowerQ

end TranslatedDepthSeven


namespace TranslatedDepthSeven

attribute [local instance] MvPolynomial.gradedAlgebra

/-- If a homogeneous quotient class belongs to a homogeneous linear
normalization, its normalization preimage may be replaced by its matching
homogeneous component. -/
theorem normalization_preimage_homogeneousComponent
    (K : Type*) [Field K] {sigma : Type*}
    (I : Ideal (MvPolynomial sigma K))
    (hIhomogeneous :
      I.IsHomogeneous (MvPolynomial.homogeneousSubmodule sigma K))
    (D : HomogeneousLinearNormalizationData I)
    (q : MvPolynomial sigma K) (d : ℕ) (hq : q.IsHomogeneous d)
    (r : MvPolynomial (Fin D.parameterCount) K)
    (heq : D.hom r = Ideal.Quotient.mk I q) :
    D.hom (MvPolynomial.homogeneousComponent d r) =
      Ideal.Quotient.mk I q := by
  have hrel : MvPolynomial.aeval D.forms r - q ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa [HomogeneousLinearNormalizationData.hom, map_sub] using
      sub_eq_zero.mpr heq
  have hcomponent := hIhomogeneous d hrel
  rw [← DirectSum.Decomposition.decompose'_eq,
    MvPolynomial.decomposition.decompose'_apply] at hcomponent
  simp only [map_sub,
    homogeneousComponent_aeval_degreeOne D.forms
      D.forms_isHomogeneous,
    MvPolynomial.homogeneousComponent_of_mem hq]
    at hcomponent
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hcomponent
  simpa [HomogeneousLinearNormalizationData.hom, map_sub] using
    sub_eq_zero.mp hcomponent

end TranslatedDepthSeven


namespace TranslatedDepthSeven

open scoped nonZeroDivisors

universe u

theorem localizedModule_finrank_eq_fractionRing_finrank
    {B A : Type u} [CommRing B] [IsDomain B]
    [CommRing A] [IsDomain A] [Algebra B A]
    [FaithfulSMul B A] [Module.Finite B A] :
    letI : Algebra (FractionRing B) (FractionRing A) :=
      FractionRing.liftAlgebra B (FractionRing A)
    Module.finrank (FractionRing B)
        (LocalizedModule (nonZeroDivisors B) A) =
      Module.finrank (FractionRing B) (FractionRing A) := by
  letI : Algebra (FractionRing B) (FractionRing A) :=
    FractionRing.liftAlgebra B (FractionRing A)
  letI : IsScalarTower B (FractionRing B) (FractionRing A) :=
    FractionRing.isScalarTower_liftAlgebra B (FractionRing A)
  have hG : Module.rank (FractionRing B)
      (LocalizedModule (nonZeroDivisors B) A) = Module.rank B A := by
    rw [IsLocalization.rank_eq (FractionRing B)
      (nonZeroDivisors B) le_rfl]
    exact IsLocalizedModule.rank_eq (R := B) (M := A)
      (N := LocalizedModule (nonZeroDivisors B) A)
      (nonZeroDivisors B) le_rfl
      (LocalizedModule.mkLinearMap (nonZeroDivisors B) A)
  have hL : Module.rank (FractionRing B) (FractionRing A) =
      Module.rank B A := by
    exact Algebra.IsAlgebraic.rank_fractionRing B A
  exact congrArg Cardinal.toNat (hG.trans hL.symm)

end TranslatedDepthSeven


namespace TranslatedDepthSeven

theorem quadratic_cayley_trace_norm
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (hdim : Module.finrank K L = 2) (x : L) :
    x ^ 2 - algebraMap K L (Algebra.trace K L x) * x +
      algebraMap K L (Algebra.norm K x) = 0 := by
  let b : Module.Basis (Fin 2) K L :=
    Module.finBasisOfFinrankEq K L hdim
  let f : Module.End K L := Algebra.lmul K L x
  let M : Matrix (Fin 2) (Fin 2) K := Algebra.leftMulMatrix b x
  have hM : M = LinearMap.toMatrix b b f := rfl
  have hcharM : M.charpoly =
      Polynomial.X ^ 2 - Polynomial.C M.trace * Polynomial.X +
        Polynomial.C M.det := Matrix.charpoly_fin_two M
  have hchar : f.charpoly =
      Polynomial.X ^ 2 - Polynomial.C (Algebra.trace K L x) * Polynomial.X +
        Polynomial.C (Algebra.norm K x) := by
    rw [← LinearMap.charpoly_toMatrix f b]
    rw [← hM, hcharM]
    rw [Algebra.trace_eq_matrix_trace b x,
      Algebra.norm_eq_matrix_det b x]
  have hCH := LinearMap.aeval_self_charpoly f
  rw [hchar] at hCH
  have happly := LinearMap.congr_fun hCH (1 : L)
  have hpow : (f ^ 2) (1 : L) = x ^ 2 := by
    change x * (x * 1) = x ^ 2
    simp [pow_two]
  simp only [map_add, map_sub, map_mul, map_pow,
    Polynomial.aeval_X, Polynomial.aeval_C] at happly
  rw [LinearMap.add_apply, LinearMap.sub_apply,
    Module.End.mul_apply] at happly
  rw [hpow] at happly
  simpa [f, map_add, map_sub, map_mul, map_pow,
    Algebra.smul_def] using happly

end TranslatedDepthSeven

namespace TranslatedDepthSeven

open scoped nonZeroDivisors

attribute [local instance] MvPolynomial.gradedAlgebra

/-- In a quadratic generic fibre, the trace of a degree-one class is again
a degree-one polynomial in the homogeneous normalization parameters. -/
theorem exists_homogeneous_trace_preimage
    (K : Type*) [Field K]
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
      Module.finrank (FractionRing B) L = 2)
    (p : MvPolynomial (Fin 13) K) (hp : p.IsHomogeneous 1) :
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
    ∃ t : B, t.IsHomogeneous 1 ∧
      algebraMap B (FractionRing B) t =
        Algebra.trace (FractionRing B) L
          (algebraMap A L (Ideal.Quotient.mk I p)) := by
  dsimp only
  letI : I.IsPrime := hIprime
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin 13) K ⧸ I
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

end TranslatedDepthSeven

namespace TranslatedDepthSeven

open scoped nonZeroDivisors

attribute [local instance] MvPolynomial.gradedAlgebra

/-- In generic degree two, a nonzero trace-zero linear class has square in
the normalization ring, represented there by a homogeneous quadratic. -/
theorem exists_homogeneous_square_preimage_live
    (K : Type*) [Field K] [CharZero K]
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
      Module.finrank (FractionRing B) L = 2)
    (p : MvPolynomial (Fin 13) K) (hp : p.IsHomogeneous 1)
    (hpnot : p ∉ I)
    (htrace :
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
      Algebra.trace (FractionRing B) L
        (algebraMap A L (Ideal.Quotient.mk I p)) = 0) :
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
    ∃ f : B, f.IsHomogeneous 2 ∧
      p ^ 2 - MvPolynomial.aeval D.forms f ∈ I ∧
      algebraMap B L f =
        (algebraMap A L (Ideal.Quotient.mk I p)) ^ 2 := by
  dsimp only
  dsimp only at htrace
  letI : I.IsPrime := hIprime
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin 13) K ⧸ I
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

end TranslatedDepthSeven

namespace TranslatedDepthSeven

open scoped nonZeroDivisors

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Over an algebraically closed field, two homogeneous linear classes of
trace zero in a quadratic homogeneous normalization are proportional over
the coefficient field. -/
theorem trace_zero_linear_classes_proportional
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
      Module.finrank (FractionRing B) L = 2)
    (p q : MvPolynomial (Fin 13) K)
    (hp : p.IsHomogeneous 1) (hq : q.IsHomogeneous 1)
    (hpnot : p ∉ I)
    (htracep :
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
      Algebra.trace (FractionRing B) L
        (algebraMap A L (Ideal.Quotient.mk I p)) = 0)
    (htraceq :
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
      Algebra.trace (FractionRing B) L
        (algebraMap A L (Ideal.Quotient.mk I q)) = 0) :
    ∃ c : K, Ideal.Quotient.mk I q = c • Ideal.Quotient.mk I p := by
  dsimp only at htracep htraceq hdim
  letI : I.IsPrime := hIprime
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin 13) K ⧸ I
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

end TranslatedDepthSeven

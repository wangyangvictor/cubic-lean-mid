import TranslatedDepthSeven.StandardGradedQuotientFiltration
import TranslatedDepthSeven.TruncatedPolynomialJets

/-!
# Generic-rank degree in an arbitrary number of linear parameters

This is the parameter-count-uniform form of the three-parameter argument in
`StandardGradedQuotientFiltration`.  A finite injective normalization by
degree-one forms squeezes the cumulative Hilbert function between the generic
rank times two shifted polynomial-ring counts.  The degree is therefore the
literal generic rank, with no Hilbert--Serre theorem hidden in the statement.
-/

namespace TranslatedDepthSeven

noncomputable section

set_option synthInstance.maxHeartbeats 200000

universe u v

open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem homogeneousComponent_aeval_degreeOne_fin
    {K : Type u} [Field K] {sigma : Type v} {tau : Type*}
    (ell : sigma → MvPolynomial tau K)
    (hell : ∀ i, (ell i).IsHomogeneous 1)
    (f : MvPolynomial sigma K) (k : ℕ) :
    MvPolynomial.homogeneousComponent k (MvPolynomial.aeval ell f) =
      MvPolynomial.aeval ell (MvPolynomial.homogeneousComponent k f) := by
  classical
  conv_lhs =>
    rw [← f.sum_homogeneousComponent]
    simp only [map_sum]
  by_cases hk : k ∈ Finset.range (f.totalDegree + 1)
  · rw [Finset.sum_eq_single k]
    · have hh : (MvPolynomial.aeval ell
          (MvPolynomial.homogeneousComponent k f)).IsHomogeneous k := by
        simpa using
          (MvPolynomial.homogeneousComponent_isHomogeneous k f).aeval ell hell
      rw [MvPolynomial.homogeneousComponent_of_mem hh]
      simp
    · intro j hj hjk
      have hh : (MvPolynomial.aeval ell
          (MvPolynomial.homogeneousComponent j f)).IsHomogeneous j := by
        simpa using
          (MvPolynomial.homogeneousComponent_isHomogeneous j f).aeval ell hell
      rw [MvPolynomial.homogeneousComponent_of_mem hh]
      simp [Ne.symm hjk]
    · exact fun h ↦ (h hk).elim
  · have hfk : MvPolynomial.homogeneousComponent k f = 0 := by
      apply MvPolynomial.homogeneousComponent_eq_zero
      simpa only [Finset.mem_range, Nat.lt_add_one_iff, not_le] using hk
    rw [hfk, map_zero]
    apply Finset.sum_eq_zero
    intro j hj
    have hjk : j ≠ k := by
      intro h
      exact hk (h ▸ hj)
    have hh : (MvPolynomial.aeval ell
        (MvPolynomial.homogeneousComponent j f)).IsHomogeneous j := by
      simpa using
        (MvPolynomial.homogeneousComponent_isHomogeneous j f).aeval ell hell
    rw [MvPolynomial.homogeneousComponent_of_mem hh]
    simp [Ne.symm hjk]

/-- Linear normalization by an arbitrary finite number of degree-one forms. -/
def linearNormalizationHomFin
    (K : Type u) [Field K] (sigma : Type v)
    (I : Ideal (MvPolynomial sigma K)) {r : ℕ}
    (ell : Fin r → MvPolynomial sigma K) :
    MvPolynomial (Fin r) K →ₐ[K] (MvPolynomial sigma K ⧸ I) :=
  (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval ell)

@[simp]
theorem linearNormalizationHomFin_apply
    (K : Type u) [Field K] (sigma : Type v)
    (I : Ideal (MvPolynomial sigma K)) {r : ℕ}
    (ell : Fin r → MvPolynomial sigma K)
    (f : MvPolynomial (Fin r) K) :
    linearNormalizationHomFin K sigma I ell f =
      Ideal.Quotient.mk I (MvPolynomial.aeval ell f) := rfl

/-- Substitution by degree-one forms preserves homogeneous degree. -/
theorem linearNormalizationHomFin_mem_homogeneousComponent
    (K : Type u) [Field K] (sigma : Type v)
    (I : Ideal (MvPolynomial sigma K)) {r : ℕ}
    (ell : Fin r → MvPolynomial sigma K)
    (hell : ∀ i, (ell i).IsHomogeneous 1)
    {n : ℕ} {f : MvPolynomial (Fin r) K}
    (hf : f.IsHomogeneous n) :
    linearNormalizationHomFin K sigma I ell f ∈
      quotientHomogeneousComponent K sigma I n := by
  apply Submodule.mem_map.mpr
  refine ⟨MvPolynomial.aeval ell f, ?_, rfl⟩
  simpa only [one_mul] using hf.aeval ell hell

/-- Homogeneous projection commutes with a linear normalization. -/
theorem quotientDecomposeLinearMap_linearNormalizationHomFin_apply
    (K : Type u) [Field K] (sigma : Type v)
    (I : Ideal (MvPolynomial sigma K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule sigma K))
    {r : ℕ} (ell : Fin r → MvPolynomial sigma K)
    (hell : ∀ i, (ell i).IsHomogeneous 1)
    (f : MvPolynomial (Fin r) K) (n : ℕ) :
    ((quotientDecomposeLinearMap K sigma I hI
        (linearNormalizationHomFin K sigma I ell f)) n :
      MvPolynomial sigma K ⧸ I) =
        linearNormalizationHomFin K sigma I ell
          (MvPolynomial.homogeneousComponent n f) := by
  rw [linearNormalizationHomFin_apply,
    quotientDecomposeLinearMap_mk_apply,
    homogeneousComponent_aeval_degreeOne_fin ell hell]
  rfl

/-- The degree-`k+E` piece of a product with a homogeneous vector only sees
the degree-`k` piece of the normalized coefficient. -/
theorem quotientDecomposeLinearMap_linearNormalizationHomFin_mul_apply
    (K : Type u) [Field K] (sigma : Type v)
    (I : Ideal (MvPolynomial sigma K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule sigma K))
    {r : ℕ} (ell : Fin r → MvPolynomial sigma K)
    (hell : ∀ i, (ell i).IsHomogeneous 1)
    (f : MvPolynomial (Fin r) K) {E : ℕ}
    {x : MvPolynomial sigma K ⧸ I}
    (hx : x ∈ quotientHomogeneousComponent K sigma I E) (k : ℕ) :
    ((quotientDecomposeLinearMap K sigma I hI
        (linearNormalizationHomFin K sigma I ell f * x)) (k + E) :
      MvPolynomial sigma K ⧸ I) =
        linearNormalizationHomFin K sigma I ell
          (MvPolynomial.homogeneousComponent k f) * x := by
  let Q := fun n ↦ quotientHomogeneousComponent K sigma I n
  letI : GradedAlgebra Q := quotientGradedAlgebra K sigma I hI
  change ((DirectSum.decompose Q
      (linearNormalizationHomFin K sigma I ell f * x) (k + E) : Q (k + E)) :
        MvPolynomial sigma K ⧸ I) = _
  rw [DirectSum.coe_decompose_mul_add_of_right_mem Q hx]
  change ((quotientDecomposeLinearMap K sigma I hI
      (linearNormalizationHomFin K sigma I ell f)) k :
        MvPolynomial sigma K ⧸ I) * x = _
  rw [quotientDecomposeLinearMap_linearNormalizationHomFin_apply
    K sigma I hI ell hell]

/-- The generic normalization preserves cumulative degree. -/
theorem linearNormalizationHomFin_mem_quotientTotalDegreeFiltration
    (K : Type u) [Field K] (sigma : Type v)
    (I : Ideal (MvPolynomial sigma K)) {r : ℕ}
    (ell : Fin r → MvPolynomial sigma K)
    (hell : ∀ i, (ell i).IsHomogeneous 1)
    {n : ℕ} {f : MvPolynomial (Fin r) K}
    (hf : f.totalDegree ≤ n) :
    linearNormalizationHomFin K sigma I ell f ∈
      quotientTotalDegreeFiltration K sigma I n := by
  rw [quotientTotalDegreeFiltration_eq_iSup_homogeneousComponent]
  rw [← MvPolynomial.sum_homogeneousComponent f, map_sum]
  apply Submodule.sum_mem
  intro k hk
  apply le_iSup
      (fun j : {j : ℕ // j ≤ n} ↦
        quotientHomogeneousComponent K sigma I j.1)
      ⟨k, (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)).trans hf⟩
  exact linearNormalizationHomFin_mem_homogeneousComponent
    K sigma I ell hell (MvPolynomial.homogeneousComponent_mem k f)

/-- Every quotient filtration piece is no larger than the polynomial-ring
piece in the same number of parameters. -/
theorem finrank_quotientTotalDegreeFiltration_fin_le
    (K : Type u) [Field K] (r : ℕ)
    (I : Ideal (MvPolynomial (Fin r) K)) (n : ℕ) :
    Module.finrank K (quotientTotalDegreeFiltration K (Fin r) I n) ≤
      (n + r).choose r := by
  calc
    Module.finrank K (quotientTotalDegreeFiltration K (Fin r) I n) ≤
        Module.finrank K (MvPolynomial.restrictTotalDegree (Fin r) K n) :=
      Submodule.finrank_map_le _ _
    _ = (n + r).choose r :=
      finrank_mvPolynomial_restrictTotalDegree_fin K r n

/-- Equal-degree strictness for an arbitrary number of normalization
parameters. -/
theorem equalDegree_coefficients_mem_restrictTotalDegree_fin
    (K : Type u) [Field K] (sigma : Type v)
    (I : Ideal (MvPolynomial sigma K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule sigma K))
    {r : ℕ} (ell : Fin r → MvPolynomial sigma K)
    (hell : ∀ i, (ell i).IsHomogeneous 1)
    {delta E N : ℕ}
    (x : Fin delta → MvPolynomial sigma K ⧸ I)
    (hxHom : ∀ i, x i ∈ quotientHomogeneousComponent K sigma I E)
    (hxLI :
      let B := MvPolynomial (Fin r) K
      let A := MvPolynomial sigma K ⧸ I
      let g := linearNormalizationHomFin K sigma I ell
      letI : Algebra B A := g.toRingHom.toAlgebra
      LinearIndependent B x)
    (b : Fin delta → MvPolynomial (Fin r) K)
    (hsum :
      ∑ i, linearNormalizationHomFin K sigma I ell (b i) * x i ∈
        quotientTotalDegreeFiltration K sigma I N) :
    ∀ i, b i ∈ MvPolynomial.restrictTotalDegree (Fin r) K N := by
  let B := MvPolynomial (Fin r) K
  let A := MvPolynomial sigma K ⧸ I
  let g := linearNormalizationHomFin K sigma I ell
  letI : Algebra B A := g.toRingHom.toAlgebra
  have hcomponent (k : ℕ) (hNk : N < k) :
      ∀ i, MvPolynomial.homogeneousComponent k (b i) = 0 := by
    have hzero := quotientDecomposeLinearMap_eq_zero_of_mem_filtration
      K sigma I hI hsum (hNk.trans_le (Nat.le_add_right k E))
    rw [map_sum] at hzero
    rw [DFinsupp.finset_sum_apply] at hzero
    change (quotientHomogeneousComponent K sigma I (k + E)).subtype
      (∑ a, (quotientDecomposeLinearMap K sigma I hI
        (g (b a) * x a)) (k + E)) = 0 at hzero
    rw [map_sum] at hzero
    have hzero' :
        ∑ i, g (MvPolynomial.homogeneousComponent k (b i)) * x i = 0 := by
      calc
        ∑ i, g (MvPolynomial.homogeneousComponent k (b i)) * x i =
            ∑ i, ((quotientDecomposeLinearMap K sigma I hI
              (g (b i) * x i)) (k + E) : A) := by
              apply Finset.sum_congr rfl
              intro i _
              exact
                (quotientDecomposeLinearMap_linearNormalizationHomFin_mul_apply
                  K sigma I hI ell hell (b i) (hxHom i) k).symm
        _ = 0 := hzero
    have hrelation :
        ∑ i, MvPolynomial.homogeneousComponent k (b i) • x i = 0 := by
      simpa only [Algebra.smul_def] using hzero'
    exact Fintype.linearIndependent_iff.mp hxLI _ hrelation
  intro i
  rw [restrictTotalDegree_eq_iSup_homogeneousSubmodule]
  rw [← MvPolynomial.sum_homogeneousComponent (b i)]
  apply Submodule.sum_mem
  intro k hk
  by_cases hkN : k ≤ N
  · apply le_iSup
      (fun j : {j : ℕ // j ≤ N} ↦
        MvPolynomial.homogeneousSubmodule (Fin r) K j.1)
      ⟨k, hkN⟩
    exact MvPolynomial.homogeneousComponent_mem k (b i)
  · rw [hcomponent k (lt_of_not_ge hkN) i]
    exact Submodule.zero_mem _

/-- Lower generic-rank bound by shifted binomial coefficients. -/
theorem equalDegree_genericRank_lower_binomial_fin
    (K : Type u) [Field K] (sigma : Type v) [Finite sigma]
    (I : Ideal (MvPolynomial sigma K))
    {r : ℕ} (ell : Fin r → MvPolynomial sigma K)
    (hell : ∀ i, (ell i).IsHomogeneous 1)
    {delta E : ℕ}
    (x : Fin delta → MvPolynomial sigma K ⧸ I)
    (hxHom : ∀ i, x i ∈ quotientHomogeneousComponent K sigma I E)
    (hxLI :
      let B := MvPolynomial (Fin r) K
      let A := MvPolynomial sigma K ⧸ I
      let g := linearNormalizationHomFin K sigma I ell
      letI : Algebra B A := g.toRingHom.toAlgebra
      LinearIndependent B x)
    (n : ℕ) :
    delta * (n + r).choose r ≤
      Module.finrank K
        (quotientTotalDegreeFiltration K sigma I (n + E)) := by
  let B := MvPolynomial (Fin r) K
  let A := MvPolynomial sigma K ⧸ I
  let g := linearNormalizationHomFin K sigma I ell
  let P := MvPolynomial.restrictTotalDegree (Fin r) K n
  let F := quotientTotalDegreeFiltration K sigma I (n + E)
  letI : Algebra B A := g.toRingHom.toAlgebra
  let L : (Fin delta → P) →ₗ[K] F :=
    { toFun := fun b ↦ ⟨∑ i, g (b i) * x i, by
        apply Submodule.sum_mem
        intro i _
        apply mul_mem_quotientTotalDegreeFiltration K sigma I
        · apply linearNormalizationHomFin_mem_quotientTotalDegreeFiltration
            K sigma I ell hell
          have hb := (b i).2
          change (b i : B) ∈
            MvPolynomial.restrictTotalDegree (Fin r) K n at hb
          exact (MvPolynomial.mem_restrictTotalDegree
            (Fin r) n (b i : B)).mp hb
        · exact quotientHomogeneousComponent_le_filtration
            K sigma I E (hxHom i)⟩
      map_add' := by
        intro b c
        apply Subtype.ext
        change ∑ i, g ((b i : B) + (c i : B)) * x i =
          (∑ i, g (b i) * x i) + ∑ i, g (c i) * x i
        simp only [map_add, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a b
        apply Subtype.ext
        change ∑ i, g (a • (b i : B)) * x i =
          a • ∑ i, g (b i) * x i
        simp only [map_smul, smul_mul_assoc, Finset.smul_sum] }
  have hLinj : Function.Injective L := by
    intro b c hbc
    have hsum : ∑ i, g (b i) * x i = ∑ i, g (c i) * x i := by
      exact congrArg Subtype.val hbc
    have hrelation : ∑ i, ((b i : B) - (c i : B)) • x i = 0 := by
      change ∑ i, g ((b i : B) - (c i : B)) * x i = 0
      simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr hsum
    have hcoeff := Fintype.linearIndependent_iff.mp hxLI _ hrelation
    funext i
    apply Subtype.ext
    exact sub_eq_zero.mp (hcoeff i)
  have hfin := L.finrank_le_finrank_of_injective hLinj
  rw [Module.finrank_pi_fintype K] at hfin
  dsimp only [P, F] at hfin
  simpa [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    finrank_mvPolynomial_restrictTotalDegree_fin K r n] using hfin

/-- Upper generic-rank bound after clearing one denominator. -/
theorem equalDegree_genericRank_upper_binomial_fin
    (K : Type u) [Field K] (sigma : Type v) [Finite sigma]
    (I : Ideal (MvPolynomial sigma K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule sigma K))
    (hprime : I.IsPrime)
    {r : ℕ} (ell : Fin r → MvPolynomial sigma K)
    (hell : ∀ i, (ell i).IsHomogeneous 1)
    (hinjective : Function.Injective
      (linearNormalizationHomFin K sigma I ell))
    {delta E : ℕ}
    (x : Fin delta → MvPolynomial sigma K ⧸ I)
    (hxHom : ∀ i, x i ∈ quotientHomogeneousComponent K sigma I E)
    (hxLI :
      let B := MvPolynomial (Fin r) K
      let A := MvPolynomial sigma K ⧸ I
      let g := linearNormalizationHomFin K sigma I ell
      letI : Algebra B A := g.toRingHom.toAlgebra
      LinearIndependent B x)
    (d : MvPolynomial (Fin r) K) (hd : d ≠ 0)
    (hclear :
      let B := MvPolynomial (Fin r) K
      let A := MvPolynomial sigma K ⧸ I
      let g := linearNormalizationHomFin K sigma I ell
      letI : Algebra B A := g.toRingHom.toAlgebra
      ∀ a : A, d • a ∈ Submodule.span B (Set.range x))
    (n : ℕ) :
    Module.finrank K (quotientTotalDegreeFiltration K sigma I n) ≤
      delta * (n + d.totalDegree + r).choose r := by
  let B := MvPolynomial (Fin r) K
  let A := MvPolynomial sigma K ⧸ I
  let g := linearNormalizationHomFin K sigma I ell
  let F := quotientTotalDegreeFiltration K sigma I n
  let c := d.totalDegree + n
  let P := MvPolynomial.restrictTotalDegree (Fin r) K c
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : IsDomain A :=
    (Ideal.Quotient.isDomain_iff_prime (I := I)).mpr hprime
  let S := Submodule.span B (Set.range x)
  let D : F →ₗ[K] S :=
    { toFun := fun a ↦ ⟨d • (a : A), by
          change d • (a : A) ∈ Submodule.span B (Set.range x)
          exact hclear (a : A)⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        simp only [Submodule.coe_add, smul_add]
      map_smul' := by
        intro a b
        apply Subtype.ext
        change g d * (a • (b : A)) = a • (g d * (b : A))
        simp only [Algebra.smul_def]
        ring }
  let R : S →ₗ[K] (Fin delta → B) :=
    ((Finsupp.linearEquivFunOnFinite B B (Fin delta)).toLinearMap.restrictScalars K).comp
      (hxLI.repr.restrictScalars K)
  let C : F →ₗ[K] (Fin delta → B) := R.comp D
  have hC_mem (a : F) (i : Fin delta) : C a i ∈ P := by
    have hrecomb0 := hxLI.linearCombination_repr (D a)
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_fintype _ _ (by simp)] at hrecomb0
    have hrecomb : ∑ i, g (C a i) * x i = (D a : A) := by
      simpa only [C, R, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
        LinearEquiv.coe_coe, Finsupp.linearEquivFunOnFinite_apply,
        Algebra.smul_def] using hrecomb0
    have hDa : (D a : A) ∈ quotientTotalDegreeFiltration K sigma I c := by
      apply mul_mem_quotientTotalDegreeFiltration K sigma I
      · apply linearNormalizationHomFin_mem_quotientTotalDegreeFiltration
          K sigma I ell hell
        exact le_rfl
      · exact a.2
    have hsum : ∑ i, g (C a i) * x i ∈
        quotientTotalDegreeFiltration K sigma I c := by
      rw [hrecomb]
      exact hDa
    exact equalDegree_coefficients_mem_restrictTotalDegree_fin
      K sigma I hI ell hell x hxHom hxLI (C a) hsum i
  let U : F →ₗ[K] (Fin delta → P) :=
    { toFun := fun a i ↦ ⟨C a i, hC_mem a i⟩
      map_add' := by
        intro a b
        funext i
        apply Subtype.ext
        exact congrFun (C.map_add a b) i
      map_smul' := by
        intro a b
        funext i
        apply Subtype.ext
        exact congrFun (C.map_smul a b) i }
  have hDinj : Function.Injective D := by
    intro a b hab
    apply Subtype.ext
    apply mul_left_cancel₀ (hinjective.ne hd)
    exact congrArg Subtype.val hab
  have hRinj : Function.Injective R := by
    intro y z hyz
    apply (LinearMap.ker_eq_bot.mp hxLI.repr_ker)
    apply (Finsupp.linearEquivFunOnFinite B B (Fin delta)).injective
    exact hyz
  have hUinj : Function.Injective U := by
    intro a b hab
    apply hDinj
    apply hRinj
    apply funext
    intro i
    exact congrArg Subtype.val (congrFun hab i)
  have hfin := U.finrank_le_finrank_of_injective hUinj
  rw [Module.finrank_pi_fintype K] at hfin
  dsimp only [F, P, c] at hfin
  simpa [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    finrank_mvPolynomial_restrictTotalDegree_fin K r
      (d.totalDegree + n), Nat.add_comm n d.totalDegree,
    Nat.add_assoc] using hfin

/-- A finite degree-one normalization has a finite homogeneous spanning
family, in any parameter count. -/
theorem exists_homogeneous_generators_of_finite_linearNormalization_fin
    (K : Type u) [Field K] (sigma : Type v) [Finite sigma]
    (I : Ideal (MvPolynomial sigma K)) {r : ℕ}
    (ell : Fin r → MvPolynomial sigma K)
    (hfinite : (linearNormalizationHomFin K sigma I ell).Finite) :
    let B := MvPolynomial (Fin r) K
    let A := MvPolynomial sigma K ⧸ I
    let g := linearNormalizationHomFin K sigma I ell
    letI : Algebra B A := g.toRingHom.toAlgebra
    ∃ N : ℕ, ∃ t : Fin N → A, ∃ degree : Fin N → ℕ,
      (∀ i, t i ∈ quotientHomogeneousComponent K sigma I (degree i)) ∧
      Submodule.span B (Set.range t) = ⊤ := by
  dsimp only
  let B := MvPolynomial (Fin r) K
  let A := MvPolynomial sigma K ⧸ I
  let g := linearNormalizationHomFin K sigma I ell
  letI : Algebra B A := g.toRingHom.toAlgebra
  haveI : Module.Finite B A := hfinite
  obtain ⟨M, s, hs⟩ := Module.Finite.exists_fin (R := B) (M := A)
  choose f hf using fun i : Fin M ↦ Ideal.Quotient.mk_surjective (s i)
  let D : ℕ := Finset.univ.sup fun i : Fin M ↦ (f i).totalDegree
  let index := Fin M × Fin (D + 1)
  let t0 : index → A := fun ik ↦
    Ideal.Quotient.mk I (MvPolynomial.homogeneousComponent ik.2.1 (f ik.1))
  let degree0 : index → ℕ := fun ik ↦ ik.2.1
  have ht0Hom (ik : index) :
      t0 ik ∈ quotientHomogeneousComponent K sigma I (degree0 ik) := by
    apply Submodule.mem_map.mpr
    exact ⟨MvPolynomial.homogeneousComponent ik.2.1 (f ik.1),
      MvPolynomial.homogeneousComponent_mem ik.2.1 (f ik.1), rfl⟩
  have ht0Span : Submodule.span B (Set.range t0) = ⊤ := by
    apply top_unique
    rw [← hs, Submodule.span_le]
    rintro a ⟨i, rfl⟩
    rw [← hf i, ← MvPolynomial.sum_homogeneousComponent (f i), map_sum]
    apply Submodule.sum_mem
    intro k hk
    apply Submodule.subset_span
    have hiD : (f i).totalDegree ≤ D := by
      exact Finset.le_sup (f := fun j : Fin M ↦ (f j).totalDegree)
        (Finset.mem_univ i)
    let k' : Fin (D + 1) := ⟨k,
      Nat.lt_succ_iff.mpr
        ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)).trans hiD)⟩
    exact ⟨(i, k'), rfl⟩
  let e := Fintype.equivFin index
  let t : Fin (Fintype.card index) → A := fun i ↦ t0 (e.symm i)
  let degree : Fin (Fintype.card index) → ℕ :=
    fun i ↦ degree0 (e.symm i)
  refine ⟨Fintype.card index, t, degree, ?_, ?_⟩
  · intro i
    exact ht0Hom (e.symm i)
  · have hrange : Set.range t = Set.range t0 := by
      apply Set.ext
      intro a
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e.symm i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨e i, by simp only [t, Equiv.symm_apply_apply]⟩
    rw [hrange]
    exact ht0Span

/-- The generic-rank lattice can be chosen in one homogeneous degree. -/
theorem exists_equalDegree_genericRank_lattice_sandwich_fin
    (K : Type u) [Field K] (sigma : Type v) [Finite sigma]
    (I : Ideal (MvPolynomial sigma K)) {r : ℕ} [NeZero r]
    (ell : Fin r → MvPolynomial sigma K)
    (hell : ∀ i, (ell i).IsHomogeneous 1)
    (hfinite : (linearNormalizationHomFin K sigma I ell).Finite) :
    let B := MvPolynomial (Fin r) K
    let A := MvPolynomial sigma K ⧸ I
    let g := linearNormalizationHomFin K sigma I ell
    letI : Algebra B A := g.toRingHom.toAlgebra
    ∀ {N : ℕ} (t : Fin N → A) (degree : Fin N → ℕ),
      (∀ i, t i ∈ quotientHomogeneousComponent K sigma I (degree i)) →
      Submodule.span B (Set.range t) = ⊤ →
      let delta := Module.finrank (FractionRing B)
        (LocalizedModule (nonZeroDivisors B) A)
      ∃ E : ℕ, ∃ d : B, ∃ x : Fin delta → A,
        d ≠ 0 ∧
        LinearIndependent B x ∧
        (∀ i, x i ∈ quotientHomogeneousComponent K sigma I E) ∧
        (∀ a : A, d • a ∈ Submodule.span B (Set.range x)) := by
  dsimp only
  let B := MvPolynomial (Fin r) K
  let A := MvPolynomial sigma K ⧸ I
  let g := linearNormalizationHomFin K sigma I ell
  letI : Algebra B A := g.toRingHom.toAlgebra
  haveI : Module.Finite B A := hfinite
  intro N t degree htHom htSpan
  obtain ⟨e, _heInjective, heLI, _heLIK, _heSpanK,
      d, hd, hclear⟩ :=
    exists_genericRank_subfamily_lattice_sandwich t htSpan
  let delta := Module.finrank (FractionRing B)
    (LocalizedModule (nonZeroDivisors B) A)
  let E : ℕ := Finset.univ.sup fun i : Fin delta ↦ degree (e i)
  let q : Fin delta → B := fun i ↦
    MvPolynomial.X 0 ^ (E - degree (e i))
  let x : Fin delta → A := fun i ↦ q i • t (e i)
  have hdegree_le (i : Fin delta) : degree (e i) ≤ E := by
    exact Finset.le_sup (f := fun j : Fin delta ↦ degree (e j))
      (Finset.mem_univ i)
  have hq_ne (i : Fin delta) : q i ≠ 0 := by
    exact pow_ne_zero _ (MvPolynomial.X_ne_zero (R := K) (0 : Fin r))
  have hxLI : LinearIndependent B x := by
    exact linearIndependent_smul_of_ne_zero heLI q hq_ne
  have hxHom (i : Fin delta) :
      x i ∈ quotientHomogeneousComponent K sigma I E := by
    rw [show x i = g (q i) * t (e i) by
      simp only [x, Algebra.smul_def]
      rfl]
    have hqHom : (q i).IsHomogeneous (E - degree (e i)) := by
      exact MvPolynomial.isHomogeneous_X_pow 0 (E - degree (e i))
    have hgq := linearNormalizationHomFin_mem_homogeneousComponent
      K sigma I ell hell hqHom
    have hmul :=
      (quotientHomogeneousComponent_gradedMonoid K sigma I).mul_mem
        hgq (htHom (e i))
    simpa only [Nat.sub_add_cancel (hdegree_le i)] using hmul
  let X0E : B := MvPolynomial.X 0 ^ E
  have hX0E_ne : X0E ≠ 0 := by
    exact pow_ne_zero _ (MvPolynomial.X_ne_zero (R := K) (0 : Fin r))
  have hX0E_generator (i : Fin delta) :
      X0E • t (e i) ∈ Submodule.span B (Set.range x) := by
    have heq : X0E • t (e i) =
        (MvPolynomial.X (R := K) (0 : Fin r) ^ degree (e i)) • x i := by
      simp only [x, q, smul_smul, ← pow_add]
      rw [show degree (e i) + (E - degree (e i)) = E by
        exact Nat.add_sub_of_le (hdegree_le i)]
    rw [heq]
    exact (Submodule.span B (Set.range x)).smul_mem _
      (Submodule.subset_span ⟨i, rfl⟩)
  have hX0E_span (a : A)
      (ha : a ∈ Submodule.span B (Set.range fun i ↦ t (e i))) :
      X0E • a ∈ Submodule.span B (Set.range x) := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
    · rintro y ⟨i, rfl⟩
      exact hX0E_generator i
    · simp
    · intro y z _ _ hy hz
      simpa only [smul_add] using
        (Submodule.span B (Set.range x)).add_mem hy hz
    · intro b y _ hy
      rw [smul_smul, mul_comm X0E b, ← smul_smul]
      exact (Submodule.span B (Set.range x)).smul_mem b hy
  refine ⟨E, d * X0E, x, mul_ne_zero hd hX0E_ne, hxLI, hxHom, ?_⟩
  intro a
  simpa only [smul_smul, mul_comm X0E d] using
    hX0E_span (d • a) (hclear a)

/-- Generic-rank/binomial squeeze for a finite injective homogeneous linear
normalization with any positive number of parameters. -/
theorem exists_genericRank_shifted_binomial_squeeze_fin
    (K : Type u) [Field K] (sigma : Type v) [Finite sigma]
    (I : Ideal (MvPolynomial sigma K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule sigma K))
    (hprime : I.IsPrime)
    {r : ℕ} [NeZero r]
    (ell : Fin r → MvPolynomial sigma K)
    (hell : ∀ i, (ell i).IsHomogeneous 1)
    (hfinite : (linearNormalizationHomFin K sigma I ell).Finite)
    (hinjective : Function.Injective
      (linearNormalizationHomFin K sigma I ell)) :
    let B := MvPolynomial (Fin r) K
    let A := MvPolynomial sigma K ⧸ I
    let g := linearNormalizationHomFin K sigma I ell
    letI : Algebra B A := g.toRingHom.toAlgebra
    let delta := Module.finrank (FractionRing B)
      (LocalizedModule (nonZeroDivisors B) A)
    ∃ E C : ℕ, ∀ n : ℕ,
      delta * (n + r).choose r ≤
          Module.finrank K
            (quotientTotalDegreeFiltration K sigma I (n + E)) ∧
        Module.finrank K (quotientTotalDegreeFiltration K sigma I n) ≤
          delta * (n + C + r).choose r := by
  dsimp only
  let B := MvPolynomial (Fin r) K
  let A := MvPolynomial sigma K ⧸ I
  let g := linearNormalizationHomFin K sigma I ell
  letI : Algebra B A := g.toRingHom.toAlgebra
  obtain ⟨N, t, degree, htHom, htSpan⟩ :=
    exists_homogeneous_generators_of_finite_linearNormalization_fin
      K sigma I ell hfinite
  obtain ⟨E, d, x, hd, hxLI, hxHom, hclear⟩ :=
    exists_equalDegree_genericRank_lattice_sandwich_fin
      K sigma I ell hell hfinite t degree htHom htSpan
  refine ⟨E, d.totalDegree, fun n ↦ ⟨?_, ?_⟩⟩
  · exact equalDegree_genericRank_lower_binomial_fin
      K sigma I ell hell x hxHom hxLI n
  · exact equalDegree_genericRank_upper_binomial_fin
      K sigma I hI hprime ell hell hinjective x hxHom hxLI d hd hclear n

/-- The generic rank of a nonzero finite injective normalization is positive.
This supplies the positivity clause in the literal degree datum. -/
theorem genericRank_pos_of_finite_injective_linearNormalizationFin
    (K : Type u) [Field K] (sigma : Type v)
    (I : Ideal (MvPolynomial sigma K)) {r : ℕ}
    (ell : Fin r → MvPolynomial sigma K)
    (hprime : I.IsPrime)
    (hfinite : (linearNormalizationHomFin K sigma I ell).Finite)
    (hinjective : Function.Injective
      (linearNormalizationHomFin K sigma I ell)) :
    let B := MvPolynomial (Fin r) K
    let A := MvPolynomial sigma K ⧸ I
    let g := linearNormalizationHomFin K sigma I ell
    letI : Algebra B A := g.toRingHom.toAlgebra
    0 < Module.finrank (FractionRing B)
      (LocalizedModule (nonZeroDivisors B) A) := by
  dsimp only
  let B := MvPolynomial (Fin r) K
  let A := MvPolynomial sigma K ⧸ I
  let g := linearNormalizationHomFin K sigma I ell
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : IsDomain A :=
    (Ideal.Quotient.isDomain_iff_prime (I := I)).mpr hprime
  haveI : Module.Finite B A := hfinite
  let f := LocalizedModule.mkLinearMap (nonZeroDivisors B) A
  have hf : Function.Injective f := by
    rw [IsLocalizedModule.injective_iff_isRegular (nonZeroDivisors B) f]
    intro s
    apply IsSMulRegular.of_right_eq_zero_of_smul
    intro a ha
    change g (s : B) * a = 0 at ha
    exact (mul_eq_zero.mp ha).resolve_left
      (hinjective.ne (nonZeroDivisors.coe_ne_zero s))
  have hne : f (1 : A) ≠ 0 := by
    have := hf.ne (one_ne_zero : (1 : A) ≠ 0)
    simpa only [map_zero] using this
  exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨f 1, hne⟩

end

end TranslatedDepthSeven

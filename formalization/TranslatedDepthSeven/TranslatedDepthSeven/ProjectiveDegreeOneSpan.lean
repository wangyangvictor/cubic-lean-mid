import TranslatedDepthSeven.ProjectiveLinearSpanIsolation
import TranslatedDepthSeven.TruncatedPolynomialJets
import TranslatedDepthSeven.GradedLinearSubstitution
import TranslatedDepthSeven.GradedRankSandwich
import TranslatedDepthSeven.StandardGradedQuotientFiltration
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card

/-!
# Projective degree one and the rational linear span

This file proves, without a geometric counting interface, the degree-one
case of the projective minimum-degree argument required in the strict
low-rank branch.  A homogeneous linear normalization first compares its
generic module rank with the leading Hilbert coefficient.  Rank one then
forces the finite normalization to be an isomorphism because its polynomial
base is integrally closed.  The degree-one quotient is consequently spanned
by the normalizing forms, and ordinary rank-nullity supplies literal rational
linear equations in the original homogeneous prime ideal.
-/

namespace TranslatedDepthSeven

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

open MvPolynomial
open scoped TensorProduct

theorem natCard_finExponent_totalDegree_eq (r k : ℕ) :
    Nat.card {P : Fin r →₀ ℕ // Finsupp.degree P = k} =
      (r + k - 1).choose k := by
  classical
  let e : {P : Fin r →₀ ℕ // Finsupp.degree P = k} ≃
      {P : Fin r →₀ ℕ // P.sum (fun _ ↦ id) = k} :=
    Equiv.subtypeEquiv (Equiv.refl _) (by
      intro P
      simp [Finsupp.degree_eq_sum, Finsupp.sum_fintype])
  rw [Nat.card_congr e]
  rw [← Nat.card_congr (Sym.equivNatSum (Fin r) k)]
  rw [Nat.card_eq_fintype_card, Sym.card_sym_eq_choose]
  simp

theorem finrank_mvPolynomial_homogeneousSubmodule_fin
    (K : Type*) [Field K] (r k : ℕ) :
    Module.finrank K (MvPolynomial.homogeneousSubmodule (Fin r) K k) =
      (r + k - 1).choose k := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  change Module.finrank K
    (MvPolynomial.restrictSupport K
      {P : Fin r →₀ ℕ | Finsupp.degree P = k}) = _
  rw [Module.finrank_eq_nat_card_basis
    (MvPolynomial.basisRestrictSupport K
      {P : Fin r →₀ ℕ | Finsupp.degree P = k})]
  exact natCard_finExponent_totalDegree_eq r k

attribute [local instance] MvPolynomial.gradedAlgebra

theorem normalizationData_hom_mem_homogeneousComponent
    {K : Type*} [Field K] {σ : Type*}
    (I : Ideal (MvPolynomial σ K))
    (D : HomogeneousLinearNormalizationData I)
    {n : ℕ} {p : MvPolynomial (Fin D.parameterCount) K}
    (hp : p.IsHomogeneous n) :
    D.hom p ∈ quotientHomogeneousComponent K σ I n := by
  apply Submodule.mem_map.mpr
  refine ⟨MvPolynomial.aeval D.forms p, ?_, rfl⟩
  simpa only [one_mul] using hp.aeval D.forms D.forms_isHomogeneous

theorem exists_homogeneous_generators_of_finite_normalizationData
    (K : Type*) [Field K] (σ : Type*) [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (D : HomogeneousLinearNormalizationData I) :
    let B := MvPolynomial (Fin D.parameterCount) K
    let A := MvPolynomial σ K ⧸ I
    let g := D.hom
    letI : Algebra B A := g.toRingHom.toAlgebra
    ∃ N : ℕ, ∃ t : Fin N → A, ∃ degree : Fin N → ℕ,
      (∀ i, t i ∈ quotientHomogeneousComponent K σ I (degree i)) ∧
      Submodule.span B (Set.range t) = ⊤ := by
  dsimp only
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial σ K ⧸ I
  let g := D.hom
  letI : Algebra B A := g.toRingHom.toAlgebra
  haveI : Module.Finite B A := by
    exact (show g.Finite from D.hom_finite)
  obtain ⟨M, s, hs⟩ := Module.Finite.exists_fin (R := B) (M := A)
  choose p hp using fun i : Fin M ↦ Ideal.Quotient.mk_surjective (s i)
  let E : ℕ := Finset.univ.sup fun i : Fin M ↦ (p i).totalDegree
  let ι := Fin M × Fin (E + 1)
  let t₀ : ι → A := fun ik ↦
    Ideal.Quotient.mk I (MvPolynomial.homogeneousComponent ik.2.1 (p ik.1))
  let degree₀ : ι → ℕ := fun ik ↦ ik.2.1
  have ht₀Hom (ik : ι) :
      t₀ ik ∈ quotientHomogeneousComponent K σ I (degree₀ ik) := by
    apply Submodule.mem_map.mpr
    exact ⟨MvPolynomial.homogeneousComponent ik.2.1 (p ik.1),
      MvPolynomial.homogeneousComponent_mem ik.2.1 (p ik.1), rfl⟩
  have ht₀Span : Submodule.span B (Set.range t₀) = ⊤ := by
    apply top_unique
    rw [← hs, Submodule.span_le]
    rintro a ⟨i, rfl⟩
    rw [← hp i, ← MvPolynomial.sum_homogeneousComponent (p i), map_sum]
    apply Submodule.sum_mem
    intro k hk
    apply Submodule.subset_span
    have hiE : (p i).totalDegree ≤ E := by
      exact Finset.le_sup (f := fun j : Fin M ↦ (p j).totalDegree)
        (Finset.mem_univ i)
    let k' : Fin (E + 1) := ⟨k,
      Nat.lt_succ_iff.mpr
        ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)).trans hiE)⟩
    exact ⟨(i, k'), rfl⟩
  let e := Fintype.equivFin ι
  let t : Fin (Fintype.card ι) → A := fun i ↦ t₀ (e.symm i)
  let degree : Fin (Fintype.card ι) → ℕ := fun i ↦ degree₀ (e.symm i)
  refine ⟨Fintype.card ι, t, degree, ?_, ?_⟩
  · intro i
    exact ht₀Hom (e.symm i)
  · have hrange : Set.range t = Set.range t₀ := by
      apply Set.ext
      intro a
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e.symm i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨e i, by simp only [t, Equiv.symm_apply_apply]⟩
    rw [hrange]
    exact ht₀Span

theorem exists_equalDegree_genericRank_lattice_normalizationData
    (K : Type*) [Field K] (σ : Type*) [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (D : HomogeneousLinearNormalizationData I)
    (hparameterCount : 0 < D.parameterCount) :
    let B := MvPolynomial (Fin D.parameterCount) K
    let A := MvPolynomial σ K ⧸ I
    let g := D.hom
    letI : Algebra B A := g.toRingHom.toAlgebra
    ∀ {N : ℕ} (t : Fin N → A) (degree : Fin N → ℕ),
      (∀ i, t i ∈ quotientHomogeneousComponent K σ I (degree i)) →
      Submodule.span B (Set.range t) = ⊤ →
      let δ := Module.finrank (FractionRing B)
        (LocalizedModule (nonZeroDivisors B) A)
      ∃ E : ℕ, ∃ x : Fin δ → A,
        LinearIndependent B x ∧
        (∀ i, x i ∈ quotientHomogeneousComponent K σ I E) := by
  dsimp only
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial σ K ⧸ I
  let g := D.hom
  letI : Algebra B A := g.toRingHom.toAlgebra
  haveI : Module.Finite B A := by
    exact (show g.Finite from D.hom_finite)
  intro N t degree htHom htSpan
  obtain ⟨e, _heInjective, heLI, _heLIK, _heSpanK,
      _d, _hd, _hclear⟩ :=
    exists_genericRank_subfamily_lattice_sandwich t htSpan
  let δ := Module.finrank (FractionRing B)
    (LocalizedModule (nonZeroDivisors B) A)
  let E : ℕ := Finset.univ.sup fun i : Fin δ ↦ degree (e i)
  let i₀ : Fin D.parameterCount := ⟨0, hparameterCount⟩
  let q : Fin δ → B := fun i ↦
    MvPolynomial.X i₀ ^ (E - degree (e i))
  let x : Fin δ → A := fun i ↦ q i • t (e i)
  have hdegree_le (i : Fin δ) : degree (e i) ≤ E := by
    exact Finset.le_sup (f := fun j : Fin δ ↦ degree (e j))
      (Finset.mem_univ i)
  have hq_ne (i : Fin δ) : q i ≠ 0 := by
    exact pow_ne_zero _ (MvPolynomial.X_ne_zero (R := K) i₀)
  have hxLI : LinearIndependent B x := by
    exact linearIndependent_smul_of_ne_zero heLI q hq_ne
  have hxHom (i : Fin δ) :
      x i ∈ quotientHomogeneousComponent K σ I E := by
    rw [show x i = g (q i) * t (e i) by
      simp only [x, Algebra.smul_def]
      rfl]
    have hqHom : (q i).IsHomogeneous (E - degree (e i)) := by
      exact MvPolynomial.isHomogeneous_X_pow i₀ (E - degree (e i))
    have hgq := normalizationData_hom_mem_homogeneousComponent
      I D hqHom
    have hmul :=
      (quotientHomogeneousComponent_gradedMonoid K σ I).mul_mem
        hgq (htHom (e i))
    simpa only [Nat.sub_add_cancel (hdegree_le i)] using hmul
  exact ⟨E, x, hxLI, hxHom⟩

theorem equalDegree_genericRank_lower_homogeneous
    (K : Type*) [Field K] (σ : Type*) [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (D : HomogeneousLinearNormalizationData I)
    {δ E : ℕ}
    (x : Fin δ → MvPolynomial σ K ⧸ I)
    (hxHom : ∀ i, x i ∈ quotientHomogeneousComponent K σ I E)
    (hxLI :
      let B := MvPolynomial (Fin D.parameterCount) K
      let A := MvPolynomial σ K ⧸ I
      let g := D.hom
      letI : Algebra B A := g.toRingHom.toAlgebra
      LinearIndependent B x)
    (n : ℕ) :
    δ * (D.parameterCount + n - 1).choose n ≤
      Module.finrank K (quotientHomogeneousComponent K σ I (n + E)) := by
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial σ K ⧸ I
  let g := D.hom
  let P := MvPolynomial.homogeneousSubmodule (Fin D.parameterCount) K n
  let F := quotientHomogeneousComponent K σ I (n + E)
  letI : Algebra B A := g.toRingHom.toAlgebra
  let L : (Fin δ → P) →ₗ[K] F :=
    { toFun := fun b ↦ ⟨∑ i, g (b i) * x i, by
        apply Submodule.sum_mem
        intro i _
        exact (quotientHomogeneousComponent_gradedMonoid K σ I).mul_mem
          (normalizationData_hom_mem_homogeneousComponent I D (b i).2)
          (hxHom i)⟩
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
    finrank_mvPolynomial_homogeneousSubmodule_fin K D.parameterCount n]
    using hfin

theorem exists_genericRank_lower_homogeneous_normalizationData
    (K : Type*) [Field K] (σ : Type*) [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (D : HomogeneousLinearNormalizationData I)
    (hparameterCount : 0 < D.parameterCount) :
    let B := MvPolynomial (Fin D.parameterCount) K
    let A := MvPolynomial σ K ⧸ I
    let g := D.hom
    letI : Algebra B A := g.toRingHom.toAlgebra
    let δ := Module.finrank (FractionRing B)
      (LocalizedModule (nonZeroDivisors B) A)
    ∃ E : ℕ, ∀ n : ℕ,
      δ * (D.parameterCount + n - 1).choose n ≤
        Module.finrank K (quotientHomogeneousComponent K σ I (n + E)) := by
  dsimp only
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial σ K ⧸ I
  let g := D.hom
  letI : Algebra B A := g.toRingHom.toAlgebra
  obtain ⟨N, t, degree, htHom, htSpan⟩ :=
    exists_homogeneous_generators_of_finite_normalizationData K σ I D
  obtain ⟨E, x, hxLI, hxHom⟩ :=
    exists_equalDegree_genericRank_lattice_normalizationData
      K σ I D hparameterCount t degree htHom htSpan
  exact ⟨E, fun n ↦
    equalDegree_genericRank_lower_homogeneous K σ I D x hxHom hxLI n⟩

theorem multiplicity_le_of_shifted_homogeneousHilbert_lower
    (P : Polynomial ℚ) (d δ E k₀ : ℕ)
    (hPdegree : P.natDegree = 4)
    (hPleading : P.leadingCoeff = (d : ℚ) / Nat.factorial 4)
    (hlower : ∀ n ≥ k₀,
      (δ * (n + 4).choose 4 : ℕ) ≤
        (P.eval (n + E : ℕ) : ℚ)) :
    δ ≤ d := by
  let S : Polynomial ℚ := P.comp (Polynomial.X + Polynomial.C (E : ℚ))
  let B : Polynomial ℚ := Polynomial.preHilbertPoly ℚ 4 0
  have hlinearDegree :
      (Polynomial.X + Polynomial.C (E : ℚ)).natDegree = 1 :=
    Polynomial.natDegree_X_add_C (E : ℚ)
  have hSdegree : S.natDegree = 4 := by
    dsimp only [S]
    rw [Polynomial.natDegree_comp, hPdegree, hlinearDegree]
  have hBdegree : B.natDegree = 4 := by
    exact Polynomial.natDegree_preHilbertPoly ℚ 4 0
  have hSne : S ≠ 0 := by
    intro h
    have := congrArg Polynomial.natDegree h
    simp [hSdegree] at this
  have hBne : B ≠ 0 := by
    intro h
    have := congrArg Polynomial.natDegree h
    simp [hBdegree] at this
  have hdegree : S.degree = B.degree := by
    rw [Polynomial.degree_eq_natDegree hSne,
      Polynomial.degree_eq_natDegree hBne, hSdegree, hBdegree]
  have hSlc : S.leadingCoeff = (d : ℚ) / Nat.factorial 4 := by
    dsimp only [S]
    rw [Polynomial.leadingCoeff_comp (by rw [hlinearDegree]; omega),
      Polynomial.leadingCoeff_X_add_C, one_pow, mul_one, hPleading]
  have hBlc : B.leadingCoeff = (Nat.factorial 4 : ℚ)⁻¹ := by
    exact Polynomial.leadingCoeff_preHilbertPoly ℚ 4 0
  have hlimitQ : Filter.Tendsto
      (fun q : ℚ ↦ S.eval q / B.eval q) Filter.atTop (nhds (d : ℚ)) := by
    have h := Polynomial.div_tendsto_leadingCoeff_div_of_degree_eq S B hdegree
    convert h using 1
    rw [hSlc, hBlc]
    norm_num [div_eq_mul_inv]
    ring
  have hlimitN : Filter.Tendsto
      (fun n : ℕ ↦ S.eval (n : ℚ) / B.eval (n : ℚ))
      Filter.atTop (nhds (d : ℚ)) :=
    hlimitQ.comp tendsto_natCast_atTop_atTop
  have heventual : ∀ᶠ n : ℕ in Filter.atTop,
      (δ : ℚ) ≤ S.eval (n : ℚ) / B.eval (n : ℚ) := by
    filter_upwards [Filter.eventually_ge_atTop k₀] with n hn
    have hB : B.eval (n : ℚ) = ((n + 4).choose 4 : ℚ) := by
      dsimp only [B]
      simpa using
        (Polynomial.preHilbertPoly_eq_choose_sub_add ℚ 4
          (k := 0) (n := n) (by omega))
    have hBpos : 0 < B.eval (n : ℚ) := by
      rw [hB]
      exact_mod_cast Nat.choose_pos (by omega : 4 ≤ n + 4)
    have hS : S.eval (n : ℚ) = P.eval ((n + E : ℕ) : ℚ) := by
      simp [S]
    rw [le_div_iff₀ hBpos, hB, hS]
    norm_cast
    simpa [Nat.mul_comm] using hlower n hn
  exact_mod_cast ge_of_tendsto hlimitN heventual

theorem normalization_genericRank_le_projectiveDegree_fourfold
    (I : Ideal (MvPolynomial (Fin 13) ℚ))
    (D : HomogeneousLinearNormalizationData I)
    (hparameterCount : D.parameterCount = 5)
    {d : ℕ}
    (hprojective : Published.HasProjectiveDimensionDegree I 4 d) :
    let B := MvPolynomial (Fin D.parameterCount) ℚ
    let A := MvPolynomial (Fin 13) ℚ ⧸ I
    let g := D.hom
    letI : Algebra B A := g.toRingHom.toAlgebra
    Module.finrank (FractionRing B)
      (LocalizedModule (nonZeroDivisors B) A) ≤ d := by
  dsimp only
  let B := MvPolynomial (Fin D.parameterCount) ℚ
  let A := MvPolynomial (Fin 13) ℚ ⧸ I
  let g := D.hom
  letI : Algebra B A := g.toRingHom.toAlgebra
  obtain ⟨E, hlower⟩ :=
    exists_genericRank_lower_homogeneous_normalizationData
      ℚ (Fin 13) I D (hparameterCount ▸ by omega)
  rcases hprojective with
    ⟨_hdimension, _hpositive, P, hPdegree, hPleading, k₀, hPeventual⟩
  apply multiplicity_le_of_shifted_homogeneousHilbert_lower
    P d (Module.finrank (FractionRing B)
      (LocalizedModule (nonZeroDivisors B) A)) E k₀ hPdegree hPleading
  intro n hn
  have hnE : k₀ ≤ n + E := hn.trans (Nat.le_add_right n E)
  have hvalue := hPeventual (n + E) hnE
  have hvalue' :
      (Module.finrank ℚ
        (quotientHomogeneousComponent ℚ (Fin 13) I (n + E)) : ℚ) =
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
        (Module.finrank ℚ
          (quotientHomogeneousComponent ℚ (Fin 13) I (n + E)) : ℚ) := by
    exact_mod_cast hlower'
  rw [hvalue'] at hlowerQ
  exact hlowerQ

/-- A finite integral injection from an integrally closed domain is
surjective when its generic scalar fibre has dimension one.  This is the
scalar-fibre version of finite birational normality; unlike a comparison of
two fraction fields, it is stated directly for the generic module used by
the Hilbert-function argument above. -/
theorem algebraMap_surjective_of_genericScalarFibre_finrank_eq_one
    {B A : Type*}
    [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [CommRing A] [IsDomain A] [Algebra B A]
    [Algebra.IsIntegral B A]
    (hinjective : Function.Injective (algebraMap B A))
    (hdegree : Module.finrank (FractionRing B)
      (FractionRing B ⊗[B] A) = 1) :
    Function.Surjective (algebraMap B A) := by
  let K := FractionRing B
  let G := K ⊗[B] A
  letI : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective B A).mpr hinjective
  have hinclude : Function.Injective
      (Algebra.TensorProduct.includeRight : A →ₐ[B] G) := by
    have hmk : Function.Injective
        (LocalizedModule.mkLinearMap (nonZeroDivisors B) A) := by
      apply (IsLocalizedModule.injective_iff_isRegular
        (S := nonZeroDivisors B)
        (f := LocalizedModule.mkLinearMap (nonZeroDivisors B) A)).mpr
      intro c x y hxy
      change (c : B) • x = (c : B) • y at hxy
      rw [Algebra.smul_def, Algebra.smul_def] at hxy
      exact mul_left_cancel₀
        (map_ne_zero_of_mem_nonZeroDivisors
          (algebraMap B A) hinjective c.property) hxy
    intro x y hxy
    apply hmk
    apply (LocalizedModule.equivTensorProduct
      (nonZeroDivisors B) A).injective
    rw [LocalizedModule.mkLinearMap_apply,
      LocalizedModule.mkLinearMap_apply,
      LocalizedModule.equivTensorProduct_apply_mk,
      LocalizedModule.equivTensorProduct_apply_mk,
      Localization.mk_one]
    exact hxy
  letI : Nontrivial G := hinclude.nontrivial
  have hKinjective : Function.Injective (algebraMap K G) :=
    FaithfulSMul.algebraMap_injective K G
  have hsurjective : Function.Surjective (algebraMap K G) := by
    have hspan :=
      (finrank_eq_one_iff_of_nonzero' (1 : G) one_ne_zero).mp hdegree
    intro z
    obtain ⟨k, hk⟩ := hspan z
    refine ⟨k, ?_⟩
    calc
      algebraMap K G k = k • (1 : G) :=
        Algebra.algebraMap_eq_smul_one k
      _ = z := hk
  intro a
  obtain ⟨k, hk⟩ := hsurjective
    (Algebra.TensorProduct.includeRight a)
  have hkIntegral : IsIntegral B k := by
    rw [← isIntegral_algHom_iff
      (IsScalarTower.toAlgHom B K G) hKinjective]
    change IsIntegral B ((algebraMap K G) k)
    rw [hk]
    exact (Algebra.IsIntegral.isIntegral a).map
      (Algebra.TensorProduct.includeRight : A →ₐ[B] G)
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hkIntegral
  refine ⟨b, hinclude ?_⟩
  calc
    Algebra.TensorProduct.includeRight (algebraMap B A b) =
        algebraMap B G b :=
      (Algebra.TensorProduct.includeRight : A →ₐ[B] G).commutes b
    _ = algebraMap K G (algebraMap B K b) :=
      IsScalarTower.algebraMap_apply B K G b
    _ = algebraMap K G k := by rw [hb]
    _ = Algebra.TensorProduct.includeRight a := hk

/-- The preceding scalar-fibre rigidity theorem in the literal
`LocalizedModule` form used by homogeneous normalization data. -/
theorem algebraMap_surjective_of_localized_finrank_eq_one
    {B A : Type*}
    [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [CommRing A] [IsDomain A] [Algebra B A]
    [Algebra.IsIntegral B A]
    (hinjective : Function.Injective (algebraMap B A))
    (hdegree : Module.finrank (FractionRing B)
      (LocalizedModule (nonZeroDivisors B) A) = 1) :
    Function.Surjective (algebraMap B A) := by
  apply algebraMap_surjective_of_genericScalarFibre_finrank_eq_one hinjective
  rw [← (LocalizedModule.equivTensorProduct
    (nonZeroDivisors B) A).finrank_eq]
  exact hdegree

/-- If a homogeneous linear normalization map is surjective, the degree-one
part of the quotient is spanned by the normalizing linear forms.  Rank-nullity
then supplies at least `N - parameterCount` independent literal linear
equations in the ideal. -/
theorem finrank_rationalLinearFormsInIdeal_ge_of_normalization_surjective
    {N : ℕ} (I : Ideal (MvPolynomial (Fin N) ℚ))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin N) ℚ))
    (D : HomogeneousLinearNormalizationData I)
    (hsurjective : Function.Surjective D.hom) :
    N - D.parameterCount ≤
      Module.finrank ℚ (rationalLinearFormsInIdeal I) := by
  let A := MvPolynomial (Fin N) ℚ ⧸ I
  let q : (Fin N → ℚ) →ₗ[ℚ] A :=
    (Ideal.Quotient.mkₐ ℚ I).toLinearMap.comp rationalLinearPolynomial
  let S : Submodule ℚ A :=
    Submodule.span ℚ
      (Set.range fun j ↦ (Ideal.Quotient.mkₐ ℚ I) (D.forms j))
  have hX (i : Fin N) :
      (Ideal.Quotient.mkₐ ℚ I) (MvPolynomial.X i) ∈ S := by
    exact quotient_X_mem_span_linear_images_of_surjective
      I hI D.forms D.forms_isHomogeneous hsurjective i
  have hqFormula (a : Fin N → ℚ) :
      q a = ∑ i, a i •
        (Ideal.Quotient.mkₐ ℚ I) (MvPolynomial.X i) := by
    change (Ideal.Quotient.mkₐ ℚ I)
      (∑ i, MvPolynomial.C (a i) * MvPolynomial.X i) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [map_mul]
    change
      (Ideal.Quotient.mkₐ ℚ I)
          ((algebraMap ℚ (MvPolynomial (Fin N) ℚ)) (a i)) * _ = _
    rw [(Ideal.Quotient.mkₐ ℚ I).commutes]
    exact (Algebra.smul_def (a i)
      ((Ideal.Quotient.mkₐ ℚ I) (MvPolynomial.X i))).symm
  have hqrange : LinearMap.range q ≤ S := by
    rintro _ ⟨a, rfl⟩
    rw [hqFormula]
    exact Submodule.sum_mem S fun i _ ↦ S.smul_mem (a i) (hX i)
  have hSfinrank : Module.finrank ℚ S ≤ D.parameterCount := by
    change Module.finrank ℚ
      (Submodule.span ℚ (Set.range fun j ↦
        (Ideal.Quotient.mkₐ ℚ I) (D.forms j))) ≤ D.parameterCount
    simpa using finrank_range_le_card
      (fun j ↦ (Ideal.Quotient.mkₐ ℚ I) (D.forms j))
  letI : Module.Finite ℚ S :=
    Module.Finite.span_of_finite ℚ (Set.finite_range _)
  have hqfinrank : Module.finrank ℚ (LinearMap.range q) ≤
      D.parameterCount :=
    (Submodule.finrank_mono hqrange).trans hSfinrank
  have hker : LinearMap.ker q = rationalLinearFormsInIdeal I := by
    ext a
    simp only [LinearMap.mem_ker, mem_rationalLinearFormsInIdeal_iff]
    change (Ideal.Quotient.mk I) (rationalLinearPolynomial a) = 0 ↔
      rationalLinearPolynomial a ∈ I
    exact Ideal.Quotient.eq_zero_iff_mem
  have hrankNullity := q.finrank_range_add_finrank_ker
  rw [hker, Module.finrank_fin_fun] at hrankNullity
  omega

/-- A prime homogeneous projective fourfold of projective degree one has at
least eight independent rational linear equations once a five-variable
homogeneous linear normalization is displayed. -/
theorem eight_le_finrank_rationalLinearFormsInIdeal_of_degree_one
    (I : Ideal (MvPolynomial (Fin 13) ℚ))
    (hIprime : I.IsPrime)
    (hIhomogeneous :
      I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ))
    (D : HomogeneousLinearNormalizationData I)
    (hparameterCount : D.parameterCount = 5)
    (hprojective : Published.HasProjectiveDimensionDegree I 4 1) :
    8 ≤ Module.finrank ℚ (rationalLinearFormsInIdeal I) := by
  letI : I.IsPrime := hIprime
  let B := MvPolynomial (Fin D.parameterCount) ℚ
  let A := MvPolynomial (Fin 13) ℚ ⧸ I
  let g := D.hom
  letI : IsDomain A := Ideal.Quotient.isDomain I
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective B A).mpr D.hom_injective
  haveI : Module.Finite B A := by
    exact (show g.Finite from D.hom_finite)
  have hdegree_le : Module.finrank (FractionRing B)
      (LocalizedModule (nonZeroDivisors B) A) ≤ 1 :=
    normalization_genericRank_le_projectiveDegree_fourfold
      I D hparameterCount hprojective
  have hdegree_pos : 0 < Module.finrank (FractionRing B)
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
  have hdegree : Module.finrank (FractionRing B)
      (LocalizedModule (nonZeroDivisors B) A) = 1 := by
    omega
  have hsurjective : Function.Surjective g := by
    haveI : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
    exact algebraMap_surjective_of_localized_finrank_eq_one
      D.hom_injective hdegree
  have hlin :=
    finrank_rationalLinearFormsInIdeal_ge_of_normalization_surjective
      I hIhomogeneous D hsurjective
  rw [hparameterCount] at hlin
  norm_num at hlin ⊢
  exact hlin

/-- Uniform bounded-height codimension-two rational sections for a fixed
finite family of degree-one projective fourfolds.  The bound is obtained only
after all ideals and their literal linear equations have been chosen, so it
is independent of every later prime, residue class, and box parameter. -/
theorem exists_uniform_twoRow_linearSpan_of_finite_degreeOne_fourfolds
    {α : Type*} (components : Finset α)
    (ideal : α → Ideal (MvPolynomial (Fin 13) ℚ))
    (hprime : ∀ Q ∈ components, (ideal Q).IsPrime)
    (hhomogeneous : ∀ Q ∈ components,
      (ideal Q).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ))
    (normalization : ∀ Q : α,
      HomogeneousLinearNormalizationData (ideal Q))
    (hparameterCount : ∀ Q ∈ components,
      (normalization Q).parameterCount = 5)
    (hdegree : ∀ Q ∈ components,
      Published.HasProjectiveDimensionDegree (ideal Q) 4 1) :
    ∃ C : ℕ, ∀ Q ∈ components,
      ∃ v : Fin 2 → Fin 13 → ℚ,
        LinearIndependent ℚ v ∧
        (rationalLinearFormMatrix v).rank = 2 ∧
        (∀ i, rationalMatrixRowLinearPolynomial
          (rationalLinearFormMatrix v) i ∈ ideal Q) ∧
        rationalProjectiveLinearHeight
          (rationalLinearFormMatrix v) ≤ C := by
  apply exists_uniform_twoRow_linearSpan_of_finite components ideal
  intro Q hQ
  exact (by omega : 2 ≤ 8).trans
    (eight_le_finrank_rationalLinearFormsInIdeal_of_degree_one
      (ideal Q) (hprime Q hQ) (hhomogeneous Q hQ)
      (normalization Q) (hparameterCount Q hQ) (hdegree Q hQ))

end
end TranslatedDepthSeven

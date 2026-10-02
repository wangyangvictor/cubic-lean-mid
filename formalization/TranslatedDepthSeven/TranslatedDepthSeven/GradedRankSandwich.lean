import TranslatedDepthSeven.PrincipalOpenSpanningDescent
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card

/-!
# The generic-rank lattice sandwich

This file records the commutative-algebra core of the usual comparison
between generic rank and the leading term of a Hilbert function.  A finite
module over a domain contains a free lattice of rank equal to its generic
rank; one nonzero scalar sends the whole module back into that lattice.

When the displayed generators are homogeneous, the selected lattice
generators are homogeneous as well.  Thus the theorem loses no grading
information: only the final elementary count of the graded pieces of the
polynomial ring remains.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped nonZeroDivisors

universe u v

/-- Adding one slack coordinate identifies exponent vectors in three
variables of total degree at most `n` with four-tuples of total mass `n`.
This is the cumulative form of stars and bars. -/
def finThreeExponentLEEquivFinFourSum (n : ℕ) :
    {P : Fin 3 →₀ ℕ // P.sum (fun _ ↦ id) ≤ n} ≃
      {Q : Fin 4 → ℕ // ∑ i, Q i = n} where
  toFun P := ⟨Fin.cons (n - P.1.sum (fun _ ↦ id)) (fun i ↦ P.1 i), by
    rw [Fin.sum_univ_succ]
    simpa [Finsupp.sum_fintype] using Nat.sub_add_cancel P.2⟩
  invFun Q := ⟨Finsupp.equivFunOnFinite.symm (Fin.tail Q.1), by
    have htail :
        (Finsupp.equivFunOnFinite.symm (Fin.tail Q.1)).sum (fun _ ↦ id) =
          ∑ i, Fin.tail Q.1 i := by
      rw [Finsupp.sum_fintype]
      · rfl
      · intro i
        rfl
    rw [htail]
    have hsum : Q.1 0 + ∑ i, Fin.tail Q.1 i = n := by
      simpa only [Fin.sum_univ_succ] using Q.2
    omega⟩
  left_inv P := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    simp
  right_inv Q := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [Fin.cons_zero]
      have htail :
          (Finsupp.equivFunOnFinite.symm (Fin.tail Q.1)).sum (fun _ ↦ id) =
            ∑ j, Fin.tail Q.1 j := by
        rw [Finsupp.sum_fintype]
        · rfl
        · intro j
          rfl
      rw [htail]
      have hsum : Q.1 0 + ∑ j, Fin.tail Q.1 j = n := by
        simpa only [Fin.sum_univ_succ] using Q.2
      omega
    · change Q.1 j.succ = Q.1 j.succ
      rfl

/-- The cumulative monomial count in three variables. -/
theorem natCard_finThreeExponent_totalDegree_le (n : ℕ) :
    Nat.card {P : Fin 3 →₀ ℕ // P.sum (fun _ ↦ id) ≤ n} =
      (n + 3).choose 3 := by
  classical
  rw [Nat.card_congr (finThreeExponentLEEquivFinFourSum n)]
  rw [← Nat.card_congr (Sym.equivNatSumOfFintype (Fin 4) n)]
  rw [Nat.card_eq_fintype_card, Sym.card_sym_eq_choose]
  norm_num
  simpa [Nat.add_comm] using (Nat.choose_symm_add (a := 3) (b := n)).symm

/-- The subspace of polynomials in three variables of total degree at most
`n` has dimension `choose (n+3) 3`. -/
theorem finrank_mvPolynomial_finThree_restrictTotalDegree
    (K : Type u) [Field K] (n : ℕ) :
    Module.finrank K (MvPolynomial.restrictTotalDegree (Fin 3) K n) =
      (n + 3).choose 3 := by
  change Module.finrank K
    (MvPolynomial.restrictSupport K
      {P : Fin 3 →₀ ℕ | P.sum (fun _ ↦ id) ≤ n}) = (n + 3).choose 3
  rw [Module.finrank_eq_nat_card_basis
    (MvPolynomial.basisRestrictSupport K
      {P : Fin 3 →₀ ℕ | P.sum (fun _ ↦ id) ≤ n})]
  exact natCard_finThreeExponent_totalDegree_le n

/-- If a finite family spans a module and another family spans its generic
fibre, one nonzero scalar sends the whole module into the span of the second
family.  This is the denominator-clearing half of the rank sandwich. -/
theorem exists_nonzero_smul_mem_span_of_fractionRing_span
    {R : Type u} {M : Type v}
    [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M]
    {N D : ℕ} (t : Fin N → M) (s : Fin D → M)
    (ht : Submodule.span R (Set.range t) = ⊤)
    (hs :
      Submodule.span (FractionRing R)
          (Set.range (fun i ↦
            LocalizedModule.mkLinearMap R⁰ M (s i))) = ⊤) :
    ∃ d : R, d ≠ 0 ∧
      ∀ x : M, d • x ∈ Submodule.span R (Set.range s) := by
  classical
  let f : M →ₗ[R] LocalizedModule R⁰ M :=
    LocalizedModule.mkLinearMap R⁰ M
  let P : Submodule R M := Submodule.span R (Set.range s)
  have hs' : P.localized' (FractionRing R) R⁰ f = ⊤ := by
    rw [Submodule.localized'_span]
    rw [← Set.range_comp']
    simpa only [f, P] using hs
  have hdenom :
      ∀ i : Fin N, ∃ d : R, d ≠ 0 ∧ d • t i ∈ P := by
    intro i
    have hfti : f (t i) ∈ P.localized' (FractionRing R) R⁰ f := by
      rw [hs']
      trivial
    obtain ⟨a, ha, z, hz⟩ :=
      (Submodule.mem_localized' (FractionRing R) R⁰ f P (f (t i))).mp hfti
    have hfa : f a = z • f (t i) :=
      IsLocalizedModule.mk'_eq_iff.mp hz
    have hfa' : f a = f (z • t i) := by
      simpa only [Submonoid.smul_def, map_smul] using hfa
    obtain ⟨c, hc⟩ :=
      (IsLocalizedModule.eq_iff_exists R⁰ f).mp hfa'
    refine ⟨(c * z : R⁰), mem_nonZeroDivisors_iff_ne_zero.mp (c * z).property, ?_⟩
    simp only [Submonoid.smul_def] at hc
    change ((c : R) * (z : R)) • t i ∈ P
    rw [mul_smul]
    rw [← hc]
    exact P.smul_mem c ha
  choose d hd hclear using hdenom
  refine ⟨∏ i, d i, Finset.prod_ne_zero_iff.mpr fun i _ ↦ hd i, ?_⟩
  intro x
  have hx : x ∈ Submodule.span R (Set.range t) := by
    rw [ht]
    trivial
  exact prod_denominators_smul_mem_of_mem_span_range P t d hclear hx

/-- A finite spanning family contains a subfamily whose images form a basis
of the generic fibre.  Its cardinality is exactly the generic rank, and one
nonzero scalar sends the entire module into its span.

The fact that this is literally a subfamily is important for graded
applications: any property of the original generators (in particular,
homogeneity of a prescribed degree) is automatically retained. -/
theorem exists_genericRank_subfamily_lattice_sandwich
    {R : Type u} {M : Type v}
    [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    {N : ℕ} (t : Fin N → M)
    (ht : Submodule.span R (Set.range t) = ⊤) :
    let K := FractionRing R
    let G := LocalizedModule R⁰ M
    let f : M →ₗ[R] G := LocalizedModule.mkLinearMap R⁰ M
    ∃ e : Fin (Module.finrank K G) → Fin N,
      Function.Injective e ∧
      LinearIndependent R (fun i ↦ t (e i)) ∧
      LinearIndependent K (fun i ↦ f (t (e i))) ∧
      Submodule.span K (Set.range (fun i ↦ f (t (e i)))) = ⊤ ∧
      ∃ d : R, d ≠ 0 ∧
        ∀ x : M, d • x ∈
          Submodule.span R (Set.range (fun i ↦ t (e i))) := by
  classical
  dsimp only
  let K := FractionRing R
  let G := LocalizedModule R⁰ M
  let f : M →ₗ[R] G := LocalizedModule.mkLinearMap R⁰ M
  let u : Fin N → G := fun i ↦ f (t i)
  have huSpan : Submodule.span K (Set.range u) = ⊤ := by
    have h := span_eq_top_of_isLocalizedModule K R⁰ f ht
    rw [show Set.range u = f '' Set.range t by
      ext x
      simp only [Set.mem_range, Set.mem_image]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨t i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩]
    exact h
  let b := Module.Basis.ofSpan huSpan.ge
  let I := (linearIndepOn_empty K id).extend
    (Set.empty_subset (Set.range u))
  have hI_finite : Set.Finite I := by
    apply (Set.finite_range u).subset
    intro x hx
    apply Module.Basis.ofSpan_subset huSpan.ge
    exact ⟨⟨x, hx⟩, Module.Basis.ofSpan_apply_self huSpan.ge ⟨x, hx⟩⟩
  letI : Fintype I := hI_finite.fintype
  have hcard : Fintype.card I = Module.finrank K G := by
    exact (Module.finrank_eq_card_basis b).symm
  let φ : Fin (Module.finrank K G) ≃ I :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hcard.symm)
  have hb_mem (i : Fin (Module.finrank K G)) : b (φ i) ∈ Set.range u := by
    apply Module.Basis.ofSpan_subset huSpan.ge
    exact ⟨φ i, rfl⟩
  choose e he using hb_mem
  have heq (i : Fin (Module.finrank K G)) :
      f (t (e i)) = b (φ i) := by
    exact he i
  have he_injective : Function.Injective e := by
    intro i j hij
    apply φ.injective
    apply b.injective
    rw [← heq i, ← heq j, hij]
  have hliK : LinearIndependent K (fun i ↦ f (t (e i))) := by
    have hbφ : LinearIndependent K (fun i ↦ b (φ i)) :=
      b.linearIndependent.comp φ φ.injective
    simpa only [heq] using hbφ
  have hspanK :
      Submodule.span K (Set.range (fun i ↦ f (t (e i)))) = ⊤ := by
    apply hliK.span_eq_top_of_card_eq_finrank'
    simp
  have hliR : LinearIndependent R (fun i ↦ t (e i)) := by
    apply LinearIndependent.of_comp f
    exact hliK.restrict_scalars <|
      (faithfulSMul_iff_injective_smul_one R K).mp inferInstance
  obtain ⟨d, hd, hclear⟩ :=
    exists_nonzero_smul_mem_span_of_fractionRing_span
      t (fun i ↦ t (e i)) ht hspanK
  exact ⟨e, he_injective, hliR, hliK, hspanK, d, hd, hclear⟩

end

end TranslatedDepthSeven

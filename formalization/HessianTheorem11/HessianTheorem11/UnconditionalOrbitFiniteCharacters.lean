import HessianTheorem11.UnconditionalOrbitCharacterOrder

/-! One fixed finite character universe controls every bounded target
ideal and every evaluation point. The active character set records actual
nonzero evaluations of character projections, not merely monomial support. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace HessianTheorem11.UnconditionalOrbitIdeal
open MvPolynomial ReducedRelative UnconditionalOrbitWeights
variable {K : Type*} [Field K] {n d : ℕ}

def boundedMonomials (σ : Type*) [Fintype σ] [DecidableEq σ] (N : ℕ) : Finset (σ →₀ ℕ) :=
  (Finset.range (N+1)).biUnion (fun k => Finset.univ.finsuppAntidiag k)

theorem support_subset_boundedMonomials {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : MvPolynomial σ K) (N : ℕ) (hP : P.totalDegree ≤ N) :
    P.support ⊆ boundedMonomials σ N := by
  intro e he
  apply Finset.mem_biUnion.mpr
  refine ⟨e.sum (fun _ a => a),Finset.mem_range.mpr ?_,?_⟩
  · exact Nat.lt_succ_of_le ((le_totalDegree he).trans hP)
  · exact Finset.mem_finsuppAntidiag'.mpr ⟨rfl,Finset.subset_univ _⟩

def equationMonomials (n d N : ℕ) : Finset (DegreeIndex n d →₀ ℕ) :=
  boundedMonomials (DegreeIndex n d) N

def possibleCharacters (n d N : ℕ) : Finset (Fin n → ℤ) := by
  classical
  exact (equationMonomials n d N).image equationCharacter

theorem support_subset_equationMonomials (P : MvPolynomial (DegreeIndex n d) K)
    (N : ℕ) (hP : P.totalDegree ≤ N) : P.support ⊆ equationMonomials n d N :=
  support_subset_boundedMonomials P N hP

def activeCharacters (F : MvPolynomial (Fin n) K)
    (S : Set (MvPolynomial (Fin n) K)) (N : ℕ) : Finset (Fin n → ℤ) := by
  classical
  exact (possibleCharacters n d N).filter (fun c =>
    ∃ P : boundedIdeal (finiteTarget (d := d) S) N,
      eval (coefficientVector F) (characterPart P.val c) ≠ 0)

theorem character_mem_possible_of_eval_ne_zero (F : MvPolynomial (Fin n) K)
    (S : Set (MvPolynomial (Fin n) K)) (N : ℕ)
    (P : boundedIdeal (finiteTarget (d := d) S) N) (c : Fin n → ℤ)
    (hc : eval (coefficientVector F) (characterPart P.val c) ≠ 0) :
    c ∈ possibleCharacters n d N := by
  classical
  have hmem : c ∈ P.val.support.image equationCharacter := by
    by_contra h
    apply hc
    rw [characterPart_zero_outside P.val c h,map_zero]
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hmem
  exact Finset.mem_image.mpr ⟨e,support_subset_equationMonomials P.val N
    ((mem_boundedIdeal _ _ _).mp P.property).2 he,rfl⟩

theorem mem_activeCharacters (F : MvPolynomial (Fin n) K)
    (S : Set (MvPolynomial (Fin n) K)) (N : ℕ) (c : Fin n → ℤ) :
    c ∈ activeCharacters (d := d) F S N ↔
      ∃ P : boundedIdeal (finiteTarget (d := d) S) N,
        eval (coefficientVector F) (characterPart P.val c) ≠ 0 := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · rintro ⟨P,hP⟩
    exact Finset.mem_filter.mpr ⟨character_mem_possible_of_eval_ne_zero F S N P c hP,⟨P,hP⟩⟩

theorem activeCharacters_subset (F : MvPolynomial (Fin n) K)
    (S : Set (MvPolynomial (Fin n) K)) (N : ℕ) :
    activeCharacters (d := d) F S N ⊆ possibleCharacters n d N := by
  classical
  exact Finset.filter_subset _ _

theorem activeCharacters_sum (F : MvPolynomial (Fin n) K)
    (S : Set (MvPolynomial (Fin n) K)) (N : ℕ)
    (c : Fin n → ℤ) (hc : c ∈ activeCharacters (d := d) F S N) : ∑ i, c i = 0 := by
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp (activeCharacters_subset F S N hc)
  exact equationCharacter_sum e

theorem character_weights_iff_active (hn : 0 < n)
    (F : MvPolynomial (Fin n) K) (S : Set (MvPolynomial (Fin n) K)) (N : ℕ)
    (w : Fin n → ℤ) (hw : ∑ i, w i = 0) (m : ℕ) :
    (∀ P : boundedIdeal (finiteTarget (d := d) S) N, ∀ e ∈ P.val.support,
      eval (coefficientVector F) (characterPart P.val (equationCharacter e)) ≠ 0 →
        (m : ℤ) ≤ exponentWeight (coefficientWeights w) e) ↔
    (∀ c ∈ activeCharacters (d := d) F S N, (n : ℤ) * m ≤ ∑ i, c i * w i) := by
  classical
  constructor
  · intro h c hc
    obtain ⟨P,hP⟩ := (mem_activeCharacters F S N c).mp hc
    have hmem : c ∈ P.val.support.image equationCharacter := by
      by_contra hm
      apply hP
      rw [characterPart_zero_outside P.val c hm,map_zero]
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hmem
    rw [equationCharacter_pairing e w hw]
    exact mul_le_mul_of_nonneg_left (h P e he hP) (by omega)
  · intro h P e he hP
    have hc := h (equationCharacter e) ((mem_activeCharacters F S N _).mpr ⟨P,hP⟩)
    rw [equationCharacter_pairing e w hw] at hc
    exact (mul_le_mul_iff_right₀ (by omega : (0 : ℤ) < n)).mp hc

/-- A genuinely finite set, chosen before the one-parameter subgroup, now
computes lower bounds for the previously defined relative ideal order. -/
theorem le_relativeOrder_iff_activeCharacters [Infinite K] (hn : 0 < n)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (hclosed : coefficientClosed S)
    (hS : slInvariant S) (hhom : ∀ G ∈ S, G.IsHomogeneous d) (hnot : F ∉ S)
    (w : Fin n → ℤ) (hw : ∑ i, w i = 0) (hW : HasNonnegativeWeights F w) (N m : ℕ)
    (hgen : Ideal.span (boundedIdeal (finiteTarget (d := d) S) N :
      Set (MvPolynomial (DegreeIndex n d) K)) = vanishingIdeal K (finiteTarget (d := d) S)) :
    m ≤ relativeOrder d F S (identityWeightFrame w hw) ↔
      ∀ c ∈ activeCharacters (d := d) F S N, (n : ℤ) * m ≤ ∑ i, c i * w i := by
  rw [le_relativeOrder_iff_character_weights hn F hF S hclosed hS hhom hnot w hw hW N m hgen,
    character_weights_iff_active hn F S N w hw m]

theorem coefficientVector_mem_finiteTarget_iff
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (hhom : ∀ G ∈ S, G.IsHomogeneous d) :
    coefficientVector (d := d) F ∈ finiteTarget (d := d) S ↔ F ∈ S := by
  constructor
  · rintro ⟨G,hG,he⟩
    have h := congrArg (decode (K := K)) he
    rw [decode_coefficientVector G (hhom G hG),decode_coefficientVector F hF] at h
    exact h ▸ hG
  · exact fun h => ⟨F,h,rfl⟩

/-- A closed target avoiding F always has at least one active character
in any bounded ideal piece that generates its full vanishing ideal. -/
theorem activeCharacters_nonempty
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (hclosed : coefficientClosed S)
    (hhom : ∀ G ∈ S, G.IsHomogeneous d) (hnot : F ∉ S) (N : ℕ)
    (hgen : Ideal.span (boundedIdeal (finiteTarget (d := d) S) N :
      Set (MvPolynomial (DegreeIndex n d) K)) = vanishingIdeal K (finiteTarget (d := d) S)) :
    (activeCharacters (d := d) F S N).Nonempty := by
  classical
  have hne : boundedEvaluation (finiteTarget (d := d) S) N (coefficientVector F) ≠ 0 := by
    intro hz
    apply hnot
    apply (coefficientVector_mem_finiteTarget_iff F hF S hhom).mp
    have h := (boundedEvaluation_eq_zero_iff (finiteTarget S) N hgen (coefficientVector F)).mp hz
    rwa [finiteTarget_zeroLocus S hclosed hhom] at h
  have hex : ∃ P : boundedIdeal (finiteTarget (d := d) S) N,
      eval (coefficientVector F) P.val ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    ext P
    exact h P
  obtain ⟨P,hP⟩ := hex
  have hex' : ∃ c ∈ P.val.support.image equationCharacter,
      eval (coefficientVector F) (characterPart P.val c) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hP
    have he := congrArg (eval (coefficientVector F)) (sum_characterParts P.val)
    rw [map_sum] at he
    rw [← he]
    exact Finset.sum_eq_zero h
  obtain ⟨c,hc,he⟩ := hex'
  exact ⟨c,(mem_activeCharacters F S N c).mpr ⟨P,he⟩⟩

end HessianTheorem11.UnconditionalOrbitIdeal

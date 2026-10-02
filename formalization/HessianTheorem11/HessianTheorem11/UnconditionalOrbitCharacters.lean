import HessianTheorem11.UnconditionalOrbitTargetWeights
import HessianTheorem11.UnconditionalCharacterSeparation

/-! Integral characters of the special-linear diagonal torus on actual
finite coefficient equations. Centering removes precisely the scalar
character, without choosing a one-parameter subgroup. -/
noncomputable section
namespace HessianTheorem11.UnconditionalOrbitIdeal
open MvPolynomial UnconditionalOrbitWeights
variable {K : Type*} [Field K] {n d : ℕ}

def equationExponent (e : DegreeIndex n d →₀ ℕ) (i : Fin n) : ℤ :=
  ∑ m, (e m : ℤ) * (m.val i : ℤ)

def equationCharacter (e : DegreeIndex n d →₀ ℕ) (i : Fin n) : ℤ :=
  (n : ℤ) * equationExponent e i - ∑ j, equationExponent e j

theorem equationCharacter_sum (e : DegreeIndex n d →₀ ℕ) :
    ∑ i, equationCharacter e i = 0 := by
  simp [equationCharacter,Finset.sum_sub_distrib,← Finset.mul_sum]

theorem equationExponent_pairing (e : DegreeIndex n d →₀ ℕ) (w : Fin n → ℤ) :
    (∑ i, equationExponent e i * w i) = exponentWeight (coefficientWeights w) e := by
  classical
  unfold equationExponent exponentWeight coefficientWeights monomialWeight
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [Finsupp.sum_fintype _ _ (by simp)]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem equationCharacter_pairing (e : DegreeIndex n d →₀ ℕ)
    (w : Fin n → ℤ) (hw : ∑ i, w i = 0) :
    (∑ i, equationCharacter e i * w i) =
      (n : ℤ) * exponentWeight (coefficientWeights w) e := by
  simp only [equationCharacter,sub_mul,Finset.sum_sub_distrib]
  rw [← Finset.mul_sum,hw,mul_zero,sub_zero]
  calc
    (∑ i, (n : ℤ) * equationExponent e i * w i) =
        (n : ℤ) * ∑ i, equationExponent e i * w i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [equationExponent_pairing]

def characterPart (P : MvPolynomial (DegreeIndex n d) K)
    (c : Fin n → ℤ) : MvPolynomial (DegreeIndex n d) K :=
  Finsupp.filter (fun e => equationCharacter e = c) P

@[simp] theorem coeff_characterPart (P : MvPolynomial (DegreeIndex n d) K)
    (c : Fin n → ℤ) (e : DegreeIndex n d →₀ ℕ) :
    coeff e (characterPart P c) = if equationCharacter e = c then coeff e P else 0 := rfl

theorem characterPart_zero_outside (P : MvPolynomial (DegreeIndex n d) K)
    (c : Fin n → ℤ) (hc : c ∉ P.support.image equationCharacter) :
    characterPart P c = 0 := by
  ext e
  rw [coeff_characterPart,coeff_zero]
  split_ifs with he
  · by_contra h
    exact hc (Finset.mem_image.mpr ⟨e,mem_support_iff.mpr h,he⟩)
  · rfl

theorem sum_characterParts (P : MvPolynomial (DegreeIndex n d) K) :
    (∑ c ∈ P.support.image equationCharacter, characterPart P c) = P := by
  classical
  ext e
  simp only [coeff_sum,coeff_characterPart]
  by_cases hc : coeff e P = 0
  · simp [hc]
  · have he : equationCharacter e ∈ P.support.image equationCharacter :=
      Finset.mem_image.mpr ⟨e,mem_support_iff.mpr hc,rfl⟩
    rw [Finset.sum_eq_single (equationCharacter e)]
    · simp
    · intro c hc hce
      simp [Ne.symm hce]
    · exact fun h => (h he).elim

/-- A single integral one-parameter subgroup separates all characters of
any given finite coefficient equation. -/
theorem exists_character_separating_weight (hn : 0 < n)
    (P : MvPolynomial (DegreeIndex n d) K) :
    ∃ w : Fin n → ℤ, (∑ i, w i = 0) ∧
      ∀ e ∈ P.support, ∀ f ∈ P.support,
        exponentWeight (coefficientWeights w) e = exponentWeight (coefficientWeights w) f ↔
          equationCharacter e = equationCharacter f := by
  classical
  obtain ⟨w,hw,hs⟩ := UnconditionalCharacters.exists_separating_sum_zero hn
    (P.support.image equationCharacter) (by
      intro c hc
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hc
      exact equationCharacter_sum e)
  refine ⟨w,hw,?_⟩
  intro e he f hf
  constructor
  · intro h
    by_contra hne
    apply hs _ (Finset.mem_image.mpr ⟨e,he,rfl⟩)
      _ (Finset.mem_image.mpr ⟨f,hf,rfl⟩) hne
    rw [equationCharacter_pairing e w hw,equationCharacter_pairing f w hw,h]
  · intro h
    have hp := congrArg (fun c : Fin n → ℤ => ∑ i, c i * w i) h
    dsimp only at hp
    rw [equationCharacter_pairing e w hw,equationCharacter_pairing f w hw] at hp
    exact mul_left_cancel₀ (by omega : (n : ℤ) ≠ 0) hp

/-- Every full special-linear character component of a bounded invariant
ideal equation belongs to the same bounded ideal piece. -/
theorem target_characterPart_mem [Infinite K] (hn : 0 < n)
    (S : Set (MvPolynomial (Fin n) K)) (hS : ReducedRelative.slInvariant S)
    (hhom : ∀ G ∈ S, G.IsHomogeneous d) (N : ℕ)
    (P : boundedIdeal (finiteTarget (d := d) S) N) (c : Fin n → ℤ) :
    characterPart P.val c ∈ boundedIdeal (finiteTarget (d := d) S) N := by
  classical
  by_cases hc : c ∈ P.val.support.image equationCharacter
  · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨w,hw,hs⟩ := exists_character_separating_weight hn P.val
    have hp : characterPart P.val (equationCharacter e) =
        weightPart P.val (coefficientWeights w) (exponentWeight (coefficientWeights w) e) := by
      ext f
      rw [coeff_characterPart,coeff_weightPart]
      by_cases hf : coeff f P.val = 0
      · simp [hf]
      · simp only [hs f (mem_support_iff.mpr hf) e he]
    rw [hp]
    exact target_weightPart_mem S hS hhom N w hw P _
  · rw [characterPart_zero_outside P.val c hc]
    exact Submodule.zero_mem _

theorem weight_eq_of_equationCharacter_eq (hn : 0 < n)
    (w : Fin n → ℤ) (hw : ∑ i, w i = 0)
    (e f : DegreeIndex n d →₀ ℕ) (he : equationCharacter e = equationCharacter f) :
    exponentWeight (coefficientWeights w) e = exponentWeight (coefficientWeights w) f := by
  have hp := congrArg (fun c : Fin n → ℤ => ∑ i, c i * w i) he
  dsimp only at hp
  rw [equationCharacter_pairing e w hw,equationCharacter_pairing f w hw] at hp
  exact mul_left_cancel₀ (by omega : (n : ℤ) ≠ 0) hp

/-- A full character component is a pure weight component for every
special-linear one-parameter subgroup, not just a separating subgroup. -/
theorem characterPart_pure_weight (hn : 0 < n)
    (P : MvPolynomial (DegreeIndex n d) K) (w : Fin n → ℤ) (hw : ∑ i, w i = 0)
    (e : DegreeIndex n d →₀ ℕ) :
    weightPart (characterPart P (equationCharacter e)) (coefficientWeights w)
      (exponentWeight (coefficientWeights w) e) = characterPart P (equationCharacter e) := by
  ext f
  simp only [coeff_weightPart,coeff_characterPart]
  by_cases hf : equationCharacter f = equationCharacter e
  · simp [hf,weight_eq_of_equationCharacter_eq hn w hw f e hf]
  · simp [hf]

end HessianTheorem11.UnconditionalOrbitIdeal

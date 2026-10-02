import HessianTheorem11.UnconditionalValuationPolynomial
import HessianTheorem11.UnconditionalPolynomialLift
import HessianTheorem11.UnconditionalOrbitFiniteCharacters

/-! From an integral diagonal degeneration to an actual special-linear
one-parameter weight meeting a closed invariant target. -/
noncomputable section
namespace HessianTheorem11.UnconditionalValuationRelative
open MvPolynomial PolynomialRestriction ReducedRelative UnconditionalOrbitIdeal
  UnconditionalValuationWeights

section Ordered
variable {E Γ : Type*} [Field E] [Infinite E]
  [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] {n d : ℕ}

/-- The finite active-character criterion turns weak/strict inequalities
in any ordered abelian group into an actual integral relative degeneration. -/
theorem relative_weight_of_ordered_support (hn : 0 < n)
    (F : MvPolynomial (Fin n) E) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) E)) (hclosed : coefficientClosed S)
    (hS : slInvariant S) (hhom : ∀ G ∈ S, G.IsHomogeneous d) (hnot : F ∉ S)
    (N : ℕ)
    (hgen : Ideal.span (boundedIdeal (finiteTarget (d := d) S) N :
      Set (MvPolynomial (DegreeIndex n d) E)) = vanishingIdeal E (finiteTarget (d := d) S))
    (x : Fin n → Γ) (hx : ∑ i, x i = 0)
    (hweak : ∀ e ∈ F.support,
      0 ≤ UnconditionalOrderedWeights.value (fun i => (e i : ℤ)) x)
    (hstrict : ∀ a ∈ activeCharacters (d := d) F S N,
      0 < UnconditionalOrderedWeights.value a x) :
    ∃ w : Fin n → ℤ, w ≠ 0 ∧ (∑ i, w i = 0) ∧ HasNonnegativeWeights F w ∧
      ∃ hw : ∑ i, w i = 0, 1 ≤ relativeOrder d F S (identityWeightFrame w hw) := by
  classical
  let M : Finset (Fin n → ℤ) := F.support.image (fun e i => (e i : ℤ))
  let T := activeCharacters (d := d) F S N
  have hM : ∀ a ∈ M, 0 ≤ UnconditionalOrderedWeights.value a x := by
    intro a ha
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp ha
    exact hweak e he
  obtain ⟨v,hv,hMv,hTv⟩ := UnconditionalOrderedWeights.exists_integral_weight x hx M T hM hstrict
  let w : Fin n → ℤ := fun i => (n : ℤ) * v i
  have hw : ∑ i, w i = 0 := by simp [w,←Finset.mul_sum,hv]
  have hdot (a : Fin n → ℤ) :
      (∑ i, a i * w i) = (n : ℤ) * ∑ i, a i * v i := by
    dsimp [w]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hW : HasNonnegativeWeights F w := by
    intro e he
    rw [monomialWeight,hdot]
    exact mul_nonneg (by positivity) (hMv _ (Finset.mem_image.mpr ⟨e,he,rfl⟩))
  have hT : ∀ a ∈ T, (n : ℤ) * (1 : ℕ) ≤ ∑ i, a i * w i := by
    intro a ha
    rw [hdot]
    have hp := hTv a ha
    have hn0 : (0 : ℤ) ≤ n := by positivity
    exact mul_le_mul_of_nonneg_left (by omega) hn0
  have hrel : 1 ≤ relativeOrder d F S (identityWeightFrame w hw) :=
    (le_relativeOrder_iff_activeCharacters hn F hF S hclosed hS hhom hnot
      w hw hW N 1 hgen).mpr hT
  refine ⟨w,?_,hw,hW,hw,hrel⟩
  intro hz
  obtain ⟨a,ha⟩ := activeCharacters_nonempty F hF S hclosed hhom hnot N hgen
  have hp := hT a ha
  simp [hz] at hp
  omega

end Ordered

section Lift
variable {K : Type*} [Field K] (V : ValuationSubring K) {n d : ℕ}

/-- Integral evaluation of an actual finite coefficient equation. The
coefficient vector here is defined over V, which need not be a field. -/
def integralEquationValue (F : MvPolynomial (Fin n) V)
    (P : MvPolynomial (DegreeIndex n d) V) : V :=
  eval (fun e => coeff e.val F) P

theorem map_integralEquationValue {E : Type*} [Field E] (f : V →+* E)
    (F : MvPolynomial (Fin n) V) (P : MvPolynomial (DegreeIndex n d) V) :
    f (integralEquationValue V F P) =
      eval (coefficientVector (map f F)) (map f P) := by
  rw [integralEquationValue,map_eval]
  have he : (f ∘ fun e : DegreeIndex n d => coeff e.val F) =
      coefficientVector (map f F) := by
    funext e
    simp [coefficientVector,coeff_map]
  rw [he]

/-- A residue character equation lifts with exactly the same monomials, so
its lift retains the same full special-linear character. -/
theorem exists_pure_character_lift
    (P : MvPolynomial (DegreeIndex n d) (IsLocalRing.ResidueField V)) (a : Fin n → ℤ) :
    ∃ p : MvPolynomial (DegreeIndex n d) V,
      map (IsLocalRing.residue V) p = characterPart P a ∧
      ∀ e ∈ p.support, equationCharacter e = a := by
  obtain ⟨p,hp,hsupp⟩ := UnconditionalPolynomialLift.exists_lift_same_support
    (IsLocalRing.residue V) IsLocalRing.residue_surjective (characterPart P a)
  refine ⟨p,hp,?_⟩
  intro e he
  rw [hsupp] at he
  by_contra h
  have hc := mem_support_iff.mp he
  rw [coeff_characterPart,if_neg h] at hc
  exact hc rfl

/-- Every active target character has an actual integral equation lift whose
source evaluation survives and whose target evaluation vanishes in residue. -/
theorem exists_active_equation_lift [Infinite (IsLocalRing.ResidueField V)]
    (hn : 0 < n) (F H : MvPolynomial (Fin n) V)
    (S : Set (MvPolynomial (Fin n) (IsLocalRing.ResidueField V)))
    (hS : slInvariant S) (hhom : ∀ G ∈ S, G.IsHomogeneous d)
    (hH : residuePolynomial V H ∈ S) (N : ℕ) (a : Fin n → ℤ)
    (ha : a ∈ activeCharacters (d := d) (residuePolynomial V F) S N) :
    ∃ p : MvPolynomial (DegreeIndex n d) V,
      (∀ e ∈ p.support, equationCharacter e = a) ∧
      integralEquationValue V F p ∉ IsLocalRing.maximalIdeal V ∧
      integralEquationValue V H p ∈ IsLocalRing.maximalIdeal V := by
  obtain ⟨P,hP⟩ := (mem_activeCharacters (residuePolynomial V F) S N a).mp ha
  obtain ⟨p,hp,hpure⟩ := exists_pure_character_lift V P.val a
  have hpart := target_characterPart_mem hn S hS hhom N P a
  have hzero : eval (coefficientVector (residuePolynomial V H)) (characterPart P.val a) = 0 :=
    ((mem_boundedIdeal _ _ _).mp hpart).1 _ ⟨residuePolynomial V H,hH,rfl⟩
  have hC : IsLocalRing.residue V (integralEquationValue V F p) =
      eval (coefficientVector (residuePolynomial V F)) (characterPart P.val a) := by
    rw [map_integralEquationValue,hp]
    rfl
  have hHz : IsLocalRing.residue V (integralEquationValue V H p) = 0 := by
    rw [map_integralEquationValue,hp]
    exact hzero
  refine ⟨p,hpure,?_,(IsLocalRing.residue_eq_zero_iff _).mp hHz⟩
  intro hmem
  apply hP
  rw [←hC]
  exact (IsLocalRing.residue_eq_zero_iff _).mpr hmem

/-- Centered SL characters are n times ordinary exponents. A corresponding
nth-power scaling identity still gives strict positivity in the value group. -/
theorem character_positive_of_power_relation (hn : 0 < n)
    (x : Fin n → Kˣ) (a : Fin n → ℤ) (c z : V)
    (hc : c ∉ IsLocalRing.maximalIdeal V) (hz : z ∈ IsLocalRing.maximalIdeal V)
    (he : (z : K)^n = (c : K)^n * ((∏ i, x i ^ a i : Kˣ) : K)) :
    0 < UnconditionalOrderedWeights.value a (fun i => weight V (x i)) := by
  apply character_positive V x a (c^n) (z^n)
  · intro h
    have hc0 : IsLocalRing.residue V c ≠ 0 := fun h0 =>
      hc ((IsLocalRing.residue_eq_zero_iff _).mp h0)
    have hp := (IsLocalRing.residue_eq_zero_iff _).mpr h
    rw [map_pow] at hp
    exact pow_ne_zero n hc0 hp
  · apply (IsLocalRing.residue_eq_zero_iff _).mp
    rw [map_pow,(IsLocalRing.residue_eq_zero_iff _).mpr hz]
    exact zero_pow (Nat.ne_of_gt hn)
  · simpa using he

end Lift
end HessianTheorem11.UnconditionalValuationRelative

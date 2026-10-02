import HessianTheorem11.UnconditionalOrbitRelativeSpeed
import Mathlib.Data.Fintype.Lattice

/-! Global maximization of the actual relative ideal order. There are only
finitely many pairs consisting of the form's monomial support and the
active characters of a fixed generating piece of the target ideal. Each
feasible pair has a proved integral optimum; a largest one is realized by
an actual special-linear coordinate frame. -/
noncomputable section
namespace HessianTheorem11.UnconditionalOrbitGlobal
open MvPolynomial PolynomialRestriction PolynomialWeightTransport RationalDescent ReducedRelative
  ReducedOrbitCoordinates UnconditionalOrbitIdeal UnconditionalOrbitWeights
open UnconditionalWeightMixed
variable {K : Type*} [Field K] [Infinite K] {n d : ℕ}

def monomialCharacter (e : Fin n →₀ ℕ) : Fin n → ℤ := fun i => e i

def weakCharacters (F : MvPolynomial (Fin n) K) : Finset (Fin n → ℤ) := by
  classical
  exact F.support.image monomialCharacter

theorem integralCharacter_monomial (e : Fin n →₀ ℕ) (w : Fin n → ℤ) :
    integralCharacter (monomialCharacter e) w = monomialWeight w e := rfl

theorem hasNonnegativeWeights_iff_weakCharacters
    (F : MvPolynomial (Fin n) K) (w : Fin n → ℤ) :
    HasNonnegativeWeights F w ↔ ∀ a ∈ weakCharacters F, 0 ≤ integralCharacter a w := by
  classical
  constructor
  · intro h a ha
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp ha
    exact h e he
  · intro h e he
    exact h _ (Finset.mem_image.mpr ⟨e,he,rfl⟩)

theorem weakCharacters_subset (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d) :
    weakCharacters F ⊆ (degreeMonomials n d).image monomialCharacter := by
  classical
  intro a ha
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp ha
  apply Finset.mem_image.mpr
  refine ⟨e,?_,rfl⟩
  apply Finset.mem_finsuppAntidiag'.mpr
  refine ⟨?_,Finset.subset_univ _⟩
  simpa [Finsupp.weight_apply,smul_eq_mul] using hF (Finsupp.mem_support_iff.mp he)

theorem mixed_feasible_of_integral (W T : Finset (Fin n → ℤ)) (w : Fin n → ℤ)
    (hw : ∑ i, w i = 0) (hW : ∀ a ∈ W, 0 ≤ integralCharacter a w)
    (hT : ∀ a ∈ T, 0 < integralCharacter a w) :
    (feasible W T).Nonempty := by
  refine ⟨UnconditionalWeightOptimization.realWeight w,by simp [hw],?_,?_⟩
  · intro a ha
    rw [character_realWeight]
    exact_mod_cast hW a ha
  · intro a ha
    rw [character_realWeight]
    exact_mod_cast (show 1 ≤ integralCharacter a w from hT a ha)

def relativeSupports (F : MvPolynomial (Fin n) K)
    (S : Set (MvPolynomial (Fin n) K)) (N : ℕ) :
    Set (Finset (Fin n → ℤ) × Finset (Fin n → ℤ)) :=
  {p | ∃ B : Matrix (Fin n) (Fin n) K, B.det = 1 ∧
    weakCharacters (restrict B F) = p.1 ∧
    activeCharacters (d := d) (restrict B F) S N = p.2 ∧
    (feasible p.1 p.2).Nonempty}

theorem relativeSupports_finite (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (N : ℕ) :
    (relativeSupports (d := d) F S N).Finite := by
  classical
  apply (((degreeMonomials n d).image monomialCharacter).powerset.product
    (possibleCharacters n d N).powerset).finite_toSet.subset
  rintro p ⟨B,hB,hW,hT,hfeas⟩
  apply Finset.mem_product.mpr
  constructor
  · rw [Finset.mem_powerset,← hW]
    exact weakCharacters_subset _ (homogeneous_restrict B F hF)
  · rw [Finset.mem_powerset,← hT]
    exact activeCharacters_subset _ S N

theorem relativeSupports_of_positive (hn : 0 < n)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (hclosed : coefficientClosed S)
    (hS : slInvariant S) (hhom : ∀ G ∈ S, G.IsHomogeneous d) (hnot : F ∉ S)
    (N : ℕ)
    (hgen : Ideal.span (boundedIdeal (finiteTarget (d := d) S) N :
      Set (MvPolynomial (DegreeIndex n d) K)) = vanishingIdeal K (finiteTarget (d := d) S))
    (f : WeightFrame K n) (hdet : f.matrix.det = 1)
    (hW : HasNonnegativeWeights (restrict f.matrix F) f.weight)
    (hpos : 0 < relativeOrder d F S f) :
    (weakCharacters (restrict f.matrix F),
      activeCharacters (d := d) (restrict f.matrix F) S N) ∈ relativeSupports (d := d) F S N := by
  refine ⟨f.matrix,hdet,rfl,rfl,mixed_feasible_of_integral _ _ f.weight f.sum_zero
    ((hasNonnegativeWeights_iff_weakCharacters _ _).mp hW) ?_⟩
  intro a ha
  have hh := (le_relativeOrder_iff_activeCharacters hn (restrict f.matrix F)
    (homogeneous_restrict f.matrix F hF) S hclosed hS hhom
    (restrict_not_mem_target F S hS hnot f.matrix hdet) f.weight f.sum_zero hW N
    (relativeOrder d F S f) hgen).mp
    (le_of_eq (relativeOrder_coordinate F hF S hclosed hS hhom hnot f hdet)) a ha
  exact lt_of_lt_of_le (mul_pos (by exact_mod_cast hn) (by exact_mod_cast hpos)) hh

/-- The normalized actual relative ideal order attains a positive maximum
among all admissible special-linear frames, including zero-weight competitors. -/
theorem exists_sl_maximizing_frame (hn : 0 < n)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (hclosed : coefficientClosed S)
    (hS : slInvariant S) (hhom : ∀ G ∈ S, G.IsHomogeneous d) (hnot : F ∉ S)
    (hpositive : ∃ f : WeightFrame K n, f.matrix.det = 1 ∧
      HasNonnegativeWeights (restrict f.matrix F) f.weight ∧ 0 < relativeOrder d F S f) :
    ∃ f : WeightFrame K n, SLMaximizingFrame d F S f := by
  classical
  obtain ⟨N,hgen⟩ := exists_boundedIdeal_generates (finiteTarget (d := d) S)
  let States := {p // p ∈ relativeSupports (d := d) F S N}
  letI : Finite States := (relativeSupports_finite F hF S N).to_subtype
  have hStates : Nonempty States := by
    obtain ⟨f,hdet,hW,hpos⟩ := hpositive
    exact ⟨⟨_,relativeSupports_of_positive hn F hF S hclosed hS hhom hnot N hgen f hdet hW hpos⟩⟩
  letI : Nonempty States := hStates
  have hnonempty (p : States) : p.val.2.Nonempty := by
    obtain ⟨B,hB,hW,hT,hfeas⟩ := p.property
    rw [← hT]
    exact activeCharacters_nonempty _ (homogeneous_restrict B F hF) S hclosed hhom
      (restrict_not_mem_target F S hS hnot B hB) N hgen
  have hfeasible (p : States) : (feasible p.val.1 p.val.2).Nonempty := by
    obtain ⟨B,hB,hW,hT,hfeas⟩ := p.property
    exact hfeas
  choose z hz using (fun p : States =>
    exists_fixed_support_maximizer p.val.1 p.val.2 (hnonempty p) (hfeasible p))
  obtain ⟨p,hpmax⟩ := Finite.exists_max (fun p : States => finiteSpeed p.val.2 (z p))
  obtain ⟨B,hB,hBW,hBT,_⟩ := p.property
  have hBinj : Function.Injective B.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (hB ▸ isUnit_one))
  let f : WeightFrame K n := ⟨B,hBinj,z p,(hz p).1⟩
  have hfW : HasNonnegativeWeights (restrict f.matrix F) f.weight := by
    apply (hasNonnegativeWeights_iff_weakCharacters _ _).mpr
    change ∀ a ∈ weakCharacters (restrict B F), 0 ≤ integralCharacter a (z p)
    rw [hBW]
    exact (hz p).2.1
  have hfspeed : relativeSpeed d F S f = finiteSpeed p.val.2 (z p) / n := by
    rw [relativeSpeed_eq_finiteSpeed_div hn F hF S hclosed hS hhom hnot f hB hfW N hgen]
    change finiteSpeed (activeCharacters (d := d) (restrict B F) S N) (z p) / n = _
    rw [hBT]
  have hfspeedpos : 0 < relativeSpeed d F S f := by
    rw [hfspeed]
    exact div_pos (hz p).2.2.2.1 (by exact_mod_cast hn)
  have hfpos : 0 < relativeOrder d F S f := by
    by_contra h
    have hzorder : relativeOrder d F S f = 0 := Nat.eq_zero_of_not_pos h
    simp [relativeSpeed,hzorder] at hfspeedpos
  have hfne : f.weight ≠ 0 := by
    intro he
    obtain ⟨a,ha⟩ := hnonempty p
    have hh := (hz p).2.2.1 a ha
    have he' : z p = 0 := he
    simp [integralCharacter,he'] at hh
  refine ⟨f,hB,hfne,hfW,hfpos,?_⟩
  intro g hgdet hgW
  by_cases hgpos : 0 < relativeOrder d F S g
  · let q : States := ⟨_,relativeSupports_of_positive hn F hF S hclosed hS hhom hnot
      N hgen g hgdet hgW hgpos⟩
    rw [hfspeed,relativeSpeed_eq_finiteSpeed_div hn F hF S hclosed hS hhom hnot g hgdet hgW N hgen]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact ((hz q).2.2.2.2 g.weight g.sum_zero
      ((hasNonnegativeWeights_iff_weakCharacters _ _).mp hgW)).trans (hpmax q)
  · have hzorder : relativeOrder d F S g = 0 := Nat.eq_zero_of_not_pos hgpos
    have hzero : relativeSpeed d F S g = 0 := by simp [relativeSpeed,hzorder]
    rw [hzero]
    exact hfspeedpos.le

end HessianTheorem11.UnconditionalOrbitGlobal

import CubicTenVariables.CubicTaylorExpansion
import HessianTheorem11.BibleHyperplaneRank
import Mathlib.Algebra.MvPolynomial.Funext

/-! The actual maximal affine vertex of a cubic over fields away from
characteristics two and three. Its kernel description and hyperplane rank
bound use the literal formal Hessian. Translation equivalence even holds
over finite fields; only the coordinate polynomial identity uses infinitude. -/

noncomputable section
namespace CubicTenVariables.ReducedCubicVertex
open MvPolynomial HessianTheorem11 Matrix Module PolynomialRestriction
open CubicTaylorExpansion
open scoped BigOperators

variable {K : Type*} [Field K] {n : ℕ}

/-- The actual linear Hessian-pencil kernel. -/
def affineVertex (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3) :
    Submodule K (Fin n → K) := LinearMap.ker (hessianLinearMap F hF)

@[simp] theorem mem_affineVertex (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (v : Fin n → K) :
    v ∈ affineVertex F hF ↔ hessian F v=0 := Iff.rfl

/-- Invariance of the actual polynomial function on every translated line. -/
def TranslationDirection (F : MvPolynomial (Fin n) K) (v : Fin n → K) : Prop :=
  ∀x : Fin n → K, ∀t : K, eval (x+t • v) F=eval x F

/-- Vanishing Hessian directions are true translations, not merely points
of the cubic. Both excluded characteristics are displayed. -/
theorem translation_of_hessian_zero (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (h2 : (2 : K)≠0) (h3 : (3 : K)≠0)
    (v : Fin n → K) (hv : hessian F v=0) : TranslationDirection F v := by
  have h6 : (6 : K)≠0 := by
    simpa only [show (2 : K)*3=6 by ring] using mul_ne_zero h2 h3
  have hfv : eval v F=0 := by
    have he := hessian_cubic_identity hF v
    rw [hv] at he
    exact (mul_eq_zero.mp (show 6*eval v F=0 by simpa using he.symm)).resolve_left h6
  have hq (x : Fin n → K) : quadraticAt F v x=0 := by
    have he := two_mul_quadraticAt F hF v x
    rw [hv] at he
    exact (mul_eq_zero.mp (show 2*quadraticAt F v x=0 by simpa using he)).resolve_left h2
  have hq' (x : Fin n → K) : quadraticAt F x v=0 := by
    have he := two_mul_quadraticAt F hF x v
    rw [hessian_polarization hF x v,hv] at he
    exact (mul_eq_zero.mp (show 2*quadraticAt F x v=0 by simpa using he)).resolve_left h2
  intro x t
  rw [eval_cubic_add_smul F hF,hfv,hq',show directional F x v=0 from hq x]
  simp

/-- Translation implies the actual zero Hessian. The proof uses t=1,-1
and the division-free quadratic polarization identity, so only 2 is excluded. -/
theorem hessian_zero_of_translation (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (h2 : (2 : K)≠0)
    (v : Fin n → K) (hv : TranslationDirection F v) : hessian F v=0 := by
  have h0 : eval (0 : Fin n → K) F=0 := by
    rw [eval_zero]
    change coeff 0 F=0
    exact hF.coeff_eq_zero (by simp)
  have hfv : eval v F=0 := by
    simpa using (hv 0 1).trans h0
  have hq (x : Fin n → K) : quadraticAt F v x=0 := by
    have hp := eval_cubic_add_smul F hF x v 1
    have hm := eval_cubic_add_smul F hF x v (-1)
    rw [hv x 1,hfv] at hp
    rw [hv x (-1),hfv] at hm
    simp only [one_pow,one_mul,mul_zero,add_zero] at hp
    simp only [neg_one_sq,one_mul,neg_one_mul,mul_zero,add_zero] at hm
    have hz : 2*quadraticAt F x v=0 := by linear_combination -hp-hm
    have hz' := (mul_eq_zero.mp hz).resolve_left h2
    change directional F x v=0
    rw [hz'] at hp
    linear_combination -hp
  have hp (a b : Fin n → K) : dotProduct a ((hessian F v).mulVec b)=0 := by
    have he := quadraticAt_add F hF v a b
    rw [hq,hq,hq] at he
    simpa using he.symm
  ext i j
  simpa [Matrix.mulVec,dotProduct,Pi.single_apply] using
    hp (Pi.single i 1) (Pi.single j 1)

theorem mem_affineVertex_iff_translation (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (h2 : (2 : K)≠0) (h3 : (3 : K)≠0)
    (v : Fin n → K) : v ∈ affineVertex F hF ↔ TranslationDirection F v :=
  ⟨translation_of_hessian_zero F hF h2 h3 v,
    hessian_zero_of_translation F hF h2 v⟩

/-- Every subspace of translation directions lies in this one maximal vertex. -/
theorem maximal_vertex (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (h2 : (2 : K)≠0) (h3 : (3 : K)≠0)
    (W : Submodule K (Fin n → K)) :
    W ≤ affineVertex F hF ↔ ∀v∈W,TranslationDirection F v := by
  simp only [SetLike.le_def,mem_affineVertex_iff_translation F hF h2 h3]

/-- All points of the maximal affine vertex lie on the actual cubic. -/
theorem eval_eq_zero_of_mem_affineVertex (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (h2 : (2 : K)≠0) (h3 : (3 : K)≠0)
    {v : Fin n → K} (hv : v∈affineVertex F hF) : eval v F=0 := by
  have ht := translation_of_hessian_zero F hF h2 h3 v hv
  have he := ht 0 1
  have h0 : eval (0 : Fin n → K) F=0 := by
    rw [eval_zero]
    change coeff 0 F=0
    exact hF.coeff_eq_zero (by simp)
  simpa using he.trans h0

/-- A concrete injective hyperplane frame sends every section vertex into
ambient Hessian rank at most two. This matrix implication is characteristic-free. -/
theorem ambient_rank_le_two_of_section_vertex {m : ℕ}
    (F : MvPolynomial (Fin (m+1)) K) (hF : F.IsHomogeneous 3)
    (B : Matrix (Fin (m+1)) (Fin m) K) (hB : Function.Injective B.mulVec)
    (v : Fin m → K)
    (hv : v∈affineVertex (restrict B F) (homogeneous_restrict B F hF)) :
    (hessian F (B.mulVec v)).rank≤2 := by
  apply BibleHyperplanes.rank_le_two_of_hyperplane_restriction_zero B hB
  rw [← hessian_restrict]
  exact hv

/-- The same rank conclusion starts from literal geometric translation
invariance of the hyperplane section; no kernel premise is supplied. -/
theorem ambient_rank_le_two_of_section_translation {m : ℕ}
    (F : MvPolynomial (Fin (m+1)) K) (hF : F.IsHomogeneous 3)
    (h2 : (2 : K)≠0)
    (B : Matrix (Fin (m+1)) (Fin m) K) (hB : Function.Injective B.mulVec)
    (v : Fin m → K) (hv : TranslationDirection (restrict B F) v) :
    (hessian F (B.mulVec v)).rank≤2 := by
  apply ambient_rank_le_two_of_section_vertex F hF B hB v
  exact hessian_zero_of_translation _ (homogeneous_restrict B F hF) h2 v hv

/-- Explicit characteristic-p specialization; no characteristic-zero
instance or infinite-field hypothesis is hidden in the translation criterion. -/
theorem mem_affineVertex_iff_translation_charP
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (p : ℕ) [CharP K p] (hp : 3<p) (v : Fin n → K) :
    v∈affineVertex F hF ↔ TranslationDirection F v := by
  apply mem_affineVertex_iff_translation F hF
  · exact (CharP.cast_eq_zero_iff K p 2).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  · exact (CharP.cast_eq_zero_iff K p 3).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by decide) hp)

/-- Restriction transports literal translation invariance through any matrix. -/
theorem translation_restrict {m : ℕ}
    (F : MvPolynomial (Fin n) K) (B : Matrix (Fin n) (Fin m) K)
    (v : Fin m → K) (hv : TranslationDirection F (B.mulVec v)) :
    TranslationDirection (restrict B F) v := by
  intro x t
  rw [eval_restrict,eval_restrict,Matrix.mulVec_add,Matrix.mulVec_smul]
  exact hv (B.mulVec x) t

/-- Setting one actual coordinate equal to zero in the polynomial. -/
def eraseCoordinate (F : MvPolynomial (Fin n) K) (j : Fin n) :
    MvPolynomial (Fin n) K := aeval (fun i => if i=j then 0 else X i) F

theorem eval_eraseCoordinate (F : MvPolynomial (Fin n) K)
    (j : Fin n) (x : Fin n → K) :
    eval x (eraseCoordinate F j)=eval (fun i => if i=j then 0 else x i) F := by
  classical
  change aeval x (aeval (fun i => if i=j then 0 else X i) F)=
    aeval (fun i => if i=j then 0 else x i) F
  rw [MvPolynomial.comp_aeval_apply]
  have he : (fun i => aeval x (if i=j then (0 : MvPolynomial (Fin n) K) else X i))=
      (fun i => if i=j then (0 : K) else x i) := by
    funext i
    by_cases hi : i=j <;> simp [hi]
  rw [he]

/-- The geometric translation criterion gives an actual polynomial equation
independent of the vertex coordinate, over an infinite field. -/
theorem eq_eraseCoordinate_of_translation [Infinite K]
    (F : MvPolynomial (Fin n) K) (j : Fin n)
    (hv : TranslationDirection F (Pi.single j 1)) : F=eraseCoordinate F j := by
  classical
  apply MvPolynomial.funext
  intro x
  rw [eval_eraseCoordinate]
  have he : (fun i => if i=j then (0 : K) else x i)=x+(-x j) • (Pi.single j (1 : K) : Fin n → K) := by
    funext i
    by_cases hi : i=j <;> simp [hi]
  rw [he]
  exact (hv x (-x j)).symm

/-- In every coordinate frame whose jth column lies in the maximal vertex,
the restricted polynomial is literally independent of coordinate j. For an
invertible frame this is the ordinary coordinate description of a cone. -/
theorem restrict_eq_eraseCoordinate_of_column_vertex [Infinite K] {m : ℕ}
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (h2 : (2 : K)≠0) (h3 : (3 : K)≠0)
    (B : Matrix (Fin n) (Fin m) K) (j : Fin m)
    (hj : B.mulVec (Pi.single j 1)∈affineVertex F hF) :
    restrict B F=eraseCoordinate (restrict B F) j := by
  apply eq_eraseCoordinate_of_translation
  exact translation_restrict F B _
    ((mem_affineVertex_iff_translation F hF h2 h3 _).mp hj)

/-- A cone direction is an actual nonzero invariant line; maximal_vertex
identifies all such lines simultaneously with one linear submodule. -/
def IsProjectiveCone (F : MvPolynomial (Fin n) K) : Prop :=
  ∃v : Fin n → K,v≠0 ∧ TranslationDirection F v

theorem isProjectiveCone_iff_vertex_ne_bot (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (h2 : (2 : K)≠0) (h3 : (3 : K)≠0) :
    IsProjectiveCone F ↔ affineVertex F hF≠⊥ := by
  rw [Submodule.ne_bot_iff]
  simp only [IsProjectiveCone,mem_affineVertex_iff_translation F hF h2 h3]
  exact ⟨fun ⟨v,hv,ht⟩ => ⟨v,ht,hv⟩,fun ⟨v,ht,hv⟩ => ⟨v,hv,ht⟩⟩

end CubicTenVariables.ReducedCubicVertex

import TranslatedDepthSeven.ConcreteIntegralCount
import TranslatedDepthSeven.ExplicitLineContribution
import Mathlib.Data.Int.Interval

/-!
# A literal product coordinate and its lattice fibres

The isolated-vertex reduction ultimately puts the vertex direction in the
first coordinate and makes all defining equations independent of that
coordinate.  This file records the two elementary consequences needed after
that algebraic change of variables:

* the common-zero condition is exactly the common-zero condition on the
  remaining coordinates; and
* in a box, forgetting the first coordinate has fibres of size at most
  `2 M + 1`.

No assertion that a vertex ideal has this form is made here.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

/-- Forget the distinguished first coordinate. -/
def dropFirstIntVector {n : ℕ} (x : IntVector (n + 1)) : IntVector n :=
  fun i => x i.succ

/-- Regard an equation in the remaining variables as an equation independent
of the distinguished first variable. -/
def liftPolynomialAfterFirst {R : Type*} [CommSemiring R] {n : ℕ}
    (f : MvPolynomial (Fin n) R) : MvPolynomial (Fin (n + 1)) R :=
  MvPolynomial.rename Fin.succ f

/-- The lift as an embedding.  Using an embedding makes finite-family
transport independent of a chosen `DecidableEq` instance. -/
def liftPolynomialAfterFirstEmbedding {R : Type*} [CommSemiring R] {n : ℕ} :
    MvPolynomial (Fin n) R ↪ MvPolynomial (Fin (n + 1)) R where
  toFun := liftPolynomialAfterFirst
  inj' := MvPolynomial.rename_injective Fin.succ (Fin.succ_injective n)

@[simp]
theorem eval_liftPolynomialAfterFirst {R : Type*} [CommSemiring R] {n : ℕ}
    (x : Fin (n + 1) → R) (f : MvPolynomial (Fin n) R) :
    MvPolynomial.eval x (liftPolynomialAfterFirst f) =
      MvPolynomial.eval (fun i => x i.succ) f := by
  rw [liftPolynomialAfterFirst, MvPolynomial.eval_rename]
  rfl

/-- Lift a finite equation family so that none of its members uses the first
coordinate. -/
def liftEquationFinsetAfterFirst {R : Type*} [CommSemiring R] {n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) R)) :
    Finset (MvPolynomial (Fin (n + 1)) R) :=
  equations.map liftPolynomialAfterFirstEmbedding

/-- The lifted equations impose precisely the original equations on the
remaining coordinates. -/
theorem integralCommonZero_liftEquationFinsetAfterFirst_iff {n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) ℤ))
    (x : IntVector (n + 1)) :
    IntegralCommonZero (liftEquationFinsetAfterFirst equations) x ↔
    IntegralCommonZero equations (dropFirstIntVector x) := by
  constructor
  · intro hx f hf
    have hlift : liftPolynomialAfterFirst f ∈
        liftEquationFinsetAfterFirst equations :=
      Finset.mem_map.mpr ⟨f, hf, rfl⟩
    simpa [dropFirstIntVector, liftPolynomialAfterFirstEmbedding] using
      hx (liftPolynomialAfterFirst f) hlift
  · intro hx g hg
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp hg
    simpa [dropFirstIntVector, liftPolynomialAfterFirstEmbedding] using hx f hf

/-- Adjoin a distinguished first coordinate to an integral vector. -/
def prependFirstIntVector {n : ℕ} (a : ℤ) (z : IntVector n) :
    IntVector (n + 1) :=
  Fin.cons a z

@[simp]
theorem prependFirstIntVector_zero {n : ℕ} (a : ℤ) (z : IntVector n) :
    prependFirstIntVector a z 0 = a := by
  rfl

@[simp]
theorem prependFirstIntVector_succ {n : ℕ} (a : ℤ) (z : IntVector n)
    (i : Fin n) :
    prependFirstIntVector a z i.succ = z i := by
  rfl

@[simp]
theorem dropFirstIntVector_prependFirstIntVector {n : ℕ}
    (a : ℤ) (z : IntVector n) :
    dropFirstIntVector (prependFirstIntVector a z) = z := by
  rfl

/-- Splitting off and adjoining the first coordinate are inverse operations. -/
def splitFirstIntVectorEquiv {n : ℕ} :
    IntVector (n + 1) ≃ ℤ × IntVector n :=
  (Fin.consEquiv (fun _ : Fin (n + 1) => ℤ)).symm

@[simp]
theorem splitFirstIntVectorEquiv_apply {n : ℕ} (x : IntVector (n + 1)) :
    splitFirstIntVectorEquiv x = (x 0, dropFirstIntVector x) := by
  rfl

@[simp]
theorem splitFirstIntVectorEquiv_symm_apply {n : ℕ}
    (p : ℤ × IntVector n) :
    splitFirstIntVectorEquiv.symm p = prependFirstIntVector p.1 p.2 := by
  rfl

/-- The integral interval available for the distinguished coordinate. -/
def symmetricIntegerInterval (M : ℕ) : Finset ℤ :=
  Finset.Icc (-(M : ℤ)) (M : ℤ)

@[simp]
theorem card_symmetricIntegerInterval (M : ℕ) :
    (symmetricIntegerInterval M).card = 2 * M + 1 := by
  rw [symmetricIntegerInterval, Int.card_Icc]
  omega

/-- The literal common zero set of a finite integral equation family inside
the symmetric sup-norm box. -/
def integralCommonZeroInBox {n M : ℕ}
    (equations : Finset (MvPolynomial (Fin n) ℤ)) :
    Finset (IntVector n) := by
  classical
  exact (integerSupNormBox n M).filter (IntegralCommonZero equations)

@[simp]
theorem mem_integralCommonZeroInBox_iff {n M : ℕ}
    (equations : Finset (MvPolynomial (Fin n) ℤ)) (x : IntVector n) :
    x ∈ integralCommonZeroInBox (M := M) equations ↔
      (∀ i, (x i).natAbs ≤ M) ∧ IntegralCommonZero equations x := by
  classical
  simp [integralCommonZeroInBox, mem_integerSupNormBox_iff]

/-- Inside a symmetric box, the common zero set of equations which omit the
first coordinate is literally the product of the first-coordinate interval
and the common zero set in the remaining coordinates. -/
theorem integralCommonZeroInBox_liftEquationFinsetAfterFirst_eq_product
    {n M : ℕ} (equations : Finset (MvPolynomial (Fin n) ℤ)) :
    integralCommonZeroInBox (M := M)
        (liftEquationFinsetAfterFirst equations) =
      (symmetricIntegerInterval M ×ˢ
          integralCommonZeroInBox (M := M) equations).map
        splitFirstIntVectorEquiv.symm.toEmbedding := by
  classical
  apply Finset.ext
  intro x
  constructor
  · intro hx
    obtain ⟨hbox, hzero⟩ :=
      (mem_integralCommonZeroInBox_iff
        (liftEquationFinsetAfterFirst equations) x).mp hx
    apply Finset.mem_map.mpr
    refine ⟨(x 0, dropFirstIntVector x), ?_, ?_⟩
    · apply Finset.mem_product.mpr
      constructor
      · rw [symmetricIntegerInterval, Finset.mem_Icc]
        have := hbox 0
        omega
      · apply (mem_integralCommonZeroInBox_iff equations _).mpr
        exact ⟨fun i => hbox i.succ,
          (integralCommonZero_liftEquationFinsetAfterFirst_iff
            equations x).mp hzero⟩
    · change splitFirstIntVectorEquiv.symm
          (splitFirstIntVectorEquiv x) = x
      exact splitFirstIntVectorEquiv.symm_apply_apply x
  · intro hx
    obtain ⟨p, hp, hpx⟩ := Finset.mem_map.mp hx
    rcases p with ⟨a, z⟩
    have hp' := Finset.mem_product.mp hp
    change splitFirstIntVectorEquiv.symm (a, z) = x at hpx
    rw [splitFirstIntVectorEquiv_symm_apply] at hpx
    rw [← hpx]
    apply (mem_integralCommonZeroInBox_iff
      (liftEquationFinsetAfterFirst equations) _).mpr
    constructor
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [prependFirstIntVector_zero]
        rw [symmetricIntegerInterval, Finset.mem_Icc] at hp'
        omega
      · rw [prependFirstIntVector_succ]
        exact (mem_integralCommonZeroInBox_iff equations z).mp hp'.2 |>.1 j
    · apply (integralCommonZero_liftEquationFinsetAfterFirst_iff
        equations _).mpr
      rw [dropFirstIntVector_prependFirstIntVector]
      exact (mem_integralCommonZeroInBox_iff equations z).mp hp'.2 |>.2

/-- Exact cardinality form of the product decomposition. -/
theorem card_integralCommonZeroInBox_liftEquationFinsetAfterFirst
    {n M : ℕ} (equations : Finset (MvPolynomial (Fin n) ℤ)) :
    (integralCommonZeroInBox (M := M)
      (liftEquationFinsetAfterFirst equations)).card =
        (2 * M + 1) *
          (integralCommonZeroInBox (M := M) equations).card := by
  rw [integralCommonZeroInBox_liftEquationFinsetAfterFirst_eq_product,
    Finset.card_map, Finset.card_product, card_symmetricIntegerInterval]

/-- Two vectors are equal when their first coordinates and their remaining
coordinate vectors are equal. -/
theorem intVector_ext_first_dropFirst {n : ℕ}
    {x y : IntVector (n + 1)}
    (hfirst : x 0 = y 0)
    (hrest : dropFirstIntVector x = dropFirstIntVector y) : x = y := by
  funext i
  refine Fin.cases hfirst ?_ i
  intro j
  exact congrFun hrest j

/-- In the coordinate box `|x_0| <= M`, every fibre of the projection which
forgets `x_0` has at most `2 M + 1` points. -/
theorem dropFirstIntVector_fibre_card_le {n M : ℕ}
    (points : Finset (IntVector (n + 1)))
    (hbox : ∀ x ∈ points, (x 0).natAbs ≤ M)
    (z : IntVector n) :
    (points.filter fun x => dropFirstIntVector x = z).card ≤ 2 * M + 1 := by
  classical
  let fibre := points.filter fun x => dropFirstIntVector x = z
  let firstImage : Finset ℤ := fibre.image fun x => x 0
  have hinjective : Set.InjOn (fun x : IntVector (n + 1) => x 0)
      (↑fibre : Set (IntVector (n + 1))) := by
    intro x hx y hy hxy
    apply intVector_ext_first_dropFirst hxy
    have hxrest : dropFirstIntVector x = z :=
      (Finset.mem_filter.mp hx).2
    have hyrest : dropFirstIntVector y = z :=
      (Finset.mem_filter.mp hy).2
    exact hxrest.trans hyrest.symm
  have hcard : firstImage.card = fibre.card :=
    Finset.card_image_iff.mpr hinjective
  have hsubset : firstImage ⊆ symmetricIntegerInterval M := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    have hxpoint := (Finset.mem_filter.mp hx).1
    have habs := hbox x hxpoint
    rw [symmetricIntegerInterval, Finset.mem_Icc]
    omega
  calc
    fibre.card = firstImage.card := hcard.symm
    _ ≤ (symmetricIntegerInterval M).card := Finset.card_le_card hsubset
    _ = 2 * M + 1 := card_symmetricIntegerInterval M

/-- Every quotient zero in the remaining-coordinate box has exactly the full
`2 M + 1` first-coordinate fibre in the lifted common zero set. -/
theorem dropFirstIntVector_fibre_card_eq_of_mem_integralCommonZeroInBox
    {n M : ℕ} (equations : Finset (MvPolynomial (Fin n) ℤ))
    (z : IntVector n)
    (hz : z ∈ integralCommonZeroInBox (M := M) equations) :
    ((integralCommonZeroInBox (M := M)
        (liftEquationFinsetAfterFirst equations)).filter
      fun x => dropFirstIntVector x = z).card = 2 * M + 1 := by
  classical
  calc
    ((integralCommonZeroInBox (M := M)
          (liftEquationFinsetAfterFirst equations)).filter
        fun x => dropFirstIntVector x = z).card =
        (symmetricIntegerInterval M).card := by
      symm
      apply Finset.card_bij
        (s := symmetricIntegerInterval M)
        (t := (integralCommonZeroInBox (M := M)
          (liftEquationFinsetAfterFirst equations)).filter
            fun x => dropFirstIntVector x = z)
        (fun a _ha => prependFirstIntVector a z)
      · intro a ha
        apply Finset.mem_filter.mpr
        constructor
        · apply (mem_integralCommonZeroInBox_iff
            (liftEquationFinsetAfterFirst equations) _).mpr
          obtain ⟨hzbox, hzzero⟩ :=
            (mem_integralCommonZeroInBox_iff equations z).mp hz
          constructor
          · intro i
            refine Fin.cases ?_ (fun j => ?_) i
            · rw [prependFirstIntVector_zero]
              rw [symmetricIntegerInterval, Finset.mem_Icc] at ha
              omega
            · rw [prependFirstIntVector_succ]
              exact hzbox j
          · apply (integralCommonZero_liftEquationFinsetAfterFirst_iff
              equations _).mpr
            simpa using hzzero
        · simp
      · intro a _ha b _hb hab
        have hfirst := congrFun hab 0
        simpa using hfirst
      · intro x hx
        obtain ⟨hxzeroBox, hxdrop⟩ := Finset.mem_filter.mp hx
        obtain ⟨hxbox, _hxzero⟩ :=
          (mem_integralCommonZeroInBox_iff
            (liftEquationFinsetAfterFirst equations) x).mp hxzeroBox
        refine ⟨x 0, ?_, ?_⟩
        · rw [symmetricIntegerInterval, Finset.mem_Icc]
          have := hxbox 0
          omega
        · apply intVector_ext_first_dropFirst
          · rfl
          · simpa using hxdrop.symm
    _ = 2 * M + 1 := card_symmetricIntegerInterval M

/-- Consequently a finite set in the same box has at most `2 M + 1` lifts
of each projected point. -/
theorem card_le_dropFirst_image_mul_interval {n M : ℕ}
    (points : Finset (IntVector (n + 1)))
    (hbox : ∀ x ∈ points, (x 0).natAbs ≤ M) :
    points.card ≤
      (points.image dropFirstIntVector).card * (2 * M + 1) := by
  classical
  apply finiteSet_card_le_index_card_mul_of_fibres
    points (points.image dropFirstIntVector) dropFirstIntVector (2 * M + 1)
  · intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · intro z _hz
    exact dropFirstIntVector_fibre_card_le points hbox z

/-- A finite set of zeros of equations which omit the first coordinate is
bounded by the exact first-coordinate interval times the corresponding
zero set in the remaining coordinates.  This is the form used to transfer a
quotient-point count back across an isolated vertex. -/
theorem card_le_interval_mul_integralCommonZeroInBox_of_lifted_equations
    {n M : ℕ} (equations : Finset (MvPolynomial (Fin n) ℤ))
    (points : Finset (IntVector (n + 1)))
    (hbox : ∀ x ∈ points, ∀ i, (x i).natAbs ≤ M)
    (hzero : ∀ x ∈ points,
      IntegralCommonZero (liftEquationFinsetAfterFirst equations) x) :
    points.card ≤ (2 * M + 1) *
      (integralCommonZeroInBox (M := M) equations).card := by
  classical
  have himage : points.image dropFirstIntVector ⊆
      integralCommonZeroInBox (M := M) equations := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    apply (mem_integralCommonZeroInBox_iff equations _).mpr
    exact ⟨fun i => hbox x hx i.succ,
      (integralCommonZero_liftEquationFinsetAfterFirst_iff
        equations x).mp (hzero x hx)⟩
  calc
    points.card ≤
        (points.image dropFirstIntVector).card * (2 * M + 1) :=
      card_le_dropFirst_image_mul_interval points
        (fun x hx => hbox x hx 0)
    _ ≤ (integralCommonZeroInBox (M := M) equations).card *
        (2 * M + 1) :=
      Nat.mul_le_mul_right _ (Finset.card_le_card himage)
    _ = (2 * M + 1) *
        (integralCommonZeroInBox (M := M) equations).card :=
      Nat.mul_comm _ _

end

end TranslatedDepthSeven

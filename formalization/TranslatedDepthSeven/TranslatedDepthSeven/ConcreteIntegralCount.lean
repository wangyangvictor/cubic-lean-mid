import TranslatedDepthSeven.IntegerBoxCount

/-!
# A literal finite set of translated integral points

This file replaces an informal predicate such as “points on the cone outside
the exceptional locus” by a concrete finite set built from integral
polynomials.  A closed piece is represented by the simultaneous zero set of
one finite family of equations; a finite family of such pieces represents
their union.  The geometry which supplies the correct equation families is a
separate obligation.
-/

namespace TranslatedDepthSeven

noncomputable section

open Finset

/-- Simultaneous integral vanishing of a literal finite equation family. -/
def IntegralCommonZero {n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) ℤ))
    (x : IntVector n) : Prop :=
  ∀ f ∈ equations, MvPolynomial.eval x f = 0

/-- The coordinate equations whose common integral zero set is exactly the
origin. -/
def coordinateEquationFinset (n : ℕ) :
    Finset (MvPolynomial (Fin n) ℤ) := by
  classical
  exact Finset.univ.image MvPolynomial.X

@[simp]
theorem mem_coordinateEquationFinset_iff {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) :
    f ∈ coordinateEquationFinset n ↔ ∃ i : Fin n, MvPolynomial.X i = f := by
  classical
  simp [coordinateEquationFinset]

/-- Literal identification of the common zero set of all coordinate
variables with the zero vector. -/
theorem integralCommonZero_coordinateEquationFinset_iff {n : ℕ}
    (x : IntVector n) :
    IntegralCommonZero (coordinateEquationFinset n) x ↔ x = 0 := by
  classical
  constructor
  · intro hx
    funext i
    have hi := hx (MvPolynomial.X i)
      (mem_coordinateEquationFinset_iff _ |>.2 ⟨i, rfl⟩)
    simpa using hi
  · intro hx
    subst x
    intro f hf
    obtain ⟨i, rfl⟩ := mem_coordinateEquationFinset_iff f |>.1 hf
    simp

/-- The point avoids the union of the common zero sets represented by
`closedPieces`.  Thus for each listed closed piece, at least one of its
displayed equations is nonzero at the point. -/
def AvoidsIntegralClosedPieces {n : ℕ}
    (closedPieces : Finset (Finset (MvPolynomial (Fin n) ℤ)))
    (x : IntVector n) : Prop :=
  ∀ equations ∈ closedPieces,
    ∃ f ∈ equations, MvPolynomial.eval x f ≠ 0

/-- `AvoidsIntegralClosedPieces` is literally avoidance of every simultaneous
zero set in the listed finite union. -/
theorem avoidsIntegralClosedPieces_iff {n : ℕ}
    (closedPieces : Finset (Finset (MvPolynomial (Fin n) ℤ)))
    (x : IntVector n) :
    AvoidsIntegralClosedPieces closedPieces x ↔
      ∀ equations ∈ closedPieces, ¬ IntegralCommonZero equations x := by
  classical
  simp [AvoidsIntegralClosedPieces, IntegralCommonZero]

/-- A literal finite set of integral points in the manuscript's translated
box and residue class, satisfying all main equations and avoiding every
listed closed piece.  The ambient box radius follows from
`|center_i| ≤ B` and `|x_i-center_i| ≤ L`. -/
def translatedIntegralPointFinset
    (p : Parameters)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (closedPieces : Finset (Finset (MvPolynomial (Fin 13) ℤ))) :
    Finset (IntVector 13) := by
  classical
  exact (integerSupNormBox 13 ⌈p.B + p.L⌉₊).filter fun x ↦
    p.InTranslatedBox (fun i ↦ (x i : ℝ)) ∧
      p.InResidueClass x ∧
      IntegralCommonZero equations x ∧
      AvoidsIntegralClosedPieces closedPieces x

/-- Every integral point in the translated box is contained in the explicit
ambient integral box used in `translatedIntegralPointFinset`. -/
theorem mem_integerSupNormBox_of_mem_translatedBox
    (p : Parameters) (x : IntVector 13)
    (hx : p.InTranslatedBox (fun i ↦ (x i : ℝ))) :
    x ∈ integerSupNormBox 13 ⌈p.B + p.L⌉₊ := by
  rw [mem_integerSupNormBox_iff]
  intro i
  have habs : |(x i : ℝ)| ≤ p.B + p.L := by
    calc
      |(x i : ℝ)| = |((x i : ℝ) - p.center i) + p.center i| := by ring_nf
      _ ≤ |(x i : ℝ) - p.center i| + |p.center i| := abs_add_le _ _
      _ ≤ p.L + p.B := add_le_add (hx i) (p.hcenter i)
      _ = p.B + p.L := add_comm _ _
  have hcast : ((x i).natAbs : ℝ) ≤ p.B + p.L := by
    simpa [Nat.cast_natAbs] using habs
  exact_mod_cast hcast.trans (Nat.le_ceil (p.B + p.L))

/-- Exact membership formula for the concrete counted finite set. -/
theorem mem_translatedIntegralPointFinset_iff
    (p : Parameters)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (closedPieces : Finset (Finset (MvPolynomial (Fin 13) ℤ)))
    (x : IntVector 13) :
    x ∈ translatedIntegralPointFinset p equations closedPieces ↔
      p.InTranslatedBox (fun i ↦ (x i : ℝ)) ∧
        p.InResidueClass x ∧
        IntegralCommonZero equations x ∧
        AvoidsIntegralClosedPieces closedPieces x := by
  classical
  constructor
  · intro hx
    exact (Finset.mem_filter.mp hx).2
  · intro hx
    exact Finset.mem_filter.mpr
      ⟨mem_integerSupNormBox_of_mem_translatedBox p x hx.1, hx⟩

/-- Including the coordinate equation family among the avoided closed pieces
removes the origin from the counted set. -/
theorem ne_zero_of_mem_translatedIntegralPointFinset
    (p : Parameters)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (closedPieces : Finset (Finset (MvPolynomial (Fin 13) ℤ)))
    (horigin : coordinateEquationFinset 13 ∈ closedPieces)
    {x : IntVector 13}
    (hx : x ∈ translatedIntegralPointFinset p equations closedPieces) :
    x ≠ 0 := by
  have havoid :=
    (mem_translatedIntegralPointFinset_iff p equations closedPieces x).mp hx |>.2.2.2
  have hnot :=
    (avoidsIntegralClosedPieces_iff closedPieces x).mp havoid
      (coordinateEquationFinset 13) horigin
  rwa [integralCommonZero_coordinateEquationFinset_iff] at hnot

/-- The concrete point set is bounded by its explicit ambient box. -/
theorem card_translatedIntegralPointFinset_le
    (p : Parameters)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (closedPieces : Finset (Finset (MvPolynomial (Fin 13) ℤ))) :
    (translatedIntegralPointFinset p equations closedPieces).card ≤
      (2 * ⌈p.B + p.L⌉₊ + 1) ^ 13 := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq
    (card_integerSupNormBox 13 ⌈p.B + p.L⌉₊)

end

end TranslatedDepthSeven

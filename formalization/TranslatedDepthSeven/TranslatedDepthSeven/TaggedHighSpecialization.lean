import TranslatedDepthSeven.LineProjectionSpecialization

/-!
# Discharging the high-direction line hypothesis

This file specializes the proved one-line congruence estimate to the
depth-seven split.  No estimate for a collection of lines is assumed.
For each occurrence label one supplies the literal primitive direction,
integral parameter, box containment, and residue congruence.  The fibre is
then bounded by the tagged-line theorem, and taking the maximum over the
finite occurrence set is an elementary `Finset.sup` operation.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- An integral version of `1 + U/X`.  The successor of `floor X` is used in
the denominator because a high direction has integral height strictly
larger than `floor X`. -/
def highLineNaturalMajorant (T : NNReal) : ℕ :=
  1 + ⌈(2 : NNReal) * uScale T⌉₊ / (⌊xScale T⌋₊ + 1)

/-- The integral tagged-line majorant is at most four times the canonical
factor `1 + U/X` whenever `T ≥ 1`. -/
theorem highLineNaturalMajorant_cast_le (T : NNReal) (hT : 1 ≤ T) :
    (highLineNaturalMajorant T : NNReal) ≤
      4 * primitiveTaggedHighFactor 1 T := by
  have hu : 1 ≤ uScale T :=
    NNReal.one_le_rpow hT (by norm_num)
  have hx : 0 < xScale T :=
    NNReal.rpow_pos (lt_of_lt_of_le zero_lt_one hT)
  have hceil : (⌈(2 : NNReal) * uScale T⌉₊ : NNReal) ≤
      3 * uScale T := by
    have hlt := Nat.ceil_lt_add_one
      (show 0 ≤ (2 : NNReal) * uScale T by positivity)
    have hle : (⌈(2 : NNReal) * uScale T⌉₊ : NNReal) ≤
        2 * uScale T + 1 := hlt.le
    calc
      (⌈(2 : NNReal) * uScale T⌉₊ : NNReal) ≤
          2 * uScale T + 1 := hle
      _ ≤ 2 * uScale T + uScale T := by gcongr
      _ = 3 * uScale T := by ring
  have hfloor : xScale T < (⌊xScale T⌋₊ + 1 : ℕ) := by
    simpa using Nat.lt_floor_add_one (xScale T)
  have hdiv :
      ((⌈(2 : NNReal) * uScale T⌉₊ /
          (⌊xScale T⌋₊ + 1) : ℕ) : NNReal) ≤
        3 * uScale T / xScale T := by
    calc
      ((⌈(2 : NNReal) * uScale T⌉₊ /
          (⌊xScale T⌋₊ + 1) : ℕ) : NNReal) ≤
          (⌈(2 : NNReal) * uScale T⌉₊ : NNReal) /
            (⌊xScale T⌋₊ + 1 : ℕ) := Nat.cast_div_le
      _ ≤ 3 * uScale T / xScale T := by
        apply div_le_div₀ (by positivity) hceil hx hfloor.le
  have hratio : 1 ≤ uScale T / xScale T := by
    rw [uScale_div_xScale hT]
    exact NNReal.one_le_rpow hT (by norm_num)
  rw [highLineNaturalMajorant]
  norm_num only [Nat.cast_add, Nat.cast_one]
  calc
    1 + ((⌈(2 : NNReal) * uScale T⌉₊ /
      (⌊xScale T⌋₊ + 1) : ℕ) : NNReal) ≤
        1 + 3 * (uScale T / xScale T) := by
          simpa [mul_div_assoc] using add_le_add_left hdiv 1
    _ ≤ 4 * (uScale T / xScale T) := by
      calc
        1 + 3 * (uScale T / xScale T) ≤
            (uScale T / xScale T) + 3 * (uScale T / xScale T) := by
          simpa [add_comm] using
            add_le_add_right hratio (3 * (uScale T / xScale T))
        _ = 4 * (uScale T / xScale T) := by ring
    _ ≤ 4 * primitiveTaggedHighFactor 1 T := by
      simp only [primitiveTaggedHighFactor]
      gcongr
      exact le_add_of_nonneg_left (by positivity)

theorem highLineNaturalMajorant_bound :
    UniformPowerBound
      (fun _H T ↦ (highLineNaturalMajorant T : NNReal))
      highDirectionFactorExponent := by
  intro ε hε
  obtain ⟨C, hC⟩ :=
    (primitiveTaggedHighFactor_bound.const_mul 4) ε hε
  refine ⟨C, ?_⟩
  intro H T hH hT hTH
  exact (highLineNaturalMajorant_cast_le T hT).trans
    (hC H T hH hT hTH)

/-- A high-direction occurrence fibre satisfies the canonical natural
majorant by the literal tagged-line estimate. -/
theorem highLineFibre_card_le_naturalMajorant
    {Point : Type*} [DecidableEq Point] {n : ℕ}
    (points : Finset Point) (parameter : Point → ℤ)
    (hParameter : Set.InjOn parameter (↑points : Set Point))
    (h y₀ residue : IntVector n) (center : RealVector n)
    (T : NNReal) {r : ℕ} (hr : 0 < r)
    (hPrimitive : PrimitiveDirection h)
    (hHeight : lowDirectionNaturalRadius T < directionHeight h)
    (hBox : ∀ x ∈ points, ∀ i,
      |((y₀ i + parameter x * h i : ℤ) : ℝ) - center i| ≤ uScale T)
    (hResidue : ∀ x ∈ points, ∀ i,
      y₀ i + parameter x * h i ≡ residue i [ZMOD (r : ℤ)]) :
    points.card ≤ highLineNaturalMajorant T := by
  have hTagged := highLineFibre_card_le_tagged
    points parameter hParameter h y₀ residue center hr hPrimitive hBox hResidue
  have hden : lowDirectionNaturalRadius T + 1 ≤
      r * directionHeight h := by
    have hrOne : 1 ≤ r := hr
    have hheight : lowDirectionNaturalRadius T + 1 ≤ directionHeight h := by
      omega
    have hmul : directionHeight h ≤ r * directionHeight h := by
      nlinarith
    exact hheight.trans hmul
  have hpos : 0 < lowDirectionNaturalRadius T + 1 := Nat.zero_lt_succ _
  calc
    points.card ≤
        1 + ⌈2 * (uScale T : ℝ)⌉₊ /
          (r * directionHeight h) := hTagged
    _ ≤ 1 + ⌈2 * (uScale T : ℝ)⌉₊ /
          (lowDirectionNaturalRadius T + 1) := by
      simpa [add_comm] using
        add_le_add_left (Nat.div_le_div_left hden hpos) 1
    _ = highLineNaturalMajorant T := by
      simp only [highLineNaturalMajorant, lowDirectionNaturalRadius]
      congr 2

/-- The actual high fibre attached to an occurrence label. -/
def highOccurrenceFibre
    {Point Occurrence Direction : Type*}
    [DecidableEq Point] [DecidableEq Occurrence] [DecidableEq Direction]
    (points : Finset Point)
    (smoothDirections singularDirections : Finset Direction)
    (occurrence : Point → Occurrence) (direction : Point → Direction)
    (o : Occurrence) : Finset Point :=
  points.filter fun x ↦
    direction x ∉ smoothDirections ∧
      direction x ∉ singularDirections ∧ occurrence x = o

/-- The largest actual high occurrence fibre.  This is a definition, not an
assumed line estimate. -/
def maximumHighOccurrenceFibre
    {Point Occurrence Direction : Type*}
    [DecidableEq Point] [DecidableEq Occurrence] [DecidableEq Direction]
    (points : Finset Point) (occurrences : Finset Occurrence)
    (smoothDirections singularDirections : Finset Direction)
    (occurrence : Point → Occurrence) (direction : Point → Direction) : ℕ :=
  occurrences.sup fun o ↦
    (highOccurrenceFibre points smoothDirections singularDirections
      occurrence direction o).card

theorem highOccurrenceFibre_card_le_maximum
    {Point Occurrence Direction : Type*}
    [DecidableEq Point] [DecidableEq Occurrence] [DecidableEq Direction]
    (points : Finset Point) (occurrences : Finset Occurrence)
    (smoothDirections singularDirections : Finset Direction)
    (occurrence : Point → Occurrence) (direction : Point → Direction)
    {o : Occurrence} (ho : o ∈ occurrences) :
    (highOccurrenceFibre points smoothDirections singularDirections
      occurrence direction o).card ≤
      maximumHighOccurrenceFibre points occurrences smoothDirections
        singularDirections occurrence direction := by
  exact Finset.le_sup (f := fun o ↦
    (highOccurrenceFibre points smoothDirections singularDirections
      occurrence direction o).card) ho

/-- If each literal occurrence fibre has its displayed tagged-line data,
then their actual maximum has the required exponent `4/21`. -/
theorem maximumHighOccurrenceFibre_bound_of_tagged_data
    {Point Occurrence Direction : Type*}
    [DecidableEq Point] [DecidableEq Occurrence] [DecidableEq Direction]
    {n : ℕ}
    (points : NNReal → NNReal → Finset Point)
    (occurrences : NNReal → NNReal → Finset Occurrence)
    (smoothDirections singularDirections :
      NNReal → NNReal → Finset Direction)
    (occurrence : NNReal → NNReal → Point → Occurrence)
    (direction : NNReal → NNReal → Point → Direction)
    (parameter : NNReal → NNReal → Occurrence → Point → ℤ)
    (lineDirection lineBase residue :
      NNReal → NNReal → Occurrence → IntVector n)
    (center : NNReal → NNReal → Occurrence → RealVector n)
    (modulus : NNReal → NNReal → Occurrence → ℕ)
    (hParameter : ∀ H T o, o ∈ occurrences H T →
      Set.InjOn (parameter H T o)
        (↑(highOccurrenceFibre (points H T)
          (smoothDirections H T) (singularDirections H T)
          (occurrence H T) (direction H T) o) : Set Point))
    (hModulus : ∀ H T o, o ∈ occurrences H T → 0 < modulus H T o)
    (hPrimitive : ∀ H T o, o ∈ occurrences H T →
      PrimitiveDirection (lineDirection H T o))
    (hHeight : ∀ H T o, o ∈ occurrences H T →
      lowDirectionNaturalRadius T < directionHeight (lineDirection H T o))
    (hBox : ∀ H T o, o ∈ occurrences H T →
      ∀ x ∈ highOccurrenceFibre (points H T)
        (smoothDirections H T) (singularDirections H T)
        (occurrence H T) (direction H T) o, ∀ i,
      |((lineBase H T o i + parameter H T o x *
          lineDirection H T o i : ℤ) : ℝ) - center H T o i| ≤ uScale T)
    (hResidue : ∀ H T o, o ∈ occurrences H T →
      ∀ x ∈ highOccurrenceFibre (points H T)
        (smoothDirections H T) (singularDirections H T)
        (occurrence H T) (direction H T) o, ∀ i,
      lineBase H T o i + parameter H T o x * lineDirection H T o i ≡
        residue H T o i [ZMOD (modulus H T o : ℤ)]) :
    UniformPowerBound
      (fun H T ↦
        (maximumHighOccurrenceFibre (points H T) (occurrences H T)
          (smoothDirections H T) (singularDirections H T)
          (occurrence H T) (direction H T) : NNReal))
      highDirectionFactorExponent := by
  intro ε hε
  obtain ⟨C, hC⟩ := highLineNaturalMajorant_bound ε hε
  refine ⟨C, ?_⟩
  intro H T hH hT hTH
  apply le_trans _ (hC H T hH hT hTH)
  simp only [maximumHighOccurrenceFibre]
  exact_mod_cast Finset.sup_le fun o ho ↦
    highLineFibre_card_le_naturalMajorant
      (highOccurrenceFibre (points H T)
        (smoothDirections H T) (singularDirections H T)
        (occurrence H T) (direction H T) o)
      (parameter H T o) (hParameter H T o ho)
      (lineDirection H T o) (lineBase H T o) (residue H T o)
      (center H T o) T (hModulus H T o ho)
      (hPrimitive H T o ho) (hHeight H T o ho)
      (hBox H T o ho) (hResidue H T o ho)

end

end TranslatedDepthSeven

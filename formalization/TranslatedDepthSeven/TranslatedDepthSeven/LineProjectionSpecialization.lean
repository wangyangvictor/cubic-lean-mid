import TranslatedDepthSeven.ExplicitLineContribution

/-!
# Concrete finite-projection inputs for the low-direction line calculation

This file removes the two abstract low-direction cardinality estimates from
the line ledger.  A displayed map with fibres of size at most `D` into a
`d`-dimensional integral box gives the required count by summing its fibres.
The only geometry left in an application is therefore the construction of
the literal projection and the verification of its fibre bound.

At the depth-seven line split the projective direction height is
`X = T^(2/21)`.  A five-coordinate projection gives exponent `10/21`, while
a four-coordinate projection gives exponent `8/21`.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- The elementary majorant attached to a `d`-coordinate integral projection
with fibres of cardinality at most `D`. -/
def finiteProjectionBoxMajorant
    (d D : ℕ) (radius : NNReal → NNReal → ℕ) : CountFunction :=
  fun H T ↦ (D * (2 * radius H T + 1) ^ d : ℕ)

private theorem constantOne_uniformPowerBound_zero :
    UniformPowerBound (fun _H _T ↦ 1) 0 := by
  intro ε hε
  refine ⟨1, ?_⟩
  intro H T hH hT _hTH
  have hHpow : 1 ≤ H ^ ε := NNReal.one_le_rpow hH hε.le
  have hTpow : 1 ≤ T ^ ε := NNReal.one_le_rpow hT hε.le
  calc
    1 = 1 * 1 := by simp
    _ ≤ H ^ ε * T ^ ε :=
      mul_le_mul hHpow hTpow (by positivity) (by positivity)
    _ = powerEnvelope 1 H T 0 ε := by simp [powerEnvelope]

/-- Fixed natural powers multiply the exponent of a uniform power bound. -/
theorem UniformPowerBound.natPow
    {f : CountFunction} {a : ℝ} (hf : UniformPowerBound f a) (d : ℕ) :
    UniformPowerBound (fun H T ↦ (f H T) ^ d) ((d : ℝ) * a) := by
  induction d with
  | zero =>
      simpa using constantOne_uniformPowerBound_zero
  | succ d ih =>
      have hmul := ih.mul hf
      simpa [pow_succ, Nat.cast_add, add_mul] using hmul

/-- Polynomial growth of the radius gives the expected `d`-dimensional
box bound.  This is purely elementary and contains no point-counting input. -/
theorem finiteProjectionBoxMajorant_bound
    (d D : ℕ) (radius : NNReal → NNReal → ℕ) {s : ℝ}
    (hs : 0 ≤ s)
    (hRadius : UniformPowerBound
      (fun H T ↦ (radius H T : NNReal)) s) :
    UniformPowerBound
      (finiteProjectionBoxMajorant d D radius) ((d : ℝ) * s) := by
  have hOne : UniformPowerBound (fun _H _T ↦ 1) s :=
    constantOne_uniformPowerBound_zero.weaken hs
  have hRadiusPlusOne : UniformPowerBound
      (fun H T ↦ (radius H T : NNReal) + 1) s :=
    hRadius.add hOne
  have hTwiceRadiusPlusOne : UniformPowerBound
      (fun H T ↦ 2 * ((radius H T : NNReal) + 1)) s :=
    hRadiusPlusOne.const_mul 2
  have hBase : UniformPowerBound
      (fun H T ↦ 2 * (radius H T : NNReal) + 1) s := by
    apply UniformPowerBound.mono _ hTwiceRadiusPlusOne
    intro H T
    calc
      2 * (radius H T : NNReal) + 1 ≤
          2 * (radius H T : NNReal) + 2 := by gcongr; norm_num
      _ = 2 * ((radius H T : NNReal) + 1) := by ring
  have hPow : UniformPowerBound
      (fun H T ↦ (2 * (radius H T : NNReal) + 1) ^ d)
      ((d : ℝ) * s) := hBase.natPow d
  have hD : UniformPowerBound
      (fun H T ↦ (D : NNReal) *
        (2 * (radius H T : NNReal) + 1) ^ d)
      ((d : ℝ) * s) := hPow.const_mul D
  apply UniformPowerBound.mono _ hD
  intro H T
  change ((D * (2 * radius H T + 1) ^ d : ℕ) : NNReal) ≤ _
  norm_num

/-- A literal bounded-fibre projection into an integral box supplies a
uniform direction-count bound. -/
theorem directionCount_uniformPowerBound_of_finiteProjection
    {Direction : Type*} [DecidableEq Direction]
    (directions : NNReal → NNReal → Finset Direction)
    {d : ℕ} (projection : NNReal → NNReal → Direction → IntVector d)
    (radius : NNReal → NNReal → ℕ) (D : ℕ) {s : ℝ}
    (hBox : ∀ H T h, h ∈ directions H T → ∀ i,
      (projection H T h i).natAbs ≤ radius H T)
    (hFibre : ∀ H T z,
      ((directions H T).filter fun h ↦ projection H T h = z).card ≤ D)
    (hs : 0 ≤ s)
    (hRadius : UniformPowerBound
      (fun H T ↦ (radius H T : NNReal)) s) :
    UniformPowerBound
      (fun H T ↦ ((directions H T).card : NNReal)) ((d : ℝ) * s) := by
  apply UniformPowerBound.mono _
    (finiteProjectionBoxMajorant_bound d D radius hs hRadius)
  intro H T
  have hcard := finiteSet_card_le_fibre_mul_integerBox
    (directions H T) (projection H T) (radius H T) D
    (hBox H T) (hFibre H T)
  change ((directions H T).card : NNReal) ≤
    ((D * (2 * radius H T + 1) ^ d : ℕ) : NNReal)
  exact_mod_cast (by simpa [Nat.mul_comm] using hcard)

/-- The canonical radius `floor X` has exponent `2/21`. -/
def lowDirectionNaturalRadius (T : NNReal) : ℕ := ⌊xScale T⌋₊

theorem lowDirectionNaturalRadius_bound :
    UniformPowerBound
      (fun _H T ↦ (lowDirectionNaturalRadius T : NNReal)) (2 / 21) := by
  have hScale : UniformPowerBound
      (fun _H T ↦ (T ^ (2 / 21 : ℝ)) ^ (1 : ℝ))
      ((2 / 21 : ℝ) * 1) :=
    ScalePowerLaw.toUniformPowerBound (by norm_num)
      (scaleFunction_scalePowerLaw (2 / 21 : ℝ) 1 (by norm_num))
  have hRadius : UniformPowerBound
      (fun _H T ↦ (lowDirectionNaturalRadius T : NNReal))
      ((2 / 21 : ℝ) * 1) := by
    apply UniformPowerBound.mono _ hScale
    intro H T
    change (↑⌊xScale T⌋₊ : NNReal) ≤ (T ^ (2 / 21 : ℝ)) ^ (1 : ℝ)
    simpa [lowDirectionNaturalRadius, xScale] using
      (Nat.floor_le (a := xScale T) (show 0 ≤ xScale T by positivity))
  simpa only [mul_one] using hRadius

/-- Five projected coordinates give the smooth low-direction exponent. -/
theorem smoothDirectionCount_uniformPowerBound_of_finiteProjection
    {Direction : Type*} [DecidableEq Direction]
    (directions : NNReal → NNReal → Finset Direction)
    (projection : NNReal → NNReal → Direction → IntVector 5)
    (D : ℕ)
    (hBox : ∀ H T h, h ∈ directions H T → ∀ i,
      (projection H T h i).natAbs ≤ lowDirectionNaturalRadius T)
    (hFibre : ∀ H T z,
      ((directions H T).filter fun h ↦ projection H T h = z).card ≤ D) :
    UniformPowerBound
      (fun H T ↦ ((directions H T).card : NNReal))
      smoothLowDirectionExponent := by
  have h := directionCount_uniformPowerBound_of_finiteProjection
    directions projection (fun _H T ↦ lowDirectionNaturalRadius T) D
    hBox hFibre (by norm_num : (0 : ℝ) ≤ 2 / 21)
    lowDirectionNaturalRadius_bound
  convert h using 1
  norm_num [smoothLowDirectionExponent]

/-- Four projected coordinates give the singular low-direction exponent. -/
theorem singularDirectionCount_uniformPowerBound_of_finiteProjection
    {Direction : Type*} [DecidableEq Direction]
    (directions : NNReal → NNReal → Finset Direction)
    (projection : NNReal → NNReal → Direction → IntVector 4)
    (D : ℕ)
    (hBox : ∀ H T h, h ∈ directions H T → ∀ i,
      (projection H T h i).natAbs ≤ lowDirectionNaturalRadius T)
    (hFibre : ∀ H T z,
      ((directions H T).filter fun h ↦ projection H T h = z).card ≤ D) :
    UniformPowerBound
      (fun H T ↦ ((directions H T).card : NNReal))
      singularLowDirectionExponent := by
  have h := directionCount_uniformPowerBound_of_finiteProjection
    directions projection (fun _H T ↦ lowDirectionNaturalRadius T) D
    hBox hFibre (by norm_num : (0 : ℝ) ≤ 2 / 21)
    lowDirectionNaturalRadius_bound
  convert h using 1
  norm_num [singularLowDirectionExponent]

/-- The natural integral radius `floor T` used by the three-dimensional
projection of a smooth star. -/
def terminalNaturalRadius (T : NNReal) : ℕ := ⌊T⌋₊

theorem terminalNaturalRadius_bound :
    UniformPowerBound
      (fun _H T ↦ (terminalNaturalRadius T : NNReal)) 1 := by
  have hScale : UniformPowerBound
      (fun _H T ↦ (T ^ (1 : ℝ)) ^ (1 : ℝ)) ((1 : ℝ) * 1) :=
    ScalePowerLaw.toUniformPowerBound (by norm_num)
      (scaleFunction_scalePowerLaw (1 : ℝ) 1 (by norm_num))
  have hRadius : UniformPowerBound
      (fun _H T ↦ (terminalNaturalRadius T : NNReal)) ((1 : ℝ) * 1) := by
    apply UniformPowerBound.mono _ hScale
    intro H T
    change (↑⌊T⌋₊ : NNReal) ≤ (T ^ (1 : ℝ)) ^ (1 : ℝ)
    simpa [terminalNaturalRadius] using
      (Nat.floor_le (a := T) (show 0 ≤ T by positivity))
  simpa only [one_mul] using hRadius

end

end TranslatedDepthSeven

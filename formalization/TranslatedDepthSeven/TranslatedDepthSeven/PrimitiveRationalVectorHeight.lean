import Mathlib.LinearAlgebra.Matrix.Integer

/-!
# Primitive height of a finite rational vector

This file gives the literal LCM/GCD normalization of a finite rational
vector and proves that its height is unchanged by a nonzero rational scalar.
The proof is the elementary uniqueness of a primitive integral
representative of a rational line.
-/

namespace TranslatedDepthSeven

noncomputable section

open Matrix

lemma rat_den_dvd_int_of_mul_eq_int (q : ℚ) (z w : ℤ)
    (h : q * (z : ℚ) = (w : ℚ)) : q.den ∣ z.natAbs := by
  have hq : (q.num : ℚ) * (z : ℚ) = (q.den : ℚ) * (w : ℚ) := by
    calc
      (q.num : ℚ) * (z : ℚ) = (q * q.den) * (z : ℚ) := by rw [Rat.mul_den_eq_num]
      _ = (q.den : ℚ) * (q * (z : ℚ)) := by ac_rfl
      _ = (q.den : ℚ) * (w : ℚ) := congrArg ((q.den : ℚ) * ·) h
  have hz : q.num * z = (q.den : ℤ) * w := by
    exact_mod_cast hq
  have habs := congrArg Int.natAbs hz
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at habs
  apply q.reduced.symm.dvd_of_dvd_mul_left
  use w.natAbs

variable {ι : Type*} [Fintype ι]

/-- The GCD of the absolute coordinates of an integral vector. -/
def intVectorContent (z : ι → ℤ) : ℕ :=
  Finset.univ.gcd (fun i ↦ (z i).natAbs)

/-- A literal primitive integral vector has content one. -/
def IsPrimitiveIntVector (z : ι → ℤ) : Prop :=
  intVectorContent z = 1

lemma rat_den_eq_one_of_primitive_proportional
    (q : ℚ) (z w : ι → ℤ) (hz : IsPrimitiveIntVector z)
    (h : ∀ i, (w i : ℚ) = q * (z i : ℚ)) : q.den = 1 := by
  have hd : q.den ∣ intVectorContent z := by
    apply Finset.dvd_gcd
    intro i hi
    exact rat_den_dvd_int_of_mul_eq_int q (z i) (w i) (h i).symm
  rw [hz] at hd
  exact Nat.dvd_one.mp hd

lemma primitive_proportional_scalar_eq_one_or_neg_one
    (q : ℚ) (z w : ι → ℤ) (hq : q ≠ 0)
    (hz : IsPrimitiveIntVector z) (hw : IsPrimitiveIntVector w)
    (h : ∀ i, (w i : ℚ) = q * (z i : ℚ)) : q = 1 ∨ q = -1 := by
  have hdq : q.den = 1 := rat_den_eq_one_of_primitive_proportional q z w hz h
  have hinv : ∀ i, (z i : ℚ) = q⁻¹ * (w i : ℚ) := by
    intro i
    rw [h i]
    simp [hq]
  have hdqi : q⁻¹.den = 1 :=
    rat_den_eq_one_of_primitive_proportional q⁻¹ w z hw hinv
  have hqnum : (q.num : ℚ) = q := (Rat.den_eq_one_iff q).mp hdq
  have hqinum : (q⁻¹.num : ℚ) = q⁻¹ := (Rat.den_eq_one_iff q⁻¹).mp hdqi
  have hmulQ : ((q.num * q⁻¹.num : ℤ) : ℚ) = 1 := by
    rw [Int.cast_mul, hqnum, hqinum, mul_inv_cancel₀ hq]
  have hmulZ : q.num * q⁻¹.num = 1 := by
    exact_mod_cast hmulQ
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hmulZ with hn | hn
  · left
    rw [← hqnum, hn]
    simp
  · right
    rw [← hqnum, hn]
    simp

lemma primitive_proportional_natAbs_eq
    (q : ℚ) (z w : ι → ℤ) (hq : q ≠ 0)
    (hz : IsPrimitiveIntVector z) (hw : IsPrimitiveIntVector w)
    (h : ∀ i, (w i : ℚ) = q * (z i : ℚ)) :
    ∀ i, (w i).natAbs = (z i).natAbs := by
  rcases primitive_proportional_scalar_eq_one_or_neg_one q z w hq hz hw h with hq1 | hq1
  · intro i
    have hiQ : (w i : ℚ) = (z i : ℚ) := by simpa [hq1] using h i
    have hi : w i = z i := by exact_mod_cast hiQ
    rw [hi]
  · intro i
    have hiQ : (w i : ℚ) = -(z i : ℚ) := by simpa [hq1] using h i
    have hi : w i = -z i := by exact_mod_cast hiQ
    rw [hi, Int.natAbs_neg]

/-- A one-row matrix containing a finite rational vector. -/
def rationalVectorRow (v : ι → ℚ) : Matrix (Fin 1) ι ℚ :=
  fun _ i ↦ v i

/-- The LCM of the coordinate denominators. -/
def rationalVectorDenominator (v : ι → ℚ) : ℕ :=
  (rationalVectorRow v).den

/-- The integral coordinate obtained by clearing the LCM denominator. -/
def integralRationalVectorCoordinate (v : ι → ℚ) (i : ι) : ℤ :=
  (rationalVectorRow v).num 0 i

/-- The content of the cleared integral vector. -/
def integralRationalVectorContent (v : ι → ℚ) : ℕ :=
  intVectorContent (integralRationalVectorCoordinate v)

/-- The signed primitive integral coordinate. -/
def primitiveRationalVectorCoordinate (v : ι → ℚ) (i : ι) : ℤ :=
  integralRationalVectorCoordinate v i / (integralRationalVectorContent v : ℤ)

/-- The maximum absolute primitive coordinate. -/
def primitiveRationalVectorHeight (v : ι → ℚ) : ℕ :=
  Finset.univ.sup (fun i ↦ (primitiveRationalVectorCoordinate v i).natAbs)

lemma integralRationalVectorCoordinate_div_denominator (v : ι → ℚ) (i : ι) :
    (integralRationalVectorCoordinate v i : ℚ) /
        (rationalVectorDenominator v : ℚ) = v i := by
  exact Matrix.num_div_den (rationalVectorRow v) 0 i

lemma integralRationalVectorContent_dvd (v : ι → ℚ) (i : ι) :
    integralRationalVectorContent v ∣ (integralRationalVectorCoordinate v i).natAbs := by
  exact Finset.gcd_dvd (Finset.mem_univ i)

lemma integralRationalVectorCoordinate_ne_zero_of_ne_zero
    (v : ι → ℚ) {i : ι} (hi : v i ≠ 0) :
    integralRationalVectorCoordinate v i ≠ 0 := by
  intro hz
  have h := integralRationalVectorCoordinate_div_denominator v i
  rw [hz, Int.cast_zero, zero_div] at h
  exact hi h.symm

lemma exists_integralRationalVectorCoordinate_ne_zero
    (v : ι → ℚ) (hv : v ≠ 0) :
    ∃ i, integralRationalVectorCoordinate v i ≠ 0 := by
  have hex : ∃ i, v i ≠ 0 := by
    by_contra hn
    apply hv
    funext i
    by_contra hi
    exact hn ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, integralRationalVectorCoordinate_ne_zero_of_ne_zero v hi⟩

lemma integralRationalVectorContent_ne_zero
    (v : ι → ℚ) (hv : v ≠ 0) :
    integralRationalVectorContent v ≠ 0 := by
  rw [integralRationalVectorContent, intVectorContent, Finset.gcd_ne_zero_iff]
  obtain ⟨i, hi⟩ := exists_integralRationalVectorCoordinate_ne_zero v hv
  exact ⟨i, Finset.mem_univ i, Int.natAbs_ne_zero.mpr hi⟩

lemma primitiveRationalVectorCoordinate_natAbs (v : ι → ℚ) (i : ι) :
    (primitiveRationalVectorCoordinate v i).natAbs =
      (integralRationalVectorCoordinate v i).natAbs /
        integralRationalVectorContent v := by
  apply Int.natAbs_ediv_of_dvd
  exact Int.natCast_dvd.mpr (integralRationalVectorContent_dvd v i)

lemma primitiveRationalVectorCoordinate_isPrimitive
    (v : ι → ℚ) (hv : v ≠ 0) :
    IsPrimitiveIntVector (primitiveRationalVectorCoordinate v) := by
  simp only [IsPrimitiveIntVector, intVectorContent,
    primitiveRationalVectorCoordinate_natAbs]
  obtain ⟨i, hi⟩ := exists_integralRationalVectorCoordinate_ne_zero v hv
  exact Finset.gcd_div_eq_one (Finset.mem_univ i)
    (Int.natAbs_ne_zero.mpr hi)

/-- The rational factor relating the primitive integral vector to the
original rational vector. -/
def primitiveRationalVectorScale (v : ι → ℚ) : ℚ :=
  (rationalVectorDenominator v : ℚ) /
    (integralRationalVectorContent v : ℚ)

lemma rationalVectorDenominator_ne_zero (v : ι → ℚ) :
    rationalVectorDenominator v ≠ 0 := by
  exact Matrix.den_ne_zero (rationalVectorRow v)

lemma primitiveRationalVectorScale_ne_zero
    (v : ι → ℚ) (hv : v ≠ 0) :
    primitiveRationalVectorScale v ≠ 0 := by
  apply div_ne_zero
  · exact_mod_cast rationalVectorDenominator_ne_zero v
  · exact_mod_cast integralRationalVectorContent_ne_zero v hv

lemma primitiveRationalVectorCoordinate_cast
    (v : ι → ℚ) (hv : v ≠ 0) (i : ι) :
    (primitiveRationalVectorCoordinate v i : ℚ) =
      primitiveRationalVectorScale v * v i := by
  have hcontent : (integralRationalVectorContent v : ℤ) ∣
      integralRationalVectorCoordinate v i := by
    exact Int.natCast_dvd.mpr (integralRationalVectorContent_dvd v i)
  have hmulZ := Int.ediv_mul_cancel hcontent
  have hmulQ : (primitiveRationalVectorCoordinate v i : ℚ) *
      (integralRationalVectorContent v : ℚ) =
      (integralRationalVectorCoordinate v i : ℚ) := by
    exact_mod_cast hmulZ
  have hg : (integralRationalVectorContent v : ℚ) ≠ 0 := by
    exact_mod_cast integralRationalVectorContent_ne_zero v hv
  have hD : (rationalVectorDenominator v : ℚ) ≠ 0 := by
    exact_mod_cast rationalVectorDenominator_ne_zero v
  have hprim : (primitiveRationalVectorCoordinate v i : ℚ) =
      (integralRationalVectorCoordinate v i : ℚ) /
        (integralRationalVectorContent v : ℚ) :=
    (eq_div_iff hg).mpr hmulQ
  have hnum : (integralRationalVectorCoordinate v i : ℚ) =
      (rationalVectorDenominator v : ℚ) * v i := by
    have h := (div_eq_iff hD).mp
      (integralRationalVectorCoordinate_div_denominator v i)
    simpa [mul_comm] using h
  rw [hprim, hnum]
  simp only [primitiveRationalVectorScale, div_eq_mul_inv]
  ac_rfl

/-- Primitive projective height is invariant under a nonzero rational
scalar. -/
theorem primitiveRationalVectorHeight_smul
    (v : ι → ℚ) (r : ℚ) (hv : v ≠ 0) (hr : r ≠ 0) :
    primitiveRationalVectorHeight (r • v) =
      primitiveRationalVectorHeight v := by
  have hw : r • v ≠ 0 := smul_ne_zero hr hv
  let q : ℚ := primitiveRationalVectorScale (r • v) * r *
    (primitiveRationalVectorScale v)⁻¹
  have hq : q ≠ 0 := by
    dsimp [q]
    exact mul_ne_zero
      (mul_ne_zero (primitiveRationalVectorScale_ne_zero (r • v) hw) hr)
      (inv_ne_zero (primitiveRationalVectorScale_ne_zero v hv))
  have hprop : ∀ i,
      (primitiveRationalVectorCoordinate (r • v) i : ℚ) =
        q * (primitiveRationalVectorCoordinate v i : ℚ) := by
    intro i
    rw [primitiveRationalVectorCoordinate_cast (r • v) hw i,
      primitiveRationalVectorCoordinate_cast v hv i]
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      primitiveRationalVectorScale (r • v) * (r * v i) =
          (primitiveRationalVectorScale (r • v) * r) * v i := by
            rw [mul_assoc]
      _ = (primitiveRationalVectorScale (r • v) * r) *
          ((primitiveRationalVectorScale v)⁻¹ *
            (primitiveRationalVectorScale v * v i)) := by
            apply congrArg ((primitiveRationalVectorScale (r • v) * r) * ·)
            rw [← mul_assoc,
              inv_mul_cancel₀ (primitiveRationalVectorScale_ne_zero v hv), one_mul]
      _ = q * (primitiveRationalVectorScale v * v i) := by
            dsimp [q]
            ac_rfl
  have habs := primitive_proportional_natAbs_eq q
    (primitiveRationalVectorCoordinate v)
    (primitiveRationalVectorCoordinate (r • v)) hq
    (primitiveRationalVectorCoordinate_isPrimitive v hv)
    (primitiveRationalVectorCoordinate_isPrimitive (r • v) hw) hprop
  unfold primitiveRationalVectorHeight
  apply Finset.sup_congr rfl
  intro i hi
  exact habs i

end

end TranslatedDepthSeven

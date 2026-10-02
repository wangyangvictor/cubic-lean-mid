import TranslatedDepthSeven.PrimitiveRationalVectorHeight
import TranslatedDepthSeven.TaggedLineCount

/-!
# Primitive normalization without increasing integral coordinates

The finite integer Bezout identity converts content-one normalization to
the primitive-direction predicate used by the line and plane estimates.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- The gcd of finitely many integers is an integral linear combination. -/
lemma exists_intLinearCombination_eq_finset_gcd
    {ι : Type*} [Fintype ι]
    (s : Finset ι) (z : ι → ℤ) :
    ∃ c : ι → ℤ,
      ∑ i ∈ s, c i * z i =
        ((s.gcd (fun i ↦ (z i).natAbs) : ℕ) : ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨c, hc⟩ := ih
      let g : ℤ := ((s.gcd (fun i ↦ (z i).natAbs) : ℕ) : ℤ)
      let A : ℤ := (z a).gcdA g
      let B : ℤ := (z a).gcdB g
      refine ⟨fun i ↦ if i = a then A else B * c i, ?_⟩
      rw [Finset.sum_insert ha]
      have hsum : ∑ i ∈ s, (if i = a then A else B * c i) * z i =
          B * ∑ i ∈ s, c i * z i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [show i ≠ a from fun hia ↦ ha (hia ▸ hi), ↓reduceIte]
        ring
      rw [hsum, hc]
      change (if a = a then A else B * c a) * z a +
        B * ((s.gcd (fun i ↦ (z i).natAbs) : ℕ) : ℤ) = _
      rw [if_pos rfl]
      calc
        A * z a + B * g = z a * A + g * B := by ring
        _ = ((z a).gcd g : ℤ) := (Int.gcd_eq_gcd_ab (z a) g).symm
        _ = _ := by
          simp [g, Finset.gcd_insert, Int.gcd]
          exact congrArg Nat.cast
            (gcd_eq_nat_gcd (z a).natAbs
              (s.gcd fun i ↦ (z i).natAbs)).symm

theorem IsPrimitiveIntVector.primitiveDirection
    {n : ℕ} {h : IntVector n} (hp : IsPrimitiveIntVector h) :
    PrimitiveDirection h := by
  obtain ⟨c, hc⟩ :=
    exists_intLinearCombination_eq_finset_gcd
      (Finset.univ : Finset (Fin n)) h
  refine ⟨c, ?_⟩
  rw [hc]
  unfold IsPrimitiveIntVector intVectorContent at hp
  exact_mod_cast hp

/-- Dividing the coordinates of an integral vector by their gcd cannot
increase any absolute coordinate. -/
theorem primitiveRationalVectorCoordinate_intCast_natAbs_le
    {n : ℕ} (z : IntVector n) (i : Fin n) :
    (primitiveRationalVectorCoordinate (fun j ↦ (z j : ℚ)) i).natAbs ≤
      (z i).natAbs := by
  rw [primitiveRationalVectorCoordinate_natAbs]
  have hnum : integralRationalVectorCoordinate
      (fun j ↦ (z j : ℚ)) i = z i := by
    change ((show Matrix (Fin 1) (Fin n) ℤ from fun _ j ↦ z j).map
      (fun t : ℤ ↦ (t : ℚ))).num 0 i = _
    rw [Matrix.num_map_intCast]
  rw [hnum]
  exact Nat.div_le_self _ _

/-- A nonzero integral vector has a primitive rationally proportional
representative with no larger absolute coordinate. -/
theorem exists_bounded_primitiveDirection_of_ne_zero
    {n : ℕ} (z : IntVector n) (hz : z ≠ 0) :
    ∃ h : IntVector n, ∃ r : ℚ,
      PrimitiveDirection h ∧ r ≠ 0 ∧
      (∀ i, (h i : ℚ) = r * (z i : ℚ)) ∧
      (∀ i, (h i).natAbs ≤ (z i).natAbs) := by
  let v : Fin n → ℚ := fun i ↦ (z i : ℚ)
  have hv : v ≠ 0 := by
    intro hzero
    apply hz
    funext i
    have hi := congrFun hzero i
    change (z i : ℚ) = 0 at hi
    exact_mod_cast hi
  refine ⟨primitiveRationalVectorCoordinate v,
    primitiveRationalVectorScale v,
    (primitiveRationalVectorCoordinate_isPrimitive v hv).primitiveDirection,
    primitiveRationalVectorScale_ne_zero v hv,
    primitiveRationalVectorCoordinate_cast v hv, ?_⟩
  exact primitiveRationalVectorCoordinate_intCast_natAbs_le z

end

end TranslatedDepthSeven

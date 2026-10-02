import CubicTenVariables.HessianProfileRoots
import CubicTenVariables.TranslatedHessianRankCount
import CubicTenVariables.MatrixSmithOneDigit

/-!
# One-digit fibers of the actual Hessian profile

An integral center fixes the matrix translation before the new digit is
chosen. The digit parametrization then embeds the literal root fiber into
the translated Hessian rank locus. The new root equation may be discarded
for this upper bound, while the original fiber retains it.
-/

noncomputable section
namespace CubicTenVariables.HessianProfileLifts
open MvPolynomial HessianTheorem11 MatrixSmithProfileInvariant
open HessianProfileRoots SmoothResidueLifting PrimePowerFibers

variable {n : ℕ}

theorem digit_profile_entry (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (p : ℕ) (hp : p.Prime) (a : ℕ) (y : Fin n → ℤ) (x : Fin n → ZMod p) :
    profileEntry F p (a+1) (digitLift p a y x) a =
      entry (hessian F y + (p : ℤ)^a • hessian F (fun i => (x i).val)) p a := by
  have heq : digitLift p a y x =
      (fun i => ((y + (p : ℤ)^a • (fun j => ((x j).val : ℤ))) i : ZMod (p^(a+1)))) := by
    funext i
    simp only [digitLift, Nat.cast_pow, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq, profileEntry_int_cast F p hp (by omega), hessian_add hF, hessian_smul hF]

theorem digit_hessian_map (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [NeZero p]
    (x : Fin n → ZMod p) :
    (hessian F (fun i => ((x i).val : ℤ))).map (Int.castRingHom (ZMod p)) =
      matrix F p x := by
  rw [matrix_int_cast]
  congr 1
  funext i
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- Adapter from the general matrix theorem. The matrix premise is
discharged by the proved one-digit theorem in the final endpoint below. -/
theorem exists_digit_rank_bound_of_matrix_bound
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (p : ℕ) (hp : p.Prime) (a : ℕ) (y : Fin n → ℤ)
    (hstep : ∃ T : Matrix (Fin n) (Fin n) (ZMod p),
      ∀ B : Matrix (Fin n) (Fin n) ℤ,
        (T + B.map (Int.castRingHom (ZMod p))).rank ≤
          entry (hessian F y) p (a-1) + entry (hessian F y + (p : ℤ)^a • B) p a) :
    ∃ T : Matrix (Fin n) (Fin n) (ZMod p), ∀ x : Fin n → ZMod p,
      (T + matrix F p x).rank ≤
        entry (hessian F y) p (a-1) + profileEntry F p (a+1) (digitLift p a y x) a := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨T,hT⟩ := hstep
  refine ⟨T, fun x => ?_⟩
  simpa only [digit_hessian_map, digit_profile_entry F hF p hp] using
    hT (hessian F (fun i => ((x i).val : ℤ)))

/-- The literal fiber embeds into one translated rank locus. Both profile
entries in its rank label are those of the actual prescribed sequence. -/
theorem card_fiber_le_of_digit_bound
    (F : MvPolynomial (Fin 10) ℤ) (p : ℕ) [Fact p.Prime]
    (a : ℕ) (ha : 1 ≤ a) (c : ℕ → ℕ) (y : Fin 10 → ZMod (p^a))
    (hy : y ∈ roots F p a c)
    (hstep : ∀ yZ : Fin 10 → ℤ,
      ∃ T : Matrix (Fin 10) (Fin 10) (ZMod p), ∀ x : Fin 10 → ZMod p,
        (T + matrix F p x).rank ≤
          entry (hessian F yZ) p (a-1) + profileEntry F p (a+1) (digitLift p a yZ x) a) :
    ∃ T : Matrix (Fin 10) (Fin 10) (ZMod p),
      ((roots F p (a+1) c).filter fun z =>
        (fun i => reduction p (Nat.le_succ a) (z i)) = y).card ≤
          TranslatedHessianRankCount.count F p T (c (a-1)+c a) := by
  classical
  let yZ : Fin 10 → ℤ := fun i => (y i).val
  have hyZ : (fun i => (yZ i : ZMod (p^a))) = y := by
    funext i
    simp [yZ]
  have hold : entry (hessian F yZ) p (a-1) = c (a-1) := by
    have hh := (mem_roots F p a c y).mp hy
    rw [← profileEntry_int_cast F p Fact.out (a := a) (i := a-1) (by omega) yZ, hyZ]
    exact hh.2 (a-1) (by omega)
  obtain ⟨T,hT⟩ := hstep yZ
  refine ⟨T, ?_⟩
  let S := (roots F p (a+1) c).filter fun z =>
    (fun i => reduction p (Nat.le_succ a) (z i)) = y
  let e := digitLiftEquiv p a yZ
  let fiberPoint (z : {z // z ∈ S}) :
      {z : Fin 10 → ZMod (p^(a+1)) //
        ∀ i, reduction p (Nat.le_succ a) (z i) = (yZ i : ZMod (p^a))} :=
    ⟨z.val, fun i => (congrFun (Finset.mem_filter.mp z.property).2 i).trans
      (congrFun hyZ i).symm⟩
  have hlift (z : {z // z ∈ S}) : digitLift p a yZ (e.symm (fiberPoint z)) = z.val := by
    exact congrArg Subtype.val (e.apply_symm_apply (fiberPoint z))
  let f : {z // z ∈ S} → {x : Fin 10 → ZMod p //
      (T + matrix F p x).rank ≤ c (a-1)+c a} := fun z =>
    ⟨e.symm (fiberPoint z), by
      have hz := (mem_roots F p (a+1) c z.val).mp (Finset.mem_filter.mp z.property).1
      have ht := hT (e.symm (fiberPoint z))
      rwa [hold, hlift, hz.2 a (by omega)] at ht⟩
  have hf : Function.Injective f := by
    intro z z' h
    have hx := congrArg Subtype.val h
    have hz := congrArg (digitLift p a yZ) hx
    rw [hlift, hlift] at hz
    exact Subtype.ext hz
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, TranslatedHessianRankCount.count,
    matrix] using hc

/-- A fixed integral center gives a fixed translation before any next
digit; the matrix transition theorem is proved, not supplied as input. -/
theorem exists_digit_rank_bound
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (p : ℕ) (hp : p.Prime) (a : ℕ) (ha : 1 ≤ a) (y : Fin n → ℤ) :
    ∃ T : Matrix (Fin n) (Fin n) (ZMod p), ∀ x : Fin n → ZMod p,
      (T + matrix F p x).rank ≤
        entry (hessian F y) p (a-1) + profileEntry F p (a+1) (digitLift p a y x) a :=
  exists_digit_rank_bound_of_matrix_bound F hF p hp a y
    (MatrixSmithOneDigit.exists_translated_rank_bound (hessian F y) p hp a ha)

/-- One constant precedes every prime, level, profile and actual center.
This transition bound uses no literature premise. -/
theorem exists_uniform_fiber_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime],
      ∀ (a : ℕ), 1 ≤ a → ∀ (c : ℕ → ℕ) (y : Fin 10 → ZMod (p^a)),
        y ∈ roots F p a c →
        ((roots F p (a+1) c).filter fun z =>
          (fun i => reduction p (Nat.le_succ a) (z i)) = y).card ≤
            C*p^(TranslatedHessianLeadingGeometry.tauNat (c (a-1)+c a)) := by
  obtain ⟨C,hC,hcount⟩ := TranslatedHessianRankCount.exists_uniform_bound F hF hA
  refine ⟨C,hC,?_⟩
  intro p hp a ha c y hy
  obtain ⟨T,hT⟩ := card_fiber_le_of_digit_bound F p a ha c y hy
    (exists_digit_rank_bound F hF p hp.out a ha)
  exact hT.trans (hcount p hp.out T (c (a-1)+c a))

end CubicTenVariables.HessianProfileLifts

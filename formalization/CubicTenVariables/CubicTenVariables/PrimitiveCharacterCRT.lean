import CubicTenVariables.WeightedCRTAdapters

/-! Exact CRT for the full primitive scalar character sum. The inverse
modulus twists are absorbed by permutations of the actual unit groups. -/
noncomputable section
namespace CubicTenVariables.PrimitiveCharacterCRT
open CRTCharacters PrimeSumAdapter
open scoped BigOperators Classical

def characterSum (q : ℕ) [NeZero q] (z : ZMod q) : ℂ :=
  ∑ u : (ZMod q)ˣ, ZMod.stdAddChar ((u : ZMod q)*z)

theorem sum_ite_coprime_eq_units (q : ℕ) [NeZero q] (f : ZMod q → ℂ) :
    (∑ a : ZMod q, if Nat.Coprime a.val q then f a else 0) =
      ∑ u : (ZMod q)ˣ, f u := by
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun a : ZMod q => Nat.Coprime a.val q)
    (fun a => if Nat.Coprime a.val q then f a else 0)
  have he : (∑ a : {a : ZMod q // Nat.Coprime a.val q}, f a) =
      ∑ u : (ZMod q)ˣ, f u := by
    exact (Equiv.sum_comp (ZMod.unitsEquivCoprime (n := q)) (fun a => f a.val)).symm
  have hneg (a : {a : ZMod q // ¬ Nat.Coprime a.val q}) : ¬ Nat.Coprime (a:ZMod q).val q := a.property
  simp only [hneg, ite_false, Finset.sum_const_zero, add_zero] at hs
  refine hs.symm.trans (Eq.trans ?_ he)
  apply Finset.sum_congr rfl
  intro a ha
  exact if_pos a.property

theorem sum_fin_eq (q : ℕ) [NeZero q] (z : ℤ) :
    (∑ a : Fin q, if Nat.Coprime a.val q then
      residueExponential q ((a.val:ℤ)*z) else 0) = characterSum q (z:ZMod q) := by
  calc
    _ = ∑ a : ZMod q, if Nat.Coprime a.val q then
        ZMod.stdAddChar (a*(z:ZMod q)) else 0 := by
      apply Fintype.sum_equiv (finResidueEquiv q)
      intro a
      simp only [finResidueEquiv_apply, ZMod.val_natCast_of_lt a.is_lt,
        residueExponential_eq_stdAddChar, Int.cast_mul, Int.cast_natCast]
    _ = _ := sum_ite_coprime_eq_units q _

theorem sum_twist (q : ℕ) [NeZero q] (t : (ZMod q)ˣ) (z : ZMod q) :
    (∑ u : (ZMod q)ˣ, ZMod.stdAddChar ((t:ZMod q)*(u:ZMod q)*z)) =
      characterSum q z := by
  exact Equiv.sum_comp (Equiv.mulLeft t)
    (fun u : (ZMod q)ˣ => ZMod.stdAddChar ((u:ZMod q)*z))

theorem characterSum_crt {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (z : ZMod (m*n)) :
    characterSum (m*n) z =
      characterSum m (leftProjection h z) * characterSum n (rightProjection h z) := by
  calc
    _ = ∑ a : (ZMod m)ˣ × (ZMod n)ˣ,
        ZMod.stdAddChar ((leftTwist h:ZMod m)*(a.1:ZMod m)*leftProjection h z) *
        ZMod.stdAddChar ((rightTwist h:ZMod n)*(a.2:ZMod n)*rightProjection h z) := by
      apply Fintype.sum_equiv (unitEquiv h)
      intro u
      rw [stdAddChar_crt h]
      simp only [map_mul, unitEquiv_fst_coe, unitEquiv_snd_coe, mul_assoc]
    _ = (∑ u : (ZMod m)ˣ,
        ZMod.stdAddChar ((leftTwist h:ZMod m)*(u:ZMod m)*leftProjection h z)) *
        (∑ u : (ZMod n)ˣ,
        ZMod.stdAddChar ((rightTwist h:ZMod n)*(u:ZMod n)*rightProjection h z)) := by
      rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    _ = _ := by rw [sum_twist, sum_twist]

end CubicTenVariables.PrimitiveCharacterCRT

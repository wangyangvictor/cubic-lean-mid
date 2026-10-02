import CubicTenVariables.LocalizedFourierCRT
import CubicTenVariables.ResidueUnitInvariant
import CubicTenVariables.CubicGradientScaling

/-! The actual localized Fourier sum is unchanged by multiplying its
frequency by a residue unit. Homogeneity and scalar-unit stability of the
restriction are explicit; no such assertion is made for arbitrary sets. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalizedFourierUnit
open MvPolynomial PrimitiveCharacterCRT LocalizedFourierCRT
open scoped BigOperators Classical

theorem characterSum_unit_mul (q : ℕ) [NeZero q]
    (u : (ZMod q)ˣ) (z : ZMod q) :
    characterSum q ((u : ZMod q)*z) = characterSum q z := by
  simpa only [characterSum,mul_assoc,mul_left_comm,mul_comm] using sum_twist q u z

/-- Unit-scaled homogeneous polynomial values have the same primitive
numerator character sum. -/
theorem characterSum_homogeneous_smul {n d q A : ℕ} [NeZero q]
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous d)
    (f : ZMod A →+* ZMod q) (u : (ZMod A)ˣ) (x : Fin n → ZMod A) :
    characterSum q (eval₂ (Int.castRingHom (ZMod q))
      (fun i => f ((u:ZMod A)*x i)) F) =
      characterSum q (eval₂ (Int.castRingHom (ZMod q)) (fun i => f (x i)) F) := by
  have he := CubicGradientScaling.homogeneous_eval₂_smul F hF
    (Int.castRingHom (ZMod q)) (fun i => f (x i)) (f (u:ZMod A))
  change eval₂ (Int.castRingHom (ZMod q)) (fun i => f (u:ZMod A)*f (x i)) F =
    (f (u:ZMod A))^d * eval₂ (Int.castRingHom (ZMod q)) (fun i => f (x i)) F at he
  simp only [map_mul]
  rw [he]
  let t : (ZMod q)ˣ := (Units.map f.toMonoidHom u)^d
  simpa only [t,Units.val_pow_eq_pow_val,Units.coe_map] using
    characterSum_unit_mul q t
      (eval₂ (Int.castRingHom (ZMod q)) (fun i => f (x i)) F)

/-- The intrinsic modular-frequency statement. The substitution is an
actual permutation of the residue vectors, and preserves Ω. -/
theorem residueFourierSum_unit_frequency {n d q A W : ℕ}
    [NeZero q] [NeZero A]
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous d)
    (hqA : q ∣ A) (hWA : W ∣ A) (Ω : Set (Fin n → ZMod W))
    (hΩ : ResidueUnitInvariant Ω) (u : (ZMod A)ˣ) (v : Fin n → ZMod A) :
    residueFourierSum F q A W hqA hWA Ω (fun i => (u:ZMod A)*v i) =
      residueFourierSum F q A W hqA hWA Ω v := by
  unfold residueFourierSum
  apply Fintype.sum_equiv (Equiv.piCongrRight fun _ : Fin n => u.mulLeft)
  intro x
  change (if (fun i => ZMod.castHom hWA (ZMod W) (x i)) ∈ Ω then
      characterSum q (eval₂ (Int.castRingHom (ZMod q))
        (fun i => ZMod.castHom hqA (ZMod q) (x i)) F) *
        ZMod.stdAddChar (∑ i, ((u:ZMod A)*v i)*x i) else 0) =
    (if (fun i => ZMod.castHom hWA (ZMod W) ((u:ZMod A)*x i)) ∈ Ω then
      characterSum q (eval₂ (Int.castRingHom (ZMod q))
        (fun i => ZMod.castHom hqA (ZMod q) ((u:ZMod A)*x i)) F) *
        ZMod.stdAddChar (∑ i, v i*((u:ZMod A)*x i)) else 0)
  have hr : (fun i => ZMod.castHom hWA (ZMod W) ((u:ZMod A)*x i)) ∈ Ω ↔
      (fun i => ZMod.castHom hWA (ZMod W) (x i)) ∈ Ω := by
    simpa only [map_mul,Units.coe_map] using
      hΩ (Units.map (ZMod.castHom hWA (ZMod W)).toMonoidHom u)
        (fun i => ZMod.castHom hWA (ZMod W) (x i))
  rw [hr,characterSum_homogeneous_smul F hF (ZMod.castHom hqA (ZMod q)) u x]
  simp only [mul_assoc,mul_left_comm]

end CubicTenVariables.LocalizedFourierUnit

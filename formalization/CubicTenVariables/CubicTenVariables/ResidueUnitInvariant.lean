import Mathlib.Data.ZMod.Basic

/-! Scalar-unit stability for actual residue-vector restrictions. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables

def ResidueUnitInvariant {n W : ℕ} (Ω : Set (Fin n → ZMod W)) : Prop :=
  ∀ (u : (ZMod W)ˣ) (x : Fin n → ZMod W),
    (fun i => (u : ZMod W)*x i) ∈ Ω ↔ x ∈ Ω

namespace ResidueUnitInvariant

theorem univ (n W : ℕ) : ResidueUnitInvariant (Set.univ : Set (Fin n → ZMod W)) :=
  fun _ _ => Iff.rfl

/-- Unit stability pulls back along every actual residue ring map. -/
theorem preimage {n W V : ℕ} (f : ZMod W →+* ZMod V)
    {Ω : Set (Fin n → ZMod V)} (hΩ : ResidueUnitInvariant Ω) :
    ResidueUnitInvariant {x : Fin n → ZMod W | (fun i => f (x i)) ∈ Ω} := by
  intro u x
  simpa only [Set.mem_setOf_eq,map_mul,Units.coe_map] using
    hΩ (Units.map f.toMonoidHom u) (fun i => f (x i))

theorem inter {n W : ℕ} {Ω Ψ : Set (Fin n → ZMod W)}
    (hΩ : ResidueUnitInvariant Ω) (hΨ : ResidueUnitInvariant Ψ) :
    ResidueUnitInvariant (Ω ∩ Ψ) := by
  intro u x
  exact and_congr (hΩ u x) (hΨ u x)

end ResidueUnitInvariant
end CubicTenVariables

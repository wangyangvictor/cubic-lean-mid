import CubicTenVariables.PrimeLocalizationSeries
import CubicTenVariables.ResidueUnitInvariant
import Mathlib.Data.ZMod.Units

/-! Scalar-unit invariance for the actual finite reductions of p-adic unit
orbits, and for the simultaneous finite-prime restriction. Residue units
are lifted by their integral representatives; no lifting input is assumed. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables
open MvPolynomial
open scoped BigOperators Classical

namespace PadicUnitOrbit
variable (p : ℕ) [Fact p.Prime]

/-- Every unit modulo a prime power is the reduction of an actual p-adic
unit, including the one-element residue ring at level zero. -/
theorem exists_unit_lift (k : ℕ) (u : (ZMod (p^k))ˣ) :
    ∃ U : ℤ_[p]ˣ, PadicInt.toZModPow k (U : ℤ_[p]) = (u : ZMod (p^k)) := by
  rcases k with _ | k
  · haveI : Subsingleton (ZMod (p^0)) := by
      simpa using (inferInstance : Subsingleton (ZMod 1))
    exact ⟨1,Subsingleton.elim _ _⟩
  · have hdiv : p ∣ p^(k+1) := by
      simpa only [pow_one] using (pow_dvd_pow p (Nat.succ_pos k))
    have hcop : p.Coprime (u : ZMod (p^(k+1))).val :=
      ((ZMod.val_coe_unit_coprime u).of_dvd_right hdiv).symm
    have hunit : IsUnit ((u : ZMod (p^(k+1))).val : ℤ_[p]) :=
      PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hcop)
    obtain ⟨U,hU⟩ := hunit
    refine ⟨U,?_⟩
    rw [hU,map_natCast,ZMod.natCast_zmod_val]

/-- Reduction at any level of any literal unit orbit is closed under
every scalar unit of the residue ring. -/
theorem mul_mem_reduction_image {n : ℕ} (ξ : Fin n → ℤ_[p]) (M k : ℕ)
    (u : (ZMod (p^k))ˣ) (x : Fin n → ZMod (p^k))
    (hx : x ∈ (fun z : Fin n → ℤ_[p] => fun i => PadicInt.toZModPow k (z i)) ''
      unitOrbit p ξ M) :
    (fun i => (u : ZMod (p^k))*x i) ∈
      (fun z : Fin n → ℤ_[p] => fun i => PadicInt.toZModPow k (z i)) ''
        unitOrbit p ξ M := by
  obtain ⟨U,hU⟩ := exists_unit_lift p k u
  obtain ⟨z,hz,hzx⟩ := hx
  refine ⟨(U:ℤ_[p]) • z,?_,?_⟩
  · rw [←unit_smul_unitOrbit p ξ M U]
    exact ⟨z,hz,rfl⟩
  · funext i
    simp only [Pi.smul_apply,smul_eq_mul,map_mul,hU,congrFun hzx i]

/-- The finite reduction of the actual orbit is invariant under all
residue units; the orbit level and reduction level can be different. -/
theorem reduction_image_unitInvariant {n : ℕ} (ξ : Fin n → ℤ_[p]) (M k : ℕ) :
    ResidueUnitInvariant
      ((fun z : Fin n → ℤ_[p] => fun i => PadicInt.toZModPow k (z i)) ''
        unitOrbit p ξ M) := by
  intro u x
  constructor
  · intro hx
    have h := mul_mem_reduction_image p ξ M k u⁻¹ _ hx
    simpa only [←mul_assoc,Units.inv_mul,one_mul] using h
  · exact mul_mem_reduction_image p ξ M k u x

end PadicUnitOrbit

namespace PrimeLocalizationData
variable {p : ℕ} [Fact p.Prime] {F : MvPolynomial (Fin 10) ℤ}

theorem residueSet_unitInvariant (D : PrimeLocalizationData p F) :
    ResidueUnitInvariant D.residueSet :=
  PadicUnitOrbit.reduction_image_unitInvariant p D.center D.modulusExponent D.modulusExponent

end PrimeLocalizationData

namespace LocalizedFinitePrimeAssembly

/-- Simultaneous residue restrictions inherit scalar-unit invariance
through the canonical reduction ring homomorphisms. -/
theorem restriction_unitInvariant {n : ℕ} (s : Finset ℕ) (M : ℕ → ℕ)
    (Ω : ∀ p, Set (Fin n → ZMod (p^(M p))))
    (hlocal : ∀ p ∈ s, ResidueUnitInvariant (Ω p)) :
    ResidueUnitInvariant (restriction s M Ω) := by
  intro u x
  rw [mem_restriction_iff,mem_restriction_iff]
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  let f : ZMod (modulus s M) →+* ZMod (p^(M p)) :=
    ZMod.castHom (primePower_dvd_modulus s M p hp) (ZMod (p^(M p)))
  have h := hlocal p hp (Units.map f u) (fun i => f (x i))
  simpa only [Units.coe_map,MonoidHom.coe_coe,map_mul] using h

end LocalizedFinitePrimeAssembly

namespace PrimeLocalizationSeries
variable {F : MvPolynomial (Fin 10) ℤ}

/-- The particular global restriction selected by the supplied local
data satisfies the finite scalar-unit invariance required downstream. -/
theorem restriction_unitInvariant (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F) :
    ResidueUnitInvariant (restriction s hprimes D) := by
  apply LocalizedFinitePrimeAssembly.restriction_unitInvariant
  intro p hp
  letI : Fact p.Prime := ⟨hprimes p hp⟩
  have h := (D p hp).residueSet_unitInvariant
  exact (congrArg (fun spec : Σ M : ℕ, Set (Fin 10 → ZMod (p^M)) =>
    ResidueUnitInvariant spec.2) (localSpecification_of_mem s hprimes D p hp)).mpr h

end PrimeLocalizationSeries
end CubicTenVariables

import CubicTenVariables.FixedFamilyPrimeFieldPointCount
import CubicTenVariables.GeometricEquationDimensionProved
import CubicTenVariables.UniformPrimeFieldIdealCount

/-! The prime-field count for the actual fibers of a fixed integral
polynomial family. The raw Noetherian ideal count applies to its coefficient
ring; geometric and ordinary equation-quotient dimensions agree. No
point-count literature proposition is an argument to the final theorem.
-/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FixedFamilyPrimeFieldPointCountProved
open MvPolynomial BihomogeneousIncidenceFamily
open scoped Classical

/-- The constant is chosen for the integral family before the prime field,
its parameter value, and the geometric fiber-dimension threshold. -/
theorem proved : FixedFamilyPrimeFieldPointCount.Uniform := by
  intro m n t f
  let I : Ideal (Polynomial m n) := Ideal.span (Set.range f)
  obtain ⟨C,hC,hcount⟩ := UniformPrimeFieldIdealCount.exists_bound I
  refine ⟨C,hC,?_⟩
  intro p hp v j hdim
  let ρ : MvPolynomial (Fin m) ℤ →+* ZMod p :=
    eval₂Hom (Int.castRingHom (ZMod p)) v
  have hmap : I.map (MvPolynomial.map ρ) =
      Literature.integralFamilyFiberIdeal f (ZMod p) v := by
    dsimp only [I,Literature.integralFamilyFiberIdeal,ρ]
    rw [Ideal.map_span,← Set.range_comp']
  have hd : ringKrullDim (MvPolynomial (Fin n) (ZMod p) ⧸
      I.map (MvPolynomial.map ρ)) ≤ (j : WithBot ℕ∞) := by
    rw [hmap,← GeometricEquationDimensionProved.geometricFiberDimension_eq_quotient]
    exact hdim
  have hc := hcount p ρ j hd
  change Nat.card (NoetherianPrimeFieldBound.zeroSet I ρ) ≤ C * p^j at hc
  have hzero (x : Fin n → ZMod p) :
      (∀ P ∈ I, eval₂Hom ρ x P = 0) ↔ ∀ i, value (f i) v x = 0 := by
    constructor
    · intro hx i
      exact hx (f i) (Ideal.subset_span (Set.mem_range_self i))
    · intro hx P hP
      have hle : I ≤ RingHom.ker (eval₂Hom ρ x) := by
        apply Ideal.span_le.mpr
        rintro Q ⟨i,rfl⟩
        exact hx i
      exact hle hP
  have he : Nat.card (NoetherianPrimeFieldBound.zeroSet I ρ) =
      (Finset.univ.filter (fun x : Fin n → ZMod p =>
        ∀ i, value (f i) v x = 0)).card := by
    calc
      _ = Nat.card {x : Fin n → ZMod p // ∀ i, value (f i) v x = 0} :=
        Nat.card_congr (Equiv.subtypeEquivRight hzero)
      _ = _ := by simp only [Nat.card_eq_fintype_card,Fintype.card_subtype]
  rwa [he] at hc

end CubicTenVariables.FixedFamilyPrimeFieldPointCountProved

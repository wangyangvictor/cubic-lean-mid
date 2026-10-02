import HessianTheorem11.UnconditionalCutHeight

/-! The dimension inequality for algebraic fibers follows from the
Noetherian height inequality and full height of every closed point. -/
noncomputable section
namespace HessianTheorem11.UnconditionalFiberHeight
open Ideal UnconditionalCutHeight

/-- A fiber through any closed point has the dimension required by the
usual fiber-dimension inequality. No smoothness or generic rank is used. -/
theorem dimension_le_base_add_fiber
    (R S : Type*) [CommRing R] [CommRing S] [IsDomain S]
    [Algebra GeometricField R] [Algebra GeometricField S]
    [Algebra.FiniteType GeometricField R] [Algebra.FiniteType GeometricField S]
    (f : R →ₐ[GeometricField] S) (m : Ideal S) [m.IsMaximal] :
    ringKrullDim S ≤ ringKrullDim R +
      ringKrullDim (S ⧸ (m.comap f.toRingHom).map f.toRingHom) := by
  letI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing GeometricField R
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing GeometricField S
  letI : Algebra R S := f.toRingHom.toAlgebra
  let p := m.under R
  have hh := Ideal.height_le_height_add_of_liesOver p m
  have hp : (p.height : Dimension) ≤ ringKrullDim R :=
    Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
  have hm : ((m.map (Ideal.Quotient.mk (p.map (algebraMap R S)))).height : Dimension) ≤
      ringKrullDim (S ⧸ p.map (algebraMap R S)) :=
    Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
  rw [← finiteType_maximal_height S m]
  exact (show (m.height : Dimension) ≤ (p.height : Dimension) +
    ((m.map (Ideal.Quotient.mk (p.map (algebraMap R S)))).height : Dimension) by
      exact_mod_cast hh).trans (add_le_add hp hm)

end HessianTheorem11.UnconditionalFiberHeight

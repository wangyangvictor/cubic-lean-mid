import CubicTenVariables.GeneralHomogeneousIrreducibilityOpen
import CubicTenVariables.Literature.HomogeneousHypersurfaceIntegralityOpen

/-!
# The fixed-degree homogeneous integrality open, proved explicitly

The reducible locus is cut out by the finite projective factor-minor systems
constructed in `GeneralHomogeneousFactorMinors`.  Consequently the standard
spreading input previously isolated in `Literature` is now a theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
noncomputable section

namespace CubicTenVariables.HomogeneousHypersurfaceIntegralityOpenProved

open MvPolynomial

/-- The exact former literature premise, derived from explicit bounded
factor matrices and homogeneous Nullstellensatz certificates. -/
theorem proved : Literature.HomogeneousHypersurfaceIntegralityOpen := by
  intro R Omega _ _ _ n d hd rho F hF hne hdomain
  have hprime := (Ideal.Quotient.isDomain_iff_prime _).mp hdomain
  have hirr : Irreducible (map rho F) :=
    ((Ideal.span_singleton_prime hne).mp hprime).irreducible
  obtain ⟨s, hs, hopen⟩ :=
    GeneralHomogeneousIrreducibilityOpen.exists_principal_open
      rho F hd hF hirr
  refine ⟨s, hs, ?_⟩
  intro K _ tau htau
  let alpha := algebraMap K (AlgebraicClosure K)
  have has : (alpha.comp tau) s ≠ 0 := by
    simpa only [RingHom.comp_apply] using (map_ne_zero alpha).mpr htau
  have hirrbar := hopen (AlgebraicClosure K) (alpha.comp tau) has
  have hmap : map (alpha.comp tau) F = map alpha (map tau F) := by
    rw [map_map]
  rw [hmap] at hirrbar
  have hneK : map tau F ≠ 0 := by
    intro hz
    apply hirrbar.ne_zero
    rw [hz, map_zero]
  refine ⟨(hF.map tau).totalDegree hneK, ?_⟩
  exact (Ideal.Quotient.isDomain_iff_prime _).mpr
    ((Ideal.span_singleton_prime hirrbar.ne_zero).mpr hirrbar.prime)

end CubicTenVariables.HomogeneousHypersurfaceIntegralityOpenProved

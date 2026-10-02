import TranslatedDepthSeven.RationalLocalEqualityIntegralCertificate
import Mathlib.RingTheory.Ideal.Colon

/-!
# A finite, point-independent menu of principal-open certificates

For two fixed ideals `I ⊆ J` in a Noetherian ring, the colon ideal
`I : J` is finitely generated.  Its fixed generators form a finite menu of
principal opens: whenever some element clears `J` into `I` and is nonzero at
a point, one member of this menu is already nonzero there.

Applied to a fixed integral affine model of a rational surface component,
this removes the apparent dependence of the clearing polynomial on the
marked point.  The only point-dependent integer is then the value of one of
finitely many fixed polynomials times a fixed selected Jacobian determinant.
Consequently its size has the elementary polynomial height bound proved in
`IntegralLocalEquationMultiplicitySpecialization`.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

/-- Fixed generators of a colon ideal form a universal finite menu of
clearing elements.  The last assertion applies to every ring homomorphism,
not just evaluation maps. -/
theorem exists_finite_colon_clearing_menu
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I J : Ideal R) :
    ∃ n : ℕ, ∃ menu : Fin n → R,
      (∀ i, ∀ f ∈ J, menu i * f ∈ I) ∧
      ∀ {S : Type*} [CommRing S] (phi : R →+* S) (u : R),
        (∀ f ∈ J, u * f ∈ I) → phi u ≠ 0 →
          ∃ i, phi (menu i) ≠ 0 := by
  classical
  obtain ⟨n, menu, hmenu⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp
      (IsNoetherian.noetherian (I.colon J))
  refine ⟨n, menu, ?_, ?_⟩
  · intro i f hf
    have hi : menu i ∈ I.colon J := by
      rw [← hmenu]
      exact Submodule.subset_span (Set.mem_range_self i)
    exact Submodule.mem_colon.mp hi f hf
  · intro S _ phi u hu hphi
    by_contra hnone
    push_neg at hnone
    have hcolonKer : I.colon J ≤ RingHom.ker phi := by
      rw [← hmenu]
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact RingHom.mem_ker.mpr (hnone i)
    have huColon : u ∈ I.colon J := by
      apply Submodule.mem_colon.mpr
      simpa only [smul_eq_mul] using hu
    exact hphi (RingHom.mem_ker.mp (hcolonKer huColon))

/-- For a fixed integral local equation ideal and a fixed integral component
model, one may choose finitely many clearing polynomials once and for all.
Every integral rational point at which the rational stalks agree and the
selected Jacobian determinant is nonzero is covered by one of them.  The
corresponding explicit integer controls all prime reductions and has a
polynomial point-height bound. -/
theorem exists_finite_projectiveSurface_multiplicityOne_menu
    {N : ℕ} (hN : 2 ≤ N)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (equations : Fin (N - 2) → MvPolynomial (Fin N) ℤ)
    (selectedVar : Fin (N - 2) → Fin N)
    (hselected : Function.Injective selectedVar)
    (hIJ : Ideal.span (Set.range equations) ≤
      Ideal.map integralDehomogenizeAtZeroHom
        (projectiveIntegralClosureIdeal I)) :
    ∃ n : ℕ, ∃ menu : Fin n → MvPolynomial (Fin N) ℤ,
      (∀ i, ∀ f ∈ Ideal.map integralDehomogenizeAtZeroHom
          (projectiveIntegralClosureIdeal I),
        menu i * f ∈ Ideal.span (Set.range equations)) ∧
      ∀ (z : Fin N → ℤ),
        (∀ f ∈ Ideal.map rationalDehomogenizeAtZeroHom I,
          MvPolynomial.eval (fun i ↦ (z i : ℚ)) f = 0) →
        (Ideal.map
            (algebraMap (MvPolynomial (Fin N) ℚ)
              (Localization.AtPrime
                (RingHom.ker
                  (MvPolynomial.eval (fun i ↦ (z i : ℚ))))))
            (Ideal.map (MvPolynomial.map (Int.castRingHom ℚ))
              (Ideal.span (Set.range equations))) =
          Ideal.map
            (algebraMap (MvPolynomial (Fin N) ℚ)
              (Localization.AtPrime
                (RingHom.ker
                  (MvPolynomial.eval (fun i ↦ (z i : ℚ))))))
            (Ideal.map rationalDehomogenizeAtZeroHom I)) →
        MvPolynomial.eval z
            (selectedJacobianDeterminant equations selectedVar) ≠ 0 →
        ∃ i : Fin n,
          MvPolynomial.eval z (menu i) ≠ 0 ∧
          let Δ : ℤ := integralSelectedJacobianChartCertificate
            equations selectedVar (menu i) z
          Δ ≠ 0 ∧
            (∀ (p : ℕ) (hp : p.Prime), ¬p ∣ Δ.natAbs →
              HasHilbertSamuelMultiplicityAt hp
                (projectiveSpecialFiberIdeal I)
                (fun j ↦ (integralAffineProjectivePoint z j : ZMod p)) 2 1) ∧
            ∀ (Y : ℕ), (∀ j, (z j).natAbs ≤ Y) →
              Δ.natAbs ≤
                ((menu i).support.card *
                    mvPolynomialCoefficientNatAbsMax (menu i) *
                    max 1 Y ^ (menu i).totalDegree) *
                  ((selectedJacobianDeterminant equations selectedVar).support.card *
                    mvPolynomialCoefficientNatAbsMax
                      (selectedJacobianDeterminant equations selectedVar) *
                    max 1 Y ^
                      (selectedJacobianDeterminant equations selectedVar).totalDegree) := by
  let equationIdeal : Ideal (MvPolynomial (Fin N) ℤ) :=
    Ideal.span (Set.range equations)
  let componentIdeal : Ideal (MvPolynomial (Fin N) ℤ) :=
    Ideal.map integralDehomogenizeAtZeroHom
      (projectiveIntegralClosureIdeal I)
  obtain ⟨n, menu, hclearMenu, hcoverMenu⟩ :=
    exists_finite_colon_clearing_menu equationIdeal componentIdeal
  refine ⟨n, menu, ?_, ?_⟩
  · simpa only [equationIdeal, componentIdeal] using hclearMenu
  · intro z hpoint hatPoint hminor
    obtain ⟨U, hU, hUclear, _hcertificate⟩ :=
      exists_integralCertificate_projectiveSurface_multiplicityOne_of_local_eq
        hN I z equations selectedVar hselected hpoint hIJ hatPoint hminor
    obtain ⟨i, hi⟩ := hcoverMenu (MvPolynomial.eval z) U
      (by simpa only [equationIdeal, componentIdeal] using hUclear) hU
    refine ⟨i, hi, ?_⟩
    let Δ : ℤ := integralSelectedJacobianChartCertificate
      equations selectedVar (menu i) z
    have hpointIntegral :=
      integralAffineChart_point_of_rationalProjectivePoint I z hpoint
    have hspecialize :=
      hasHilbertSamuelMultiplicityAt_surface_one_of_integral_localEquations
        hN (projectiveIntegralClosureIdeal I) z equations selectedVar hselected
          (menu i) hpointIntegral hIJ
          (by simpa only [equationIdeal, componentIdeal] using hclearMenu i)
          hi hminor
    dsimp only at hspecialize
    refine ⟨hspecialize.1, ?_, ?_⟩
    · intro p hp hpDelta
      simpa only [projectiveSpecialFiberIdeal] using
        hspecialize.2 p hp hpDelta
    · intro Y hz
      exact integralSelectedJacobianChartCertificate_natAbs_le
        equations selectedVar (menu i) z hz

end

end TranslatedDepthSeven

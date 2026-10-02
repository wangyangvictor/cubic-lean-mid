import CubicTenVariables.PlanAlphaWeightedReduced
import CubicTenVariables.PlanAlphaMixedWeight

/-! Apply the proved weighted cube-free estimate to the literal localized
sum with two fixed factors. The finite sample set retains arbitrary further
restrictions, including a dyadic restriction on the product modulus. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PlanAlphaFixedFactorsReduced
open MvPolynomial HessianTheorem11 NumericalPrimeDepth
open IntegerResidueClasses (residue)
open ComplementCubeFreePiece (Sample)
open PlanAlphaMixedWeight (weight)
open scoped BigOperators

variable {t N Betti : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
  {tables : ∀ k : Fin 4, MicrolocalPromotionTable.Table F f (k.val+1)}
  {C : ℝ} {d₀ : ℕ} {h : CoarseBounds F C}

/-- The bound constant precedes the localized factor, the cube-full
factor, the residue majorant and every allowed subset of pairs. -/
theorem of_data
    (integrality : CubicPrincipalOpenUniform.Uniform)
    (cubicWeil : Literature.SmoothCubicWeil)
    (isolated : CubicSurfacePointCountReduced.IsolatedConjugateCubicSurfacePointCount)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    (hP : MicrolocalRationalPartition.Conclusion F f N Betti tables)
    (hhom : F.IsHomogeneous 3) (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C d₀ h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ D : ℝ, 1 ≤ D →
      ∀ (u : Fin 10 → ℝ) (L : ℝ), 1 ≤ L → ∀ (m : ℕ) [NeZero m],
      ∀ (g r W : ℕ) [NeZero g] [NeZero r] [NeZero W],
      ∀ (Ω : Set (Fin 10 → ZMod W)), ResidueUnitInvariant Ω →
      (g*W).Coprime r → ∀ (V : Finset (Fin 10 → ℤ))
        (P : (Fin 10 → ZMod m) → ℝ),
      (∀ v ∈ V, v ≠ 0 ∧ ∀ k, |(v k : ℝ)-u k| ≤ L) →
      (∀ b, 0 ≤ P b) →
      (∀ v ∈ V, weight F g W Ω r v ≤ P (residue m v)) →
      ∀ E : Finset Sample,
      (∀ x ∈ E, x.1 ∈ CubeFreeNonzeroAverage.window D ∧
        x.1.Coprime (m*N) ∧ x.2 ∈ V ∧ ((g*r)*W).Coprime x.1) →
      (∑ x ∈ E, ‖localizedCompleteCubicSum F (g*x.1*r) W Ω x.2‖) ≤
        M*(D*(2+‖u‖+L+(m : ℝ)))^ε *
          (min (D^((59 : ℝ)/6)*
            ((1+L/(m : ℝ))/D^((1 : ℝ)/3)+((1+L/(m : ℝ))/D^((1 : ℝ)/3))^9)*(∑ b, P b))
            (D^9*(∑ v ∈ V, weight F g W Ω r v)) +
           D^((13 : ℝ)/2)*(1+L/(m : ℝ))^((20 : ℝ)/3)*
             (∑ b, P b)^((2 : ℝ)/3)*(∑ v ∈ V, weight F g W Ω r v)^((1 : ℝ)/3)) := by
  obtain ⟨M,hM,hbound⟩ := PlanAlphaWeightedReduced.of_data
    integrality cubicWeil isolated pointcount hP hhom hAn hc ε hε
  refine ⟨M,hM,?_⟩
  intro D hD u L hL m hm g r W hg hr hW Ω hΩ hgr V P hV hP0 hmajor E hE
  have hb := hbound D hD u L hL m V (weight F g W Ω r) P hV
    (fun v _ => PlanAlphaMixedWeight.weight_nonneg F g W Ω r v) hP0 hmajor
    E (fun x hx => ⟨(hE x hx).1,(hE x hx).2.1,(hE x hx).2.2.1⟩)
  apply le_trans (le_of_eq ?_) hb
  apply Finset.sum_congr rfl
  intro x hx
  have hwindow := (CubeFreeNonzeroAverage.mem_window D x.1).mp (hE x hx).1
  have hxpos : 0 < x.1 := by
    exact_mod_cast (zero_lt_one.trans_le (hD.trans hwindow.2.1))
  letI : NeZero x.1 := ⟨hxpos.ne'⟩
  exact PlanAlphaMixedWeight.norm_eq_weight F hhom g x.1 r W Ω hΩ hgr
    (hE x hx).2.2.2 x.2

end CubicTenVariables.PlanAlphaFixedFactorsReduced

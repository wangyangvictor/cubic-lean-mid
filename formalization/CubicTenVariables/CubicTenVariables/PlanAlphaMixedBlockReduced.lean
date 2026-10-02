import CubicTenVariables.PlanAlphaFixedFactorsReduced
import CubicTenVariables.PlanAlphaMixedNumerics

/-! The literal mixed-modulus block sum, obtained by summing the fixed-factor
bound and applying outer Hölder. Residue majorants and their common modulus
cap remain supplied hypotheses; this does not claim the final mixed-modulus
power saving. The finite subtype indexes exactly the selected factors. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PlanAlphaMixedBlockReduced
open MvPolynomial HessianTheorem11 NumericalPrimeDepth
open IntegerResidueClasses (residue)
open ComplementCubeFreePiece (Sample)
open PlanAlphaMixedWeight (weight)
open scoped BigOperators

variable {t N Betti : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
  {tables : ∀ k : Fin 4, MicrolocalPromotionTable.Table F f (k.val+1)}
  {C : ℝ} {d₀ : ℕ} {h : CoarseBounds F C}

/-- The constant precedes every block parameter, finite family, majorant,
and sample restriction. Empty families and zero masses are allowed. -/
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
      ∀ (u : Fin 10 → ℝ) (L : ℝ), 1 ≤ L →
      ∀ (g W : ℕ) [NeZero g] [NeZero W],
      ∀ (Ω : Set (Fin 10 → ZMod W)), ResidueUnitInvariant Ω →
      ∀ (R : Finset ℕ), (∀ r ∈ R, 0 < r) →
      ∀ (m : R → ℕ) [∀ r, NeZero (m r)] (Hmod : ℝ), 0 ≤ Hmod →
      (∀ r, (m r : ℝ) ≤ Hmod) →
      (∀ r : R, (g*W).Coprime r.val) →
      ∀ (V : Finset (Fin 10 → ℤ)) (P : ∀ r : R, (Fin 10 → ZMod (m r)) → ℝ),
      (∀ v ∈ V, v ≠ 0 ∧ ∀ k, |(v k : ℝ)-u k| ≤ L) →
      (∀ r b, 0 ≤ P r b) →
      (∀ r v, v ∈ V → weight F g W Ω r.val v ≤ P r (residue (m r) v)) →
      ∀ E : R → Finset Sample,
      (∀ r x, x ∈ E r → x.1 ∈ CubeFreeNonzeroAverage.window D ∧
        x.1.Coprime (m r*N) ∧ x.2 ∈ V ∧ ((g*r.val)*W).Coprime x.1) →
      let T : R → ℝ := fun r => 1+L/(m r : ℝ)
      let Pmass : R → ℝ := fun r => ∑ b, P r b
      let Wmass : R → ℝ := fun r => ∑ v ∈ V, weight F g W Ω r.val v
      (∑ r : R, ∑ x ∈ E r, ‖localizedCompleteCubicSum F (g*x.1*r.val) W Ω x.2‖) ≤
        M*(D*(2+‖u‖+L+Hmod))^ε *
          ((∑ r : R, min (D^((59 : ℝ)/6)*
            (T r/D^((1 : ℝ)/3)+(T r/D^((1 : ℝ)/3))^9)*Pmass r)
            (D^9*Wmass r)) +
           D^((13 : ℝ)/2)*(∑ r : R, (T r)^10*Pmass r)^((2 : ℝ)/3)*
             (∑ r : R, Wmass r)^((1 : ℝ)/3)) := by
  obtain ⟨M,hM,hbound⟩ := PlanAlphaFixedFactorsReduced.of_data
    integrality cubicWeil isolated pointcount hP hhom hAn hc ε hε
  refine ⟨M,hM,?_⟩
  intro D hD u L hL g W hg hW Ω hΩ R hR m hm Hmod hHmod hcap hgr V P hV hP0 hmajor E hE
  let T : R → ℝ := fun r => 1+L/(m r : ℝ)
  let Pmass : R → ℝ := fun r => ∑ b, P r b
  let Wmass : R → ℝ := fun r => ∑ v ∈ V, weight F g W Ω r.val v
  let Aterm : R → ℝ := fun r => min (D^((59 : ℝ)/6)*
    (T r/D^((1 : ℝ)/3)+(T r/D^((1 : ℝ)/3))^9)*Pmass r) (D^9*Wmass r)
  let Hterm : R → ℝ := fun r => (T r)^((20 : ℝ)/3)*
    (Pmass r)^((2 : ℝ)/3)*(Wmass r)^((1 : ℝ)/3)
  let B : ℝ := M*(D*(2+‖u‖+L+Hmod))^ε
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hT0 : ∀ r, 0 ≤ T r := fun r => by dsimp [T]; positivity
  have hPm0 : ∀ r, 0 ≤ Pmass r := fun r => Finset.sum_nonneg (fun b _ => hP0 r b)
  have hWm0 : ∀ r, 0 ≤ Wmass r := fun r => Finset.sum_nonneg
    (fun v _ => PlanAlphaMixedWeight.weight_nonneg F g W Ω r.val v)
  have hAt0 : ∀ r, 0 ≤ Aterm r := fun r => by
    have ht := hT0 r
    have hp := hPm0 r
    have hw := hWm0 r
    dsimp [Aterm]
    exact le_min (by positivity) (by positivity)
  have hHt0 : ∀ r, 0 ≤ Hterm r := fun r => by
    have ht := hT0 r
    have hp := hPm0 r
    have hw := hWm0 r
    dsimp [Hterm]
    positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hpoint : ∀ r : R,
      (∑ x ∈ E r, ‖localizedCompleteCubicSum F (g*x.1*r.val) W Ω x.2‖) ≤
        B*(Aterm r+D^((13 : ℝ)/2)*Hterm r) := by
    intro r
    letI : NeZero r.val := ⟨(hR r.val r.property).ne'⟩
    have hb := hbound D hD u L hL (m r) g r.val W Ω hΩ (hgr r)
      V (P r) hV (hP0 r) (hmajor r) (E r) (hE r)
    have hheight : (D*(2+‖u‖+L+(m r : ℝ)))^ε ≤
        (D*(2+‖u‖+L+Hmod))^ε := by
      apply Real.rpow_le_rpow (by positivity) _ hε.le
      exact mul_le_mul_of_nonneg_left (add_le_add (le_refl _) (hcap r)) hD0
    have heq : D^((13 : ℝ)/2)*(T r)^((20 : ℝ)/3)*
        (Pmass r)^((2 : ℝ)/3)*(Wmass r)^((1 : ℝ)/3) =
        D^((13 : ℝ)/2)*Hterm r := by dsimp [Hterm]; ring
    change _ ≤ M*(D*(2+‖u‖+L+(m r : ℝ)))^ε *
      (Aterm r+D^((13 : ℝ)/2)*(T r)^((20 : ℝ)/3)*
        (Pmass r)^((2 : ℝ)/3)*(Wmass r)^((1 : ℝ)/3)) at hb
    rw [heq] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hheight hM0)
      (add_nonneg (hAt0 r) (mul_nonneg (Real.rpow_nonneg hD0 _) (hHt0 r))))
  have hholder := PlanAlphaMixedNumerics.outer_holder Finset.univ T Pmass Wmass
    (fun r _ => hT0 r) (fun r _ => hPm0 r) (fun r _ => hWm0 r)
  change (∑ r : R, Hterm r) ≤
    (∑ r : R, (T r)^10*Pmass r)^((2 : ℝ)/3)*(∑ r : R, Wmass r)^((1 : ℝ)/3) at hholder
  change _ ≤ B*((∑ r : R, Aterm r)+
    D^((13 : ℝ)/2)*(∑ r : R, (T r)^10*Pmass r)^((2 : ℝ)/3)*
      (∑ r : R, Wmass r)^((1 : ℝ)/3))
  calc
    _ ≤ ∑ r : R, B*(Aterm r+D^((13 : ℝ)/2)*Hterm r) :=
      Finset.sum_le_sum (fun r _ => hpoint r)
    _ = B*((∑ r : R, Aterm r)+D^((13 : ℝ)/2)*(∑ r : R, Hterm r)) := by
      rw [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hB0
      rw [mul_assoc]
      exact add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left hholder (Real.rpow_nonneg hD0 _))

end CubicTenVariables.PlanAlphaMixedBlockReduced

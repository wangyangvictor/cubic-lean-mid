import CubicTenVariables.ConductorLowModulusFiber
import CubicTenVariables.ConductorMeanDomain
import CubicTenVariables.ConductorPositiveMeanNumerics

/-! Regroup an actual finite modulus/frequency family with one fixed
high-radical tag by its frequency. Each frequency fiber maps injectively
to its modulus pairs, so the proved low-modulus estimate applies without
any additional counting or residue-periodicity premise. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ConductorMeanFiber
open MvPolynomial NumericalPrimeDepth NumericalConductorRadical
open ConductorFixedFrequency ConductorMeanDomain
open scoped BigOperators

variable {F : MvPolynomial (Fin 10) ℤ} {C : ℝ}

/-- The only sample hypotheses are the literal domain restrictions and
equality of their actual high-depth tags. One constant precedes the entire
box, progression, tag, and finite sample family. -/
theorem exists_bound {t : ℕ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
    {tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)}
    {N d₀ : ℕ} {h : CoarseBounds F C}
    (hF : F.IsHomogeneous 3)
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C d₀ h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ (D K0 : ℝ) (m : ℕ) (u : Fin 10 → ℝ) (L : ℝ) (v₀ : Fin 10 → ℤ),
        1 ≤ D → 0 ≤ L → ∀ (r : ℕ × ℕ) (Q : Finset Sample),
        (∀ x ∈ Q, InWindow h f tables D K0 m u L v₀ x) →
        (∀ x ∈ Q, tag h x = r) →
        (∑ x ∈ Q, ‖completeCubicSum F (x.1.1*x.1.2^2) x.2‖) ≤
          M*(D*(2+‖u‖+L+(m : ℝ)))^ε*D^((13 : ℝ)/2)*
            C^(r.1.primeFactors.card+r.2.primeFactors.card)*
              ∑ v ∈ Q.image Prod.snd, NumericalConductor.K h r.1 r.2 v := by
  classical
  obtain ⟨M,hM,hbound⟩ := ConductorLowModulusFiber.exists_bound hF hc ε hε
  refine ⟨M,hM,?_⟩
  intro D K0 m u L v₀ hD hL r Q hQ htag
  have hC : 0 ≤ C := zero_le_one.trans h.constant_pos
  have hfiber (v : Fin 10 → ℤ) (hv : v ∈ Q.image Prod.snd) :
      (∑ x ∈ Q.filter (fun x => x.2=v),
        ‖completeCubicSum F (x.1.1*x.1.2^2) x.2‖) ≤
        M*(D*(2+‖u‖+L+(m : ℝ)))^ε*D^((13 : ℝ)/2)*
          C^(r.1.primeFactors.card+r.2.primeFactors.card)*NumericalConductor.K h r.1 r.2 v := by
    obtain ⟨x₀,hx₀,hv₀⟩ := Finset.mem_image.mp hv
    have hw₀ := hQ x₀ hx₀
    have hgood : GoodFrequency F f tables v := hv₀ ▸ hw₀.good
    have hbox : ∀ i, |(v i : ℝ)-u i| ≤ L := hv₀ ▸ hw₀.box
    let S : Finset Sample := Q.filter (fun x => x.2=v)
    let P : Finset (ℕ × ℕ) := S.image Prod.fst
    have hP : ∀ y ∈ P,
        1 ≤ y.1 ∧ 1 ≤ y.2 ∧ Squarefree y.1 ∧ Squarefree y.2 ∧
          y.1.Coprime y.2 ∧ (y.1 : ℝ)*(y.2 : ℝ)^2 ≤ 2*D ∧
          primeHigh h y.1 v = r.1 ∧ squareHigh h y.2 v = r.2 := by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hxQ,hxv⟩ := Finset.mem_filter.mp hx
      have hw := hQ x hxQ
      refine ⟨hw.positive_left,hw.positive_right,hw.squarefree_left,hw.squarefree_right,
        hw.coprime,hw.size,?_,?_⟩
      · have he := congrArg Prod.fst (htag x hxQ)
        simpa only [tag,hxv] using he
      · have he := congrArg Prod.snd (htag x hxQ)
        simpa only [tag,hxv] using he
    have hinj : Set.InjOn (Prod.fst : Sample → ℕ × ℕ) (↑S : Set Sample) := by
      intro x hx y hy he
      apply Prod.ext he
      exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    have heq : (∑ x ∈ S, ‖completeCubicSum F (x.1.1*x.1.2^2) x.2‖) =
        ∑ y ∈ P, ‖completeCubicSum F (y.1*y.2^2) v‖ := by
      calc
        _ = ∑ x ∈ S, ‖completeCubicSum F (x.1.1*x.1.2^2) v‖ := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [(Finset.mem_filter.mp hx).2]
        _ = _ := (Finset.sum_image
          (f := fun y : ℕ × ℕ => ‖completeCubicSum F (y.1*y.2^2) v‖) hinj).symm
    have hs := hbound v hgood D hD r.1 r.2 P hP
    have hheight := ConductorPositiveMeanNumerics.height_le u L hL m v hbox
    have hheight0 : 0 ≤ frequencyHeight v := by dsimp [frequencyHeight]; positivity
    have hK : 0 ≤ NumericalConductor.K h r.1 r.2 v :=
      (NumericalConductor.K_pos h r.1 r.2 v).le
    change (∑ x ∈ S, ‖completeCubicSum F (x.1.1*x.1.2^2) x.2‖) ≤ _
    rw [heq]
    apply hs.trans
    gcongr
  calc
    _ = ∑ v ∈ Q.image Prod.snd, ∑ x ∈ Q.filter (fun x => x.2=v),
        ‖completeCubicSum F (x.1.1*x.1.2^2) x.2‖ := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩) _
    _ ≤ ∑ v ∈ Q.image Prod.snd,
        M*(D*(2+‖u‖+L+(m : ℝ)))^ε*D^((13 : ℝ)/2)*
          C^(r.1.primeFactors.card+r.2.primeFactors.card)*NumericalConductor.K h r.1 r.2 v :=
      Finset.sum_le_sum hfiber
    _ = _ := (Finset.mul_sum ..).symm

end CubicTenVariables.ConductorMeanFiber

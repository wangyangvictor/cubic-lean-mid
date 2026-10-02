import CubicTenVariables.ComplementCubeFreeMeanReduced
import CubicTenVariables.CubeFreeConductorMoments
import CubicTenVariables.FiniteWeightedClassSum
import CubicTenVariables.IntegerResidueClasses

/-! Actual weighted cube-free means obtained by grouping integer frequencies
by their residue class. The majorant is fixed before the modulus sum. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.CubeFreeWeightedResiduesReduced
open MvPolynomial HessianTheorem11 NumericalPrimeDepth
open SquarefullModulusDecomposition CubeFreeModulusDecomposition
open ComplementCubeFreePiece (Sample)
open CubeFreePositiveMean (frequencies mem_frequencies)
open CubeFreeConductorMoments (positiveModuli)
open CubeFreeFixedFrequency (conductor)
open IntegerResidueClasses (residue lift residue_eq_iff_dvd_sub)
open scoped BigOperators Classical

variable {t N Betti : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
  {tables : ∀ k : Fin 4, MicrolocalPromotionTable.Table F f (k.val+1)}
  {C : ℝ} {d₀ : ℕ} {h : CoarseBounds F C}

/-- Complementary pairs before separation into residue classes. -/
structure InComplement (F : MvPolynomial (Fin 10) ℤ)
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (tables : ∀ k : Fin 4, MicrolocalPromotionTable.Table F f (k.val+1))
    (N : ℕ) (h : CoarseBounds F C) (D : ℝ)
    (u : Fin 10 → ℝ) (L : ℝ) (m : ℕ) (x : Sample) : Prop where
  window : x.1 ∈ CubeFreeNonzeroAverage.window D
  good_primes : x.1.Coprime N
  progression_coprime : m.Coprime x.1
  nonzero : x.2 ≠ 0
  box : ∀ k, |(x.2 k : ℝ)-u k| ≤ L
  complement : ¬ ConductorFixedFrequency.GoodFrequency F f tables x.2 ∨
    1+L/(m : ℝ) < (NumericalConductorRadical.R22 h (d x.1) (c x.1) x.2 : ℝ)

/-- Good pairs for the positive half-moment, before residue grouping.
No good-prime restriction is needed in this stronger form. -/
structure InPositive (F : MvPolynomial (Fin 10) ℤ)
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (tables : ∀ k : Fin 4, MicrolocalPromotionTable.Table F f (k.val+1))
    (h : CoarseBounds F C) (D : ℝ)
    (u : Fin 10 → ℝ) (L : ℝ) (m : ℕ) (x : Sample) : Prop where
  window : x.1 ∈ CubeFreeNonzeroAverage.window D
  progression_coprime : m.Coprime x.1
  good : ConductorFixedFrequency.GoodFrequency F f tables x.2
  box : ∀ k, |(x.2 k : ℝ)-u k| ≤ L
  cutoff : (NumericalConductorRadical.R22 h (d x.1) (c x.1) x.2 : ℝ) ≤ 1+L/(m : ℝ)

/-- Complementary weighted sum controlled by the unnormalised mass of
the periodic majorant, uniformly in every later parameter and weight. -/
theorem exists_complement_bound
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
      ∀ (E : Finset Sample) (w : (Fin 10 → ℤ) → ℝ) (P : (Fin 10 → ZMod m) → ℝ),
      (∀ x ∈ E, InComplement F f tables N h D u L m x) →
      (∀ b, 0 ≤ P b) → (∀ x ∈ E, w x.2 ≤ P (residue m x.2)) →
      (∑ x ∈ E, w x.2 * ‖completeCubicSum F x.1 x.2‖) ≤
        M*(D*(2+‖u‖+L+(m : ℝ)))^ε*D^((59 : ℝ)/6)*
          ((1+L/(m : ℝ))/D^((1 : ℝ)/3)+((1+L/(m : ℝ))/D^((1 : ℝ)/3))^9) *
            ∑ b, P b := by
  obtain ⟨M,hM,hbound⟩ := ComplementCubeFreeMeanReduced.of_data
    integrality cubicWeil isolated pointcount hP hhom hAn hc ε hε
  refine ⟨M,hM,?_⟩
  intro D hD u L hL m hm E w P hE hP0 hmajor
  apply FiniteWeightedClassSum.sum_mul_le E Finset.univ (fun x => residue m x.2)
    (fun x => ‖completeCubicSum F x.1 x.2‖) (fun x => w x.2) P
    (M*(D*(2+‖u‖+L+(m : ℝ)))^ε*D^((59 : ℝ)/6)*
      ((1+L/(m : ℝ))/D^((1 : ℝ)/3)+((1+L/(m : ℝ))/D^((1 : ℝ)/3))^9))
    (fun _ _ => Finset.mem_univ _) (fun _ _ => norm_nonneg _) (fun b _ => hP0 b) hmajor
  intro b _
  apply hbound D hD u L hL m (Nat.pos_of_ne_zero (NeZero.ne m)) (lift b)
  intro x hx
  obtain ⟨hx,hb⟩ := Finset.mem_filter.mp hx
  have hh := hE x hx
  exact ⟨hh.window,hh.good_primes,hh.progression_coprime,hh.nonzero,hh.box,
    (residue_eq_iff_dvd_sub m x.2 b).mp hb,hh.complement⟩

/-- The weighted positive half-moment, retaining the exact tenth power of
the progression width and using the same data as the complementary mean. -/
theorem exists_positive_bound
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    (hP : MicrolocalRationalPartition.Conclusion F f N Betti tables)
    (hhom : F.IsHomogeneous 3) (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C d₀ h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ D : ℝ, 1 ≤ D →
      ∀ (u : Fin 10 → ℝ) (L : ℝ), 1 ≤ L → ∀ (m : ℕ) [NeZero m],
      ∀ (E : Finset Sample) (w : (Fin 10 → ℤ) → ℝ) (P : (Fin 10 → ZMod m) → ℝ),
      (∀ x ∈ E, InPositive F f tables h D u L m x) →
      (∀ b, 0 ≤ P b) → (∀ x ∈ E, w x.2 ≤ P (residue m x.2)) →
      (∑ x ∈ E, w x.2 * ‖completeCubicSum F x.1 x.2‖ *
        (conductor h x.1 x.2)^((1 : ℝ)/2)) ≤
        M*(D*(2+‖u‖+L+(m : ℝ)))^ε*D^((13 : ℝ)/2)*(1+L/(m : ℝ))^10 *
          ∑ b, P b := by
  obtain ⟨M,hM,hbound⟩ := CubeFreeConductorMoments.exists_positive_bound
    pointcount hP.geometry hhom hAn hP.incidence hP.modulus_pos hc ε hε
  refine ⟨M,hM,?_⟩
  intro D hD u L hL m hm E w P hE hP0 hmajor
  let K := M*(D*(2+‖u‖+L+(m : ℝ)))^ε*(1+L/(m : ℝ))^10*D^((13 : ℝ)/2)
  have hclass (b : Fin 10 → ZMod m) :
      (∑ x ∈ E.filter (fun x => residue m x.2 = b),
        ‖completeCubicSum F x.1 x.2‖*(conductor h x.1 x.2)^((1 : ℝ)/2)) ≤ K := by
    let V := frequencies f tables u L m (lift b)
    let Q := ((CubeFreeNonzeroAverage.window D).product V).filter fun x =>
      x.1.Coprime m ∧
        (NumericalConductorRadical.R22 h (d x.1) (c x.1) x.2 : ℝ) ≤ 1+L/(m : ℝ)
    have hsub : E.filter (fun x => residue m x.2 = b) ⊆ Q := by
      intro x hx
      obtain ⟨hx,hb⟩ := Finset.mem_filter.mp hx
      have hh := hE x hx
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨hh.window,?_⟩,hh.progression_coprime.symm,hh.cutoff⟩
      exact (mem_frequencies f tables u L m (lift b) x.2).mpr
        ⟨hh.box,(residue_eq_iff_dvd_sub m x.2 b).mp hb,hh.good⟩
    calc
      _ ≤ ∑ x ∈ Q, ‖completeCubicSum F x.1 x.2‖*(conductor h x.1 x.2)^((1 : ℝ)/2) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ =>
          mul_nonneg (norm_nonneg _) (Real.rpow_nonneg
            (zero_le_one.trans (CubeFreeFixedFrequency.one_le_conductor h x.1 x.2)) _))
      _ = ∑ v ∈ V, ∑ q ∈ positiveModuli h v D m L,
          ‖completeCubicSum F q v‖*(conductor h q v)^((1 : ℝ)/2) := by
        simp only [Q,positiveModuli,Finset.product_eq_sprod,Finset.sum_filter,Finset.sum_product]
        rw [Finset.sum_comm]
      _ ≤ K := hbound D m u L (lift b) hD (Nat.pos_of_ne_zero (NeZero.ne m))
        (zero_le_one.trans hL)
  have hs := FiniteWeightedClassSum.sum_mul_le E Finset.univ (fun x => residue m x.2)
    (fun x => ‖completeCubicSum F x.1 x.2‖*(conductor h x.1 x.2)^((1 : ℝ)/2))
    (fun x => w x.2) P K (fun _ _ => Finset.mem_univ _)
    (fun x _ => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg
      (zero_le_one.trans (CubeFreeFixedFrequency.one_le_conductor h x.1 x.2)) _))
    (fun b _ => hP0 b) hmajor (fun b _ => hclass b)
  convert hs using 1
  · apply Finset.sum_congr rfl
    intro x _
    ring
  · dsimp [K]
    ring

end CubicTenVariables.CubeFreeWeightedResiduesReduced

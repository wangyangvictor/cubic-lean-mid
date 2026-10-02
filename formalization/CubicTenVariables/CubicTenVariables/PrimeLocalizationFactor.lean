import CubicTenVariables.LocalizedFirstLiftVanishing
import CubicTenVariables.PrimeLocalizationResidues
import CubicTenVariables.LocalZeroLowerBound
import CubicTenVariables.LocalizedRootSeriesIdentity

/-! The local factor of the actual smooth unit-orbit restriction has only
finitely many nonzero prime-power coefficients. Its normalized root density
stabilizes, and the resulting factor is strictly positive. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PrimeLocalizationData
open MvPolynomial PadicUnitOrbit LocalZeroResidues NormalizedLocalCounts
open PrimePowerFibers LocalizedRootSeriesIdentity Filter
open scoped BigOperators Topology
variable {p : ℕ} [Fact p.Prime] {F : MvPolynomial (Fin 10) ℤ}

/-- Fixed-level restrictions and a uniformly nonzero derivative force exact
character cancellation at every sufficiently high equation modulus. -/
theorem exists_local_coefficient_vanishing (D : PrimeLocalizationData p F)
    (hF : F.IsHomogeneous 3) :
    ∃ K : ℕ, D.modulusExponent ≤ K ∧ ∀ k ≥ K,
      localizedSingularSeriesTerm F (p^D.modulusExponent) D.residueSet (p^k) = 0 := by
  obtain ⟨t,ht,hderiv⟩ := D.exists_uniform_partial_not_dvd
  let K := max (2*t) (D.modulusExponent+t)
  refine ⟨K,by dsimp [K]; omega,?_⟩
  intro k hk
  have htk : t ≤ k := by dsimp [K] at hk; omega
  have htkt : t ≤ k-t := by dsimp [K] at hk; omega
  have hMkt : D.modulusExponent ≤ k-t := by dsimp [K] at hk; omega
  haveI : NeZero (p^t) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero (p^(k-t)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hs := LocalizedFirstLiftVanishing.complete_sum_eq_zero F hF
    (p^t) (p^(k-t)) (p^D.modulusExponent) (pow_dvd_pow p htkt)
    (pow_dvd_pow p hMkt) D.residueSet (fun y hy => ⟨D.partialIndex,hderiv _ hy⟩)
  have he : p^t * p^(k-t) = p^k := by rw [←pow_add,Nat.add_sub_of_le htk]
  rw [he] at hs
  simp only [localizedSingularSeriesTerm, if_neg (pow_ne_zero _
    (Fact.out : p.Prime).ne_zero),hs,zero_div]

/-- At levels containing the restriction modulus, the literal residue
condition selects exactly the modular roots admitting a lift in the orbit. -/
theorem modularZeroResidues_eq_restricted (D : PrimeLocalizationData p F)
    (s : ℕ) (hMs : D.modulusExponent ≤ s) :
    modularZeroResidues p F (unitOrbit p D.center D.modulusExponent) s =
      {v | (fun i => reduction p hMs (v i)) ∈ D.residueSet ∧
        eval₂ (Int.castRingHom (ZMod (p^s))) v F = 0} := by
  ext v
  constructor
  · rintro ⟨hzero,z,hz,hv⟩
    refine ⟨⟨z,hz,?_⟩,hzero⟩
    funext i
    rw [←hv i]
    simp only [reduction,ZMod.castHom_apply,PadicInt.cast_toZModPow _ _ hMs]
  · rintro ⟨⟨y,hy,hred⟩,hzero⟩
    obtain ⟨z,hz,hv⟩ := exists_integral_lift_mem_coset p y D.modulusExponent s hMs v
      (fun j => (congrFun hred j).symm)
    exact ⟨hzero,z,mem_unitOrbit_of_reduction_eq p D.center D.modulusExponent y z hy
      ((mem_coset_iff p y z D.modulusExponent).mp hz),hv⟩

/-- Root-density normalization agrees with the actual modular-zero count
on the selected p-adic unit orbit. -/
theorem rootDensity_eq_normalizedCount (D : PrimeLocalizationData p F)
    (s : ℕ) (hMs : D.modulusExponent ≤ s) :
    rootDensity F p D.modulusExponent s D.residueSet =
      (normalizedCount p 9 (fun t => Nat.card (modularZeroResidues p F
        (unitOrbit p D.center D.modulusExponent) t)) s : ℂ) := by
  classical
  rw [root_density_eq_sum,←residue_root_density_eq_sum_of_le F (by norm_num)
    p D.modulusExponent s D.residueSet hMs]
  rw [normalizedCount,D.modularZeroResidues_eq_restricted s hMs]
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype,Set.mem_setOf_eq,
    Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_pow]

/-- The root density stabilizes at a finite level, without a convergence
hypothesis. The threshold is fixed by the supplied local data. -/
theorem exists_rootDensity_stabilization (D : PrimeLocalizationData p F)
    (hF : F.IsHomogeneous 3) :
    ∃ K : ℕ, D.modulusExponent ≤ K ∧ ∀ s ≥ K,
      rootDensity F p D.modulusExponent s D.residueSet =
        rootDensity F p D.modulusExponent K D.residueSet := by
  obtain ⟨K,hMK,hvan⟩ := D.exists_local_coefficient_vanishing hF
  refine ⟨K,hMK,?_⟩
  intro s hs
  induction s,hs using Nat.le_induction with
  | base => rfl
  | succ s hs ih =>
    have he : rootDensity F p D.modulusExponent (s+1) D.residueSet =
        rootDensity F p D.modulusExponent s D.residueSet := by
      apply sub_eq_zero.mp
      rw [←localizedSingularSeriesTerm_prime_power]
      exact hvan (s+1) (by omega)
    exact he.trans ih

/-- Absolute convergence of the actual prime-power factor follows from
finite support, not an estimate or a supplied convergence premise. -/
theorem summable_norm_local_coefficient (D : PrimeLocalizationData p F)
    (hF : F.IsHomogeneous 3) :
    Summable (fun k => ‖localizedSingularSeriesTerm F
      (p^D.modulusExponent) D.residueSet (p^k)‖) := by
  obtain ⟨K,_,hvan⟩ := D.exists_local_coefficient_vanishing hF
  apply summable_of_ne_finset_zero (s := Finset.range K)
  intro k hk
  rw [hvan k (by simpa only [Finset.mem_range,not_lt] using hk),norm_zero]

/-- The normalized count on the literal unit orbit is eventually equal
to a strictly positive real number, and therefore converges to it. -/
theorem exists_positive_normalized_root_limit (D : PrimeLocalizationData p F)
    (hF : F.IsHomogeneous 3) :
    ∃ L : ℝ, 0 < L ∧
      (∀ᶠ s : ℕ in atTop, normalizedCount p 9
        (fun t => Nat.card (modularZeroResidues p F
          (unitOrbit p D.center D.modulusExponent) t)) s = L) ∧
      Tendsto (normalizedCount p 9 (fun t => Nat.card (modularZeroResidues p F
        (unitOrbit p D.center D.modulusExponent) t))) atTop (𝓝 L) := by
  obtain ⟨K,hMK,hstab⟩ := D.exists_rootDensity_stabilization hF
  let N := normalizedCount p 9 (fun t => Nat.card (modularZeroResidues p F
    (unitOrbit p D.center D.modulusExponent) t))
  have heq : ∀ᶠ s : ℕ in atTop, N s = N K := by
    filter_upwards [eventually_ge_atTop K] with s hs
    apply Complex.ofReal_injective
    change (N s : ℂ) = (N K : ℂ)
    rw [←D.rootDensity_eq_normalizedCount s (hMK.trans hs),
      ←D.rootDensity_eq_normalizedCount K hMK]
    exact hstab s hs
  have hlim : Tendsto N atTop (𝓝 (N K)) :=
    tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heq)
  exact ⟨N K,D.modular_zero_density_pos_of_tendsto (N K) hlim,heq,hlim⟩

/-- The actual localized prime-power series has a strictly positive real
sum. Its modulus-one term is included with its actual restriction density. -/
theorem exists_positive_local_factor (D : PrimeLocalizationData p F)
    (hF : F.IsHomogeneous 3) :
    ∃ L : ℝ, 0 < L ∧
      Summable (fun k => ‖localizedSingularSeriesTerm F
        (p^D.modulusExponent) D.residueSet (p^k)‖) ∧
      HasSum (fun k => localizedSingularSeriesTerm F
        (p^D.modulusExponent) D.residueSet (p^k)) (L : ℂ) ∧
      Tendsto (fun k => rootDensity F p D.modulusExponent k D.residueSet)
        atTop (𝓝 (L : ℂ)) := by
  obtain ⟨K,hMK,hvan⟩ := D.exists_local_coefficient_vanishing hF
  have hsum : HasSum (fun k => localizedSingularSeriesTerm F
      (p^D.modulusExponent) D.residueSet (p^k))
      (rootDensity F p D.modulusExponent K D.residueSet) := by
    rw [root_density_eq_sum]
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    exact hvan k (by simp only [Finset.mem_range,not_lt] at hk; omega)
  obtain ⟨L,hL,_,hlim⟩ := D.exists_positive_normalized_root_limit hF
  have hrootlim : Tendsto (fun k => rootDensity F p D.modulusExponent k D.residueSet)
      atTop (𝓝 (L:ℂ)) := by
    apply (Complex.continuous_ofReal.tendsto L |>.comp hlim).congr'
    filter_upwards [eventually_ge_atTop D.modulusExponent] with k hk
    exact (D.rootDensity_eq_normalizedCount k hk).symm
  have hsumlim : Tendsto (fun k => rootDensity F p D.modulusExponent k D.residueSet)
      atTop (𝓝 (rootDensity F p D.modulusExponent K D.residueSet)) := by
    simpa only [Function.comp_def,root_density_eq_sum] using
      hsum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have heq := tendsto_nhds_unique hsumlim hrootlim
  exact ⟨L,hL,D.summable_norm_local_coefficient hF,heq ▸ hsum,hrootlim⟩

end CubicTenVariables.PrimeLocalizationData

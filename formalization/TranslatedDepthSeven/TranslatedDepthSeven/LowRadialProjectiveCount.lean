import TranslatedDepthSeven.PublishedCountingApplications
import Mathlib.Tactic

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators LinearAlgebra.Projectivization

theorem primitiveRationalVectorHeight_pos
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → ℚ) (hv : v ≠ 0) :
    0 < primitiveRationalVectorHeight v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hn
    apply hv
    funext i
    by_contra hvi
    exact hn ⟨i, hvi⟩
  have hcoord : primitiveRationalVectorCoordinate v i ≠ 0 := by
    intro hzero
    have hcast := primitiveRationalVectorCoordinate_cast v hv i
    rw [hzero, Int.cast_zero] at hcast
    exact (mul_ne_zero (primitiveRationalVectorScale_ne_zero v hv) hi)
      hcast.symm
  have hpositive : 0 < (primitiveRationalVectorCoordinate v i).natAbs :=
    Int.natAbs_pos.mpr hcoord
  have hle : (primitiveRationalVectorCoordinate v i).natAbs ≤
      primitiveRationalVectorHeight v := by
    exact Finset.le_sup (f := fun j ↦
      (primitiveRationalVectorCoordinate v j).natAbs) (Finset.mem_univ i)
  omega

theorem projectivePrimitiveHeight_pos
    {N : ℕ}
    (x : Projectivization ℚ (Fin (N + 1) → ℚ)) :
    0 < primitiveRationalVectorHeight x.rep :=
  primitiveRationalVectorHeight_pos x.rep x.rep_nonzero

theorem one_div_nat_eq_terminal_add_sum
    {h X : ℕ} (hh : 0 < h) (hX : h ≤ X) :
    (1 : ℝ) / h =
      1 / (X + 1) +
        ∑ k ∈ Finset.Icc h X,
          (1 : ℝ) / ((k : ℝ) * (k + 1)) := by
  induction X, hX using Nat.le_induction with
  | base =>
      simp only [Finset.Icc_self, Finset.sum_singleton]
      have hhreal : (0 : ℝ) < h := by exact_mod_cast hh
      field_simp
  | succ X hle ih =>
      rw [Finset.sum_Icc_succ_top (hle.trans (Nat.le_succ X))]
      rw [ih]
      have hXp : (0 : ℝ) < X + 1 := by positivity
      have hX2p : (0 : ℝ) < X + 2 := by positivity
      have htel : (1 : ℝ) / (X + 1) =
          1 / (X + 2) + 1 / ((X + 1) * (X + 2)) := by
        field_simp
        ring
      rw [htel]
      norm_num [Nat.cast_add, Nat.cast_one, pow_two]
      ring_nf

def heightPrefix {α : Type*} [DecidableEq α]
    (S : Finset α) (height : α → ℕ) (k : ℕ) : Finset α :=
  S.filter fun x ↦ height x ≤ k

theorem sum_Icc_from_positive_eq_indicator
    {h X : ℕ} (hh : 0 < h) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc h X, f k) =
      ∑ k ∈ Finset.Icc 1 X, if h ≤ k then f k else 0 := by
  classical
  have hset : Finset.Icc h X =
      (Finset.Icc 1 X).filter fun k ↦ h ≤ k := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_filter]
    omega
  rw [hset, Finset.sum_filter]

theorem reciprocalHeight_sum_eq_partialSummation
    {α : Type*} [DecidableEq α]
    (S : Finset α) (height : α → ℕ) (X : ℕ)
    (hpositive : ∀ x ∈ S, 0 < height x)
    (hbounded : ∀ x ∈ S, height x ≤ X) :
    (∑ x ∈ S, (1 : ℝ) / height x) =
      (S.card : ℝ) / (X + 1) +
        ∑ k ∈ Finset.Icc 1 X,
          ((heightPrefix S height k).card : ℝ) /
            ((k : ℝ) * (k + 1)) := by
  classical
  calc
    (∑ x ∈ S, (1 : ℝ) / height x) =
        ∑ x ∈ S,
          ((1 : ℝ) / (X + 1) +
            ∑ k ∈ Finset.Icc (height x) X,
              (1 : ℝ) / ((k : ℝ) * (k + 1))) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact one_div_nat_eq_terminal_add_sum (hpositive x hx) (hbounded x hx)
    _ = ∑ x ∈ S,
          ((1 : ℝ) / (X + 1) +
            ∑ k ∈ Finset.Icc 1 X,
              if height x ≤ k then
                (1 : ℝ) / ((k : ℝ) * (k + 1)) else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [sum_Icc_from_positive_eq_indicator (hpositive x hx)]
    _ = (S.card : ℝ) / (X + 1) +
        ∑ x ∈ S, ∑ k ∈ Finset.Icc 1 X,
          if height x ≤ k then
            (1 : ℝ) / ((k : ℝ) * (k + 1)) else 0 := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    _ = (S.card : ℝ) / (X + 1) +
        ∑ k ∈ Finset.Icc 1 X, ∑ x ∈ S,
          if height x ≤ k then
            (1 : ℝ) / ((k : ℝ) * (k + 1)) else 0 := by
      rw [Finset.sum_comm]
    _ = (S.card : ℝ) / (X + 1) +
        ∑ k ∈ Finset.Icc 1 X,
          ((heightPrefix S height k).card : ℝ) /
            ((k : ℝ) * (k + 1)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      simp only [heightPrefix, div_eq_mul_inv]
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      simp

theorem rpow_four_add_div_nat_mul_succ_le_rpow_two_add
    (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) :
    (k : ℝ) ^ ((4 : ℝ) + ε) /
        ((k : ℝ) * (k + 1)) ≤
      (k : ℝ) ^ ((2 : ℝ) + ε) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.zero_lt_of_lt hk
  have hksucc : (0 : ℝ) < k + 1 := by positivity
  rw [div_le_iff₀ (mul_pos hkpos hksucc)]
  have hpow :
      (k : ℝ) ^ ((4 : ℝ) + ε) =
        (k : ℝ) ^ ((2 : ℝ) + ε) * (k : ℝ) ^ (2 : ℝ) := by
    rw [show (4 : ℝ) + ε = ((2 : ℝ) + ε) + 2 by ring,
      Real.rpow_add hkpos]
  rw [hpow, Real.rpow_two]
  have hnonneg : 0 ≤ (k : ℝ) ^ ((2 : ℝ) + ε) :=
    Real.rpow_nonneg (by positivity) _
  nlinarith

theorem terminal_power_div_succ_le_lower_power
    (X : ℕ) (hX : 1 ≤ X) (ε : ℝ) :
    (X : ℝ) ^ ((4 : ℝ) + ε) / (X + 1) ≤
      (X : ℝ) ^ ((3 : ℝ) + ε) := by
  have hXpos : (0 : ℝ) < X := by exact_mod_cast Nat.zero_lt_of_lt hX
  have hXsucc : (0 : ℝ) < X + 1 := by positivity
  rw [div_le_iff₀ hXsucc]
  have hpow :
      (X : ℝ) ^ ((4 : ℝ) + ε) =
        (X : ℝ) ^ ((3 : ℝ) + ε) * (X : ℝ) := by
    rw [show (4 : ℝ) + ε = ((3 : ℝ) + ε) + 1 by ring,
      Real.rpow_add hXpos]
    simp
  rw [hpow]
  have hnonneg : 0 ≤ (X : ℝ) ^ ((3 : ℝ) + ε) :=
    Real.rpow_nonneg (by positivity) _
  nlinarith

theorem reciprocalHeight_sum_le_two_mul_power
    {α : Type*} [DecidableEq α]
    (S : Finset α) (height : α → ℕ) (X : ℕ) (C ε : ℝ)
    (hX : 1 ≤ X) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hpositive : ∀ x ∈ S, 0 < height x)
    (hbounded : ∀ x ∈ S, height x ≤ X)
    (hprefix : ∀ k : ℕ, 1 ≤ k → k ≤ X →
      ((heightPrefix S height k).card : ℝ) ≤
        C * (k : ℝ) ^ ((4 : ℝ) + ε)) :
    (∑ x ∈ S, (1 : ℝ) / height x) ≤
      2 * C * (X : ℝ) ^ ((3 : ℝ) + ε) := by
  classical
  rw [reciprocalHeight_sum_eq_partialSummation S height X hpositive hbounded]
  have hprefixX := hprefix X hX (le_refl X)
  have hfilterX : heightPrefix S height X = S := by
    ext x
    simp only [heightPrefix, Finset.mem_filter]
    constructor
    · exact fun hx ↦ hx.1
    · intro hx
      exact ⟨hx, hbounded x hx⟩
  rw [hfilterX] at hprefixX
  have hterminal :
      (S.card : ℝ) / (X + 1) ≤
        C * (X : ℝ) ^ ((3 : ℝ) + ε) := by
    calc
      (S.card : ℝ) / (X + 1) ≤
          (C * (X : ℝ) ^ ((4 : ℝ) + ε)) / (X + 1) := by
        exact div_le_div_of_nonneg_right hprefixX (by positivity)
      _ = C * ((X : ℝ) ^ ((4 : ℝ) + ε) / (X + 1)) := by ring
      _ ≤ C * (X : ℝ) ^ ((3 : ℝ) + ε) := by
        exact mul_le_mul_of_nonneg_left
          (terminal_power_div_succ_le_lower_power X hX ε) hC
  have hsummand : ∀ k ∈ Finset.Icc 1 X,
      ((heightPrefix S height k).card : ℝ) /
          ((k : ℝ) * (k + 1)) ≤
        C * (X : ℝ) ^ ((2 : ℝ) + ε) := by
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    have hkpos : (0 : ℝ) < k := by
      exact_mod_cast Nat.zero_lt_of_lt hk'.1
    have hdenom : (0 : ℝ) < (k : ℝ) * (k + 1) := by positivity
    calc
      ((heightPrefix S height k).card : ℝ) /
          ((k : ℝ) * (k + 1)) ≤
          (C * (k : ℝ) ^ ((4 : ℝ) + ε)) /
            ((k : ℝ) * (k + 1)) := by
        exact div_le_div_of_nonneg_right
          (hprefix k hk'.1 hk'.2) hdenom.le
      _ = C * ((k : ℝ) ^ ((4 : ℝ) + ε) /
          ((k : ℝ) * (k + 1))) := by ring
      _ ≤ C * (k : ℝ) ^ ((2 : ℝ) + ε) := by
        exact mul_le_mul_of_nonneg_left
          (rpow_four_add_div_nat_mul_succ_le_rpow_two_add k hk'.1 ε) hC
      _ ≤ C * (X : ℝ) ^ ((2 : ℝ) + ε) := by
        apply mul_le_mul_of_nonneg_left _ hC
        exact Real.rpow_le_rpow (by positivity)
          (by exact_mod_cast hk'.2) (by linarith)
  have hsum :
      (∑ k ∈ Finset.Icc 1 X,
          ((heightPrefix S height k).card : ℝ) /
            ((k : ℝ) * (k + 1))) ≤
        C * (X : ℝ) ^ ((3 : ℝ) + ε) := by
    calc
      (∑ k ∈ Finset.Icc 1 X,
          ((heightPrefix S height k).card : ℝ) /
            ((k : ℝ) * (k + 1))) ≤
          ∑ k ∈ Finset.Icc 1 X,
            C * (X : ℝ) ^ ((2 : ℝ) + ε) := by
        exact Finset.sum_le_sum hsummand
      _ = (X : ℝ) * (C * (X : ℝ) ^ ((2 : ℝ) + ε)) := by
        simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
        have hcard : X + 1 - 1 = X := by omega
        rw [hcard]
      _ = C * (X : ℝ) ^ ((3 : ℝ) + ε) := by
        have hXpos : (0 : ℝ) < X := by
          exact_mod_cast Nat.zero_lt_of_lt hX
        have hpow3 :
            (X : ℝ) ^ ((3 : ℝ) + ε) =
              (X : ℝ) ^ ((2 : ℝ) + ε) * X := by
          rw [show (3 : ℝ) + ε = ((2 : ℝ) + ε) + 1 by ring,
            Real.rpow_add hXpos]
          simp
        rw [hpow3]
        ring
  linarith

/-- Salberger's projective dimension-growth estimate, summed with the
reciprocal primitive height on a geometrically integral projective
fourfold.  The loss of one power is proved by the preceding discrete Abel
identity; it is not included in the published input. -/
theorem finiteProjectiveFourfold_reciprocalHeight_le_salberger2023
    (hSalberger : Published.Salberger2023Theorem01)
    {N d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : Published.IsIntegralProjectiveVariety I 4 d)
    (hd : 2 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
      ∀ S : Finset (Projectivization ℚ (Fin (N + 1) → ℚ)),
        (∀ x ∈ S, ∀ f ∈ I, MvPolynomial.eval x.rep f = 0) →
        (∀ x ∈ S, primitiveRationalVectorHeight x.rep ≤ X) →
        (∑ x ∈ S,
            (1 : ℝ) / primitiveRationalVectorHeight x.rep) ≤
          C * (X : ℝ) ^ ((3 : ℝ) + ε) := by
  classical
  obtain ⟨C₀, hC₀, hsource⟩ :=
    Published.salberger2023_theorem01_apply hSalberger I hI hd hε
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro X hX S hvanish hheight
  have hprefix : ∀ k : ℕ, 1 ≤ k → k ≤ X →
      ((heightPrefix S
          (fun x ↦ primitiveRationalVectorHeight x.rep) k).card : ℝ) ≤
        C₀ * (k : ℝ) ^ ((4 : ℝ) + ε) := by
    intro k hk hkX
    obtain ⟨hfinite, hbound⟩ :=
      hsource (k : ℝ) (by exact_mod_cast hk)
    let Sₖ := heightPrefix S
      (fun x ↦ primitiveRationalVectorHeight x.rep) k
    have hsubset : (↑Sₖ : Set
        (Projectivization ℚ (Fin (N + 1) → ℚ))) ⊆
        Published.rationalProjectivePoints I (k : ℝ) := by
      intro x hx
      change x ∈ heightPrefix S
        (fun y ↦ primitiveRationalVectorHeight y.rep) k at hx
      rw [heightPrefix, Finset.mem_filter] at hx
      exact ⟨hvanish x hx.1, by exact_mod_cast hx.2⟩
    have hncard : Sₖ.card ≤
        (Published.rationalProjectivePoints I (k : ℝ)).ncard := by
      simpa only [Set.ncard_coe_finset] using
        Set.ncard_le_ncard hsubset hfinite
    exact (by exact_mod_cast hncard :
      (Sₖ.card : ℝ) ≤
        ((Published.rationalProjectivePoints I (k : ℝ)).ncard : ℝ)).trans
      hbound
  exact reciprocalHeight_sum_le_two_mul_power S
    (fun x ↦ primitiveRationalVectorHeight x.rep) X C₀ ε hX hC₀.le
    hε.le (fun x hx ↦ projectivePrimitiveHeight_pos x) hheight hprefix

/-- The literal low-radial summand after the normalized two-plane lattice
bound.  It combines one application of Salberger's unweighted projective
fourfold estimate with the independently proved reciprocal-height estimate.
-/
theorem finiteProjectiveFourfold_radialWeight_le_salberger2023
    (hSalberger : Published.Salberger2023Theorem01)
    {N d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : Published.IsIntegralProjectiveVariety I 4 d)
    (hd : 2 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
      ∀ T : ℝ, 1 ≤ T →
      ∀ S : Finset (Projectivization ℚ (Fin (N + 1) → ℚ)),
        (∀ x ∈ S, ∀ f ∈ I, MvPolynomial.eval x.rep f = 0) →
        (∀ x ∈ S, primitiveRationalVectorHeight x.rep ≤ X) →
        (∑ x ∈ S,
            ((1 : ℝ) + T +
              T ^ 2 / primitiveRationalVectorHeight x.rep)) ≤
          C * (T * (X : ℝ) ^ ((4 : ℝ) + ε) +
            T ^ 2 * (X : ℝ) ^ ((3 : ℝ) + ε)) := by
  classical
  obtain ⟨C₀, hC₀, hcard⟩ :=
    Published.salberger2023_theorem01_apply hSalberger I hI hd hε
  obtain ⟨C₁, hC₁, hreciprocal⟩ :=
    finiteProjectiveFourfold_reciprocalHeight_le_salberger2023
      hSalberger I hI hd ε hε
  let C : ℝ := 2 * C₀ + C₁
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro X hX T hT S hvanish hheight
  have hmembership : ∀ x ∈ S,
      x ∈ Published.rationalProjectivePoints I (X : ℝ) := by
    intro x hx
    exact ⟨hvanish x hx, by exact_mod_cast hheight x hx⟩
  obtain ⟨hfinite, hsourceBound⟩ :=
    hcard (X : ℝ) (by exact_mod_cast hX)
  have hsubset : (↑S : Set
      (Projectivization ℚ (Fin (N + 1) → ℚ))) ⊆
      Published.rationalProjectivePoints I (X : ℝ) := by
    intro x hx
    exact hmembership x hx
  have hncard : S.card ≤
      (Published.rationalProjectivePoints I (X : ℝ)).ncard := by
    simpa only [Set.ncard_coe_finset] using
      Set.ncard_le_ncard hsubset hfinite
  have hcardBound : (S.card : ℝ) ≤
      C₀ * (X : ℝ) ^ ((4 : ℝ) + ε) :=
    (by exact_mod_cast hncard :
      (S.card : ℝ) ≤
        ((Published.rationalProjectivePoints I (X : ℝ)).ncard : ℝ)).trans
      hsourceBound
  have hreciprocalBound := hreciprocal X hX S hvanish hheight
  have hTnonneg : 0 ≤ T := zero_le_one.trans hT
  have hX4 : 0 ≤ (X : ℝ) ^ ((4 : ℝ) + ε) :=
    Real.rpow_nonneg (by positivity) _
  have hX3 : 0 ≤ (X : ℝ) ^ ((3 : ℝ) + ε) :=
    Real.rpow_nonneg (by positivity) _
  have hreciprocalNonneg :
      0 ≤ ∑ x ∈ S, (1 : ℝ) /
        primitiveRationalVectorHeight x.rep := by
    apply Finset.sum_nonneg
    intro x hx
    positivity
  calc
    (∑ x ∈ S,
        ((1 : ℝ) + T +
          T ^ 2 / primitiveRationalVectorHeight x.rep)) =
        (S.card : ℝ) * (1 + T) +
          T ^ 2 * (∑ x ∈ S,
            (1 : ℝ) / primitiveRationalVectorHeight x.rep) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const,
        nsmul_eq_mul, div_eq_mul_inv]
      rw [Finset.mul_sum]
      ring_nf
    _ ≤ (C₀ * (X : ℝ) ^ ((4 : ℝ) + ε)) * (2 * T) +
          T ^ 2 * (C₁ * (X : ℝ) ^ ((3 : ℝ) + ε)) := by
      have honeT : 1 + T ≤ 2 * T := by linarith
      gcongr
    _ ≤ C * (T * (X : ℝ) ^ ((4 : ℝ) + ε) +
          T ^ 2 * (X : ℝ) ^ ((3 : ℝ) + ε)) := by
      have hterm0 : 0 ≤ T * (X : ℝ) ^ ((4 : ℝ) + ε) :=
        mul_nonneg hTnonneg hX4
      have hterm1 : 0 ≤ T ^ 2 * (X : ℝ) ^ ((3 : ℝ) + ε) :=
        mul_nonneg (sq_nonneg T) hX3
      have hcoeff0 : 2 * C₀ ≤ C := by
        dsimp only [C]
        linarith
      have hcoeff1 : C₁ ≤ C := by
        dsimp only [C]
        linarith
      calc
        (C₀ * (X : ℝ) ^ ((4 : ℝ) + ε)) * (2 * T) +
            T ^ 2 * (C₁ * (X : ℝ) ^ ((3 : ℝ) + ε)) =
            (2 * C₀) * (T * (X : ℝ) ^ ((4 : ℝ) + ε)) +
              C₁ * (T ^ 2 * (X : ℝ) ^ ((3 : ℝ) + ε)) := by ring
        _ ≤ C * (T * (X : ℝ) ^ ((4 : ℝ) + ε)) +
              C * (T ^ 2 * (X : ℝ) ^ ((3 : ℝ) + ε)) :=
          add_le_add
            (mul_le_mul_of_nonneg_right hcoeff0 hterm0)
            (mul_le_mul_of_nonneg_right hcoeff1 hterm1)
        _ = C * (T * (X : ℝ) ^ ((4 : ℝ) + ε) +
              T ^ 2 * (X : ℝ) ^ ((3 : ℝ) + ε)) := by ring

end

end TranslatedDepthSeven

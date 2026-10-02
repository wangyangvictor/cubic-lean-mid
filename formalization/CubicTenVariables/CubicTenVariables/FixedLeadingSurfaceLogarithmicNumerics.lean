import CubicTenVariables.FixedLeadingSurfaceSurvivorNumerics
import CubicTenVariables.FixedLeadingSurfacePersistentRootDegreeSplit
import TranslatedDepthSeven.SurfaceMixedLogDegreeChoice

/-!
# Numerical caps for logarithmic surface auxiliaries

The original Salberger degree is sharper than the power-sized degree used by
the existing changed-edge ledger.  Above one fixed height, the factor
`L * log H` is bounded by `H ^ eta`.  Consequently the logarithmic family can
reuse every existing modulus-sensitive edge estimate, while its terminal
degree remains genuinely `O(log H)` for the high-degree curve argument.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceLogarithmicNumerics

open Filter MvPolynomial TranslatedDepthSeven
open FixedLeadingSurfaceSurvivorNumerics
open FixedLeadingSurfacePersistentRootDegreeSplit
open scoped Topology

/-- A fixed multiple of `log H` is eventually bounded by any prescribed
positive power of `H`.  The threshold is chosen before the natural height. -/
theorem exists_logarithmicFactor_le_power
    (L eta : ℝ) (hL : 0 ≤ L) (heta : 0 < eta) :
    ∃ H₀ : ℕ, 1 ≤ H₀ ∧ ∀ H : ℕ, H₀ ≤ H →
      L * Real.log (H : ℝ) ≤ (H : ℝ) ^ eta := by
  have hc : 0 < (L + 1)⁻¹ := inv_pos.mpr (by linarith)
  have hsmall : ∀ᶠ H : ℝ in atTop,
      ‖Real.log H‖ ≤ (L + 1)⁻¹ * ‖H ^ eta‖ :=
    (isLittleO_log_rpow_atTop heta).bound hc
  have hall : ∀ᶠ H : ℝ in atTop,
      1 ≤ H ∧ L * Real.log H ≤ H ^ eta := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall] with H hH hsmallH
    have hlog : 0 ≤ Real.log H := Real.log_nonneg hH
    have hpow : 0 ≤ H ^ eta := Real.rpow_nonneg (by linarith) eta
    simp only [Real.norm_eq_abs, abs_of_nonneg hlog, abs_of_nonneg hpow] at hsmallH
    have hratio : L * (L + 1)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv]
      exact (div_le_one (by linarith : 0 < L + 1)).2 (by linarith)
    refine ⟨hH, ?_⟩
    calc
      L * Real.log H ≤ L * ((L + 1)⁻¹ * H ^ eta) :=
        mul_le_mul_of_nonneg_left hsmallH hL
      _ = (L * (L + 1)⁻¹) * H ^ eta := by ring
      _ ≤ H ^ eta := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hratio hpow
  obtain ⟨Hreal, hHreal⟩ := eventually_atTop.1 hall
  let H₀ : ℕ := max 1 ⌈Hreal⌉₊
  refine ⟨H₀, le_max_left _ _, ?_⟩
  intro H hH
  have hreal : Hreal ≤ (H : ℝ) :=
    (Nat.le_ceil Hreal).trans (by
      exact_mod_cast (Nat.le_max_right 1 ⌈Hreal⌉₊).trans hH)
  exact (hHreal (H : ℝ) hreal).2

/-- The sharp logarithmic block bound implies the older power majorant above
the fixed compatibility threshold. -/
theorem logarithmic_block_bound_le_power
    {L eta alpha : ℝ} {H B q k : ℕ}
    (hfactor : L * Real.log (H : ℝ) ≤ (H : ℝ) ^ eta)
    (hB : 1 ≤ B) (hq : 0 < q)
    (hk : (k : ℝ) ≤ 2 * L * Real.log (H : ℝ) *
      (1 + (B : ℝ) ^ alpha / (q : ℝ))) :
    (k : ℝ) ≤ 2 * (H : ℝ) ^ eta *
      (1 + (B : ℝ) ^ alpha / (q : ℝ)) := by
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hbracket : 0 ≤ 1 + (B : ℝ) ^ alpha / (q : ℝ) := by positivity
  calc
    (k : ℝ) ≤ 2 * L * Real.log (H : ℝ) *
        (1 + (B : ℝ) ^ alpha / (q : ℝ)) := hk
    _ = 2 * (L * Real.log (H : ℝ)) *
        (1 + (B : ℝ) ^ alpha / (q : ℝ)) := by ring
    _ ≤ 2 * (H : ℝ) ^ eta *
        (1 + (B : ℝ) ^ alpha / (q : ℝ)) := by gcongr

/-- Root cap obtained from the logarithmic degree without discarding its
sharp formula. -/
theorem logarithmic_root_degree_cap
    {P : Finset ℕ} {depth H B b : ℕ} {L alpha : ℝ}
    (hL : 0 ≤ L) (hH : 1 ≤ H)
    (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ)
    (hblock : ∀ v, (blockDegree v : ℝ) ≤
      2 * L * Real.log (H : ℝ) *
        (1 + (B : ℝ) ^ alpha /
          (PrimeSubsetPrefix.modulus v : ℝ))) :
    b + blockDegree (PrimeSubsetPrefix.root P depth) ≤
      b + ⌈4 * L * Real.log (H : ℝ) *
        (1 + (B : ℝ) ^ alpha)⌉₊ := by
  have hmod : PrimeSubsetPrefix.modulus
      (PrimeSubsetPrefix.root P depth) = 1 :=
    PrimeSubsetPrefix.modulus_root P depth
  have hk := hblock (PrimeSubsetPrefix.root P depth)
  rw [hmod, Nat.cast_one, div_one] at hk
  have hk' : (blockDegree (PrimeSubsetPrefix.root P depth) : ℝ) ≤
      4 * L * Real.log (H : ℝ) * (1 + (B : ℝ) ^ alpha) := by
    have hnonneg : 0 ≤ L * Real.log (H : ℝ) *
        (1 + (B : ℝ) ^ alpha) := by
      have hlog : 0 ≤ Real.log (H : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hH)
      positivity
    nlinarith
  exact Nat.add_le_add_left (by
    exact_mod_cast hk'.trans (Nat.le_ceil _)) b

/-- At a terminal modulus at least `B^alpha`, the logarithmic auxiliary has
degree at most a fixed multiple of `log H`. -/
theorem logarithmic_terminal_degree_cap
    {P : Finset ℕ} {depth H B b : ℕ} {L alpha : ℝ}
    (hL : 0 ≤ L) (hH : 1 ≤ H)
    (hP : ∀ p ∈ P, p.Prime)
    (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ)
    (hblock : ∀ v, (blockDegree v : ℝ) ≤
      2 * L * Real.log (H : ℝ) *
        (1 + (B : ℝ) ^ alpha /
          (PrimeSubsetPrefix.modulus v : ℝ)))
    (v : PrimeSubsetPrefix.Vertex P depth)
    (hlower : (B : ℝ) ^ alpha ≤
      (PrimeSubsetPrefix.modulus v : ℝ)) :
    b + blockDegree v ≤ b + ⌈4 * L * Real.log (H : ℝ)⌉₊ := by
  have hprime : ∀ p ∈ v.1, p.Prime := fun p hp =>
    hP p ((PrimeSubsetPrefix.mem_vertices.mp v.2).1 hp)
  have hq : (0 : ℝ) < PrimeSubsetPrefix.modulus v := by
    exact_mod_cast Nat.pos_of_ne_zero (primeProduct_ne_zero hprime)
  have hdiv : (B : ℝ) ^ alpha /
      (PrimeSubsetPrefix.modulus v : ℝ) ≤ 1 :=
    (div_le_one hq).mpr hlower
  have hk := hblock v
  have hk' : (blockDegree v : ℝ) ≤ 4 * L * Real.log (H : ℝ) := by
    have hlogfactor : 0 ≤ 2 * L * Real.log (H : ℝ) := by
      have hlog : 0 ≤ Real.log (H : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hH)
      positivity
    calc
      (blockDegree v : ℝ) ≤ 2 * L * Real.log (H : ℝ) *
          (1 + (B : ℝ) ^ alpha /
            (PrimeSubsetPrefix.modulus v : ℝ)) := hk
      _ ≤ 2 * L * Real.log (H : ℝ) * 2 := by gcongr; linarith
      _ = 4 * L * Real.log (H : ℝ) := by ring
  exact Nat.add_le_add_left (by
    exact_mod_cast hk'.trans (Nat.le_ceil _)) b

/-- The three-way degree split is bounded by the active-cardinality times
one copy of each possible nonlinear error.  In the eventual application the
low error uses the side length, whereas the high error uses the cube of that
length, the projective box volume in Salberger's notation. -/
theorem sum_persistentRootUniformDegreeSplitError_le_card_mul
    (degree : Ideal (MvPolynomial (Fin 4) Qbar) → ℕ)
    (active : Finset (Option (Ideal (MvPolynomial (Fin 4) Qbar))))
    (cutoff degreeCap : ℕ) (lowError highConstant epsilon volume : ℝ)
    (hdegreeCap : ∀ o ∈ active,
      rootOptionDegree degree o ≤ degreeCap)
    (hlow : 0 ≤ lowError) (hhigh : 0 ≤
      salberger2023Theorem316CurveError highConstant epsilon volume) :
    (∑ o ∈ active,
      persistentRootUniformDegreeSplitError degree cutoff lowError
        highConstant epsilon volume o) ≤
      (active.card : ℝ) *
        (lowError +
          salberger2023Theorem316CurveError highConstant epsilon volume +
          (degreeCap : ℝ) ^ 2) := by
  have hcap0 : 0 ≤ (degreeCap : ℝ) ^ 2 := sq_nonneg _
  have hpoint : ∀ o ∈ active,
      persistentRootUniformDegreeSplitError degree cutoff lowError
          highConstant epsilon volume o ≤
        lowError +
          salberger2023Theorem316CurveError highConstant epsilon volume +
          (degreeCap : ℝ) ^ 2 := by
    intro o ho
    have hcap := hdegreeCap o ho
    unfold persistentRootUniformDegreeSplitError
    split
    · linarith
    · split
      · linarith
      · unfold persistentRootHighDegreeError
        cases o with
        | none => simp; linarith
        | some Q =>
            simp only
            split
            · linarith
            · have hcapReal : (degree Q : ℝ) ≤ degreeCap := by
                exact_mod_cast hcap
              have hsquare : (degree Q : ℝ) ^ 2 ≤ (degreeCap : ℝ) ^ 2 := by
                gcongr
              linarith
  calc
    (∑ o ∈ active,
        persistentRootUniformDegreeSplitError degree cutoff lowError
          highConstant epsilon volume o) ≤
        ∑ _o ∈ active,
          (lowError +
            salberger2023Theorem316CurveError highConstant epsilon volume +
            (degreeCap : ℝ) ^ 2) := by
      exact Finset.sum_le_sum fun o ho ↦ hpoint o ho
    _ = (active.card : ℝ) *
        (lowError +
          salberger2023Theorem316CurveError highConstant epsilon volume +
          (degreeCap : ℝ) ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      ring

/-- The useful aggregate estimate keeps the degree-square contribution as
the square of the *total* root degree.  This is essential in the original
Salberger argument: the root degree is `O(H^alpha log H)`, so its square is
of order `H^(2 alpha)`; multiplying a worst individual square by the number
of components would lose an unnecessary additional factor `H^alpha`. -/
theorem sum_persistentRootUniformDegreeSplitError_le_card_mul_add_mass_sq
    (degree : Ideal (MvPolynomial (Fin 4) Qbar) → ℕ)
    (active : Finset (Option (Ideal (MvPolynomial (Fin 4) Qbar))))
    (cutoff degreeMass : ℕ) (lowError highConstant epsilon volume : ℝ)
    (hdegreeMass :
      (∑ o ∈ active, rootOptionDegree degree o) ≤ degreeMass)
    (hlow : 0 ≤ lowError) (hhigh : 0 ≤
      salberger2023Theorem316CurveError highConstant epsilon volume) :
    (∑ o ∈ active,
      persistentRootUniformDegreeSplitError degree cutoff lowError
        highConstant epsilon volume o) ≤
      (active.card : ℝ) *
        (lowError +
          salberger2023Theorem316CurveError highConstant epsilon volume) +
        (degreeMass : ℝ) ^ 2 := by
  let highError :=
    salberger2023Theorem316CurveError highConstant epsilon volume
  have hhigh' : 0 ≤ highError := hhigh
  have hpoint : ∀ o ∈ active,
      persistentRootUniformDegreeSplitError degree cutoff lowError
          highConstant epsilon volume o ≤
        lowError + highError + (rootOptionDegree degree o : ℝ) ^ 2 := by
    intro o ho
    unfold persistentRootUniformDegreeSplitError
    split
    · dsimp only [highError]
      positivity
    · split
      · dsimp only [highError]
        nlinarith [sq_nonneg (rootOptionDegree degree o : ℝ)]
      · unfold persistentRootHighDegreeError
        cases o with
        | none =>
            simp [rootOptionDegree, highError]
            positivity
        | some Q =>
            simp only [rootOptionDegree]
            split
            · dsimp only [highError]
              nlinarith [sq_nonneg (degree Q : ℝ)]
            · exact le_add_of_nonneg_left (by positivity)
  have hsumPoint :
      (∑ o ∈ active,
        persistentRootUniformDegreeSplitError degree cutoff lowError
          highConstant epsilon volume o) ≤
        ∑ o ∈ active,
          (lowError + highError +
            (rootOptionDegree degree o : ℝ) ^ 2) := by
    exact Finset.sum_le_sum fun o ho ↦ hpoint o ho
  have hsquare :
      (∑ o ∈ active, (rootOptionDegree degree o : ℝ) ^ 2) ≤
        ((∑ o ∈ active, rootOptionDegree degree o : ℕ) : ℝ) ^ 2 := by
    simpa only [Nat.cast_sum] using
      (Finset.sum_sq_le_sq_sum_of_nonneg
        (s := active) (f := fun o ↦ (rootOptionDegree degree o : ℝ))
        (fun _ _ ↦ by positivity))
  have hmassReal :
      ((∑ o ∈ active, rootOptionDegree degree o : ℕ) : ℝ) ≤
        (degreeMass : ℝ) := by
    exact_mod_cast hdegreeMass
  have hsquareMass :
      ((∑ o ∈ active, rootOptionDegree degree o : ℕ) : ℝ) ^ 2 ≤
        (degreeMass : ℝ) ^ 2 := by
    gcongr
  calc
    (∑ o ∈ active,
        persistentRootUniformDegreeSplitError degree cutoff lowError
          highConstant epsilon volume o) ≤
        ∑ o ∈ active,
          (lowError + highError +
            (rootOptionDegree degree o : ℝ) ^ 2) := hsumPoint
    _ = (active.card : ℝ) * (lowError + highError) +
        ∑ o ∈ active, (rootOptionDegree degree o : ℝ) ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ (active.card : ℝ) * (lowError + highError) +
        (degreeMass : ℝ) ^ 2 := by
      gcongr
      exact hsquare.trans hsquareMass
    _ = (active.card : ℝ) *
          (lowError +
            salberger2023Theorem316CurveError highConstant epsilon volume) +
        (degreeMass : ℝ) ^ 2 := by rfl

/-- Power-scale absorption for the preceding aggregate estimate.  It keeps
the three numerically different contributions separate: bounded-degree
curves, Salberger's high-degree curves, and distinct-conjugate intersections.
The caller only supplies their actual power scales. -/
theorem sum_persistentRootUniformDegreeSplitError_le_power_of_scales
    (degree : Ideal (MvPolynomial (Fin 4) Qbar) → ℕ)
    (active : Finset (Option (Ideal (MvPolynomial (Fin 4) Qbar))))
    (cutoff degreeMass : ℕ) (lowError highConstant epsilon volume : ℝ)
    (X Aroot Alow Ahigh rho sigma tau target : ℝ)
    (hdegreeMass :
      (∑ o ∈ active, rootOptionDegree degree o) ≤ degreeMass)
    (hX : 1 ≤ X)
    (hAroot : 0 ≤ Aroot) (hAlow : 0 ≤ Alow)
    (hAhigh : 0 ≤ Ahigh)
    (hlow : 0 ≤ lowError)
    (hhigh : 0 ≤
      salberger2023Theorem316CurveError highConstant epsilon volume)
    (hactiveScale : (active.card : ℝ) ≤ Aroot * X ^ rho)
    (hmassScale : (degreeMass : ℝ) ≤ Aroot * X ^ rho)
    (hlowScale : lowError ≤ Alow * X ^ sigma)
    (hhighScale :
      salberger2023Theorem316CurveError highConstant epsilon volume ≤
        Ahigh * X ^ tau)
    (hlowExponent : rho + sigma ≤ target)
    (hhighExponent : rho + tau ≤ target)
    (hmassExponent : 2 * rho ≤ target) :
    (∑ o ∈ active,
      persistentRootUniformDegreeSplitError degree cutoff lowError
        highConstant epsilon volume o) ≤
      (Aroot * Alow + Aroot * Ahigh + Aroot ^ 2) * X ^ target := by
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hXrho : 0 ≤ X ^ rho := by positivity
  have hXsigma : 0 ≤ X ^ sigma := by positivity
  have hXtau : 0 ≤ X ^ tau := by positivity
  have hlowProduct :
      (active.card : ℝ) * lowError ≤
        Aroot * Alow * X ^ target := by
    calc
      (active.card : ℝ) * lowError ≤
          (Aroot * X ^ rho) * (Alow * X ^ sigma) := by
        exact mul_le_mul hactiveScale hlowScale hlow
          (mul_nonneg hAroot hXrho)
      _ = Aroot * Alow * X ^ (rho + sigma) := by
        rw [Real.rpow_add hXpos]
        ring
      _ ≤ Aroot * Alow * X ^ target := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hX hlowExponent)
          (mul_nonneg hAroot hAlow)
  have hhighProduct :
      (active.card : ℝ) *
          salberger2023Theorem316CurveError highConstant epsilon volume ≤
        Aroot * Ahigh * X ^ target := by
    calc
      (active.card : ℝ) *
          salberger2023Theorem316CurveError highConstant epsilon volume ≤
          (Aroot * X ^ rho) * (Ahigh * X ^ tau) := by
        exact mul_le_mul hactiveScale hhighScale hhigh
          (mul_nonneg hAroot hXrho)
      _ = Aroot * Ahigh * X ^ (rho + tau) := by
        rw [Real.rpow_add hXpos]
        ring
      _ ≤ Aroot * Ahigh * X ^ target := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hX hhighExponent)
          (mul_nonneg hAroot hAhigh)
  have hmassProduct : (degreeMass : ℝ) ^ 2 ≤
      Aroot ^ 2 * X ^ target := by
    calc
      (degreeMass : ℝ) ^ 2 ≤ (Aroot * X ^ rho) ^ 2 := by
        gcongr
      _ = Aroot ^ 2 * X ^ (2 * rho) := by
        rw [mul_pow]
        congr 1
        calc
          (X ^ rho) ^ (2 : ℕ) = X ^ rho * X ^ rho := by ring
          _ = X ^ (rho + rho) := (Real.rpow_add hXpos rho rho).symm
          _ = X ^ (2 * rho) := by ring_nf
      _ ≤ Aroot ^ 2 * X ^ target := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hX hmassExponent)
          (sq_nonneg Aroot)
  have hbase :=
    sum_persistentRootUniformDegreeSplitError_le_card_mul_add_mass_sq
      degree active cutoff degreeMass lowError highConstant epsilon volume
      hdegreeMass hlow hhigh
  calc
    (∑ o ∈ active,
        persistentRootUniformDegreeSplitError degree cutoff lowError
          highConstant epsilon volume o) ≤
      (active.card : ℝ) *
          (lowError +
            salberger2023Theorem316CurveError highConstant epsilon volume) +
        (degreeMass : ℝ) ^ 2 := hbase
    _ = (active.card : ℝ) * lowError +
        (active.card : ℝ) *
          salberger2023Theorem316CurveError highConstant epsilon volume +
        (degreeMass : ℝ) ^ 2 := by ring
    _ ≤ Aroot * Alow * X ^ target +
        Aroot * Ahigh * X ^ target + Aroot ^ 2 * X ^ target := by
      gcongr
    _ = (Aroot * Alow + Aroot * Ahigh + Aroot ^ 2) * X ^ target := by
      ring

/-- Salberger's volume parameter is the cube of the affine side length in
the chart `[1,z₁,z₂,z₃]`.  This lemma converts the uniform high-degree error
to an explicit power of that side length, including its three logarithms. -/
theorem salberger2023Theorem316CurveError_cube_le_power
    (constant epsilon X eta : ℝ)
    (hconstant : 0 ≤ constant) (hepsilon : 0 ≤ epsilon)
    (hX : 1 ≤ X) (heta : 0 < eta) :
    salberger2023Theorem316CurveError constant epsilon (X ^ (3 : ℕ)) ≤
      constant * (1 + 3 * eta⁻¹) ^ (3 : ℕ) *
        X ^ (3 * epsilon / 2 + 3 * eta) := by
  have hX0 : 0 ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  have hinv : 0 ≤ eta⁻¹ := inv_nonneg.mpr heta.le
  have hlogX : Real.log X ≤ eta⁻¹ * X ^ eta := by
    have h := Real.log_le_rpow_div hX0 heta
    rw [div_eq_inv_mul] at h
    exact h
  have hpowOne : 1 ≤ X ^ eta := Real.one_le_rpow hX heta.le
  have hlogVolume : Real.log (X ^ (3 : ℕ)) = 3 * Real.log X := by
    rw [Real.log_pow]
    norm_num
  have hvolumeOne : 1 ≤ X ^ (3 : ℕ) := one_le_pow₀ hX
  have hlogNonneg : 0 ≤ Real.log (X ^ (3 : ℕ)) :=
    Real.log_nonneg hvolumeOne
  have hlogBound : 1 + Real.log (X ^ (3 : ℕ)) ≤
      (1 + 3 * eta⁻¹) * X ^ eta := by
    rw [hlogVolume]
    calc
      1 + 3 * Real.log X ≤ X ^ eta + 3 * (eta⁻¹ * X ^ eta) := by
        linarith
      _ = (1 + 3 * eta⁻¹) * X ^ eta := by ring
  have hlogPow : (1 + Real.log (X ^ (3 : ℕ))) ^ (3 : ℕ) ≤
      (1 + 3 * eta⁻¹) ^ (3 : ℕ) * X ^ (3 * eta) := by
    have hbase0 : 0 ≤ 1 + Real.log (X ^ (3 : ℕ)) := by linarith
    have hraw := pow_le_pow_left₀ hbase0 hlogBound 3
    calc
      (1 + Real.log (X ^ (3 : ℕ))) ^ (3 : ℕ) ≤
          ((1 + 3 * eta⁻¹) * X ^ eta) ^ (3 : ℕ) := hraw
      _ = (1 + 3 * eta⁻¹) ^ (3 : ℕ) *
          (X ^ eta) ^ (3 : ℕ) := by rw [mul_pow]
      _ = (1 + 3 * eta⁻¹) ^ (3 : ℕ) * X ^ (3 * eta) := by
        congr 1
        calc
          (X ^ eta) ^ (3 : ℕ) = Real.rpow (X ^ eta) 3 :=
            (Real.rpow_natCast (X ^ eta) 3).symm
          _ = X ^ (eta * 3) := (Real.rpow_mul hX0 eta 3).symm
          _ = X ^ (3 * eta) := by ring_nf
  have hvolumePower : (X ^ (3 : ℕ)) ^ (epsilon / 2) =
      X ^ (3 * epsilon / 2) := by
    calc
      (X ^ (3 : ℕ)) ^ (epsilon / 2) =
          Real.rpow (Real.rpow X 3) (epsilon / 2) := by
            congr 1
            exact (Real.rpow_natCast X 3).symm
      _ = X ^ ((3 : ℝ) * (epsilon / 2)) :=
        (Real.rpow_mul hX0 3 (epsilon / 2)).symm
      _ = X ^ (3 * epsilon / 2) := by ring_nf
  unfold salberger2023Theorem316CurveError
  rw [hvolumePower]
  calc
    constant * X ^ (3 * epsilon / 2) *
        (1 + Real.log (X ^ (3 : ℕ))) ^ (3 : ℕ) ≤
      constant * X ^ (3 * epsilon / 2) *
        ((1 + 3 * eta⁻¹) ^ (3 : ℕ) * X ^ (3 * eta)) := by
          gcongr
    _ = constant * (1 + 3 * eta⁻¹) ^ (3 : ℕ) *
        X ^ (3 * epsilon / 2 + 3 * eta) := by
      rw [Real.rpow_add hXpos]
      ring

/-- One simultaneous exponent choice for the original Salberger route.

`alpha + eta` is the root-component mass exponent; `1/2 + pilaEpsilon`
is the bounded-degree curve exponent; and
`3 * highEpsilon / 2 + 3 * eta` is the high-degree error after substituting
the three-dimensional affine-box volume and absorbing the three logarithms.
The same parameters retain the already proved changed-edge inequality. -/
theorem exists_originalSalberger_exponent_parameters
    {d : ℕ} (hd : 4 ≤ d) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ K alpha eta delta pilaEpsilon highEpsilon : ℝ,
      1 < K ∧ 0 < alpha ∧ alpha < 1 ∧
      0 < eta ∧ 0 < delta ∧
      0 < pilaEpsilon ∧ 0 < highEpsilon ∧
      Real.sqrt K / Real.sqrt (d : ℝ) < alpha ∧
      2 * eta + 3 * delta + 2 * alpha ≤ 1 + epsilon ∧
      (alpha + eta) + ((1 / 2 : ℝ) + pilaEpsilon) ≤
        1 + epsilon ∧
      (alpha + eta) +
          (3 * highEpsilon / 2 + 3 * eta) ≤ 1 + epsilon ∧
      2 * (alpha + eta) ≤ 1 + epsilon := by
  let t : ℝ := min epsilon 1
  have ht : 0 < t := lt_min hepsilon (by norm_num)
  have htepsilon : t ≤ epsilon := min_le_left _ _
  have htone : t ≤ 1 := min_le_right _ _
  let K : ℝ := (1 + t / 16) ^ 2
  let alpha : ℝ := 1 / 2 + t / 16
  let eta : ℝ := t / 64
  let delta : ℝ := t / 64
  let pilaEpsilon : ℝ := t / 64
  let highEpsilon : ℝ := t / 16
  have hK : 1 < K := by dsimp [K]; nlinarith
  have halpha : 0 < alpha := by dsimp [alpha]; linarith
  have halphaOne : alpha < 1 := by dsimp [alpha]; linarith
  have hroot : Real.sqrt K = 1 + t / 16 := by
    dsimp [K]
    exact Real.sqrt_sq (by linarith)
  have hdreal : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hdroot : (2 : ℝ) ≤ Real.sqrt (d : ℝ) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (d : ℝ) by positivity),
      Real.sqrt_nonneg (d : ℝ)]
  have hrange : Real.sqrt K / Real.sqrt (d : ℝ) < alpha := by
    apply (div_lt_iff₀ (by linarith : 0 < Real.sqrt (d : ℝ))).mpr
    rw [hroot]
    have hmul := mul_le_mul_of_nonneg_left hdroot halpha.le
    dsimp [alpha] at hmul ⊢
    nlinarith
  refine ⟨K, alpha, eta, delta, pilaEpsilon, highEpsilon,
    hK, halpha, halphaOne, by dsimp [eta]; positivity,
    by dsimp [delta]; positivity, by dsimp [pilaEpsilon]; positivity,
    by dsimp [highEpsilon]; positivity, hrange, ?_, ?_, ?_, ?_⟩
  · dsimp [alpha, eta, delta]
    linarith
  · dsimp [alpha, eta, pilaEpsilon]
    linarith
  · dsimp [alpha, eta, highEpsilon]
    linarith
  · dsimp [alpha, eta]
    linarith

end CubicTenVariables.FixedLeadingSurfaceLogarithmicNumerics

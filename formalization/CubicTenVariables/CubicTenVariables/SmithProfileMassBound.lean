import CubicTenVariables.SmithProfileMinimumBound
import CubicTenVariables.ProfileConstantAbsorption

/-!
# The actual local weighted Smith-profile mass

The cubic roots are partitioned by their canonical cumulative Hessian
profile. The proved minimum-cost count and finite profile cardinality give
one bound for every length and every terminal exponent beyond one prime
threshold. The minimum-cost estimate is proved; no profile count, weighted
mass estimate or unproved literature input is supplied.
-/

noncomputable section
namespace CubicTenVariables.SmithProfileMassBound
open MvPolynomial HessianTheorem11 SmithProfileNumerics HessianProfileRoots
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The finite profile of the literal residue Hessian. -/
def actualProfile (F : MvPolynomial (Fin 10) ℤ) (p a : ℕ)
    (z : Fin 10 → ZMod (p^a)) : Profile a :=
  MatrixSmithProfileInvariant.toProfile
    (MatrixSmithProfileInvariant.integerLift (matrix F (p^a) z)) p a

theorem entry_actualProfile (F : MvPolynomial (Fin 10) ℤ) (p a : ℕ)
    (z : Fin 10 → ZMod (p^a)) {i : ℕ} (hi : i < a) :
    entry (actualProfile F p a z) i = profileEntry F p a z i :=
  MatrixSmithProfileInvariant.entry_toProfile _ p hi

theorem profile_ext {a : ℕ} {c d : Profile a}
    (h : ∀ i < a, entry c i = entry d i) : c = d := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  simpa only [entry, dif_pos i.isLt] using h i i.isLt

theorem actualProfile_int_cast (F : MvPolynomial (Fin 10) ℤ)
    (p : ℕ) (hp : p.Prime) (a : ℕ) (y : Fin 10 → ℤ) :
    actualProfile F p a (fun i => (y i : ZMod (p^a))) =
      MatrixSmithProfileInvariant.toProfile (hessian F y) p a := by
  apply profile_ext
  intro i hi
  rw [entry_actualProfile F p a _ hi, profileEntry_int_cast F p hp hi,
    MatrixSmithProfileInvariant.entry_toProfile _ p hi]

theorem actualProfile_eq_ofDiagonal (F : MvPolynomial (Fin 10) ℤ)
    (p : ℕ) (hp : p.Prime) (a : ℕ) (y : Fin 10 → ℤ)
    (U V : (Matrix (Fin 10) (Fin 10) ℤ)ˣ) (d : Fin 10 → ℤ)
    (hD : (U : Matrix (Fin 10) (Fin 10) ℤ) * hessian F y *
      (V : Matrix (Fin 10) (Fin 10) ℤ) = Matrix.diagonal d) :
    actualProfile F p a (fun i => (y i : ZMod (p^a))) =
      HessianSmithProfile.ofDiagonal p a d := by
  apply profile_ext
  intro i hi
  rw [entry_actualProfile F p a _ hi, profileEntry_int_cast F p hp hi,
    HessianSmithProfile.entry_ofDiagonal p a d i hi]
  exact MatrixSmithProfileInvariant.entry_eq_truncated_profile_of_diagonalization
    _ d U V hD p hp hi

/-- The actual profile fiber agrees with the already counted literal roots. -/
theorem mem_roots_iff_profile (F : MvPolynomial (Fin 10) ℤ)
    (p : ℕ) [Fact p.Prime] (a : ℕ) (c : Profile a)
    (z : Fin 10 → ZMod (p^a)) :
    z ∈ roots F p a (entry c) ↔
      eval₂ (Int.castRingHom (ZMod (p^a))) z F = 0 ∧ actualProfile F p a z = c := by
  rw [mem_roots]
  constructor
  · rintro ⟨hz, hc⟩
    refine ⟨hz, profile_ext (fun i hi => ?_)⟩
    rw [entry_actualProfile F p a z hi]
    exact hc i hi
  · rintro ⟨hz, hc⟩
    refine ⟨hz, fun i hi => ?_⟩
    rw [← entry_actualProfile F p a z hi, hc]

theorem roots_eq_filter_profile (F : MvPolynomial (Fin 10) ℤ)
    (p : ℕ) [Fact p.Prime] (a : ℕ) (c : Profile a) :
    roots F p a (entry c) = Finset.univ.filter fun z =>
      eval₂ (Int.castRingHom (ZMod (p^a))) z F = 0 ∧ actualProfile F p a z = c := by
  classical
  ext z
  simp only [mem_roots_iff_profile, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Exact finite regrouping, valid for an arbitrary real profile weight. -/
theorem sum_roots_eq_sum_profiles (F : MvPolynomial (Fin 10) ℤ)
    (p : ℕ) [Fact p.Prime] (a : ℕ) (w : Profile a → ℝ) :
    (∑ z : Fin 10 → ZMod (p^a),
      if eval₂ (Int.castRingHom (ZMod (p^a))) z F = 0 then
        w (actualProfile F p a z) else 0) =
      ∑ c : Profile a, ((roots F p a (entry c)).card : ℝ) * w c := by
  classical
  symm
  calc
    _ = ∑ c : Profile a, ∑ z : Fin 10 → ZMod (p^a),
        if eval₂ (Int.castRingHom (ZMod (p^a))) z F = 0 ∧
          actualProfile F p a z = c then w c else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      rw [roots_eq_filter_profile]
      simp only [← nsmul_eq_mul, ← Finset.sum_const, Finset.sum_filter]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : eval₂ (Int.castRingHom (ZMod (p^a))) z F = 0
      · simp [hz]
      · simp [hz]

/-- A crude exponential count suffices because primes are eligible. -/
theorem card_profiles_le (a : ℕ) : Fintype.card (Profile a) ≤ 11^a := by
  calc
    _ ≤ Fintype.card (Fin a → Fin 11) :=
      Fintype.card_le_of_injective (fun c : Profile a => c.val) Subtype.val_injective
    _ = _ := by simp

/-- Literal local root mass with the manuscript's exact rational penalty. -/
def profileMass (F : MvPolynomial (Fin 10) ℤ) (p : ℕ) [Fact p.Prime]
    (a t : ℕ) : ℝ := by
  classical
  exact ∑ z : Fin 10 → ZMod (p^a),
    if eval₂ (Int.castRingHom (ZMod (p^a))) z F = 0 then
      (p : ℝ)^(((10*t : ℕ) : ℝ) - (penalty (actualProfile F p a z) t : ℝ)) else 0

theorem profileMass_eq_sum_profiles (F : MvPolynomial (Fin 10) ℤ)
    (p : ℕ) [Fact p.Prime] (a t : ℕ) :
    profileMass F p a t = ∑ c : Profile a,
      ((roots F p a (entry c)).card : ℝ) *
        (p : ℝ)^(((10*t : ℕ) : ℝ) - (penalty c t : ℝ)) :=
  sum_roots_eq_sum_profiles F p a
    (fun c => (p : ℝ)^(((10*t : ℕ) : ℝ) - (penalty c t : ℝ)))

/-- A displayed finite-profile estimate gives the corresponding actual mass.
The final endpoint below supplies this estimate internally. -/
theorem profileMass_le_of_profile_bound (F : MvPolynomial (Fin 10) ℤ)
    (p : ℕ) [Fact p.Prime] (a t : ℕ) (C η : ℝ) (hC : 0 ≤ C)
    (hc : ∀ c : Profile a, ((roots F p a (entry c)).card : ℝ) ≤
      C * (p : ℝ)^((delta (entry c 0) : ℝ) +
        (min (easyCost c) (transitionCost c) : ℝ) + η*(a : ℝ))) :
    profileMass F p a t ≤ C * (11 : ℝ)^a *
      (p : ℝ)^(((10*t : ℕ) : ℝ) + (phi a t : ℝ) + η*(a : ℝ)) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  rw [profileMass_eq_sum_profiles]
  calc
    _ ≤ ∑ c : Profile a,
        C * (p : ℝ)^(((10*t : ℕ) : ℝ) + (phi a t : ℝ) + η*(a : ℝ)) := by
      apply Finset.sum_le_sum
      intro c _
      calc
        _ ≤ (C * (p : ℝ)^((delta (entry c 0) : ℝ) +
            (min (easyCost c) (transitionCost c) : ℝ) + η*(a : ℝ))) *
            (p : ℝ)^(((10*t : ℕ) : ℝ) - (penalty c t : ℝ)) :=
          mul_le_mul_of_nonneg_right (hc c) (Real.rpow_nonneg hp0.le _)
        _ = C * (p : ℝ)^(((10*t : ℕ) : ℝ) + (score c t : ℝ) + η*(a : ℝ)) := by
          rw [mul_assoc, ← Real.rpow_add hp0]
          congr 2
          simp only [score, Rat.cast_sub, Rat.cast_add, Rat.cast_min]
          ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ hC
          apply Real.rpow_le_rpow_of_exponent_le hp1
          have h : (score c t : ℝ) ≤ (phi a t : ℝ) := by exact_mod_cast score_le_phi c t
          linarith
    _ = (Fintype.card (Profile a) : ℝ) *
        (C * (p : ℝ)^(((10*t : ℕ) : ℝ) + (phi a t : ℝ) + η*(a : ℝ))) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := by
      have hcard : (Fintype.card (Profile a) : ℝ) ≤ (11 : ℝ)^a := by
        exact_mod_cast card_profiles_le a
      calc
        _ ≤ (11 : ℝ)^a *
            (C * (p : ℝ)^(((10*t : ℕ) : ℝ) + (phi a t : ℝ) + η*(a : ℝ))) :=
          mul_le_mul_of_nonneg_right hcard
            (mul_nonneg hC (Real.rpow_nonneg hp0.le _))
        _ = _ := by ring

/-- One threshold precedes every prime, profile length and terminal exponent.
No unproved literature premise remains. -/
theorem exists_uniform_bound 
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, 3 ≤ P ∧ ∀ (p : ℕ) [Fact p.Prime], P ≤ p →
      ∀ a : ℕ, 1 ≤ a → ∀ t : ℕ,
        profileMass F p a t ≤
          (p : ℝ)^(((10*t : ℕ) : ℝ) + (phi a t : ℝ) + ε*(a : ℝ)) := by
  obtain ⟨P, C, hP, hC, hc⟩ :=
    SmithProfileMinimumBound.exists_uniform_bound  F hF hA (ε/2) (by positivity)
  let K : ℕ := ⌈C⌉₊
  have hK : C ≤ (K : ℝ) := Nat.le_ceil C
  have hK1 : 1 ≤ (K : ℝ) := hC.trans hK
  obtain ⟨Q, hQ, hQbound⟩ :=
    ProfileConstantAbsorption.exists_threshold (11*K) (ε/2) (by positivity)
  refine ⟨max 3 (max P Q), le_max_left _ _, ?_⟩
  intro p hp hpP a ha t
  have hpP' : P ≤ p := (le_max_left P Q).trans ((le_max_right 3 (max P Q)).trans hpP)
  have hpQ : Q ≤ p := (le_max_right P Q).trans ((le_max_right 3 (max P Q)).trans hpP)
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hcoef : C * (11 : ℝ)^a ≤ (p : ℝ)^((ε/2)*(a : ℝ)) := by
    calc
      _ ≤ (K : ℝ)^a * (11 : ℝ)^a :=
        mul_le_mul_of_nonneg_right (hK.trans (le_self_pow₀ hK1 (by omega))) (by positivity)
      _ = ((11*K : ℕ) : ℝ)^a := by rw [Nat.cast_mul, mul_pow]; ring
      _ ≤ _ := hQbound p hpQ a
  calc
    _ ≤ C * (11 : ℝ)^a *
        (p : ℝ)^(((10*t : ℕ) : ℝ) + (phi a t : ℝ) + (ε/2)*(a : ℝ)) :=
      profileMass_le_of_profile_bound F p a t C (ε/2) (zero_le_one.trans hC)
        (hc p hpP' a ha)
    _ ≤ (p : ℝ)^((ε/2)*(a : ℝ)) *
        (p : ℝ)^(((10*t : ℕ) : ℝ) + (phi a t : ℝ) + (ε/2)*(a : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hp0.le _)
    _ = _ := by rw [← Real.rpow_add hp0]; congr 1; ring

end CubicTenVariables.SmithProfileMassBound

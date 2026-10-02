import Mathlib.Tactic

/-!
# The literal ten-variable finite Smith-profile optimization

Profiles here are actual finite monotone sequences of integers in [0,10].
The score uses the manuscript's two competing costs and exact penalties.
The comparison i < 2a-t is in the integers, so t>2a never incurs a truncated
natural-subtraction error. These are numerical definitions and finite-rank
certificates only: no matrix Smith form or geometric profile count is input.
-/

noncomputable section
namespace CubicTenVariables.SmithProfileNumerics
open scoped BigOperators

/-- A finite monotone rank profile of length a. -/
def Profile (a : ℕ) := {c : Fin a → Fin 11 // Monotone c}
instance (a : ℕ) : Fintype (Profile a) := by
  classical
  unfold Profile
  infer_instance
instance (a : ℕ) : Inhabited (Profile a) := ⟨⟨fun _ => 0, monotone_const⟩⟩

/-- Entries outside the finite profile are zero; only indices below a enter the score. -/
def entry {a : ℕ} (c : Profile a) (i : ℕ) : ℕ :=
  if hi : i < a then (c.val ⟨i, hi⟩).val else 0

def delta (x : ℕ) : ℚ :=
  if x ≤ 1 then 0 else if x < 8 then min (2*(x : ℚ)-2) (min ((x : ℚ)+2) 8) else 9

def gamma (x : ℕ) : ℚ :=
  (if delta x ≤ 5 then 1 else 0) + (if x = 0 then 1 else 0)

def tau (j : ℕ) : ℚ :=
  if j = 0 then 0 else if j < 10 then min 9 ((j : ℚ)+2) else 10

/-- The exact upper envelope max_{x≤z≤10}(tau(2z)-z); equality is proved below. -/
def eta (x : ℕ) : ℚ := if x ≤ 5 then 5 else 10-(x : ℚ)

/-- The manuscript's penalty, with the threshold formed in Z. -/
def penaltyWeight (a t i : ℕ) : ℚ :=
  if t ≤ a then (if i < t then 1/2 else 0)
  else if (i : ℤ) < 2*(a : ℤ)-(t : ℤ) then 1/2 else 1

def easyCost {a : ℕ} (c : Profile a) : ℚ :=
  9*(a-1 : ℕ) + if 2 ≤ a then gamma (entry c 0) else 0

def transitionCost {a : ℕ} (c : Profile a) : ℚ :=
  ∑ i ∈ Finset.range (a-1), tau (entry c i + entry c (i+1))

def penalty {a : ℕ} (c : Profile a) (t : ℕ) : ℚ :=
  ∑ i ∈ Finset.range a, penaltyWeight a t i * (entry c i : ℚ)

def score {a : ℕ} (c : Profile a) (t : ℕ) : ℚ :=
  delta (entry c 0) + min (easyCost c) (transitionCost c) - penalty c t

/-- An actual maximum over all finite monotone profiles. -/
def phi (a t : ℕ) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty (fun c : Profile a => score c t)

def localD (a t : ℕ) : ℚ := 12*a + 11*t + phi a t

@[simp] theorem entry_lt_eleven {a : ℕ} (c : Profile a) (i : ℕ) : entry c i < 11 := by
  unfold entry
  split_ifs with hi
  · exact (c.val ⟨i, hi⟩).isLt
  · omega

theorem entry_mono {a : ℕ} (c : Profile a) {i j : ℕ} (hij : i ≤ j) (hj : j < a) :
    entry c i ≤ entry c j := by
  have hi : i < a := hij.trans_lt hj
  simpa only [entry, dif_pos hi, dif_pos hj] using c.property (show (⟨i,hi⟩ : Fin a) ≤ ⟨j,hj⟩ from hij)

theorem gamma_nonneg (x : ℕ) : 0 ≤ gamma x := by unfold gamma; split_ifs <;> norm_num

theorem eta_le_five (x : ℕ) : eta x ≤ 5 := by
  unfold eta
  split_ifs with hx
  · norm_num
  · have hxQ : (5 : ℚ) < x := by exact_mod_cast (by omega : 5 < x)
    linarith

theorem certificate_one (x : ℕ) (hx : x ≤ 10) :
    delta x - (x : ℚ)/2 + gamma x/2 ≤ 5 := by
  interval_cases x <;> norm_num [delta, gamma]

theorem certificate_two (x : ℕ) (hx : x ≤ 10) :
    delta x - (x : ℚ) + gamma x/2 ≤ 2 := by
  interval_cases x <;> norm_num [delta, gamma]

theorem certificate_three (x : ℕ) (hx : x ≤ 10) :
    delta x - (x : ℚ)/2 + gamma x/2 + eta x/2 ≤ 7 := by
  interval_cases x <;> norm_num [delta, gamma, eta]

theorem certificate_four (x : ℕ) (hx : x ≤ 10) :
    delta x - (x : ℚ)/2 + gamma x ≤ 5 := by
  interval_cases x <;> norm_num [delta, gamma]

theorem tau_le_ten (j : ℕ) : tau j ≤ 10 := by
  unfold tau
  split_ifs
  · norm_num
  · exact (min_le_left _ _).trans (by norm_num)
  · rfl

theorem tau_mono : Monotone tau := by
  intro i j hij
  by_cases hi : i = 0
  · rw [hi]
    have hj : 0 ≤ tau j := by unfold tau; split_ifs <;> positivity
    simpa [tau] using hj
  by_cases hj : j = 0
  · omega
  by_cases hi10 : i < 10
  · by_cases hj10 : j < 10
    · simp only [tau, if_neg hi, if_neg hj, if_pos hi10, if_pos hj10]
      exact min_le_min_left _ (by exact_mod_cast Nat.add_le_add_right hij 2)
    · simp only [tau, if_neg hi, if_neg hj, if_pos hi10, if_neg hj10]
      exact (min_le_left _ _).trans (by norm_num)
  · have hj10 : ¬j < 10 := by omega
    simp [tau, hi, hj, hi10, hj10]

theorem eta_envelope (x z : ℕ) (hxz : x ≤ z) (hz : z ≤ 10) :
    tau (2*z) - (z : ℚ) ≤ eta x := by
  have hx : x ≤ 10 := hxz.trans hz
  interval_cases x <;> interval_cases z <;> norm_num [tau, eta] at *

/-- The displayed eta formula is attained, so it is the exact finite envelope. -/
theorem eta_attained (x : ℕ) (hx : x ≤ 10) :
    ∃ z : ℕ, x ≤ z ∧ z ≤ 10 ∧ tau (2*z) - (z : ℚ) = eta x := by
  refine ⟨max x 5, le_max_left _ _, max_le hx (by omega), ?_⟩
  interval_cases x <;> norm_num [tau, eta]

theorem transition_envelope (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) (hz : z ≤ 10) :
    tau (y+z) ≤ eta x + z := by
  have he := eta_envelope x z (hxy.trans hyz) hz
  have ht := tau_mono (show y+z ≤ 2*z by omega)
  linarith

theorem phi_le (a t : ℕ) (b : ℚ) (h : ∀ c : Profile a, score c t ≤ b) : phi a t ≤ b := by
  exact Finset.sup'_le Finset.univ_nonempty _ (fun c _ => h c)

theorem score_le_phi {a : ℕ} (c : Profile a) (t : ℕ) : score c t ≤ phi a t := by
  exact Finset.le_sup' (fun c : Profile a => score c t) (Finset.mem_univ c)

theorem phi_attained (a t : ℕ) : ∃ c : Profile a, phi a t = score c t := by
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Profile a)))
    Finset.univ_nonempty (fun c => score c t)
  exact ⟨c, hc⟩

end CubicTenVariables.SmithProfileNumerics

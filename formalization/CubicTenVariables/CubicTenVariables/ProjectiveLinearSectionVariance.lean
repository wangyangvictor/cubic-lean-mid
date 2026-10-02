import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.Projectivization.Independence
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic

/-! # Exact incidence counts for projective linear sections

All points are actual projectivizations of finite-field vector spaces, and
all parameters are literal tuples of linear equations. No smoothness,
cohomology, or literature input occurs. These counts underlie the
Hooley--Katz slicing argument (Matera--Perez--Privitelli, Lemma 4.2).
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace CubicTenVariables.ProjectiveLinearSectionVariance

variable {K : Type*} [Field K] [Fintype K] {n k : ℕ}

omit [Fintype K] in
theorem card_matrix_kernel {m : ℕ} (A : Matrix (Fin m) (Fin n) K) :
    Nat.card {v : Fin n → K // A.mulVec v = 0} =
      Nat.card K ^ (n - A.rank) := by
  change Nat.card (LinearMap.ker A.mulVecLin) = _
  rw [Module.natCard_eq_pow_finrank (K := K)]
  congr 1
  have h := A.mulVecLin.finrank_range_add_finrank_ker
  have h' : A.rank + Module.finrank K (LinearMap.ker A.mulVecLin) = n := by
    simpa only [Matrix.rank, Module.finrank_pi, Fintype.card_fin] using h
  omega

/-- Exactly q^(n-1) linear equations vanish at a projective point. -/
theorem card_normals_through_point (p : Projectivization K (Fin n → K)) :
    Nat.card {v : Fin n → K // dotProduct v p.rep = 0} = Nat.card K ^ (n - 1) := by
  let A : Matrix (Fin 1) (Fin n) K := fun _ => p.rep
  have hind : LinearIndependent K A.row :=
    linearIndependent_unique_iff.mpr p.rep_nonzero
  have hrank : A.rank = 1 := by simpa using hind.rank_matrix
  have hker (v : Fin n → K) : A.mulVec v = 0 ↔ dotProduct v p.rep = 0 := by
    simp [funext_iff, A, Matrix.mulVec, dotProduct_comm]
  simpa only [hker, hrank] using card_matrix_kernel A

/-- Distinct projective points impose two independent linear equations. -/
theorem card_normals_through_pair (p q : Projectivization K (Fin n → K))
    (hpq : p ≠ q) :
    Nat.card {v : Fin n → K // dotProduct v p.rep = 0 ∧ dotProduct v q.rep = 0} =
      Nat.card K ^ (n - 2) := by
  let A : Matrix (Fin 2) (Fin n) K := ![p.rep, q.rep]
  have hind : LinearIndependent K A.row := by
    have h := Projectivization.independent_iff.mp
      ((Projectivization.independent_pair_iff_ne p q).mpr hpq)
    convert h using 1
    ext i
    fin_cases i <;> rfl
  have hrank : A.rank = 2 := by simpa using hind.rank_matrix
  have hker (v : Fin n → K) : A.mulVec v = 0 ↔
      dotProduct v p.rep = 0 ∧ dotProduct v q.rep = 0 := by
    simp [funext_iff, A, Matrix.mulVec, Fin.forall_fin_two, dotProduct_comm]
  simpa only [hker, hrank] using card_matrix_kernel A

/-- A point lies on all the equations of the chosen linear section. -/
def incident (γ : Fin k → Fin n → K) (p : Projectivization K (Fin n → K)) : Prop :=
  ∀ j, dotProduct (γ j) p.rep = 0

theorem card_sections_through_point (p : Projectivization K (Fin n → K)) :
    Nat.card {γ : Fin k → Fin n → K // incident γ p} =
      Nat.card K ^ ((n - 1) * k) := by
  rw [show {γ : Fin k → Fin n → K // incident γ p} =
    {γ : Fin k → Fin n → K // ∀ j, dotProduct (γ j) p.rep = 0} from rfl]
  let e : {γ : Fin k → Fin n → K // ∀ j, dotProduct (γ j) p.rep = 0} ≃
      (Fin k → {v : Fin n → K // dotProduct v p.rep = 0}) :=
    Equiv.subtypePiEquivPi (β := fun _ : Fin k => Fin n → K)
      (p := fun _ v => dotProduct v p.rep = 0)
  rw [Nat.card_congr e, Nat.card_fun,
    Nat.card_fin, card_normals_through_point, ← pow_mul]

theorem card_sections_through_pair (p q : Projectivization K (Fin n → K))
    (hpq : p ≠ q) :
    Nat.card {γ : Fin k → Fin n → K // incident γ p ∧ incident γ q} =
      Nat.card K ^ ((n - 2) * k) := by
  have hpred : (fun γ : Fin k → Fin n → K => incident γ p ∧ incident γ q) =
      (fun γ => ∀ j, dotProduct (γ j) p.rep = 0 ∧ dotProduct (γ j) q.rep = 0) := by
    funext γ
    simp [incident, forall_and]
  let e : {γ : Fin k → Fin n → K // ∀ j,
      dotProduct (γ j) p.rep = 0 ∧ dotProduct (γ j) q.rep = 0} ≃
      (Fin k → {v : Fin n → K // dotProduct v p.rep = 0 ∧
        dotProduct v q.rep = 0}) :=
    Equiv.subtypePiEquivPi (β := fun _ : Fin k => Fin n → K)
      (p := fun _ v => dotProduct v p.rep = 0 ∧ dotProduct v q.rep = 0)
  rw [hpred, Nat.card_congr e, Nat.card_fun,
    Nat.card_fin, card_normals_through_pair p q hpq, ← pow_mul]

/-- Number of points of a finite projective set on a literal linear section. -/
def sectionCount (S : Finset (Projectivization K (Fin n → K)))
    (γ : Fin k → Fin n → K) : ℕ :=
  (S.filter (incident γ)).card

omit [Fintype K] in
theorem sectionCount_eq_sum (S : Finset (Projectivization K (Fin n → K)))
    (γ : Fin k → Fin n → K) :
    (sectionCount S γ : ℝ) = ∑ p ∈ S, if incident γ p then 1 else 0 := by
  simp [sectionCount, Finset.sum_boole]

theorem first_moment (S : Finset (Projectivization K (Fin n → K))) :
    (∑ γ : Fin k → Fin n → K, (sectionCount S γ : ℝ)) =
      (S.card : ℝ) * (Nat.card K : ℝ) ^ ((n - 1) * k) := by
  simp_rw [sectionCount_eq_sum]
  rw [Finset.sum_comm]
  have h (p : Projectivization K (Fin n → K)) :
      (∑ γ : Fin k → Fin n → K, if incident γ p then (1 : ℝ) else 0) =
        (Nat.card K : ℝ) ^ ((n - 1) * k) := by
    have hc := card_sections_through_point (k := k) p
    exact_mod_cast (by simpa [Nat.card_eq_fintype_card, Fintype.card_subtype,
      Finset.sum_boole] using hc)
  simp_rw [h]
  simp

/-- The exact second moment counts equal and distinct pairs of points separately. -/
theorem second_moment (S : Finset (Projectivization K (Fin n → K))) :
    (∑ γ : Fin k → Fin n → K, (sectionCount S γ : ℝ) ^ 2) =
      (S.card : ℝ) * (Nat.card K : ℝ) ^ ((n - 1) * k) +
        (S.card : ℝ) * ((S.card : ℝ) - 1) * (Nat.card K : ℝ) ^ ((n - 2) * k) := by
  have hpair (p q : Projectivization K (Fin n → K)) :
      (∑ γ : Fin k → Fin n → K,
        if incident γ p ∧ incident γ q then (1 : ℝ) else 0) =
      if p = q then (Nat.card K : ℝ) ^ ((n - 1) * k)
        else (Nat.card K : ℝ) ^ ((n - 2) * k) := by
    split_ifs with hpq
    · subst q
      have hc := card_sections_through_point (k := k) p
      exact_mod_cast (by simpa [Nat.card_eq_fintype_card, Fintype.card_subtype,
        Finset.sum_boole] using hc)
    · have hc := card_sections_through_pair (k := k) p q hpq
      exact_mod_cast (by simpa [Nat.card_eq_fintype_card, Fintype.card_subtype,
        Finset.sum_boole] using hc)
  have hexpand (γ : Fin k → Fin n → K) :
      (sectionCount S γ : ℝ) ^ 2 =
        ∑ p ∈ S, ∑ q ∈ S, if incident γ p ∧ incident γ q then (1 : ℝ) else 0 := by
    rw [sectionCount_eq_sum, pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    split_ifs <;> simp_all
  simp_rw [hexpand]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext p
    rw [Finset.sum_comm]
  simp_rw [hpair]
  have hinner (p : Projectivization K (Fin n → K)) (hp : p ∈ S) :
      (∑ q ∈ S, if p = q then (Nat.card K : ℝ) ^ ((n - 1) * k)
        else (Nat.card K : ℝ) ^ ((n - 2) * k)) =
      (Nat.card K : ℝ) ^ ((n - 1) * k) +
        ((S.card : ℝ) - 1) * (Nat.card K : ℝ) ^ ((n - 2) * k) := by
    have heq (q : Projectivization K (Fin n → K)) :
        (if p = q then (Nat.card K : ℝ) ^ ((n - 1) * k)
          else (Nat.card K : ℝ) ^ ((n - 2) * k)) =
        (Nat.card K : ℝ) ^ ((n - 2) * k) +
          if p = q then (Nat.card K : ℝ) ^ ((n - 1) * k) -
            (Nat.card K : ℝ) ^ ((n - 2) * k) else 0 := by
      split_ifs <;> ring
    simp_rw [heq]
    rw [Finset.sum_add_distrib]
    simp [hp]
    ring
  rw [Finset.sum_congr rfl (fun p hp => hinner p hp)]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

/-- Exact variance over all tuples of linear equations, including dependent tuples.
This is a finite-set identity; the set of points need not be algebraic. -/
theorem variance (hn : 2 ≤ n) (S : Finset (Projectivization K (Fin n → K))) :
    (∑ γ : Fin k → Fin n → K,
      ((S.card : ℝ) - (Nat.card K : ℝ) ^ k * (sectionCount S γ : ℝ)) ^ 2) =
      (S.card : ℝ) * (Nat.card K : ℝ) ^ (n * k) * ((Nat.card K : ℝ) ^ k - 1) := by
  let N : ℝ := S.card
  let t : ℝ := (Nat.card K : ℝ) ^ k
  let A : ℝ := (Nat.card K : ℝ) ^ ((n - 1) * k)
  let B : ℝ := (Nat.card K : ℝ) ^ ((n - 2) * k)
  let Q : ℝ := (Nat.card K : ℝ) ^ (n * k)
  have hA : t * A = Q := by
    dsimp [t, A, Q]
    rw [← pow_add]
    congr 1
    calc
      k + (n - 1) * k = (1 + (n - 1)) * k := by ring
      _ = n * k := by congr 1; omega
  have hB : t ^ 2 * B = Q := by
    dsimp [t, B, Q]
    rw [← pow_mul, ← pow_add]
    congr 1
    calc
      k * 2 + (n - 2) * k = (2 + (n - 2)) * k := by ring
      _ = n * k := by congr 1; omega
  have hcard : (Fintype.card (Fin k → Fin n → K) : ℝ) = Q := by
    simp [Q, Nat.card_eq_fintype_card, pow_mul]
  have hexpand (γ : Fin k → Fin n → K) :
      (N - t * (sectionCount S γ : ℝ)) ^ 2 = N ^ 2 -
        (2 * N * t) * (sectionCount S γ : ℝ) +
        t ^ 2 * (sectionCount S γ : ℝ) ^ 2 := by ring
  change (∑ γ : Fin k → Fin n → K,
    (N - t * (sectionCount S γ : ℝ)) ^ 2) = N * Q * (t - 1)
  simp_rw [hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  rw [hcard, first_moment, second_moment]
  change Q * N ^ 2 - (2 * N * t) * (N * A) +
    t ^ 2 * (N * A + N * (N - 1) * B) = _
  calc
    _ = N ^ 2 * Q - 2 * N ^ 2 * (t * A) +
        N * t * (t * A) + N * (N - 1) * (t ^ 2 * B) := by ring
    _ = N * Q * (t - 1) := by rw [hA, hB]; ring

/-- Any set containing more than half the section parameters contains a section
with at most twice the average squared deviation. For the slicing application,
the separate geometric step will supply the finite set of smooth sections. -/
theorem exists_good_section_of_card (hn : 2 ≤ n)
    (S : Finset (Projectivization K (Fin n → K)))
    (G : Finset (Fin k → Fin n → K))
    (hG : Fintype.card (Fin k → Fin n → K) < 2 * G.card) :
    ∃ γ ∈ G, ((S.card : ℝ) - (Nat.card K : ℝ) ^ k *
      (sectionCount S γ : ℝ)) ^ 2 ≤
        2 * (S.card : ℝ) * ((Nat.card K : ℝ) ^ k - 1) := by
  let b : ℝ := (S.card : ℝ) * ((Nat.card K : ℝ) ^ k - 1)
  let f (γ : Fin k → Fin n → K) : ℝ :=
    ((S.card : ℝ) - (Nat.card K : ℝ) ^ k * (sectionCount S γ : ℝ)) ^ 2
  have hq : (1 : ℝ) ≤ Nat.card K := by
    have hq' : 1 ≤ Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_pos
    exact_mod_cast hq'
  have hb : 0 ≤ b := mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (one_le_pow₀ hq))
  have hcard : (Fintype.card (Fin k → Fin n → K) : ℝ) =
      (Nat.card K : ℝ) ^ (n * k) := by
    simp [Nat.card_eq_fintype_card, pow_mul]
  have hsum : (∑ γ, f γ) = (Fintype.card (Fin k → Fin n → K) : ℝ) * b := by
    dsimp [f, b]
    rw [variance hn S, hcard]
    ring
  have hnonempty : G.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    subst G
    simp at hG
  have hG' : (Fintype.card (Fin k → Fin n → K) : ℝ) ≤ (G.card : ℝ) * 2 := by
    have hG'' : (Fintype.card (Fin k → Fin n → K) : ℝ) < 2 * (G.card : ℝ) := by
      exact_mod_cast hG
    nlinarith
  have hle : (∑ γ ∈ G, f γ) ≤ ∑ γ, f γ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ G)
      (fun γ _ _ => sq_nonneg _)
  by_contra! hbad
  have hbad' (γ) (hγ : γ ∈ G) : 2 * b < f γ := by
    simpa only [b, f, mul_assoc] using hbad γ hγ
  obtain ⟨γ₀, hγ₀⟩ := hnonempty
  have hstrict : (∑ γ ∈ G, 2 * b) < ∑ γ ∈ G, f γ :=
    Finset.sum_lt_sum (fun γ hγ => (hbad' γ hγ).le) ⟨γ₀, hγ₀, hbad' γ₀ hγ₀⟩
  simp only [Finset.sum_const, nsmul_eq_mul] at hstrict
  have hmean := mul_le_mul_of_nonneg_right hG' hb
  rw [hsum] at hle
  nlinarith

end CubicTenVariables.ProjectiveLinearSectionVariance

import CubicTenVariables.SquarefullModulusDecomposition

/-! Cube-free moduli use the existing canonical square and odd-prime parts.
No new choice of prime factors or decomposition parameters is introduced. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CubeFreeModulusDecomposition
open SquarefullModulusDecomposition

/-- A positive integer whose prime exponents are at most two. -/
def CubeFree (q : ℕ) : Prop := q ≠ 0 ∧ ∀ p : ℕ, q.factorization p ≤ 2

/-- The factorization definition is exactly the absence of a prime cube
divisor. This condition itself excludes zero and includes one. -/
theorem cubeFree_iff_prime_cube_not_dvd (q : ℕ) :
    CubeFree q ↔ ∀ p : ℕ, p.Prime → ¬ p^3 ∣ q := by
  constructor
  · intro hq p hp hd
    have hh := (hp.pow_dvd_iff_le_factorization hq.1).mp hd
    have he := hq.2 p
    omega
  · intro hq
    have hq0 : q ≠ 0 := by
      intro hz
      subst q
      exact hq 2 Nat.prime_two (dvd_zero _)
    refine ⟨hq0,?_⟩
    intro p
    by_cases hp : p.Prime
    · have hh : ¬ 3 ≤ q.factorization p := by
        intro he
        exact hq p hp ((hp.pow_dvd_iff_le_factorization hq0).mpr he)
      omega
    · rw [Nat.factorization_eq_zero_of_not_prime q hp]
      omega

@[simp] theorem cubeFree_one : CubeFree 1 := by simp [CubeFree]

/-- The square-root of the square part is itself squarefree for cube-free q. -/
theorem c_squarefree (q : ℕ) (hq : CubeFree q) : Squarefree (c q) := by
  apply (Nat.squarefree_iff_factorization_le_one (c_pos q).ne').mpr
  intro p
  rw [factorization_c]
  have he := hq.2 p
  omega

/-- For exponents zero, one, and two the odd-prime and square-root parts
have disjoint prime support. -/
theorem coprime_d_c (q : ℕ) (hq : CubeFree q) : (d q).Coprime (c q) := by
  apply Nat.coprime_of_dvd
  intro p hp hpd hpc
  have hd := (hp.dvd_iff_one_le_factorization (d_pos q).ne').mp hpd
  have hc := (hp.dvd_iff_one_le_factorization (c_pos q).ne').mp hpc
  rw [factorization_d] at hd
  rw [factorization_c] at hc
  have he := hq.2 p
  omega

/-- The manuscript's squarefree-times-square convention uses precisely the
previously defined d and c, in that order. -/
theorem eq_d_mul_c_sq (q : ℕ) (hq : CubeFree q) : q = d q*(c q)^2 := by
  exact (eq_c_sq_mul_d q (Nat.pos_of_ne_zero hq.1)).trans (Nat.mul_comm _ _)

theorem decomposition (q : ℕ) (hq : CubeFree q) :
    0 < d q ∧ 0 < c q ∧ Squarefree (d q) ∧ Squarefree (c q) ∧
      (d q).Coprime (c q) ∧ q = d q*(c q)^2 :=
  ⟨d_pos q,c_pos q,d_squarefree q,c_squarefree q hq,coprime_d_c q hq,
    eq_d_mul_c_sq q hq⟩

/-- The reversed parameter pair remains injective on all positive moduli;
no cube-free hypothesis is needed for this reconstruction fact. -/
theorem parameters_injOn : Set.InjOn (fun q => (d q,c q)) {q : ℕ | 0 < q} := by
  intro q hq r hr he
  apply eq_of_parameters_eq q r hq hr
  obtain ⟨hd,hc⟩ := Prod.mk.inj he
  exact Prod.ext hc hd

theorem parameters_injective :
    Function.Injective (fun q : {q : ℕ // 0 < q} => (d q.val,c q.val)) := by
  intro q r he
  exact Subtype.ext (parameters_injOn q.property r.property he)

end CubicTenVariables.CubeFreeModulusDecomposition

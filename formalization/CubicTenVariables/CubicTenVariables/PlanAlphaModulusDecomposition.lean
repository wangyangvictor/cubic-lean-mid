import CubicTenVariables.CubeFreeModulusDecomposition

/-! Canonical decomposition of an actual positive modulus into its part
supported on the excluded primes, its remaining cube-free part, and its
remaining cube-full part. Only finite prime-power products are used. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PlanAlphaModulusDecomposition
open CubeFreeModulusDecomposition (CubeFree)
open CubeFullSmithParameters (CubeFull factorization_prime_power_prod)
open scoped BigOperators Classical

/-- Complete prime-power factors supported on the fixed excluded set. -/
def g (s : Finset ℕ) (q : ℕ) : ℕ :=
  ∏ p ∈ q.primeFactors.filter (fun p => p ∈ s), p^(q.factorization p)

/-- Complete prime-power factors of exponent one or two outside the set. -/
def d (s : Finset ℕ) (q : ℕ) : ℕ :=
  ∏ p ∈ q.primeFactors.filter (fun p => p ∉ s ∧ q.factorization p ≤ 2), p^(q.factorization p)

/-- Complete prime-power factors of exponent at least three outside the set. -/
def r (s : Finset ℕ) (q : ℕ) : ℕ :=
  ∏ p ∈ q.primeFactors.filter (fun p => p ∉ s ∧ 3 ≤ q.factorization p), p^(q.factorization p)

/-- The excluded factor is also the product over the whole fixed set;
primes absent from the original modulus contribute exponent zero. -/
theorem g_eq_prod_s (s : Finset ℕ) (q : ℕ) :
    g s q = ∏ p ∈ s, p^(q.factorization p) := by
  unfold g
  apply Finset.prod_subset
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · intro p hp hnot
    have hn : p ∉ q.primeFactors := by
      intro hq
      exact hnot (Finset.mem_filter.mpr ⟨hq,hp⟩)
    rw [Finsupp.notMem_support_iff.mp hn,pow_zero]

theorem g_pos (s : Finset ℕ) (q : ℕ) : 0 < g s q :=
  Finset.prod_pos (fun _p hp => pow_pos
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos _)

theorem d_pos (s : Finset ℕ) (q : ℕ) : 0 < d s q :=
  Finset.prod_pos (fun _p hp => pow_pos
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos _)

theorem r_pos (s : Finset ℕ) (q : ℕ) : 0 < r s q :=
  Finset.prod_pos (fun _p hp => pow_pos
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos _)

theorem factorization_g (s : Finset ℕ) (q p : ℕ) :
    (g s q).factorization p = if p ∈ s then q.factorization p else 0 := by
  rw [g,factorization_prime_power_prod _
    (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)]
  by_cases hp : p ∈ q.primeFactors
  · simp [hp]
  · have hz : q.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    simp [hp,hz]

theorem factorization_d (s : Finset ℕ) (q p : ℕ) :
    (d s q).factorization p = if p ∉ s ∧ q.factorization p ≤ 2 then q.factorization p else 0 := by
  rw [d,factorization_prime_power_prod _
    (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)]
  by_cases hp : p ∈ q.primeFactors
  · simp [hp]
  · have hz : q.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    simp [hp,hz]

theorem factorization_r (s : Finset ℕ) (q p : ℕ) :
    (r s q).factorization p = if p ∉ s ∧ 3 ≤ q.factorization p then q.factorization p else 0 := by
  rw [r,factorization_prime_power_prod _
    (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)]
  by_cases hp : p ∈ q.primeFactors
  · simp [hp]
  · have hz : q.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    simp [hp,hz]

theorem primeFactors_g (s : Finset ℕ) (q : ℕ) :
    (g s q).primeFactors = q.primeFactors.filter (fun p => p ∈ s) := by
  ext p
  rw [← Nat.support_factorization,Finsupp.mem_support_iff,Finset.mem_filter,
    ← Nat.support_factorization,Finsupp.mem_support_iff,factorization_g]
  by_cases hp : p ∈ s <;> simp [hp]

theorem primeFactors_d (s : Finset ℕ) (q : ℕ) :
    (d s q).primeFactors = q.primeFactors.filter (fun p => p ∉ s ∧ q.factorization p ≤ 2) := by
  ext p
  rw [← Nat.support_factorization,Finsupp.mem_support_iff,Finset.mem_filter,
    ← Nat.support_factorization,Finsupp.mem_support_iff,factorization_d]
  by_cases hp : p ∉ s ∧ q.factorization p ≤ 2 <;> simp [hp]

theorem primeFactors_r (s : Finset ℕ) (q : ℕ) :
    (r s q).primeFactors = q.primeFactors.filter (fun p => p ∉ s ∧ 3 ≤ q.factorization p) := by
  ext p
  rw [← Nat.support_factorization,Finsupp.mem_support_iff,Finset.mem_filter,
    ← Nat.support_factorization,Finsupp.mem_support_iff,factorization_r]
  by_cases hp : p ∉ s ∧ 3 ≤ q.factorization p <;> simp [hp]

/-- Each prime contributes its entire original exponent to exactly one factor. -/
theorem reconstruction (s : Finset ℕ) (q : ℕ) (hq : 0 < q) : q = g s q*d s q*r s q := by
  have hg := g_pos s q
  have hd := d_pos s q
  have hr := r_pos s q
  apply Nat.eq_of_factorization_eq hq.ne' (by positivity)
  intro p
  rw [Nat.factorization_mul (by positivity) hr.ne',Finsupp.add_apply,
    Nat.factorization_mul hg.ne' hd.ne',Finsupp.add_apply,
    factorization_g,factorization_d,factorization_r]
  by_cases hp : p ∈ s
  · simp [hp]
  · by_cases he : q.factorization p ≤ 2
    · have hn : ¬ 3 ≤ q.factorization p := by omega
      simp [hp,he,hn]
    · have he' : 3 ≤ q.factorization p := by omega
      simp [hp,he,he']

theorem coprime_g_d (s : Finset ℕ) (q : ℕ) : (g s q).Coprime (d s q) := by
  apply (Nat.disjoint_primeFactors (g_pos s q).ne' (d_pos s q).ne').mp
  rw [primeFactors_g,primeFactors_d]
  apply Finset.disjoint_left.mpr
  intro p hg hd
  exact (Finset.mem_filter.mp hd).2.1 (Finset.mem_filter.mp hg).2

theorem coprime_g_r (s : Finset ℕ) (q : ℕ) : (g s q).Coprime (r s q) := by
  apply (Nat.disjoint_primeFactors (g_pos s q).ne' (r_pos s q).ne').mp
  rw [primeFactors_g,primeFactors_r]
  apply Finset.disjoint_left.mpr
  intro p hg hr
  exact (Finset.mem_filter.mp hr).2.1 (Finset.mem_filter.mp hg).2

theorem coprime_d_r (s : Finset ℕ) (q : ℕ) : (d s q).Coprime (r s q) := by
  apply (Nat.disjoint_primeFactors (d_pos s q).ne' (r_pos s q).ne').mp
  rw [primeFactors_d,primeFactors_r]
  apply Finset.disjoint_left.mpr
  intro p hd hr
  have h₂ := (Finset.mem_filter.mp hd).2.2
  have h₃ := (Finset.mem_filter.mp hr).2.2
  omega

theorem g_supported (s : Finset ℕ) (q : ℕ) : (g s q).primeFactors ⊆ s := by
  rw [primeFactors_g]
  exact fun p hp => (Finset.mem_filter.mp hp).2

theorem d_disjoint (s : Finset ℕ) (q : ℕ) : Disjoint (d s q).primeFactors s := by
  rw [primeFactors_d]
  exact Finset.disjoint_left.mpr (fun p hp hs => (Finset.mem_filter.mp hp).2.1 hs)

theorem r_disjoint (s : Finset ℕ) (q : ℕ) : Disjoint (r s q).primeFactors s := by
  rw [primeFactors_r]
  exact Finset.disjoint_left.mpr (fun p hp hs => (Finset.mem_filter.mp hp).2.1 hs)

theorem d_cubeFree (s : Finset ℕ) (q : ℕ) : CubeFree (d s q) := by
  refine ⟨(d_pos s q).ne',?_⟩
  intro p
  rw [factorization_d]
  split_ifs with hp
  · exact hp.2
  · omega

theorem r_cubeFull (s : Finset ℕ) (q : ℕ) : CubeFull (r s q) := by
  intro p hp
  rw [primeFactors_r] at hp
  have hh := (Finset.mem_filter.mp hp).2
  rw [factorization_r,if_pos hh]
  exact hh.2

theorem g_dvd (s : Finset ℕ) (q : ℕ) (hq : 0 < q) : g s q ∣ q := by
  refine ⟨d s q*r s q,?_⟩
  simpa only [Nat.mul_assoc] using reconstruction s q hq

theorem d_dvd (s : Finset ℕ) (q : ℕ) (hq : 0 < q) : d s q ∣ q := by
  refine ⟨g s q*r s q,?_⟩
  calc
    q = g s q*d s q*r s q := reconstruction s q hq
    _ = _ := by ring

theorem r_dvd (s : Finset ℕ) (q : ℕ) (hq : 0 < q) : r s q ∣ q := by
  refine ⟨g s q*d s q,?_⟩
  calc
    q = g s q*d s q*r s q := reconstruction s q hq
    _ = _ := by ring

theorem g_le (s : Finset ℕ) (q : ℕ) (hq : 0 < q) : g s q ≤ q := Nat.le_of_dvd hq (g_dvd s q hq)
theorem d_le (s : Finset ℕ) (q : ℕ) (hq : 0 < q) : d s q ≤ q := Nat.le_of_dvd hq (d_dvd s q hq)
theorem r_le (s : Finset ℕ) (q : ℕ) (hq : 0 < q) : r s q ≤ q := Nat.le_of_dvd hq (r_dvd s q hq)

/-- All arithmetic properties needed to split a positive original modulus
into the three factors of the mixed-modulus argument. -/
theorem decomposition (s : Finset ℕ) (q : ℕ) (hq : 0 < q) :
    0 < g s q ∧ 0 < d s q ∧ 0 < r s q ∧ q = g s q*d s q*r s q ∧
    (g s q).Coprime (d s q) ∧ (g s q).Coprime (r s q) ∧ (d s q).Coprime (r s q) ∧
    (g s q).primeFactors ⊆ s ∧ CubeFree (d s q) ∧ CubeFull (r s q) ∧
    Disjoint (d s q).primeFactors s ∧ Disjoint (r s q).primeFactors s ∧
    g s q ≤ q ∧ d s q ≤ q ∧ r s q ≤ q :=
  ⟨g_pos s q,d_pos s q,r_pos s q,reconstruction s q hq,
    coprime_g_d s q,coprime_g_r s q,coprime_d_r s q,g_supported s q,
    d_cubeFree s q,r_cubeFull s q,d_disjoint s q,r_disjoint s q,
    g_le s q hq,d_le s q hq,r_le s q hq⟩

/-- Reindexing by the canonical triple counts each positive modulus once. -/
theorem parameters_injOn (s : Finset ℕ) :
    Set.InjOn (fun q => (g s q,d s q,r s q)) {q : ℕ | 0 < q} := by
  intro q hq z hz he
  have hg : g s q = g s z := congrArg Prod.fst he
  have hd : d s q = d s z := congrArg (fun x => x.2.1) he
  have hr : r s q = r s z := congrArg (fun x => x.2.2) he
  rw [reconstruction s q hq,reconstruction s z hz,hg,hd,hr]

end CubicTenVariables.PlanAlphaModulusDecomposition

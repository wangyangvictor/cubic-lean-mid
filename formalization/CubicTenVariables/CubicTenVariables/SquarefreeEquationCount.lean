import CubicTenVariables.IntegralModelDimension
import CubicTenVariables.SquarefreePolynomialRoots
import CubicTenVariables.PrimeFactorEpsilonBound

/-! Exact Chinese remainder decomposition and squarefree counts for the
actual reductions of fixed integral equations. The final bounds supply
their prime estimates internally, including every exceptional prime. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.SquarefreeEquationCount
open MvPolynomial IntegralEquationCounts CRTCharacters HessianTheorem11
open scoped BigOperators

variable {σ ι : Type*}

theorem map_eval₂_int {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : MvPolynomial σ ℤ) (x : σ → R) :
    φ (eval₂ (Int.castRingHom R) x f) =
      eval₂ (Int.castRingHom S) (fun i => φ (x i)) f := by
  have hc : φ.comp (Int.castRingHom R) = Int.castRingHom S := by
    ext z
    simp
  simpa only [hc, Function.comp_def] using
    eval₂_comp_left φ (Int.castRingHom R) x f

/-- Coordinatewise CRT for arbitrary variable types. -/
def vectorEquiv {a b : ℕ} (hab : a.Coprime b) :
    (σ → ZMod (a*b)) ≃ ((σ → ZMod a) × (σ → ZMod b)) :=
  (Equiv.piCongrRight fun _ => (ZMod.chineseRemainder hab).toEquiv).trans
    (Equiv.arrowProdEquivProdArrow σ (fun _ => ZMod a) (fun _ => ZMod b))

theorem polynomial_zero_crt_iff (f : MvPolynomial σ ℤ)
    {a b : ℕ} (hab : a.Coprime b) (x : σ → ZMod (a*b)) :
    eval₂ (Int.castRingHom (ZMod (a*b))) x f=0 ↔
      eval₂ (Int.castRingHom (ZMod a)) (vectorEquiv hab x).1 f=0 ∧
      eval₂ (Int.castRingHom (ZMod b)) (vectorEquiv hab x).2 f=0 := by
  constructor
  · intro hx
    constructor
    · simpa only [map_eval₂_int,map_zero] using congrArg (leftProjection hab) hx
    · simpa only [map_eval₂_int,map_zero] using congrArg (rightProjection hab) hx
  · rintro ⟨ha,hb⟩
    apply (ZMod.chineseRemainder hab).injective
    apply Prod.ext
    · change leftProjection hab _=leftProjection hab 0
      simpa only [map_eval₂_int,map_zero] using ha
    · change rightProjection hab _=rightProjection hab 0
      simpa only [map_eval₂_int,map_zero] using hb

theorem common_zero_crt_iff (G : ι → MvPolynomial σ ℤ)
    {a b : ℕ} (hab : a.Coprime b) (x : σ → ZMod (a*b)) :
    (∀i,eval₂ (Int.castRingHom (ZMod (a*b))) x (G i)=0) ↔
      (∀i,eval₂ (Int.castRingHom (ZMod a)) (vectorEquiv hab x).1 (G i)=0) ∧
      (∀i,eval₂ (Int.castRingHom (ZMod b)) (vectorEquiv hab x).2 (G i)=0) := by
  simp only [polynomial_zero_crt_iff _ hab,forall_and]

def zeroCrtEquiv (G : ι → MvPolynomial σ ℤ) {a b : ℕ} (hab : a.Coprime b) :
    {x : σ → ZMod (a*b) // ∀i,eval₂ (Int.castRingHom (ZMod (a*b))) x (G i)=0} ≃
      ({x : σ → ZMod a // ∀i,eval₂ (Int.castRingHom (ZMod a)) x (G i)=0} ×
       {x : σ → ZMod b // ∀i,eval₂ (Int.castRingHom (ZMod b)) x (G i)=0}) :=
  (Equiv.subtypeEquiv (vectorEquiv hab) (common_zero_crt_iff G hab)).trans
    Equiv.subtypeProdEquivProd

/-- Exact multiplicativity concerns all residue solutions, not only
reductions of integer solutions. It also permits a modulus-one factor. -/
theorem zeroCount_mul (G : ι → MvPolynomial σ ℤ) {a b : ℕ} (hab : a.Coprime b) :
    zeroCount G (a*b)=zeroCount G a*zeroCount G b := by
  rw [zeroCount,Nat.card_congr (zeroCrtEquiv G hab),Nat.card_prod]
  rfl

@[simp] theorem zeroCount_one (G : ι → MvPolynomial σ ℤ) : zeroCount G 1=1 := by
  have hz (x : σ → ZMod 1) (i : ι) :
      eval₂ (Int.castRingHom (ZMod 1)) x (G i)=0 := Subsingleton.elim _ _
  simp [zeroCount,hz]

theorem zeroCount_eq_filter [Fintype σ] [DecidableEq σ] [Fintype ι]
    (G : ι → MvPolynomial σ ℤ) (q : ℕ) [NeZero q] :
    zeroCount G q=(Finset.univ.filter fun x : σ → ZMod q =>
      ∀i,eval₂ (Int.castRingHom (ZMod q)) x (G i)=0).card := by
  classical
  simp only [zeroCount,Nat.card_eq_fintype_card,Fintype.card_subtype]

theorem zeroCount_squarefree (G : ι → MvPolynomial σ ℤ)
    (q : ℕ) (hq : Squarefree q) : zeroCount G q=∏p∈q.primeFactors,zeroCount G p :=
  SquarefreePolynomialRoots.squarefree_product _
    (fun _ _ h => zeroCount_mul G h) (zeroCount_one G) q hq

/-- The prime bound is an explicit premise only at this elementary
arithmetic interface; the final fixed-model theorem supplies it. -/
theorem zeroCount_le_prime_bound (G : ι → MvPolynomial σ ℤ) (C d : ℕ)
    (hprime : ∀p : ℕ,p.Prime → zeroCount G p≤C*p^d)
    (q : ℕ) (hq : Squarefree q) :
    zeroCount G q≤C^q.primeFactors.card*q^d := by
  rw [zeroCount_squarefree G q hq]
  calc
    _ ≤ ∏p∈q.primeFactors,C*p^d :=
      Finset.prod_le_prod' fun p hp => hprime p (Nat.prime_of_mem_primeFactors hp)
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.prod_pow,
        Nat.prod_primeFactors_of_squarefree hq]

theorem exists_bound_of_prime_bound (G : ι → MvPolynomial σ ℤ)
    (C : ℕ) (hC : 1≤C) (d : ℕ)
    (hprime : ∀p : ℕ,p.Prime → zeroCount G p≤C*p^d)
    (ε : ℝ) (hε : 0<ε) :
    ∃K : ℝ,1≤K ∧ ∀q : ℕ,Squarefree q →
      (zeroCount G q : ℝ)≤K*(q : ℝ)^((d : ℝ)+ε) := by
  obtain ⟨K,hK,hbound⟩ :=
    PrimeFactorEpsilonBound.exists_uniform_prime_factor_bound C hC ε hε
  refine ⟨K,hK,?_⟩
  intro q hq
  have hqpos : 0<q := Nat.pos_of_ne_zero hq.ne_zero
  have hqR : 0<(q : ℝ) := by exact_mod_cast hqpos
  have hc : ((C^q.primeFactors.card : ℕ) : ℝ)≤K*(q : ℝ)^ε := by
    have he : (∏p∈q.primeFactors,C*q.factorization p)=C^q.primeFactors.card := by
      calc
        _ = ∏_p∈q.primeFactors,C := by
          apply Finset.prod_congr rfl
          intro p hp
          rw [Nat.factorization_eq_one_of_squarefree hq (Nat.prime_of_mem_primeFactors hp)
            (Nat.dvd_of_mem_primeFactors hp),mul_one]
        _ = _ := by rw [Finset.prod_const]
    simpa only [he] using hbound q hqpos
  calc
    (zeroCount G q : ℝ) ≤ ((C^q.primeFactors.card : ℕ) : ℝ)*(q : ℝ)^d := by
      exact_mod_cast zeroCount_le_prime_bound G C d hprime q hq
    _ ≤ (K*(q : ℝ)^ε)*(q : ℝ)^d :=
      mul_le_mul_of_nonneg_right hc (pow_nonneg hqR.le _)
    _ = _ := by
      rw [mul_assoc,←Real.rpow_natCast,←Real.rpow_add hqR]
      congr 2
      ring

/-- Rational quotient dimension supplies the all-prime estimates
internally. There is no prime-count or excluded-prime premise here. -/
theorem exists_uniform_bound [Fintype σ] {t d : ℕ}
    (G : Fin t → MvPolynomial σ ℤ)
    (hproper : Ideal.span (Set.range (fun i => map (Int.castRingHom ℚ) (G i)))≠⊤)
    (hdim : ringKrullDim (MvPolynomial σ ℚ ⧸
      Ideal.span (Set.range (fun i => map (Int.castRingHom ℚ) (G i))))≤
        (d : WithBot ℕ∞)) (ε : ℝ) (hε : 0<ε) :
    ∃K : ℝ,1≤K ∧ ∀q : ℕ,Squarefree q →
      (zeroCount G q : ℝ)≤K*(q : ℝ)^((d : ℝ)+ε) := by
  obtain ⟨C,hC,hprime⟩ := FixedEquationPrimeCount.exists_uniform_bound G hproper hdim
  exact exists_bound_of_prime_bound G C hC d hprime ε hε

/-- An actual identified integral model gives one constant before all
squarefree moduli, including every bad-reduction prime and modulus one.
It makes no assertion about a separately defined special-fiber locus. -/
theorem exists_model_bound [Fintype σ] {t : ℕ}
    (G : Fin t → MvPolynomial σ ℤ) (Z : Set (σ → GeometricField))
    (hZ : Z.Nonempty)
    (hmodel : IntegralModelDimension.geometricIdeal G=vanishingIdeal GeometricField Z)
    (d : ℕ) (hdim : affineDimension Z≤(d : Dimension)) (ε : ℝ) (hε : 0<ε) :
    ∃K : ℝ,1≤K ∧ ∀q : ℕ,Squarefree q →
      (zeroCount G q : ℝ)≤K*(q : ℝ)^((d : ℝ)+ε) := by
  obtain ⟨C,hC,hprime⟩ := IntegralModelDimension.exists_uniform_bound G Z hZ hmodel d hdim
  exact exists_bound_of_prime_bound G C hC d hprime ε hε

end CubicTenVariables.SquarefreeEquationCount

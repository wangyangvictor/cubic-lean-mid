import CubicTenVariables.AllPrimeConductorWeight
import CubicTenVariables.SimultaneousResidueWeightSum

/-! The actual conductor moment for fixed high-depth radicals in a
translated progression box. The numerical weights remain evaluated at
integer frequencies; only their proven majorants are residue functions. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.ConductorResidueMoment
open MvPolynomial HessianTheorem11 ProjectiveMicrolocalData
open scoped BigOperators Classical

private abbrev Index (a b : ℕ) := a.primeFactors ⊕ b.primeFactors

private def modulus {a b : ℕ} : Index a b → ℕ := Sum.elim Subtype.val Subtype.val

private theorem modulus_prime {a b : ℕ} (i : Index a b) : (modulus i).Prime := by
  cases i with
  | inl p => exact Nat.prime_of_mem_primeFactors p.property
  | inr p => exact Nat.prime_of_mem_primeFactors p.property

private instance modulus_fact {a b : ℕ} (i : Index a b) : Fact (modulus i).Prime :=
  ⟨modulus_prime i⟩

private instance modulus_neZero {a b : ℕ} (i : Index a b) : NeZero (modulus i) :=
  ⟨(modulus_prime i).ne_zero⟩

private theorem modulus_coprime {a b : ℕ} (hab : a.Coprime b) :
    Pairwise (fun i j : Index a b => (modulus i).Coprime (modulus j)) := by
  intro i j hij
  cases i with
  | inl p =>
    cases j with
    | inl q =>
      apply (Nat.coprime_primes (modulus_prime (.inl p : Index a b))
        (modulus_prime (.inl q : Index a b))).mpr
      intro he
      exact hij (congrArg Sum.inl (Subtype.ext he))
    | inr q =>
      exact Nat.Coprime.of_dvd (Nat.dvd_of_mem_primeFactors p.property)
        (Nat.dvd_of_mem_primeFactors q.property) hab
  | inr p =>
    cases j with
    | inl q =>
      exact Nat.Coprime.of_dvd (Nat.dvd_of_mem_primeFactors p.property)
        (Nat.dvd_of_mem_primeFactors q.property) hab.symm
    | inr q =>
      apply (Nat.coprime_primes (modulus_prime (.inr p : Index a b))
        (modulus_prime (.inr q : Index a b))).mpr
      intro he
      exact hij (congrArg Sum.inr (Subtype.ext he))

private theorem prod_modulus {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    (∏ i : Index a b, modulus i) = a*b := by
  rw [Fintype.prod_sum_type]
  simp only [modulus, Sum.elim_inl, Sum.elim_inr]
  rw [Finset.prod_coe_sort a.primeFactors (fun p : ℕ => p),
    Finset.prod_coe_sort b.primeFactors (fun p : ℕ => p),
    Nat.prod_primeFactors_of_squarefree ha,
    Nat.prod_primeFactors_of_squarefree hb]

private def residueWeight {t a b : ℕ}
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10) (D : ℕ)
    (i : Index a b) : (Fin 10 → ZMod (modulus i)) → ℝ :=
  match i with
  | .inl p => @AllPrimeConductorWeight.primeResidueWeight t f D p.val
      ⟨Nat.prime_of_mem_primeFactors p.property⟩
  | .inr p => @AllPrimeConductorWeight.squareResidueWeight t f D p.val
      ⟨Nat.prime_of_mem_primeFactors p.property⟩

private theorem residueWeight_nonneg {t a b : ℕ}
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10) (D : ℕ)
    (i : Index a b) (v : Fin 10 → ZMod (modulus i)) :
    0 ≤ residueWeight f D i v := by
  cases i with
  | inl p =>
    dsimp only [residueWeight,AllPrimeConductorWeight.primeResidueWeight]
    split_ifs
    · positivity
    · exact Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  | inr p =>
    dsimp only [residueWeight,AllPrimeConductorWeight.squareResidueWeight]
    split_ifs
    · positivity
    · exact Finset.sum_nonneg fun j _ => by split_ifs <;> positivity

variable {t N d : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
  {T : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)}
  {C : ℝ} {h : NumericalPrimeDepth.CoarseBounds F C}

/-- Fixed local residue bounds imply the actual conductor moment.
The hypotheses are local residue sums, not an assumed global moment. -/
theorem sum_le (hc : MicrolocalConductorDepth.Conclusion F f T N C d h)
    (D : ℕ) (hND : N ∣ D) (A : ℝ) (hA : 1 ≤ A)
    (hlocal : ∀ (p : ℕ) [Fact p.Prime],
      (∑ v : Fin 10 → ZMod p, AllPrimeConductorWeight.primeResidueWeight f D p v)
        ≤ A*(p : ℝ)^8 ∧
      (∑ v : Fin 10 → ZMod p, AllPrimeConductorWeight.squareResidueWeight f D p v)
        ≤ A*(p : ℝ)^9)
    (a b : ℕ) (ha : Squarefree a) (hb : Squarefree b) (hab : a.Coprime b)
    (m : ℕ) (hm : 0 < m) (hmab : m.Coprime (a*b))
    (u : Fin 10 → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (habL : ((a*b : ℕ) : ℝ) ≤ 1+L/(m : ℝ))
    (v₀ : Fin 10 → ℤ) (S : Finset (Fin 10 → ℤ))
    (hbox : ∀ v ∈ S, ∀ i, |(v i : ℝ)-u i| ≤ L)
    (hres : ∀ v ∈ S, ∀ i, (m : ℤ) ∣ v i-v₀ i)
    (hpdepth : ∀ v ∈ S, ∀ p ∈ a.primeFactors, 2 ≤ NumericalConductor.primeDepth h p v)
    (hsdepth : ∀ v ∈ S, ∀ p ∈ b.primeFactors, 2 ≤ NumericalConductor.squareDepth h p v) :
    (∑ v ∈ S, (NumericalConductor.K h a b v)^((3 : ℝ)/2)) ≤
      7^10*A^(a.primeFactors.card+b.primeFactors.card)*(1+L/(m : ℝ))^10 /
        ((a : ℝ)^2*(b : ℝ)) := by
  have hprod := prod_modulus ha hb
  have hmq (i : Index a b) : m.Coprime (modulus i) := by
    apply Nat.Coprime.of_dvd_right _ hmab
    rw [← hprod]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have haR : 0 < (a : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero ha.ne_zero
  have hbR : 0 < (b : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hb.ne_zero
  have hpoint (v : Fin 10 → ℤ) (hv : v ∈ S) :
      (NumericalConductor.K h a b v)^((3 : ℝ)/2) ≤
        ∏ i : Index a b, residueWeight f D i (fun j => (v j : ZMod (modulus i))) := by
    have hpn (p : ℕ) : 0 ≤ NumericalConductor.primeWeight h p v :=
      zero_le_one.trans (NumericalConductor.one_le_primeWeight h p v)
    have hsn (p : ℕ) : 0 ≤ NumericalConductor.squareWeight h p v :=
      zero_le_one.trans (NumericalConductor.one_le_squareWeight h p v)
    rw [NumericalConductor.K,
      Real.mul_rpow (Finset.prod_nonneg fun p _ => hpn p)
        (Finset.prod_nonneg fun p _ => hsn p),
      ← Real.finset_prod_rpow _ _ (fun p _ => hpn p),
      ← Real.finset_prod_rpow _ _ (fun p _ => hsn p),Fintype.prod_sum_type]
    apply mul_le_mul
    · rw [← Finset.prod_coe_sort a.primeFactors
        (fun p : ℕ => (NumericalConductor.primeWeight h p v)^((3 : ℝ)/2))]
      apply Finset.prod_le_prod
      · intro p _; exact Real.rpow_nonneg (hpn p) _
      · intro p _
        exact @AllPrimeConductorWeight.prime_domination t N d F f T C h hc D hND
          p ⟨Nat.prime_of_mem_primeFactors p.property⟩ v (hpdepth v hv p p.property)
    · rw [← Finset.prod_coe_sort b.primeFactors
        (fun p : ℕ => (NumericalConductor.squareWeight h p v)^((3 : ℝ)/2))]
      apply Finset.prod_le_prod
      · intro p _; exact Real.rpow_nonneg (hsn p) _
      · intro p _
        exact @AllPrimeConductorWeight.square_domination t N d F f T C h hc D hND
          p ⟨Nat.prime_of_mem_primeFactors p.property⟩ v (hsdepth v hv p p.property)
    · exact Finset.prod_nonneg fun p _ => Real.rpow_nonneg (hsn p) _
    · exact Finset.prod_nonneg fun p _ => residueWeight_nonneg f D (.inl p) _
  have hmass :
      (∏ i : Index a b, ∑ y : Fin 10 → ZMod (modulus i), residueWeight f D i y) ≤
        A^(a.primeFactors.card+b.primeFactors.card)*(a : ℝ)^8*(b : ℝ)^9 := by
    calc
      _ ≤ ∏ i : Index a b,
          match i with
          | .inl p => A*(p.val : ℝ)^8
          | .inr p => A*(p.val : ℝ)^9 := by
        apply Finset.prod_le_prod
        · intro i _; exact Finset.sum_nonneg fun y _ => residueWeight_nonneg f D i y
        · intro i _
          cases i with
          | inl p => exact (@hlocal p ⟨Nat.prime_of_mem_primeFactors p.property⟩).1
          | inr p => exact (@hlocal p ⟨Nat.prime_of_mem_primeFactors p.property⟩).2
      _ = _ := by
        rw [Fintype.prod_sum_type]
        simp only [Finset.prod_mul_distrib,Finset.prod_const,
          Fintype.card_coe,Finset.card_univ,Finset.prod_pow]
        rw [Finset.prod_coe_sort a.primeFactors (fun p : ℕ => (p : ℝ)),
          Finset.prod_coe_sort b.primeFactors (fun p : ℕ => (p : ℝ)),
          ← Nat.cast_prod,← Nat.cast_prod,
          Nat.prod_primeFactors_of_squarefree ha,Nat.prod_primeFactors_of_squarefree hb]
        rw [pow_add]
        ring
  have hweight := SimultaneousResidueWeightSum.sum_le_normalized
    (fun i : Index a b => modulus i) (modulus_coprime hab) m hm hmq
    (residueWeight f D) (residueWeight_nonneg f D) u L hL
    (by simpa only [hprod] using habL) v₀ S hbox hres
  calc
    _ ≤ ∑ v ∈ S, ∏ i : Index a b,
        residueWeight f D i (fun j => (v j : ZMod (modulus i))) :=
      Finset.sum_le_sum hpoint
    _ ≤ _ := hweight
    _ ≤ (7*(1+L/(m : ℝ))/((a*b : ℕ) : ℝ))^10 *
        (A^(a.primeFactors.card+b.primeFactors.card)*(a : ℝ)^8*(b : ℝ)^9) := by
      rw [hprod]
      exact mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by
      rw [Nat.cast_mul]
      field_simp [ne_of_gt haR,ne_of_gt hbR]
      <;> ring

/-- One constant, obtained from the actual all-prime residue estimates,
works before every pair of high-depth radicals and every progression box. -/
theorem exists_bound (lit : FixedFamilyPrimeFieldPointCount.Uniform)
    {B : ℕ} (hgeo : Geometry F f) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hData : TenMicrolocalIncidence.Conclusion F f N B) (hN : 1 ≤ N)
    (hc : MicrolocalConductorDepth.Conclusion F f T N C d h) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ (a b : ℕ), Squarefree a → Squarefree b → a.Coprime b →
      ∀ (m : ℕ), 0 < m → m.Coprime (a*b) →
      ∀ (u : Fin 10 → ℝ) (L : ℝ), 0 ≤ L →
      ((a*b : ℕ) : ℝ) ≤ 1+L/(m : ℝ) →
      ∀ (v₀ : Fin 10 → ℤ) (S : Finset (Fin 10 → ℤ)),
      (∀ v ∈ S, ∀ i, |(v i : ℝ)-u i| ≤ L) →
      (∀ v ∈ S, ∀ i, (m : ℤ) ∣ v i-v₀ i) →
      (∀ v ∈ S, ∀ p ∈ a.primeFactors, 2 ≤ NumericalConductor.primeDepth h p v) →
      (∀ v ∈ S, ∀ p ∈ b.primeFactors, 2 ≤ NumericalConductor.squareDepth h p v) →
      (∑ v ∈ S, (NumericalConductor.K h a b v)^((3 : ℝ)/2)) ≤
        7^10*A^(a.primeFactors.card+b.primeFactors.card)*(1+L/(m : ℝ))^10 /
          ((a : ℝ)^2*(b : ℝ)) := by
  obtain ⟨D,A,_hD,hND,hA,hbounds⟩ :=
    AllPrimeConductorWeight.exists_bound lit hgeo hhom hAn hData hN hc
  refine ⟨A,hA,?_⟩
  intro a b ha hb hab m hm hmab u L hL habL v₀ S hbox hres hpdepth hsdepth
  exact sum_le hc D hND A hA (fun p _ => ⟨(hbounds p).1,(hbounds p).2.1⟩)
    a b ha hb hab m hm hmab u L hL habL v₀ S hbox hres hpdepth hsdepth

end CubicTenVariables.ConductorResidueMoment

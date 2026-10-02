import CubicTenVariables.ComplementAllocationLocalBound
import CubicTenVariables.NumericalDepthThreshold

/-! Fixed exact high-depth allocation. The low pair retains the original
integer frequency, while the high powers cancel against the decreased
modulus range. Every factorization uses the actual numerical depths. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ComplementAllocationBound
open MvPolynomial NumericalPrimeDepth NumericalDepthAllocation NumericalDepthThreshold
open scoped BigOperators

variable {F : MvPolynomial (Fin 10) ℤ} {C : ℝ}

private theorem filtered_depth_power_product (s : Finset ℕ) (depth : ℕ → ℕ)
    (hdepth : ∀ p ∈ s, depth p ≤ 6) (r : ℕ) (e : ℕ → ℝ) :
    (∏ p ∈ s.filter (fun p => r ≤ depth p), (p : ℝ)^(e (depth p))) =
      ∏ j ∈ Finset.Icc r 6, ((∏ p ∈ s.filter (fun p => depth p=j), p : ℕ) : ℝ)^(e j) := by
  classical
  calc
    _ = ∏ j ∈ Finset.Icc r 6,
        ∏ p ∈ (s.filter (fun p => r ≤ depth p)).filter (fun p => depth p=j),
          (p : ℝ)^(e (depth p)) := (Finset.prod_fiberwise_of_maps_to
      (fun p hp => Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp hp).2,
        hdepth p (Finset.mem_filter.mp hp).1⟩) _).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j hj
      have hset : (s.filter (fun p => r ≤ depth p)).filter (fun p => depth p=j) =
          s.filter (fun p => depth p=j) := by
        ext p
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨hp,_⟩,he⟩
          exact ⟨hp,he⟩
        · rintro ⟨hp,he⟩
          exact ⟨⟨hp,he ▸ (Finset.mem_Icc.mp hj).1⟩,he⟩
      rw [hset]
      calc
        _ = ∏ p ∈ s.filter (fun p => depth p=j), (p : ℝ)^(e j) := by
          apply Finset.prod_congr rfl
          intro p hp
          rw [(Finset.mem_filter.mp hp).2]
        _ = _ := by
          rw [Real.finset_prod_rpow _ _ (fun p _ => Nat.cast_nonneg p),← Nat.cast_prod]

private theorem raw_power_product_eq (r : ℕ) (A B : ℕ → ℕ)
    (hA : ∀ j ∈ Finset.Icc r 6, 0 < A j)
    (hB : ∀ j ∈ Finset.Icc r 6, 0 < B j) :
    (∏ j ∈ Finset.Icc r 6, (A j : ℝ)^((11+(j : ℝ))/2)*(B j : ℝ)^(11+(j : ℝ))) =
      ((∏ j ∈ Finset.Icc r 6, A j*(B j)^2 : ℕ) : ℝ)^((11+(r : ℝ))/2)*
        ∏ j ∈ Finset.Icc r 6, (A j : ℝ)^(((j : ℝ)-(r : ℝ))/2)*
          (B j : ℝ)^((j : ℝ)-(r : ℝ)) := by
  rw [Nat.cast_prod,← Real.finset_prod_rpow _ _ (fun j _ => Nat.cast_nonneg _),
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have ha : 0 < (A j : ℝ) := by exact_mod_cast hA j hj
  have hb : 0 < (B j : ℝ) := by exact_mod_cast hB j hj
  rw [Nat.cast_mul,Nat.cast_pow,Real.mul_rpow ha.le (sq_nonneg _),
    ← Real.rpow_natCast_mul hb.le]
  norm_num only [Nat.cast_ofNat]
  symm
  calc
    _ = ((A j : ℝ)^((11+(r : ℝ))/2)*(A j : ℝ)^(((j : ℝ)-(r : ℝ))/2))*
        ((B j : ℝ)^(2*((11+(r : ℝ))/2))*(B j : ℝ)^((j : ℝ)-(r : ℝ))) := by ring
    _ = _ := by
      rw [← Real.rpow_add ha,← Real.rpow_add hb]
      congr 2 <;> ring

/-- The exact high-depth weight appearing after cancellation of its modulus. -/
def weight (r : ℕ) (A B : ℕ → ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc r 6, (A j : ℝ)^(((j : ℝ)-(r : ℝ))/2)*
    (B j : ℝ)^((j : ℝ)-(r : ℝ))

private theorem high_prime_product_bound (h : CoarseBounds F C)
    (a : ℕ) (v : Fin 10 → ℤ) (r : ℕ) :
    (∏ p ∈ a.primeFactors.filter (fun p => r ≤ NumericalConductor.primeDepth h p v),
      ‖completeCubicSum F p v‖) ≤
      C^(a.primeFactors.filter (fun p => r ≤ NumericalConductor.primeDepth h p v)).card *
        ∏ j ∈ Finset.Icc r 6, (primePart h a v j : ℝ)^((11+(j : ℝ))/2) := by
  have hd (p : ℕ) (hp : p ∈ a.primeFactors) : NumericalConductor.primeDepth h p v ≤ 6 := by
    letI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    simpa only [NumericalConductor.primeDepth_of_prime] using primeDepth_le_six h p v
  have hp := Finset.prod_le_prod
    (fun p (_ : p ∈ a.primeFactors.filter (fun p => r ≤ NumericalConductor.primeDepth h p v)) =>
      norm_nonneg (completeCubicSum F p v)) (fun p hp => by
        letI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1⟩
        exact (by simpa only [NumericalConductor.primeDepth_of_prime] using prime_bound h p v :
          ‖completeCubicSum F p v‖ ≤ C*(p : ℝ)^((11+(NumericalConductor.primeDepth h p v : ℝ))/2)))
  simp only [Finset.prod_mul_distrib,Finset.prod_const] at hp
  rw [filtered_depth_power_product a.primeFactors (fun p => NumericalConductor.primeDepth h p v)
    hd r (fun j => (11+(j : ℝ))/2)] at hp
  exact hp

private theorem high_square_product_bound (h : CoarseBounds F C)
    (b : ℕ) (v : Fin 10 → ℤ) (r : ℕ) :
    (∏ p ∈ b.primeFactors.filter (fun p => r ≤ NumericalConductor.squareDepth h p v),
      ‖completeCubicSum F (p^2) v‖) ≤
      C^(b.primeFactors.filter (fun p => r ≤ NumericalConductor.squareDepth h p v)).card *
        ∏ j ∈ Finset.Icc r 6, (squarePart h b v j : ℝ)^(11+(j : ℝ)) := by
  have hd (p : ℕ) (hp : p ∈ b.primeFactors) : NumericalConductor.squareDepth h p v ≤ 6 := by
    letI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    simpa only [NumericalConductor.squareDepth_of_prime] using squareDepth_le_six h p v
  have hp := Finset.prod_le_prod
    (fun p (_ : p ∈ b.primeFactors.filter (fun p => r ≤ NumericalConductor.squareDepth h p v)) =>
      norm_nonneg (completeCubicSum F (p^2) v)) (fun p hp => by
        letI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1⟩
        have he : (11+(NumericalConductor.squareDepth h p v : ℝ)) =
            ((11+squareDepth h p v : ℕ) : ℝ) := by
          rw [NumericalConductor.squareDepth_of_prime,Nat.cast_add,Nat.cast_ofNat]
        exact (by rw [he,Real.rpow_natCast]; exact square_bound h p v :
          ‖completeCubicSum F (p^2) v‖ ≤ C*(p : ℝ)^(11+(NumericalConductor.squareDepth h p v : ℝ))))
  simp only [Finset.prod_mul_distrib,Finset.prod_const] at hp
  rw [filtered_depth_power_product b.primeFactors (fun p => NumericalConductor.squareDepth h p v)
    hd r (fun j => 11+(j : ℝ))] at hp
  exact hp

/-- The actual high-modulus norm, expressed as its common modulus power
and the precise depth-allocation weight. -/
theorem high_norm_bound (h : CoarseBounds F C) (hF : F.IsHomogeneous 3)
    (a b : ℕ) (ha : Squarefree a) (hb : Squarefree b) (hab : a.Coprime b)
    (v : Fin 10 → ℤ) (r : ℕ) :
    ‖completeCubicSum F (primeHigh h a v r * (squareHigh h b v r)^2) v‖ ≤
      C^((primeHigh h a v r).primeFactors.card+(squareHigh h b v r).primeFactors.card)*
        ((primeHigh h a v r * (squareHigh h b v r)^2 : ℕ) : ℝ)^((11+(r : ℝ))/2)*
        weight r (primePart h a v) (squarePart h b v) := by
  have hsf := NumericalDepthThreshold.parts_squarefree h a b ha hb v r
  have hcop := (parts_pairwise_coprime h a b ha hb hab v r).2.2.2.2.2
  have hprime := high_prime_product_bound h a v r
  have hsquare := high_square_product_bound h b v r
  rw [← primeFactors_primeHigh h a v r] at hprime
  rw [← primeFactors_squareHigh h b v r] at hsquare
  have hmod : (∏ j ∈ Finset.Icc r 6, primePart h a v j*(squarePart h b v j)^2) =
      primeHigh h a v r*(squareHigh h b v r)^2 := by
    rw [Finset.prod_mul_distrib,Finset.prod_pow,
      ← (high_eq_products h a b v r).1,← (high_eq_products h a b v r).2]
  have hpowers := raw_power_product_eq r (primePart h a v) (squarePart h b v)
    (fun j _ => (NumericalDepthAllocation.parts_pos h a b v j).1)
    (fun j _ => (NumericalDepthAllocation.parts_pos h a b v j).2)
  rw [hmod] at hpowers
  rw [CompleteSumMultiplicativity.norm_squarefree_pair_product F hF _ _
    hsf.2.1 hsf.2.2.2 hcop v]
  calc
    _ ≤ (C^(primeHigh h a v r).primeFactors.card *
          ∏ j ∈ Finset.Icc r 6, (primePart h a v j : ℝ)^((11+(j : ℝ))/2))*
        (C^(squareHigh h b v r).primeFactors.card *
          ∏ j ∈ Finset.Icc r 6, (squarePart h b v j : ℝ)^(11+(j : ℝ))) :=
      mul_le_mul hprime hsquare (Finset.prod_nonneg fun _ _ => norm_nonneg _)
        (by have := h.constant_pos; positivity)
    _ = C^((primeHigh h a v r).primeFactors.card+(squareHigh h b v r).primeFactors.card)*
        (∏ j ∈ Finset.Icc r 6, (primePart h a v j : ℝ)^((11+(j : ℝ))/2)*
          (squarePart h b v j : ℝ)^(11+(j : ℝ))) := by
      rw [pow_add,Finset.prod_mul_distrib]
      ring
    _ = _ := by rw [hpowers]; dsimp [weight]; ring

/-- Fixed exact high-depth allocations, summed over the remaining actual
cube-free factor pairs. The constant precedes the frequency, cutoffs,
allocation functions and arbitrary finite family. -/
theorem exists_bound {t : ℕ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
    {T : ∀ k : Fin 4, MicrolocalPromotionTable.Table F f (k.val+1)}
    {N d : ℕ} {h : CoarseBounds F C}
    (hF : F.IsHomogeneous 3) (hc : MicrolocalConductorDepth.Conclusion F f T N C d h)
    (i : Fin 5) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ v : Fin 10 → ℤ,
      (fun k => (v k : ℚ)) ∈ ComplementFrequencyPieces.piece F f T i →
      ∀ D H : ℝ, 1 ≤ D → 1 ≤ H → (∀ k, |(v k : ℝ)| ≤ H) →
      ∀ A B : ℕ → ℕ, ∀ Q : Finset (ℕ × ℕ),
        (∀ x ∈ Q, Squarefree x.1 ∧ Squarefree x.2 ∧ x.1.Coprime x.2 ∧
          (x.1 : ℝ)*(x.2 : ℝ)^2 ≤ 2*D ∧
          ∀ j ∈ Finset.Icc (i.val+2) 6,
            primePart h x.1 v j = A j ∧ squarePart h x.2 v j = B j) →
        (∑ x ∈ Q, ‖completeCubicSum F (x.1*x.2^2) v‖) ≤
          M*(D*H)^ε*D^((13+(i.val : ℝ))/2)*weight (i.val+2) A B := by
  classical
  obtain ⟨M₀,hM₀,hlowbound⟩ := ComplementAllocationLocalBound.exists_low_sum_bound
    hF hc i (ε/2) (by linarith)
  obtain ⟨K,hK,hprimeweight⟩ := PrimeConstantEpsilonBound.exists_two_factor_bound
    C h.constant_pos (ε/2) (by linarith)
  let α : ℝ := (13+(i.val : ℝ))/2
  let M : ℝ := max 1 (M₀*K*(2 : ℝ)^(ε/2)*(2 : ℝ)^(ε/2)*(2 : ℝ)^α)
  refine ⟨M,le_max_left _ _,?_⟩
  intro v hv D H hD hH hvH A B Q hQ
  have hM : 0 ≤ M := zero_le_one.trans (le_max_left _ _)
  have hW : 0 ≤ weight (i.val+2) A B := Finset.prod_nonneg fun j _ => by positivity
  by_cases hne : Q.Nonempty
  · obtain ⟨x₀,hx₀⟩ := hne
    let r : ℕ := i.val+2
    let aH : ℕ := ∏ j ∈ Finset.Icc r 6, A j
    let bH : ℕ := ∏ j ∈ Finset.Icc r 6, B j
    have hhigh (x : ℕ × ℕ) (hx : x ∈ Q) :
        primeHigh h x.1 v r = aH ∧ squareHigh h x.2 v r = bH := by
      rw [(high_eq_products h x.1 x.2 v r).1,(high_eq_products h x.1 x.2 v r).2]
      constructor
      · exact Finset.prod_congr rfl (fun j hj => ((hQ x hx).2.2.2.2 j hj).1)
      · exact Finset.prod_congr rfl (fun j hj => ((hQ x hx).2.2.2.2 j hj).2)
    have haH : 0 < aH := (hhigh x₀ hx₀).1 ▸
      (NumericalDepthThreshold.parts_pos h x₀.1 x₀.2 v r).2.1
    have hbH : 0 < bH := (hhigh x₀ hx₀).2 ▸
      (NumericalDepthThreshold.parts_pos h x₀.1 x₀.2 v r).2.2.2
    let E : ℝ := ((aH*bH^2 : ℕ) : ℝ)
    have hE1 : 1 ≤ E := by
      dsimp [E]
      exact_mod_cast Nat.succ_le_iff.mpr (Nat.mul_pos haH (pow_pos hbH 2))
    have hE : 0 < E := zero_lt_one.trans_le hE1
    let X : ℝ := 2*D/E
    let low : ℕ × ℕ → ℕ × ℕ := fun x => (primeLow h x.1 v r,squareLow h x.2 v r)
    let Qlow : Finset (ℕ × ℕ) := Q.image low
    have hsplit (x : ℕ × ℕ) (hx : x ∈ Q) :
        (x.1 : ℝ)*(x.2 : ℝ)^2 = ((low x).1 : ℝ)*((low x).2 : ℝ)^2*E := by
      have he := modulus_reconstruction h x.1 x.2 (hQ x hx).1 (hQ x hx).2.1 v r
      rw [(hhigh x hx).1,(hhigh x hx).2] at he
      dsimp only [low,E]
      exact_mod_cast he
    have hlow1 (x : ℕ × ℕ) : 1 ≤ ((low x).1 : ℝ)*((low x).2 : ℝ)^2 := by
      have ha : (1 : ℝ) ≤ (low x).1 := by exact_mod_cast
        (NumericalDepthThreshold.parts_pos h x.1 x.2 v r).1
      have hb : (1 : ℝ) ≤ (low x).2 := by exact_mod_cast
        (NumericalDepthThreshold.parts_pos h x.1 x.2 v r).2.2.1
      nlinarith [sq_nonneg ((low x).2 : ℝ)]
    have hED : E ≤ 2*D := by
      have he := hsplit x₀ hx₀
      have hm := mul_le_mul_of_nonneg_right (hlow1 x₀) hE.le
      have hs := (hQ x₀ hx₀).2.2.2.1
      nlinarith
    have hX : 1 ≤ X := (le_div_iff₀ hE).mpr (by simpa using hED)
    have hX0 : 0 ≤ X := zero_le_one.trans hX
    have hXle : X ≤ 2*D := by
      apply (div_le_iff₀ hE).mpr
      nlinarith
    have hXE : X*E = 2*D := div_mul_cancel₀ _ hE.ne'
    have hlowQ : ∀ y ∈ Qlow, Squarefree y.1 ∧ Squarefree y.2 ∧ y.1.Coprime y.2 ∧
        (y.1 : ℝ)*(y.2 : ℝ)^2 ≤ 2*X ∧
        (∀ p ∈ y.1.primeFactors, NumericalConductor.primeDepth h p v ≤ i.val+1) ∧
        (∀ p ∈ y.2.primeFactors, NumericalConductor.squareDepth h p v ≤ i.val+1) := by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      have hs := NumericalDepthThreshold.parts_squarefree h x.1 x.2 (hQ x hx).1 (hQ x hx).2.1 v r
      have hp := parts_pairwise_coprime h x.1 x.2 (hQ x hx).1
        (hQ x hx).2.1 (hQ x hx).2.2.1 v r
      refine ⟨hs.1,hs.2.2.1,hp.2.2.1,?_,?_,?_⟩
      · have hsize := (hQ x hx).2.2.2.1
        rw [hsplit x hx] at hsize
        have hh : ((low x).1 : ℝ)*((low x).2 : ℝ)^2 ≤ X := (le_div_iff₀ hE).mpr hsize
        linarith
      · intro p hp
        rw [show (low x).1 = primeLow h x.1 v r from rfl,primeFactors_primeLow] at hp
        have hd := (Finset.mem_filter.mp hp).2
        dsimp [r] at hd
        omega
      · intro p hp
        rw [show (low x).2 = squareLow h x.2 v r from rfl,primeFactors_squareLow] at hp
        have hd := (Finset.mem_filter.mp hp).2
        dsimp [r] at hd
        omega
    have hinj : Set.InjOn low (↑Q : Set (ℕ × ℕ)) := by
      intro x hx y hy he
      have ha := congrArg Prod.fst he
      have hb := congrArg Prod.snd he
      apply Prod.ext
      · calc
          x.1 = (low x).1*aH := by
            simpa only [low,(hhigh x hx).1] using
              prime_reconstruction h x.1 (hQ x hx).1 v r
          _ = (low y).1*aH := by rw [ha]
          _ = y.1 := by
            symm
            simpa only [low,(hhigh y hy).1] using
              prime_reconstruction h y.1 (hQ y hy).1 v r
      · calc
          x.2 = (low x).2*bH := by
            simpa only [low,(hhigh x hx).2] using
              square_reconstruction h x.2 (hQ x hx).2.1 v r
          _ = (low y).2*bH := by rw [hb]
          _ = y.2 := by
            symm
            simpa only [low,(hhigh y hy).2] using
              square_reconstruction h y.2 (hQ y hy).2.1 v r
    have hs : (∑ y ∈ Qlow, ‖completeCubicSum F (y.1*y.2^2) v‖) ≤
        M₀*(X*H)^(ε/2)*X^α := hlowbound v hv X H hX hH hvH Qlow hlowQ
    have hexact : (∑ x ∈ Q, ‖completeCubicSum F (x.1*x.2^2) v‖) =
        ‖completeCubicSum F (aH*bH^2) v‖ *
          (∑ y ∈ Qlow, ‖completeCubicSum F (y.1*y.2^2) v‖) := by
      rw [Finset.mul_sum]
      rw [show (∑ y ∈ Qlow, ‖completeCubicSum F (aH*bH^2) v‖ *
          ‖completeCubicSum F (y.1*y.2^2) v‖) =
          ∑ x ∈ Q, ‖completeCubicSum F (aH*bH^2) v‖ *
            ‖completeCubicSum F ((low x).1*(low x).2^2) v‖ from
        Finset.sum_image (f := fun y : ℕ × ℕ => ‖completeCubicSum F (aH*bH^2) v‖ *
          ‖completeCubicSum F (y.1*y.2^2) v‖) hinj]
      apply Finset.sum_congr rfl
      intro x hx
      simpa only [low,(hhigh x hx).1,(hhigh x hx).2,mul_comm] using
        norm_split h hF x.1 x.2 (hQ x hx).1 (hQ x hx).2.1 (hQ x hx).2.2.1 v r
    have hw : weight r (primePart h x₀.1 v) (squarePart h x₀.2 v) = weight r A B := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [((hQ x₀ hx₀).2.2.2.2 j hj).1,((hQ x₀ hx₀).2.2.2.2 j hj).2]
    have heα : (11+(r : ℝ))/2 = α := by dsimp [r,α]; push_cast; ring
    have hh : ‖completeCubicSum F (aH*bH^2) v‖ ≤
        C^(aH.primeFactors.card+bH.primeFactors.card)*E^α*weight r A B := by
      have ht := high_norm_bound h hF x₀.1 x₀.2 (hQ x₀ hx₀).1
        (hQ x₀ hx₀).2.1 (hQ x₀ hx₀).2.2.1 v r
      simpa only [(hhigh x₀ hx₀).1,(hhigh x₀ hx₀).2,hw,heα] using ht
    have habD : ((aH*bH : ℕ) : ℝ) ≤ 2*D := by
      have hb1 : (1 : ℝ) ≤ bH := by exact_mod_cast hbH
      have hbb : (bH : ℝ) ≤ (bH : ℝ)^2 := by nlinarith
      calc
        _ = (aH : ℝ)*(bH : ℝ) := by rw [Nat.cast_mul]
        _ ≤ (aH : ℝ)*(bH : ℝ)^2 := mul_le_mul_of_nonneg_left hbb (Nat.cast_nonneg _)
        _ = E := by dsimp [E]; push_cast; rfl
        _ ≤ _ := hED
    have hcoeff : C^(aH.primeFactors.card+bH.primeFactors.card) ≤ K*(2*D)^(ε/2) :=
      (hprimeweight aH bH haH hbH).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) habD (by linarith)) (by linarith))
    have hDH : 0 ≤ D*H := by positivity
    have hsmall : (X*H)^(ε/2) ≤ (2 : ℝ)^(ε/2)*(D*H)^(ε/2) := by
      calc
        _ ≤ (2*D*H)^(ε/2) := Real.rpow_le_rpow (by positivity)
          (mul_le_mul_of_nonneg_right hXle (by linarith)) (by linarith)
        _ = _ := by rw [mul_assoc,Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hDH]
    have hlarge : (2*D)^(ε/2) ≤ (2 : ℝ)^(ε/2)*(D*H)^(ε/2) := by
      calc
        _ ≤ (2*(D*H))^(ε/2) := Real.rpow_le_rpow (by positivity) (by nlinarith) (by linarith)
        _ = _ := Real.mul_rpow (by norm_num) hDH
    have hscale : E^α*X^α = (2 : ℝ)^α*D^α := by
      rw [← Real.mul_rpow hE.le hX0,mul_comm E X,hXE,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ D)]
    have hhalf : (D*H)^(ε/2)*(D*H)^(ε/2) = (D*H)^ε := by
      rw [← Real.rpow_add (by positivity : 0 < D*H)]
      congr 1
      ring
    rw [hexact]
    calc
      _ ≤ (C^(aH.primeFactors.card+bH.primeFactors.card)*E^α*weight r A B)*
          (M₀*(X*H)^(ε/2)*X^α) :=
        mul_le_mul hh hs (Finset.sum_nonneg fun _ _ => norm_nonneg _)
          (by have := h.constant_pos; positivity)
      _ = (M₀*C^(aH.primeFactors.card+bH.primeFactors.card))*
          (X*H)^(ε/2)*(E^α*X^α)*weight r A B := by ring
      _ ≤ (M₀*(K*((2 : ℝ)^(ε/2)*(D*H)^(ε/2))))*
          ((2 : ℝ)^(ε/2)*(D*H)^(ε/2))*((2 : ℝ)^α*D^α)*weight r A B := by
        rw [hscale]
        have hc' := hcoeff.trans (mul_le_mul_of_nonneg_left hlarge (by linarith))
        gcongr
      _ = (M₀*K*(2 : ℝ)^(ε/2)*(2 : ℝ)^(ε/2)*(2 : ℝ)^α)*
          (D*H)^ε*D^α*weight r A B := by rw [← hhalf]; ring
      _ ≤ _ := by
        gcongr
        exact le_max_right _ _
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty]
    positivity

end CubicTenVariables.ComplementAllocationBound

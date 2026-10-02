import TranslatedDepthSeven.HypersurfaceSmoothPrimePacket
import TranslatedDepthSeven.PolynomialCRTResidueCount
import TranslatedDepthSeven.SchwartzZippelResidueCount
import TranslatedDepthSeven.FixedConeOccupiedResidueCRT

/-! The surface-sized occupied-residue bound for literal progression points.
Nonsingular reductions imply nonzero reduced equations; Schwartz--Zippel
and exact CRT then give degree(f)^k*q^2. -/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

theorem integerPolynomialValue_intCast_eq {N q : ℕ}
    (f : MvPolynomial (Fin N) ℤ) (x : Fin N → ℤ) :
    integerPolynomialValue f (fun i => (x i : ZMod q)) = (MvPolynomial.eval x f : ZMod q) := by
  exact (MvPolynomial.eval₂_comp (Int.castRingHom (ZMod q)) x f).symm

/-- A nonzero reduced partial at one actual point rules out the identically
zero reduction of the whole polynomial. -/
theorem map_intCast_ne_zero_of_pderiv_eval_ne_zero {N p : ℕ}
    (f : MvPolynomial (Fin N) ℤ) (x : Fin N → ℤ) (v : Fin N)
    (hv : (MvPolynomial.eval x (MvPolynomial.pderiv v f) : ZMod p) ≠ 0) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) f ≠ 0 := by
  intro hf
  apply hv
  rw [← eval_map_intCast]
  rw [← MvPolynomial.pderiv_map, hf, map_zero, map_zero]

/-- The literal integral-polynomial zero set modulo a prime has the usual
three-variable degree times p squared bound. -/
theorem card_integerPolynomialZeroSet_three_le
    (f : MvPolynomial (Fin 3) ℤ) (p : ℕ) (hp : p.Prime)
    (hf : MvPolynomial.map (Int.castRingHom (ZMod p)) f ≠ 0) :
    (integerPolynomialZeroSet p 3 hp.ne_zero {f}).card ≤ f.totalDegree * p ^ 2 := by
  classical
  have he : integerPolynomialZeroSet p 3 hp.ne_zero {f} =
      mvPolynomialZeroSet p 3 hp (MvPolynomial.map (Int.castRingHom (ZMod p)) f) := by
    ext x
    simp [mem_integerPolynomialZeroSet_iff, mem_mvPolynomialZeroSet_iff,
      integerPolynomialValue, MvPolynomial.eval_map]
  rw [he]
  apply card_mvPolynomialZeroSet_le_degree_mul hp _ hf
  exact Finset.sup_mono (MvPolynomial.support_map_subset (Int.castRingHom (ZMod p)) f)

/-- Exact CRT multiplies the local two-dimensional bounds, including the
explicit factor degree(f) for every selected prime. -/
theorem card_integerPolynomialZeroSet_three_primeProduct_le
    (f : MvPolynomial (Fin 3) ℤ) (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hgood : ∀ p ∈ P, MvPolynomial.map (Int.castRingHom (ZMod p)) f ≠ 0) :
    (integerPolynomialZeroSet (primeProduct P) 3 (primeProduct_ne_zero hprime) {f}).card ≤
      f.totalDegree ^ P.card * (primeProduct P) ^ 2 := by
  classical
  rw [card_integerPolynomialZeroSet_primeProduct P hprime]
  calc
    _ ≤ ∏ p : P, f.totalDegree * (p : ℕ) ^ 2 := by
      apply Finset.prod_le_prod'
      intro p _hp
      exact card_integerPolynomialZeroSet_three_le f p (hprime p p.property) (hgood p p.property)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_coe, Finset.prod_pow, primeSubtype_prod_eq_primeProduct P]

/-- Coprimality with the whole modulus makes the actual progression map
injective, including composite moduli. -/
theorem zmodIntegralAffineMap_injective_of_coprime {N q m : ℕ}
    (hqm : Nat.Coprime q m) (u : Fin N → ℤ) :
    Function.Injective (zmodIntegralAffineMap q m u) := by
  have hunit : IsUnit (m : ZMod q) := (ZMod.isUnit_iff_coprime m q).mpr hqm.symm
  intro y z he
  funext i
  exact hunit.mul_left_cancel (add_left_cancel (congrFun he i))

/-- Occupied displacement residues inject into the actual equation's zero
set modulo q. The original equation is retained, rather than its possibly
coefficient-growing translated polynomial. -/
theorem card_occupiedIntegralResidues_le_polynomialZeroSet_of_progression
    {N q m : ℕ} (f : MvPolynomial (Fin N) ℤ) (hq : q ≠ 0)
    (hqm : Nat.Coprime q m) (u : Fin N → ℤ) (Y : Finset (Fin N → ℤ))
    (hzero : ∀ y ∈ Y, MvPolynomial.eval (fun i => u i + (m : ℤ) * y i) f = 0) :
    (occupiedIntegralResidues q Y).card ≤ (integerPolynomialZeroSet q N hq {f}).card := by
  classical
  let φ := zmodIntegralAffineMap q m u
  have hφ : Function.Injective φ := zmodIntegralAffineMap_injective_of_coprime hqm u
  have hsub : (occupiedIntegralResidues q Y).image φ ⊆ integerPolynomialZeroSet q N hq {f} := by
    intro a ha
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := mem_occupiedIntegralResidues_iff.mp hw
    rw [mem_integerPolynomialZeroSet_iff]
    intro g hg
    have hgf : g = f := Finset.mem_singleton.mp hg
    subst g
    have he : φ (fun i => (y i : ZMod q)) =
        (fun i => ((u i + (m : ℤ) * y i : ℤ) : ZMod q)) := by
      funext i
      simp [φ, zmodIntegralAffineMap]
    rw [he, integerPolynomialValue_intCast_eq, hzero y hy, Int.cast_zero]
  calc
    (occupiedIntegralResidues q Y).card = ((occupiedIntegralResidues q Y).image φ).card :=
      (Finset.card_image_iff.mpr hφ.injOn).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- The squarefree-q form does not require a retained reservoir label. -/
theorem card_occupiedProgressionResidues_le_squarefree
    (f : MvPolynomial (Fin 3) ℤ) {q m : ℕ} (hq : Squarefree q)
    (hqm : Nat.Coprime q m) (u : Fin 3 → ℤ) (Y : Finset (Fin 3 → ℤ))
    (hzero : ∀ y ∈ Y, MvPolynomial.eval (fun i => u i + (m : ℤ) * y i) f = 0)
    (hgood : ∀ p, p.Prime → p ∣ q → ∃ (x : Fin 3 → ℤ) (v : Fin 3),
      (MvPolynomial.eval x (MvPolynomial.pderiv v f) : ZMod p) ≠ 0) :
    (occupiedIntegralResidues q Y).card ≤ f.totalDegree ^ q.primeFactors.card * q ^ 2 := by
  have hsprime : ∀ p ∈ q.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have he : primeProduct q.primeFactors = q := Nat.prod_primeFactors_of_squarefree hq
  have hq0 : q ≠ 0 := by
    rw [← he]
    exact primeProduct_ne_zero hsprime
  have hbound := card_integerPolynomialZeroSet_three_primeProduct_le f q.primeFactors hsprime
    (fun p hp => by
      obtain ⟨x, v, hv⟩ := hgood p (hsprime p hp) (Nat.dvd_of_mem_primeFactors hp)
      exact map_intCast_ne_zero_of_pderiv_eval_ne_zero f x v hv)
  have hcardeq := card_integerPolynomialZeroSet_congr_modulus he
    (primeProduct_ne_zero hsprime) hq0 {f}
  rw [hcardeq, he] at hbound
  exact (card_occupiedIntegralResidues_le_polynomialZeroSet_of_progression
    f hq0 hqm u Y hzero).trans hbound

/-- The exact degree(f)^k*q^2 bound for a literal reservoir modulus. One
nonsingular reduction at each prime factor suffices, with base points and
partial coordinates allowed to depend on the prime. -/
theorem card_occupiedProgressionResidues_le_of_smooth_modulus
    (f : MvPolynomial (Fin 3) ℤ) (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {k q m : ℕ} (hq : q ∈ modulusReservoir P k) (hqm : Nat.Coprime q m)
    (u : Fin 3 → ℤ) (Y : Finset (Fin 3 → ℤ))
    (hzero : ∀ y ∈ Y, MvPolynomial.eval (fun i => u i + (m : ℤ) * y i) f = 0)
    (hgood : ∀ p, p.Prime → p ∣ q → ∃ (x : Fin 3 → ℤ) (v : Fin 3),
      (MvPolynomial.eval x (MvPolynomial.pderiv v f) : ZMod p) ≠ 0) :
    (occupiedIntegralResidues q Y).card ≤ f.totalDegree ^ k * q ^ 2 := by
  have h := card_occupiedProgressionResidues_le_squarefree f
    (squarefree_of_mem_modulusReservoir hprime hq) hqm u Y hzero hgood
  simpa only [(primeFactors_spec_of_mem_modulusReservoir hprime hq).2.1] using h

/-- Packet-cover form for a four-variable equation and an arbitrary
squarefree modulus. Empty packets are allowed without choosing a base point. -/
theorem card_occupiedHypersurfaceProgressionResidues_le_squarefree
    (F : MvPolynomial (Fin 4) ℤ) {q m : ℕ} (hq : Squarefree q)
    (hqm : Nat.Coprime q m) (u : Fin 3 → ℤ) (Y : Finset (Fin 3 → ℤ))
    (hzero : ∀ y ∈ Y, MvPolynomial.eval (progressionHomogeneousPoint u m y) F = 0)
    (hsmooth : ∀ y ∈ Y, ∀ p, p.Prime → p ∣ q → ∃ v,
      (MvPolynomial.eval (fun i => u i + (m : ℤ) * y i)
        (MvPolynomial.pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) :
    (occupiedIntegralResidues q Y).card ≤
      (surfaceHypersurfaceFirstChartDehomogenize F).totalDegree ^ q.primeFactors.card * q ^ 2 := by
  classical
  by_cases hY : Y.Nonempty
  · obtain ⟨y₀, hy₀⟩ := hY
    apply card_occupiedProgressionResidues_le_squarefree
      (surfaceHypersurfaceFirstChartDehomogenize F) hq hqm u Y
    · intro y hy
      rw [surfaceHypersurfaceFirstChart_eval]
      exact hzero y hy
    · intro p hp hpq
      obtain ⟨v, hv⟩ := hsmooth y₀ hy₀ p hp hpq
      exact ⟨(fun i => u i + (m : ℤ) * y₀ i), v, hv⟩
  · have he : Y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hY
    simp [he, occupiedIntegralResidues]

/-- Reservoir-labelled form with exactly k degree factors. -/
theorem card_occupiedHypersurfaceProgressionResidues_le
    (F : MvPolynomial (Fin 4) ℤ) (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {k q m : ℕ} (hq : q ∈ modulusReservoir P k) (hqm : Nat.Coprime q m)
    (u : Fin 3 → ℤ) (Y : Finset (Fin 3 → ℤ))
    (hzero : ∀ y ∈ Y, MvPolynomial.eval (progressionHomogeneousPoint u m y) F = 0)
    (hsmooth : ∀ y ∈ Y, ∀ p, p.Prime → p ∣ q → ∃ v,
      (MvPolynomial.eval (fun i => u i + (m : ℤ) * y i)
        (MvPolynomial.pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) :
    (occupiedIntegralResidues q Y).card ≤
      (surfaceHypersurfaceFirstChartDehomogenize F).totalDegree ^ k * q ^ 2 := by
  have h := card_occupiedHypersurfaceProgressionResidues_le_squarefree F
    (squarefree_of_mem_modulusReservoir hprime hq) hqm u Y hzero hsmooth
  simpa only [(primeFactors_spec_of_mem_modulusReservoir hprime hq).2.1] using h

end
end TranslatedDepthSeven

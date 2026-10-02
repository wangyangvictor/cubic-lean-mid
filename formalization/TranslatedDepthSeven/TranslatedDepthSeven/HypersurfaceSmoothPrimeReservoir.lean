import TranslatedDepthSeven.ManuscriptModulusReservoir
import TranslatedDepthSeven.CharacteristicPolynomialHeight
import TranslatedDepthSeven.HypersurfaceSurfaceResidueDiscFirstChart

/-! A reservoir of actual primes usable at nonsingular integer points of a
fixed hypersurface.  The reservoir is chosen before the progression modulus
and point; polynomial coefficient bounds are derived from the fixed equation.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Filter
open scoped BigOperators Topology
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

/-- A finite family of literal integral polynomials has one coefficient
constant and degree bound, valid on every integral box. -/
theorem exists_uniform_integral_polynomial_family_height
    {σ : Type*} {n : ℕ} (G : Fin n → MvPolynomial σ ℤ) :
    ∃ C e : ℕ, 1 ≤ C ∧ ∀ (H : ℕ), 1 ≤ H → ∀ (x : σ → ℤ),
      (∀ i, (x i).natAbs ≤ H) → ∀ j,
        (MvPolynomial.eval x (G j)).natAbs ≤ C * H ^ e := by
  classical
  let C := max 1 (Finset.univ.sup fun j =>
    (G j).support.card * mvPolynomialCoefficientNatAbsMax (G j))
  let e := Finset.univ.sup fun j => (G j).totalDegree
  refine ⟨C, e, Nat.le_max_left _ _, ?_⟩
  intro H hH x hx j
  have he : (G j).totalDegree ≤ e := Finset.le_sup (f := fun j => (G j).totalDegree)
    (Finset.mem_univ j)
  have h := eval_natAbs_le_support_mul_coeff_mul_pow_generic (G j) x
    (fun m hm => coeff_natAbs_le_mvPolynomialCoefficientNatAbsMax (G j) hm) he hx
  rw [max_eq_right hH] at h
  exact h.trans (Nat.mul_le_mul_right (H ^ e)
    ((Finset.le_sup (f := fun j => (G j).support.card * mvPolynomialCoefficientNatAbsMax (G j))
      (Finset.mem_univ j)).trans (Nat.le_max_right _ _)))

/-- The fixed coefficient factors in the progression and Jacobian
certificates are absorbed into one fixed integer height exponent. -/
theorem exists_hypersurface_gradient_certificate_height
    (F : MvPolynomial (Fin 4) ℤ) (D : ℤ) :
    ∃ A C : ℕ, 2 ≤ A ∧ 1 ≤ C ∧ ∀ H : ℕ, C ≤ H →
      (∀ m : ℕ, m ≤ H → ((m : ℤ) * D).natAbs ≤ H ^ A) ∧
      ∀ x : Fin 3 → ℤ, (∀ i, (x i).natAbs ≤ H) → ∀ v,
        (MvPolynomial.eval x
          (MvPolynomial.pderiv v (surfaceHypersurfaceFirstChartDehomogenize F))).natAbs ≤ H ^ A := by
  obtain ⟨C₀, e, hC₀, hheight⟩ := exists_uniform_integral_polynomial_family_height
    (fun v : Fin 3 => MvPolynomial.pderiv v (surfaceHypersurfaceFirstChartDehomogenize F))
  refine ⟨e + 2, max C₀ (max 1 D.natAbs), by omega,
    (Nat.le_max_left 1 D.natAbs).trans (Nat.le_max_right _ _), ?_⟩
  intro H hH
  have h1 : 1 ≤ H := (Nat.le_max_left 1 D.natAbs).trans
    ((Nat.le_max_right _ _).trans hH)
  have hD : D.natAbs ≤ H := (Nat.le_max_right 1 D.natAbs).trans
    ((Nat.le_max_right _ _).trans hH)
  have hC : C₀ ≤ H := (Nat.le_max_left _ _).trans hH
  constructor
  · intro m hm
    simp only [Int.natAbs_mul, Int.natAbs_natCast]
    calc
      m * D.natAbs ≤ H * H := Nat.mul_le_mul hm hD
      _ = H ^ 2 := by ring
      _ ≤ H ^ (e + 2) := Nat.pow_le_pow_right h1 (by omega)
  · intro x hx v
    calc
      _ ≤ C₀ * H ^ e := hheight H h1 x hx v
      _ ≤ H * H ^ e := Nat.mul_le_mul_right _ hC
      _ = H ^ (e + 1) := by rw [pow_succ]; ring
      _ ≤ H ^ (e + 2) := Nat.pow_le_pow_right h1 (by omega)

/-- For a fixed equation and bad-reduction integer, one finite reservoir is
chosen before every modulus and point. Each nonzero-gradient integral point
has a member avoiding `m*D` and with nonsingular reduction at every prime
factor. The prime supply and quantitative bounds are proved by the existing
manuscript reservoir theorem, not hypotheses of this statement. -/
theorem exists_hypersurfaceSmoothPrimeReservoir
    (F : MvPolynomial (Fin 4) ℤ) (D : ℤ) (hD : D ≠ 0)
    (a Cres ε : ℝ) (ha : 0 < a) (haOne : a < 1)
    (hCres : 1 < Cres) (hε : 0 < ε) :
    ∃ A : ℕ, ∃ H₀ : ℝ, 1 ≤ H₀ ∧
      ∀ H : ℕ, H₀ ≤ (H : ℝ) → ∀ T : ℝ, 1 ≤ T → T ≤ H →
        ∃ (P : Finset ℕ) (k : ℕ) (hPprime : ∀ p ∈ P, p.Prime),
          P = manuscriptPrimePoolAt A a H ∧
          k = manuscriptCrossingAt A a Cres H T ∧
          (∀ q ∈ modulusReservoir P k, Squarefree q ∧
            Cres * T ^ a ≤ (q : ℝ) ∧
            (q : ℝ) ≤ (4 * manuscriptPrimeIntervalCoefficient A a * (ε / 3)⁻¹) *
              Cres * T ^ a * H ^ ε) ∧
          ((modulusReservoir P k).card : ℝ) ≤ 2 * H ^ ε ∧
          (∀ (m : ℕ), 0 < m → m ≤ H → ∀ (x : Fin 3 → ℤ),
            (∀ i, (x i).natAbs ≤ H) →
            (∃ v, MvPolynomial.eval x
              (MvPolynomial.pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) ≠ 0) →
            ∃ q ∈ modulusReservoir P k,
              Nat.Coprime q m ∧ Nat.Coprime q D.natAbs ∧
              ∀ p, p.Prime → p ∣ q → ∃ v,
                (MvPolynomial.eval x
                  (MvPolynomial.pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) := by
  obtain ⟨A, C, hA, hC, hheight⟩ := exists_hypersurface_gradient_certificate_height F D
  have hAreal : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
  obtain ⟨H₁, hreservoir⟩ := eventually_atTop.mp
    (eventually_exists_manuscriptModulusReservoir hAreal ha haOne hCres hε)
  refine ⟨A, max (max 1 C) H₁, (le_max_left 1 (C : ℝ)).trans (le_max_left _ _), ?_⟩
  intro H hH T hT hTH
  have hCcast : (C : ℝ) ≤ H := (le_max_right 1 (C : ℝ)).trans
    ((le_max_left _ _).trans hH)
  have hCH : C ≤ H := by exact_mod_cast hCcast
  have hH₁ : H₁ ≤ (H : ℝ) := (le_max_right _ _).trans hH
  obtain ⟨P, k, hPprime, hP, hk, _hPcard, _hPbounds, _hkP,
    hmoduli, _hconnected, hcard, _hlcm, _hcertOne, hcertTwo⟩ := hreservoir H hH₁ T hT hTH
  refine ⟨P, k, hPprime, hP, hk, ?_, ?_, ?_⟩
  · intro q hq
    exact hmoduli ⟨q, hq⟩
  · have hn : ((modulusReservoir P k).card : ℝ) ≤
        (((modulusReservoir P k).card + (modulusReservoirDirectedEdges P k hPprime).card : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_right (modulusReservoir P k).card _
    exact hn.trans hcard
  · intro m hm hmH x hx hgrad
    obtain ⟨v, hv⟩ := hgrad
    let J := MvPolynomial.eval x
      (MvPolynomial.pderiv v (surfaceHypersurfaceFirstChartDehomogenize F))
    have hfixed : (m : ℤ) * D ≠ 0 := mul_ne_zero (by exact_mod_cast hm.ne') hD
    have hfixedSize : (((m : ℤ) * D).natAbs : ℝ) ≤ (H : ℝ) ^ (A : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast (hheight H hCH).1 m hmH
    have hJSize : (J.natAbs : ℝ) ≤ (H : ℝ) ^ (A : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast (hheight H hCH).2 x hx v
    obtain ⟨_, ⟨q⟩, _⟩ := hcertTwo ((m : ℤ) * D) J hfixed hv hfixedSize hJSize
    obtain ⟨hq, hqfixed, hqJ⟩ := (mem_certificateAllowedTwo_modulusReservoir_iff
      hPprime ((m : ℤ) * D) J).mp q.2
    have hqfixed' : Nat.Coprime q.1 (m * D.natAbs) := by
      simpa only [Int.natAbs_mul, Int.natAbs_natCast] using hqfixed
    refine ⟨q.1, hq, hqfixed'.of_dvd_right (dvd_mul_right _ _),
      hqfixed'.of_dvd_right (dvd_mul_left _ _), ?_⟩
    intro p hp hpq
    refine ⟨v, ?_⟩
    have hnot : ¬ p ∣ J.natAbs := hp.coprime_iff_not_dvd.mp (hqJ.of_dvd_left hpq)
    intro hz
    exact hnot (Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd J p).mp hz))

end
end TranslatedDepthSeven

import CubicTenVariables.HomogeneousPerturbationExistence
import CubicTenVariables.LowerDegreePerturbation
import CubicTenVariables.UniformFiniteZeroCount
import TranslatedDepthSeven.PrincipalOpenReduction

/-!
# Uniform finite-field bounds for arbitrary lower-degree perturbations

A fixed proper homogeneous integral equation family with rational dimension
at most r has at most C p^r common zeros after every lower-degree perturbation
over every prime field. The constant is chosen before both the prime and all
perturbation coefficients. Normalization, coefficient descent, finite fiber
counting and the exceptional primes are proved internally.
-/

noncomputable section
namespace CubicTenVariables.UniformHomogeneousPerturbationCount
open MvPolynomial TranslatedDepthSeven HomogeneousPerturbationCertificate
open scoped BigOperators

variable {n s : ℕ} {ι : Type*} [Fintype ι]

/-- The same coordinate-power certificate bounds every fiber of every
lower-degree perturbation, over any finite field. -/
theorem natCard_commonZeros_le_of_certificate {K : Type*} [Field K] [Finite K]
    (f f' : ι → MvPolynomial (Fin n) K) (e : ι → ℕ) (d : Fin n → ℕ)
    (D : Certificate f e d s)
    (hpert : ∀ j, (f' j - f j).totalDegree < e j) :
    Nat.card {x : Fin n → K // ∀ j, MvPolynomial.eval x (f' j) = 0} ≤
      (∏ i, d i) * (Nat.card K) ^ s := by
  classical
  have haug (t : Fin s → K) (j : ι ⊕ Fin s) :
      (Sum.elim f' (fun k => D.forms k - C (t k)) j -
        Sum.elim f D.forms j).totalDegree < Sum.elim e (fun _ => 1) j := by
    cases j with
    | inl j => exact hpert j
    | inr j =>
      simp only [Sum.elim_inr]
      have h : D.forms j - C (t j) - D.forms j = -C (t j) := by ring
      rw [h, totalDegree_neg, totalDegree_C]
      exact Nat.zero_lt_one
  apply UniformFiniteZeroCount.natCard_commonZeros_le_mul_pow f' D.forms (∏ i, d i)
  · intro t
    exact LowerDegreePerturbation.finite_quotient
      (Sum.elim f D.forms) (Sum.elim f' (fun k => D.forms k - C (t k)))
      (Sum.elim e (fun _ => 1)) d D.coefficients D.powers_pos
      D.coefficients_homogeneous D.coefficients_zero D.identity (haug t)
  · intro t
    exact LowerDegreePerturbation.finrank_quotient_le
      (Sum.elim f D.forms) (Sum.elim f' (fun k => D.forms k - C (t k)))
      (Sum.elim e (fun _ => 1)) d D.coefficients D.powers_pos
      D.coefficients_homogeneous D.coefficients_zero D.identity (haug t)

/-- One constant precedes every prime and every independently chosen
lower-degree perturbation of the fixed integral leading forms. -/
theorem exists_uniform_bound {r : ℕ}
    (f : ι → MvPolynomial (Fin n) ℤ) (e : ι → ℕ)
    (hhom : ∀ j, (f j).IsHomogeneous (e j))
    (hproper : Ideal.span (Set.range (fun j => map (Int.castRingHom ℚ) (f j))) ≠ ⊤)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℚ ⧸
      Ideal.span (Set.range (fun j => map (Int.castRingHom ℚ) (f j)))) ≤
        (r : WithBot ℕ∞)) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (p : ℕ), p.Prime →
      ∀ f' : ι → MvPolynomial (Fin n) (ZMod p),
        (∀ j, (f' j - map (Int.castRingHom (ZMod p)) (f j)).totalDegree < e j) →
        Nat.card {x : Fin n → ZMod p // ∀ j, MvPolynomial.eval x (f' j) = 0} ≤ A*p^r := by
  classical
  obtain ⟨s, hs, d, ⟨D⟩⟩ := HomogeneousPerturbationExistence.exists_certificate
    (fun j => map (Int.castRingHom ℚ) (f j)) e
    (fun j => (hhom j).map _) hproper r hdim
  obtain ⟨Δ, hΔ, ⟨D₀⟩⟩ := exists_principal_model f e d D
  let B : ℕ := ∏ i, d i
  let A : ℕ := 1 + B + Δ.natAbs ^ n
  refine ⟨A, by dsimp [A]; omega, ?_⟩
  intro p hp f' hpert
  letI : Fact p.Prime := ⟨hp⟩
  have hΔpos : 0 < Δ.natAbs := Int.natAbs_pos.mpr hΔ
  by_cases hbad : p ∣ Δ.natAbs
  · have hpΔ : p ≤ Δ.natAbs := Nat.le_of_dvd hΔpos hbad
    calc
      _ ≤ Nat.card (Fin n → ZMod p) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ = p^n := by rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
      _ ≤ Δ.natAbs^n := Nat.pow_le_pow_left hpΔ n
      _ ≤ A := by dsimp [A]; omega
      _ ≤ A*p^r := Nat.le_mul_of_pos_right _ (pow_pos hp.pos _)
  · let φ := awayIntToZMod Δ p hp hbad
    have hcomp : φ.comp (Int.castRingHom (Localization.Away Δ)) =
        Int.castRingHom (ZMod p) := RingHom.ext_int _ _
    have hfamily : (fun j => map φ (map (Int.castRingHom (Localization.Away Δ)) (f j))) =
        (fun j => map (Int.castRingHom (ZMod p)) (f j)) := by
      funext j
      rw [map_map, hcomp]
    have Dp : Certificate (fun j => map (Int.castRingHom (ZMod p)) (f j)) e d s :=
      hfamily ▸ D₀.map φ
    have hbound := natCard_commonZeros_le_of_certificate _ f' e d Dp hpert
    rw [Nat.card_zmod] at hbound
    exact hbound.trans (Nat.mul_le_mul (by dsimp [B, A]; omega)
      (Nat.pow_le_pow_right hp.pos hs))

end CubicTenVariables.UniformHomogeneousPerturbationCount

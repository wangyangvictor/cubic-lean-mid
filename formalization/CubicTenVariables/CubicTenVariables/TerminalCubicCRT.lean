import CubicTenVariables.CRTCharacters
import CubicTenVariables.TerminalCubicSum

/-! Exact CRT multiplicativity of the actual terminal sums and their finite
maxima. Coefficients and base points come from integers, and both linear
and scalar phases retain their inverse-modulus twists. -/

noncomputable section
namespace CubicTenVariables.TerminalCubicCRT

open MvPolynomial HessianTheorem11 CubicTaylorExpansion TerminalCubicSum CRTCharacters
open scoped BigOperators

section Algebra
variable {R S : Type*} [CommRing R] [CommRing S] {d : ℕ}

theorem map_terminalPhase (f : R →+* S) (F : MvPolynomial (Fin d) R)
    (A alpha : R) (ell y z : Fin d → R) :
    f (terminalPhase F A ell alpha y z) =
      terminalPhase (MvPolynomial.map f F) (f A) (fun i => f (ell i)) (f alpha)
        (fun i => f (y i)) (fun i => f (z i)) := by
  simp only [terminalPhase, quadraticAt, directional, dotProduct, gradient,
    map_add, map_mul, map_sum, MvPolynomial.map_eval, pderiv_map, Function.comp_def]

theorem terminalPhase_smul (F : MvPolynomial (Fin d) R) (A alpha c : R)
    (ell y z : Fin d → R) :
    terminalPhase F A (c • ell) (c * alpha) y z = c * terminalPhase F A ell alpha y z := by
  simp only [terminalPhase, smul_dotProduct, smul_eq_mul]
  ring

theorem map_int_polynomial (f : R →+* S) (F : MvPolynomial (Fin d) ℤ) :
    MvPolynomial.map f (MvPolynomial.map (Int.castRingHom R) F) =
      MvPolynomial.map (Int.castRingHom S) F := by
  have hf : f.comp (Int.castRingHom R) = Int.castRingHom S := by
    ext a
    simp
  rw [MvPolynomial.map_map, hf]

theorem map_integer_terminalPhase (f : R →+* S) (F : MvPolynomial (Fin d) ℤ)
    (A : ℤ) (alpha : R) (ell z : Fin d → R) (y : Fin d → ℤ) :
    f (terminalPhase (MvPolynomial.map (Int.castRingHom R) F) (A : R)
      ell alpha (fun i => (y i : R)) z) =
      terminalPhase (MvPolynomial.map (Int.castRingHom S) F) (A : S)
        (fun i => f (ell i)) (f alpha) (fun i => (y i : S)) (fun i => f (z i)) := by
  rw [map_terminalPhase, map_int_polynomial]
  simp only [map_intCast]

end Algebra

variable {m n d : ℕ} (h : m.Coprime n) [NeZero m] [NeZero n]

/-- Pointwise standard-character CRT, displaying both inverse-modulus twists. -/
theorem stdAddChar_terminalPhase_crt (F : MvPolynomial (Fin d) ℤ) (A : ℤ)
    (alpha : ZMod (m*n)) (ell z : Fin d → ZMod (m*n)) (y : Fin d → ℤ) :
    ZMod.stdAddChar (terminalPhase (MvPolynomial.map (Int.castRingHom (ZMod (m*n))) F)
      (A : ZMod (m*n)) ell alpha (fun i => (y i : ZMod (m*n))) z) =
      ZMod.stdAddChar (terminalPhase (MvPolynomial.map (Int.castRingHom (ZMod m)) F)
        (A : ZMod m) ((leftTwist h : ZMod m) • (fun i => leftProjection h (ell i)))
        ((leftTwist h : ZMod m) * leftProjection h alpha)
        (fun i => (y i : ZMod m)) (fun i => leftProjection h (z i))) *
      ZMod.stdAddChar (terminalPhase (MvPolynomial.map (Int.castRingHom (ZMod n)) F)
        (A : ZMod n) ((rightTwist h : ZMod n) • (fun i => rightProjection h (ell i)))
        ((rightTwist h : ZMod n) * rightProjection h alpha)
        (fun i => (y i : ZMod n)) (fun i => rightProjection h (z i))) := by
  rw [stdAddChar_crt h, map_integer_terminalPhase, map_integer_terminalPhase,
    ← terminalPhase_smul, ← terminalPhase_smul]

/-- Exact multiplicativity of the terminal sum; there is no degree or
smoothness hypothesis, and the two inverse-modulus twists are explicit. -/
theorem terminalSum_crt (F : MvPolynomial (Fin d) ℤ) (A : ℤ)
    (ell : Fin d → ZMod (m*n)) (alpha : ZMod (m*n)) (y : Fin d → ℤ) :
    terminalSum (m*n) (MvPolynomial.map (Int.castRingHom (ZMod (m*n))) F)
      (A : ZMod (m*n)) ell alpha (fun i => (y i : ZMod (m*n))) =
      terminalSum m (MvPolynomial.map (Int.castRingHom (ZMod m)) F) (A : ZMod m)
        ((leftTwist h : ZMod m) • (fun i => leftProjection h (ell i)))
        ((leftTwist h : ZMod m) * leftProjection h alpha) (fun i => (y i : ZMod m)) *
      terminalSum n (MvPolynomial.map (Int.castRingHom (ZMod n)) F) (A : ZMod n)
        ((rightTwist h : ZMod n) • (fun i => rightProjection h (ell i)))
        ((rightTwist h : ZMod n) * rightProjection h alpha) (fun i => (y i : ZMod n)) := by
  classical
  let L (z : Fin d → ZMod m) := ZMod.stdAddChar
    (terminalPhase (MvPolynomial.map (Int.castRingHom (ZMod m)) F) (A : ZMod m)
      ((leftTwist h : ZMod m) • (fun i => leftProjection h (ell i)))
      ((leftTwist h : ZMod m) * leftProjection h alpha) (fun i => (y i : ZMod m)) z)
  let R (z : Fin d → ZMod n) := ZMod.stdAddChar
    (terminalPhase (MvPolynomial.map (Int.castRingHom (ZMod n)) F) (A : ZMod n)
      ((rightTwist h : ZMod n) • (fun i => rightProjection h (ell i)))
      ((rightTwist h : ZMod n) * rightProjection h alpha) (fun i => (y i : ZMod n)) z)
  calc
    _ = ∑ p : (Fin d → ZMod m) × (Fin d → ZMod n), L p.1 * R p.2 := by
      apply Fintype.sum_equiv (vectorEquiv h d)
      intro z
      exact stdAddChar_terminalPhase_crt h F A alpha ell z y
    _ = _ := by
      rw [Fintype.sum_prod_type, ← Finset.sum_mul_sum]
      rfl

private theorem exists_twisted_parameters
    (a : (ZMod m)ˣ) (b : (ZMod n)ˣ) (ell₁ : Fin d → ZMod m) (ell₂ : Fin d → ZMod n) :
    ∃ u : (ZMod (m*n))ˣ, ∃ ell : Fin d → ZMod (m*n),
      (leftTwist h : ZMod m) * leftProjection h (u : ZMod (m*n)) = (a : ZMod m) ∧
      (rightTwist h : ZMod n) * rightProjection h (u : ZMod (m*n)) = (b : ZMod n) ∧
      (leftTwist h : ZMod m) • (fun i => leftProjection h (ell i)) = ell₁ ∧
      (rightTwist h : ZMod n) • (fun i => rightProjection h (ell i)) = ell₂ := by
  obtain ⟨u, hu⟩ := (unitEquiv h).surjective
    ((leftTwist h)⁻¹ * a, (rightTwist h)⁻¹ * b)
  obtain ⟨ell, hell⟩ := (vectorEquiv h d).surjective
    ((↑((leftTwist h)⁻¹) : ZMod m) • ell₁, (↑((rightTwist h)⁻¹) : ZMod n) • ell₂)
  refine ⟨u, ell, ?_, ?_, ?_, ?_⟩
  · have he := congrArg (fun p : (ZMod m)ˣ × (ZMod n)ˣ => (p.1 : ZMod m)) hu
    change leftProjection h (u : ZMod (m*n)) =
      (↑((leftTwist h)⁻¹ * a) : ZMod m) at he
    rw [he]
    simp [← mul_assoc]
  · have he := congrArg (fun p : (ZMod m)ˣ × (ZMod n)ˣ => (p.2 : ZMod n)) hu
    change rightProjection h (u : ZMod (m*n)) =
      (↑((rightTwist h)⁻¹ * b) : ZMod n) at he
    rw [he]
    simp [← mul_assoc]
  · have he := congrArg Prod.fst hell
    change (fun i => leftProjection h (ell i)) = _ at he
    rw [he]
    ext i
    simp [← mul_assoc]
  · have he := congrArg Prod.snd hell
    change (fun i => rightProjection h (ell i)) = _ at he
    rw [he]
    ext i
    simp [← mul_assoc]

include h in
/-- Exact multiplicativity of the actual finite maximum over all residue
units and linear terms. All lower-modulus maximizers lift simultaneously by CRT. -/
theorem terminalMax_crt (F : MvPolynomial (Fin d) ℤ) (A : ℤ) (y : Fin d → ℤ) :
    terminalMax (m*n) (MvPolynomial.map (Int.castRingHom (ZMod (m*n))) F)
      (A : ZMod (m*n)) (fun i => (y i : ZMod (m*n))) =
      terminalMax m (MvPolynomial.map (Int.castRingHom (ZMod m)) F)
        (A : ZMod m) (fun i => (y i : ZMod m)) *
      terminalMax n (MvPolynomial.map (Int.castRingHom (ZMod n)) F)
        (A : ZMod n) (fun i => (y i : ZMod n)) := by
  apply le_antisymm
  · obtain ⟨u, ell, he⟩ := terminalMax_attained (m*n)
      (MvPolynomial.map (Int.castRingHom (ZMod (m*n))) F) (A : ZMod (m*n))
      (fun i => (y i : ZMod (m*n)))
    rw [he, terminalSum_crt h, norm_mul]
    apply mul_le_mul
    · simpa only [Units.val_mul, unitEquiv_fst_coe] using
        norm_terminalSum_le_terminalMax m (MvPolynomial.map (Int.castRingHom (ZMod m)) F)
          (A : ZMod m) _ (leftTwist h * (unitEquiv h u).1) (fun i => (y i : ZMod m))
    · simpa only [Units.val_mul, unitEquiv_snd_coe] using
        norm_terminalSum_le_terminalMax n (MvPolynomial.map (Int.castRingHom (ZMod n)) F)
          (A : ZMod n) _ (rightTwist h * (unitEquiv h u).2) (fun i => (y i : ZMod n))
    · exact norm_nonneg _
    · exact terminalMax_nonneg _ _ _ _
  · obtain ⟨a, ell₁, ha⟩ := terminalMax_attained m
      (MvPolynomial.map (Int.castRingHom (ZMod m)) F) (A : ZMod m) (fun i => (y i : ZMod m))
    obtain ⟨b, ell₂, hb⟩ := terminalMax_attained n
      (MvPolynomial.map (Int.castRingHom (ZMod n)) F) (A : ZMod n) (fun i => (y i : ZMod n))
    obtain ⟨u, ell, hu₁, hu₂, hell₁, hell₂⟩ := exists_twisted_parameters h a b ell₁ ell₂
    have he := norm_terminalSum_le_terminalMax (m*n)
      (MvPolynomial.map (Int.castRingHom (ZMod (m*n))) F) (A : ZMod (m*n)) ell u
      (fun i => (y i : ZMod (m*n)))
    rw [terminalSum_crt h, norm_mul, hu₁, hu₂, hell₁, hell₂] at he
    rwa [ha, hb]

end CubicTenVariables.TerminalCubicCRT

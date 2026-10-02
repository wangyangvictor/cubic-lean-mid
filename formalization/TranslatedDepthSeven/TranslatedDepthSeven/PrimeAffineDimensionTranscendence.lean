import TranslatedDepthSeven.FieldPolynomialKrullDimension
import TranslatedDepthSeven.PrimeAffineNoetherNormalization

/-!
# Dimension equals transcendence degree for the affine domains used here

For a prime quotient of a finite polynomial algebra over a
characteristic-zero field, Noether normalization and the exact field-case
polynomial-dimension theorem identify the quotient's Krull dimension with
its transcendence degree.  This is proved only in the concrete finite
polynomial setting required below.
-/

namespace TranslatedDepthSeven

noncomputable section

universe u

/-- A prime affine quotient whose Krull dimension is the displayed natural
number has the same displayed transcendence degree. -/
theorem trdeg_eq_nat_of_primeAffine_ringKrullDim_eq
    (k : Type u) [Field k] [CharZero k] {n d : ℕ}
    (P : Ideal (MvPolynomial (Fin n) k)) (hP : P.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) k ⧸ P) =
      (d : WithBot ℕ∞)) :
    Algebra.trdeg k (MvPolynomial (Fin n) k ⧸ P) = (d : Cardinal) := by
  letI : P.IsPrime := hP
  obtain ⟨s, _hsn, g, hg, hfinite⟩ :=
    exists_finite_injective_normalization_of_primeAffine P
  let B := MvPolynomial (Fin s) k
  let A := MvPolynomial (Fin n) k ⧸ P
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : Algebra.IsIntegral B A := ⟨hfinite.to_isIntegral⟩
  have hdimensional : ringKrullDim A = ringKrullDim B :=
    ringKrullDim_eq_of_isIntegral_injective hg
  have hs : s = d := by
    have hsd : (s : WithBot ℕ∞) = (d : WithBot ℕ∞) := by
      calc
        (s : WithBot ℕ∞) = ringKrullDim B :=
          (ringKrullDim_mvPolynomial_fin_eq_of_field k s).symm
        _ = ringKrullDim A := hdimensional.symm
        _ = (d : WithBot ℕ∞) := hdim
    exact_mod_cast hsd
  have htrdeg :=
    trdeg_eq_nat_of_finite_injective_polynomial g hg hfinite
  simpa only [hs] using htrdeg

/-- Converse numerical form: if the transcendence degree of a prime affine
quotient is `d`, then its Krull dimension is `d`. -/
theorem ringKrullDim_eq_nat_of_primeAffine_trdeg_eq
    (k : Type u) [Field k] [CharZero k] {n d : ℕ}
    (P : Ideal (MvPolynomial (Fin n) k)) (hP : P.IsPrime)
    (htrdeg : Algebra.trdeg k (MvPolynomial (Fin n) k ⧸ P) =
      (d : Cardinal)) :
    ringKrullDim (MvPolynomial (Fin n) k ⧸ P) =
      (d : WithBot ℕ∞) := by
  letI : P.IsPrime := hP
  obtain ⟨s, _hsn, g, hg, hfinite⟩ :=
    exists_finite_injective_normalization_of_primeAffine P
  have hs : s = d :=
    normalization_parameter_eq_of_trdeg_eq g hg hfinite htrdeg
  let B := MvPolynomial (Fin s) k
  let A := MvPolynomial (Fin n) k ⧸ P
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : Algebra.IsIntegral B A := ⟨hfinite.to_isIntegral⟩
  calc
    ringKrullDim A = ringKrullDim B :=
      ringKrullDim_eq_of_isIntegral_injective hg
    _ = (s : WithBot ℕ∞) :=
      ringKrullDim_mvPolynomial_fin_eq_of_field k s
    _ = (d : WithBot ℕ∞) := by rw [hs]

end

end TranslatedDepthSeven

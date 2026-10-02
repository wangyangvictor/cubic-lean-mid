import TranslatedDepthSeven.ProjectiveAffineChartDimensionInternal

/-! # Dimension of the literal Option-indexed affine chart

This is the field-generic dimension bridge for projective Bertini. It uses
the already proved algebraicity of the cone embedding into the polynomial
ring over the chart, together with affine dimension and transcendence
degree. No projective dimension premise is introduced.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

/-- A nonempty standard chart of a homogeneous prime cone has dimension
one less than the cone, over any characteristic-zero field. -/
theorem optionAffineChart_ringKrullDim_eq_of_cone
    {K : Type*} [Field K] [CharZero K] {N r : ℕ}
    (I : Ideal (MvPolynomial (Option (Fin N)) K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Option (Fin N)) K))
    (hprime : I.IsPrime) (hX : X (none : Option (Fin N)) ∉ I)
    (hdim : ringKrullDim (MvPolynomial (Option (Fin N)) K ⧸ I) =
      ((r + 1 : ℕ) : WithBot ℕ∞)) :
    ringKrullDim (MvPolynomial (Fin N) K ⧸
      I.map multivariateDehomogenization.toRingHom) = (r : WithBot ℕ∞) := by
  let e := (_root_.finSuccEquiv N).symm
  let I' := I.map (MvPolynomial.renameEquiv K e)
  letI : I.IsPrime := hprime
  have hI'prime : I'.IsPrime := by dsimp only [I']; infer_instance
  let eqv := renameQuotientAlgEquiv K e I
  have hdim' : ringKrullDim (MvPolynomial (Fin (N + 1)) K ⧸ I') =
      ((r + 1 : ℕ) : WithBot ℕ∞) :=
    (ringKrullDim_eq_of_ringEquiv eqv.toRingEquiv).symm.trans hdim
  have hconeTrdeg : Algebra.trdeg K (MvPolynomial (Option (Fin N)) K ⧸ I) =
      ((r + 1 : ℕ) : Cardinal) :=
    eqv.trdeg_eq.trans (trdeg_eq_nat_of_primeAffine_ringKrullDim_eq K I' hI'prime hdim')
  let J := I.map multivariateDehomogenization.toRingHom
  let R := MvPolynomial (Fin N) K ⧸ J
  have hJprime : J.IsPrime := map_multivariateDehomogenization_isPrime I hI hprime hX
  letI : J.IsPrime := hJprime
  have hpolyTrdeg : Algebra.trdeg K (Polynomial R) = ((r + 1 : ℕ) : Cardinal) :=
    (trdeg_optionChartPolynomial_eq_cone I hI hprime hX).trans hconeTrdeg
  obtain ⟨s, _hsN, _g, _hginj, _hgfinite, hsTrdeg⟩ :=
    exists_finite_injective_normalization_of_primeAffine_with_trdeg J
  have hs : s = r := by
    have h := trdeg_add_eq K R (A := Polynomial R)
    rw [Polynomial.trdeg_of_isDomain, hpolyTrdeg] at h
    change Algebra.trdeg K (MvPolynomial (Fin N) K ⧸ J) + 1 =
      ((r + 1 : ℕ) : Cardinal) at h
    rw [hsTrdeg] at h
    have hn : s + 1 = r + 1 := by exact_mod_cast h
    omega
  exact ringKrullDim_eq_nat_of_primeAffine_trdeg_eq K J hJprime
    (by simpa only [hs] using hsTrdeg)

end
end TranslatedDepthSeven

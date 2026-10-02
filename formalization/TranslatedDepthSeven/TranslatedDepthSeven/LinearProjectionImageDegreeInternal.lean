import TranslatedDepthSeven.HomogeneousComponentDegreeMassInternal

/-!
# A homogeneous linear image does not increase degree

Each homogeneous piece of the image coordinate ring injects into the
corresponding piece of the source coordinate ring. If source and image
have the same projective dimension, comparison of the leading Hilbert
coefficients proves that the image degree is no larger. No finiteness or
birationality assertion is assumed in the homogeneous-piece inequality.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 300000

/-- Literal homogeneous-piece injection for an image defined by linear
forms. The source ideal need not be prime or homogeneous for this inequality. -/
theorem finrank_homogeneousLinearImage_component_le
    {K σ τ : Type*} [Field K] [Finite σ] [Finite τ]
    (I : Ideal (MvPolynomial σ K))
    (forms : τ → MvPolynomial σ K)
    (hforms : ∀ i, (forms i).IsHomogeneous 1) (k : ℕ) :
    let h := (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval forms)
    let J := RingHom.ker h.toRingHom
    Module.finrank K (quotientHomogeneousComponent K τ J k) ≤
      Module.finrank K (quotientHomogeneousComponent K σ I k) := by
  let h := (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval forms)
  let J := RingHom.ker h.toRingHom
  let q := Ideal.kerLiftAlg h
  let S := quotientHomogeneousComponent K τ J k
  let T := quotientHomogeneousComponent K σ I k
  have hmem (z : S) : q z.val ∈ T := by
    obtain ⟨f, hf, hzf⟩ := z.property
    refine ⟨MvPolynomial.aeval forms f, ?_, ?_⟩
    · simpa only [one_mul] using hf.aeval forms hforms
    rw [← hzf]
    change Ideal.Quotient.mk I (MvPolynomial.aeval forms f) =
      Ideal.kerLiftAlg h (Ideal.Quotient.mk J f)
    exact (Ideal.kerLiftAlg_mk h f).symm
  let L : S →ₗ[K] T := (q.toLinearMap.comp S.subtype).codRestrict T hmem
  have hL : Function.Injective L := by
    intro x y hxy
    apply Subtype.ext
    apply Ideal.kerLiftAlg_injective h
    exact congrArg Subtype.val hxy
  exact L.finrank_le_finrank_of_injective hL

/-- At unchanged projective dimension, a linear image has degree no
larger than the source. Hilbert certificates are explicit theorem data;
no claim that an arbitrary image has the same dimension is hidden here. -/
theorem projectiveDegree_homogeneousLinearImage_le
    {K : Type*} [Field K] {N M r d e : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (forms : Fin (M + 1) → MvPolynomial (Fin (N + 1)) K)
    (hforms : ∀ i, (forms i).IsHomogeneous 1)
    (hsource : HasProjectiveDimensionDegree I r d)
    (himage : HasProjectiveDimensionDegree
      (RingHom.ker ((Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval forms)).toRingHom)
      r e) : e ≤ d := by
  obtain ⟨_hdim, hd, P, hPdegree, hPlc, kP, hPeval⟩ := hsource
  obtain ⟨_hedim, he, Q, hQdegree, hQlc, kQ, hQeval⟩ := himage
  have hcompare := sum_degrees_le_of_shifted_hilbertPolynomial_comparison
    (fun _ : Unit ↦ Q) P r d 0 (max kP kQ) (fun _ : Unit ↦ e)
    hd (fun _ ↦ he) (fun _ ↦ hQdegree) (fun _ ↦ hQlc) hPdegree hPlc (by
      intro n hn
      have hkP : kP ≤ n := (le_max_left _ _).trans hn
      have hkQ : kQ ≤ n := (le_max_right _ _).trans hn
      simp only [Fintype.sum_unique, Nat.add_zero]
      rw [← hQeval n hkQ, ← hPeval n hkP]
      exact_mod_cast finrank_homogeneousLinearImage_component_le I forms hforms n)
  simpa only [Fintype.sum_unique] using hcompare

end
end TranslatedDepthSeven

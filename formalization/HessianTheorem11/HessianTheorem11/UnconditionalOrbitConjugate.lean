import HessianTheorem11.UnconditionalOrbitMaximumDefs
import HessianTheorem11.ReducedRelativeKempf

/-! Conjugation preserves actual global SL relative maximizers. This uses
the literal ideal-order identity and does not assume invariant flags. -/
noncomputable section
namespace HessianTheorem11.UnconditionalOrbitGlobal
open MvPolynomial RationalDescent PolynomialRestriction ReducedRelative
variable {K : Type*} [Field K] [Infinite K] {n d : ℕ}

theorem conjugate_det_one (σ : K ≃+* K) (f : WeightFrame K n)
    (hf : f.matrix.det = 1) : (f.conjugate σ).matrix.det = 1 := by
  change (σ.toRingHom.mapMatrix f.matrix).det = 1
  rw [← RingHom.map_det,hf,map_one]

/-- The normalized speed comparison is transported through the inverse
field automorphism, so maximality is preserved against every SL competitor. -/
theorem SLMaximizingFrame.conjugate (σ : K ≃+* K)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (f : WeightFrame K n)
    (hf : SLMaximizingFrame d F S f) :
    SLMaximizingFrame d (map σ.toRingHom F) (conjugateSet σ S) (f.conjugate σ) := by
  refine ⟨conjugate_det_one σ f hf.det_one,hf.nonzero,
    (admissible_conjugate_iff σ F f).mpr hf.admissible,?_,?_⟩
  · rw [relativeOrder_map σ F hF]
    exact hf.positive_order
  · intro g hg hga
    have hadm := (admissible_conjugate_iff σ.symm (map σ.toRingHom F) g).mpr hga
    rw [map_symm_map] at hadm
    have h := hf.maximal (g.conjugate σ.symm) (conjugate_det_one σ.symm g hg) hadm
    have he := relativeSpeed_map σ F hF S (g.conjugate σ.symm)
    rw [WeightFrame.conjugate_symm] at he
    rw [relativeSpeed_map σ F hF,he]
    exact h

/-- For a rational form, its literal orbit boundary is fixed by Galois
conjugation, hence every conjugate of a maximizing frame is another
maximizing frame for precisely the same data. -/
theorem boundary_maximizing_conjugate (F : RationalPolynomial n)
    (hF : F.IsHomogeneous d) (f : WeightFrame GeometricField n)
    (hf : SLMaximizingFrame d (geometricPolynomial F)
      (orbitBoundary (geometricPolynomial F)) f)
    (σ : GeometricField ≃ₐ[ℚ] GeometricField) :
    SLMaximizingFrame d (geometricPolynomial F)
      (orbitBoundary (geometricPolynomial F)) (f.conjugate σ.toRingEquiv) := by
  have h := hf.conjugate σ.toRingEquiv (geometricPolynomial F) (hF.map _) _ f
  rwa [conjugateSet_orbitBoundary,
    show σ.toRingEquiv.toRingHom = σ.toRingHom from rfl,
    geometricPolynomial_galois_fixed F σ] at h

end HessianTheorem11.UnconditionalOrbitGlobal

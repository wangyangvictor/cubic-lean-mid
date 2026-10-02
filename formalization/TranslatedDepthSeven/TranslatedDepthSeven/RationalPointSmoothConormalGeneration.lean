import TranslatedDepthSeven.RationalPointResidueField
import TranslatedDepthSeven.RationalSmoothConormalGeneration

/-!
# Smooth conormal generation at a rational affine point

This file removes the abstract residue-field equivalence from the smooth
conormal-generation theorem.  The local ring is the literal localization at
the kernel of a `k`-rational point.  The final theorem specializes further to
an affine quotient of a multivariate polynomial ring at a specified point.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct
open KaehlerDifferential IsLocalRing

universe u v w

/-- The literal local ring of an affine `k`-algebra at a `k`-rational point. -/
abbrev RationalPointLocalRing
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    (x : A →ₐ[k] k) :=
  Localization.AtPrime (RingHom.ker x.toRingHom)

/-- The rational-smooth conormal-generation theorem at the literal stalk of
an affine `k`-algebra.  The residue-field equivalence is supplied canonically
by the rational point. -/
theorem extension_ker_eq_span_at_rationalPoint_of_smooth_krullDim_and_selectedMinor
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    (x : A →ₐ[k] k)
    [IsNoetherianRing (RationalPointLocalRing x)]
    (P : Algebra.Extension k (RationalPointLocalRing x))
    [IsLocalRing P.Ring]
    [Algebra.FormallySmooth k P.Ring]
    [Module.Free P.Ring Ω[P.Ring⁄k]]
    [Module.Finite P.Ring Ω[P.Ring⁄k]]
    (hker : P.ker.FG)
    [Algebra.FormallySmooth k (RationalPointLocalRing x)]
    {N s : ℕ}
    (hdim : ringKrullDim (RationalPointLocalRing x) = s)
    (hambient : Module.finrank (ResidueField (RationalPointLocalRing x))
      (ResidueField (RationalPointLocalRing x) ⊗[RationalPointLocalRing x]
        P.CotangentSpace) = N)
    (g : Fin (N - s) → P.ker)
    (ambientCoordinates :
      (ResidueField (RationalPointLocalRing x) ⊗[RationalPointLocalRing x]
          P.CotangentSpace) ≃ₗ[ResidueField (RationalPointLocalRing x)]
        (Fin N → ResidueField (RationalPointLocalRing x)))
    (cols : Fin (N - s) → Fin N)
    (hminor : Matrix.det (Matrix.of (fun i j ↦
      ambientCoordinates
        ((P.cotangentComplex.baseChange
            (ResidueField (RationalPointLocalRing x)))
          ((1 : ResidueField (RationalPointLocalRing x))
            ⊗ₜ[RationalPointLocalRing x]
              Algebra.Extension.Cotangent.mk (g i))) (cols j))) ≠ 0) :
    Ideal.span (Set.range fun i ↦ ((g i : P.ker) : P.Ring)) = P.ker := by
  exact extension_ker_eq_span_of_rationalSmooth_krullDim_and_selectedMinor
    (rationalPointResidueFieldAlgEquiv x) P hker hdim hambient g
      ambientCoordinates cols hminor

/-- The literal stalk of `k[σ]/I` at the point induced by `z`. -/
abbrev AffineQuotientRationalPointLocalRing
    {k : Type u} {σ : Type w} [Field k]
    (I : Ideal (MvPolynomial σ k)) (z : σ → k)
    (hI : I ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom) :=
  RationalPointLocalRing (affineQuotientRationalPoint I z hI)

/-- Concrete affine-polynomial-quotient specialization.  For finitely many
variables, Noetherianity of the quotient and of its local ring is inferred
from Mathlib; the remaining assumptions are exactly the smoothness,
dimension, finite-kernel, and selected-minor hypotheses used by the
conormal-generation theorem. -/
theorem extension_ker_eq_span_at_affineQuotientRationalPoint_of_smooth_krullDim_and_selectedMinor
    {k : Type u} {σ : Type w} [Field k] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) (z : σ → k)
    (hI : I ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom)
    (P : Algebra.Extension k
      (AffineQuotientRationalPointLocalRing I z hI))
    [IsLocalRing P.Ring]
    [Algebra.FormallySmooth k P.Ring]
    [Module.Free P.Ring Ω[P.Ring⁄k]]
    [Module.Finite P.Ring Ω[P.Ring⁄k]]
    (hker : P.ker.FG)
    [Algebra.FormallySmooth k
      (AffineQuotientRationalPointLocalRing I z hI)]
    {N s : ℕ}
    (hdim : ringKrullDim
      (AffineQuotientRationalPointLocalRing I z hI) = s)
    (hambient : Module.finrank
      (ResidueField (AffineQuotientRationalPointLocalRing I z hI))
      (ResidueField (AffineQuotientRationalPointLocalRing I z hI)
        ⊗[AffineQuotientRationalPointLocalRing I z hI] P.CotangentSpace) = N)
    (g : Fin (N - s) → P.ker)
    (ambientCoordinates :
      (ResidueField (AffineQuotientRationalPointLocalRing I z hI)
          ⊗[AffineQuotientRationalPointLocalRing I z hI] P.CotangentSpace)
        ≃ₗ[ResidueField (AffineQuotientRationalPointLocalRing I z hI)]
          (Fin N →
            ResidueField (AffineQuotientRationalPointLocalRing I z hI)))
    (cols : Fin (N - s) → Fin N)
    (hminor : Matrix.det (Matrix.of (fun i j ↦
      ambientCoordinates
        ((P.cotangentComplex.baseChange
            (ResidueField (AffineQuotientRationalPointLocalRing I z hI)))
          ((1 : ResidueField
              (AffineQuotientRationalPointLocalRing I z hI))
            ⊗ₜ[AffineQuotientRationalPointLocalRing I z hI]
              Algebra.Extension.Cotangent.mk (g i))) (cols j))) ≠ 0) :
    Ideal.span (Set.range fun i ↦ ((g i : P.ker) : P.Ring)) = P.ker := by
  exact
    extension_ker_eq_span_at_rationalPoint_of_smooth_krullDim_and_selectedMinor
      (affineQuotientRationalPoint I z hI) P hker hdim hambient g
        ambientCoordinates cols hminor

end

end TranslatedDepthSeven

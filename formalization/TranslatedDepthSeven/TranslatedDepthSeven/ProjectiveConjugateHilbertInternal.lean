import TranslatedDepthSeven.IsolatedVertexQuotientPersistentPila
import TranslatedDepthSeven.ProjectiveHilbertCoefficientExtension

/-!
# Projective Hilbert data under coefficient-field automorphisms

An automorphism is a coefficient extension along its own ring map.  The
already proved coefficient-extension equality of the homogeneous Hilbert
pieces therefore applies directly.  The quotient ring isomorphism supplies
the equality of Krull dimensions.  No further geometric input is needed.
-/

namespace TranslatedDepthSeven

noncomputable section

open Published

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2000000

/-- Coefficientwise conjugation leaves every homogeneous Hilbert-function
value unchanged.  The nonidentity scalar map is installed only as the
coefficient extension, not as a new action on either Hilbert piece. -/
theorem projectiveHilbertPiece_finrank_conjugate_eq
    (N k : ℕ) (g : Qbar ≃ₐ[ℚ] Qbar)
    (I : Ideal (MvPolynomial (Fin (N + 1)) Qbar)) :
    Module.finrank Qbar
        (projectiveHilbertPiece Qbar N (conjugateIdeal g I) k) =
      Module.finrank Qbar (projectiveHilbertPiece Qbar N I k) := by
  letI : Algebra Qbar Qbar := g.toRingHom.toAlgebra
  exact projectiveHilbertPiece_finrank_map_eq (K := Qbar) (L := Qbar) N k I

/-- The formerly external projective dimension--degree invariance under
Qbar conjugation follows from the internal coefficient-extension theorem
and the explicit quotient ring equivalence. -/
theorem qbarConjugatePreservesProjectiveDimensionDegree :
    StandardAG.QbarConjugatePreservesProjectiveDimensionDegree := by
  intro N r d g I hI
  rcases hI with ⟨hdim, hd, P, hdegree, hleading, k₀, heventual⟩
  refine ⟨?_, hd, P, hdegree, hleading, k₀, ?_⟩
  · exact (ringKrullDim_eq_of_ringEquiv
      (Ideal.quotientEquiv I (conjugateIdeal g I)
        (conjugatePolynomial g) rfl)).symm.trans hdim
  · intro k hk
    rw [projectiveHilbertPiece_finrank_conjugate_eq]
    exact heventual k hk

end

end TranslatedDepthSeven

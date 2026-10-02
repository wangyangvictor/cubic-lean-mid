import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.Operations

/-!
# Noetherian induction on exceptional parameter loci

For an affine Noetherian parameter space, removing the principal open `D(s)`
from the closed stratum defined by `I` leaves the strictly smaller closed
stratum defined by `I + (s)`, provided `s ∉ I`.  Consequently a statement
proved over a dense principal open, with the same statement available on its
closed complement, holds on every parameter stratum by ordinary Noetherian
induction.

This concerns dimension of the parameter stratum.  It makes no assertion
that an individual exceptional fibre has smaller dimension.
-/

namespace TranslatedDepthSeven

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
/-- The ideal of the exceptional locus `V(I) \ D(s)` strictly contains the
ideal of the original stratum whenever `s` is nonzero on that stratum. -/
theorem lt_sup_span_singleton_of_notMem
    (I : Ideal R) {s : R} (hs : s ∉ I) :
    I < I ⊔ Ideal.span {s} := by
  refine lt_of_le_of_ne le_sup_left ?_
  intro hEq
  apply hs
  rw [hEq]
  exact (le_sup_right : Ideal.span {s} ≤ I ⊔ Ideal.span {s})
    (Ideal.subset_span (by simp))

/-- Noetherian parameter devissage in the form used by the relative
component construction.  At the stratum `I`, the induction hypothesis is
needed only for closed complements of principal opens `D(s)` with `s ∉ I`.
-/
theorem noetherian_parameter_induction_on_principal_open
    {P : Ideal R → Prop}
    (step : ∀ I : Ideal R,
      (∀ s : R, s ∉ I → P (I ⊔ Ideal.span {s})) → P I) :
    ∀ I : Ideal R, P I := by
  intro I
  induction I using IsNoetherian.induction with
  | hgt I hgt =>
      apply step I
      intro s hs
      exact hgt (I ⊔ Ideal.span {s})
        (lt_sup_span_singleton_of_notMem I hs)

end TranslatedDepthSeven

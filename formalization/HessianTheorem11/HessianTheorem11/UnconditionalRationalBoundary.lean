import HessianTheorem11.UnconditionalGeometricRelativeLimit
import HessianTheorem11.UnconditionalOrbitGlobal
import HessianTheorem11.UnconditionalOrbitFlags
import HessianTheorem11.UnconditionalOrbitConjugate
import HessianTheorem11.UnconditionalOrbitBoundary
import HessianTheorem11.UnconditionalBoundaryDimension
import HessianTheorem11.ReducedRationalBoundaryDescent

/-! Rational existing-limit descent for an actual nonclosed SL orbit.
Every geometric, optimization, and descent step is proved; this module
constructs the formerly external boundary interface without inputs. -/
noncomputable section
namespace HessianTheorem11.UnconditionalBoundary
open MvPolynomial RationalDescent PolynomialRestriction NonzeroLimitTransport
  ReducedRelative ReducedOrbitCoordinates UnconditionalOrbitGlobal

/-- A maximizing frame for the actual boundary of a rational form has an
exactly Galois-invariant weighted flag. Conjugation preserves its weight
vector, so the proved equal-norm uniqueness theorem applies directly. -/
theorem boundary_maximizing_rationalFlag {n d : ℕ} (hn : 0 < n)
    (F : RationalPolynomial n) (hF : F.IsHomogeneous d)
    (f : WeightFrame GeometricField n)
    (hf : SLMaximizingFrame d (geometricPolynomial F)
      (orbitBoundary (geometricPolynomial F)) f) : f.RationalFlag := by
  intro σ
  exact maximizing_flag_eq_of_norm_eq hn _ (hF.map _) _
    (UnconditionalOrbitBoundary.orbitBoundary_coefficientClosed _ (hF.map _))
    (orbitBoundary_invariant _ (hF.map _))
    (fun G hG => slOrbitClosure_homogeneous _ (hF.map _) G hG.1)
    (self_notMem_orbitBoundary _) (f.conjugate σ.toRingEquiv) f
    (boundary_maximizing_conjugate F hF f hf σ) hf rfl

/-- The universal rational boundary statement, now proved. For every
nonzero positive-degree rational homogeneous form with nonclosed geometric
SL orbit, there are rational coordinates and a nonzero sum-zero integer
weight on which every supported monomial has nonnegative weight. -/
def rationalRelativeBoundaryInput : RationalRelativeBoundaryInput where
  boundary F hd hF hne hclosed := by
    have hn := positive_dimension F hd hF hne
    let S := orbitBoundary (geometricPolynomial F)
    have hSc : coefficientClosed S :=
      UnconditionalOrbitBoundary.orbitBoundary_coefficientClosed _ (hF.map _)
    have hSi : slInvariant S := orbitBoundary_invariant _ (hF.map _)
    have hSh : ∀ G ∈ S, G.IsHomogeneous _ :=
      fun G hG => slOrbitClosure_homogeneous _ (hF.map _) G hG.1
    have hnot : geometricPolynomial F ∉ S := self_notMem_orbitBoundary _
    obtain ⟨G,hG⟩ := orbitBoundary_nonempty _ hclosed
    obtain ⟨f,hdet,_,hW,hpos⟩ :=
      UnconditionalGeometricRelativeLimit.exists_geometric_relative_frame hn
        _ (hF.map _) S hSc hSi hSh G hG hG.1 hnot
    obtain ⟨g,hg⟩ := exists_sl_maximizing_frame hn _ (hF.map _) S hSc hSi hSh hnot
      ⟨f,hdet,hW,hpos⟩
    exact ReducedRationalBoundary.rational_existing_limit_of_invariant_flag F g
      (boundary_maximizing_rationalFlag hn F hF g hg) hg.nonzero hg.admissible

end HessianTheorem11.UnconditionalBoundary

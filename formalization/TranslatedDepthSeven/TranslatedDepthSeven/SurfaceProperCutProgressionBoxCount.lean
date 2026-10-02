import TranslatedDepthSeven.RationalPrimeCurveProgressionBoxCount
import TranslatedDepthSeven.SurfaceAuxiliaryCurveComponentCover

/-! Elementary progression counts on proper surface cuts, with all prime
curve components and their degrees constructed internally. The constants
depend only on the displayed degrees and the number of cutting forms. -/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 2500000

/-- A finite proper-cut family has at most d*e*#A*(2B+1) progression points.
This is a coarse curve count, not the stronger smooth-surface estimate. -/
theorem card_surface_progression_cutFamily_le
    {N d e B m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hdegree : HasProjectiveDimensionDegree I 2 d)
    (A : Finset (MvPolynomial (Fin (N + 1)) ℚ))
    (hA : ∀ G ∈ A, G.IsHomogeneous e ∧ G ∉ I)
    (u : Fin N → ℤ) (S : Finset (Fin N → ℤ))
    (hsource : ∀ z ∈ S,
      (fun i => (progressionHomogeneousPoint u m z i : ℚ)) ∈ affineIdealZeroLocus I)
    (hcut : ∀ z ∈ S, ∃ G ∈ A,
      eval (fun i => (progressionHomogeneousPoint u m z i : ℚ)) G = 0)
    (hbox : ∀ z ∈ S, ∀ i, (z i).natAbs ≤ B) :
    S.card ≤ d * e * A.card * (2 * B + 1) := by
  classical
  obtain ⟨C, degree, hcert, hmass, _hcard, hcover⟩ :=
    exists_surfaceAuxiliary_primeCurve_cover I hprime hhom hdegree A hA
  let points : Ideal (MvPolynomial (Fin (N + 1)) ℚ) → Finset (Fin N → ℤ) :=
    fun P => S.filter fun z =>
      (fun i => (progressionHomogeneousPoint u m z i : ℚ)) ∈ affineIdealZeroLocus P
  have hsub : S ⊆ C.biUnion points := by
    intro z hz
    obtain ⟨P, hPC, hzP⟩ := (hcover _).mpr ⟨hsource z hz, hcut z hz⟩
    exact Finset.mem_biUnion.mpr ⟨P, hPC, Finset.mem_filter.mpr ⟨hz, hzP⟩⟩
  calc
    S.card ≤ (C.biUnion points).card := Finset.card_le_card hsub
    _ ≤ ∑ P ∈ C, (points P).card := Finset.card_biUnion_le
    _ ≤ ∑ P ∈ C, degree P * (2 * B + 1) := by
      apply Finset.sum_le_sum
      intro P hPC
      obtain ⟨hp, hh, _, hd, _⟩ := hcert P hPC
      exact card_primeCurve_progression_box_le hm P hp hh hd u (points P)
        (fun z hz => (Finset.mem_filter.mp hz).2)
        (fun z hz => hbox z (Finset.mem_filter.mp hz).1)
    _ = (∑ P ∈ C, degree P) * (2 * B + 1) := (Finset.sum_mul _ _ _).symm
    _ ≤ d * e * A.card * (2 * B + 1) := Nat.mul_le_mul_right _ hmass

/-- One actual proper homogeneous cut of a prime surface has at most
d*e*(2B+1) progression points, uniformly in all coefficients and centers. -/
theorem card_surface_progression_properCut_le
    {N d e B m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hdegree : HasProjectiveDimensionDegree I 2 d)
    (G : MvPolynomial (Fin (N + 1)) ℚ) (hGhom : G.IsHomogeneous e) (hGnot : G ∉ I)
    (u : Fin N → ℤ) (S : Finset (Fin N → ℤ))
    (hsource : ∀ z ∈ S,
      (fun i => (progressionHomogeneousPoint u m z i : ℚ)) ∈ affineIdealZeroLocus I)
    (hcut : ∀ z ∈ S,
      eval (fun i => (progressionHomogeneousPoint u m z i : ℚ)) G = 0)
    (hbox : ∀ z ∈ S, ∀ i, (z i).natAbs ≤ B) :
    S.card ≤ d * e * (2 * B + 1) := by
  classical
  have h := card_surface_progression_cutFamily_le hm I hprime hhom hdegree {G}
    (by intro f hf; simpa only [Finset.mem_singleton.mp hf] using And.intro hGhom hGnot)
    u S hsource (fun z hz => ⟨G, Finset.mem_singleton_self G, hcut z hz⟩) hbox
  simpa using h

end
end TranslatedDepthSeven

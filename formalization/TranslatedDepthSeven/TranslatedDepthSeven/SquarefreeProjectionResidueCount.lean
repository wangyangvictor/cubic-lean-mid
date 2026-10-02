import TranslatedDepthSeven.FiniteProjectionResidueCount
import TranslatedDepthSeven.SquarefreeResidueCount

/-!
# From local coordinate fibres to a square-free residue count

This file composes two literal finite counting statements.  At each prime
`p` in `P`, the local residue set is a `Finset` in `(ZMod p)^N`, and a
specified projection to `d` coordinates has fibres of cardinality at most
`D`.  The local bound `D * p^d` follows from summing those fibres.  Exact
Chinese remaindering then gives the product bound for the global residue set
defined by requiring all of the stated local conditions.

The coordinate projection is allowed to depend on the prime.  Taking it to
be constant gives the special case of one fixed coordinate projection at
every prime.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- Fibre bounds for arbitrary explicitly specified local maps imply the
exact square-free product estimate.  This includes linear and affine-linear
Noether-normalisation maps, and the map may vary with the prime. -/
theorem card_squarefreePrime_crtGlobalResidues_le_of_map_fibers
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (N d D : ℕ)
    (projection : ∀ p : P,
      (Fin N → ZMod (p : ℕ)) → (Fin d → ZMod (p : ℕ)))
    (R : ∀ p : P, Finset (Fin N → ZMod (p : ℕ)))
    (hfibre : ∀ (_p : P) (y : Fin d → ZMod (_p : ℕ)),
      (finiteMapFiber (projection _p) (R _p) y).card ≤ D) :
    (crtGlobalResidues (fun p : P ↦ (p : ℕ))
      (primeSubtype_pairwise_coprime hprime)
      (primeSubtype_ne_zero hprime) N R).card ≤
      D ^ P.card * (primeProduct P) ^ d := by
  apply card_squarefreePrime_crtGlobalResidues_le P hprime N d D R
  intro p
  exact card_zmod_finiteSet_le_of_map_fibers_le
    (hprime p p.property) (projection p) (R p) (hfibre p)

/-- The arbitrary-map form with the fixed local factor absorbed into
H^epsilon at logarithmic reservoir depth. -/
theorem card_squarefreePrime_crtGlobalResidues_cast_le_rpow_mul_of_map_fibers
    {M0 ε H : ℝ} (hM0 : 0 ≤ M0) (hε : 0 < ε)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (N d D : ℕ) (hD : 1 ≤ D)
    (hPcard : P.card ≤ reservoirDepth M0 H)
    (hH : reservoirSubpowerThreshold M0 (D : ℝ) ε ≤ H)
    (projection : ∀ p : P,
      (Fin N → ZMod (p : ℕ)) → (Fin d → ZMod (p : ℕ)))
    (R : ∀ p : P, Finset (Fin N → ZMod (p : ℕ)))
    (hfibre : ∀ (_p : P) (y : Fin d → ZMod (_p : ℕ)),
      (finiteMapFiber (projection _p) (R _p) y).card ≤ D) :
    ((crtGlobalResidues (fun p : P ↦ (p : ℕ))
      (primeSubtype_pairwise_coprime hprime)
      (primeSubtype_ne_zero hprime) N R).card : ℝ) ≤
      H ^ ε * (primeProduct P : ℝ) ^ d := by
  apply card_squarefreePrime_crtGlobalResidues_cast_le_rpow_mul
    hM0 hε P hprime N d D hD hPcard hH R
  intro p
  exact card_zmod_finiteSet_le_of_map_fibers_le
    (hprime p p.property) (projection p) (R p) (hfibre p)

/-- Fibre bounds for explicitly given local residue sets imply the exact
square-free product estimate.  The set on the left is the literal set of
vectors modulo `∏ p ∈ P, p` whose reduction at every `p ∈ P` lies in `R p`.
-/
theorem card_squarefreePrime_crtGlobalResidues_le_of_projection_fibers
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (N d D : ℕ)
    (coordinates : P → Fin d → Fin N)
    (R : ∀ p : P, Finset (Fin N → ZMod (p : ℕ)))
    (hfibre : ∀ (_p : P) (y : Fin d → ZMod (_p : ℕ)),
      (finiteCoordinateProjectionFiber (coordinates _p) (R _p) y).card ≤ D) :
    (crtGlobalResidues (fun p : P ↦ (p : ℕ))
      (primeSubtype_pairwise_coprime hprime)
      (primeSubtype_ne_zero hprime) N R).card ≤
      D ^ P.card * (primeProduct P) ^ d := by
  apply card_squarefreePrime_crtGlobalResidues_le P hprime N d D R
  intro p
  exact card_zmod_finiteSet_le_of_coordinateProjection_fibers_le
    (hprime p p.property) (coordinates p) (R p) (hfibre p)

/-- The same concrete fibre-to-CRT implication with the fixed factor
`D^(#P)` absorbed into `H^ε` by the logarithmic reservoir-depth bound.
-/
theorem card_squarefreePrime_crtGlobalResidues_cast_le_rpow_mul_of_projection_fibers
    {M0 ε H : ℝ} (hM0 : 0 ≤ M0) (hε : 0 < ε)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (N d D : ℕ) (hD : 1 ≤ D)
    (hPcard : P.card ≤ reservoirDepth M0 H)
    (hH : reservoirSubpowerThreshold M0 (D : ℝ) ε ≤ H)
    (coordinates : P → Fin d → Fin N)
    (R : ∀ p : P, Finset (Fin N → ZMod (p : ℕ)))
    (hfibre : ∀ (_p : P) (y : Fin d → ZMod (_p : ℕ)),
      (finiteCoordinateProjectionFiber (coordinates _p) (R _p) y).card ≤ D) :
    ((crtGlobalResidues (fun p : P ↦ (p : ℕ))
      (primeSubtype_pairwise_coprime hprime)
      (primeSubtype_ne_zero hprime) N R).card : ℝ) ≤
      H ^ ε * (primeProduct P : ℝ) ^ d := by
  apply card_squarefreePrime_crtGlobalResidues_cast_le_rpow_mul
    hM0 hε P hprime N d D hD hPcard hH R
  intro p
  exact card_zmod_finiteSet_le_of_coordinateProjection_fibers_le
    (hprime p p.property) (coordinates p) (R p) (hfibre p)

end

end TranslatedDepthSeven

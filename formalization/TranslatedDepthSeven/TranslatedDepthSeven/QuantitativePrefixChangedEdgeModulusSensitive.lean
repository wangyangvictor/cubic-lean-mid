import TranslatedDepthSeven.FixedSurfaceQuantitativePrefixEdgeSum
import TranslatedDepthSeven.PrimeSubsetPrefixReservoirBridge

/-!
# Modulus-sensitive changed-edge bounds

The old changed-edge estimate replaced every inverse-modulus determinant
degree by the modulus-one root degree before multiplying by the square of
the edge lcm.  This loses the cancellation which makes the squarefree term
small.

Here a point in a nonempty changed-edge cell supplies more structure.  Both
edge endpoints survive for that point, and the larger endpoint extends
inside the same allowed prime set to a full-depth terminal vertex.  Hence
the edge lcm is bounded by any uniform upper bound for terminal moduli.
Keeping the one new edge prime visible then gives the exact cancellation

`(pq)^2 (1 + A/q) (1 + A/(pq))
   = (pq)^2 + A(pq)p + A(pq) + A^2 p`.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra

local instance quantitativePrefixModulusSensitivePropDecidable
    (p : Prop) : Decidable p := Classical.propDecidable p

namespace PrimeSubsetPrefix

/-- A surviving prefix can be extended, inside the same surviving prime
set, to a terminal prefix of any available target depth. -/
theorem exists_fullDepth_survivingPrefix_extending
    {P Q : Finset ℕ} {depth : ℕ}
    (hQP : Q ⊆ P) (hroom : depth ≤ Q.card)
    (v : Vertex P depth) (hv : v ∈ survivingVertices P Q depth) :
    ∃ t : Vertex P depth,
      t ∈ survivingVertices P Q depth ∧
      t.1.card = depth ∧ v.1 ⊆ t.1 := by
  classical
  have hvQ : v.1 ⊆ Q := (mem_survivingVertices_iff v).mp hv
  have hvCard : v.1.card ≤ depth := (mem_vertices.mp v.2).2
  obtain ⟨s, hvs, hsQ, hsCard⟩ :=
    Finset.exists_subsuperset_card_eq hvQ hvCard hroom
  have hsP : s ⊆ P := hsQ.trans hQP
  let t : Vertex P depth :=
    ⟨s, mem_vertices.mpr ⟨hsP, hsCard.le⟩⟩
  refine ⟨t, ?_, hsCard, ?_⟩
  · exact (mem_survivingVertices_iff t).mpr hsQ
  · exact hvs

/-- The modulus of an extendible surviving prefix divides the modulus of
the chosen full-depth extension. -/
theorem exists_fullDepth_survivingPrefix_modulus_multiple
    {P Q : Finset ℕ} {depth : ℕ}
    (hQP : Q ⊆ P) (hroom : depth ≤ Q.card)
    (v : Vertex P depth) (hv : v ∈ survivingVertices P Q depth) :
    ∃ t : Vertex P depth,
      t ∈ survivingVertices P Q depth ∧
      t.1.card = depth ∧ modulus v ∣ modulus t := by
  obtain ⟨t, ht, htCard, hvt⟩ :=
    exists_fullDepth_survivingPrefix_extending hQP hroom v hv
  refine ⟨t, ht, htCard, ?_⟩
  exact Finset.prod_dvd_prod_of_subset v.1 t.1 id hvt

end PrimeSubsetPrefix

/-- A point in a changed-edge cell produces a full-depth terminal prefix
whose modulus is a multiple of the edge lcm. -/
theorem exists_terminalPrefix_multiple_of_changedEdgeLcm
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    {P : Finset ℕ} {depth : ℕ}
    (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
        MvPolynomial (Fin 4) ℚ)
    (u : Fin 3 → ℤ) (m : ℕ) (X : Finset (Fin 3 → ℤ))
    (allowed : (Fin 3 → ℤ) → Finset ℕ)
    (hallowed : ∀ z ∈ X, allowed z ⊆ P)
    (hroom : ∀ z ∈ X, depth ≤ (allowed z).card)
    (v w : PrimeSubsetPrefix.Vertex P depth)
    {z : Fin 3 → ℤ}
    (hz : z ∈ quantitativePrefixChangedEdgeCell sourceEquations auxiliary
      u m X allowed v w) :
    ∃ t : PrimeSubsetPrefix.Vertex P depth,
      t ∈ PrimeSubsetPrefix.survivingVertices P (allowed z) depth ∧
      t.1.card = depth ∧
      Nat.lcm (PrimeSubsetPrefix.modulus v)
        (PrimeSubsetPrefix.modulus w) ∣ PrimeSubsetPrefix.modulus t := by
  have hzX : z ∈ X := (Finset.mem_filter.mp hz).1
  have hzdata := (Finset.mem_filter.mp hz).2
  have hv := hzdata.1
  have hw := hzdata.2.1
  have hadj := hzdata.2.2.1
  obtain ⟨p, hp, hfactor⟩ :=
    PrimeSubsetPrefix.adjacent_modulus_factor hadj
  rcases hfactor with ⟨_hmod, hlcm⟩ | ⟨_hmod, hlcm⟩
  · obtain ⟨t, ht, htCard, hwt⟩ :=
      PrimeSubsetPrefix.exists_fullDepth_survivingPrefix_modulus_multiple
        (hallowed z hzX) (hroom z hzX) w hw
    refine ⟨t, ht, htCard, ?_⟩
    rw [hlcm]
    exact hwt
  · obtain ⟨t, ht, htCard, hvt⟩ :=
      PrimeSubsetPrefix.exists_fullDepth_survivingPrefix_modulus_multiple
        (hallowed z hzX) (hroom z hzX) v hv
    refine ⟨t, ht, htCard, ?_⟩
    rw [hlcm]
    exact hvt

/-- A supplied upper bound for all pointwise terminal moduli therefore
bounds the lcm on every nonempty changed-edge cell. -/
theorem changedEdgeLcm_le_terminalModulusCap
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    {P : Finset ℕ} {depth : ℕ}
    (hP : ∀ p ∈ P, p.Prime)
    (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
        MvPolynomial (Fin 4) ℚ)
    (u : Fin 3 → ℤ) (m : ℕ) (X : Finset (Fin 3 → ℤ))
    (allowed : (Fin 3 → ℤ) → Finset ℕ)
    (hallowed : ∀ z ∈ X, allowed z ⊆ P)
    (hroom : ∀ z ∈ X, depth ≤ (allowed z).card)
    (Q : ℕ)
    (hterminal : ∀ z ∈ X,
      ∀ t ∈ PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
        t.1.card = depth → PrimeSubsetPrefix.modulus t ≤ Q)
    (v w : PrimeSubsetPrefix.Vertex P depth)
    {z : Fin 3 → ℤ}
    (hz : z ∈ quantitativePrefixChangedEdgeCell sourceEquations auxiliary
      u m X allowed v w) :
    Nat.lcm (PrimeSubsetPrefix.modulus v)
      (PrimeSubsetPrefix.modulus w) ≤ Q := by
  have hzX : z ∈ X := (Finset.mem_filter.mp hz).1
  obtain ⟨t, ht, htCard, hdiv⟩ :=
    exists_terminalPrefix_multiple_of_changedEdgeLcm
      sourceEquations auxiliary u m X allowed hallowed hroom v w hz
  have htPrime : ∀ p ∈ t.1, p.Prime := by
    intro p hp
    exact hP p ((PrimeSubsetPrefix.mem_vertices.mp t.2).1 hp)
  have htPos : 0 < PrimeSubsetPrefix.modulus t :=
    Nat.pos_of_ne_zero (primeProduct_ne_zero htPrime)
  exact (Nat.le_of_dvd htPos hdiv).trans
    (hterminal z hzX t ht htCard)

/-- Exact inverse-modulus cancellation for one oriented prefix edge. -/
theorem adjacentInverseModulusCancellation
    (A p q Q R : ℝ)
    (hA : 0 ≤ A) (hp : 0 < p) (hq : 0 < q)
    (hpR : p ≤ R) (hpqQ : p * q ≤ Q) :
    (p * q) ^ (2 : ℕ) * (1 + A / q) * (1 + A / (p * q)) ≤
      Q ^ (2 : ℕ) + A * Q * R + A * Q + A ^ (2 : ℕ) * R := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hpq : 0 < p * q := mul_pos hp hq
  have hQ : 0 ≤ Q := (le_trans hpq.le hpqQ)
  have hR : 0 ≤ R := (le_trans hp.le hpR)
  have hexact :
      (p * q) ^ (2 : ℕ) * (1 + A / q) * (1 + A / (p * q)) =
        (p * q) ^ (2 : ℕ) + A * (p * q) * p +
          A * (p * q) + A ^ (2 : ℕ) * p := by
    field_simp [hp0, hq0]
    ring
  rw [hexact]
  have hsq : (p * q) ^ (2 : ℕ) ≤ Q ^ (2 : ℕ) :=
    pow_le_pow_left₀ hpq.le hpqQ 2
  have hcross : A * (p * q) * p ≤ A * Q * R := by gcongr
  have hlinear : A * (p * q) ≤ A * Q := by gcongr
  have hquad : A ^ (2 : ℕ) * p ≤ A ^ (2 : ℕ) * R := by gcongr
  linarith

/-- The same cancellation with two quantities satisfying the inverse-
modulus degree bounds. -/
theorem adjacentInverseModulusDegreeProductCancellation
    (A p q Q R K S Esmall Elarge : ℝ)
    (hA : 0 ≤ A) (hp : 0 < p) (hq : 0 < q)
    (hK : 0 ≤ K) (hS : 0 ≤ S)
    (hElarge : 0 ≤ Elarge)
    (hpR : p ≤ R) (hpqQ : p * q ≤ Q)
    (hsmall : Esmall ≤ K * S * (1 + A / q))
    (hlarge : Elarge ≤ K * S * (1 + A / (p * q))) :
    (p * q) ^ (2 : ℕ) * Esmall * Elarge ≤
      K ^ (2 : ℕ) * S ^ (2 : ℕ) *
        (Q ^ (2 : ℕ) + A * Q * R + A * Q + A ^ (2 : ℕ) * R) := by
  have hsmallFactor : 0 ≤ 1 + A / q := by positivity
  have hlargeFactor : 0 ≤ 1 + A / (p * q) := by positivity
  have hsmallRhs : 0 ≤ K * S * (1 + A / q) := by positivity
  have hprod : Esmall * Elarge ≤
      (K * S * (1 + A / q)) * (K * S * (1 + A / (p * q))) :=
    mul_le_mul hsmall hlarge hElarge hsmallRhs
  have hcancel := adjacentInverseModulusCancellation
    A p q Q R hA hp hq hpR hpqQ
  calc
    (p * q) ^ (2 : ℕ) * Esmall * Elarge ≤
        (p * q) ^ (2 : ℕ) *
          ((K * S * (1 + A / q)) *
            (K * S * (1 + A / (p * q)))) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hprod (sq_nonneg (p * q))
    _ = K ^ (2 : ℕ) * S ^ (2 : ℕ) *
        ((p * q) ^ (2 : ℕ) * (1 + A / q) *
          (1 + A / (p * q))) := by ring
    _ ≤ K ^ (2 : ℕ) * S ^ (2 : ℕ) *
        (Q ^ (2 : ℕ) + A * Q * R + A * Q + A ^ (2 : ℕ) * R) := by
      exact mul_le_mul_of_nonneg_left hcancel
        (mul_nonneg (sq_nonneg K) (sq_nonneg S))

/-- The fixed base degree can be absorbed without destroying the inverse
modulus in the block-degree estimate.  The explicit coefficient is
`d * (b+2)`. -/
theorem quantitativePrefixDegreeMass_le_inverseModulusScale
    {P : Finset ℕ} {depth : ℕ}
    (hP : ∀ p ∈ P, p.Prime)
    (d b H B : ℕ) (eta a : ℝ)
    (hH : (1 : ℝ) ≤ H) (heta : 0 ≤ eta)
    (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ)
    (hblock : ∀ t,
      ((blockDegree t : ℕ) : ℝ) ≤ 2 * (H : ℝ) ^ eta *
        (1 + (B : ℝ) ^ a /
          (PrimeSubsetPrefix.modulus t : ℝ)))
    (t : PrimeSubsetPrefix.Vertex P depth) :
    ((d * (b + blockDegree t) : ℕ) : ℝ) ≤
      (d : ℝ) * ((b : ℝ) + 2) * (H : ℝ) ^ eta *
        (1 + (B : ℝ) ^ a /
          (PrimeSubsetPrefix.modulus t : ℝ)) := by
  have htPrime : ∀ p ∈ t.1, p.Prime := by
    intro p hp
    exact hP p ((PrimeSubsetPrefix.mem_vertices.mp t.2).1 hp)
  have hmodPos : (0 : ℝ) < PrimeSubsetPrefix.modulus t := by
    exact_mod_cast Nat.pos_of_ne_zero (primeProduct_ne_zero htPrime)
  let S : ℝ := (H : ℝ) ^ eta
  let factor : ℝ :=
    1 + (B : ℝ) ^ a / (PrimeSubsetPrefix.modulus t : ℝ)
  have hS : 1 ≤ S := by
    exact Real.one_le_rpow hH heta
  have hfactor : 1 ≤ factor := by
    dsimp only [factor]
    have hdiv : 0 ≤ (B : ℝ) ^ a /
        (PrimeSubsetPrefix.modulus t : ℝ) := div_nonneg (by positivity) hmodPos.le
    linarith
  have hSfactor : 1 ≤ S * factor := by
    have := mul_le_mul hS hfactor (by norm_num : (0 : ℝ) ≤ 1)
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) hS)
    simpa using this
  have hb : 0 ≤ (b : ℝ) := by positivity
  have hbscale : (b : ℝ) ≤ (b : ℝ) * (S * factor) := by
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hSfactor)]
  have hk : (blockDegree t : ℝ) ≤ 2 * S * factor := by
    simpa only [S, factor] using hblock t
  have hsum :
      (b : ℝ) + (blockDegree t : ℝ) ≤
        ((b : ℝ) + 2) * S * factor := by
    calc
      (b : ℝ) + (blockDegree t : ℝ) ≤
          (b : ℝ) + 2 * S * factor := add_le_add (le_refl _) hk
      _ ≤ ((b : ℝ) + 2) * S * factor := by
        nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg d)
  simpa only [Nat.cast_mul, Nat.cast_add, S, factor, mul_assoc] using hmul

/-- On one adjacent prefix pair, retain the inverse-modulus cancellation in
the product of the two actual natural cutting degrees. -/
theorem adjacentPrefixModulusDegreeProduct_le
    {P : Finset ℕ} {depth : ℕ}
    (hP : ∀ p ∈ P, p.Prime)
    {v w : PrimeSubsetPrefix.Vertex P depth}
    (hvw : (PrimeSubsetPrefix.graph P depth).Adj v w)
    (d b H B Q R : ℕ) (eta a : ℝ)
    (hH : (1 : ℝ) ≤ H) (heta : 0 ≤ eta)
    (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ)
    (hblock : ∀ t,
      ((blockDegree t : ℕ) : ℝ) ≤ 2 * (H : ℝ) ^ eta *
        (1 + (B : ℝ) ^ a /
          (PrimeSubsetPrefix.modulus t : ℝ)))
    (hlcmQ : Nat.lcm (PrimeSubsetPrefix.modulus v)
      (PrimeSubsetPrefix.modulus w) ≤ Q)
    (hprimeCap : ∀ p ∈ P, p ≤ R) :
    (Nat.lcm (PrimeSubsetPrefix.modulus v)
        (PrimeSubsetPrefix.modulus w) : ℝ) ^ (2 : ℕ) *
      ((d * (b + blockDegree v) : ℕ) : ℝ) *
      ((d * (b + blockDegree w) : ℕ) : ℝ) ≤
      ((d : ℝ) * ((b : ℝ) + 2)) ^ (2 : ℕ) *
        (H : ℝ) ^ (2 * eta) *
        ((Q : ℝ) ^ (2 : ℕ) +
          (B : ℝ) ^ a * (Q : ℝ) * (R : ℝ) +
          (B : ℝ) ^ a * (Q : ℝ) +
          ((B : ℝ) ^ a) ^ (2 : ℕ) * (R : ℝ)) := by
  let A : ℝ := (B : ℝ) ^ a
  let K : ℝ := (d : ℝ) * ((b : ℝ) + 2)
  let S : ℝ := (H : ℝ) ^ eta
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hS : 0 ≤ S := by
    dsimp only [S]
    positivity
  have hEv : 0 ≤ ((d * (b + blockDegree v) : ℕ) : ℝ) := by positivity
  have hEw : 0 ≤ ((d * (b + blockDegree w) : ℕ) : ℝ) := by positivity
  have hdegV := quantitativePrefixDegreeMass_le_inverseModulusScale
    hP d b H B eta a hH heta blockDegree hblock v
  have hdegW := quantitativePrefixDegreeMass_le_inverseModulusScale
    hP d b H B eta a hH heta blockDegree hblock w
  have hHpos : (0 : ℝ) < H := lt_of_lt_of_le zero_lt_one hH
  have hSsq : S ^ (2 : ℕ) = (H : ℝ) ^ (2 * eta) := by
    dsimp only [S]
    rw [pow_two, ← Real.rpow_add hHpos]
    congr 1
    ring
  obtain ⟨p, hpP, hfactor⟩ :=
    PrimeSubsetPrefix.adjacent_modulus_factor hvw
  have hp : (0 : ℝ) < p := by exact_mod_cast (hP p hpP).pos
  have hpR : (p : ℝ) ≤ R := by exact_mod_cast hprimeCap p hpP
  rcases hfactor with ⟨hw, hlcm⟩ | ⟨hv, hlcm⟩
  · have hq : (0 : ℝ) < PrimeSubsetPrefix.modulus v := by
      have hvPrime : ∀ r ∈ v.1, r.Prime := by
        intro r hr
        exact hP r ((PrimeSubsetPrefix.mem_vertices.mp v.2).1 hr)
      exact_mod_cast Nat.pos_of_ne_zero (primeProduct_ne_zero hvPrime)
    have hwQ : PrimeSubsetPrefix.modulus w ≤ Q := by
      simpa only [hlcm] using hlcmQ
    have hpqQ : (p : ℝ) * (PrimeSubsetPrefix.modulus v : ℝ) ≤ Q := by
      exact_mod_cast (show p * PrimeSubsetPrefix.modulus v ≤ Q by
        simpa only [hw] using hwQ)
    have hlarge : ((d * (b + blockDegree w) : ℕ) : ℝ) ≤
        K * S * (1 + A /
          ((p : ℝ) * (PrimeSubsetPrefix.modulus v : ℝ))) := by
      simpa only [K, S, A, hw, Nat.cast_mul, mul_assoc] using hdegW
    have hsmall : ((d * (b + blockDegree v) : ℕ) : ℝ) ≤
        K * S * (1 + A / (PrimeSubsetPrefix.modulus v : ℝ)) := by
      simpa only [K, S, A, mul_assoc] using hdegV
    have hcancel := adjacentInverseModulusDegreeProductCancellation
      A (p : ℝ) (PrimeSubsetPrefix.modulus v : ℝ) (Q : ℝ) (R : ℝ)
      K S
      ((d * (b + blockDegree v) : ℕ) : ℝ)
      ((d * (b + blockDegree w) : ℕ) : ℝ)
      hA hp hq hK hS hEw hpR hpqQ hsmall hlarge
    rw [hlcm, hw, Nat.cast_mul]
    simpa only [A, K, hSsq] using hcancel
  · have hq : (0 : ℝ) < PrimeSubsetPrefix.modulus w := by
      have hwPrime : ∀ r ∈ w.1, r.Prime := by
        intro r hr
        exact hP r ((PrimeSubsetPrefix.mem_vertices.mp w.2).1 hr)
      exact_mod_cast Nat.pos_of_ne_zero (primeProduct_ne_zero hwPrime)
    have hvQ : PrimeSubsetPrefix.modulus v ≤ Q := by
      simpa only [hlcm] using hlcmQ
    have hpqQ : (p : ℝ) * (PrimeSubsetPrefix.modulus w : ℝ) ≤ Q := by
      exact_mod_cast (show p * PrimeSubsetPrefix.modulus w ≤ Q by
        simpa only [hv] using hvQ)
    have hlarge : ((d * (b + blockDegree v) : ℕ) : ℝ) ≤
        K * S * (1 + A /
          ((p : ℝ) * (PrimeSubsetPrefix.modulus w : ℝ))) := by
      simpa only [K, S, A, hv, Nat.cast_mul, mul_assoc] using hdegV
    have hsmall : ((d * (b + blockDegree w) : ℕ) : ℝ) ≤
        K * S * (1 + A / (PrimeSubsetPrefix.modulus w : ℝ)) := by
      simpa only [K, S, A, mul_assoc] using hdegW
    have hcancel := adjacentInverseModulusDegreeProductCancellation
      A (p : ℝ) (PrimeSubsetPrefix.modulus w : ℝ) (Q : ℝ) (R : ℝ)
      K S
      ((d * (b + blockDegree w) : ℕ) : ℝ)
      ((d * (b + blockDegree v) : ℕ) : ℝ)
      hA hp hq hK hS hEv hpR hpqQ hsmall hlarge
    have hcancel' :
        ((p : ℝ) * (PrimeSubsetPrefix.modulus w : ℝ)) ^ (2 : ℕ) *
          ((d * (b + blockDegree v) : ℕ) : ℝ) *
          ((d * (b + blockDegree w) : ℕ) : ℝ) ≤
        K ^ (2 : ℕ) * S ^ (2 : ℕ) *
          ((Q : ℝ) ^ (2 : ℕ) + A * (Q : ℝ) * (R : ℝ) +
            A * (Q : ℝ) + A ^ (2 : ℕ) * (R : ℝ)) := by
      calc
        ((p : ℝ) * (PrimeSubsetPrefix.modulus w : ℝ)) ^ (2 : ℕ) *
            ((d * (b + blockDegree v) : ℕ) : ℝ) *
            ((d * (b + blockDegree w) : ℕ) : ℝ) =
          ((p : ℝ) * (PrimeSubsetPrefix.modulus w : ℝ)) ^ (2 : ℕ) *
            ((d * (b + blockDegree w) : ℕ) : ℝ) *
            ((d * (b + blockDegree v) : ℕ) : ℝ) := by ring
        _ ≤ _ := hcancel
    rw [hlcm, hv, Nat.cast_mul]
    simpa only [A, K, hSsq] using hcancel'

/-- Explicit real majorant for one changed edge after retaining both
inverse-modulus degree factors. -/
def quantitativePrefixModulusSensitiveEdgeMajorant
    (Delta depth d b H B Q R : ℕ) (eta a : ℝ) : ℝ :=
  ((max 1 Delta : ℕ) : ℝ) ^ depth *
    (((d : ℝ) * ((b : ℝ) + 2)) ^ (2 : ℕ) *
      (H : ℝ) ^ (2 * eta) *
      ((Q : ℝ) ^ (2 : ℕ) +
        (B : ℝ) ^ a * (Q : ℝ) * (R : ℝ) +
        (B : ℝ) ^ a * (Q : ℝ) +
        ((B : ℝ) ^ a) ^ (2 : ℕ) * (R : ℝ)))

/-- A pointwise changed-edge bound with terminal-modulus and prime caps.
The proof uses a point of the cell only to obtain the terminal extension;
an empty cell is handled without any artificial modulus hypothesis. -/
theorem card_quantitativePrefixChangedEdgeCell_le_modulusSensitive
    {d b H B Q R Delta : ℕ} {eta a : ℝ}
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    {P : Finset ℕ} {depth : ℕ}
    (hP : ∀ p ∈ P, p.Prime)
    (u : Fin 3 → ℤ) (m : ℕ) (X : Finset (Fin 3 → ℤ))
    (allowed : (Fin 3 → ℤ) → Finset ℕ)
    (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ)
    (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
        MvPolynomial (Fin 4) ℚ)
    (hH : (1 : ℝ) ≤ H) (heta : 0 ≤ eta)
    (hallowed : ∀ z ∈ X, allowed z ⊆ P)
    (hroom : ∀ z ∈ X, depth ≤ (allowed z).card)
    (hterminal : ∀ z ∈ X,
      ∀ t ∈ PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
        t.1.card = depth → PrimeSubsetPrefix.modulus t ≤ Q)
    (hprimeCap : ∀ p ∈ P, p ≤ R)
    (hblock : ∀ t,
      ((blockDegree t : ℕ) : ℝ) ≤ 2 * (H : ℝ) ^ eta *
        (1 + (B : ℝ) ^ a /
          (PrimeSubsetPrefix.modulus t : ℝ)))
    (v w : PrimeSubsetPrefix.Vertex P depth)
    (hcell :
      (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
        u m X allowed v w).card ≤
        (Delta ^ (Nat.lcm (PrimeSubsetPrefix.modulus v)
          (PrimeSubsetPrefix.modulus w)).primeFactors.card *
          Nat.lcm (PrimeSubsetPrefix.modulus v)
            (PrimeSubsetPrefix.modulus w) ^ 2) *
          ((d * (b + blockDegree v)) *
            (d * (b + blockDegree w)))) :
    ((quantitativePrefixChangedEdgeCell sourceEquations auxiliary
      u m X allowed v w).card : ℝ) ≤
      quantitativePrefixModulusSensitiveEdgeMajorant
        Delta depth d b H B Q R eta a := by
  classical
  by_cases hnonempty :
      (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
        u m X allowed v w).Nonempty
  · obtain ⟨z, hz⟩ := hnonempty
    have hadj : (PrimeSubsetPrefix.graph P depth).Adj v w :=
      (Finset.mem_filter.mp hz).2.2.2.1
    have hlcmQ := changedEdgeLcm_le_terminalModulusCap
      sourceEquations hP auxiliary u m X allowed hallowed hroom Q hterminal
        v w hz
    have harithmetic := adjacentPrefixModulusDegreeProduct_le
      hP hadj d b H B Q R eta a hH heta blockDegree hblock hlcmQ hprimeCap
    have hpf := PrimeSubsetPrefix.card_primeFactors_lcm_adjacent_le hP hadj
    have hDelta : Delta ^
        (Nat.lcm (PrimeSubsetPrefix.modulus v)
          (PrimeSubsetPrefix.modulus w)).primeFactors.card ≤
        (max 1 Delta) ^ depth := by
      calc
        Delta ^ (Nat.lcm (PrimeSubsetPrefix.modulus v)
            (PrimeSubsetPrefix.modulus w)).primeFactors.card ≤
            (max 1 Delta) ^ (Nat.lcm (PrimeSubsetPrefix.modulus v)
              (PrimeSubsetPrefix.modulus w)).primeFactors.card :=
          Nat.pow_le_pow_left (le_max_right _ _) _
        _ ≤ (max 1 Delta) ^ depth :=
          Nat.pow_le_pow_right
            (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)) hpf
    have hDeltaReal :
        (Delta : ℝ) ^
            (Nat.lcm (PrimeSubsetPrefix.modulus v)
              (PrimeSubsetPrefix.modulus w)).primeFactors.card ≤
          ((max 1 Delta : ℕ) : ℝ) ^ depth := by
      exact_mod_cast hDelta
    have hcellReal :
        ((quantitativePrefixChangedEdgeCell sourceEquations auxiliary
          u m X allowed v w).card : ℝ) ≤
          (Delta : ℝ) ^
              (Nat.lcm (PrimeSubsetPrefix.modulus v)
                (PrimeSubsetPrefix.modulus w)).primeFactors.card *
            (Nat.lcm (PrimeSubsetPrefix.modulus v)
              (PrimeSubsetPrefix.modulus w) : ℝ) ^ (2 : ℕ) *
            ((d * (b + blockDegree v) : ℕ) : ℝ) *
            ((d * (b + blockDegree w) : ℕ) : ℝ) := by
      have hcellReal0 :
          ((quantitativePrefixChangedEdgeCell sourceEquations auxiliary
            u m X allowed v w).card : ℝ) ≤
            ((Delta : ℝ) ^
                (Nat.lcm (PrimeSubsetPrefix.modulus v)
                  (PrimeSubsetPrefix.modulus w)).primeFactors.card *
              (Nat.lcm (PrimeSubsetPrefix.modulus v)
                (PrimeSubsetPrefix.modulus w) : ℝ) ^ (2 : ℕ)) *
              (((d * (b + blockDegree v) : ℕ) : ℝ) *
                ((d * (b + blockDegree w) : ℕ) : ℝ)) := by
        exact_mod_cast hcell
      simpa only [mul_assoc] using hcellReal0
    calc
      ((quantitativePrefixChangedEdgeCell sourceEquations auxiliary
          u m X allowed v w).card : ℝ) ≤
          (Delta : ℝ) ^
              (Nat.lcm (PrimeSubsetPrefix.modulus v)
                (PrimeSubsetPrefix.modulus w)).primeFactors.card *
            ((Nat.lcm (PrimeSubsetPrefix.modulus v)
              (PrimeSubsetPrefix.modulus w) : ℝ) ^ (2 : ℕ) *
              ((d * (b + blockDegree v) : ℕ) : ℝ) *
              ((d * (b + blockDegree w) : ℕ) : ℝ)) := by
            simpa only [mul_assoc] using hcellReal
      _ ≤ ((max 1 Delta : ℕ) : ℝ) ^ depth *
          (((d : ℝ) * ((b : ℝ) + 2)) ^ (2 : ℕ) *
            (H : ℝ) ^ (2 * eta) *
            ((Q : ℝ) ^ (2 : ℕ) +
              (B : ℝ) ^ a * (Q : ℝ) * (R : ℝ) +
              (B : ℝ) ^ a * (Q : ℝ) +
              ((B : ℝ) ^ a) ^ (2 : ℕ) * (R : ℝ))) := by
        exact mul_le_mul hDeltaReal harithmetic (by positivity) (by positivity)
      _ = quantitativePrefixModulusSensitiveEdgeMajorant
          Delta depth d b H B Q R eta a := rfl
  · have hempty : quantitativePrefixChangedEdgeCell sourceEquations auxiliary
        u m X allowed v w = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    dsimp only [quantitativePrefixModulusSensitiveEdgeMajorant]
    positivity

/-- Sum the sharp pointwise estimate over the literal directed prefix graph.
No root-uniform edge majorant occurs in the conclusion. -/
theorem sum_card_quantitativePrefixChangedEdgeCell_le_modulusSensitive
    {d b H B Q R Delta : ℕ} {eta a : ℝ}
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    (P : Finset ℕ) (depth : ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (u : Fin 3 → ℤ) (m : ℕ) (X : Finset (Fin 3 → ℤ))
    (allowed : (Fin 3 → ℤ) → Finset ℕ)
    (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ)
    (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
        MvPolynomial (Fin 4) ℚ)
    (hH : (1 : ℝ) ≤ H) (heta : 0 ≤ eta)
    (hallowed : ∀ z ∈ X, allowed z ⊆ P)
    (hroom : ∀ z ∈ X, depth ≤ (allowed z).card)
    (hterminal : ∀ z ∈ X,
      ∀ t ∈ PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
        t.1.card = depth → PrimeSubsetPrefix.modulus t ≤ Q)
    (hprimeCap : ∀ p ∈ P, p ≤ R)
    (hblock : ∀ t,
      ((blockDegree t : ℕ) : ℝ) ≤ 2 * (H : ℝ) ^ eta *
        (1 + (B : ℝ) ^ a /
          (PrimeSubsetPrefix.modulus t : ℝ)))
    (hcell : ∀ v w : PrimeSubsetPrefix.Vertex P depth,
      (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
        u m X allowed v w).card ≤
        (Delta ^ (Nat.lcm (PrimeSubsetPrefix.modulus v)
          (PrimeSubsetPrefix.modulus w)).primeFactors.card *
          Nat.lcm (PrimeSubsetPrefix.modulus v)
            (PrimeSubsetPrefix.modulus w) ^ 2) *
          ((d * (b + blockDegree v)) *
            (d * (b + blockDegree w)))) :
    ((∑ v : PrimeSubsetPrefix.Vertex P depth,
      ∑ w : PrimeSubsetPrefix.Vertex P depth,
        (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
          u m X allowed v w).card : ℕ) : ℝ) ≤
      (PrimeSubsetPrefix.directedEdges P depth).card *
        quantitativePrefixModulusSensitiveEdgeMajorant
          Delta depth d b H B Q R eta a := by
  classical
  rw [sum_card_quantitativePrefixChangedEdgeCell_eq_directedEdges]
  norm_num only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat]
  calc
    ∑ e ∈ PrimeSubsetPrefix.directedEdges P depth,
        ((quantitativePrefixChangedEdgeCell sourceEquations auxiliary
          u m X allowed e.1 e.2).card : ℝ) ≤
      ∑ _e ∈ PrimeSubsetPrefix.directedEdges P depth,
        quantitativePrefixModulusSensitiveEdgeMajorant
          Delta depth d b H B Q R eta a := by
      apply Finset.sum_le_sum
      intro e he
      exact card_quantitativePrefixChangedEdgeCell_le_modulusSensitive
        sourceEquations hP u m X allowed blockDegree auxiliary hH heta
          hallowed hroom hterminal hprimeCap hblock e.1 e.2 (hcell e.1 e.2)
    _ = (PrimeSubsetPrefix.directedEdges P depth).card *
        quantitativePrefixModulusSensitiveEdgeMajorant
          Delta depth d b H B Q R eta a := by simp

/-- Direct squarefree-residual form of the modulus-sensitive global edge
bound.  This consumes the established pointwise geometric estimate and
retains the sharp arithmetic majorant. -/
theorem sum_card_quantitativePrefixChangedEdgeCell_le_squarefree_modulusSensitive
    {d b H B Q R : ℕ} {eta a : ℝ}
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    (hgeometricPrime : ((finiteEquationIdeal sourceEquations).map
      (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime)
    (hhom : (finiteEquationIdeal sourceEquations).IsHomogeneous
      (homogeneousSubmodule (Fin 4) ℚ))
    (hdegree : HasProjectiveDimensionDegree
      (finiteEquationIdeal sourceEquations) 2 d)
    (F : MvPolynomial (Fin 4) ℤ)
    (P : Finset ℕ) (depth : ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (m : ℕ) (hm : 0 < m) (hPm : ∀ p ∈ P, ¬ p ∣ m)
    (u : Fin 3 → ℤ) (X : Finset (Fin 3 → ℤ))
    (allowed : (Fin 3 → ℤ) → Finset ℕ)
    (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ)
    (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
        MvPolynomial (Fin 4) ℚ)
    (hH : (1 : ℝ) ≤ H) (heta : 0 ≤ eta)
    (hallowed : ∀ z ∈ X, allowed z ⊆ P)
    (hroom : ∀ z ∈ X, depth ≤ (allowed z).card)
    (hterminal : ∀ z ∈ X,
      ∀ t ∈ PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
        t.1.card = depth → PrimeSubsetPrefix.modulus t ≤ Q)
    (hprimeCap : ∀ p ∈ P, p ≤ R)
    (hblock : ∀ t,
      ((blockDegree t : ℕ) : ℝ) ≤ 2 * (H : ℝ) ^ eta *
        (1 + (B : ℝ) ^ a /
          (PrimeSubsetPrefix.modulus t : ℝ)))
    (hauxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      ∀ rho ∈ occupiedIntegralResidues (PrimeSubsetPrefix.modulus v) X,
        (auxiliary v rho).IsHomogeneous (b + blockDegree v) ∧
          auxiliary v rho ∉ finiteEquationIdeal sourceEquations)
    (hauxZero : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      ∀ z ∈ X, MvPolynomial.eval
        (fun i => (progressionHomogeneousPoint u m z i : ℚ))
          (auxiliary v (integralResidueVector z)) = 0)
    (hsource : ∀ z ∈ X,
      (fun i => (progressionHomogeneousPoint u m z i : ℚ)) ∈
        finiteAffineCommonZeroLocus sourceEquations)
    (hzero : ∀ z ∈ X,
      MvPolynomial.eval (progressionHomogeneousPoint u m z) F = 0)
    (hsmooth : ∀ z ∈ X, ∀ p ∈ P, ∃ i,
      (MvPolynomial.eval (fun j => u j + (m : ℤ) * z j)
        (MvPolynomial.pderiv i
          (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) :
    ((∑ v : PrimeSubsetPrefix.Vertex P depth,
      ∑ w : PrimeSubsetPrefix.Vertex P depth,
        (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
          u m X allowed v w).card : ℕ) : ℝ) ≤
      (PrimeSubsetPrefix.directedEdges P depth).card *
        quantitativePrefixModulusSensitiveEdgeMajorant
          (surfaceHypersurfaceFirstChartDehomogenize F).totalDegree
          depth d b H B Q R eta a := by
  apply sum_card_quantitativePrefixChangedEdgeCell_le_modulusSensitive
    sourceEquations P depth hP u m X allowed blockDegree auxiliary hH heta
      hallowed hroom hterminal hprimeCap hblock
  intro v w
  exact card_quantitativePrefixChangedEdgeCell_le_squarefree
    sourceEquations hgeometricPrime hhom hdegree F P depth hP m hm hPm
      u X allowed blockDegree auxiliary hauxiliary hauxZero hsource
      hzero hsmooth v w

end

end TranslatedDepthSeven

import CubicTenVariables.FixedLeadingFormCoefficientReduction
import CubicTenVariables.IrreducibleFromTopHomogeneousPart
import CubicTenVariables.Literature.HomogeneousHypersurfaceIntegralityOpen
import TranslatedDepthSeven.AbsoluteIrreducibility

/-!
# One fixed good-reduction integer for a fixed leading form

The sole geometric input is the explicitly parameterized
`HomogeneousHypersurfaceIntegralityOpen`. Applied to the fixed integral
homogeneous form `k`, it supplies an integer before any varying polynomial
`g` or rational scalar `c` is chosen. Multiplying by one fixed nonzero
coefficient of `k` produces a positive integer `D`.

If the degree-`d` component of `g` is a nonzero rational scalar multiple of
`k`, the corresponding integral coefficient `b` is nonzero and bounded by
the literal coefficient height of `g`. At every prime not dividing `D*b`,
the actual reduced degree-`d` component is geometrically irreducible and has
degree `d`. With the degree upper bound on `g`, the same exclusion also
gives geometric irreducibility of the full reduced polynomial. These are
good-reduction statements, not point-count estimates.
-/

set_option autoImplicit false
noncomputable section

namespace CubicTenVariables.FixedLeadingFormGoodReduction

open MvPolynomial
open TranslatedDepthSeven TranslatedDepthSeven.Published
open FixedLeadingFormCoefficientReduction

/-- Spreading for one fixed homogeneous equation. The integer is chosen
before the reduction field, and the conclusion states actual irreducibility
after extending coefficients to that field's algebraic closure. -/
theorem exists_fixed_irreducible_reduction_certificate
    (integralityOpen : Literature.HomogeneousHypersurfaceIntegralityOpen)
    {n d : ℕ} (hd : 1 ≤ d) (k : MvPolynomial (Fin n) ℤ)
    (hhom : k.IsHomogeneous d)
    (hirr : IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k)) :
    ∃ s : ℤ, s ≠ 0 ∧ ∀ (K : Type) [Field K], (s : K) ≠ 0 →
      (map (Int.castRingHom K) k).totalDegree = d ∧
      Irreducible (map (algebraMap K (AlgebraicClosure K))
        (map (Int.castRingHom K) k)) := by
  have hcomp : (algebraMap ℚ (AlgebraicClosure ℚ)).comp (Int.castRingHom ℚ) =
      Int.castRingHom (AlgebraicClosure ℚ) := RingHom.ext_int _ _
  have hgeo : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) k) := by
    change Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ))
      (map (Int.castRingHom ℚ) k)) at hirr
    simpa only [MvPolynomial.map_map, hcomp] using hirr
  have hdomain : IsDomain (MvPolynomial (Fin n) (AlgebraicClosure ℚ) ⧸
      Ideal.span {map (Int.castRingHom (AlgebraicClosure ℚ)) k}) := by
    apply (Ideal.Quotient.isDomain_iff_prime _).mpr
    exact (Ideal.span_singleton_prime hgeo.ne_zero).mpr
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hgeo)
  obtain ⟨s, hs, hgood⟩ := integralityOpen ℤ (AlgebraicClosure ℚ) n d hd
    (Int.castRingHom (AlgebraicClosure ℚ)) k hhom hgeo.ne_zero hdomain
  refine ⟨s, (fun hz => hs (by rw [hz, map_zero])), ?_⟩
  intro K _ hsK
  obtain ⟨hdegree, hdom⟩ := hgood K (Int.castRingHom K) hsK
  have hkK : map (Int.castRingHom K) k ≠ 0 := by
    intro hz
    rw [hz, totalDegree_zero] at hdegree
    omega
  have hkbar : map (algebraMap K (AlgebraicClosure K))
      (map (Int.castRingHom K) k) ≠ 0 := by
    exact fun hz => hkK ((map_injective _ (algebraMap K (AlgebraicClosure K)).injective)
      (by simpa only [map_zero] using hz))
  exact ⟨hdegree, ((Ideal.span_singleton_prime hkbar).mp
    ((Ideal.Quotient.isDomain_iff_prime _).mp hdom)).irreducible⟩

/-- The fixed coefficient and fixed positive integer are selected before
every varying polynomial and leading scalar. The only varying prime
exclusion is a literal nonzero coefficient of the homogeneous component. -/
theorem exists_fixed_leading_good_reduction
    (integralityOpen : Literature.HomogeneousHypersurfaceIntegralityOpen)
    {n d : ℕ} (hd : 1 ≤ d) (k : MvPolynomial (Fin n) ℤ)
    (hhom : k.IsHomogeneous d)
    (hirr : IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k)) :
    ∃ (μ : Fin n →₀ ℕ) (D : ℕ), 0 < D ∧ k.coeff μ ≠ 0 ∧
      ∀ (g : MvPolynomial (Fin n) ℤ) (c : ℚ), c ≠ 0 →
        map (Int.castRingHom ℚ) (homogeneousComponent d g) =
          C c * map (Int.castRingHom ℚ) k →
        (homogeneousComponent d g).coeff μ ≠ 0 ∧
        ((homogeneousComponent d g).coeff μ).natAbs ≤
          mvPolynomialCoefficientNatAbsMax g ∧
        ∀ (p : ℕ) [Fact p.Prime],
          ¬ (p : ℤ) ∣ (D : ℤ) * (homogeneousComponent d g).coeff μ →
          (homogeneousComponent d (map (Int.castRingHom (ZMod p)) g)).totalDegree = d ∧
          Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
            (homogeneousComponent d (map (Int.castRingHom (ZMod p)) g))) := by
  obtain ⟨s, hs, hgood⟩ := exists_fixed_irreducible_reduction_certificate
    integralityOpen hd k hhom hirr
  have hk : k ≠ 0 := by
    intro hz
    exact hirr.ne_zero (by rw [hz, map_zero])
  obtain ⟨μ, ha⟩ := MvPolynomial.exists_coeff_ne_zero hk
  let D : ℕ := (s * k.coeff μ).natAbs
  refine ⟨μ, D, Int.natAbs_pos.mpr (mul_ne_zero hs ha), ha, ?_⟩
  intro g c hc htop
  obtain ⟨hb, _hcross, hheight⟩ := top_coefficient_certificate μ htop hc ha
  refine ⟨hb, hheight, ?_⟩
  intro p _ hp
  have hsa : ¬ (p : ℤ) ∣ s * k.coeff μ := by
    intro hdiv
    have hD : (p : ℤ) ∣ (D : ℤ) := Int.dvd_natAbs.mpr hdiv
    exact hp (dvd_mul_of_dvd_left hD _)
  have hsK : (s : ZMod p) ≠ 0 := by
    intro hz
    exact hsa (dvd_mul_of_dvd_left
      ((ZMod.intCast_zmod_eq_zero_iff_dvd s p).mp hz) _)
  have haK : ((k.coeff μ : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    exact hsa (dvd_mul_of_dvd_right
      ((ZMod.intCast_zmod_eq_zero_iff_dvd (k.coeff μ) p).mp hz) _)
  have hbK : (((homogeneousComponent d g).coeff μ : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    exact hp (dvd_mul_of_dvd_right
      ((ZMod.intCast_zmod_eq_zero_iff_dvd ((homogeneousComponent d g).coeff μ) p).mp hz) _)
  have habK : ((k.coeff μ * (homogeneousComponent d g).coeff μ : ℤ) : ZMod p) ≠ 0 := by
    simpa only [Int.cast_mul] using mul_ne_zero haK hbK
  have hgeom := geometrically_irreducible_top_reduction μ htop habK
    (hgood (ZMod p) hsK).2
  have htopne : homogeneousComponent d (map (Int.castRingHom (ZMod p)) g) ≠ 0 := by
    intro hz
    exact hgeom.ne_zero (by rw [hz, map_zero])
  exact ⟨(homogeneousComponent_isHomogeneous d _).totalDegree htopne, hgeom⟩

/-- With the degree upper bound on the varying polynomial, the same fixed
integer controls geometric irreducibility of both its actual reduced top
component and the full reduced polynomial. -/
theorem exists_fixed_leading_full_good_reduction
    (integralityOpen : Literature.HomogeneousHypersurfaceIntegralityOpen)
    {n d : ℕ} (hd : 1 ≤ d) (k : MvPolynomial (Fin n) ℤ)
    (hhom : k.IsHomogeneous d)
    (hirr : IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k)) :
    ∃ (μ : Fin n →₀ ℕ) (D : ℕ), 0 < D ∧ k.coeff μ ≠ 0 ∧
      ∀ (g : MvPolynomial (Fin n) ℤ) (c : ℚ), c ≠ 0 →
        g.totalDegree ≤ d →
        map (Int.castRingHom ℚ) (homogeneousComponent d g) =
          C c * map (Int.castRingHom ℚ) k →
        (homogeneousComponent d g).coeff μ ≠ 0 ∧
        ((homogeneousComponent d g).coeff μ).natAbs ≤
          mvPolynomialCoefficientNatAbsMax g ∧
        ∀ (p : ℕ) [Fact p.Prime],
          ¬ (p : ℤ) ∣ (D : ℤ) * (homogeneousComponent d g).coeff μ →
          (homogeneousComponent d (map (Int.castRingHom (ZMod p)) g)).totalDegree = d ∧
          Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
            (homogeneousComponent d (map (Int.castRingHom (ZMod p)) g))) ∧
          Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
            (map (Int.castRingHom (ZMod p)) g)) := by
  obtain ⟨μ, D, hD, ha, hgood⟩ := exists_fixed_leading_good_reduction
    integralityOpen hd k hhom hirr
  refine ⟨μ, D, hD, ha, ?_⟩
  intro g c hc hdegree htop
  obtain ⟨hb, hheight, hprimes⟩ := hgood g c hc htop
  refine ⟨hb, hheight, ?_⟩
  intro p _ hp
  obtain ⟨hdegreeTop, htopGeom⟩ := hprimes p hp
  refine ⟨hdegreeTop, htopGeom, ?_⟩
  apply IrreducibleFromTopHomogeneousPart.irreducible_map_of_irreducible_homogeneousComponent
    (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
    (map (Int.castRingHom (ZMod p)) g) _ htopGeom
  exact (Finset.sup_mono (support_map_subset _ _)).trans hdegree

end CubicTenVariables.FixedLeadingFormGoodReduction

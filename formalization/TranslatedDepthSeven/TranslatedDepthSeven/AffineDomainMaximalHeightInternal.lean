import TranslatedDepthSeven.PolynomialMaximalHeightInternal
import TranslatedDepthSeven.PrimeAffineNoetherNormalization
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

/-!
# Maximal-ideal heights in affine domains

Noether normalization embeds a polynomial ring finitely in the affine
domain.  Incomparability gives the upper height inequality on contraction;
going down over the integrally closed polynomial ring gives the reverse
inequality.  Thus every closed point has height equal to the dimension of
the affine domain.  No catenarity statement is used or asserted here.
-/

namespace TranslatedDepthSeven

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

theorem prime_height_eq_contraction_of_integral_goingDown
    {R S : Type*} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [Algebra R S] [Algebra.IsIntegral R S] [Algebra.HasGoingDown R S]
    (P : Ideal S) [P.IsPrime] :
    P.height = (P.under R).height := by
  apply le_antisymm
  · have hstrict : StrictMono (algebraMap R S).specComap := by
      intro p q hpq
      change p.asIdeal < q.asIdeal at hpq
      change p.asIdeal.comap (algebraMap R S) < q.asIdeal.comap (algebraMap R S)
      obtain ⟨hle, x, hxq, hxp⟩ := SetLike.lt_iff_le_and_exists.mp hpq
      exact Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hxq, hxp⟩
        (Algebra.IsIntegral.isIntegral x)
    exact Order.height_le_height_apply_of_strictMono
      (algebraMap R S).specComap hstrict (⟨P, inferInstance⟩ : PrimeSpectrum S) |>
      (by simpa only [Ideal.height_eq_primeHeight, Ideal.primeHeight] using ·)
  · have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (P.under R) P
    rw [h]
    exact le_add_of_nonneg_right (zero_le _)

/-- Every maximal ideal of a finite-type domain over a characteristic-zero
field has the full Krull dimension.  This is the closed-point case only. -/
theorem affineDomain_maximal_height_eq_dimension
    (K A : Type*) [Field K] [CharZero K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] [IsNoetherianRing A]
    (M : Ideal A) [M.IsMaximal] :
    (M.height : WithBot ℕ∞) = ringKrullDim A := by
  obtain ⟨n, g, hginj, hgintegral⟩ := exists_integral_inj_algHom_of_fg K A
  let B := MvPolynomial (Fin n) K
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : Algebra.IsIntegral B A := ⟨hgintegral⟩
  letI : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hginj
  letI : IsIntegrallyClosed B := inferInstance
  letI : Algebra.HasGoingDown B A := inferInstance
  have hdim : ringKrullDim A = ringKrullDim B :=
    ringKrullDim_eq_of_isIntegral_injective hginj
  let p : Ideal B := M.under B
  letI : p.IsMaximal := Ideal.IsMaximal.under B M
  have hheight : M.height = p.height := prime_height_eq_contraction_of_integral_goingDown M
  rw [hheight, mvPolynomial_maximal_height_eq K n p, hdim]
  exact (ringKrullDim_mvPolynomial_fin_eq_of_field K n).symm

end
end TranslatedDepthSeven

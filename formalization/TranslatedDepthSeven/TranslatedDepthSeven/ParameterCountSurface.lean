import TranslatedDepthSeven.HomogeneousLinearElimination
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.KrullDimension.Basic

/-!
# The parameter count in homogeneous linear normalization

A finite injective normalization has the same transcendence degree as its
target.  This file makes that elementary dimension bridge explicit for the
homogeneous linear normalization data used in the projective argument.
-/

namespace TranslatedDepthSeven

noncomputable section

universe u v

open MvPolynomial

set_option synthInstance.maxHeartbeats 200000

/-- In an injective integral extension of domains, contraction preserves every
strict chain of prime ideals.  Consequently the target has Krull dimension at
most that of the source.  This is the incomparability half of dimension
invariance for integral extensions. -/
theorem ringKrullDim_le_of_isIntegral_injective
    {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsDomain S] [Algebra.IsIntegral R S]
    [FaithfulSMul R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  apply Order.krullDim_le_of_strictMono
    (fun P : PrimeSpectrum S ↦
      ⟨P.asIdeal.comap (algebraMap R S), Ideal.comap_isPrime _ P.asIdeal⟩)
  intro P Q hPQ
  change P.asIdeal.comap (algebraMap R S) <
    Q.asIdeal.comap (algebraMap R S)
  letI : P.asIdeal.IsPrime := P.2
  obtain ⟨_, x, hxQ, hxP⟩ := SetLike.lt_iff_le_and_exists.mp hPQ
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff
    (I := P.asIdeal) (J := Q.asIdeal)
    (show P.asIdeal ≤ Q.asIdeal from hPQ.le) ⟨hxQ, hxP⟩
    (Algebra.IsIntegral.isIntegral x)

/-- Going-up lifts every finite strict chain of primes through an injective
integral extension, without changing its length. -/
theorem exists_primeSpectrum_ltSeries_lift_of_isIntegral
    {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsDomain S] [Algebra.IsIntegral R S]
    [FaithfulSMul R S]
    (p : LTSeries (PrimeSpectrum R)) :
    ∃ q : LTSeries (PrimeSpectrum S),
      q.length = p.length ∧
      q.last.asIdeal.comap (algebraMap R S) = p.last.asIdeal := by
  induction p using RelSeries.inductionOn' with
  | singleton P =>
      letI : P.asIdeal.IsPrime := P.2
      obtain ⟨Q, -, hQprime, hQcomap⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral
          (S := S) P.asIdeal (⊥ : Ideal S) (by simp)
      let Q' : PrimeSpectrum S := ⟨Q, hQprime⟩
      let q : LTSeries (PrimeSpectrum S) :=
        RelSeries.singleton {PQ : PrimeSpectrum S × PrimeSpectrum S | PQ.1 < PQ.2} Q'
      refine ⟨q, ?_, ?_⟩
      · rfl
      · simpa only [q, RelSeries.last_singleton] using hQcomap
  | snoc p P hp ih =>
      obtain ⟨q, hlen, hlast⟩ := ih
      letI : p.last.asIdeal.IsPrime := p.last.2
      letI : q.last.asIdeal.IsPrime := q.last.2
      letI : P.asIdeal.IsPrime := P.2
      obtain ⟨Q, hqQ, hQprime, hQcomap⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime
          (R := R) (S := S) P.asIdeal q.last.asIdeal (by
            rw [hlast]
            exact hp.le)
      let Q' : PrimeSpectrum S := ⟨Q, hQprime⟩
      have hqQ' : q.last < Q' := by
        apply lt_of_le_of_ne hqQ
        intro heq
        have : p.last = P := by
          apply PrimeSpectrum.ext
          rw [← hlast, ← hQcomap]
          exact congrArg (Ideal.comap (algebraMap R S)) heq
        exact hp.ne this
      refine ⟨q.snoc Q' hqQ', ?_, ?_⟩
      · simp only [RelSeries.snoc_length, hlen]
      · simpa only [RelSeries.last_snoc] using hQcomap

/-- The going-up half of dimension invariance for an injective integral
extension. -/
theorem ringKrullDim_le_target_of_isIntegral_injective
    {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsDomain S] [Algebra.IsIntegral R S]
    [FaithfulSMul R S] :
    ringKrullDim R ≤ ringKrullDim S := by
  rw [ringKrullDim, ringKrullDim, Order.krullDim]
  apply iSup_le
  intro p
  obtain ⟨q, hlen, -⟩ :=
    exists_primeSpectrum_ltSeries_lift_of_isIntegral
      (R := R) (S := S) p
  simpa only [hlen] using Order.LTSeries.length_le_krullDim q

/-- Finite injective integral extensions of domains preserve Krull
dimension, proved directly from incomparability and finite-chain going-up. -/
theorem ringKrullDim_eq_of_isIntegral_injective_parameterCount
    {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsDomain S] [Algebra.IsIntegral R S]
    [FaithfulSMul R S] :
    ringKrullDim R = ringKrullDim S :=
  le_antisymm ringKrullDim_le_target_of_isIntegral_injective
    ringKrullDim_le_of_isIntegral_injective

/-- A finite injective homogeneous linear normalization identifies the
Krull dimension of the quotient domain with that of its parameter polynomial
ring.  This is the literal going-up/incomparability dimension statement; it
does not pass through a geometric dimension interface. -/
theorem HomogeneousLinearNormalizationData.ringKrullDim_eq_parameterPolynomial
    {K : Type u} [Field K] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K))
    (hprime : I.IsPrime)
    (D : HomogeneousLinearNormalizationData I) :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ I) =
      ringKrullDim (MvPolynomial (Fin D.parameterCount) K) := by
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin n) K ⧸ I
  let g : B →ₐ[K] A := D.hom
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : IsDomain A :=
    (Ideal.Quotient.isDomain_iff_prime (I := I)).mpr hprime
  letI : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective B A).mpr D.hom_injective
  haveI : Module.Finite B A := D.hom_finite
  letI : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  exact (ringKrullDim_eq_of_isIntegral_injective_parameterCount
    (R := B) (S := A)).symm

/-- The number of parameters in a finite injective homogeneous linear
normalization is exactly the transcendence degree of the quotient domain. -/
theorem HomogeneousLinearNormalizationData.trdeg_eq_parameterCount
    {K : Type u} [Field K] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K))
    (hprime : I.IsPrime)
    (D : HomogeneousLinearNormalizationData I) :
    Algebra.trdeg K (MvPolynomial (Fin n) K ⧸ I) =
      (D.parameterCount : Cardinal) := by
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin n) K ⧸ I
  let g : B →ₐ[K] A := D.hom
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : IsDomain A :=
    (Ideal.Quotient.isDomain_iff_prime (I := I)).mpr hprime
  letI : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective B A).mpr D.hom_injective
  haveI : Module.Finite B A := D.hom_finite
  letI : Algebra.IsAlgebraic B A := Algebra.IsAlgebraic.of_finite B A
  have hz : Algebra.trdeg B A = 0 := trdeg_eq_zero
  have h := trdeg_add_eq K B (A := A)
  rw [hz] at h
  simpa [B, A, Cardinal.lift_id] using h.symm

/-- A finite injective homogeneous linear normalization has `m` parameters
as soon as the quotient domain has transcendence degree `m`. -/
theorem HomogeneousLinearNormalizationData.parameterCount_eq_of_trdeg_eq_nat
    {K : Type u} [Field K] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K))
    (hprime : I.IsPrime)
    (D : HomogeneousLinearNormalizationData I)
    (m : ℕ)
    (htrdeg : Algebra.trdeg K (MvPolynomial (Fin n) K ⧸ I) = m) :
    D.parameterCount = m := by
  have hcard : (D.parameterCount : Cardinal) = m :=
    (D.trdeg_eq_parameterCount n I hprime).symm.trans htrdeg
  exact_mod_cast hcard

/-- The affine cone over a projective surface has transcendence degree three;
under that precise hypothesis every homogeneous linear normalization has
three parameters. -/
theorem HomogeneousLinearNormalizationData.parameterCount_eq_three
    {K : Type u} [Field K] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K))
    (hprime : I.IsPrime)
    (D : HomogeneousLinearNormalizationData I)
    (htrdeg : Algebra.trdeg K (MvPolynomial (Fin n) K ⧸ I) = 3) :
    D.parameterCount = 3 :=
  D.parameterCount_eq_of_trdeg_eq_nat n I hprime 3 htrdeg

/-- The corresponding affine cone over a projective curve has transcendence
degree two; under that precise hypothesis every homogeneous linear
normalization has two parameters. -/
theorem HomogeneousLinearNormalizationData.parameterCount_eq_two
    {K : Type u} [Field K] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K))
    (hprime : I.IsPrime)
    (D : HomogeneousLinearNormalizationData I)
    (htrdeg : Algebra.trdeg K (MvPolynomial (Fin n) K ⧸ I) = 2) :
    D.parameterCount = 2 :=
  D.parameterCount_eq_of_trdeg_eq_nat n I hprime 2 htrdeg

end

end TranslatedDepthSeven

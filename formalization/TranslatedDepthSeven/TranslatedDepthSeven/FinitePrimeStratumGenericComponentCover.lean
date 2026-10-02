import TranslatedDepthSeven.PrimeStratumGenericIdealSpreading
import TranslatedDepthSeven.FinitePrincipalOpenDevissage

/-!
# Finite locally closed cover by closures of generic components

This file combines the concrete dense-open spreading theorem with the
already-proved Noetherian principal-open devissage.  On each integral
locally closed parameter stratum, the payload is the literal finite set of
ambient ideals obtained by contracting the minimal components of the
generic fibre twice: first to the coordinate ring of the stratum, and then
to the ambient parameter ring.

The conclusion is only equality of field-valued zero loci.  No member of a
payload is asserted to have prime, reduced, or equidimensional special
fibres, and no component is labelled across two different strata.
-/

namespace TranslatedDepthSeven

noncomputable section

universe u v w x

/-- The finite set of ambient closures of the generic minimal components on
the prime parameter stratum `P`. -/
def primeStratumGenericComponentClosures
    {R : Type u} {sigma : Type v}
    [CommRing R] [IsNoetherianRing R] [Fintype sigma]
    (I : Ideal (MvPolynomial sigma R))
    (P : Ideal R) [P.IsPrime] :
    Finset (Ideal (MvPolynomial sigma R)) := by
  classical
  let q : R →+* R ⧸ P := Ideal.Quotient.mk P
  let qPoly : MvPolynomial sigma R →+*
      MvPolynomial sigma (R ⧸ P) := MvPolynomial.map q
  let genericMap : MvPolynomial sigma (R ⧸ P) →+*
      MvPolynomial sigma (FractionRing (R ⧸ P)) :=
    MvPolynomial.map (algebraMap (R ⧸ P) (FractionRing (R ⧸ P)))
  exact
    (finiteMinimalPrimes ((I.map qPoly).map genericMap)).image
      (fun Q ↦ (Q.comap genericMap).comap qPoly)

/-- A finite set of ambient ideals gives a literal zero-locus cover at a
prime parameter point when it gives an equivalence for every field realizing
that point as the kernel of its parameter specialization. -/
def AmbientComponentClosuresCoverAtPrime
    {R : Type u} {sigma : Type v} [CommRing R]
    (I : Ideal (MvPolynomial sigma R))
    (components : Finset (Ideal (MvPolynomial sigma R)))
    (T : Ideal R) : Prop :=
  ∀ {L : Type (max u v)} [Field L] (rho : R →+* L),
    RingHom.ker rho = T →
    ∀ z : sigma → L,
      ((∀ f ∈ I, MvPolynomial.eval₂Hom rho z f = 0) ↔
        ∃ J ∈ components,
          ∀ f ∈ J, MvPolynomial.eval₂Hom rho z f = 0)

/-- Vanishing of an ideal after a coefficient change is equivalent to
vanishing of its extended ideal. -/
theorem vanishes_map_iff
    {A : Type u} {B : Type v} {L : Type w} {sigma : Type x}
    [CommRing A] [CommRing B] [CommRing L]
    (q : A →+* B)
    (rho : B →+* L) (z : sigma → L) (I : Ideal (MvPolynomial sigma A)) :
    (∀ f ∈ I, MvPolynomial.eval₂Hom (rho.comp q) z f = 0) ↔
      ∀ g ∈ I.map (MvPolynomial.map q),
        MvPolynomial.eval₂Hom rho z g = 0 := by
  have heval (f : MvPolynomial sigma A) :
      MvPolynomial.eval₂Hom rho z (MvPolynomial.map q f) =
        MvPolynomial.eval₂Hom (rho.comp q) z f := by
    change MvPolynomial.eval₂ rho z (MvPolynomial.map q f) =
      MvPolynomial.eval₂ (rho.comp q) z f
    exact MvPolynomial.eval₂_map q z rho f
  constructor
  · intro hzero
    have hle : I.map (MvPolynomial.map q) ≤
        RingHom.ker (MvPolynomial.eval₂Hom rho z) := by
      rw [Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap, RingHom.mem_ker]
      rw [heval]
      exact hzero f hf
    intro g hg
    exact RingHom.mem_ker.mp (hle hg)
  · intro hzero f hf
    have hmap : MvPolynomial.map q f ∈ I.map (MvPolynomial.map q) :=
      Ideal.mem_map_of_mem _ hf
    rw [← heval]
    exact hzero _ hmap

/-- For a surjective coefficient map, vanishing of an ideal is equivalent
to vanishing of its contraction, evaluated through the quotient map. -/
theorem vanishes_comap_iff_of_surjective
    {A : Type u} {B : Type v} {L : Type w} {sigma : Type x}
    [CommRing A] [CommRing B] [CommRing L]
    (q : A →+* B) (hq : Function.Surjective q)
    (rho : B →+* L) (z : sigma → L) (J : Ideal (MvPolynomial sigma B)) :
    (∀ f ∈ J.comap (MvPolynomial.map q),
        MvPolynomial.eval₂Hom (rho.comp q) z f = 0) ↔
      ∀ g ∈ J, MvPolynomial.eval₂Hom rho z g = 0 := by
  have heval (f : MvPolynomial sigma A) :
      MvPolynomial.eval₂Hom rho z (MvPolynomial.map q f) =
        MvPolynomial.eval₂Hom (rho.comp q) z f := by
    change MvPolynomial.eval₂ rho z (MvPolynomial.map q f) =
      MvPolynomial.eval₂ (rho.comp q) z f
    exact MvPolynomial.eval₂_map q z rho f
  constructor
  · intro hzero g hg
    obtain ⟨f, rfl⟩ := MvPolynomial.map_surjective q hq g
    have hf : f ∈ J.comap (MvPolynomial.map q) := by
      exact hg
    rw [heval]
    exact hzero f hf
  · intro hzero f hf
    have := hzero (MvPolynomial.map q f) hf
    rw [← heval]
    exact this

/-- On a dense principal open of a prime parameter stratum, the ambient
closures of the generic minimal components give a literal field-valued
zero-locus cover. -/
theorem exists_primeStratum_open_genericComponentClosures_cover
    {R : Type u} {sigma : Type v}
    [CommRing R] [IsNoetherianRing R] [Fintype sigma]
    (I : Ideal (MvPolynomial sigma R))
    (P : Ideal R) (hPprime : P.IsPrime) :
    ∃ d : R, d ∉ P ∧
      ∀ T : Ideal R, T.IsPrime → P ≤ T → d ∉ T →
        AmbientComponentClosuresCoverAtPrime I
          (let _ : P.IsPrime := hPprime
           primeStratumGenericComponentClosures I P) T := by
  classical
  letI : P.IsPrime := hPprime
  let q : R →+* R ⧸ P := Ideal.Quotient.mk P
  let qPoly : MvPolynomial sigma R →+*
      MvPolynomial sigma (R ⧸ P) := MvPolynomial.map q
  let genericMap : MvPolynomial sigma (R ⧸ P) →+*
      MvPolynomial sigma (FractionRing (R ⧸ P)) :=
    MvPolynomial.map (algebraMap (R ⧸ P) (FractionRing (R ⧸ P)))
  let IP : Ideal (MvPolynomial sigma (R ⧸ P)) := I.map qPoly
  obtain ⟨d, hdP, hquotientCover⟩ :=
    exists_primeStratum_denominator_fieldPoint_zeroLocus_cover P IP
  refine ⟨d, hdP, ?_⟩
  intro T _hTprime hPT hdT
  change AmbientComponentClosuresCoverAtPrime I
    (primeStratumGenericComponentClosures I P) T
  intro L _ rho hker z
  have hPzero : ∀ x ∈ P, rho x = 0 := fun x hx ↦ by
      apply RingHom.mem_ker.mp
      rw [hker]
      exact hPT hx
  let barRho : R ⧸ P →+* L :=
    Ideal.Quotient.lift P rho hPzero
  have hbarComp : barRho.comp q = rho := by
    exact Ideal.Quotient.lift_comp_mk P rho _
  have hrhod : rho d ≠ 0 := by
    intro hzero
    apply hdT
    rw [← hker]
    exact RingHom.mem_ker.mpr hzero
  have hquotient := hquotientCover rho hPzero z hrhod
  constructor
  · intro hIzero
    have hIPzero : ∀ f ∈ IP,
        MvPolynomial.eval₂Hom barRho z f = 0 := by
      apply (vanishes_map_iff q barRho z I).mp
      simpa only [hbarComp] using hIzero
    obtain ⟨Q, hQ, hQzero⟩ := hquotient.mp hIPzero
    let J : Ideal (MvPolynomial sigma (R ⧸ P)) := Q.comap genericMap
    have hJzero : ∀ f ∈ J,
        MvPolynomial.eval₂Hom barRho z f = 0 := by
      simpa only [J, genericMap] using hQzero
    have hambientZero : ∀ f ∈ J.comap qPoly,
        MvPolynomial.eval₂Hom (barRho.comp q) z f = 0 :=
      (vanishes_comap_iff_of_surjective q
        Ideal.Quotient.mk_surjective barRho z J).mpr hJzero
    refine ⟨J.comap qPoly, ?_, ?_⟩
    · rw [primeStratumGenericComponentClosures]
      apply Finset.mem_image.mpr
      exact ⟨Q, hQ, rfl⟩
    · simpa only [hbarComp] using hambientZero
  · rintro ⟨Jambient, hJambient, hJambientZero⟩
    rw [primeStratumGenericComponentClosures] at hJambient
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hJambient
    let J : Ideal (MvPolynomial sigma (R ⧸ P)) := Q.comap genericMap
    have hambientZero : ∀ f ∈ J.comap qPoly,
        MvPolynomial.eval₂Hom (barRho.comp q) z f = 0 := by
      simpa only [J, qPoly, genericMap, hbarComp] using hJambientZero
    have hJzero : ∀ f ∈ J,
        MvPolynomial.eval₂Hom barRho z f = 0 :=
      (vanishes_comap_iff_of_surjective q
        Ideal.Quotient.mk_surjective barRho z J).mp hambientZero
    have hIPzero : ∀ f ∈ IP,
        MvPolynomial.eval₂Hom barRho z f = 0 := by
      apply hquotient.mpr
      exact ⟨Q, hQ, by simpa only [J, genericMap] using hJzero⟩
    have hIzero : ∀ f ∈ I,
        MvPolynomial.eval₂Hom (barRho.comp q) z f = 0 :=
      (vanishes_map_iff q barRho z I).mpr hIPzero
    simpa only [hbarComp] using hIzero

/-- The dense-open generic-component construction has exactly the abstract
prime-stratum input shape required by finite principal-open devissage.  A
single payload suffices on each dense open: it is the whole finite set of
ambient generic-component closures on that prime stratum. -/
theorem primeStratumGenericComponentClosures_principalOpenData
    {R : Type u} {sigma : Type v}
    [CommRing R] [IsNoetherianRing R] [Fintype sigma]
    (I : Ideal (MvPolynomial sigma R)) :
    PrimeStratumGenericPrincipalOpenData
      (AmbientComponentClosuresCoverAtPrime I) := by
  classical
  intro P hPprime
  obtain ⟨d, hdP, hcover⟩ :=
    exists_primeStratum_open_genericComponentClosures_cover I P hPprime
  letI : P.IsPrime := hPprime
  let components := primeStratumGenericComponentClosures I P
  refine ⟨d, hdP, [components], ?_⟩
  intro T hTprime hPT hdT
  refine ⟨components, by simp only [List.mem_singleton], ?_⟩
  intro L _ rho hker z
  simpa only [components] using
    (hcover T hTprime hPT hdT rho hker z)

/-- Finite locally closed cover obtained by ordinary Noetherian devissage.
Every prime point above `baseIdeal` is assigned a chart whose payload is a
finite set of ambient generic-component closures and whose payload gives an
exact field-valued zero-locus cover at that prime point. -/
theorem exists_finitePrincipalOpen_genericComponentZeroLocusCover
    {R : Type u} {sigma : Type v}
    [CommRing R] [IsNoetherianRing R] [Fintype sigma]
    (I : Ideal (MvPolynomial sigma R)) (baseIdeal : Ideal R) :
    ∃ charts : List
        (PrincipalOpenStratumDatum R
          (Finset (Ideal (MvPolynomial sigma R)))),
      IsFinitePrincipalOpenStratifiedCover
        (AmbientComponentClosuresCoverAtPrime I) baseIdeal charts := by
  exact exists_finitePrincipalOpenStratifiedCover_of_primeGenericData
    (AmbientComponentClosuresCoverAtPrime I)
    (primeStratumGenericComponentClosures_principalOpenData I)
    baseIdeal

/-- Fully expanded field-valued consequence of the finite locally closed
cover.  For every specialization whose kernel lies over `baseIdeal`, one of
the finitely many locally closed strata contains that kernel, and its finite
payload gives the displayed equality of fibre zero loci. -/
theorem exists_finitePrincipalOpen_literal_fieldPoint_zeroLocusCover
    {R : Type u} {sigma : Type v}
    [CommRing R] [IsNoetherianRing R] [Fintype sigma]
    (I : Ideal (MvPolynomial sigma R)) (baseIdeal : Ideal R) :
    ∃ charts : List
        (PrincipalOpenStratumDatum R
          (Finset (Ideal (MvPolynomial sigma R)))),
      (∀ chart ∈ charts,
        baseIdeal ≤ chart.closedIdeal ∧
          chart.closedIdeal.IsPrime ∧
          chart.openElement ∉ chart.closedIdeal) ∧
      ∀ {L : Type (max u v)} [Field L] (rho : R →+* L),
        baseIdeal ≤ RingHom.ker rho →
        ∃ chart ∈ charts,
          chart.closedIdeal ≤ RingHom.ker rho ∧
          chart.openElement ∉ RingHom.ker rho ∧
          ∀ z : sigma → L,
            ((∀ f ∈ I, MvPolynomial.eval₂Hom rho z f = 0) ↔
              ∃ J ∈ chart.payload,
                ∀ f ∈ J, MvPolynomial.eval₂Hom rho z f = 0) := by
  obtain ⟨charts, hstructure, hcover⟩ :=
    exists_finitePrincipalOpen_genericComponentZeroLocusCover I baseIdeal
  refine ⟨charts, hstructure, ?_⟩
  intro L _ rho hbase
  have hkerPrime : (RingHom.ker rho).IsPrime := RingHom.ker_isPrime rho
  obtain ⟨chart, hchart, hcovers, hvalid⟩ :=
    hcover (RingHom.ker rho) hkerPrime hbase
  refine ⟨chart, hchart, hcovers.1, hcovers.2, ?_⟩
  exact hvalid rho rfl

/-- A certified finite payload.  Its component list is not arbitrary: it is
definitionally the list of ambient contractions of the generic minimal
components over the fraction field of the recorded prime stratum. -/
structure PrimeStratumGenericComponentClosurePayload
    {R : Type u} {sigma : Type v}
    [CommRing R] [IsNoetherianRing R] [Fintype sigma]
    (I : Ideal (MvPolynomial sigma R)) where
  stratumIdeal : Ideal R
  stratumPrime : stratumIdeal.IsPrime

/-- The literal finite component-closure list carried by a certified
payload. -/
def PrimeStratumGenericComponentClosurePayload.components
    {R : Type u} {sigma : Type v}
    [CommRing R] [IsNoetherianRing R] [Fintype sigma]
    {I : Ideal (MvPolynomial sigma R)}
    (payload : PrimeStratumGenericComponentClosurePayload I) :
    Finset (Ideal (MvPolynomial sigma R)) := by
  letI : payload.stratumIdeal.IsPrime := payload.stratumPrime
  exact primeStratumGenericComponentClosures I payload.stratumIdeal

/-- Exact validity predicate for a certified payload at a parameter prime.
The parameter prime specializes the payload's integral stratum, and the
computed finite component list gives the fibre zero-locus equality there. -/
def PrimeStratumGenericComponentClosurePayload.ValidAt
    {R : Type u} {sigma : Type v}
    [CommRing R] [IsNoetherianRing R] [Fintype sigma]
    {I : Ideal (MvPolynomial sigma R)}
    (payload : PrimeStratumGenericComponentClosurePayload I)
    (T : Ideal R) : Prop :=
  payload.stratumIdeal ≤ T ∧
    AmbientComponentClosuresCoverAtPrime I payload.components T

/-- Certified generic-component payloads satisfy the generic input to
Noetherian principal-open devissage. -/
theorem certifiedPrimeStratumGenericComponentClosures_principalOpenData
    {R : Type u} {sigma : Type v}
    [CommRing R] [IsNoetherianRing R] [Fintype sigma]
    (I : Ideal (MvPolynomial sigma R)) :
    PrimeStratumGenericPrincipalOpenData
      (fun payload : PrimeStratumGenericComponentClosurePayload I ↦
        payload.ValidAt) := by
  classical
  intro P hPprime
  obtain ⟨d, hdP, hcover⟩ :=
    exists_primeStratum_open_genericComponentClosures_cover I P hPprime
  let payload : PrimeStratumGenericComponentClosurePayload I :=
    { stratumIdeal := P
      stratumPrime := hPprime }
  refine ⟨d, hdP, [payload], ?_⟩
  intro T hTprime hPT hdT
  refine ⟨payload, by simp only [List.mem_singleton], hPT, ?_⟩
  intro L _ rho hker z
  simpa only [payload,
    PrimeStratumGenericComponentClosurePayload.components] using
      (hcover T hTprime hPT hdT rho hker z)

/-- The finite locally closed cover with certified payloads.  Each payload
retains the prime stratum from whose generic fibre its finite component list
was contracted; validity at a parameter prime includes the containment of
that recorded stratum in the parameter prime. -/
theorem exists_finitePrincipalOpen_certifiedGenericComponentZeroLocusCover
    {R : Type u} {sigma : Type v}
    [CommRing R] [IsNoetherianRing R] [Fintype sigma]
    (I : Ideal (MvPolynomial sigma R)) (baseIdeal : Ideal R) :
    ∃ charts : List
        (PrincipalOpenStratumDatum R
          (PrimeStratumGenericComponentClosurePayload I)),
      IsFinitePrincipalOpenStratifiedCover
        (fun payload : PrimeStratumGenericComponentClosurePayload I ↦
          payload.ValidAt)
        baseIdeal charts := by
  exact exists_finitePrincipalOpenStratifiedCover_of_primeGenericData
    (fun payload : PrimeStratumGenericComponentClosurePayload I ↦
      payload.ValidAt)
    (certifiedPrimeStratumGenericComponentClosures_principalOpenData I)
    baseIdeal

/-- Expanded field-valued form of the certified finite cover.  The selected
payload at each specialization visibly consists of the generic-component
contractions belonging to its recorded integral prime stratum. -/
theorem exists_finitePrincipalOpen_certified_literal_fieldPoint_zeroLocusCover
    {R : Type u} {sigma : Type v}
    [CommRing R] [IsNoetherianRing R] [Fintype sigma]
    (I : Ideal (MvPolynomial sigma R)) (baseIdeal : Ideal R) :
    ∃ charts : List
        (PrincipalOpenStratumDatum R
          (PrimeStratumGenericComponentClosurePayload I)),
      (∀ chart ∈ charts,
        baseIdeal ≤ chart.closedIdeal ∧
          chart.closedIdeal.IsPrime ∧
          chart.openElement ∉ chart.closedIdeal) ∧
      ∀ {L : Type (max u v)} [Field L] (rho : R →+* L),
        baseIdeal ≤ RingHom.ker rho →
        ∃ chart ∈ charts,
          chart.closedIdeal ≤ RingHom.ker rho ∧
          chart.openElement ∉ RingHom.ker rho ∧
          chart.payload.stratumIdeal ≤ RingHom.ker rho ∧
          ∀ z : sigma → L,
            ((∀ f ∈ I, MvPolynomial.eval₂Hom rho z f = 0) ↔
              ∃ J ∈ chart.payload.components,
                ∀ f ∈ J, MvPolynomial.eval₂Hom rho z f = 0) := by
  obtain ⟨charts, hstructure, hcover⟩ :=
    exists_finitePrincipalOpen_certifiedGenericComponentZeroLocusCover
      I baseIdeal
  refine ⟨charts, hstructure, ?_⟩
  intro L _ rho hbase
  have hkerPrime : (RingHom.ker rho).IsPrime := RingHom.ker_isPrime rho
  obtain ⟨chart, hchart, hcovers, hvalid⟩ :=
    hcover (RingHom.ker rho) hkerPrime hbase
  refine ⟨chart, hchart, hcovers.1, hcovers.2, hvalid.1, ?_⟩
  exact hvalid.2 rho rfl

end

end TranslatedDepthSeven

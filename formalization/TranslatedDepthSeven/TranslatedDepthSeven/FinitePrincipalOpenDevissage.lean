import TranslatedDepthSeven.NoetherianParameterDevissage
import TranslatedDepthSeven.FiniteEquationMinimalComponents

/-!
# Finite principal-open devissage from generic data

This file isolates the formal Noetherian-induction part of the usual
``spread out at the generic points and recurse on the closed complement''
argument.  The input is required only for a prime closed stratum.  It gives
one dense principal open and a finite list of data which cover every prime
point of that open.  The output is a finite list of locally closed prime
strata covering the original closed set.

For a non-prime closed set, the proof passes to its finitely many minimal
primes.  For a prime closed set `V(I)`, it uses the supplied open `D(s)` and
recurses on the strictly smaller closed set `V(I + (s))`.  Thus both the
minimal-component step and the closed-complement recursion are literal.

The theorem is independent of what the payload is.  It can be a triangular
normalization table, a reduced-equidimensional relative model, or the fixed
syzygy chart of `RelativePersistentStratumSyzygy.lean`.  The genuinely
geometric task is precisely to construct the finite payload list on one
dense open of each prime stratum.
-/

namespace TranslatedDepthSeven

universe u v

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {Data : Type v}

/-- One payload attached to the locally closed subset `V(closedIdeal) ∩
D(openElement)` of the parameter spectrum. -/
structure PrincipalOpenStratumDatum (R : Type u) [CommRing R]
    (Data : Type v) where
  closedIdeal : Ideal R
  openElement : R
  payload : Data

/-- A prime point belongs to the displayed locally closed stratum. -/
def PrincipalOpenStratumDatum.CoversPrime
    (chart : PrincipalOpenStratumDatum R Data) (P : Ideal R) : Prop :=
  chart.closedIdeal ≤ P ∧ chart.openElement ∉ P

/-- A finite list of valid locally closed charts covers every prime point of
`V(I)`.  Each chart closure is itself prime and contains `I`; its displayed
principal open is dense in that closure. -/
def IsFinitePrincipalOpenStratifiedCover
    (Valid : Data → Ideal R → Prop) (I : Ideal R)
    (charts : List (PrincipalOpenStratumDatum R Data)) : Prop :=
  (∀ chart ∈ charts,
      I ≤ chart.closedIdeal ∧ chart.closedIdeal.IsPrime ∧
        chart.openElement ∉ chart.closedIdeal) ∧
    ∀ P : Ideal R, P.IsPrime → I ≤ P →
      ∃ chart ∈ charts, chart.CoversPrime P ∧ Valid chart.payload P

/-- The only input needed at an irreducible generic stratum: after removing
one proper closed subset, finitely many fixed payloads cover all prime points
of the remaining principal open. -/
def PrimeStratumGenericPrincipalOpenData
    (Valid : Data → Ideal R → Prop) : Prop :=
  ∀ I : Ideal R, I.IsPrime →
    ∃ s : R, s ∉ I ∧ ∃ payloads : List Data,
      ∀ P : Ideal R, P.IsPrime → I ≤ P → s ∉ P →
        ∃ payload ∈ payloads, Valid payload P

/-- Noetherian devissage turns dense-open generic data on prime strata into
a finite locally closed stratification.  This is the complete combinatorial
and topological recursion; no termination or component-ordering assumption
is hidden in the conclusion. -/
theorem exists_finitePrincipalOpenStratifiedCover_of_primeGenericData
    (Valid : Data → Ideal R → Prop)
    (hgeneric : PrimeStratumGenericPrincipalOpenData Valid) :
    ∀ I : Ideal R, ∃ charts : List (PrincipalOpenStratumDatum R Data),
      IsFinitePrincipalOpenStratifiedCover Valid I charts := by
  classical
  intro I
  induction I using IsNoetherian.induction with
  | hgt I hgt =>
      change Ideal R at I
      by_cases hIprime : I.IsPrime
      · obtain ⟨s, hsI, payloads, hpayloads⟩ := hgeneric I hIprime
        let openCharts : List (PrincipalOpenStratumDatum R Data) :=
          payloads.map fun payload ↦
            { closedIdeal := I, openElement := s, payload := payload }
        let J := I ⊔ Ideal.span {s}
        have hIJ : I < J := lt_sup_span_singleton_of_notMem I hsI
        obtain ⟨closedCharts, hclosedStructure, hclosedCover⟩ := hgt J hIJ
        refine ⟨openCharts ++ closedCharts, ?_, ?_⟩
        · intro chart hchart
          rw [List.mem_append] at hchart
          rcases hchart with hchart | hchart
          · obtain ⟨payload, hpayload, rfl⟩ := List.mem_map.mp hchart
            exact ⟨le_rfl, hIprime, hsI⟩
          · obtain ⟨hJchart, hprime, hopen⟩ :=
              hclosedStructure chart hchart
            exact ⟨le_sup_left.trans hJchart, hprime, hopen⟩
        · intro P hPprime hIP
          by_cases hsP : s ∈ P
          · have hJP : J ≤ P := by
              apply sup_le hIP
              apply Ideal.span_le.mpr
              simpa only [Set.singleton_subset_iff]
            obtain ⟨chart, hchart, hcovers, hvalid⟩ :=
              hclosedCover P hPprime hJP
            exact ⟨chart, List.mem_append_right _ hchart, hcovers, hvalid⟩
          · obtain ⟨payload, hpayload, hvalid⟩ :=
              hpayloads P hPprime hIP hsP
            let chart : PrincipalOpenStratumDatum R Data :=
              { closedIdeal := I, openElement := s, payload := payload }
            refine ⟨chart, List.mem_append_left _ ?_, ⟨hIP, hsP⟩, hvalid⟩
            exact List.mem_map.mpr ⟨payload, hpayload, rfl⟩
      · let minimal := finiteMinimalPrimes I
        have hstrict : ∀ P : {P // P ∈ minimal}, I < (P : Ideal R) := by
          intro P
          have hPminimal : (P : Ideal R) ∈ I.minimalPrimes :=
            (mem_finiteMinimalPrimes_iff I P).mp P.property
          have hIP : I ≤ (P : Ideal R) := hPminimal.1.2
          refine lt_of_le_of_ne hIP ?_
          intro hPI
          apply hIprime
          rw [hPI]
          exact Ideal.minimalPrimes_isPrime hPminimal
        have hcomponentCover : ∀ P : {P // P ∈ minimal},
            ∃ charts : List (PrincipalOpenStratumDatum R Data),
              IsFinitePrincipalOpenStratifiedCover Valid P charts := by
          intro P
          exact hgt P (hstrict P)
        choose componentCharts hcomponentCharts using hcomponentCover
        let charts : List (PrincipalOpenStratumDatum R Data) :=
          minimal.attach.toList.flatMap componentCharts
        refine ⟨charts, ?_, ?_⟩
        · intro chart hchart
          obtain ⟨P, hP, hchartP⟩ := List.mem_flatMap.mp hchart
          obtain ⟨hPchart, hprime, hopen⟩ :=
            (hcomponentCharts P).1 chart hchartP
          have hPminimal : (P : Ideal R) ∈ I.minimalPrimes :=
            (mem_finiteMinimalPrimes_iff I P).mp P.property
          exact ⟨hPminimal.1.2.trans hPchart, hprime, hopen⟩
        · intro Q hQprime hIQ
          letI : Q.IsPrime := hQprime
          obtain ⟨P, hPminimal, hPQ⟩ := Ideal.exists_minimalPrimes_le hIQ
          have hPfinite : P ∈ minimal :=
            (mem_finiteMinimalPrimes_iff I P).mpr hPminimal
          let P' : {P // P ∈ minimal} := ⟨P, hPfinite⟩
          obtain ⟨chart, hchartP, hcovers, hvalid⟩ :=
            (hcomponentCharts P').2 Q hQprime hPQ
          refine ⟨chart, ?_, hcovers, hvalid⟩
          apply List.mem_flatMap.mpr
          exact ⟨P', by simp, hchartP⟩

end TranslatedDepthSeven

import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Ideal.BigOperators
import TranslatedDepthSeven.GenericFiberComponentSpread
import TranslatedDepthSeven.FiniteEquationMinimalComponents
import TranslatedDepthSeven.ExplicitDenominatorClearing
import TranslatedDepthSeven.RelativePersistentStratumSyzygy
import TranslatedDepthSeven.VerticalGenericSpreading

/-!
# Algebraic spreading on an integral parameter stratum

This file proves the purely commutative-algebraic part of spreading a
generic component and one of its principal-open equation charts.  If `B` is
the coordinate ring of an integral parameter stratum and `K` is its fraction
field, then `K[X]` is the localization of `B[X]` at the nonzero constants.
Consequently:

* a minimal component of the generic fibre is the extension of its
  contraction to `B[X]`;
* the contraction is finitely generated when `B` is Noetherian; and
* a generic clearing identity for a fixed affine chart can be cleared by
  one nonzero element of `B`.

The last conclusion retains the literal identity

`C(s) * u * J ⊆ I`.

It therefore survives every specialization at which `s` is invertible, and
it identifies `I` and `J` after also inverting the fixed affine-chart
polynomial `u`.  No assertion about reduced fibres, equidimensional fibres,
Hilbert polynomials, or smooth-locus coverage is made here.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped nonZeroDivisors

universe u v w

/-- A minimal prime of a generic polynomial fibre contracts to a minimal
prime of the integral polynomial family and extends back exactly. -/
theorem genericFibre_minimalComponent_contracts_to_base
    {B : Type u} {K : Type v} {sigma : Type w}
    [CommRing B] [IsDomain B] [Field K] [Algebra B K]
    [IsFractionRing B K]
    (I : Ideal (MvPolynomial sigma B))
    (Q : Ideal (MvPolynomial sigma K))
    (hQ : Q ∈
      (I.map (MvPolynomial.map (algebraMap B K))).minimalPrimes) :
    Q.comap (MvPolynomial.map (algebraMap B K)) ∈ I.minimalPrimes ∧
      (Q.comap (MvPolynomial.map (algebraMap B K))).map
          (MvPolynomial.map (algebraMap B K)) = Q := by
  letI : Algebra (MvPolynomial sigma B) (MvPolynomial sigma K) :=
    MvPolynomial.algebraMvPolynomial
  have hQ' : Q ∈
      (I.map (algebraMap (MvPolynomial sigma B)
        (MvPolynomial sigma K))).minimalPrimes := by
    simpa only [MvPolynomial.algebraMap_apply] using hQ
  simpa only [MvPolynomial.algebraMap_apply] using
    (localization_minimalComponent_contracts
      ((nonZeroDivisors B).map (MvPolynomial.C (σ := sigma))) I Q hQ')

/-- Over a Noetherian integral parameter ring, the contraction of a generic
minimal component has a literal finite generating family. -/
theorem genericFibre_minimalComponent_has_finite_base_model
    {B : Type u} {K : Type v} {sigma : Type w}
    [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Fintype sigma]
    [Field K] [Algebra B K] [IsFractionRing B K]
    (I : Ideal (MvPolynomial sigma B))
    (Q : Ideal (MvPolynomial sigma K))
    (hQ : Q ∈
      (I.map (MvPolynomial.map (algebraMap B K))).minimalPrimes) :
    ∃ n : ℕ, ∃ g : Fin n → MvPolynomial sigma B,
      Ideal.span (Set.range g) ∈ I.minimalPrimes ∧
        (Ideal.span (Set.range g)).map
            (MvPolynomial.map (algebraMap B K)) = Q := by
  let J := Q.comap (MvPolynomial.map (algebraMap B K))
  have hJ := genericFibre_minimalComponent_contracts_to_base I Q hQ
  have hJfg : J.FG := IsNoetherian.noetherian J
  obtain ⟨n, g, hg⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp hJfg
  have hgIdeal : Ideal.span (Set.range g) = J := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change g i ∈ (J : Submodule (MvPolynomial sigma B)
        (MvPolynomial sigma B))
      rw [← hg]
      exact Submodule.subset_span (Set.mem_range_self i)
    · intro x hx
      change x ∈ Submodule.span (MvPolynomial sigma B) (Set.range g)
      rw [hg]
      exact hx
  refine ⟨n, g, ?_, ?_⟩
  · rw [hgIdeal]
    exact hJ.1
  · rw [hgIdeal]
    exact hJ.2

/-- A fixed generic affine chart of a finitely generated ideal descends to
one dense principal open of the integral parameter stratum.

The hypothesis says that, over the fraction field, multiplication by the
fixed chart polynomial `chart` carries the larger ideal `J` into `I`.  The
output is stronger than equality after localization: it retains the exact
base-ring identity `C(s) * chart * J ⊆ I`. -/
theorem exists_nonzero_base_clearing_for_generic_chart
    {B : Type u} {K : Type v} {sigma : Type w}
    [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Fintype sigma]
    [Field K] [Algebra B K] [IsFractionRing B K]
    (I J : Ideal (MvPolynomial sigma B))
    (chart : MvPolynomial sigma B)
    (hIJ : I ≤ J)
    (hgeneric : ∀ x ∈ J,
      MvPolynomial.map (algebraMap B K) chart *
          MvPolynomial.map (algebraMap B K) x ∈
        Ideal.map (MvPolynomial.map (algebraMap B K)) I) :
    ∃ s : B, s ≠ 0 ∧
      (∀ x ∈ J, MvPolynomial.C s * chart * x ∈ I) ∧
      Ideal.map
          (algebraMap (MvPolynomial sigma B)
            (Localization.Away (MvPolynomial.C s * chart))) I =
        Ideal.map
          (algebraMap (MvPolynomial sigma B)
            (Localization.Away (MvPolynomial.C s * chart))) J := by
  classical
  let A := MvPolynomial sigma B
  let AK := MvPolynomial sigma K
  let M : Submonoid A :=
    (nonZeroDivisors B).map (MvPolynomial.C (σ := sigma))
  letI : Algebra A AK := MvPolynomial.algebraMvPolynomial
  have hJfg : J.FG := IsNoetherian.noetherian J
  obtain ⟨n, g, hg⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp hJfg
  have hdenom : ∀ i : Fin n, ∃ d : B, d ≠ 0 ∧
      MvPolynomial.C d * chart * g i ∈ I := by
    intro i
    have hgiJ : g i ∈ J := by
      change g i ∈ (J : Submodule A A)
      rw [← hg]
      exact Submodule.subset_span (Set.mem_range_self i)
    have hmap : algebraMap A AK (chart * g i) ∈
        Ideal.map (algebraMap A AK) I := by
      simpa only [map_mul, MvPolynomial.algebraMap_apply] using
        hgeneric (g i) hgiJ
    obtain ⟨e, heM, heI⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff
        M AK I (chart * g i)).mp hmap
    obtain ⟨d, hd, hde⟩ := Submonoid.mem_map.mp heM
    refine ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp hd, ?_⟩
    rw [← hde] at heI
    simpa only [mul_assoc] using heI
  choose d hd hdi using hdenom
  let s : B := ∏ i, d i
  have hs : s ≠ 0 := by
    simp only [s, Finset.prod_ne_zero_iff]
    intro i _hi
    exact hd i
  have hclear : ∀ x ∈ J, MvPolynomial.C s * chart * x ∈ I := by
    intro x hx
    have hxspan : x ∈ Submodule.span A (Set.range g) := by
      rw [hg]
      exact hx
    refine Submodule.span_induction
      (p := fun x (_ : x ∈ Submodule.span A (Set.range g)) ↦
        MvPolynomial.C s * chart * x ∈ I)
      ?gen ?zero ?add ?smul hxspan
    · rintro _ ⟨i, rfl⟩
      obtain ⟨c, hc⟩ : d i ∣ s :=
        Finset.dvd_prod_of_mem d (Finset.mem_univ i)
      rw [hc, map_mul]
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        I.mul_mem_left (MvPolynomial.C c) (hdi i)
    · simp
    · intro x y _ _ hx hy
      simpa only [mul_add] using I.add_mem hx hy
    · intro a x _ hx
      simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
        I.mul_mem_left a hx
  refine ⟨s, hs, hclear, ?_⟩
  exact map_away_eq_of_mul_mem I J (MvPolynomial.C s * chart) hIJ
    (by
      intro x hx
      exact hclear x hx)

/-- The previous certificate specializes through any algebra in which both
the base denominator and the affine chart become units.  Thus it is an
actual principal-open spreading statement, not merely an equality in the
generic fibre. -/
theorem map_eq_of_base_clearing_and_chart_units
    {B : Type u} {sigma : Type w}
    [CommRing B]
    (I J : Ideal (MvPolynomial sigma B))
    (s : B) (chart : MvPolynomial sigma B)
    (hIJ : I ≤ J)
    (hclear : ∀ x ∈ J, MvPolynomial.C s * chart * x ∈ I)
    {T : Type*} [CommRing T] [Algebra (MvPolynomial sigma B) T]
    (hs : IsUnit (algebraMap (MvPolynomial sigma B) T
      (MvPolynomial.C s)))
    (hchart : IsUnit (algebraMap (MvPolynomial sigma B) T chart)) :
    Ideal.map (algebraMap (MvPolynomial sigma B) T) I =
      Ideal.map (algebraMap (MvPolynomial sigma B) T) J := by
  apply map_eq_of_mul_mem_of_isUnit I J
    (MvPolynomial.C s * chart) hIJ
  · simpa only [map_mul] using hs.mul hchart
  · exact hclear

/-- Finite algebraic data obtained after spreading one generic component
chart.  Unlike an informal assertion that two ideals agree on an open set,
this structure stores all coefficients of the two required ideal
containments. -/
structure PrincipalOpenIdealSyzygyModel
    {B : Type u} {sigma : Type w} [CommRing B]
    {equationCount componentCount : ℕ}
    (equations : Fin equationCount → MvPolynomial sigma B)
    (components : Fin componentCount → MvPolynomial sigma B)
    (chart : MvPolynomial sigma B) where
  denominator : B
  denominator_ne_zero : denominator ≠ 0
  equationInComponentCoefficient :
    Fin equationCount → Fin componentCount → MvPolynomial sigma B
  clearingInEquationCoefficient :
    Fin componentCount → Fin equationCount → MvPolynomial sigma B
  equation_syzygy : ∀ i,
    equations i =
      ∑ j, equationInComponentCoefficient i j * components j
  clearing_syzygy : ∀ j,
    MvPolynomial.C denominator * chart * components j =
      ∑ i, clearingInEquationCoefficient j i * equations i

/-- The displayed equation syzygies give the first ideal containment. -/
theorem PrincipalOpenIdealSyzygyModel.equationIdeal_le_componentIdeal
    {B : Type u} {sigma : Type w} [CommRing B]
    {equationCount componentCount : ℕ}
    {equations : Fin equationCount → MvPolynomial sigma B}
    {components : Fin componentCount → MvPolynomial sigma B}
    {chart : MvPolynomial sigma B}
    (model : PrincipalOpenIdealSyzygyModel equations components chart) :
    Ideal.span (Set.range equations) ≤ Ideal.span (Set.range components) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  rw [model.equation_syzygy i]
  apply Ideal.sum_mem
  intro j _hj
  exact (Ideal.span (Set.range components)).mul_mem_left _
    (Ideal.subset_span (Set.mem_range_self j))

/-- The displayed clearing syzygies clear the whole component ideal. -/
theorem PrincipalOpenIdealSyzygyModel.clearing_mul_mem
    {B : Type u} {sigma : Type w} [CommRing B]
    {equationCount componentCount : ℕ}
    {equations : Fin equationCount → MvPolynomial sigma B}
    {components : Fin componentCount → MvPolynomial sigma B}
    {chart : MvPolynomial sigma B}
    (model : PrincipalOpenIdealSyzygyModel equations components chart) :
    ∀ x ∈ Ideal.span (Set.range components),
      MvPolynomial.C model.denominator * chart * x ∈
        Ideal.span (Set.range equations) := by
  intro x hx
  refine Submodule.span_induction
    (p := fun x (_ : x ∈ Submodule.span
      (MvPolynomial sigma B) (Set.range components)) ↦
        MvPolynomial.C model.denominator * chart * x ∈
          Ideal.span (Set.range equations))
    ?gen ?zero ?add ?smul hx
  · rintro _ ⟨j, rfl⟩
    rw [model.clearing_syzygy j]
    apply Ideal.sum_mem
    intro i _hi
    exact (Ideal.span (Set.range equations)).mul_mem_left _
      (Ideal.subset_span (Set.mem_range_self i))
  · simp
  · intro x y _ _ hx hy
    simpa only [mul_add] using
      (Ideal.span (Set.range equations)).add_mem hx hy
  · intro a x _ hx
    simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
      (Ideal.span (Set.range equations)).mul_mem_left a hx

/-- Exact ideal equality after inverting the base denominator and the fixed
affine-chart polynomial. -/
theorem PrincipalOpenIdealSyzygyModel.map_away_eq
    {B : Type u} {sigma : Type w} [CommRing B]
    {equationCount componentCount : ℕ}
    {equations : Fin equationCount → MvPolynomial sigma B}
    {components : Fin componentCount → MvPolynomial sigma B}
    {chart : MvPolynomial sigma B}
    (model : PrincipalOpenIdealSyzygyModel equations components chart) :
    Ideal.map
        (algebraMap (MvPolynomial sigma B)
          (Localization.Away
            (MvPolynomial.C model.denominator * chart)))
        (Ideal.span (Set.range equations)) =
      Ideal.map
        (algebraMap (MvPolynomial sigma B)
          (Localization.Away
            (MvPolynomial.C model.denominator * chart)))
        (Ideal.span (Set.range components)) := by
  exact map_away_eq_of_mul_mem
    (Ideal.span (Set.range equations))
    (Ideal.span (Set.range components))
    (MvPolynomial.C model.denominator * chart)
    model.equationIdeal_le_componentIdeal model.clearing_mul_mem

/-- Generic component equations and one generic chart-clearing relation
produce a literal finite syzygy table over one dense base principal open. -/
theorem exists_principalOpenIdealSyzygyModel_of_generic_chart
    {B : Type u} {K : Type v} {sigma : Type w}
    [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Fintype sigma]
    [Field K] [Algebra B K] [IsFractionRing B K]
    {equationCount componentCount : ℕ}
    (equations : Fin equationCount → MvPolynomial sigma B)
    (components : Fin componentCount → MvPolynomial sigma B)
    (chart : MvPolynomial sigma B)
    (hIJ : Ideal.span (Set.range equations) ≤
      Ideal.span (Set.range components))
    (hgeneric : ∀ x ∈ Ideal.span (Set.range components),
      MvPolynomial.map (algebraMap B K) chart *
          MvPolynomial.map (algebraMap B K) x ∈
        Ideal.map (MvPolynomial.map (algebraMap B K))
          (Ideal.span (Set.range equations))) :
    Nonempty (PrincipalOpenIdealSyzygyModel equations components chart) := by
  classical
  obtain ⟨s, hs, hclear, _haway⟩ :=
    exists_nonzero_base_clearing_for_generic_chart
      (Ideal.span (Set.range equations))
      (Ideal.span (Set.range components)) chart hIJ hgeneric
  have hequationRepresentation : ∀ i : Fin equationCount,
      ∃ c : Fin componentCount → MvPolynomial sigma B,
        ∑ j, c j * components j = equations i := by
    intro i
    apply Ideal.mem_span_range_iff_exists_fun.mp
    exact hIJ (Ideal.subset_span (Set.mem_range_self i))
  choose equationCoefficient hequationCoefficient using
    hequationRepresentation
  have hclearingRepresentation : ∀ j : Fin componentCount,
      ∃ c : Fin equationCount → MvPolynomial sigma B,
        ∑ i, c i * equations i =
          MvPolynomial.C s * chart * components j := by
    intro j
    apply Ideal.mem_span_range_iff_exists_fun.mp
    exact hclear (components j)
      (Ideal.subset_span (Set.mem_range_self j))
  choose clearingCoefficient hclearingCoefficient using
    hclearingRepresentation
  exact ⟨
    { denominator := s
      denominator_ne_zero := hs
      equationInComponentCoefficient := equationCoefficient
      clearingInEquationCoefficient := clearingCoefficient
      equation_syzygy := fun i ↦ (hequationCoefficient i).symm
      clearing_syzygy := fun j ↦ (hclearingCoefficient j).symm }⟩

/-- Complete algebraic prime-stratum adaptor.  A generic minimal component
is first contracted to the integral parameter ring, a finite generating
family is chosen there, and every generic chart relation is then spread to
one explicit finite syzygy table. -/
theorem genericMinimalComponent_has_principalOpenIdealSyzygyModel
    {B : Type u} {K : Type v} {sigma : Type w}
    [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Fintype sigma]
    [Field K] [Algebra B K] [IsFractionRing B K]
    (originalIdeal : Ideal (MvPolynomial sigma B))
    (Q : Ideal (MvPolynomial sigma K))
    (hQ : Q ∈
      (originalIdeal.map
        (MvPolynomial.map (algebraMap B K))).minimalPrimes)
    {equationCount : ℕ}
    (equations : Fin equationCount → MvPolynomial sigma B)
    (chart : MvPolynomial sigma B)
    (hEquationComponent : Ideal.span (Set.range equations) ≤
      Q.comap (MvPolynomial.map (algebraMap B K)))
    (hgeneric : ∀ x ∈ Q.comap (MvPolynomial.map (algebraMap B K)),
      MvPolynomial.map (algebraMap B K) chart *
          MvPolynomial.map (algebraMap B K) x ∈
        Ideal.map (MvPolynomial.map (algebraMap B K))
          (Ideal.span (Set.range equations))) :
    ∃ componentCount : ℕ,
      ∃ components : Fin componentCount → MvPolynomial sigma B,
        Ideal.span (Set.range components) ∈ originalIdeal.minimalPrimes ∧
        (Ideal.span (Set.range components)).map
            (MvPolynomial.map (algebraMap B K)) = Q ∧
        Nonempty
          (PrincipalOpenIdealSyzygyModel equations components chart) := by
  let J := Q.comap (MvPolynomial.map (algebraMap B K))
  have hcontract :=
    genericFibre_minimalComponent_contracts_to_base originalIdeal Q hQ
  have hJfg : J.FG := IsNoetherian.noetherian J
  obtain ⟨componentCount, components, hcomponents⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp hJfg
  have hcomponentIdeal : Ideal.span (Set.range components) = J := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      change components j ∈ (J : Submodule (MvPolynomial sigma B)
        (MvPolynomial sigma B))
      rw [← hcomponents]
      exact Submodule.subset_span (Set.mem_range_self j)
    · intro x hx
      change x ∈ Submodule.span (MvPolynomial sigma B)
        (Set.range components)
      rw [hcomponents]
      exact hx
  have hIJ : Ideal.span (Set.range equations) ≤
      Ideal.span (Set.range components) := by
    rw [hcomponentIdeal]
    exact hEquationComponent
  have hgeneric' : ∀ x ∈ Ideal.span (Set.range components),
      MvPolynomial.map (algebraMap B K) chart *
          MvPolynomial.map (algebraMap B K) x ∈
        Ideal.map (MvPolynomial.map (algebraMap B K))
          (Ideal.span (Set.range equations)) := by
    intro x hx
    apply hgeneric x
    change x ∈ J
    rw [← hcomponentIdeal]
    exact hx
  have hmodel := exists_principalOpenIdealSyzygyModel_of_generic_chart
    equations components chart hIJ hgeneric'
  refine ⟨componentCount, components, ?_, ?_, hmodel⟩
  · rw [hcomponentIdeal]
    exact hcontract.1
  · rw [hcomponentIdeal]
    exact hcontract.2

/-- If `h` generates a parameter ideal `P`, then its constant-polynomial
lifts generate exactly the kernel of coefficient reduction modulo `P`.
This is the algebraic reason that every quotient-level identity lifts to an
ambient identity with a finite linear combination of the stratum
equations as its error term. -/
theorem ker_map_quotient_eq_span_constant_generators
    {R : Type u} {sigma : Type w} [CommRing R]
    (P : Ideal R) {stratumEquationCount : ℕ}
    (h : Fin stratumEquationCount → R)
    (hspan : Ideal.span (Set.range h) = P) :
    RingHom.ker
        (MvPolynomial.map (Ideal.Quotient.mk P) :
          MvPolynomial sigma R →+* MvPolynomial sigma (R ⧸ P)) =
      Ideal.span
        (Set.range (fun i ↦ MvPolynomial.C (h i))) := by
  rw [MvPolynomial.ker_map, Ideal.mk_ker, ← hspan, Ideal.map_span]
  congr 1
  ext f
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨h i, ⟨i, rfl⟩, rfl⟩

/-- A quotient-level finite syzygy table on a prime parameter stratum has
a completely explicit ambient lift.  All failures of the lifted identities
are displayed as finite linear combinations of fixed generators of the
stratum ideal.  The lifted denominator lies outside the prime stratum
ideal, so it defines a dense principal open there.

The output is exactly the `RelativePersistentSurfaceStratumSyzygy` consumed
by the integral specialization and multiplicity certificate lemmas. -/
theorem exists_relativePersistentSurfaceStratumSyzygy_of_quotientModel
    {M N equationCount componentCount : ℕ}
    (P : Ideal (MvPolynomial (Fin M) ℤ)) [P.IsPrime]
    (equations : Fin equationCount →
      MvPolynomial (Fin N) (MvPolynomial (Fin M) ℤ ⧸ P))
    (components : Fin componentCount →
      MvPolynomial (Fin N) (MvPolynomial (Fin M) ℤ ⧸ P))
    (chart : MvPolynomial (Fin N) (MvPolynomial (Fin M) ℤ ⧸ P))
    (model : PrincipalOpenIdealSyzygyModel equations components chart)
    (selectedVar : Fin equationCount → Fin N)
    (hselected : Function.Injective selectedVar) :
    ∃ stratumEquationCount : ℕ,
      ∃ data : RelativePersistentSurfaceStratumSyzygy
        M N equationCount 1 componentCount stratumEquationCount,
        data.parameterDenominator ∉ P ∧
        (Ideal.Quotient.mk P data.parameterDenominator =
          model.denominator) ∧
        (∀ i, MvPolynomial.map (Ideal.Quotient.mk P)
          (data.toRelativePersistentSurfaceChart.equation i) = equations i) ∧
        (∀ j, MvPolynomial.map (Ideal.Quotient.mk P)
          (data.componentGenerator j) = components j) ∧
        MvPolynomial.map (Ideal.Quotient.mk P)
          (data.toRelativePersistentSurfaceChart.clearingPolynomial 0) =
            MvPolynomial.C model.denominator * chart := by
  classical
  let R := MvPolynomial (Fin M) ℤ
  let q : R →+* R ⧸ P := Ideal.Quotient.mk P
  let polyQ : MvPolynomial (Fin N) R →+*
      MvPolynomial (Fin N) (R ⧸ P) := MvPolynomial.map q
  have hqSurjective : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hpolyQSurjective : Function.Surjective polyQ := by
    exact MvPolynomial.map_surjective q hqSurjective
  have hPfg : P.FG := IsNoetherian.noetherian P
  obtain ⟨stratumEquationCount, stratumEquation, hstratumSubmodule⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp hPfg
  have hstratum : Ideal.span (Set.range stratumEquation) = P := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change stratumEquation i ∈ (P : Submodule R R)
      rw [← hstratumSubmodule]
      exact Submodule.subset_span (Set.mem_range_self i)
    · intro x hx
      change x ∈ Submodule.span R (Set.range stratumEquation)
      rw [hstratumSubmodule]
      exact hx
  choose equationLift hequationLift using fun i ↦
    hpolyQSurjective (equations i)
  choose componentLift hcomponentLift using fun j ↦
    hpolyQSurjective (components j)
  obtain ⟨chartLift, hchartLift⟩ := hpolyQSurjective chart
  obtain ⟨denominatorLift, hdenominatorLift⟩ :=
    hqSurjective model.denominator
  choose equationCoefficientLift hequationCoefficientLift using fun i j ↦
    hpolyQSurjective (model.equationInComponentCoefficient i j)
  choose clearingCoefficientLift hclearingCoefficientLift using fun j i ↦
    hpolyQSurjective (model.clearingInEquationCoefficient j i)
  have hdenominatorPolynomialLift :
      polyQ (MvPolynomial.C denominatorLift) =
        MvPolynomial.C model.denominator := by
    change MvPolynomial.map q (MvPolynomial.C denominatorLift) = _
    rw [MvPolynomial.map_C, hdenominatorLift]
  have hequationErrorKer : ∀ i,
      equationLift i -
          ∑ j, equationCoefficientLift i j * componentLift j ∈
        RingHom.ker polyQ := by
    intro i
    rw [RingHom.mem_ker]
    simp only [map_sub, map_sum, map_mul, hequationLift,
      hequationCoefficientLift, hcomponentLift]
    rw [model.equation_syzygy i, sub_self]
  have hclearingErrorKer : ∀ j,
      MvPolynomial.C denominatorLift * chartLift * componentLift j -
          ∑ i, clearingCoefficientLift j i * equationLift i ∈
        RingHom.ker polyQ := by
    intro j
    rw [RingHom.mem_ker]
    simp only [map_sub, map_sum, map_mul,
      hdenominatorPolynomialLift, hchartLift, hcomponentLift,
      hclearingCoefficientLift, hequationLift]
    rw [model.clearing_syzygy j, sub_self]
  have hkernel : RingHom.ker polyQ =
      Ideal.span (Set.range (fun r ↦
        MvPolynomial.C (stratumEquation r))) := by
    exact ker_map_quotient_eq_span_constant_generators
      P stratumEquation hstratum
  have hequationErrorRepresentation : ∀ i,
      ∃ c : Fin stratumEquationCount → MvPolynomial (Fin N) R,
        ∑ r, c r * MvPolynomial.C (stratumEquation r) =
          equationLift i -
            ∑ j, equationCoefficientLift i j * componentLift j := by
    intro i
    apply Ideal.mem_span_range_iff_exists_fun.mp
    rw [← hkernel]
    exact hequationErrorKer i
  choose equationErrorCoefficient hequationErrorCoefficient using
    hequationErrorRepresentation
  have hclearingErrorRepresentation : ∀ j,
      ∃ c : Fin stratumEquationCount → MvPolynomial (Fin N) R,
        ∑ r, c r * MvPolynomial.C (stratumEquation r) =
          MvPolynomial.C denominatorLift * chartLift * componentLift j -
            ∑ i, clearingCoefficientLift j i * equationLift i := by
    intro j
    apply Ideal.mem_span_range_iff_exists_fun.mp
    rw [← hkernel]
    exact hclearingErrorKer j
  choose clearingErrorCoefficient hclearingErrorCoefficient using
    hclearingErrorRepresentation
  have hdenominatorOutside : denominatorLift ∉ P := by
    intro hmem
    have hz : q denominatorLift = 0 := RingHom.mem_ker.mp <| by
      simpa only [q, Ideal.mk_ker] using hmem
    rw [hdenominatorLift] at hz
    exact model.denominator_ne_zero hz
  let data : RelativePersistentSurfaceStratumSyzygy
      M N equationCount 1 componentCount stratumEquationCount :=
    { equation := equationLift
      selectedVar := selectedVar
      selectedVar_injective := hselected
      clearingPolynomial := fun _ ↦
        MvPolynomial.C denominatorLift * chartLift
      componentGenerator := componentLift
      stratumEquation := stratumEquation
      parameterDenominator := denominatorLift
      equationInComponentCoefficient := equationCoefficientLift
      equationStratumErrorCoefficient := equationErrorCoefficient
      equation_syzygy := by
        intro i
        have h := hequationErrorCoefficient i
        simp only [liftRelativeIntegralParameterPolynomial]
        rw [h]
        ring
      clearingInEquationCoefficient := fun _ j i ↦
        clearingCoefficientLift j i
      clearingStratumErrorCoefficient := fun _ j r ↦
        clearingErrorCoefficient j r
      clearing_syzygy := by
        intro _mark j
        have h := hclearingErrorCoefficient j
        simp only [liftRelativeIntegralParameterPolynomial]
        rw [h]
        ring }
  refine ⟨stratumEquationCount, data, ?_, ?_, ?_, ?_, ?_⟩
  · exact hdenominatorOutside
  · exact hdenominatorLift
  · exact hequationLift
  · exact hcomponentLift
  · change polyQ (MvPolynomial.C denominatorLift * chartLift) = _
    rw [map_mul, hdenominatorPolynomialLift, hchartLift]

/-- The finite intersection of the contractions of all generic minimal
components.  These are the horizontal component closures inside the total
space over the integral parameter stratum. -/
def genericHorizontalComponentIntersection
    {B : Type u} {K : Type v} {sigma : Type w}
    [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Fintype sigma]
    [Field K] [Algebra B K] [IsFractionRing B K]
    (I : Ideal (MvPolynomial sigma B)) : Ideal (MvPolynomial sigma B) :=
  (finiteMinimalPrimes
      (I.map (MvPolynomial.map (algebraMap B K)))).inf
    (fun Q ↦ Q.comap (MvPolynomial.map (algebraMap B K)))

/-- The horizontal component intersection is exactly the contraction of
the generic radical.  This includes the empty generic fibre: then both
sides are the unit ideal. -/
theorem genericHorizontalComponentIntersection_eq_comap_radical
    {B : Type u} {K : Type v} {sigma : Type w}
    [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Fintype sigma]
    [Field K] [Algebra B K] [IsFractionRing B K]
    (I : Ideal (MvPolynomial sigma B)) :
    genericHorizontalComponentIntersection (K := K) I =
      (I.map (MvPolynomial.map (algebraMap B K))).radical.comap
        (MvPolynomial.map (algebraMap B K)) := by
  let IK := I.map (MvPolynomial.map (algebraMap B K))
  apply le_antisymm
  · intro x hx
    rw [Ideal.mem_comap]
    rw [← Ideal.sInf_minimalPrimes]
    apply Ideal.mem_sInf.mpr
    intro Q hQ
    have hQfinite : Q ∈ finiteMinimalPrimes IK :=
      (mem_finiteMinimalPrimes_iff IK Q).mpr hQ
    have hxQcomap : x ∈ Q.comap
        (MvPolynomial.map (algebraMap B K)) := by
      exact (Finset.inf_le
        (f := fun Q ↦ Q.comap (MvPolynomial.map (algebraMap B K)))
        hQfinite) hx
    exact hxQcomap
  · intro x hx
    change x ∈
      (finiteMinimalPrimes IK).inf
        (fun Q ↦ Q.comap (MvPolynomial.map (algebraMap B K)))
    rw [Submodule.mem_finsetInf]
    intro Q hQ
    change x ∈ Q.comap (MvPolynomial.map (algebraMap B K))
    rw [Ideal.mem_comap]
    have hminimal : Q ∈ IK.minimalPrimes :=
      (mem_finiteMinimalPrimes_iff IK Q).mp hQ
    exact (hminimal.1.1.radical_le_iff.mpr hminimal.1.2) hx

/-- Mapping the horizontal component intersection to the generic fibre
recovers the generic radical exactly. -/
theorem map_genericHorizontalComponentIntersection_eq_radical
    {B : Type u} {K : Type v} {sigma : Type w}
    [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Fintype sigma]
    [Field K] [Algebra B K] [IsFractionRing B K]
    (I : Ideal (MvPolynomial sigma B)) :
    (genericHorizontalComponentIntersection (K := K) I).map
        (MvPolynomial.map (algebraMap B K)) =
      (I.map (MvPolynomial.map (algebraMap B K))).radical := by
  let A := MvPolynomial sigma B
  let AK := MvPolynomial sigma K
  let M : Submonoid A :=
    (nonZeroDivisors B).map (MvPolynomial.C (σ := sigma))
  letI : Algebra A AK := MvPolynomial.algebraMvPolynomial
  rw [genericHorizontalComponentIntersection_eq_comap_radical]
  simpa only [MvPolynomial.algebraMap_apply] using
    (IsLocalization.map_comap M AK
      (I.map (MvPolynomial.map (algebraMap B K))).radical)

/-- The radical of the total-space ideal is contained in the horizontal
generic-component intersection. -/
theorem radical_le_genericHorizontalComponentIntersection
    {B : Type u} {K : Type v} {sigma : Type w}
    [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Fintype sigma]
    [Field K] [Algebra B K] [IsFractionRing B K]
    (I : Ideal (MvPolynomial sigma B)) :
    I.radical ≤ genericHorizontalComponentIntersection (K := K) I := by
  rw [genericHorizontalComponentIntersection_eq_comap_radical]
  apply ((Ideal.radical_isRadical
    (I.map (MvPolynomial.map (algebraMap B K)))).comap
      (MvPolynomial.map (algebraMap B K))).radical_le_iff.mpr
  intro x hx
  rw [Ideal.mem_comap]
  exact Ideal.le_radical
    (Ideal.mem_map_of_mem _ hx)

/-- One base principal open removes every vertical discrepancy between the
total-space radical and the closures of the generic components.  The
elementwise clearing identity is retained in addition to equality after
localization. -/
theorem exists_nonzero_base_open_radical_eq_horizontalComponents
    {B : Type u} {K : Type v} {sigma : Type w}
    [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Fintype sigma]
    [Field K] [Algebra B K] [IsFractionRing B K]
    (I : Ideal (MvPolynomial sigma B)) :
    ∃ s : B, s ≠ 0 ∧
      (∀ x ∈ genericHorizontalComponentIntersection (K := K) I,
        MvPolynomial.C (σ := sigma) s * x ∈ I.radical) ∧
      Ideal.map
          (algebraMap (MvPolynomial sigma B)
            (Localization.Away (MvPolynomial.C (σ := sigma) s))) I.radical =
        Ideal.map
          (algebraMap (MvPolynomial sigma B)
            (Localization.Away (MvPolynomial.C (σ := sigma) s)))
          (genericHorizontalComponentIntersection (K := K) I) := by
  let A := MvPolynomial sigma B
  let AK := MvPolynomial sigma K
  letI : Algebra A AK := MvPolynomial.algebraMvPolynomial
  have hlocalized :
      Ideal.map (algebraMap A AK) I.radical =
        Ideal.map (algebraMap A AK)
          (genericHorizontalComponentIntersection (K := K) I) := by
    rw [IsLocalization.map_radical
      ((nonZeroDivisors B).map (MvPolynomial.C (σ := sigma))) AK I]
    simpa only [MvPolynomial.algebraMap_apply] using
      (map_genericHorizontalComponentIntersection_eq_radical
        (K := K) I).symm
  have hgeneric : ∀ x ∈
      genericHorizontalComponentIntersection (K := K) I,
      MvPolynomial.map (algebraMap B K) (1 : MvPolynomial sigma B) *
          MvPolynomial.map (algebraMap B K) x ∈
        Ideal.map (MvPolynomial.map (algebraMap B K)) I.radical := by
    intro x hx
    have hxmap : MvPolynomial.map (algebraMap B K) x ∈
        Ideal.map (MvPolynomial.map (algebraMap B K))
          (genericHorizontalComponentIntersection (K := K) I) :=
      Ideal.mem_map_of_mem _ hx
    have hxrad : MvPolynomial.map (algebraMap B K) x ∈
        Ideal.map (MvPolynomial.map (algebraMap B K)) I.radical := by
      simpa only [MvPolynomial.algebraMap_apply] using
        (show algebraMap A AK x ∈ Ideal.map (algebraMap A AK) I.radical by
          rw [hlocalized]
          exact hxmap)
    simpa only [map_one, one_mul] using hxrad
  obtain ⟨s, hs, hclear, _haway⟩ :=
    exists_nonzero_base_clearing_for_generic_chart
      I.radical (genericHorizontalComponentIntersection (K := K) I)
      (1 : MvPolynomial sigma B)
      (radical_le_genericHorizontalComponentIntersection (K := K) I)
      hgeneric
  refine ⟨s, hs, ?_, ?_⟩
  · simpa only [mul_one] using hclear
  · exact map_away_eq_of_mul_mem I.radical
      (genericHorizontalComponentIntersection (K := K) I)
      (MvPolynomial.C (σ := sigma) s)
      (radical_le_genericHorizontalComponentIntersection (K := K) I)
      (by
        intro x hx
        simpa only [mul_one] using hclear x hx)

/-- Static form of “all vertical failure lies in the closed complement.”
After deleting one proper closed subset of the integral parameter stratum,
every prime point of the original total space lies on the contraction of at
least one generic minimal component.  No claim is made about reducedness or
equidimensionality of that component's special fibre. -/
theorem exists_nonzero_base_open_every_prime_lies_on_genericComponentClosure
    {B : Type u} {K : Type v} {sigma : Type w}
    [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Fintype sigma]
    [Field K] [Algebra B K] [IsFractionRing B K]
    (I : Ideal (MvPolynomial sigma B)) :
    ∃ s : B, s ≠ 0 ∧
      ∀ T : Ideal (MvPolynomial sigma B), T.IsPrime → I ≤ T →
        MvPolynomial.C (σ := sigma) s ∉ T →
        ∃ Q ∈ finiteMinimalPrimes
            (I.map (MvPolynomial.map (algebraMap B K))),
          Q.comap (MvPolynomial.map (algebraMap B K)) ≤ T := by
  obtain ⟨s, hs, hclear, _haway⟩ :=
    exists_nonzero_base_open_radical_eq_horizontalComponents (K := K) I
  refine ⟨s, hs, ?_⟩
  intro T hTprime hIT hsT
  letI : T.IsPrime := hTprime
  have hradT : I.radical ≤ T :=
    hTprime.radical_le_iff.mpr hIT
  have hhorizontalT :
      genericHorizontalComponentIntersection (K := K) I ≤ T := by
    intro x hx
    have hprod : MvPolynomial.C (σ := sigma) s * x ∈ T :=
      hradT (hclear x hx)
    exact (hTprime.mul_mem_iff_mem_or_mem.mp hprod).resolve_left hsT
  exact (hTprime.inf_le').mp hhorizontalT

/-- Field-valued form of the preceding prime-ideal statement.  After one
principal shrink of the integral base, the zero locus of the original ideal
is, set-theoretically, the union of the zero loci of the contractions of the
generic minimal components.  The field and the specialization of the base
are arbitrary.

This is only a statement about sets of field-valued points.  In particular,
it does not assert that the specialized component ideals are prime, reduced,
or equidimensional. -/
theorem exists_nonzero_base_open_fieldPoint_zeroLocus_cover
    {B : Type u} {K : Type v} {sigma : Type w}
    [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Fintype sigma]
    [Field K] [Algebra B K] [IsFractionRing B K]
    (I : Ideal (MvPolynomial sigma B)) :
    ∃ s : B, s ≠ 0 ∧
      ∀ {L : Type*} [Field L] (rho : B →+* L) (z : sigma → L),
        rho s ≠ 0 →
        ((∀ f ∈ I, MvPolynomial.eval₂Hom rho z f = 0) ↔
          ∃ Q ∈ finiteMinimalPrimes
              (I.map (MvPolynomial.map (algebraMap B K))),
            ∀ f ∈ Q.comap (MvPolynomial.map (algebraMap B K)),
              MvPolynomial.eval₂Hom rho z f = 0) := by
  obtain ⟨s, hs, hprimeCover⟩ :=
    exists_nonzero_base_open_every_prime_lies_on_genericComponentClosure
      (K := K) I
  refine ⟨s, hs, ?_⟩
  intro L _ rho z hrhos
  let ev : MvPolynomial sigma B →+* L := MvPolynomial.eval₂Hom rho z
  constructor
  · intro hzero
    let T : Ideal (MvPolynomial sigma B) := RingHom.ker ev
    have hTprime : T.IsPrime := RingHom.ker_isPrime ev
    have hIT : I ≤ T := by
      intro f hf
      exact RingHom.mem_ker.mpr (hzero f hf)
    have hsT : MvPolynomial.C (σ := sigma) s ∉ T := by
      intro hCs
      have hzeroCs : ev (MvPolynomial.C (σ := sigma) s) = 0 :=
        RingHom.mem_ker.mp hCs
      exact hrhos (by simpa [ev] using hzeroCs)
    obtain ⟨Q, hQ, hQT⟩ := hprimeCover T hTprime hIT hsT
    refine ⟨Q, hQ, ?_⟩
    intro f hf
    exact RingHom.mem_ker.mp (hQT hf)
  · rintro ⟨Q, hQ, hzeroQ⟩ f hf
    apply hzeroQ f
    rw [Ideal.mem_comap]
    exact le_of_mem_finiteMinimalPrimes hQ
      (Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap B K)) hf)

/-- Ambient-coordinate form of the field-valued cover on a prime parameter
stratum.  A denominator in the quotient coordinate ring is lifted to a
literal element `d` of the ambient parameter ring.  The condition `d ∉ P`
is exactly the assertion that its restriction to the integral stratum is
not identically zero.

For every specialization annihilating `P` and avoiding `d`, the original
zero locus is the union of the specialized contractions of the generic
minimal components over the fraction field of `R ⨸ P`.  This theorem still
makes no assertion about the scheme structures of those specialized
contractions. -/
theorem exists_primeStratum_denominator_fieldPoint_zeroLocus_cover
    {R : Type u} {sigma : Type w}
    [CommRing R] [IsNoetherianRing R] [Fintype sigma]
    (P : Ideal R) [P.IsPrime]
    (I : Ideal (MvPolynomial sigma (R ⧸ P))) :
    ∃ d : R, d ∉ P ∧
      ∀ {L : Type*} [Field L] (rho : R →+* L)
        (hPzero : ∀ x ∈ P, rho x = 0) (z : sigma → L),
        rho d ≠ 0 →
        ((∀ f ∈ I,
            MvPolynomial.eval₂Hom (Ideal.Quotient.lift P rho hPzero) z f = 0) ↔
          ∃ Q ∈ finiteMinimalPrimes
              (I.map (MvPolynomial.map
                (algebraMap (R ⧸ P) (FractionRing (R ⧸ P))))),
            ∀ f ∈ Q.comap (MvPolynomial.map
                (algebraMap (R ⧸ P) (FractionRing (R ⧸ P)))),
              MvPolynomial.eval₂Hom
                (Ideal.Quotient.lift P rho hPzero) z f = 0) := by
  obtain ⟨s, hs, hcover⟩ :=
    exists_nonzero_base_open_fieldPoint_zeroLocus_cover
      (B := R ⧸ P) (K := FractionRing (R ⧸ P)) I
  obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective s
  refine ⟨d, ?_, ?_⟩
  · intro hdP
    have hzero : Ideal.Quotient.mk P d = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hdP
    rw [hd] at hzero
    exact hs hzero
  · intro L _ rho hPzero z hrhod
    have hrhos : Ideal.Quotient.lift P rho hPzero s ≠ 0 := by
      rw [← hd, Ideal.Quotient.lift_mk]
      exact hrhod
    exact hcover (Ideal.Quotient.lift P rho hPzero) z hrhos

end

end TranslatedDepthSeven

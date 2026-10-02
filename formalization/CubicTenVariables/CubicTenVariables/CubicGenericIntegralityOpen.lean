import CubicTenVariables.CubicFactorCharts
import CubicTenVariables.GenericEmptyFiberSpreading
import Mathlib.RingTheory.Nullstellensatz

/-! Geometric integrality on one base open for an actual cubic polynomial.
The finitely many normalized factor charts are empty over the supplied
algebraically closed generic field. Nullstellensatz and literal constant
certificates spread that emptiness. The specialized degree-three condition
is retained explicitly; no geometric-integrality spreading input is used. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.CubicGenericIntegralityOpen
open MvPolynomial CubicFactorCharts
open scoped BigOperators

/-- The literal ideal of one normalized factor chart. -/
def chartIdeal {n : ℕ} {B : Type*} [CommRing B]
    (F : MvPolynomial (Fin n) B) (i : Fin n) :
    Ideal (MvPolynomial (FactorVar n) B) := Ideal.span (Set.range (equations F i))

/-- An actual degree-three domain quotient over an algebraically closed
field makes each factor-chart equation ideal the unit ideal. -/
theorem chartIdeal_map_eq_top
    {n : ℕ} {B Ω : Type*} [CommRing B] [Field Ω] [IsAlgClosed Ω]
    (ι : B →+* Ω) (F : MvPolynomial (Fin n) B)
    (hdegree : (map ι F).totalDegree = 3)
    (hdomain : IsDomain (MvPolynomial (Fin n) Ω ⧸ Ideal.span {map ι F}))
    (i : Fin n) : (chartIdeal F i).map (MvPolynomial.map ι) = ⊤ := by
  classical
  have hnone := (isDomain_iff_no_solution ι F hdegree).mp hdomain
  have hzero : zeroLocus Ω ((chartIdeal F i).map (MvPolynomial.map ι)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    apply hnone
    refine ⟨i, x, ?_⟩
    intro e
    have hh := hx (map ι (equations F i e))
      (Ideal.mem_map_of_mem (MvPolynomial.map ι)
        (Ideal.subset_span (Set.mem_range_self e)))
    change eval x (map ι (equations F i e)) = 0 at hh
    simpa only [eval_map] using hh
  apply Ideal.radical_eq_top.mp
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := Ω), hzero, vanishingIdeal_empty]

private theorem no_solution_of_chartIdeal_map_top
    {n : ℕ} {B K : Type*} [CommRing B] [Field K]
    (ρ : B →+* K) (F : MvPolynomial (Fin n) B) (i : Fin n)
    (htop : (chartIdeal F i).map (MvPolynomial.map ρ) = ⊤)
    (x : FactorVar n → K)
    (hx : ∀ e, eval₂Hom ρ x (equations F i e) = 0) : False := by
  have hle : (chartIdeal F i).map (MvPolynomial.map ρ) ≤ RingHom.ker (eval x) := by
    rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.mpr
    rintro g ⟨e, rfl⟩
    change eval x (map ρ (equations F i e)) = 0
    simpa only [eval_map] using hx e
  have h1 : (1 : MvPolynomial (FactorVar n) K) ∈
      (chartIdeal F i).map (MvPolynomial.map ρ) := by
    rw [htop]
    trivial
  have hz := hle h1
  exact one_ne_zero (by simpa only [RingHom.mem_ker, map_one] using hz)

/-- One nonzero base element works before every coefficient specialization
into a field. Degree preservation remains an explicit condition on the
specialized cubic. -/
theorem exists_nonzero_open
    {n : ℕ} {B Ω : Type*} [CommRing B] [IsDomain B]
    [Field Ω] [IsAlgClosed Ω]
    (ι : B →+* Ω) (hι : Function.Injective ι)
    (F : MvPolynomial (Fin n) B)
    (hdegree : (map ι F).totalDegree = 3)
    (hdomain : IsDomain (MvPolynomial (Fin n) Ω ⧸ Ideal.span {map ι F})) :
    ∃ s : B, s ≠ 0 ∧
      ∀ (K : Type*) [Field K] (ρ : B →+* K), ρ s ≠ 0 →
        (map ρ F).totalDegree = 3 →
        IsDomain (MvPolynomial (Fin n) K ⧸ Ideal.span {map ρ F}) := by
  classical
  have hchart (i : Fin n) := GenericEmptyFiberSpreading.exists_nonzero_open_of_injective
    (chartIdeal F i) ι hι (chartIdeal_map_eq_top ι F hdegree hdomain i)
  choose s hs hgood using hchart
  refine ⟨∏ i, s i, Finset.prod_ne_zero_iff.mpr (fun i _ => hs i), ?_⟩
  intro K _ ρ hρ hdegreeρ
  apply (isDomain_iff_no_solution ρ F hdegreeρ).mpr
  rintro ⟨i, x, hx⟩
  have hprod : ∏ j, ρ (s j) ≠ 0 := by simpa only [map_prod] using hρ
  have hi : ρ (s i) ≠ 0 := Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)
  exact no_solution_of_chartIdeal_map_top ρ F i (hgood i K ρ hi) x hx

end CubicTenVariables.CubicGenericIntegralityOpen

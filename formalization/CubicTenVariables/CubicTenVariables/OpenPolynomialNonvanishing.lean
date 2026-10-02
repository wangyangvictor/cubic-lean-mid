import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# A nonzero polynomial does not vanish on a nonempty open set

Over any nontrivially normed field, a nonempty open subset of a finite
coordinate space contains a product of infinite coordinate neighborhoods.
The proved polynomial identity theorem on such products then gives the
claim for literal multivariate polynomial evaluation. The proof includes
zero variables: the coordinate space is a singleton, and the polynomial
is a constant. No completeness, characteristic, or local-solubility premise
is used.
-/

noncomputable section

namespace CubicTenVariables.OpenPolynomialNonvanishing

open MvPolynomial
open scoped Topology

variable {K : Type*} [NontriviallyNormedField K] {m : ℕ}

/-- A polynomial vanishing at every point of a nonempty open set is the
zero polynomial. Both the set and the evaluation are literal. -/
theorem eq_zero_of_eval_eq_zero_on_nonempty_open
    (P : MvPolynomial (Fin m) K) (U : Set (Fin m → K))
    (hU : IsOpen U) (hne : U.Nonempty)
    (hzero : ∀ x ∈ U, eval x P = 0) : P = 0 := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨s, hs, hsub⟩ := isOpen_pi_iff'.mp hU x hx
  apply MvPolynomial.funext_set s
    (fun i => infinite_of_mem_nhds (x i) ((hs i).1.mem_nhds (hs i).2))
  intro y hy
  simpa only [map_zero] using hzero y (hsub hy)

/-- Every nonempty open set contains a point where an actual nonzero
polynomial evaluates to a nonzero field element. -/
theorem exists_eval_ne_zero_mem_open
    (P : MvPolynomial (Fin m) K) (hP : P ≠ 0)
    (U : Set (Fin m → K)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, eval x P ≠ 0 := by
  by_contra h
  push_neg at h
  exact hP (eq_zero_of_eval_eq_zero_on_nonempty_open P U hU hne h)

/-- The complement of the actual polynomial zero set is dense in the
ordinary norm topology. -/
theorem dense_nonvanishing_locus (P : MvPolynomial (Fin m) K) (hP : P ≠ 0) :
    Dense {x : Fin m → K | eval x P ≠ 0} := by
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨x, hx, hPx⟩ := exists_eval_ne_zero_mem_open P hP U hU hne
  exact ⟨x, hx, hPx⟩

/-- Polynomial nonvanishing is also an open condition. -/
theorem isOpen_nonvanishing_locus (P : MvPolynomial (Fin m) K) :
    IsOpen {x : Fin m → K | eval x P ≠ 0} :=
  isOpen_ne.preimage (MvPolynomial.continuous_eval P)

end CubicTenVariables.OpenPolynomialNonvanishing

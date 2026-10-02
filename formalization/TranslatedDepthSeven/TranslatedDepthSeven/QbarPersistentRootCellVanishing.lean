import TranslatedDepthSeven.QuantitativeSurfacePrefixGeometricPartition

/-!
# Rational vanishing from a persistent geometric component

The rooted auxiliary partition is made after coefficient extension to
`Qbar`, whereas the proper-cut Pila theorem uses the original rational
surface and rational auxiliary.  A persistent geometric minimal-prime label
contains the extended source ideal and the extended terminal form.  Evaluating
at rational coordinates and using injectivity of `ℚ → Qbar` descends both
vanishing statements to `ℚ`.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000

/-- One common geometric component at the root and a terminal vertex forces
the whole root cell to lie on the original rational source and on the chosen
rational terminal cut. -/
theorem qbarPersistentRootCell_rationalVanishing
    {Point Vertex : Type*} [DecidableEq Vertex]
    {N : ℕ}
    (sourceEquations : Finset (MvPolynomial (Fin (N + 1)) ℚ))
    (G₀ G : MvPolynomial (Fin (N + 1)) ℚ)
    (equations : Point → Vertex →
      Finset (MvPolynomial (Fin (N + 1)) Qbar))
    (coordinate : Point → Fin (N + 1) → ℚ)
    (vertices : Point → Finset Vertex)
    (cell : Finset Point)
    (x : Point) (v : Vertex)
    (o : Option (Ideal (MvPolynomial (Fin (N + 1)) Qbar)))
    (hx : x ∈ cell)
    (hv : v ∈ vertices x)
    (ho : o ≠ none)
    (hpersistent : ∀ w ∈ vertices x,
      selectedFiniteEquationComponent (equations x w)
        (fun i => algebraMap ℚ Qbar (coordinate x i)) = o)
    (hequations : equations x v =
      qbarSurfaceCutEquationFamily sourceEquations G)
    (hrootSelected : ∀ z ∈ cell,
      selectedFiniteEquationComponent
        (qbarSurfaceCutEquationFamily sourceEquations G₀)
        (fun i => algebraMap ℚ Qbar (coordinate z i)) = o) :
    ∃ Q,
      o = some Q ∧
      Q ∈ finiteEquationMinimalPrimes
        (qbarSurfaceCutEquationFamily sourceEquations G₀) ∧
      Q ∈ finiteEquationMinimalPrimes
        (qbarSurfaceCutEquationFamily sourceEquations G) ∧
      ∀ z ∈ cell,
        (∀ f ∈ finiteEquationIdeal sourceEquations,
          MvPolynomial.eval (coordinate z) f = 0) ∧
        MvPolynomial.eval (coordinate z) G = 0 := by
  classical
  obtain ⟨Q, hQo⟩ := Option.ne_none_iff_exists'.mp ho
  have hterminalSome : selectedFiniteEquationComponent
      (qbarSurfaceCutEquationFamily sourceEquations G)
      (fun i => algebraMap ℚ Qbar (coordinate x i)) = some Q := by
    rw [← hequations]
    exact (hpersistent v hv).trans hQo
  have hQterminal := (selectedFiniteEquationComponent_spec
    (qbarSurfaceCutEquationFamily sourceEquations G)
      (fun i => algebraMap ℚ Qbar (coordinate x i)) hterminalSome).1
  have hrootSome : selectedFiniteEquationComponent
      (qbarSurfaceCutEquationFamily sourceEquations G₀)
      (fun i => algebraMap ℚ Qbar (coordinate x i)) = some Q :=
    (hrootSelected x hx).trans hQo
  have hQroot := (selectedFiniteEquationComponent_spec
    (qbarSurfaceCutEquationFamily sourceEquations G₀)
      (fun i => algebraMap ℚ Qbar (coordinate x i)) hrootSome).1
  have hsourceQ : finiteEquationIdeal
      (qbarSurfaceEquationFamily sourceEquations) ≤ Q := by
    have hcontain := le_of_mem_finiteMinimalPrimes hQroot
    unfold qbarSurfaceCutEquationFamily at hcontain
    rw [finiteEquationIdeal_union] at hcontain
    exact le_sup_left.trans hcontain
  have hterminalQ : finiteEquationIdeal
      (qbarSurfaceCutEquationFamily sourceEquations G) ≤ Q :=
    le_of_mem_finiteMinimalPrimes hQterminal
  have hGfamily : MvPolynomial.map (algebraMap ℚ Qbar) G ∈
      qbarSurfaceCutEquationFamily sourceEquations G := by
    unfold qbarSurfaceCutEquationFamily
    exact (mem_finiteEquationFamilyUnion _ _ _).mpr (Or.inr (by simp))
  have hGQ : MvPolynomial.map (algebraMap ℚ Qbar) G ∈ Q :=
    hterminalQ (Ideal.subset_span hGfamily)
  refine ⟨Q, hQo, hQroot, hQterminal, ?_⟩
  intro z hz
  have hzSome : selectedFiniteEquationComponent
      (qbarSurfaceCutEquationFamily sourceEquations G₀)
      (fun i => algebraMap ℚ Qbar (coordinate z i)) = some Q :=
    (hrootSelected z hz).trans hQo
  have hQkernel := (selectedFiniteEquationComponent_spec
    (qbarSurfaceCutEquationFamily sourceEquations G₀)
      (fun i => algebraMap ℚ Qbar (coordinate z i)) hzSome).2
  have hdescend (f : MvPolynomial (Fin (N + 1)) ℚ)
      (hfQ : MvPolynomial.map (algebraMap ℚ Qbar) f ∈ Q) :
      MvPolynomial.eval (coordinate z) f = 0 := by
    have hevalQbar : MvPolynomial.eval
        (fun i => algebraMap ℚ Qbar (coordinate z i))
        (MvPolynomial.map (algebraMap ℚ Qbar) f) = 0 :=
      RingHom.mem_ker.mp (hQkernel hfQ)
    have hmapEval : algebraMap ℚ Qbar
        (MvPolynomial.eval (coordinate z) f) = 0 := by
      rw [← hevalQbar]
      simpa only [Function.comp_def] using
        (MvPolynomial.map_eval (algebraMap ℚ Qbar) (coordinate z) f)
    exact (map_eq_zero_iff (algebraMap ℚ Qbar)
      (algebraMap ℚ Qbar).injective).mp hmapEval
  constructor
  · intro f hf
    apply hdescend f
    apply hsourceQ
    rw [finiteEquationIdeal_qbarSurfaceEquationFamily]
    exact Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap ℚ Qbar)) hf
  · exact hdescend G hGQ

end

end TranslatedDepthSeven

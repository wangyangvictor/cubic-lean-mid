import HessianTheorem11.KernelGradientSpan
import HessianTheorem11.AffineGeometry

/-! Elementary closure facts for linear subspaces and full affine space,
proved from polynomial vanishing and the nondegenerate coordinate pairing. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Module
variable {n : ℕ}

theorem algebraicallyClosedSet_submodule (S : Submodule GeometricField (GeometricPoint n)) :
    AlgebraicallyClosedSet (S : Set (GeometricPoint n)) := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [← LinearMap.BilinForm.orthogonal_orthogonal
      (coordinatePairing_nondegenerate (K := GeometricField) (n := n))
      coordinatePairing_reflexive S]
    intro v hv
    let P : GeometricPolynomial n := ∑ i, C (v i) * X i
    have he (y : GeometricPoint n) : eval y P = dotProduct v y := by
      simp [P, dotProduct]
    have hp : P ∈ vanishingIdeal GeometricField (S : Set (GeometricPoint n)) := by
      intro y hy
      change eval y P = 0
      rw [he, dotProduct_comm]
      exact hv y hy
    have h : eval x P = 0 := hx P hp
    rw [he] at h
    exact h
  · exact subset_geometricClosure _

theorem algebraicallyClosedSet_univ :
    AlgebraicallyClosedSet (Set.univ : Set (GeometricPoint n)) :=
  Set.eq_univ_of_forall (fun x => subset_geometricClosure _ (Set.mem_univ x))

theorem vanishingIdeal_univ_eq_bot_geometric :
    vanishingIdeal GeometricField (Set.univ : Set (GeometricPoint n)) = ⊥ := by
  ext P
  rw [Ideal.mem_bot]
  constructor
  · intro h
    apply MvPolynomial.funext
    intro x
    simpa using h x (Set.mem_univ x)
  · intro h
    subst P
    exact (vanishingIdeal GeometricField (Set.univ : Set (GeometricPoint n))).zero_mem

theorem geometricallyIrreducible_univ :
    GeometricallyIrreducible (Set.univ : Set (GeometricPoint n)) := by
  unfold GeometricallyIrreducible
  rw [vanishingIdeal_univ_eq_bot_geometric]
  exact Ideal.bot_prime

theorem affineTangentSpace_univ_geometric (x : GeometricPoint n) :
    affineTangentSpace (Set.univ : Set (GeometricPoint n)) x = ⊤ := by
  apply top_unique
  intro v hv
  simp only [affineTangentSpace, Submodule.mem_iInf]
  intro P
  have hp : P.val = 0 := by
    have h : P.val ∈ (⊥ : Ideal (GeometricPolynomial n)) := by
      simpa only [vanishingIdeal_univ_eq_bot_geometric] using P.property
    exact Ideal.mem_bot.mp h
  simp [hp, polynomialDifferential]

end HessianTheorem11

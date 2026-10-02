import CubicTenVariables.CubicSingularCoplanar

/-! A literal general-position alternative for four singular points of an
integral cubic surface. No isolatedness or singular-locus classification is
assumed: a dependent fourth point forces an entire singular secant line. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.CubicSingularGeneralPosition
open MvPolynomial HessianTheorem11
open CubicSingularCollinear CubicSingularCoplanar
variable {K : Type*} [Field K] [IsAlgClosed K]

/-- Three independent singular columns and a fourth singular point in their
plane, distinct from each column projectively, force a whole singular line. -/
theorem exists_singular_line_of_fourth_in_plane
    (B : Matrix (Fin 4) (Fin 3) K) (hB : Function.Injective B.mulVec)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (hz : ∀ i : Fin 3, eval (B.mulVec (Pi.single i 1)) F = 0)
    (hg : ∀ i : Fin 3, HessianTheorem11.gradient F (B.mulVec (Pi.single i 1)) = 0)
    (x : Fin 3 → K) (hFx : eval (B.mulVec x) F = 0)
    (hgx : HessianTheorem11.gradient F (B.mulVec x) = 0)
    (hdist : ∀ i : Fin 3, B.mulVec x ∉
      Submodule.span K ({B.mulVec (Pi.single i 1)} : Set (Fin 4 → K))) :
    ∃ i j : Fin 3, i ≠ j ∧ ∀ s t : K,
      eval (s • B.mulVec (Pi.single i 1) + t • B.mulVec (Pi.single j 1)) F = 0 ∧
      HessianTheorem11.gradient F
        (s • B.mulVec (Pi.single i 1) + t • B.mulVec (Pi.single j 1)) = 0 := by
  have hzcoord : ∃ i : Fin 3, x i = 0 := by
    by_contra! h
    exact not_fourth_zero_of_independent_singular_columns B hB F hF hirr hz hg x h hFx
  obtain ⟨i,hi⟩ := hzcoord
  have helper (j k : Fin 3) (hjk : j ≠ k)
      (he : x = x j • (Pi.single j (1 : K) : Fin 3 → K) +
        x k • (Pi.single k (1 : K) : Fin 3 → K)) :
      ∃ i j : Fin 3, i ≠ j ∧ ∀ s t : K,
        eval (s • B.mulVec (Pi.single i 1) + t • B.mulVec (Pi.single j 1)) F = 0 ∧
        HessianTheorem11.gradient F
          (s • B.mulVec (Pi.single i 1) + t • B.mulVec (Pi.single j 1)) = 0 := by
    refine ⟨j,k,hjk,?_⟩
    have hspan : B.mulVec x ∈ Submodule.span K
        ({B.mulVec (Pi.single j 1),B.mulVec (Pi.single k 1)} : Set (Fin 4 → K)) := by
      apply Submodule.mem_span_pair.mpr
      refine ⟨x j,x k,?_⟩
      conv_rhs => rw [he]
      simp only [Matrix.mulVec_add,Matrix.mulVec_smul]
    intro s t
    apply singular_span_of_nonproportional_third F hF _ _ (B.mulVec x)
      (hz j) (hg j) (hz k) (hg k) hgx hspan (hdist j) (hdist k)
    exact Submodule.mem_span_pair.mpr ⟨s,t,rfl⟩
  fin_cases i
  · apply helper 1 2 (by decide)
    ext j; fin_cases j <;> simp_all [Pi.smul_apply,smul_eq_mul]
  · apply helper 0 2 (by decide)
    ext j; fin_cases j <;> simp_all [Pi.smul_apply,smul_eq_mul]
  · apply helper 0 1 (by decide)
    ext j; fin_cases j <;> simp_all [Pi.smul_apply,smul_eq_mul]

end CubicTenVariables.CubicSingularGeneralPosition

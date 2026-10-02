import CubicTenVariables.MicrolocalPromotionCover
import CubicTenVariables.ConeComponentSurfaceSlicingEndpoint

/-!
# Surface-slicing data through the promoted microlocal cover

Only an original table component can survive the residual construction as a
high-dimensional component.  Every genuine residual and every incoming
next-depth component has coordinate-ring dimension at most the target `r`;
therefore the high branch, whose Hilbert datum has dimension `r + 1`, is
impossible for those components.

Consequently surface-slicing data are required only for the original table.
This gives the direct no-Salberger version of `exists_part_bound`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section

namespace CubicTenVariables.MicrolocalPromotionCover

open MvPolynomial HessianTheorem11 TranslatedDepthSeven
open ProjectiveMicrolocalData ProjectiveMicrolocalModels RationalConeClosure
open ConeComponentProgressionCount MicrolocalPromotedPartition
open ConeComponentSurfaceSlicingEndpoint

attribute [local instance] MvPolynomial.gradedAlgebra Classical.propDecidable

/-- A component of coordinate-ring dimension at most `r` has surface-slicing
data vacuously: a high witness would force its dimension to be `r + 1`. -/
theorem highComponentSurfaceSlicingData_of_dimension_le
    {N r : ℕ} {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    (hlow : ringKrullDim (MvPolynomial (Fin (N + 1)) ℚ ⧸ I) ≤
      (r : WithBot ℕ∞)) :
    HighComponentSurfaceSlicingData r I := by
  intro d _hprime _hgeometric hdimension _hd
  have hstrict : (r : WithBot ℕ∞) <
      ringKrullDim (MvPolynomial (Fin (N + 1)) ℚ ⧸ I) := by
    rw [hdimension.1]
    exact_mod_cast Nat.lt_succ_self r
  exact (not_lt_of_ge hlow hstrict).elim

/-- The residual cover carries high-component slicing data using only the
data on the original table.  If the residual is the original component, use
the supplied datum; otherwise its proved dimension drop makes the datum
vacuous. -/
theorem exists_residual_cover_of_surfaceSlicing {N r c : ℕ}
    (I : Fin c → Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hprime : ∀ i, (I i).IsPrime)
    (hhom : ∀ i, (I i).IsHomogeneous
      (homogeneousSubmodule (Fin (N + 1)) ℚ))
    (g : Fin c → MvPolynomial (Fin (N + 1)) ℚ)
    (Z : Set (Fin (N + 1) → ℚ))
    (hcase : ∀ i, ComponentCondition r (I i) ∨
      affineIdealZeroLocus (I i) ⊆ Z ∨
      ∃ e : ℕ, 0 < e ∧ (g i).IsHomogeneous e ∧
        ringKrullDim (MvPolynomial (Fin (N + 1)) ℚ ⧸
          ConePrincipalOpen.residualIdeal (I i) (g i)) ≤
            (r : WithBot ℕ∞))
    (slicing : ∀ i, HighComponentSurfaceSlicingData r (I i)) :
    ∃ (k : ℕ) (J : Fin k → Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
      (∀ a, ComponentCondition r (J a)) ∧
      (∀ a, HighComponentSurfaceSlicingData r (J a)) ∧
      ∀ x, (∃ i, x ∈ affineIdealZeroLocus (I i)) → x ∉ Z →
        x ∉ promotionOpen I g →
          ∃ a, x ∈ affineIdealZeroLocus (J a) := by
  classical
  let Active := {i : Fin c // ¬ affineIdealZeroLocus (I i) ⊆ Z}
  let J0 : Active → Ideal (MvPolynomial (Fin (N + 1)) ℚ) := fun i =>
    if ComponentCondition r (I i) then I i
    else ConePrincipalOpen.residualIdeal (I i) (g i)
  have hJ (a : Active) : ComponentCondition r (J0 a) := by
    dsimp [J0]
    split_ifs with hgood
    · exact hgood
    · rcases hcase a with hcomponent | hcontained | ⟨e, he, hg, hdim⟩
      · exact (hgood hcomponent).elim
      · exact (a.property hcontained).elim
      · exact ⟨residual_ne_top _ (hprime a) (hhom a) _ e he hg,
          HomogeneousPrincipalOpen.residual_isHomogeneous _ (hhom a) _ e hg,
          Or.inl hdim⟩
  have hJslice (a : Active) : HighComponentSurfaceSlicingData r (J0 a) := by
    dsimp [J0]
    split_ifs with hgood
    · exact slicing a
    · rcases hcase a with hcomponent | hcontained | ⟨_e, _he, _hg, hdim⟩
      · exact (hgood hcomponent).elim
      · exact (a.property hcontained).elim
      · exact highComponentSurfaceSlicingData_of_dimension_le hdim
  refine ⟨Fintype.card Active,
    fun a => J0 ((Fintype.equivFin Active).symm a),
    (fun a => hJ _), (fun a => hJslice _), ?_⟩
  intro x ⟨i, hi⟩ hxZ hxU
  have hactive : ¬ affineIdealZeroLocus (I i) ⊆ Z :=
    fun hsubset => hxZ (hsubset hi)
  let a : Active := ⟨i, hactive⟩
  refine ⟨Fintype.equivFin Active a, ?_⟩
  simp only [Equiv.symm_apply_apply]
  dsimp [J0]
  split_ifs with hgood
  · exact hi
  · apply mem_affineIdealZeroLocus_sup_span_singleton _ _ x hi
    by_contra hnonzero
    exact hxU ⟨i, hi, hnonzero⟩

variable {t : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}

/-- Incoming components from depth `j+1` retain the actual dimension bound,
rather than only its disjunction inside `ComponentCondition`. -/
theorem exists_incoming_cover_with_dimension_le (h : Geometry F f)
    (hF : Anisotropic (map (Int.castRingHom ℚ) F))
    (j : ℕ) (hj : j = 3 ∨ j = 4) :
    ∃ (k : ℕ) (J : Fin k → Ideal (MvPolynomial (Fin 10) ℚ)),
      (∀ a, J a ≠ ⊤) ∧
      (∀ a, (J a).IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ)) ∧
      (∀ a, ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸ J a) ≤
        ((8 - j : ℕ) : WithBot ℕ∞)) ∧
      ∀ x ∈ filtration f (j + 1),
        ∃ a, x ∈ affineIdealZeroLocus (J a) := by
  obtain ⟨c, _Y, _s, G, _d, hcover, hcomp⟩ :=
    MicrolocalRationalComponents.exists_components h hF
      (j := j + 1) (by omega) (by omega)
  refine ⟨c, fun i => IntegralModelDimension.rationalIdeal (G i),
    (fun i => (hcomp i).2.2.2.2.1.ne_top),
    (fun i => (hcomp i).2.2.2.2.2.2.1), ?_, ?_⟩
  · intro i
    have hdim := (hcomp i).2.2.2.2.2.2.2.2.1
    simpa only [show 10 - (j + 1 + 1) = 8 - j by omega] using hdim
  · intro x hx
    have hR : rationalEmbedding x ∈ rationalDepth f (j + 1) := by
      change x ∈ rationalPoints (rationalDepth f (j + 1))
      rw [rationalDepth_points h (by omega)]
      simpa only [filtration, if_neg (by omega : j + 1 ≠ 0)] using hx
    rw [hcover] at hR
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hR
    refine ⟨i, ?_⟩
    change ∀ P ∈ IntegralModelDimension.rationalIdeal (G i), eval x P = 0
    rw [(hcomp i).2.2.1]
    intro P hP
    exact hP x hi

/-- Exact promoted-part cover carrying slicing data.  The caller supplies it
only for the original classified table. -/
theorem exists_part_cover_of_surfaceSlicing (h : Geometry F f)
    (hF : Anisotropic (map (Int.castRingHom ℚ) F))
    (j : Fin 6) (hj : j.val = 3 ∨ j.val = 4) {c : ℕ}
    (I : Fin c → Ideal (MvPolynomial (Fin 10) ℚ))
    (hprime : ∀ i, (I i).IsPrime)
    (hhom : ∀ i, (I i).IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ))
    (hcover : ∀ x ∈ filtration f j.val,
      ∃ i, x ∈ affineIdealZeroLocus (I i))
    (g : Fin c → MvPolynomial (Fin 10) ℚ)
    (hcase : ∀ i, ComponentCondition (8 - j.val) (I i) ∨
      affineIdealZeroLocus (I i) ⊆ filtration f (j.val + 1) ∨
      ∃ e : ℕ, 0 < e ∧ (g i).IsHomogeneous e ∧
        ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸
          ConePrincipalOpen.residualIdeal (I i) (g i)) ≤
            ((8 - j.val : ℕ) : WithBot ℕ∞))
    (slicing : ∀ i,
      HighComponentSurfaceSlicingData (8 - j.val) (I i))
    (U : ℕ → Set (Fin 10 → ℚ)) (hU : Compatible f U)
    (hopen : U j.val = promotionOpen I g) :
    ∃ (k : ℕ) (J : Fin k → Ideal (MvPolynomial (Fin 10) ℚ)),
      (∀ a, ComponentCondition (8 - j.val) (J a)) ∧
      (∀ a, HighComponentSurfaceSlicingData (8 - j.val) (J a)) ∧
      ∀ x ∈ part f U j, ∃ a, x ∈ affineIdealZeroLocus (J a) := by
  classical
  obtain ⟨k, J, hJ, hJslice, hJcover⟩ :=
    exists_residual_cover_of_surfaceSlicing I hprime hhom g
      (filtration f (j.val + 1)) hcase slicing
  obtain ⟨l, K, hKproper, hKhom, hKdim, hKcover⟩ :=
    exists_incoming_cover_with_dimension_le h hF j.val hj
  let Index := Fin k ⊕ Fin l
  let M : Index → Ideal (MvPolynomial (Fin 10) ℚ) := Sum.elim J K
  have hMcondition : ∀ a : Index,
      ComponentCondition (8 - j.val) (M a) := by
    intro a
    cases a with
    | inl a => exact hJ a
    | inr a => exact ⟨hKproper a, hKhom a, Or.inl (hKdim a)⟩
  have hMslicing : ∀ a : Index,
      HighComponentSurfaceSlicingData (8 - j.val) (M a) := by
    intro a
    cases a with
    | inl a => exact hJslice a
    | inr a => exact highComponentSurfaceSlicingData_of_dimension_le (hKdim a)
  refine ⟨Fintype.card Index,
    fun a => M ((Fintype.equivFin Index).symm a),
    (fun a => hMcondition _), (fun a => hMslicing _), ?_⟩
  intro x hx
  rw [part_eq_source U j (by omega)] at hx
  have hMx : ∃ a : Index, x ∈ affineIdealZeroLocus (M a) := by
    rcases hx.1 with hxCurrent | hxIncoming
    · obtain ⟨a, ha⟩ := hJcover x (hcover x hxCurrent.1.1)
          hxCurrent.1.2 (hopen ▸ hxCurrent.2)
      exact ⟨Sum.inl a, ha⟩
    · have hnext := PromotedFrequencyPartition.layer_subset
          (filtration f) (by omega) (hU.2.2 (j.val + 1) (by omega) hxIncoming)
      obtain ⟨a, ha⟩ := hKcover x hnext
      exact ⟨Sum.inr a, ha⟩
  obtain ⟨a, ha⟩ := hMx
  exact ⟨Fintype.equivFin Index a, by
    simpa only [Equiv.symm_apply_apply] using ha⟩

/-- Direct no-Salberger replacement for `exists_part_bound`.  Surface
slicing is requested only on the original classified table; residual and
incoming components are discharged from their literal dimension bounds. -/
theorem exists_part_bound_of_surfaceSlicing
    (h : Geometry F f)
    (hF : Anisotropic (map (Int.castRingHom ℚ) F))
    (j : Fin 6) (hj : j.val = 3 ∨ j.val = 4) {c : ℕ}
    (I : Fin c → Ideal (MvPolynomial (Fin 10) ℚ))
    (hprime : ∀ i, (I i).IsPrime)
    (hhom : ∀ i, (I i).IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ))
    (hcover : ∀ x ∈ filtration f j.val,
      ∃ i, x ∈ affineIdealZeroLocus (I i))
    (g : Fin c → MvPolynomial (Fin 10) ℚ)
    (hcase : ∀ i, ComponentCondition (8 - j.val) (I i) ∨
      affineIdealZeroLocus (I i) ⊆ filtration f (j.val + 1) ∨
      ∃ e : ℕ, 0 < e ∧ (g i).IsHomogeneous e ∧
        ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸
          ConePrincipalOpen.residualIdeal (I i) (g i)) ≤
            ((8 - j.val : ℕ) : WithBot ℕ∞))
    (slicing : ∀ i,
      HighComponentSurfaceSlicingData (8 - j.val) (I i))
    (U : ℕ → Set (Fin 10 → ℚ)) (hU : Compatible f U)
    (hopen : U j.val = promotionOpen I g) (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (u : Fin 10 → ℝ) (L : ℝ), 0 ≤ L →
      ∀ (m : ℕ), 0 < m → ∀ b : Fin 10 → ℤ,
      ((points (part f U j) u L m b).card : ℝ) ≤
        C * (2 + ‖u‖ + L + (m : ℝ)) ^ epsilon *
          (1 + L / (m : ℝ)) ^ (8 - j.val) := by
  obtain ⟨k, J, hJ, hJslicing, hJcover⟩ :=
    exists_part_cover_of_surfaceSlicing h hF j hj I hprime hhom hcover g
      hcase slicing U hU hopen
  obtain ⟨C, hC, hcount⟩ :=
    exists_n10_high_level_bound_of_surfaceSlicing
      j.val hj J hJ hJslicing epsilon hepsilon
  exact ⟨C, hC, hcount _ hJcover⟩

end CubicTenVariables.MicrolocalPromotionCover

import CubicTenVariables.FixedLeadingSurfaceParallelLinesCount
import CubicTenVariables.FrameRestrictionIrreducibility
import TranslatedDepthSeven.IndependentFamilyComplementDualInternal

/-!
# Transporting actual parallel lines to one coordinate direction

The transverse coordinates of a line after an invertible rational linear
change determine that line. Thus distinct actual parallel lines inject
into the coefficient zero locus used by the proved d² bound. A rational
coordinate frame with any prescribed nonzero first vector is constructed
by extending that vector to a basis.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceParallelLineTransport

open MvPolynomial TranslatedDepthSeven Module
open HessianTheorem11.PolynomialRestriction
open FixedLeadingSurfaceParallelLines FrameRestrictionIrreducibility

def affineLine (base v : Fin 3 → ℚ) : Set (Fin 3 → ℚ) :=
  Set.range (fun t : ℚ => base + t • v)

def transverseBase (e : (Fin 3 → ℚ) ≃ₗ[ℚ] (Fin 3 → ℚ))
    (base : Fin 3 → ℚ) : Fin 2 → ℚ := fun i => e.symm base i.succ

theorem exists_direction_coordinates (v : Fin 3 → ℚ) (hv : v ≠ 0) :
    ∃ e : (Fin 3 → ℚ) ≃ₗ[ℚ] (Fin 3 → ℚ), e (Pi.single 0 1) = v := by
  classical
  let u : Fin 1 → (Fin 3 → ℚ) := fun _ => v
  have hu : LinearIndependent ℚ u := LinearIndependent.of_subsingleton 0 hv
  obtain ⟨b₀, hb₀⟩ := exists_basis_finSum_extending_independent_family u hu
  have hdim : finrank ℚ (Fin 3 → ℚ) = 3 := by simp
  let E : (Fin 1 ⊕ Fin (finrank ℚ (Fin 3 → ℚ) - 1)) ≃ Fin 3 :=
    finSumFinEquiv.trans (finCongr (by rw [hdim]))
  let b := b₀.reindex E
  have hE : E (Sum.inl 0) = 0 := by rfl
  have hb : b 0 = v := by
    rw [← hE]
    simpa only [b, Basis.reindex_apply, Equiv.symm_apply_apply] using hb₀ 0
  refine ⟨b.equivFun.symm, ?_⟩
  apply b.equivFun.injective
  rw [LinearEquiv.apply_symm_apply, ← hb]
  ext i
  simp [Basis.equivFun_self, Pi.single_apply, eq_comm]

theorem coordinate_line_point
    (e : (Fin 3 → ℚ) ≃ₗ[ℚ] (Fin 3 → ℚ))
    (v base : Fin 3 → ℚ) (he : e (Pi.single 0 1) = v) (t : ℚ) :
    e (Fin.cons t (transverseBase e base)) =
      base + (t - e.symm base 0) • v := by
  have hcoord : Fin.cons t (transverseBase e base) =
      e.symm base + (t - e.symm base 0) • (Pi.single 0 (1 : ℚ) : Fin 3 → ℚ) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [transverseBase, Fin.succ_ne_zero]
  rw [hcoord, map_add, map_smul, LinearEquiv.apply_symm_apply, he]

theorem affineLine_eq_coordinate_range
    (e : (Fin 3 → ℚ) ≃ₗ[ℚ] (Fin 3 → ℚ))
    (v base : Fin 3 → ℚ) (he : e (Pi.single 0 1) = v) :
    affineLine base v = Set.range (fun t : ℚ => e (Fin.cons t (transverseBase e base))) := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t + e.symm base 0, ?_⟩
    dsimp only
    rw [coordinate_line_point e v base he]
    simp
  · rintro ⟨t, rfl⟩
    exact ⟨t - e.symm base 0, (coordinate_line_point e v base he t).symm⟩

theorem affineLine_eq_of_transverseBase_eq
    (e : (Fin 3 → ℚ) ≃ₗ[ℚ] (Fin 3 → ℚ))
    (v base₁ base₂ : Fin 3 → ℚ) (he : e (Pi.single 0 1) = v)
    (hbase : transverseBase e base₁ = transverseBase e base₂) :
    affineLine base₁ v = affineLine base₂ v := by
  rw [affineLine_eq_coordinate_range e v base₁ he,
    affineLine_eq_coordinate_range e v base₂ he, hbase]

theorem totalDegree_restrict_le (e : (Fin 3 → ℚ) ≃ₗ[ℚ] (Fin 3 → ℚ))
    (g : MvPolynomial (Fin 3) ℚ) :
    (restrict (coordinateMatrix e) g).totalDegree ≤ g.totalDegree := by
  nth_rw 1 [← g.sum_homogeneousComponent]
  change (aeval (linearForms (coordinateMatrix e))
    (∑ j ∈ Finset.range (g.totalDegree + 1), homogeneousComponent j g)).totalDegree ≤ _
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro j hj
  exact (homogeneous_restrict _ _ (homogeneousComponent_isHomogeneous j g)).totalDegree_le.trans
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

theorem lineRestriction_restrict_eq_zero
    (e : (Fin 3 → ℚ) ≃ₗ[ℚ] (Fin 3 → ℚ))
    (v base : Fin 3 → ℚ) (he : e (Pi.single 0 1) = v)
    (g : MvPolynomial (Fin 3) ℚ)
    (hline : ∀ t : ℚ, eval (base + t • v) g = 0) :
    lineRestriction (restrict (coordinateMatrix e) g) (transverseBase e base) = 0 := by
  apply Polynomial.funext
  intro t
  rw [eval_lineRestriction, eval_restrict, coordinateMatrix_mulVec,
    coordinate_line_point e v base he]
  simpa only [Polynomial.eval_zero] using hline (t - e.symm base 0)

/-- The line family consists of actual distinct subsets of affine space;
the transverse coordinates, not a claimed multiplicity bound, supply the
injection into the finite coefficient locus. -/
theorem parallel_line_family_card_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ℕ} (hd : 1 ≤ d) (g : MvPolynomial (Fin 3) ℚ)
    (hdegree : g.totalDegree ≤ d) (hg : Irreducible g)
    (e : (Fin 3 → ℚ) ≃ₗ[ℚ] (Fin 3 → ℚ))
    (v : Fin 3 → ℚ) (he : e (Pi.single 0 1) = v)
    (hdir : 0 < (restrict (coordinateMatrix e) g).degreeOf 0)
    (base : ι → Fin 3 → ℚ)
    (hdistinct : Function.Injective (fun l => affineLine (base l) v))
    (hline : ∀ l, ∀ t : ℚ, eval (base l + t • v) g = 0) :
    Fintype.card ι ≤ d ^ 2 := by
  classical
  let S := Finset.univ.image (fun l => transverseBase e (base l))
  have hinj : Function.Injective (fun l => transverseBase e (base l)) := by
    intro l l' h
    apply hdistinct
    exact affineLine_eq_of_transverseBase_eq e v (base l) (base l') he h
  have hcard : S.card = Fintype.card ι := by
    simpa [S] using Finset.card_image_of_injective Finset.univ hinj
  rw [← hcard]
  apply rational_parallel_lines_card_le hd (restrict (coordinateMatrix e) g)
    ((totalDegree_restrict_le e g).trans hdegree) (restrict_irreducible e g hg) hdir S
  intro a ha
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp ha
  exact lineRestriction_restrict_eq_zero e v (base l) he g (hline l)

end CubicTenVariables.FixedLeadingSurfaceParallelLineTransport

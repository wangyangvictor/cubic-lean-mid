import CubicTenVariables.CubicSurfaceProjectiveSingular

/-! Independence of actual singular-point representatives follows from the
finite projective singular locus. No coordinate-frame premise is used. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace CubicTenVariables.CubicSurfaceSingularPointFrames
open MvPolynomial HessianTheorem11
open CubicSurfaceProjectiveSingular CubicSingularCollinear CubicSingularGeneralPosition
variable {K : Type*} [Field K] [IsAlgClosed K]

omit [IsAlgClosed K] in
private theorem pair_independent (p q : Fin 4 → K) (hp : p ≠ 0)
    (hqp : q ∉ Submodule.span K ({p} : Set (Fin 4 → K))) :
    LinearIndependent K ![p,q] := by
  apply (LinearIndependent.pair_iff' hp).mpr
  intro a ha
  exact hqp (Submodule.mem_span_singleton.mpr ⟨a,ha⟩)

/-- Any three distinct projective singular points have independent vectors
if the projective singular locus is finite. -/
theorem independent_three
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hfin : (singularPoints F).Finite) (v : Fin 3 → Fin 4 → K)
    (hv : ∀ i, v i ≠ 0)
    (hz : ∀ i, eval (v i) F = 0 ∧ HessianTheorem11.gradient F (v i) = 0)
    (hdist : ∀ i j, i ≠ j → v i ∉ Submodule.span K ({v j} : Set (Fin 4 → K))) :
    LinearIndependent K v := by
  have hpq : LinearIndependent K ![v 1,v 2] :=
    pair_independent _ _ (hv 1) (hdist 2 1 (by decide))
  have hn : v 0 ∉ Submodule.span K ({v 1,v 2} : Set (Fin 4 → K)) := by
    intro hm
    apply no_singular_span_pair F hfin (v 1) (v 2) hpq
    intro s t
    exact singular_span_of_nonproportional_third F hF _ _ (v 0)
      (hz 1).1 (hz 1).2 (hz 2).1 (hz 2).2 (hz 0).2 hm
      (hdist 0 1 (by decide)) (hdist 0 2 (by decide)) _
      (Submodule.mem_span_pair.mpr ⟨s,t,rfl⟩)
  have hi : LinearIndependent K ![v 0,v 1,v 2] :=
    linearIndependent_fin_cons.mpr ⟨hpq,by simpa only [Matrix.range_cons_cons_empty] using hn⟩
  convert hi using 1
  ext i
  fin_cases i <;> rfl

/-- Any four distinct projective singular points of an integral cubic surface
have independent representatives when the singular locus is finite. -/
theorem independent_four
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (hfin : (singularPoints F).Finite) (v : Fin 4 → Fin 4 → K)
    (hv : ∀ i, v i ≠ 0)
    (hz : ∀ i, eval (v i) F = 0 ∧ HessianTheorem11.gradient F (v i) = 0)
    (hdist : ∀ i j, i ≠ j → v i ∉ Submodule.span K ({v j} : Set (Fin 4 → K))) :
    LinearIndependent K v := by
  let w : Fin 3 → Fin 4 → K := fun i => v i.succ
  have hw : LinearIndependent K w := independent_three F hF hfin w
    (fun i => hv i.succ) (fun i => hz i.succ)
    (fun i j hij => hdist _ _ (fun h => hij (Fin.succ_inj.mp h)))
  let B := pointMatrix w
  have hB : Function.Injective B.mulVec := pointMatrix_injective w hw
  have hn : v 0 ∉ Submodule.span K (Set.range w) := by
    intro hm
    have hmB : v 0 ∈ LinearMap.range B.mulVecLin := by
      rw [Matrix.range_mulVecLin]
      exact hm
    obtain ⟨x,hx⟩ := hmB
    have hx' : B.mulVec x = v 0 := hx
    obtain ⟨i,j,hij,hline⟩ := exists_singular_line_of_fourth_in_plane B hB F hF hirr
      (fun i => by simpa only [B,pointMatrix_single,w] using (hz i.succ).1)
      (fun i => by simpa only [B,pointMatrix_single,w] using (hz i.succ).2)
      x (by simpa only [hx'] using (hz 0).1)
      (by simpa only [hx'] using (hz 0).2)
      (fun i => by
        simpa only [hx',B,pointMatrix_single,w] using
          (hdist 0 i.succ (Ne.symm (Fin.succ_ne_zero i))))
    have hpq : LinearIndependent K ![w i,w j] := pair_independent _ _ (hv i.succ)
      (hdist j.succ i.succ (fun h => hij (Fin.succ_inj.mp h).symm))
    apply no_singular_span_pair F hfin (w i) (w j) hpq
    simpa only [B,pointMatrix_single] using hline
  exact linearIndependent_fin_succ.mpr ⟨hw,hn⟩

end CubicTenVariables.CubicSurfaceSingularPointFrames

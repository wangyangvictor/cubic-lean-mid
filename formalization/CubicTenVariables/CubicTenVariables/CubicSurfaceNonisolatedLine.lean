import CubicTenVariables.CubicSurfaceSingularCoordinateTransport
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! Five distinct actual singular points of an integral cubic surface force
an actual singular line. In particular a nonfinite projective singular set
contains a line, without any dimension, purity, or classification premise. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace CubicTenVariables.CubicSurfaceNonisolatedLine
open MvPolynomial HessianTheorem11 Module
open CubicSurfaceProjectiveSingular CubicSingularCollinear CubicSingularGeneralPosition
open CubicSurfaceSingularCoordinateTransport
variable {K : Type*} [Field K] [IsAlgClosed K]

omit [IsAlgClosed K] in
private theorem pair_independent (p q : Fin 4 → K) (hp : p ≠ 0)
    (hqp : q ∉ Submodule.span K ({p} : Set (Fin 4 → K))) :
    LinearIndependent K ![p,q] := by
  apply (LinearIndependent.pair_iff' hp).mpr
  intro a ha
  exact hqp (Submodule.mem_span_singleton.mpr ⟨a,ha⟩)

omit [IsAlgClosed K] in
/-- Any three distinct projective singular points have independent vectors
if there is no singular line. -/
private theorem independent_three
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hno : ∀ p q : Fin 4 → K, LinearIndependent K ![p,q] →
      ¬ (∀ s t : K, eval (s • p + t • q) F = 0 ∧ gradient F (s • p + t • q) = 0)) (v : Fin 3 → Fin 4 → K)
    (hv : ∀ i, v i ≠ 0)
    (hz : ∀ i, eval (v i) F = 0 ∧ HessianTheorem11.gradient F (v i) = 0)
    (hdist : ∀ i j, i ≠ j → v i ∉ Submodule.span K ({v j} : Set (Fin 4 → K))) :
    LinearIndependent K v := by
  have hpq : LinearIndependent K ![v 1,v 2] :=
    pair_independent _ _ (hv 1) (hdist 2 1 (by decide))
  have hn : v 0 ∉ Submodule.span K ({v 1,v 2} : Set (Fin 4 → K)) := by
    intro hm
    apply hno (v 1) (v 2) hpq
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
have independent representatives when there is no singular line. -/
private theorem independent_four
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (hno : ∀ p q : Fin 4 → K, LinearIndependent K ![p,q] →
      ¬ (∀ s t : K, eval (s • p + t • q) F = 0 ∧ gradient F (s • p + t • q) = 0)) (v : Fin 4 → Fin 4 → K)
    (hv : ∀ i, v i ≠ 0)
    (hz : ∀ i, eval (v i) F = 0 ∧ HessianTheorem11.gradient F (v i) = 0)
    (hdist : ∀ i j, i ≠ j → v i ∉ Submodule.span K ({v j} : Set (Fin 4 → K))) :
    LinearIndependent K v := by
  let w : Fin 3 → Fin 4 → K := fun i => v i.succ
  have hw : LinearIndependent K w := independent_three F hF hno w
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
    apply hno (w i) (w j) hpq
    simpa only [B,pointMatrix_single] using hline
  exact linearIndependent_fin_succ.mpr ⟨hw,hn⟩

private theorem not_five_without_line
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (hno : ∀ p q : Fin 4 → K, LinearIndependent K ![p,q] →
      ¬ (∀ s t : K, eval (s • p + t • q) F = 0 ∧ gradient F (s • p + t • q) = 0)) (v : Fin 5 → Fin 4 → K)
    (hv : ∀ i, v i ≠ 0)
    (hz : ∀ i, eval (v i) F = 0 ∧ HessianTheorem11.gradient F (v i) = 0)
    (hdist : ∀ i j, i ≠ j → v i ∉ Submodule.span K ({v j} : Set (Fin 4 → K))) :
    False := by
  let w : Fin 4 → Fin 4 → K := fun i => v i.castSucc
  have hw : LinearIndependent K w := independent_four F hF hirr hno w
    (fun i => hv i.castSucc) (fun i => hz i.castSucc)
    (fun i j hij => hdist _ _ (fun h => hij (Fin.castSucc_inj.mp h)))
  let b : Basis (Fin 4) K (Fin 4 → K) :=
    basisOfLinearIndependentOfCardEqFinrank hw (by simp)
  let e : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K) := b.equivFun.symm
  have he (i : Fin 4) : e (Pi.single i 1) = v i.castSucc := by
    simp only [e,Basis.equivFun_symm_single,b,coe_basisOfLinearIndependentOfCardEqFinrank,w]
  obtain ⟨i,t,hi⟩ := singular_in_frame e F hF hirr
    (fun i => by simpa only [he] using (hz i.castSucc).1)
    (fun i => by simpa only [he] using (hz i.castSucc).2)
    (v 4) (hz 4).1 (hz 4).2
  apply hdist 4 i.castSucc (by
    intro h
    have hh := congrArg Fin.val h
    have hb := i.isLt
    change 4 = i.val at hh
    omega)
  apply Submodule.mem_span_singleton.mpr
  exact ⟨t,by simpa only [he] using hi.symm⟩

/-- Five projectively distinct actual singular representatives force a
literal two-dimensional singular vector space. -/
theorem exists_line_of_five
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (v : Fin 5 → Fin 4 → K) (hv : ∀ i, v i ≠ 0)
    (hz : ∀ i, eval (v i) F = 0 ∧ gradient F (v i) = 0)
    (hdist : ∀ i j, i ≠ j → v i ∉ Submodule.span K ({v j} : Set (Fin 4 → K))) :
    ∃ L : Submodule K (Fin 4 → K), finrank K L = 2 ∧
      ∀ x ∈ L, eval x F = 0 ∧ gradient F x = 0 := by
  classical
  have hex : ∃ p q : Fin 4 → K, LinearIndependent K ![p,q] ∧
      ∀ s t : K, eval (s • p + t • q) F = 0 ∧ gradient F (s • p + t • q) = 0 := by
    by_contra hn
    exact not_five_without_line F hF hirr (fun p q hp hline => hn ⟨p,q,hp,hline⟩) v hv hz hdist
  obtain ⟨p,q,hpq,hline⟩ := hex
  refine ⟨Submodule.span K {p,q}, ?_, ?_⟩
  · have hr : Set.range ![p,q] = ({p,q} : Set (Fin 4 → K)) := by
      ext x
      simp [eq_comm, or_comm]
    have hh := finrank_span_eq_card hpq
    rw [hr] at hh
    exact hh
  · intro x hx
    obtain ⟨s,t,rfl⟩ := Submodule.mem_span_pair.mp hx
    exact hline s t

/-- A nonfinite actual projective singular set of an integral cubic surface
contains a genuine singular line. No dimension or reducedness premise is used. -/
theorem exists_line_of_not_finite
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (hinf : ¬ (singularPoints F).Finite) :
    ∃ L : Submodule K (Fin 4 → K), finrank K L = 2 ∧
      ∀ x ∈ L, eval x F = 0 ∧ gradient F x = 0 := by
  classical
  let f : Fin 5 ↪ singularPoints F :=
    ⟨fun i => (Set.Infinite.natEmbedding (singularPoints F) hinf) i.val,
      fun i j h => Fin.ext ((Set.Infinite.natEmbedding (singularPoints F) hinf).injective h)⟩
  choose v hv hmk hz hg using fun i : Fin 5 => (f i).property
  apply exists_line_of_five F hF hirr v hv (fun i => ⟨hz i,hg i⟩)
  intro i j hij
  apply not_mem_span_of_mk_ne _ _ (hv i) (hv j)
  intro heq
  apply hij
  apply f.injective
  apply Subtype.ext
  rw [← hmk i,← hmk j]
  exact heq

end CubicTenVariables.CubicSurfaceNonisolatedLine

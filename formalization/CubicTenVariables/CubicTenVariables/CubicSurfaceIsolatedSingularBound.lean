import CubicTenVariables.CubicSurfaceSingularPointFrames
import CubicTenVariables.CubicSurfaceSingularCoordinateTransport
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! An integral cubic surface over an algebraically closed field has at most
four isolated projective singular points. Here isolatedness is stated as the
finiteness of the actual projective singular-point set; all representatives,
independence, coordinate changes, and cardinality arguments are proved. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace CubicTenVariables.CubicSurfaceIsolatedSingularBound
open MvPolynomial HessianTheorem11 Module
open CubicSurfaceProjectiveSingular CubicSurfaceSingularPointFrames
open CubicSurfaceSingularCoordinateTransport
variable {K : Type*} [Field K] [IsAlgClosed K]

/-- Five pairwise projectively distinct singular representatives cannot exist
when the actual projective singular locus is finite. -/
theorem not_five_distinct_singular_vectors
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (hfin : (singularPoints F).Finite) (v : Fin 5 → Fin 4 → K)
    (hv : ∀ i, v i ≠ 0)
    (hz : ∀ i, eval (v i) F = 0 ∧ HessianTheorem11.gradient F (v i) = 0)
    (hdist : ∀ i j, i ≠ j → v i ∉ Submodule.span K ({v j} : Set (Fin 4 → K))) :
    False := by
  let w : Fin 4 → Fin 4 → K := fun i => v i.castSucc
  have hw : LinearIndependent K w := independent_four F hF hirr hfin w
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

/-- The actual finite projective singular-point set has cardinality at most
four. No characteristic restriction or classification premise is used. -/
theorem ncard_singularPoints_le_four
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (hfin : (singularPoints F).Finite) : (singularPoints F).ncard ≤ 4 := by
  classical
  letI : Fintype (singularPoints F) := hfin.fintype
  by_contra! hn
  have hcard : Fintype.card (Fin 5) ≤ Fintype.card (singularPoints F) := by
    rw [Fintype.card_fin,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
    omega
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
  choose v hv hmk hz hg using fun i : Fin 5 => (f i).property
  apply not_five_distinct_singular_vectors F hF hirr hfin v hv (fun i => ⟨hz i,hg i⟩)
  intro i j hij
  apply not_mem_span_of_mk_ne _ _ (hv i) (hv j)
  intro heq
  apply hij
  apply f.injective
  apply Subtype.ext
  rw [← hmk i,← hmk j]
  exact heq

end CubicTenVariables.CubicSurfaceIsolatedSingularBound

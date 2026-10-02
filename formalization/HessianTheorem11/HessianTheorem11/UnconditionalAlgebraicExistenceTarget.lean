import HessianTheorem11.UnconditionalAlgebraicExistenceAction
import HessianTheorem11.UnconditionalOrbitCoefficients

/-! The literal extension-field target defined by the original finite
coefficient vanishing ideal. Closedness and base-field membership are proved
without claiming equality of ideals after base change. -/
noncomputable section
namespace HessianTheorem11.UnconditionalAlgebraicExistence
open MvPolynomial ReducedRelative ReducedOrbitCoordinates UnconditionalOrbitIdeal
variable {K E : Type*} [Field K] [IsAlgClosed K] [Field E] [Algebra K E] {n : ℕ}

def extendedTarget (d : ℕ) (S : Set (MvPolynomial (Fin n) K)) :
    Set (MvPolynomial (Fin n) E) :=
  {H | H.IsHomogeneous d ∧ coefficientVector (d := d) H ∈
    zeroLocus E (vanishingIdeal K (finiteTarget (d := d) S))}

theorem extendedTarget_homogeneous (d : ℕ) (S : Set (MvPolynomial (Fin n) K))
    (H : MvPolynomial (Fin n) E) (hH : H ∈ extendedTarget d S) : H.IsHomogeneous d := hH.1

theorem eval_extendedEquation {d : ℕ} (H : MvPolynomial (Fin n) E)
    (q : MvPolynomial (DegreeIndex n d) K) :
    eval (fun e => coeff e H) (rename Subtype.val (map (algebraMap K E) q)) =
      aeval (coefficientVector (d := d) H) q := by
  rw [eval_rename,eval_map]
  rfl

/-- This target is closed in the original coefficient-polynomial
convention, even if the original set S was not closed. -/
theorem extendedTarget_coefficientClosed (d : ℕ) (S : Set (MvPolynomial (Fin n) K)) :
    coefficientClosed (extendedTarget (E := E) d S) := by
  intro G hG
  have hhom : G.IsHomogeneous d := by
    intro e he
    by_contra hn
    have hp : coefficientVanishing (extendedTarget (E := E) d S) (X e) := by
      intro H hH
      simp only [eval_X]
      by_contra hne
      exact hn (hH.1 hne)
    have hz := hG (X e) hp
    exact he (by simpa only [eval_X] using hz)
  refine ⟨hhom,?_⟩
  intro q hq
  rw [← eval_extendedEquation]
  apply hG
  intro H hH
  rw [eval_extendedEquation]
  exact hH.2 q hq

theorem aeval_coefficientVector_map {d : ℕ} (G : MvPolynomial (Fin n) K)
    (q : MvPolynomial (DegreeIndex n d) K) :
    aeval (coefficientVector (d := d) (map (algebraMap K E) G)) q =
      algebraMap K E (eval (coefficientVector (d := d) G) q) := by
  have he : coefficientVector (d := d) (map (algebraMap K E) G) =
      (algebraMap K E) ∘ coefficientVector (d := d) G := by
    ext e
    exact coeff_map (algebraMap K E) G e.val
  change eval₂ (algebraMap K E) (coefficientVector (d := d) (map (algebraMap K E) G)) q = _
  rw [he]
  exact (eval₂_comp (algebraMap K E) (coefficientVector G) q).symm

theorem map_mem_extendedTarget (d : ℕ) (S : Set (MvPolynomial (Fin n) K))
    (hhom : ∀ H ∈ S, H.IsHomogeneous d) (G : MvPolynomial (Fin n) K) (hG : G ∈ S) :
    map (algebraMap K E) G ∈ extendedTarget d S := by
  refine ⟨(hhom G hG).map _,?_⟩
  intro q hq
  rw [aeval_coefficientVector_map]
  have hz := hq (coefficientVector (d := d) G) ⟨G,hG,rfl⟩
  change eval (coefficientVector (d := d) G) q = 0 at hz
  rw [hz,map_zero]

theorem map_notMem_extendedTarget (d : ℕ) (S : Set (MvPolynomial (Fin n) K))
    (hclosed : coefficientClosed S) (hhom : ∀ H ∈ S, H.IsHomogeneous d)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d) (hnot : F ∉ S) :
    map (algebraMap K E) F ∉ extendedTarget d S := by
  intro hf
  have hc : coefficientVector (d := d) F ∈ zeroLocus K
      (vanishingIdeal K (finiteTarget (d := d) S)) := by
    intro q hq
    have hz := hf.2 q hq
    rw [aeval_coefficientVector_map] at hz
    exact (algebraMap K E).injective (hz.trans (map_zero _).symm)
  rw [finiteTarget_zeroLocus S hclosed hhom] at hc
  obtain ⟨H,hH,he⟩ := hc
  have hh := congrArg (decode (d := d)) he
  rw [decode_coefficientVector H (hhom H hH),decode_coefficientVector F hF] at hh
  exact hnot (hh ▸ hH)

theorem aeval_finiteEquation {d : ℕ} (H : MvPolynomial (Fin n) E)
    (hH : H.IsHomogeneous d) (p : MvPolynomial (Fin n →₀ ℕ) K) :
    aeval (coefficientVector (d := d) H) (finiteEquation (d := d) p) =
      aeval (fun e => coeff e H) p := by
  rw [finiteEquation,MvPolynomial.comp_aeval_apply]
  have heq : (fun e : Fin n →₀ ℕ => aeval (coefficientVector (d := d) H)
      (if he : e ∈ degreeMonomials n d then
        (X ⟨e,he⟩ : MvPolynomial (DegreeIndex n d) K) else 0)) =
      (fun e => coeff e H) := by
    ext e
    by_cases he : e ∈ degreeMonomials n d
    · simp [he,coefficientVector]
    · simp [he,coeff_zero_outside_degree H hH e he]
  rw [heq]

/-- Every original coefficient equation, including equations with
arbitrary finite monomial support, holds on the extended target. -/
theorem extendedTarget_equations (d : ℕ) (S : Set (MvPolynomial (Fin n) K))
    (hhom : ∀ G ∈ S, G.IsHomogeneous d)
    (H : MvPolynomial (Fin n) E) (hH : H ∈ extendedTarget d S)
    (p : MvPolynomial (Fin n →₀ ℕ) K) (hp : coefficientVanishing S p) :
    aeval (fun e => coeff e H) p = 0 := by
  have hfinite : finiteEquation (d := d) p ∈ vanishingIdeal K (finiteTarget (d := d) S) := by
    rintro _ ⟨G,hG,rfl⟩
    change eval (coefficientVector (d := d) G) (finiteEquation (d := d) p) = 0
    rw [eval_finiteEquation G (hhom G hG)]
    exact hp G hG
  have he := hH.2 _ hfinite
  rwa [aeval_finiteEquation H hH.1] at he

end HessianTheorem11.UnconditionalAlgebraicExistence

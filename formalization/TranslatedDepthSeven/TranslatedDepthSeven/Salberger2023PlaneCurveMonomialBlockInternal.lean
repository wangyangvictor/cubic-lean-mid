import TranslatedDepthSeven.Salberger2023PlaneCurveLocalPacket
import TranslatedDepthSeven.PrincipalHomogeneousHypersurfaceDegreeInternal
import TranslatedDepthSeven.ProjectiveHilbertCoefficientExtension
import Mathlib.Data.Fintype.EquivFin

/-!
# The standard monomial block for a plane curve

For a nonzero homogeneous plane equation of degree `δ`, the degree-`δ`
piece of its principal quotient has dimension
`δ(δ+3)/2`: the full triangular block loses exactly the equation itself.
Selecting a basis from the literal coefficient-one monomials gives the
block used in Salberger's local determinant, including its sharp box bound.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

/-- The displayed triangular index enumerates every exponent vector in
three variables of the prescribed total degree. -/
theorem exists_affinePlaneMonomialIndex_exponent_eq
    (δ : ℕ) (d : Fin 3 →₀ ℕ) (hd : Finsupp.degree d = δ) :
    ∃ u : AffinePlaneMonomialIndex δ,
      affinePlaneMonomialExponent δ u = d := by
  have hsum : d 0 + d 1 + d 2 = δ := by
    rw [← hd, Finsupp.degree_eq_sum, Fin.sum_univ_three]
  let j : Fin (δ + 1) := ⟨d 1 + d 2, by omega⟩
  let a : Fin (j.1 + 1) := ⟨d 1, by dsimp only [j]; omega⟩
  refine ⟨⟨j, a⟩, ?_⟩
  apply Finsupp.ext
  intro i
  fin_cases i <;> simp [affinePlaneMonomialExponent, j, a] <;> omega

/-- Literal degree-`δ` monomials have the exact coefficient-one box bound
in arbitrary homogeneous coordinates. -/
theorem eval_affinePlaneHomogeneousMonomial_natAbs_le
    (δ V : ℕ) (u : AffinePlaneMonomialIndex δ)
    (x : Fin 3 → ℤ) (hx : ∀ i, (x i).natAbs ≤ V) :
    (eval x (affinePlaneHomogeneousMonomial ℤ δ u)).natAbs ≤ V ^ δ := by
  rw [affinePlaneHomogeneousMonomial, eval_monomial]
  simp only [one_mul]
  rw [Finsupp.prod_fintype]
  · rw [Fin.prod_univ_three]
    have hzero : (affinePlaneMonomialExponent δ u) 0 = δ - u.1.1 := by
      simp [affinePlaneMonomialExponent]
    have hone : (affinePlaneMonomialExponent δ u) 1 = u.2.1 := by
      simp [affinePlaneMonomialExponent]
    have htwo :
        (affinePlaneMonomialExponent δ u) 2 = u.1.1 - u.2.1 := by
      simp [affinePlaneMonomialExponent]
    rw [hzero, hone, htwo, Int.natAbs_mul, Int.natAbs_mul,
      Int.natAbs_pow, Int.natAbs_pow, Int.natAbs_pow]
    calc
      (x 0).natAbs ^ (δ - u.1.1) * (x 1).natAbs ^ u.2.1 *
          (x 2).natAbs ^ (u.1.1 - u.2.1) ≤
          V ^ (δ - u.1.1) * V ^ u.2.1 * V ^ (u.1.1 - u.2.1) := by
        gcongr <;> exact hx _
      _ = V ^ ((δ - u.1.1) + u.2.1 + (u.1.1 - u.2.1)) := by
        rw [← pow_add, ← pow_add]
      _ = V ^ δ := by
        congr 1
        have huj : u.2.1 ≤ u.1.1 := Nat.lt_succ_iff.mp u.2.2
        have hjδ : u.1.1 ≤ δ := Nat.lt_succ_iff.mp u.1.2
        omega
  · intro i
    simp

/-- The images of all displayed degree-`δ` monomials span the corresponding
homogeneous quotient piece. -/
theorem span_affinePlaneMonomials_eq_quotientHomogeneousComponent
    (δ : ℕ) (I : Ideal (MvPolynomial (Fin 3) ℚ)) :
    Submodule.span ℚ (Set.range fun u : AffinePlaneMonomialIndex δ ↦
      Ideal.Quotient.mk I (affinePlaneHomogeneousMonomial ℚ δ u)) =
      quotientHomogeneousComponent ℚ (Fin 3) I δ := by
  change Submodule.span ℚ (Set.range fun u : AffinePlaneMonomialIndex δ ↦
      Ideal.Quotient.mk I (affinePlaneHomogeneousMonomial ℚ δ u)) =
    projectiveHilbertPiece ℚ 2 I δ
  rw [projectiveHilbertPiece_eq_span_monomials_general]
  congr 1
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨affinePlaneMonomialExponent δ u,
      affinePlaneMonomialExponent_degree δ u, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨u, hu⟩ := exists_affinePlaneMonomialIndex_exponent_eq δ d hd
    refine ⟨u, ?_⟩
    simp only [affinePlaneHomogeneousMonomial, hu]

/-- At its own degree, a nonzero principal plane equation removes exactly
one dimension from the full monomial block. -/
theorem finrank_principal_planeCurve_degree_piece
    (δ : ℕ) (G : MvPolynomial (Fin 3) ℚ)
    (hGhom : G.IsHomogeneous δ) (hGne : G ≠ 0) :
    Module.finrank ℚ (quotientHomogeneousComponent ℚ (Fin 3)
      (Ideal.span ({G} : Set _)) δ) = salbergerCurveMonomialCount δ := by
  have hcolon : (⊥ : Ideal (MvPolynomial (Fin 3) ℚ)).colon
      (Ideal.span ({G} : Set _)) = ⊥ := by
    ext f
    rw [Ideal.mem_colon_singleton, Ideal.mem_bot, Ideal.mem_bot]
    exact mul_eq_zero.trans (or_iff_left hGne)
  have hrec := finrank_homogeneous_section_add_colon_eq
    (⊥ : Ideal (MvPolynomial (Fin 3) ℚ))
    (Ideal.IsHomogeneous.bot _) G hGhom 0
  rw [hcolon, bot_sup_eq,
    finrank_quotientHomogeneousComponent_bot_fin,
    finrank_quotientHomogeneousComponent_bot_fin] at hrec
  have hzeroadd : 0 + δ = δ := Nat.zero_add δ
  rw [hzeroadd] at hrec
  have hchoose : (2 + δ).choose δ = affinePlaneMonomialCount δ := by
    rw [← Nat.choose_symm (by omega : δ ≤ 2 + δ)]
    have hsub : 2 + δ - δ = 2 := by omega
    rw [hsub, Nat.choose_two_right]
    have hcount := two_mul_affinePlaneMonomialCount δ
    have hone : 2 + δ - 1 = δ + 1 := by omega
    have hrewrite : (2 + δ) * (2 + δ - 1) =
        2 * affinePlaneMonomialCount δ := by
      rw [hone]
      calc
        (2 + δ) * (δ + 1) = (δ + 1) * (δ + 2) := by ring
        _ = 2 * affinePlaneMonomialCount δ := hcount.symm
    rw [hrewrite, Nat.mul_div_cancel_left _ (by omega)]
  norm_num at hrec
  rw [hchoose] at hrec
  have hcounts := two_mul_affinePlaneMonomialCount δ
  have hsalberger := two_mul_salbergerCurveMonomialCount δ
  have hpoly : (δ + 1) * (δ + 2) = δ * (δ + 3) + 2 := by ring
  omega

/-- Internal proof of the monomial block for the principal ideal of a
literal integral homogeneous plane equation. -/
theorem exists_planeCurveDegreeMonomialBlock_internal
    {δ : ℕ} (P : MvPolynomial (Fin 3) ℤ)
    (hPhom : P.IsHomogeneous δ) (hPne : P ≠ 0) :
    ∃ F : Fin (salbergerCurveMonomialCount δ) →
        MvPolynomial (Fin 3) ℤ,
      SalbergerCurveDegreeMonomialBlock
        (Ideal.span ({P.map (Int.castRingHom ℚ)} : Set _)) F := by
  classical
  let I : Ideal (MvPolynomial (Fin 3) ℚ) :=
    Ideal.span ({P.map (Int.castRingHom ℚ)} : Set _)
  let v : AffinePlaneMonomialIndex δ →
      (MvPolynomial (Fin 3) ℚ ⧸ I) := fun u ↦
    Ideal.Quotient.mk I (affinePlaneHomogeneousMonomial ℚ δ u)
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent ℚ (Set.range v)
  letI : Fintype b := ((Set.finite_range v).subset hb).fintype
  have hb' : ∀ q : b, ∃ u, v u = q.1 := fun q ↦ hb q.2
  choose pre hpre using hb'
  have hspanAll : Submodule.span ℚ (Set.range v) =
      quotientHomogeneousComponent ℚ (Fin 3) I δ :=
    span_affinePlaneMonomials_eq_quotientHomogeneousComponent δ I
  have hcard : Fintype.card b =
      Module.finrank ℚ (quotientHomogeneousComponent ℚ (Fin 3) I δ) := by
    have h := finrank_span_eq_card hli
    have hrange : Set.range ((↑) : b → (MvPolynomial (Fin 3) ℚ ⧸ I)) = b := by
      ext q
      simp
    rw [hrange, hspan, hspanAll] at h
    exact h.symm
  have hmapne : P.map (Int.castRingHom ℚ) ≠ 0 := by
    intro hz
    apply hPne
    apply map_injective (Int.castRingHom ℚ) Int.cast_injective
    simpa only [map_zero] using hz
  have hfinrank : Module.finrank ℚ
      (quotientHomogeneousComponent ℚ (Fin 3) I δ) =
        salbergerCurveMonomialCount δ := by
    exact finrank_principal_planeCurve_degree_piece δ _
      (hPhom.map (Int.castRingHom ℚ)) hmapne
  have hcardle : Fintype.card (Fin (salbergerCurveMonomialCount δ)) ≤
      Fintype.card b := by
    rw [Fintype.card_fin, hcard, hfinrank]
  let emb : Fin (salbergerCurveMonomialCount δ) ↪ b :=
    Classical.choice (Function.Embedding.nonempty_of_card_le hcardle)
  let F : Fin (salbergerCurveMonomialCount δ) →
      MvPolynomial (Fin 3) ℤ := fun i ↦
    affinePlaneHomogeneousMonomial ℤ δ (pre (emb i))
  refine ⟨F, ?_, ?_, ?_⟩
  · have hcomp := hli.comp emb emb.injective
    have heq :
        (fun i ↦ Ideal.Quotient.mk
          (Ideal.span ({P.map (Int.castRingHom ℚ)} : Set _))
          ((F i).map (Int.castRingHom ℚ))) =
        (fun i ↦ (emb i).1) := by
      funext i
      change Ideal.Quotient.mk I
          ((affinePlaneHomogeneousMonomial ℤ δ (pre (emb i))).map
            (Int.castRingHom ℚ)) = (emb i : b).1
      rw [show (affinePlaneHomogeneousMonomial ℤ δ (pre (emb i))).map
          (Int.castRingHom ℚ) =
          affinePlaneHomogeneousMonomial ℚ δ (pre (emb i)) by
        simp [affinePlaneHomogeneousMonomial]]
      exact hpre (emb i)
    rw [heq]
    simpa only [Function.comp_apply] using hcomp
  · intro i
    simpa only [F] using
      affinePlaneHomogeneousMonomial_isHomogeneous ℤ δ (pre (emb i))
  · intro V x hx i
    simpa only [F] using
      eval_affinePlaneHomogeneousMonomial_natAbs_le δ V (pre (emb i)) x hx

end

end TranslatedDepthSeven

import CubicTenVariables.GeometricSievePairCount
import Mathlib.Data.Fintype.BigOperators

/-! Uniform subpower multiplicity of tuples of positive equation divisors.
Each original integral ideal is treated literally, without a coprimality
restriction or supplied local counting estimate. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.GeometricSieveTupleMultiplicity
open MvPolynomial
open scoped BigOperators

/-- Positive moduli at one point outside the original ideal zero set. -/
theorem exists_modulus_bound {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℤ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃K : ℝ,1≤K ∧ ∀u : Fin n → ℝ,∀L : ℝ,1≤L → ∀x : Fin n → ℤ,
      (∀i,|(x i : ℝ)-u i|≤L) → (∃f∈J,eval x f≠0) →
      ∀Q : Finset ℕ,(∀q∈Q,0<q) →
      (∀q∈Q,∀f∈J,(q : ℤ)∣eval x f) →
      (Q.card : ℝ)≤K*(L+‖u‖)^ε := by
  obtain ⟨t,P,hP⟩ := GeometricSievePairCount.exists_finite_generators J
  obtain ⟨K,hK,hb⟩ :=
    PolynomialDivisorBound.exists_family_translated_box_divisor_bound P ε hε
  refine ⟨K,hK,?_⟩
  intro u L hL x hbox hout Q hpos hdiv
  apply hb u L hL x hbox (GeometricSievePairCount.exists_nonzero_generator J P hP x hout) Q
  intro q hq
  refine ⟨hpos q hq,?_⟩
  intro i
  apply hdiv q hq
  rw [←hP]
  exact Ideal.subset_span (Set.mem_range_self i)

theorem card_le_prod_coordinate_images {s : ℕ} (Q : Finset (Fin s → ℕ)) :
    Q.card≤∏i,(Q.image fun q => q i).card := by
  classical
  calc
    _ ≤ (Fintype.piFinset (fun i => Q.image fun q => q i)).card :=
      Finset.card_le_card (fun q hq => Fintype.mem_piFinset.mpr
        (fun i => Finset.mem_image.mpr ⟨q,hq,rfl⟩))
    _ = _ := Fintype.card_piFinset _

/-- One constant precedes the center, radius, point and finite modulus
tuple set. Empty tuples are permitted and require no outside condition. -/
theorem exists_point_bound {n s : ℕ}
    (J : Fin s → Ideal (MvPolynomial (Fin n) ℤ)) (ε : ℝ) (hε : 0 < ε) :
    ∃K : ℝ,1≤K ∧ ∀u : Fin n → ℝ,∀L : ℝ,1≤L → ∀x : Fin n → ℤ,
      (∀i,|(x i : ℝ)-u i|≤L) → (∀i,∃f∈J i,eval x f≠0) →
      ∀Q : Finset (Fin s → ℕ),(∀q∈Q,∀i,0<q i) →
      (∀q∈Q,∀i,∀f∈J i,(q i : ℤ)∣eval x f) →
      (Q.card : ℝ)≤K*(L+‖u‖)^ε := by
  classical
  let η : ℝ := ε/((s : ℝ)+1)
  have hη : 0 < η := div_pos hε (by positivity)
  choose C hC hb using fun i => exists_modulus_bound (J i) η hη
  have hK : 1≤∏i,C i := by
    calc
      1 = ∏_i : Fin s,(1 : ℝ) := by simp
      _ ≤ ∏i,C i := Finset.prod_le_prod (by intros; norm_num) (fun i _ => hC i)
  refine ⟨∏i,C i,hK,?_⟩
  intro u L hL x hbox hout Q hpos hdiv
  have hH : 1≤L+‖u‖ := by linarith [norm_nonneg u]
  have hexp : η*(s : ℝ)≤ε := by
    have he : ((s : ℝ)+1)*η=ε := by dsimp [η]; field_simp
    nlinarith
  have hcoord (i : Fin s) :
      ((Q.image fun q => q i).card : ℝ)≤C i*(L+‖u‖)^η := by
    apply hb i u L hL x hbox (hout i)
    · intro a ha
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ha
      exact hpos q hq i
    · intro a ha f hf
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ha
      exact hdiv q hq i f hf
  calc
    (Q.card : ℝ) ≤ ∏i,((Q.image fun q => q i).card : ℝ) := by
      exact_mod_cast card_le_prod_coordinate_images Q
    _ ≤ ∏i,C i*(L+‖u‖)^η :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => hcoord i)
    _ = (∏i,C i)*(L+‖u‖)^(η*(s : ℝ)) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const]
      simp only [Finset.card_univ,Fintype.card_fin]
      rw [Real.rpow_mul_natCast (zero_le_one.trans hH)]
    _ ≤ (∏i,C i)*(L+‖u‖)^ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hH hexp) (zero_le_one.trans hK)

/-- Actual tuple-point pair multiplicity, with one uniform constant
before all finite pair sets. There is no coprimality or squarefree premise. -/
theorem exists_uniform_bound {n s : ℕ}
    (J : Fin s → Ideal (MvPolynomial (Fin n) ℤ)) (ε : ℝ) (hε : 0 < ε) :
    ∃K : ℝ,1≤K ∧ ∀u : Fin n → ℝ,∀L : ℝ,1≤L →
      ∀T : Finset ((Fin s → ℕ) × (Fin n → ℤ)),
      (∀a∈T,∀i,|(a.2 i : ℝ)-u i|≤L) →
      (∀a∈T,∀i,∃f∈J i,eval a.2 f≠0) →
      (∀a∈T,∀i,0<a.1 i) →
      (∀a∈T,∀i,∀f∈J i,(a.1 i : ℤ)∣eval a.2 f) →
      (T.card : ℝ)≤K*(L+‖u‖)^ε*((T.image Prod.snd).card : ℝ) := by
  classical
  obtain ⟨K,hK,hb⟩ := exists_point_bound J ε hε
  refine ⟨K,hK,?_⟩
  intro u L hL T hbox hout hpos hdiv
  have hfiber (x : Fin n → ℤ) (hx : x∈T.image Prod.snd) :
      ((T.filter fun a => a.2=x).card : ℝ)≤K*(L+‖u‖)^ε := by
    obtain ⟨a,ha,hax⟩ := Finset.mem_image.mp hx
    let U := T.filter fun a => a.2=x
    let Q := U.image Prod.fst
    have hinj : Set.InjOn Prod.fst (U : Set ((Fin s → ℕ) × (Fin n → ℤ))) := by
      intro a ha b hb he
      apply Prod.ext he
      exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
    have hcard : Q.card=U.card := Finset.card_image_iff.mpr hinj
    change (U.card : ℝ)≤_
    rw [←hcard]
    apply hb u L hL x
    · rw [←hax]
      exact hbox a ha
    · rw [←hax]
      exact hout a ha
    · intro q hq i
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hq
      exact hpos b (Finset.mem_filter.mp hb).1 i
    · intro q hq i f hf
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hq
      rw [←(Finset.mem_filter.mp hb).2]
      exact hdiv b (Finset.mem_filter.mp hb).1 i f hf
  calc
    (T.card : ℝ) = ∑x∈T.image Prod.snd,((T.filter fun a => a.2=x).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image Prod.snd T
    _ ≤ ∑_x∈T.image Prod.snd,K*(L+‖u‖)^ε := Finset.sum_le_sum hfiber
    _ = _ := by simp [mul_comm]

end CubicTenVariables.GeometricSieveTupleMultiplicity

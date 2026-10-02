import TranslatedDepthSeven.BoundedPointSpanEquations
import TranslatedDepthSeven.IntegerGridAvoidance

/-!
# A small integral equation from bounded evaluation vectors

If bounded integral vectors satisfy one nonzero rational linear equation,
they satisfy a nonzero integral equation with a coefficient bound depending
only on their coordinate bound and ambient dimension. Cramer's rule chooses
the equation from a basis of the vectors themselves; no height bound on the
given rational equation is assumed.

Applied to monomial evaluation vectors, this is the elementary alternative
behind Salberger's 2007 Lemma 6.3: the small equation either supplies a proper
cut or is proportional to the original hypersurface equation.
-/

namespace TranslatedDepthSeven

noncomputable section

open Matrix
open scoped BigOperators

theorem exists_bounded_integral_annihilator_of_rational_annihilator
    {N M : ℕ} (Z : Finset (IntVector N))
    (g : Fin N → ℚ) (hg : g ≠ 0)
    (hzero : ∀ z ∈ Z, ∑ i, g i * (z i : ℚ) = 0)
    (hcoord : ∀ z ∈ Z, ∀ i, (z i).natAbs ≤ M) :
    ∃ a : Fin N → ℤ,
      a ≠ 0 ∧
      (∀ z ∈ Z, ∑ i, a i * z i = 0) ∧
      ∀ i, (a i).natAbs ≤
        (N - 1).factorial * (max 1 M) ^ (N - 1) := by
  classical
  let A : Matrix (Fin 1) (Fin N) ℚ := fun _ i ↦ g i
  have hlinear : LinearIndependent ℚ A.row := by
    apply linearIndependent_unique_iff.mpr
    exact hg
  have hrank : A.rank = 1 := by
    simpa using hlinear.rank_matrix
  have hspan : Submodule.span ℚ
      (Set.range fun z : {z // z ∈ Z} ↦ fun i ↦ (z.1 i : ℚ)) ≤
        LinearMap.ker A.mulVecLin := by
    apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    change A *ᵥ (fun i ↦ (z.1 i : ℚ)) = 0
    funext j
    exact hzero z.1 z.2
  have hdimension := A.mulVecLin.finrank_range_add_finrank_ker
  have hrange : Module.finrank ℚ (LinearMap.range A.mulVecLin) = 1 := hrank
  have hdimension' :
      1 + Module.finrank ℚ (LinearMap.ker A.mulVecLin) = N := by
    simpa only [hrange, Module.finrank_pi, Fintype.card_fin] using hdimension
  have hN : 1 ≤ N := by omega
  have hdim : Module.finrank ℚ
      (Submodule.span ℚ (Set.range fun z : {z // z ∈ Z} ↦
        fun i ↦ (z.1 i : ℚ))) ≤ N - 1 := by
    have := Submodule.finrank_mono hspan
    omega
  obtain ⟨B, hBrank, hBzero, hBcoeff, _hBheight⟩ :=
    exists_bounded_integral_equations_of_pointSpan_finrank_le hN Z hdim hcoord
  have hrow : B 0 ≠ 0 := by
    intro hz
    have hB : B = 0 := by
      ext i j
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact congrFun hz j
    simp [hB] at hBrank
  refine ⟨B 0, hrow, ?_, hBcoeff 0⟩
  intro z hz
  exact congrFun (hBzero z hz) 0

/-- The polynomial form of the same argument. In the intended application
the `F i` are the distinct monomials in the support of the image equation,
so their coefficient and support bounds are both one. No coefficient
bound on the original nonzero relation `g` is required. -/
theorem exists_bounded_integral_polynomial_relation
    {N s e R C S : ℕ}
    (F : Fin s → MvPolynomial (Fin N) ℤ)
    (hF : LinearIndependent ℚ
      (fun i ↦ (F i).map (Int.castRingHom ℚ)))
    (hhomogeneous : ∀ i, (F i).IsHomogeneous e)
    (hcoeff : ∀ i m, ((F i).coeff m).natAbs ≤ C)
    (hsupport : ∀ i, (F i).support.card ≤ S)
    (Z : Finset (IntVector N))
    (hcoord : ∀ z ∈ Z, ∀ i, (z i).natAbs ≤ R)
    (g : Fin s → ℚ) (hg : g ≠ 0)
    (hrelation : ∀ z ∈ Z,
      ∑ i, g i * (MvPolynomial.eval z (F i) : ℚ) = 0) :
    ∃ G : MvPolynomial (Fin N) ℤ,
      G ≠ 0 ∧ G.IsHomogeneous e ∧
      (∀ z ∈ Z, MvPolynomial.eval z G = 0) ∧
      ∀ m, (G.coeff m).natAbs ≤
        s * ((s - 1).factorial *
          (max 1 (S * C * max 1 R ^ e)) ^ (s - 1)) * C := by
  classical
  let v : IntVector N → IntVector s := fun z i ↦ MvPolynomial.eval z (F i)
  let M : ℕ := S * C * max 1 R ^ e
  have hv : ∀ z ∈ Z.image v, ∀ i, (z i).natAbs ≤ M := by
    intro z hz i
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    have h := eval_natAbs_le_support_mul_coeff_mul_pow (F i) y
      (fun m _hm ↦ hcoeff i m) (hhomogeneous i).totalDegree_le (hcoord y hy)
    exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right C (hsupport i)))
  obtain ⟨a, ha, hazero, habound⟩ :=
    exists_bounded_integral_annihilator_of_rational_annihilator
      (Z.image v) g hg (by
        intro z hz
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
        exact hrelation y hy) hv
  let G : MvPolynomial (Fin N) ℤ :=
    ∑ i, MvPolynomial.C (a i) * F i
  have hG : G ≠ 0 := by
    intro hz
    have hsum : ∑ i, (a i : ℚ) • (F i).map (Int.castRingHom ℚ) = 0 := by
      simpa [G, Algebra.smul_def] using
        congrArg (MvPolynomial.map (Int.castRingHom ℚ)) hz
    have haQ := Fintype.linearIndependent_iff.mp hF (fun i ↦ (a i : ℚ)) hsum
    apply ha
    funext i
    change a i = 0
    have hi : (a i : ℚ) = 0 := haQ i
    exact_mod_cast hi
  refine ⟨G, hG, ?_, ?_, ?_⟩
  · exact MvPolynomial.IsHomogeneous.sum Finset.univ
      (fun i ↦ MvPolynomial.C (a i) * F i) e
      (fun i _hi ↦ (hhomogeneous i).C_mul (a i))
  · intro z hz
    simpa [G, v] using hazero (v z) (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
  · intro m
    let B : ℕ := (s - 1).factorial * max 1 M ^ (s - 1)
    calc
      (G.coeff m).natAbs =
          (∑ i, a i * (F i).coeff m).natAbs := by
            simp only [G, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
      _ ≤ ∑ i, (a i * (F i).coeff m).natAbs :=
        int_natAbs_sum_le_sum_natAbs _ _
      _ ≤ ∑ _i : Fin s, B * C := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [Int.natAbs_mul]
        exact Nat.mul_le_mul (habound i) (hcoeff i m)
      _ = _ := by simp [B, M, mul_assoc]

end

end TranslatedDepthSeven

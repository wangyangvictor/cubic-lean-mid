import HessianTheorem11.GradedCubic
import HessianTheorem11.GeometricFirstNormal
import HessianTheorem11.FiveQuadricsDominance

/-! The actual graded singular polynomial has generic Hessian rank at
most eight in the twelve-variable, five-normal-coordinate case. Its
contradiction with the proved geometric rank theorem is independent of
how the normal form and dominance were constructed. -/
noncomputable section
namespace HessianTheorem11.GradedCubic
open MvPolynomial Matrix SingularNormalEquations
variable {s r n : ℕ}

theorem cubic_homogeneous
    (q : GeometricPolynomial r) (hq : q.IsHomogeneous 2)
    (p : Fin r → GeometricPolynomial s) (hp : ∀ i, (p i).IsHomogeneous 2) :
    (cubic q p).IsHomogeneous 3 := by
  apply IsHomogeneous.add
  · exact (isHomogeneous_X GeometricField radial).mul hq.rename_isHomogeneous
  · apply IsHomogeneous.sum
    intro i _
    exact (isHomogeneous_X GeometricField (Sum.inl i)).mul (hp i).rename_isHomogeneous

theorem hessian_rank_on_radial_chart
    (MR : GenericMatrixRankInput)
    (q : GeometricPolynomial r) (hq : q.IsHomogeneous 2) (hdet : (quadraticHessian q).det ≠ 0)
    (p : Fin r → GeometricPolynomial s) (hp : ∀ i, (p i).IsHomogeneous 2)
    (hrel : TangentHessianRank.quadraticRelation (quadraticHessian q)⁻¹ p = 0)
    (hdom : ∀ v, dotProduct v ((quadraticHessian q)⁻¹.mulVec v) = 0 →
      v ∈ geometricClosure (polynomialMap p '' Set.univ))
    (Xc : GeometricField) (hX : Xc ≠ 0) (a : GeometricPoint s) (d : GeometricPoint r)
    (hz : eval (point Xc a d) (cubic q p) = 0) :
    ((SplitPolynomial.fullHessian (cubic q p)).map (eval (point Xc a d))).rank ≤ r + (r - 2) := by
  let Q := quadraticHessian q
  have hQ : Q.IsSymm := quadraticHessian_symm q
  have hQi : Q⁻¹.IsSymm := by
    change Q⁻¹.transpose = Q⁻¹
    rw [Matrix.transpose_nonsing_inv, hQ]
  have hdi : Q⁻¹.det ≠ 0 := by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]; exact inv_ne_zero hdet
  have he : Xc / 2 * dotProduct d (Q.mulVec d) + dotProduct d (polynomialMap p a) = 0 := by
    rw [quadratic_eval_identity q hq]
    rw [eval_cubic] at hz
    change Xc / 2 * (2 * eval d q) + dotProduct d (fun i => eval a (p i)) = 0
    linear_combination hz
  rw [hessian_eq_full q hq]
  exact graded_matrix_rank_le_of_dominance MR Q Q⁻¹ hQ hQi
    (Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hdet))
    (Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.mpr hdet)) hdi p hp hrel hdom Xc hX a d he

theorem hessian_rank_rename_equiv {σ : Type*} [Fintype σ]
    (e : σ ≃ Fin n) (G : MvPolynomial σ GeometricField) (x : GeometricPoint n) :
    (hessian (rename e G) x).rank =
      ((SplitPolynomial.fullHessian G).map (eval (x ∘ e))).rank := by
  have he : hessian (rename e G) x =
      ((SplitPolynomial.fullHessian G).map (eval (x ∘ e))).submatrix e.symm e.symm := by
    ext i j
    change eval x (pderiv j (pderiv i (rename e G))) =
      eval (x ∘ e) (pderiv (e.symm j) (pderiv (e.symm i) G))
    have hi := pderiv_rename e.injective (e.symm i) G
    have hj := pderiv_rename e.injective (e.symm j) (pderiv (e.symm i) G)
    simp only [e.apply_symm_apply] at hi hj
    rw [hi, hj, eval_rename]
  rw [he, Matrix.rank_submatrix]

/-- A nonempty radial chart intersects the true generic rank open. -/
theorem generic_rank_le_of_chart
    (MR : GenericMatrixRankInput)
    (F : GeometricPolynomial n) (hF : Irreducible F) (c : Fin n)
    (y : GeometricPoint n) (hy : eval y F = 0) (hyc : y c ≠ 0)
    (b : ℕ) (hb : ∀ x, eval x F = 0 → x c ≠ 0 → (hessian F x).rank ≤ b) :
    geometricCubicGenericRank F ≤ b := by
  let I : Ideal (GeometricPolynomial n) := Ideal.span {F}
  letI : I.IsPrime := (Ideal.span_singleton_prime hF.ne_zero).mpr hF.prime
  have hyI : y ∈ zeroLocus GeometricField I := by
    rw [zeroLocus_span]
    intro P hP
    have hPF : P = F := Set.mem_singleton_iff.mp hP
    rw [hPF]
    exact hy
  have hc : X c ∉ I := by
    intro h
    exact hyc (by simpa using hyI (X c) h)
  obtain ⟨P, hP, hopen⟩ := MR.principal_open I (hessianPolynomial F)
  have hprod : P * X c ∉ I := fun h =>
    (Ideal.IsPrime.mem_or_mem inferInstance h).elim hP hc
  obtain ⟨x, hx, hxP⟩ := exists_zeroLocus_eval_ne_zero I (P * X c) hprod
  have hxF : eval x F = 0 := hx F (Ideal.subset_span (Set.mem_singleton F))
  have hxc : x c ≠ 0 := by
    intro h
    exact hxP (by simp [h])
  have heP : eval x P ≠ 0 := by
    intro h
    exact hxP (by simp [h])
  change genericMatrixRank I (hessianPolynomial F) ≤ b
  rw [← hopen x hx heP]
  exact hb x hxF hxc

theorem generic_hessian_rank_le_of_dominance
    (MR : GenericMatrixRankInput) (e : Index r s ≃ Fin n)
    (q : GeometricPolynomial r) (hq : q.IsHomogeneous 2) (hdet : (quadraticHessian q).det ≠ 0)
    (p : Fin r → GeometricPolynomial s) (hp : ∀ i, (p i).IsHomogeneous 2)
    (hrel : TangentHessianRank.quadraticRelation (quadraticHessian q)⁻¹ p = 0)
    (hdom : ∀ v, dotProduct v ((quadraticHessian q)⁻¹.mulVec v) = 0 →
      v ∈ geometricClosure (polynomialMap p '' Set.univ))
    (hirred : Irreducible (rename e (cubic q p))) :
    geometricCubicGenericRank (rename e (cubic q p)) ≤ r + (r - 2) := by
  let y : GeometricPoint n := point 1 0 0 ∘ e.symm
  have hyc : y (e radial) ≠ 0 := by simp [y, point, radial]
  have heq : y ∘ e = point (1 : GeometricField) (0 : GeometricPoint s) (0 : GeometricPoint r) := by
    funext i
    simp [y]
  have hq0 : eval (0 : GeometricPoint r) q = 0 := by
    have hh := quadratic_eval_identity q hq (0 : GeometricPoint r)
    simp only [Matrix.mulVec_zero, dotProduct_zero] at hh
    linear_combination (1/2 : GeometricField) * hh.symm
  have hy : eval y (rename e (cubic q p)) = 0 := by
    rw [eval_rename, heq, eval_cubic]
    simpa only [one_mul, zero_dotProduct, add_zero] using hq0
  apply generic_rank_le_of_chart MR _ hirred (e radial) y hy hyc
  intro x hx hxc
  let Xc := x (e radial)
  let a : GeometricPoint s := fun i => x (e (tangent i))
  let d : GeometricPoint r := fun i => x (e (Sum.inl i))
  have he : x ∘ e = point Xc a d := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => cases i with
      | inl i => rfl
      | inr i => cases i; rfl
  have hz : eval (point Xc a d) (cubic q p) = 0 := by
    rwa [eval_rename, he] at hx
  rw [hessian_rank_rename_equiv, he]
  exact hessian_rank_on_radial_chart MR q hq hdet p hp hrel hdom Xc hxc a d hz

/-- The source's exceptional twelve-variable graded cubic cannot exist:
its actual Hessian would have generic rank at most eight, contradicting
the already proved geometric rank lower bound ten. -/
theorem twelve_graded_cubic_impossible
    (MR : GenericMatrixRankInput) (DT : SymmetricDeterminantalTangentInput)
    (FI : FormalImplicitFunctionInput GeometricField)
    (e : Index 5 6 ≃ Fin 12)
    (q : GeometricPolynomial 5) (hq : q.IsHomogeneous 2) (hqdet : (quadraticHessian q).det ≠ 0)
    (p : Fin 5 → GeometricPolynomial 6) (hp : ∀ i, (p i).IsHomogeneous 2)
    (hrel : TangentHessianRank.quadraticRelation (quadraticHessian q)⁻¹ p = 0)
    (hdom : ∀ v, dotProduct v ((quadraticHessian q)⁻¹.mulVec v) = 0 →
      v ∈ geometricClosure (polynomialMap p '' Set.univ))
    (hirred : Irreducible (rename e (cubic q p)))
    (hdet : hessianDeterminantPolynomial (rename e (cubic q p)) ≠ 0) : False := by
  have hu := generic_hessian_rank_le_of_dominance MR e q hq hqdet p hp hrel hdom hirred
  have hl := geometric_rank_twelve MR DT FI (rename e (cubic q p))
    (cubic_homogeneous q hq p hp).rename_isHomogeneous hirred hdet
  omega

/-- For the actual five-coordinate tuple, proved independence is enough:
quadric dominance has already been derived from it in Lean. -/
theorem twelve_graded_cubic_impossible_of_independence
    (MR : GenericMatrixRankInput) (DT : SymmetricDeterminantalTangentInput)
    (FI : FormalImplicitFunctionInput GeometricField)
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (e : Index 5 6 ≃ Fin 12)
    (q : GeometricPolynomial 5) (hq : q.IsHomogeneous 2) (hqdet : (quadraticHessian q).det ≠ 0)
    (p : Fin 5 → GeometricPolynomial 6) (hp : ∀ i, (p i).IsHomogeneous 2)
    (hrel : TangentHessianRank.quadraticRelation (quadraticHessian q)⁻¹ p = 0)
    (hlin : LinearIndependent GeometricField p)
    (hirred : Irreducible (rename e (cubic q p)))
    (hdet : hessianDeterminantPolynomial (rename e (cubic q p)) ≠ 0) : False := by
  have hQi : (quadraticHessian q)⁻¹.IsSymm := by
    change (quadraticHessian q)⁻¹.transpose = _
    rw [Matrix.transpose_nonsing_inv, quadraticHessian_symm q]
  have hdi : (quadraticHessian q)⁻¹.det ≠ 0 := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    exact inv_ne_zero hqdet
  have hdom := five_quadrics_dominant_on_quadric GR AD p hp hlin
    (quadraticHessian q)⁻¹ hQi hdi hrel
  exact twelve_graded_cubic_impossible MR DT FI e q hq hqdet p hp hrel
    (fun v hv => by rw [hdom]; exact hv) hirred hdet

end HessianTheorem11.GradedCubic

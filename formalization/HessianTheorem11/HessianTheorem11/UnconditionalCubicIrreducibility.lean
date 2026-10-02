import HessianTheorem11.UnconditionalFactorization
import HessianTheorem11.GeometricFactorization
import HessianTheorem11.ReducedGaloisSubspace
import HessianTheorem11.ReducedDeterminantalTangent

/-! Direct absolute irreducibility of anisotropic rational cubics in at least
four variables. A unique geometric linear factor has Galois-stable kernel,
so proved rational subspace descent gives a rational zero. If the quadratic
factor splits, the three linear factors force the Hessian determinant to
vanish. No optimality, geometric-component descent or geometry input. -/
noncomputable section
namespace HessianTheorem11.UnconditionalIrreducibility
open MvPolynomial Module ReducedRationalDescent RationalDescent
variable {n : ℕ}

theorem conjugate_linear_dvd_left (F : RationalPolynomial n)
    (L Q : GeometricPolynomial n) (hL : L.IsHomogeneous 1)
    (hQ : Q.IsHomogeneous 2) (hQi : Irreducible Q)
    (hL0 : L ≠ 0) (hprod : geometricPolynomial F = L * Q)
    (σ : GeometricField ≃ₐ[ℚ] GeometricField) : map σ.toRingHom L ∣ L := by
  have hmap0 : map σ.toRingHom L ≠ 0 := by
    intro hz
    apply hL0
    exact (MvPolynomial.map_injective σ.toRingHom σ.injective) (hz.trans (map_zero _).symm)
  have hdL := (hL.map σ.toRingHom).totalDegree hmap0
  have hiL := irreducible_of_totalDegree_one _ hdL
  have hd : map σ.toRingHom L ∣ L * Q := by
    have he := congrArg (map σ.toRingHom) hprod
    rw [RationalDescent.geometricPolynomial_galois_fixed F σ, map_mul] at he
    exact ⟨map σ.toRingHom Q, hprod.symm.trans he⟩
  rcases hiL.prime.dvd_or_dvd hd with h | h
  · exact h
  · have ha := hiL.associated_of_dvd hQi h
    have hdeg := totalDegree_le_of_dvd_of_isDomain ha.symm.dvd hmap0
    rw [hQ.totalDegree hQi.ne_zero, hdL] at hdeg
    omega

/-- A Galois-stable geometric hyperplane contains a nonzero rational vector.
This uses the already proved rational-basis theorem for actual subspaces. -/
theorem rational_zero_of_conjugate_dvd (L : GeometricPolynomial n)
    (hL : L.IsHomogeneous 1) (hn : 2 ≤ n)
    (hstable : ∀ σ : GeometricField ≃ₐ[ℚ] GeometricField, map σ.toRingHom L ∣ L) :
    ∃ x : Fin n → ℚ, x ≠ 0 ∧
      eval (fun i => algebraMap ℚ GeometricField (x i)) L = 0 := by
  classical
  let l : GeometricPoint n →ₗ[GeometricField] GeometricField := {
    toFun := fun x => eval x L
    map_add' := eval_add_homogeneous_one hL
    map_smul' := fun a x => eval_smul_homogeneous_one hL a x }
  let T := LinearMap.ker l
  have hinv : ∀ σ : GeometricField ≃ₐ[ℚ] GeometricField,
      ∀ x ∈ T, (fun i => σ (x i)) ∈ T := by
    intro σ x hx
    obtain ⟨P,hP⟩ := hstable σ
    change eval (fun i => σ (x i)) L = 0
    rw [hP,eval_mul]
    have he : eval (fun i => σ (x i)) (map σ.toRingHom L) = 0 := by
      have he := MvPolynomial.map_eval σ.toRingHom x L
      rw [show eval x L = 0 from hx, map_zero] at he
      simpa only [Function.comp_apply] using he.symm
    rw [he,zero_mul]
  obtain ⟨b,hb⟩ := invariant_subspace_rational_basis T hinv
  have hdim := l.finrank_range_add_finrank_ker
  have hrange : finrank GeometricField (LinearMap.range l) ≤ 1 := by
    simpa using (Submodule.finrank_le (LinearMap.range l))
  simp only [finrank_pi,Fintype.card_fin] at hdim
  have hpos : 0 < finrank GeometricField T := by
    change 0 < finrank GeometricField (LinearMap.ker l)
    omega
  let j : Fin (finrank GeometricField T) := ⟨0,hpos⟩
  choose x hx using hb j
  refine ⟨x,?_,?_⟩
  · intro hz
    have hbj : b j = 0 := by
      apply Subtype.ext
      funext i
      rw [← hx i]
      simp [hz]
    exact b.ne_zero j hbj
  · have he : (fun i => algebraMap ℚ GeometricField (x i)) = (b j).val := funext hx
    rw [he]
    exact (b j).property

/-- Unconditional absolute irreducibility for the rational anisotropic cubic.
The only assumptions are the actual cubic's homogeneity and anisotropy. -/
theorem anisotropic_geometric_irreducible (F : AnisotropicCubic n) (hn : 4 ≤ n) :
    Irreducible (geometricPolynomial F.polynomial) := by
  have hF0 := geometricPolynomial_ne_zero F.polynomial
    (anisotropic_polynomial_ne_zero (by omega) F)
  by_contra hred
  obtain ⟨L,Q,hL,hQ,hprod⟩ := reducible_homogeneous_cubic_linear_times_quadratic
    _ (geometric_homogeneous F.homogeneous) hF0 hred
  have hL0 : L ≠ 0 := by intro hz; exact hF0 (by simp [hprod,hz])
  have hQ0 : Q ≠ 0 := by intro hz; exact hF0 (by simp [hprod,hz])
  by_cases hQi : Irreducible Q
  · obtain ⟨x,hx,hLx⟩ := rational_zero_of_conjugate_dvd L hL (by omega)
      (conjugate_linear_dvd_left F.polynomial L Q hL hQ hQi hL0 hprod)
    apply hx
    apply F.anisotropic
    apply (algebraMap ℚ GeometricField).injective
    have he : eval (fun i => algebraMap ℚ GeometricField (x i))
        (geometricPolynomial F.polynomial) = 0 := by
      rw [hprod,eval_mul,hLx,zero_mul]
    simpa only [map_zero] using
      (MvPolynomial.map_eval (algebraMap ℚ GeometricField) x F.polynomial).trans he
  · obtain ⟨A,B,hA,hB,hAB⟩ :=
      reducible_homogeneous_quadratic_linear_times_linear Q hQ hQ0 hQi
    let factors : Fin 3 → GeometricPolynomial n := ![L,A,B]
    have hlinear : ∀ i, (factors i).IsHomogeneous 1 := by
      intro i
      fin_cases i <;> assumption
    have hfac : geometricPolynomial F.polynomial = C 1 * ∏ i, factors i := by
      simp [factors,Fin.prod_univ_succ,hprod,hAB,mul_assoc]
    have hz := hessianDeterminantPolynomial_product_linearForms_eq_zero
      (1 : GeometricField) factors hlinear (by omega)
    exact geometric_hessianDeterminantPolynomial_ne_zero (provedDeterminantalTangentOver ℚ) F
      (by rw [hfac]; exact hz)

end HessianTheorem11.UnconditionalIrreducibility

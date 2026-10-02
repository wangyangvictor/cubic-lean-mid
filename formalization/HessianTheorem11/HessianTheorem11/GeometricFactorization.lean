import HessianTheorem11.RationalIrreducibility
import HessianTheorem11.FewerVariables

/-! Absolute irreducibility from rational irreducibility and the nonzero
Hessian determinant. The one external input is the general homogeneous
factorization consequence of Galois transitivity on geometric components.
It is stated for every degree, with no anisotropy or Hessian hypothesis. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial

/-- Standard geometric-component descent over a perfect field, specialized
to homogeneous hypersurfaces over Q: the geometric irreducible factors of
an irreducible rational form form one Galois orbit, hence have equal degree.
Characteristic zero ensures geometric reducedness. See Stacks 04KY, 04KZ,
and the usual homogeneous factorization theorem for polynomial rings. -/
structure GeometricHomogeneousFactorizationInput : Prop where
  factorization : ∀ {n d : ℕ} (F : RationalPolynomial n),
    0 < d → F.IsHomogeneous d → Irreducible F →
    ∃ (k e : ℕ) (a : GeometricField) (L : Fin k → GeometricPolynomial n),
      0 < k ∧ 0 < e ∧ k * e = d ∧ a ≠ 0 ∧
      (∀ i, (L i).IsHomogeneous e) ∧ (∀ i, Irreducible (L i)) ∧
      geometricPolynomial F = C a * ∏ i, L i

/-- Source Lemma 7.1, using the already proved nonzero Hessian determinant
to rule out the three-linear-factor alternative. No absolute-irreducibility
claim about anisotropic cubics is part of the textbook input. -/
theorem anisotropic_cubic_geometrically_irreducible
    (GF : GeometricHomogeneousFactorizationInput) (DT : DeterminantalTangentOver ℚ)
    {n : ℕ} (F : AnisotropicCubic n) (hn : 4 ≤ n) :
    Irreducible (geometricPolynomial F.polynomial) := by
  obtain ⟨k, e, a, L, hk, he, hdegree, ha, hhom, hirred, hprod⟩ :=
    GF.factorization F.polynomial (by norm_num) F.homogeneous
      (anisotropic_cubic_irreducible F (by omega))
  by_cases hkone : k = 1
  · subst k
    simp only [Fin.prod_univ_one] at hprod
    rw [hprod]
    apply (irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr ha).map C)).mpr
    exact hirred 0
  have hktwo : 2 ≤ k := by omega
  have heone : e = 1 := by nlinarith
  have hkthree : k = 3 := by simpa [heone] using hdegree
  have hsmall : k < n := by omega
  have hlinear : ∀ i, (L i).IsHomogeneous 1 := by simpa [heone] using hhom
  have hzero := hessianDeterminantPolynomial_product_linearForms_eq_zero a L hlinear hsmall
  have hnonzero := geometric_hessianDeterminantPolynomial_ne_zero DT F
  exact False.elim (hnonzero (by rwa [hprod]))

end HessianTheorem11

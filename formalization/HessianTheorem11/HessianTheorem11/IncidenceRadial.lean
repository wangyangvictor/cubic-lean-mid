import HessianTheorem11.ConePointSelection
import HessianTheorem11.GeometricRadial
import HessianTheorem11.IncidenceNumerics

/-! The radial estimate on an actual concentrated incidence base. The
concentration identity is stated explicitly here and proved separately. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Module

theorem incidence_radial_of_concentrated_base
    (GP : GenericConePointSelectionInput) (DT : SymmetricDeterminantalTangentInput)
    {n : ℕ} (F : RationalPolynomial n) (hF : F.IsHomogeneous 3)
    (hsemi : WeightSemistable (geometricPolynomial F))
    (Z : Set (GeometricPoint n)) (hclosed : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z) (hcone : IsAffineCone Z)
    (hcontained : Z ⊆ cubicLocus F)
    (t r ell : ℕ) (hZdim : affineDimension Z = (t : Dimension))
    (hIdim : incidenceDimension F = ((t + ell : ℕ) : Dimension))
    (hranknullity : r + ell = n)
    (hattained : ∃ x ∈ Z, (hessian (geometricPolynomial F) x).rank = r)
    (hmax : ∀ x ∈ Z, (hessian (geometricPolynomial F) x).rank ≤ r) :
    ∃ D : ℕ, incidenceDimension F = (D : Dimension) ∧
      (D ≤ n ∨ 3 * ((D : ℤ) - (n : ℤ)) + 3 ≤ (n : ℤ)) := by
  refine ⟨t + ell, hIdim, ?_⟩
  by_cases hsmall : t + ell ≤ n
  · exact Or.inl hsmall
  right
  have hnonorigin : ¬ Z ⊆ {0} := by
    intro ho
    have hd := affineDimension_mono ho
    rw [hZdim, affineDimension_singleton] at hd
    have ht : t ≤ 0 := by exact_mod_cast hd
    omega
  let P := GP.choose Z hclosed hirred hcone hnonorigin
    (hessianLinearMap (geometricPolynomial F) (geometric_homogeneous hF))
    (fun i => pderiv i (geometricPolynomial F))
  have hprank : (hessian (geometricPolynomial F) P.point).rank = r := by
    apply le_antisymm (hmax P.point P.member)
    obtain ⟨y, hy, hyr⟩ := hattained
    have h := P.rank_maximal y hy
    change (hessian (geometricPolynomial F) y).rank ≤ _ at h
    rwa [hyr] at h
  have hpt : finrank GeometricField (affineTangentSpace Z P.point) = t := by
    have hd := P.dimension
    rw [hZdim] at hd
    exact_mod_cast hd.symm
  have hgenericSing : gradient (geometricPolynomial F) P.point = 0 →
      ∀ y ∈ Z, gradient (geometricPolynomial F) y = 0 := by
    intro hx
    have hp : P.point ∈ finiteEquationZeroSet (fun i => pderiv i (geometricPolynomial F)) := by
      intro i
      exact congrFun hx i
    intro y hy
    ext i
    exact P.detects_equations hp hy i
  have hrad := geometric_radial_inequality DT (geometricPolynomial F)
    (geometric_homogeneous hF) hsemi Z P.point P.member P.nonzero P.radial
    P.rank_maximal (fun y hy => hcontained hy) hgenericSing
  rw [hprank, hpt] at hrad
  omega

theorem incidence_eleven_le_thirteen_of_concentrated_base
    (GP : GenericConePointSelectionInput) (DT : SymmetricDeterminantalTangentInput)
    (F : RationalPolynomial 11) (hF : F.IsHomogeneous 3)
    (hsemi : WeightSemistable (geometricPolynomial F))
    (Z : Set (GeometricPoint 11)) (hclosed : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z) (hcone : IsAffineCone Z)
    (hcontained : Z ⊆ cubicLocus F)
    (t r ell : ℕ) (hZdim : affineDimension Z = (t : Dimension))
    (hIdim : incidenceDimension F = ((t + ell : ℕ) : Dimension))
    (hranknullity : r + ell = 11)
    (hattained : ∃ x ∈ Z, (hessian (geometricPolynomial F) x).rank = r)
    (hmax : ∀ x ∈ Z, (hessian (geometricPolynomial F) x).rank ≤ r) :
    incidenceDimension F ≤ 13 := by
  obtain ⟨D, hD, hrad⟩ := incidence_radial_of_concentrated_base GP DT F hF hsemi
    Z hclosed hirred hcone hcontained t r ell hZdim hIdim hranknullity hattained hmax
  have hnum : D ≤ 13 := by rcases hrad with h | h <;> omega
  rw [hD]
  exact_mod_cast hnum

end HessianTheorem11

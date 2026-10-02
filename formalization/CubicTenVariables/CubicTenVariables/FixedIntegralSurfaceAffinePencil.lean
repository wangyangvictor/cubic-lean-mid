import CubicTenVariables.FixedIntegralSurfacePencil
import CubicTenVariables.ProjectivePlaneCurveAffineChart
import CubicTenVariables.PolynomialDegreePrincipalOpen

/-!
# Affine plane-curve fibers of the fixed integral surface pencil

The projective pencil is dehomogenized at its fixed first plane coordinate.
Coefficient specialization commutes literally with this operation.  Thus
every projectively integral good fiber supplied by the pencil certificate
gives the exact affine geometric-domain hypothesis used by the curve Weil
bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace CubicTenVariables.FixedIntegralSurfaceAffinePencil

open MvPolynomial
open HessianTheorem11
open TranslatedDepthSeven
open FixedIntegralSurfacePencil
open ProjectivePlaneCurveAffineChart
open HessianTheorem11.PolynomialRestriction
open Module

/-- The actual two-variable affine curve family over `Z[T]`. -/
def affineCurveFamily
    (F : MvPolynomial (Fin 4) ℤ) (C : Matrix (Fin 4) (Fin 3) ℤ) :
    MvPolynomial (Fin 2) (MvPolynomial (Fin 1) ℤ) :=
  standardDehomogenizationHom (MvPolynomial (Fin 1) ℤ) 2
    (projectivePencilPolynomial F C)

/-- Specializing the affine family is exactly dehomogenizing the literal
specialized projective section. -/
theorem specialize_affineCurveFamily
    {K : Type*} [CommRing K]
    (F : MvPolynomial (Fin 4) ℤ) (C : Matrix (Fin 4) (Fin 3) ℤ)
    (t : K) :
    map (eval₂Hom (Int.castRingHom K) (fun _ : Fin 1 => t))
        (affineCurveFamily F C) =
      standardDehomogenizationHom K 2
        (restrict (pencilFrame C t) (map (Int.castRingHom K) F)) := by
  let τ : MvPolynomial (Fin 1) ℤ →+* K :=
    eval₂Hom (Int.castRingHom K) (fun _ : Fin 1 => t)
  have hcomm := standardDehomogenizationHom_comp_map 2 τ
  have happ := RingHom.congr_fun hcomm (projectivePencilPolynomial F C)
  have hspec := specialize_projectivePencilPolynomial F C t
  have happ' : standardDehomogenizationHom K 2
      (map τ (projectivePencilPolynomial F C)) =
      map τ (standardDehomogenizationHom (MvPolynomial (Fin 1) ℤ) 2
        (projectivePencilPolynomial F C)) := by
    simpa only [RingHom.comp_apply] using happ
  change map τ (affineCurveFamily F C) = _
  rw [affineCurveFamily, ← happ', hspec]

/-- An injective projective-plane restriction of a geometrically integral
surface equation of degree at least two is not the zero polynomial. -/
theorem hyperplaneRestriction_ne_zero
    {K : Type*} [Field K] {d : ℕ} (hd : 2 ≤ d)
    (G : MvPolynomial (Fin 4) K) (hGdeg : G.totalDegree = d)
    (hGdom : IsDomain (MvPolynomial (Fin 4) (AlgebraicClosure K) ⧸
      Ideal.span {map (algebraMap K (AlgebraicClosure K)) G}))
    (B : Matrix (Fin 4) (Fin 3) K) (hB : Function.Injective B.mulVec) :
    restrict B G ≠ 0 := by
  let L := AlgebraicClosure K
  let Bbar : Matrix (Fin 4) (Fin 3) L := B.map (algebraMap K L)
  let Gbar : MvPolynomial (Fin 4) L := map (algebraMap K L) G
  have hBbar : Function.Injective Bbar.mulVec :=
    ReducedVertexBaseChange.map_frame_injective B hB
  have hGdegbar : Gbar.totalDegree = d := by
    exact (PolynomialDegreePrincipalOpen.totalDegree_map_of_injective
      (algebraMap K L) (algebraMap K L).injective G).trans hGdeg
  have hGbar0 : Gbar ≠ 0 := by
    intro hz
    rw [hz, totalDegree_zero] at hGdegbar
    omega
  have hprime := (Ideal.Quotient.isDomain_iff_prime _).mp hGdom
  have hirr : Irreducible Gbar :=
    ((Ideal.span_singleton_prime hGbar0).mp hprime).irreducible
  intro hzero
  have hzeroBar : restrict Bbar Gbar = 0 := by
    rw [← map_restrict]
    rw [hzero, map_zero]
  let W : Submodule L (Fin 4 → L) := LinearMap.range Bbar.mulVecLin
  have hWdim : finrank L W = 3 := by
    rw [LinearMap.finrank_range_of_inj hBbar]
    simp only [Module.finrank_pi, Fintype.card_fin]
  have hWlt : W < ⊤ := Submodule.lt_top_of_finrank_lt_finrank (by
    rw [hWdim]
    simp only [Module.finrank_pi, Fintype.card_fin]
    omega)
  obtain ⟨ell, hell, hWell⟩ := W.exists_le_ker_of_lt_top hWlt
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hell
  have hWeq : W = LinearMap.ker ell :=
    Submodule.eq_of_le_of_finrank_eq hWell (by
      rw [hWdim]
      simp only [Module.finrank_pi, Fintype.card_fin] at hker
      omega)
  have hvanish : ∀ x, ell x = 0 → eval x Gbar = 0 := by
    intro x hx
    have hxW : x ∈ W := hWeq ▸ hx
    obtain ⟨y, hy⟩ := hxW
    have hy' : Bbar.mulVec y = x := hy
    calc
      eval x Gbar = eval y (restrict Bbar Gbar) := by
        rw [eval_restrict, hy']
      _ = 0 := by rw [hzeroBar, map_zero]
  have hle := PlaneCubicSingularGeometry.degree_le_one_of_vanishes_on_hyperplane
    Gbar hirr ell hell hvanish
  rw [hGdegbar] at hle
  omega

/-- Every affine fiber in the fixed pencil is a nonzero plane polynomial,
including the finitely many exceptional fibers. -/
theorem affineCurveFiber_ne_zero
    {K : Type*} [Field K] {d : ℕ} (hd : 2 ≤ d)
    (F : MvPolynomial (Fin 4) ℤ) (hF : F.IsHomogeneous d)
    (C : Matrix (Fin 4) (Fin 3) ℤ) (t : K)
    (hC00 : (C 0 0 : K) ≠ 0) (hC01 : C 0 1 = 0) (hC02 : C 0 2 = 0)
    (hdet : ((spatialPencilMatrix C).det : K) ≠ 0)
    (hFdeg : (map (Int.castRingHom K) F).totalDegree = d)
    (hFdom : IsDomain (MvPolynomial (Fin 4) (AlgebraicClosure K) ⧸
      Ideal.span {map (algebraMap K (AlgebraicClosure K))
        (map (Int.castRingHom K) F)})) :
    map (eval₂Hom (Int.castRingHom K) (fun _ : Fin 1 => t))
      (affineCurveFamily F C) ≠ 0 := by
  let H := restrict (pencilFrame C t) (map (Int.castRingHom K) F)
  have hB := pencilFrame_injective C hC00 hC01 hC02 hdet t
  have hH0 : H ≠ 0 :=
    hyperplaneRestriction_ne_zero hd _ hFdeg hFdom _ hB
  have hHhom : H.IsHomogeneous d :=
    homogeneous_restrict _ _ (hF.map _)
  have hchart : standardDehomogenizationHom K 2 H ≠ 0 :=
    standardDehomogenization_ne_zero H hHhom hH0
  rw [specialize_affineCurveFamily F C t]
  exact hchart

theorem totalDegree_pos_of_geometricDomain
    {K : Type*} [Field K]
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0)
    (hdom : IsDomain (MvPolynomial (Fin 2) (AlgebraicClosure K) ⧸
      Ideal.span {map (algebraMap K (AlgebraicClosure K)) f})) :
    1 ≤ f.totalDegree := by
  by_contra h
  have hdeg : f.totalDegree = 0 := by omega
  have hu : IsUnit f := by
    rw [totalDegree_eq_zero_iff_eq_C.mp hdeg]
    apply IsUnit.map MvPolynomial.C
    apply isUnit_iff_ne_zero.mpr
    intro hc
    apply hf
    rw [totalDegree_eq_zero_iff_eq_C.mp hdeg, hc, map_zero]
  have huL : IsUnit (map (algebraMap K (AlgebraicClosure K)) f) :=
    hu.map (map (algebraMap K (AlgebraicClosure K)))
  have hprime := (Ideal.Quotient.isDomain_iff_prime _).mp hdom
  exact hprime.ne_top (Ideal.span_singleton_eq_top.mpr huL)

/-- The exact affine good-fiber conclusion needed by
`Literature.AffinePlaneCurveWeil`. -/
theorem goodFiber_geometricallyIntegral
    {K : Type*} [Field K] {d : ℕ} (hd : 2 ≤ d)
    (F : MvPolynomial (Fin 4) ℤ) (C : Matrix (Fin 4) (Fin 3) ℤ)
    (t : K)
    (hhom : (restrict (pencilFrame C t)
      (map (Int.castRingHom K) F)).IsHomogeneous d)
    (hdeg : (restrict (pencilFrame C t)
      (map (Int.castRingHom K) F)).totalDegree = d)
    (hdom : IsDomain (MvPolynomial (Fin 3) (AlgebraicClosure K) ⧸
      Ideal.span {map (algebraMap K (AlgebraicClosure K))
        (restrict (pencilFrame C t) (map (Int.castRingHom K) F))})) :
    IsDomain (MvPolynomial (Fin 2) (AlgebraicClosure K) ⧸
      Ideal.span {map (algebraMap K (AlgebraicClosure K))
        (map (eval₂Hom (Int.castRingHom K) (fun _ : Fin 1 => t))
          (affineCurveFamily F C))}) := by
  let H := restrict (pencilFrame C t) (map (Int.castRingHom K) F)
  let L := AlgebraicClosure K
  have hdegL : (map (algebraMap K L) H).totalDegree = d := by
    rw [PolynomialDegreePrincipalOpen.totalDegree_map_of_injective
      (algebraMap K L) (algebraMap K L).injective H]
    exact hdeg
  have hchart := standardDehomogenization_isDomain hd
    (map (algebraMap K L) H) (hhom.map _) hdegL hdom
  have hcomm := standardDehomogenizationHom_comp_map 2 (algebraMap K L)
  have happ := RingHom.congr_fun hcomm H
  have happ' : standardDehomogenizationHom L 2 (map (algebraMap K L) H) =
      map (algebraMap K L) (standardDehomogenizationHom K 2 H) := by
    simpa only [RingHom.comp_apply] using happ
  have hspec := specialize_affineCurveFamily F C t
  rw [hspec]
  change IsDomain (MvPolynomial (Fin 2) L ⧸
    Ideal.span {map (algebraMap K L)
      (standardDehomogenizationHom K 2 H)})
  rw [← happ']
  exact hchart

/-- Complete affine-fiber geometry furnished by the fixed projective pencil.
The exceptional polynomial is genuinely nonzero after every permitted
coefficient reduction; every fiber equation is nonzero, while every
nonexceptional fiber has positive degree and the exact geometric-domain
hypothesis of the affine curve Weil bound. -/
theorem exists_fixed_integral_affine_pencil_certificate
    (integralityOpen : Literature.HomogeneousHypersurfaceIntegralityOpen)
    {d : ℕ} (hd : 2 ≤ d)
    (F : MvPolynomial (Fin 4) ℤ) (hF0 : F ≠ 0)
    (hF : F.IsHomogeneous d)
    (hgeom : IsDomain (MvPolynomial (Fin 4) GeometricField ⧸
      Ideal.span {map (Int.castRingHom GeometricField) F})) :
    ∃ (C : Matrix (Fin 4) (Fin 3) ℤ) (N : ℤ)
        (g : MvPolynomial (Fin 1) ℤ),
      C 0 0 ≠ 0 ∧ C 0 1 = 0 ∧ C 0 2 = 0 ∧ N ≠ 0 ∧
      ∀ (K : Type) [Field K], (N : K) ≠ 0 →
        (C 0 0 : K) ≠ 0 ∧
        ((spatialPencilMatrix C).det : K) ≠ 0 ∧
        map (Int.castRingHom K) g ≠ 0 ∧
        (∀ t : K, map (eval₂Hom (Int.castRingHom K) (fun _ : Fin 1 => t))
          (affineCurveFamily F C) ≠ 0) ∧
        ∀ t : K, eval (fun _ : Fin 1 => t) (map (Int.castRingHom K) g) ≠ 0 →
          1 ≤ (map (eval₂Hom (Int.castRingHom K) (fun _ : Fin 1 => t))
            (affineCurveFamily F C)).totalDegree ∧
          IsDomain (MvPolynomial (Fin 2) (AlgebraicClosure K) ⧸
            Ideal.span {map (algebraMap K (AlgebraicClosure K))
              (map (eval₂Hom (Int.castRingHom K) (fun _ : Fin 1 => t))
                (affineCurveFamily F C))}) := by
  obtain ⟨C, N, g, hC00Z, hC01, hC02, _hg0, hN, hcert⟩ :=
    exists_fixed_integral_surface_pencil_certificate
      integralityOpen hd F hF0 hF hgeom
  refine ⟨C, N, g, hC00Z, hC01, hC02, hN, ?_⟩
  intro K _ hNK
  obtain ⟨hC00, hdet, hFdeg, hFdom, hgK, hgood⟩ := hcert K hNK
  have hall : ∀ t : K,
      map (eval₂Hom (Int.castRingHom K) (fun _ : Fin 1 => t))
        (affineCurveFamily F C) ≠ 0 := fun t =>
    affineCurveFiber_ne_zero hd F hF C t hC00 hC01 hC02 hdet hFdeg hFdom
  refine ⟨hC00, hdet, hgK, hall, ?_⟩
  intro t hgt
  obtain ⟨hhom, hdeg, hdom⟩ := hgood t hgt
  have haffdom := goodFiber_geometricallyIntegral hd F C t hhom hdeg hdom
  exact ⟨totalDegree_pos_of_geometricDomain _ (hall t) haffdom, haffdom⟩

end CubicTenVariables.FixedIntegralSurfaceAffinePencil

import CubicTenVariables.ProjectiveMicrolocalModels
import CubicTenVariables.ProjectiveMicrolocalNumericalDepth

/-! Ten-variable assembly of the actual microlocal incidence conclusions.
There are exactly two explicit literature premises: the joint generic
projective microlocal certificate and the proper homogeneous-family depth
model corollary. Neither is given an inhabitant here. Closedness, both
codimension bounds, rational equality, exact good-characteristic depth
models and the literal exponential-sum bounds are then proved consequences.

The nested integral polynomials have frequency variables in their
coefficients and point variables outside. The existing geometricIncidence
uses (point,normal) coordinates in Fin(10+10); its fiber f K v is literally
the common zero set in point coordinates. This module makes no claim about
an internally constructed singular-support object or an adapted lisse
stratification (the separate SS13.2 obligation).
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.TenMicrolocalIncidence

open MvPolynomial HessianTheorem11
open BihomogeneousIncidenceFamily ProjectiveMicrolocalData
open ProjectiveMicrolocalModels RationalConeClosure
open ProjectiveFourierIdentity

/-- A concrete collection of the n=10 incidence conclusions. The depth
loci and rational loci are the actual previously defined sets; all nine
integral models and all arithmetic estimates share the same N and B. -/
structure Conclusion {t : ℕ} (F : MvPolynomial (Fin 10) ℤ)
    (f : Fin t → Polynomial 10 10) (N B : ℕ) : Prop where
  incidence_closed : AlgebraicallyClosedSet (geometricIncidence f)
  point_scaling : ∀ (v x : GeometricPoint 10), x ∈ fiber f GeometricField v →
    ∀ a : GeometricField, a • x ∈ fiber f GeometricField v
  normal_scaling : ∀ (v x : GeometricPoint 10), x ∈ fiber f GeometricField v →
    ∀ a : GeometricField, x ∈ fiber f GeometricField (a • v)
  geometric_incidence : IncidenceAndGauss F f GeometricField
  good_incidence : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ N →
    ∀ (K : Type) [Field K] [CharP K p], IncidenceAndGauss F f K
  geometric_depth : ∀ j : ℕ, 1 ≤ j → j ≤ 9 →
    AlgebraicallyClosedSet (ProjectiveMicrolocalDepth.depth f j) ∧
      IsAffineCone (ProjectiveMicrolocalDepth.depth f j) ∧
      affineDimension (ProjectiveMicrolocalDepth.depth f j) ≤ ((10-j : ℕ) : Dimension)
  rational_depth : ∀ j : ℕ, 1 ≤ j → j ≤ 9 →
    AlgebraicallyClosedSet (rationalDepth f j) ∧ IsAffineCone (rationalDepth f j) ∧
      rationalDepth f j ⊆ ProjectiveMicrolocalDepth.depth f j ∧
      rationalPoints (rationalDepth f j) = rationalPoints (ProjectiveMicrolocalDepth.depth f j) ∧
      affineDimension (rationalDepth f j) ≤ ((9-j : ℕ) : Dimension)
  rational_models : ∀ j : ℕ, 1 ≤ j → j ≤ 9 →
    ∃ (u : ℕ) (G : Fin u → MvPolynomial (Fin 10) ℤ) (d : Fin u → ℕ),
      (∀ i, (G i).IsHomogeneous (d i)) ∧
      IntegralModelDimension.rationalIdeal G =
        vanishingIdeal ℚ (rationalPoints (ProjectiveMicrolocalDepth.depth f j)) ∧
      IntegralModelDimension.geometricIdeal G = vanishingIdeal GeometricField (rationalDepth f j) ∧
      (∀ x : GeometricPoint 10, x ∈ rationalDepth f j ↔
        ∀ i, eval₂ (Int.castRingHom GeometricField) x (G i) = 0) ∧
      (∀ q : Fin 10 → ℚ, (∀ i, eval₂ (Int.castRingHom ℚ) q (G i) = 0) ↔
        rationalEmbedding q ∈ ProjectiveMicrolocalDepth.depth f j)
  depth_models : ∀ i : Fin 9, ZDepthModel f (i.val+1) N
  actual_depth : ∀ (K : Type) [Field K] (v : Fin 10 → K),
    (ProjectiveMicrolocalNumericalDepth.depth f K v : Dimension) =
        max (IntegralGeometricFiberDepth.geometricFiberDimension f K v) 0 ∧
      ProjectiveMicrolocalNumericalDepth.depth f K v ≤ 10
  fourier_bound : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ N →
    ∀ (K : Type) [Field K] [Fintype K] [CharP K p]
      (ψ : AddChar K ℂ), ψ ≠ 1 → ∀ (v : Fin 10 → K), v ≠ 0 →
      ‖normalizedFourierSum ψ (map (Int.castRingHom K) F) v‖ ≤
        (1+2*(B : ℝ)) * (Fintype.card K : ℝ)^
          ((9+(ProjectiveMicrolocalNumericalDepth.depth f K v : ℝ))/2)
  prime_bound : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ N →
    ∀ (v : Fin 10 → ℤ), (fun i => (v i : ZMod p)) ≠ 0 →
      ‖completeCubicSum F p v‖ ≤
        (1+2*(B : ℝ)) * (p : ℝ)^((11+
          (ProjectiveMicrolocalNumericalDepth.depth f (ZMod p)
            (fun i => (v i : ZMod p)) : ℝ))/2)

/-- Actual SS13.1 incidence/depth/trace conclusions from the two stated
generic literature premises. Anisotropy supplies nonzeroness of F, rather
than imposing an additional nonzero-polynomial hypothesis. -/
theorem exists_incidence
    (microlocal : Literature.ProjectiveMicrolocalCertificate)
    (F : MvPolynomial (Fin 10) ℤ) (hhom : F.IsHomogeneous 3)
    (hF : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ (t : ℕ) (f : Fin t → Polynomial 10 10) (N B : ℕ),
      1 ≤ N ∧ 1 ≤ B ∧ Conclusion F f N B := by
  let FQ : AnisotropicCubic 10 := ⟨map (Int.castRingHom ℚ) F,hhom.map _,hF⟩
  have hne : F ≠ 0 := by
    intro hz
    have h := anisotropic_polynomial_ne_zero (by norm_num) FQ
    apply h
    simp [FQ,hz]
  obtain ⟨t,f,N₀,B,hN₀,hB,hgeom,hgood⟩ :=
    microlocal 10 3 (by norm_num) (by norm_num) F hne hhom
  obtain ⟨N₁,hN₁,hmodels⟩ := exists_uniform_ten_depth_models hgeom
  have hred : GoodReduction F f (N₀*N₁) B := by
    constructor
    · intro p _ hp K _ _
      exact hgood.incidenceAndGauss p
        (fun hdiv => hp (hdiv.trans (dvd_mul_right N₀ N₁))) K
    · intro p _ hp K _ _ _ v hv e he
      exact hgood.trace p (fun hdiv => hp (hdiv.trans (dvd_mul_right N₀ N₁))) K v hv e he
  refine ⟨t,f,N₀*N₁,B,by nlinarith,hB,?_⟩
  constructor
  · exact ProjectiveMicrolocalModels.incidence_closed hgeom
  · exact incidence_point_scaling hgeom
  · exact incidence_normal_scaling hgeom
  · exact hgeom.incidenceAndGauss
  · exact hred.incidenceAndGauss
  · intro j hj hj9
    exact ⟨ProjectiveMicrolocalDepth.depth_closed hgeom (by omega),
      ProjectiveMicrolocalDepth.depth_cone hgeom j,
      ProjectiveMicrolocalDepth.depth_dimension_le hgeom (by omega)⟩
  · intro j hj hj9
    refine ⟨rationalDepth_closed j,rationalDepth_cone hgeom j,
      rationalDepth_subset hgeom (by omega),rationalDepth_points hgeom (by omega),?_⟩
    have hd := rationalDepth_dimension_le hgeom hF (j:=j) (by omega) (by omega)
    simpa only [show 10-(j+1) = 9-j by omega] using hd
  · intro j hj hj9
    obtain ⟨u,G,d,hd,hI,hIG,hpts,hrat,_⟩ :=
      exists_rational_depth_model hgeom hF (j:=j) (by omega) (by omega)
    exact ⟨u,G,d,hd,hI,hIG,hpts,hrat⟩
  · intro i
    exact (hmodels i).of_dvd (dvd_mul_left N₁ N₀)
  · intro K _ v
    exact ⟨ProjectiveMicrolocalNumericalDepth.depth_eq_max f K v,
      ProjectiveMicrolocalNumericalDepth.depth_le f K v⟩
  · intro p _ hp K _ _ _ ψ hψ v hv
    have hb := ProjectiveMicrolocalNumericalDepth.normalizedFourierSum_bound
      (by norm_num) F hhom (by norm_num) f (N₀*N₁) B hred p hp K ψ hψ v hv
    simpa only [Nat.cast_ofNat,show (10 : ℝ)-1 = 9 by norm_num] using hb
  · intro p _ hp v hv
    have hb := ProjectiveMicrolocalNumericalDepth.completeCubicSum_bound
      (by norm_num) F hhom (by norm_num) f (N₀*N₁) B hred p hp v hv
    simpa only [Nat.cast_ofNat,show (10 : ℝ)+1 = 11 by norm_num] using hb

end CubicTenVariables.TenMicrolocalIncidence

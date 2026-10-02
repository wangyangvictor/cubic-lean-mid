import CubicTenVariables.IntegralHypersurfaceBertiniFrame
import CubicTenVariables.CubicIntegralFrameFamily
import CubicTenVariables.Literature.HomogeneousHypersurfaceIntegralityOpen

/-!
# Integral principal-open certificates for hypersurface sections

The good extension-field frame is supplied by the internally proved Bertini
construction.  The sole input is openness of geometric integrality in a
fixed-degree homogeneous hypersurface family.  A maximal minor is included
in the same certificate, so every specialization on the resulting principal
open is an actual injective frame.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
noncomputable section

namespace CubicTenVariables.HypersurfaceIntegralFrameCertificate

open MvPolynomial Literature HessianTheorem11
open HessianTheorem11.PolynomialRestriction
open CubicIntegralFrameFamily ReducedHyperplaneIntegrality
universe u

private theorem eval_minor
    {R K : Type*} [CommRing R] [CommRing K] {n m : ℕ}
    (τ : R →+* K) (B : Matrix (Fin n) (Fin m) K)
    (rows : Fin m → Fin n) (cols : Fin m → Fin m) :
    eval₂Hom τ (fun ij : Parameters n m => B ij.1 ij.2)
      (((frame R n m).submatrix rows cols).det) =
        (B.submatrix rows cols).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  change eval₂Hom τ (fun ij : Parameters n m => B ij.1 ij.2)
    (frame R n m (rows i) (cols j)) = B (rows i) (cols j)
  simp only [frame_apply, eval₂Hom_X']

/-- A single good frame yields one literal coefficient polynomial.  Every
specialization where it is nonzero remains injective, of degree `d`, and
geometrically integral after the displayed algebraic-closure extension. -/
theorem exists_nonzero_certificate_of_good_frame
    (integralityOpen : HomogeneousHypersurfaceIntegralityOpen)
    {R Ω : Type} [CommRing R] [Field Ω] [IsAlgClosed Ω]
    {n m d : ℕ} (hd : 1 ≤ d)
    (ρ : R →+* Ω) (F : MvPolynomial (Fin n) R)
    (hF : F.IsHomogeneous d)
    (B : Matrix (Fin n) (Fin m) Ω) (hB : Function.Injective B.mulVec)
    (hrestricted : restrict B (map ρ F) ≠ 0)
    (hgood : IsDomain (MvPolynomial (Fin m) Ω ⧸
      Ideal.span {restrict B (map ρ F)})) :
    ∃ Δ : MvPolynomial (Parameters n m) R,
      eval₂Hom ρ (fun ij => B ij.1 ij.2) Δ ≠ 0 ∧
      ∀ (K : Type) [Field K] (τ : R →+* K)
        (A : Matrix (Fin n) (Fin m) K),
        eval₂Hom τ (fun ij => A ij.1 ij.2) Δ ≠ 0 →
          Function.Injective A.mulVec ∧
          (restrict A (map τ F)).IsHomogeneous d ∧
          (restrict A (map τ F)).totalDegree = d ∧
          IsDomain (MvPolynomial (Fin m) (AlgebraicClosure K) ⧸
            Ideal.span {map (algebraMap K (AlgebraicClosure K))
              (restrict A (map τ F))}) := by
  classical
  let ψ : MvPolynomial (Parameters n m) R →+* Ω :=
    eval₂Hom ρ (fun ij => B ij.1 ij.2)
  have hfamilyGood : IsDomain (MvPolynomial (Fin m) Ω ⧸
      Ideal.span {map ψ (polynomial (m := m) F)}) := by
    rw [show map ψ (polynomial (m := m) F) = restrict B (map ρ F) by
      exact specialize F ρ B]
    exact hgood
  obtain ⟨s, hs, hopen⟩ := integralityOpen
    (MvPolynomial (Parameters n m) R) Ω m d hd ψ
    (polynomial (m := m) F) (homogeneous F hF)
      (by rw [specialize F ρ B]; exact hrestricted) hfamilyGood
  have hBrank : B.rank = m := by
    change Module.finrank Ω (LinearMap.range B.mulVecLin) = m
    rw [LinearMap.finrank_range_of_inj hB]
    simp only [Module.finrank_pi, Fintype.card_fin]
  obtain ⟨rows, cols, hdet⟩ : ∃ (rows : Fin m → Fin n) (cols : Fin m → Fin m),
      (B.submatrix rows cols).det ≠ 0 :=
    Eq.mp (congrArg (fun t => ∃ (rows : Fin t → Fin n) (cols : Fin t → Fin m),
      (B.submatrix rows cols).det ≠ 0) hBrank)
      (HessianTheorem11.MatrixRankMinors.exists_rank_minor B)
  let M := ((frame R n m).submatrix rows cols).det
  have hM : ψ M ≠ 0 := by
    change eval₂Hom ρ (fun ij => B ij.1 ij.2)
      (((frame R n m).submatrix rows cols).det) ≠ 0
    rw [eval_minor]
    exact hdet
  let Δ := s * M
  have hΔ : ψ Δ ≠ 0 := by
    simpa only [Δ, map_mul] using mul_ne_zero hs hM
  refine ⟨Δ, hΔ, ?_⟩
  intro K _ τ A hA
  let ε : MvPolynomial (Parameters n m) R →+* K :=
    eval₂Hom τ (fun ij => A ij.1 ij.2)
  have hh : ε s ≠ 0 ∧ ε M ≠ 0 :=
    mul_ne_zero_iff.mp (by simpa only [Δ, map_mul] using hA)
  have hminor : (A.submatrix rows cols).det ≠ 0 := by
    simpa only [ε, M, eval_minor] using hh.2
  have hopenA := hopen K ε hh.1
  have hspecialize : map ε (polynomial (m := m) F) = restrict A (map τ F) :=
    specialize F τ A
  rw [hspecialize] at hopenA
  exact ⟨injective_of_minor A (rows, cols) hminor,
    homogeneous_restrict A _ (hF.map τ), hopenA⟩

/-- The internally proved Bertini theorem supplies the good frame needed by
the preceding certificate construction for every integral surface equation
which is geometrically integral in characteristic zero. -/
theorem exists_nonzero_surface_hyperplane_certificate
    (integralityOpen : HomogeneousHypersurfaceIntegralityOpen)
    {d : ℕ} (hd : 2 ≤ d)
    (F : MvPolynomial (Fin 4) ℤ) (hF0 : F ≠ 0) (hF : F.IsHomogeneous d)
    (hgeom : IsDomain (MvPolynomial (Fin 4) GeometricField ⧸
      Ideal.span {map (Int.castRingHom GeometricField) F})) :
    ∃ Δ : MvPolynomial (Parameters 4 3) ℤ, Δ ≠ 0 ∧
      ∀ (K : Type) [Field K] (A : Matrix (Fin 4) (Fin 3) K),
        eval₂ (Int.castRingHom K) (fun ij => A ij.1 ij.2) Δ ≠ 0 →
          Function.Injective A.mulVec ∧
          (restrict A (map (Int.castRingHom K) F)).IsHomogeneous d ∧
          (restrict A (map (Int.castRingHom K) F)).totalDegree = d ∧
          IsDomain (MvPolynomial (Fin 3) (AlgebraicClosure K) ⧸
            Ideal.span {map (algebraMap K (AlgebraicClosure K))
              (restrict A (map (Int.castRingHom K) F))}) := by
  have hFne : map (Int.castRingHom GeometricField) F ≠ 0 := by
    intro hz
    exact hF0 ((map_injective (Int.castRingHom GeometricField)
      Int.cast_injective) (by simpa only [map_zero] using hz))
  have hprime := (Ideal.Quotient.isDomain_iff_prime _).mp hgeom
  have hirr : Irreducible (map (Int.castRingHom GeometricField) F) :=
    ((Ideal.span_singleton_prime hFne).mp hprime).irreducible
  obtain ⟨L, hL, hdata⟩ :=
    IntegralHypersurfaceBertiniFrame.exists_integral_surface_hyperplane_frame_nonzero
      hd (map (Int.castRingHom GeometricField) F)
      (hF.map (Int.castRingHom GeometricField)) hirr
  letI : Field L := hL
  obtain ⟨hA, hdata⟩ := hdata
  letI : Algebra GeometricField L := hA
  obtain ⟨hclosed, B, hB, hrestriction, _hhom, hdomain⟩ := hdata
  letI : IsAlgClosed L := hclosed
  let ρ : ℤ →+* L := Int.castRingHom L
  have hmap : map ρ F = map (algebraMap GeometricField L)
      (map (Int.castRingHom GeometricField) F) := by
    rw [map_map]
    exact congrArg (fun φ : ℤ →+* L => map φ F)
      (RingHom.ext_int ρ ((algebraMap GeometricField L).comp
        (Int.castRingHom GeometricField)))
  have hdomain' : IsDomain (MvPolynomial (Fin 3) L ⧸
      Ideal.span {restrict B (map ρ F)}) := by
    rw [hmap]
    exact hdomain
  obtain ⟨Δ, hΔ, hgood⟩ := exists_nonzero_certificate_of_good_frame
    integralityOpen (by omega : 1 ≤ d) ρ F hF B hB (by rw [hmap]; exact hrestriction) hdomain'
  refine ⟨Δ, ?_, ?_⟩
  · intro hz
    exact hΔ (by rw [hz, map_zero])
  · intro K _ A hAeval
    simpa only [eval₂_eq_eval_map] using
      hgood K (Int.castRingHom K) A hAeval

end CubicTenVariables.HypersurfaceIntegralFrameCertificate

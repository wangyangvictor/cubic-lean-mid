import CubicTenVariables.CubicIntegralFrameFamily
import CubicTenVariables.CubicIrreducibilityOpen

/-! Integral cubic hyperplane-frame certificates in arbitrary dimension.
The generic helper starts from an actual good matrix; the public hyperplane
theorem constructs that matrix using the internally proved Bertini theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
noncomputable section
namespace CubicTenVariables.CubicSurfaceFrameCertificate
open MvPolynomial Literature HessianTheorem11.PolynomialRestriction
open CubicIntegralFrameFamily ReducedHyperplaneIntegrality

private theorem eval_minor {R K : Type*} [CommRing R] [CommRing K] {n m : ℕ}
    (τ : R →+* K) (B : Matrix (Fin n) (Fin m) K)
    (rows : Fin m → Fin n) (cols : Fin m → Fin m) :
    eval₂Hom τ (fun ij : Parameters n m => B ij.1 ij.2)
      (((frame R n m).submatrix rows cols).det) = (B.submatrix rows cols).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  change eval₂Hom τ (fun ij : Parameters n m => B ij.1 ij.2)
    (frame R n m (rows i) (cols j)) = B (rows i) (cols j)
  simp only [frame_apply, eval₂Hom_X']

/-- A literal integral frame at one algebraically closed specialization
produces an open certificate for injectivity and geometric integrality.
There is no characteristic or injectivity requirement on the coefficient map. -/
theorem exists_nonzero_certificate_of_good_frame
    {R Ω : Type*} [CommRing R] [Field Ω] [IsAlgClosed Ω] {n m : ℕ}
    (ρ : R →+* Ω) (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous 3)
    (B : Matrix (Fin n) (Fin m) Ω) (hB : Function.Injective B.mulVec)
    (hirr : Irreducible (restrict B (map ρ F))) :
    ∃ Δ : MvPolynomial (Parameters n m) R, map ρ Δ ≠ 0 ∧
      ∀ (K : Type*) [Field K] (τ : R →+* K) (A : Matrix (Fin n) (Fin m) K),
        eval₂Hom τ (fun ij => A ij.1 ij.2) Δ ≠ 0 →
          Function.Injective A.mulVec ∧
          (restrict A (map τ F)).IsHomogeneous 3 ∧
          (restrict A (map τ F)).totalDegree = 3 ∧
          GeometricallyIntegralForm (restrict A (map τ F)) := by
  classical
  let ψ : MvPolynomial (Parameters n m) R →+* Ω :=
    eval₂Hom ρ (fun ij => B ij.1 ij.2)
  have hψ : Irreducible (map ψ (polynomial (m := m) F)) := by
    rw [show ψ = eval₂Hom ρ (fun ij => B ij.1 ij.2) from rfl, specialize]
    exact hirr
  obtain ⟨s, hs, hgood⟩ := CubicIrreducibilityOpen.exists_geometrically_integral_principal_open
    ψ (polynomial (m := m) F) (homogeneous F hF) hψ
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
  refine ⟨Δ, ?_, ?_⟩
  · intro hz
    have he : ψ Δ = eval (fun ij => B ij.1 ij.2) (map ρ Δ) := by
      rw [eval_map]
      rfl
    exact hΔ (by rw [he, hz, map_zero])
  · intro K _ τ A hA
    let ε : MvPolynomial (Parameters n m) R →+* K :=
      eval₂Hom τ (fun ij => A ij.1 ij.2)
    have hh : ε s ≠ 0 ∧ ε M ≠ 0 :=
      mul_ne_zero_iff.mp (by simpa only [Δ, map_mul] using hA)
    have hminor : (A.submatrix rows cols).det ≠ 0 := by
      simpa only [ε, M, eval_minor] using hh.2
    have hcert := hgood K ε hh.1
    rw [show ε = eval₂Hom τ (fun ij => A ij.1 ij.2) from rfl, specialize] at hcert
    exact ⟨injective_of_minor A (rows, cols) hminor,
      homogeneous_restrict A _ (hF.map τ), hcert⟩

/-- Integral cubic hyperplane sections have an actual nonzero coefficient
certificate. The good frame is constructed internally over an extension
field; no section-existence or openness premise appears. -/
theorem exists_nonzero_hyperplane_certificate
    {R Ω : Type*} [CommRing R] [Field Ω] [CharZero Ω] [IsAlgClosed Ω]
    (r : ℕ) (ρ : R →+* Ω) (F : MvPolynomial (Fin (r+4)) R)
    (hF : F.IsHomogeneous 3) (hirr : Irreducible (map ρ F)) :
    ∃ Δ : MvPolynomial (Parameters (r+4) (r+3)) R, map ρ Δ ≠ 0 ∧
      ∀ (K : Type*) [Field K] (τ : R →+* K)
        (B : Matrix (Fin (r+4)) (Fin (r+3)) K),
        eval₂Hom τ (fun ij => B ij.1 ij.2) Δ ≠ 0 →
          Function.Injective B.mulVec ∧
          (restrict B (map τ F)).IsHomogeneous 3 ∧
          (restrict B (map τ F)).totalDegree = 3 ∧
          GeometricallyIntegralForm (restrict B (map τ F)) := by
  obtain ⟨L, hL, hdata⟩ := IntegralCubicBertiniFrame.exists_integral_hyperplane_frame
    r (map ρ F) (hF.map ρ) hirr
  letI : Field L := hL
  obtain ⟨hA, hdata⟩ := hdata
  letI : Algebra Ω L := hA
  obtain ⟨hclosed, B, hB, _, hI⟩ := hdata
  letI : IsAlgClosed L := hclosed
  let α : Ω →+* L := algebraMap Ω L
  obtain ⟨Δ, hΔ, hgood⟩ := exists_nonzero_certificate_of_good_frame
    (α.comp ρ) F hF B hB (by simpa only [map_map] using hI)
  refine ⟨Δ, ?_, hgood⟩
  intro hz
  exact hΔ (by rw [← map_map, hz, map_zero])

/-- A geometrically integral cubic specialization forces irreducibility
at an injective algebraically closed coefficient embedding, in any number
of variables and without characteristic or Noetherian hypotheses. -/
theorem irreducible_of_geometricallyIntegral_specialization
    {R Ω K : Type*} [CommRing R] [Field Ω] [IsAlgClosed Ω] [Field K] {n : ℕ}
    (κ : R →+* Ω) (hκ : Function.Injective κ)
    (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous 3)
    (τ : R →+* K) (hI : GeometricallyIntegralForm (map τ F)) :
    Irreducible (map κ F) := by
  let α := algebraMap K (AlgebraicClosure K)
  have hne : map α (map τ F) ≠ 0 := by
    intro hz
    exact hI.1 ((map_injective α α.injective) (by simpa only [map_zero] using hz))
  have hp := (Ideal.Quotient.isDomain_iff_prime _).mp hI.2
  have hirr : Irreducible (map (α.comp τ) F) := by
    simpa only [map_map] using ((Ideal.span_singleton_prime hne).mp hp).irreducible
  obtain ⟨s, hs, hgood⟩ := CubicIrreducibilityOpen.exists_principal_open
    (α.comp τ) F hF hirr
  have hs0 : s ≠ 0 := fun hz => hs (by rw [hz, map_zero])
  exact hgood Ω κ (fun hz => hs0 (hκ (by simpa only [map_zero] using hz)))

end CubicTenVariables.CubicSurfaceFrameCertificate

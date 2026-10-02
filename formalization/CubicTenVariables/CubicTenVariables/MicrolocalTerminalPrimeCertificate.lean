import CubicTenVariables.MicrolocalIntegerCertificate
import CubicTenVariables.TerminalTenBound
import HessianTheorem11.NormalCrossGenericRank

/-! The terminal p^8 certificate at every nonzero integer frequency.
The geometric assertion proved here concerns rational points of Z6, not
all its geometric points. It follows from the existing rational terminal
bound and incidence containment. The j=5 certificate then supplies the
actual prime sum estimate with polynomially bounded exceptional integer.
No additional point-count or literature premise is introduced. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.MicrolocalTerminalPrimeCertificate

open MvPolynomial HessianTheorem11 Module
open BihomogeneousIncidenceFamily ProjectiveMicrolocalData RationalConeClosure

/-- A cone of dimension at most zero has no nonzero point: such a point
would put its entire one-dimensional linear span inside the cone. -/
theorem cone_subset_origin_of_dimension_le_zero {n : ℕ}
    (Z : Set (GeometricPoint n)) (hcone : IsAffineCone Z)
    (hdim : affineDimension Z ≤ 0) : Z ⊆ {0} := by
  intro z hz
  change z = 0
  by_contra hn
  have hsub : (Submodule.span GeometricField {z} : Set (GeometricPoint n)) ⊆ Z := by
    intro x hx
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
    exact hcone a z hz
  have hd := (affineDimension_mono hsub).trans hdim
  rw [affineDimension_submodule_from_generic_rank Unconditional.genericRankOpen,
    finrank_span_singleton hn] at hd
  norm_num at hd

/-- The sixth actual microlocal depth locus has no nonzero rational point.
This does not assert emptiness of its nonzero geometric points. -/
theorem rational_not_mem_depth_six {t : ℕ} (F : MvPolynomial (Fin 10) ℤ)
    (hhom : F.IsHomogeneous 3) (hF : Anisotropic (map (Int.castRingHom ℚ) F))
    (f : Fin t → Polynomial 10 10) (hgeom : Geometry F f)
    (v : Fin 10 → ℚ) (hv : v ≠ 0) :
    rationalEmbedding v ∉ ProjectiveMicrolocalDepth.depth f 6 := by
  let FQ : AnisotropicCubic 10 := ⟨map (Int.castRingHom ℚ) F,hhom.map _,hF⟩
  intro hdepth
  have hbad : rationalEmbedding v ∈
      TerminalBadNormals.badNormals (geometricPolynomial FQ.polynomial) 5 :=
    ConormalTerminalComparison.depth_subset_section_badNormals
      (geometricPolynomial FQ.polynomial) (geometricIncidence f)
      (ProjectiveMicrolocalDepth.incidence_subset_section hgeom) 5 hdepth
  have hmem : rationalEmbedding v ∈ rationalConeClosure
      (TerminalBadNormals.badNormals (geometricPolynomial FQ.polynomial) 5) :=
    Or.inl (subset_geometricClosure _ ⟨v,hbad,rfl⟩)
  have hz := cone_subset_origin_of_dimension_le_zero _
    (rationalConeClosure_isAffineCone _ (TerminalBadNormals.badNormals_isAffineCone _ _))
    (TerminalTenBound.rational_higher_stratum_dimension_le_zero FQ 5 (by omega)) hmem
  exact hv ((rationalEmbedding_eq_zero_iff v).mp hz)

theorem integer_not_mem_depth_six {t : ℕ} (F : MvPolynomial (Fin 10) ℤ)
    (hhom : F.IsHomogeneous 3) (hF : Anisotropic (map (Int.castRingHom ℚ) F))
    (f : Fin t → Polynomial 10 10) (hgeom : Geometry F f)
    (v : Fin 10 → ℤ) (hv : v ≠ 0) :
    (fun a => (v a : GeometricField)) ∉ ProjectiveMicrolocalDepth.depth f 6 := by
  have hvQ : (fun a => (v a : ℚ)) ≠ 0 := by
    intro hz
    apply hv
    ext a
    change v a = 0
    have ha : (v a : ℚ) = 0 := congrFun hz a
    exact_mod_cast ha
  simpa only [rationalEmbedding,map_intCast] using
    rational_not_mem_depth_six F hhom hF f hgeom (fun a => (v a : ℚ)) hvQ

/-- Fixed constants precede every nonzero integer frequency, height and
prime. Both the positive exceptional integer and the actual p^8 estimate
are constructed from the existing shared geometric/trace conclusions. -/
theorem exists_terminal_certificate {t : ℕ} (F : MvPolynomial (Fin 10) ℤ)
    (hhom : F.IsHomogeneous 3) (hF : Anisotropic (map (Int.castRingHom ℚ) F))
    (f : Fin t → Polynomial 10 10) (N B : ℕ) (hN : 1 ≤ N)
    (hgeom : Geometry F f) (h : TenMicrolocalIncidence.Conclusion F f N B) :
    ∃ (C : ℝ) (D : ℕ), 1 ≤ C ∧ ∀ v : Fin 10 → ℤ, v ≠ 0 →
      ∃ Δ : ℕ, 1 ≤ Δ ∧
        (∀ H : ℝ, 1 ≤ H → (∀ a, |(v a : ℝ)| ≤ H) → (Δ : ℝ) ≤ C * H^D) ∧
        ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ Δ →
          ‖completeCubicSum F p v‖ ≤ C * (p : ℝ)^(8 : ℝ) := by
  obtain ⟨u,G,C₀,D,hC₀,hgeo,hcert⟩ :=
    MicrolocalIntegerCertificate.exists_off_depth_certificate h hN 5 (by omega)
  let C : ℝ := max C₀ (1+2*(B : ℝ))
  refine ⟨C,D,hC₀.trans (le_max_left _ _),?_⟩
  intro v hv
  obtain ⟨Δ,hΔ,heq,hheight,hprime⟩ := hcert v hv
    (integer_not_mem_depth_six F hhom hF f hgeom v hv)
  refine ⟨Δ,hΔ,?_,?_⟩
  · intro H hH hvH
    exact (hheight H hH hvH).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (by linarith) D))
  · intro p _ hp
    have hb := (hprime p hp).2
    have hb' : ‖completeCubicSum F p v‖ ≤
        (1+2*(B : ℝ)) * (p : ℝ)^(8 : ℝ) := by
      convert hb using 1
      norm_num
    exact hb'.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))

end CubicTenVariables.MicrolocalTerminalPrimeCertificate

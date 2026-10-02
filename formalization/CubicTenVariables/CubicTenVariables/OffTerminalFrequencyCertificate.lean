import CubicTenVariables.MicrolocalTerminalDepth
import CubicTenVariables.PrimeSquareIntegerCertificate

/-! The actual off-terminal exceptional set and one common integer certificate.
The rational set below is the manuscript's punctured cone over B₄: the
projectivized section-singularity fiber has dimension at least four.
The proof uses the raw incidence containment, not avoidance of a potentially
larger geometric closure. One integer from the same depth-five model gives
the actual prime and prime-square bounds outside its prime divisors. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.OffTerminalFrequencyCertificate
open MvPolynomial HessianTheorem11 BibleProjectiveGeometry
open BihomogeneousIncidenceFamily ProjectiveMicrolocalData RationalConeClosure
open TerminalSectionIncidence TerminalProjectiveDimension

/-- The literal rational exceptional set B of the manuscript. No closure
of its rational points or of its bad-normal parameter set is taken. -/
def exceptionalSet (F : MvPolynomial (Fin 10) ℤ) : Set (Fin 10 → ℚ) :=
  {v | v ≠ 0 ∧ (4 : Dimension) ≤ projectiveDimension
    (sectionSingularFiber (geometricPolynomial (map (Int.castRingHom ℚ) F))
      (rationalEmbedding v))}

theorem mem_exceptional_iff (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (v : Fin 10 → ℚ) :
    v ∈ exceptionalSet F ↔ v ≠ 0 ∧ rationalEmbedding v ∈
      TerminalBadNormals.badNormals (geometricPolynomial (map (Int.castRingHom ℚ) F)) 4 := by
  change (v ≠ 0 ∧ (4 : Dimension) ≤ projectiveDimension
    (sectionSingularFiber (geometricPolynomial (map (Int.castRingHom ℚ) F))
      (rationalEmbedding v))) ↔ _
  exact and_congr Iff.rfl (sectionSingularFiber_projective_threshold
    (geometricPolynomial (map (Int.castRingHom ℚ) F))
    (geometric_homogeneous (hF.map (Int.castRingHom ℚ))) (rationalEmbedding v) 4)

/-- Outside the actual projective bad-section locus, the same microlocal
family is outside its actual depth-five locus. -/
theorem integer_not_mem_depth_five {t : ℕ} {F : MvPolynomial (Fin 10) ℤ}
    {f : Fin t → Polynomial 10 10} (hgeo : Geometry F f) (hF : F.IsHomogeneous 3)
    (v : Fin 10 → ℤ) (hv : v ≠ 0)
    (hoff : (fun i => (v i : ℚ)) ∉ exceptionalSet F) :
    (fun i => (v i : GeometricField)) ∉ ProjectiveMicrolocalDepth.depth f 5 := by
  intro hd
  have hbad := MicrolocalTerminalDepth.depth_succ_subset_badNormals hgeo 4 hd
  apply hoff
  apply (mem_exceptional_iff F hF _).mpr
  constructor
  · intro hz
    apply hv
    funext i
    have hi : (v i : ℚ) = 0 := congrFun hz i
    exact_mod_cast hi
  · simpa only [rationalEmbedding,map_intCast] using hbad

private theorem cast_eval (P : MvPolynomial (Fin 10) ℤ) (v : Fin 10 → ℤ) :
    (eval v P : GeometricField) =
      eval₂ (Int.castRingHom GeometricField) (fun i => (v i : GeometricField)) P := by
  simpa only [Function.comp_def,Int.coe_castRingHom,eval₂_eq_eval_map] using
    map_eval (Int.castRingHom GeometricField) v P

/-- Constants precede every frequency and height. The common positive
integer is constructed as N times one nonzero defining-equation value
times one nonzero coordinate, in absolute value. It works for both literal
complete sums at every prime not dividing it. -/
theorem exists_certificate (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    {t : ℕ} {F : MvPolynomial (Fin 10) ℤ} (hF : F.IsHomogeneous 3)
    {f : Fin t → Polynomial 10 10} {N B : ℕ}
    (hN : 1 ≤ N) (hgeo : Geometry F f)
    (hData : TenMicrolocalIncidence.Conclusion F f N B) :
    ∃ (C : ℝ) (D : ℕ), 1 ≤ C ∧ ∀ v : Fin 10 → ℤ, v ≠ 0 →
      (fun i => (v i : ℚ)) ∉ exceptionalSet F →
      ∃ Δ : ℕ, 1 ≤ Δ ∧ N ∣ Δ ∧
        (∀ H : ℝ, 1 ≤ H → (∀ i, |(v i : ℝ)| ≤ H) → (Δ : ℝ) ≤ C*H^D) ∧
        ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ Δ →
          ‖completeCubicSum F p v‖ ≤ C*(p : ℝ)^((15 : ℝ)/2) ∧
          ‖completeCubicSum F (p^2) v‖ ≤ C*(p : ℝ)^15 := by
  obtain ⟨u,G,d,hd,hI,hzero,hgood⟩ := hData.depth_models ⟨4,by decide⟩
  obtain ⟨Ch,D,hCh,hcert⟩ := MicrolocalIntegerCertificate.exists_bounded_certificate N hN G
  obtain ⟨Cs,hCs,hsquare⟩ := PrimeSquareMicrolocalBound.exists_off_depth_bound pointcount hF hData
  let C : ℝ := max Ch (max (1+2*(B : ℝ)) Cs)
  have hC : 1 ≤ C := hCh.trans (le_max_left _ _)
  have hprimeC : 1+2*(B : ℝ) ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hsquareC : Cs ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C,D,hC,?_⟩
  intro v hv hoff
  have hdepth := integer_not_mem_depth_five hgeo hF v hv hoff
  have hG : ∃ i, eval v (G i) ≠ 0 := by
    by_contra! hz
    apply hdepth
    apply (hzero _).mp
    intro i
    rw [← cast_eval,hz i,Int.cast_zero]
  obtain ⟨Δ,hΔ,heq,hheight,hreduce⟩ := hcert v hv hG
  have hND : N ∣ Δ := by
    obtain ⟨i,k,hi,hk,rfl⟩ := heq
    exact dvd_mul_right _ _
  refine ⟨Δ,hΔ,hND,?_,?_⟩
  · intro H hH hvH
    exact (hheight H hH hvH).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · intro p _ hp
    obtain ⟨hpN,hvp,hGp⟩ := hreduce p hp (ZMod p)
    have hdim : ¬ (5 : Dimension) ≤ IntegralGeometricFiberDepth.geometricFiberDimension f
        (ZMod p) (fun i => (v i : ZMod p)) := by
      intro hdim
      obtain ⟨i,hi⟩ := hGp
      exact hi (((hgood p Fact.out hpN (ZMod p)).1 _).mpr hdim i)
    constructor
    · have hbound := MicrolocalOffDepthBound.prime_bound hData p hpN v hvp 4 hdim
      norm_num only [Nat.cast_ofNat,show (11+(4 : ℝ))/2 = 15/2 by norm_num] at hbound
      exact hbound.trans (mul_le_mul_of_nonneg_right hprimeC (by positivity))
    · have hbound := hsquare p hpN v hvp 4 hdim
      norm_num only [show 11+4 = (15 : ℕ) by decide] at hbound
      exact hbound.trans (mul_le_mul_of_nonneg_right hsquareC (by positivity))

end CubicTenVariables.OffTerminalFrequencyCertificate

import CubicTenVariables.MicrolocalTerminalDepth
import CubicTenVariables.TerminalFifthComparison
import CubicTenVariables.TenMicrolocalIncidence
import CubicTenVariables.Literature.BoundedDegreeAffinePointCount

/-! Uniform finite-field support counts for the actual depth loci Z2,...,Z6.
The last two exponents come from the proved terminal section/Gauss geometry.
The very same integral equations selected by the supplied depth models are
used for dimension spreading and point counting, including empty models.
Only the previously stated generic bounded-degree point-count input is used. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.MicrolocalDepthSupportCount
open MvPolynomial HessianTheorem11
open ProjectiveMicrolocalData ProjectiveMicrolocalDepth ProjectiveMicrolocalModels
open BihomogeneousIncidenceFamily TerminalIntegralClosureModels
open scoped BigOperators

def profile : Fin 5 → ℕ := ![8,7,6,4,3]

theorem profile_values :
    profile 0 = 8 ∧ profile 1 = 7 ∧ profile 2 = 6 ∧ profile 3 = 4 ∧ profile 4 = 3 := by
  decide

theorem depth_five_dimension_le_four {t : ℕ} {F : MvPolynomial (Fin 10) ℤ}
    {f : Fin t → Polynomial 10 10} (h : Geometry F f) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F)) :
    affineDimension (depth f 5) ≤ (4 : Dimension) := by
  let A : AnisotropicCubic 10 := ⟨map (Int.castRingHom ℚ) F,hhom.map _,hAn⟩
  exact (affineDimension_mono
    (MicrolocalTerminalDepth.depth_succ_subset_sectionClosure h 4)).trans
      (ten_sectionClosure_dimension A)

theorem depth_six_dimension_le_three {t : ℕ} {F : MvPolynomial (Fin 10) ℤ}
    {f : Fin t → Polynomial 10 10} (h : Geometry F f) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F)) :
    affineDimension (depth f 6) ≤ (3 : Dimension) := by
  let A : AnisotropicCubic 10 := ⟨map (Int.castRingHom ℚ) F,hhom.map _,hAn⟩
  have hd : affineDimension (sectionClosure A.polynomial 5) ≤ (3 : Dimension) := by
    rw [TerminalFifthComparison.ten_fifth_closures_eq A]
    exact ten_gaussClosure_dimension A
  exact (affineDimension_mono
    (MicrolocalTerminalDepth.depth_succ_subset_sectionClosure h 5)).trans hd

theorem depth_dimension_profile {t : ℕ} {F : MvPolynomial (Fin 10) ℤ}
    {f : Fin t → Polynomial 10 10} (h : Geometry F f) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F)) (j : Fin 5) :
    affineDimension (depth f (j.val+2)) ≤ (profile j : Dimension) := by
  fin_cases j
  · simpa [profile] using depth_dimension_le h (j := 2) (by decide)
  · simpa [profile] using depth_dimension_le h (j := 3) (by decide)
  · simpa [profile] using depth_dimension_le h (j := 4) (by decide)
  · simpa [profile] using depth_five_dimension_le_four h hhom hAn
  · simpa [profile] using depth_six_dimension_le_three h hhom hAn

private theorem equation_count (lit : Literature.BoundedDegreeAffinePointCount)
    {n u : ℕ} (G : Fin u → MvPolynomial (Fin n) ℤ) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (K : Type) [Field K] [Fintype K] (r : ℕ),
      ringKrullDim (MvPolynomial (Fin n) (AlgebraicClosure K) ⧸
        FixedEquationNormalization.equationIdeal G (AlgebraicClosure K)) ≤
          (r : Dimension) →
      Nat.card {v : Fin n → K // ∀ i, eval₂ (Int.castRingHom K) v (G i) = 0} ≤
        C * (Fintype.card K)^r := by
  classical
  let d := 1 + ∑ i, (G i).totalDegree
  obtain ⟨C,hC,hbound⟩ := lit n u d (by dsimp [d]; omega)
  refine ⟨C,hC,?_⟩
  intro K _ _ r hd
  have hdegree (i : Fin u) : (map (Int.castRingHom K) (G i)).totalDegree ≤ d := by
    have hm : (map (Int.castRingHom K) (G i)).totalDegree ≤ (G i).totalDegree :=
      Finset.sup_mono (support_map_subset _ _)
    have hs : (G i).totalDegree ≤ ∑ a, (G a).totalDegree :=
      Finset.single_le_sum (fun a _ => Nat.zero_le (G a).totalDegree) (Finset.mem_univ i)
    dsimp [d]
    omega
  have hcomp : (algebraMap K (AlgebraicClosure K)).comp (Int.castRingHom K) =
      Int.castRingHom (AlgebraicClosure K) := RingHom.ext_int _ _
  have hg : Literature.geometricEquationDimension
      (fun i => map (Int.castRingHom K) (G i)) ≤ (r : Dimension) := by
    have he : (fun i => map (algebraMap K (AlgebraicClosure K))
        (map (Int.castRingHom K) (G i))) =
        FixedEquationNormalization.equationsOver G (AlgebraicClosure K) := by
      funext i
      rw [MvPolynomial.map_map,hcomp]
      rfl
    unfold Literature.geometricEquationDimension
    rw [he]
    exact hd
  simpa only [eval_map] using hbound K (fun i => map (Int.castRingHom K) (G i))
    hdegree r hg

private theorem exists_level_bound (lit : Literature.BoundedDegreeAffinePointCount)
    {t : ℕ} {F : MvPolynomial (Fin 10) ℤ} {f : Fin t → Polynomial 10 10}
    {N B : ℕ} (h : Geometry F f) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hData : TenMicrolocalIncidence.Conclusion F f N B) (j : Fin 5) :
    ∃ E C : ℕ, 1 ≤ E ∧ 1 ≤ C ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ N → ¬ p ∣ E →
      ∀ (K : Type) [Field K] [Fintype K] [CharP K p],
        Nat.card {v : Fin 10 → K // ((j.val+2 : ℕ) : Dimension) ≤
          IntegralGeometricFiberDepth.geometricFiberDimension f K v} ≤
            C * (Fintype.card K)^(profile j) := by
  obtain ⟨u,G,d,hd,hI,hpts,hgood⟩ := hData.depth_models ⟨j.val+1,by omega⟩
  have hI' : IntegralModelDimension.geometricIdeal G =
      vanishingIdeal GeometricField (depth f (j.val+2)) := by simpa using hI
  have hdim : ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸
      FixedEquationNormalization.equationIdeal G ℚ) ≤ (profile j : Dimension) := by
    change ringKrullDim (_ ⧸ IntegralModelDimension.rationalIdeal G) ≤ _
    rw [ExactRationalConeModel.rational_quotient_dimension_eq G _ hI']
    exact depth_dimension_profile h hhom hAn j
  obtain ⟨E,hE,hEgood⟩ := FixedEquationDimensionAll.exists_good_characteristic_dimension_bound G hdim
  obtain ⟨C,hC,hcount⟩ := equation_count lit G
  refine ⟨E,C,hE,hC,?_⟩
  intro p hp hpN hpE K _ _ _
  have hc := hcount K (profile j) (hEgood p hp hpE (AlgebraicClosure K)).1
  have heq : {v : Fin 10 → K | ∀ i, eval₂ (Int.castRingHom K) v (G i) = 0} =
      {v | ((j.val+2 : ℕ) : Dimension) ≤
        IntegralGeometricFiberDepth.geometricFiberDimension f K v} := by
    ext v
    simpa using (hgood p hp hpN K).1 v
  change Nat.card ({v : Fin 10 → K | ((j.val+2 : ℕ) : Dimension) ≤
    IntegralGeometricFiberDepth.geometricFiberDimension f K v}) ≤ _
  rw [← heq]
  exact hc

/-- One exceptional integer and one constant precede all five depth levels,
all good primes and every finite extension of their prime fields. The
counted loci are the actual geometric-fiber depth loci, not supplied models. -/
theorem exists_uniform_bound (lit : Literature.BoundedDegreeAffinePointCount)
    {t : ℕ} {F : MvPolynomial (Fin 10) ℤ} {f : Fin t → Polynomial 10 10}
    {N B : ℕ} (h : Geometry F f) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hData : TenMicrolocalIncidence.Conclusion F f N B) (hN : 1 ≤ N) :
    ∃ D C : ℕ, 1 ≤ D ∧ N ∣ D ∧ 1 ≤ C ∧ ∀ j : Fin 5,
      ∀ p : ℕ, p.Prime → ¬ p ∣ D → ∀ (K : Type) [Field K] [Fintype K] [CharP K p],
        Nat.card {v : Fin 10 → K // ((j.val+2 : ℕ) : Dimension) ≤
          IntegralGeometricFiberDepth.geometricFiberDimension f K v} ≤
            C * (Fintype.card K)^(profile j) := by
  classical
  choose E C hE hC hb using fun j : Fin 5 => exists_level_bound lit h hhom hAn hData j
  have hsum (j : Fin 5) : C j ≤ ∑ i, C i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (C i)) (Finset.mem_univ j)
  refine ⟨N * ∏ i, E i,∑ i, C i,?_,dvd_mul_right _ _,(hC 0).trans (hsum 0),?_⟩
  · have hp : 1 ≤ ∏ i, E i := Finset.one_le_prod' (fun i _ => hE i)
    nlinarith
  · intro j p hp hpD K _ _ _
    have hpN : ¬ p ∣ N := fun hdiv => hpD (hdiv.trans (dvd_mul_right _ _))
    have hpE : ¬ p ∣ E j := fun hdiv => hpD
      ((hdiv.trans (Finset.dvd_prod_of_mem E (Finset.mem_univ j))).trans (dvd_mul_left _ _))
    exact (hb j p hp hpN hpE K).trans (Nat.mul_le_mul_right _ (hsum j))

end CubicTenVariables.MicrolocalDepthSupportCount

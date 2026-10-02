import CubicTenVariables.CubicIntegralHyperplaneNormalCertificate
import CubicTenVariables.CubicNonconicalHyperplaneCertificate
import CubicTenVariables.CubicSurfaceFrameCertificate
import CubicTenVariables.CharacteristicZeroCertificateUniformity

/-! One-normal certificates for integral nonconical cubic hyperplane sections.
Noetherian induction covers every coefficient stratum. The excluded integer
and degree bound are fixed before all fields and all coefficient fibers.
The parameter variables are the actual entries of one normal vector. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
noncomputable section
open scoped Classical
namespace CubicTenVariables.CubicGoodHyperplaneUniformity
open MvPolynomial Literature HessianTheorem11.PolynomialRestriction
open CharacteristicZeroCertificateUniformity CubicNonconicalHyperplaneCertificate

/-- A nonconical specialization gives a nonzero actual Hessian minor in
R. It remains nonzero at any injective coefficient embedding. -/
theorem nonconical_of_specialization
    {R Ω K : Type*} [CommRing R] [Field Ω] [Field K] {n : ℕ}
    (κ : R →+* Ω) (hκ : Function.Injective κ)
    (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous 3)
    (h2Ω : (2 : Ω) ≠ 0) (h3Ω : (3 : Ω) ≠ 0)
    (τ : R →+* K) (h2K : (2 : K) ≠ 0) (h3K : (3 : K) ≠ 0)
    (hNC : GeometricallyNonconicalCubic (map τ F)) :
    GeometricallyNonconicalCubic (map κ F) := by
  obtain ⟨rows, cols, hminor, hgood⟩ :=
    CubicNonconicalMinorCertificate.exists_minor_certificate F hF τ h2K h3K hNC
  apply hgood Ω κ h2Ω h3Ω
  intro hz
  have hm : CubicNonconicalMinorCertificate.minor F rows cols = 0 :=
    hκ (by simpa only [map_zero] using hz)
  exact hminor (by rw [hm, map_zero])

variable {R : Type} [CommRing R] {r : ℕ}

private def Eligible (F : MvPolynomial (Fin (r+4)) R)
    (K : Type) [Field K] (ρ : R →+* K) : Prop :=
  GeometricallyIntegralForm (map ρ F) ∧ GeometricallyNonconicalCubic (map ρ F) ∧
    (2 : K) ≠ 0 ∧ (3 : K) ≠ 0

/-- All conclusions concern the same literal kernel frame of one normal. -/
def GoodSection (F : MvPolynomial (Fin (r+4)) R)
    (K : Type) [Field K] (ρ : R →+* K) (u : Fin (r+4) → K) : Prop :=
  Function.Injective (frame u).mulVec ∧
    LinearMap.range (frame u).mulVecLin =
      LinearMap.ker (GenericHyperplaneFrameKernel.normal u) ∧
    (restrict (frame u) (map ρ F)).IsHomogeneous 3 ∧
    (restrict (frame u) (map ρ F)).totalDegree = 3 ∧
    GeometricallyIntegralForm (restrict (frame u) (map ρ F)) ∧
    GeometricallyNonconicalCubic (restrict (frame u) (map ρ F))

/-- One N and D suffice for every eligible fiber of a fixed Noetherian
coefficient family. Characteristics 2 and 3 are absorbed into N. The
certificate may depend on the fiber, while N and D do not. -/
theorem exists_uniform_certificate [IsNoetherianRing R]
    (r : ℕ) (F : MvPolynomial (Fin (r+4)) R) (hF : F.IsHomogeneous 3) :
    ∃ N : ℕ, 0 < N ∧ ∃ D : ℕ,
      ∀ (K : Type) [Field K] (ρ : R →+* K), (N : K) ≠ 0 →
        GeometricallyIntegralForm (map ρ F) → GeometricallyNonconicalCubic (map ρ F) →
        ∃ Δ : MvPolynomial (Fin (r+4)) K, Δ ≠ 0 ∧ Δ.totalDegree ≤ D ∧
          ∀ u : Fin (r+4) → K, eval u Δ ≠ 0 →
            Function.Injective (frame u).mulVec ∧
            LinearMap.range (frame u).mulVecLin =
              LinearMap.ker (GenericHyperplaneFrameKernel.normal u) ∧
            (restrict (frame u) (map ρ F)).IsHomogeneous 3 ∧
            (restrict (frame u) (map ρ F)).totalDegree = 3 ∧
            GeometricallyIntegralForm (restrict (frame u) (map ρ F)) ∧
            GeometricallyNonconicalCubic (restrict (frame u) (map ρ F)) := by
  classical
  have hopen : ∀ P : Ideal R, P.IsPrime →
      (∀ a : ℕ, 0 < a → (a : R) ∉ P) →
      ∃ s : R, s ∉ P ∧ ∃ D : ℕ,
        ∀ (K : Type) [Field K] (ρ : R →+* K),
          P ≤ RingHom.ker ρ → ρ s ≠ 0 → Eligible F K ρ →
            HasCertificate (GoodSection F) D ρ := by
    intro P hP hzero
    letI : P.IsPrime := hP
    let B := R ⧸ P
    let q : R →+* B := Ideal.Quotient.mk P
    letI : CharZero B := charZero_of_inj_zero (fun a ha => by
      by_contra hne
      have hm : (a : R) ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp (by
        simpa only [map_natCast] using ha)
      exact hzero a (Nat.pos_of_ne_zero hne) hm)
    let k := FractionRing B
    let Ω := AlgebraicClosure k
    let κ : B →+* Ω := (algebraMap k Ω).comp (algebraMap B k)
    have hκ : Function.Injective κ :=
      (algebraMap k Ω).injective.comp (IsFractionRing.injective B k)
    by_cases hgeneric : Irreducible (map κ (map q F)) ∧
        GeometricallyNonconicalCubic (map κ (map q F))
    · obtain ⟨ΔI, hΔIκ, hIGood⟩ :=
        CubicIntegralHyperplaneNormalCertificate.exists_nonzero_certificate
          r κ (map q F) (hF.map q) hgeneric.1
      obtain ⟨rows, cols, hΔNκ, hNGood⟩ :=
        CubicNonconicalHyperplaneCertificate.exists_nonzero_certificate
          κ (map q F) (hF.map q) hgeneric.2
      let ΔN := X 0 * CubicNonconicalMinorCertificate.minor
        (family (map q F)) rows cols
      let Δ := ΔI * ΔN
      have hΔ : Δ ≠ 0 := by
        intro hz
        have hh : map κ Δ ≠ 0 := by
          simpa only [Δ, ΔN, map_mul] using mul_ne_zero hΔIκ hΔNκ
        exact hh (by rw [hz, map_zero])
      obtain ⟨a, ha⟩ := exists_coeff_ne_zero hΔ
      obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (coeff a Δ)
      refine ⟨s, ?_, Δ.totalDegree, ?_⟩
      · intro hsP
        exact ha (hs.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hsP))
      · intro K _ ρ hPρ hsρ he
        let τ : B →+* K := Ideal.Quotient.lift P ρ
          (fun _ hx => RingHom.mem_ker.mp (hPρ hx))
        have hcomp : τ.comp q = ρ := Ideal.Quotient.lift_comp_mk P ρ _
        have hcoeff : τ (coeff a Δ) ≠ 0 := by
          rw [← hs]
          exact hsρ
        have hmap : map τ Δ ≠ 0 := by
          intro hz
          exact hcoeff (by simpa only [coeff_map, coeff_zero] using congrArg (coeff a) hz)
        refine ⟨map τ Δ, hmap, Finset.sup_mono (support_map_subset τ Δ), ?_⟩
        intro u hu
        have heval : eval₂Hom τ u ΔI ≠ 0 ∧ eval₂Hom τ u ΔN ≠ 0 := by
          apply mul_ne_zero_iff.mp
          simpa only [eval_map, Δ, map_mul] using hu
        obtain ⟨hinj, hrange, hhom, hdeg, hgi⟩ := hIGood K τ u heval.1
        have hnc := (hNGood K τ u he.2.2.1 he.2.2.2 heval.2).2.2
        simpa only [GoodSection, map_map, hcomp] using
          And.intro hinj (And.intro hrange (And.intro hhom (And.intro hdeg (And.intro hgi hnc))))
    · refine ⟨1, hP.one_notMem, 0, ?_⟩
      intro K _ ρ hPρ _hs he
      let τ : B →+* K := Ideal.Quotient.lift P ρ
        (fun _ hx => RingHom.mem_ker.mp (hPρ hx))
      have hcomp : τ.comp q = ρ := Ideal.Quotient.lift_comp_mk P ρ _
      have hI : GeometricallyIntegralForm (map τ (map q F)) := by
        simpa only [map_map, hcomp] using he.1
      have hNC : GeometricallyNonconicalCubic (map τ (map q F)) := by
        simpa only [map_map, hcomp] using he.2.1
      exact (hgeneric ⟨
        CubicSurfaceFrameCertificate.irreducible_of_geometricallyIntegral_specialization
          κ hκ (map q F) (hF.map q) τ hI,
        nonconical_of_specialization κ hκ (map q F) (hF.map q)
          (by norm_num) (by norm_num) τ he.2.2.1 he.2.2.2 hNC⟩).elim
  obtain ⟨N, hN, D, hD⟩ :=
    exists_uniform_degree_away_from_integer (Eligible F) (GoodSection F) hopen
  refine ⟨6 * N, Nat.mul_pos (by decide) hN, D, ?_⟩
  intro K _ ρ hNρ hGI hNC
  have hprod : (6 : K) * (N : K) ≠ 0 := by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hNρ
  have h6 : (6 : K) ≠ 0 := (mul_ne_zero_iff.mp hprod).1
  have hN' : (N : K) ≠ 0 := (mul_ne_zero_iff.mp hprod).2
  have h23 : (2 : K) * (3 : K) ≠ 0 := by
    rw [show (2 : K) * (3 : K) = 6 by norm_num]
    exact h6
  exact hD K ρ hN' ⟨hGI, hNC, (mul_ne_zero_iff.mp h23).1, (mul_ne_zero_iff.mp h23).2⟩

private abbrev CubicCoefficients (r : ℕ) := CubicFactorCharts.Monomial (r+4) 3

private def universalCubic (r : ℕ) :
    MvPolynomial (Fin (r+4)) (MvPolynomial (CubicCoefficients r) ℤ) :=
  homogeneousComponent 3 (CubicFactorCharts.polynomial X)

private theorem universalCubic_homogeneous (r : ℕ) : (universalCubic r).IsHomogeneous 3 :=
  homogeneousComponent_isHomogeneous _ _

private theorem specialize_universalCubic
    {K : Type} [Field K] (F : MvPolynomial (Fin (r+4)) K) (hF : F.IsHomogeneous 3) :
    map (eval₂Hom (Int.castRingHom K) (fun m : CubicCoefficients r => coeff m.val F))
      (universalCubic r) = F := by
  classical
  ext a
  rw [coeff_map]
  change eval₂Hom (Int.castRingHom K) (fun m : CubicCoefficients r => coeff m.val F)
    (coeff a (homogeneousComponent 3 (CubicFactorCharts.polynomial X))) = coeff a F
  rw [coeff_homogeneousComponent]
  by_cases ha : a.degree = 3
  · rw [if_pos ha]
    have hac : a.degree ≤ 3 := ha.le
    rw [CubicFactorCharts.coeff_polynomial _ ⟨a, hac⟩, eval₂Hom_X']
  · rw [if_neg ha, map_zero, hF.coeff_eq_zero ha]

/-- Absolute bounds for all cubic forms in r+4 variables: one excluded
positive integer and one normal-certificate degree bound precede every
field and every polynomial. There are no supplied open-set certificates. -/
theorem exists_absolute_certificate (r : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∃ D : ℕ,
      ∀ (K : Type) [Field K] (F : MvPolynomial (Fin (r+4)) K),
        (N : K) ≠ 0 → F.IsHomogeneous 3 → GeometricallyIntegralForm F →
        GeometricallyNonconicalCubic F →
        ∃ Δ : MvPolynomial (Fin (r+4)) K, Δ ≠ 0 ∧ Δ.totalDegree ≤ D ∧
          ∀ u : Fin (r+4) → K, eval u Δ ≠ 0 →
            Function.Injective (frame u).mulVec ∧
            LinearMap.range (frame u).mulVecLin =
              LinearMap.ker (GenericHyperplaneFrameKernel.normal u) ∧
            (restrict (frame u) F).IsHomogeneous 3 ∧
            (restrict (frame u) F).totalDegree = 3 ∧
            GeometricallyIntegralForm (restrict (frame u) F) ∧
            GeometricallyNonconicalCubic (restrict (frame u) F) := by
  obtain ⟨N, hN, D, hcert⟩ :=
    exists_uniform_certificate r (universalCubic r) (universalCubic_homogeneous r)
  refine ⟨N, hN, D, ?_⟩
  intro K _ F hNK hF hGI hNC
  let ρ := eval₂Hom (Int.castRingHom K) (fun m : CubicCoefficients r => coeff m.val F)
  have hs : map ρ (universalCubic r) = F := specialize_universalCubic F hF
  simpa only [hs] using hcert K ρ hNK (by rwa [hs]) (by rwa [hs])

end CubicTenVariables.CubicGoodHyperplaneUniformity

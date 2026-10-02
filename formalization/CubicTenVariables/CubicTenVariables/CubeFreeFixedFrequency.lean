import CubicTenVariables.ConductorFixedFrequency
import CubicTenVariables.CubeFreeModulusDecomposition

/-! The fixed-frequency conductor-band estimate for the actual cube-free
modulus sum. The canonical decomposition q = d(q)c(q)² is injective on the
positive moduli, so the finite pair estimate counts each modulus exactly
once. The final wrapper constructs the same P/Q and numerical-depth data
from the listed geometric hypotheses and proved prime-field count interface. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CubeFreeFixedFrequency
open MvPolynomial HessianTheorem11 TranslatedDepthSeven
open NumericalPrimeDepth ProjectiveMicrolocalData
open SquarefullModulusDecomposition CubeFreeModulusDecomposition
open ConductorFixedFrequency
open scoped BigOperators

variable {F : MvPolynomial (Fin 10) ℤ} {C : ℝ}

/-- The literal conductor at a modulus, using its canonical squarefree
and square parts. The estimates below restrict to cube-free moduli. -/
def conductor (h : CoarseBounds F C) (q : ℕ) (v : Fin 10 → ℤ) : ℝ :=
  NumericalConductor.K h (d q) (c q) v

theorem one_le_conductor (h : CoarseBounds F C) (q : ℕ) (v : Fin 10 → ℤ) :
    1 ≤ conductor h q v := NumericalConductor.one_le_K h (d q) (c q) v

/-- The source's half-open modulus and conductor bands, with no radical
cutoff and no coprimality condition against an auxiliary progression. -/
def window (h : CoarseBounds F C) (v : Fin 10 → ℤ) (D K0 : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (⌊2*D⌋₊+1)).filter (fun q =>
    CubeFree q ∧ D ≤ (q : ℝ) ∧ (q : ℝ) < 2*D ∧
      K0 ≤ conductor h q v ∧ conductor h q v < 2*K0)

theorem mem_window (h : CoarseBounds F C) (v : Fin 10 → ℤ) (D K0 : ℝ) (q : ℕ) :
    q ∈ window h v D K0 ↔
      CubeFree q ∧ D ≤ (q : ℝ) ∧ (q : ℝ) < 2*D ∧
        K0 ≤ conductor h q v ∧ conductor h q v < 2*K0 := by
  classical
  simp only [window, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · exact And.right
  · intro hq
    exact ⟨Nat.le_floor hq.2.2.1.le,hq⟩

/-- One constant precedes the integer frequency and both real band
parameters. This is the actual source modulus sum, not a sum over chosen
decomposition witnesses. -/
theorem exists_band_bound {t : ℕ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
    {T : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)}
    {N : ℕ} {d₀ : ℕ} {h : CoarseBounds F C}
    (hF : F.IsHomogeneous 3) (hc : MicrolocalConductorDepth.Conclusion F f T N C d₀ h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ v : Fin 10 → ℤ, GoodFrequency F f T v →
      ∀ D K0 : ℝ, 1 ≤ D → 1 ≤ K0 →
        (∑ q ∈ window h v D K0, ‖completeCubicSum F q v‖) ≤
          M*(D*frequencyHeight v)^ε*D^((13 : ℝ)/2)*K0 := by
  classical
  obtain ⟨M,hM,hbound⟩ := ConductorFixedFrequency.exists_band_bound hF hc ε hε
  refine ⟨M,hM,?_⟩
  intro v hv D K0 hD hK
  let Q : Finset (ℕ × ℕ) := (window h v D K0).image (fun q => (d q,c q))
  have hQ : ∀ x ∈ Q,
      1 ≤ x.1 ∧ 1 ≤ x.2 ∧ Squarefree x.1 ∧ Squarefree x.2 ∧
        x.1.Coprime x.2 ∧ (x.1 : ℝ)*(x.2 : ℝ)^2 ≤ 2*D ∧
        NumericalConductor.K h x.1 x.2 v < 2*K0 := by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
    have hw := (mem_window h v D K0 q).mp hq
    refine ⟨d_pos q,c_pos q,d_squarefree q,c_squarefree q hw.1,
      coprime_d_c q hw.1,?_,hw.2.2.2.2⟩
    have he : (q : ℝ) = (d q : ℝ)*(c q : ℝ)^2 := by
      exact_mod_cast eq_d_mul_c_sq q hw.1
    exact he ▸ hw.2.2.1.le
  have hinj : Set.InjOn (fun q => (d q,c q)) (↑(window h v D K0) : Set ℕ) := by
    intro q hq r hr he
    exact CubeFreeModulusDecomposition.parameters_injOn
      (Nat.pos_of_ne_zero ((mem_window h v D K0 q).mp hq).1.1)
      (Nat.pos_of_ne_zero ((mem_window h v D K0 r).mp hr).1.1) he
  calc
    _ = ∑ q ∈ window h v D K0, ‖completeCubicSum F (d q*(c q)^2) v‖ := by
      apply Finset.sum_congr rfl
      intro q hq
      exact congrArg (fun n => ‖completeCubicSum F n v‖)
        (eq_d_mul_c_sq q ((mem_window h v D K0 q).mp hq).1)
    _ = ∑ x ∈ Q, ‖completeCubicSum F (x.1*x.2^2) v‖ := by
      exact (Finset.sum_image (f := fun x : ℕ × ℕ => ‖completeCubicSum F (x.1*x.2^2) v‖) hinj).symm
    _ ≤ M*(D*frequencyHeight v)^ε*D^((13 : ℝ)/2)*K0 :=
      hbound v hv D K0 hD hK Q hQ

/-- The same actual incidence, P/Q partitions, and least-depth constant
are constructed once, before epsilon and all summation parameters. There
is no supplied partition, divisibility certificate, or arithmetic estimate
among the final application inputs. -/
theorem exists_data
    (microlocal : Literature.ProjectiveMicrolocalCertificate)
    (degreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (weil : Literature.AffinePlaneCubicWeil)
    (dichotomy : Literature.ProperHyperplaneWeightDichotomy)
    (salberger : Published.Salberger2023Theorem04)
    (integrality : CubicPrincipalOpenUniform.Uniform)
    (cubicWeil : Literature.SmoothCubicWeil)
    (ampl : Literature.CubicSurfacePointCountAmplification)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    (F : MvPolynomial (Fin 10) ℤ) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ (t : ℕ) (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10) (N B : ℕ)
      (T : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)),
      MicrolocalRationalPartition.Conclusion F f N B T ∧
      MicrolocalSquareRationalPartition.Conclusion F f N B ∧
      ∃ (C : ℝ) (d₀ : ℕ) (h : CoarseBounds F C),
        MicrolocalConductorDepth.Conclusion F f T N C d₀ h ∧
        ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 1 ≤ M ∧
          ∀ v : Fin 10 → ℤ, GoodFrequency F f T v →
            ∀ D K0 : ℝ, 1 ≤ D → 1 ≤ K0 →
              (∑ q ∈ window h v D K0, ‖completeCubicSum F q v‖) ≤
                M*(D*frequencyHeight v)^ε*D^((13 : ℝ)/2)*K0 := by
  obtain ⟨t,f,N,B,T,hP,hQ,C,d₀,h,hc⟩ := MicrolocalConductorDepth.exists_data
    microlocal degreeSpan smooth spread weil dichotomy salberger
    integrality cubicWeil ampl pointcount F hhom hAn
  exact ⟨t,f,N,B,T,hP,hQ,C,d₀,h,hc,fun ε hε => exists_band_bound hhom hc ε hε⟩

end CubicTenVariables.CubeFreeFixedFrequency

import CubicTenVariables.ConductorPositiveMean
import CubicTenVariables.CubeFreeFixedFrequency
import CubicTenVariables.ConeComponentProgressionCount

/-! The literal cube-free positive mean over the source progression box,
radical cutoff, and half-open modulus and conductor bands. Canonical
decomposition reindexes each modulus exactly once. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.CubeFreePositiveMean
open MvPolynomial HessianTheorem11 TranslatedDepthSeven
open NumericalPrimeDepth ProjectiveMicrolocalData ConductorFixedFrequency
open SquarefullModulusDecomposition CubeFreeModulusDecomposition
open scoped BigOperators Classical

variable {F : MvPolynomial (Fin 10) ℤ} {C : ℝ}

/-- Actual integer frequencies in P0∩Q0, the real-centered box, and the
specified progression. -/
def frequencies {t : ℕ}
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1))
    (u : Fin 10 → ℝ) (L : ℝ) (m : ℕ) (v₀ : Fin 10 → ℤ) : Finset (Fin 10 → ℤ) :=
  ConeComponentProgressionCount.points
    (MicrolocalPromotedPartition.part f
      (MicrolocalPartitionCounts.promotionFamily (fun i => (tables i).open)) 0 ∩
      MicrolocalSquarePartition.part f 0) u L m v₀

theorem mem_frequencies {t : ℕ}
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1))
    (u : Fin 10 → ℝ) (L : ℝ) (m : ℕ) (v₀ v : Fin 10 → ℤ) :
    v ∈ frequencies f tables u L m v₀ ↔
      (∀ i, |(v i : ℝ)-u i| ≤ L) ∧
      (∀ i, (m : ℤ) ∣ v i-v₀ i) ∧ GoodFrequency F f tables v := by
  simp only [frequencies,ConeComponentProgressionCount.mem_points,Set.mem_inter_iff,
    GoodFrequency]

/-- The source modulus/conductor bands with precisely the additional
coprimality and R22 cutoff required by the positive mean. -/
def moduli (h : CoarseBounds F C) (v : Fin 10 → ℤ) (D K0 : ℝ) (m : ℕ)
    (L : ℝ) : Finset ℕ :=
  (CubeFreeFixedFrequency.window h v D K0).filter fun q =>
    q.Coprime m ∧
      (NumericalConductorRadical.R22 h (d q) (c q) v : ℝ) ≤ 1+L/(m : ℝ)

theorem mem_moduli (h : CoarseBounds F C) (v : Fin 10 → ℤ)
    (D K0 : ℝ) (m : ℕ) (L : ℝ) (q : ℕ) :
    q ∈ moduli h v D K0 m L ↔
      (CubeFree q ∧ D ≤ (q : ℝ) ∧ (q : ℝ) < 2*D ∧
        K0 ≤ CubeFreeFixedFrequency.conductor h q v ∧
        CubeFreeFixedFrequency.conductor h q v < 2*K0) ∧
      q.Coprime m ∧
        (NumericalConductorRadical.R22 h (d q) (c q) v : ℝ) ≤ 1+L/(m : ℝ) := by
  simp only [moduli,Finset.mem_filter,CubeFreeFixedFrequency.mem_window]

/-- Exact finite rearrangement into the manuscript's modulus-first order. -/
theorem sum_eq_modulus_outer {t : ℕ}
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1))
    (h : CoarseBounds F C) (D K0 : ℝ) (m : ℕ) (u : Fin 10 → ℝ)
    (L : ℝ) (v₀ : Fin 10 → ℤ) :
    (∑ v ∈ frequencies f tables u L m v₀,
      ∑ q ∈ moduli h v D K0 m L, ‖completeCubicSum F q v‖) =
    ∑ q ∈ Finset.range (⌊2*D⌋₊+1),
      ∑ v ∈ (frequencies f tables u L m v₀).filter
        (fun v => q ∈ moduli h v D K0 m L), ‖completeCubicSum F q v‖ := by
  have hsub (v : Fin 10 → ℤ) :
      moduli h v D K0 m L ⊆ Finset.range (⌊2*D⌋₊+1) := by
    intro q hq
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
  have hsum (v : Fin 10 → ℤ) :
      (∑ q ∈ moduli h v D K0 m L, ‖completeCubicSum F q v‖) =
      ∑ q ∈ Finset.range (⌊2*D⌋₊+1),
        if q ∈ moduli h v D K0 m L then ‖completeCubicSum F q v‖ else 0 := by
    calc
      _ = ∑ q ∈ moduli h v D K0 m L,
          if q ∈ moduli h v D K0 m L then ‖completeCubicSum F q v‖ else 0 := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [if_pos hq]
      _ = _ := Finset.sum_subset (hsub v) (fun q _ hq => if_neg hq)
  simp_rw [hsum]
  rw [Finset.sum_comm]
  simp only [Finset.sum_filter]

/-- The actual nested sum of complete cubic sums, with one constant before
all modulus bands, frequency boxes, and progressions. -/
theorem exists_bound (lit : FixedFamilyPrimeFieldPointCount.Uniform)
    {t N B d₀ : ℕ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
    {tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)}
    {h : CoarseBounds F C}
    (hgeo : Geometry F f) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hData : TenMicrolocalIncidence.Conclusion F f N B) (hN : 1 ≤ N)
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C d₀ h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (D K0 : ℝ) (m : ℕ) (u : Fin 10 → ℝ)
      (L : ℝ) (v₀ : Fin 10 → ℤ), 1 ≤ D → 1 ≤ K0 → 0 < m → 0 ≤ L →
      (∑ v ∈ frequencies f tables u L m v₀,
        ∑ q ∈ moduli h v D K0 m L, ‖completeCubicSum F q v‖) ≤
          M*(D*(2+‖u‖+L+(m : ℝ)))^ε*(1+L/(m : ℝ))^(10+ε)*
            D^((13 : ℝ)/2)*K0^(-(1 : ℝ)/2) := by
  obtain ⟨M,hM,hbound⟩ :=
    ConductorPositiveMean.exists_bound lit hgeo hhom hAn hData hN hc ε hε
  refine ⟨M,hM,?_⟩
  intro D K0 m u L v₀ hD hK hm hL
  let E := (frequencies f tables u L m v₀).sigma (fun v => moduli h v D K0 m L)
  let encode : (Σ _v : Fin 10 → ℤ, ℕ) → ConductorMeanDomain.Sample :=
    fun x => ((d x.2,c x.2),x.1)
  let Q := E.image encode
  have hwindow (x) (hx : x ∈ E) :
      ConductorMeanDomain.InWindow h f tables D K0 m u L v₀ (encode x) := by
    have hmem := Finset.mem_sigma.mp hx
    have hv := (mem_frequencies f tables u L m v₀ x.1).mp hmem.1
    have hq := (mem_moduli h x.1 D K0 m L x.2).mp hmem.2
    have hsize : (x.2 : ℝ) = (d x.2 : ℝ)*(c x.2 : ℝ)^2 := by
      exact_mod_cast eq_d_mul_c_sq x.2 hq.1.1
    refine ⟨d_pos x.2,c_pos x.2,d_squarefree x.2,c_squarefree x.2 hq.1.1,
      coprime_d_c x.2 hq.1.1,?_,hv.2.2,hv.1,hv.2.1,?_,hq.2.2,hq.1.2.2.2.1⟩
    · exact hsize ▸ hq.1.2.2.1.le
    · apply Nat.Coprime.of_dvd_right _ hq.2.1.symm
      refine ⟨c x.2,?_⟩
      change x.2 = (d x.2*c x.2)*c x.2
      calc
        x.2 = d x.2*(c x.2)^2 := eq_d_mul_c_sq x.2 hq.1.1
        _ = _ := by ring
  have hQ : ∀ x ∈ Q, ConductorMeanDomain.InWindow h f tables D K0 m u L v₀ x := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hwindow y hy
  have hinj : Set.InjOn encode (E : Set (Σ _v : Fin 10 → ℤ, ℕ)) := by
    intro x hx y hy he
    have hv : x.1 = y.1 := congrArg Prod.snd he
    have hp : (d x.2,c x.2) = (d y.2,c y.2) := congrArg Prod.fst he
    have hxq := (mem_moduli h x.1 D K0 m L x.2).mp (Finset.mem_sigma.mp hx).2
    have hyq := (mem_moduli h y.1 D K0 m L y.2).mp (Finset.mem_sigma.mp hy).2
    have hq : x.2 = y.2 := CubeFreeModulusDecomposition.parameters_injOn
      (Nat.pos_of_ne_zero hxq.1.1.1) (Nat.pos_of_ne_zero hyq.1.1.1) hp
    cases x
    cases y
    cases hv
    cases hq
    rfl
  calc
    _ = ∑ x ∈ E, ‖completeCubicSum F x.2 x.1‖ := by
      rw [Finset.sum_sigma]
    _ = ∑ x ∈ E, ‖completeCubicSum F ((d x.2)*(c x.2)^2) x.1‖ := by
      apply Finset.sum_congr rfl
      intro x hx
      have hq := (mem_moduli h x.1 D K0 m L x.2).mp (Finset.mem_sigma.mp hx).2
      rw [← eq_d_mul_c_sq x.2 hq.1.1]
    _ = ∑ x ∈ Q, ‖completeCubicSum F (x.1.1*x.1.2^2) x.2‖ :=
      (Finset.sum_image (f := fun x : ConductorMeanDomain.Sample =>
        ‖completeCubicSum F (x.1.1*x.1.2^2) x.2‖) hinj).symm
    _ ≤ _ := hbound D K0 m u L v₀ hD hK hm hL Q hQ

/-- The same proved estimate with the modulus sum outermost. -/
theorem exists_modulus_outer_bound (lit : FixedFamilyPrimeFieldPointCount.Uniform)
    {t N B d₀ : ℕ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
    {tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)}
    {h : CoarseBounds F C}
    (hgeo : Geometry F f) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hData : TenMicrolocalIncidence.Conclusion F f N B) (hN : 1 ≤ N)
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C d₀ h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (D K0 : ℝ) (m : ℕ) (u : Fin 10 → ℝ)
      (L : ℝ) (v₀ : Fin 10 → ℤ), 1 ≤ D → 1 ≤ K0 → 0 < m → 0 ≤ L →
      (∑ q ∈ Finset.range (⌊2*D⌋₊+1),
        ∑ v ∈ (frequencies f tables u L m v₀).filter
          (fun v => q ∈ moduli h v D K0 m L), ‖completeCubicSum F q v‖) ≤
          M*(D*(2+‖u‖+L+(m : ℝ)))^ε*(1+L/(m : ℝ))^(10+ε)*
            D^((13 : ℝ)/2)*K0^(-(1 : ℝ)/2) := by
  obtain ⟨M,hM,hbound⟩ := exists_bound lit hgeo hhom hAn hData hN hc ε hε
  refine ⟨M,hM,?_⟩
  intro D K0 m u L v₀ hD hK hm hL
  rw [← sum_eq_modulus_outer]
  exact hbound D K0 m u L v₀ hD hK hm hL

/-- The same actual incidence, P/Q partitions, and least-depth constant
are chosen before epsilon and every summation parameter. -/
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
      (tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)),
      MicrolocalRationalPartition.Conclusion F f N B tables ∧
      MicrolocalSquareRationalPartition.Conclusion F f N B ∧
      ∃ (C : ℝ) (d₀ : ℕ) (h : CoarseBounds F C),
        MicrolocalConductorDepth.Conclusion F f tables N C d₀ h ∧
        (∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 1 ≤ M ∧
          ∀ (D K0 : ℝ) (m : ℕ) (u : Fin 10 → ℝ) (L : ℝ) (v₀ : Fin 10 → ℤ),
            1 ≤ D → 1 ≤ K0 → 0 < m → 0 ≤ L →
            (∑ q ∈ Finset.range (⌊2*D⌋₊+1),
              ∑ v ∈ (frequencies f tables u L m v₀).filter
                (fun v => q ∈ moduli h v D K0 m L), ‖completeCubicSum F q v‖) ≤
                M*(D*(2+‖u‖+L+(m : ℝ)))^ε*(1+L/(m : ℝ))^(10+ε)*
                  D^((13 : ℝ)/2)*K0^(-(1 : ℝ)/2)) ∧
        ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 1 ≤ M ∧
          ∀ v : Fin 10 → ℤ, GoodFrequency F f tables v →
            ∀ D K0 : ℝ, 1 ≤ D → 1 ≤ K0 →
              (∑ q ∈ CubeFreeFixedFrequency.window h v D K0, ‖completeCubicSum F q v‖) ≤
                M*(D*frequencyHeight v)^ε*D^((13 : ℝ)/2)*K0 := by
  obtain ⟨t,f,N,B,tables,hP,hQ,C,d₀,h,hc⟩ := MicrolocalConductorDepth.exists_data
    microlocal degreeSpan smooth spread weil dichotomy salberger
    integrality cubicWeil ampl pointcount F hhom hAn
  exact ⟨t,f,N,B,tables,hP,hQ,C,d₀,h,hc,
    fun ε hε => exists_modulus_outer_bound pointcount hP.geometry hhom hAn
      hP.incidence hP.modulus_pos hc ε hε,
    fun ε hε => CubeFreeFixedFrequency.exists_band_bound hhom hc ε hε⟩

end CubicTenVariables.CubeFreePositiveMean

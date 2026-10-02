import CubicTenVariables.ConductorPositiveMoment
import CubicTenVariables.CubeFreePositiveMean
import CubicTenVariables.CubeFreeNonzeroAverage

/-! The two literal cube-free conductor moments. The positive half-moment
retains exactly the progression, generic-frequency and high-radical cutoff;
the inverse moment has no progression, conductor-band or radical cutoff.
Both are constructed for the same incidence and numerical conductor data. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.CubeFreeConductorMoments
open MvPolynomial HessianTheorem11 TranslatedDepthSeven
open NumericalPrimeDepth ProjectiveMicrolocalData ConductorFixedFrequency
open SquarefullModulusDecomposition CubeFreeModulusDecomposition
open CubeFreePositiveMean (frequencies mem_frequencies)
open CubeFreeFixedFrequency (conductor)
open scoped BigOperators Classical

variable {F : MvPolynomial (Fin 10) ℤ} {C : ℝ}

/-- All cube-free moduli in the half-open D-window satisfying the literal
coprimality and high-radical cutoff. No conductor band is imposed. -/
def positiveModuli (h : CoarseBounds F C) (v : Fin 10 → ℤ) (D : ℝ) (m : ℕ)
    (L : ℝ) : Finset ℕ :=
  (CubeFreeNonzeroAverage.window D).filter fun q =>
    q.Coprime m ∧
      (NumericalConductorRadical.R22 h (d q) (c q) v : ℝ) ≤ 1+L/(m : ℝ)

theorem mem_positiveModuli (h : CoarseBounds F C) (v : Fin 10 → ℤ)
    (D : ℝ) (m : ℕ) (L : ℝ) (q : ℕ) :
    q ∈ positiveModuli h v D m L ↔
      (CubeFree q ∧ D ≤ (q : ℝ) ∧ (q : ℝ) < 2*D) ∧
      q.Coprime m ∧
        (NumericalConductorRadical.R22 h (d q) (c q) v : ℝ) ≤ 1+L/(m : ℝ) := by
  simp only [positiveModuli,Finset.mem_filter,CubeFreeNonzeroAverage.mem_window]

/-- Exact finite rearrangement into the manuscript's modulus-first order. -/
theorem positive_sum_eq_modulus_outer {t : ℕ}
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1))
    (h : CoarseBounds F C) (D : ℝ) (m : ℕ) (u : Fin 10 → ℝ)
    (L : ℝ) (v₀ : Fin 10 → ℤ) :
    (∑ v ∈ frequencies f tables u L m v₀,
      ∑ q ∈ positiveModuli h v D m L, ‖completeCubicSum F q v‖*(conductor h q v)^((1 : ℝ)/2)) =
    ∑ q ∈ Finset.range (⌊2*D⌋₊+1),
      ∑ v ∈ (frequencies f tables u L m v₀).filter
        (fun v => q ∈ positiveModuli h v D m L), ‖completeCubicSum F q v‖*(conductor h q v)^((1 : ℝ)/2) := by
  have hsub (v : Fin 10 → ℤ) :
      positiveModuli h v D m L ⊆ Finset.range (⌊2*D⌋₊+1) := by
    intro q hq
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
  have hsum (v : Fin 10 → ℤ) :
      (∑ q ∈ positiveModuli h v D m L, ‖completeCubicSum F q v‖*(conductor h q v)^((1 : ℝ)/2)) =
      ∑ q ∈ Finset.range (⌊2*D⌋₊+1),
        if q ∈ positiveModuli h v D m L then ‖completeCubicSum F q v‖*(conductor h q v)^((1 : ℝ)/2) else 0 := by
    calc
      _ = ∑ q ∈ positiveModuli h v D m L,
          if q ∈ positiveModuli h v D m L then ‖completeCubicSum F q v‖*(conductor h q v)^((1 : ℝ)/2) else 0 := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [if_pos hq]
      _ = _ := Finset.sum_subset (hsub v) (fun q _ hq => if_neg hq)
  simp_rw [hsum]
  rw [Finset.sum_comm]
  simp only [Finset.sum_filter]

/-- The actual half-moment with one constant before all modulus windows,
frequency boxes, and progressions. -/
theorem exists_positive_bound (lit : FixedFamilyPrimeFieldPointCount.Uniform)
    {t N B d₀ : ℕ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
    {tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)}
    {h : CoarseBounds F C}
    (hgeo : Geometry F f) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hData : TenMicrolocalIncidence.Conclusion F f N B) (hN : 1 ≤ N)
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C d₀ h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (D : ℝ) (m : ℕ) (u : Fin 10 → ℝ)
      (L : ℝ) (v₀ : Fin 10 → ℤ), 1 ≤ D → 0 < m → 0 ≤ L →
      (∑ v ∈ frequencies f tables u L m v₀,
        ∑ q ∈ positiveModuli h v D m L, ‖completeCubicSum F q v‖*(conductor h q v)^((1 : ℝ)/2)) ≤
          M*(D*(2+‖u‖+L+(m : ℝ)))^ε*(1+L/(m : ℝ))^10*D^((13 : ℝ)/2) := by
  obtain ⟨M,hM,hbound⟩ :=
    ConductorPositiveMoment.exists_bound lit hgeo hhom hAn hData hN hc ε hε
  refine ⟨M,hM,?_⟩
  intro D m u L v₀ hD hm hL
  let E := (frequencies f tables u L m v₀).sigma (fun v => positiveModuli h v D m L)
  let encode : (Σ _v : Fin 10 → ℤ, ℕ) → ConductorMeanDomain.Sample :=
    fun x => ((d x.2,c x.2),x.1)
  let Q := E.image encode
  have hwindow (x) (hx : x ∈ E) :
      ConductorMeanDomain.InWindow h f tables D 1 m u L v₀ (encode x) := by
    have hmem := Finset.mem_sigma.mp hx
    have hv := (mem_frequencies f tables u L m v₀ x.1).mp hmem.1
    have hq := (mem_positiveModuli h x.1 D m L x.2).mp hmem.2
    have hsize : (x.2 : ℝ) = (d x.2 : ℝ)*(c x.2 : ℝ)^2 := by
      exact_mod_cast eq_d_mul_c_sq x.2 hq.1.1
    refine ⟨d_pos x.2,c_pos x.2,d_squarefree x.2,c_squarefree x.2 hq.1.1,
      coprime_d_c x.2 hq.1.1,?_,hv.2.2,hv.1,hv.2.1,?_,hq.2.2,NumericalConductor.one_le_K h (d x.2) (c x.2) x.1⟩
    · exact hsize ▸ hq.1.2.2.le
    · apply Nat.Coprime.of_dvd_right _ hq.2.1.symm
      refine ⟨c x.2,?_⟩
      change x.2 = (d x.2*c x.2)*c x.2
      calc
        x.2 = d x.2*(c x.2)^2 := eq_d_mul_c_sq x.2 hq.1.1
        _ = _ := by ring
  have hQ : ∀ x ∈ Q, ConductorMeanDomain.InWindow h f tables D 1 m u L v₀ x := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hwindow y hy
  have hinj : Set.InjOn encode (E : Set (Σ _v : Fin 10 → ℤ, ℕ)) := by
    intro x hx y hy he
    have hv : x.1 = y.1 := congrArg Prod.snd he
    have hp : (d x.2,c x.2) = (d y.2,c y.2) := congrArg Prod.fst he
    have hxq := (mem_positiveModuli h x.1 D m L x.2).mp (Finset.mem_sigma.mp hx).2
    have hyq := (mem_positiveModuli h y.1 D m L y.2).mp (Finset.mem_sigma.mp hy).2
    have hq : x.2 = y.2 := CubeFreeModulusDecomposition.parameters_injOn
      (Nat.pos_of_ne_zero hxq.1.1.1) (Nat.pos_of_ne_zero hyq.1.1.1) hp
    cases x
    cases y
    cases hv
    cases hq
    rfl
  calc
    _ = ∑ x ∈ E, ‖completeCubicSum F x.2 x.1‖*(conductor h x.2 x.1)^((1 : ℝ)/2) := by
      rw [Finset.sum_sigma]
    _ = ∑ x ∈ E, ‖completeCubicSum F ((d x.2)*(c x.2)^2) x.1‖*(conductor h x.2 x.1)^((1 : ℝ)/2) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hq := (mem_positiveModuli h x.1 D m L x.2).mp (Finset.mem_sigma.mp hx).2
      exact congrArg (fun q => ‖completeCubicSum F q x.1‖ *
        (conductor h x.2 x.1)^((1 : ℝ)/2)) (eq_d_mul_c_sq x.2 hq.1.1)
    _ = ∑ x ∈ Q, ‖completeCubicSum F (x.1.1*x.1.2^2) x.2‖*(NumericalConductor.K h x.1.1 x.1.2 x.2)^((1 : ℝ)/2) :=
      (Finset.sum_image (f := fun x : ConductorMeanDomain.Sample =>
        ‖completeCubicSum F (x.1.1*x.1.2^2) x.2‖*(NumericalConductor.K h x.1.1 x.1.2 x.2)^((1 : ℝ)/2)) hinj).symm
    _ ≤ _ := hbound D m u L v₀ hD hm hL Q hQ

/-- The same proved estimate with the modulus sum outermost. -/
theorem exists_positive_modulus_outer_bound (lit : FixedFamilyPrimeFieldPointCount.Uniform)
    {t N B d₀ : ℕ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
    {tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)}
    {h : CoarseBounds F C}
    (hgeo : Geometry F f) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hData : TenMicrolocalIncidence.Conclusion F f N B) (hN : 1 ≤ N)
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C d₀ h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (D : ℝ) (m : ℕ) (u : Fin 10 → ℝ)
      (L : ℝ) (v₀ : Fin 10 → ℤ), 1 ≤ D → 0 < m → 0 ≤ L →
      (∑ q ∈ Finset.range (⌊2*D⌋₊+1),
        ∑ v ∈ (frequencies f tables u L m v₀).filter
          (fun v => q ∈ positiveModuli h v D m L), ‖completeCubicSum F q v‖*(conductor h q v)^((1 : ℝ)/2)) ≤
          M*(D*(2+‖u‖+L+(m : ℝ)))^ε*(1+L/(m : ℝ))^10*D^((13 : ℝ)/2) := by
  obtain ⟨M,hM,hbound⟩ := exists_positive_bound lit hgeo hhom hAn hData hN hc ε hε
  refine ⟨M,hM,?_⟩
  intro D m u L v₀ hD hm hL
  rw [← positive_sum_eq_modulus_outer]
  exact hbound D m u L v₀ hD hm hL


/-- The inverse-conductor moment over every cube-free modulus in the window.
There is no radical cutoff or auxiliary progression condition. -/
theorem exists_inverse_bound {t N d₀ : ℕ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
    {tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)}
    {h : CoarseBounds F C}
    (hhom : F.IsHomogeneous 3)
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C d₀ h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ v : Fin 10 → ℤ, GoodFrequency F f tables v →
      ∀ D : ℝ, 1 ≤ D →
      (∑ q ∈ CubeFreeNonzeroAverage.window D, ‖completeCubicSum F q v‖ / conductor h q v) ≤
        M*(D*frequencyHeight v)^ε*D^((13 : ℝ)/2) := by
  obtain ⟨M,hM,hbound⟩ := ConductorFixedFrequency.exists_inverse_bound hhom hc ε hε
  refine ⟨M,hM,?_⟩
  intro v hv D hD
  let Q : Finset (ℕ × ℕ) := (CubeFreeNonzeroAverage.window D).image (fun q => (d q,c q))
  have hQ : ∀ x ∈ Q,
      1 ≤ x.1 ∧ 1 ≤ x.2 ∧ Squarefree x.1 ∧ Squarefree x.2 ∧
        x.1.Coprime x.2 ∧ (x.1 : ℝ)*(x.2 : ℝ)^2 ≤ 2*D := by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
    have hw := (CubeFreeNonzeroAverage.mem_window D q).mp hq
    refine ⟨d_pos q,c_pos q,d_squarefree q,c_squarefree q hw.1,
      coprime_d_c q hw.1,?_⟩
    have he : (q : ℝ) = (d q : ℝ)*(c q : ℝ)^2 := by
      exact_mod_cast eq_d_mul_c_sq q hw.1
    exact he ▸ hw.2.2.le
  have hinj : Set.InjOn (fun q => (d q,c q)) (↑(CubeFreeNonzeroAverage.window D) : Set ℕ) := by
    intro q hq r hr he
    exact CubeFreeModulusDecomposition.parameters_injOn
      (Nat.pos_of_ne_zero ((CubeFreeNonzeroAverage.mem_window D q).mp hq).1.1)
      (Nat.pos_of_ne_zero ((CubeFreeNonzeroAverage.mem_window D r).mp hr).1.1) he
  calc
    _ = ∑ q ∈ CubeFreeNonzeroAverage.window D, ‖completeCubicSum F (d q*(c q)^2) v‖ / conductor h q v := by
      apply Finset.sum_congr rfl
      intro q hq
      exact congrArg (fun k => ‖completeCubicSum F k v‖ / conductor h q v)
        (eq_d_mul_c_sq q ((CubeFreeNonzeroAverage.mem_window D q).mp hq).1)
    _ = ∑ x ∈ Q, ‖completeCubicSum F (x.1*x.2^2) v‖ / NumericalConductor.K h x.1 x.2 v :=
      (Finset.sum_image (f := fun x : ℕ × ℕ => ‖completeCubicSum F (x.1*x.2^2) v‖ / NumericalConductor.K h x.1 x.2 v) hinj).symm
    _ ≤ _ := hbound v hv D hD Q hQ

/-- Both actual moments use one incidence, P/Q partition and least-depth
constant, all chosen before epsilon and every summation parameter. -/
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
          ∀ (D : ℝ) (m : ℕ) (u : Fin 10 → ℝ) (L : ℝ) (v₀ : Fin 10 → ℤ),
            1 ≤ D → 0 < m → 0 ≤ L →
            (∑ q ∈ Finset.range (⌊2*D⌋₊+1),
              ∑ v ∈ (frequencies f tables u L m v₀).filter
                (fun v => q ∈ positiveModuli h v D m L), ‖completeCubicSum F q v‖*(conductor h q v)^((1 : ℝ)/2)) ≤
                M*(D*(2+‖u‖+L+(m : ℝ)))^ε*(1+L/(m : ℝ))^10*D^((13 : ℝ)/2)) ∧
        ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 1 ≤ M ∧
          ∀ v : Fin 10 → ℤ, GoodFrequency F f tables v →
            ∀ D : ℝ, 1 ≤ D →
              (∑ q ∈ CubeFreeNonzeroAverage.window D, ‖completeCubicSum F q v‖ / conductor h q v) ≤
                M*(D*frequencyHeight v)^ε*D^((13 : ℝ)/2) := by
  obtain ⟨t,f,N,B,tables,hP,hQ,C,d₀,h,hc⟩ := MicrolocalConductorDepth.exists_data
    microlocal degreeSpan smooth spread weil dichotomy salberger
    integrality cubicWeil ampl pointcount F hhom hAn
  exact ⟨t,f,N,B,tables,hP,hQ,C,d₀,h,hc,
    fun ε hε => exists_positive_modulus_outer_bound pointcount hP.geometry hhom hAn
      hP.incidence hP.modulus_pos hc ε hε,
    fun ε hε => exists_inverse_bound hhom hc ε hε⟩

end CubicTenVariables.CubeFreeConductorMoments

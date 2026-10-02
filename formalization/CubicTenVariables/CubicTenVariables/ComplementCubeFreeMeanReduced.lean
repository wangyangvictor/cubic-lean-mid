import CubicTenVariables.ComplementCubeFreePiece
import CubicTenVariables.TerminalCubeFreeAverageReduced
import CubicTenVariables.MicrolocalConductorDepthReduced

/-! The complete complementary cube-free mean. Actual nonzero frequencies
are covered by the five proved pieces and the terminal exceptional locus;
the generic piece retains exactly the high-radical cutoff. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.ComplementCubeFreeMeanReduced
open MvPolynomial HessianTheorem11 NumericalPrimeDepth
open SquarefullModulusDecomposition CubeFreeModulusDecomposition
open ComplementCubeFreePiece (Sample)
open ConeComponentProgressionCount (points mem_points)
open scoped BigOperators Classical

variable {t N Betti : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
  {tables : ∀ k : Fin 4, MicrolocalPromotionTable.Table F f (k.val+1)}
  {C : ℝ} {d₀ : ℕ} {h : CoarseBounds F C}

/-- The original complementary summation conditions. -/
structure InComplement (F : MvPolynomial (Fin 10) ℤ)
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (tables : ∀ k : Fin 4, MicrolocalPromotionTable.Table F f (k.val+1))
    (N : ℕ) (h : CoarseBounds F C) (D : ℝ)
    (u : Fin 10 → ℝ) (L : ℝ) (m : ℕ) (v₀ : Fin 10 → ℤ) (x : Sample) : Prop where
  window : x.1 ∈ CubeFreeNonzeroAverage.window D
  good_primes : x.1.Coprime N
  progression_coprime : m.Coprime x.1
  nonzero : x.2 ≠ 0
  box : ∀ k, |(x.2 k : ℝ)-u k| ≤ L
  progression : ∀ k, (m : ℤ) ∣ x.2 k-v₀ k
  complement : ¬ ConductorFixedFrequency.GoodFrequency F f tables x.2 ∨
    1+L/(m : ℝ) < (NumericalConductorRadical.R22 h (d x.1) (c x.1) x.2 : ℝ)

/-- The literal source domain, including `(q,m*N)=1`, nonzero vectors,
the translated progression box and the complementary radical condition. -/
def pairs (F : MvPolynomial (Fin 10) ℤ)
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (tables : ∀ k : Fin 4, MicrolocalPromotionTable.Table F f (k.val+1))
    (N : ℕ) (h : CoarseBounds F C) (D : ℝ)
    (u : Fin 10 → ℝ) (L : ℝ) (m : ℕ) (v₀ : Fin 10 → ℤ) : Finset Sample := by
  classical
  exact ((CubeFreeNonzeroAverage.window D).product (TranslatedIntegerBoxes.box u L)).filter fun x =>
    x.1.Coprime (m*N) ∧ (∀ k, (m : ℤ) ∣ x.2 k-v₀ k) ∧ x.2 ≠ 0 ∧
      (¬ ConductorFixedFrequency.GoodFrequency F f tables x.2 ∨
        1+L/(m : ℝ) < (NumericalConductorRadical.R22 h (d x.1) (c x.1) x.2 : ℝ))

theorem mem_pairs (D : ℝ) (u : Fin 10 → ℝ) (L : ℝ) (m : ℕ) (v₀ : Fin 10 → ℤ) (x : Sample) :
    x ∈ pairs F f tables N h D u L m v₀ ↔
      InComplement F f tables N h D u L m v₀ x := by
  classical
  simp only [pairs,Finset.product_eq_sprod,Finset.mem_filter,Finset.mem_product,
    TranslatedIntegerBoxes.mem_box]
  constructor
  · rintro ⟨⟨hq,hbox⟩,hcop,hprog,hne,hcomp⟩
    have hc := Nat.coprime_mul_iff_right.mp hcop
    exact ⟨hq,hc.2,hc.1.symm,hne,hbox,hprog,hcomp⟩
  · intro hx
    exact ⟨⟨hx.window,hx.box⟩,Nat.coprime_mul_iff_right.mpr
      ⟨hx.progression_coprime.symm,hx.good_primes⟩,hx.progression,hx.nonzero,hx.complement⟩

/-- The full complementary estimate, with an arbitrary finite subset of
the literal summation domain and one constant before all parameters. -/
theorem of_data
    (integrality : CubicPrincipalOpenUniform.Uniform)
    (cubicWeil : Literature.SmoothCubicWeil)
    (isolated : CubicSurfacePointCountReduced.IsolatedConjugateCubicSurfacePointCount)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    (hP : MicrolocalRationalPartition.Conclusion F f N Betti tables)
    (hhom : F.IsHomogeneous 3) (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C d₀ h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ D : ℝ, 1 ≤ D →
      ∀ (u : Fin 10 → ℝ) (L : ℝ), 1 ≤ L → ∀ m : ℕ, 0 < m →
      ∀ (v₀ : Fin 10 → ℤ) (E : Finset Sample),
      (∀ x ∈ E, InComplement F f tables N h D u L m v₀ x) →
      (∑ x ∈ E, ‖completeCubicSum F x.1 x.2‖) ≤
        M*(D*(2+‖u‖+L+(m : ℝ)))^ε*D^((59 : ℝ)/6)*
          ((1+L/(m : ℝ))/D^((1 : ℝ)/3)+((1+L/(m : ℝ))/D^((1 : ℝ)/3))^9) := by
  classical
  choose A hA hpiece using fun i : Fin 5 =>
    ComplementCubeFreePiece.exists_bound hP hhom hAn hc i ε hε
  obtain ⟨B,hB,hterminal⟩ := TerminalCubeFreeAverageReduced.of_data integrality cubicWeil isolated pointcount
    F hhom hAn f N Betti hP.modulus_pos hP.geometry hP.incidence ε hε
  let M := B+∑ i, A i
  have hM : 1 ≤ M := by
    have hs : 0 ≤ ∑ i, A i := Finset.sum_nonneg fun i _ => zero_le_one.trans (hA i)
    dsimp [M]
    linarith
  refine ⟨M,hM,?_⟩
  intro D hD u L hL m hm v₀ E hE
  let H : ℝ := 2+‖u‖+L+(m : ℝ)
  let T : ℝ := 1+L/(m : ℝ)
  let Q : ℝ := (D*H)^ε*D^((59 : ℝ)/6)*(T/D^((1 : ℝ)/3)+(T/D^((1 : ℝ)/3))^9)
  let EB := E.filter fun x => (fun k => (x.2 k : ℚ)) ∈ OffTerminalFrequencyCertificate.exceptionalSet F
  let Ei (i : Fin 5) := E.filter fun x => (fun k => (x.2 k : ℚ)) ∈ ComplementFrequencyPieces.piece F f tables i
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hH0 : 0 ≤ H := by dsimp [H]; positivity
  have hT : 1 ≤ T := by dsimp [T]; exact le_add_of_nonneg_right (by positivity)
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hpieces (i : Fin 5) : (∑ x ∈ Ei i, ‖completeCubicSum F x.1 x.2‖) ≤ A i*Q := by
    have hp := hpiece i D hD u L hL m hm v₀ (Ei i) (fun x hx => by
      obtain ⟨hx,hmem⟩ := Finset.mem_filter.mp hx
      have hh := hE x hx
      refine ⟨hh.window,hh.good_primes,hh.progression_coprime,hmem,hh.box,hh.progression,?_⟩
      intro hi
      have hi0 : i=0 := Fin.ext hi
      have hg : ConductorFixedFrequency.GoodFrequency F f tables x.2 :=
        (ComplementFrequencyPieces.zero_iff_goodFrequency tables x.2).mp (hi0 ▸ hmem)
      exact hh.complement.resolve_left (fun hnot => hnot hg))
    convert hp using 1 <;> dsimp [Q,H,T] <;> ring
  have hterminalE : (∑ x ∈ EB, ‖completeCubicSum F x.1 x.2‖) ≤ B*Q := by
    let V := points (OffTerminalFrequencyCertificate.exceptionalSet F) u L m v₀
    have hsub : EB ⊆ (CubeFreeNonzeroAverage.window D).product V := by
      intro x hx
      obtain ⟨hx,hmem⟩ := Finset.mem_filter.mp hx
      have hh := hE x hx
      exact Finset.mem_product.mpr ⟨hh.window,(mem_points _ u L m v₀ x.2).mpr
        ⟨hh.box,hh.progression,hmem⟩⟩
    have hs : (∑ x ∈ EB, ‖completeCubicSum F x.1 x.2‖) ≤
        ∑ v ∈ V, ∑ q ∈ CubeFreeNonzeroAverage.window D, ‖completeCubicSum F q v‖ := by
      calc
        _ ≤ ∑ x ∈ (CubeFreeNonzeroAverage.window D).product V,
            ‖completeCubicSum F x.1 x.2‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => norm_nonneg _)
        _ = _ := by rw [Finset.product_eq_sprod,Finset.sum_product,Finset.sum_comm]
    have hb := hterminal D u L m v₀ hD (zero_le_one.trans hL) hm
    have hnum := ComplementProfileNumerics.term_le D T 1 9 hD hT0
      (by norm_num) (by norm_num) (by norm_num)
    simp only [Real.rpow_one,Real.rpow_ofNat] at hnum
    calc
      _ ≤ B*(D*H)^ε*T*D^9 := hs.trans hb
      _ = B*(D*H)^ε*(T*D^9) := by ring
      _ ≤ B*(D*H)^ε*(D^((59 : ℝ)/6)*(T/D^((1 : ℝ)/3)+(T/D^((1 : ℝ)/3))^9)) :=
        mul_le_mul_of_nonneg_left hnum (by have hB0 := zero_le_one.trans hB; positivity)
      _ = _ := by dsimp [Q]; ring
  have hpoint (x : Sample) (hx : x ∈ E) :
      ‖completeCubicSum F x.1 x.2‖ ≤
        (if (fun k => (x.2 k : ℚ)) ∈ OffTerminalFrequencyCertificate.exceptionalSet F then
          ‖completeCubicSum F x.1 x.2‖ else 0)+
        ∑ i : Fin 5, if (fun k => (x.2 k : ℚ)) ∈ ComplementFrequencyPieces.piece F f tables i then
          ‖completeCubicSum F x.1 x.2‖ else 0 := by
    have hterms : ∀ i : Fin 5, 0 ≤ if (fun k => (x.2 k : ℚ)) ∈ ComplementFrequencyPieces.piece F f tables i then
        ‖completeCubicSum F x.1 x.2‖ else 0 := fun i => by split_ifs <;> positivity
    rcases ComplementFrequencyPieces.integer_cover tables hP.geometry hhom x.2 (hE x hx).nonzero with hb | ⟨i,hi⟩
    · rw [if_pos hb]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hterms i)
    · have hs := Finset.single_le_sum (fun j _ => hterms j) (Finset.mem_univ i)
      rw [if_pos hi] at hs
      have hb : 0 ≤ if (fun k => (x.2 k : ℚ)) ∈ OffTerminalFrequencyCertificate.exceptionalSet F then
          ‖completeCubicSum F x.1 x.2‖ else 0 := by split_ifs <;> positivity
      linarith
  calc
    _ ≤ (∑ x ∈ EB, ‖completeCubicSum F x.1 x.2‖)+
        ∑ i : Fin 5, ∑ x ∈ Ei i, ‖completeCubicSum F x.1 x.2‖ := by
      have hs := Finset.sum_le_sum hpoint
      simp only [Finset.sum_add_distrib] at hs
      rw [Finset.sum_comm] at hs
      simpa only [EB,Ei,Finset.sum_filter] using hs
    _ ≤ B*Q+∑ i : Fin 5, A i*Q := add_le_add hterminalE (Finset.sum_le_sum fun i _ => hpieces i)
    _ = _ := by rw [← Finset.sum_mul]; dsimp [M,Q,H,T]; ring

/-- Exact conversion to the manuscript's modulus-first double sum. -/
theorem sum_pairs_eq_modulus_outer
    (D : ℝ) (u : Fin 10 → ℝ) (L : ℝ) (m : ℕ) (v₀ : Fin 10 → ℤ) :
    (∑ x ∈ pairs F f tables N h D u L m v₀, ‖completeCubicSum F x.1 x.2‖) =
      ∑ q ∈ CubeFreeNonzeroAverage.window D,
        ∑ v ∈ (TranslatedIntegerBoxes.box u L).filter
          (fun v => q.Coprime (m*N) ∧ (∀ k, (m : ℤ) ∣ v k-v₀ k) ∧ v ≠ 0 ∧
            (¬ ConductorFixedFrequency.GoodFrequency F f tables v ∨
              1+L/(m : ℝ) < (NumericalConductorRadical.R22 h (d q) (c q) v : ℝ))),
          ‖completeCubicSum F q v‖ := by
  classical
  simp only [pairs,Finset.product_eq_sprod,Finset.sum_filter,Finset.sum_product]

/-- The literal complementary sum, with no supplied finite-set hypotheses. -/
theorem modulus_outer_of_data
    (integrality : CubicPrincipalOpenUniform.Uniform)
    (cubicWeil : Literature.SmoothCubicWeil)
    (isolated : CubicSurfacePointCountReduced.IsolatedConjugateCubicSurfacePointCount)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    (hP : MicrolocalRationalPartition.Conclusion F f N Betti tables)
    (hhom : F.IsHomogeneous 3) (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C d₀ h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ D : ℝ, 1 ≤ D →
      ∀ (u : Fin 10 → ℝ) (L : ℝ), 1 ≤ L → ∀ m : ℕ, 0 < m →
      ∀ v₀ : Fin 10 → ℤ,
      (∑ q ∈ CubeFreeNonzeroAverage.window D,
        ∑ v ∈ (TranslatedIntegerBoxes.box u L).filter
          (fun v => q.Coprime (m*N) ∧ (∀ k, (m : ℤ) ∣ v k-v₀ k) ∧ v ≠ 0 ∧
            (¬ ConductorFixedFrequency.GoodFrequency F f tables v ∨
              1+L/(m : ℝ) < (NumericalConductorRadical.R22 h (d q) (c q) v : ℝ))),
          ‖completeCubicSum F q v‖) ≤
        M*(D*(2+‖u‖+L+(m : ℝ)))^ε*D^((59 : ℝ)/6)*
          ((1+L/(m : ℝ))/D^((1 : ℝ)/3)+((1+L/(m : ℝ))/D^((1 : ℝ)/3))^9) := by
  classical
  obtain ⟨M,hM,hbound⟩ := of_data integrality cubicWeil isolated pointcount hP hhom hAn hc ε hε
  refine ⟨M,hM,?_⟩
  intro D hD u L hL m hm v₀
  have hb := hbound D hD u L hL m hm v₀ (pairs F f tables N h D u L m v₀)
    (fun x hx => (mem_pairs D u L m v₀ x).mp hx)
  rwa [sum_pairs_eq_modulus_outer] at hb

/-- All geometric and conductor data are constructed from the listed
geometric hypotheses and proved prime-field count interface before epsilon
or any summation parameter is chosen. -/
theorem exists_data
    (microlocal : Literature.ProjectiveMicrolocalCertificate)
    (degreeSpan : TranslatedDepthSeven.StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (weil : Literature.AffinePlaneCubicWeil)
    (dichotomy : Literature.ProperHyperplaneWeightDichotomy)
    (salberger : TranslatedDepthSeven.Published.Salberger2023Theorem04)
    (integrality : CubicPrincipalOpenUniform.Uniform)
    (cubicWeil : Literature.SmoothCubicWeil)
    (isolated : CubicSurfacePointCountReduced.IsolatedConjugateCubicSurfacePointCount)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    (F : MvPolynomial (Fin 10) ℤ) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ (t : ℕ) (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10) (N B : ℕ)
      (tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)),
      MicrolocalRationalPartition.Conclusion F f N B tables ∧
      MicrolocalSquareRationalPartition.Conclusion F f N B ∧
      ∃ (C : ℝ) (d₀ : ℕ) (h : CoarseBounds F C),
        MicrolocalConductorDepth.Conclusion F f tables N C d₀ h ∧
        ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 1 ≤ M ∧
          ∀ D : ℝ, 1 ≤ D → ∀ (u : Fin 10 → ℝ) (L : ℝ), 1 ≤ L →
          ∀ m : ℕ, 0 < m → ∀ v₀ : Fin 10 → ℤ,
          (∑ q ∈ CubeFreeNonzeroAverage.window D,
            ∑ v ∈ (TranslatedIntegerBoxes.box u L).filter
              (fun v => q.Coprime (m*N) ∧ (∀ k, (m : ℤ) ∣ v k-v₀ k) ∧ v ≠ 0 ∧
                (¬ ConductorFixedFrequency.GoodFrequency F f tables v ∨
                  1+L/(m : ℝ) < (NumericalConductorRadical.R22 h (d q) (c q) v : ℝ))),
              ‖completeCubicSum F q v‖) ≤
            M*(D*(2+‖u‖+L+(m : ℝ)))^ε*D^((59 : ℝ)/6)*
              ((1+L/(m : ℝ))/D^((1 : ℝ)/3)+((1+L/(m : ℝ))/D^((1 : ℝ)/3))^9) := by
  obtain ⟨t,f,N,B,tables,hP,hQ,C,d₀,h,hc⟩ := MicrolocalConductorDepthReduced.exists_data
    microlocal degreeSpan smooth spread weil dichotomy salberger
    integrality cubicWeil isolated pointcount F hhom hAn
  exact ⟨t,f,N,B,tables,hP,hQ,C,d₀,h,hc,
    fun ε hε => modulus_outer_of_data integrality cubicWeil isolated pointcount hP hhom hAn hc ε hε⟩

end CubicTenVariables.ComplementCubeFreeMeanReduced

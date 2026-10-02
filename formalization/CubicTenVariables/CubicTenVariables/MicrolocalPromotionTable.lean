import CubicTenVariables.MicrolocalPromotionChoice
import CubicTenVariables.MicrolocalPromotionCover

/-! Finite promotion tables on the actual rational microlocal components.
The components and their integral equations are constructed from the same
incidence. A supplied exact model of its next depth locus is used only to
choose equations vanishing on that locus. All component choices share one
exceptional integer and one trace constant. No new literature input occurs. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.MicrolocalPromotionTable
open MvPolynomial HessianTheorem11 TranslatedDepthSeven
open ProjectiveMicrolocalData ProjectiveMicrolocalModels RationalConeClosure
open PolynomialExponentialFamily MicrolocalPromotionChoice MicrolocalPromotedPartition
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A finite family of constructed choices has constants uniform in the
component index as well as in all primes, fields and frequencies. -/
theorem exists_uniform_choices
    (degreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (weil : Literature.AffinePlaneCubicWeil)
    (dichotomy : Literature.ProperHyperplaneWeightDichotomy)
    (F : ParameterPolynomial 10) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    {c u : ℕ} (s : Fin c → ℕ)
    (G : ∀ i, Fin (s i) → ParameterPolynomial 10)
    (H : Fin u → ParameterPolynomial 10) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ 4)
    (hprime : ∀ i, (baseIdeal (G i)).IsPrime)
    (hgeometric : ∀ i, ((baseIdeal (G i)).map
      (MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime)
    (hhom : ∀ i, (baseIdeal (G i)).IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ))
    (hdim : ∀ i, ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸ baseIdeal (G i)) ≤
      ((9-j : ℕ) : WithBot ℕ∞))
    (hH : (baseIdeal H).IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ)) :
    ∃ (h : Fin c → ParameterPolynomial 10) (e : Fin c → ℕ) (N C : ℕ),
      1 ≤ N ∧ 1 ≤ C ∧ ∀ i, Choice F (G i) H j (h i) (e i) N C := by
  classical
  choose h e N C hc using fun i => exists_choice degreeSpan smooth spread weil dichotomy
    F hF hAn (G i) H j hj (hprime i) (hgeometric i) (hhom i) (hdim i) hH
  let C₀ : ℕ := 1 + ∑ i, C i
  have hCC (i : Fin c) : (C i : ℝ) ≤ (C₀ : ℝ) := by
    have hs : C i ≤ ∑ a, C a :=
      Finset.single_le_sum (fun a _ => Nat.zero_le (C a)) (Finset.mem_univ i)
    have hi : C i ≤ C₀ := by dsimp [C₀]; omega
    exact_mod_cast hi
  have hN : 1 ≤ ∏ i, N i := Finset.one_le_prod' (fun i _ => (hc i).modulus_pos)
  have hC : 1 ≤ C₀ := by dsimp [C₀]; omega
  have hgood (p : ℕ) (hp : ¬ p ∣ ∏ i, N i) (i : Fin c) : ¬ p ∣ N i := by
    intro hi
    exact hp (hi.trans (Finset.dvd_prod_of_mem N (Finset.mem_univ i)))
  refine ⟨h,e,∏ i, N i,C₀,hN,hC,?_⟩
  intro i
  refine ⟨(hc i).positive_degree,(hc i).homogeneous,(hc i).mem_excluded,hN,hC,
    (hc i).cases,?_,?_⟩
  · intro p _ hp ψ hψ K _ _ _ v hv
    exact ((hc i).fourier_bound p (hgood p hp i) ψ hψ K v hv).trans
      (mul_le_mul_of_nonneg_right (hCC i) (Real.rpow_nonneg (by positivity) _))
  · intro p _ hp v hv
    exact ((hc i).complete_sum_bound p (hgood p hp i) v hv).trans
      (mul_le_mul_of_nonneg_right (hCC i) (Real.rpow_nonneg (by positivity) _))

private theorem mem_base_zero_iff {n u : ℕ} (G : Fin u → ParameterPolynomial n)
    (x : Fin n → ℚ) : x ∈ affineIdealZeroLocus (baseIdeal G) ↔
      ∀ a, eval₂ (Int.castRingHom ℚ) x (G a) = 0 := by
  constructor
  · intro hx a
    simpa only [eval_map] using hx _ (Ideal.subset_span ⟨a,rfl⟩)
  · intro hx
    have hker : baseIdeal G ≤ RingHom.ker (eval x) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨a,rfl⟩
      change eval x (map (Int.castRingHom ℚ) (G a)) = 0
      simpa only [eval_map] using hx a
    exact fun P hP => hker hP

private theorem rational_geometric_zero_iff {n : ℕ} (P : ParameterPolynomial n)
    (x : Fin n → ℚ) : eval₂ (Int.castRingHom ℚ) x P = 0 ↔
      eval₂ (Int.castRingHom GeometricField) (rationalEmbedding x) P = 0 := by
  have hc : (algebraMap ℚ GeometricField).comp (Int.castRingHom ℚ) =
      Int.castRingHom GeometricField := by ext a; simp
  have he : eval₂ (Int.castRingHom GeometricField) (rationalEmbedding x) P =
      algebraMap ℚ GeometricField (eval₂ (Int.castRingHom ℚ) x P) := by
    simpa only [hc,Function.comp_def,rationalEmbedding] using
      (eval₂_comp_left (algebraMap ℚ GeometricField) (Int.castRingHom ℚ) x P).symm
  rw [he]
  exact (map_eq_zero (algebraMap ℚ GeometricField)).symm

/-- Concrete finite data, retaining the exact next locus and the actual
rational component cover. A zero promotion equation disables a component. -/
structure Table {t : ℕ} (F : ParameterPolynomial 10)
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10) (j : ℕ) where
  c : ℕ
  s : Fin c → ℕ
  G : ∀ i, Fin (s i) → ParameterPolynomial 10
  h : Fin c → ParameterPolynomial 10
  e : Fin c → ℕ
  N : ℕ
  C : ℕ
  next_count : ℕ
  H : Fin next_count → ParameterPolynomial 10
  modulus_pos : 1 ≤ N
  constant_pos : 1 ≤ C
  prime : ∀ i, (baseIdeal (G i)).IsPrime
  geometric : ∀ i, GeometricallyPrimeMvPolynomialIdeal (baseIdeal (G i))
  homogeneous : ∀ i, (baseIdeal (G i)).IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ)
  dimension : ∀ i, ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸ baseIdeal (G i)) ≤
    ((9-j : ℕ) : WithBot ℕ∞)
  cover : filtration f j = ⋃ i, affineIdealZeroLocus (baseIdeal (G i))
  next_exact : affineIdealZeroLocus (baseIdeal H) = filtration f (j+1)
  choice : ∀ i, Choice F (G i) H j (h i) (e i) N C

variable {t : ℕ} {F : ParameterPolynomial 10}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10} {j : ℕ}

/-- The promotion set is the literal union of the chosen component opens. -/
def Table.open (T : Table F f j) : Set (Fin 10 → ℚ) :=
  MicrolocalPromotionCover.promotionOpen (fun i => baseIdeal (T.G i))
    (fun i => map (Int.castRingHom ℚ) (T.h i))

theorem Table.cover_point (T : Table F f j) (x : Fin 10 → ℚ)
    (hx : x ∈ filtration f j) : ∃ i, x ∈ affineIdealZeroLocus (baseIdeal (T.G i)) := by
  rw [T.cover] at hx
  exact Set.mem_iUnion.mp hx

/-- The same chosen equations force the promotion to avoid the next
actual depth locus, without a new open-containment assumption. -/
theorem Table.open_subset_layer (T : Table F f j) (hj : j < 5) :
    T.open ⊆ PromotedFrequencyPartition.layer (filtration f) j := by
  rw [PromotedFrequencyPartition.layer,if_pos hj]
  rintro x ⟨i,hxi,hx⟩
  refine ⟨?_,?_⟩
  · rw [T.cover]
    exact Set.mem_iUnion.mpr ⟨i,hxi⟩
  · intro hnext
    rw [← T.next_exact] at hnext
    exact hx (hnext _ (T.choice i).mem_excluded)

theorem Table.open_nonzero (T : Table F f j) : (0 : Fin 10 → ℚ) ∉ T.open := by
  rintro ⟨i,_,hi⟩
  exact hi (HomogeneousPrincipalOpen.eval_zero_of_positive_degree (T.h i) (T.e i)
    (T.choice i).positive_degree (T.choice i).homogeneous ℚ)

/-- At the two high counting levels the table gives the exact alternatives
consumed by the finite residual-cover theorem. -/
theorem Table.cases_for_high_levels (T : Table F f j) (hj : j=3 ∨ j=4) (i : Fin T.c) :
    ConeComponentProgressionCount.ComponentCondition (8-j) (baseIdeal (T.G i)) ∨
    affineIdealZeroLocus (baseIdeal (T.G i)) ⊆ filtration f (j+1) ∨
    ∃ e : ℕ, 0 < e ∧ (map (Int.castRingHom ℚ) (T.h i)).IsHomogeneous e ∧
      ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸ ConePrincipalOpen.residualIdeal
        (baseIdeal (T.G i)) (map (Int.castRingHom ℚ) (T.h i))) ≤
          ((8-j : ℕ) : WithBot ℕ∞) := by
  rcases MicrolocalPromotionChoice.cases_for_high_levels (T.choice i) hj
      (T.prime i) (T.geometric i) (T.homogeneous i) with hc | hc | ⟨he,hh,hd⟩
  · exact Or.inl hc
  · refine Or.inr (Or.inl ?_)
    intro x hx
    rw [← T.next_exact]
    exact fun P hP => hx P (hc hP)
  · exact Or.inr (Or.inr ⟨T.e i,he,hh.map _,hd⟩)

/-- Construct the promotion table on all actual rational components of
depth j. The next equations come from the same incidence's exact model. -/
theorem exists_table
    (degreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (weil : Literature.AffinePlaneCubicWeil)
    (dichotomy : Literature.ProperHyperplaneWeightDichotomy)
    (hgeo : Geometry F f) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hj : 1 ≤ j ∧ j ≤ 4) {M : ℕ} (hnext : ZDepthModel f (j+1) M) :
    Nonempty (Table F f j) := by
  classical
  obtain ⟨u,H,dH,hdH,_,hHpoints,_⟩ := hnext
  have hH : (baseIdeal H).IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ) := by
    apply Ideal.homogeneous_span
    rintro P ⟨a,rfl⟩
    exact ⟨dH a,(hdH a).map _⟩
  have hHexact : affineIdealZeroLocus (baseIdeal H) = filtration f (j+1) := by
    ext x
    rw [mem_base_zero_iff]
    simp only [filtration,if_neg (by omega : j+1 ≠ 0)]
    change (∀ a, eval₂ (Int.castRingHom ℚ) x (H a) = 0) ↔
      rationalEmbedding x ∈ ProjectiveMicrolocalDepth.depth f (j+1)
    rw [← hHpoints]
    exact forall_congr' (fun a => rational_geometric_zero_iff (H a) x)
  obtain ⟨c,Y,s,G,d,hcover,hcomp⟩ := MicrolocalRationalComponents.exists_components
    hgeo hAn (j:=j) (by omega) (by omega)
  have hprime : ∀ i, (baseIdeal (G i)).IsPrime := fun i => (hcomp i).2.2.2.2.1
  have hgeom : ∀ i, GeometricallyPrimeMvPolynomialIdeal (baseIdeal (G i)) :=
    fun i => (hcomp i).2.2.2.2.2.1
  have hhom : ∀ i, (baseIdeal (G i)).IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ) :=
    fun i => (hcomp i).2.2.2.2.2.2.1
  have hdim : ∀ i, ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸ baseIdeal (G i)) ≤
      ((9-j : ℕ) : WithBot ℕ∞) := by
    intro i
    simpa only [show 10-(j+1)=9-j by omega] using (hcomp i).2.2.2.2.2.2.2.2.1
  obtain ⟨h,e,N,C,hN,hC,hchoice⟩ := exists_uniform_choices degreeSpan smooth spread weil dichotomy
    F hF hAn s G H j hj hprime (fun i => hgeom i (AlgebraicClosure ℚ)) hhom hdim hH
  have hpoints (i : Fin c) (x : Fin 10 → ℚ) :
      x ∈ affineIdealZeroLocus (baseIdeal (G i)) ↔ rationalEmbedding x ∈ Y i := by
    rw [mem_base_zero_iff,(hcomp i).2.2.2.2.2.2.2.2.2]
    exact forall_congr' (fun a => rational_geometric_zero_iff (G i a) x)
  have hexact : filtration f j = ⋃ i, affineIdealZeroLocus (baseIdeal (G i)) := by
    ext x
    simp only [filtration,if_neg (by omega : j ≠ 0),Set.mem_iUnion]
    rw [← rationalDepth_points hgeo (by omega : 0 < j)]
    change rationalEmbedding x ∈ rationalDepth f j ↔ _
    rw [hcover,Set.mem_iUnion]
    exact exists_congr (fun i => (hpoints i x).symm)
  exact ⟨⟨c,s,G,h,e,N,C,u,H,hN,hC,hprime,hgeom,hhom,hdim,hexact,hHexact,hchoice⟩⟩

end CubicTenVariables.MicrolocalPromotionTable

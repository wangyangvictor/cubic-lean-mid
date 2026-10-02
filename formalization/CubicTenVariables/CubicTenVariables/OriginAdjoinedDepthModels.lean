import CubicTenVariables.ComplementFrequencyPieces
import CubicTenVariables.MicrolocalDepthSupportCount
import CubicTenVariables.RationalEquationDimension

/-! Integral models for the actual depth supports with the origin adjoined.
Multiplying every original equation by every coordinate gives precisely the
union with the origin over every field. The resulting ideals need not be
radical; their dimensions are transferred through their actual zero loci. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.OriginAdjoinedDepthModels
open MvPolynomial HessianTheorem11 TranslatedDepthSeven RationalConeClosure
open ProjectiveMicrolocalData ProjectiveMicrolocalDepth ProjectiveMicrolocalModels
open IntegralModelDimension NumericalPrimeDepth
attribute [local instance] MvPolynomial.gradedAlgebra

/-- All products GₐXᵢ, with a literal finite natural-number index. -/
def adjoinOrigin {n s : ℕ} (G : Fin s → MvPolynomial (Fin n) ℤ) :
    Fin (s*n) → MvPolynomial (Fin n) ℤ :=
  fun a => G (finProdFinEquiv.symm a).1 * X (finProdFinEquiv.symm a).2

theorem vanishing_iff {n s : ℕ} (G : Fin s → MvPolynomial (Fin n) ℤ)
    (K : Type*) [Field K] (v : Fin n → K) :
    (∀ a, eval₂ (Int.castRingHom K) v (adjoinOrigin G a) = 0) ↔
      v = 0 ∨ ∀ a, eval₂ (Int.castRingHom K) v (G a) = 0 := by
  constructor
  · intro hv
    by_cases hz : v=0
    · exact Or.inl hz
    · right
      obtain ⟨i,hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra! hzero
        exact hz (funext hzero)
      intro a
      have he := hv (finProdFinEquiv (a,i))
      simp only [adjoinOrigin,Equiv.symm_apply_apply,eval₂_mul,eval₂_X] at he
      exact (mul_eq_zero.mp he).resolve_right hi
  · rintro (rfl | hv) a
    · simp [adjoinOrigin]
    · simp only [adjoinOrigin,eval₂_mul,eval₂_X,hv,zero_mul]

theorem homogeneous {n s : ℕ} (G : Fin s → MvPolynomial (Fin n) ℤ)
    (d : Fin s → ℕ) (hd : ∀ a, (G a).IsHomogeneous (d a)) (a : Fin (s*n)) :
    (adjoinOrigin G a).IsHomogeneous (d (finProdFinEquiv.symm a).1+1) :=
  (hd _).mul (isHomogeneous_X ℤ _)

private theorem mem_zeroLocus_equations {n s : ℕ}
    (G : Fin s → MvPolynomial (Fin n) ℤ) (K : Type*) [Field K] (v : Fin n → K) :
    v ∈ zeroLocus K (Ideal.span (Set.range (fun a => map (Int.castRingHom K) (G a)))) ↔
      ∀ a, eval₂ (Int.castRingHom K) v (G a) = 0 := by
  rw [zeroLocus_span]
  change (∀ P ∈ Set.range (fun a => map (Int.castRingHom K) (G a)), eval v P=0) ↔ _
  simp only [Set.forall_mem_range,eval_map]

theorem rationalIdeal_ne_top {n s : ℕ} (G : Fin s → MvPolynomial (Fin n) ℤ) :
    IntegralModelDimension.rationalIdeal (adjoinOrigin G) ≠ ⊤ := by
  have hzero : (0 : Fin n → ℚ) ∈ zeroLocus ℚ
      (IntegralModelDimension.rationalIdeal (adjoinOrigin G)) :=
    (mem_zeroLocus_equations _ ℚ 0).mpr ((vanishing_iff G ℚ 0).mpr (Or.inl rfl))
  intro htop
  rw [htop,zeroLocus_top] at hzero
  exact hzero

/-- One support model uses the same excluded integer as the original
incidence. Its dimension concerns the actual equation quotient. -/
structure Model {t : ℕ}
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10) (N : ℕ) (j : Fin 5) where
  count : ℕ
  equations : Fin count → MvPolynomial (Fin 10) ℤ
  degree : Fin count → ℕ
  degree_pos : ∀ a, 0 < degree a
  homogeneous : ∀ a, (equations a).IsHomogeneous (degree a)
  proper : IntegralModelDimension.rationalIdeal equations ≠ ⊤
  ideal_homogeneous : (IntegralModelDimension.rationalIdeal equations).IsHomogeneous
    (homogeneousSubmodule (Fin 10) ℚ)
  dimension : ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸
    IntegralModelDimension.rationalIdeal equations) ≤ (MicrolocalDepthSupportCount.profile j : Dimension)
  geometric_exact : ∀ v : GeometricPoint 10,
    (∀ a, eval₂ (Int.castRingHom GeometricField) v (equations a)=0) ↔
      v=0 ∨ v ∈ depth f (j.val+2)
  good_exact : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ (K : Type) [Field K] [CharP K p],
    ∀ v : Fin 10 → K, (∀ a, eval₂ (Int.castRingHom K) v (equations a)=0) ↔
      v=0 ∨ ((j.val+2 : ℕ) : Dimension) ≤
        IntegralGeometricFiberDepth.geometricFiberDimension f K v

variable {t N B : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}

/-- Construct the support equations from the same chosen depth model.
The stronger last two dimensions are the already proved terminal bounds. -/
theorem exists_model (hgeo : Geometry F f) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hData : TenMicrolocalIncidence.Conclusion F f N B) (j : Fin 5) :
    Nonempty (Model f N j) := by
  have hm : ZDepthModel f (j.val+2) N := by
    simpa only [Nat.add_assoc] using hData.depth_models ⟨j.val+1,by omega⟩
  obtain ⟨s,G,d,hd,_hIdeal,hpoints,hgood⟩ := hm
  let H := adjoinOrigin G
  have hp : IntegralModelDimension.rationalIdeal H ≠ ⊤ := rationalIdeal_ne_top G
  have hGeo (v : GeometricPoint 10) :
      (∀ a, eval₂ (Int.castRingHom GeometricField) v (H a)=0) ↔
        v=0 ∨ v ∈ depth f (j.val+2) := by
    rw [vanishing_iff,hpoints]
  have hz : zeroLocus GeometricField (geometricIdeal H) = depth f (j.val+2) ∪ {0} := by
    ext v
    rw [geometricIdeal,mem_zeroLocus_equations,hGeo]
    simp only [Set.mem_union,Set.mem_singleton_iff]
    tauto
  have hdim : ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸ rationalIdeal H) ≤
      (MicrolocalDepthSupportCount.profile j : Dimension) := by
    have he := RationalEquationDimension.rational_quotient_dimension_eq_geometric_zeroLocus
      (rationalIdeal H) hp
    change affineDimension (zeroLocus GeometricField
      ((rationalIdeal H).map (map (algebraMap ℚ GeometricField)))) = _ at he
    rw [map_rationalIdeal,hz] at he
    rw [← he,affineDimension_union,affineDimension_singleton]
    apply max_le
    · exact MicrolocalDepthSupportCount.depth_dimension_profile hgeo hhom hAn j
    · exact_mod_cast Nat.zero_le (MicrolocalDepthSupportCount.profile j)
  refine ⟨⟨s*10,H,(fun a => d (finProdFinEquiv.symm a).1+1),
    (fun a => Nat.succ_pos _),(fun a => homogeneous G d hd a),hp,?_,hdim,hGeo,?_⟩⟩
  · apply Ideal.homogeneous_span
    rintro P ⟨a,rfl⟩
    exact ⟨d (finProdFinEquiv.symm a).1+1,(homogeneous G d hd a).map _⟩
  · intro p hp hpN K _ _ v
    rw [vanishing_iff,(hgood p hp hpN K).1 v]

/-- All five supports are modeled with the original common excluded
integer N, not separately enlarged exceptional-prime sets. -/
theorem exists_models (hgeo : Geometry F f) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hData : TenMicrolocalIncidence.Conclusion F f N B) :
    Nonempty (∀ j : Fin 5, Model f N j) := by
  classical
  exact ⟨fun j => Classical.choice (exists_model hgeo hhom hAn hData j)⟩

/-- On each piece, every deeper support model has an actually nonzero
integer equation value. This is the outside condition required by the sieve. -/
theorem Model.outside_piece {j : Fin 5} (M : Model f N j)
    (tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1))
    (i : Fin 5) (hij : i.val ≤ j.val) (v : Fin 10 → ℤ)
    (hv : (fun a => (v a : ℚ)) ∈ ComplementFrequencyPieces.piece F f tables i) :
    ∃ a, eval v (M.equations a) ≠ 0 := by
  by_contra! hzero
  have hcast (a : Fin M.count) :
      eval₂ (Int.castRingHom GeometricField) (fun k => (v k : GeometricField))
        (M.equations a) = 0 := by
    have he := map_eval (Int.castRingHom GeometricField) v (M.equations a)
    rw [hzero a,map_zero] at he
    simpa only [Function.comp_def,Int.coe_castRingHom,eval₂_eq_eval_map] using he.symm
  have hs := (M.geometric_exact _).mp hcast
  have hoff := ComplementFrequencyPieces.not_mem_depth_with_origin tables i
    (fun a => (v a : ℚ)) hv (j.val+2) (by omega)
  apply hoff
  have he : rationalEmbedding (fun a => (v a : ℚ)) = fun a => (v a : GeometricField) := by
    ext a
    simp only [rationalEmbedding,map_intCast]
  rw [he]
  exact hs.elim (fun hz => Or.inl (Set.mem_singleton_iff.mpr hz)) Or.inr

/-- Large actual numerical prime or prime-square depth implies vanishing
of every literal support equation modulo the same good prime. -/
theorem Model.modular_vanishing {j : Fin 5} (M : Model f N j)
    {tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)}
    {C : ℝ} {d : ℕ} {h : CoarseBounds F C}
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C d h)
    (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) (v : Fin 10 → ℤ)
    (hv : j.val+2 ≤ primeDepth h p v ∨ j.val+2 ≤ squareDepth h p v) :
    ∀ a, eval₂ (Int.castRingHom (ZMod p)) (fun k => (v k : ZMod p)) (M.equations a)=0 := by
  exact (M.good_exact p Fact.out hpN (ZMod p) _).mpr
    (hc.geometric_support p hpN v (j.val+2) (by omega) hv)

end CubicTenVariables.OriginAdjoinedDepthModels

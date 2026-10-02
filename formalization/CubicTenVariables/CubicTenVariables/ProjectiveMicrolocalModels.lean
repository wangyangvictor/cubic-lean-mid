import CubicTenVariables.ProjectiveMicrolocalDepth
import CubicTenVariables.ExactRationalConeModel
import CubicTenVariables.HomogeneousFiberDepthModelsProved

/-! Exact rational closures and integral models for the shared incidence's
positive-depth loci. The closure preserves empty loci and adds no rational
points. All dimension bounds are consequences, not literature inputs. -/

noncomputable section
namespace CubicTenVariables.ProjectiveMicrolocalModels
open MvPolynomial HessianTheorem11
open ProjectiveMicrolocalData ProjectiveMicrolocalDepth BihomogeneousIncidenceFamily
open RationalConeClosure ExactRationalConeModel
open scoped BigOperators

variable {n t : ℕ} {F : MvPolynomial (Fin n) ℤ}
  {f : Fin t → Polynomial n n}

theorem incidence_closed (h : Geometry F f) : AlgebraicallyClosedSet (geometricIncidence f) := by
  obtain ⟨c,Y,O,hcover,hY,_⟩ := h.conormalCover
  rw [hcover]
  exact FiniteIncidenceDepth.closed_iUnion Y hY

theorem incidence_point_scaling (h : Geometry F f) (v x : GeometricPoint n)
    (hx : x ∈ fiber f GeometricField v) (a : GeometricField) :
    a • x ∈ fiber f GeometricField v := by
  obtain ⟨dx,dv,hdx,hfx,hfv⟩ := h.bihomogeneous
  exact fiber_stable_smul_point f dx hfx v a x hx

theorem incidence_normal_scaling (h : Geometry F f) (v x : GeometricPoint n)
    (hx : x ∈ fiber f GeometricField v) (a : GeometricField) :
    x ∈ fiber f GeometricField (a • v) := by
  obtain ⟨dx,dv,hdx,hfx,hfv⟩ := h.bihomogeneous
  exact fiber_subset_smul_parameter f dv hfv v a hx

theorem fiber_eq_integral_fiber (K : Type*) [Field K] (v : Fin n → K) :
    fiber f K v = IntegralGeometricFiberDepth.fiber f K v := by
  rw [BihomogeneousIncidenceFamily.fiber_eq_zeroLocus,
    IntegralGeometricFiberDepth.fiber_eq_zeroLocus]

theorem depth_eq_integral_fiber_locus (j : ℕ) :
    depth f j = {v : GeometricPoint n | (j : Dimension) ≤
      ReducedGaussSection.coordinateDimension (IntegralGeometricFiberDepth.fiber f GeometricField v)} := by
  rw [depth_eq_fiber_dimension]
  ext v
  simp only [Set.mem_setOf_eq]
  rw [fiber_eq_integral_fiber (f:=f) GeometricField v]
  rfl

def rationalDepth (f : Fin t → Polynomial n n) (j : ℕ) : Set (GeometricPoint n) :=
  rationalClosure (depth f j)

theorem rationalDepth_closed (j : ℕ) : AlgebraicallyClosedSet (rationalDepth f j) :=
  algebraicallyClosedSet_geometricClosure _

theorem rationalDepth_subset (h : Geometry F f) {j : ℕ} (hj : 0 < j) :
    rationalDepth f j ⊆ depth f j := by
  apply geometricClosure_subset_closed _ (depth_closed h hj)
  rintro _ ⟨q,hq,rfl⟩
  exact hq

theorem rationalDepth_points (h : Geometry F f) {j : ℕ} (hj : 0 < j) :
    rationalPoints (rationalDepth f j) = rationalPoints (depth f j) := by
  ext q
  constructor
  · intro hq
    exact rationalDepth_subset h hj hq
  · intro hq
    exact subset_geometricClosure _ ⟨q,hq,rfl⟩

theorem rationalDepth_cone (h : Geometry F f) (j : ℕ) :
    IsAffineCone (rationalDepth f j) := by
  apply geometricClosure_isAffineCone_of_rational_smul
  rintro a _ ⟨q,hq,rfl⟩
  refine ⟨a • q,?_,rationalEmbedding_smul a q⟩
  change rationalEmbedding (a • q) ∈ depth f j
  rw [rationalEmbedding_smul]
  exact depth_cone h j _ _ hq

theorem rationalDepth_dimension_le (h : Geometry F f)
    (hF : Anisotropic (map (Int.castRingHom ℚ) F)) {j : ℕ}
    (hj : 0 < j) (hjn : j < n) :
    affineDimension (rationalDepth f j) ≤ ((n-(j+1) : ℕ) : Dimension) := by
  exact (affineDimension_mono (show rationalDepth f j ⊆ rationalConeClosure (depth f j)
    from fun _ hx => Or.inl hx)).trans (rational_depth_dimension_le h hF hj hjn)

/-- Same finite integral equations give the actual rational closure, its
exact rational points, and the improved dimension in every good field. -/
theorem exists_rational_depth_model (h : Geometry F f)
    (hF : Anisotropic (map (Int.castRingHom ℚ) F)) {j : ℕ}
    (hj : 0 < j) (hjn : j < n) :
    ∃ (m : ℕ) (G : Fin m → MvPolynomial (Fin n) ℤ) (d : Fin m → ℕ),
      (∀ i, (G i).IsHomogeneous (d i)) ∧
      IntegralModelDimension.rationalIdeal G = vanishingIdeal ℚ (rationalPoints (depth f j)) ∧
      IntegralModelDimension.geometricIdeal G = vanishingIdeal GeometricField (rationalDepth f j) ∧
      (∀ x : GeometricPoint n, x ∈ rationalDepth f j ↔
        ∀ i, eval₂ (Int.castRingHom GeometricField) x (G i) = 0) ∧
      (∀ q : Fin n → ℚ, (∀ i, eval₂ (Int.castRingHom ℚ) q (G i) = 0) ↔
        rationalEmbedding q ∈ depth f j) ∧
      ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ D →
        ∀ (K : Type) [Field K] [CharP K p],
          ringKrullDim (MvPolynomial (Fin n) K ⧸
            FixedEquationNormalization.equationIdeal G K) ≤ ((n-(j+1) : ℕ) : Dimension) ∧
          ringKrullDim (MvPolynomial (Fin n) K ⧸ vanishingIdeal K
            (FixedEquationDimensionReduction.zeroSet G K)) ≤ ((n-(j+1) : ℕ) : Dimension) :=
  exists_model_good_characteristic_dimension_bound (depth f j) (depth_cone h j)
    (depth_closed h hj) (rationalDepth_dimension_le h hF hj hjn)

/-- A fixed model of the actual depth locus, with exact reduction and the
proved geometric codimension bound. The same equations occur throughout. -/
def ZDepthModel (f : Fin t → Polynomial n n) (j N : ℕ) : Prop :=
  ∃ (u : ℕ) (G : Fin u → MvPolynomial (Fin n) ℤ) (d : Fin u → ℕ),
    (∀ i, (G i).IsHomogeneous (d i)) ∧
    IntegralModelDimension.geometricIdeal G = vanishingIdeal GeometricField (depth f j) ∧
    (∀ v : GeometricPoint n, (∀ i, eval₂ (Int.castRingHom GeometricField) v (G i) = 0) ↔
      v ∈ depth f j) ∧
    ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ (K : Type) [Field K] [CharP K p],
      (∀ v : Fin n → K, (∀ i, eval₂ (Int.castRingHom K) v (G i) = 0) ↔
        (j : Dimension) ≤ IntegralGeometricFiberDepth.geometricFiberDimension f K v) ∧
      ringKrullDim (MvPolynomial (Fin n) K ⧸
        FixedEquationNormalization.equationIdeal G K) ≤ ((n-j : ℕ) : Dimension)

theorem ZDepthModel.of_dvd {j D N : ℕ} (h : ZDepthModel f j D) (hDN : D ∣ N) :
    ZDepthModel f j N := by
  obtain ⟨u,G,d,hd,hideal,hpoints,hgood⟩ := h
  refine ⟨u,G,d,hd,hideal,hpoints,?_⟩
  intro p hp hpN K _ _
  exact hgood p hp (fun hpD => hpN (hpD.trans hDN)) K

/-- The proved homogeneous-family models and the proved depth bound
supply exact good-characteristic models; no dimension bound is assumed. -/
theorem exists_depth_model
    (h : Geometry F f) {j : ℕ} (hj : 0 < j) :
    ∃ D : ℕ, 1 ≤ D ∧ ZDepthModel f j D := by
  obtain ⟨dx,dv,hdx,hfx,hfv⟩ := h.bihomogeneous
  obtain ⟨u,G,d,D,hd,hD,hideal,hgood⟩ :=
    HomogeneousFiberDepthModelsProved.proved n n t j hj f dx dv hdx hfx hfv
  have hi : IntegralModelDimension.geometricIdeal G =
      vanishingIdeal GeometricField (depth f j) := by
    rw [depth_eq_integral_fiber_locus]
    exact hideal
  have hdim : ringKrullDim (MvPolynomial (Fin n) ℚ ⧸
      FixedEquationNormalization.equationIdeal G ℚ) ≤ ((n-j : ℕ) : Dimension) := by
    change ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ IntegralModelDimension.rationalIdeal G) ≤ _
    rw [ExactRationalConeModel.rational_quotient_dimension_eq G (depth f j) hi]
    exact depth_dimension_le h hj
  obtain ⟨E,hE,hbound⟩ := FixedEquationDimensionAll.exists_good_characteristic_dimension_bound G hdim
  refine ⟨D*E,by nlinarith, u,G,d,hd,hi,?_,?_⟩
  · intro v
    have he : zeroLocus GeometricField (IntegralModelDimension.geometricIdeal G) = depth f j := by
      rw [hi]
      exact depth_closed h hj
    rw [← he,IntegralModelDimension.geometricIdeal,zeroLocus_span]
    change _ ↔ ∀ P ∈ Set.range (fun i => map (Int.castRingHom GeometricField) (G i)), eval v P = 0
    simp only [Set.forall_mem_range,eval_map]
  · intro p hp hpDE K _ _
    exact ⟨hgood p hp (fun hpD => hpDE (hpD.trans (dvd_mul_right D E))) K,
      (hbound p hp (fun hpE => hpDE (hpE.trans (dvd_mul_left E D))) K).1⟩

/-- All nine models share one excluded integer, fixed before every prime
and field. Model equations and degrees may vary with the depth index. -/
theorem exists_uniform_ten_depth_models
    {F : MvPolynomial (Fin 10) ℤ} {f : Fin t → Polynomial 10 10}
    (h : Geometry F f) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ i : Fin 9, ZDepthModel f (i.val+1) N := by
  classical
  choose D hD hmodel using fun i : Fin 9 => exists_depth_model h (j:=i.val+1) (by omega)
  refine ⟨∏ i, D i,Finset.one_le_prod' (fun i _ => hD i),?_⟩
  intro i
  exact (hmodel i).of_dvd (Finset.dvd_prod_of_mem D (Finset.mem_univ i))

end CubicTenVariables.ProjectiveMicrolocalModels

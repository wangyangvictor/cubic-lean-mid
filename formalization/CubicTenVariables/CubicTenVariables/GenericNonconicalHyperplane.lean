import CubicTenVariables.GenericNormalDerivations
import CubicTenVariables.GenericHyperplaneFrameKernel
import CubicTenVariables.Literature.FiniteFieldPointCounts

/-! Generic hyperplane sections of nonconical cubics are nonconical in
characteristic zero. Actual parameter derivations force each section vertex
into the original Hessian kernel. No nonconical-section witness is assumed. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
noncomputable section
namespace CubicTenVariables.GenericNonconicalHyperplane
open MvPolynomial HessianTheorem11 Matrix Module Literature
open HessianTheorem11.PolynomialRestriction ReducedCubicVertex ReducedVertexBaseChange
open GenericNormalDerivations
open scoped BigOperators

/-- A symmetric form zero on a hyperplane is zero everywhere if its kernel
contains one vector outside that hyperplane. -/
theorem symmetric_matrix_eq_zero_of_hyperplane_and_kernel
    {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hA : A.transpose = A)
    (u : Module.Dual K (Fin n → K))
    (hzero : ∀ x y, u x = 0 → u y = 0 → dotProduct x (A.mulVec y) = 0)
    (v : Fin n → K) (huv : u v ≠ 0) (hv : A.mulVec v = 0) : A = 0 := by
  classical
  have hleft (y : Fin n → K) : dotProduct v (A.mulVec y) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, hv, zero_dotProduct]
  have hdecomp (x : Fin n → K) :
      ∃ y : Fin n → K, u y = 0 ∧ x = y + (u x / u v) • v := by
    refine ⟨x - (u x / u v) • v, ?_, by module⟩
    rw [map_sub, map_smul]
    change u x - (u x / u v) * u v = 0
    rw [div_mul_cancel₀ _ huv, sub_self]
  have hall (x y : Fin n → K) : dotProduct x (A.mulVec y) = 0 := by
    obtain ⟨x',hx',hxe⟩ := hdecomp x
    obtain ⟨y',hy',hye⟩ := hdecomp y
    rw [hxe,hye,Matrix.mulVec_add,Matrix.mulVec_smul,hv,smul_zero,add_zero,
      add_dotProduct,smul_dotProduct,hzero x' y' hx' hy',hleft,smul_zero,add_zero]
  ext i j
  simpa [Matrix.mulVec,dotProduct,Pi.single_apply] using hall (Pi.single i 1) (Pi.single j 1)

/-- Vanishing of the literal restricted matrix is the corresponding
bilinear vanishing on its image. -/
theorem dot_eq_zero_of_restriction_zero
    {K : Type*} [Field K] {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (B : Matrix (Fin n) (Fin m) K)
    (hzero : B.transpose * A * B = 0) (x y : Fin m → K) :
    dotProduct (B.mulVec x) (A.mulVec (B.mulVec y)) = 0 := by
  rw [dotProduct_comm,Matrix.dotProduct_mulVec,← Matrix.mulVec_transpose,
    Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,hzero,Matrix.zero_mulVec,zero_dotProduct]

/-- The actual generic normal coefficients embed injectively in the
algebraic closure of their fraction field. -/
theorem parameterMap_injective (k : Type*) [Field k] (m n : ℕ) :
    Function.Injective (parameterMap k m n) := by
  let B := ParameterRing k m n
  let L := FractionRing B
  have he : parameterMap k m n = (algebraMap L (GenericField k m n)).comp
      (algebraMap B L) := IsScalarTower.algebraMap_eq B L (GenericField k m n)
  rw [he]
  exact (algebraMap L _).injective.comp (IsFractionRing.injective B L)

/-- Any vertex of a frame spanning the literal generic hyperplane maps
into the original cubic's actual Hessian kernel. This is the geometric
content of generic preservation of nonconicality. -/
theorem generic_section_vertex_maps_to_ambient_vertex
    {k : Type*} [Field k] [CharZero k] {n : ℕ}
    (F : MvPolynomial (Fin (n+1)) k) (hF : F.IsHomogeneous 3)
    (B : Matrix (Fin (n+1)) (Fin n) (GenericField k 1 (n+1)))
    (hB : Function.Injective B.mulVec)
    (hγB : genericNormal k 1 (n+1) * B = 0)
    (y : Fin n → GenericField k 1 (n+1))
    (hy : hessian (restrict B (map (algebraMap k (GenericField k 1 (n+1))) F)) y = 0) :
    hessian (map (algebraMap k (GenericField k 1 (n+1))) F) (B.mulVec y) = 0 := by
  classical
  let E := GenericField k 1 (n+1)
  let G := map (algebraMap k E) F
  let γ := genericNormal k 1 (n+1)
  let x := B.mulVec y
  change hessian (restrict B G) y = 0 at hy
  by_cases hx : x = 0
  · change hessian G x = 0
    rw [hx]
    exact (hessianLinearMap G (hF.map _)).map_zero
  have h2 : (2 : E) ≠ 0 := by norm_num
  have h3 : (3 : E) ≠ 0 := by norm_num
  have hhom : (restrict B G).IsHomogeneous 3 := homogeneous_restrict B G (hF.map _)
  have hGy : eval y (restrict B G) = 0 :=
    eval_eq_zero_of_mem_affineVertex _ hhom h2 h3 hy
  have hgradGy : ∀ j, eval y (pderiv j (restrict B G)) = 0 := by
    intro j
    have he := congrFun (hessian_mulVec_self hhom y) j
    have hz : (2 : E) * gradient (restrict B G) y j = 0 := by
      simpa only [hy,Matrix.zero_mulVec,Pi.zero_apply,Pi.smul_apply,nsmul_eq_mul] using he.symm
    exact (mul_eq_zero.mp hz).resolve_left h2
  have hxF : aeval x F = 0 := by
    change eval₂ (algebraMap k E) x F = 0
    rw [eval₂_eq_eval_map]
    exact (eval_restrict B G y).symm.trans hGy
  have hxγ : γ.mulVec x = 0 := by
    change γ.mulVec (B.mulVec y) = 0
    rw [Matrix.mulVec_mulVec,hγB,Matrix.zero_mulVec]
  have hcritical : (ProjectiveLinearSectionJacobian.augmentedSectionJacobian G γ x).rank ≠ 1+1 := by
    intro hr
    have hz := ProjectiveLinearSectionJacobian.augmentedSectionJacobian_mul_eq_zero
      G γ B hγB y hgradGy
    have hsum := Matrix.rank_add_rank_le_card_of_mul_eq_zero hz
    have hb := ProjectiveLinearSectionJacobian.frame_rank B hB
    change (ProjectiveLinearSectionJacobian.augmentedSectionJacobian G γ x).rank + B.rank ≤ _ at hsum
    rw [hr,hb,Fintype.card_fin] at hsum
    omega
  have hsing := generic_critical_implies_original_singular F x hx hxF hxγ hcritical
  obtain ⟨b,hb⟩ : ∃ b, x b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  let D := parameterPartial k 1 (n+1) (finProdFinEquiv (0,b))
  let v : Fin (n+1) → E := fun i => D (x i)
  let u := GenericHyperplaneFrameKernel.normal (γ 0)
  have huv : u v = -x b := by
    have hrow : ∑ c, γ 0 c * x c = 0 := congrFun hxγ 0
    have hd := congrArg D hrow
    simp only [map_sum,Derivation.leibniz,smul_eq_mul,map_zero,Finset.sum_add_distrib,
      D,γ,parameterPartial_genericNormal] at hd
    change (∑ c, γ 0 c * D (x c)) = -x b
    simpa [D,γ] using eq_neg_of_add_eq_zero_left hd
  have hMv : (hessian G x).mulVec v = 0 := by
    ext i
    have he := derivation_aeval D x (pderiv i F)
    rw [hsing i,map_zero] at he
    simpa only [G,hessian,hessianPolynomial,Matrix.mulVec,dotProduct,pderiv_map,
      eval_map,aeval_def,v,Pi.zero_apply] using he.symm
  have hu0 : γ 0 0 ≠ 0 :=
    (map_ne_zero_iff _ (parameterMap_injective k 1 (n+1))).mpr (X_ne_zero _)
  have hrange := GenericHyperplaneFrameKernel.range_eq_ker (γ 0) hu0 B hB
    (fun j => congrFun (congrFun hγB 0) j)
  have hmatrix : B.transpose * hessian G x * B = 0 := by
    rw [← hessian_restrict]
    exact hy
  apply symmetric_matrix_eq_zero_of_hyperplane_and_kernel (hessian G x)
    (hessian_symmetric G x) u ?_ v (by rw [huv]; exact neg_ne_zero.mpr hb) hMv
  intro a c ha hc
  have har : a ∈ LinearMap.range B.mulVecLin := by rw [hrange]; exact ha
  have hcr : c ∈ LinearMap.range B.mulVecLin := by rw [hrange]; exact hc
  obtain ⟨a,rfl⟩ := har
  obtain ⟨c,rfl⟩ := hcr
  exact dot_eq_zero_of_restriction_zero (hessian G x) B hmatrix a c

/-- Generic hyperplane restriction retains triviality of the actual vertex. -/
theorem generic_section_vertex_eq_bot
    {k : Type*} [Field k] [CharZero k] {n : ℕ}
    (F : MvPolynomial (Fin (n+1)) k) (hF : F.IsHomogeneous 3)
    (hnoncone : GeometricallyNonconicalCubic F)
    (B : Matrix (Fin (n+1)) (Fin n) (GenericField k 1 (n+1)))
    (hB : Function.Injective B.mulVec)
    (hγB : genericNormal k 1 (n+1) * B = 0) :
    affineVertex (restrict B (map (algebraMap k (GenericField k 1 (n+1))) F))
      (homogeneous_restrict B _ (hF.map _)) = ⊥ := by
  have hbar : affineVertex (map (algebraMap k (AlgebraicClosure k)) F) (hF.map _) = ⊥ := by
    apply bot_unique
    intro v hv
    exact (geometricallyNonconicalCubic_iff_hessian F hF (by norm_num) (by norm_num)).mp
      hnoncone v hv
  have hbase := (affineVertex_baseChange_eq_bot_iff (L := AlgebraicClosure k) F hF).mp hbar
  have hgeneric := (affineVertex_baseChange_eq_bot_iff
    (L := GenericField k 1 (n+1)) F hF).mpr hbase
  apply bot_unique
  intro y hy
  have hx := generic_section_vertex_maps_to_ambient_vertex F hF B hB hγB y hy
  have hm : B.mulVec y ∈ affineVertex
      (map (algebraMap k (GenericField k 1 (n+1))) F) (hF.map _) := hx
  rw [hgeneric] at hm
  exact hB (by simpa only [Matrix.mulVec_zero] using hm)

/-- Nonconicality is geometric, including all further scalar directions. -/
theorem generic_section_geometricallyNonconical
    {k : Type*} [Field k] [CharZero k] {n : ℕ}
    (F : MvPolynomial (Fin (n+1)) k) (hF : F.IsHomogeneous 3)
    (hnoncone : GeometricallyNonconicalCubic F)
    (B : Matrix (Fin (n+1)) (Fin n) (GenericField k 1 (n+1)))
    (hB : Function.Injective B.mulVec)
    (hγB : genericNormal k 1 (n+1) * B = 0) :
    GeometricallyNonconicalCubic
      (restrict B (map (algebraMap k (GenericField k 1 (n+1))) F)) := by
  let G := restrict B (map (algebraMap k (GenericField k 1 (n+1))) F)
  have hG : G.IsHomogeneous 3 := homogeneous_restrict B _ (hF.map _)
  have hbot := generic_section_vertex_eq_bot F hF hnoncone B hB hγB
  have hbar := (affineVertex_baseChange_eq_bot_iff
    (L := AlgebraicClosure (GenericField k 1 (n+1))) G hG).mpr hbot
  apply (geometricallyNonconicalCubic_iff_hessian G hG (by norm_num) (by norm_num)).mpr
  intro v hv
  have hm : v ∈ affineVertex (map (algebraMap _ _) G) (hG.map _) := hv
  rwa [hbar] at hm

/-- An actual kernel frame is constructed from the independent normal
parameters. Thus no frame-existence or generic nonconicality input is supplied. -/
theorem exists_generic_nonconical_frame
    {k : Type*} [Field k] [CharZero k] {n : ℕ}
    (F : MvPolynomial (Fin (n+1)) k) (hF : F.IsHomogeneous 3)
    (hnoncone : GeometricallyNonconicalCubic F) :
    ∃ B : Matrix (Fin (n+1)) (Fin n) (GenericField k 1 (n+1)),
      Function.Injective B.mulVec ∧ genericNormal k 1 (n+1) * B = 0 ∧
      LinearMap.range B.mulVecLin = LinearMap.ker
        (GenericHyperplaneFrameKernel.normal (genericNormal k 1 (n+1) 0)) ∧
      GeometricallyNonconicalCubic
        (restrict B (map (algebraMap k (GenericField k 1 (n+1))) F)) := by
  classical
  let u := genericNormal k 1 (n+1) 0
  let B := GenericHyperplaneFrameOpen.chartFrame u (1 : Matrix (Fin n) (Fin n) _)
  have hu0 : u 0 ≠ 0 :=
    (map_ne_zero_iff _ (parameterMap_injective k 1 (n+1))).mpr (X_ne_zero _)
  have hB : Function.Injective B.mulVec := by
    intro y z h
    ext i
    have he := congrFun h i.succ
    have he' : u 0 * y i = u 0 * z i := by
      simpa [B,GenericHyperplaneFrameOpen.chartFrame,Matrix.mulVec,dotProduct,
        Matrix.one_apply] using he
    exact mul_left_cancel₀ hu0 he'
  have hcol (j : Fin n) : ∑ i, u i * B i j = 0 := by
    rw [Fin.sum_univ_succ]
    simp [B,GenericHyperplaneFrameOpen.chartFrame,Matrix.one_apply,mul_comm]
  have hγB : genericNormal k 1 (n+1) * B = 0 := by
    ext a j
    have ha : a = 0 := Subsingleton.elim _ _
    subst a
    exact hcol j
  exact ⟨B,hB,hγB,GenericHyperplaneFrameKernel.range_eq_ker u hu0 B hB hcol,
    generic_section_geometricallyNonconical F hF hnoncone B hB hγB⟩

end CubicTenVariables.GenericNonconicalHyperplane

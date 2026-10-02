import CubicTenVariables.Literature.FiberGeometricIntegralitySpreading
import CubicTenVariables.GeometryTen
import HessianTheorem11.BibleHyperplanes
import HessianTheorem11.UnconditionalCutDimension
import HessianTheorem11.MatrixRankMinors

/-! All actual hyperplane restrictions of the ten-variable cubic are integral
in every sufficiently large characteristic. The sole literature premise is
the generic geometric-integrality spreading corollary. A universal rectangular
frame gives polynomial parameters without denominators. The finite cover uses
all ordered maximal minors; redundant charts do not change the conclusion. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

noncomputable section
namespace CubicTenVariables.ReducedHyperplaneIntegrality
open MvPolynomial HessianTheorem11 Matrix Module PolynomialRestriction
open scoped BigOperators

abbrev Parameters (n m : ℕ) := Fin n × Fin m
abbrev MinorIndex (n m : ℕ) := (Fin m → Fin n) × (Fin m → Fin m)

/-- The entries of the actual hyperplane frame are independent parameters. -/
def universalFrame {n m : ℕ} : Matrix (Fin n) (Fin m) (MvPolynomial (Parameters n m) ℤ) :=
  fun i j => X (i,j)

/-- The literal original cubic restricted to the universal frame. -/
def family {n m : ℕ} (F : MvPolynomial (Fin n) ℤ) :
    MvPolynomial (Fin m) (MvPolynomial (Parameters n m) ℤ) :=
  restrict universalFrame (map C F)

/-- A principal parameter open on which the frame is injective. -/
def minorPolynomial {n m : ℕ} (j : MinorIndex n m) : MvPolynomial (Parameters n m) ℤ :=
  (universalFrame.submatrix j.1 j.2).det

theorem specialize_family {n m : ℕ} {K : Type*} [CommRing K]
    (F : MvPolynomial (Fin n) ℤ) (v : Parameters n m → K) :
    map (eval₂Hom (Int.castRingHom K) v) (family F) =
      restrict (fun i j => v (i,j)) (map (Int.castRingHom K) F) := by
  have hc : (eval₂Hom (Int.castRingHom K) v).comp
      (C : ℤ →+* MvPolynomial (Parameters n m) ℤ) = Int.castRingHom K :=
    RingHom.ext_int _ _
  rw [family, map_restrict, MvPolynomial.map_map, hc]
  congr 1
  ext i j
  exact eval₂Hom_X' _ _ _

theorem evaluate_minor {n m : ℕ} {K : Type*} [CommRing K]
    (j : MinorIndex n m) (v : Parameters n m → K) :
    eval₂ (Int.castRingHom K) v (minorPolynomial j) =
      (Matrix.submatrix (fun i k => v (i,k)) j.1 j.2).det := by
  change (eval₂Hom (Int.castRingHom K) v) (universalFrame.submatrix j.1 j.2).det = _
  rw [RingHom.map_det]
  congr 1
  ext i k
  exact eval₂Hom_X' _ _ _

theorem family_ideal {n m : ℕ} {K : Type*} [CommRing K]
    (F : MvPolynomial (Fin n) ℤ) (v : Parameters n m → K) :
    Literature.integralityFiberIdeal (fun _ : Unit => family F) K v =
      Ideal.span {restrict (fun i j => v (i,j)) (map (Int.castRingHom K) F)} := by
  simp only [Literature.integralityFiberIdeal, specialize_family, Set.range_const]

/-- Nonvanishing of an actual maximal minor forces injectivity. -/
theorem injective_of_minor {n m : ℕ} {K : Type*} [Field K]
    (B : Matrix (Fin n) (Fin m) K) (j : MinorIndex n m)
    (hj : (B.submatrix j.1 j.2).det ≠ 0) : Function.Injective B.mulVec := by
  have hl : m ≤ B.rank := MatrixRankMinors.minor_size_le_rank B j.1 j.2 hj
  have hh := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  change B.rank + finrank K (LinearMap.ker B.mulVecLin) = _ at hh
  simp only [Module.finrank_pi, Fintype.card_fin] at hh
  have hk : finrank K (LinearMap.ker B.mulVecLin)=0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)

/-- The characteristic-zero hypothesis needed by spreading is proved from
rational anisotropy, not supplied as a geometric-integrality premise. -/
theorem geometric_section_isDomain
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (B : Matrix (Fin 10) (Fin 9) GeometricField) (hB : Function.Injective B.mulVec) :
    IsDomain (MvPolynomial (Fin 9) GeometricField ⧸
      Ideal.span {restrict B (map (Int.castRingHom GeometricField) F)}) := by
  let A : AnisotropicCubic 10 := ⟨map (Int.castRingHom ℚ) F,hF.map _,hA⟩
  have hgeom : geometricPolynomial A.polynomial =
      map (Int.castRingHom GeometricField) F := by
    unfold geometricPolynomial
    change map (algebraMap ℚ GeometricField) (map (Int.castRingHom ℚ) F) = _
    rw [MvPolynomial.map_map, RingHom.ext_int ((algebraMap ℚ GeometricField).comp
      (Int.castRingHom ℚ)) (Int.castRingHom GeometricField)]
  have hs : affineDimension (BibleHyperplanes.singularCone
      (map (Int.castRingHom GeometricField) F)) ≤ (5 : Dimension) := by
    simpa only [singularDimension,singularLocus,BibleHyperplanes.singularCone,hgeom] using
      Geometry.singularDimension_le_five A
  have hi := BibleHyperplanes.section_irreducible
    UnconditionalCutDimension.homogeneousCutDimensionInput Unconditional.genericRankOpen
    B hB (map (Int.castRingHom GeometricField) F) (hF.map _) hs (by norm_num : 5+3<9)
  letI : (Ideal.span {restrict B (map (Int.castRingHom GeometricField) F)}).IsPrime :=
    (Ideal.span_singleton_prime hi.ne_zero).mpr hi.prime
  infer_instance

/-- A finite cover by maximal-minor principal opens spreads integrality for
all injective frames simultaneously. The generic hypothesis is discharged
for the actual ten-variable cubic in the endpoint below. -/
theorem exists_uniform_bound_of_geometric_sections
    (spread : Literature.FiberGeometricIntegralitySpreading)
    {n m : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hgeo : ∀ B : Matrix (Fin n) (Fin m) GeometricField,
      Function.Injective B.mulVec → IsDomain (MvPolynomial (Fin m) GeometricField ⧸
        Ideal.span {restrict B (map (Int.castRingHom GeometricField) F)})) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, p.Prime → ¬p∣D →
      ∀ (K : Type) [Field K] [IsAlgClosed K] [CharP K p]
      (B : Matrix (Fin n) (Fin m) K), Function.Injective B.mulVec →
        IsDomain (MvPolynomial (Fin m) K ⧸
          Ideal.span {restrict B (map (Int.castRingHom K) F)}) := by
  classical
  letI : Fintype (MinorIndex n m) := Fintype.ofFinite (MinorIndex n m)
  have hchart (j : MinorIndex n m) := spread (Parameters n m) (Fin m) Unit
    (fun _ => family F) (minorPolynomial j) (by
      intro v hv
      rw [family_ideal]
      apply hgeo
      apply injective_of_minor _ j
      rw [evaluate_minor] at hv
      exact hv)
  choose D hD hgood using hchart
  refine ⟨∏ j, D j,?_,?_⟩
  · exact Finset.prod_pos (fun j _ => lt_of_lt_of_le Nat.zero_lt_one (hD j))
  · intro p hp hpD K _ _ _ B hB
    have hr : B.rank=m := by
      change finrank K (LinearMap.range B.mulVecLin)=m
      rw [LinearMap.finrank_range_of_inj hB]
      simp
    have hminor := MatrixRankMinors.exists_rank_minor B
    rw [hr] at hminor
    obtain ⟨rows,cols,hdet⟩ := hminor
    have hpj : ¬p∣D (rows,cols) := fun hd => hpD (hd.trans
      (Finset.dvd_prod_of_mem D (Finset.mem_univ (rows,cols))))
    have hm := hgood (rows,cols) p hp hpj K (fun ij => B ij.1 ij.2)
      (by rw [evaluate_minor]; exact hdet)
    rw [family_ideal] at hm
    exact hm

/-- One exceptional integer works for every actual injective hyperplane frame
and every algebraically closed field in all remaining characteristics. -/
theorem exists_uniform_bound
    (spread : Literature.FiberGeometricIntegralitySpreading)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, p.Prime → ¬p∣D →
      ∀ (K : Type) [Field K] [IsAlgClosed K] [CharP K p]
      (B : Matrix (Fin 10) (Fin 9) K), Function.Injective B.mulVec →
        IsDomain (MvPolynomial (Fin 9) K ⧸
          Ideal.span {restrict B (map (Int.castRingHom K) F)}) :=
  exists_uniform_bound_of_geometric_sections spread F (geometric_section_isDomain F hF hA)

/-- The ambient affine cubic cone is geometrically integral in characteristic
zero, with the same original integer coefficients. -/
theorem geometric_ambient_isDomain
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    IsDomain (MvPolynomial (Fin 10) GeometricField ⧸
      Ideal.span {map (Int.castRingHom GeometricField) F}) := by
  let A : AnisotropicCubic 10 := ⟨map (Int.castRingHom ℚ) F,hF.map _,hA⟩
  have hi := Unconditional.cubicGeometricIrreducibility A (by norm_num)
  have hgeom : geometricPolynomial A.polynomial =
      map (Int.castRingHom GeometricField) F := by
    unfold geometricPolynomial
    change map (algebraMap ℚ GeometricField) (map (Int.castRingHom ℚ) F) = _
    rw [MvPolynomial.map_map, RingHom.ext_int ((algebraMap ℚ GeometricField).comp
      (Int.castRingHom ℚ)) (Int.castRingHom GeometricField)]
  rw [hgeom] at hi
  letI : (Ideal.span {map (Int.castRingHom GeometricField) F}).IsPrime :=
    (Ideal.span_singleton_prime hi.ne_zero).mpr hi.prime
  infer_instance

/-- Constant families have their literal original coefficient reductions. -/
theorem constant_family_ideal {K : Type*} [CommRing K]
    (F : MvPolynomial (Fin 10) ℤ) (v : Fin 0 → K) :
    Literature.integralityFiberIdeal
      (fun _ : Unit => map (C : ℤ →+* MvPolynomial (Fin 0) ℤ) F) K v =
        Ideal.span {map (Int.castRingHom K) F} := by
  have hc : (eval₂Hom (Int.castRingHom K) v).comp C = Int.castRingHom K := by
    ext a
    exact eval₂Hom_C _ _ _
  simp only [Literature.integralityFiberIdeal, MvPolynomial.map_map,hc,Set.range_const]

/-- A separate fixed exceptional integer also gives integrality of the
ambient reduced cubic over every algebraically closed characteristic-p field. -/
theorem exists_uniform_ambient_bound
    (spread : Literature.FiberGeometricIntegralitySpreading)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, p.Prime → ¬p∣D →
      ∀ (K : Type) [Field K] [IsAlgClosed K] [CharP K p],
        IsDomain (MvPolynomial (Fin 10) K ⧸ Ideal.span {map (Int.castRingHom K) F}) := by
  obtain ⟨D,hD,hgood⟩ := spread (Fin 0) (Fin 10) Unit
    (fun _ => map (C : ℤ →+* MvPolynomial (Fin 0) ℤ) F) 1 (by
      intro v _hv
      rw [constant_family_ideal]
      exact geometric_ambient_isDomain F hF hA)
  refine ⟨D,hD,?_⟩
  intro p hp hpD K _ _ _
  have h := hgood p hp hpD K (fun i => Fin.elim0 i) (by simp)
  rw [constant_family_ideal] at h
  exact h

end CubicTenVariables.ReducedHyperplaneIntegrality

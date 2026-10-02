import CubicTenVariables.ReducedHyperplaneIntegrality
import CubicTenVariables.CubicPrincipalOpenUniform

/-! The actual ten-variable ambient cubic and every injective hyperplane
restriction are integral in all sufficiently large characteristics, proved
using finite cubic factor equations instead of general spreading inputs. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
noncomputable section
namespace CubicTenVariables.ReducedHyperplaneIntegralityProved
open MvPolynomial HessianTheorem11 Matrix Module PolynomialRestriction
open ReducedHyperplaneIntegrality
open scoped BigOperators

/-- The previously proved singular-locus bound gives literal irreducibility,
including nonvanishing, of each characteristic-zero hyperplane equation. -/
theorem geometric_section_irreducible
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (B : Matrix (Fin 10) (Fin 9) GeometricField) (hB : Function.Injective B.mulVec) :
    Irreducible (restrict B (map (Int.castRingHom GeometricField) F)) := by
  let A : AnisotropicCubic 10 := ⟨map (Int.castRingHom ℚ) F, hF.map _, hA⟩
  have hgeom : geometricPolynomial A.polynomial =
      map (Int.castRingHom GeometricField) F := by
    unfold geometricPolynomial
    change map (algebraMap ℚ GeometricField) (map (Int.castRingHom ℚ) F) = _
    rw [MvPolynomial.map_map, RingHom.ext_int ((algebraMap ℚ GeometricField).comp
      (Int.castRingHom ℚ)) (Int.castRingHom GeometricField)]
  have hs : affineDimension (BibleHyperplanes.singularCone
      (map (Int.castRingHom GeometricField) F)) ≤ (5 : Dimension) := by
    simpa only [singularDimension, singularLocus, BibleHyperplanes.singularCone, hgeom] using
      Geometry.singularDimension_le_five A
  exact BibleHyperplanes.section_irreducible
    UnconditionalCutDimension.homogeneousCutDimensionInput Unconditional.genericRankOpen
    B hB (map (Int.castRingHom GeometricField) F) (hF.map _) hs (by norm_num : 5 + 3 < 9)

/-- The finite maximal-minor cover uses only the internally proved cubic
principal-open statement. -/
theorem exists_uniform_bound_of_geometric_sections
    (spread : CubicPrincipalOpenUniform.Uniform)
    {n m : ℕ} (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hgeo : ∀ B : Matrix (Fin n) (Fin m) GeometricField,
      Function.Injective B.mulVec →
        (restrict B (map (Int.castRingHom GeometricField) F)).totalDegree = 3 ∧
        IsDomain (MvPolynomial (Fin m) GeometricField ⧸
          Ideal.span {restrict B (map (Int.castRingHom GeometricField) F)})) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ D →
      ∀ (K : Type) [Field K] [IsAlgClosed K] [CharP K p]
      (B : Matrix (Fin n) (Fin m) K), Function.Injective B.mulVec →
        IsDomain (MvPolynomial (Fin m) K ⧸
          Ideal.span {restrict B (map (Int.castRingHom K) F)}) := by
  classical
  letI : Fintype (MinorIndex n m) := Fintype.ofFinite _
  have hfamily : (family (m := m) F).IsHomogeneous 3 :=
    homogeneous_restrict universalFrame _ (hF.map C)
  have hchart (j : MinorIndex n m) := spread (Parameters n m) m (family F)
    hfamily (minorPolynomial j) (by
      intro v hv
      rw [specialize_family]
      have hB : Function.Injective (Matrix.mulVec (fun i k => v (i, k))) := by
        apply injective_of_minor _ j
        rw [← evaluate_minor]
        exact hv
      exact hgeo _ hB)
  choose D hD hgood using hchart
  refine ⟨∏ j, D j, Finset.one_le_prod' (fun j _ => hD j), ?_⟩
  intro p _ hpD K _ _ _ B hB
  have hr : B.rank = m := by
    change finrank K (LinearMap.range B.mulVecLin) = m
    rw [LinearMap.finrank_range_of_inj hB]
    simp
  have hminor := MatrixRankMinors.exists_rank_minor B
  rw [hr] at hminor
  obtain ⟨rows, cols, hdet⟩ := hminor
  have hpj : ¬ p ∣ D (rows, cols) := fun hd => hpD (hd.trans
    (Finset.dvd_prod_of_mem D (Finset.mem_univ (rows, cols))))
  have hopen : eval₂ (Int.castRingHom K) (fun ij => B ij.1 ij.2)
      (minorPolynomial (rows, cols)) ≠ 0 := by
    rw [evaluate_minor]
    exact hdet
  have hm := hgood (rows, cols) p hpj K (fun ij => B ij.1 ij.2) hopen
  rw [ReducedHyperplaneIntegrality.specialize_family] at hm
  exact hm

/-- All required characteristic-zero geometric hypotheses are proved for
the actual anisotropic ten-variable cubic. -/
theorem exists_uniform_bound_of_uniform
    (spread : CubicPrincipalOpenUniform.Uniform)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ D →
      ∀ (K : Type) [Field K] [IsAlgClosed K] [CharP K p]
      (B : Matrix (Fin 10) (Fin 9) K), Function.Injective B.mulVec →
        IsDomain (MvPolynomial (Fin 9) K ⧸
          Ideal.span {restrict B (map (Int.castRingHom K) F)}) :=
  exists_uniform_bound_of_geometric_sections spread F hF (fun B hB =>
    ⟨(homogeneous_restrict _ _ (hF.map _)).totalDegree
      (geometric_section_irreducible F hF hA B hB).ne_zero,
      geometric_section_isDomain F hF hA B hB⟩)

/-- The ambient cubic has the same literal geometric irreducibility used
by the established characteristic-zero geometry. -/
theorem geometric_ambient_irreducible
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    Irreducible (map (Int.castRingHom GeometricField) F) := by
  let A : AnisotropicCubic 10 := ⟨map (Int.castRingHom ℚ) F, hF.map _, hA⟩
  have hi := Unconditional.cubicGeometricIrreducibility A (by norm_num)
  have hc : (algebraMap ℚ GeometricField).comp (Int.castRingHom ℚ) =
      Int.castRingHom GeometricField := RingHom.ext_int _ _
  simpa only [geometricPolynomial, A, MvPolynomial.map_map, hc] using hi

/-- One integer also gives integrality of the ambient reduced cubic. -/
theorem exists_uniform_ambient_bound_of_uniform
    (spread : CubicPrincipalOpenUniform.Uniform)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ D →
      ∀ (K : Type) [Field K] [IsAlgClosed K] [CharP K p],
        IsDomain (MvPolynomial (Fin 10) K ⧸ Ideal.span {map (Int.castRingHom K) F}) := by
  let G := map (C : ℤ →+* MvPolynomial (Fin 0) ℤ) F
  have he (K : Type) [Field K] (v : Fin 0 → K) :
      map (eval₂Hom (Int.castRingHom K) v) G = map (Int.castRingHom K) F := by
    have hc : (eval₂Hom (Int.castRingHom K) v).comp C = Int.castRingHom K := by
      ext a
      exact eval₂Hom_C _ _ _
    simp only [G, MvPolynomial.map_map, hc]
  obtain ⟨D, hD, hgood⟩ := spread (Fin 0) 10 G (hF.map C) 1 (by
    intro v _
    rw [he]
    exact ⟨(hF.map _).totalDegree (geometric_ambient_irreducible F hF hA).ne_zero,
      geometric_ambient_isDomain F hF hA⟩)
  refine ⟨D, hD, ?_⟩
  intro p _ hpD K _ _ _
  have hh := hgood p hpD K (fun i => Fin.elim0 i) (by simp)
  rw [he] at hh
  exact hh

/-- Unconditional integrality for all actual injective hyperplane frames. -/
theorem exists_uniform_bound
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ D →
      ∀ (K : Type) [Field K] [IsAlgClosed K] [CharP K p]
      (B : Matrix (Fin 10) (Fin 9) K), Function.Injective B.mulVec →
        IsDomain (MvPolynomial (Fin 9) K ⧸
          Ideal.span {restrict B (map (Int.castRingHom K) F)}) :=
  exists_uniform_bound_of_uniform CubicPrincipalOpenUniform.proved F hF hA

/-- Unconditional integrality for the actual ambient cubic. -/
theorem exists_uniform_ambient_bound
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ D →
      ∀ (K : Type) [Field K] [IsAlgClosed K] [CharP K p],
        IsDomain (MvPolynomial (Fin 10) K ⧸ Ideal.span {map (Int.castRingHom K) F}) :=
  exists_uniform_ambient_bound_of_uniform CubicPrincipalOpenUniform.proved F hF hA

end CubicTenVariables.ReducedHyperplaneIntegralityProved

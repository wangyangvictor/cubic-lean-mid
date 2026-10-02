import HessianTheorem11.SingularExceptionalComponent
import HessianTheorem11.AffineOpenSets
import HessianTheorem11.KernelAnnihilatorGeometry
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-! Derived replacements for the assembled cone-point and cone-cover inputs.
The point selection is a consequence of the already retained generic smooth
rank open; finite decomposition is supplied by mathlib's minimal-prime theorem. -/
noncomputable section
namespace HessianTheorem11.ReducedInputs
open MvPolynomial Module

/-- GP is derived from the existing general generic-rank-open theorem.
Avoidance, nonzero choice, and the radial tangent are proved, not assumed. -/
theorem genericConePointSelection (GR : GenericRankOpenInput) :
    GenericConePointSelectionInput where
  select Z hZ hi hc hn M q := by
    classical
    obtain ⟨G⟩ := GR.choose Z hZ hi q M
    obtain ⟨z, hz, hz0⟩ : ∃ z ∈ Z, z ≠ 0 := by
      simpa only [Set.subset_def, Set.mem_singleton_iff, not_forall, exists_prop] using hn
    obtain ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hz0 (funext h)
    have hxj : (X j : GeometricPolynomial _) ∉ vanishingIdeal GeometricField Z := by
      intro hh
      exact hj (by simpa using hh z hz)
    obtain ⟨P, hP, hdetect⟩ : ∃ P : GeometricPolynomial _,
        P ∉ vanishingIdeal GeometricField Z ∧
        (∀ x, eval x P ≠ 0 → x ∈ finiteEquationZeroSet q → Z ⊆ finiteEquationZeroSet q) := by
      by_cases hq : Z ⊆ finiteEquationZeroSet q
      · exact ⟨1, by intro hh; have he := hh z hz; simpa using he, fun _ _ _ => hq⟩
      · obtain ⟨w, hw, hqw⟩ : ∃ w ∈ Z, ∃ i, eval w (q i) ≠ 0 := by
          simpa only [Set.subset_def, finiteEquationZeroSet, Set.mem_setOf_eq,
            not_forall, exists_prop] using hq
        obtain ⟨i, hiw⟩ := hqw
        exact ⟨q i, fun hh => hiw (hh w hw), fun x hx hqx => (hx (hqx i)).elim⟩
    have hprod : X j * P ∉ vanishingIdeal GeometricField Z := by
      intro hh
      exact (hi.mem_or_mem hh).elim hxj hP
    have hp : ∃ x ∈ Z, eval x (X j * P) ≠ 0 := by
      by_contra hh
      push_neg at hh
      exact hprod hh
    obtain ⟨x, hx, he⟩ := exists_on_dense_set_eval_ne_zero G.dense (X j * P) hp
    have hxj' : x j ≠ 0 := by
      intro hh
      apply he
      simp [hh]
    have hxP : eval x P ≠ 0 := by
      intro hh
      apply he
      simp [hh]
    refine ⟨{
      point := x
      member := G.subset hx
      nonzero := fun hh => hxj' (congrFun hh j)
      dimension := G.dimension_base.trans (congrArg (fun d : ℕ => (d : Dimension)) (G.smooth x hx).symm)
      radial := hc.radial_tangent x (G.subset hx)
      rank_maximal := G.maximal_rank x hx
      detects_equations := hdetect x hxP }⟩

/-- Actual finite irreducible decomposition from the proved Noetherian
minimal-prime theorem and the proved Nullstellensatz. -/
theorem finite_components {n : ℕ} (Z : Set (GeometricPoint n))
    (hZ : AlgebraicallyClosedSet Z) :
    ∃ (c : ℕ) (C : Fin c → Set (GeometricPoint n)),
      Z = ⋃ i, C i ∧ ∀ i, IsIrreducibleComponent Z (C i) := by
  classical
  let I := vanishingIdeal GeometricField Z
  let T := I.minimalPrimes
  have hT : T.Finite := I.finite_minimalPrimes_of_isNoetherianRing
  letI : Fintype T := hT.fintype
  let e := (Fintype.equivFin T).symm
  let C (i : Fin (Fintype.card T)) := zeroLocus GeometricField (e i).val
  have hc (i) : IsIrreducibleComponent Z (C i) := by
    have hp := (e i).property
    letI : (e i).val.IsPrime := hp.1.1
    have hv : vanishingIdeal GeometricField (C i) = (e i).val :=
      MvPolynomial.IsPrime.vanishingIdeal_zeroLocus _
    refine ⟨algebraicallyClosedSet_zeroLocus _, ?_, ?_, ?_⟩
    · change (vanishingIdeal GeometricField (C i)).IsPrime
      rw [hv]
      infer_instance
    · intro x hx
      have hx' : x ∈ geometricClosure Z := fun p hp' => hx p (hp.1.2 hp')
      rwa [hZ] at hx'
    · intro W hW hiW hCW hWZ
      have hle : vanishingIdeal GeometricField W ≤ (e i).val := by
        rw [← hv]
        exact vanishingIdeal_anti_mono hCW
      have hI : I ≤ vanishingIdeal GeometricField W := vanishingIdeal_anti_mono hWZ
      have heq := le_antisymm (hp.2 ⟨hiW, hI⟩ hle) hle
      change W = zeroLocus GeometricField (e i).val
      rw [heq]
      exact hW.symm
  refine ⟨Fintype.card T, C, ?_, hc⟩
  ext x
  constructor
  · intro hx
    let J := RingHom.ker (eval x : GeometricPolynomial n →+* GeometricField)
    letI : J.IsPrime := RingHom.ker_isPrime _
    have hIJ : I ≤ J := fun p hp => hp x hx
    obtain ⟨p, hp, hpJ⟩ := Ideal.exists_minimalPrimes_le hIJ
    obtain ⟨i, hi⟩ := e.surjective ⟨p, hp⟩
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    change x ∈ zeroLocus GeometricField (e i).val
    rw [hi]
    exact fun q hq => hpJ hq
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact (hc i).subset hi

/-- QC is assembled from actual finite components and the derived common
smooth rank-open point. No independent finite quadratic cover is assumed. -/
theorem finiteQuadraticConeCover (AC : AffineComponentsInput)
    (GR : GenericRankOpenInput) : FiniteQuadraticConeCoverInput where
  cover q hq M := by
    classical
    let GP := genericConePointSelection GR
    have hz := finiteEquationZeroSet_closed q
    have hcone := finiteQuadraticZeroSet_cone q hq
    obtain ⟨c, C, hC, hc⟩ := finite_components (finiteEquationZeroSet q) hz
    have hx : ∀ i : Fin c, ∃ x : GeometricPoint _,
        C i ⊆ {0} ∨ (x ≠ 0 ∧ x ∈ C i ∧
          affineDimension (C i) = (finrank GeometricField (affineTangentSpace (C i) x) : Dimension) ∧
          x ∈ affineTangentSpace (C i) x ∧ ∀ y ∈ C i, (M y).rank ≤ (M x).rank) := by
      intro i
      by_cases hi : C i ⊆ {0}
      · exact ⟨0, Or.inl hi⟩
      · obtain ⟨D⟩ := GP.select (C i) (hc i).closed (hc i).irreducible
          ((hc i).isAffineCone AC hz hcone) hi M q
        exact ⟨D.point, Or.inr ⟨D.nonzero, D.member, D.dimension, D.radial, D.rank_maximal⟩⟩
    choose point hp using hx
    exact ⟨{
      count := c
      component := C
      point := point
      covers := hC
      component_property := hp }⟩

end HessianTheorem11.ReducedInputs

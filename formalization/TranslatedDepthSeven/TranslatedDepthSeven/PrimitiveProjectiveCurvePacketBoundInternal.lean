import TranslatedDepthSeven.PrimitiveProjectiveCurvePacketInternal
import TranslatedDepthSeven.PrimitiveProjectiveCurveBezoutInternal
import TranslatedDepthSeven.PrimitiveProjectiveCurveThreshold

/-! The full primitive-vector packet bound on a smooth projective residue
class, with actual polynomial zeros and without a residue-disc premise. -/
namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 3000000

private theorem eval_map_intCast_projective {N : ℕ}
    (x : Fin N → ℤ) (P : MvPolynomial (Fin N) ℤ) :
    eval (fun i ↦ (x i : ℚ)) (P.map (Int.castRingHom ℚ)) = (eval x P : ℚ) := by
  rw [eval_map]
  exact (eval₂_comp (Int.castRingHom ℚ) x P).symm

/-- Every smooth projective residue class in the first chart contains at
most 2d² primitive integral zeros of height B once p>4B. Both signs count. -/
theorem card_primitivePlaneCurve_firstChartPacket_le
    {d B p : ℕ} (hd : 2 ≤ d) (hB : 1 ≤ B) (hp : p.Prime)
    (P : MvPolynomial (Fin 3) ℤ) (hPhom : P.IsHomogeneous d)
    (hPirred : Irreducible (P.map (Int.castRingHom ℚ)))
    (S : Finset (Fin 3 → ℤ))
    (hprimitive : ∀ z ∈ S, IsPrimitiveIntVector z)
    (hPzero : ∀ z ∈ S, eval z P = 0)
    (hchart : ∀ z ∈ S, (z 0 : ZMod p) ≠ 0)
    (center : Fin 2 → ℤ)
    (hcenter : (eval center (planeCurveFirstChartDehomogenize P) : ZMod p) = 0)
    (hcong : ∀ z ∈ S, ∀ i, (z i.succ : ZMod p) =
      (z 0 : ZMod p) * (center i : ZMod p))
    (v : Fin 2)
    (hpartial : (eval center (pderiv v (planeCurveFirstChartDehomogenize P)) : ZMod p) ≠ 0)
    (hbox : ∀ z ∈ S, ∀ i, (z i).natAbs ≤ B)
    (hlarge : 4 * B < p) : S.card ≤ 2 * d ^ 2 := by
  classical
  let Pq := P.map (Int.castRingHom ℚ)
  let I : Ideal (MvPolynomial (Fin 3) ℚ) := Ideal.span {Pq}
  have hPne : P ≠ 0 := by
    intro h
    subst P
    exact hPirred.ne_zero rfl
  have hI : I.IsPrime := (Ideal.span_singleton_prime hPirred.ne_zero).mpr hPirred.prime
  have hIhom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) ℚ) := by
    apply Ideal.homogeneous_span
    intro f hf
    have hfP : f = Pq := Set.mem_singleton_iff.mp hf
    exact ⟨d, hfP.symm ▸ hPhom.map (Int.castRingHom ℚ)⟩
  have hdegree : HasProjectiveDimensionDegree I 1 d :=
    hasProjectiveDimensionDegree_principal_homogeneous Pq (hPhom.map _)
      hPirred.ne_zero (by omega) hI
  have hIzero : ∀ z ∈ S, (fun i ↦ (z i : ℚ)) ∈ affineIdealZeroLocus I := by
    intro z hz
    rw [mem_affineIdealZeroLocus_iff_le_ker_aeval, Ideal.span_le]
    intro f hf
    have hfP : f = Pq := Set.mem_singleton_iff.mp hf
    subst f
    change eval (fun i ↦ (z i : ℚ)) (P.map (Int.castRingHom ℚ)) = 0
    rw [eval_map_intCast_projective, hPzero z hz, Int.cast_zero]
  obtain ⟨F, hFind, hFhom, hFbox⟩ := exists_planeCurveDegreeMonomialBlock_internal P hPhom hPne
  let s := salbergerCurveMonomialCount d
  let x : Fin S.card → Fin 3 → ℤ := fun j ↦ (S.equivFin.symm j).1
  have hE : 0 < affineLineJetWeight s := by
    have hs : 2 ≤ s := salbergerCurveMonomialCount_two_le (by omega)
    have he := two_mul_affineLineJetWeight s
    have hprod := Nat.mul_le_mul hs (show 1 ≤ s - 1 by omega)
    omega
  have hdetlarge := primitivePlaneCurve_determinant_size_of_linear_threshold hd hB hlarge
  have haux : ∃ G : MvPolynomial (Fin 3) ℚ,
      G.IsHomogeneous d ∧ G ∉ I ∧ ∀ j, eval (fun i ↦ (x j i : ℚ)) G = 0 := by
    apply exists_auxiliaryHomogeneousPolynomial_of_all_evaluation_minors_eq_zero
      I (fun i ↦ (F i).map (Int.castRingHom ℚ))
        (fun j i ↦ (x j i : ℚ)) hFind (fun i ↦ (hFhom i).map _)
    intro cols _hcols
    let V : Matrix (Fin s) (Fin s) ℤ := Matrix.of (fun i j ↦ eval (x (cols j)) (F i))
    have hdiv : (p : ℤ) ^ affineLineJetWeight s ∣ V.det := by
      have hdvd := projectivePlaneCurve_evaluation_det_dvd hp
        (by simpa only [Fintype.card_fin] using hE) P hPhom
        (fun j ↦ x (cols j))
        (fun j ↦ hPzero _ (S.equivFin.symm (cols j)).2)
        (fun j ↦ hchart _ (S.equivFin.symm (cols j)).2)
        center hcenter (fun j i ↦ hcong _ (S.equivFin.symm (cols j)).2 i)
        v hpartial F hFhom
      simpa only [Fintype.card_fin] using hdvd
    have hbound : V.det.natAbs ≤ s.factorial * B ^ (d * s) := by
      have h := det_natAbs_le_factorial_mul_prod_column_bounds V.transpose
        (fun _ ↦ B ^ d) (fun i j ↦ hFbox B (x (cols i))
          (hbox _ (S.equivFin.symm (cols i)).2) j)
      simpa only [Matrix.det_transpose, Fintype.card_fin, Finset.prod_const,
        Finset.card_univ, ← pow_mul] using h
    have hzero : V.det = 0 :=
      TangentMinors.eq_zero_of_dvd_of_natAbs_lt hdiv (by
        simpa only [Int.natAbs_pow, Int.natAbs_natCast] using hbound.trans_lt hdetlarge)
    have heq : (Matrix.of (fun i j ↦ eval (fun a ↦ (x j a : ℚ))
        ((F i).map (Int.castRingHom ℚ)))).submatrix id cols =
          (Int.castRingHom ℚ).mapMatrix V := by
      ext i j
      exact eval_map_intCast_projective (x (cols j)) (F i)
    rw [heq, ← RingHom.map_det, hzero, map_zero]
  obtain ⟨G, hGhom, hGI, hGzero⟩ := haux
  have hSzero : ∀ z ∈ S, eval (fun i ↦ (z i : ℚ)) G = 0 := by
    intro z hz
    have h := hGzero (S.equivFin ⟨z, hz⟩)
    simpa only [x, Equiv.symm_apply_apply] using h
  have hchartZ : ∀ z ∈ S, z 0 ≠ 0 := by
    intro z hz heq
    exact hchart z hz (by rw [heq, Int.cast_zero])
  simpa only [pow_two] using card_primitiveFirstChart_curve_auxiliary_le
    I hI hIhom hdegree G hGhom hGI S hprimitive hchartZ hIzero hSzero

end
end TranslatedDepthSeven

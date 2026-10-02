import TranslatedDepthSeven.QbarDistinctCurveFirstChartBezoutInternal

/-!
# Degree-bounded homogeneous separators on every projective chart

A coordinate permutation reduces an arbitrary nonzero exterior point to
the first affine chart.  Multiplying the resulting equation by a power
of a nonvanishing coordinate puts all separators in the same degree.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

/-- Coordinate permutations preserve the complete projective degree
certificate, over any field. -/
theorem hasProjectiveDimensionDegree_map_renameEquiv_over
    {K : Type*} [Field K] {N r d : ℕ}
    (e : Equiv.Perm (Fin (N + 1)))
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hI : HasProjectiveDimensionDegree I r d) :
    HasProjectiveDimensionDegree (I.map (renameEquiv K e)) r d := by
  rcases hI with ⟨hdim, hd, P, hPdegree, hPlc, k₀, heventual⟩
  refine ⟨?_, hd, P, hPdegree, hPlc, k₀, ?_⟩
  · rw [← ringKrullDim_eq_of_ringEquiv (renameQuotientAlgEquiv K e I).toRingEquiv]
    exact hdim
  · intro k hk
    have heq := finrank_quotientHomogeneousComponent_map_renameEquiv K e I k
    change Module.finrank K (projectiveHilbertPiece K N I k) =
      Module.finrank K
        (projectiveHilbertPiece K N (I.map (renameEquiv K e)) k) at heq
    rw [← heq]
    exact heventual k hk

/-- Every nonzero exterior point is separated by a homogeneous equation
whose degree is at most the projective degree. -/
theorem exists_homogeneous_projectiveDegree_separator_at_nonzeroPoint
    {K : Type*} [Field K] [CharZero K] {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hIprime : I.IsPrime)
    (hIhom : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (hdegree : HasProjectiveDimensionDegree I r d)
    (x : Fin (N + 1) → K) (hx : x ≠ 0)
    (hexterior : ∃ f ∈ I, eval x f ≠ 0) :
    ∃ (k : ℕ) (G : MvPolynomial (Fin (N + 1)) K),
      k ≤ d ∧ G.IsHomogeneous k ∧ G ∈ I ∧ eval x G ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  let e : Equiv.Perm (Fin (N + 1)) := Equiv.swap 0 i
  let E := renameEquiv K e
  let J := I.map E
  let x' : Fin (N + 1) → K := x ∘ e.symm
  let z : Fin (N + 1) → K := fun j ↦ (x i)⁻¹ * x' j
  have hz0 : z 0 = 1 := by simp [z, x', e, hi]
  have heval (f : MvPolynomial (Fin (N + 1)) K) :
      eval x' (E f) = eval x f := by
    change eval x' (rename e f) = _
    rw [eval_rename]
    have hpoint : x' ∘ e = x := by
      funext j
      simp [x']
    rw [hpoint]
  letI : I.IsPrime := hIprime
  have hJprime : J.IsPrime := by dsimp only [J, E]; infer_instance
  have hJhom : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) :=
    map_renameEquiv_isHomogeneous e I hIhom
  have hJdegree : HasProjectiveDimensionDegree J r d :=
    hasProjectiveDimensionDegree_map_renameEquiv_over e I hdegree
  have hnotle : ¬ I ≤ RingHom.ker (eval x) := by
    intro h
    obtain ⟨f, hf, hfx⟩ := hexterior
    exact hfx (h hf)
  obtain ⟨k, f, hfhom, hfI, hfx⟩ :=
    exists_homogeneous_form_mem_not_mem_of_not_le
      (RingHom.ker (eval x)) I hIhom hnotle
  have hJexterior : ∃ g ∈ J, eval z g ≠ 0 := by
    refine ⟨E f, Ideal.mem_map_of_mem E hfI, ?_⟩
    change eval (fun j ↦ (x i)⁻¹ * x' j) (E f) ≠ 0
    rw [eval_smul_of_isHomogeneous (E f) x' (x i)⁻¹ k
      (show (E f).IsHomogeneous k from hfhom.rename_isHomogeneous), heval]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hi)) hfx
  obtain ⟨l, H, hld, hHhom, hHJ, hHz⟩ :=
    exists_homogeneous_projectiveDegree_separator_at_firstChartPoint
      J hJprime hJhom hJdegree z hz0 hJexterior
  let G := E.symm H
  have hGI : G ∈ I := by
    exact (Ideal.symm_apply_mem_of_equiv_iff (f := E.toRingEquiv)).2 hHJ
  refine ⟨l, G, hld, hHhom.rename_isHomogeneous, hGI, ?_⟩
  have hHx' : eval x' H ≠ 0 := by
    intro hzero
    have hscaled := eval_smul_of_isHomogeneous H x' (x i)⁻¹ l hHhom
    change eval z H = _ at hscaled
    rw [hHz, hzero, mul_zero] at hscaled
    exact one_ne_zero hscaled
  have h : eval x' H = eval x G := by simpa only [G, AlgEquiv.apply_symm_apply] using heval G
  exact h ▸ hHx'

/-- Every nonzero exterior point is separated by an equation in exactly
the projective degree.  This allows one common finite-dimensional space
of equations, with dimension `choose (N+d) d`. -/
theorem exists_exact_projectiveDegree_separator_at_nonzeroPoint
    {K : Type*} [Field K] [CharZero K] {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hIprime : I.IsPrime)
    (hIhom : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (hdegree : HasProjectiveDimensionDegree I r d)
    (x : Fin (N + 1) → K) (hx : x ≠ 0)
    (hexterior : ∃ f ∈ I, eval x f ≠ 0) :
    ∃ G : MvPolynomial (Fin (N + 1)) K,
      G.IsHomogeneous d ∧ G ∈ I ∧ eval x G ≠ 0 := by
  classical
  obtain ⟨k, G, hkd, hGhom, hGI, hGx⟩ :=
    exists_homogeneous_projectiveDegree_separator_at_nonzeroPoint
      I hIprime hIhom hdegree x hx hexterior
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  refine ⟨X i ^ (d - k) * G, ?_, I.mul_mem_left _ hGI, ?_⟩
  · have hhom := ((isHomogeneous_X K i).pow (d - k)).mul hGhom
    simpa only [one_mul, Nat.sub_add_cancel hkd] using hhom
  · simpa only [map_mul, map_pow, eval_X] using
      mul_ne_zero (pow_ne_zero _ hi) hGx

end

end TranslatedDepthSeven

import HessianTheorem11.PolynomialAnnihilatorMatrix
import HessianTheorem11.PolynomialKernelBundleGeometry
import HessianTheorem11.ReducedGenericRank

/-! The successive kernel-annihilator package is derived from the retained
ordinary kernel-bundle theorem. Actual maximal minors provide one dense
principal open, and the polynomial equations are linearized by their graph.
No new geometric or cubic-specific hypothesis is introduced. -/
noncomputable section
namespace HessianTheorem11.ReducedKernelAnnihilator
open MvPolynomial Matrix Module ReducedDeterminantal KernelAnnihilatorProjector
set_option maxHeartbeats 1200000

theorem ker_reindex_rows {K α β γ : Type*} [Field K]
    [Fintype α] [Fintype β] [Fintype γ]
    (A : Matrix α β K) (e : γ ≃ α) :
    LinearMap.ker (A.submatrix e id).mulVecLin = LinearMap.ker A.mulVecLin := by
  ext v
  constructor
  · intro hv
    ext i
    simpa [Matrix.mulVec, dotProduct] using congrFun hv (e.symm i)
  · intro hv
    ext i
    exact congrFun hv (e i)

/-- The complete former KA input, with only the previously retained ordinary
constant-rank kernel-bundle theorem as an input. -/
theorem kernelAnnihilatorGeometry (KI : KernelBundleInput) :
    KernelAnnihilatorGeometryInput where
  choose {n a b c} U hU hi M N P hP := by
    classical
    let I := vanishingIdeal GeometricField U
    letI : I.IsPrime := hi
    let PM := pencilPolynomial M
    let r := genericMatrixRank I PM
    obtain ⟨rows,cols,hminor⟩ := MatrixRankMinors.exists_rank_minor (genericMatrix I PM)
    let q : GeometricPolynomial n := (PM.submatrix rows cols).det
    have hq : q ∉ I := by
      intro hq
      apply hminor
      have he : genericPointMap I q = 0 :=
        (ReducedGenericRank.genericPointMap_eq_zero_iff I q).mpr hq
      have hd := (genericPointMap I).map_det (PM.submatrix rows cols)
      exact hd.symm.trans he
    have hPM (x : GeometricPoint n) : PM.map (eval x) = M x := by
      ext i j
      exact eval_pencilPolynomial M x i j
    have heq (x : GeometricPoint n) : eval x q = ((M x).submatrix rows cols).det := by
      have hh := (eval x).map_det (PM.submatrix rows cols)
      change eval x q = ((PM.map (eval x)).submatrix rows cols).det at hh
      rwa [hPM] at hh
    have hUzero : U = zeroLocus GeometricField I := hU.symm
    have hMbound (x : GeometricPoint n) (hx : x ∈ U) : (M x).rank ≤ r := by
      have hh := ReducedGenericRank.specialization_le I PM x (hUzero ▸ hx)
      change (PM.map (eval x)).rank ≤ r at hh
      rwa [hPM] at hh
    let ρ := Fin a ⊕ (Fin b × Fin c)
    let e : Fin (Fintype.card ρ) ≃ ρ := (Fintype.equivFin ρ).symm
    let PA := annihilatorPolynomialMatrix M N rows cols
    let A : Matrix (Fin (Fintype.card ρ)) (Fin b) (GeometricPolynomial n) :=
      PA.submatrix e id
    have hker (x : GeometricPoint n) (hx : x ∈ U) (hqx : eval x q ≠ 0) :
        LinearMap.ker (A.map (eval x)).mulVecLin = kernelAnnihilator M N x := by
      change LinearMap.ker ((PA.map (eval x)).submatrix e id).mulVecLin = _
      rw [ker_reindex_rows, eval_annihilatorPolynomialMatrix]
      exact ker_annihilatorMatrix M N rows cols x (heq x ▸ hqx) (hMbound x hx)
    obtain ⟨s,hs,hsrank⟩ := ReducedGenericRank.principal_open I A
    have hPnot : P ∉ I := by
      intro hh
      obtain ⟨x,hx,hPx⟩ := hP
      exact hPx (hh x hx)
    let Q := P*q*s
    have hQ : Q ∉ I := by
      intro hh
      rcases hi.mem_or_mem hh with hh | hh
      · exact (hi.mem_or_mem hh).elim hPnot hq
      · exact hs hh
    let O : Set (GeometricPoint n) := {x | x ∈ U ∧ eval x Q ≠ 0}
    have hO : RelativelyOpenSet U O := by
      refine ⟨zeroLocus GeometricField (Ideal.span {Q}), algebraicallyClosedSet_zeroLocus _, ?_⟩
      ext x
      simp [O, zeroLocus_span, Set.mem_diff]
    have hne : O.Nonempty := by
      obtain ⟨x,hx,hQx⟩ := exists_zeroLocus_eval_ne_zero I Q hQ
      exact ⟨x,hUzero.symm ▸ hx,hQx⟩
    have hdense := hO.dense_of_nonempty hU hi hne
    have havoid (x : GeometricPoint n) (hx : x ∈ O) :
        eval x P ≠ 0 ∧ eval x q ≠ 0 ∧ eval x s ≠ 0 := by
      have hh := hx.2
      change eval x (P*q*s) ≠ 0 at hh
      simpa only [map_mul, mul_ne_zero_iff, and_assoc] using hh
    let ell := b - genericMatrixRank I A
    have hnullA (x : GeometricPoint n) (hx : x ∈ O) :
        finrank GeometricField (LinearMap.ker (A.map (eval x)).mulVecLin) = ell := by
      have hr := hsrank x (hUzero ▸ hx.1) (havoid x hx).2.2
      have hd := (A.map (eval x)).mulVecLin.finrank_range_add_finrank_ker
      change (A.map (eval x)).rank + _ = _ at hd
      change (A.map (eval x)).rank = genericMatrixRank I A at hr
      simp only [Module.finrank_pi, Fintype.card_fin] at hd
      dsimp [ell]
      omega
    have hbundle : PolynomialKernelBundle.bundle A O = kernelAnnihilatorBundle M N O := by
      ext p
      change (pairLeft p ∈ O ∧ (A.map (eval (pairLeft p))).mulVec (pairRight p) = 0) ↔ _
      by_cases hp : pairLeft p ∈ O
      · have hk := hker (pairLeft p) hp.1 (havoid _ hp).2.1
        change (pairLeft p ∈ O ∧ pairRight p ∈ LinearMap.ker
          (A.map (eval (pairLeft p))).mulVecLin) ↔ _
        rw [hk]
        rfl
      · simp [kernelAnnihilatorBundle, hp]
    refine ⟨{
      openSet := O
      isOpen := hO
      subset := fun x hx => hx.1
      dense := hdense
      nonempty := hne
      avoids := fun x hx => (havoid x hx).1
      nullity := ell
      dimension_kernel := ?_
      maximal_rank := ?_
      bundle_irreducible := ?_
      bundle_locally_closed := ?_
      bundle_dimension := ?_ }⟩
    · intro x hx
      rw [← hker x hx.1 (havoid x hx).2.1]
      exact hnullA x hx
    · intro x hx y hy
      have hl := MatrixRankMinors.minor_size_le_rank (M x) rows cols
        (heq x ▸ (havoid x hx).2.1)
      exact (hMbound y hy).trans hl
    · rw [← hbundle]
      exact PolynomialKernelBundle.bundle_irreducible KI A U O hU hi hO hdense ell hnullA
    · rw [← hbundle]
      exact PolynomialKernelBundle.bundle_locally_closed A U O hU hO
    · intro t ht
      rw [← hbundle]
      exact PolynomialKernelBundle.bundle_dimension KI A U O hU hi hO hdense t ell ht hnullA

end HessianTheorem11.ReducedKernelAnnihilator

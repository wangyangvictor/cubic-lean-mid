import TranslatedDepthSeven.TangentMinors
import TranslatedDepthSeven.TangentTaylor
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
# From tangent minors to a rational affine packet plane

This file completes the elementary implication in the last sentence of the
tangent-minor lemma.  It contains no geometric or counting interface.  Its
inputs are integral polynomial equations, their evaluated Jacobian matrices,
an exact common-modulus factorization of point differences, and an explicit
integer size inequality.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators

namespace TangentPacketSpan

/-- The elementary archimedean determinant bound used after tangent-minor
divisibility.  The constant is explicit: the determinant of a `k x k`
integer matrix whose entries have absolute value at most `M` has absolute
value at most `k! M^k`. -/
theorem det_natAbs_le_factorial_mul_pow {k M : ℕ}
    (A : Matrix (Fin k) (Fin k) ℤ)
    (hentry : ∀ i j, (A i j).natAbs ≤ M) :
    A.det.natAbs ≤ k.factorial * M ^ k := by
  have hentryZ : ∀ i j, |A i j| ≤ (M : ℤ) := by
    intro i j
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hentry i j
  have h := Matrix.det_le (A := A)
    (abv := (AbsoluteValue.abs : AbsoluteValue ℤ ℤ))
    (x := (M : ℤ)) hentryZ
  simp only [Fintype.card_fin, nsmul_eq_mul] at h
  have h' : |A.det| ≤ (k.factorial : ℤ) * (M : ℤ) ^ k := h
  rw [Int.abs_eq_natAbs] at h'
  exact_mod_cast h'

/-- A square matrix over `ℚ` with linearly independent rows has nonzero
determinant. -/
theorem det_ne_zero_of_linearIndependent_rows {k : ℕ}
    (A : Matrix (Fin k) (Fin k) ℚ)
    (hA : LinearIndependent ℚ A.row) : A.det ≠ 0 := by
  classical
  let b : Module.Basis (Fin k) ℚ (Fin k → ℚ) :=
    basisOfPiSpaceOfLinearIndependent hA
  have hu := Module.Basis.isUnit_det (Pi.basisFun ℚ (Fin k)) b
  have hb : (b : Fin k → Fin k → ℚ) = A.row :=
    coe_basisOfPiSpaceOfLinearIndependent hA
  rw [Pi.basisFun_det_apply, hb] at hu
  exact hu.ne_zero

/-- From `k` linearly independent rows in `ℚ^N`, select `k` distinct
coordinates on which they still form a nonsingular square matrix. -/
theorem exists_selectedMinor_ne_zero_of_linearIndependent_rows {k N : ℕ}
    (A : Matrix (Fin k) (Fin N) ℚ)
    (hA : LinearIndependent ℚ A.row) :
    ∃ cols : Fin k → Fin N, Function.Injective cols ∧
      (A.submatrix id cols).det ≠ 0 := by
  classical
  have hrank : A.rank = k := by
    exact hA.rank_matrix.trans (Fintype.card_fin k)
  have hfinrank : Module.finrank ℚ
      (Submodule.span ℚ (Set.range A.col)) = k := by
    rw [← Matrix.rank_eq_finrank_span_cols, hrank]
  obtain ⟨f, hfmem, _, hfindep⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range A.col)
  let e : Fin k ≃ Fin (Module.finrank ℚ
      (Submodule.span ℚ (Set.range A.col))) :=
    Equiv.cast (congrArg Fin hfinrank.symm)
  let f' : Fin k → (Fin k → ℚ) := fun i ↦ f (e i)
  have hf'mem : ∀ i, f' i ∈ Set.range A.col := fun i ↦ hfmem (e i)
  let cols : Fin k → Fin N := fun i ↦ Classical.choose (hf'mem i)
  have hcols : ∀ i, A.col (cols i) = f' i :=
    fun i ↦ Classical.choose_spec (hf'mem i)
  have hf'indep : LinearIndependent ℚ f' := hfindep.comp e e.injective
  have hcolsInj : Function.Injective cols := by
    intro i j hij
    apply hf'indep.injective
    rw [← hcols i, ← hcols j, hij]
  refine ⟨cols, hcolsInj, ?_⟩
  rw [← Matrix.det_transpose]
  apply det_ne_zero_of_linearIndependent_rows
  have htransRows : (Matrix.transpose (A.submatrix id cols)).row = f' := by
    funext i j
    change A j (cols i) = f' i j
    exact congrFun (hcols i) j
  rw [htransRows]
  exact hf'indep

/-- If the span of a family of rational vectors has dimension at least `k`,
then `k` members and `k` coordinates give a nonzero selected minor. -/
theorem exists_nonzero_minor_of_finrank_span_ge {k N : ℕ}
    {ι : Type*} (v : ι → Fin N → ℚ)
    (hlarge : k ≤ Module.finrank ℚ
      (Submodule.span ℚ (Set.range v))) :
    ∃ rows : Fin k → ι, ∃ cols : Fin k → Fin N,
      Function.Injective rows ∧ Function.Injective cols ∧
      Matrix.det (Matrix.of (fun i j ↦ v (rows i) (cols j))) ≠ 0 := by
  classical
  obtain ⟨f, hfmem, _, hfindep⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range v)
  let inc : Fin k → Fin (Module.finrank ℚ
      (Submodule.span ℚ (Set.range v))) := Fin.castLE hlarge
  let f' : Fin k → (Fin N → ℚ) := fun i ↦ f (inc i)
  have hf'mem : ∀ i, f' i ∈ Set.range v := fun i ↦ hfmem (inc i)
  let rows : Fin k → ι := fun i ↦ Classical.choose (hf'mem i)
  have hrows : ∀ i, v (rows i) = f' i :=
    fun i ↦ Classical.choose_spec (hf'mem i)
  have hf'indep : LinearIndependent ℚ f' :=
    hfindep.comp inc (Fin.castLE_injective hlarge)
  have hrowsInj : Function.Injective rows := by
    intro i j hij
    apply hf'indep.injective
    rw [← hrows i, ← hrows j, hij]
  let A : Matrix (Fin k) (Fin N) ℚ := fun i j ↦ v (rows i) j
  have hA : LinearIndependent ℚ A.row := by
    have hArows : A.row = f' := by
      funext i j
      simp [A, hrows]
    rw [hArows]
    exact hf'indep
  obtain ⟨cols, hcolsInj, hminor⟩ :=
    exists_selectedMinor_ne_zero_of_linearIndependent_rows A hA
  refine ⟨rows, cols, hrowsInj, hcolsInj, ?_⟩
  simpa [A] using hminor

/-- Vanishing of every selected `k`-minor forces the rational row span to
have dimension strictly smaller than `k`. -/
theorem finrank_span_lt_of_all_minors_zero {k N : ℕ}
    {ι : Type*} (v : ι → Fin N → ℚ)
    (hzero : ∀ (rows : Fin k → ι) (cols : Fin k → Fin N),
      Matrix.det (Matrix.of (fun i j ↦ v (rows i) (cols j))) = 0) :
    Module.finrank ℚ (Submodule.span ℚ (Set.range v)) < k := by
  by_contra hnot
  have hlarge : k ≤ Module.finrank ℚ
      (Submodule.span ℚ (Set.range v)) := Nat.le_of_not_gt hnot
  obtain ⟨rows, cols, _, _, hminor⟩ :=
    exists_nonzero_minor_of_finrank_span_ge v hlarge
  exact hminor (hzero rows cols)

/-- If every row of `Z` lies in the kernel of a Jacobian matrix of rank at
least `N-d`, then `Z` has rank at most `d`.  This is the precise rank-nullity
calculation used after the Taylor congruence. -/
theorem rank_le_of_jacobian_mul_transpose_eq_zero
    {K : Type*} [Field K] {r N k d : ℕ}
    (J : Matrix (Fin r) (Fin N) K) (Z : Matrix (Fin k) (Fin N) K)
    (hJ : N - d ≤ J.rank) (hzero : J * Matrix.transpose Z = 0) :
    Z.rank ≤ d := by
  have hrank := Matrix.rank_add_rank_le_card_of_mul_eq_zero hzero
  rw [Matrix.rank_transpose, Fintype.card_fin] at hrank
  omega

/-- **Concrete tangent-packet span theorem.**

The family `eqs` is an explicit list of integral equations.  All points
`y i` are common integral zeros, and their differences from `y i₀` are
exactly `q * z i`.  At every prime factor of the square-free modulus, the
displayed evaluated Jacobian has rank at least `N-d`.  If the explicit
integer inequality `k! M^k < q^(2k-d)` holds, the rational span of all point
differences has dimension strictly smaller than `k`.
-/
theorem packet_affineDifferenceSpan_finrank_lt
    {ι : Type*} {N r k d q M : ℕ}
    (eqs : Fin r → MvPolynomial (Fin N) ℤ)
    (y : ι → Fin N → ℤ) (i₀ : ι) (z : ι → Fin N → ℤ)
    (hqpos : 0 < q) (hqsf : Squarefree q)
    (hdk : d < k)
    (hzero : ∀ i f, MvPolynomial.eval (y i) (eqs f) = 0)
    (hdiff : ∀ i j, y i j - y i₀ j = (q : ℤ) * z i j)
    (hJac : ∀ p, p.Prime → p ∣ q →
      N - d ≤
        Matrix.rank (Matrix.of (fun f j ↦
          (MvPolynomial.eval (y i₀)
            (MvPolynomial.pderiv j (eqs f)) : ZMod p))))
    (hcoord : ∀ i j, (y i j - y i₀ j).natAbs ≤ M)
    (hlarge : k.factorial * M ^ k < q ^ (2 * k - d)) :
    Module.finrank ℚ
      (Submodule.span ℚ
        (Set.range fun i ↦ fun j ↦
          ((y i j - y i₀ j : ℤ) : ℚ))) < k := by
  let v : ι → Fin N → ℚ := fun i j ↦
    ((y i j - y i₀ j : ℤ) : ℚ)
  apply finrank_span_lt_of_all_minors_zero v
  intro rows cols
  let Y : Fin (k + 1) → Fin N → ℤ :=
    Fin.cases (y i₀) (fun i ↦ y (rows i))
  let Z : Matrix (Fin k) (Fin N) ℤ := fun i j ↦ z (rows i) j
  let B : Matrix (Fin k) (Fin k) ℤ :=
    (TangentMinors.differenceMatrix Y).submatrix id cols
  have hdiffYZ : ∀ i j,
      Y i.succ j - Y 0 j = (q : ℤ) * Z i j := by
    intro i j
    simpa [Y, Z] using hdiff (rows i) j
  have hrankZ : ∀ p, p.Prime → p ∣ q →
      (Z.map (Int.castRingHom (ZMod p))).rank ≤ d := by
    intro p hp hpq
    letI : Fact p.Prime := ⟨hp⟩
    let J : Matrix (Fin r) (Fin N) (ZMod p) := fun f j ↦
      (MvPolynomial.eval (y i₀)
        (MvPolynomial.pderiv j (eqs f)) : ZMod p)
    let Zp : Matrix (Fin k) (Fin N) (ZMod p) :=
      Z.map (Int.castRingHom (ZMod p))
    have hJZ : J * Matrix.transpose Zp = 0 := by
      ext f i
      have hyi : ∀ g,
          MvPolynomial.eval (fun j ↦ y i₀ j + (q : ℤ) * Z i j) (eqs g) = 0 := by
        intro g
        have heq : (fun j ↦ y i₀ j + (q : ℤ) * Z i j) = y (rows i) := by
          funext j
          have hij := hdiffYZ i j
          simp only [Y, Fin.cases_succ, Fin.cases_zero] at hij
          linarith
        rw [heq]
        exact hzero (rows i) g
      have htaylor := jacobian_zmod_of_two_zeros eqs (y i₀) (Z i)
        (q := (q : ℤ)) (by exact_mod_cast hqpos.ne')
        (by exact_mod_cast hpq) (hzero i₀) hyi f
      simpa [J, Zp, Matrix.mul_apply, dotProduct] using htaylor
    have hJrank : N - d ≤ J.rank := by
      simpa [J] using hJac p hp hpq
    have hZrank : Zp.rank ≤ d :=
      rank_le_of_jacobian_mul_transpose_eq_zero J Zp hJrank hJZ
    simpa [Zp] using hZrank
  have hdiv : (q : ℤ) ^ (2 * k - d) ∣ B.det := by
    have h := TangentMinors.selectedMinor_dvd_pow_two_mul_sub_of_squarefree_rank
      (Nat.le_of_lt hdk) hqsf Y Z hdiffYZ cols hrankZ
    simpa [B, TangentMinors.selectedMinor] using h
  have hBentry : ∀ i j, (B i j).natAbs ≤ M := by
    intro i j
    simpa [B, TangentMinors.differenceMatrix, Y] using
      hcoord (rows i) (cols j)
  have hBbound : B.det.natAbs ≤ k.factorial * M ^ k :=
    det_natAbs_le_factorial_mul_pow B hBentry
  have hqabs : ((q : ℤ) ^ (2 * k - d)).natAbs = q ^ (2 * k - d) := by
    simp [Int.natAbs_pow]
  have hBlt : B.det.natAbs < ((q : ℤ) ^ (2 * k - d)).natAbs := by
    rw [hqabs]
    exact hBbound.trans_lt hlarge
  have hBzero : B.det = 0 :=
    TangentMinors.eq_zero_of_dvd_of_natAbs_lt hdiv hBlt
  have hmap : (B.map (Int.castRingHom ℚ)).det = 0 := by
    have hm := (Int.castRingHom ℚ).map_det B
    rw [hBzero, map_zero] at hm
    exact hm.symm
  have hmatrix : B.map (Int.castRingHom ℚ) =
      Matrix.of (fun i j ↦ v (rows i) (cols j)) := by
    ext i j
    simp [B, TangentMinors.differenceMatrix, Y, v]
  rw [hmatrix] at hmap
  exact hmap

/-- Literal rational affine-subspace form of
`packet_affineDifferenceSpan_finrank_lt`. -/
theorem exists_affineSubspace_of_tangent_packet
    {ι : Type*} {N r k d q M : ℕ}
    (eqs : Fin r → MvPolynomial (Fin N) ℤ)
    (y : ι → Fin N → ℤ) (i₀ : ι) (z : ι → Fin N → ℤ)
    (hqpos : 0 < q) (hqsf : Squarefree q)
    (hdk : d < k)
    (hzero : ∀ i f, MvPolynomial.eval (y i) (eqs f) = 0)
    (hdiff : ∀ i j, y i j - y i₀ j = (q : ℤ) * z i j)
    (hJac : ∀ p, p.Prime → p ∣ q →
      N - d ≤
        Matrix.rank (Matrix.of (fun f j ↦
          (MvPolynomial.eval (y i₀)
            (MvPolynomial.pderiv j (eqs f)) : ZMod p))))
    (hcoord : ∀ i j, (y i j - y i₀ j).natAbs ≤ M)
    (hlarge : k.factorial * M ^ k < q ^ (2 * k - d)) :
    ∃ A : AffineSubspace ℚ (Fin N → ℚ),
      Module.finrank ℚ A.direction < k ∧
      ∀ i, (fun j ↦ (y i j : ℚ)) ∈ A := by
  let v : ι → Fin N → ℚ := fun i j ↦
    ((y i j - y i₀ j : ℤ) : ℚ)
  let P : Submodule ℚ (Fin N → ℚ) :=
    Submodule.span ℚ (Set.range v)
  let base : Fin N → ℚ := fun j ↦ (y i₀ j : ℚ)
  let A : AffineSubspace ℚ (Fin N → ℚ) := AffineSubspace.mk' base P
  refine ⟨A, ?_, ?_⟩
  · have hspan := packet_affineDifferenceSpan_finrank_lt eqs y i₀ z
      hqpos hqsf hdk hzero hdiff hJac hcoord hlarge
    rw [show A.direction = P from AffineSubspace.direction_mk' base P]
    simpa [P, v] using hspan
  · intro i
    rw [show A = AffineSubspace.mk' base P by rfl,
      AffineSubspace.mem_mk']
    have hv : v i ∈ P := by
      apply Submodule.subset_span
      exact Set.mem_range_self i
    simpa [P, v, base, Pi.vsub_apply] using hv

end TangentPacketSpan

end

end TranslatedDepthSeven

import HessianTheorem11.HessianDeterminant
import HessianTheorem11.MatrixRankMinors

/-!
# Actual equations of translated Hessian rank loci

A constant matrix changes every positive-size minor of a linear matrix only
in lower degree. The finite equations below encode the entire translated
rank locus, with no cubic-zero or symmetry restriction on the translating matrix.
-/

noncomputable section
namespace CubicTenVariables.TranslatedHessianMinors
open MvPolynomial HessianTheorem11
open scoped BigOperators

variable {R S σ : Type*} [CommRing R] [CommRing S]

/-- A finite product of affine-linear polynomials has the expected degree bound. -/
theorem totalDegree_prod_add_C_le {ι : Type*} (s : Finset ι)
    (g : ι → MvPolynomial σ R) (t : ι → R)
    (hg : ∀ i ∈ s, (g i).totalDegree ≤ 1) :
    (∏ i ∈ s, (g i + C (t i))).totalDegree ≤ s.card := by
  refine (totalDegree_finset_prod s (fun i => g i + C (t i))).trans ?_
  calc
    (∑ i ∈ s, (g i + C (t i)).totalDegree) ≤ ∑ _i ∈ s, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact (totalDegree_add (g i) (C (t i))).trans
        (max_le (hg i hi) (by rw [totalDegree_C]; exact Nat.zero_le 1))
    _ = s.card := by simp

/-- The top-degree part of a nonempty product is unchanged by constant shifts. -/
theorem totalDegree_prod_add_C_sub_lt {ι : Type*} (s : Finset ι)
    (g : ι → MvPolynomial σ R) (t : ι → R)
    (hg : ∀ i ∈ s, (g i).totalDegree ≤ 1) (hs : s.Nonempty) :
    ((∏ i ∈ s, (g i + C (t i))) - ∏ i ∈ s, g i).totalDegree < s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    by_cases he : s = ∅
    · subst s
      simp
    · have hsn : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
      have hgs : ∀ i ∈ s, (g i).totalDegree ≤ 1 := fun i hi => hg i (by simp [hi])
      have hd := ih hgs hsn
      have hp := totalDegree_prod_add_C_le s g t hgs
      have hid :
          (g a + C (t a)) * (∏ i ∈ s, (g i + C (t i))) - g a * (∏ i ∈ s, g i) =
          g a * ((∏ i ∈ s, (g i + C (t i))) - ∏ i ∈ s, g i) +
            C (t a) * (∏ i ∈ s, (g i + C (t i))) := by ring
      rw [hid]
      apply lt_of_le_of_lt (totalDegree_add _ _)
      apply max_lt
      · apply lt_of_le_of_lt (totalDegree_mul _ _)
        have hga := hg a (Finset.mem_insert_self a s)
        omega
      · apply lt_of_le_of_lt (totalDegree_mul _ _)
        simp only [totalDegree_C, zero_add]
        omega

/-- The lower-degree difference of actual determinants, over any commutative ring. -/
theorem totalDegree_det_add_C_sub_lt {k : ℕ}
    (B : Matrix (Fin k) (Fin k) (MvPolynomial σ R)) (T : Matrix (Fin k) (Fin k) R)
    (hB : ∀ i j, (B i j).totalDegree ≤ 1) (hk : 0 < k) :
    ((B + T.map C).det - B.det).totalDegree < k := by
  classical
  rw [Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
  apply lt_of_le_of_lt (totalDegree_finsetSum_le (d := k-1) ?_) (by omega)
  intro e _
  rw [← smul_sub]
  apply le_trans (totalDegree_smul_le _ _)
  have h := totalDegree_prod_add_C_sub_lt (Finset.univ : Finset (Fin k))
    (fun i => B (e i) i) (fun i => T (e i) i) (fun i _ => hB (e i) i)
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩)
  simpa only [Matrix.add_apply, Matrix.map_apply, Finset.card_univ, Fintype.card_fin]
    using Nat.le_sub_one_of_lt h

variable {n k : ℕ}

/-- A literal polynomial minor; repeated row or column choices are allowed. -/
def minor (B : Matrix (Fin n) (Fin n) (MvPolynomial σ R))
    (rows cols : Fin k → Fin n) : MvPolynomial σ R := (B.submatrix rows cols).det

/-- The corresponding minor after an arbitrary constant matrix translation. -/
def translatedMinor (B : Matrix (Fin n) (Fin n) (MvPolynomial σ R))
    (T : Matrix (Fin n) (Fin n) R) (rows cols : Fin k → Fin n) :
    MvPolynomial σ R := minor (B + T.map C) rows cols

theorem minor_isHomogeneous
    (B : Matrix (Fin n) (Fin n) (MvPolynomial σ R))
    (hB : ∀ i j, (B i j).IsHomogeneous 1) (rows cols : Fin k → Fin n) :
    (minor B rows cols).IsHomogeneous k :=
  determinant_isHomogeneous_of_linear_entries _ (fun i j => hB (rows i) (cols j))

theorem translatedMinor_sub_totalDegree_lt
    (B : Matrix (Fin n) (Fin n) (MvPolynomial σ R))
    (hB : ∀ i j, (B i j).totalDegree ≤ 1) (T : Matrix (Fin n) (Fin n) R)
    (rows cols : Fin k → Fin n) (hk : 0 < k) :
    (translatedMinor B T rows cols - minor B rows cols).totalDegree < k := by
  exact totalDegree_det_add_C_sub_lt (B.submatrix rows cols) (T.submatrix rows cols)
    (fun i j => hB (rows i) (cols j)) hk

@[simp] theorem map_minor (f : R →+* S)
    (B : Matrix (Fin n) (Fin n) (MvPolynomial σ R)) (rows cols : Fin k → Fin n) :
    map f (minor B rows cols) = minor (B.map (map f)) rows cols := by
  exact (map f).map_det _

@[simp] theorem map_translatedMinor (f : R →+* S)
    (B : Matrix (Fin n) (Fin n) (MvPolynomial σ R))
    (T : Matrix (Fin n) (Fin n) R) (rows cols : Fin k → Fin n) :
    map f (translatedMinor B T rows cols) =
      translatedMinor (B.map (map f)) (T.map f) rows cols := by
  rw [translatedMinor, map_minor]
  congr 1
  ext i j
  simp

@[simp] theorem eval₂_minor (f : R →+* S) (x : σ → S)
    (B : Matrix (Fin n) (Fin n) (MvPolynomial σ R)) (rows cols : Fin k → Fin n) :
    eval₂ f x (minor B rows cols) = ((B.map (eval₂ f x)).submatrix rows cols).det :=
  (eval₂Hom f x).map_det _

@[simp] theorem eval₂_translatedMinor (f : R →+* S) (x : σ → S)
    (B : Matrix (Fin n) (Fin n) (MvPolynomial σ R))
    (T : Matrix (Fin n) (Fin n) R) (rows cols : Fin k → Fin n) :
    eval₂ f x (translatedMinor B T rows cols) =
      ((B.map (eval₂ f x) + T.map f).submatrix rows cols).det := by
  rw [translatedMinor, eval₂_minor]
  congr 2
  ext i j
  simp

/-- All and only the positive-size minors relevant to the rank bound. -/
abbrev MinorIndex (n r : ℕ) :=
  Σ k : {k : Fin (n+1) // r < k.val}, (Fin k.val.val → Fin n) × (Fin k.val.val → Fin n)

def degree {r : ℕ} (i : MinorIndex n r) : ℕ := i.1.val.val

theorem degree_pos {r : ℕ} (i : MinorIndex n r) : 0 < degree i :=
  lt_of_le_of_lt (Nat.zero_le r) i.1.property

def equation (B : Matrix (Fin n) (Fin n) (MvPolynomial σ R))
    {r : ℕ} (i : MinorIndex n r) : MvPolynomial σ R := minor B i.2.1 i.2.2

def translatedEquation (B : Matrix (Fin n) (Fin n) (MvPolynomial σ R))
    (T : Matrix (Fin n) (Fin n) R) {r : ℕ} (i : MinorIndex n r) :
    MvPolynomial σ R := translatedMinor B T i.2.1 i.2.2

@[simp] theorem map_equation (f : R →+* S)
    (B : Matrix (Fin n) (Fin n) (MvPolynomial σ R))
    {r : ℕ} (i : MinorIndex n r) :
    map f (equation B i) = equation (B.map (map f)) i := map_minor f B _ _

@[simp] theorem map_translatedEquation (f : R →+* S)
    (B : Matrix (Fin n) (Fin n) (MvPolynomial σ R))
    (T : Matrix (Fin n) (Fin n) R) {r : ℕ} (i : MinorIndex n r) :
    map f (translatedEquation B T i) =
      translatedEquation (B.map (map f)) (T.map f) i := map_translatedMinor f B T _ _

theorem equation_isHomogeneous
    (B : Matrix (Fin n) (Fin n) (MvPolynomial σ R))
    (hB : ∀ i j, (B i j).IsHomogeneous 1) {r : ℕ} (i : MinorIndex n r) :
    (equation B i).IsHomogeneous (degree i) := minor_isHomogeneous B hB _ _

theorem translatedEquation_sub_totalDegree_lt
    (B : Matrix (Fin n) (Fin n) (MvPolynomial σ R))
    (hB : ∀ i j, (B i j).IsHomogeneous 1)
    (T : Matrix (Fin n) (Fin n) R) {r : ℕ} (i : MinorIndex n r) :
    (translatedEquation B T i - equation B i).totalDegree < degree i :=
  translatedMinor_sub_totalDegree_lt B (fun i j => (hB i j).totalDegree_le) T _ _
    (degree_pos i)

/-- Literal common zeros are the entire translated rank locus. -/
theorem translatedEquation_zero_iff {K : Type*} [Field K]
    (f : R →+* K) (x : σ → K)
    (B : Matrix (Fin n) (Fin n) (MvPolynomial σ R))
    (T : Matrix (Fin n) (Fin n) R) (r : ℕ) :
    (∀ i : MinorIndex n r, eval₂ f x (translatedEquation B T i) = 0) ↔
      (B.map (eval₂ f x) + T.map f).rank ≤ r := by
  constructor
  · intro hz
    by_contra hr
    let M := B.map (eval₂ f x) + T.map f
    have hrr : r < M.rank := Nat.lt_of_not_ge hr
    obtain ⟨rows, cols, hd⟩ := MatrixRankMinors.exists_rank_minor M
    let k : {k : Fin (n+1) // r < k.val} :=
      ⟨⟨M.rank, Nat.lt_succ_of_le (Matrix.rank_le_width M)⟩, hrr⟩
    have h := hz ⟨k, rows, cols⟩
    exact hd (by simpa only [translatedEquation, eval₂_translatedMinor] using h)
  · intro hr i
    rw [translatedEquation, eval₂_translatedMinor]
    by_contra hd
    have hk := MatrixRankMinors.minor_size_le_rank _ i.2.1 i.2.2 hd
    have hi := i.1.property
    omega

/-- The fixed unshifted family cuts out the full unshifted rank locus. -/
theorem equation_zero_iff {K : Type*} [Field K]
    (f : R →+* K) (x : σ → K)
    (B : Matrix (Fin n) (Fin n) (MvPolynomial σ R)) (r : ℕ) :
    (∀ i : MinorIndex n r, eval₂ f x (equation B i) = 0) ↔
      (B.map (eval₂ f x)).rank ≤ r := by
  simpa only [translatedEquation, translatedMinor, equation,
    Matrix.map_zero, map_zero, add_zero] using
      translatedEquation_zero_iff f x B 0 r

/-- Actual cubic Hessian entries are homogeneous linear forms in every characteristic. -/
theorem hessian_entries_isHomogeneous (F : MvPolynomial (Fin n) R)
    (hF : F.IsHomogeneous 3) (i j : Fin n) :
    (hessianPolynomial F i j).IsHomogeneous 1 := hF.pderiv.pderiv

theorem hessian_translatedEquation_sub_totalDegree_lt (F : MvPolynomial (Fin n) R)
    (hF : F.IsHomogeneous 3) (T : Matrix (Fin n) (Fin n) R)
    {r : ℕ} (i : MinorIndex n r) :
    (translatedEquation (hessianPolynomial F) T i - equation (hessianPolynomial F) i).totalDegree <
      degree i := translatedEquation_sub_totalDegree_lt _ (hessian_entries_isHomogeneous F hF) T i

theorem hessian_translatedEquation_zero_iff {K : Type*} [Field K]
    (f : R →+* K) (F : MvPolynomial (Fin n) R)
    (T : Matrix (Fin n) (Fin n) R) (r : ℕ) (x : Fin n → K) :
    (∀ i : MinorIndex n r,
      eval₂ f x (translatedEquation (hessianPolynomial F) T i) = 0) ↔
      (T.map f + hessian (map f F) x).rank ≤ r := by
  rw [translatedEquation_zero_iff]
  have h : (hessianPolynomial F).map (eval₂ f x) = hessian (map f F) x := by
    ext i j
    simp [hessian, hessianPolynomial, pderiv_map, eval_map]
  rw [h, add_comm]

/-- The fixed Hessian equations commute exactly with scalar extension. -/
@[simp] theorem map_hessian_equation (f : R →+* S) (F : MvPolynomial (Fin n) R)
    {r : ℕ} (i : MinorIndex n r) :
    map f (equation (hessianPolynomial F) i) =
      equation (hessianPolynomial (map f F)) i := by
  rw [map_equation]
  congr 1
  ext a b
  simp [hessianPolynomial, pderiv_map]

/-- The matrix shift may live in the target ring, independently of the fixed
integral or rational coefficient ring of the original cubic. -/
theorem specialized_hessian_lower_degree (f : R →+* S)
    (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous 3)
    (T : Matrix (Fin n) (Fin n) S) {r : ℕ} (i : MinorIndex n r) :
    (translatedEquation (hessianPolynomial (map f F)) T i -
      map f (equation (hessianPolynomial F) i)).totalDegree < degree i := by
  rw [map_hessian_equation]
  exact hessian_translatedEquation_sub_totalDegree_lt (map f F) (hF.map f) T i

/-- Over any target field, the actual specialized equations cut out every
point of the translated rank locus, with no cubic-zero restriction. -/
theorem specialized_hessian_zero_iff {K : Type*} [Field K]
    (f : R →+* K) (F : MvPolynomial (Fin n) R)
    (T : Matrix (Fin n) (Fin n) K) (r : ℕ) (x : Fin n → K) :
    (∀ i : MinorIndex n r,
      eval x (translatedEquation (hessianPolynomial (map f F)) T i) = 0) ↔
      (T + hessian (map f F) x).rank ≤ r := by
  simpa only [eval₂_id, map_id, Matrix.map_id] using
    hessian_translatedEquation_zero_iff (RingHom.id K) (map f F) T r x

/-- The empty determinant is one and is never included in the rank-equation family. -/
theorem translatedMinor_zero (B : Matrix (Fin n) (Fin n) (MvPolynomial σ R))
    (T : Matrix (Fin n) (Fin n) R) (rows cols : Fin 0 → Fin n) :
    translatedMinor B T rows cols = 1 := by
  simp [translatedMinor, minor]

end CubicTenVariables.TranslatedHessianMinors

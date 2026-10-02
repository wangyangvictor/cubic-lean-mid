import CubicTenVariables.HessianRankZeroReduction
import CubicTenVariables.ReducedVertexBaseChange
import CubicTenVariables.Literature.FiniteFieldPointCounts
import HessianTheorem11.MatrixRankMinors

/-! Actual maximal minors of the flattened cubic Hessian pencil certify
geometric nonconicality. A good specialization supplies a concrete minor;
no geometric spreading or generic nonconicality premise is hidden here. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CubicNonconicalMinorCertificate
open MvPolynomial HessianTheorem11 Matrix Module Literature
open HessianRankZeroReduction ReducedCubicVertex ReducedVertexBaseChange

def minor {R : Type*} [CommRing R] {n : ℕ}
    (F : MvPolynomial (Fin n) R)
    (rows : Fin n → Fin n × Fin n) (cols : Fin n → Fin n) : R :=
  ((hessianCoefficientMatrix F).submatrix rows cols).det

theorem minor_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (F : MvPolynomial (Fin n) R) (ρ : R →+* S)
    (rows : Fin n → Fin n × Fin n) (cols : Fin n → Fin n) :
    minor (map ρ F) rows cols = ρ (minor F rows cols) := by
  rw [minor, hessianCoefficientMatrix_map, minor, RingHom.map_det]
  rfl

theorem coefficientMatrix_injective_of_nonconical
    {K : Type*} [Field K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (hNC : GeometricallyNonconicalCubic F) :
    Function.Injective (hessianCoefficientMatrix F).mulVec := by
  have hbar : affineVertex (map (algebraMap K (AlgebraicClosure K)) F) (hF.map _) = ⊥ := by
    apply bot_unique
    intro x hx
    exact (geometricallyNonconicalCubic_iff_hessian F hF h2 h3).mp hNC x hx
  have hbase := (affineVertex_baseChange_eq_bot_iff
    (L := AlgebraicClosure K) F hF).mp hbar
  change Function.Injective (hessianCoefficientMatrix F).mulVecLin
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro x hx
  have hv : x ∈ affineVertex F hF := by
    change hessian F x = 0
    ext i j
    have he := congrFun hx (i,j)
    change (hessianCoefficientMatrix F).mulVec x (i,j) = 0 at he
    rw [coefficientMatrix_mulVec F hF x] at he
    exact he
  rwa [hbase] at hv

theorem hessian_eq_zero_imp_zero_of_minor
    {K : Type*} [Field K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (rows : Fin n → Fin n × Fin n) (cols : Fin n → Fin n)
    (hminor : minor F rows cols ≠ 0)
    (x : Fin n → K) (hx : hessian F x = 0) : x = 0 := by
  let M := hessianCoefficientMatrix F
  have hl : n ≤ M.rank := MatrixRankMinors.minor_size_le_rank M rows cols hminor
  have hh := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  change M.rank + finrank K (LinearMap.ker M.mulVecLin) = _ at hh
  simp only [Module.finrank_pi, Fintype.card_fin] at hh
  have hk : finrank K (LinearMap.ker M.mulVecLin) = 0 := by omega
  have hinj := LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)
  apply hinj
  change M.mulVec x = M.mulVec 0
  rw [Matrix.mulVec_zero]
  ext ij
  change (hessianCoefficientMatrix F).mulVec x ij = 0
  rw [coefficientMatrix_mulVec F hF x, hx]
  rfl

theorem nonconical_of_minor
    {K : Type*} [Field K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (rows : Fin n → Fin n × Fin n) (cols : Fin n → Fin n)
    (hminor : minor F rows cols ≠ 0) : GeometricallyNonconicalCubic F := by
  apply (geometricallyNonconicalCubic_iff_hessian F hF h2 h3).mpr
  intro x hx
  apply hessian_eq_zero_imp_zero_of_minor _ (hF.map _) rows cols _ x hx
  rw [minor_map]
  exact (map_ne_zero (algebraMap K (AlgebraicClosure K))).mpr hminor

/-- One actual maximal minor, nonzero at the given good specialization,
certifies every field specialization where it stays nonzero. -/
theorem exists_minor_certificate
    {R Ω : Type*} [CommRing R] [Field Ω] {n : ℕ}
    (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous 3)
    (ρ : R →+* Ω) (h2 : (2 : Ω) ≠ 0) (h3 : (3 : Ω) ≠ 0)
    (hNC : GeometricallyNonconicalCubic (map ρ F)) :
    ∃ (rows : Fin n → Fin n × Fin n) (cols : Fin n → Fin n),
      ρ (minor F rows cols) ≠ 0 ∧
      ∀ (K : Type*) [Field K] (τ : R →+* K),
        (2 : K) ≠ 0 → (3 : K) ≠ 0 → τ (minor F rows cols) ≠ 0 →
          GeometricallyNonconicalCubic (map τ F) := by
  let M := hessianCoefficientMatrix (map ρ F)
  have hinj : Function.Injective M.mulVec :=
    coefficientMatrix_injective_of_nonconical _ (hF.map _) h2 h3 hNC
  have hrank : M.rank = n := by
    change finrank Ω (LinearMap.range M.mulVecLin) = n
    rw [LinearMap.finrank_range_of_inj hinj]
    simp only [Module.finrank_pi, Fintype.card_fin]
  have hex : ∃ (rows : Fin n → Fin n × Fin n) (cols : Fin n → Fin n),
      (M.submatrix rows cols).det ≠ 0 :=
    Eq.mp (congrArg (fun t => ∃ (rows : Fin t → Fin n × Fin n) (cols : Fin t → Fin n),
      (M.submatrix rows cols).det ≠ 0) hrank) (MatrixRankMinors.exists_rank_minor M)
  obtain ⟨rows, cols, hd⟩ := hex
  have hρ : ρ (minor F rows cols) ≠ 0 := by
    rw [← minor_map]
    exact hd
  refine ⟨rows, cols, hρ, ?_⟩
  intro K _ τ hK2 hK3 hτ
  exact nonconical_of_minor _ (hF.map _) hK2 hK3 rows cols (by rwa [minor_map])

end CubicTenVariables.CubicNonconicalMinorCertificate

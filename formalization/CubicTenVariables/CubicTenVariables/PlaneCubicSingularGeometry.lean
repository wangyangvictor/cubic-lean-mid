import CubicTenVariables.SingularCubicProjectionCoprime
import CubicTenVariables.CubicGradientScaling
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Perfect

/-! Elementary geometry of the singular points of an integral plane cubic.
The line joining two singular points lies on the cubic by its division-free
Taylor identity. A plane cubic cannot contain a line if its equation is
irreducible. All geometric statements here are proved, not literature inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.PlaneCubicSingularGeometry
open MvPolynomial HessianTheorem11 Module
open scoped BigOperators
variable {K : Type*} [Field K]

/-- The actual polynomial representing a linear functional. -/
def linearPolynomial {n : ℕ} (f : (Fin n → K) →ₗ[K] K) : MvPolynomial (Fin n) K :=
  ∑ i, C (f (Pi.single i 1)) * X i

theorem eval_linearPolynomial {n : ℕ} (f : (Fin n → K) →ₗ[K] K) (x : Fin n → K) :
    eval x (linearPolynomial f) = f x := by
  classical
  have hx : x = ∑ i, x i • (Pi.single i 1 : Fin n → K) := by
    ext j
    simp [Pi.single_apply]
  conv_rhs => rw [hx]
  simp [linearPolynomial, mul_comm]

theorem homogeneous_linearPolynomial {n : ℕ} (f : (Fin n → K) →ₗ[K] K) :
    (linearPolynomial f).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_C_mul_X _ _

theorem linearPolynomial_ne_zero {n : ℕ} (f : (Fin n → K) →ₗ[K] K) (hf : f ≠ 0) :
    linearPolynomial f ≠ 0 := by
  intro h
  apply hf
  apply LinearMap.ext
  intro x
  change f x = 0
  have hx := eval_linearPolynomial f x
  rw [h, map_zero] at hx
  exact hx.symm

/-- Over a field, a polynomial of total degree one is irreducible. -/
theorem irreducible_of_totalDegree_eq_one {n : ℕ} (L : MvPolynomial (Fin n) K)
    (hL : L.totalDegree = 1) : Irreducible L := by
  have hn : L ≠ 0 := by intro h; simp [h] at hL
  have hunit (G : MvPolynomial (Fin n) K) (hG : G ≠ 0) (hd : G.totalDegree = 0) :
      IsUnit G := by
    rw [totalDegree_eq_zero_iff_eq_C.mp hd]
    apply IsUnit.map C
    apply isUnit_iff_ne_zero.mpr
    intro hc
    apply hG
    rw [totalDegree_eq_zero_iff_eq_C.mp hd, hc, map_zero]
  refine ⟨?_, ?_⟩
  · intro hu
    have := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    omega
  · intro A B he
    have ha : A ≠ 0 := by intro h; simp [h] at he; exact hn he
    have hb : B ≠ 0 := by intro h; simp [h] at he; exact hn he
    have hd : A.totalDegree + B.totalDegree = 1 := by
      rw [← totalDegree_mul_of_isDomain ha hb, ← he, hL]
    rcases (show A.totalDegree = 0 ∨ B.totalDegree = 0 by omega) with h | h
    · exact Or.inl (hunit A ha h)
    · exact Or.inr (hunit B hb h)

/-- An irreducible positive-degree hypersurface containing a hyperplane
must have degree one. This uses Mathlib's proved Nullstellensatz. -/
theorem degree_le_one_of_vanishes_on_hyperplane [IsAlgClosed K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (hF : Irreducible F)
    (f : (Fin n → K) →ₗ[K] K) (hf : f ≠ 0)
    (hz : ∀ x, f x = 0 → eval x F = 0) : F.totalDegree ≤ 1 := by
  let L := linearPolynomial f
  have hL0 : L ≠ 0 := linearPolynomial_ne_zero f hf
  have hLd : L.totalDegree = 1 := (homogeneous_linearPolynomial f).totalDegree hL0
  have hLp : Prime L := (irreducible_of_totalDegree_eq_one L hLd).prime
  let I : Ideal (MvPolynomial (Fin n) K) := Ideal.span {L}
  have hIp : I.IsPrime := (Ideal.span_singleton_prime hL0).mpr hLp
  letI := hIp
  have hmem : F ∈ vanishingIdeal K (zeroLocus K I) := by
    intro x hx
    apply hz x
    have h := hx L (Ideal.subset_span (Set.mem_singleton L))
    simpa only [L, aeval_eq_eval, eval_linearPolynomial] using h
  rw [IsPrime.vanishingIdeal_zeroLocus] at hmem
  have hdiv : L ∣ F := Ideal.mem_span_singleton.mp hmem
  have hnot : ¬ IsUnit L := (irreducible_of_totalDegree_eq_one L hLd).not_isUnit
  have hback : F ∣ L := hLp.irreducible.dvd_symm hF hdiv
  simpa [hLd] using totalDegree_le_of_dvd_of_isDomain hback hL0

/-- A cubic vanishes on the entire line through two singular zeros,
in every characteristic. -/
theorem eval_singular_span {n : ℕ} (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (z w : Fin n → K)
    (hz : eval z F = 0) (hgz : gradient F z = 0)
    (hw : eval w F = 0) (hgw : gradient F w = 0) (a b : K) :
    eval (a • z + b • w) F = 0 := by
  have haz : eval (a • z) F = 0 := by
    simpa only [eval₂_id, hz, mul_zero] using
      CubicGradientScaling.homogeneous_eval₂_smul F hF (RingHom.id K) z a
  have hag : gradient F (a • z) = 0 := by
    funext i
    have hi : eval z (pderiv i F) = 0 := congrFun hgz i
    change eval (a • z) (pderiv i F) = 0
    simpa only [eval₂_id, hi, mul_zero] using
      CubicGradientScaling.eval₂_partial_smul F hF (RingHom.id K) i z a
  rw [CubicTaylorExpansion.eval_cubic_add_smul F hF]
  simp [CubicTaylorExpansion.directional, CubicTaylorExpansion.quadraticAt,
    haz, hag, hw, hgw]

/-- Two linearly independent singular zeros of a ternary cubic force
reducibility. No smoothness or separability assumption is used. -/
theorem not_independent_vanishing_span [IsAlgClosed K]
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (z w : Fin 3 → K) (hspan : ∀ a b : K, eval (a • z + b • w) F = 0) :
    ¬ LinearIndependent K ![z,w] := by
  intro hi
  let W := Submodule.span K ({z,w} : Set (Fin 3 → K))
  have hWd : finrank K W = 2 := by
    have hr : Set.range ![z,w] = ({z,w} : Set (Fin 3 → K)) := by
      ext x
      simp [or_comm]
    change finrank K (Submodule.span K ({z,w} : Set (Fin 3 → K))) = 2
    rw [← hr]
    simpa using finrank_span_eq_card hi
  have hWlt : W < ⊤ := Submodule.lt_top_of_finrank_lt_finrank (by simpa using hWd ▸ (by decide : 2 < 3))
  obtain ⟨f,hf,hWf⟩ := W.exists_le_ker_of_lt_top hWlt
  have hkd := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  have hkeq : W = LinearMap.ker f := Submodule.eq_of_le_of_finrank_eq hWf (by
    simp only [Module.finrank_pi, Fintype.card_fin] at hkd
    omega)
  have hd := degree_le_one_of_vanishes_on_hyperplane F hirr f hf (by
    intro x hx
    have hxW : x ∈ W := hkeq ▸ hx
    obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hxW
    exact hspan a b)
  rw [hF.totalDegree hirr.ne_zero] at hd
  omega

/-- The line joining two singular points would be a component. -/
theorem not_independent_singular_pair [IsAlgClosed K]
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (z w : Fin 3 → K) (hz : eval z F = 0) (hgz : gradient F z = 0)
    (hw : eval w F = 0) (hgw : gradient F w = 0) :
    ¬ LinearIndependent K ![z,w] :=
  not_independent_vanishing_span F hF hirr z w
    (eval_singular_span F hF z w hz hgz hw hgw)

/-- All nonzero singular vectors of an integral plane cubic represent the
same projective point. -/
theorem singular_proportional [IsAlgClosed K]
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (z w : Fin 3 → K) (hz0 : z ≠ 0)
    (hz : eval z F = 0) (hgz : gradient F z = 0)
    (hw : eval w F = 0) (hgw : gradient F w = 0) : ∃ a : K, a • z = w := by
  have hi := not_independent_singular_pair F hF hirr w z hw hgw hz hgz
  simp only [linearIndependent_fin2, Matrix.cons_val_zero, Matrix.cons_val_one] at hi
  push_neg at hi
  exact hi hz0

/-- An integral plane cubic has a geometric zero off any given hyperplane. -/
theorem exists_zero_off_hyperplane [IsAlgClosed K]
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (f : (Fin 3 → K) →ₗ[K] K) (hf : f ≠ 0) :
    ∃ x : Fin 3 → K, eval x F = 0 ∧ f x ≠ 0 := by
  classical
  by_contra! h
  let I : Ideal (MvPolynomial (Fin 3) K) := Ideal.span {F}
  have hp : I.IsPrime := (Ideal.span_singleton_prime hirr.ne_zero).mpr hirr.prime
  letI := hp
  have hm : linearPolynomial f ∈ vanishingIdeal K (zeroLocus K I) := by
    intro x hx
    rw [aeval_eq_eval, eval_linearPolynomial]
    apply h
    have he := hx F (Ideal.subset_span (Set.mem_singleton F))
    exact he
  rw [IsPrime.vanishingIdeal_zeroLocus] at hm
  have hd := totalDegree_le_of_dvd_of_isDomain
    (Ideal.mem_span_singleton.mp hm) (linearPolynomial_ne_zero f hf)
  rw [hF.totalDegree hirr.ne_zero,
    (homogeneous_linearPolynomial f).totalDegree (linearPolynomial_ne_zero f hf)] at hd
  omega

/-- An integral plane cubic is geometrically nonconical: a translation
vertex and a point away from it would generate a line component. -/
theorem translation_eq_zero [IsAlgClosed K]
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (v : Fin 3 → K) (hv : ReducedCubicVertex.TranslationDirection F v) : v = 0 := by
  classical
  by_contra hv0
  let W := Submodule.span K ({v} : Set (Fin 3 → K))
  have hWlt : W < ⊤ := Submodule.lt_top_of_finrank_lt_finrank (by
    have hle : finrank K W ≤ 1 := by
      simpa [W] using finrank_span_le_card ({v} : Set (Fin 3 → K))
    simpa using lt_of_le_of_lt hle (by decide : 1 < 3))
  obtain ⟨f,hf,hWf⟩ := W.exists_le_ker_of_lt_top hWlt
  have hfv : f v = 0 := hWf (Submodule.subset_span (Set.mem_singleton v))
  obtain ⟨x,hx,hfx⟩ := exists_zero_off_hyperplane F hF hirr f hf
  have hi : LinearIndependent K ![x,v] := by
    rw [linearIndependent_fin2]
    refine ⟨hv0, ?_⟩
    intro a ha
    change a • v = x at ha
    apply hfx
    rw [← ha, map_smul, hfv, smul_zero]
  apply not_independent_vanishing_span F hF hirr x v ?_ hi
  intro a b
  rw [hv]
  simpa only [eval₂_id, hx, mul_zero] using
    CubicGradientScaling.homogeneous_eval₂_smul F hF (RingHom.id K) x a

/-- Actual geometric integrality supplies the irreducibility used by both
singular-point uniqueness and nonconicality. -/
theorem geometric_irreducible (F : MvPolynomial (Fin 3) K)
    (hI : Literature.GeometricallyIntegralForm F) :
    Irreducible (map (algebraMap K (AlgebraicClosure K)) F) := by
  have hn : map (algebraMap K (AlgebraicClosure K)) F ≠ 0 :=
    fun he => hI.1 ((MvPolynomial.map_injective (algebraMap K (AlgebraicClosure K))
      (algebraMap K (AlgebraicClosure K)).injective) (he.trans (map_zero _).symm))
  exact ((Ideal.span_singleton_prime hn).mp
    ((Ideal.Quotient.isDomain_iff_prime _).mp hI.2)).irreducible

theorem geometricallyNonconical (F : MvPolynomial (Fin 3) K)
    (hF : F.IsHomogeneous 3) (hI : Literature.GeometricallyIntegralForm F) :
    Literature.GeometricallyNonconicalCubic F := by
  intro v hv
  exact translation_eq_zero _ (hF.map _) (geometric_irreducible F hI) v hv

/-- The unique geometric singular point is rational over a perfect field.
We normalize one coordinate, use uniqueness under every field automorphism,
and apply the proved fixed-field theorem. -/
theorem exists_rational_singular_of_geometric [PerfectField K]
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3)
    (hI : Literature.GeometricallyIntegralForm F)
    (hs : ∃ x : Fin 3 → AlgebraicClosure K,
      x ≠ 0 ∧ x ∈ Literature.geometricSingularCone F) :
    ∃ x : Fin 3 → K, x ≠ 0 ∧ eval x F = 0 ∧ gradient F x = 0 := by
  classical
  let L := AlgebraicClosure K
  let α : K →+* L := algebraMap K L
  let G := map α F
  letI : IsGalois K L := ⟨⟩
  obtain ⟨x,hx,hxz,hxg⟩ := hs
  change eval x G = 0 at hxz
  have hxg' : gradient G x = 0 := funext hxg
  obtain ⟨i,hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! he
    exact hx (funext he)
  let z : Fin 3 → L := (x i)⁻¹ • x
  have hzi : z i = 1 := by simp [z, hi]
  have hz0 : z ≠ 0 := by intro he; have := congrFun he i; simp [hzi] at this
  have hz : eval z G = 0 := by
    have he := CubicGradientScaling.homogeneous_eval₂_smul
      G (hF.map α) (RingHom.id L) x ((x i)⁻¹)
    change eval z G = (x i)⁻¹ ^ 3 * eval x G at he
    rw [hxz, mul_zero] at he
    exact he
  have hgz : gradient G z = 0 := by
    funext j
    have hj : eval x (pderiv j G) = 0 := hxg j
    change eval z (pderiv j G) = 0
    have he := CubicGradientScaling.eval₂_partial_smul
      G (hF.map α) (RingHom.id L) j x ((x i)⁻¹)
    change eval z (pderiv j G) = (x i)⁻¹ ^ 2 * eval x (pderiv j G) at he
    rw [hj, mul_zero] at he
    exact he
  have htransport (σ : L ≃ₐ[K] L) (P : MvPolynomial (Fin 3) K) :
      eval (fun j => σ (z j)) (map α P) = σ (eval z (map α P)) := by
    induction P using MvPolynomial.induction_on with
    | C c => simp [α]
    | add P Q hP hQ => simp only [map_add, hP, hQ]
    | mul_X P j hP => simp only [map_mul, map_X, eval_X, hP]
  have hfixed (j : Fin 3) (σ : L ≃ₐ[K] L) : σ (z j) = z j := by
    have hez : eval (fun k => σ (z k)) G = 0 := by
      rw [htransport σ F, hz, map_zero]
    have heg : gradient G (fun k => σ (z k)) = 0 := by
      funext k
      change eval (fun j => σ (z j)) (pderiv k G) = 0
      change eval (fun j => σ (z j)) (pderiv k (map α F)) = 0
      rw [pderiv_map, htransport, ← pderiv_map]
      have hk : eval z (pderiv k G) = 0 := congrFun hgz k
      rw [show eval z (pderiv k (map α F)) = 0 from hk, map_zero]
    obtain ⟨a,ha⟩ := singular_proportional G (hF.map α) (geometric_irreducible F hI)
      z (fun k => σ (z k)) hz0 hz hgz hez heg
    have hai : a = 1 := by
      have hi' := congrFun ha i
      simpa only [Pi.smul_apply, smul_eq_mul, hzi, mul_one, map_one] using hi'
    simpa only [hai, one_smul] using (congrFun ha j).symm
  have hdesc (j : Fin 3) : ∃ a : K, α a = z j :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (z j)).mpr (hfixed j)
  choose y hy using hdesc
  have hbase (P : MvPolynomial (Fin 3) K) : eval z (map α P) = α (eval y P) := by
    induction P using MvPolynomial.induction_on with
    | C c => simp
    | add P Q hP hQ => simp only [map_add, hP, hQ]
    | mul_X P j hP => simp only [map_mul, map_X, eval_X, hP, hy]
  refine ⟨y, ?_, ?_, ?_⟩
  · intro he
    have hyi := hy i
    rw [he] at hyi
    simp only [Pi.zero_apply, map_zero, hzi] at hyi
    exact zero_ne_one hyi
  · apply α.injective
    rw [map_zero, ← hbase F]
    exact hz
  · funext j
    change eval y (pderiv j F) = 0
    apply α.injective
    rw [map_zero, ← hbase (pderiv j F), ← pderiv_map]
    exact congrFun hgz j

end CubicTenVariables.PlaneCubicSingularGeometry

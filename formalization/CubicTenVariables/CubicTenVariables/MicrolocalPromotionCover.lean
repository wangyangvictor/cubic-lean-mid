import CubicTenVariables.MicrolocalPromotedPartition
import CubicTenVariables.HomogeneousPrincipalOpen
import TranslatedDepthSeven.IsolatedVertexQuotientNodeDecomposition
import TranslatedDepthSeven.ProjectiveFourfoldHyperplanePila

/-! Finite residual covers for the actual promoted microlocal parts.
The promotion polynomials form an explicit supplied table; this file does
not assert their construction or a global relative-openness property.
Each table entry is already countable, lies in the next closed level, or
has a positive homogeneous principal-open equation with a lower-dimensional
residual. The incoming promotion is covered by the actual next rational
depth locus. No new literature premise is introduced. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.MicrolocalPromotionCover
open MvPolynomial HessianTheorem11 TranslatedDepthSeven
open ProjectiveMicrolocalData ProjectiveMicrolocalModels RationalConeClosure
open ConeComponentProgressionCount MicrolocalPromotedPartition
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Union of the literal componentwise principal opens. The zero polynomial
can disable an entry without changing the index type. -/
def promotionOpen {n c : ℕ} (I : Fin c → Ideal (MvPolynomial (Fin n) ℚ))
    (g : Fin c → MvPolynomial (Fin n) ℚ) : Set (Fin n → ℚ) :=
  {x | ∃ i, x ∈ affineIdealZeroLocus (I i) ∧ eval x (g i) ≠ 0}

/-- Positive homogeneous residuals contain the origin, so their ideals
are proper even when their dimension drops further than expected. -/
theorem residual_ne_top {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin n) ℚ))
    (g : MvPolynomial (Fin n) ℚ) (e : ℕ) (he : 0 < e) (hg : g.IsHomogeneous e) :
    ConePrincipalOpen.residualIdeal I g ≠ ⊤ := by
  have hgzero : eval (0 : Fin n → ℚ) g = 0 := by
    have hs := CubicGradientScaling.homogeneous_eval₂_smul g hg
      (RingHom.id ℚ) (0 : Fin n → ℚ) (0 : ℚ)
    simpa only [zero_smul,zero_pow (Nat.ne_of_gt he),zero_mul,eval₂_id] using hs
  have hzero : (0 : Fin n → ℚ) ∈ affineIdealZeroLocus
      (ConePrincipalOpen.residualIdeal I g) :=
    mem_affineIdealZeroLocus_sup_span_singleton I g 0
      (homogeneousPrimeIdeal_le_eval_zero I hprime hhom) hgzero
  intro htop
  have hone : (1 : MvPolynomial (Fin n) ℚ) ∈ ConePrincipalOpen.residualIdeal I g := by
    rw [htop]
    trivial
  have ho := hzero 1 hone
  simp at ho

/-- A finite classified table gives an actual finite residual cover.
Contained components disappear because points in the next level have
already been removed. Only componentwise principal opens are used. -/
theorem exists_residual_cover {N r c : ℕ}
    (I : Fin c → Ideal (MvPolynomial (Fin (N+1)) ℚ))
    (hprime : ∀ i, (I i).IsPrime)
    (hhom : ∀ i, (I i).IsHomogeneous (homogeneousSubmodule (Fin (N+1)) ℚ))
    (g : Fin c → MvPolynomial (Fin (N+1)) ℚ) (Z : Set (Fin (N+1) → ℚ))
    (hcase : ∀ i, ComponentCondition r (I i) ∨ affineIdealZeroLocus (I i) ⊆ Z ∨
      ∃ e : ℕ, 0 < e ∧ (g i).IsHomogeneous e ∧
        ringKrullDim (MvPolynomial (Fin (N+1)) ℚ ⧸
          ConePrincipalOpen.residualIdeal (I i) (g i)) ≤ (r : WithBot ℕ∞)) :
    ∃ (k : ℕ) (J : Fin k → Ideal (MvPolynomial (Fin (N+1)) ℚ)),
      (∀ a, ComponentCondition r (J a)) ∧
      ∀ x, (∃ i, x ∈ affineIdealZeroLocus (I i)) → x ∉ Z →
        x ∉ promotionOpen I g → ∃ a, x ∈ affineIdealZeroLocus (J a) := by
  classical
  let A := {i : Fin c // ¬ affineIdealZeroLocus (I i) ⊆ Z}
  let J₀ : A → Ideal (MvPolynomial (Fin (N+1)) ℚ) := fun i =>
    if ComponentCondition r (I i) then I i else ConePrincipalOpen.residualIdeal (I i) (g i)
  have hJ (a : A) : ComponentCondition r (J₀ a) := by
    dsimp [J₀]
    split_ifs with hgood
    · exact hgood
    · rcases hcase a with hc | hc | ⟨e,he,hg,hd⟩
      · exact (hgood hc).elim
      · exact (a.property hc).elim
      · exact ⟨residual_ne_top _ (hprime a) (hhom a) _ e he hg,
          HomogeneousPrincipalOpen.residual_isHomogeneous _ (hhom a) _ e hg,Or.inl hd⟩
  refine ⟨Fintype.card A,fun a => J₀ ((Fintype.equivFin A).symm a),
    fun a => hJ _,?_⟩
  intro x ⟨i,hi⟩ hxZ hxU
  have hactive : ¬ affineIdealZeroLocus (I i) ⊆ Z := fun hh => hxZ (hh hi)
  let a : A := ⟨i,hactive⟩
  refine ⟨Fintype.equivFin A a,?_⟩
  simp only [Equiv.symm_apply_apply]
  dsimp [J₀]
  split_ifs with hgood
  · exact hi
  · apply mem_affineIdealZeroLocus_sup_span_singleton _ _ x hi
    by_contra hnonzero
    exact hxU ⟨i,hi,hnonzero⟩

variable {t : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}

/-- The actual next rational depth locus supplies the incoming finite
cover, with the required ordinary dimension for levels three and four. -/
theorem exists_incoming_cover (h : Geometry F f)
    (hF : Anisotropic (map (Int.castRingHom ℚ) F))
    (j : ℕ) (hj : j=3 ∨ j=4) :
    ∃ (k : ℕ) (J : Fin k → Ideal (MvPolynomial (Fin 10) ℚ)),
      (∀ a, ComponentCondition (8-j) (J a)) ∧
      ∀ x ∈ filtration f (j+1), ∃ a, x ∈ affineIdealZeroLocus (J a) := by
  obtain ⟨c,Y,s,G,d,hcover,hcomp⟩ := MicrolocalRationalComponents.exists_components h hF
    (j:=j+1) (by omega) (by omega)
  refine ⟨c,fun i => IntegralModelDimension.rationalIdeal (G i),?_,?_⟩
  · intro i
    refine ⟨(hcomp i).2.2.2.2.1.ne_top,(hcomp i).2.2.2.2.2.2.1,Or.inl ?_⟩
    have hd := (hcomp i).2.2.2.2.2.2.2.2.1
    simpa only [show 10-(j+1+1)=8-j by omega] using hd
  · intro x hx
    have hR : rationalEmbedding x ∈ rationalDepth f (j+1) := by
      change x ∈ rationalPoints (rationalDepth f (j+1))
      rw [rationalDepth_points h (by omega)]
      simpa only [filtration,if_neg (by omega : j+1 ≠ 0)] using hx
    rw [hcover] at hR
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hR
    refine ⟨i,?_⟩
    change ∀ P ∈ IntegralModelDimension.rationalIdeal (G i), eval x P = 0
    rw [(hcomp i).2.2.1]
    intro P hP
    exact hP x hi

/-- Exact finite cover of the actual part, including incoming promotions.
The classified table is explicit data; it is not assumed to exist here. -/
theorem exists_part_cover (h : Geometry F f)
    (hF : Anisotropic (map (Int.castRingHom ℚ) F))
    (j : Fin 6) (hj : j.val=3 ∨ j.val=4) {c : ℕ}
    (I : Fin c → Ideal (MvPolynomial (Fin 10) ℚ))
    (hprime : ∀ i, (I i).IsPrime)
    (hhom : ∀ i, (I i).IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ))
    (hcover : ∀ x ∈ filtration f j.val, ∃ i, x ∈ affineIdealZeroLocus (I i))
    (g : Fin c → MvPolynomial (Fin 10) ℚ)
    (hcase : ∀ i, ComponentCondition (8-j.val) (I i) ∨
      affineIdealZeroLocus (I i) ⊆ filtration f (j.val+1) ∨
      ∃ e : ℕ, 0 < e ∧ (g i).IsHomogeneous e ∧
        ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸
          ConePrincipalOpen.residualIdeal (I i) (g i)) ≤ ((8-j.val : ℕ) : WithBot ℕ∞))
    (U : ℕ → Set (Fin 10 → ℚ)) (hU : Compatible f U)
    (hopen : U j.val = promotionOpen I g) :
    ∃ (k : ℕ) (J : Fin k → Ideal (MvPolynomial (Fin 10) ℚ)),
      (∀ a, ComponentCondition (8-j.val) (J a)) ∧
      ∀ x ∈ part f U j, ∃ a, x ∈ affineIdealZeroLocus (J a) := by
  classical
  obtain ⟨k,J,hJ,hJcover⟩ := exists_residual_cover I hprime hhom g
    (filtration f (j.val+1)) hcase
  obtain ⟨l,K,hK,hKcover⟩ := exists_incoming_cover h hF j.val hj
  let A := Fin k ⊕ Fin l
  let M : A → Ideal (MvPolynomial (Fin 10) ℚ) := Sum.elim J K
  refine ⟨Fintype.card A,fun a => M ((Fintype.equivFin A).symm a),?_,?_⟩
  · intro a
    have hM : ∀ b : A, ComponentCondition (8-j.val) (M b) := by
      intro b
      cases b with
      | inl b => exact hJ b
      | inr b => exact hK b
    exact hM _
  · intro x hx
    rw [part_eq_source U j (by omega)] at hx
    have hM : ∃ a : A, x ∈ affineIdealZeroLocus (M a) := by
      rcases hx.1 with hx | hx
      · obtain ⟨a,ha⟩ := hJcover x (hcover x hx.1.1) hx.1.2 (hopen ▸ hx.2)
        exact ⟨Sum.inl a,ha⟩
      · have hnext := PromotedFrequencyPartition.layer_subset (filtration f) (by omega)
          (hU.2.2 (j.val+1) (by omega) hx)
        obtain ⟨a,ha⟩ := hKcover x hnext
        exact ⟨Sum.inr a,ha⟩
    obtain ⟨a,ha⟩ := hM
    exact ⟨Fintype.equivFin A a,by simpa only [Equiv.symm_apply_apply] using ha⟩

/-- The classified finite principal-open table therefore yields the
selected T^5/T^4 progression estimates. Salberger is the only counting
input; the component classification and open table remain explicit. -/
theorem exists_part_bound (lit : Published.Salberger2023Theorem04)
    (h : Geometry F f) (hF : Anisotropic (map (Int.castRingHom ℚ) F))
    (j : Fin 6) (hj : j.val=3 ∨ j.val=4) {c : ℕ}
    (I : Fin c → Ideal (MvPolynomial (Fin 10) ℚ))
    (hprime : ∀ i, (I i).IsPrime)
    (hhom : ∀ i, (I i).IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ))
    (hcover : ∀ x ∈ filtration f j.val, ∃ i, x ∈ affineIdealZeroLocus (I i))
    (g : Fin c → MvPolynomial (Fin 10) ℚ)
    (hcase : ∀ i, ComponentCondition (8-j.val) (I i) ∨
      affineIdealZeroLocus (I i) ⊆ filtration f (j.val+1) ∨
      ∃ e : ℕ, 0 < e ∧ (g i).IsHomogeneous e ∧
        ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸
          ConePrincipalOpen.residualIdeal (I i) (g i)) ≤ ((8-j.val : ℕ) : WithBot ℕ∞))
    (U : ℕ → Set (Fin 10 → ℚ)) (hU : Compatible f U)
    (hopen : U j.val = promotionOpen I g) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (u : Fin 10 → ℝ) (L : ℝ), 0 ≤ L →
      ∀ (m : ℕ), 0 < m → ∀ b : Fin 10 → ℤ,
      ((points (part f U j) u L m b).card : ℝ) ≤
        C*(2+‖u‖+L+(m : ℝ))^ε*(1+L/(m : ℝ))^(8-j.val) := by
  obtain ⟨k,J,hJ,hJC⟩ := exists_part_cover h hF j hj I hprime hhom hcover g hcase U hU hopen
  obtain ⟨C,hC,hcount⟩ := exists_high_level_bound lit j.val hj J hJ ε hε
  exact ⟨C,hC,hcount _ hJC⟩

end CubicTenVariables.MicrolocalPromotionCover

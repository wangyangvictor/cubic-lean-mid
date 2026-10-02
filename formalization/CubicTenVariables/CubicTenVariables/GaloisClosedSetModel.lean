import CubicTenVariables.RationalComponentDescent

/-! Galois-stable closed subsets of affine space over Qbar have finite
rational defining equations for the same geometric set. The construction
descends a finite coefficient space containing actual ideal generators;
no rational-point density is assumed. -/

noncomputable section
namespace CubicTenVariables.GaloisClosedSetModel
open MvPolynomial HessianTheorem11 Module RationalComponentDescent
open scoped BigOperators

/-- Synthesis of an actual polynomial from finitely many monomial coefficients. -/
def synthesize {n k : ℕ} {K : Type*} [CommSemiring K]
    (μ : Fin k → (Fin n →₀ ℕ)) : (Fin k → K) →ₗ[K] MvPolynomial (Fin n) K where
  toFun v := ∑ j, monomial (μ j) (v j)
  map_add' v w := by simp [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' a v := by simp [Pi.smul_apply, Finset.smul_sum, smul_monomial]

@[simp] theorem synthesize_apply {n k : ℕ} {K : Type*} [CommSemiring K]
    (μ : Fin k → (Fin n →₀ ℕ)) (v : Fin k → K) :
    synthesize μ v = ∑ j, monomial (μ j) (v j) := rfl

@[simp] theorem map_synthesize {n k : ℕ} {K L : Type*} [CommSemiring K] [CommSemiring L]
    (μ : Fin k → (Fin n →₀ ℕ)) (φ : K →+* L) (v : Fin k → K) :
    map φ (synthesize μ v) = synthesize μ (fun j => φ (v j)) := by
  simp [synthesize]

/-- A fixed finite monomial set recovers every polynomial supported there. -/
theorem synthesize_coeff {n : ℕ} {K : Type*} [CommSemiring K]
    (M : Finset (Fin n →₀ ℕ))
    (f : MvPolynomial (Fin n) K) (hf : f.support ⊆ M) :
    synthesize (fun j => ((Fintype.equivFin M).symm j).val)
      (fun j => coeff ((Fintype.equivFin M).symm j).val f) = f := by
  classical
  rw [synthesize_apply]
  calc
    _ = ∑ j : M, monomial j.val (coeff j.val f) :=
      Equiv.sum_comp (Fintype.equivFin M).symm _
    _ = ∑ j ∈ M, monomial j (coeff j f) := by
      simpa using Finset.sum_attach M (fun j => monomial j (coeff j f))
    _ = ∑ j ∈ f.support, monomial j (coeff j f) := by
      symm
      apply Finset.sum_subset hf
      intro j _ hj
      simp [notMem_support_iff.mp hj]
    _ = f := support_sum_monomial_coeff f

/-- Set stability forces coefficient-conjugation stability of its actual
vanishing ideal, without any density assumption. -/
theorem coefficientMap_mem {n : ℕ} (Z : Set (GeometricPoint n))
    (hZ : ∀ (σ : GeometricField ≃ₐ[ℚ] GeometricField),
      ∀ x ∈ Z, galoisPoint σ x ∈ Z)
    (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (f : GeometricPolynomial n) (hf : f ∈ vanishingIdeal GeometricField Z) :
    map σ.toRingHom f ∈ vanishingIdeal GeometricField Z := by
  intro x hx
  have hz := congrArg σ (hf _ (hZ σ.symm x hx))
  change σ (eval (galoisPoint σ.symm x) f) = σ 0 at hz
  change eval x (map σ.toRingHom f) = 0
  rw [← eval_coefficientMap, galoisPoint_apply_symm, map_zero] at hz
  exact hz

/-- A coefficient-stable ideal has actual finite rational generators after
extending coefficients back to Qbar. -/
theorem exists_rational_generators {n : ℕ} (I : Ideal (GeometricPolynomial n))
    (hI : ∀ (σ : GeometricField ≃ₐ[ℚ] GeometricField),
      ∀ f ∈ I, map σ.toRingHom f ∈ I) :
    ∃ m : ℕ, ∃ f : Fin m → MvPolynomial (Fin n) ℚ,
      Ideal.span (Set.range (fun i => map (algebraMap ℚ GeometricField) (f i))) = I := by
  classical
  obtain ⟨S,hS⟩ := IsNoetherian.noetherian I
  let M := S.biUnion (fun f => f.support)
  let μ : Fin (Fintype.card M) → (Fin n →₀ ℕ) :=
    fun j => ((Fintype.equivFin M).symm j).val
  let L := synthesize (K := GeometricField) μ
  let T : Submodule GeometricField (GeometricPoint (Fintype.card M)) :=
    (I.restrictScalars GeometricField).comap L
  have hT : ∀ (σ : GeometricField ≃ₐ[ℚ] GeometricField),
      ∀ v ∈ T, (fun j => σ (v j)) ∈ T := by
    intro σ v hv
    change L (fun j => σ (v j)) ∈ I
    change L v ∈ I at hv
    simpa only [L, map_synthesize] using hI σ (L v) hv
  obtain ⟨b,hb⟩ := ReducedRationalDescent.invariant_subspace_rational_basis T hT
  choose q hq using hb
  let f : Fin (finrank GeometricField T) → MvPolynomial (Fin n) ℚ :=
    fun i => synthesize μ (q i)
  have hmap (i) : map (algebraMap ℚ GeometricField) (f i) = L (b i).val := by
    simp only [f,map_synthesize,L]
    congr 1
    funext j
    exact hq i j
  let J := Ideal.span (Set.range (fun i => map (algebraMap ℚ GeometricField) (f i)))
  have hgen (i) : L (b i).val ∈ J := by
    rw [← hmap]
    exact Ideal.subset_span ⟨i,rfl⟩
  have hTmem (v : T) : L v.val ∈ J := by
    have hv := congrArg (fun w : T => L w.val) (b.sum_repr v)
    have hsum : ∑ i, b.repr v i • L (b i).val ∈ J := by
      apply (J.restrictScalars GeometricField).sum_mem
      intro i _
      exact (J.restrictScalars GeometricField).smul_mem _ (hgen i)
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul] at hv
    exact hv ▸ hsum
  refine ⟨finrank GeometricField T,f,le_antisymm ?_ ?_⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change map (algebraMap ℚ GeometricField) (f i) ∈ I
    rw [hmap]
    exact (b i).property
  · rw [← hS]
    apply Ideal.span_le.mpr
    intro g hg
    have hgI : g ∈ I := by rw [← hS]; exact Ideal.subset_span hg
    have hsupport : g.support ⊆ M := fun j hj => Finset.mem_biUnion.mpr ⟨g,hg,hj⟩
    have hrecover : L (fun j => coeff (μ j) g) = g := synthesize_coeff M g hsupport
    let v : T := ⟨fun j => coeff (μ j) g, by change L _ ∈ I; rwa [hrecover]⟩
    simpa only [v,hrecover] using hTmem v

/-- Finite rational equations cut out the same closed geometric set Z,
not merely the closure of its rational points. -/
theorem exists_rational_equations {n : ℕ} (Z : Set (GeometricPoint n))
    (hclosed : AlgebraicallyClosedSet Z)
    (hstable : ∀ (σ : GeometricField ≃ₐ[ℚ] GeometricField),
      ∀ x ∈ Z, galoisPoint σ x ∈ Z) :
    ∃ m : ℕ, ∃ f : Fin m → MvPolynomial (Fin n) ℚ,
      Ideal.span (Set.range (fun i => map (algebraMap ℚ GeometricField) (f i))) =
        vanishingIdeal GeometricField Z ∧
      ∀ x : GeometricPoint n,
        x ∈ Z ↔ ∀ i, eval x (map (algebraMap ℚ GeometricField) (f i)) = 0 := by
  obtain ⟨m,f,hf⟩ := exists_rational_generators (vanishingIdeal GeometricField Z)
    (coefficientMap_mem Z hstable)
  refine ⟨m,f,hf,?_⟩
  intro x
  rw [← hclosed]
  change x ∈ zeroLocus GeometricField (vanishingIdeal GeometricField Z) ↔ _
  rw [← hf, zeroLocus_span]
  change (∀ g ∈ Set.range (fun i => map (algebraMap ℚ GeometricField) (f i)),
    eval x g = 0) ↔ _
  simp only [Set.forall_mem_range]

end CubicTenVariables.GaloisClosedSetModel

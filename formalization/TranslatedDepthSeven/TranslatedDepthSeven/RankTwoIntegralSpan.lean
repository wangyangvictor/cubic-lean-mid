import TranslatedDepthSeven.TangentPacketSpan
import TranslatedDepthSeven.PrimitivePlaneDirectionIncidence

/-!
# Two actual generators for a rank-two family of divided differences

Multiplication of every vector by one nonzero rational scalar does not
change its span. A rank-two family consequently has two members spanning
the entire family. A polynomial nonzero at a rational point of that span
has a nonzero restriction to these two members. These statements retain
actual vectors and polynomial evaluations, with no geometric premise.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

theorem span_range_smul_eq_of_ne_zero {ι V : Type*}
    [AddCommGroup V] [Module ℚ V] (v : ι → V) (a : ℚ) (ha : a ≠ 0) :
    Submodule.span ℚ (Set.range fun i ↦ a • v i) =
      Submodule.span ℚ (Set.range v) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.smul_mem _ a (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have h := Submodule.smul_mem
      (Submodule.span ℚ (Set.range fun i ↦ a • v i)) a⁻¹
      (Submodule.subset_span (Set.mem_range_self i))
    simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using h

/-- The two spanning vectors are members of the original integral family,
not merely arbitrary rational vectors in its span. -/
theorem exists_twoVector_generators_of_finrank_span_eq_two {n : ℕ} {ι : Type*}
    (v : ι → IntVector n)
    (hrank : Module.finrank ℚ
      (Submodule.span ℚ (Set.range fun s i ↦ (v s i : ℚ))) = 2) :
    ∃ s₀ s₁ : ι,
      Submodule.span ℚ
          ({(fun i ↦ (v s₀ i : ℚ)), (fun i ↦ (v s₁ i : ℚ))} :
            Set (Fin n → ℚ)) =
        Submodule.span ℚ (Set.range fun s i ↦ (v s i : ℚ)) ∧
      ∃ i j, v s₀ i * v s₁ j - v s₀ j * v s₁ i ≠ 0 := by
  classical
  have hb := Submodule.exists_fun_fin_finrank_span_eq ℚ
    (Set.range fun s i ↦ (v s i : ℚ))
  rw [hrank] at hb
  obtain ⟨f, hfmem, hfspan, hfindep⟩ := hb
  choose rows hrows using hfmem
  have hrange : Set.range f =
      ({(fun i ↦ (v (rows 0) i : ℚ)), (fun i ↦ (v (rows 1) i : ℚ))} :
        Set (Fin n → ℚ)) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl (hrows 0).symm
      · exact Or.inr (hrows 1).symm
    · rintro (rfl | rfl)
      · exact ⟨0, (hrows 0).symm⟩
      · exact ⟨1, (hrows 1).symm⟩
  refine ⟨rows 0, rows 1, ?_, ?_⟩
  · simpa only [hrange] using hfspan
  · obtain ⟨cols, _, hdet⟩ :=
      TangentPacketSpan.exists_selectedMinor_ne_zero_of_linearIndependent_rows
        (Matrix.of f) hfindep
    refine ⟨cols 0, cols 1, ?_⟩
    intro hzero
    apply hdet
    simp only [Matrix.det_fin_two, Matrix.submatrix_apply, Matrix.of_apply, id_eq]
    rw [← hrows 0, ← hrows 1]
    dsimp only
    exact_mod_cast hzero

/-- Detect nonvanishing of the two-variable restriction using any rational
point in the displayed span. This is also valid for an integral regular
direction whose size is not bounded. -/
theorem integralTwoVectorRestriction_ne_zero_of_mem_span_eval_ne_zero
    {n : ℕ} (f : MvPolynomial (Fin n) ℤ) (v w : IntVector n)
    (x : Fin n → ℚ)
    (hx : x ∈ Submodule.span ℚ
      ({(fun i ↦ (v i : ℚ)), (fun i ↦ (w i : ℚ))} : Set (Fin n → ℚ)))
    (heval : eval x (map (Int.castRingHom ℚ) f) ≠ 0) :
    integralTwoVectorRestriction f v w ≠ 0 := by
  intro hzero
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hx
  apply heval
  rw [← hab]
  exact eval_rationalTwoVectorCombination_eq_zero_of_restriction_eq_zero
    f v w hzero a b

end

end TranslatedDepthSeven

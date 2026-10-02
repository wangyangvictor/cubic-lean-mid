import TranslatedDepthSeven.PrimitiveProjectiveCurveFirstChartCountInternal

/-! Fixed-form primitive integer counting on all three projective charts.
Coordinate permutations preserve the literal gcd-one condition and box.
The chart cover counts both signs; overlap only increases the upper bound. -/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
open scoped BigOperators
set_option maxHeartbeats 3000000

theorem IsPrimitiveIntVector.comp_equiv {ι : Type*} [Fintype ι]
    {x : ι → ℤ} (hx : IsPrimitiveIntVector x) (e : Equiv.Perm ι) :
    IsPrimitiveIntVector (x ∘ e) := by
  classical
  apply Nat.dvd_one.mp
  change intVectorContent (x ∘ e) ∣ 1
  rw [← hx]
  apply Finset.dvd_gcd
  intro i _
  have h := Finset.gcd_dvd (s := Finset.univ)
    (f := fun j ↦ ((x ∘ e) j).natAbs) (b := e.symm i) (Finset.mem_univ _)
  simpa [Function.comp_def] using h

theorem IsPrimitiveIntVector.exists_nonzero_coordinate
    {ι : Type*} [Fintype ι] {x : ι → ℤ} (hx : IsPrimitiveIntVector x) :
    ∃ i, x i ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  have hzero : intVectorContent x = 0 :=
    Finset.gcd_eq_zero_iff.mpr (fun i _ ↦ by simp [h i])
  change intVectorContent x = 1 at hx
  omega

/-- For a fixed rationally irreducible homogeneous ternary form of degree
at least two, all primitive integer zeros in a closed box number O_P(B).
The constant precedes every height and every finite set of points. -/
theorem exists_primitivePlaneCurve_linear_count
    {d : ℕ} (hd : 2 ≤ d)
    (P : MvPolynomial (Fin 3) ℤ) (hPhom : P.IsHomogeneous d)
    (hPirred : Irreducible (P.map (Int.castRingHom ℚ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℕ, 1 ≤ B → ∀ S : Finset (Fin 3 → ℤ),
      (∀ x ∈ S, IsPrimitiveIntVector x) →
      (∀ x ∈ S, eval x P = 0) →
      (∀ x ∈ S, ∀ i, (x i).natAbs ≤ B) →
      (S.card : ℝ) ≤ C * B := by
  classical
  let e : Fin 3 → Equiv.Perm (Fin 3) := fun j ↦ Equiv.swap 0 j
  let P' : Fin 3 → MvPolynomial (Fin 3) ℤ := fun j ↦ rename (e j) P
  have hchart (j : Fin 3) := exists_primitivePlaneCurve_firstChart_linear_count
    hd (P' j) hPhom.rename_isHomogeneous
    (show Irreducible ((P' j).map (Int.castRingHom ℚ)) from by
      rw [show (P' j).map (Int.castRingHom ℚ) =
          renameEquiv ℚ (e j) (P.map (Int.castRingHom ℚ)) by
        exact map_rename _ _ _]
      exact hPirred.map (renameEquiv ℚ (e j)))
  choose C hCpos hCcount using hchart
  have hC : 0 < ∑ j : Fin 3, C j := by
    exact Finset.sum_pos (fun j _ ↦ hCpos j) (by simp)
  refine ⟨∑ j : Fin 3, C j, hC, ?_⟩
  intro B hB S hprimitive hzero hbox
  let T : Fin 3 → Finset (Fin 3 → ℤ) := fun j ↦ S.filter (fun x ↦ x j ≠ 0)
  have hcover : S ⊆ Finset.univ.biUnion T := by
    intro x hx
    obtain ⟨j, hj⟩ := (hprimitive x hx).exists_nonzero_coordinate
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hx, hj⟩⟩
  have hcard : S.card ≤ ∑ j : Fin 3, (T j).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hbound (j : Fin 3) : ((T j).card : ℝ) ≤ C j * B := by
    let f : (Fin 3 → ℤ) → (Fin 3 → ℤ) := fun x ↦ x ∘ (e j).symm
    have hf : Function.Injective f := by
      intro x y h
      funext i
      have hh := congrFun h ((e j) i)
      simpa [f] using hh
    have heval (x : Fin 3 → ℤ) : eval (f x) (P' j) = eval x P := by
      rw [show P' j = rename (e j) P from rfl, eval_rename]
      have hpoint : f x ∘ (e j) = x := by
        funext i
        simp [f]
      rw [hpoint]
    have h := hCcount j B hB ((T j).image f)
    rw [Finset.card_image_of_injective _ hf] at h
    apply h
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact (hprimitive x (Finset.mem_filter.mp hx).1).comp_equiv (e j).symm
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      simpa [f, e] using (Finset.mem_filter.mp hx).2
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      rw [heval]
      exact hzero x (Finset.mem_filter.mp hx).1
    · intro y hy i
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact hbox x (Finset.mem_filter.mp hx).1 ((e j).symm i)
  calc
    (S.card : ℝ) ≤ ∑ j : Fin 3, ((T j).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ j : Fin 3, C j * B := Finset.sum_le_sum (fun j _ ↦ hbound j)
    _ = (∑ j : Fin 3, C j) * B := by rw [Finset.sum_mul]

end
end TranslatedDepthSeven

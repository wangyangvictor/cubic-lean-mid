import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Module

/-!
# Clifford dimension obstructions

Actual finite-dimensional linear algebra, with no geometric or table-entry
assumptions. This is a component of Lemma 7.4 of the supplied manuscript.
-/

namespace HessianTheorem11.CliffordDivisibility

open Module

variable {K V : Type*} [Field K] [CharZero K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
theorem det_ne_zero_of_involution (A : Module.End K V) (hA : A * A = 1) :
    LinearMap.det A ≠ 0 := by
  have h := congrArg LinearMap.det hA
  simp only [map_mul, map_one] at h
  intro hz
  rw [hz, zero_mul] at h
  exact zero_ne_one h

omit [FiniteDimensional K V] in
/-- Two invertible anticommuting maps force even dimension. Taking
determinants avoids choosing eigenspaces for this first obstruction. -/
theorem even_finrank_of_anticommuting
    (A B : Module.End K V)
    (hA : LinearMap.det A ≠ 0) (hB : LinearMap.det B ≠ 0)
    (hab : A * B = -(B * A)) : Even (Module.finrank K V) := by
  have hdet : LinearMap.det A * LinearMap.det B =
      (-1 : K) ^ Module.finrank K V *
        (LinearMap.det B * LinearMap.det A) := by
    calc
      _ = LinearMap.det (A * B) := (map_mul LinearMap.det A B).symm
      _ = LinearMap.det (-(B * A)) := congrArg LinearMap.det hab
      _ = _ := by rw [← neg_one_smul K (B * A), LinearMap.det_smul, map_mul]
  have hp : (-1 : K) ^ Module.finrank K V = 1 := by
    apply mul_right_cancel₀ (mul_ne_zero hB hA)
    calc
      (-1 : K) ^ Module.finrank K V *
          (LinearMap.det B * LinearMap.det A) =
          LinearMap.det A * LinearMap.det B := hdet.symm
      _ = 1 * (LinearMap.det B * LinearMap.det A) := by ring
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : K) ≠ 1)).mp hp

omit [FiniteDimensional K V] in
theorem two_dvd_finrank_of_anticommuting_involutions
    (A B : Module.End K V) (hA : A * A = 1) (hB : B * B = 1)
    (hab : A * B = -(B * A)) : 2 ∣ Module.finrank K V := by
  exact even_iff_two_dvd.mp
    (even_finrank_of_anticommuting A B
      (det_ne_zero_of_involution A hA) (det_ne_zero_of_involution B hB) hab)

omit [CharZero K] [FiniteDimensional K V] in
theorem involution_apply_twice (A : Module.End K V) (hA : A * A = 1) (v : V) :
    A (A v) = v := by
  have h := congrArg (fun f : Module.End K V => f v) hA
  simpa only [Module.End.mul_apply, Module.End.one_apply] using h

omit [CharZero K] [FiniteDimensional K V] in
theorem anticommuting_apply (A B : Module.End K V)
    (hab : A * B = -(B * A)) (v : V) : A (B v) = -(B (A v)) := by
  have h := congrArg (fun f : Module.End K V => f v) hab
  simpa only [Module.End.mul_apply, LinearMap.neg_apply] using h

omit [FiniteDimensional K V] in
theorem involution_eigenspace_sup (A : Module.End K V) (hA : A * A = 1) :
    A.eigenspace 1 ⊔ A.eigenspace (-1) = ⊤ := by
  apply top_unique
  intro v _
  rw [Submodule.mem_sup]
  refine ⟨(2 : K)⁻¹ • (v + A v), ?_, (2 : K)⁻¹ • (v - A v), ?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff]
    simp [map_smul, map_add, involution_apply_twice A hA, add_comm]
  · rw [Module.End.mem_eigenspace_iff]
    simp only [map_smul, map_sub, involution_apply_twice A hA, neg_smul, one_smul]
    module
  · have ht : (2 : K) ≠ 0 := by norm_num
    calc
      _ = ((2 : K)⁻¹ * 2) • v := by module
      _ = v := by rw [inv_mul_cancel₀ ht, one_smul]

theorem involution_eigenspace_disjoint (A : Module.End K V) :
    Disjoint (A.eigenspace 1) (A.eigenspace (-1)) := by
  rw [Submodule.disjoint_def]
  intro v hp hm
  have hp' : A v = v := by simpa using (Module.End.mem_eigenspace_iff.mp hp)
  have hm' : A v = -v := by simpa using (Module.End.mem_eigenspace_iff.mp hm)
  have hz : (2 : K) • v = 0 := by
    calc
      _ = v + v := two_smul K v
      _ = A v + v := by rw [hp']
      _ = -v + v := by rw [hm']
      _ = 0 := neg_add_cancel v
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

noncomputable def eigenspaceSwap (A B : Module.End K V)
    (hB : B * B = 1) (hab : A * B = -(B * A)) :
    A.eigenspace 1 ≃ₗ[K] A.eigenspace (-1) where
  toFun v := ⟨B v, by
    rw [Module.End.mem_eigenspace_iff]
    have hv : A v = v := by simpa using Module.End.mem_eigenspace_iff.mp v.property
    rw [anticommuting_apply A B hab, hv]
    simp⟩
  invFun v := ⟨B v, by
    rw [Module.End.mem_eigenspace_iff]
    have hv : A v = -v := by simpa using Module.End.mem_eigenspace_iff.mp v.property
    rw [anticommuting_apply A B hab, hv]
    simp⟩
  left_inv v := by
    apply Subtype.ext
    exact involution_apply_twice B hB v
  right_inv v := by
    apply Subtype.ext
    exact involution_apply_twice B hB v
  map_add' v w := by apply Subtype.ext; exact B.map_add v w
  map_smul' c v := by apply Subtype.ext; exact B.map_smul c v

theorem finrank_eq_twice_eigenspace (A B : Module.End K V)
    (hA : A * A = 1) (hB : B * B = 1) (hab : A * B = -(B * A)) :
    Module.finrank K V = 2 * Module.finrank K (A.eigenspace 1) := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (A.eigenspace 1) (A.eigenspace (-1))
  rw [involution_eigenspace_sup A hA, (involution_eigenspace_disjoint A).eq_bot,
    finrank_top, finrank_bot, add_zero] at hdim
  rw [← (eigenspaceSwap A B hB hab).finrank_eq] at hdim
  omega

omit [FiniteDimensional K V] in
theorem det_ne_zero_of_square_neg_one (A : Module.End K V)
    (hA : A * A = -1) : LinearMap.det A ≠ 0 := by
  have h : LinearMap.det (A * A) ≠ 0 := by
    rw [hA, ← neg_one_smul K (1 : Module.End K V), LinearMap.det_smul,
      map_one, mul_one]
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  rw [map_mul] at h
  exact (mul_ne_zero_iff.mp h).1

omit [CharZero K] [FiniteDimensional K V] in
theorem anticommuting_reverse (A B : Module.End K V)
    (h : A * B = -(B * A)) : B * A = -(A * B) := by
  have hn := congrArg Neg.neg h
  simpa only [neg_neg] using hn.symm

omit [CharZero K] [FiniteDimensional K V] in
theorem commute_product_of_anticommuting (A B C : Module.End K V)
    (hAB : A * B = -(B * A)) (hAC : A * C = -(C * A)) :
    A * (B * C) = (B * C) * A := by
  calc
    _ = (A * B) * C := (mul_assoc _ _ _).symm
    _ = (-(B * A)) * C := by rw [hAB]
    _ = -(B * (A * C)) := by simp only [neg_mul, mul_assoc]
    _ = -(B * (-(C * A))) := by rw [hAC]
    _ = _ := by simp only [mul_neg, neg_neg, mul_assoc]

omit [CharZero K] [FiniteDimensional K V] in
theorem involution_product_mul (B C D : Module.End K V)
    (hB : B * B = 1) (hBC : B * C = -(C * B)) :
    (B * C) * (B * D) = -(C * D) := by
  calc
    _ = B * (C * B) * D := by simp only [mul_assoc]
    _ = B * (-(B * C)) * D := by rw [anticommuting_reverse B C hBC]
    _ = -((B * B) * (C * D)) := by simp only [mul_neg, neg_mul, mul_assoc]
    _ = _ := by rw [hB, one_mul]

theorem product_square_neg_one (B C : Module.End K V)
    (hB : B * B = 1) (hC : C * C = 1)
    (hBC : B * C = -(C * B)) : (B * C) * (B * C) = -1 := by
  rw [involution_product_mul B C C hB hBC, hC]

theorem products_anticommute (B C D : Module.End K V)
    (hB : B * B = 1) (hBC : B * C = -(C * B))
    (hBD : B * D = -(D * B)) (hCD : C * D = -(D * C)) :
    (B * C) * (B * D) = -((B * D) * (B * C)) := by
  rw [involution_product_mul B C D hB hBC,
    involution_product_mul B D C hB hBD, neg_neg, hCD, neg_neg]

omit [CharZero K] [FiniteDimensional K V] in
theorem preserves_eigenspace_one_of_commute (A P : Module.End K V)
    (hAP : A * P = P * A) :
    ∀ v ∈ A.eigenspace 1, P v ∈ A.eigenspace 1 := by
  intro v hv
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have h := congrArg (fun f : Module.End K V => f v) hAP
  simp only [Module.End.mul_apply] at h
  rw [h, hv, one_smul, one_smul]

/-- The `2^(4/2)` divisibility from Lemma 7.4, proved directly. Products
`BC` and `BD` act on the +1 eigenspace of `A` and force its dimension even;
`B` identifies the +1 and -1 eigenspaces. No algebraic closure is required. -/
theorem four_dvd_finrank_of_four_anticommuting_involutions
    (A B C D : Module.End K V)
    (hA : A * A = 1) (hB : B * B = 1)
    (hC : C * C = 1) (hD : D * D = 1)
    (hAB : A * B = -(B * A)) (hAC : A * C = -(C * A))
    (hAD : A * D = -(D * A)) (hBC : B * C = -(C * B))
    (hBD : B * D = -(D * B)) (hCD : C * D = -(D * C)) :
    4 ∣ Module.finrank K V := by
  let W := A.eigenspace 1
  have hp : ∀ v ∈ W, (B * C) v ∈ W :=
    preserves_eigenspace_one_of_commute A (B * C)
      (commute_product_of_anticommuting A B C hAB hAC)
  have hq : ∀ v ∈ W, (B * D) v ∈ W :=
    preserves_eigenspace_one_of_commute A (B * D)
      (commute_product_of_anticommuting A B D hAB hAD)
  let P : Module.End K W := (B * C).restrict hp
  let Q : Module.End K W := (B * D).restrict hq
  have hP : P * P = -1 := by
    ext v
    change (B * C) ((B * C) (v : V)) = -(v : V)
    have h := congrArg (fun f : Module.End K V => f (v : V))
      (product_square_neg_one B C hB hC hBC)
    simpa only [Module.End.mul_apply, LinearMap.neg_apply, Module.End.one_apply] using h
  have hQ : Q * Q = -1 := by
    ext v
    change (B * D) ((B * D) (v : V)) = -(v : V)
    have h := congrArg (fun f : Module.End K V => f (v : V))
      (product_square_neg_one B D hB hD hBD)
    simpa only [Module.End.mul_apply, LinearMap.neg_apply, Module.End.one_apply] using h
  have hPQ : P * Q = -(Q * P) := by
    ext v
    change (B * C) ((B * D) (v : V)) = -((B * D) ((B * C) (v : V)))
    have h := congrArg (fun f : Module.End K V => f (v : V))
      (products_anticommute B C D hB hBC hBD hCD)
    simpa only [Module.End.mul_apply, LinearMap.neg_apply] using h
  have heven : Even (Module.finrank K W) :=
    even_finrank_of_anticommuting P Q
      (det_ne_zero_of_square_neg_one P hP) (det_ne_zero_of_square_neg_one Q hQ) hPQ
  obtain ⟨k, hk⟩ := heven
  have hdim := finrank_eq_twice_eigenspace A B hA hB hAB
  change Module.finrank K V = 2 * Module.finrank K W at hdim
  refine ⟨k, ?_⟩
  omega

/-- A nondegenerate skew-symmetric bilinear form has even dimension,
proved by comparing the determinant of its Gram matrix with its transpose. -/
theorem even_finrank_of_nondegenerate_skew_form
    (β : LinearMap.BilinForm K V) (hβ : β.Nondegenerate)
    (hskew : ∀ v w, β v w = -β w v) : Even (Module.finrank K V) := by
  classical
  let b := Module.finBasis K V
  let M := BilinForm.toMatrix b β
  have hd : Matrix.det M ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hβ
  have ht : M.transpose = -M := by
    ext i j
    simpa [M, Matrix.transpose_apply] using hskew (b j) (b i)
  have heq := congrArg Matrix.det ht
  rw [Matrix.det_transpose, Matrix.det_neg] at heq
  have hp : (-1 : K) ^ Module.finrank K V = 1 := by
    apply mul_right_cancel₀ hd
    simpa [M, b] using heq.symm
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : K) ≠ 1)).mp hp

omit [FiniteDimensional K V] in
theorem eigenspaces_orthogonal_of_self_adjoint
    (β : LinearMap.BilinForm K V) (A : Module.End K V)
    (hself : ∀ v w, β (A v) w = β v (A w))
    {v w : V} (hv : v ∈ A.eigenspace 1) (hw : w ∈ A.eigenspace (-1)) :
    β v w = 0 := by
  have hv' : A v = v := by simpa using Module.End.mem_eigenspace_iff.mp hv
  have hw' : A w = -w := by simpa using Module.End.mem_eigenspace_iff.mp hw
  have h := hself v w
  rw [hv', hw', map_neg] at h
  exact CharZero.eq_neg_self_iff.mp h

theorem nondegenerate_restrict_involution_eigenspace
    (β : LinearMap.BilinForm K V) (hβ : β.Nondegenerate)
    (A : Module.End K V) (hA : A * A = 1)
    (hself : ∀ v w, β (A v) w = β v (A w)) :
    (β.restrict (A.eigenspace 1)).Nondegenerate := by
  intro v hv
  apply Subtype.ext
  apply hβ (v : V)
  intro y
  have hy : y ∈ A.eigenspace 1 ⊔ A.eigenspace (-1) := by
    rw [involution_eigenspace_sup A hA]
    trivial
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
  have hu0 : β (v : V) u = 0 := hv ⟨u, hu⟩
  rw [map_add, hu0, eigenspaces_orthogonal_of_self_adjoint β A hself v.property hw,
    add_zero]

/-- The additional symmetric-form divisibility in Lemma 7.4: three
anticommuting involutions self-adjoint for one common nondegenerate symmetric
form force dimension divisible by four. -/
theorem four_dvd_finrank_of_three_self_adjoint_anticommuting_involutions
    (β : LinearMap.BilinForm K V) (hβ : β.Nondegenerate) (hsym : β.IsSymm)
    (A B C : Module.End K V)
    (hA : A * A = 1) (hB : B * B = 1) (hC : C * C = 1)
    (hAB : A * B = -(B * A)) (hAC : A * C = -(C * A))
    (hBC : B * C = -(C * B))
    (hsA : ∀ v w, β (A v) w = β v (A w))
    (hsB : ∀ v w, β (B v) w = β v (B w))
    (hsC : ∀ v w, β (C v) w = β v (C w)) :
    4 ∣ Module.finrank K V := by
  let W := A.eigenspace 1
  have hp : ∀ v ∈ W, (B * C) v ∈ W :=
    preserves_eigenspace_one_of_commute A (B * C)
      (commute_product_of_anticommuting A B C hAB hAC)
  let P : Module.End K W := (B * C).restrict hp
  have hP : P * P = -1 := by
    ext v
    change (B * C) ((B * C) (v : V)) = -(v : V)
    have h := congrArg (fun f : Module.End K V => f (v : V))
      (product_square_neg_one B C hB hC hBC)
    simpa only [Module.End.mul_apply, LinearMap.neg_apply, Module.End.one_apply] using h
  let βW : LinearMap.BilinForm K W := β.restrict W
  have hnW : βW.Nondegenerate :=
    nondegenerate_restrict_involution_eigenspace β hβ A hA hsA
  let γ : LinearMap.BilinForm K W := βW.compRight P
  have hnγ : γ.Nondegenerate := by
    intro v hv
    apply hnW v
    intro w
    have h := hv (P w)
    change βW v (P (P w)) = 0 at h
    have hpw : P (P w) = -w := by
      have ht := congrArg (fun f : Module.End K W => f w) hP
      simpa only [Module.End.mul_apply, LinearMap.neg_apply, Module.End.one_apply] using ht
    rw [hpw, map_neg] at h
    exact neg_eq_zero.mp h
  have hskew : ∀ v w, γ v w = -γ w v := by
    intro v w
    change β (v : V) (B (C (w : V))) = -β (w : V) (B (C (v : V)))
    calc
      _ = β (B (v : V)) (C (w : V)) := (hsB _ _).symm
      _ = β (C (B (v : V))) (w : V) := (hsC _ _).symm
      _ = β (-(B (C (v : V)))) (w : V) := by
        rw [anticommuting_apply C B (anticommuting_reverse B C hBC)]
      _ = -β (B (C (v : V))) (w : V) := by simp
      _ = _ := congrArg Neg.neg (hsym.eq _ _)
  obtain ⟨k, hk⟩ := even_finrank_of_nondegenerate_skew_form γ hnγ hskew
  have hdim := finrank_eq_twice_eigenspace A B hA hB hAB
  change Module.finrank K V = 2 * Module.finrank K W at hdim
  refine ⟨k, ?_⟩
  omega

end HessianTheorem11.CliffordDivisibility

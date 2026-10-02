import CubicTenVariables.ZeroPatch
import CubicTenVariables.OpenPolynomialNonvanishing
import CubicTenVariables.RationalElimination

/-! Polynomial avoidance on an actual smooth hypersurface patch.

A displayed elimination identity reduces nonvanishing on the hypersurface
to nonvanishing of a polynomial in the free coordinates of the actual
implicit-function patch. The first two lemmas use that identity explicitly;
the final theorem constructs it from rational irreducibility and nondivisibility.
There is no density or local-solubility premise hidden in the conclusion.
-/

noncomputable section
namespace CubicTenVariables.LocalPolynomialAvoidance
open MvPolynomial

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]

/-- An actual nonzero eliminant prevents a polynomial from vanishing on
every point of any prescribed smooth local hypersurface patch. -/
theorem exists_zero_avoiding_of_elimination_identity {m : ℕ}
    (F D A B : MvPolynomial (Fin (m + 1)) K) (i : Fin (m + 1))
    (R : MvPolynomial (Fin m) K) (hR : R ≠ 0)
    (hidentity : A * F + B * D = rename i.succAbove R)
    (x : Fin (m + 1) → K) (hFx : eval x F = 0)
    (hi : eval x (pderiv i F) ≠ 0)
    (U : Set (Fin (m + 1) → K)) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ z ∈ U, eval z F = 0 ∧ eval z (pderiv i F) ≠ 0 ∧ eval z D ≠ 0 := by
  obtain ⟨V, hV, _, hne, hpatch⟩ :=
    ZeroPatch.exists_open_zero_patch F i x hFx hi U hU hxU
  obtain ⟨y, hy, hRy⟩ :=
    OpenPolynomialNonvanishing.exists_eval_ne_zero_mem_open R hR V hV hne
  obtain ⟨z, hzU, hFz, hiz, hzy⟩ := hpatch y hy
  refine ⟨z, hzU, hFz, hiz, ?_⟩
  intro hDz
  have he := congrArg (eval z) hidentity
  have hzR : eval z (rename i.succAbove R) = eval y R := by
    rw [eval_rename]
    change eval (i.removeNth z) R = eval y R
    rw [hzy]
  have : eval y R = 0 := by
    rw [eval_add, eval_mul, eval_mul, hFz, hDz, mul_zero, mul_zero, zero_add, hzR] at he
    exact he.symm
  exact hRy this

/-- A rational elimination identity works on a smooth patch over any
complete nontrivially normed extension field, without assuming that the
rational cubic remains anisotropic or irreducible over that field. -/
theorem exists_zero_avoiding_of_rational_elimination_identity [Algebra ℚ K] {m : ℕ}
    (F D A B : MvPolynomial (Fin (m + 1)) ℚ) (i : Fin (m + 1))
    (R : MvPolynomial (Fin m) ℚ) (hR : R ≠ 0)
    (hidentity : A * F + B * D = rename i.succAbove R)
    (x : Fin (m + 1) → K) (hFx : eval₂ (algebraMap ℚ K) x F = 0)
    (hi : eval₂ (algebraMap ℚ K) x (pderiv i F) ≠ 0)
    (U : Set (Fin (m + 1) → K)) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ z ∈ U, eval₂ (algebraMap ℚ K) z F = 0 ∧
      eval₂ (algebraMap ℚ K) z (pderiv i F) ≠ 0 ∧
      eval₂ (algebraMap ℚ K) z D ≠ 0 := by
  let φ := algebraMap ℚ K
  have hR' : map φ R ≠ 0 := by
    intro h
    apply hR
    apply map_injective φ φ.injective
    simpa using h
  have hid : map φ A * map φ F + map φ B * map φ D =
      rename i.succAbove (map φ R) := by
    simpa only [map_add, map_mul, map_rename] using congrArg (map φ) hidentity
  obtain ⟨z, hzU, hFz, hiz, hDz⟩ := exists_zero_avoiding_of_elimination_identity
    (map φ F) (map φ D) (map φ A) (map φ B) i (map φ R) hR' hid x
    (by simpa only [eval_map] using hFx)
    (by simpa only [pderiv_map, eval_map] using hi) U hU hxU
  exact ⟨z, hzU, by simpa only [eval_map] using hFz,
    by simpa only [pderiv_map, eval_map] using hiz,
    by simpa only [eval_map] using hDz⟩

/-- An irreducible rational hypersurface locally avoids every rational
polynomial not divisible by its equation, near any supplied smooth point
over a complete normed extension field. All elimination data are constructed. -/
theorem exists_zero_avoiding_rational_polynomial [Algebra ℚ K] {m : ℕ}
    (F D : MvPolynomial (Fin (m + 1)) ℚ) (hF : Irreducible F) (hFD : ¬ F ∣ D)
    (i : Fin (m + 1)) (x : Fin (m + 1) → K)
    (hFx : eval₂ (algebraMap ℚ K) x F = 0)
    (hi : eval₂ (algebraMap ℚ K) x (pderiv i F) ≠ 0)
    (U : Set (Fin (m + 1) → K)) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ z ∈ U, eval₂ (algebraMap ℚ K) z F = 0 ∧
      eval₂ (algebraMap ℚ K) z (pderiv i F) ≠ 0 ∧
      eval₂ (algebraMap ℚ K) z D ≠ 0 := by
  have hpartial : pderiv i F ≠ 0 := by
    intro h
    apply hi
    rw [h, eval₂_zero]
  obtain ⟨A, B, R, hR, hidentity⟩ :=
    RationalElimination.exists_elimination_identity i F D hF hFD hpartial
  exact exists_zero_avoiding_of_rational_elimination_identity F D A B i R hR
    hidentity x hFx hi U hU hxU

end CubicTenVariables.LocalPolynomialAvoidance

import CubicTenVariables.FixedLeadingSurfaceParallelLineTransport
import CubicTenVariables.FixedLeadingSurfaceLineDirectionSum

/-!
# Multiplicity of actual projective line directions

Primitive integral vectors representing the same projective point differ
only by sign. The coordinate-parallel d² bound therefore controls each
projective-direction fibre of any finite family of distinct actual affine
lines. Directional dependence is retained explicitly until it is supplied
by absolute irreducibility of the leading ternary form.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceDirectionMultiplicity

open MvPolynomial TranslatedDepthSeven
open HessianTheorem11.PolynomialRestriction
open FrameRestrictionIrreducibility FixedLeadingSurfaceParallelLineTransport
open FixedLeadingSurfaceLineDirectionSum

local instance : DecidableEq (Projectivization ℚ (Fin 3 → ℚ)) := Classical.decEq _

def rationalVector (v : Fin 3 → ℤ) : Fin 3 → ℚ := fun i => (v i : ℚ)

theorem rationalVector_ne_zero (v : Fin 3 → ℤ) (hv : v ≠ 0) :
    rationalVector v ≠ 0 := by
  intro h
  apply hv
  ext i
  have hi := congrFun h i
  change (v i : ℚ) = 0 at hi
  exact_mod_cast hi

theorem rationalVector_neg (v : Fin 3 → ℤ) : rationalVector (-v) = -rationalVector v := by
  ext i
  simp [rationalVector]

theorem affineLine_neg_direction (base v : Fin 3 → ℚ) :
    affineLine base (-v) = affineLine base v := by
  ext x
  constructor <;> rintro ⟨t, rfl⟩
  · exact ⟨-t, by simp⟩
  · exact ⟨-t, by simp⟩

theorem affineLine_eq_of_directionClass_eq
    (base : Fin 3 → ℚ) (h k : Fin 3 → ℤ)
    (hh : PrimitiveDirection h) (hk : PrimitiveDirection k)
    (heq : directionClass k hk = directionClass h hh) :
    affineLine base (rationalVector k) = affineLine base (rationalVector h) := by
  rcases eq_or_neg_of_primitive_integralProjectiveClass_eq h k hh hk
      (primitiveDirection_ne_zero hh) (primitiveDirection_ne_zero hk) heq with he | he
  · rw [he]
  · rw [he, rationalVector_neg, affineLine_neg_direction]

/-- A proven parallel-line bound supplies the multiplicity hypothesis in
the height summation theorem. The family is required to have distinct
underlying lines, rather than merely distinct labels. -/
theorem projective_direction_fibre_card_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ℕ} (hd : 1 ≤ d) (g : MvPolynomial (Fin 3) ℚ)
    (hdegree : g.totalDegree ≤ d) (hg : Irreducible g)
    (hdir : ∀ e : (Fin 3 → ℚ) ≃ₗ[ℚ] (Fin 3 → ℚ),
      0 < (restrict (coordinateMatrix e) g).degreeOf 0)
    (base h : ι → Fin 3 → ℤ) (hp : ∀ l, PrimitiveDirection (h l))
    (hdistinct : Function.Injective (fun l =>
      affineLine (rationalVector (base l)) (rationalVector (h l))))
    (hline : ∀ l, ∀ t : ℚ,
      eval (rationalVector (base l) + t • rationalVector (h l)) g = 0)
    (P : Projectivization ℚ (Fin 3 → ℚ)) :
    (Finset.univ.filter fun l => directionClass (h l) (hp l) = P).card ≤ d ^ 2 := by
  classical
  let J := {l : ι // directionClass (h l) (hp l) = P}
  have hcard : (Finset.univ.filter fun l => directionClass (h l) (hp l) = P).card =
      Fintype.card J := by simp [J, Fintype.card_subtype]
  rw [hcard]
  by_cases hJ : Nonempty J
  · let l₀ : J := Classical.choice hJ
    let v := rationalVector (h l₀.val)
    have hv : v ≠ 0 := rationalVector_ne_zero _ (primitiveDirection_ne_zero (hp l₀.val))
    obtain ⟨e, he⟩ := exists_direction_coordinates v hv
    have hclass (l : J) : directionClass (h l.val) (hp l.val) =
        directionClass (h l₀.val) (hp l₀.val) := l.property.trans l₀.property.symm
    have hsets (l : J) : affineLine (rationalVector (base l.val))
        (rationalVector (h l.val)) = affineLine (rationalVector (base l.val)) v :=
      affineLine_eq_of_directionClass_eq _ _ _ (hp l₀.val) (hp l.val) (hclass l)
    apply parallel_line_family_card_le hd g hdegree hg e v he (hdir e)
      (fun l : J => rationalVector (base l.val))
    · intro l l' heq
      apply Subtype.ext
      apply hdistinct
      dsimp only
      rw [hsets l, hsets l']
      exact heq
    · intro l t
      have hx : rationalVector (base l.val) + t • v ∈
          affineLine (rationalVector (base l.val)) v := ⟨t, rfl⟩
      rw [← hsets l] at hx
      obtain ⟨u, hu⟩ := hx
      rw [← hu]
      exact hline l.val u
  · haveI : IsEmpty J := not_nonempty_iff.mp hJ
    simp

end CubicTenVariables.FixedLeadingSurfaceDirectionMultiplicity

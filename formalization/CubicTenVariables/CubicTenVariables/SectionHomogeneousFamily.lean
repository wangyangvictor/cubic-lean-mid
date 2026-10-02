import CubicTenVariables.TerminalSectionIncidence
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! The literal section-incidence family, homogeneous in the point variables.
The coefficient variables are the normal coordinates. Specialization retains
all three kinds of incidence equations, including the cubic equation. -/

noncomputable section
namespace CubicTenVariables.SectionHomogeneousFamily
open MvPolynomial HessianTheorem11 TerminalSectionIncidence
open scoped BigOperators

/-- Two distinguished equations, followed by the ordered normal minors. -/
abbrev Index (n : ℕ) := Fin 2 ⊕ (Fin n × Fin n)

variable {n : ℕ} {K : Type*} [CommRing K]

/-- The cubic is constant in the normal-parameter variables. -/
def formEquation (F : MvPolynomial (Fin n) K) :
    MvPolynomial (Fin n) (MvPolynomial (Fin n) K) := map C F

/-- The outer variable is x and the coefficient variable is v: sum v_i x_i. -/
def dotEquation (n : ℕ) (K : Type*) [CommRing K] :
    MvPolynomial (Fin n) (MvPolynomial (Fin n) K) :=
  ∑ i : Fin n, C (X i) * X i

/-- The literal equation v_i F_j(x)-v_j F_i(x). -/
def minorEquation (F : MvPolynomial (Fin n) K) (i j : Fin n) :
    MvPolynomial (Fin n) (MvPolynomial (Fin n) K) :=
  C (X i) * map C (pderiv j F) - C (X j) * map C (pderiv i F)

def equation (F : MvPolynomial (Fin n) K) :
    Index n → MvPolynomial (Fin n) (MvPolynomial (Fin n) K)
  | Sum.inl k => if k = 0 then formEquation F else dotEquation n K
  | Sum.inr (i,j) => minorEquation F i j

/-- Degrees are measured only in the outer (point) variables. -/
def degree : Index n → ℕ
  | Sum.inl k => if k = 0 then 3 else 1
  | Sum.inr _ => 2

theorem degree_pos (i : Index n) : 0 < degree i := by
  rcases i with k | ⟨i,j⟩
  · change 0 < (if k = 0 then 3 else 1)
    split <;> norm_num
  · norm_num [degree]

@[simp] theorem specialize_formEquation (F : MvPolynomial (Fin n) K) (v : Fin n → K) :
    map (eval v) (formEquation F) = F := by
  have he : (eval v).comp (C : K →+* MvPolynomial (Fin n) K) = RingHom.id K := by
    ext a
    exact eval_C a
  rw [formEquation,map_map,he,map_id]

@[simp] theorem specialize_dotEquation (v : Fin n → K) :
    map (eval v) (dotEquation n K) = ∑ i : Fin n, C (v i)*X i := by
  simp only [dotEquation,map_sum,map_mul,map_C,eval_X,map_X]

@[simp] theorem specialize_minorEquation (F : MvPolynomial (Fin n) K)
    (v : Fin n → K) (i j : Fin n) :
    map (eval v) (minorEquation F i j) = C (v i)*pderiv j F-C (v j)*pderiv i F := by
  change map (eval v)
    (C (X i)*formEquation (pderiv j F)-C (X j)*formEquation (pderiv i F)) = _
  rw [map_sub,map_mul,map_mul,map_C,map_C,eval_X,eval_X,
    specialize_formEquation,specialize_formEquation]

/-- The outer cubic, linear equation and quadratic normal minors have
exactly their specified homogeneous degrees (zero equations included). -/
theorem equation_isHomogeneous (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (i : Index n) :
    (equation F i).IsHomogeneous (degree i) := by
  have hdot : (dotEquation n K).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_C_mul_X (X i) i)
  have hminor (i j : Fin n) : (minorEquation F i j).IsHomogeneous 2 := by
    have hi : (pderiv i F).IsHomogeneous 2 := hF.pderiv
    have hj : (pderiv j F).IsHomogeneous 2 := hF.pderiv
    exact ((hj.map C).C_mul (X i)).sub ((hi.map C).C_mul (X j))
  rcases i with k | ⟨i,j⟩
  · fin_cases k
    · exact hF.map C
    · exact hdot
  · exact hminor i j

/-- Evaluating first at a normal parameter and then at a point yields
exactly F(x), v.x and the displayed gradient minors. -/
theorem eval_equation (F : MvPolynomial (Fin n) K) (v x : Fin n → K) :
    (∀ i, eval x (map (eval v) (equation F i)) = 0) ↔
      x ∈ sectionSingularFiber F v := by
  have hdot : eval x (map (eval v) (dotEquation n K)) = dotProduct v x := by
    rw [specialize_dotEquation]
    simp only [map_sum,eval_mul,eval_C,eval_X,dotProduct]
  have hminor (i j : Fin n) :
      eval x (map (eval v) (minorEquation F i j)) =
        v i*gradient F x j-v j*gradient F x i := by
    rw [specialize_minorEquation]
    simp only [eval_sub,eval_mul,eval_C,gradient]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have hh := h (Sum.inl 0)
      change eval x (map (eval v) (formEquation F)) = 0 at hh
      simpa only [specialize_formEquation] using hh
    · have hh := h (Sum.inl 1)
      change eval x (map (eval v) (dotEquation n K)) = 0 at hh
      simpa only [hdot] using hh
    · intro i j
      simpa only [equation,hminor] using h (Sum.inr (i,j))
  · rintro ⟨hF,hd,hm⟩ i
    rcases i with k | ⟨i,j⟩
    · fin_cases k
      · change eval x (map (eval v) (formEquation F)) = 0
        simpa only [specialize_formEquation] using hF
      · change eval x (map (eval v) (dotEquation n K)) = 0
        simpa only [hdot] using hd
    · simpa only [equation,hminor] using hm i j

/-- The same exact specialization using the eval₂ convention. -/
theorem specialized_zero_iff (F : MvPolynomial (Fin n) K) (v x : Fin n → K) :
    (∀ i, eval₂ (eval v) x (equation F i) = 0) ↔ x ∈ sectionSingularFiber F v := by
  simpa only [eval_map] using eval_equation F v x

/-- Common zeros of the actual specialized homogeneous equations give
the literal section-singularity fiber at every normal, including zero. -/
theorem specialized_zeroSet (F : MvPolynomial (Fin n) K) (v : Fin n → K) :
    {x | ∀ i, eval x (map (eval v) (equation F i)) = 0} = sectionSingularFiber F v := by
  ext x
  exact eval_equation F v x

/-- The actual geometric equation ideal has precisely the required fiber
as its zero locus. No claim of radicality of that ideal is needed. -/
theorem geometric_zeroLocus (F : GeometricPolynomial n) (v : GeometricPoint n) :
    zeroLocus GeometricField (Ideal.span
      (Set.range (fun i => map (eval v) (equation F i)))) = sectionSingularFiber F v := by
  ext x
  rw [zeroLocus_span]
  change (∀ g ∈ Set.range (fun i => map (eval v) (equation F i)), eval x g = 0) ↔ _
  simpa only [Set.forall_mem_range] using eval_equation F v x

end CubicTenVariables.SectionHomogeneousFamily

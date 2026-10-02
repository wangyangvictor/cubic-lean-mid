import HessianTheorem11.CubicDivisorPoint
import HessianTheorem11.CubicNormalFormConstruction
import HessianTheorem11.LocalCubicSchur
import HessianTheorem11.RankNumerics

/-! The first normal rank sieve. Its numerical certificate is constructed
from an actual local cubic and determinant divisor, rather than postulated
as a geometric input. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial LocalCubicNormalForm CubicNormalFormConstruction

/-- Numerical data extracted from the actual generic Hessian and its first
normal quadratic block. This is an intermediate proof object, not an input. -/
structure FirstNormalSieve (n r : ℕ) where
  corank : ℕ
  multiplicity : ℕ
  normalRank : ℕ
  dimension : corank + r = n
  rank_ge_two : 2 ≤ r
  normalRank_le : normalRank ≤ corank
  corank_le_multiplicity : corank ≤ multiplicity
  degree_bound : 3 * multiplicity ≤ n
  normal_bound : 2 * corank ≤ multiplicity + normalRank
  even_middle : 2 ≤ normalRank → 2 ∣ r - 2
  four_middle : 3 ≤ normalRank → 4 ∣ r - 2

namespace FirstNormalSieve

theorem rank_twelve {r : ℕ} (S : FirstNormalSieve 12 r) : 10 ≤ r := by
  have heq : 12 - S.corank - 2 = r - 2 := by have hd := S.dimension; omega
  have hm := RankNumerics.corank_le_two_in_twelve S.corank S.multiplicity S.normalRank
    S.normalRank_le S.corank_le_multiplicity S.degree_bound S.normal_bound
    (by simpa only [heq] using S.even_middle)
    (by simpa only [heq] using S.four_middle)
  have hd := S.dimension
  omega

theorem rank_thirteen {r : ℕ} (S : FirstNormalSieve 13 r) : 10 ≤ r := by
  have heq : 13 - S.corank - 2 = r - 2 := by have hd := S.dimension; omega
  have hm := RankNumerics.corank_le_three_in_thirteen S.corank S.multiplicity S.normalRank
    S.normalRank_le S.corank_le_multiplicity S.degree_bound S.normal_bound
    (by simpa only [heq] using S.even_middle)
  have hd := S.dimension
  omega

theorem rank_eleven_alternative {r : ℕ} (S : FirstNormalSieve 11 r) :
    10 ≤ r ∨ (r = 9 ∧ S.normalRank = 1 ∧ S.multiplicity = 3) := by
  have heq : 11 - S.corank - 2 = r - 2 := by have hd := S.dimension; omega
  have hm := RankNumerics.eleven_remaining_alternative S.corank S.multiplicity S.normalRank
    S.normalRank_le S.corank_le_multiplicity S.degree_bound S.normal_bound
    (by simpa only [heq] using S.even_middle)
    (by simpa only [heq] using S.four_middle)
  have hd := S.dimension
  rcases hm with hm | ⟨hm, hρ, hh⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, hρ, hh⟩

/-- Every hypothesis here refers to the actual displayed polynomial, its
actual Hessian, or its actual determinant factorization. -/
def of_local_cubic
    (FI : FormalImplicitFunctionInput GeometricField)
    {n r m q h : ℕ} (D : Data (K := GeometricField) m q)
    (hirred : Irreducible (polynomial D))
    (hB0 : (quadraticMatrix D.Q0).det ≠ 0)
    (hRank : ∀ x : Coordinate m q → GeometricField, eval x (polynomial D) = 0 →
      ((polynomialHessian D).map (eval x)).rank ≤ q + 2)
    (G : MvPolynomial (Coordinate m q) GeometricField)
    (hG : eval (basePoint m q) G ≠ 0)
    (hdet : (polynomialHessian D).det = polynomial D ^ h * G)
    (hdim : m + r = n) (hq : q + 2 = r)
    (hm : m ≤ h) (hh : 3 * h ≤ n) : FirstNormalSieve n r where
  corank := m
  multiplicity := h
  normalRank := (quadraticMatrix D.QA).rank
  dimension := hdim
  rank_ge_two := by omega
  normalRank_le := by simpa only [Fintype.card_fin] using (quadraticMatrix D.QA).rank_le_card_width
  corank_le_multiplicity := hm
  degree_bound := hh
  normal_bound := normal_rank_bound_of_determinant_factor D hB0 h G hG hdet
  even_middle := by
    intro hP
    have he := two_dvd_of_geometric_rank D FI hirred hB0 hRank hP
    simpa only [← hq, Nat.add_sub_cancel] using he
  four_middle := by
    intro hP
    have he := four_dvd_of_geometric_rank D FI hirred hB0 hRank hP
    simpa only [← hq, Nat.add_sub_cancel] using he

end FirstNormalSieve

theorem coordinateMatrix_basePoint
    {n m q : ℕ} {F : GeometricPolynomial n} {x : GeometricPoint n}
    (S : HyperbolicBasis.Splitting (hessianBilinear F x) x m q) :
    (coordinateMatrix S).mulVec (basePoint m q) = x := by
  rw [coordinateMatrix_mulVec]
  simp [basePoint, xIndex, zIndex, aIndex, bIndex, blockVector, Function.comp_def]

end HessianTheorem11

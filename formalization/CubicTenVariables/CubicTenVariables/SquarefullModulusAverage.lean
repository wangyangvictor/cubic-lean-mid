import CubicTenVariables.SquarefullOnion
import CubicTenVariables.OnionModulusWeightSum
import CubicTenVariables.OnionAverageExponents

/-! The ten-variable squarefull modulus average and its cube-full restriction.
All finite modulus sets and complete cubic sums are literal. -/

noncomputable section
namespace CubicTenVariables.SquarefullModulusAverage
open MvPolynomial HessianTheorem11 SquarefullModulusDecomposition
open scoped BigOperators

/-- The actual positive cube-full integers in the dyadic interval (X,2X]. -/
def cubeFullDyadic (X : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 ⌊2*X⌋₊).filter
    (fun r => X < (r : ℝ) ∧ CubeFullSmithParameters.CubeFull r)

/-- Uniform cumulative average over any finite set of positive squarefull
moduli up to the real cutoff X. No literature input occurs. -/
theorem exists_uniform_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (X : ℝ), 1 ≤ X → ∀ (Q : Finset ℕ),
      (∀ r ∈ Q, 0 < r ∧ SquareFull r ∧ (r : ℝ) ≤ X) →
      ∀ (V : Finset (Fin 10 → ℤ)) (u : Fin 10 → ℝ) (R : ℝ),
      1 ≤ R → (∀ v ∈ V, ∀ i, |(v i : ℝ)-u i| ≤ R) →
      (∑ r ∈ Q, ∑ v ∈ V, ‖completeCubicSum F r v‖) ≤
        K*X^((13:ℝ)/2+ε)*(R+X^((1:ℝ)/3))^10 := by
  obtain ⟨C,hC,hpoint⟩ := SquarefullOnion.exists_complete_sum_bound F hF hA (ε/2) (by positivity)
  obtain ⟨U,hU,hweight⟩ := OnionModulusWeightSum.exists_uniform_bound (ε/2) (by positivity)
  refine ⟨C*U, one_le_mul_of_one_le_of_one_le hC hU, ?_⟩
  intro X hX Q hQ V u R hR hbox
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  let w (r : ℕ) : ℝ := (d r : ℝ)^((1:ℝ)/2)*
    (SquarefreeResidueFactors.d2 (c r) (d r) : ℝ)^((1:ℝ)/2)
  have hw (r : ℕ) : 0 ≤ w r := by dsimp [w]; positivity
  have hsingle (r : ℕ) (hrQ : r ∈ Q) :
      (∑ v ∈ V, ‖completeCubicSum F r v‖) ≤
        (C*X^(6+ε/2)*(R+X^((1:ℝ)/3))^10)*w r := by
    obtain ⟨hr,hsq,hrX⟩ := hQ r hrQ
    letI : NeZero (c r) := ⟨(c_pos r).ne'⟩
    letI : NeZero (d r) := ⟨(d_pos r).ne'⟩
    have hb := hpoint (c r) (d r) (d_squarefree r) (d_dvd_c r hsq) V u R hR hbox
    rw [← eq_c_sq_mul_d r hr] at hb
    have hnum := OnionAverageExponents.single_factor_le (r : ℝ) X R (ε/2)
      (by positivity) hrX (zero_le_one.trans hR) (by positivity)
    calc
      _ ≤ C*(r : ℝ)^(6+ε/2)*(d r : ℝ)^((1:ℝ)/2)*
          (SquarefreeResidueFactors.d2 (c r) (d r) : ℝ)^((1:ℝ)/2)*
            (R+(r : ℝ)^((1:ℝ)/3))^10 := hb
      _ = C*w r*((r : ℝ)^(6+ε/2)*(R+(r : ℝ)^((1:ℝ)/3))^10) := by dsimp [w]; ring
      _ ≤ C*w r*(X^(6+ε/2)*(R+X^((1:ℝ)/3))^10) :=
        mul_le_mul_of_nonneg_left hnum (mul_nonneg hC0 (hw r))
      _ = _ := by ring
  have hweight' : (∑ r ∈ Q, w r) ≤ U*X^((1:ℝ)/2+ε/2) := hweight X hX Q hQ
  calc
    _ ≤ ∑ r ∈ Q, (C*X^(6+ε/2)*(R+X^((1:ℝ)/3))^10)*w r :=
      Finset.sum_le_sum hsingle
    _ = (C*X^(6+ε/2)*(R+X^((1:ℝ)/3))^10)*(∑ r ∈ Q, w r) :=
      (Finset.mul_sum ..).symm
    _ ≤ (C*X^(6+ε/2)*(R+X^((1:ℝ)/3))^10)*(U*X^((1:ℝ)/2+ε/2)) :=
      mul_le_mul_of_nonneg_left hweight' (by positivity)
    _ = _ := OnionAverageExponents.combined_exponents C U X R ε hX0

/-- Exact dyadic source normalization. The lower cutoff is unnecessary,
so this includes every finite subset of X<r<=2X. -/
theorem exists_dyadic_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (X : ℝ), 1 ≤ X → ∀ (Q : Finset ℕ),
      (∀ r ∈ Q, 0 < r ∧ SquareFull r ∧ (r : ℝ) ≤ 2*X) →
      ∀ (V : Finset (Fin 10 → ℤ)) (u : Fin 10 → ℝ) (R : ℝ),
      1 ≤ R → (∀ v ∈ V, ∀ i, |(v i : ℝ)-u i| ≤ R) →
      (∑ r ∈ Q, ∑ v ∈ V, ‖completeCubicSum F r v‖) ≤
        K*X^((13:ℝ)/2+ε)*(R+X^((1:ℝ)/3))^10 := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_bound F hF hA ε hε
  let D : ℝ := (2:ℝ)^((13:ℝ)/2+ε)*2^10
  have hD : 1 ≤ D := by
    exact one_le_mul_of_one_le_of_one_le
      (Real.one_le_rpow (by norm_num) (by positivity)) (by norm_num)
  refine ⟨C*D,one_le_mul_of_one_le_of_one_le hC hD,?_⟩
  intro X hX Q hQ V u R hR hbox
  have hb := hbound (2*X) (by linarith) Q hQ V u R hR hbox
  have hn := OnionAverageExponents.dyadic_factor_le X R ε
    (zero_lt_one.trans_le hX) (zero_le_one.trans hR)
  calc
    _ ≤ C*(2*X)^((13:ℝ)/2+ε)*(R+(2*X)^((1:ℝ)/3))^10 := hb
    _ = C*((2*X)^((13:ℝ)/2+ε)*(R+(2*X)^((1:ℝ)/3))^10) := by ring
    _ ≤ C*(D*X^((13:ℝ)/2+ε)*(R+X^((1:ℝ)/3))^10) :=
      mul_le_mul_of_nonneg_left hn (zero_le_one.trans hC)
    _ = _ := by ring

/-- The cube-full dyadic average used later in the n=10 interpolation. -/
theorem exists_cubefull_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (X : ℝ), 1 ≤ X → ∀ (Q : Finset ℕ),
      (∀ r ∈ Q, 0 < r ∧ CubeFullSmithParameters.CubeFull r ∧ (r : ℝ) ≤ 2*X) →
      ∀ (V : Finset (Fin 10 → ℤ)) (u : Fin 10 → ℝ) (R : ℝ),
      1 ≤ R → (∀ v ∈ V, ∀ i, |(v i : ℝ)-u i| ≤ R) →
      (∑ r ∈ Q, ∑ v ∈ V, ‖completeCubicSum F r v‖) ≤
        K*X^((13:ℝ)/2+ε)*(R+X^((1:ℝ)/3))^10 := by
  obtain ⟨K,hK,hbound⟩ := exists_dyadic_bound F hF hA ε hε
  refine ⟨K,hK,?_⟩
  intro X hX Q hQ V u R hR hbox
  exact hbound X hX Q (fun r hr =>
    ⟨(hQ r hr).1,squareFull_of_cubeFull r (hQ r hr).2.1,(hQ r hr).2.2⟩)
    V u R hR hbox

/-- The required source average over its explicit dyadic cube-full set,
with no modulus-family or counting premise supplied by the caller. -/
theorem exists_literal_cubefull_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (X : ℝ), 1 ≤ X →
      ∀ (V : Finset (Fin 10 → ℤ)) (u : Fin 10 → ℝ) (R : ℝ),
      1 ≤ R → (∀ v ∈ V, ∀ i, |(v i : ℝ)-u i| ≤ R) →
      (∑ r ∈ cubeFullDyadic X, ∑ v ∈ V, ‖completeCubicSum F r v‖) ≤
        K*X^((13:ℝ)/2+ε)*(R+X^((1:ℝ)/3))^10 := by
  classical
  obtain ⟨K,hK,hbound⟩ := exists_cubefull_bound F hF hA ε hε
  refine ⟨K,hK,?_⟩
  intro X hX V u R hR hbox
  apply hbound X hX (cubeFullDyadic X) _ V u R hR hbox
  intro r hr
  obtain ⟨hrange,_,hcube⟩ := Finset.mem_filter.mp hr
  obtain ⟨hrpos,hrcut⟩ := Finset.mem_Icc.mp hrange
  refine ⟨hrpos,hcube,?_⟩
  exact (by exact_mod_cast hrcut : (r : ℝ) ≤ (⌊2*X⌋₊ : ℝ)).trans
    (Nat.floor_le (by linarith : 0 ≤ 2*X))

end CubicTenVariables.SquarefullModulusAverage

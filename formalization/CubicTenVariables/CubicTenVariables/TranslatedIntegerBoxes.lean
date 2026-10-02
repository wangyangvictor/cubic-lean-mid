import CubicTenVariables.HomogeneousProgressionBoxCount

/-! Literal closed real-centered boxes of integral points and their
progression counts on fixed homogeneous integral models. -/
noncomputable section
namespace CubicTenVariables.TranslatedIntegerBoxes
open MvPolynomial TranslatedDepthSeven
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual closed sup-norm box, including all boundary points. -/
def box {n : ℕ} (u : Fin n → ℝ) (L : ℝ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc ⌈u i-L⌉ ⌊u i+L⌋

theorem mem_box {n : ℕ} (u : Fin n → ℝ) (L : ℝ) (x : Fin n → ℤ) :
    x ∈ box u L ↔ ∀ i, |(x i : ℝ)-u i| ≤ L := by
  simp only [box,Fintype.mem_piFinset,Finset.mem_Icc,Int.ceil_le,Int.le_floor]
  constructor
  · intro h i
    exact abs_le.mpr ⟨by linarith [(h i).1],by linarith [(h i).2]⟩
  · intro h i
    have hi := abs_le.mp (h i)
    exact ⟨by linarith [hi.1],by linarith [hi.2]⟩

/-- Actual integral points of an integral ideal in the specified progression
and real-centered box. No rational radical replaces the integral equations. -/
def modelPoints {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℤ))
    (u : Fin n → ℝ) (L : ℝ) (m : ℕ) (b : Fin n → ℤ) : Finset (Fin n → ℤ) := by
  classical
  exact (box u L).filter fun x =>
    (∀ i, (m : ℤ) ∣ x i-b i) ∧ ∀ f∈J, eval x f=0

theorem mem_modelPoints {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℤ))
    (u : Fin n → ℝ) (L : ℝ) (m : ℕ) (b x : Fin n → ℤ) :
    x ∈ modelPoints J u L m b ↔
      (∀ i, |(x i : ℝ)-u i| ≤ L) ∧
      (∀ i, (m : ℤ) ∣ x i-b i) ∧ ∀ f∈J, eval x f=0 := by
  classical
  simp only [modelPoints,Finset.mem_filter,mem_box]

/-- Actual integral zeros satisfy every equation of the rational extension. -/
theorem rational_zero_of_integral_zero {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n) ℤ)) (x : Fin n → ℤ)
    (hx : ∀ f∈J, eval x f=0) :
    (fun i => (x i : ℚ)) ∈ affineIdealZeroLocus
      (J.map (MvPolynomial.map (Int.castRingHom ℚ))) := by
  let e : MvPolynomial (Fin n) ℚ →+* ℚ := eval (fun i => (x i : ℚ))
  have hle : J.map (MvPolynomial.map (Int.castRingHom ℚ)) ≤ RingHom.ker e := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro f hf
    change eval (fun i => (x i : ℚ)) (map (Int.castRingHom ℚ) f)=0
    have he := MvPolynomial.map_eval (Int.castRingHom ℚ) x f
    simpa only [Function.comp_def,Int.coe_castRingHom,hx f hf,Int.cast_zero] using he.symm
  intro f hf
  exact hle hf

/-- Source Schwartz--Zippel progression count for the required fixed cones.
It is uniform in every real center, nonnegative radius, positive modulus and
integral residue class; no literature proposition is an input. -/
theorem exists_model_count_bound {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℤ))
    (hproper : J.map (MvPolynomial.map (Int.castRingHom ℚ)) ≠ ⊤)
    (hhom : (J.map (MvPolynomial.map (Int.castRingHom ℚ))).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) ℚ))
    (d : ℕ) (hdim : ringKrullDim (MvPolynomial (Fin n) ℚ ⧸
      J.map (MvPolynomial.map (Int.castRingHom ℚ))) ≤ (d : WithBot ℕ∞)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (u : Fin n → ℝ) (L : ℝ), 0 ≤ L →
      ∀ (m : ℕ), 0 < m → ∀ b : Fin n → ℤ,
      ((modelPoints J u L m b).card : ℝ) ≤ C*(1+L/(m : ℝ))^d := by
  obtain ⟨C,hC,h⟩ := HomogeneousProgressionBoxCount.exists_bound
    _ hproper hhom d hdim
  refine ⟨C,hC,?_⟩
  intro u L hL m hm b
  apply h (modelPoints J u L m b) u L hL m hm b
  · intro x hx
    exact ((mem_modelPoints J u L m b x).mp hx).1
  · intro x hx
    exact ((mem_modelPoints J u L m b x).mp hx).2.1
  · intro x hx
    exact rational_zero_of_integral_zero J x ((mem_modelPoints J u L m b x).mp hx).2.2

end CubicTenVariables.TranslatedIntegerBoxes

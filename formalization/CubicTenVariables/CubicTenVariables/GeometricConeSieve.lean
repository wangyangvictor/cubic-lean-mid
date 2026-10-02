import CubicTenVariables.IntegralConeNormalization
import CubicTenVariables.TranslatedGeometricSievePairs
import CubicTenVariables.TerminalIntegralClosureModels

/-! The translated sieve applied to actual integral models of geometric
frequency cones, including the two ten-variable terminal closures. -/
noncomputable section
namespace CubicTenVariables.GeometricConeSieve
open MvPolynomial HessianTheorem11 TerminalIntegralClosureModels
variable {n t : ℕ}

/-- Integral evaluation commutes with reduction for every modulus. -/
theorem int_eval_cast (q : ℕ) (x : Fin n → ℤ) (f : MvPolynomial (Fin n) ℤ) :
    eval₂ (Int.castRingHom (ZMod q)) (fun i => (x i : ZMod q)) f =
      (eval x f : ZMod q) :=
  (eval₂_comp (Int.castRingHom (ZMod q)) x f).symm

/-- Divisibility of the original ideal equations means actual membership
of the reduced point in their zero locus, even for nonprime moduli. -/
theorem ideal_divisibility_iff_reduced_zeros (J : Ideal (MvPolynomial (Fin n) ℤ))
    (q : ℕ) (x : Fin n → ℤ) :
    (∀ f ∈ J, (q : ℤ) ∣ eval x f) ↔
      ∀ f ∈ J, eval₂ (Int.castRingHom (ZMod q)) (fun i => (x i : ZMod q)) f=0 := by
  simp only [int_eval_cast,ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The same modular condition expressed using the original finite family. -/
theorem generator_divisibility_iff_reduced_zeros (G : Fin t → MvPolynomial (Fin n) ℤ)
    (q : ℕ) (x : Fin n → ℤ) :
    (∀ f ∈ Ideal.span (Set.range G), (q : ℤ) ∣ eval x f) ↔
      ∀ i, eval₂ (Int.castRingHom (ZMod q)) (fun j => (x j : ZMod q)) (G i)=0 := by
  rw [ideal_divisibility_iff_reduced_zeros,IntegralConeNormalization.forall_eval_span_iff]

/-- The source pair count for one fixed family of integral equations. -/
def SieveBound (G : Fin t → MvPolynomial (Fin n) ℤ) (r : ℕ) (ε : ℝ) : Prop :=
  ∃ c K : ℝ, 1 ≤ c ∧ 1 ≤ K ∧
    ∀ (u : Fin n → ℝ) (L : ℝ), 1 ≤ L → ∀ (m : ℕ), 0 < m →
    ∀ (b : Fin n → ℤ) (S0 : ℝ), c*(1+L/(m : ℝ)) ≤ S0 →
    ((TranslatedGeometricSievePairs.pairs (Ideal.span (Set.range G)) u L m b S0).card : ℝ) ≤
      K*(L*S0+‖u‖)^ε*(1+L/(m : ℝ))^(r+1)

/-- The rational homogeneity, dimension and normalization hypotheses are
all supplied from the actual geometric model, rather than assumed anew. -/
theorem of_model (G : Fin t → MvPolynomial (Fin n) ℤ)
    (Z : Set (Fin n → GeometricField)) (hZ : Z.Nonempty)
    (hscale : ∀ (c : GeometricField), c ≠ 0 → ∀ x ∈ Z, c • x ∈ Z)
    (hmodel : IntegralModelDimension.geometricIdeal G = vanishingIdeal GeometricField Z)
    (r : ℕ) (hdim : affineDimension Z ≤ (r : Dimension)) (ε : ℝ) (hε : 0 < ε) :
    SieveBound G r ε := by
  obtain ⟨D⟩ := IntegralConeNormalization.exists_certificate G Z hZ hscale hmodel r hdim
  obtain ⟨c,K,hc,hK,hbound⟩ :=
    TranslatedGeometricSievePairs.exists_pair_bound_of_certificate D ε hε
  refine ⟨c,K,hc,hK,?_⟩
  intro u L hL m hm b S0 hS0
  exact hbound u L hL m hm b S0 hS0 _ (fun p hp =>
    (TranslatedGeometricSievePairs.mem_pairs _ u L m b S0 p).mp hp)

/-- Fixed integral model of the actual section terminal closure, with
progression/sieve exponent 5 and no unproved literature premise. -/
theorem exists_section_model (F : AnisotropicCubic 10) :
    ∃ t : ℕ, ∃ G : Fin t → MvPolynomial (Fin 10) ℤ,
      IntegralModelDimension.geometricIdeal G =
        vanishingIdeal GeometricField (sectionClosure F.polynomial 4) ∧
      (∀ x : GeometricPoint 10, x ∈ sectionClosure F.polynomial 4 ↔
        ∀ i, eval₂ (Int.castRingHom GeometricField) x (G i)=0) ∧
      ∀ ε : ℝ, 0 < ε → SieveBound G 4 ε := by
  obtain ⟨t,G,hmodel,hzero⟩ := exists_sectionClosure_equations F.polynomial 4
  refine ⟨t,G,hmodel,hzero,?_⟩
  intro ε hε
  exact of_model G _ ⟨0,zero_mem_nonzeroClosure _⟩
    (fun c _ x hx => sectionClosure_isAffineCone F.polynomial 4 c x hx)
    hmodel 4 (ten_sectionClosure_dimension F) ε hε

/-- Fixed integral model of the actual Gauss terminal closure, with
progression/sieve exponent 4 and no unproved literature premise. -/
theorem exists_gauss_model (F : AnisotropicCubic 10) :
    ∃ t : ℕ, ∃ G : Fin t → MvPolynomial (Fin 10) ℤ,
      IntegralModelDimension.geometricIdeal G =
        vanishingIdeal GeometricField (gaussClosure F.polynomial 5) ∧
      (∀ x : GeometricPoint 10, x ∈ gaussClosure F.polynomial 5 ↔
        ∀ i, eval₂ (Int.castRingHom GeometricField) x (G i)=0) ∧
      ∀ ε : ℝ, 0 < ε → SieveBound G 3 ε := by
  obtain ⟨t,G,hmodel,hzero⟩ := exists_gaussClosure_equations F.polynomial 5
  refine ⟨t,G,hmodel,hzero,?_⟩
  intro ε hε
  exact of_model G _ ⟨0,zero_mem_nonzeroClosure _⟩
    (fun c _ x hx => gaussClosure_isAffineCone F.polynomial F.homogeneous 5 c x hx)
    hmodel 3 (ten_gaussClosure_dimension F) ε hε

end CubicTenVariables.GeometricConeSieve

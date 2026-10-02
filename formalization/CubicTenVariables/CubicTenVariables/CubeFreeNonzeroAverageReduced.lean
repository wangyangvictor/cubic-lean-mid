import CubicTenVariables.ConductorNonzeroAverageReduced
import CubicTenVariables.CubeFreeModulusDecomposition
import CubicTenVariables.TenMicrolocalIncidenceData

/-! The actual coarse cube-free modulus sum at every nonzero integer
frequency. The canonical squarefree-times-square decomposition counts each
modulus once, with no conductor, radical or generic-frequency restriction. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CubeFreeNonzeroAverageReduced
open MvPolynomial HessianTheorem11 ProjectiveMicrolocalData
open SquarefullModulusDecomposition CubeFreeModulusDecomposition
open ConductorFixedFrequency
open scoped BigOperators Classical

/-- The literal half-open cube-free dyadic window. -/
def window (D : ℝ) : Finset ℕ :=
  (Finset.range (⌊2*D⌋₊+1)).filter fun q =>
    CubeFree q ∧ D ≤ (q : ℝ) ∧ (q : ℝ) < 2*D

theorem mem_window (D : ℝ) (q : ℕ) :
    q ∈ window D ↔ CubeFree q ∧ D ≤ (q : ℝ) ∧ (q : ℝ) < 2*D := by
  simp only [window,Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff]
  constructor
  · exact And.right
  · intro hq
    exact ⟨Nat.le_floor hq.2.2.le,hq⟩

/-- The actual cube-free modulus sum, retaining the supplied incidence,
the listed literature hypotheses and the proved prime-field count interface. -/
theorem of_data (spread : CubicPrincipalOpenUniform.Uniform)
    (cubicWeil : Literature.SmoothCubicWeil) (isolated : CubicSurfacePointCountReduced.IsolatedConjugateCubicSurfacePointCount)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    {t : ℕ} (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (N B : ℕ) (hN : 1 ≤ N) (hgeo : Geometry F f)
    (hData : TenMicrolocalIncidence.Conclusion F f N B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ v : Fin 10 → ℤ, v ≠ 0 → ∀ D : ℝ, 1 ≤ D →
      (∑ q ∈ window D, ‖completeCubicSum F q v‖) ≤
        M*(D*frequencyHeight v)^ε*D^9 := by
  obtain ⟨M,hM,hbound⟩ := ConductorNonzeroAverageReduced.of_data
    spread cubicWeil isolated pointcount F hF hAn f N B hN hgeo hData ε hε
  refine ⟨M,hM,?_⟩
  intro v hv D hD
  let Q : Finset (ℕ × ℕ) := (window D).image (fun q => (d q,c q))
  have hQ : ∀ x ∈ Q,
      1 ≤ x.1 ∧ 1 ≤ x.2 ∧ Squarefree x.1 ∧ Squarefree x.2 ∧
        x.1.Coprime x.2 ∧ (x.1 : ℝ)*(x.2 : ℝ)^2 ≤ 2*D := by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
    have hw := (mem_window D q).mp hq
    refine ⟨d_pos q,c_pos q,d_squarefree q,c_squarefree q hw.1,
      coprime_d_c q hw.1,?_⟩
    have he : (q : ℝ) = (d q : ℝ)*(c q : ℝ)^2 := by
      exact_mod_cast eq_d_mul_c_sq q hw.1
    exact he ▸ hw.2.2.le
  have hinj : Set.InjOn (fun q => (d q,c q)) (↑(window D) : Set ℕ) := by
    intro q hq r hr he
    exact CubeFreeModulusDecomposition.parameters_injOn
      (Nat.pos_of_ne_zero ((mem_window D q).mp hq).1.1)
      (Nat.pos_of_ne_zero ((mem_window D r).mp hr).1.1) he
  calc
    _ = ∑ q ∈ window D, ‖completeCubicSum F (d q*(c q)^2) v‖ := by
      apply Finset.sum_congr rfl
      intro q hq
      exact congrArg (fun k => ‖completeCubicSum F k v‖)
        (eq_d_mul_c_sq q ((mem_window D q).mp hq).1)
    _ = ∑ x ∈ Q, ‖completeCubicSum F (x.1*x.2^2) v‖ :=
      (Finset.sum_image (f := fun x : ℕ × ℕ => ‖completeCubicSum F (x.1*x.2^2) v‖) hinj).symm
    _ ≤ _ := hbound v hv D hD Q hQ

/-- The listed literature hypotheses and proved prime-field count interface
construct the bound; no selected incidence, coordinate, partition or
arithmetic estimate is supplied. -/
theorem exists_bound
    (microlocal : Literature.ProjectiveMicrolocalCertificate)
    (spread : CubicPrincipalOpenUniform.Uniform)
    (cubicWeil : Literature.SmoothCubicWeil)
    (isolated : CubicSurfacePointCountReduced.IsolatedConjugateCubicSurfacePointCount)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F)) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ v : Fin 10 → ℤ, v ≠ 0 → ∀ D : ℝ, 1 ≤ D →
      (∑ q ∈ window D, ‖completeCubicSum F q v‖) ≤
        M*(D*frequencyHeight v)^ε*D^9 := by
  obtain ⟨t,f,N,B,hN,_hB,hgeo,hData⟩ :=
    TenMicrolocalIncidenceData.exists_data microlocal F hF hAn
  exact of_data spread cubicWeil isolated pointcount F hF hAn f N B hN hgeo hData ε hε

end CubicTenVariables.CubeFreeNonzeroAverageReduced

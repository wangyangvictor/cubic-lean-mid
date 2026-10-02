import CubicTenVariables.CubicGenericIntegralityOpen
import CubicTenVariables.PolynomialDegreePrincipalOpen
import CubicTenVariables.GeometricGenericParameterEmbedding

/-! A proved cubic instance of generic geometric integrality on a base open.
The coefficient controlling degree is included in the exceptional element,
so every specialization on that open retains both degree and integrality.
This does not assert the former general finitely presented family input. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CubicGenericIntegralityUniform
open MvPolynomial Literature GeometricGenericParameterEmbedding

/-- One principal open preserves degree three and the domain property over
every target field. All coefficient specializations share the same element. -/
theorem exists_nonzero_open
    {n : ℕ} {B Ω : Type*} [CommRing B] [IsDomain B]
    [Field Ω] [IsAlgClosed Ω]
    (ι : B →+* Ω) (hι : Function.Injective ι)
    (F : MvPolynomial (Fin n) B)
    (hdegree : (map ι F).totalDegree = 3)
    (hdomain : IsDomain (MvPolynomial (Fin n) Ω ⧸ Ideal.span {map ι F})) :
    ∃ s : B, s ≠ 0 ∧
      ∀ (K : Type*) [Field K] (ρ : B →+* K), ρ s ≠ 0 →
        (map ρ F).totalDegree = 3 ∧
        IsDomain (MvPolynomial (Fin n) K ⧸ Ideal.span {map ρ F}) := by
  have hF : F.totalDegree = 3 := by
    rwa [PolynomialDegreePrincipalOpen.totalDegree_map_of_injective ι hι F] at hdegree
  obtain ⟨c, hc, hdegreegood⟩ :=
    PolynomialDegreePrincipalOpen.exists_nonzero_coefficient F (by decide : 0 < 3) hF
  obtain ⟨s, hs, hgood⟩ :=
    CubicGenericIntegralityOpen.exists_nonzero_open ι hι F hdegree hdomain
  refine ⟨s * c, mul_ne_zero hs hc, ?_⟩
  intro K _ ρ hρ
  have hh : ρ s ≠ 0 ∧ ρ c ≠ 0 := mul_ne_zero_iff.mp (by
    simpa only [map_mul] using hρ)
  have hd := hdegreegood K ρ hh.2
  exact ⟨hd, hgood K ρ hh.1 hd⟩

/-- Internal interface for the single cubic equation over the literal
integral parameter ring. It has the unconditional inhabitant below. -/
def Uniform : Prop :=
  ∀ (σ : Type) [Fintype σ] (n : ℕ)
    (F : MvPolynomial (Fin n) (MvPolynomial σ ℤ)),
    (map (coefficientHom σ) F).totalDegree = 3 →
    IsDomain (MvPolynomial (Fin n) (AlgebraicClosure (GeometricParameterField σ)) ⧸
      Ideal.span {map (coefficientHom σ) F}) →
    ∃ g : MvPolynomial σ ℤ, g ≠ 0 ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (v : σ → K),
        eval₂ (Int.castRingHom K) v g ≠ 0 →
        IsDomain (MvPolynomial (Fin n) K ⧸
          Ideal.span {map (eval₂Hom (Int.castRingHom K) v) F})

/-- The required uniform cubic open is a theorem, with no literature input. -/
theorem proved : Uniform := by
  intro σ _ n F hdegree hdomain
  obtain ⟨g, hg, hgood⟩ := exists_nonzero_open (coefficientHom σ)
    (coefficientHom_injective σ) F hdegree hdomain
  refine ⟨g, hg, ?_⟩
  intro K _ _ v hv
  exact (hgood K (eval₂Hom (Int.castRingHom K) v) hv).2

end CubicTenVariables.CubicGenericIntegralityUniform

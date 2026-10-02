import CubicTenVariables.ReducedHyperplaneIntegralityProved
import CubicTenVariables.ReducedHyperplaneIntegrality
import CubicTenVariables.ReducedHyperplaneVertexBounds
import CubicTenVariables.HyperplaneFrames

/-! The required n=10 uniform hyperplane geometry. The integrality interface,
vertex bounds, translation interpretation, and exclusion of zero section
equations are proved internally. One integer precedes all primes, fields,
frames and normals. -/

noncomputable section
namespace CubicTenVariables.UniformHyperplaneGeometry
open MvPolynomial HessianTheorem11 Module Matrix PolynomialRestriction
open ReducedCubicVertex ReducedGaussSection

/-- A zero polynomial has the entire coordinate space as its Hessian
vertex. This prevents mistaking the domain quotient of the zero ideal for
a genuine cubic hypersurface. -/
theorem polynomial_ne_zero_of_vertex_bound {K : Type*} [Field K] {m r : ℕ}
    (f : MvPolynomial (Fin m) K) (hf : f.IsHomogeneous 3)
    (hV : finrank K (affineVertex f hf) ≤ r) (hr : r < m) : f≠0 := by
  intro he
  have htop : affineVertex f hf=⊤ := by
    apply top_unique
    intro x _
    change hessian f x=0
    rw [he]
    ext i j
    simp [hessian,hessianPolynomial]
  rw [htop] at hV
  have hm : m≤r := by simpa using hV
  omega

/-- All clauses describe the actual restricted polynomial and its actual
maximal vertex; this record is a conclusion, never an additional premise. -/
def SectionProperties {K : Type*} [Field K]
    (f : MvPolynomial (Fin 9) K) (hf : f.IsHomogeneous 3) : Prop :=
  f≠0 ∧ Irreducible f ∧ f.totalDegree=3 ∧
  IsDomain (MvPolynomial (Fin 9) K ⧸ Ideal.span {f}) ∧
  finrank K (affineVertex f hf) ≤ 4 ∧
  ReducedGaussSection.projectiveDimension
    (affineVertex f hf : Set (Fin 9 → K)) ≤ (3 : Dimension) ∧
  ∀ x : Fin 9 → K, x∈affineVertex f hf ↔ TranslationDirection f x

/-- Every geometric hyperplane section is a genuine irreducible cubic,
with maximal projective vertex dimension at most three. -/
theorem exists_uniform_bound
    (spread : CubicPrincipalOpenUniform.Uniform)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ D : ℕ, 1≤D ∧ ∀ p : ℕ, p.Prime → ¬p∣D →
      3<p ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [CharP K p],
        IsDomain (MvPolynomial (Fin 10) K ⧸ Ideal.span {map (Int.castRingHom K) F}) ∧
        ∀ (B : Matrix (Fin 10) (Fin 9) K), Function.Injective B.mulVec →
          SectionProperties (restrict B (map (Int.castRingHom K) F))
            (homogeneous_restrict B _ (hF.map (Int.castRingHom K))) := by
  obtain ⟨DI,hDI,hI⟩ := ReducedHyperplaneIntegralityProved.exists_uniform_bound_of_uniform spread F hF hA
  obtain ⟨DA,hDA,hAfield⟩ := ReducedHyperplaneIntegralityProved.exists_uniform_ambient_bound_of_uniform spread F hF hA
  obtain ⟨DV,hDV,hV⟩ := ReducedHyperplaneVertexBounds.exists_uniform_bound F hF hA
  refine ⟨(DI*DA)*DV,Nat.mul_pos (Nat.mul_pos hDI hDA) hDV,?_⟩
  intro p hp hpD
  have hpI : ¬p∣DI := fun h => hpD (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h DA) DV)
  have hpA : ¬p∣DA := fun h => hpD (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h DI) DV)
  have hpV : ¬p∣DV := fun h => hpD (dvd_mul_of_dvd_right h (DI*DA))
  obtain ⟨hp3,hv⟩ := hV p hp hpV
  refine ⟨hp3,?_⟩
  intro K _ _ _
  refine ⟨hAfield p hp hpA K,?_⟩
  intro B hB
  let f := restrict B (map (Int.castRingHom K) F)
  have hf : f.IsHomogeneous 3 := homogeneous_restrict B _ (hF.map _)
  obtain ⟨hfin,hproj,htrans⟩ := (hv K).2.2 B hB
  have hdom := hI p hp hpI K B hB
  have hn : f≠0 := polynomial_ne_zero_of_vertex_bound f hf hfin (by decide : 4 < 9)
  have hprime : (Ideal.span {f}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp hdom
  have hirred : Irreducible f := ((Ideal.span_singleton_prime hn).mp hprime).irreducible
  exact ⟨hn,hirred,hf.totalDegree hn,hdom,hfin,hproj,htrans⟩

/-- Explicit normal-vector version: the same integer is chosen before the
normal, and an actual injective frame of its full kernel is constructed. -/
theorem exists_uniform_normal_bound
    (spread : CubicPrincipalOpenUniform.Uniform)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ D : ℕ, 1≤D ∧ ∀ p : ℕ, p.Prime → ¬p∣D →
      3<p ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [CharP K p]
        (v : Fin 10 → K), v≠0 →
        ∃ B : Matrix (Fin 10) (Fin 9) K,
          Function.Injective B.mulVec ∧
          LinearMap.range B.mulVecLin = TerminalSectionIncidence.hyperplane v ∧
          SectionProperties (restrict B (map (Int.castRingHom K) F))
            (homogeneous_restrict B _ (hF.map (Int.castRingHom K))) := by
  obtain ⟨D,hD,hgood⟩ := exists_uniform_bound spread F hF hA
  refine ⟨D,hD,?_⟩
  intro p hp hpD
  obtain ⟨hp3,h⟩ := hgood p hp hpD
  refine ⟨hp3,?_⟩
  intro K _ _ _ v hv
  obtain ⟨B,hB,hRange⟩ := HyperplaneFrames.exists_frame v hv
  exact ⟨B,hB,hRange,(h K).2 B hB⟩

end CubicTenVariables.UniformHyperplaneGeometry

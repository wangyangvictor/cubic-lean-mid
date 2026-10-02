import CubicTenVariables.LocalizedFinitePrimeAssembly
import CubicTenVariables.PrimeLocalizationFactor

/-! Actual simultaneous prime-local restrictions built from supplied smooth
local data. The modulus is the product of the selected prime powers. Local
factor convergence and positivity are proved, while ordinary global series
convergence and positivity remain explicit hypotheses. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.PrimeLocalizationSeries
open MvPolynomial
open scoped BigOperators Classical
variable {F : MvPolynomial (Fin 10) ℤ}

/-- A total family of local specifications; entries outside the finite
set have exponent zero and impose no restriction. -/
def localSpecification (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F)
    (p : ℕ) : Σ M : ℕ, Set (Fin 10 → ZMod (p^M)) :=
  if hp : p ∈ s then ⟨(@PrimeLocalizationData.modulusExponent p ⟨hprimes p hp⟩ F (D p hp)),(@PrimeLocalizationData.residueSet p ⟨hprimes p hp⟩ F (D p hp))⟩
  else ⟨0,Set.univ⟩

def exponent (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F)
    (p : ℕ) : ℕ := (localSpecification s hprimes D p).1

def localResidues (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F)
    (p : ℕ) : Set (Fin 10 → ZMod (p^exponent s hprimes D p)) :=
  (localSpecification s hprimes D p).2

def modulus (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F) : ℕ :=
  LocalizedFinitePrimeAssembly.modulus s (exponent s hprimes D)

def restriction (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F) :
    Set (Fin 10 → ZMod (modulus s hprimes D)) :=
  LocalizedFinitePrimeAssembly.restriction s (exponent s hprimes D)
    (localResidues s hprimes D)

theorem localSpecification_of_mem (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F)
    (p : ℕ) (hp : p ∈ s) :
    localSpecification s hprimes D p =
      ⟨@PrimeLocalizationData.modulusExponent p ⟨hprimes p hp⟩ F (D p hp),
        @PrimeLocalizationData.residueSet p ⟨hprimes p hp⟩ F (D p hp)⟩ := by
  exact dif_pos hp

theorem exponent_of_mem (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F)
    (p : ℕ) (hp : p ∈ s) :
    exponent s hprimes D p = (@PrimeLocalizationData.modulusExponent p ⟨hprimes p hp⟩ F (D p hp)) := by
  simp only [exponent,localSpecification,dif_pos hp]

theorem modulus_eq_prod (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F) :
    modulus s hprimes D = ∏ p : {p // p ∈ s},
      p.val ^ (@PrimeLocalizationData.modulusExponent p.val ⟨hprimes p.val p.property⟩ F (D p.val p.property)) := by
  classical
  rw [modulus,LocalizedFinitePrimeAssembly.modulus,←Finset.prod_attach]
  change (∏ p ∈ s.attach, p.val ^ exponent s hprimes D p.val) =
    ∏ p ∈ s.attach, p.val ^ (@PrimeLocalizationData.modulusExponent p.val ⟨hprimes p.val p.property⟩ F (D p.val p.property))
  apply Finset.prod_congr rfl
  intro p _
  rw [exponent_of_mem s hprimes D p.val p.property]

theorem modulus_pos (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F) :
    0 < modulus s hprimes D :=
  LocalizedFinitePrimeAssembly.modulus_pos s (exponent s hprimes D) hprimes

/-- The combined residue set is exactly simultaneous local membership. -/
theorem restriction_eq (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F) :
    restriction s hprimes D = {x | ∀ (p : ℕ) (hp : p ∈ s),
      (fun i => (ZMod.cast (x i) : ZMod (p^(@PrimeLocalizationData.modulusExponent p ⟨hprimes p hp⟩ F (D p hp))))) ∈
        (@PrimeLocalizationData.residueSet p ⟨hprimes p hp⟩ F (D p hp))} := by
  ext x
  simp only [restriction,LocalizedFinitePrimeAssembly.restriction,
    LocalizedFinitePrimeAssembly.restrictionAt,Set.mem_setOf_eq]
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  exact Iff.of_eq (congrArg (fun spec : Σ M : ℕ, Set (Fin 10 → ZMod (p^M)) =>
    (fun i => (ZMod.cast (x i) : ZMod (p^spec.1))) ∈ spec.2)
      (localSpecification_of_mem s hprimes D p hp))

/-- The integer restriction is precisely simultaneous membership in the
chosen local residue sets, with no alteration of those sets. -/
theorem integerResidue_mem_iff (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F)
    (x : Fin 10 → ℤ) :
    integerResidue (modulus s hprimes D) x ∈ restriction s hprimes D ↔
      ∀ (p : ℕ) (hp : p ∈ s),
        integerResidue (p^(@PrimeLocalizationData.modulusExponent p ⟨hprimes p hp⟩ F (D p hp))) x ∈ (@PrimeLocalizationData.residueSet p ⟨hprimes p hp⟩ F (D p hp)) := by
  change integerResidue (LocalizedFinitePrimeAssembly.modulus s (exponent s hprimes D)) x ∈
    LocalizedFinitePrimeAssembly.restriction s (exponent s hprimes D)
      (localResidues s hprimes D) ↔ _
  rw [LocalizedFinitePrimeAssembly.integerResidue_mem_iff]
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  exact Iff.of_eq (congrArg (fun spec : Σ M : ℕ, Set (Fin 10 → ZMod (p^M)) =>
    integerResidue (p^spec.1) x ∈ spec.2)
      (localSpecification_of_mem s hprimes D p hp))

/-- Supplied smooth local data suffice for each restricted local factor.
Only the ordinary global series convergence and positivity are assumed. -/
theorem assemble (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F)
    (hF : F.IsHomogeneous 3) (hordinary : SingularSeriesAbsolutelyConvergent F)
    (S : ℝ) (hS : 0 < S) (hordinaryValue : singularSeries F = (S:ℂ)) :
    Summable (fun q => ‖localizedSingularSeriesTerm F
      (modulus s hprimes D) (restriction s hprimes D) q‖) ∧
      ∃ T : ℝ, 0 < T ∧ localizedSingularSeries F
        (modulus s hprimes D) (restriction s hprimes D) = (T:ℂ) := by
  apply LocalizedFinitePrimeAssembly.assemble F (by norm_num) s
    (exponent s hprimes D) (localResidues s hprimes D) hprimes hordinary S hS hordinaryValue
  intro p hp
  letI : Fact p.Prime := ⟨hprimes p hp⟩
  obtain ⟨L,hL,hsum,hfactor,_⟩ := (D p hp).exists_positive_local_factor hF
  refine ⟨L,hL,?_,?_⟩
  · exact (congrArg (fun spec : Σ M : ℕ, Set (Fin 10 → ZMod (p^M)) =>
      Summable (fun k => ‖localizedSingularSeriesTerm F (p^spec.1) spec.2 (p^k)‖))
        (localSpecification_of_mem s hprimes D p hp)).mpr hsum
  · exact (congrArg (fun spec : Σ M : ℕ, Set (Fin 10 → ZMod (p^M)) =>
      HasSum (fun k => localizedSingularSeriesTerm F (p^spec.1) spec.2 (p^k)) (L:ℂ))
        (localSpecification_of_mem s hprimes D p hp)).mpr hfactor

/-- Explicit existence packaging of the product modulus and the exact
simultaneous residue restriction. No local-factor hypotheses are supplied. -/
theorem exists_localized_series (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F)
    (hF : F.IsHomogeneous 3) (hordinary : SingularSeriesAbsolutelyConvergent F)
    (S : ℝ) (hS : 0 < S) (hordinaryValue : singularSeries F = (S:ℂ)) :
    ∃ W : ℕ, 0 < W ∧ W = (∏ p : {p // p ∈ s},
        p.val ^ (@PrimeLocalizationData.modulusExponent p.val ⟨hprimes p.val p.property⟩ F (D p.val p.property))) ∧
      ∃ Ω : Set (Fin 10 → ZMod W),
        Ω = {x | ∀ (p : ℕ) (hp : p ∈ s),
          (fun i => (ZMod.cast (x i) : ZMod (p^(@PrimeLocalizationData.modulusExponent p ⟨hprimes p hp⟩ F (D p hp))))) ∈
            (@PrimeLocalizationData.residueSet p ⟨hprimes p hp⟩ F (D p hp))} ∧
        Summable (fun q => ‖localizedSingularSeriesTerm F W Ω q‖) ∧
        ∃ T : ℝ, 0 < T ∧ localizedSingularSeries F W Ω = (T:ℂ) := by
  refine ⟨modulus s hprimes D,modulus_pos s hprimes D,modulus_eq_prod s hprimes D,
    restriction s hprimes D,restriction_eq s hprimes D,?_⟩
  exact assemble s hprimes D hF hordinary S hS hordinaryValue

end CubicTenVariables.PrimeLocalizationSeries

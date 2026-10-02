import HessianTheorem11.RationalIrreducibility
import HessianTheorem11.FewerVariables
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

/-! Polynomial UFD arguments for the three- and four-coordinate quadric
relations of source Lemma 29.1. No classification statement is an input. -/
noncomputable section
namespace HessianTheorem11.QuadricLowRank
open MvPolynomial Module
open scoped BigOperators

/-- An actual rank-one two-by-two matrix over a gcd domain factors as a
column times a row, with polynomial entries. -/
theorem rank_one_factorization {R : Type*} [CommRing R] [IsDomain R] [GCDMonoid R]
    (a b c d : R) (ha : a ≠ 0) (he : a*d=b*c) :
    ∃ u₁ u₂ v₁ v₂ : R, a=u₁*v₁ ∧ b=u₁*v₂ ∧ c=u₂*v₁ ∧ d=u₂*v₂ := by
  obtain ⟨v₁,v₂,hae,hbe,hcop⟩ := extract_gcd a b
  let u₁ := gcd a b
  have hu₁ : u₁ ≠ 0 := by intro h; exact ha (by simpa [u₁,h] using hae)
  have hv₁ : v₁ ≠ 0 := by intro h; exact ha (by simpa [h] using hae)
  have hrel : v₁*d=v₂*c := by
    apply mul_left_cancel₀ hu₁
    change gcd a b * (v₁*d) = gcd a b * (v₂*c)
    simpa only [← mul_assoc, ← hae, ← hbe] using he
  have hvdvd : v₁ ∣ c := by
    apply (gcd_isUnit_iff_isRelPrime.mp hcop).dvd_of_dvd_mul_left
    rw [← hrel]
    exact dvd_mul_right _ _
  obtain ⟨u₂,hce⟩ := hvdvd
  have hde : d = u₂*v₂ := by
    apply mul_left_cancel₀ hv₁
    rw [hrel,hce]
    ring
  exact ⟨u₁,u₂,v₁,v₂,hae,hbe,by simpa [mul_comm] using hce,hde⟩

variable {K σ : Type*} [Field K] [Fintype σ]

/-- The homogeneous linear part of an affine linear polynomial. -/
def linearPart (P : MvPolynomial σ K) : MvPolynomial σ K := P - C (coeff 0 P)

theorem linearPart_isHomogeneous (P : MvPolynomial σ K) (hP : P.totalDegree ≤ 1) :
    (linearPart P).IsHomogeneous 1 := by
  classical
  have he := eq_affine_linear_of_totalDegree_le_one P hP
  have hlin : linearPart P = ∑ i, C (coeff (Finsupp.single i 1) P) * X i := by
    unfold linearPart
    conv_lhs => lhs; rw [he]
    ring
  rw [hlin]
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_C_mul_X _ _

/-- If a homogeneous quadric factors into affine linear polynomials, their
homogeneous linear parts already give the same product. -/
theorem homogeneous_quadric_eq_linearParts (A B : MvPolynomial σ K)
    (hA : A.totalDegree ≤ 1) (hB : B.totalDegree ≤ 1) (hAB : (A*B).IsHomogeneous 2) :
    A*B = linearPart A * linearPart B := by
  let R := A*B - linearPart A * linearPart B
  have hhom : R.IsHomogeneous 2 := hAB.sub ((linearPart_isHomogeneous A hA).mul
    (linearPart_isHomogeneous B hB))
  have he : R = C (coeff 0 A) * B + C (coeff 0 B) * A - C (coeff 0 A * coeff 0 B) := by
    simp only [R, linearPart, map_mul]
    ring
  have hdeg : R.totalDegree ≤ 1 := by
    rw [he]
    apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le
    · apply (MvPolynomial.totalDegree_add _ _).trans
      apply max_le
      · exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa using hB)
      · exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa using hA)
    · rw [totalDegree_C]
      omega
  have hzero : R = 0 := by
    by_contra hn
    have h := hhom.totalDegree hn
    omega
  exact sub_eq_zero.mp hzero

/-- Constant polynomial factors differ by an actual scalar. -/
theorem constant_factors_proportional (U V W : MvPolynomial σ K)
    (hU : U.totalDegree = 0) (hV : V.totalDegree = 0) (hU0 : U ≠ 0) :
    ∃ c : K, c • (U*W) = V*W := by
  have hUe := totalDegree_eq_zero_iff_eq_C.mp hU
  have hVe := totalDegree_eq_zero_iff_eq_C.mp hV
  have hc : coeff 0 U ≠ 0 := by
    intro h
    apply hU0
    rw [hUe,h,C_0]
  refine ⟨coeff 0 V / coeff 0 U, ?_⟩
  rw [hUe,hVe,MvPolynomial.smul_eq_C_mul,← mul_assoc,← map_mul]
  rw [coeff_zero_C,coeff_zero_C,div_mul_cancel₀ _ hc]

/-- Four independent quadratic coordinates satisfying the split rank-four
relation factor into four homogeneous linear forms. It is enough to exclude
proportionality of the first row and first column. -/
theorem four_quadric_linear_factorization
    (a b c d : MvPolynomial σ K)
    (ha : a.IsHomogeneous 2) (hb : b.IsHomogeneous 2)
    (hc : c.IsHomogeneous 2) (hd : d.IsHomogeneous 2)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hab : ∀ s : K, s • a ≠ b) (hac : ∀ s : K, s • a ≠ c)
    (hrel : a*d=b*c) :
    ∃ u₁ u₂ v₁ v₂ : MvPolynomial σ K,
      u₁.IsHomogeneous 1 ∧ u₂.IsHomogeneous 1 ∧
      v₁.IsHomogeneous 1 ∧ v₂.IsHomogeneous 1 ∧
      a=u₁*v₁ ∧ b=u₁*v₂ ∧ c=u₂*v₁ ∧ d=u₂*v₂ := by
  classical
  letI := UniqueFactorizationMonoid.toGCDMonoid (MvPolynomial σ K)
  obtain ⟨u₁,u₂,v₁,v₂,hae,hbe,hce,hde⟩ := rank_one_factorization a b c d ha0 hrel
  have hu₁ : u₁ ≠ 0 := by intro h; exact ha0 (by simp [hae,h])
  have hu₂ : u₂ ≠ 0 := by intro h; exact hc0 (by simp [hce,h])
  have hv₁ : v₁ ≠ 0 := by intro h; exact ha0 (by simp [hae,h])
  have hv₂ : v₂ ≠ 0 := by intro h; exact hb0 (by simp [hbe,h])
  have haD : u₁.totalDegree + v₁.totalDegree = 2 := by
    rw [← totalDegree_mul_of_isDomain hu₁ hv₁,← hae]
    exact ha.totalDegree ha0
  have hbD : u₁.totalDegree + v₂.totalDegree = 2 := by
    rw [← totalDegree_mul_of_isDomain hu₁ hv₂,← hbe]
    exact hb.totalDegree hb0
  have hcD : u₂.totalDegree + v₁.totalDegree = 2 := by
    rw [← totalDegree_mul_of_isDomain hu₂ hv₁,← hce]
    exact hc.totalDegree hc0
  have huD : u₁.totalDegree ≠ 0 := by
    intro h
    have h' : u₂.totalDegree = 0 := by omega
    obtain ⟨s,hs⟩ := constant_factors_proportional u₁ u₂ v₁ h h' hu₁
    exact hac s (by simpa [← hae,← hce] using hs)
  have hvD : v₁.totalDegree ≠ 0 := by
    intro h
    have h' : v₂.totalDegree = 0 := by omega
    obtain ⟨s,hs⟩ := constant_factors_proportional v₁ v₂ u₁ h h' hv₁
    exact hab s (by simpa [mul_comm,← hae,← hbe] using hs)
  have hu1D : u₁.totalDegree ≤ 1 := by omega
  have hu2D : u₂.totalDegree ≤ 1 := by omega
  have hv1D : v₁.totalDegree ≤ 1 := by omega
  have hv2D : v₂.totalDegree ≤ 1 := by omega
  refine ⟨linearPart u₁,linearPart u₂,linearPart v₁,linearPart v₂,
    linearPart_isHomogeneous _ hu1D,linearPart_isHomogeneous _ hu2D,
    linearPart_isHomogeneous _ hv1D,linearPart_isHomogeneous _ hv2D,?_,?_,?_,?_⟩
  · rw [hae]
    exact homogeneous_quadric_eq_linearParts u₁ v₁ hu1D hv1D (hae ▸ ha)
  · rw [hbe]
    exact homogeneous_quadric_eq_linearParts u₁ v₂ hu1D hv2D (hbe ▸ hb)
  · rw [hce]
    exact homogeneous_quadric_eq_linearParts u₂ v₁ hu2D hv1D (hce ▸ hc)
  · rw [hde]
    exact homogeneous_quadric_eq_linearParts u₂ v₂ hu2D hv2D (hde ▸ hd)

/-- The rank-three relation has the polynomial Veronese factorization
before any degree or independence argument is imposed. -/
theorem rank_three_factorization {R : Type*} [CommRing R] [IsDomain R] [GCDMonoid R]
    (a b c : R) (ha : a ≠ 0) (he : a*c=b^2) :
    ∃ h u v : R, a=h*u^2 ∧ b=h*u*v ∧ c=h*v^2 := by
  obtain ⟨u,v,hae,hbe,hcop⟩ := extract_gcd a b
  let g := gcd a b
  have hg : g ≠ 0 := by intro h; exact ha (by simpa [g,h] using hae)
  have hu : u ≠ 0 := by intro h; exact ha (by simpa [h] using hae)
  have hrel : u*c=g*v*v := by
    apply mul_left_cancel₀ hg
    change gcd a b * (u*c) = gcd a b * (g*v*v)
    calc
      _ = a*c := by rw [← mul_assoc,← hae]
      _ = b^2 := he
      _ = (g*v)^2 := congrArg (fun z => z^2) hbe
      _ = _ := by dsimp only [g]; ring
  have hcopp : IsRelPrime u v := gcd_isUnit_iff_isRelPrime.mp hcop
  have hudiv : u ∣ g := by
    apply hcopp.dvd_of_dvd_mul_right
    apply hcopp.dvd_of_dvd_mul_right
    rw [← hrel]
    exact dvd_mul_right _ _
  obtain ⟨h,hge⟩ := hudiv
  have hce : c=h*v^2 := by
    apply mul_left_cancel₀ hu
    rw [hrel,hge]
    ring
  refine ⟨h,u,v,?_,?_,hce⟩
  · rw [hae,show gcd a b = u*h from hge]
    ring
  · rw [hbe,show gcd a b = u*h from hge]
    ring

theorem homogeneous_of_nonzero_C_mul (a : K) (ha : a ≠ 0)
    (P : MvPolynomial σ K) (k : ℕ) (hP : (C a*P).IsHomogeneous k) : P.IsHomogeneous k := by
  intro d hd
  apply hP
  rw [coeff_C_mul]
  exact mul_ne_zero ha hd

/-- Three independent quadrics satisfying `a*c=b²` depend on two actual
homogeneous linear forms, with one nonzero common scalar. -/
theorem three_quadric_linear_factorization (a b c : MvPolynomial σ K)
    (ha : a.IsHomogeneous 2) (hb : b.IsHomogeneous 2) (hc : c.IsHomogeneous 2)
    (ha0 : a ≠ 0) (_hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hab : ∀ s : K, s • a ≠ b) (hrel : a*c=b^2) :
    ∃ t : K, t ≠ 0 ∧ ∃ u v : MvPolynomial σ K,
      u.IsHomogeneous 1 ∧ v.IsHomogeneous 1 ∧
      a=C t*u^2 ∧ b=C t*u*v ∧ c=C t*v^2 := by
  classical
  letI := UniqueFactorizationMonoid.toGCDMonoid (MvPolynomial σ K)
  obtain ⟨h,u,v,hae,hbe,hce⟩ := rank_three_factorization a b c ha0 hrel
  have hh : h ≠ 0 := by intro hz; exact ha0 (by simp [hae,hz])
  have hu : u ≠ 0 := by intro hz; exact ha0 (by simp [hae,hz])
  have hv : v ≠ 0 := by intro hz; exact hc0 (by simp [hce,hz])
  have haD : h.totalDegree + 2*u.totalDegree = 2 := by
    have hp : (h*(u*u)).totalDegree = h.totalDegree + (u.totalDegree+u.totalDegree) := by
      rw [totalDegree_mul_of_isDomain hh (mul_ne_zero hu hu),totalDegree_mul_of_isDomain hu hu]
    have hp' : h*(u*u) = a := by rw [hae]; ring
    rw [hp',ha.totalDegree ha0] at hp
    omega
  have hcD : h.totalDegree + 2*v.totalDegree = 2 := by
    have hp : (h*(v*v)).totalDegree = h.totalDegree + (v.totalDegree+v.totalDegree) := by
      rw [totalDegree_mul_of_isDomain hh (mul_ne_zero hv hv),totalDegree_mul_of_isDomain hv hv]
    have hp' : h*(v*v) = c := by rw [hce]; ring
    rw [hp',hc.totalDegree hc0] at hp
    omega
  have huD : u.totalDegree ≠ 0 := by
    intro hz
    have hvD : v.totalDegree = 0 := by omega
    obtain ⟨s,hs⟩ := constant_factors_proportional u v (h*u) hz hvD hu
    apply hab s
    have ha' : a=u*(h*u) := by rw [hae]; ring
    have hb' : b=v*(h*u) := by rw [hbe]; ring
    rw [ha',hb']
    exact hs
  have hD : h.totalDegree = 0 := by omega
  have hu1 : u.totalDegree ≤ 1 := by omega
  have hv1 : v.totalDegree ≤ 1 := by omega
  have hhC := totalDegree_eq_zero_iff_eq_C.mp hD
  have ht : coeff 0 h ≠ 0 := by intro hz; exact hh (by simpa [hz] using hhC)
  have hua : (u*u).IsHomogeneous 2 := by
    apply homogeneous_of_nonzero_C_mul (coeff 0 h) ht _ 2
    have h := ha
    rw [hae,hhC] at h
    simpa only [pow_two] using h
  have hub : (u*v).IsHomogeneous 2 := by
    apply homogeneous_of_nonzero_C_mul (coeff 0 h) ht _ 2
    have h := hb
    rw [hbe,hhC] at h
    simpa only [mul_assoc] using h
  have huc : (v*v).IsHomogeneous 2 := by
    apply homogeneous_of_nonzero_C_mul (coeff 0 h) ht _ 2
    have h := hc
    rw [hce,hhC] at h
    simpa only [pow_two] using h
  refine ⟨coeff 0 h,ht,linearPart u,linearPart v,
    linearPart_isHomogeneous u hu1,linearPart_isHomogeneous v hv1,?_,?_,?_⟩
  · rw [hae,hhC,pow_two,homogeneous_quadric_eq_linearParts u u hu1 hu1 hua]
    simp only [coeff_zero_C,pow_two]
  · rw [hbe,hhC,mul_assoc,homogeneous_quadric_eq_linearParts u v hu1 hv1 hub,mul_assoc]
    simp only [coeff_zero_C]
  · rw [hce,hhC,pow_two,homogeneous_quadric_eq_linearParts v v hv1 hv1 huc]
    simp only [coeff_zero_C,pow_two]

/-- Distinct members of a linearly independent family are not scalar
multiples, including a zero scalar. -/
theorem independent_not_proportional {ι : Type*} (p : ι → MvPolynomial σ K)
    (hp : LinearIndependent K p) (i j : ι) (hij : i ≠ j) :
    ∀ s : K, s • p i ≠ p j := by
  intro s he
  by_cases hs : s=0
  · subst s
    exact LinearIndependent.ne_zero j hp (by simpa using he.symm)
  · apply hij
    exact hp.eq_of_smul_apply_eq_smul_apply s 1 i j hs (by simpa using he)

/-- Source rank-three coordinate classification with actual independence. -/
theorem three_independent_quadrics (p : Fin 3 → MvPolynomial σ K)
    (hp : ∀ i, (p i).IsHomogeneous 2) (hlin : LinearIndependent K p)
    (hrel : p 0 * p 2 = (p 1)^2) :
    ∃ t : K, t ≠ 0 ∧ ∃ u v : MvPolynomial σ K,
      u.IsHomogeneous 1 ∧ v.IsHomogeneous 1 ∧
      p 0=C t*u^2 ∧ p 1=C t*u*v ∧ p 2=C t*v^2 :=
  three_quadric_linear_factorization (p 0) (p 1) (p 2) (hp 0) (hp 1) (hp 2)
    (LinearIndependent.ne_zero 0 hlin) (LinearIndependent.ne_zero 1 hlin)
    (LinearIndependent.ne_zero 2 hlin) (independent_not_proportional p hlin 0 1 (by decide)) hrel

/-- Source rank-four coordinate classification with actual independence. -/
theorem four_independent_quadrics (p : Fin 4 → MvPolynomial σ K)
    (hp : ∀ i, (p i).IsHomogeneous 2) (hlin : LinearIndependent K p)
    (hrel : p 0 * p 3 = p 1 * p 2) :
    ∃ u₁ u₂ v₁ v₂ : MvPolynomial σ K,
      u₁.IsHomogeneous 1 ∧ u₂.IsHomogeneous 1 ∧
      v₁.IsHomogeneous 1 ∧ v₂.IsHomogeneous 1 ∧
      p 0=u₁*v₁ ∧ p 1=u₁*v₂ ∧ p 2=u₂*v₁ ∧ p 3=u₂*v₂ :=
  four_quadric_linear_factorization (p 0) (p 1) (p 2) (p 3) (hp 0) (hp 1) (hp 2) (hp 3)
    (LinearIndependent.ne_zero 0 hlin) (LinearIndependent.ne_zero 1 hlin)
    (LinearIndependent.ne_zero 2 hlin) (independent_not_proportional p hlin 0 1 (by decide))
    (independent_not_proportional p hlin 0 2 (by decide)) hrel

end HessianTheorem11.QuadricLowRank

import CubicTenVariables.Literature.ProjectiveMicrolocalCertificate

/-! Numerical consequences of the supplied joint microlocal certificate.
Every bound below is proved from its explicit finite trace data and the
previously proved actual projective-count identities. No literature input
is introduced and no certificate is constructed here. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ProjectiveMicrolocalTraceBound

open MvPolynomial HessianTheorem11
open ProjectiveMicrolocalData ProjectiveFourierIdentity
open scoped BigOperators

/-- The actual finite-field normalized Fourier sum, with coefficient
1+2B because each of the two total ranks is at most the same integer B. -/
theorem normalizedFourierSum_bound_of_traceData {n d : ℕ} (hn : 3 ≤ n)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous d) (hd : 0 < d)
    (K : Type*) [Field K] [Fintype K] (ψ : AddChar K ℂ) (hψ : ψ ≠ 1)
    (v : Fin n → K) (hv : v ≠ 0) (e B : ℕ) (h : TraceData F K v e B) :
    ‖normalizedFourierSum ψ (map (Int.castRingHom K) F) v‖ ≤
      (1+2*(B : ℝ)) * (Fintype.card K : ℝ)^(((n : ℝ)-1+(e : ℝ))/2) := by
  obtain ⟨tX,tH,bX,bH,hcountX,hcountH,hX,hH,hBX,hBH,hcancel⟩ := h
  have hb := ProjectiveGysinTraceBound.normalizedFourierSum_bound
    ψ hψ (map (Int.castRingHom K) F) (hF.map _) hd v hv
    (B : ℝ) (B : ℝ) (2*n+1) (n-1+e) (by omega)
    tX tH bX bH
    (by simpa only [Nat.add_assoc] using hcountX) hcountH hX hH
    (by exact_mod_cast (show (∑ k ∈ Finset.range (2*n+1+2), bX k) ≤ B by
      simpa only [Nat.add_assoc] using hBX))
    (by exact_mod_cast hBH)
    (by simpa only [Nat.add_assoc] using hcancel)
  have he : ((n-1+e : ℕ) : ℝ) = (n : ℝ)-1+(e : ℝ) := by
    rw [Nat.cast_add, Nat.cast_sub (by omega)]
    norm_num
  have hc : 1+(B : ℝ)+(B : ℝ) = 1+2*(B : ℝ) := by ring
  simpa only [he,hc] using hb

/-- The actual prime-modulus complete sum. Nonzeroness is required after
reduction, and multiplication by p gives exponent (n+1+e)/2. -/
theorem completeCubicSum_bound_of_traceData {n d : ℕ} (hn : 3 ≤ n)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous d) (hd : 0 < d)
    (p : ℕ) [Fact p.Prime] (v : Fin n → ℤ)
    (hv : (fun i => (v i : ZMod p)) ≠ 0) (e B : ℕ)
    (h : TraceData F (ZMod p) (fun i => (v i : ZMod p)) e B) :
    ‖completeCubicSum F p v‖ ≤
      (1+2*(B : ℝ)) * (p : ℝ)^(((n : ℝ)+1+(e : ℝ))/2) := by
  obtain ⟨tX,tH,bX,bH,hcountX,hcountH,hX,hH,hBX,hBH,hcancel⟩ := h
  have hb := ProjectiveGysinTraceBound.completeCubicSum_bound F hF hd p v hv
    (B : ℝ) (B : ℝ) (2*n+1) (n-1+e) (by omega)
    tX tH bX bH
    (by simpa only [Nat.add_assoc] using hcountX) hcountH
    (by simpa only [ZMod.card] using hX)
    (by simpa only [ZMod.card] using hH)
    (by exact_mod_cast (show (∑ k ∈ Finset.range (2*n+1+2), bX k) ≤ B by
      simpa only [Nat.add_assoc] using hBX))
    (by exact_mod_cast hBH)
    (by simpa only [Nat.add_assoc,ZMod.card] using hcancel)
  have he : ((n-1+e : ℕ) : ℝ)/2+1 = ((n : ℝ)+1+(e : ℝ))/2 := by
    rw [Nat.cast_add, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hc : 1+(B : ℝ)+(B : ℝ) = 1+2*(B : ℝ) := by ring
  simpa only [he,hc] using hb

/-- Uniform good-prime data imply the actual Fourier bound in every finite
field of that characteristic and for every nontrivial additive character.
The integer e bounds the dimension of the actual geometric equation fiber. -/
theorem normalizedFourierSum_bound {n d t : ℕ} (hn : 3 ≤ n)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous d) (hd : 0 < d)
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial n n) (N B : ℕ)
    (h : GoodReduction F f N B) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ N)
    (K : Type) [Field K] [Fintype K] [CharP K p]
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) (v : Fin n → K) (hv : v ≠ 0) (e : ℕ)
    (he : IntegralGeometricFiberDepth.geometricFiberDimension f K v ≤ (e : Dimension)) :
    ‖normalizedFourierSum ψ (map (Int.castRingHom K) F) v‖ ≤
      (1+2*(B : ℝ)) * (Fintype.card K : ℝ)^(((n : ℝ)-1+(e : ℝ))/2) :=
  normalizedFourierSum_bound_of_traceData hn F hF hd K ψ hψ v hv e B
    (h.trace p hp K v hv e he)

/-- Prime specialization with the same fixed rank bound and prime exclusion. -/
theorem completeCubicSum_bound {n d t : ℕ} (hn : 3 ≤ n)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous d) (hd : 0 < d)
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial n n) (N B : ℕ)
    (h : GoodReduction F f N B) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ N)
    (v : Fin n → ℤ) (hv : (fun i => (v i : ZMod p)) ≠ 0) (e : ℕ)
    (he : IntegralGeometricFiberDepth.geometricFiberDimension f (ZMod p)
      (fun i => (v i : ZMod p)) ≤ (e : Dimension)) :
    ‖completeCubicSum F p v‖ ≤
      (1+2*(B : ℝ)) * (p : ℝ)^(((n : ℝ)+1+(e : ℝ))/2) :=
  completeCubicSum_bound_of_traceData hn F hF hd p v hv e B
    (h.trace p hp (ZMod p) (fun i => (v i : ZMod p)) hv e he)

end CubicTenVariables.ProjectiveMicrolocalTraceBound

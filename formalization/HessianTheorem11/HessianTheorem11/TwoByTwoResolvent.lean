import HessianTheorem11.PolynomialMoments
import HessianTheorem11.BinaryPolynomialCancellation

/-! The exact binary blocks in the four-dimensional symmetric resolvent
alternative. No diagonalization or generic coefficient assumption is used. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace HessianTheorem11.TwoByTwoResolvent
open Matrix PolynomialMoments BinaryPolynomialCancellation
variable {K : Type*} [Field K] [CharZero K]
abbrev Vec (K : Type*) := Fin 2 → K
abbrev Mat (K : Type*) := Matrix (Fin 2) (Fin 2) K

def gram : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := fromBlocks 0 1 1 0
def block (A B C : Mat K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks A B C A.transpose
def embed (u : Vec K) : Fin 2 ⊕ Fin 2 → K := Sum.elim u 0

theorem moment_one (A B C : Mat K) (u : Vec K) :
    moment gram (block A B C) (embed u) 1 = dotProduct u (C.mulVec u) := by
  simp [moment,gram,block,embed,Matrix.fromBlocks_multiply,Matrix.fromBlocks_mulVec,
    dotProduct, Fintype.sum_sum_type]

theorem moment_two (A B C : Mat K) (hC : C.IsSymm) (u : Vec K) :
    moment gram (block A B C) (embed u) 2 =
      2 * dotProduct (A.mulVec u) (C.mulVec u) := by
  simp [moment,gram,block,embed,pow_two,Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_mulVec,dotProduct,Matrix.mulVec,Matrix.mul_apply,
    Fintype.sum_sum_type,Fin.sum_univ_two]
  rw [hC.apply 0 1]
  ring

theorem moment_three (A B C : Mat K) (hC : C.IsSymm) (u : Vec K) :
    moment gram (block A B C) (embed u) 3 =
      dotProduct (A.mulVec u) (C.mulVec (A.mulVec u)) +
      2*dotProduct (C.mulVec u) (A.mulVec (A.mulVec u)) +
      dotProduct (C.mulVec u) (B.mulVec (C.mulVec u)) := by
  simp [moment,gram,block,embed,show (3:ℕ)=2+1 from rfl,pow_succ,pow_two,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_mulVec,dotProduct,Matrix.mulVec,
    Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two]
  rw [hC.apply 0 1]
  ring

/-- The forced lower-left binary block, with no generic-point premise. -/
def forcedC (b₁ b₂ : K) (u : Vec K) : Mat K :=
  !![-2*b₁*u 1, b₁*u 0-b₂*u 1;
     b₁*u 0-b₂*u 1, 2*b₂*u 0]

def perp (u : Vec K) : Vec K := ![-u 1,u 0]

theorem forcedC_mulVec (b₁ b₂ : K) (u : Vec K) :
    (forcedC b₁ b₂ u).mulVec u = (b₁*u 0+b₂*u 1) • perp u := by
  ext i
  fin_cases i <;> simp [forcedC,perp,mulVec,dotProduct,Fin.sum_univ_two] <;> ring

theorem forcedC_symm (b₁ b₂ : K) (u : Vec K) : (forcedC b₁ b₂ u).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem forcedC_pair (b₁ b₂ : K) (u v : Vec K) :
    dotProduct v ((forcedC b₁ b₂ u).mulVec v) =
      2*(b₁*v 0+b₂*v 1)*dotProduct (perp u) v := by
  simp [forcedC,perp,mulVec,dotProduct,Fin.sum_univ_two]
  ring

theorem perp_square (A : Mat K) (u : Vec K) :
    dotProduct (perp u) (A.mulVec (A.mulVec u)) =
      (A 0 0 + A 1 1) * dotProduct (perp u) (A.mulVec u) := by
  simp [perp,mulVec,dotProduct,Fin.sum_univ_two]
  ring

theorem forced_moment_three (A B : Mat K) (b₁ b₂ : K) (u : Vec K) :
    moment gram (block A B (forcedC b₁ b₂ u)) (embed u) 3 =
      2*((b₁*(A.mulVec u) 0+b₂*(A.mulVec u) 1)+
        (b₁*u 0+b₂*u 1)*(A 0 0+A 1 1))*dotProduct (perp u) (A.mulVec u) +
      (b₁*u 0+b₂*u 1)^2 * dotProduct (perp u) (B.mulVec (perp u)) := by
  rw [moment_three A B _ (forcedC_symm b₁ b₂ u),forcedC_pair,forcedC_mulVec]
  simp only [Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul,perp_square]
  ring

theorem symmetric_quadric_zero (C : Mat K) (hC : C.IsSymm)
    (hz : ∀ u, dotProduct u (C.mulVec u) = 0) : C = 0 := by
  have he := quadratic_zero_coefficients (C 0 0) (2*C 0 1) (C 1 1) (by
    intro x y
    have h := hz ![x,y]
    simp [dotProduct,mulVec,Fin.sum_univ_two] at h
    rw [hC.apply 0 1] at h
    linear_combination h)
  have h01 : C 0 1 = 0 := by linear_combination he.2.1 / 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [he.1,he.2.2,h01,hC.apply 0 1]

theorem binary_linear_expansion (C : Vec K →ₗ[K] Mat K) (u : Vec K) :
    C u = u 0 • C ![1,0] + u 1 • C ![0,1] := by
  have hu : u = u 0 • ![1,0] + u 1 • ![0,1] := by
    ext i; fin_cases i <;> simp
  conv_lhs => rw [hu,map_add,map_smul,map_smul]

theorem linearC_forced (C : Vec K →ₗ[K] Mat K) (hC : ∀ u, (C u).IsSymm)
    (hz : ∀ u, dotProduct u ((C u).mulVec u) = 0) :
    ∃ b₁ b₂ : K, ∀ u, C u = forcedC b₁ b₂ u := by
  let P := C ![1,0]
  let Q := C ![0,1]
  have hsP : P 1 0 = P 0 1 := (hC ![1,0]).apply 0 1
  have hsQ : Q 1 0 = Q 0 1 := (hC ![0,1]).apply 0 1
  have hcoef := cubic_zero_coefficients (P 0 0) (P 0 1) (P 1 1)
    (Q 0 0) (Q 0 1) (Q 1 1) (by
      intro x y
      have hh := hz ![x,y]
      rw [binary_linear_expansion] at hh
      change dotProduct ![x,y] ((x • P+y • Q).mulVec ![x,y]) = 0 at hh
      simp [dotProduct,mulVec,Fin.sum_univ_two,hsP,hsQ] at hh
      linear_combination hh)
  refine ⟨P 0 1,-Q 0 1,fun u => ?_⟩
  rw [binary_linear_expansion]
  change u 0 • P+u 1 • Q = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [forcedC,hsP,hsQ,hcoef.1,hcoef.2.1,hcoef.2.2.1,hcoef.2.2.2] <;> ring

theorem perp_self (u : Vec K) : dotProduct (perp u) u = 0 := by
  simp [perp,dotProduct,Fin.sum_univ_two]
  ring

/-- The kernel part of the lower-left block vanishes by the first moment. -/
theorem kernelC_zero (A B C : Vec K →ₗ[K] Mat K) (Az Bz Cz : Mat K)
    (hCz : Cz.IsSymm)
    (hm : ∀ u (t : K), moment gram (block (A u+t • Az) (B u+t • Bz)
      (C u+t • Cz)) (embed u) 1 = 0) : Cz=0 := by
  apply symmetric_quadric_zero Cz hCz
  intro u
  have h0 := hm u 0
  have h1 := hm u 1
  simp only [moment_one,zero_smul,one_smul,add_zero,Matrix.add_mulVec,
    dotProduct_add] at h0 h1
  linear_combination h1-h0

/-- If the forced lower block is nonzero, the upper-left kernel block is
scalar. This is a polynomial consequence of the second moment. -/
theorem kernelA_scalar (A B : Vec K →ₗ[K] Mat K) (Az Bz : Mat K)
    (b₁ b₂ : K) (hb : b₁≠0 ∨ b₂≠0)
    (hm : ∀ u (t : K), moment gram (block (A u+t • Az) (B u+t • Bz)
      (forcedC b₁ b₂ u)) (embed u) 2 = 0) : ∃ α : K, Az=α • 1 := by
  have hz (u : Vec K) : (b₁*u 0+b₂*u 1)*dotProduct (perp u) (Az.mulVec u) = 0 := by
    have h0 := hm u 0
    have h1 := hm u 1
    rw [moment_two _ _ _ (forcedC_symm b₁ b₂ u),forcedC_mulVec] at h0 h1
    simp only [zero_smul,one_smul,add_zero,Matrix.add_mulVec,dotProduct_smul,
      smul_eq_mul,add_dotProduct] at h0 h1
    rw [dotProduct_comm (Az.mulVec u) (perp u)] at h1
    linear_combination (h1-h0)/2
  have hc := cancel_linear_quadratic b₁ b₂ (Az 1 0) (Az 1 1-Az 0 0) (-Az 0 1)
    hb 1 (by
      intro x y
      have hh := hz ![x,y]
      simp [perp,dotProduct,mulVec,Fin.sum_univ_two,-mul_eq_zero,-pow_eq_zero] at hh
      linear_combination hh)
  have ha01 : Az 0 1=0 := neg_eq_zero.mp hc.2.2
  have ha11 : Az 1 1=Az 0 0 := sub_eq_zero.mp hc.2.1
  refine ⟨Az 0 0,?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hc.1,ha01,ha11,Matrix.one_apply]

/-- The third moment eliminates the symmetric upper-right kernel block
once the upper-left block is scalar. -/
theorem kernelB_zero (A B : Vec K →ₗ[K] Mat K) (Bz : Mat K) (hBz : Bz.IsSymm)
    (α b₁ b₂ : K) (hb : b₁≠0 ∨ b₂≠0)
    (hm : ∀ u (t : K) (j : ℕ), moment gram (block (A u+t • (α • (1 : Mat K))) (B u+t • Bz)
      (forcedC b₁ b₂ u)) (embed u) j = 0) : Bz=0 := by
  have hz (u : Vec K) : (b₁*u 0+b₂*u 1)^2 *
      dotProduct (perp u) (Bz.mulVec (perp u)) = 0 := by
    have h0 := hm u 0 3
    have h1 := hm u 1 3
    have h2 := hm u 0 2
    rw [forced_moment_three] at h0 h1
    rw [moment_two _ _ _ (forcedC_symm b₁ b₂ u),forcedC_mulVec] at h2
    simp only [zero_smul,one_smul,add_zero,Matrix.add_mulVec,Matrix.smul_mulVec,
      Matrix.one_mulVec,dotProduct_smul,smul_dotProduct,smul_eq_mul,
      add_dotProduct,dotProduct_add,perp_self,mul_zero,zero_add,add_zero,
      Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply,Matrix.zero_apply,ite_true] at h0 h1 h2
    rw [dotProduct_comm (A u |>.mulVec u) (perp u)] at h2
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at h1
    linear_combination h1-h0-3*α*h2
  apply symmetric_quadric_zero Bz hBz
  intro v
  have hc := cancel_linear_quadratic b₁ b₂ (Bz 1 1) (-2*Bz 0 1) (Bz 0 0)
    hb 2 (by
      intro x y
      have hh := hz ![x,y]
      simp [perp,dotProduct,mulVec,Fin.sum_univ_two,-mul_eq_zero,-pow_eq_zero] at hh
      rw [hBz.apply 0 1] at hh
      linear_combination hh)
  have hb01 : Bz 0 1=0 := by linear_combination -hc.2.1/2
  simp [dotProduct,mulVec,Fin.sum_univ_two,hc.1,hc.2.2,hb01,hBz.apply 0 1]

/-- Complete binary-block kernel comparison. The only possible obstruction
to invariance forces every kernel-direction four-by-four matrix to be scalar. -/
theorem kernel_block_scalar (A B C : Vec K →ₗ[K] Mat K)
    (hC : ∀ u, (C u).IsSymm) (hCne : C ≠ 0)
    (Az Bz Cz : Mat K) (hBz : Bz.IsSymm) (hCz : Cz.IsSymm)
    (hm : ∀ u (t : K) (j : ℕ), moment gram
      (block (A u+t • Az) (B u+t • Bz) (C u+t • Cz)) (embed u) j = 0) :
    ∃ α : K, block Az Bz Cz = α • 1 := by
  have hcz := kernelC_zero A B C Az Bz Cz hCz (fun u t => hm u t 1)
  have hbase : ∀ u, dotProduct u ((C u).mulVec u)=0 := by
    intro u
    simpa only [zero_smul,add_zero,moment_one] using hm u 0 1
  obtain ⟨b₁,b₂,hforced⟩ := linearC_forced C hC hbase
  have hb : b₁≠0 ∨ b₂≠0 := by
    by_contra hh
    push_neg at hh
    apply hCne
    apply LinearMap.ext
    intro u
    ext i j
    change C u i j = 0
    rw [hforced]
    fin_cases i <;> fin_cases j <;> simp [forcedC,hh.1,hh.2]
  have hm' : ∀ u (t : K) (j : ℕ), moment gram
      (block (A u+t • Az) (B u+t • Bz) (forcedC b₁ b₂ u)) (embed u) j=0 := by
    intro u t j
    simpa only [hcz,smul_zero,add_zero,hforced] using hm u t j
  obtain ⟨α,ha⟩ := kernelA_scalar A B Az Bz b₁ b₂ hb (fun u t => hm' u t 2)
  have hbz := kernelB_zero A B Bz hBz α b₁ b₂ hb (by simpa only [ha] using hm')
  refine ⟨α,?_⟩
  rw [ha,hbz,hcz]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [block,Matrix.one_apply,Matrix.transpose_apply]

end HessianTheorem11.TwoByTwoResolvent

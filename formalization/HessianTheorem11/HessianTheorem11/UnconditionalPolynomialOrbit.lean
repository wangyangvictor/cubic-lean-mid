import HessianTheorem11.UnconditionalOrbitCoefficients
import HessianTheorem11.UnconditionalSpectrumPointOpen

/-! The finite coefficient orbit map and right matrix translations are
actual polynomial maps. -/
noncomputable section
namespace HessianTheorem11.UnconditionalPolynomialOrbit
open MvPolynomial Matrix PolynomialRestriction PolynomialWeightTransport
  UnconditionalOrbitIdeal ReducedOrbitCoordinates

abbrev MatrixPoint (n : ℕ) := (Fin n × Fin n) → GeometricField

def matrixPoint {n : ℕ} (A : Matrix (Fin n) (Fin n) GeometricField) : MatrixPoint n :=
  fun ij => A ij.1 ij.2

def pointMatrix {n : ℕ} (x : MatrixPoint n) : Matrix (Fin n) (Fin n) GeometricField :=
  fun i j => x (i,j)

@[simp] theorem pointMatrix_matrixPoint {n : ℕ} (A : Matrix (Fin n) (Fin n) GeometricField) :
    pointMatrix (matrixPoint A) = A := rfl

@[simp] theorem matrixPoint_pointMatrix {n : ℕ} (x : MatrixPoint n) :
    matrixPoint (pointMatrix x) = x := by ext ⟨i,j⟩; rfl

def genericMatrix (n : ℕ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) GeometricField) := fun i j => X (i,j)

def universalRestriction {n : ℕ} (F : GeometricPolynomial n) :
    MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) GeometricField) :=
  restrict (genericMatrix n) (map C F)

theorem map_universalRestriction {n : ℕ} (F : GeometricPolynomial n) (x : MatrixPoint n) :
    map (eval x) (universalRestriction F) = restrict (pointMatrix x) F := by
  rw [universalRestriction, map_restrict, MvPolynomial.map_map]
  have hm : (genericMatrix n).map (eval x) = pointMatrix x := by ext i j; simp [genericMatrix,pointMatrix]
  have hc : (eval x).comp C = RingHom.id GeometricField := by ext c; simp
  rw [hm,hc,MvPolynomial.map_id]

def orbitPolynomials {n d : ℕ} (F : GeometricPolynomial n) :
    DegreeIndex n d → MvPolynomial (Fin n × Fin n) GeometricField :=
  fun e => coeff e.val (universalRestriction F)

@[simp] theorem polynomialMap_orbitPolynomials {n d : ℕ}
    (F : GeometricPolynomial n) (x : MatrixPoint n) :
    polynomialMap (orbitPolynomials (d := d) F) x = coefficientVector (restrict (pointMatrix x) F) := by
  ext e
  change eval x (coeff e.val (universalRestriction F)) = coeff e.val (restrict (pointMatrix x) F)
  rw [← coeff_map,map_universalRestriction]

def rightTranslationPolynomials {n : ℕ} (B : Matrix (Fin n) (Fin n) GeometricField) :
    (Fin n × Fin n) → MvPolynomial (Fin n × Fin n) GeometricField :=
  fun ij => ∑ k, X (ij.1,k) * C (B k ij.2)

@[simp] theorem polynomialMap_rightTranslation {n : ℕ}
    (B : Matrix (Fin n) (Fin n) GeometricField) (x : MatrixPoint n) :
    polynomialMap (rightTranslationPolynomials B) x = matrixPoint (pointMatrix x * B) := by
  ext ⟨i,j⟩
  simp [polynomialMap,rightTranslationPolynomials,matrixPoint,pointMatrix,Matrix.mul_apply]

def rightTranslatePolynomial {n : ℕ} (B : Matrix (Fin n) (Fin n) GeometricField)
    (q : MvPolynomial (Fin n × Fin n) GeometricField) :=
  aeval (rightTranslationPolynomials B) q

@[simp] theorem eval_rightTranslatePolynomial {n : ℕ}
    (B : Matrix (Fin n) (Fin n) GeometricField)
    (q : MvPolynomial (Fin n × Fin n) GeometricField) (x : MatrixPoint n) :
    eval x (rightTranslatePolynomial B q) = eval (matrixPoint (pointMatrix x * B)) q := by
  rw [rightTranslatePolynomial,← eval_polynomialMap,polynomialMap_rightTranslation]

/-- Pull a finite coefficient equation back under the actual right
coordinate action, then view it in the original coefficient test ring. -/
def translatedCoefficientTest {n d : ℕ}
    (B : Matrix (Fin n) (Fin n) GeometricField)
    (p : MvPolynomial (DegreeIndex n d) GeometricField) :
    MvPolynomial (Fin n →₀ ℕ) GeometricField :=
  aeval (fun e : DegreeIndex n d => coefficientRestriction B d e.val) p

theorem eval_translatedCoefficientTest {n d : ℕ}
    (B : Matrix (Fin n) (Fin n) GeometricField)
    (p : MvPolynomial (DegreeIndex n d) GeometricField)
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous d) :
    eval (fun e => coeff e F) (translatedCoefficientTest B p) =
      eval (coefficientVector (d := d) (restrict B F)) p := by
  change aeval (fun e => coeff e F)
    (aeval (fun e : DegreeIndex n d => coefficientRestriction B d e.val) p) = _
  rw [MvPolynomial.comp_aeval_apply]
  have he : (fun e : DegreeIndex n d => aeval (fun m => coeff m F)
      (coefficientRestriction B d e.val)) = coefficientVector (d := d) (restrict B F) := by
    ext e
    exact eval_coefficientRestriction B F hF e.val
  rw [he]
  rfl

end HessianTheorem11.UnconditionalPolynomialOrbit

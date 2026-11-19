/- Adapted from Leonardo Bonanno's lean-formalizations
(https://github.com/leobon12/lean-formalizations), modules
ReflectedGMS.Forms.ComplexSequenceSpace and ComplexifiedOperator, commit fdb5cad. -/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Complex.OperatorNorm

/-!
# Complexification of square-summable sequence operators

Real sequence operators extend to complex square-summable sequences while
preserving the operator norm and their action on real sequences.
-/

set_option autoImplicit false

open scoped ENNReal

namespace LatticeProb.Graph.LongRangeKernel.ComplexSequenceSpace

abbrev ValueSpace (V : Type*) := lp (fun _ : V => ℝ) 2

/-- The complex `lp 2` space. -/
noncomputable abbrev ComplexL2 (V : Type*) := lp (fun _ : V => ℂ) 2

variable (V : Type*)

/-- Coordinatewise real part. -/
noncomputable def realPart : ComplexL2 V →L[ℝ] ValueSpace V :=
  lp.mapCLM 2 (fun _ : V => Complex.reCLM) zero_le_one
    (fun _ => Complex.reCLM_norm.le)

/-- Coordinatewise imaginary part. -/
noncomputable def imagPart : ComplexL2 V →L[ℝ] ValueSpace V :=
  lp.mapCLM 2 (fun _ : V => Complex.imCLM) zero_le_one
    (fun _ => Complex.imCLM_norm.le)

/-- Coordinatewise real embedding into complex square-summable sequences. -/
noncomputable def ofReal : ValueSpace V →L[ℝ] ComplexL2 V :=
  lp.mapCLM 2 (fun _ : V => Complex.ofRealCLM) zero_le_one
    (fun _ => Complex.ofRealCLM_norm.le)

@[simp] theorem realPart_apply (z : ComplexL2 V) (v : V) :
    realPart V z v = (z v).re := rfl

@[simp] theorem imagPart_apply (z : ComplexL2 V) (v : V) :
    imagPart V z v = (z v).im := rfl

@[simp] theorem ofReal_apply (f : ValueSpace V) (v : V) :
    ofReal V f v = (f v : ℂ) := rfl

@[simp] theorem realPart_ofReal (f : ValueSpace V) : realPart V (ofReal V f) = f := by
  apply lp.ext
  funext v
  simp

@[simp] theorem imagPart_ofReal (f : ValueSpace V) : imagPart V (ofReal V f) = 0 := by
  apply lp.ext
  funext v
  simp

/-- Every complex square-summable sequence reconstructs from its real parts. -/
theorem reconstruction (z : ComplexL2 V) :
    ofReal V (realPart V z) + Complex.I • ofReal V (imagPart V z) = z := by
  apply lp.ext
  funext v
  change ((z v).re : ℂ) + Complex.I * ((z v).im : ℂ) = z v
  simpa only [mul_comm Complex.I] using Complex.re_add_im (z v)

/-- Equality of the real and imaginary parts determines the entire sequence. -/
theorem ext_parts {z w : ComplexL2 V}
    (hre : realPart V z = realPart V w) (him : imagPart V z = imagPart V w) : z = w := by
  rw [← reconstruction V z, ← reconstruction V w, hre, him]

/-- The real embedding is injective. -/
theorem ofReal_injective : Function.Injective (ofReal V) := by
  intro f g h
  simpa only [realPart_ofReal] using congrArg (realPart V) h

/-- The real embedding preserves the `lp 2` norm. -/
@[simp] theorem ofReal_norm (f : ValueSpace V) : ‖ofReal V f‖ = ‖f‖ := by
  apply le_antisymm
  · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro v
    simp only [ofReal_apply, Complex.norm_real, le_refl]
  · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro v
    simp only [ofReal_apply, Complex.norm_real, le_refl]

private theorem norm_sq_eq_tsum {E : V → Type*} [∀ v, NormedAddCommGroup (E v)]
    (z : lp E 2) : ‖z‖ ^ 2 = ∑' v, ‖z v‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.norm_rpow_eq_tsum (E := E) (p := 2) (by norm_num) z)

/-- The exact real/imaginary decomposition of the complex Hilbert norm. -/
theorem norm_sq_decomposition (z : ComplexL2 V) :
    ‖z‖ ^ 2 = ‖realPart V z‖ ^ 2 + ‖imagPart V z‖ ^ 2 := by
  have hs (f : ValueSpace V) : Summable (fun v => ‖f v‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (f.property.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))
  rw [norm_sq_eq_tsum, norm_sq_eq_tsum, norm_sq_eq_tsum,
    ← (hs (realPart V z)).tsum_add (hs (imagPart V z))]
  apply tsum_congr
  intro v
  simp only [realPart_apply, imagPart_apply, Real.norm_eq_abs, sq_abs,
    Complex.sq_norm, Complex.normSq_apply]
  ring

end LatticeProb.Graph.LongRangeKernel.ComplexSequenceSpace

open scoped InnerProductSpace

namespace LatticeProb.Graph.LongRangeKernel.ComplexSequenceSpace


variable {V : Type*}

/-- Real part of complex scalar multiplication. -/
theorem realPart_complex_smul (c : ℂ) (z : ComplexL2 V) :
    realPart V (c • z) = c.re • realPart V z - c.im • imagPart V z := by
  apply lp.ext
  funext v
  change (c * z v).re = c.re * (z v).re - c.im * (z v).im
  exact Complex.mul_re c (z v)

/-- Imaginary part of complex scalar multiplication. -/
theorem imagPart_complex_smul (c : ℂ) (z : ComplexL2 V) :
    imagPart V (c • z) = c.re • imagPart V z + c.im • realPart V z := by
  apply lp.ext
  funext v
  change (c * z v).im = c.re * (z v).im + c.im * (z v).re
  exact Complex.mul_im c (z v)

/-- The extension as a real-linear operator. -/
noncomputable def complexifyReal (T : ValueSpace V →L[ℝ] ValueSpace V) :
    ComplexL2 V →L[ℝ] ComplexL2 V :=
  (ofReal V).comp (T.comp (realPart V)) +
    Complex.I • ((ofReal V).comp (T.comp (imagPart V)))

@[simp] theorem complexifyReal_apply (T : ValueSpace V →L[ℝ] ValueSpace V)
    (z : ComplexL2 V) (v : V) :
    complexifyReal T z v = (T (realPart V z) v : ℂ) +
      Complex.I * (T (imagPart V z) v : ℂ) := rfl

@[simp] theorem realPart_complexifyReal (T : ValueSpace V →L[ℝ] ValueSpace V)
    (z : ComplexL2 V) : realPart V (complexifyReal T z) = T (realPart V z) := by
  apply lp.ext
  funext v
  simp [realPart_apply, complexifyReal_apply, Complex.mul_re]

@[simp] theorem imagPart_complexifyReal (T : ValueSpace V →L[ℝ] ValueSpace V)
    (z : ComplexL2 V) : imagPart V (complexifyReal T z) = T (imagPart V z) := by
  apply lp.ext
  funext v
  simp [imagPart_apply, complexifyReal_apply, Complex.mul_im]

/-- The extension as a continuous complex-linear operator. -/
noncomputable def complexify (T : ValueSpace V →L[ℝ] ValueSpace V) :
    ComplexL2 V →L[ℂ] ComplexL2 V where
  __ := complexifyReal T
  map_smul' c z := by
    change complexifyReal T (c • z) = c • complexifyReal T z
    apply ext_parts V
    · simp only [realPart_complexifyReal, realPart_complex_smul, map_sub, map_smul,
        imagPart_complexifyReal]
    · simp only [imagPart_complexifyReal, imagPart_complex_smul, map_add, map_smul,
        realPart_complexifyReal]

@[simp] theorem realPart_complexify (T : ValueSpace V →L[ℝ] ValueSpace V)
    (z : ComplexL2 V) : realPart V (complexify T z) = T (realPart V z) :=
  realPart_complexifyReal T z

@[simp] theorem imagPart_complexify (T : ValueSpace V →L[ℝ] ValueSpace V)
    (z : ComplexL2 V) : imagPart V (complexify T z) = T (imagPart V z) :=
  imagPart_complexifyReal T z

/-- The extension agrees exactly with the original real operator. -/
@[simp] theorem complexify_ofReal (T : ValueSpace V →L[ℝ] ValueSpace V)
    (f : ValueSpace V) : complexify T (ofReal V f) = ofReal V (T f) := by
  apply ext_parts V <;> simp

/-- The original operator norm controls the complex extension on every vector. -/
theorem complexify_apply_norm_le (T : ValueSpace V →L[ℝ] ValueSpace V)
    (z : ComplexL2 V) : ‖complexify T z‖ ≤ ‖T‖ * ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg (complexify T z))
    (mul_nonneg (norm_nonneg T) (norm_nonneg z))).1
  rw [norm_sq_decomposition V (complexify T z), realPart_complexify,
    imagPart_complexify, mul_pow, norm_sq_decomposition V z]
  have hre := (sq_le_sq₀ (norm_nonneg (T (realPart V z)))
    (mul_nonneg (norm_nonneg T) (norm_nonneg (realPart V z)))).2
      (T.le_opNorm (realPart V z))
  have him := (sq_le_sq₀ (norm_nonneg (T (imagPart V z)))
    (mul_nonneg (norm_nonneg T) (norm_nonneg (imagPart V z)))).2
      (T.le_opNorm (imagPart V z))
  calc
    _ ≤ (‖T‖ * ‖realPart V z‖) ^ 2 + (‖T‖ * ‖imagPart V z‖) ^ 2 :=
      add_le_add hre him
    _ = _ := by ring

/-- The complex extension has no larger operator norm. -/
theorem complexify_norm_le (T : ValueSpace V →L[ℝ] ValueSpace V) :
    ‖complexify T‖ ≤ ‖T‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) (complexify_apply_norm_le T)

/-- The isometric real embedding gives the reverse inequality as well. -/
@[simp] theorem complexify_norm (T : ValueSpace V →L[ℝ] ValueSpace V) :
    ‖complexify T‖ = ‖T‖ := by
  apply le_antisymm (complexify_norm_le T)
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (complexify T))
  intro f
  simpa only [complexify_ofReal, ofReal_norm] using
    (complexify T).le_opNorm (ofReal V f)

/-- The inner product of embedded real vectors. -/
theorem ofReal_inner (f g : ValueSpace V) :
    ⟪ofReal V f, ofReal V g⟫_ℂ = (⟪f, g⟫_ℝ : ℂ) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, Complex.ofReal_tsum]
  apply tsum_congr
  intro v
  simp [ofReal_apply, RCLike.inner_apply]

end LatticeProb.Graph.LongRangeKernel.ComplexSequenceSpace

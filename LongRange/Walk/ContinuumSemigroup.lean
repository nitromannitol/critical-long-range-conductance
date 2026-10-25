import LongRange.Model.Conductance
import LatticeProb.Prob.BrownianDirichlet.KilledStrongContinuity
import LatticeProb.Prob.BrownianDirichlet.ResolventIdentification
import LatticeProb.Analysis.ContractionSemigroupResolvent
import LatticeProb.Analysis.Elliptic.EuclideanTransport
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Brownian evolution in coordinates

Lebesgue measure transports the Euclidean ball to its coordinate image. The resulting
L² isometry conjugates the killed Brownian evolution without changing the ball's norm.
-/

namespace LongRange

open MeasureTheory LatticeProb ContractionSemigroup

noncomputable section

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "V" => Fin d → ℝ
local notation "q" => EuclideanSpace.equiv (Fin d) ℝ

/-- The coordinate image of the Euclidean ball. -/
def continuumDomain (R : ℝ) : Set V := q '' Metric.ball (0 : E) R

/-- Coordinate projection preserves restricted Lebesgue measure. -/
theorem coord_measurePreserving (R : ℝ) :
    MeasurePreserving q (volume.restrict (Metric.ball (0 : E) R))
      (volume.restrict (continuumDomain (d := d) R)) :=
  (PiLp.volume_preserving_ofLp (Fin d)).restrict_image_emb
    (MeasurableEquiv.toLp 2 V).symm.measurableEmbedding _

/-- Inverse coordinates preserve the corresponding restricted measures. -/
theorem coord_symm_measurePreserving (R : ℝ) :
    MeasurePreserving (q).symm (volume.restrict (continuumDomain (d := d) R))
      (volume.restrict (Metric.ball (0 : E) R)) :=
  MeasurePreserving.symm (MeasurableEquiv.toLp 2 V).symm (coord_measurePreserving (d := d) R)

/-- L² transport is composition with inverse coordinates. -/
def coordLp (R : ℝ) :
    Lp ℝ 2 (volume.restrict (Metric.ball (0 : E) R)) ≃ₗᵢ[ℝ]
      Lp ℝ 2 (volume.restrict (continuumDomain (d := d) R)) where
  toLinearEquiv :=
    { toLinearMap := Lp.compMeasurePreservingₗ ℝ (q).symm
        (coord_symm_measurePreserving (d := d) R)
      invFun := Lp.compMeasurePreserving q (coord_measurePreserving (d := d) R)
      left_inv := by
        intro f
        change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
        rw [← Lp.compMeasurePreserving_comp_apply]
        have he : (q).symm ∘ q = id := funext (q).symm_apply_apply
        simp only [he, Lp.compMeasurePreserving_id_apply]
      right_inv := by
        intro f
        change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
        rw [← Lp.compMeasurePreserving_comp_apply]
        have he : q ∘ (q).symm = id := funext (q).apply_symm_apply
        simp only [he, Lp.compMeasurePreserving_id_apply] }
  norm_map' := fun f => Lp.norm_compMeasurePreserving f _

/-- Balls carry finite restricted volume. -/
private instance finiteVolumeBall (R : ℝ) :
    IsFiniteMeasure (volume.restrict (Metric.ball (0 : E) R)) :=
  isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne

/-- Isometric conjugation preserves contraction and continuity of semigroup orbits. -/
private def conjugateSemigroup {H K : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]
    (e : H ≃ₗᵢ[ℝ] K) (T : StronglyContinuousContractionSemigroup H) :
    StronglyContinuousContractionSemigroup K where
  operator t := e.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((T.operator t).comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  map_zero := by
    apply ContinuousLinearMap.ext
    intro f
    change e (T.operator 0 (e.symm f)) = f
    rw [T.map_zero, ContinuousLinearMap.id_apply, e.apply_symm_apply]
  map_add s t := by
    apply ContinuousLinearMap.ext
    intro f
    change e (T.operator (s + t) (e.symm f)) =
      e (T.operator s (e.symm (e (T.operator t (e.symm f)))))
    rw [T.map_add, ContinuousLinearMap.comp_apply, e.symm_apply_apply]
  norm_le_one t := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    change ‖e (T.operator t (e.symm f))‖ ≤ 1 * ‖f‖
    rw [e.norm_map, one_mul]
    exact ((T.operator t).le_of_opNorm_le (T.norm_le_one t) _).trans_eq
      (by rw [one_mul, e.symm.norm_map])
  continuous_orbit f := e.continuous.comp (T.continuous_orbit (e.symm f))

/-- Killed Brownian evolution conjugated by its coordinate L² isometry. -/
def continuumSemigroup (R a₀ : ℝ) {μB : Measure (BrownianPath d)}
    (hμB : IsStandardBrownianLaw μB) :
    StronglyContinuousContractionSemigroup
      (Lp ℝ 2 (volume.restrict (continuumDomain (d := d) R))) :=
  conjugateSemigroup (coordLp (d := d) R)
    (killedSemigroup (B := Metric.ball (0 : E) R) Metric.isOpen_ball
      (Real.sqrt (2 * a₀)) hμB)

/-- The coordinate resolvent is the conjugate of the Euclidean killed resolvent. -/
theorem continuum_resolvent (R a₀ : ℝ) {μB : Measure (BrownianPath d)}
    (hμB : IsStandardBrownianLaw μB) {μ : ℝ} (hμ : 0 < μ)
    (f : Lp ℝ 2 (volume.restrict (continuumDomain (d := d) R))) :
    resolvent (continuumSemigroup R a₀ hμB) μ hμ f =
      coordLp (d := d) R (resolvent
        (killedSemigroup (B := Metric.ball (0 : E) R) Metric.isOpen_ball
          (Real.sqrt (2 * a₀)) hμB) μ hμ ((coordLp (d := d) R).symm f)) := by
  rw [resolvent_apply, resolvent_apply]
  calc
    _ = ∫ t in Set.Ioi (0 : ℝ), coordLp (d := d) R
        (Real.exp (-μ * t) •
          (killedSemigroup (B := Metric.ball (0 : E) R) Metric.isOpen_ball
            (Real.sqrt (2 * a₀)) hμB).operator t.toNNReal
              ((coordLp (d := d) R).symm f)) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      exact ((coordLp (d := d) R).map_smul _ _).symm
    _ = _ := (coordLp (d := d) R).toLinearIsometry.integral_comp_comm _

/-- A coordinate classical solution identifies the transported resolvent. -/
theorem continuumResolvent_classical {R a₀ μ : ℝ} {μB : Measure (BrownianPath d)}
    (hμB : IsStandardBrownianLaw μB) (hR : 0 < R) (ha₀ : 0 < a₀) (hμ : 0 < μ)
    {f u : V → ℝ} (hu : Elliptic.IsClassicalDirichletSolution
      (continuumDomain (d := d) R) μ a₀ f u)
    (hf : ContinuousOn f (closure (continuumDomain (d := d) R))) :
    ∃ (hfLp : MemLp f 2 (volume.restrict (continuumDomain (d := d) R)))
      (huLp : MemLp u 2 (volume.restrict (continuumDomain (d := d) R))),
      resolvent (continuumSemigroup R a₀ hμB) μ hμ (hfLp.toLp f) = huLp.toLp u := by
  obtain ⟨hv, hvc, hz, hpde⟩ :=
    Elliptic.isClassicalDirichletSolution_transport (0 : E) hR hu
  have hfc : ContinuousOn (f ∘ q) (closure (Metric.ball (0 : E) R)) := by
    apply hf.comp (q).continuous.continuousOn
    intro x hx
    rw [continuumDomain, ← Elliptic.image_closure_equiv]
    exact ⟨x, hx, rfl⟩
  have hfE := memLp_restrict_of_continuousOn_closure Metric.isOpen_ball
    Metric.isBounded_ball hfc
  have huE := memLp_restrict_of_continuousOn_closure Metric.isOpen_ball
    Metric.isBounded_ball hvc
  have hfLp : MemLp f 2 (volume.restrict (continuumDomain (d := d) R)) := by
    simpa only [Function.comp_def, (q).apply_symm_apply] using
      hfE.comp_measurePreserving (coord_symm_measurePreserving (d := d) R)
  have huLp : MemLp u 2 (volume.restrict (continuumDomain (d := d) R)) := by
    simpa only [Function.comp_def, (q).apply_symm_apply] using
      huE.comp_measurePreserving (coord_symm_measurePreserving (d := d) R)
  refine ⟨hfLp, huLp, ?_⟩
  have hforce : (coordLp (d := d) R).symm (hfLp.toLp f) = hfE.toLp (f ∘ q) := rfl
  have hsol : coordLp (d := d) R (huE.toLp (u ∘ q)) = huLp.toLp u := by
    change Lp.compMeasurePreserving _ _ _ = _
    rw [Lp.toLp_compMeasurePreserving]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall (fun x => congrArg u ((q).apply_symm_apply x))
  rw [continuum_resolvent R a₀ hμB hμ, hforce]
  rw [resolvent_killed_classical hμB hR ha₀ hμ hv hvc
    (by simpa only [frontier_ball _ hR.ne'] using hz) hfc hpde hfE huE]
  exact hsol

/-- Uniform ellipticity gives strictly positive mean conductance. -/
theorem meanConductance_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {lam : ℝ} {a : Ω → Edge d → ℝ} (hU : AssumptionU P lam a) (hd : 1 ≤ d) :
    0 < meanConductance P hd a := by
  letI := hU.isProbabilityMeasure
  have hi : Integrable (fun ω => a ω (baseEdge hd)) P :=
    (integrable_const (lam⁻¹)).mono'
      (hU.measurable _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg ((hU.lam_pos.le).trans (hU.bounds ω _).1)]
        exact (hU.bounds ω _).2)
  have hmean : lam ≤ meanConductance P hd a := by
    simpa only [meanConductance, integral_const, probReal_univ, one_smul] using
      integral_mono (integrable_const lam) hi (fun ω => (hU.bounds ω _).1)
  exact hU.lam_pos.trans_le hmean

/-- The effective diffusion coefficient has the paper's positive normalization. -/
theorem continuum_coefficient_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {lam : ℝ} {a : Ω → Edge d → ℝ} (hU : AssumptionU P lam a) (hd : 1 ≤ d) :
    0 < meanConductance P hd a / (2 * (d : ℝ)) :=
  div_pos (meanConductance_pos hU hd)
    (mul_pos (by norm_num) (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)))

end

end LongRange

import LatticeProb.Prob.Cadlag.HalfLine.AldousFinite
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite-horizon Aldous criterion

The canonical-path-law form of the finite-horizon criterion uses the raw natural
filtration and the Euclidean metric with vector J1 topology. The two cited book results
remain explicit inputs; the finite-horizon adapters are proved in the library.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

/-- Aldous' sufficient finite-horizon criterion at paper lines 478–490, with the raw
natural stopping filtration and the two genuine cited book inputs made explicit. -/

theorem LongRange.Statements.aldous
    (hEK : LatticeProb.External.EthierKurtzRelativeCompactnessStopping)
    (hPol : LatticeProb.External.BillingsleySkorokhodPolish) :
    ∀ (d : ℕ) (T : ℝ) (hT : 0 < T),
      let E := EuclideanSpace ℝ (Fin d)
      let I := Set.Icc (0 : ℝ) T
      let Pth := LatticeProb.Cadlag.D T E
      let info : I → MeasurableSpace Pth := fun t =>
        ⨆ s : I, ⨆ (_ : s ≤ t),
          MeasurableSpace.comap (fun x : Pth => x.1 s) (borel E)
      let clip : I → ℝ≥0 → I := fun t u =>
        ⟨min ((t : ℝ) + (u : ℝ)) T,
          ⟨le_min (add_nonneg t.2.1 u.2) hT.le, min_le_right _ _⟩⟩
      ∀ mu : ℕ → ProbabilityMeasure Pth,
        (∀ t : I,
          IsTightMeasureSet (Set.range (fun n =>
            (((mu n).map
              (LatticeProb.Cadlag.measurable_eval t).aemeasurable) : Measure E)))) →
        (∀ eta : ℝ, 0 < eta →
          ∀ tau : ℕ → Pth → I,
            (∀ n (t : I), @MeasurableSet Pth (info t)
              {x | tau n x ≤ t}) →
            Tendsto (fun delta : ℝ =>
              Filter.limsup (fun n =>
                ⨆ u : ℝ≥0, ⨆ (_ : (u : ℝ) ≤ delta),
                  (mu n : Measure Pth)
                    {x | eta ≤ dist (x.1 (clip (tau n x) u))
                      (x.1 (tau n x))}) atTop)
              (𝓝[>] 0) (𝓝 0)) →
        IsTightMeasureSet
          (Set.range (fun n => (mu n : Measure Pth))) :=

by
  intro d T hT E I Pth info clip mu hmarginal hincrement
  exact LatticeProb.Cadlag.HalfLine.isTightMeasureSet_of_finite_stoppingIncrementCondition
    hEK hPol hT mu hmarginal hincrement

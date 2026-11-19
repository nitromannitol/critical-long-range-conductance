import LongRange.Support.Prob.Cadlag.HalfLine.Paths
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Locally uniform limits of càdlàg paths

Locally uniform convergence preserves the càdlàg property when the state space
is complete. This is used in the construction of limits of Skorokhod Cauchy sequences.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter
open scoped Topology

/-- A uniform limit retains filter limits when the target is complete. -/
theorem exists_tendsto_of_tendstoUniformlyOn {α E : Type*} [MetricSpace E] [CompleteSpace E]
    {p : Filter α} [NeBot p] {s : Set α} (hs : s ∈ p)
    {f : ℕ → α → E} {g : α → E} {l : ℕ → E}
    (hu : TendstoUniformlyOn f g atTop s)
    (hl : ∀ n, Tendsto (f n) p (𝓝 (l n))) :
    ∃ a, Tendsto g p (𝓝 a) := by
  have hc : CauchySeq l := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (Metric.tendstoUniformlyOn_iff.mp hu (ε / 3) (by positivity))
    refine ⟨N, fun m hm n hn => ?_⟩
    have hb : ∀ᶠ x in p, dist (f m x) (f n x) ≤ 2 * (ε / 3) := by
      filter_upwards [hs] with x hx
      have hm' := hN m hm x hx
      have hn' := hN n hn x hx
      have htri := dist_triangle (f m x) (g x) (f n x)
      rw [dist_comm (f m x) (g x)] at htri
      linarith
    have hlim := (hl m).dist (hl n)
    have hbound : dist (l m) (l n) ≤ 2 * (ε / 3) := le_of_tendsto hlim hb
    linarith
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hc
  have hu' : TendstoUniformlyOnFilter f g atTop p :=
    hu.tendstoUniformlyOnFilter.mono_right (le_principal_iff.mpr hs)
  exact ⟨a, hu'.tendsto_of_eventually_tendsto (Eventually.of_forall hl) ha⟩

/-- Locally uniform limits of càdlàg paths remain càdlàg. -/
theorem IsCadlag.of_tendstoUniformlyOn {E : Type*} [MetricSpace E] [CompleteSpace E]
    {f : ℕ → Time → E} {g : Time → E} (hf : ∀ n, IsCadlag (f n))
    (hu : ∀ T : Time, TendstoUniformlyOn f g atTop (Iic T)) : IsCadlag g := by
  constructor
  · intro t
    have hs : Iic (t + 1) ∈ 𝓝[Ici t] t :=
      mem_inf_of_left (Iic_mem_nhds (by simp))
    obtain ⟨a, ha⟩ := exists_tendsto_of_tendstoUniformlyOn hs (hu (t + 1))
      (fun n => (hf n).1 t)
    have hb : Tendsto g (pure t) (𝓝 (g t)) := tendsto_pure_nhds g t
    have he : a = g t := tendsto_nhds_unique
      (ha.mono_left (pure_le_nhdsWithin (by simp))) hb
    change Tendsto g (𝓝[Ici t] t) (𝓝 (g t))
    rw [he] at ha
    exact ha
  · intro t ht
    have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
    have hs : Iic t ∈ 𝓝[<] t := mem_of_superset self_mem_nhdsWithin (fun _ h => show _ ≤ t from h.le)
    choose l hl using fun n => (hf n).2 t ht
    exact exists_tendsto_of_tendstoUniformlyOn hs (hu t) hl

end LatticeProb.Cadlag.HalfLine

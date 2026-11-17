import LongRange.Support.Prob.Cadlag.HalfLine.TimeChange
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.IntermediateValue

/-!
# Time changes from small displacements

A bounded Lipschitz displacement with a small Lipschitz constant induces an
onto half-line time change with controlled logarithmic distortion.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter
open scoped ENNReal NNReal Topology

/-- A bounded displacement with sufficiently small Lipschitz constant induces
a time change whose logarithmic distortion and displacement are controlled. -/
theorem exists_timeChange_of_lipschitz_displacement (b : Time → ℝ) (K B : ℝ≥0)
    {g : ℝ} (hg : 0 ≤ g) (hb : LipschitzWith K b) (hbzero : b 0 = 0)
    (hbound : ∀ t, |b t| ≤ B) (hK : (K : ℝ) < 1)
    (hKlo : (K : ℝ) ≤ 1 - Real.exp (-g))
    (hKhi : (K : ℝ) ≤ Real.exp g - 1) :
    ∃ l : Lambda, gamma l.1 ≤ ENNReal.ofReal g ∧
      (∀ t, (l.1 t : ℝ) = (t : ℝ) + b t) ∧
      ∀ t, dist t (l.1 t) ≤ B := by
  have hbnonneg (t : Time) : 0 ≤ (t : ℝ) + b t := by
    have hd := hb.dist_le_mul t 0
    have hd' : |b t| ≤ (K : ℝ) * (t : ℝ) := by
      simpa only [Real.dist_eq, hbzero, sub_zero, NNReal.dist_eq,
        NNReal.coe_zero, sub_zero, abs_of_nonneg (NNReal.coe_nonneg t)] using hd
    have hm : (K : ℝ) * (t : ℝ) ≤ (t : ℝ) := by
      nlinarith [NNReal.coe_nonneg t]
    have hl : -((K : ℝ) * (t : ℝ)) ≤ b t := (abs_le.mp hd').1
    linarith only [hm, hl]
  let L : Time → Time := fun t => ⟨t + b t, hbnonneg t⟩
  have hLzero : L 0 = 0 := by
    apply NNReal.eq
    change (0 : ℝ) + b 0 = 0
    rw [hbzero, add_zero]
  have hLc : Continuous L :=
    (continuous_subtype_val.add hb.continuous).subtype_mk _
  have hLmono : StrictMono L := by
    intro t s hts
    have hdist := hb.dist_le_mul t s
    have htsReal : (t : ℝ) < s := hts
    have hsmall : |b t - b s| ≤ (K : ℝ) * ((s : ℝ) - t) := by
      simpa only [Real.dist_eq, NNReal.dist_eq, abs_of_neg (sub_neg.mpr htsReal),
        neg_sub] using hdist
    change (t : ℝ) + b t < (s : ℝ) + b s
    have hmul := mul_lt_mul_of_pos_right hK (sub_pos.mpr htsReal)
    have hdiff := (abs_le.mp hsmall).2
    linarith
  have hLsurj : Function.Surjective L := by
    intro y
    have hy : y ≤ L (y + B) := by
      change (y : ℝ) ≤ ((y + B : Time) : ℝ) + b (y + B)
      have hh := (abs_le.mp (hbound (y + B))).1
      simp only [NNReal.coe_add]
      linarith
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc (show (0 : Time) ≤ y + B from zero_le)
      hLc.continuousOn (show y ∈ Icc (L 0) (L (y + B)) from ⟨by rw [hLzero]; exact zero_le, hy⟩)
    exact ⟨t, ht⟩
  let l : LambdaPrime := hLmono.orderIsoOfSurjective L hLsurj
  have hgamma : gamma l ≤ ENNReal.ofReal g := by
    apply gamma_le_of_secant l hg
    intro t s hts
    have htsReal : (t : ℝ) < s := hts
    have hdist := hb.dist_le_mul s t
    have hdiff : |b s - b t| ≤ (K : ℝ) * ((s : ℝ) - t) := by
      simpa only [Real.dist_eq, NNReal.dist_eq, abs_of_pos (sub_pos.mpr htsReal)]
        using hdist
    change Real.exp (-g) ≤ ((s + b s) - (t + b t)) / ((s : ℝ) - t) ∧
      ((s + b s) - (t + b t)) / ((s : ℝ) - t) ≤ Real.exp g
    have algebra (d a k lo hi : ℝ) (hd : 0 ≤ d) (hlo : k ≤ 1 - lo)
        (hhi : k ≤ hi - 1) (ha : |a| ≤ k * d) :
        lo * d ≤ d + a ∧ d + a ≤ hi * d := by
      have hl := mul_le_mul_of_nonneg_right hlo hd
      have hh := mul_le_mul_of_nonneg_right hhi hd
      have habs := abs_le.mp ha
      constructor <;> nlinarith only [hl, hh, habs.1, habs.2]
    have hbounds := algebra _ _ _ _ _ (sub_nonneg.mpr htsReal.le) hKlo hKhi hdiff
    have hnum : (s : ℝ) + b s - ((t : ℝ) + b t) =
        ((s : ℝ) - t) + (b s - b t) := by ring
    rw [hnum]
    exact ⟨(le_div_iff₀ (sub_pos.mpr htsReal)).mpr hbounds.1,
      (div_le_iff₀ (sub_pos.mpr htsReal)).mpr hbounds.2⟩
  let l' : Lambda := ⟨l, ⟨⟨_, lipschitzWith_of_gamma l
    (ne_of_lt (hgamma.trans_lt ENNReal.ofReal_lt_top))⟩,
    hgamma.trans_lt ENNReal.ofReal_lt_top⟩⟩
  refine ⟨l', hgamma, fun _ => rfl, fun t => ?_⟩
  change |(t : ℝ) - (t + b t)| ≤ B
  rw [sub_add_cancel_left, abs_neg]
  exact hbound t


/-- Small Lipschitz displacements on a set containing zero extend to a
controlled time change that interpolates those displacements. -/
theorem exists_timeChange_interpolating_displacement (S : Set Time) (b : Time → ℝ)
    (K B : ℝ≥0) {g : ℝ} (hg : 0 ≤ g) (hzero : (0 : Time) ∈ S)
    (hb : LipschitzOnWith K b S) (hbzero : b 0 = 0)
    (hbound : ∀ t ∈ S, |b t| ≤ B) (hK : (K : ℝ) < 1)
    (hKlo : (K : ℝ) ≤ 1 - Real.exp (-g))
    (hKhi : (K : ℝ) ≤ Real.exp g - 1) :
    ∃ l : Lambda, gamma l.1 ≤ ENNReal.ofReal g ∧
      (∀ t, dist t (l.1 t) ≤ B) ∧
      ∀ t ∈ S, (l.1 t : ℝ) = (t : ℝ) + b t := by
  obtain ⟨f, hf, hbf⟩ := hb.extend_real
  let c : Time → ℝ := fun t => max (min (f t) B) (-B)
  have hc : LipschitzWith K c := by
    simpa only [c] using (hf.min_const B).max_const (-B)
  have hc_eq (t : Time) (ht : t ∈ S) : c t = b t := by
    have hh := abs_le.mp (hbound t ht)
    simp only [c, ← hbf ht, min_eq_left hh.2, max_eq_left hh.1]
  have hczero : c 0 = 0 := (hc_eq 0 hzero).trans hbzero
  have hcbound (t : Time) : |c t| ≤ B := by
    apply abs_le.mpr
    constructor
    · exact le_max_right _ _
    · exact max_le (min_le_right _ _) (by exact neg_le_self (NNReal.coe_nonneg B))
  obtain ⟨l, hl, heq, hdist⟩ :=
    exists_timeChange_of_lipschitz_displacement c K B hg hc hczero hcbound hK hKlo hKhi
  exact ⟨l, hl, hdist, fun t ht => by rw [heq t, hc_eq t ht]⟩


/-- Displacements tending to zero on finitely many knots can eventually be
interpolated by time changes with prescribed small distortion. -/
theorem eventually_exists_timeChange_interpolating (F : Finset Time)
    (b : ℕ → Time → ℝ) (K B : ℝ≥0) {g : ℝ} (hg : 0 ≤ g)
    (hzero : (0 : Time) ∈ F) (hbzero : ∀ n, b n 0 = 0)
    (hlim : ∀ t ∈ F, Tendsto (fun n => b n t) atTop (𝓝 0))
    (hKpos : 0 < (K : ℝ)) (hBpos : 0 < (B : ℝ)) (hK : (K : ℝ) < 1)
    (hKlo : (K : ℝ) ≤ 1 - Real.exp (-g))
    (hKhi : (K : ℝ) ≤ Real.exp g - 1) :
    ∀ᶠ n in atTop, ∃ l : Lambda, gamma l.1 ≤ ENNReal.ofReal g ∧
      (∀ t, dist t (l.1 t) ≤ B) ∧
      ∀ t ∈ F, (l.1 t : ℝ) = (t : ℝ) + b n t := by
  have hpairs : ∀ᶠ n in atTop, ∀ c ∈ F, ∀ d ∈ F,
      dist (b n c) (b n d) ≤ K * dist c d := by
    apply (F.eventually_all).mpr
    intro c hc
    apply (F.eventually_all).mpr
    intro d hd
    by_cases hcd : c = d
    · subst d
      exact Eventually.of_forall (fun _ => by simp only [dist_self, mul_zero, le_refl])
    · have hpos : 0 < (K : ℝ) * dist c d := mul_pos hKpos (dist_pos.mpr hcd)
      have ht : Tendsto (fun n => dist (b n c) (b n d)) atTop (𝓝 0) := by
        simpa only [dist_self] using (hlim c hc).dist (hlim d hd)
      filter_upwards [ht.eventually (Iio_mem_nhds hpos)] with n hn
      exact hn.le
  have hvalues : ∀ᶠ n in atTop, ∀ c ∈ F, |b n c| ≤ B := by
    apply (F.eventually_all).mpr
    intro c hc
    have ht : Tendsto (fun n => |b n c|) atTop (𝓝 0) := by
      simpa only [abs_zero] using (hlim c hc).abs
    filter_upwards [ht.eventually (Iio_mem_nhds hBpos)] with n hn
    exact hn.le
  filter_upwards [hpairs, hvalues] with n hn hv
  have hlip : LipschitzOnWith K (b n) (↑F : Set Time) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro c hc d hd
    exact hn c hc d hd
  exact exists_timeChange_interpolating_displacement F (b n) K B hg hzero hlip
    (hbzero n) hv hK hKlo hKhi


/-- Finite knots with images converging to the knots admit asymptotically
undistorted interpolating time changes. -/
theorem eventually_exists_timeChange_interpolating_knots (F : Finset Time)
    (v : ℕ → Time → Time) (K B : ℝ≥0) {g : ℝ} (hg : 0 ≤ g)
    (hzero : (0 : Time) ∈ F) (hvzero : ∀ n, v n 0 = 0)
    (hlim : ∀ t ∈ F, Tendsto (fun n => v n t) atTop (𝓝 t))
    (hKpos : 0 < (K : ℝ)) (hBpos : 0 < (B : ℝ)) (hK : (K : ℝ) < 1)
    (hKlo : (K : ℝ) ≤ 1 - Real.exp (-g))
    (hKhi : (K : ℝ) ≤ Real.exp g - 1) :
    ∀ᶠ n in atTop, ∃ l : Lambda, gamma l.1 ≤ ENNReal.ofReal g ∧
      (∀ t, dist t (l.1 t) ≤ B) ∧ ∀ t ∈ F, l.1 t = v n t := by
  let b : ℕ → Time → ℝ := fun n t => (v n t : ℝ) - t
  have hbzero (n : ℕ) : b n 0 = 0 := by
    simp only [b, hvzero, NNReal.coe_zero, sub_self]
  have hb (t : Time) (ht : t ∈ F) : Tendsto (fun n => b n t) atTop (𝓝 0) := by
    have hv := (NNReal.continuous_coe.tendsto t).comp (hlim t ht)
    have hc : Tendsto (fun _ : ℕ => (t : ℝ)) atTop (𝓝 (t : ℝ)) := tendsto_const_nhds
    simpa only [b, Function.comp_apply, sub_self] using hv.sub hc
  filter_upwards [eventually_exists_timeChange_interpolating F b K B hg hzero hbzero hb
    hKpos hBpos hK hKlo hKhi] with n ⟨l, hl, hd, hi⟩
  refine ⟨l, hl, hd, fun t ht => ?_⟩
  apply NNReal.eq
  rw [hi t ht]
  dsimp only [b]
  ring


/-- An injective finite vector of knots can be aligned with convergent
vectors of knots, provided their initial points are zero. -/
theorem eventually_exists_timeChange_interpolating_indexed_knots (N : ℕ)
    (s : Fin (N + 1) → Time) (v : ℕ → Fin (N + 1) → Time)
    (K B : ℝ≥0) {g : ℝ} (hg : 0 ≤ g) (hs : Function.Injective s)
    (hszero : s 0 = 0) (hvzero : ∀ n, v n 0 = 0)
    (hlim : ∀ i, Tendsto (fun n => v n i) atTop (𝓝 (s i)))
    (hKpos : 0 < (K : ℝ)) (hBpos : 0 < (B : ℝ)) (hK : (K : ℝ) < 1)
    (hKlo : (K : ℝ) ≤ 1 - Real.exp (-g))
    (hKhi : (K : ℝ) ≤ Real.exp g - 1) :
    ∀ᶠ n in atTop, ∃ l : Lambda, gamma l.1 ≤ ENNReal.ofReal g ∧
      (∀ t, dist t (l.1 t) ≤ B) ∧ ∀ i, l.1 (s i) = v n i := by
  classical
  let F : Finset Time := Finset.univ.image s
  let w : ℕ → Time → Time := fun n t => v n (Function.invFun s t)
  have hinv (i : Fin (N + 1)) : Function.invFun s (s i) = i :=
    Function.leftInverse_invFun hs i
  have hzero : (0 : Time) ∈ F := by
    rw [← hszero]
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  have hwzero (n : ℕ) : w n 0 = 0 := by
    have hi0 : Function.invFun s 0 = 0 := by simpa only [hszero] using hinv 0
    simpa only [w, hi0] using hvzero n
  have hwlim : ∀ t ∈ F, Tendsto (fun n => w n t) atTop (𝓝 t) := by
    intro t ht
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
    simpa only [w, hinv] using hlim i
  filter_upwards [eventually_exists_timeChange_interpolating_knots F w K B hg hzero
    hwzero hwlim hKpos hBpos hK hKlo hKhi] with n ⟨l, hl, hd, hi⟩
  refine ⟨l, hl, hd, fun i => ?_⟩
  have hh := hi (s i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  simpa only [w, hinv] using hh


/-- Convergent finite knot vectors can be aligned by time changes with any
prescribed positive distortion and displacement bounds. -/
theorem eventually_exists_small_timeChange_interpolating_knots (N : ℕ)
    (s : Fin (N + 1) → Time) (v : ℕ → Fin (N + 1) → Time)
    (B : ℝ≥0) {g : ℝ} (hg : 0 < g) (hB : 0 < (B : ℝ))
    (hs : Function.Injective s) (hszero : s 0 = 0) (hvzero : ∀ n, v n 0 = 0)
    (hlim : ∀ i, Tendsto (fun n => v n i) atTop (𝓝 (s i))) :
    ∀ᶠ n in atTop, ∃ l : Lambda, gamma l.1 ≤ ENNReal.ofReal g ∧
      (∀ t, dist t (l.1 t) ≤ B) ∧ ∀ i, l.1 (s i) = v n i := by
  have hlo : 0 < 1 - Real.exp (-g) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hg))
  have hhi : 0 < Real.exp g - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hg)
  let K : ℝ≥0 := ⟨min (1 - Real.exp (-g)) (Real.exp g - 1) / 2,
    (half_pos (lt_min hlo hhi)).le⟩
  have hKpos : 0 < (K : ℝ) := half_pos (lt_min hlo hhi)
  have hKlo : (K : ℝ) ≤ 1 - Real.exp (-g) :=
    (half_le_self (lt_min hlo hhi).le).trans (min_le_left _ _)
  have hKhi : (K : ℝ) ≤ Real.exp g - 1 :=
    (half_le_self (lt_min hlo hhi).le).trans (min_le_right _ _)
  have hK : (K : ℝ) < 1 := by linarith [Real.exp_pos (-g)]
  exact eventually_exists_timeChange_interpolating_indexed_knots N s v K B hg.le hs
    hszero hvzero hlim hKpos hB hK hKlo hKhi

end LatticeProb.Cadlag.HalfLine

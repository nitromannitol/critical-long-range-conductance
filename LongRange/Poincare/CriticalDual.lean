import LongRange.Model.CriticalDual
import LongRange.Poincare.Inequality
import LongRange.TwoScale.DualPart

/-!
# Well-definedness and test characterization of the critical dual norm

Finite-lattice Cauchy--Schwarz and the proved Poincaré inequality bound the literal
signed supremum. Normalizing arbitrary supported tests gives the full dual estimate,
including zero-energy tests. No openness condition on the source domain is needed.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- Every source test has an absolutely summable critical energy series. -/
theorem CriticalDomain.summable_energy (D : CriticalDomain d)
    {h : Site d → ℝ} (hh : SupportedIn D.spacing D.domain h) :
    Summable (fun p : Site d × Site d => jumpKernel (physical D.spacing p.2) *
      (h (p.1 + p.2) - h p.1) ^ 2) :=
  summable_h1CritSq D.dimension_pos D.spacing_mem.1
    (hh.hasFiniteSupport D.spacing_mem.1 D.bounded)

/-- Supported tests make the source pairing absolutely summable for every datum. -/
theorem CriticalDomain.summable_pairing (D : CriticalDomain d) (g : Site d → ℝ)
    {h : Site d → ℝ} (hh : SupportedIn D.spacing D.domain h) :
    Summable (fun q => g q * h q) :=
  summable_of_hasFiniteSupport
    (Function.HasFiniteSupport.mul_right g (hh.hasFiniteSupport D.spacing_mem.1 D.bounded))

/-- Multiplication by a real scalar preserves support. -/
theorem SupportedIn.const_mul {ε : ℝ} {U : Set (Fin d → ℝ)}
    {h : Site d → ℝ} (hh : SupportedIn ε U h) (c : ℝ) :
    SupportedIn ε U (fun q => c * h q) := by
  intro q hq
  change c * h q = 0
  rw [hh q hq, mul_zero]

/-- The squared critical energy is homogeneous of degree two. -/
theorem h1CritSq_const_mul (ε c : ℝ) (h : Site d → ℝ) :
    h1CritSq ε (fun q => c * h q) = c ^ 2 * h1CritSq ε h := by
  unfold h1CritSq
  have he (p : Site d × Site d) :
      jumpKernel (physical ε p.2) * (c * h (p.1 + p.2) - c * h p.1) ^ 2 =
        c ^ 2 * (jumpKernel (physical ε p.2) * (h (p.1 + p.2) - h p.1) ^ 2) := by
    ring
  simp_rw [he]
  rw [tsum_mul_left]
  ring

/-- Homogeneity of the critical seminorm, including negative scalars. -/
theorem sqrt_h1CritSq_const_mul (ε c : ℝ) (h : Site d → ℝ) :
    Real.sqrt (h1CritSq ε (fun q => c * h q)) =
      |c| * Real.sqrt (h1CritSq ε h) := by
  rw [h1CritSq_const_mul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- The pairing is linear in scalar multiples of its test. -/
theorem criticalPairing_const_mul (ε c : ℝ) (g h : Site d → ℝ) :
    criticalPairing ε g (fun q => c * h q) = c * criticalPairing ε g h := by
  unfold criticalPairing
  simp_rw [show ∀ q, g q * (c * h q) = c * (g q * h q) from fun q => by ring]
  rw [tsum_mul_left]
  ring

/-- A supported global pairing is its domain-restricted pairing. -/
theorem criticalPairing_eq_subtype (ε : ℝ) (U : Set (Fin d → ℝ))
    (g : Site d → ℝ) {h : Site d → ℝ} (hh : SupportedIn ε U h) :
    criticalPairing ε g h = ε ^ d * ∑' q : latticeSet ε U, g q * h q := by
  unfold criticalPairing
  congr 1
  symm
  apply tsum_subtype_eq_of_support_subset (f := fun q : Site d => g q * h q)
  intro q hq
  by_contra hn
  exact hq (by change g q * h q = 0; rw [hh q hn, mul_zero])

/-- A supported squared norm can be summed over the entire lattice. -/
theorem l2NormSq_eq_global {ε : ℝ} {U : Set (Fin d → ℝ)}
    {h : Site d → ℝ} (hh : SupportedIn ε U h) :
    l2NormSq ε U h = ε ^ d * ∑' q, h q ^ 2 := by
  unfold l2NormSq
  congr 1
  apply tsum_subtype_eq_of_support_subset (f := fun q : Site d => h q ^ 2)
  intro q hq
  by_contra hn
  exact hq (by change h q ^ 2 = 0; rw [hh q hn]; norm_num)

/-- Poincaré on a bounded set follows by placing it in an open bounded ball. -/
theorem CriticalDomain.exists_poincare (D : CriticalDomain d) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : Site d → ℝ, SupportedIn D.spacing D.domain h →
      l2NormSq D.spacing D.domain h ≤ C * h1CritSq D.spacing h := by
  obtain ⟨r, hr⟩ := D.bounded.subset_ball (0 : Fin d → ℝ)
  let V := Metric.ball (0 : Fin d → ℝ) r
  obtain ⟨C, hC, hp⟩ := poincare d D.dimension_pos (euclideanDiam V)
  refine ⟨C, hC, ?_⟩
  intro h hh
  have hv : SupportedIn D.spacing V h := by
    intro q hq
    apply hh q
    exact fun hmem => hq (hr hmem)
  rw [l2NormSq_eq_global hh, ← l2NormSq_eq_global hv]
  exact hp V Metric.isOpen_ball Metric.isBounded_ball le_rfl D.spacing D.spacing_mem h hv

/-- Finite-lattice Cauchy--Schwarz with exactly the physical-volume normalization. -/
theorem criticalPairing_le_l2Norm (D : CriticalDomain d) (g : Site d → ℝ)
    {h : Site d → ℝ} (hh : SupportedIn D.spacing D.domain h) :
    criticalPairing D.spacing g h ≤
      l2Norm D.spacing D.domain g * l2Norm D.spacing D.domain h := by
  classical
  letI := (latticeSet_finite D.spacing_mem.1 D.bounded).fintype
  rw [criticalPairing_eq_subtype D.spacing D.domain g hh]
  simp only [l2Norm, l2NormSq, tsum_fintype]
  rw [Real.sqrt_mul (pow_nonneg D.spacing_mem.1.le _),
    Real.sqrt_mul (pow_nonneg D.spacing_mem.1.le _)]
  have he := Real.sq_sqrt (pow_nonneg D.spacing_mem.1.le d)
  calc
    _ ≤ D.spacing ^ d * (Real.sqrt (∑ q : latticeSet D.spacing D.domain, g q ^ 2) *
        Real.sqrt (∑ q : latticeSet D.spacing D.domain, h q ^ 2)) :=
      mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _)
        (pow_nonneg D.spacing_mem.1.le _)
    _ = _ := by
      conv_lhs => rw [← he]
      ring

/-- Poincaré supplies an actual finite bound for every supported-test pairing. -/
theorem CriticalDomain.exists_pairing_bound (D : CriticalDomain d) (g : Site d → ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ h : Site d → ℝ, SupportedIn D.spacing D.domain h →
      criticalPairing D.spacing g h ≤ A * Real.sqrt (h1CritSq D.spacing h) := by
  obtain ⟨C, hC, hp⟩ := D.exists_poincare
  refine ⟨l2Norm D.spacing D.domain g * Real.sqrt C, by
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  intro h hh
  have hn : l2Norm D.spacing D.domain h ≤
      Real.sqrt C * Real.sqrt (h1CritSq D.spacing h) := by
    exact (Real.sqrt_le_sqrt (hp h hh)).trans_eq (Real.sqrt_mul hC.le _)
  exact (criticalPairing_le_l2Norm D g hh).trans (by
    simpa only [mul_assoc, l2Norm] using
      mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg (l2NormSq _ _ _)))

/-- The zero test belongs to the actual critical unit ball. -/
theorem zero_mem_criticalDualValues (D : CriticalDomain d) (g : D.Field) :
    0 ∈ criticalDualValues D g := by
  refine ⟨fun _ => 0, fun _ _ => rfl, ?_, ?_⟩ <;>
    simp [h1CritSq, criticalPairing]

/-- The literal signed pairing set is nonempty. -/
theorem criticalDualValues_nonempty (D : CriticalDomain d) (g : D.Field) :
    (criticalDualValues D g).Nonempty :=
  ⟨0, zero_mem_criticalDualValues D g⟩

/-- The literal signed pairing set is bounded above, by the proved Poincaré inequality. -/
theorem criticalDualValues_bddAbove (D : CriticalDomain d) (g : D.Field) :
    BddAbove (criticalDualValues D g) := by
  obtain ⟨A, hA, hb⟩ := D.exists_pairing_bound g
  refine ⟨A, ?_⟩
  rintro r ⟨h, hh, hunit, rfl⟩
  exact (hb h hh).trans ((mul_le_mul_of_nonneg_left hunit hA).trans_eq (mul_one A))

/-- The signed supremum is a nonnegative real number. -/
theorem criticalDualNorm_nonneg (D : CriticalDomain d) (g : D.Field) :
    0 ≤ criticalDualNorm D g :=
  le_csSup (criticalDualValues_bddAbove D g) (zero_mem_criticalDualValues D g)

/-- Exact least-upper-bound characterization on supported unit tests. -/
theorem criticalDualNorm_le_iff_unit (D : CriticalDomain d) (g : D.Field) (B : ℝ) :
    criticalDualNorm D g ≤ B ↔ ∀ h : Site d → ℝ,
      SupportedIn D.spacing D.domain h → Real.sqrt (h1CritSq D.spacing h) ≤ 1 →
        criticalPairing D.spacing g h ≤ B := by
  constructor
  · intro hb h hh hu
    exact (le_csSup (criticalDualValues_bddAbove D g) ⟨h, hh, hu, rfl⟩).trans hb
  · intro hb
    apply csSup_le (criticalDualValues_nonempty D g)
    rintro r ⟨h, hh, hu, rfl⟩
    exact hb h hh hu

/-- Normalizing a positive-energy test gives the signed estimate for every test.
Zero-energy tests are controlled by the independently proved finite pairing bound. -/
theorem criticalPairing_le_criticalDualNorm (D : CriticalDomain d) (g : D.Field)
    {h : Site d → ℝ} (hh : SupportedIn D.spacing D.domain h) :
    criticalPairing D.spacing g h ≤
      criticalDualNorm D g * Real.sqrt (h1CritSq D.spacing h) := by
  let t := Real.sqrt (h1CritSq D.spacing h)
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  by_cases hz : t = 0
  · obtain ⟨A, _, hb⟩ := D.exists_pairing_bound g
    have hb' := hb h hh
    change criticalPairing D.spacing g h ≤ criticalDualNorm D g * t
    change criticalPairing D.spacing g h ≤ A * t at hb'
    simpa only [hz, mul_zero] using hb'
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
    have hu : Real.sqrt (h1CritSq D.spacing (fun q => t⁻¹ * h q)) ≤ 1 := by
      rw [sqrt_h1CritSq_const_mul, abs_of_nonneg (inv_nonneg.mpr ht)]
      change t⁻¹ * t ≤ 1
      rw [inv_mul_cancel₀ hz]
    have hb := (criticalDualNorm_le_iff_unit D g (criticalDualNorm D g)).mp le_rfl
      (fun q => t⁻¹ * h q) (hh.const_mul t⁻¹) hu
    rw [criticalPairing_const_mul] at hb
    have hm := mul_le_mul_of_nonneg_left hb ht
    rw [mul_comm t (criticalDualNorm D g)] at hm
    change criticalPairing D.spacing g h ≤ criticalDualNorm D g * t
    simpa only [← mul_assoc, mul_inv_cancel₀ hz, one_mul] using hm

/-- Full absolute pairing estimate from the literal signed supremum. -/
theorem abs_criticalPairing_le (D : CriticalDomain d) (g : D.Field)
    {h : Site d → ℝ} (hh : SupportedIn D.spacing D.domain h) :
    |criticalPairing D.spacing g h| ≤
      criticalDualNorm D g * Real.sqrt (h1CritSq D.spacing h) := by
  apply abs_le.mpr
  constructor
  · have hn := criticalPairing_le_criticalDualNorm D g (hh.const_mul (-1))
    rw [criticalPairing_const_mul, sqrt_h1CritSq_const_mul] at hn
    norm_num only [abs_neg, abs_one, one_mul, neg_one_mul] at hn
    linarith only [hn]
  · exact criticalPairing_le_criticalDualNorm D g hh

/-- The complete characterization by all supported tests, with the necessary sign
condition explicit even when the lattice domain is empty. -/
theorem criticalDualNorm_le_iff (D : CriticalDomain d) (g : D.Field) (B : ℝ) :
    criticalDualNorm D g ≤ B ↔ 0 ≤ B ∧ ∀ h : Site d → ℝ,
      SupportedIn D.spacing D.domain h →
        |criticalPairing D.spacing g h| ≤ B * Real.sqrt (h1CritSq D.spacing h) := by
  constructor
  · intro hb
    refine ⟨(criticalDualNorm_nonneg D g).trans hb, ?_⟩
    intro h hh
    exact (abs_criticalPairing_le D g hh).trans
      (mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg _))
  · rintro ⟨hB, hb⟩
    apply (criticalDualNorm_le_iff_unit D g B).mpr
    intro h hh hu
    exact (le_abs_self _).trans ((hb h hh).trans
      ((mul_le_mul_of_nonneg_left hu hB).trans_eq (mul_one B)))

/-- A field nonzero at a lattice site has strictly positive literal dual norm. -/
theorem criticalDualNorm_pos (D : CriticalDomain d) (g : D.Field)
    (q : Site d) (hq : g.val q ≠ 0) : 0 < criticalDualNorm D g := by
  have hf := g.property.hasFiniteSupport D.spacing_mem.1 D.bounded
  have hs : Summable (fun x => g.val x * g.val x) :=
    summable_of_hasFiniteSupport (Function.HasFiniteSupport.mul_right g.val hf)
  have hsum : 0 < ∑' x, g.val x * g.val x :=
    hs.tsum_pos (fun x => mul_self_nonneg (g.val x)) q (by
      simpa only [pow_two] using sq_pos_of_ne_zero hq)
  have hp : 0 < criticalPairing D.spacing g.val g.val := by
    change 0 < D.spacing ^ d * ∑' x, g.val x * g.val x
    exact mul_pos (pow_pos D.spacing_mem.1 d) hsum
  apply lt_of_not_ge
  intro hn
  have hb := abs_criticalPairing_le D g g.property
  have hm := mul_nonpos_of_nonpos_of_nonneg hn
    (Real.sqrt_nonneg (h1CritSq D.spacing g.val))
  exact (not_le_of_gt hp) ((le_abs_self _).trans (hb.trans hm))

/-- Absolute-value and literal signed suprema agree; symmetry has been proved rather
than built into the definition. -/
theorem criticalDualNorm_eq_sSup_abs (D : CriticalDomain d) (g : D.Field) :
    criticalDualNorm D g = sSup {r : ℝ | ∃ h : Site d → ℝ,
      SupportedIn D.spacing D.domain h ∧ Real.sqrt (h1CritSq D.spacing h) ≤ 1 ∧
        r = |criticalPairing D.spacing g h|} := by
  let S := {r : ℝ | ∃ h : Site d → ℝ,
    SupportedIn D.spacing D.domain h ∧ Real.sqrt (h1CritSq D.spacing h) ≤ 1 ∧
      r = |criticalPairing D.spacing g h|}
  have hb : ∀ r ∈ S, r ≤ criticalDualNorm D g := by
    rintro r ⟨h, hh, hu, rfl⟩
    exact (abs_criticalPairing_le D g hh).trans
      ((mul_le_mul_of_nonneg_left hu (criticalDualNorm_nonneg D g)).trans_eq (mul_one _))
  have hn : S.Nonempty := by
    refine ⟨0, fun _ => 0, fun _ _ => rfl, ?_, ?_⟩ <;>
      simp [h1CritSq, criticalPairing]
  apply le_antisymm
  · apply (criticalDualNorm_le_iff_unit D g _).mpr
    intro h hh hu
    exact (le_abs_self _).trans (le_csSup ⟨criticalDualNorm D g, hb⟩ ⟨h, hh, hu, rfl⟩)
  · exact csSup_le hn hb

/-- Restriction changes no pairing against a supported test. -/
theorem criticalPairing_restrict (D : CriticalDomain d) (g : Site d → ℝ)
    {h : Site d → ℝ} (hh : SupportedIn D.spacing D.domain h) :
    criticalPairing D.spacing (D.restrict g) h = criticalPairing D.spacing g h := by
  unfold criticalPairing
  congr 1
  apply tsum_congr
  intro q
  by_cases hq : q ∈ latticeSet D.spacing D.domain
  · simp only [CriticalDomain.restrict, hq, ↓reduceIte]
  · simp only [CriticalDomain.restrict, hq, ↓reduceIte, hh q hq, mul_zero]

/-- Direct supported-test estimates, as produced by `dualPart_bound`, imply the
literal source norm bound for the residual restricted to the domain. -/
theorem criticalDualNorm_restrict_le (D : CriticalDomain d) (g : Site d → ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ h : Site d → ℝ, SupportedIn D.spacing D.domain h →
      |D.spacing ^ d * ∑' q, g q * h q| ≤ B * Real.sqrt (h1CritSq D.spacing h)) :
    criticalDualNorm D (D.restrict g) ≤ B := by
  apply (criticalDualNorm_le_iff D (D.restrict g) B).mpr
  refine ⟨hB, ?_⟩
  intro h hh
  rw [criticalPairing_restrict D g hh]
  exact hb h hh

/-- The proved two-scale direct test estimate bounds the literal critical norm of the
supported residual, with exactly the same constant and scale dependence. -/
theorem dualPart_criticalDualNorm_bound (hd : 1 ≤ d) (lam R B : ℝ) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ D : CriticalDomain d,
      IsOpen D.domain → D.domain.Nonempty → euclideanDiam D.domain ≤ R →
      ∀ a : Edge d → ℝ, (∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) →
      ∀ v : (Fin d → ℝ) → ℝ, ContDiff ℝ 2 v →
      (∀ x, ‖fderiv ℝ v x‖ ≤ B) → (∀ x, ‖iteratedFDeriv ℝ 2 v x‖ ≤ B) →
      (∀ x, R < radius x → v x = 0) → (∀ x ∈ frontier D.domain, v x = 0) →
      ∀ (φ : Fin d → Site d → ℝ) (K : ℝ),
      (∀ i, SupportedIn D.spacing D.domain (φ i)) →
      (∀ i, h1CritSq D.spacing (φ i) + l2NormSq D.spacing D.domain (φ i) ≤ K) →
      criticalDualNorm D (D.restrict (fun q =>
        boundaryDefect D.spacing a (exteriorDefect D.spacing D.domain v) q +
          correctorError D.spacing a v φ q)) ≤
        C * (1 / Real.sqrt (kappa d D.spacing) + Real.sqrt K) := by
  obtain ⟨C, hC, hb⟩ := dualPart_bound hd lam R B hlam
  refine ⟨C, hC, ?_⟩
  intro D hUo hne hdiam a ha v hv hDv hD₂v hR h0 φ K hφ hK
  apply criticalDualNorm_restrict_le D _ (by positivity)
  exact hb D.domain hUo D.bounded hne hdiam D.spacing D.spacing_mem a ha
    v hv hDv hD₂v hR h0 φ K hφ hK

end

end LongRange

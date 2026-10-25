import LongRange.Calculus.BilinForm
import LongRange.Corrector.Support

/-!
# Closing the deterministic energy estimate

Testing the residual equation gives the critical energy bound, followed by Poincaré.
The closing theorem explicitly requires a nonnegative dual bound; without this sign,
empty lattice domains give counterexamples. The installed discrete calculus supplies
Green's identity and ellipticity for the Euclidean jump kernel.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- A global pairing with a supported function is its domain-restricted pairing. -/
private theorem pairing_eq_subtype (ε : ℝ) (U : Set (Fin d → ℝ))
    (f : Site d → ℝ) {h : Site d → ℝ} (hh : SupportedIn ε U h) :
    (∑' q : Site d, f q * h q) = ∑' q : latticeSet ε U, f q * h q := by
  symm
  apply tsum_subtype_eq_of_support_subset
    (f := fun q : Site d => f q * h q) (s := latticeSet ε U)
  intro q hq
  by_contra hn
  apply hq
  change f q * h q = 0
  rw [hh q hn, mul_zero]

/-- Weighted discrete Cauchy--Schwarz on a bounded domain, with the physical volume factor. -/
private theorem pairing_le_l2Norm {ε : ℝ} (hε : 0 < ε) {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) (f : Site d → ℝ) {h : Site d → ℝ}
    (hh : SupportedIn ε U h) :
    ε ^ d * ∑' q : Site d, f q * h q ≤ l2Norm ε U f * l2Norm ε U h := by
  classical
  letI := (latticeSet_finite hε hU).fintype
  rw [pairing_eq_subtype ε U f hh]
  simp only [l2Norm, l2NormSq, tsum_fintype]
  rw [Real.sqrt_mul (pow_nonneg hε.le _), Real.sqrt_mul (pow_nonneg hε.le _)]
  have he := Real.sq_sqrt (pow_nonneg hε.le d)
  calc
    _ ≤ ε ^ d * (Real.sqrt (∑ q : latticeSet ε U, f q ^ 2) *
        Real.sqrt (∑ q : latticeSet ε U, h q ^ 2)) :=
      mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _)
        (pow_nonneg hε.le _)
    _ = _ := by
      conv_lhs => rw [← he]
      ring

/-- Poincaré in squared form implies the corresponding norm inequality. -/
private theorem l2Norm_le_of_poincare {ε Cp : ℝ} {U : Set (Fin d → ℝ)}
    (hCp : 0 ≤ Cp) {h : Site d → ℝ}
    (hp : l2NormSq ε U h ≤ Cp * h1CritSq ε h) :
    l2Norm ε U h ≤ Real.sqrt Cp * Real.sqrt (h1CritSq ε h) := by
  exact (Real.sqrt_le_sqrt hp).trans_eq (Real.sqrt_mul hCp _)

/-- Nonnegativity of the squared critical seminorm at nonnegative scales. -/
private theorem h1CritSq_nonneg {ε : ℝ} (hε : 0 ≤ ε) (h : Site d → ℝ) :
    0 ≤ h1CritSq ε h := by
  unfold h1CritSq
  exact mul_nonneg (div_nonneg (pow_nonneg hε _) (kappa_nonneg hε))
    (tsum_nonneg (fun _ => mul_nonneg (jumpKernel_nonneg _) (sq_nonneg _)))

/-- Testing the residual equation against its finitely supported solution gives the energy
bound. The nonnegative mass term is discarded only after the exact Green identity. -/
theorem energy_le_pairings (hd : 1 ≤ d) {ε lam μ : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) (hμ : 0 ≤ μ)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {h F G : Site d → ℝ} (hh : SupportedIn ε U h)
    (heq : ∀ q ∈ latticeSet ε U, μ * h q - generator ε a h q = F q + G q) :
    lam / 2 * h1CritSq ε h ≤
      ε ^ d * ∑' q, F q * h q + ε ^ d * ∑' q, G q * h q := by
  have hfin := SupportedIn.hasFiniteSupport hε hU hh
  have hs (f : Site d → ℝ) : Summable (fun q => f q * h q) :=
    summable_of_hasFiniteSupport (Function.HasFiniteSupport.mul_right f hfin)
  have hid : (∑' q, F q * h q) + (∑' q, G q * h q) =
      μ * (∑' q, h q ^ 2) - ∑' q, h q * generator ε a h q := by
    rw [← (hs F).tsum_add (hs G)]
    have hp : (fun q => F q * h q + G q * h q) =
        (fun q => μ * (h q * h q) - generator ε a h q * h q) := by
      funext q
      by_cases hq : q ∈ latticeSet ε U
      · have htest := congrArg (fun r : ℝ => r * h q) (heq q hq)
        nlinarith only [htest]
      · rw [hh q hq]
        ring
    rw [hp, ((hs h).mul_left μ).tsum_sub (hs (generator ε a h)), tsum_mul_left]
    simp only [pow_two]
    congr 1
    apply tsum_congr
    intro q
    ring
  have hgreen := bilinForm_eq_neg_generator_bounded hd hε hlam ha
    (exists_bound_of_finite_support hfin) hfin
  have hmass : 0 ≤ μ * (ε ^ d * ∑' q, h q ^ 2) :=
    mul_nonneg hμ (mul_nonneg (pow_nonneg hε.le _)
      (tsum_nonneg (fun _ => sq_nonneg _)))
  have hell := (bilinForm_self_bounds hd hε hlam ha hfin).1
  have hid_scaled := congrArg (fun r : ℝ => ε ^ d * r) hid
  rw [mul_add, mul_sub] at hid_scaled
  have hm : ε ^ d * (μ * ∑' q, h q ^ 2) = μ * (ε ^ d * ∑' q, h q ^ 2) := by
    ring
  rw [hm] at hid_scaled
  linarith only [hid_scaled, hgreen, hmass, hell]

/-- Closing the deterministic residual estimate from a Poincaré constant and a nonnegative
dual bound. The sign of `B` is needed even when the lattice domain is empty. -/
theorem energy_estimate_of_poincare_of_nonneg (hd : 1 ≤ d) {ε lam μ A B Cp : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hlam : 0 < lam) (hμ : 0 ≤ μ)
    (hB : 0 ≤ B) (hCp : 0 ≤ Cp)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {h F G : Site d → ℝ} (hh : SupportedIn ε U h)
    (heq : ∀ q ∈ latticeSet ε U, μ * h q - generator ε a h q = F q + G q)
    (hF : l2Norm ε U F ≤ A)
    (hG : ∀ ψ, SupportedIn ε U ψ →
      |ε ^ d * ∑' q, G q * ψ q| ≤ B * Real.sqrt (h1CritSq ε ψ))
    (hp : ∀ ψ, SupportedIn ε U ψ → l2NormSq ε U ψ ≤ Cp * h1CritSq ε ψ) :
    Real.sqrt (h1CritSq ε h) ≤ (2 / lam) * (A * Real.sqrt Cp + B) ∧
      l2Norm ε U h ≤ Real.sqrt Cp * (2 / lam) * (A * Real.sqrt Cp + B) := by
  have hA : 0 ≤ A := (Real.sqrt_nonneg _).trans hF
  have hpoin := l2Norm_le_of_poincare hCp (hp h hh)
  have htest := energy_le_pairings hd hε.1 hlam hμ hU ha hh heq
  have hpair := pairing_le_l2Norm hε.1 hU F hh
  have hdual := (le_abs_self _).trans (hG h hh)
  have hnorm : 0 ≤ l2Norm ε U h := Real.sqrt_nonneg _
  have hbound : lam / 2 * h1CritSq ε h ≤
      (A * Real.sqrt Cp + B) * Real.sqrt (h1CritSq ε h) := by
    calc
      _ ≤ l2Norm ε U F * l2Norm ε U h +
          B * Real.sqrt (h1CritSq ε h) := htest.trans (add_le_add hpair hdual)
      _ ≤ A * l2Norm ε U h + B * Real.sqrt (h1CritSq ε h) :=
        add_le_add (mul_le_mul_of_nonneg_right hF hnorm) le_rfl
      _ ≤ A * (Real.sqrt Cp * Real.sqrt (h1CritSq ε h)) +
          B * Real.sqrt (h1CritSq ε h) :=
        add_le_add (mul_le_mul_of_nonneg_left hpoin hA) le_rfl
      _ = _ := by ring
  have hs := Real.sq_sqrt (h1CritSq_nonneg hε.1.le h)
  have hsnonneg := Real.sqrt_nonneg (h1CritSq ε h)
  have hK : 0 ≤ A * Real.sqrt Cp + B :=
    add_nonneg (mul_nonneg hA (Real.sqrt_nonneg _)) hB
  have hclose : Real.sqrt (h1CritSq ε h) ≤ (2 / lam) * (A * Real.sqrt Cp + B) := by
    have hc : lam * Real.sqrt (h1CritSq ε h) ≤ 2 * (A * Real.sqrt Cp + B) := by
      by_cases hz : Real.sqrt (h1CritSq ε h) = 0
      · rw [hz, mul_zero]
        positivity
      · have hpos := lt_of_le_of_ne hsnonneg (Ne.symm hz)
        have hm : (lam * Real.sqrt (h1CritSq ε h)) * Real.sqrt (h1CritSq ε h) ≤
            (2 * (A * Real.sqrt Cp + B)) * Real.sqrt (h1CritSq ε h) := by
          calc
            _ = 2 * (lam / 2 * h1CritSq ε h) := by
              conv_rhs => rw [← hs]
              ring
            _ ≤ 2 * ((A * Real.sqrt Cp + B) * Real.sqrt (h1CritSq ε h)) :=
              mul_le_mul_of_nonneg_left hbound (by norm_num)
            _ = _ := by ring
        exact (mul_le_mul_iff_left₀ hpos).mp hm
    calc
      _ ≤ (2 * (A * Real.sqrt Cp + B)) / lam :=
        (le_div_iff₀ hlam).mpr (by simpa only [mul_comm] using hc)
      _ = _ := by ring
  exact ⟨hclose, hpoin.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hclose
      (Real.sqrt_nonneg Cp))⟩

end

end LongRange

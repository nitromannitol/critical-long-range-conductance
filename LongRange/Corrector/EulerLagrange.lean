import LongRange.Corrector.Quadratic

/-!
# First variations of the corrector functional

The convergent quadratic expansion identifies minimality with vanishing first variations.
Green's identity then identifies these variations with the pointwise Dirichlet equation.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- Admissibility is preserved under addition. -/
theorem SupportedIn.add {ε : ℝ} {U : Set (Fin d → ℝ)} {u v : Site d → ℝ}
    (hu : SupportedIn ε U u) (hv : SupportedIn ε U v) : SupportedIn ε U (u + v) := by
  intro q hq
  change u q + v q = 0
  rw [hu q hq, hv q hq, add_zero]

/-- Admissibility is preserved under real scalar multiplication. -/
theorem SupportedIn.smul {ε : ℝ} {U : Set (Fin d → ℝ)} {u : Site d → ℝ}
    (hu : SupportedIn ε U u) (t : ℝ) : SupportedIn ε U (t • u) := by
  intro q hq
  change t * u q = 0
  rw [hu q hq, mul_zero]

/-- The exact second-order expansion along an admissible variation. -/
theorem correctorFunctional_variation (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : 0 < ε) {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p : Fin d → ℝ)
    {φ η : Site d → ℝ} (hφ : SupportedIn ε U φ) (hη : SupportedIn ε U η) (t : ℝ) :
    correctorFunctional ε U a p (φ + t • η) = correctorFunctional ε U a p φ +
      2 * t * bilinForm ε a (fun q => linearFn ε p q + φ q) η +
        t ^ 2 * bilinForm ε a η η := by
  have hf := hφ.hasFiniteSupport hε hU
  have hg := hη.hasFiniteSupport hε hU
  have ht := (hη.smul t).hasFiniteSupport hε hU
  rw [correctorFunctional_eq_quadratic hd hε hU hlam ha p (hφ.add (hη.smul t)),
    correctorFunctional_eq_quadratic hd hε hU hlam ha p hφ,
    bilinForm_add_left hd hε hlam ha hf ht (hf.add ht),
    bilinForm_add_right hd hε hlam ha hf hf ht,
    bilinForm_add_right hd hε hlam ha ht hf ht,
    bilinForm_linear_add_right hd hε hlam ha p hf ht,
    bilinForm_smul_left, bilinForm_smul_right, bilinForm_smul_right,
    bilinForm_smul_right, bilinForm_comm ε a η φ,
    bilinForm_affine_add hd hε hlam ha p hf hg]
  rw [bilinForm_smul_left]
  ring

/-- Minimality is equivalent to vanishing first variations against all admissible tests. -/
theorem correctorMinimizer_iff_variations (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : 0 < ε) {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p : Fin d → ℝ)
    {φ : Site d → ℝ} (hφ : SupportedIn ε U φ) :
    (∀ w, SupportedIn ε U w →
      correctorFunctional ε U a p φ ≤ correctorFunctional ε U a p w) ↔
    ∀ η, SupportedIn ε U η →
      bilinForm ε a (fun q => linearFn ε p q + φ q) η = 0 := by
  constructor
  · intro hmin η hη
    have hquad : ∀ t : ℝ, 0 ≤ bilinForm ε a η η * (t * t) +
        (2 * bilinForm ε a (fun q => linearFn ε p q + φ q) η) * t + 0 := by
      intro t
      have ht := hmin (φ + t • η) (hφ.add (hη.smul t))
      rw [correctorFunctional_variation hd hε hU hlam ha p hφ hη] at ht
      nlinarith only [ht]
    have hdisc := discrim_le_zero hquad
    unfold discrim at hdisc
    nlinarith only [hdisc, sq_nonneg
      (bilinForm ε a (fun q => linearFn ε p q + φ q) η)]
  · intro hv w hw
    let η := w - φ
    have hη : SupportedIn ε U η := by
      intro q hq
      change w q - φ q = 0
      rw [hw q hq, hφ q hq, sub_self]
    have heq : φ + (1 : ℝ) • η = w := by
      ext q
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, η, Pi.sub_apply]
      ring
    have hexp := correctorFunctional_variation hd hε hU hlam ha p hφ hη 1
    rw [heq, hv η hη] at hexp
    have hn := bilinForm_self_nonneg hε.le (fun e => hlam.le.trans (ha e).1) η
    linarith only [hexp, hn]

/-- The first variations vanish exactly when the affine perturbation is harmonic in the
physical lattice domain. -/
theorem isCorrectorMinimizer_iff {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    {lam : ℝ} (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p : Fin d → ℝ)
    {φ : Site d → ℝ} (hφ : SupportedIn ε U φ) :
    (∀ w, SupportedIn ε U w →
      correctorFunctional ε U a p φ ≤ correctorFunctional ε U a p w) ↔
    ∀ q ∈ latticeSet ε U, generator ε a (fun x => linearFn ε p x + φ x) q = 0 := by
  classical
  rw [correctorMinimizer_iff_variations hd hε.1 hU hlam ha p hφ]
  have hb := exists_bound_of_finite_support (hφ.hasFiniteSupport hε.1 hU)
  constructor
  · intro hv q hq
    let η : Site d → ℝ := fun x => if x = q then 1 else 0
    have hη : SupportedIn ε U η := by
      intro x hx
      have hne : x ≠ q := fun heq => hx (heq.symm ▸ hq)
      exact if_neg hne
    have heq := hv η hη
    rw [bilinForm_eq_neg_generator_affine hd hε.1 hlam ha p hb
      (hη.hasFiniteSupport hε.1 hU)] at heq
    have hsum : (∑' x : Site d, η x *
        generator ε a (fun x => linearFn ε p x + φ x) x) =
        generator ε a (fun x => linearFn ε p x + φ x) q := by
      simp only [η, ite_mul, one_mul, zero_mul, tsum_ite_eq]
    rw [hsum] at heq
    exact (mul_eq_zero.mp (neg_eq_zero.mp heq)).resolve_left (pow_ne_zero _ hε.1.ne')
  · intro hg η hη
    rw [bilinForm_eq_neg_generator_affine hd hε.1 hlam ha p hb
      (hη.hasFiniteSupport hε.1 hU)]
    have hz : ∀ q, η q * generator ε a (fun x => linearFn ε p x + φ x) q = 0 := by
      intro q
      by_cases hq : q ∈ latticeSet ε U
      · rw [hg q hq, mul_zero]
      · rw [hη q hq, zero_mul]
    simp only [hz, tsum_zero, mul_zero, neg_zero]

end

end LongRange

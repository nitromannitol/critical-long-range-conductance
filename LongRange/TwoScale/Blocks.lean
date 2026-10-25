import LongRange.Appendix.Kappa

/-!
# Logarithmic blocks and centred enlarged cubes

The block index uses arbitrary real translates of the paper's open coordinate cube.
For bounded nonempty open domains the infimum side is positive and is attained:
coordinate projections are open, so their extremal endpoints are omitted. The enlarged
cube is centred at the origin in the original coordinates; its enlargement depends on
both the size and the location of the domain. Coordinate bounds here describe cubes;
the normalization `kappa` retains the Euclidean lattice norm.
-/

namespace LongRange.TwoScale

noncomputable section

variable {d : ℕ}

/-- The open coordinate cube of side `s`, centred at `a`. -/
def openCube (a : Fin d → ℝ) (s : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, |x i - a i| < s / 2}

/-- Some real translate of the open cube of side `s` contains the domain. -/
def cubeFits (U : Set (Fin d → ℝ)) (s : ℝ) : Prop :=
  ∃ a, U ⊆ openCube a s

/-- The infimum of positive side lengths of open cubes containing a translate of `U`. -/
def cubeSide (U : Set (Fin d → ℝ)) : ℝ :=
  sInf {s : ℝ | 0 < s ∧ cubeFits U s}

/-- Coordinate projections of a bounded domain have finite upper and lower bounds. -/
lemma coordinate_bounded {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    (i : Fin d) : BddBelow ((fun x => x i) '' U) ∧ BddAbove ((fun x => x i) '' U) := by
  obtain ⟨R, hR⟩ := hU.exists_norm_le
  constructor
  · refine ⟨-R, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have h := (norm_le_pi_norm x i).trans (hR x hx)
    rw [Real.norm_eq_abs] at h
    exact (abs_le.mp h).1
  · refine ⟨R, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have h := (norm_le_pi_norm x i).trans (hR x hx)
    rw [Real.norm_eq_abs] at h
    exact (abs_le.mp h).2

/-- Points in a bounded open subset of the line lie strictly between its extrema. -/
lemma strict_coordinate_extrema {S : Set ℝ} (hS : IsOpen S)
    (hb : BddBelow S) (ha : BddAbove S) {x : ℝ} (hx : x ∈ S) :
    sInf S < x ∧ x < sSup S := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hS x hx
  have hminus : x - r / 2 ∈ S := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have : x - r / 2 - x = -(r / 2) := by ring
    rw [this, abs_neg, abs_of_pos (by positivity : 0 < r / 2)]
    linarith
  have hplus : x + r / 2 ∈ S := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have : x + r / 2 - x = r / 2 := by ring
    rw [this, abs_of_pos (by positivity : 0 < r / 2)]
    linarith
  constructor
  · exact (csInf_le hb hminus).trans_lt (by linarith)
  · exact (show x < x + r / 2 by linarith).trans_le (le_csSup ha hplus)

/-- A nonempty open domain has a positive minimal side, attained by an open cube. -/
theorem cubeSide_pos_and_fits (hd : 1 ≤ d) {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) (ho : IsOpen U) (hne : U.Nonempty) :
    0 < cubeSide U ∧ cubeFits U (cubeSide U) := by
  let S (i : Fin d) := (fun x => x i) '' U
  let b (i : Fin d) := sSup (S i) - sInf (S i)
  let w := sSup (Set.range b)
  have hbr : BddAbove (Set.range b) := (Set.finite_range b).bddAbove
  have hS (i : Fin d) : (S i).Nonempty := hne.image _
  have hbound (i : Fin d) : BddBelow (S i) ∧ BddAbove (S i) :=
    coordinate_bounded hU i
  have hopen (i : Fin d) : IsOpen (S i) := isOpenMap_eval i U ho
  have hwidth (i : Fin d) : b i ≤ w := le_csSup hbr (Set.mem_range_self i)
  let i : Fin d := ⟨0, hd⟩
  obtain ⟨x, hx⟩ := hne
  have hxS : x i ∈ S i := Set.mem_image_of_mem _ hx
  have hext := strict_coordinate_extrema (hopen i) (hbound i).1 (hbound i).2 hxS
  have hw : 0 < w := lt_of_lt_of_le (by dsimp [b]; linarith) (hwidth i)
  have hfit : cubeFits U w := by
    refine ⟨fun i => (sSup (S i) + sInf (S i)) / 2, ?_⟩
    intro y hy j
    have hyS : y j ∈ S j := Set.mem_image_of_mem _ hy
    have he := strict_coordinate_extrema (hopen j) (hbound j).1 (hbound j).2 hyS
    have hwj := hwidth j
    dsimp [b] at hwj
    change |y j - (sSup (S j) + sInf (S j)) / 2| < w / 2
    rw [abs_lt]
    constructor <;> linarith
  have hminimal : ∀ s, cubeFits U s → w ≤ s := by
    rintro s ⟨a, ha⟩
    apply csSup_le ⟨b i, Set.mem_range_self i⟩
    rintro _ ⟨j, rfl⟩
    have hu : sSup (S j) ≤ a j + s / 2 := by
      apply csSup_le (hS j)
      rintro _ ⟨y, hy, rfl⟩
      have h := (abs_lt.mp (ha hy j)).2
      linarith
    have hl : a j - s / 2 ≤ sInf (S j) := by
      apply le_csInf (hS j)
      rintro _ ⟨y, hy, rfl⟩
      have h := (abs_lt.mp (ha hy j)).1
      linarith
    dsimp [b]
    linarith
  have hwb : BddBelow {s : ℝ | 0 < s ∧ cubeFits U s} :=
    ⟨w, fun _ hs => hminimal _ hs.2⟩
  have heq : cubeSide U = w := by
    apply le_antisymm
    · exact csInf_le hwb ⟨hw, hfit⟩
    · exact le_csInf ⟨w, hw, hfit⟩ (fun s hs => hminimal s hs.2)
  rw [heq]
  exact ⟨hw, hfit⟩

/-- Every fitting positive side bounds the infimum side from above. -/
lemma cubeSide_le {U : Set (Fin d → ℝ)} {s : ℝ} (hs : 0 < s)
    (hf : cubeFits U s) : cubeSide U ≤ s :=
  csInf_le ⟨0, fun _ ht => ht.1.le⟩ ⟨hs, hf⟩

/-- Enlarging a side preserves containment in a translated open cube. -/
lemma cubeFits_mono {U : Set (Fin d → ℝ)} {s t : ℝ}
    (hf : cubeFits U s) (hst : s ≤ t) : cubeFits U t := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨a, fun x hx i => (ha hx i).trans_le (by linarith)⟩

/-- For an open domain, fitting is exactly comparison with its positive infimum side. -/
theorem cubeFits_iff (hd : 1 ≤ d) {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) (ho : IsOpen U) (hne : U.Nonempty)
    {s : ℝ} (hs : 0 < s) : cubeFits U s ↔ cubeSide U ≤ s := by
  exact ⟨cubeSide_le hs, (cubeFits_mono (cubeSide_pos_and_fits hd hU ho hne).2)⟩

/-- Positive rescaled triadic sides eventually exceed any fixed finite side. -/
lemma exists_block_scale (w : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 1 ≤ m ∧ w ≤ ε * 3 ^ m := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (w / ε) (by norm_num : (1 : ℝ) < 3)
  refine ⟨n + 1, by omega, ?_⟩
  have hp : (3 : ℝ) ^ n ≤ 3 ^ (n + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  exact (le_of_lt ((div_lt_iff₀ hε).mp hn)).trans
    (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp hε.le)

/-- The least `m ≥ 1` with `ε 3^m ≥ cubeSide U`, defined only at positive scales.
For bounded nonempty open domains `cubeFits_iff` identifies this with the paper's index. -/
def blockIndex (U : Set (Fin d → ℝ)) (ε : ℝ) (hε : 0 < ε) : ℕ :=
  Nat.find (exists_block_scale (cubeSide U) hε)

/-- The block index is positive and its rescaled side contains the minimal side. -/
theorem blockIndex_spec (U : Set (Fin d → ℝ)) {ε : ℝ} (hε : 0 < ε) :
    1 ≤ blockIndex U ε hε ∧ cubeSide U ≤ ε * 3 ^ blockIndex U ε hε :=
  Nat.find_spec (exists_block_scale (cubeSide U) hε)

/-- No smaller positive index has a large enough side. -/
theorem blockIndex_min (U : Set (Fin d → ℝ)) {ε : ℝ} (hε : 0 < ε)
    {n : ℕ} (hn : 1 ≤ n) (hlt : n < blockIndex U ε hε) :
    ε * 3 ^ n < cubeSide U := by
  exact lt_of_not_ge (fun h => Nat.find_min (exists_block_scale (cubeSide U) hε) hlt
    ⟨hn, h⟩)

/-- The index agrees with the least positive index whose translated cube contains `U`. -/
theorem blockIndex_cube_spec (hd : 1 ≤ d) {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) (ho : IsOpen U) (hne : U.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    cubeFits U (ε * 3 ^ blockIndex U ε hε) ∧
      ∀ n, 1 ≤ n → n < blockIndex U ε hε → ¬cubeFits U (ε * 3 ^ n) := by
  refine ⟨(cubeFits_iff hd hU ho hne (by positivity)).mpr (blockIndex_spec U hε).2, ?_⟩
  intro n hn hlt hf
  exact (blockIndex_min U hε hn hlt).not_ge (cubeSide_le (by positivity) hf)

/-- The positive integer block index is characterized by its side and the preceding side. -/
theorem blockIndex_eq_iff (U : Set (Fin d → ℝ)) {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    blockIndex U ε hε = m ↔
      1 ≤ m ∧ cubeSide U ≤ ε * 3 ^ m ∧
        (m = 1 ∨ ε * 3 ^ (m - 1) < cubeSide U) := by
  constructor
  · rintro rfl
    obtain ⟨hm, hs⟩ := blockIndex_spec U hε
    refine ⟨hm, hs, ?_⟩
    by_cases h : blockIndex U ε hε = 1
    · exact Or.inl h
    · exact Or.inr (blockIndex_min U hε (by omega) (by omega))
  · rintro ⟨hm, hs, hprev⟩
    apply le_antisymm
    · exact Nat.find_min' (exists_block_scale (cubeSide U) hε) ⟨hm, hs⟩
    · by_contra h
      have hlt : blockIndex U ε hε < m := by omega
      rcases hprev with rfl | hprev
      · have := (blockIndex_spec U hε).1
        omega
      · have hp : (3 : ℝ) ^ blockIndex U ε hε ≤ 3 ^ (m - 1) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have hb := (blockIndex_spec U hε).2
        have := mul_le_mul_of_nonneg_left hp hε.le
        linarith

/-- Uniform upper side constant, including the truncated first block `m = 1`. -/
def blockUpper (U : Set (Fin d → ℝ)) : ℝ := max 3 (3 * cubeSide U)

/-- Every block has the paper's two-sided triadic scale bounds. -/
theorem block_scale_bounds (U : Set (Fin d → ℝ)) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    cubeSide U / 3 ^ blockIndex U ε hε.1 ≤ ε ∧
      ε ≤ blockUpper U / 3 ^ blockIndex U ε hε.1 := by
  have hp : 0 < (3 : ℝ) ^ blockIndex U ε hε.1 := by positivity
  constructor
  · exact (div_le_iff₀ hp).mpr (blockIndex_spec U hε.1).2
  · rw [le_div_iff₀ hp]
    obtain ⟨hm, hs, hprev⟩ := (blockIndex_eq_iff U hε.1 _).mp rfl
    rcases hprev with hfirst | hprev
    · rw [hfirst, pow_one]
      exact (mul_le_mul_of_nonneg_right hε.2.le (by norm_num)).trans
        (by simpa only [one_mul, blockUpper] using le_max_left 3 (3 * cubeSide U))
    · have heq : blockIndex U ε hε.1 = (blockIndex U ε hε.1 - 1) + 1 := by omega
      rw [heq, pow_succ]
      calc
        ε * ((3 : ℝ) ^ (blockIndex U ε hε.1 - 1) * 3) =
            (ε * 3 ^ (blockIndex U ε hε.1 - 1)) * 3 := by ring
        _ ≤ cubeSide U * 3 := mul_le_mul_of_nonneg_right hprev.le (by norm_num)
        _ ≤ blockUpper U := by
          simpa only [mul_comm, blockUpper] using le_max_right 3 (3 * cubeSide U)

/-- The endpoint representative has exactly index `m` whenever it is an admissible scale. -/
theorem blockIndex_representative {U : Set (Fin d → ℝ)} (hw : 0 < cubeSide U)
    {m : ℕ} (hm : 1 ≤ m) :
    blockIndex U (cubeSide U / 3 ^ m) (div_pos hw (by positivity)) = m := by
  apply (blockIndex_eq_iff U _ m).mpr
  have hp : (3 : ℝ) ^ m ≠ 0 := by positivity
  refine ⟨hm, by rw [div_mul_cancel₀ _ hp], ?_⟩
  by_cases hfirst : m = 1
  · exact Or.inl hfirst
  · right
    have heq : m = (m - 1) + 1 := by omega
    have hpow : (3 : ℝ) ^ m = 3 ^ (m - 1) * 3 := by
      conv_lhs => rw [heq, pow_succ]
    rw [hpow]
    have hn : (3 : ℝ) ^ (m - 1) ≠ 0 := by positivity
    have he : cubeSide U / (3 ^ (m - 1) * 3) * 3 ^ (m - 1) = cubeSide U / 3 := by
      field_simp [hn]
    rw [he]
    linarith

/-- In every nonempty block the canonical representative belongs to `(0,1)` and that block. -/
theorem representative_mem_block {U : Set (Fin d → ℝ)} (hw : 0 < cubeSide U)
    {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    let m := blockIndex U ε hε.1
    ∃ hrep : cubeSide U / 3 ^ m ∈ Set.Ioo (0 : ℝ) 1,
      blockIndex U (cubeSide U / 3 ^ m) hrep.1 = m := by
  refine ⟨⟨div_pos hw (by positivity),
    ((block_scale_bounds U hε).1.trans_lt hε.2)⟩, ?_⟩
  exact blockIndex_representative hw (blockIndex_spec U hε.1).1

/-- Two scales in one block differ by at most the width of its triadic interval. -/
theorem block_scale_dist {U : Set (Fin d → ℝ)} {ε ε' : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hε' : ε' ∈ Set.Ioo (0 : ℝ) 1)
    (hm : blockIndex U ε hε.1 = blockIndex U ε' hε'.1) :
    |ε - ε'| ≤ (blockUpper U - cubeSide U) / 3 ^ blockIndex U ε hε.1 := by
  obtain ⟨hlo, hhi⟩ := block_scale_bounds U hε
  obtain ⟨hlo', hhi'⟩ := block_scale_bounds U hε'
  rw [← hm] at hlo' hhi'
  rw [sub_div, abs_le]
  constructor <;> linarith

/-- Ratios of any two scales in one block are bounded by a domain-only constant. -/
theorem block_scale_ratio {U : Set (Fin d → ℝ)} (hw : 0 < cubeSide U)
    {ε ε' : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hε' : ε' ∈ Set.Ioo (0 : ℝ) 1)
    (hm : blockIndex U ε hε.1 = blockIndex U ε' hε'.1) :
    ε ≤ (blockUpper U / cubeSide U) * ε' := by
  have hu : 0 < blockUpper U := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hlo := (block_scale_bounds U hε').1
  rw [← hm] at hlo
  calc
    ε ≤ blockUpper U / 3 ^ blockIndex U ε hε.1 := (block_scale_bounds U hε).2
    _ = (blockUpper U / cubeSide U) *
        (cubeSide U / 3 ^ blockIndex U ε hε.1) := by field_simp [hw.ne']
    _ ≤ (blockUpper U / cubeSide U) * ε' :=
      mul_le_mul_of_nonneg_left hlo (div_pos hu hw).le

/-- A fixed centred enlargement contains the domain for every scale in every block. -/
theorem exists_enlarged_cube {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    (hw : 0 < cubeSide U) :
    ∃ L : ℕ, 1 ≤ L ∧ ∀ ε : ℝ, ∀ hε : 0 < ε,
      U ⊆ openCube 0 (ε * 3 ^ (blockIndex U ε hε + L - 1)) := by
  obtain ⟨R, hR, hbound⟩ := hU.exists_pos_norm_lt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * R / cubeSide U)
    (by norm_num : (1 : ℝ) < 3)
  refine ⟨n + 1, by omega, ?_⟩
  intro ε hε x hx i
  have hxi : |x i| < R := by
    exact (show |x i| ≤ ‖x‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i).trans_lt
      (hbound x hx)
  have hlarge : 2 * R < cubeSide U * 3 ^ n := by
    simpa only [mul_comm] using (div_lt_iff₀ hw).mp hn
  have hs := mul_le_mul_of_nonneg_right (blockIndex_spec U hε).2
    (by positivity : 0 ≤ (3 : ℝ) ^ n)
  have he : blockIndex U ε hε + (n + 1) - 1 = blockIndex U ε hε + n := by omega
  change |x i - 0| < ε * 3 ^ (blockIndex U ε hε + (n + 1) - 1) / 2
  rw [sub_zero, he, pow_add]
  nlinarith only [hxi, hlarge, hs]

/-- Taking logarithms of the block side bounds compares the logarithmic scale with its index. -/
theorem block_log_bounds {U : Set (Fin d → ℝ)} (hw : 0 < cubeSide U)
    {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    1 + |Real.log ε| ≤
        (1 + Real.log 3 + |Real.log (cubeSide U)|) * blockIndex U ε hε.1 ∧
      (blockIndex U ε hε.1 : ℝ) * Real.log 3 ≤
        |Real.log ε| + |Real.log (blockUpper U)| := by
  have hp : 0 < (3 : ℝ) ^ blockIndex U ε hε.1 := by positivity
  have hm : (1 : ℝ) ≤ blockIndex U ε hε.1 := by
    exact_mod_cast (blockIndex_spec U hε.1).1
  have hlogε : Real.log ε < 0 := Real.log_neg hε.1 hε.2
  have hlo := Real.log_le_log hw (blockIndex_spec U hε.1).2
  rw [Real.log_mul hε.1.ne' hp.ne', Real.log_pow] at hlo
  have hhi := (le_div_iff₀ hp).mp (block_scale_bounds U hε).2
  have hupper := Real.log_le_log (mul_pos hε.1 hp) hhi
  rw [Real.log_mul hε.1.ne' hp.ne', Real.log_pow] at hupper
  rw [abs_of_neg hlogε]
  constructor
  · have hprod := mul_nonneg (abs_nonneg (Real.log (cubeSide U)))
      (sub_nonneg.mpr hm)
    have hneg := neg_le_abs (Real.log (cubeSide U))
    nlinarith only [hlo, hm, hprod, hneg]
  · exact (by linarith only [hupper, le_abs_self (Real.log (blockUpper U))])

/-- The Euclidean normalization is bounded above by a domain-dependent multiple of the index. -/
theorem kappa_le (d : ℕ) {U : Set (Fin d → ℝ)} (hw : 0 < cubeSide U) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ∀ hε : ε ∈ Set.Ioo (0 : ℝ) 1,
      LongRange.kappa d ε ≤ C * blockIndex U ε hε.1 := by
  obtain ⟨K, hK, hk⟩ := LongRange.kappa_le d
  have hA : 0 < 1 + Real.log 3 + |Real.log (cubeSide U)| := by
    have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
    positivity
  refine ⟨K * (1 + Real.log 3 + |Real.log (cubeSide U)|), mul_pos hK hA, ?_⟩
  intro ε hε
  calc
    LongRange.kappa d ε ≤ K * (1 + |Real.log ε|) := hk ε hε
    _ ≤ K * ((1 + Real.log 3 + |Real.log (cubeSide U)|) * blockIndex U ε hε.1) :=
      mul_le_mul_of_nonneg_left (block_log_bounds hw hε).1 hK.le
    _ = _ := by ring

/-- The Euclidean normalization bounds a positive domain-dependent multiple of the index. -/
theorem le_kappa (hd : 1 ≤ d) {U : Set (Fin d → ℝ)} (hw : 0 < cubeSide U) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, ∀ hε : ε ∈ Set.Ioo (0 : ℝ) 1,
      c * blockIndex U ε hε.1 ≤ LongRange.kappa d ε := by
  obtain ⟨k, hk, hbound⟩ := LongRange.le_kappa hd
  let B := 1 + |Real.log (blockUpper U)|
  have hB : 0 < B := by dsimp [B]; positivity
  have hl : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨k * Real.log 3 / B, div_pos (mul_pos hk hl) hB, ?_⟩
  intro ε hε
  have hlog := (block_log_bounds hw hε).2
  have ht : 0 ≤ |Real.log ε| := abs_nonneg _
  have hprod := mul_nonneg (abs_nonneg (Real.log (blockUpper U))) ht
  have hscale : (blockIndex U ε hε.1 : ℝ) * Real.log 3 ≤
      B * (1 + |Real.log ε|) := by
    dsimp [B]
    nlinarith only [hlog, hprod]
  calc
    k * Real.log 3 / B * blockIndex U ε hε.1 =
        k * ((blockIndex U ε hε.1 : ℝ) * Real.log 3) / B := by ring
    _ ≤ k * (B * (1 + |Real.log ε|)) / B :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hscale hk.le) hB.le
    _ = k * (1 + |Real.log ε|) := by field_simp [hB.ne']
    _ ≤ LongRange.kappa d ε := hbound ε hε

/-- Step 4 scale constants and a centred enlargement follow from the domain assumptions. -/
theorem block_geometry (hd : 1 ≤ d) {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) (ho : IsOpen U) (hne : U.Nonempty) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∃ L : ℕ, 1 ≤ L ∧
      ∀ ε : ℝ, ∀ hε : ε ∈ Set.Ioo (0 : ℝ) 1,
        c / 3 ^ blockIndex U ε hε.1 ≤ ε ∧
        ε ≤ C / 3 ^ blockIndex U ε hε.1 ∧
        U ⊆ openCube 0 (ε * 3 ^ (blockIndex U ε hε.1 + L - 1)) := by
  have hw := (cubeSide_pos_and_fits hd hU ho hne).1
  obtain ⟨L, hL, hcontain⟩ := exists_enlarged_cube hU hw
  refine ⟨cubeSide U, blockUpper U, hw, ?_, L, hL, ?_⟩
  · exact (by linarith only [hw] : cubeSide U ≤ 3 * cubeSide U).trans (le_max_right _ _)
  · intro ε hε
    exact ⟨(block_scale_bounds U hε).1, (block_scale_bounds U hε).2, hcontain ε hε.1⟩

/-- On all blocks the normalization is comparable to the index under the standing assumptions. -/
theorem kappa_comparable (hd : 1 ≤ d) {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) (ho : IsOpen U) (hne : U.Nonempty) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ ε : ℝ, ∀ hε : ε ∈ Set.Ioo (0 : ℝ) 1,
        c * blockIndex U ε hε.1 ≤ LongRange.kappa d ε ∧
        LongRange.kappa d ε ≤ C * blockIndex U ε hε.1 := by
  have hw := (cubeSide_pos_and_fits hd hU ho hne).1
  obtain ⟨c, hc, hlo⟩ := le_kappa hd hw
  obtain ⟨C, hC, hhi⟩ := kappa_le d hw
  exact ⟨c, C, hc, hC, fun ε hε => ⟨hlo ε hε, hhi ε hε⟩⟩

end
end LongRange.TwoScale

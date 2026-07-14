/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TH.KernelReduction
import CITED.CorvajaZannierProof
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Stage 2b/2b′: the two unconditional slices of the kernel (K) from CZ 2004

Both slices of the M4/A3 kernel that the Corvaja–Zannier Main Theorem
(`CZ.pseudoPisot_approx_of_subspace`, [CZ04] — **derived** from the Subspace
Theorem in `CITED/CorvajaZannierProof.lean`) kills, per [M4A3] §6.2 and §6.2′:

* **2b, bounded gaps** (`boundedGap_slice_finite`): for every *fixed* gap `s₀`,
  only finitely many `a` with `‖(3/2)^{a+s₀} − (3/2)^a‖ ≤ θ^{a+s₀}`.  CZ data:
  `δ = (3/2)^{s₀} − 1` (fixed multiplier), `q = 1`, `u = (3/2)^a`, `H(u) = 3^a`;
  rate conversion `ε := log θ⁻¹ / (2 log 3)`.  Aggregated over `s₀ ≤ S` as
  `gapBounded_slice_finite`, and consumed for repetitions as
  `boundedGap_repetition_short`: fixed-gap repetitions of linear length
  (`k ≥ (num/den)·a`, certified rational slope) are finite in number.
* **2b′, huge gaps — Theorem B2** (`hugeGap_slice_finite`): for every `θ` there
  is `ε′(θ) > 0` such that only finitely many (K)-violating pairs have
  `a ≤ ε′·c`.  This uses the theorem's built-in uniformity over the *integer*
  multiplier slot: multiply by `2^a` (`‖x‖ ≥ ‖2^a·x‖ / 2^a`, and
  `2^a((3/2)^c − (3/2)^a) ≡ 3^a(3/2)^s mod 1`, `s := c − a`), then apply CZ with
  `δ = 1`, `q = 3^a`, `u = (3/2)^s`.  The windows nest whenever
  `a·log 2 + (1+ε)a·log 3 + εs·log 3 < c·log θ⁻¹`, which
  `ε := min 1 (log θ⁻¹/(4 log 3))` and rational
  `ε′ < (3/4)·log θ⁻¹ / (log 2 + 2 log 3)` guarantee ([M4A3] §6.2′).

Both finiteness results are **ineffective** (inherited from the Subspace
Theorem).  What remains of (K) after these two slices is exactly the *middle band*
(`a ≥ ε′c` and gap `s → ∞`) — consumed as a named hypothesis by
`TH.CapstoneM4`, attacked as Stage 2c ([M4A3] §6.3).

Axiom footprint: std3 + `Subspace.evertseSchlickewei` ([EvSc02], via the derived
`CZ.pseudoPisot_approx_of_subspace`; the bespoke [CZ04] axiom was retired 2026-07-14).

## Contents

* `boundedGap_slice_finite` — **Stage 2b**: the fixed-gap slice of (K) is finite.
* `gapBounded_slice_finite` — union over gaps `≤ S`: the gap-bounded slice of
  `kernelViolators θ` is finite.
* `boundedGap_repetition_short` — fixed-gap repetitions are short: only finitely
  many `(a, k)` with `k ≥ (num/den)·a` and `IsRepetition a (a+s₀) k`.
* `hugeGap_slice_finite` — **Stage 2b′ / Theorem B2**: the huge-gap band
  `a ≤ ε′·c` of `kernelViolators θ` is finite, for some `ε′(θ) > 0`.

## References

* [CZ04] Corvaja, Zannier. *On the rational approximations to the powers of an
  algebraic number.* Acta Math. **193** (2004), 175–191.  (Main Theorem, derived
  in `CITED/CorvajaZannierProof.lean` from the Subspace Theorem.)
* [M4A3] `plan-M4A3.html` (this repository, 2026-07): §6.2 (bounded gaps),
  §6.2′ (huge gaps via the `q`-slot), §10.1 (the `θ < 1/2` remark).
-/

namespace TH

/-! ## ℚ-side helpers -/

private lemma two_zpow_neg_mul_three_zpow (n : ℕ) :
    (2 : ℚ) ^ (-(n : ℤ)) * (3 : ℚ) ^ ((n : ℤ)) = (3 / 2) ^ n := by
  rw [zpow_neg, zpow_natCast, zpow_natCast, div_pow, inv_mul_eq_div]

/-! ## ℝ-side helpers: the ε-window conversions -/

private lemma log_three_pos : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)

private lemma log_inv_pos {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    0 < Real.log θ⁻¹ := by
  rw [Real.log_inv]
  have := Real.log_neg hθ0 hθ1
  linarith

/-- 2b window: `θ^a < (3^a)^{-ε}` for `ε = log θ⁻¹ / (2 log 3)` and `a ≥ 1`. -/
private lemma pow_lt_rpow_neg {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {a : ℕ}
    (ha : 1 ≤ a) :
    θ ^ a < ((3 : ℝ) ^ a) ^ (-(Real.log θ⁻¹ / (2 * Real.log 3))) := by
  have h3 := log_three_pos
  have hlogθ : Real.log θ < 0 := Real.log_neg hθ0 hθ1
  have hpow3 : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
  have hθa : (0 : ℝ) < θ ^ a := by positivity
  rw [Real.rpow_def_of_pos hpow3, ← Real.exp_log hθa, Real.log_pow, Real.log_pow,
    Real.exp_lt_exp, Real.log_inv]
  have hkey : (a : ℝ) * Real.log 3 * (-(-Real.log θ / (2 * Real.log 3)))
      = (a : ℝ) * Real.log θ / 2 := by
    field_simp
  rw [hkey]
  have ha' : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hneg : (a : ℝ) * Real.log θ < 0 :=
    mul_neg_of_pos_of_neg (by linarith) hlogθ
  linarith

/-- 2b′ window nesting ([M4A3] §6.2′): with `ε = min 1 (log θ⁻¹/(4 log 3))` and
`ε′·(log 2 + 2 log 3) < (3/4)·log θ⁻¹`, a pair `c = a + s` with `a ≤ ε′·c`
satisfies `2^a·θ^c < (3^s)^{-ε}·(3^a)^{-1-ε}`. -/
private lemma hugeGap_window {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {ε' : ℚ}
    (hε'D : (ε' : ℝ) * (Real.log 2 + 2 * Real.log 3) < 3 * Real.log θ⁻¹ / 4)
    {a s c : ℕ} (ha : 1 ≤ a) (hs : 1 ≤ s) (hcas : c = a + s)
    (hac : (a : ℝ) ≤ (ε' : ℝ) * c) :
    (2 : ℝ) ^ a * θ ^ c
      < ((3 : ℝ) ^ s) ^ (-(min 1 (Real.log θ⁻¹ / (4 * Real.log 3))))
        * ((3 : ℝ) ^ a) ^ (-1 - min 1 (Real.log θ⁻¹ / (4 * Real.log 3))) := by
  have h3 := log_three_pos
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hLpos : 0 < Real.log θ⁻¹ := log_inv_pos hθ0 hθ1
  set L : ℝ := Real.log θ⁻¹ with hL
  set ε : ℝ := min 1 (L / (4 * Real.log 3)) with hε
  have hεpos : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεle : ε ≤ L / (4 * Real.log 3) := min_le_right _ _
  -- the exponent inequality: a·log2 + (1+ε)·a·log3 + ε·s·log3 < c·L
  have hexp : (a : ℝ) * Real.log 2 + (c : ℝ) * Real.log θ
      < (s : ℝ) * Real.log 3 * (-ε) + (a : ℝ) * Real.log 3 * (-1 - ε) := by
    have hlogθ : Real.log θ = -L := by
      rw [hL, Real.log_inv]
      ring
    rw [hlogθ]
    have hc1 : (1 : ℝ) ≤ (c : ℝ) := by
      have : 1 ≤ c := by omega
      exact_mod_cast this
    have hslec : (s : ℝ) ≤ (c : ℝ) := by
      have : s ≤ c := by omega
      exact_mod_cast this
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    have hc0 : (0 : ℝ) < (c : ℝ) := by linarith
    -- (1+ε)·a·log3 ≤ 2·a·log3
    have h1 : (1 + ε) * ((a : ℝ) * Real.log 3) ≤ 2 * ((a : ℝ) * Real.log 3) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    -- a·(log2 + 2·log3) ≤ (ε'·c)·(log2 + 2·log3)
    have hD : (0 : ℝ) < Real.log 2 + 2 * Real.log 3 := by linarith
    have h2' : (a : ℝ) * (Real.log 2 + 2 * Real.log 3)
        ≤ ((ε' : ℝ) * c) * (Real.log 2 + 2 * Real.log 3) :=
      mul_le_mul_of_nonneg_right hac hD.le
    -- (ε'·(log2 + 2·log3))·c < (3L/4)·c
    have h3' : ((ε' : ℝ) * (Real.log 2 + 2 * Real.log 3)) * c
        < (3 * L / 4) * c := mul_lt_mul_of_pos_right hε'D hc0
    -- ε·s·log3 ≤ s·L/4 ≤ c·L/4
    have h4 : ε * ((s : ℝ) * Real.log 3)
        ≤ (L / (4 * Real.log 3)) * ((s : ℝ) * Real.log 3) :=
      mul_le_mul_of_nonneg_right hεle (by positivity)
    have h5 : (L / (4 * Real.log 3)) * ((s : ℝ) * Real.log 3) = (s : ℝ) * L / 4 := by
      field_simp
    have h6 : (s : ℝ) * L / 4 ≤ (c : ℝ) * L / 4 := by
      have := mul_le_mul_of_nonneg_right hslec hLpos.le
      linarith
    nlinarith [h1, h2', h3', h4, h5, h6]
  -- wrap into exp
  have hLHS : (2 : ℝ) ^ a * θ ^ c
      = Real.exp ((a : ℝ) * Real.log 2 + (c : ℝ) * Real.log θ) := by
    rw [Real.exp_add]
    congr 1
    · rw [← Real.log_pow, Real.exp_log (by positivity)]
    · rw [← Real.log_pow, Real.exp_log (by positivity)]
  have hRHS : ((3 : ℝ) ^ s) ^ (-ε) * ((3 : ℝ) ^ a) ^ (-1 - ε)
      = Real.exp ((s : ℝ) * Real.log 3 * (-ε)
          + (a : ℝ) * Real.log 3 * (-1 - ε)) := by
    rw [Real.exp_add]
    congr 1
    · rw [Real.rpow_def_of_pos (by positivity), Real.log_pow]
    · rw [Real.rpow_def_of_pos (by positivity), Real.log_pow]
  rw [hLHS, hRHS]
  exact Real.exp_lt_exp.mpr hexp

/-! ## Stage 2b: the bounded-gap slice -/

/-- **Stage 2b** ([M4A3] §6.2): for every fixed gap `s₀ ≥ 1` and every rational
scale `θ ∈ (0, 1)`, only finitely many `a ≥ 2` satisfy
`‖(3/2)^{a+s₀} − (3/2)^a‖ ≤ θ^{a+s₀}`.  CZ data: `δ = (3/2)^{s₀} − 1`, `q = 1`,
`u = (3/2)^a`; the pseudo-Pisot proviso is vacuous (odd numerator over a power
of 2 is never an integer).  Ineffective; footprint std3 + [CZ04]. -/
theorem boundedGap_slice_finite (s₀ : ℕ) (hs₀ : 1 ≤ s₀) (θ : ℚ) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) :
    {a : ℕ | 2 ≤ a ∧
      ((3 / 2 : ℚ) ^ (a + s₀) - (3 / 2 : ℚ) ^ a).distToNearestInt
        ≤ θ ^ (a + s₀)}.Finite := by
  have hθ0' : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ0
  have hθ1' : (θ : ℝ) < 1 := by exact_mod_cast hθ1
  have hδpos : (0 : ℚ) < (3 / 2) ^ s₀ - 1 := by
    have h1 : (3 / 2 : ℚ) ^ 1 ≤ (3 / 2) ^ s₀ :=
      pow_le_pow_right₀ (by norm_num) hs₀
    rw [pow_one] at h1
    linarith
  have hεpos : 0 < Real.log (θ : ℝ)⁻¹ / (2 * Real.log 3) :=
    div_pos (log_inv_pos hθ0' hθ1') (by positivity)
  have hfin := CZ.pseudoPisot_approx_of_subspace ((3 / 2 : ℚ) ^ s₀ - 1) hδpos.ne'
    (Real.log (θ : ℝ)⁻¹ / (2 * Real.log 3)) hεpos
  have hginj : Function.Injective
      (fun a : ℕ => ((1, -(a : ℤ), (a : ℤ)) : ℕ × ℤ × ℤ)) := by
    intro a b hab
    simpa using hab
  refine Set.Finite.subset (hfin.preimage hginj.injOn) ?_
  rintro a ⟨ha2, hdist⟩
  rw [Set.mem_preimage, Set.mem_setOf_eq]
  have hsval : CZ.sval ((3 / 2 : ℚ) ^ s₀ - 1) 1 (-(a : ℤ)) (a : ℤ)
      = (3 / 2 : ℚ) ^ (a + s₀) - (3 / 2 : ℚ) ^ a := by
    unfold CZ.sval
    rw [two_zpow_neg_mul_three_zpow]
    push_cast
    rw [pow_add]
    ring
  have hdpos : 0 < ((3 / 2 : ℚ) ^ (a + s₀)
      - (3 / 2 : ℚ) ^ a).distToNearestInt :=
    distToNearestInt_orbit_pos (by omega) (by omega)
  refine ⟨le_refl 1, ?_, ?_, ?_, ?_⟩
  · -- 1 < |δ·q·u|
    rw [hsval, show (3 / 2 : ℚ) ^ (a + s₀) - (3 / 2 : ℚ) ^ a
        = ((3 / 2 : ℚ) ^ s₀ - 1) * (3 / 2) ^ a by rw [pow_add]; ring]
    have hδhalf : (1 / 2 : ℚ) ≤ (3 / 2) ^ s₀ - 1 := by
      have h1 : (3 / 2 : ℚ) ^ 1 ≤ (3 / 2) ^ s₀ :=
        pow_le_pow_right₀ (by norm_num) hs₀
      rw [pow_one] at h1
      linarith
    have hpa : (9 / 4 : ℚ) ≤ (3 / 2) ^ a := by
      calc (9 / 4 : ℚ) = (3 / 2) ^ 2 := by norm_num
        _ ≤ (3 / 2) ^ a := pow_le_pow_right₀ (by norm_num) ha2
    rw [abs_of_pos (mul_pos hδpos (by positivity))]
    nlinarith
  · -- not an integer (pseudo-Pisot proviso, discharged from ‖·‖ > 0)
    rw [hsval]
    exact CZ.not_intCast_of_distToNearestInt_pos hdpos
  · -- 0 < ‖δ·q·u‖
    rw [hsval]
    exact hdpos
  · -- ‖δ·q·u‖ < H(u)^{-ε}·q^{-1-ε}
    rw [hsval, CZ.height23_neg_natCast, Nat.cast_one, Real.one_rpow, mul_one]
    have hcast3 : ((3 ^ a : ℕ) : ℝ) = (3 : ℝ) ^ a := by push_cast; ring
    rw [hcast3]
    calc (((3 / 2 : ℚ) ^ (a + s₀) - (3 / 2 : ℚ) ^ a).distToNearestInt : ℝ)
        ≤ ((θ ^ (a + s₀) : ℚ) : ℝ) := by exact_mod_cast hdist
      _ = (θ : ℝ) ^ (a + s₀) := by push_cast; ring
      _ ≤ (θ : ℝ) ^ a :=
          pow_le_pow_of_le_one hθ0'.le hθ1'.le (Nat.le_add_right a s₀)
      _ < ((3 : ℝ) ^ a) ^ (-(Real.log (θ : ℝ)⁻¹ / (2 * Real.log 3))) :=
          pow_lt_rpow_neg hθ0' hθ1' (by omega)

/-- The gap-bounded slice of the kernel: (K)-violating pairs of gap `≤ S` are
finite in number — the union of the fixed-gap slices `1 ≤ s₀ ≤ S` of Stage 2b.
[M4A3] §6.2.  Footprint std3 + [CZ04]. -/
theorem gapBounded_slice_finite (S : ℕ) (θ : ℚ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    {p ∈ kernelViolators θ | p.2 ≤ p.1 + S}.Finite := by
  have hsub : {p ∈ kernelViolators θ | p.2 ≤ p.1 + S} ⊆
      ⋃ s₀ ∈ Finset.Icc 1 S, (fun a => (a, a + s₀)) ''
        {a : ℕ | 2 ≤ a ∧
          ((3 / 2 : ℚ) ^ (a + s₀) - (3 / 2 : ℚ) ^ a).distToNearestInt
            ≤ θ ^ (a + s₀)} := by
    rintro ⟨a, c⟩ ⟨⟨ha, hac, hdist⟩, hgap⟩
    have hs₀ : c - a ∈ Finset.Icc 1 S := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    refine Set.mem_biUnion hs₀ ⟨a, ⟨ha, ?_⟩, ?_⟩
    · rw [show a + (c - a) = c by omega]
      exact hdist
    · simp only [Prod.mk.injEq, true_and]
      omega
  refine Set.Finite.subset ?_ hsub
  refine Set.Finite.biUnion (Finset.finite_toSet _) fun s₀ hs₀ => ?_
  exact Set.Finite.image _
    (boundedGap_slice_finite s₀ (Finset.mem_Icc.mp hs₀).1 θ hθ0 hθ1)

/-- **Bounded-gap repetitions are short** ([M4A3] §6.2, corollary): for every
fixed gap `s₀ ≥ 1` and every certified rational slope `num/den > 0`, only
finitely many pairs `(a, k)` satisfy `k ≥ (num/den)·a` together with
`IsRepetition a (a+s₀) k`.  Strictly beyond T0.1 in its regime; kills the
`D = 0` subspace degeneracy of [M4A3] §5 for good.  Ineffective; footprint
std3 + [CZ04]. -/
theorem boundedGap_repetition_short (s₀ : ℕ) (hs₀ : 1 ≤ s₀) (num den : ℕ)
    (hnum : 0 < num) (hden : 0 < den) :
    {p : ℕ × ℕ | 2 ≤ p.1 ∧ num * p.1 ≤ den * p.2 ∧
      IsRepetition p.1 (p.1 + s₀) p.2}.Finite := by
  -- rational scale θ with (2/3)^num ≤ θ^{den·(1+s₀)}
  obtain ⟨θ, hθ0, hθ1, hθpow⟩ := exists_pow_ge ((2 / 3 : ℚ) ^ num)
    (by positivity) (pow_lt_one₀ (by norm_num) (by norm_num) (by omega))
    (den * (1 + s₀)) (Nat.mul_pos hden (by omega))
  have hslice := boundedGap_slice_finite s₀ hs₀ θ hθ0 hθ1
  obtain ⟨A, hA⟩ := hslice.bddAbove
  refine Set.Finite.subset (hslice.prod (Set.finite_Iic (24 * (A + s₀) + 24))) ?_
  rintro ⟨a, k⟩ ⟨ha2, hslope, hrep⟩
  have hmem : a ∈ {a : ℕ | 2 ≤ a ∧
      ((3 / 2 : ℚ) ^ (a + s₀) - (3 / 2 : ℚ) ^ a).distToNearestInt
        ≤ θ ^ (a + s₀)} := by
    refine ⟨ha2, ?_⟩
    have hnc : num * (a + s₀) ≤ den * (1 + s₀) * k := by
      have e1 : a + s₀ ≤ a * (1 + s₀) := by
        have h1 : s₀ ≤ a * s₀ := Nat.le_mul_of_pos_left s₀ (by omega)
        calc a + s₀ ≤ a + a * s₀ := by omega
          _ = a * (1 + s₀) := by ring
      calc num * (a + s₀) ≤ num * (a * (1 + s₀)) := Nat.mul_le_mul_left _ e1
        _ = (num * a) * (1 + s₀) := by ring
        _ ≤ (den * k) * (1 + s₀) := Nat.mul_le_mul_right _ hslope
        _ = den * (1 + s₀) * k := by ring
    have hp : ((2 / 3 : ℚ) ^ k) ^ num ≤ (θ ^ (a + s₀)) ^ num := by
      calc ((2 / 3 : ℚ) ^ k) ^ num = ((2 / 3 : ℚ) ^ num) ^ k := by
            rw [← pow_mul, ← pow_mul, mul_comm]
        _ ≤ (θ ^ (den * (1 + s₀))) ^ k := pow_le_pow_left₀ (by positivity) hθpow k
        _ = θ ^ (den * (1 + s₀) * k) := by rw [← pow_mul]
        _ ≤ θ ^ (num * (a + s₀)) := pow_le_pow_of_le_one hθ0.le hθ1.le hnc
        _ = (θ ^ (a + s₀)) ^ num := by rw [← pow_mul, mul_comm]
    have hstep : ((3 / 2 : ℚ) ^ (a + s₀) - (3 / 2 : ℚ) ^ a).distToNearestInt
        ≤ (2 / 3 : ℚ) ^ k :=
      le_trans (distToNearestInt_orbit_le a (a + s₀))
        (abs_eps_sub_le_of_repetition hrep)
    exact le_trans hstep
      ((pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega)).mp hp)
  refine Set.mem_prod.mpr ⟨hmem, ?_⟩
  -- growth ceiling bounds k: 41·k ≤ 24·(a+s₀) + 24 with a ≤ A
  have hbound := repetition_linear_bound ha2 (by omega : a < a + s₀) hrep
  have haA : a ≤ A := hA hmem
  simp only [Set.mem_Iic]
  omega

/-! ## Stage 2b′: the huge-gap slice (Theorem B2) -/

/-- **Stage 2b′ / Theorem B2** ([M4A3] §6.2′): for every rational scale
`θ ∈ (0, 1)` there is a rational `ε′ > 0` such that only finitely many
(K)-violating pairs sit in the huge-gap band `a ≤ ε′·c`.  Uses the
`(q, u)`-pair uniformity of the CZ Main Theorem: multiply by `2^a`
(`‖3^a(3/2)^s‖ ≤ 2^a·‖(3/2)^c − (3/2)^a‖`, `s := c − a`) and apply the axiom
with `δ = 1`, `q = 3^a`, `u = (3/2)^s`.  Together with 2b, the capstone
hypothesis shrinks to the middle band `ε′c ≤ a`, `s → ∞`.  Ineffective;
footprint std3 + [CZ04]. -/
theorem hugeGap_slice_finite (θ : ℚ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ ε' : ℚ, 0 < ε' ∧
      {p ∈ kernelViolators θ | (p.1 : ℚ) ≤ ε' * p.2}.Finite := by
  have hθ0' : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ0
  have hθ1' : (θ : ℝ) < 1 := by exact_mod_cast hθ1
  have h3 := log_three_pos
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hLpos := log_inv_pos hθ0' hθ1'
  have hDpos : (0 : ℝ) < Real.log 2 + 2 * Real.log 3 := by linarith
  obtain ⟨ε', hε'0, hε'lt⟩ := exists_rat_btwn
    (show (0 : ℝ) < 3 * Real.log (θ : ℝ)⁻¹ / 4 / (Real.log 2 + 2 * Real.log 3)
      by positivity)
  have hε'D : (ε' : ℝ) * (Real.log 2 + 2 * Real.log 3)
      < 3 * Real.log (θ : ℝ)⁻¹ / 4 := (lt_div_iff₀ hDpos).mp hε'lt
  refine ⟨ε', by exact_mod_cast hε'0, ?_⟩
  have hεpos : (0 : ℝ) < min 1 (Real.log (θ : ℝ)⁻¹ / (4 * Real.log 3)) :=
    lt_min one_pos (by positivity)
  have hfin := CZ.pseudoPisot_approx_of_subspace 1 one_ne_zero
    (min 1 (Real.log (θ : ℝ)⁻¹ / (4 * Real.log 3))) hεpos
  -- the embedding (a, c) ↦ (q, x, y) = (3^a, −(c−a), c−a)
  refine Set.Finite.subset (Set.Finite.preimage
    (f := fun p : ℕ × ℕ => ((3 ^ p.1, -((p.2 - p.1 : ℕ) : ℤ), ((p.2 - p.1 : ℕ) : ℤ))
      : ℕ × ℤ × ℤ)) ?_ hfin) ?_
  · -- injectivity on the preimage: a from 3^a; gap 0 is excluded by ‖·‖ > 0
    have hgap : ∀ p : ℕ × ℕ, (p ∈ (fun p : ℕ × ℕ =>
        ((3 ^ p.1, -((p.2 - p.1 : ℕ) : ℤ), ((p.2 - p.1 : ℕ) : ℤ)) : ℕ × ℤ × ℤ)) ⁻¹'
        {p : ℕ × ℤ × ℤ | 1 ≤ p.1 ∧ 1 < |CZ.sval 1 p.1 p.2.1 p.2.2| ∧
          ¬(∃ n : ℤ, CZ.sval 1 p.1 p.2.1 p.2.2 = n) ∧
          0 < (CZ.sval 1 p.1 p.2.1 p.2.2).distToNearestInt ∧
          ((CZ.sval 1 p.1 p.2.1 p.2.2).distToNearestInt : ℝ)
            < (CZ.height23 p.2.1 p.2.2 : ℝ)
                ^ (-(min 1 (Real.log (θ : ℝ)⁻¹ / (4 * Real.log 3))))
              * (p.1 : ℝ)
                ^ (-1 - min 1 (Real.log (θ : ℝ)⁻¹ / (4 * Real.log 3)))}) →
        1 ≤ p.2 - p.1 := by
      rintro ⟨a, c⟩ hp
      by_contra h0
      have hs0 : c - a = 0 := by omega
      rw [Set.mem_preimage, Set.mem_setOf_eq, hs0] at hp
      obtain ⟨-, -, -, hpos, -⟩ := hp
      have hint : CZ.sval 1 (3 ^ a) (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ)
          = (((3 ^ a : ℕ) : ℤ) : ℚ) := by
        unfold CZ.sval
        push_cast
        simp
      rw [hint, Rat.distToNearestInt_intCast] at hpos
      exact lt_irrefl 0 hpos
    rintro ⟨a, c⟩ hac ⟨a', c'⟩ hac' heq
    have h1 : (3 : ℕ) ^ a = 3 ^ a' := congrArg Prod.fst heq
    have haa : a = a' := Nat.pow_right_injective (by norm_num) h1
    have h2' : ((c - a : ℕ) : ℤ) = ((c' - a' : ℕ) : ℤ) :=
      congrArg (fun p : ℕ × ℤ × ℤ => p.2.2) heq
    have hss : c - a = c' - a' := by exact_mod_cast h2'
    have hg1 := hgap (a, c) hac
    have hg2 := hgap (a', c') hac'
    simp only [Prod.mk.injEq]
    exact ⟨haa, by omega⟩
  · -- membership of the huge-gap violators
    rintro ⟨a, c⟩ ⟨⟨ha2, hac, hdist⟩, hhuge⟩
    rw [Set.mem_preimage, Set.mem_setOf_eq]
    have hs1 : 1 ≤ c - a := by omega
    have hcas : c = a + (c - a) := by omega
    set s := c - a with hsdef
    have hsval : CZ.sval 1 (3 ^ a) (-(s : ℤ)) (s : ℤ)
        = (3 : ℚ) ^ a * (3 / 2) ^ s := by
      unfold CZ.sval
      rw [two_zpow_neg_mul_three_zpow]
      push_cast
      ring
    -- ‖3^a·(3/2)^s‖ > 0 from the odd numerator 3^{a+s} over 2^s
    have hwpos : 0 < ((3 : ℚ) ^ a * (3 / 2) ^ s).distToNearestInt := by
      refine Rat.distToNearestInt_pos_of_two_pow_mul_odd hs1
        (O := 3 ^ (a + s)) (Int.odd_iff.mp ((Int.odd_iff.mpr (by norm_num)).pow)) ?_
      rw [div_pow]
      have h2s : ((2 : ℚ)) ^ s ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    refine ⟨Nat.one_le_pow _ _ (by norm_num), ?_, ?_, ?_, ?_⟩
    · -- 1 < |q·u|
      rw [hsval, abs_of_pos (by positivity)]
      have h1 : (1 : ℚ) ≤ (3 : ℚ) ^ a := one_le_pow₀ (by norm_num)
      have h2'' : (1 : ℚ) < (3 / 2 : ℚ) ^ s :=
        one_lt_pow₀ (by norm_num) (by omega)
      nlinarith
    · rw [hsval]
      exact CZ.not_intCast_of_distToNearestInt_pos hwpos
    · rw [hsval]
      exact hwpos
    · -- the threshold: ‖q·u‖ ≤ 2^a·θ^c < (3^s)^{-ε}·(3^a)^{-1-ε}
      rw [hsval, CZ.height23_neg_natCast]
      -- reduction ‖3^a(3/2)^s‖ ≤ 2^a·‖(3/2)^c − (3/2)^a‖
      have hw : (3 : ℚ) ^ a * (3 / 2) ^ s
          = ((2 ^ a : ℤ) : ℚ) * ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a)
            + ((3 ^ a : ℤ) : ℚ) := by
        rw [hcas]
        have h2a : ((2 : ℚ)) ^ a ≠ 0 := by positivity
        have h2s : ((2 : ℚ)) ^ s ≠ 0 := by positivity
        rw [div_pow, div_pow, div_pow]
        push_cast
        field_simp
        ring
      have hstep : ((3 : ℚ) ^ a * (3 / 2) ^ s).distToNearestInt
          ≤ 2 ^ a * ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a).distToNearestInt := by
        rw [hw, Rat.distToNearestInt_add_intCast]
        calc (((2 ^ a : ℤ) : ℚ)
            * ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a)).distToNearestInt
            ≤ |((2 ^ a : ℤ) : ℚ)|
              * ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a).distToNearestInt :=
              Rat.distToNearestInt_intCast_mul_le _ _
          _ = 2 ^ a * ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a).distToNearestInt := by
              rw [show |((2 ^ a : ℤ) : ℚ)| = 2 ^ a by
                rw [abs_of_nonneg (by positivity)]; push_cast; ring]
      have hchain : ((3 : ℚ) ^ a * (3 / 2) ^ s).distToNearestInt
          ≤ 2 ^ a * θ ^ c :=
        le_trans hstep (mul_le_mul_of_nonneg_left hdist (by positivity))
      have hcast3s : ((3 ^ s : ℕ) : ℝ) = (3 : ℝ) ^ s := by push_cast; ring
      have hcast3a : ((3 ^ a : ℕ) : ℝ) = (3 : ℝ) ^ a := by push_cast; ring
      rw [hcast3s, hcast3a]
      calc (((3 : ℚ) ^ a * (3 / 2) ^ s).distToNearestInt : ℝ)
          ≤ ((2 ^ a * θ ^ c : ℚ) : ℝ) := by exact_mod_cast hchain
        _ = (2 : ℝ) ^ a * (θ : ℝ) ^ c := by push_cast; ring
        _ < ((3 : ℝ) ^ s) ^ (-(min 1 (Real.log (θ : ℝ)⁻¹ / (4 * Real.log 3))))
            * ((3 : ℝ) ^ a) ^ (-1 - min 1 (Real.log (θ : ℝ)⁻¹ / (4 * Real.log 3))) :=
            hugeGap_window hθ0' hθ1' hε'D (by omega) hs1 hcas
              (by exact_mod_cast hhuge)

end TH

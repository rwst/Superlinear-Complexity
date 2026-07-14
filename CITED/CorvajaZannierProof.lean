/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Data.Set.Finite.Basic
import Mathlib.NumberTheory.Ostrowski
import CITED.CorvajaZannier
import CITED.Ridout



/-!
# Deriving the Corvaja–Zannier Main Theorem from Ridout / the Subspace Theorem

Second step of the one-axiom refactor (`report-formalize-subspace.html` §6):
turn `CZ.pseudoPisot_approx` from a cited `axiom` into a **theorem** resting only
on `Subspace.evertseSchlickewei` (via `Ridout.finite_ratios`).  The `ℚ`,
`δ ∈ ℚ`, `Γ = ⟨2,3⟩` case of the Main Theorem is a single application of
**Ridout's theorem** (`report-formalize-subspace.html` §3), so no new axiom is
needed.

**Status: COMPLETE (2026-07-14).**  `pseudoPisot_approx_of_subspace` below is
**sorry-free** with footprint `std3 + Subspace.evertseSchlickewei`.  The proof:

* *shape reduction* — the pseudo-Pisot exclusion clause only shrinks the
  exceptional set, so finiteness reduces to the pure approximation core;
* *the key cancellation* (`key_num_le`) — on the coprime representative
  `(A, B)` of the orbit ratio `p₀/(q·2^x·3^y)` the Subspace-product numerator
  collapses **exactly** to `‖v‖·A₆′·B₆′/|p₀| ≤ ‖v‖·q` (prime-to-6 parts via
  `ordCompl`; the p-adic factors are computed, never bounded by `1`);
* *Ridout membership* (`orbit_mem_ratios`) — with the height bound
  `M ≤ (|δ|+1)·q·h ≤ (q·h)²` (valid once `q·h ≥ |δ|+1`) and `ε' := ε/2`,
  every good triple's orbit point solves the `S = {∞, 2, 3}` Subspace
  inequality `approxProduct ≤ M^{-2-ε'}`;
* *fibres* (`fibre_finite`, `small_finite`) — on the fibre over a ratio `ρ`,
  `‖v‖ ≥ |δρ − 1| > 0` bounds `height23` and `q`, so each fibre is finite;
  the finitely many small triples (`q·h < |δ|+1`) are absorbed directly.

The bespoke cited axiom `CZ.pseudoPisot_approx` has been **retired** (deleted
from `CITED/CorvajaZannier.lean`, 2026-07-14) and the live consumers in
`TH/GapSlices.lean` repointed to the theorem below — completing the one-axiom
refactor for the CZ side.

## References

* [CZ04] Corvaja–Zannier, Acta Math. **193** (2004), 175–191
  (`CITED/CorvajaZannier.lean` carries the statement vocabulary; the Main
  Theorem is derived below).
* [Rid57] Ridout, Mathematika **4** (1957) (`CITED/Ridout.lean`
  — `Ridout.finite_ratios`, the engine).
* `report-formalize-subspace.html` (this repository, 2026-07): §3 (CZ → Ridout),
  §6 (the one-axiom refactor).
-/

namespace CZ

open Ridout Subspace Rat.AbsoluteValue Height

/-- `2 ^ |x| ≤ height23 x y`: the height dominates the `2`-part of the `S`-unit. -/
private lemma two_pow_natAbs_le_height23 (x y : ℤ) : 2 ^ x.natAbs ≤ height23 x y := by
  unfold height23
  rcases le_total 0 x with hx | hx
  · have hnat : x.natAbs = x.toNat := by omega
    calc 2 ^ x.natAbs = 2 ^ x.toNat := by rw [hnat]
      _ ≤ 2 ^ x.toNat * 3 ^ y.toNat := Nat.le_mul_of_pos_right _ (by positivity)
      _ ≤ _ := le_max_left _ _
  · have hnat : x.natAbs = (-x).toNat := by omega
    calc 2 ^ x.natAbs = 2 ^ (-x).toNat := by rw [hnat]
      _ ≤ 2 ^ (-x).toNat * 3 ^ (-y).toNat := Nat.le_mul_of_pos_right _ (by positivity)
      _ ≤ _ := le_max_right _ _

/-- `3 ^ |y| ≤ height23 x y`: the height dominates the `3`-part of the `S`-unit. -/
private lemma three_pow_natAbs_le_height23 (x y : ℤ) : 3 ^ y.natAbs ≤ height23 x y := by
  unfold height23
  rcases le_total 0 y with hy | hy
  · have hnat : y.natAbs = y.toNat := by omega
    calc 3 ^ y.natAbs = 3 ^ y.toNat := by rw [hnat]
      _ ≤ 2 ^ x.toNat * 3 ^ y.toNat := Nat.le_mul_of_pos_left _ (by positivity)
      _ ≤ _ := le_max_left _ _
  · have hnat : y.natAbs = (-y).toNat := by omega
    calc 3 ^ y.natAbs = 3 ^ (-y).toNat := by rw [hnat]
      _ ≤ 2 ^ (-x).toNat * 3 ^ (-y).toNat := Nat.le_mul_of_pos_left _ (by positivity)
      _ ≤ _ := le_max_right _ _

/-- **Finitely many `S`-unit exponent pairs of bounded height** ([CZ04], ℚ-case):
for any real `B`, only finitely many `(x, y) ∈ ℤ²` have `height23 x y ≤ B`.  This
is the finiteness leaf of the ratios→triples reduction: once Ridout bounds the
height of the `S`-unit `u = 2^x 3^y`, its exponents `(x, y)` are confined to a
box (from `2^{|x|}, 3^{|y|} ≤ height23 x y`). -/
theorem finite_height23_le (B : ℝ) :
    {q : ℤ × ℤ | (height23 q.1 q.2 : ℝ) ≤ B}.Finite := by
  set M : ℕ := ⌊B⌋₊ with hM
  apply Set.Finite.subset
    ((Set.finite_Icc (-(M : ℤ)) M).prod (Set.finite_Icc (-(M : ℤ)) M))
  rintro ⟨x, y⟩ hxy
  simp only [Set.mem_setOf_eq] at hxy
  have hle : height23 x y ≤ M := Nat.le_floor hxy
  have hx2 : 2 ^ x.natAbs ≤ M := le_trans (two_pow_natAbs_le_height23 x y) hle
  have hy3 : 3 ^ y.natAbs ≤ M := le_trans (three_pow_natAbs_le_height23 x y) hle
  have hxb : x.natAbs < M := lt_of_lt_of_le Nat.lt_two_pow_self hx2
  have hyb : y.natAbs < M :=
    lt_of_lt_of_le (lt_of_lt_of_le Nat.lt_two_pow_self
      (Nat.pow_le_pow_left (by norm_num) _)) hy3
  exact Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ⟨by omega, by omega⟩,
    Set.mem_Icc.mpr ⟨by omega, by omega⟩⟩

/-- **Projective height of a rational pair = affine height of the ratio**:
`mulHeight ![a, b] = mulHeight₁ (a / b)` for `b ≠ 0`.  Combined with
`Rat.mulHeight₁_eq_max` this computes the RHS of the Ridout bound for the orbit
point `ξ = ![p₀, q·2^x·3^y]`, namely `mulHeight ξ = max(num, den)` of the ratio
`p₀ / (q·2^x·3^y)`.  (Uses Mathlib's `Height` API for `ℚ`.) -/
theorem mulHeight_pair_eq (a b : ℚ) (hb : b ≠ 0) :
    Height.mulHeight ![a, b] = Height.mulHeight₁ (a / b) := by
  have hsm : ![a, b] = b • ![a / b, 1] := by
    ext i; fin_cases i <;> simp [smul_eq_mul] <;> field_simp
  rw [hsm, Height.mulHeight_smul_eq_mulHeight _ hb, ← Height.mulHeight₁_eq_mulHeight]

/-- **The 2-adic absolute value of the `S`-unit `2^x 3^y` is `2^{-x}`**
(`|·|₂ = Rat.AbsoluteValue.padic 2 = padicNorm 2`).  A finite-place factor of the
Ridout `approxProduct` for the CZ orbit point. -/
theorem padic_two_sUnit (x y : ℤ) :
    padic 2 ((2 : ℚ) ^ x * (3 : ℚ) ^ y) = (2 : ℝ) ^ (-x) := by
  have h2 : padic 2 (2 : ℚ) = (2 : ℝ)⁻¹ := by
    rw [padic_eq_padicNorm, show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num,
      padicNorm.padicNorm_p_of_prime]; norm_num
  have h3q : padicNorm 2 (3 : ℚ) = 1 := by
    rw [show (3 : ℚ) = ((3 : ℤ) : ℚ) by norm_num]
    exact (padicNorm.int_eq_one_iff 3).mpr (by norm_num)
  have h3 : padic 2 (3 : ℚ) = 1 := by rw [padic_eq_padicNorm, h3q]; norm_num
  rw [map_mul, map_zpow₀, map_zpow₀, h2, h3, one_zpow, mul_one, inv_zpow, ← zpow_neg]

/-- **The 3-adic absolute value of the `S`-unit `2^x 3^y` is `3^{-y}`**.  The other
finite-place factor of the Ridout `approxProduct` for the CZ orbit point. -/
theorem padic_three_sUnit (x y : ℤ) :
    padic 3 ((2 : ℚ) ^ x * (3 : ℚ) ^ y) = (3 : ℝ) ^ (-y) := by
  have h3 : padic 3 (3 : ℚ) = (3 : ℝ)⁻¹ := by
    rw [padic_eq_padicNorm, show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num,
      padicNorm.padicNorm_p_of_prime]; norm_num
  have h2q : padicNorm 3 (2 : ℚ) = 1 := by
    rw [show (2 : ℚ) = ((2 : ℤ) : ℚ) by norm_num]
    exact (padicNorm.int_eq_one_iff 2).mpr (by norm_num)
  have h2 : padic 3 (2 : ℚ) = 1 := by rw [padic_eq_padicNorm, h2q]; norm_num
  rw [map_mul, map_zpow₀, map_zpow₀, h2, h3, one_zpow, one_mul, inv_zpow, ← zpow_neg]

/-- **Archimedean form factor**: at the real place, the form `x₀ − δ·x₁` at the CZ
orbit point `ξ = ![round(δ·q·2^x·3^y), q·2^x·3^y]` evaluates to the nearest-integer
distance `‖·‖`, since `x₀ − δ·x₁ = round(sval) − sval`:
`real (round w − w) = distToNearestInt w`. -/
theorem real_round_sub_eq_dist (w : ℚ) :
    real ((round w : ℚ) - w) = (w.distToNearestInt : ℝ) := by
  rw [real_eq_abs, Rat.distToNearestInt, abs_sub_comm]

/-!
### The Subspace product on the coprime-integer representative (the STEP-2 core)

The one genuinely deep obstacle to the CZ derivation was relating the `S = {∞,2,3}`
Subspace product `approxProduct` to Mathlib's `Height.mulHeight`, which is a product over
*all* places of `ℚ` (`InfinitePlace`/`FinitePlace`).  For a general representative of the
orbit point this needs the full product formula over the infinitely many places outside `S`.

The resolution (`report-formalize-subspace.html` §3): evaluate the (scale-invariant)
`approxProduct` and `mulHeight` on the **coprime-integer representative** `![A, B]` of the
projective point.  There every finite local norm is `1` (`coprime_padic_max`), so the
product formula collapses and both sides become elementary:
`mulHeight ![A,B] = max(|A|,|B|)` (`Rat.mulHeight_eq_max_abs_of_gcd_eq_one`) and
`approxProduct` has the closed form of `approxProduct_pair_eq` below.  This discharges the
product-formula step; what remains (`hcore`) is the elementary `M`-bound and fibre count.
-/

attribute [local instance] Classical.propDecidable

/-- The per-place linear forms of the CZ Ridout application: at the real place the pair
`X₀ − δ·X₁, X₁` (so the first form measures `p₀ − δ·qu`, whose size is `‖sval‖`), and at
every other place the coordinate forms `X₀, X₁` (measuring the `p`-adic sizes of the two
coordinates). -/
noncomputable def Lforms (δ : ℚ) (v : AbsoluteValue ℚ ℝ) : Fin 2 → ((Fin 2 → ℚ) →ₗ[ℚ] ℚ) :=
  if v = Rat.AbsoluteValue.real
  then ![LinearMap.proj 0 - δ • LinearMap.proj 1, LinearMap.proj 1]
  else ![LinearMap.proj 0, LinearMap.proj 1]

/-- Both per-place pairs of `Lforms` are linearly independent, so `Lforms` satisfies the
hypothesis of `Ridout.finite_ratios` at every place. -/
lemma lforms_linearIndependent (δ : ℚ) (v : AbsoluteValue ℚ ℝ) :
    LinearIndependent ℚ (Lforms δ v) := by
  unfold Lforms
  by_cases h : v = Rat.AbsoluteValue.real
  · rw [if_pos h, LinearIndependent.pair_iff]
    intro a b hab
    have h1 := LinearMap.congr_fun hab ![1, 0]
    have h2 := LinearMap.congr_fun hab ![0, 1]
    simp at h1 h2
    exact ⟨h1, by rw [h1] at h2; simpa using h2⟩
  · rw [if_neg h, LinearIndependent.pair_iff]
    intro a b hab
    exact ⟨by have := LinearMap.congr_fun hab ![1, 0]; simpa using this,
      by have := LinearMap.congr_fun hab ![0, 1]; simpa using this⟩

/-- The local sup-norm of a pair `‖![a,b]‖_v = max(|a|_v, |b|_v)`. -/
lemma localNorm_pair (v : AbsoluteValue ℚ ℝ) (a b : ℚ) :
    localNorm v ![a, b] = max (v a) (v b) := by
  unfold localNorm
  have hcoe : ∀ i : Fin 2, v (![a, b] i) = ![v a, v b] i := by intro i; fin_cases i <;> simp
  rw [show (⨆ i, v (![a, b] i)) = ⨆ i, ![v a, v b] i from iSup_congr hcoe]
  refine (eq_of_forall_ge_iff ?_).symm
  intro c; simp [ciSup_le_iff, Fin.forall_fin_two]

/-- **Coprimality kills the finite places**: for coprime integers `A, B` and any prime `p`,
`max(|A|_p, |B|_p) = 1`.  This is what collapses the Subspace product formula on the
coprime-integer representative — every non-archimedean local norm is `1`. -/
lemma coprime_padic_max (p : ℕ) [Fact p.Prime] (A B : ℤ) (h : IsCoprime A B) :
    max (padic p (A : ℚ)) (padic p (B : ℚ)) = 1 := by
  have hpp : p.Prime := Fact.out
  have hA1 : padic p (A : ℚ) ≤ 1 := by rw [padic_eq_padicNorm]; exact_mod_cast padicNorm.of_int A
  have hB1 : padic p (B : ℚ) ≤ 1 := by rw [padic_eq_padicNorm]; exact_mod_cast padicNorm.of_int B
  by_cases hAdvd : (p : ℤ) ∣ A
  · have hBndvd : ¬ (p : ℤ) ∣ B := by
      intro hBdvd
      have hu : IsUnit (p : ℤ) := h.isUnit_of_dvd' hAdvd hBdvd
      rw [Int.isUnit_iff] at hu; have := hpp.two_le; omega
    have hB : padic p (B : ℚ) = 1 := by
      rw [padic_eq_padicNorm]; exact_mod_cast (padicNorm.int_eq_one_iff B).mpr hBndvd
    rw [max_eq_right (by rw [hB]; exact hA1)]; exact hB
  · have hA : padic p (A : ℚ) = 1 := by
      rw [padic_eq_padicNorm]; exact_mod_cast (padicNorm.int_eq_one_iff A).mpr hAdvd
    rw [max_eq_left (by rw [hA]; exact hB1)]; exact hA

/-- The real place is distinct from the `2`-adic place (they disagree at `2`). -/
lemma real_ne_padic2 : (Rat.AbsoluteValue.real) ≠ padic 2 := by
  intro h
  have := congrArg (fun v => v (2 : ℚ)) h
  simp only [real_eq_abs] at this
  rw [padic_eq_padicNorm, show (2:ℚ) = ((2:ℕ):ℚ) by norm_num, padicNorm.padicNorm_p_of_prime] at this
  norm_num at this

/-- The real place is distinct from the `3`-adic place (they disagree at `3`). -/
lemma real_ne_padic3 : (Rat.AbsoluteValue.real) ≠ padic 3 := by
  intro h
  have := congrArg (fun v => v (3 : ℚ)) h
  simp only [real_eq_abs] at this
  rw [padic_eq_padicNorm, show (3:ℚ) = ((3:ℕ):ℚ) by norm_num, padicNorm.padicNorm_p_of_prime] at this
  norm_num at this

/-- The `2`-adic and `3`-adic places are distinct (they disagree at `2`). -/
lemma padic2_ne_padic3 : (padic 2) ≠ padic 3 := by
  intro h
  have := congrArg (fun v => v (2 : ℚ)) h
  rw [padic_eq_padicNorm, padic_eq_padicNorm, show (2:ℚ) = ((2:ℕ):ℚ) by norm_num,
    padicNorm.padicNorm_p_of_prime] at this
  have h3 : padicNorm 3 ((2:ℕ):ℚ) = 1 := by
    rw [show ((2:ℕ):ℚ) = ((2:ℤ):ℚ) by norm_num]
    exact (padicNorm.int_eq_one_iff 2).mpr (by norm_num)
  rw [h3] at this; norm_num at this

/-- **The Subspace product on the coprime-integer representative, in closed form.**
For coprime integers `A, B`, the `S = {∞, 2, 3}` double product of `Lforms δ` at the point
`![A, B]` collapses (all finite local norms are `1`, by `coprime_padic_max`) to
`|A − δB|·|B| / max(|A|,|B|)² · |A|₂|B|₂ · |A|₃|B|₃`.  This is the ℚ-specialization of the
Subspace product that the Ridout bound is compared against — the product-formula step
(`report-formalize-subspace.html` §3) already discharged. -/
lemma approxProduct_pair_eq (δ : ℚ) (A B : ℤ) (hAB : IsCoprime A B) :
    approxProduct {Rat.AbsoluteValue.real, padic 2, padic 3} (Lforms δ) ![(A : ℚ), (B : ℚ)]
    = real ((A : ℚ) - δ * B) * real (B : ℚ) / (max (real (A : ℚ)) (real (B : ℚ))) ^ 2
      * (padic 2 (A : ℚ) * padic 2 (B : ℚ))
      * (padic 3 (A : ℚ) * padic 3 (B : ℚ)) := by
  have hLNr : localNorm Rat.AbsoluteValue.real ![(A : ℚ), (B : ℚ)]
      = max (real (A : ℚ)) (real (B : ℚ)) := localNorm_pair _ _ _
  have hLN2 : localNorm (padic 2) ![(A : ℚ), (B : ℚ)] = 1 := by
    rw [localNorm_pair]; exact coprime_padic_max 2 A B hAB
  have hLN3 : localNorm (padic 3) ![(A : ℚ), (B : ℚ)] = 1 := by
    rw [localNorm_pair]; exact coprime_padic_max 3 A B hAB
  unfold approxProduct
  rw [show ({Rat.AbsoluteValue.real, padic 2, padic 3} : Finset (AbsoluteValue ℚ ℝ))
      = insert Rat.AbsoluteValue.real (insert (padic 2) {padic 3}) from rfl,
    Finset.prod_insert (by simp [real_ne_padic2, real_ne_padic3]),
    Finset.prod_insert (by simp [padic2_ne_padic3]), Finset.prod_singleton]
  rw [hLNr, hLN2, hLN3]
  simp only [Lforms, if_true, if_neg real_ne_padic2.symm, if_neg real_ne_padic3.symm,
    Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  ring

/-- **The Ridout engine, wired to the Corvaja–Zannier forms** (sorry-free, resting only on
`Subspace.evertseSchlickewei` via `Ridout.finite_ratios`): for every `ε' > 0` the ratios
`x₁/x₀` of the nonzero rational solutions of the `S = {∞,2,3}` Subspace inequality with forms
`Lforms δ` form a **finite set**.  This is the whole `Subspace → Ridout → CZ-forms` chain,
assembled.  Discharging `hcore` is now exactly: show each good triple's orbit point is one of
these solutions — the `M`-bound `approxProduct ≤ mulHeight^{-2-ε'}` of
`report-formalize-subspace.html` §3, which via `approxProduct_pair_eq` reduces to the
elementary `|A − δB| ≤ max(|A|,|B|)^{-1-ε'}` — and that the fibres of `triple ↦ ratio` are
finite (bounding `height23` and `q`, via `finite_height23_le`). -/
lemma finite_ratios_cz (δ : ℚ) (ε' : ℝ) (hε' : 0 < ε') :
    {r : ℚ | ∃ x : Fin 2 → ℚ, x ≠ 0 ∧ x 0 ≠ 0 ∧ r = x 1 / x 0 ∧
      approxProduct {Rat.AbsoluteValue.real, padic 2, padic 3} (Lforms δ) x
        ≤ Height.mulHeight x ^ (-(2 : ℝ) - ε')}.Finite :=
  Ridout.finite_ratios _ (Lforms δ) (fun v _ => lforms_linearIndependent δ v) ε' hε'

/-!
### STEP 3 tooling — scale invariance and the height bound

Writing `M := mulHeight ![p₀, q·2^x·3^y]` and `Φ := |A|₂|B|₂·|A|₃|B|₃` for the finite-place
factors of `approxProduct_pair_eq`, and using `|A−δB| = B·‖sval‖/(q·2^x·3^y)`, the Subspace
product on the coprime representative is
  `approxProduct = B²·‖sval‖·Φ / (q·2^x·3^y · M²)`.
**Caution (corrected 2026-07-13).** One must *not* bound `Φ ≤ 1` here: that discards the p-adic
gain and the ε-inequality then fails (it would demand `height23^{-1-ε} ≤ height23^{-2-ε'}`).  The
p-adic factor is `Φ = 2^{-|v₂(r)|}·3^{-|v₃(r)|}` (`r = p₀/(q·2^x·3^y)`), which supplies exactly the
missing `1/height23`; `Φ` is *anti-correlated* with `M` (when the `S`-unit cancels into `p₀`,
`Φ → 1` but `M → q`).  So `hkey` needs the p-adic valuations computed, not bounded — the genuine
Corvaja–Zannier content.  **Executed below** (`key_num_le`) via `ordCompl` prime-to-6 parts on
the coprime representative directly: `|m|₂·|m|₃·|m| = m₆′` exactly, and the divisibilities
`A ∣ p₀·2^{x⁻}3^{y⁻}`, `B ∣ q·2^{x⁺}3^{y⁺}` give `A₆′ ≤ |p₀|`, `B₆′ ≤ q`.
`approxProduct_smul` (below) and the polynomial height bound `mulHeight_orbit_le` are retained
as API (the executed route bounds the height linearly inside `orbit_mem_ratios` instead).
-/

/-- The local sup-norm scales by `|c|_v`: `‖c • x‖_v = |c|_v · ‖x‖_v`. -/
lemma localNorm_smul {n : ℕ} (v : AbsoluteValue ℚ ℝ) (c : ℚ) (x : Fin n → ℚ) :
    localNorm v (c • x) = v c * localNorm v x := by
  unfold localNorm
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  rw [Real.mul_iSup_of_nonneg (v.nonneg c)]

/-- **`approxProduct` is scale-invariant** (a projective quantity): `approxProduct S L (c•x) =
approxProduct S L x` for `c ≠ 0`.  This lets the Subspace product be evaluated on the
integer representative `![P,Q]` of the orbit point instead of `![p₀, q·2^x·3^y]`. -/
lemma approxProduct_smul {n : ℕ} (S : Finset (AbsoluteValue ℚ ℝ))
    (L : AbsoluteValue ℚ ℝ → Fin n → ((Fin n → ℚ) →ₗ[ℚ] ℚ)) (c : ℚ) (hc : c ≠ 0)
    (x : Fin n → ℚ) :
    approxProduct S L (c • x) = approxProduct S L x := by
  unfold approxProduct
  refine Finset.prod_congr rfl (fun v _ => Finset.prod_congr rfl (fun i _ => ?_))
  have hvc : v c ≠ 0 := (AbsoluteValue.ne_zero_iff v).mpr hc
  have hL : (L v i) (c • x) = c * (L v i) x := by rw [← smul_eq_mul, ← map_smul]
  rw [localNorm_smul, hL, map_mul]
  exact mul_div_mul_left _ _ hvc

/-!
### STEP 3: the height (`M`-)bound — the orbit point's height is polynomially bounded

`mulHeight_orbit_le` bounds `M = mulHeight ![p₀, q·2^x·3^y] ≤ (|δ|+2)·(q·height23)³`, reached via
Mathlib's `mulHeight₁_mul_le` / `mulHeight₁_zpow` with no gcd bookkeeping.  (This lossy bound is
*not* by itself the key inequality — see the caution above — but it feeds the Northcott
small-`M` case.)
-/

/-- The `S`-unit `2^x·3^y` is bounded by its height `height23`. -/
lemma u_le_height23 (x y : ℤ) : (2 : ℚ) ^ x * (3 : ℚ) ^ y ≤ (height23 x y : ℚ) := by
  have h2 : (2 : ℚ) ^ x ≤ (2 : ℚ) ^ x.toNat := by
    rw [show ((2:ℚ) ^ x.toNat) = (2:ℚ) ^ (x.toNat : ℤ) by rw [zpow_natCast]]
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  have h3 : (3 : ℚ) ^ y ≤ (3 : ℚ) ^ y.toNat := by
    rw [show ((3:ℚ) ^ y.toNat) = (3:ℚ) ^ (y.toNat : ℤ) by rw [zpow_natCast]]
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  calc (2 : ℚ) ^ x * (3 : ℚ) ^ y
      ≤ (2 : ℚ) ^ x.toNat * (3 : ℚ) ^ y.toNat := by gcongr
    _ = ((2 ^ x.toNat * 3 ^ y.toNat : ℕ) : ℚ) := by push_cast; ring
    _ ≤ (height23 x y : ℚ) := by rw [height23]; exact_mod_cast le_max_left _ _

/-- `height23 ≥ 1`. -/
lemma one_le_height23 (x y : ℤ) : 1 ≤ height23 x y := by
  rw [height23]; exact le_max_of_le_left (Nat.one_le_iff_ne_zero.mpr (by positivity))

/-- `2^{|x|}·3^{|y|} ≤ height23²` (the numerator·denominator of the `S`-unit). -/
lemma pow_natAbs_le_height23_sq (x y : ℤ) :
    2 ^ x.natAbs * 3 ^ y.natAbs ≤ (height23 x y) ^ 2 := by
  have hx : x.natAbs = x.toNat + (-x).toNat := by omega
  have hy : y.natAbs = y.toNat + (-y).toNat := by omega
  rw [hx, hy, pow_add, pow_add]
  have e1 : 2 ^ x.toNat * 3 ^ y.toNat ≤ height23 x y := by rw [height23]; exact le_max_left _ _
  have e2 : 2 ^ (-x).toNat * 3 ^ (-y).toNat ≤ height23 x y := by
    rw [height23]; exact le_max_right _ _
  calc 2 ^ x.toNat * 2 ^ (-x).toNat * (3 ^ y.toNat * 3 ^ (-y).toNat)
      = (2 ^ x.toNat * 3 ^ y.toNat) * (2 ^ (-x).toNat * 3 ^ (-y).toNat) := by ring
    _ ≤ height23 x y * height23 x y := Nat.mul_le_mul e1 e2
    _ = (height23 x y) ^ 2 := by ring

/-- The height of the `S`-unit part: `H(2^x·3^y) ≤ height23²`. -/
lemma mulHeight₁_sUnit_le (x y : ℤ) :
    mulHeight₁ ((2:ℚ)^x * (3:ℚ)^y) ≤ ((height23 x y : ℕ) : ℝ) ^ 2 := by
  have hmul : mulHeight₁ ((2:ℚ)^x * (3:ℚ)^y) ≤ mulHeight₁ ((2:ℚ)^x) * mulHeight₁ ((3:ℚ)^y) :=
    mulHeight₁_mul_le _ _
  rw [mulHeight₁_zpow, mulHeight₁_zpow] at hmul
  have h2 : mulHeight₁ (2:ℚ) = 2 := by
    rw [show (2:ℚ) = ((2:ℕ):ℚ) by norm_num]; exact_mod_cast Rat.mulHeight₁_natCast 2
  have h3 : mulHeight₁ (3:ℚ) = 3 := by
    rw [show (3:ℚ) = ((3:ℕ):ℚ) by norm_num]; exact_mod_cast Rat.mulHeight₁_natCast 3
  rw [h2, h3] at hmul
  refine hmul.trans ?_
  calc (2:ℝ) ^ x.natAbs * (3:ℝ) ^ y.natAbs
      = ((2 ^ x.natAbs * 3 ^ y.natAbs : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (((height23 x y) ^ 2 : ℕ) : ℝ) := by exact_mod_cast pow_natAbs_le_height23_sq x y
    _ = ((height23 x y : ℕ) : ℝ) ^ 2 := by push_cast; ring

/-- The height of the denominator side `q·2^x·3^y ≤ q·height23²`. -/
lemma mulHeight₁_qu_le (q : ℕ) (hq : 1 ≤ q) (x y : ℤ) :
    mulHeight₁ ((q:ℚ) * ((2:ℚ)^x * (3:ℚ)^y)) ≤ (q:ℝ) * ((height23 x y : ℕ) : ℝ) ^ 2 := by
  haveI : NeZero q := ⟨by omega⟩
  have hqh : mulHeight₁ ((q:ℚ)) = (q:ℝ) := Rat.mulHeight₁_natCast q
  calc mulHeight₁ ((q:ℚ) * ((2:ℚ)^x * (3:ℚ)^y))
      ≤ mulHeight₁ ((q:ℚ)) * mulHeight₁ ((2:ℚ)^x * (3:ℚ)^y) := mulHeight₁_mul_le _ _
    _ = (q:ℝ) * mulHeight₁ ((2:ℚ)^x * (3:ℚ)^y) := by rw [hqh]
    _ ≤ (q:ℝ) * ((height23 x y : ℕ) : ℝ) ^ 2 := by gcongr; exact mulHeight₁_sUnit_le x y

/-- The height of the numerator side `p₀ = round(sval) ≤ (|δ|+2)·q·height23`
(from `|round w| ≤ |w| + ½` and `2^x·3^y ≤ height23`). -/
lemma mulHeight₁_p0_le (δ : ℚ) (q : ℕ) (hq : 1 ≤ q) (x y : ℤ) :
    mulHeight₁ ((round (sval δ q x y) : ℤ) : ℚ) ≤ (|δ| + 2) * q * (height23 x y : ℝ) := by
  set w := sval δ q x y with hw
  rw [Rat.cast_abs]
  have hmh : mulHeight₁ ((round w : ℤ) : ℚ) = max ((round w).natAbs : ℝ) 1 := by
    rw [Rat.mulHeight₁_eq_max]; simp [Rat.num_intCast, Rat.den_intCast, Nat.cast_max]
  rw [hmh]
  have hroundQ : |((round w : ℤ) : ℚ)| ≤ |w| + 1/2 := by
    have h := abs_sub_round w
    have h2 := abs_sub_abs_le_abs_sub ((round w : ℤ) : ℚ) w
    rw [abs_sub_comm] at h2; linarith
  have hround : |((round w : ℤ) : ℝ)| ≤ |(w : ℝ)| + 1/2 := by
    have h : ((|((round w : ℤ) : ℚ)| : ℚ) : ℝ) ≤ ((|w| + 1/2 : ℚ) : ℝ) := Rat.cast_le.mpr hroundQ
    push_cast at h; exact h
  have hu : (2:ℝ)^x * (3:ℝ)^y ≤ (height23 x y : ℝ) := by
    calc (2:ℝ)^x*(3:ℝ)^y = (((2:ℚ)^x*(3:ℚ)^y : ℚ) : ℝ) := by push_cast; ring
      _ ≤ ((height23 x y : ℚ) : ℝ) := by exact_mod_cast u_le_height23 x y
      _ = (height23 x y : ℝ) := by push_cast; ring
  have hwabs : |(w : ℝ)| ≤ |(δ:ℝ)| * q * (height23 x y : ℝ) := by
    have hexp : (0:ℝ) < (2:ℝ)^x * (3:ℝ)^y := by positivity
    have hcast : (w : ℝ) = (δ : ℝ) * q * ((2:ℝ)^x * (3:ℝ)^y) := by rw [hw, sval]; push_cast; ring
    rw [hcast, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (q:ℝ)), abs_of_pos hexp]
    gcongr
  have hnatabs : ((round w).natAbs : ℝ) = |((round w : ℤ) : ℝ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  have hmax : max ((round w).natAbs : ℝ) 1 ≤ ((round w).natAbs : ℝ) + 1 := by
    have : (0:ℝ) ≤ ((round w).natAbs : ℝ) := by positivity
    exact max_le (by linarith) (by linarith)
  have hh1 : (1:ℝ) ≤ (height23 x y : ℝ) := by exact_mod_cast one_le_height23 x y
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  calc max ((round w).natAbs : ℝ) 1
      ≤ ((round w).natAbs : ℝ) + 1 := hmax
    _ = |((round w : ℤ) : ℝ)| + 1 := by rw [hnatabs]
    _ ≤ (|(δ:ℝ)| * q * (height23 x y : ℝ) + 1/2) + 1 := by linarith
    _ ≤ (|(δ:ℝ)| + 2) * q * (height23 x y : ℝ) := by
        have hqh : (1:ℝ) ≤ (q:ℝ) * (height23 x y : ℝ) :=
          hq1.trans (le_mul_of_one_le_right (by positivity) hh1)
        have hexp : (|(δ:ℝ)| + 2) * q * (height23 x y : ℝ)
            = |(δ:ℝ)| * q * (height23 x y : ℝ) + 2 * ((q:ℝ) * (height23 x y : ℝ)) := by ring
        rw [hexp]; linarith

/-- **The orbit point's projective height is polynomially bounded** by `q·height23`:
`mulHeight ![p₀, q·2^x·3^y] ≤ (|δ|+2)·(q·height23)³`, where `p₀ = round(sval δ q x y)`.  This
is the `M`-bound of `report-formalize-subspace.html` §3 — lossy but polynomial, which is all the
ε-juggling needs (`ε' < ε/3`).  It combines the numerator/denominator height factors
(`mulHeight₁_p0_le`, `mulHeight₁_qu_le`) via `mulHeight₁_mul_le`, sidestepping the gcd/coprime
reduction entirely. -/
lemma mulHeight_orbit_le (δ : ℚ) (q : ℕ) (hq : 1 ≤ q) (x y : ℤ) :
    mulHeight ![((round (sval δ q x y) : ℤ) : ℚ), (q:ℚ) * ((2:ℚ)^x * (3:ℚ)^y)]
      ≤ (|δ| + 2) * ((q:ℝ) * (height23 x y : ℝ)) ^ 3 := by
  set p₀ : ℚ := ((round (sval δ q x y) : ℤ) : ℚ) with hp₀
  set qu : ℚ := (q:ℚ) * ((2:ℚ)^x * (3:ℚ)^y) with hqu
  have hprod : mulHeight ![p₀, qu] ≤ mulHeight₁ p₀ * mulHeight₁ qu := by
    rw [← mulHeight₁_div_eq_mulHeight, div_eq_mul_inv]
    exact (mulHeight₁_mul_le _ _).trans (le_of_eq (by rw [mulHeight₁_inv]))
  have hp0 := mulHeight₁_p0_le δ q hq x y
  have hqub := mulHeight₁_qu_le q hq x y
  have hh1 : (1:ℝ) ≤ (height23 x y : ℝ) := by exact_mod_cast one_le_height23 x y
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  refine hprod.trans (le_trans (mul_le_mul hp0 hqub (by positivity) (by positivity)) ?_)
  have hqh0 : (0:ℝ) ≤ (q:ℝ) * (height23 x y : ℝ) := by positivity
  have hδ : (0:ℝ) ≤ |δ| + 2 := by positivity
  nlinarith [mul_nonneg hqh0 hqh0, hq1, hh1, sq_nonneg ((q:ℝ)*(height23 x y:ℝ)),
    mul_le_mul_of_nonneg_left hq1 (mul_nonneg hδ (mul_nonneg hqh0 hqh0))]

/-!
### STEP 3, the `hkey` cancellation: prime-to-6 parts and the exact p-adic identity

The p-adic factors of the Subspace product are **computed exactly** (see the caution above):
for a nonzero integer `m`, `|m|₂·|m|₃·|m| = m₆′`, the prime-to-6 part of `m`
(`padic_mul_padic_natAbs`).  Together with the divisibilities `A ∣ p₀·D`, `B ∣ q·N`
(`D = 2^{x⁻}3^{y⁻}`, `N = 2^{x⁺}3^{y⁺}`) of the coprime representative, the Subspace-product
numerator collapses **exactly** to `‖v‖·A₆′·B₆′/|p₀| ≤ ‖v‖·q` (`key_num_le`) — this is the
Corvaja–Zannier cancellation, where the `1/height23` earned by the `S`-unit denominator is
supplied by the p-adic places.
-/

/-- The prime-to-6 part of a natural number: divide out all factors `2` and `3`. -/
private def sixCompl (n : ℕ) : ℕ := ordCompl[3] (ordCompl[2] n)

private lemma sixCompl_pos {n : ℕ} (hn : n ≠ 0) : 0 < sixCompl n :=
  Nat.ordCompl_pos 3 (Nat.ordCompl_pos 2 hn).ne'

private lemma sixCompl_le (n : ℕ) : sixCompl n ≤ n :=
  le_trans (Nat.ordCompl_le _ 3) (Nat.ordCompl_le n 2)

private lemma sixCompl_dvd_sixCompl {m n : ℕ} (h : m ∣ n) : sixCompl m ∣ sixCompl n :=
  Nat.ordCompl_dvd_ordCompl_of_dvd (Nat.ordCompl_dvd_ordCompl_of_dvd h 2) 3

private lemma ordCompl_two_pow_three (b : ℕ) : ordCompl[2] (3 ^ b) = 3 ^ b := by
  refine (Nat.ordCompl_eq_self_iff_zero_or_not_dvd _ Nat.prime_two).mpr (Or.inr ?_)
  intro h
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
  norm_num at this

private lemma sixCompl_mul_pow23 (n a b : ℕ) : sixCompl (n * (2 ^ a * 3 ^ b)) = sixCompl n := by
  unfold sixCompl
  rw [Nat.ordCompl_mul, Nat.ordCompl_mul (2 ^ a), Nat.ordCompl_self_pow Nat.prime_two,
    one_mul, ordCompl_two_pow_three, Nat.ordCompl_mul, Nat.ordCompl_self_pow Nat.prime_three,
    mul_one]

private lemma sixCompl_le_of_dvd_mul {m n : ℕ} (a b : ℕ) (hn : n ≠ 0)
    (h : m ∣ n * (2 ^ a * 3 ^ b)) : sixCompl m ≤ n :=
  le_trans (Nat.le_of_dvd (sixCompl_pos hn)
    ((sixCompl_mul_pow23 n a b) ▸ sixCompl_dvd_sixCompl h)) (sixCompl_le n)

private lemma padic_int_zpow (p : ℕ) [Fact p.Prime] (m : ℤ) (hm : m ≠ 0) :
    padic p (m : ℚ) = (p : ℝ) ^ (-(padicValNat p m.natAbs : ℤ)) := by
  rw [padic_eq_padicNorm,
    padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hm), padicValRat.of_int]
  push_cast [padicValInt]
  norm_num

/-- The exact p-adic identity: `|m|₂ · |m|₃ · |m| = m₆′`, the prime-to-6 part of `m`. -/
private lemma padic_mul_padic_natAbs (m : ℤ) (hm : m ≠ 0) :
    padic 2 (m : ℚ) * padic 3 (m : ℚ) * (m.natAbs : ℝ) = (sixCompl m.natAbs : ℝ) := by
  set n := m.natAbs with hndef
  have hn0 : n ≠ 0 := Int.natAbs_ne_zero.mpr hm
  set a := n.factorization 2 with hadef
  set b := n.factorization 3 with hbdef
  have hva : padicValNat 2 n = a := (Nat.factorization_def n Nat.prime_two).symm
  have hvb : padicValNat 3 n = b := (Nat.factorization_def n Nat.prime_three).symm
  -- decomposition n = 2^a * (3^b * sixCompl n)
  have hd2 : 2 ^ a * ordCompl[2] n = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hb' : (ordCompl[2] n).factorization 3 = b := by
    rw [Nat.factorization_ordCompl, Finsupp.erase_ne (by norm_num : (3 : ℕ) ≠ 2)]
  have hd3 : 3 ^ b * sixCompl n = ordCompl[2] n := by
    conv_lhs => rw [← hb']
    exact Nat.ordProj_mul_ordCompl_eq_self (ordCompl[2] n) 3
  have hn_eq : n = 2 ^ a * (3 ^ b * sixCompl n) := by rw [hd3, hd2]
  rw [padic_int_zpow 2 m hm, padic_int_zpow 3 m hm, hva, hvb]
  rw [show ((n : ℝ)) = ((2 ^ a * (3 ^ b * sixCompl n) : ℕ) : ℝ) from by rw [← hn_eq]]
  push_cast
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
  have h2 : ((2 : ℝ) ^ a) ≠ 0 := by positivity
  have h3 : ((3 : ℝ) ^ b) ≠ 0 := by positivity
  field_simp

/-! ### Round of a value of modulus `> 1` is nonzero -/

private lemma round_ne_zero_of_one_lt_abs {w : ℚ} (h : 1 < |w|) : round w ≠ 0 := by
  intro h0
  have h1 := abs_sub_round w
  rw [h0] at h1
  simp only [Int.cast_zero, sub_zero] at h1
  linarith

/-! ### The key numerator bound -/

/-- **The Corvaja–Zannier cancellation**: for the coprime representative `(A, B)` of the
orbit ratio `p₀/(q·2^x·3^y)`, the Subspace-product numerator collapses to
`‖v‖·A₆′·B₆′/|p₀| ≤ ‖v‖·q`.  The p-adic factors are *computed* (via the prime-to-6 parts),
not bounded by `1`. -/
private lemma key_num_le (δ : ℚ) (q : ℕ) (hq : 1 ≤ q) (x y : ℤ) (A B : ℤ)
    (hA : A ≠ 0) (hB : 0 < B)
    (hcross : (A : ℚ) * ((q : ℚ) * ((2 : ℚ) ^ x * (3 : ℚ) ^ y))
      = (B : ℚ) * ((round (sval δ q x y) : ℤ) : ℚ))
    (hAdvd : A.natAbs ∣ (round (sval δ q x y)).natAbs * (2 ^ (-x).toNat * 3 ^ (-y).toNat))
    (hBdvd : B.natAbs ∣ q * (2 ^ x.toNat * 3 ^ y.toNat))
    (hp₀ : round (sval δ q x y) ≠ 0) :
    real ((A : ℚ) - δ * (B : ℚ)) * real ((B : ℤ) : ℚ)
      * (padic 2 (A : ℚ) * padic 2 (B : ℚ)) * (padic 3 (A : ℚ) * padic 3 (B : ℚ))
      ≤ ((sval δ q x y).distToNearestInt : ℝ) * q := by
  set v := sval δ q x y with hvdef
  set p₀ := round v with hp₀def
  set u : ℚ := (2 : ℚ) ^ x * (3 : ℚ) ^ y with hudef
  have hu0 : (0 : ℚ) < u := by positivity
  have hq0 : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hqu0 : (0 : ℚ) < (q : ℚ) * u := mul_pos hq0 hu0
  have hBQ : (0 : ℚ) < (B : ℚ) := by exact_mod_cast hB
  -- six-part bounds
  have ha6 : sixCompl A.natAbs ≤ p₀.natAbs :=
    sixCompl_le_of_dvd_mul _ _ (Int.natAbs_ne_zero.mpr hp₀) hAdvd
  have hb6 : sixCompl B.natAbs ≤ q :=
    sixCompl_le_of_dvd_mul _ _ (by omega) hBdvd
  -- exact p-adic identities
  have hA6 := padic_mul_padic_natAbs A hA
  have hB6 := padic_mul_padic_natAbs B hB.ne'
  -- archimedean identity (in ℚ): |A − δB| · (q·u) = B · ‖v‖
  have harch : |(A : ℚ) - δ * B| * ((q : ℚ) * u) = (B : ℚ) * v.distToNearestInt := by
    have hveq : v = δ * ((q : ℚ) * u) := by rw [hvdef, sval, hudef]; ring
    have h1 : ((A : ℚ) - δ * B) * ((q : ℚ) * u) = (B : ℚ) * ((p₀ : ℚ) - v) := by
      calc ((A : ℚ) - δ * B) * ((q : ℚ) * u)
          = (A : ℚ) * ((q : ℚ) * u) - (B : ℚ) * (δ * ((q : ℚ) * u)) := by ring
        _ = (B : ℚ) * (p₀ : ℚ) - (B : ℚ) * v := by rw [hcross, ← hveq]
        _ = (B : ℚ) * ((p₀ : ℚ) - v) := by ring
    calc |(A : ℚ) - δ * B| * ((q : ℚ) * u)
        = |((A : ℚ) - δ * B) * ((q : ℚ) * u)| := by rw [abs_mul, abs_of_pos hqu0]
      _ = |(B : ℚ) * ((p₀ : ℚ) - v)| := by rw [h1]
      _ = (B : ℚ) * |v - (p₀ : ℚ)| := by rw [abs_mul, abs_of_pos hBQ, abs_sub_comm]
      _ = (B : ℚ) * v.distToNearestInt := by rw [Rat.distToNearestInt, ← hp₀def]
  -- |A| cross identity (in ℚ): |A| · (q·u) = B · |p₀|
  have hcrossAbs : (A.natAbs : ℚ) * ((q : ℚ) * u) = (B : ℚ) * (p₀.natAbs : ℚ) := by
    have h2 := congrArg abs hcross
    rw [abs_mul (A : ℚ), abs_mul (B : ℚ), abs_of_pos hqu0, abs_of_pos hBQ] at h2
    have hAabs : |(A : ℚ)| = (A.natAbs : ℚ) := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    have hPabs : |((p₀ : ℤ) : ℚ)| = (p₀.natAbs : ℚ) := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    rw [hAabs, hPabs] at h2
    exact h2
  -- move to ℝ: push everything into the common `push_cast` normal form
  have hd0 : (0 : ℝ) ≤ (v.distToNearestInt : ℝ) := by
    exact_mod_cast v.distToNearestInt_nonneg
  have hα0 : (0 : ℝ) < (A.natAbs : ℝ) := by
    exact_mod_cast Int.natAbs_pos.mpr hA
  have hu0R : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu0
  have hq0R : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hBR : (0 : ℝ) < ((B : ℤ) : ℝ) := by exact_mod_cast hB
  have hBZ : (B.natAbs : ℤ) = B := Int.natAbs_of_nonneg hB.le
  have hBcast : ((B.natAbs : ℕ) : ℝ) = ((B : ℤ) : ℝ) := by
    conv_rhs => rw [← hBZ]
    rw [Int.cast_natCast]
  have F1 : |(A : ℝ) - (δ : ℝ) * ((B : ℤ) : ℝ)| * ((q : ℝ) * (u : ℝ))
      = ((B : ℤ) : ℝ) * (v.distToNearestInt : ℝ) := by
    exact_mod_cast harch
  have F2 : ((A.natAbs : ℕ) : ℝ) * ((q : ℝ) * (u : ℝ))
      = ((B : ℤ) : ℝ) * ((p₀.natAbs : ℕ) : ℝ) := by
    have h := congrArg (fun z : ℚ => (z : ℝ)) hcrossAbs
    push_cast at h
    exact h
  rw [hBcast] at hB6
  -- assemble
  rw [real_eq_abs, real_eq_abs]
  push_cast
  rw [abs_of_pos hBR]
  refine le_of_mul_le_mul_right ?_ (mul_pos hα0 (mul_pos hq0R hu0R))
  calc |(A : ℝ) - (δ : ℝ) * (B : ℝ)| * (B : ℝ)
        * (padic 2 (A : ℚ) * padic 2 (B : ℚ)) * (padic 3 (A : ℚ) * padic 3 (B : ℚ))
        * ((A.natAbs : ℝ) * ((q : ℝ) * (u : ℝ)))
      = (|(A : ℝ) - (δ : ℝ) * (B : ℝ)| * ((q : ℝ) * (u : ℝ)))
        * ((padic 2 (A : ℚ) * padic 3 (A : ℚ)) * (A.natAbs : ℝ))
        * ((padic 2 (B : ℚ) * padic 3 (B : ℚ)) * (B : ℝ)) := by ring
    _ = ((B : ℝ) * (v.distToNearestInt : ℝ))
        * (sixCompl A.natAbs : ℝ) * (sixCompl B.natAbs : ℝ) := by
        rw [F1, hA6, hB6]
    _ ≤ ((B : ℝ) * (v.distToNearestInt : ℝ)) * (p₀.natAbs : ℝ) * (q : ℝ) := by
        have h6a : (sixCompl A.natAbs : ℝ) ≤ (p₀.natAbs : ℝ) := by exact_mod_cast ha6
        have h6b : (sixCompl B.natAbs : ℝ) ≤ (q : ℝ) := by exact_mod_cast hb6
        have hBd : (0 : ℝ) ≤ (B : ℝ) * (v.distToNearestInt : ℝ) :=
          mul_nonneg hBR.le hd0
        have h6b0 : (0 : ℝ) ≤ (sixCompl B.natAbs : ℝ) := by positivity
        have hP0 : (0 : ℝ) ≤ (p₀.natAbs : ℝ) := by positivity
        exact mul_le_mul (mul_le_mul_of_nonneg_left h6a hBd) h6b h6b0
          (mul_nonneg hBd hP0)
    _ = ((v.distToNearestInt : ℝ) * (q : ℝ)) * ((B : ℝ) * (p₀.natAbs : ℝ)) := by ring
    _ = ((v.distToNearestInt : ℝ) * (q : ℝ)) * ((A.natAbs : ℝ) * ((q : ℝ) * (u : ℝ))) := by
        rw [← F2]


/-! ### The orbit point solves the Ridout inequality (`hkey`, assembled) -/

/-- **The Ridout membership of the orbit point** — the `hkey` inequality of
`report-formalize-subspace.html` §3, discharged: for every good triple `(q, x, y)` with
`q·height23 ≥ |δ| + 1`, the coprime representative `![A, B]` of the orbit point
`[p₀ : q·2^x·3^y]` (`p₀ = round(sval)`) solves the `S = {∞, 2, 3}` Subspace inequality
`approxProduct ≤ mulHeight^{-2-ε/2}`, so its ratio `q·2^x·3^y/p₀` lies in the finite ratio set
of `finite_ratios_cz δ (ε/2)`.  Combines `key_num_le` (the exact p-adic cancellation), the
linear height bound `M ≤ (|δ|+1)·q·h ≤ (q·h)²`, and the approximation hypothesis
`‖v‖ < h^{-ε}·q^{-1-ε}`. -/
lemma orbit_mem_ratios (δ : ℚ) (ε : ℝ) (hε : 0 < ε) (q : ℕ) (x y : ℤ) (hq : 1 ≤ q)
    (hv1 : 1 < |sval δ q x y|)
    (hlt : ((sval δ q x y).distToNearestInt : ℝ)
      < (height23 x y : ℝ) ^ (-ε) * (q : ℝ) ^ (-1 - ε))
    (hlarge : |(δ : ℝ)| + 1 ≤ (q : ℝ) * (height23 x y : ℝ)) :
    ((q : ℚ) * ((2 : ℚ) ^ x * (3 : ℚ) ^ y)) / ((round (sval δ q x y) : ℤ) : ℚ) ∈
      {r : ℚ | ∃ x' : Fin 2 → ℚ, x' ≠ 0 ∧ x' 0 ≠ 0 ∧ r = x' 1 / x' 0 ∧
        approxProduct {Rat.AbsoluteValue.real, padic 2, padic 3} (Lforms δ) x'
          ≤ mulHeight x' ^ (-(2 : ℝ) - ε / 2)} := by
  set v := sval δ q x y with hvdef
  set p₀ := round v with hp₀def
  have hp₀ : p₀ ≠ 0 := round_ne_zero_of_one_lt_abs hv1
  set u : ℚ := (2 : ℚ) ^ x * (3 : ℚ) ^ y with hudef
  have hu0 : (0 : ℚ) < u := by positivity
  have hq0 : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hqu0 : (0 : ℚ) < (q : ℚ) * u := mul_pos hq0 hu0
  set r : ℚ := ((p₀ : ℤ) : ℚ) / ((q : ℚ) * u) with hrdef
  have hr0 : r ≠ 0 := div_ne_zero (Int.cast_ne_zero.mpr hp₀) hqu0.ne'
  set A : ℤ := r.num with hAdef
  set B : ℤ := (r.den : ℤ) with hBdef
  have hA : A ≠ 0 := Rat.num_ne_zero.mpr hr0
  have hB : 0 < B := by
    rw [hBdef]
    exact_mod_cast Nat.pos_of_ne_zero r.den_nz
  have hAB : IsCoprime A B := by
    rw [Int.isCoprime_iff_gcd_eq_one, hAdef, hBdef]
    simpa [Int.gcd, Int.natAbs_natCast] using r.reduced
  have hAeq : (A : ℚ) / ((B : ℤ) : ℚ) = r := by
    rw [hAdef, hBdef]
    push_cast
    exact r.num_div_den
  -- the cross identity in ℚ
  have hcross : (A : ℚ) * ((q : ℚ) * u) = ((B : ℤ) : ℚ) * ((p₀ : ℤ) : ℚ) := by
    have h : (A : ℚ) / ((B : ℤ) : ℚ) = ((p₀ : ℤ) : ℚ) / ((q : ℚ) * u) := by
      rw [hAeq, hrdef]
    rw [div_eq_div_iff (Int.cast_ne_zero.mpr hB.ne') hqu0.ne'] at h
    linear_combination h
  -- the S-unit denominator/numerator identity  u·D = N
  have hND : u * ((2 ^ (-x).toNat * 3 ^ (-y).toNat : ℕ) : ℚ)
      = ((2 ^ x.toNat * 3 ^ y.toNat : ℕ) : ℚ) := by
    push_cast
    rw [hudef,
      show ((2 : ℚ) ^ ((-x).toNat)) = (2 : ℚ) ^ (((-x).toNat : ℤ)) from (zpow_natCast _ _).symm,
      show ((3 : ℚ) ^ ((-y).toNat)) = (3 : ℚ) ^ (((-y).toNat : ℤ)) from (zpow_natCast _ _).symm,
      show ((2 : ℚ) ^ (x.toNat)) = (2 : ℚ) ^ ((x.toNat : ℤ)) from (zpow_natCast _ _).symm,
      show ((3 : ℚ) ^ (y.toNat)) = (3 : ℚ) ^ ((y.toNat : ℤ)) from (zpow_natCast _ _).symm,
      mul_mul_mul_comm, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0),
      ← zpow_add₀ (by norm_num : (3 : ℚ) ≠ 0),
      show x + ((-x).toNat : ℤ) = (x.toNat : ℤ) by omega,
      show y + ((-y).toNat : ℤ) = (y.toNat : ℤ) by omega]
  -- the cross identity in ℤ
  have hcrossZ : A * ((q : ℤ) * ((2 ^ x.toNat * 3 ^ y.toNat : ℕ) : ℤ))
      = B * (p₀ * ((2 ^ (-x).toNat * 3 ^ (-y).toNat : ℕ) : ℤ)) := by
    have h2 : (A : ℚ) * ((q : ℚ) * ((2 ^ x.toNat * 3 ^ y.toNat : ℕ) : ℚ))
        = ((B : ℤ) : ℚ) * (((p₀ : ℤ) : ℚ) * ((2 ^ (-x).toNat * 3 ^ (-y).toNat : ℕ) : ℚ)) := by
      calc (A : ℚ) * ((q : ℚ) * ((2 ^ x.toNat * 3 ^ y.toNat : ℕ) : ℚ))
          = (A : ℚ) * ((q : ℚ) * (u * ((2 ^ (-x).toNat * 3 ^ (-y).toNat : ℕ) : ℚ))) := by
            rw [hND]
        _ = ((A : ℚ) * ((q : ℚ) * u)) * ((2 ^ (-x).toNat * 3 ^ (-y).toNat : ℕ) : ℚ) := by
            ring
        _ = (((B : ℤ) : ℚ) * ((p₀ : ℤ) : ℚ)) * ((2 ^ (-x).toNat * 3 ^ (-y).toNat : ℕ) : ℚ) := by
            rw [hcross]
        _ = ((B : ℤ) : ℚ) * (((p₀ : ℤ) : ℚ) * ((2 ^ (-x).toNat * 3 ^ (-y).toNat : ℕ) : ℚ)) := by
            ring
    exact_mod_cast h2
  -- divisibilities
  have hAdvdZ : A ∣ p₀ * ((2 ^ (-x).toNat * 3 ^ (-y).toNat : ℕ) : ℤ) :=
    hAB.dvd_of_dvd_mul_left
      ⟨(q : ℤ) * ((2 ^ x.toNat * 3 ^ y.toNat : ℕ) : ℤ), hcrossZ.symm⟩
  have hBdvdZ : B ∣ (q : ℤ) * ((2 ^ x.toNat * 3 ^ y.toNat : ℕ) : ℤ) :=
    hAB.symm.dvd_of_dvd_mul_left
      ⟨p₀ * ((2 ^ (-x).toNat * 3 ^ (-y).toNat : ℕ) : ℤ), hcrossZ⟩
  have hAdvdN : A.natAbs ∣ p₀.natAbs * (2 ^ (-x).toNat * 3 ^ (-y).toNat) := by
    have h := Int.natAbs_dvd_natAbs.mpr hAdvdZ
    rwa [Int.natAbs_mul, Int.natAbs_natCast] at h
  have hBdvdN : B.natAbs ∣ q * (2 ^ x.toNat * 3 ^ y.toNat) := by
    have h := Int.natAbs_dvd_natAbs.mpr hBdvdZ
    rwa [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast] at h
  -- the key numerator bound
  have hnum := key_num_le δ q hq x y A B hA hB hcross hAdvdN hBdvdN hp₀
  -- size bounds for the height
  have hNleh : (2 ^ x.toNat * 3 ^ y.toNat : ℕ) ≤ height23 x y := by
    rw [height23]; exact le_max_left _ _
  have hDleh : (2 ^ (-x).toNat * 3 ^ (-y).toNat : ℕ) ≤ height23 x y := by
    rw [height23]; exact le_max_right _ _
  have hh1 : (1 : ℚ) ≤ (height23 x y : ℚ) := by exact_mod_cast one_le_height23 x y
  have hq1 : (1 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hp₀le : (p₀.natAbs : ℚ) ≤ |δ| * ((q : ℚ) * u) + 1 / 2 := by
    have habs : ((p₀.natAbs : ℕ) : ℚ) = |((p₀ : ℤ) : ℚ)| := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    have h1 : |((p₀ : ℤ) : ℚ)| ≤ |v| + 1 / 2 := by
      have h := abs_sub_round v
      have h2 := abs_sub_abs_le_abs_sub ((round v : ℤ) : ℚ) v
      rw [abs_sub_comm] at h2
      rw [hp₀def]
      linarith
    have hveq : |v| = |δ| * ((q : ℚ) * u) := by
      rw [hvdef, sval, ← hudef]
      rw [show δ * (q : ℚ) * u = δ * ((q : ℚ) * u) from by ring, abs_mul,
        abs_of_pos hqu0]
    rw [habs]
    linarith
  have hAsize : (A.natAbs : ℚ)
      ≤ (p₀.natAbs : ℚ) * ((2 ^ (-x).toNat * 3 ^ (-y).toNat : ℕ) : ℚ) := by
    have h := Nat.le_of_dvd
      (Nat.mul_pos (Int.natAbs_pos.mpr hp₀) (by positivity)) hAdvdN
    exact_mod_cast h
  have hBsize : (B.natAbs : ℚ) ≤ (q : ℚ) * ((2 ^ x.toNat * 3 ^ y.toNat : ℕ) : ℚ) := by
    have h := Nat.le_of_dvd (Nat.mul_pos (by omega) (by positivity)) hBdvdN
    exact_mod_cast h
  -- M ≤ (|δ|+1)·q·h in ℚ
  have hMQ : ((max r.num.natAbs r.den : ℕ) : ℚ)
      ≤ (|δ| + 1) * ((q : ℚ) * (height23 x y : ℚ)) := by
    rw [Nat.cast_max]
    have hNQ : ((2 ^ x.toNat * 3 ^ y.toNat : ℕ) : ℚ) ≤ (height23 x y : ℚ) := by
      exact_mod_cast hNleh
    have hDQ : ((2 ^ (-x).toNat * 3 ^ (-y).toNat : ℕ) : ℚ) ≤ (height23 x y : ℚ) := by
      exact_mod_cast hDleh
    have hD0 : (0 : ℚ) ≤ ((2 ^ (-x).toNat * 3 ^ (-y).toNat : ℕ) : ℚ) := by positivity
    apply max_le
    · calc (r.num.natAbs : ℚ)
          ≤ (p₀.natAbs : ℚ) * ((2 ^ (-x).toNat * 3 ^ (-y).toNat : ℕ) : ℚ) := hAsize
        _ ≤ (|δ| * ((q : ℚ) * u) + 1 / 2) * ((2 ^ (-x).toNat * 3 ^ (-y).toNat : ℕ) : ℚ) :=
            mul_le_mul_of_nonneg_right hp₀le hD0
        _ = |δ| * (q : ℚ) * (u * ((2 ^ (-x).toNat * 3 ^ (-y).toNat : ℕ) : ℚ))
            + ((2 ^ (-x).toNat * 3 ^ (-y).toNat : ℕ) : ℚ) / 2 := by ring
        _ = |δ| * (q : ℚ) * ((2 ^ x.toNat * 3 ^ y.toNat : ℕ) : ℚ)
            + ((2 ^ (-x).toNat * 3 ^ (-y).toNat : ℕ) : ℚ) / 2 := by rw [hND]
        _ ≤ |δ| * (q : ℚ) * (height23 x y : ℚ) + (height23 x y : ℚ) / 2 := by
            gcongr
        _ ≤ (|δ| + 1) * ((q : ℚ) * (height23 x y : ℚ)) := by
            have hqh_h : (height23 x y : ℚ) ≤ (q : ℚ) * (height23 x y : ℚ) :=
              le_mul_of_one_le_left (by linarith) hq1
            nlinarith [hqh_h]
    · calc (r.den : ℚ) = (B.natAbs : ℚ) := by rw [hBdef, Int.natAbs_natCast]
        _ ≤ (q : ℚ) * ((2 ^ x.toNat * 3 ^ y.toNat : ℕ) : ℚ) := hBsize
        _ ≤ (q : ℚ) * (height23 x y : ℚ) := by gcongr
        _ ≤ (|δ| + 1) * ((q : ℚ) * (height23 x y : ℚ)) := by
            refine le_mul_of_one_le_left ?_ ?_
            · positivity
            · linarith [abs_nonneg δ]
  -- cast the M-bound to ℝ and square it
  have hMR : ((max r.num.natAbs r.den : ℕ) : ℝ)
      ≤ (|(δ : ℝ)| + 1) * ((q : ℝ) * (height23 x y : ℝ)) := by
    exact_mod_cast hMQ
  have hqh1 : (1 : ℝ) ≤ (q : ℝ) * (height23 x y : ℝ) :=
    le_trans (by linarith [abs_nonneg ((δ : ℝ))]) hlarge
  have hqh0 : (0 : ℝ) < (q : ℝ) * (height23 x y : ℝ) := lt_of_lt_of_le one_pos hqh1
  have hM2 : ((max r.num.natAbs r.den : ℕ) : ℝ) ≤ ((q : ℝ) * (height23 x y : ℝ)) ^ 2 := by
    calc ((max r.num.natAbs r.den : ℕ) : ℝ)
        ≤ (|(δ : ℝ)| + 1) * ((q : ℝ) * (height23 x y : ℝ)) := hMR
      _ ≤ ((q : ℝ) * (height23 x y : ℝ)) * ((q : ℝ) * (height23 x y : ℝ)) :=
          mul_le_mul_of_nonneg_right hlarge hqh0.le
      _ = ((q : ℝ) * (height23 x y : ℝ)) ^ 2 := by ring
  have hM1 : (1 : ℝ) ≤ ((max r.num.natAbs r.den : ℕ) : ℝ) := by
    have h : 1 ≤ max r.num.natAbs r.den :=
      le_max_of_le_right (Nat.one_le_iff_ne_zero.mpr r.den_nz)
    exact_mod_cast h
  have hM0 : (0 : ℝ) < ((max r.num.natAbs r.den : ℕ) : ℝ) := lt_of_lt_of_le one_pos hM1
  -- the rpow chain: dist·q < (qh)^{-ε} ≤ M^{-ε/2}
  have hq0R : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hh0R : (0 : ℝ) < (height23 x y : ℝ) := by
    have := one_le_height23 x y
    exact_mod_cast lt_of_lt_of_le zero_lt_one (by exact_mod_cast this)
  have h1 : (v.distToNearestInt : ℝ) * q < ((q : ℝ) * (height23 x y : ℝ)) ^ (-ε) := by
    have hq_id : (q : ℝ) ^ (-1 - ε) * (q : ℝ) = (q : ℝ) ^ (-ε) := by
      nth_rewrite 2 [show ((q : ℝ)) = (q : ℝ) ^ (1 : ℝ) from (Real.rpow_one _).symm]
      rw [← Real.rpow_add hq0R]
      congr 1
      ring
    calc (v.distToNearestInt : ℝ) * q
        < ((height23 x y : ℝ) ^ (-ε) * (q : ℝ) ^ (-1 - ε)) * q :=
          mul_lt_mul_of_pos_right hlt hq0R
      _ = (height23 x y : ℝ) ^ (-ε) * ((q : ℝ) ^ (-1 - ε) * q) := by ring
      _ = (height23 x y : ℝ) ^ (-ε) * (q : ℝ) ^ (-ε) := by rw [hq_id]
      _ = ((q : ℝ) * (height23 x y : ℝ)) ^ (-ε) := by
          rw [Real.mul_rpow hq0R.le hh0R.le]
          ring
  have h2 : ((q : ℝ) * (height23 x y : ℝ)) ^ (-ε)
      ≤ ((max r.num.natAbs r.den : ℕ) : ℝ) ^ (-(ε / 2)) := by
    have hstep : ((max r.num.natAbs r.den : ℕ) : ℝ) ^ (ε / 2)
        ≤ (((q : ℝ) * (height23 x y : ℝ)) ^ 2) ^ (ε / 2) :=
      Real.rpow_le_rpow hM0.le hM2 (by positivity)
    have hqh2 : ((((q : ℝ) * (height23 x y : ℝ)) ^ 2 : ℝ)) ^ (ε / 2)
        = ((q : ℝ) * (height23 x y : ℝ)) ^ ε := by
      rw [← Real.rpow_natCast ((q : ℝ) * (height23 x y : ℝ)) 2,
        ← Real.rpow_mul hqh0.le]
      congr 1
      ring
    rw [Real.rpow_neg hqh0.le, Real.rpow_neg hM0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hM0 _) (hqh2 ▸ hstep)
  -- membership
  refine ⟨![(A : ℚ), ((B : ℤ) : ℚ)], ?_, ?_, ?_, ?_⟩
  · intro hzero
    have h0 := congrFun hzero 0
    simp only [Matrix.cons_val_zero, Pi.zero_apply] at h0
    exact hA (by exact_mod_cast h0)
  · simp only [Matrix.cons_val_zero]
    exact Int.cast_ne_zero.mpr hA
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    have h2' : ((B : ℤ) : ℚ) / (A : ℚ) = ((q : ℚ) * u) / ((p₀ : ℤ) : ℚ) := by
      rw [div_eq_div_iff (Int.cast_ne_zero.mpr hA) (Int.cast_ne_zero.mpr hp₀)]
      linear_combination - hcross
    exact h2'.symm
  · rw [approxProduct_pair_eq δ A B hAB]
    have hmaxeq : max (real (A : ℚ)) (real ((B : ℤ) : ℚ))
        = ((max r.num.natAbs r.den : ℕ) : ℝ) := by
      rw [real_eq_abs, real_eq_abs, Nat.cast_max]
      congr 1
      · rw [show |((A : ℤ) : ℚ)| = ((A.natAbs : ℕ) : ℚ) from by
          rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]]
        rw [hAdef]
        push_cast
        ring
      · rw [show |((B : ℤ) : ℚ)| = ((B.natAbs : ℕ) : ℚ) from by
          rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]]
        rw [hBdef, Int.natAbs_natCast]
        push_cast
        ring
    have hM : mulHeight ![(A : ℚ), ((B : ℤ) : ℚ)] = ((max r.num.natAbs r.den : ℕ) : ℝ) := by
      rw [mulHeight_pair_eq _ _ (Int.cast_ne_zero.mpr hB.ne'), hAeq,
        Rat.mulHeight₁_eq_max]
    rw [hM, hmaxeq]
    have hRHS : ((max r.num.natAbs r.den : ℕ) : ℝ) ^ (-(2 : ℝ) - ε / 2)
        = ((max r.num.natAbs r.den : ℕ) : ℝ) ^ (-(ε / 2))
          / ((max r.num.natAbs r.den : ℕ) : ℝ) ^ 2 := by
      rw [eq_div_iff (ne_of_gt (pow_pos hM0 2)), ← Real.rpow_natCast
        ((max r.num.natAbs r.den : ℕ) : ℝ) 2, ← Real.rpow_add hM0]
      congr 1
      push_cast
      ring
    rw [hRHS, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_mul_inv,
      div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (by positivity))
    calc real ((A : ℚ) - δ * ((B : ℤ) : ℚ)) * real ((B : ℤ) : ℚ)
          * (padic 2 (A : ℚ) * padic 2 ((B : ℤ) : ℚ))
          * (padic 3 (A : ℚ) * padic 3 ((B : ℤ) : ℚ))
        ≤ (v.distToNearestInt : ℝ) * q := hnum
      _ ≤ ((max r.num.natAbs r.den : ℕ) : ℝ) ^ (-(ε / 2)) := le_trans h1.le h2


/-! ### STEP 4: fibre and small-set finiteness -/

private lemma small_finite (δ : ℚ) :
    {p : ℕ × ℤ × ℤ | 1 ≤ p.1 ∧
      (p.1 : ℝ) * (height23 p.2.1 p.2.2 : ℝ) < |(δ : ℝ)| + 1}.Finite := by
  apply Set.Finite.subset
    ((Set.finite_Icc 1 ⌊(|(δ : ℝ)| + 1)⌋₊).prod (finite_height23_le (|(δ : ℝ)| + 1)))
  rintro ⟨q, x, y⟩ ⟨hq1, hlt⟩
  have hh1 : (1 : ℝ) ≤ (height23 x y : ℝ) := by exact_mod_cast one_le_height23 x y
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hqh_q : (q : ℝ) ≤ (q : ℝ) * (height23 x y : ℝ) :=
    le_mul_of_one_le_right (by linarith) hh1
  have hqh_h : (height23 x y : ℝ) ≤ (q : ℝ) * (height23 x y : ℝ) :=
    le_mul_of_one_le_left (by linarith) hq1R
  exact Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ⟨hq1, Nat.le_floor (by linarith)⟩,
    by simp only [Set.mem_setOf_eq]; linarith⟩

private lemma fibre_finite (δ : ℚ) (ε : ℝ) (hε : 0 < ε) (ρ : ℚ) :
    {p : ℕ × ℤ × ℤ | (1 ≤ p.1 ∧ 1 < |sval δ p.1 p.2.1 p.2.2| ∧
        0 < (sval δ p.1 p.2.1 p.2.2).distToNearestInt ∧
        ((sval δ p.1 p.2.1 p.2.2).distToNearestInt : ℝ)
          < (height23 p.2.1 p.2.2 : ℝ) ^ (-ε) * (p.1 : ℝ) ^ (-1 - ε)) ∧
      ((p.1 : ℚ) * ((2 : ℚ) ^ p.2.1 * (3 : ℚ) ^ p.2.2))
        / ((round (sval δ p.1 p.2.1 p.2.2) : ℤ) : ℚ) = ρ}.Finite := by
  by_cases hδρ : δ * ρ = 1
  · -- the fibre is empty: `δ·ρ = 1` forces `v = round v`, contradicting `0 < ‖v‖`
    convert Set.finite_empty
    ext ⟨q, x, y⟩
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨hq1, hv1, hd, hlt⟩, hρ⟩
    have hp₀ : round (sval δ q x y) ≠ 0 := round_ne_zero_of_one_lt_abs hv1
    have hp₀Q : ((round (sval δ q x y) : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hp₀
    have hvp : sval δ q x y = ((round (sval δ q x y) : ℤ) : ℚ) := by
      have h1 : δ * (((q : ℚ) * ((2 : ℚ) ^ x * (3 : ℚ) ^ y))
          / ((round (sval δ q x y) : ℤ) : ℚ)) = 1 := by rw [hρ]; exact hδρ
      rw [← mul_div_assoc, div_eq_one_iff_eq hp₀Q] at h1
      rw [← h1, sval]
      ring
    rw [hvp] at hd
    simp at hd
  · set c : ℚ := |δ * ρ - 1| with hcdef
    have hc0 : (0 : ℚ) < c := abs_pos.mpr (sub_ne_zero.mpr hδρ)
    have hc0R : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc0
    apply Set.Finite.subset ((Set.finite_Icc 1 ⌊((c : ℝ))⁻¹⌋₊).prod
      (finite_height23_le (((c : ℝ))⁻¹ ^ (1 / ε))))
    rintro ⟨q, x, y⟩ ⟨⟨hq1, hv1, hd, hlt⟩, hρ⟩
    have hp₀ : round (sval δ q x y) ≠ 0 := round_ne_zero_of_one_lt_abs hv1
    have hp₀Q : ((round (sval δ q x y) : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hp₀
    -- `c ≤ ‖v‖` on the fibre
    have hδρ_eq : (δ * ρ - 1) * ((round (sval δ q x y) : ℤ) : ℚ)
        = sval δ q x y - ((round (sval δ q x y) : ℤ) : ℚ) := by
      rw [← hρ, ← mul_div_assoc]
      field_simp
      rw [sval]
      ring
    have hcd : c * |((round (sval δ q x y) : ℤ) : ℚ)|
        = (sval δ q x y).distToNearestInt := by
      rw [hcdef, ← abs_mul, hδρ_eq, Rat.distToNearestInt]
    have h1p₀ : (1 : ℚ) ≤ |((round (sval δ q x y) : ℤ) : ℚ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (by exact hp₀)
    have hcle : c ≤ (sval δ q x y).distToNearestInt := by
      calc c = c * 1 := by ring
        _ ≤ c * |((round (sval δ q x y) : ℤ) : ℚ)| :=
            mul_le_mul_of_nonneg_left h1p₀ hc0.le
        _ = (sval δ q x y).distToNearestInt := hcd
    have hcleR : (c : ℝ) ≤ ((sval δ q x y).distToNearestInt : ℝ) := by exact_mod_cast hcle
    have hh1 : (1 : ℝ) ≤ (height23 x y : ℝ) := by exact_mod_cast one_le_height23 x y
    have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    have hh0 : (0 : ℝ) < (height23 x y : ℝ) := lt_of_lt_of_le one_pos hh1
    have hq0R : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le one_pos hq1R
    have hchain : (c : ℝ) < (height23 x y : ℝ) ^ (-ε) * (q : ℝ) ^ (-1 - ε) :=
      lt_of_le_of_lt hcleR hlt
    have hhle1 : (height23 x y : ℝ) ^ (-ε) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hh1 (by linarith)
    have hqle1 : (q : ℝ) ^ (-1 - ε) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hq1R (by linarith)
    have hrpow_pos_h : (0 : ℝ) < (height23 x y : ℝ) ^ (-ε) := Real.rpow_pos_of_pos hh0 _
    have hrpow_pos_q : (0 : ℝ) < (q : ℝ) ^ (-1 - ε) := Real.rpow_pos_of_pos hq0R _
    -- `q` is bounded
    have hcq : (c : ℝ) < (q : ℝ)⁻¹ := by
      have h1 : (c : ℝ) < (q : ℝ) ^ (-1 - ε) := by
        calc (c : ℝ) < (height23 x y : ℝ) ^ (-ε) * (q : ℝ) ^ (-1 - ε) := hchain
          _ ≤ 1 * (q : ℝ) ^ (-1 - ε) := mul_le_mul_of_nonneg_right hhle1 hrpow_pos_q.le
          _ = (q : ℝ) ^ (-1 - ε) := one_mul _
      have h2 : (q : ℝ) ^ (-1 - ε) ≤ (q : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hq1R (by linarith)
      rw [Real.rpow_neg_one] at h2
      linarith
    have hqK : q ≤ ⌊((c : ℝ))⁻¹⌋₊ := by
      apply Nat.le_floor
      have hmul : (c : ℝ) * (q : ℝ) < 1 := by
        have h := mul_lt_mul_of_pos_right hcq hq0R
        rwa [inv_mul_cancel₀ hq0R.ne'] at h
      rw [inv_eq_one_div, le_div_iff₀ hc0R]
      linarith [hmul]
    -- `height23` is bounded
    have hch : (c : ℝ) < (height23 x y : ℝ) ^ (-ε) := by
      calc (c : ℝ) < (height23 x y : ℝ) ^ (-ε) * (q : ℝ) ^ (-1 - ε) := hchain
        _ ≤ (height23 x y : ℝ) ^ (-ε) * 1 := mul_le_mul_of_nonneg_left hqle1 hrpow_pos_h.le
        _ = (height23 x y : ℝ) ^ (-ε) := mul_one _
    have hhK : (height23 x y : ℝ) ≤ ((c : ℝ))⁻¹ ^ (1 / ε) := by
      have h1 : (height23 x y : ℝ) ^ ε ≤ ((c : ℝ))⁻¹ := by
        rw [Real.rpow_neg hh0.le] at hch
        have hmul : (c : ℝ) * (height23 x y : ℝ) ^ ε < 1 := by
          have h := mul_lt_mul_of_pos_right hch (Real.rpow_pos_of_pos hh0 ε)
          rwa [inv_mul_cancel₀ (Real.rpow_pos_of_pos hh0 ε).ne'] at h
        rw [inv_eq_one_div, le_div_iff₀ hc0R]
        linarith [hmul]
      have hpow : (height23 x y : ℝ) = ((height23 x y : ℝ) ^ ε) ^ (1 / ε) := by
        rw [← Real.rpow_mul hh0.le, mul_one_div, div_self hε.ne', Real.rpow_one]
      calc (height23 x y : ℝ) = ((height23 x y : ℝ) ^ ε) ^ (1 / ε) := hpow
        _ ≤ ((c : ℝ))⁻¹ ^ (1 / ε) :=
          Real.rpow_le_rpow (Real.rpow_pos_of_pos hh0 ε).le h1 (by positivity)
    exact Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ⟨hq1, hqK⟩,
      by simp only [Set.mem_setOf_eq]; exact hhK⟩


/-- **The Corvaja–Zannier Main Theorem, ℚ-specialized, derived** — same statement
as the cited axiom `CZ.pseudoPisot_approx`, here **proved sorry-free** from Ridout's
theorem `Ridout.finite_ratios`, i.e. from `Subspace.evertseSchlickewei` at `n = 2`
(the only non-std3 axiom in its footprint).

The pseudo-Pisot integrality clause (`v ∉ ℤ`) only *removes* points from the
exceptional set, so finiteness follows from the pure approximation core `hcore`:
split off the finitely many small triples (`q·h < |δ|+1`, `small_finite`); every
large triple's orbit ratio lies in the finite ratio set of `finite_ratios_cz`
(`orbit_mem_ratios` = the Ridout application), and each ratio fibre is finite
(`fibre_finite`).  The hypothesis `δ ≠ 0` is inherited from the axiom's statement
(fidelity) but is not needed: for `δ = 0` the clause `1 < |v|` already empties the set. -/
theorem pseudoPisot_approx_of_subspace (δ : ℚ) (_hδ : δ ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    {p : ℕ × ℤ × ℤ | 1 ≤ p.1 ∧
      1 < |sval δ p.1 p.2.1 p.2.2| ∧
      ¬ (∃ n : ℤ, sval δ p.1 p.2.1 p.2.2 = n) ∧
      0 < (sval δ p.1 p.2.1 p.2.2).distToNearestInt ∧
      ((sval δ p.1 p.2.1 p.2.2).distToNearestInt : ℝ)
        < (height23 p.2.1 p.2.2 : ℝ) ^ (-ε) * (p.1 : ℝ) ^ (-1 - ε)}.Finite := by
  have hcore : {p : ℕ × ℤ × ℤ | 1 ≤ p.1 ∧
      1 < |sval δ p.1 p.2.1 p.2.2| ∧
      0 < (sval δ p.1 p.2.1 p.2.2).distToNearestInt ∧
      ((sval δ p.1 p.2.1 p.2.2).distToNearestInt : ℝ)
        < (height23 p.2.1 p.2.2 : ℝ) ^ (-ε) * (p.1 : ℝ) ^ (-1 - ε)}.Finite := by
    have hR := finite_ratios_cz δ (ε / 2) (by positivity)
    apply Set.Finite.subset ((small_finite δ).union
      (hR.biUnion (fun ρ _ => fibre_finite δ ε hε ρ)))
    intro p hp
    obtain ⟨hq1, hv1, hd, hlt⟩ := hp
    rcases le_or_gt (|(δ : ℝ)| + 1) ((p.1 : ℝ) * (height23 p.2.1 p.2.2 : ℝ)) with hlg | hsm
    case inr => exact Or.inl ⟨hq1, hsm⟩
    case inl => exact Or.inr (Set.mem_biUnion
        (orbit_mem_ratios δ ε hε p.1 p.2.1 p.2.2 hq1 hv1 hlt hlg)
        ⟨⟨hq1, hv1, hd, hlt⟩, rfl⟩)
  exact hcore.subset (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.2.1, hp.2.2.2.2⟩)

end CZ

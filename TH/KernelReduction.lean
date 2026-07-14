/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TH.ComplexityLower
import Mathlib.Algebra.Order.Ring.Pow

/-!
# Stage 1: the Diophantine kernel (K) and the reduction M4-from-(K)

**M4** — superlinear subword complexity of the steering word, `p_T(k)/k → ∞` — reduces
by pigeonhole + Lemma R to a single Diophantine statement, the **kernel (K)** —
exponential pair repulsion for the orbit of `(3/2)^n`:

  (K)  for every `θ < 1`, `‖(3/2)^c − (3/2)^a‖ ≤ θ^c` has only finitely many
       solutions `2 ≤ a < c`.

Here `θ` ranges over *rationals* in `(0, 1)` — no loss against the real
formulation (the sets are monotone in `θ` and `ℚ` is dense), and it keeps the
whole Stage-0/1 layer inside `ℚ`.  The trivial floor is `2^{-c}`
(`one_le_two_pow_mul_distToNearestInt_orbit`); (K) asks for any exponential
saving over it.

**The reduction** (`superlinear_of_kernel`): if `p_T(k) ≤ C·k` for some `k`,
pigeonhole among the `C·k + 1` windows starting at positions `2, …, C·k + 2`
gives a repetition `(a, c, k)` with `2 ≤ a < c ≤ C·k + 2 ≤ (C+2)·k`; Lemma R
contracts it to `‖(3/2)^c − (3/2)^a‖ ≤ (2/3)^k ≤ θ^c` for the *fixed* rational
scale `θ := 1 − (1/3)/(C+2)` (Bernoulli certificate `exists_pow_ge`:
`θ^{C+2} ≥ 2/3`), while the growth ceiling (`repetition_linear_bound`) forces
`c ≥ (41k − 24)/24 → ∞` — so (K) at the single scale `θ` bounds `k`.  Hence (K)
⟹ `p_T(k)/k → ∞`.

Everything here is std3 (no cited axioms): (K) is *consumed as a hypothesis*
(`Kernel`), never axiomatized — per the layered-QA policy the open kernel stays
a named hypothesis.  Its two unconditional slices (bounded gap, huge gap) are
proved from the CZ 2004 axiom in `TH.GapSlices`, and the conditional capstone
(middle band only) is `TH.CapstoneM4`.

## Contents

* `TH.kernelViolators` — the (K)-violating pairs at scale `θ`.
* `TH.PairRepulsion`, `TH.Kernel` — the kernel, per-scale and quantified.
* `TH.Superlinear` — the M4 target `p_T(k)/k → ∞`.
* `TH.exists_pow_ge` — rational Bernoulli certificate `∃ θ < 1, r ≤ θ^N`
  (trades the irrational `(2/3)^{1/N}` for a rational kernel scale).
* `TH.mem_kernelViolators_of_repetition` — the Lemma-R contraction of a
  repetition into the kernel.
* `TH.superlinear_of_kernel` — **the Stage-1 reduction**: (K) ⟹ M4.
-/

namespace TH

/-- The (K)-violating pairs at scale `θ`: `2 ≤ a < c` with
`‖(3/2)^c − (3/2)^a‖ ≤ θ^c`. -/
def kernelViolators (θ : ℚ) : Set (ℕ × ℕ) :=
  {p | 2 ≤ p.1 ∧ p.1 < p.2 ∧
    ((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1).distToNearestInt ≤ θ ^ p.2}

/-- **Exponential pair repulsion at scale `θ`**: only finitely many (K)-violating
pairs. -/
def PairRepulsion (θ : ℚ) : Prop := (kernelViolators θ).Finite

/-- **The Diophantine kernel (K)**: pair repulsion at every rational
scale `θ ∈ (0, 1)` — the orbit's points repel at every exponential scale. -/
def Kernel : Prop := ∀ θ : ℚ, 0 < θ → θ < 1 → PairRepulsion θ

/-- **M4**: the subword complexity of the steering word is superlinear,
`p_T(k)/k → ∞` — the target of the development. -/
def Superlinear : Prop := ∀ C : ℕ, ∃ K : ℕ, ∀ k, K ≤ k → C * k < complexity k

/-- Rational Bernoulli certificate: for `r ∈ (0, 1)` and `N ≥ 1` there is a
rational `θ ∈ (0, 1)` with `r ≤ θ^N` — take `θ = 1 − (1 − r)/N`.  Used to trade
the irrational `(2/3)^{1/N}` for a rational kernel scale. -/
lemma exists_pow_ge (r : ℚ) (hr0 : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N) :
    ∃ θ : ℚ, 0 < θ ∧ θ < 1 ∧ r ≤ θ ^ N := by
  have hN0 : (0 : ℚ) < N := by exact_mod_cast hN
  have hdivle : (1 - r) / N ≤ 1 - r := div_le_self (by linarith) (by exact_mod_cast hN)
  have hdivpos : 0 < (1 - r) / N := div_pos (by linarith) hN0
  refine ⟨1 - (1 - r) / N, by linarith, by linarith, ?_⟩
  have hb := one_add_mul_le_pow (a := -((1 - r) / N)) (by linarith) N
  calc r = 1 + (N : ℚ) * (-((1 - r) / N)) := by
        field_simp
        ring
    _ ≤ (1 + -((1 - r) / N)) ^ N := hb
    _ = (1 - (1 - r) / N) ^ N := by rw [← sub_eq_add_neg]

/-- The Lemma-R contraction into the kernel: a length-`k` repetition
`(a, c, k)` with `c ≤ (C+2)·k` lands in `kernelViolators θ` for any rational
scale `θ` with `θ^{C+2} ≥ 2/3`. -/
lemma mem_kernelViolators_of_repetition {θ : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {C k a c : ℕ} (hθpow : (2 / 3 : ℚ) ≤ θ ^ (C + 2)) (ha : 2 ≤ a) (hac : a < c)
    (hck : c ≤ (C + 2) * k) (hrep : IsRepetition a c k) :
    (a, c) ∈ kernelViolators θ := by
  refine ⟨ha, hac, ?_⟩
  calc ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a).distToNearestInt
      ≤ |eps c - eps a| := distToNearestInt_orbit_le a c
    _ ≤ (2 / 3 : ℚ) ^ k := abs_eps_sub_le_of_repetition hrep
    _ ≤ (θ ^ (C + 2)) ^ k := pow_le_pow_left₀ (by norm_num) hθpow k
    _ = θ ^ ((C + 2) * k) := (pow_mul θ (C + 2) k).symm
    _ ≤ θ ^ c := pow_le_pow_of_le_one hθ0.le hθ1.le hck

/-- **Stage 1 reduction, (K) ⟹ M4**: exponential pair repulsion at
every rational scale forces superlinear subword complexity of the steering word.
Proof: pigeonhole a failing `C` into a repetition, contract by Lemma R into
`kernelViolators θ` at the Bernoulli scale `θ(C)`, and let the growth ceiling
push `c → ∞` against the finiteness. -/
theorem superlinear_of_kernel (hK : Kernel) : Superlinear := by
  intro C
  obtain ⟨θ, hθ0, hθ1, hθpow⟩ :=
    exists_pow_ge (2 / 3) (by norm_num) (by norm_num) (C + 2) (by omega)
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ p ∈ kernelViolators θ, p.2 ≤ M := by
    obtain ⟨M, hM⟩ := ((hK θ hθ0 hθ1).image Prod.snd).bddAbove
    exact ⟨M, fun p hp => hM (Set.mem_image_of_mem _ hp)⟩
  refine ⟨M + 1, fun k hk => ?_⟩
  by_contra hle
  have hple : complexity k ≤ C * k := Nat.not_lt.mp hle
  -- pigeonhole among the C·k + 1 windows at positions 2, …, C·k + 2
  have hncard : complexity k = (factorSet_finite k).toFinset.card :=
    Set.ncard_eq_toFinset_card _ (factorSet_finite k)
  have hcard : ((factorSet_finite k).toFinset).card
      < (Finset.Icc 2 (C * k + 2)).card := by
    rw [Nat.card_Icc, ← hncard]
    have harith : C * k + 2 + 1 - 2 = C * k + 1 := by
      generalize C * k = P
      omega
    rw [harith]
    exact Nat.lt_succ_of_le hple
  have hmaps : ∀ a ∈ Finset.Icc 2 (C * k + 2),
      factor a k ∈ (factorSet_finite k).toFinset := fun a _ => by
    rw [Set.Finite.mem_toFinset]
    exact ⟨a, rfl⟩
  obtain ⟨x, hx, y, hy, hxy, hfeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  rw [Finset.mem_Icc] at hx hy
  have hmem : ∃ a c, 2 ≤ a ∧ a < c ∧ c ≤ C * k + 2 ∧ IsRepetition a c k := by
    rcases Nat.lt_or_ge x y with h | h
    · exact ⟨x, y, hx.1, h, hy.2, factor_eq_iff.mp hfeq⟩
    · have hlt : y < x := by omega
      exact ⟨y, x, hy.1, hlt, hx.2, factor_eq_iff.mp hfeq.symm⟩
  obtain ⟨a, c, ha, hac, hc, hrep⟩ := hmem
  have hck : c ≤ (C + 2) * k := by
    have h2k : 2 ≤ 2 * k := by omega
    calc c ≤ C * k + 2 := hc
      _ ≤ C * k + 2 * k := Nat.add_le_add_left h2k _
      _ = (C + 2) * k := by ring
  have hkv := mem_kernelViolators_of_repetition hθ0 hθ1 hθpow ha hac hck hrep
  have hcM : c ≤ M := hM (a, c) hkv
  -- growth ceiling: 41·k ≤ 24·c + 24 ≤ 24·M + 24, against k ≥ M + 1
  have hbound := repetition_linear_bound ha hac hrep
  omega

end TH

/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TH.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Lemma R: the repetition identity for the (3/2)ⁿ steering word

Stage 0 of the M4/A3 program, part 2 ([M4A3] §3.2–3.3).  A **repetition** is a
length-`k` factor of the steering word occurring at two positions `a < c`
(occurrences may overlap; nothing anchors them to the prefix — the dynamics is
autonomous, so all constants are position-uniform, in contrast to
Adamczewski–Bugeaud's prefix-anchored Condition (∗)).

Because equal factors accumulate equal circuit sums (`W_eq_of_repetition`), the
closed form `W(a,k) = 3^k ε_a − 2^k ε_{a+k}` of `TH.Basic` collapses every
repetition into **Lemma R**:

  `3^k (ε_c − ε_a) = 2^k (ε_{c+k} − ε_{a+k})`   (`lemmaR_eps`)
  `3^k (m_c − m_a) = 2^k (m_{c+k} − m_{a+k})`   (`lemmaR_int`)

with three quantitative shadows:

* **divisibility** — `2^k ∣ m_c − m_a` and `3^k ∣ m_{c+k} − m_{a+k}`
  (`gcd(2,3) = 1`);
* **contraction** — `|ε_c − ε_a| ≤ (2/3)^k` (`abs_eps_sub_le_of_repetition`):
  a long repetition forces two orbit points exponentially close — the interface
  to the Diophantine kernel (K) of [M4A3] §4–5;
* **growth ceiling** — for `2 ≤ a < c`, `2^k ≤ m_c − m_a ≤ m_c` bounds the
  repetition length: `2^(k+c+1) ≤ 3^(c+1)` (`repetition_pow_le`), i.e.
  `k ≲ 0.585·c` — pure integer arithmetic, no logarithms.

Elementary harvest, no Diophantine input:

* **T0.2 (milestone M1)**: the steering word is **not eventually periodic**
  (`not_eventually_periodic`) — a fixed-gap repetition of every length beats the
  growth ceiling.
* **T0.3**: `j`-fold repetitions of a length-`p` block are quantitatively
  forbidden late in the word (`power_repetition_bound`).
* the trivial repulsion floor `|ε_c − ε_a| ≥ 2^{-c}`
  (`one_le_two_pow_mul_abs_eps_sub`), from oddness of the numerators `R`.

Novelty status (M-0 gate, resolved 2026-07-05): the identity-and-divisibility
machinery is **known** for the sibling objects — AFS 2008 eq. (4) + Lemmas 6/8
(shared continuations force `q^k`-congruences in base 3/2), [Kop21] Lemma 3.8 (the
same telescoping identity for companion words of arbitrary reals; Lemma R is its
`ξ₁ = (3/2)^a, ξ₂ = (3/2)^c` instance in round convention), and aperiodicity
(T0.2) is a special case of [DN05] Lemma 1.  Not previously stated for the
nearest-integer steering word of the orbit of 1; this file is a transport of that
machinery plus, to our knowledge, its first formalization.

## Contents

* `TH.IsRepetition` — two occurrences of one length-`k` factor.
* `W_eq_of_repetition`, `lemmaR_int`, `lemmaR_eps` — **Lemma R**.
* `two_pow_dvd_of_repetition`, `three_pow_dvd_of_repetition` — divisibilities.
* `two_pow_le_sub`, `repetition_pow_le`, `repetition_pow_le_nat` — the growth
  ceiling `2^(k+c+1) ≤ 3^(c+1)`.
* `abs_eps_sub_le_of_repetition` — the `(2/3)^k` contraction (kernel interface).
* `one_le_two_pow_mul_abs_eps_sub` — the `2^{-c}` repulsion floor.
* `not_eventually_periodic` (T0.2), `power_repetition_bound` (T0.3).

## References

* [M4A3] `plan-M4A3.html` (this repository, 2026-07): §3.2 (Lemma R), §3.3
  (elementary theorems), §4 (kernel interface), §10 (M-0 verdicts).
* [AFS08] Akiyama, Frougny, Sakarovitch. *Powers of rationals modulo 1 and
  rational base number systems.* Israel J. Math. **168** (2008), 53–91.
  (Eq. (4), Lemmas 6/8: the congruence machinery.)
* [Kop21] Kopra. *On the trace subshifts of fractional multiplication automata.*
  Theoret. Comput. Sci. **851** (2021), 92–110. (Lemma 3.8: the identity for
  companion words.)
* [DN05] Dubickas, Novikas. *Integer parts of powers of rational numbers.*
  Math. Z. **251** (2005), 635–648. (Lemma 1: aperiodicity of the family.)
-/

namespace TH

/-- A length-`k` factor of the steering word occurring at positions `a` and `c`:
`t (a+i) = t (c+i)` for all `i < k`.  Occurrences may overlap. -/
def IsRepetition (a c k : ℕ) : Prop := ∀ i < k, t (a + i) = t (c + i)

/-- Equal factors accumulate equal circuit sums. -/
lemma W_eq_of_repetition {a c k : ℕ} (h : IsRepetition a c k) : W a k = W c k :=
  Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.mp hi)]

/-- **Lemma R, integer form** ([M4A3] §3.2): a repetition at `a < c` of length `k`
forces `3^k (m_c − m_a) = 2^k (m_{c+k} − m_{a+k})`. -/
theorem lemmaR_int {a c k : ℕ} (h : IsRepetition a c k) :
    3 ^ k * (m c - m a) = 2 ^ k * (m (c + k) - m (a + k)) := by
  have ha := circuit_sum a k
  have hc := circuit_sum c k
  have hw := W_eq_of_repetition h
  linear_combination ha - hc + hw

/-- **Lemma R, fractional form** ([M4A3] §3.2): a repetition at `a < c` of length
`k` forces `3^k (ε_c − ε_a) = 2^k (ε_{c+k} − ε_{a+k})`. -/
theorem lemmaR_eps {a c k : ℕ} (h : IsRepetition a c k) :
    (3 : ℚ) ^ k * (eps c - eps a) = 2 ^ k * (eps (c + k) - eps (a + k)) := by
  have ha := W_closed a k
  have hc := W_closed c k
  have hw' : (W a k : ℚ) = W c k := by exact_mod_cast W_eq_of_repetition h
  linear_combination ha - hc - hw'

/-- `2^k` and `3^k` are coprime in `ℤ`. -/
private lemma coprime_pow (k : ℕ) : IsCoprime ((2 : ℤ) ^ k) ((3 : ℤ) ^ k) := by
  refine IsCoprime.pow ?_
  rw [Int.isCoprime_iff_gcd_eq_one]
  decide

/-- Divisibility shadow of Lemma R: `2^k ∣ m_c − m_a`. -/
theorem two_pow_dvd_of_repetition {a c k : ℕ} (h : IsRepetition a c k) :
    (2 : ℤ) ^ k ∣ m c - m a := by
  have hdvd : (2 : ℤ) ^ k ∣ 3 ^ k * (m c - m a) := by
    rw [lemmaR_int h]
    exact Dvd.intro _ rfl
  exact (coprime_pow k).dvd_of_dvd_mul_left hdvd

/-- Divisibility shadow of Lemma R, other side: `3^k ∣ m_{c+k} − m_{a+k}`. -/
theorem three_pow_dvd_of_repetition {a c k : ℕ} (h : IsRepetition a c k) :
    (3 : ℤ) ^ k ∣ m (c + k) - m (a + k) := by
  have hdvd : (3 : ℤ) ^ k ∣ 2 ^ k * (m (c + k) - m (a + k)) := by
    rw [← lemmaR_int h]
    exact Dvd.intro _ rfl
  exact (coprime_pow k).symm.dvd_of_dvd_mul_left hdvd

/-- For `2 ≤ a < c`, the divisibility upgrades to size: `2^k ≤ m_c − m_a`. -/
theorem two_pow_le_sub {a c k : ℕ} (ha : 2 ≤ a) (hac : a < c)
    (h : IsRepetition a c k) : (2 : ℤ) ^ k ≤ m c - m a :=
  Int.le_of_dvd (sub_pos.mpr (m_strictMono ha hac)) (two_pow_dvd_of_repetition h)

/-- **Growth ceiling** ([M4A3] §3.2): a length-`k` repetition at `2 ≤ a < c`
forces `2^(k+c+1) ≤ 3^(c+1)` — i.e. `k ≤ c·log₂(3/2) + O(1) ≈ 0.585·c`, stated
as a pure integer inequality. -/
theorem repetition_pow_le {a c k : ℕ} (ha : 2 ≤ a) (hac : a < c)
    (h : IsRepetition a c k) : (2 : ℤ) ^ (k + c + 1) ≤ 3 ^ (c + 1) := by
  have h1 := two_pow_le_sub ha hac h
  have h3 : 0 < m a := m_pos a
  have h4 : (2 : ℤ) ^ k ≤ m c := by linarith
  have h5 : (2 : ℤ) ^ c ≤ 3 ^ c := by
    apply pow_le_pow_left₀ <;> norm_num
  have h2 := two_pow_mul_m_le c
  calc (2 : ℤ) ^ (k + c + 1) = 2 ^ k * (2 * 2 ^ c) := by
        rw [pow_add, pow_succ]
        ring
    _ ≤ m c * (2 * 2 ^ c) := by
        apply mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = 2 * (2 ^ c * m c) := by ring
    _ ≤ 2 * 3 ^ c + 2 ^ c := h2
    _ ≤ 3 ^ (c + 1) := by
        rw [pow_succ]
        linarith

/-- `ℕ`-cast of the growth ceiling, for the pigeonhole bookkeeping downstream. -/
theorem repetition_pow_le_nat {a c k : ℕ} (ha : 2 ≤ a) (hac : a < c)
    (h : IsRepetition a c k) : 2 ^ (k + c + 1) ≤ 3 ^ (c + 1) := by
  exact_mod_cast repetition_pow_le ha hac h

/-- **Contraction / kernel interface** ([M4A3] §3.2, §4): a length-`k` repetition
forces the two orbit points exponentially close, `|ε_c − ε_a| ≤ (2/3)^k`.  This is
the inequality the Diophantine kernel (K) forbids at scale `k ≍ c`. -/
theorem abs_eps_sub_le_of_repetition {a c k : ℕ} (h : IsRepetition a c k) :
    |eps c - eps a| ≤ (2 / 3 : ℚ) ^ k := by
  have hR := lemmaR_eps h
  have h3 : (0 : ℚ) < 3 ^ k := by positivity
  have heq : eps c - eps a = (2 / 3 : ℚ) ^ k * (eps (c + k) - eps (a + k)) := by
    rw [div_pow]
    field_simp
    linarith [hR]
  have hpos : (0 : ℚ) ≤ (2 / 3 : ℚ) ^ k := by positivity
  rw [heq, abs_mul, abs_of_nonneg hpos]
  calc (2 / 3 : ℚ) ^ k * |eps (c + k) - eps (a + k)|
      ≤ (2 / 3 : ℚ) ^ k * 1 :=
        mul_le_mul_of_nonneg_left (abs_eps_sub_lt_one _ _).le hpos
    _ = (2 / 3 : ℚ) ^ k := mul_one _

/-- **Trivial repulsion floor** ([M4A3] §3.2): for `1 ≤ a < c` the difference
`ε_c − ε_a` has odd numerator over `2^c`, hence `2^c·|ε_c − ε_a| ≥ 1`.  The kernel
(K) asks to improve `2^{-c}` to `θ^c` for every `θ < 1`. -/
theorem one_le_two_pow_mul_abs_eps_sub {a c : ℕ} (ha : 1 ≤ a) (hac : a < c) :
    (1 : ℚ) ≤ 2 ^ c * |eps c - eps a| := by
  set N : ℤ := R c - 2 ^ (c - a) * R a with hN
  have hodd : N % 2 = 1 := by
    have h1 := R_emod_two c (by omega)
    have h2 : ((2 : ℤ) ^ (c - a) * R a) % 2 = 0 := by
      obtain ⟨j, hj⟩ : ∃ j, c - a = j + 1 := ⟨c - a - 1, by omega⟩
      rw [hj, show (2 : ℤ) ^ (j + 1) * R a = 2 * (2 ^ j * R a) by ring]
      exact Int.mul_emod_right 2 _
    omega
  have hne : N ≠ 0 := by omega
  have habs : (1 : ℤ) ≤ |N| := Int.one_le_abs hne
  have e1 : (2 : ℚ) ^ c * eps c = R c := two_pow_mul_eps c
  have e2 : (2 : ℚ) ^ c * eps a = ((2 : ℤ) ^ (c - a) * R a : ℤ) := by
    conv_lhs => rw [show c = (c - a) + a by omega, pow_add, mul_assoc,
      two_pow_mul_eps a]
    push_cast
    ring
  have hcast : (2 : ℚ) ^ c * (eps c - eps a) = (N : ℚ) := by
    rw [mul_sub, e1, e2, hN]
    push_cast
    ring
  calc (1 : ℚ) ≤ |(N : ℚ)| := by exact_mod_cast habs
    _ = |2 ^ c * (eps c - eps a)| := by rw [hcast]
    _ = 2 ^ c * |eps c - eps a| := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ (2 : ℚ) ^ c)]

/-- **T0.2 (milestone M1)**: the steering word is not eventually periodic.  A
fixed-gap repetition of every length would beat the growth ceiling
`2^(k+c+1) ≤ 3^(c+1)` at fixed `c`.  [M4A3] §3.3. -/
theorem not_eventually_periodic :
    ¬ ∃ N p, 0 < p ∧ ∀ n, N ≤ n → t (n + p) = t n := by
  rintro ⟨N, p, hp, hper⟩
  set a := max N 2 with ha
  set c := a + p with hc
  have ha2 : 2 ≤ a := le_max_right N 2
  have hac : a < c := by omega
  have hrep : ∀ k, IsRepetition a c k := by
    intro k i _
    have hci : c + i = (a + i) + p := by omega
    rw [hci, hper (a + i) (by have := le_max_left N 2; omega)]
  have hbound := repetition_pow_le_nat ha2 hac (hrep (3 ^ (c + 1)))
  have hlt : (3 : ℕ) ^ (c + 1) < 2 ^ (3 ^ (c + 1)) := Nat.lt_two_pow_self
  have hmono : (2 : ℕ) ^ (3 ^ (c + 1)) ≤ 2 ^ (3 ^ (c + 1) + c + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- **T0.3 (power-repetition gap)** ([M4A3] §3.3): a `(j+1)`-fold repetition of a
length-`p` block starting at position `a ≥ 2` obeys
`2^(j·p + a + p + 1) ≤ 3^(a+p+1)`, i.e. `j·p ≲ 0.585·(a+p)`: long periodic
windows cannot occur late in the word. -/
theorem power_repetition_bound {a p j : ℕ} (ha : 2 ≤ a) (hp : 0 < p)
    (h : ∀ i < j * p, t (a + i) = t (a + p + i)) :
    2 ^ (j * p + (a + p) + 1) ≤ 3 ^ (a + p + 1) :=
  repetition_pow_le_nat ha (by omega) h

end TH

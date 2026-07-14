/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import ForMathlib.Data.Rat.NearestInt



/-!
# The (3/2)ⁿ steering word: basic objects (M4/A3 program, Stage 0)

Stage 0 of the M4/A3 program ([M4A3] §2–3): the nearest-integer decomposition of the
orbit of `(3/2)ⁿ`, its symbolic **steering word**, and the exact circuit-sum algebra
that everything downstream rests on.

Write `(3/2)ⁿ = mₙ + εₙ` with `mₙ ∈ ℤ` and `εₙ ∈ [-1/2, 1/2)` (centered fractional
part, the house `E`/`ε` convention of the Bertin files; `mₙ = round ((3/2)ⁿ)`).  The
**steering letter** is

  `tₙ := 2·mₙ₊₁ − 3·mₙ  =  3εₙ − 2εₙ₊₁  ∈ {-2, …, 2}`,   `tₙ ≡ mₙ (mod 2)`,

so `T = (tₙ)` is the full symbolic itinerary of the `×(3/2)` dynamics and the parity
word `b = T mod 2` its reduction.  The numerator `Rₙ := 3ⁿ − 2ⁿ·mₙ` (so `εₙ = Rₙ/2ⁿ`)
is *odd* for `n ≥ 1` — the source of the trivial `2⁻ⁿ` repulsion floor.

The load-bearing algebra is the circuit sum `W(a,k) := Σ_{i<k} 3^{k-1-i}·2^i·t_{a+i}`
(the same two-power/three-power shape as `CC.linear_decomposition` and
`paradoxical/CircuitSum.lean`), with **exact closed form**

  `W(a,k) = 3^k·ε_a − 2^k·ε_{a+k}`      (`W_closed`)

and its integer companion `2^k·m_{a+k} = 3^k·m_a + W(a,k)` (`circuit_sum`).  These
feed the repetition identity of `TH.RepetitionIdentity` (Lemma R) and the complexity
bounds of `TH.ComplexityLower`.

Everything here is pure `ℤ`/`ℚ` arithmetic — no real analysis.  Sanity values
(`category test` lemmas) match the computed row `m = 1,2,2,3,5,8,…`,
`t = 1,−2,0,1,1,…` of [M4A3] §2.

## Contents

* `TH.m`, `TH.eps` — nearest integer and centered fractional part of `(3/2)ⁿ`;
  bounds `neg_half_le_eps`, `eps_lt_half`.
* `TH.R` — numerator `3ⁿ − 2ⁿ·mₙ`; `eps_eq`, `R_emod_two` (oddness for `n ≥ 1`),
  two-sided bounds `neg_two_pow_le_two_mul_R`, `two_mul_R_lt_two_pow`.
* `TH.t`, `TH.b` — steering letter and parity letter; `t_eq_eps`, `t_abs_le`
  (5-letter alphabet), `t_emod_two` (parity link), recurrence `two_mul_m_succ`.
* `TH.W` — the circuit sum; recurrence `W_succ`, **closed form `W_closed`**,
  integer form `circuit_sum`.
* growth: `m_pos`, `two_pow_mul_m_le` (`2·2ⁿmₙ ≤ 2·3ⁿ + 2ⁿ`), strict monotonicity
  `m_strictMono` from position 2 on.
* kernel interface: `distToNearestInt_orbit_le` (`‖(3/2)^c − (3/2)^a‖ ≤ |ε_c − ε_a|`,
  the bridge from `eps`-differences to the `‖·‖` of the Diophantine kernel (K)),
  `one_le_two_pow_mul_distToNearestInt_orbit` and `distToNearestInt_orbit_pos`
  (the trivial `2^{-c}` repulsion floor in kernel form, from odd numerators).
* sanity: `m_zero` … `m_five`, `t_sanity`, `eps_zero`.

## References

* [M4A3] `plan-M4A3.html` (this repository, 2026-07): *Plan M4/A3 — superlinear
  complexity of the (3/2)ⁿ steering word via the Subspace theorem*, §2 (objects and
  normalizations), §3.1 (circuit-sum closed form).
* [AFS08] Akiyama, Frougny, Sakarovitch. *Powers of rationals modulo 1 and rational
  base number systems.* Israel J. Math. **168** (2008), 53–91.  (Symbolic context.)
-/

namespace TH

/-- `m n` is the nearest integer to `(3/2)^n` (round-half-up: `round` is `⌊·+1/2⌋`,
so ties go up and `eps` below lands in `[-1/2, 1/2)`).  [M4A3] §2. -/
def m (n : ℕ) : ℤ := round ((3 / 2 : ℚ) ^ n)

/-- `eps n = (3/2)^n − m n ∈ [-1/2, 1/2)` — the centered fractional part of the
orbit point (house ε convention).  [M4A3] §2. -/
def eps (n : ℕ) : ℚ := (3 / 2 : ℚ) ^ n - m n

/-- `R n = 3^n − 2^n·(m n)`, the integer numerator of `eps n` over `2^n`. -/
def R (n : ℕ) : ℤ := 3 ^ n - 2 ^ n * m n

/-- The steering letter `t n = 2·m (n+1) − 3·m n`: which integer translate the
`×(3/2)` map selects at step `n`.  [M4A3] §2. -/
def t (n : ℕ) : ℤ := 2 * m (n + 1) - 3 * m n

/-- The parity letter `b n = m n % 2`; the parity word is the mod-2 reduction of the
steering word (`t_emod_two`).  [M4A3] §2. -/
def b (n : ℕ) : ℤ := m n % 2

/-- The circuit sum `W a k = Σ_{i<k} 3^(k-1-i)·2^i·t (a+i)` — the inhomogeneous term
accumulated by `k` steps of the orbit from position `a`; same algebra as
`CC.linear_decomposition`.  [M4A3] §3.1. -/
def W (a k : ℕ) : ℤ := ∑ i ∈ Finset.range k, 3 ^ (k - 1 - i) * 2 ^ i * t (a + i)

/-! ## Bounds on `eps` -/

/-- Lower bound of the centered window: `-1/2 ≤ eps n`. -/
lemma neg_half_le_eps (n : ℕ) : -(1 / 2 : ℚ) ≤ eps n := by
  have h := Int.floor_le ((3 / 2 : ℚ) ^ n + 1 / 2)
  unfold eps m
  rw [round_eq]
  linarith

/-- Upper bound of the centered window: `eps n < 1/2` (strict; ties round up). -/
lemma eps_lt_half (n : ℕ) : eps n < 1 / 2 := by
  have h := Int.lt_floor_add_one ((3 / 2 : ℚ) ^ n + 1 / 2)
  unfold eps m
  rw [round_eq]
  linarith

/-- `|eps n| ≤ 1/2`. -/
lemma abs_eps_le_half (n : ℕ) : |eps n| ≤ 1 / 2 :=
  abs_le.mpr ⟨neg_half_le_eps n, (eps_lt_half n).le⟩

/-- The difference of two centered fractional parts has modulus `< 1`. -/
lemma abs_eps_sub_lt_one (x y : ℕ) : |eps x - eps y| < 1 := by
  have h1 := neg_half_le_eps x
  have h2 := eps_lt_half x
  have h3 := neg_half_le_eps y
  have h4 := eps_lt_half y
  rw [abs_lt]
  constructor <;> linarith

/-! ## The numerator `R` -/

/-- `eps n = R n / 2^n`: the orbit point's fractional part has exact denominator a
power of 2. -/
lemma eps_eq (n : ℕ) : eps n = (R n : ℚ) / 2 ^ n := by
  have h2 : ((2 : ℚ) ^ n) ≠ 0 := by positivity
  unfold eps R
  push_cast
  rw [div_pow]
  field_simp

/-- `2^n · eps n = R n` (in `ℚ`). -/
lemma two_pow_mul_eps (n : ℕ) : (2 : ℚ) ^ n * eps n = R n := by
  have h2 : ((2 : ℚ) ^ n) ≠ 0 := by positivity
  rw [eps_eq, mul_div_cancel₀ _ h2]

/-- **`R n` is odd for `n ≥ 1`** — the trivial repulsion floor `|ε_c − ε_a| ≥ 2^{-c}`
of [M4A3] §3.2 rests on this. -/
lemma R_emod_two (n : ℕ) (hn : 1 ≤ n) : R n % 2 = 1 := by
  have h3 : (3 : ℤ) ^ n % 2 = 1 :=
    Int.odd_iff.mp ((Int.odd_iff.mpr (by norm_num)).pow)
  have h2 : ((2 : ℤ) ^ n * m n) % 2 = 0 := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [show (2 : ℤ) ^ (j + 1) * m (j + 1) = 2 * (2 ^ j * m (j + 1)) by ring]
    exact Int.mul_emod_right 2 _
  unfold R
  rw [Int.sub_emod, h3, h2]
  norm_num

/-- `R 0 = 0` (the orbit starts on an integer). -/
lemma R_zero : R 0 = 0 := by
  have : m 0 = 1 := by
    unfold m
    norm_num
  simp [R, this]

/-- Two-sided bound, lower half: `-2^n ≤ 2·R n`. -/
lemma neg_two_pow_le_two_mul_R (n : ℕ) : -(2 : ℤ) ^ n ≤ 2 * R n := by
  have h := neg_half_le_eps n
  rw [eps_eq] at h
  have h2 : (0 : ℚ) < 2 ^ n := by positivity
  rw [le_div_iff₀ h2] at h
  have hq : -(2 : ℚ) ^ n ≤ 2 * (R n : ℚ) := by linarith
  exact_mod_cast hq

/-- Two-sided bound, upper half: `2·R n < 2^n`. -/
lemma two_mul_R_lt_two_pow (n : ℕ) : 2 * R n < (2 : ℤ) ^ n := by
  have h := eps_lt_half n
  rw [eps_eq] at h
  have h2 : (0 : ℚ) < 2 ^ n := by positivity
  rw [div_lt_iff₀ h2] at h
  have hq : 2 * (R n : ℚ) < (2 : ℚ) ^ n := by linarith
  exact_mod_cast hq

/-! ## The steering letter -/

/-- The step recurrence `2·m (n+1) = 3·m n + t n` (definitional rearrangement). -/
lemma two_mul_m_succ (n : ℕ) : 2 * m (n + 1) = 3 * m n + t n := by
  unfold t
  ring

/-- `t n = 3·eps n − 2·eps (n+1)`: the steering letter measures the fractional-part
transport of one `×(3/2)` step. -/
lemma t_eq_eps (n : ℕ) : (t n : ℚ) = 3 * eps n - 2 * eps (n + 1) := by
  unfold t eps
  push_cast
  rw [pow_succ]
  ring

/-- The fractional-part step recurrence `eps (n+1) = (3·eps n − t n) / 2`. -/
lemma eps_succ (n : ℕ) : eps (n + 1) = (3 * eps n - t n) / 2 := by
  have h := t_eq_eps n
  field_simp
  linarith

/-- **The alphabet is 5 letters**: `|t n| ≤ 2`. -/
lemma t_abs_le (n : ℕ) : |t n| ≤ 2 := by
  have h1 := neg_half_le_eps n
  have h2 := eps_lt_half n
  have h3 := neg_half_le_eps (n + 1)
  have h4 := eps_lt_half (n + 1)
  have ht := t_eq_eps n
  have habs : |(t n : ℚ)| < 3 := by
    rw [ht, abs_lt]
    constructor <;> linarith
  have hz : |t n| < 3 := by exact_mod_cast habs
  omega

/-- `t n ≡ m n (mod 2)`: the parity word is the mod-2 reduction of the steering
word. -/
lemma t_emod_two (n : ℕ) : t n % 2 = m n % 2 := by
  unfold t
  omega

/-- `b n = t n % 2`. -/
lemma b_eq_t_emod_two (n : ℕ) : b n = t n % 2 := by
  rw [b, t_emod_two]

/-! ## Growth of `m` -/

/-- `m n ≥ 1 > 0`. -/
lemma m_pos (n : ℕ) : 0 < m n := by
  have h1 : (1 : ℚ) ≤ (3 / 2 : ℚ) ^ n := one_le_pow₀ (by norm_num)
  have h2 := eps_lt_half n
  have h3 : (0 : ℚ) < m n := by
    unfold eps at h2
    linarith
  exact_mod_cast h3

/-- Integer growth cap: `2·(2^n·m n) ≤ 2·3^n + 2^n` — the elementary ceiling that
bounds repetition lengths (`k ≲ 0.585·c`, [M4A3] §3.2). -/
lemma two_pow_mul_m_le (n : ℕ) : 2 * ((2 : ℤ) ^ n * m n) ≤ 2 * 3 ^ n + 2 ^ n := by
  have h := neg_two_pow_le_two_mul_R n
  unfold R at h
  linarith

/-! ## Sanity row ([M4A3] §2): `m = 1, 2, 2, 3, 5, 8, …`, `t = 1, −2, 0, 1, 1, …` -/

private lemma round_helper {x : ℚ} {z : ℤ} (h1 : (z : ℚ) ≤ x + 1 / 2)
    (h2 : x + 1 / 2 < z + 1) : round x = z := by
  rw [round_eq]
  exact Int.floor_eq_iff.mpr ⟨h1, by exact_mod_cast h2⟩

/-- `m 0 = 1`. -/
lemma m_zero : m 0 = 1 := round_helper (by norm_num) (by norm_num)

/-- `m 1 = 2` (the tie `3/2` rounds up: `ε_1 = −1/2`). -/
lemma m_one : m 1 = 2 := round_helper (by norm_num) (by norm_num)

/-- `m 2 = 2`. -/
lemma m_two : m 2 = 2 := round_helper (by norm_num) (by norm_num)

/-- `m 3 = 3`. -/
lemma m_three : m 3 = 3 := round_helper (by norm_num) (by norm_num)

/-- `m 4 = 5`. -/
lemma m_four : m 4 = 5 := round_helper (by norm_num) (by norm_num)

/-- `m 5 = 8`. -/
lemma m_five : m 5 = 8 := round_helper (by norm_num) (by norm_num)

/-- `eps 0 = 0`. -/
lemma eps_zero : eps 0 = 0 := by
  unfold eps
  rw [m_zero]
  norm_num

/-- The steering word starts `1, −2, 0, 1, 1` — matching the computed sanity row of
[M4A3] §2. -/
lemma t_sanity : t 0 = 1 ∧ t 1 = -2 ∧ t 2 = 0 ∧ t 3 = 1 ∧ t 4 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [t, m_zero, m_one, m_two, m_three, m_four, m_five]

/-! ## The circuit sum and its closed form -/

/-- `W a 0 = 0`. -/
lemma W_zero (a : ℕ) : W a 0 = 0 := by
  simp [W]

/-- Circuit-sum recurrence: `W a (k+1) = 3·W a k + 2^k·t (a+k)`. -/
lemma W_succ (a k : ℕ) : W a (k + 1) = 3 * W a k + 2 ^ k * t (a + k) := by
  unfold W
  rw [Finset.sum_range_succ]
  have h1 : k + 1 - 1 - k = 0 := by omega
  rw [h1, pow_zero, one_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i < k := Finset.mem_range.mp hi
  have h2 : k + 1 - 1 - i = (k - 1 - i) + 1 := by omega
  rw [h2, pow_succ]
  ring

/-- **Closed form of the circuit sum** ([M4A3] §3.1, boxed):
`W(a,k) = 3^k·ε_a − 2^k·ε_{a+k}`.  The main terms of the orbit cancel exactly;
every repetition statement downstream flows from this. -/
theorem W_closed (a k : ℕ) : (W a k : ℚ) = 3 ^ k * eps a - 2 ^ k * eps (a + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [W_succ]
    push_cast
    rw [ih, t_eq_eps (a + k)]
    have hsucc : a + (k + 1) = (a + k) + 1 := rfl
    rw [hsucc]
    ring

/-- Integer circuit sum ([M4A3] §3.1): `2^k·m_{a+k} = 3^k·m_a + W(a,k)` — the same
decomposition as `CC.linear_decomposition`, here for the `×(3/2)` orbit. -/
theorem circuit_sum (a k : ℕ) : 2 ^ k * m (a + k) = 3 ^ k * m a + W a k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsucc : a + (k + 1) = (a + k) + 1 := rfl
    rw [hsucc, W_succ]
    calc (2 : ℤ) ^ (k + 1) * m ((a + k) + 1)
        = 2 ^ k * (2 * m ((a + k) + 1)) := by ring
      _ = 2 ^ k * (3 * m (a + k) + t (a + k)) := by rw [two_mul_m_succ]
      _ = 3 * (2 ^ k * m (a + k)) + 2 ^ k * t (a + k) := by ring
      _ = 3 * (3 ^ k * m a + W a k) + 2 ^ k * t (a + k) := by rw [ih]
      _ = 3 ^ (k + 1) * m a + (3 * W a k + 2 ^ k * t (a + k)) := by ring

/-! ## Strict monotonicity of `m` from position 2 -/

/-- `m n ≥ 3` for `n ≥ 3`. -/
lemma three_le_m {n : ℕ} (hn : 3 ≤ n) : 3 ≤ m n := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 3 with hk | hk
    · have hk2 : k = 2 := by omega
      subst hk2
      rw [m_three]
    · have h1 := ih hk
      have h2 := two_mul_m_succ k
      have ht := abs_le.mp (t_abs_le k)
      omega

/-- `m` steps up strictly from position 2 on. -/
lemma m_lt_m_succ {n : ℕ} (hn : 2 ≤ n) : m n < m (n + 1) := by
  rcases eq_or_lt_of_le hn with h | h
  · rw [← h, m_two, m_three]
    norm_num
  · have h1 := three_le_m h
    have h2 := two_mul_m_succ n
    have ht := abs_le.mp (t_abs_le n)
    omega

/-- **Strict monotonicity**: `2 ≤ a < c → m a < m c` — gives `m c − m a > 0` in the
repetition growth bound. -/
lemma m_strictMono {a c : ℕ} (ha : 2 ≤ a) (hac : a < c) : m a < m c := by
  induction c with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge a k with h | h
    · exact lt_trans (ih h) (m_lt_m_succ (by omega))
    · have hak : a = k := by omega
      subst hak
      exact m_lt_m_succ ha

/-! ## Kernel interface: distance to the nearest integer

The Diophantine kernel (K) of [M4A3] §4 speaks about `‖(3/2)^c − (3/2)^a‖`, the
distance from the orbit difference to the *nearest* integer.  The bridge from the
`eps`-world: the orbit difference is `(ε_c − ε_a)` away from the particular integer
`m_c − m_a`, so `‖·‖ ≤ |ε_c − ε_a|`; and the odd-numerator argument of
`R_emod_two` gives the trivial repulsion floor `‖·‖ ≥ 2^{-c}` directly. -/

/-- Bridge to the kernel quantity: `‖(3/2)^c − (3/2)^a‖ ≤ |ε_c − ε_a|` — the
distance to the nearest integer is at most the distance to `m_c − m_a`. -/
lemma distToNearestInt_orbit_le (a c : ℕ) :
    ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a).distToNearestInt ≤ |eps c - eps a| := by
  have h : (3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a
      = (eps c - eps a) + ((m c - m a : ℤ) : ℚ) := by
    unfold eps
    push_cast
    ring
  rw [h, Rat.distToNearestInt_add_intCast]
  exact Rat.distToNearestInt_le_abs _

/-- **Trivial repulsion floor, kernel form** ([M4A3] §3.2): for `1 ≤ a < c` the
orbit difference `(3/2)^c − (3/2)^a = 3^a(3^{c-a} − 2^{c-a})/2^c` has odd numerator
over `2^c`, so `1 ≤ 2^c · ‖(3/2)^c − (3/2)^a‖`.  The kernel (K) asks to improve
this `2^{-c}` to `θ^c` for every `θ < 1`. -/
theorem one_le_two_pow_mul_distToNearestInt_orbit {a c : ℕ} (ha : 1 ≤ a)
    (hac : a < c) :
    1 ≤ 2 ^ c * ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a).distToNearestInt := by
  obtain ⟨s, rfl⟩ : ∃ s, c = a + s := ⟨c - a, by omega⟩
  have hs : 1 ≤ s := by omega
  have h3a : (3 : ℤ) ^ a % 2 = 1 :=
    Int.odd_iff.mp ((Int.odd_iff.mpr (by norm_num)).pow)
  have h3s : (3 : ℤ) ^ s % 2 = 1 :=
    Int.odd_iff.mp ((Int.odd_iff.mpr (by norm_num)).pow)
  have h2s : (2 : ℤ) ^ s % 2 = 0 := by
    obtain ⟨j, rfl⟩ : ∃ j, s = j + 1 := ⟨s - 1, by omega⟩
    rw [show (2 : ℤ) ^ (j + 1) = 2 * 2 ^ j by ring]
    exact Int.mul_emod_right 2 _
  have hOodd : ((3 : ℤ) ^ a * (3 ^ s - 2 ^ s)) % 2 = 1 := by
    have hsub : ((3 : ℤ) ^ s - 2 ^ s) % 2 = 1 := by omega
    rw [Int.mul_emod, h3a, hsub]
    norm_num
  refine Rat.one_le_two_pow_mul_distToNearestInt (by omega) hOodd ?_
  have h2 : ((2 : ℚ)) ^ (a + s) ≠ 0 := by positivity
  push_cast
  rw [div_pow, div_pow]
  field_simp
  ring

/-- Positivity form of the trivial floor: the kernel quantity never vanishes. -/
lemma distToNearestInt_orbit_pos {a c : ℕ} (ha : 1 ≤ a) (hac : a < c) :
    0 < ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a).distToNearestInt := by
  have h := one_le_two_pow_mul_distToNearestInt_orbit ha hac
  rcases (Rat.distToNearestInt_nonneg _).lt_or_eq with h0 | h0
  · exact h0
  · rw [← h0, mul_zero] at h
    norm_num at h

end TH

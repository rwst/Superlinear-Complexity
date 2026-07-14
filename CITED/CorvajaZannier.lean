/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Finite.Basic
import ForMathlib.Data.Rat.NearestInt



/-!
# The Corvaja–Zannier Main Theorem (Acta 2004), ℚ-specialization

The **Main Theorem** of Corvaja–Zannier ([CZ04], p. 2; arXiv `math/0403522`, read in
full 2026-07-05), the Subspace-theorem engine behind their solution of Mahler's
problem on `‖αⁿ‖`:

> Let `Γ ⊂ 𝔸*` (`𝔸` = the algebraic numbers) be a finitely generated multiplicative
> group, let `δ ≠ 0` be a fixed algebraic number and let `ε > 0`.  Then there are
> only finitely many pairs `(q, u) ∈ ℤ × Γ`, `d := [ℚ(u) : ℚ]`, such that
> `|δqu| > 1`, `δqu` is **not pseudo-Pisot**, and
>
>   `0 < ‖δqu‖ < H(u)^{-ε} · q^{-d-ε}`.                                    (1.1)

`‖x‖` is the distance from `x` to the nearest integer; *pseudo-Pisot* means
`|α| > 1`, all (complex) conjugates of modulus `< 1`, and integral trace.

## Statement conventions (the ℚ-specialization — all uses in this corpus)

Stated in the ℚ-specialization every current consumer needs (each
specialization *weakens* the source statement, hence is safe):

* **Group**: `Γ = ⟨2, 3⟩ ≤ ℚ*`, encoded by exponent pairs — `(x, y) : ℤ × ℤ`
  stands for `u = 2^x·3^y` (a bijection onto `Γ`, since `2` and `3` are
  multiplicatively independent; so finiteness over triples `(q, x, y)` is
  equivalent to finiteness over the pairs `(q, u)` of the source).
* **Degree**: `u ∈ ℚ`, so `d = [ℚ(u) : ℚ] = 1` and the `q`-tax is `q^{-1-ε}`.
* **Multiplier slot**: `q` ranges over *positive* integers (`1 ≤ q`; the source
  allows `q ∈ ℤ` — restriction to a subset of the pairs weakens the claim).
* **Pseudo-Pisot, spelled out**: over `ℚ` the conjugate condition is vacuous and
  the trace of `α ∈ ℚ` is `α` itself, so `α` pseudo-Pisot `↔ |α| > 1 ∧ α ∈ ℤ`.
  Under the hypothesis `1 < |δqu|`, the exclusion "not pseudo-Pisot" is exactly
  `δqu ∉ ℤ`, transcribed as `¬ ∃ n : ℤ, δqu = n`; the two-line lemma
  `CZ.not_intCast_of_distToNearestInt_pos` discharges it from `‖δqu‖ > 0`, so it
  never costs a consumer anything.
* **Height**: for `u = 2^x·3^y` in lowest terms the absolute Weil height is
  `max(numerator, denominator)` — the explicit `CZ.height23`
  (e.g. `H((3/2)^a) = 3^a`, `CZ.height23_neg_natCast`).
* **Norms/threshold**: `‖·‖ = Rat.distToNearestInt` (exact, in `ℚ`); the threshold
  `H(u)^{-ε} q^{-1-ε}` lives in `ℝ` via `rpow`, with `ε : ℝ` free.  Exponential
  rates `ℓ^{-a}` convert via `ε < log ℓ / log 3`.

The finiteness is **ineffective** (Subspace-based): no bound on the exceptional
set is provided, only its finiteness.  Do not expect computable exceptional
bounds downstream.

Consumers (formalized in `TH/GapSlices.lean`): the
bounded-gap slice of the kernel (K) (`δ = (3/2)^{s₀} − 1`, `q = 1`,
`u = (3/2)^a`) and the huge-gap band (`δ = 1`, `q = 3^a`, `u = (3/2)^s` — the
`(q, u)`-pair uniformity of the theorem is what makes this slice fall).

## Contents

* `CZ.height23` — the absolute Weil height of `2^x·3^y`, explicitly.
* `CZ.sval` — the value `δ·q·2^x·3^y` under the exponent encoding.
* `CZ.not_intCast_of_distToNearestInt_pos` — discharges the spelled-out
  pseudo-Pisot clause from `‖δqu‖ > 0`.
* `CZ.height23_neg_natCast` — `H(2^{-a}·3^a) = 3^a`, the height normalization
  used by both consumers.

**The Main Theorem itself** ([CZ04], ℚ-specialized) is stated and **derived**
from the `S`-arithmetic Subspace Theorem (`Subspace.evertseSchlickewei`, the one
cited axiom of the refactor) as `CZ.pseudoPisot_approx_of_subspace` in
`CITED/CorvajaZannierProof.lean`.  The cited `axiom CZ.pseudoPisot_approx` that
used to live here was **retired 2026-07-14** — the statement survives verbatim
as that theorem.

## References

* [CZ04] Corvaja, Pietro, and Umberto Zannier. "On the rational approximations to
  the powers of an algebraic number: solution of two problems of Mahler and
  Mendès France." *Acta Mathematica* **193** (2004), 175–191. arXiv `math/0403522`.
  (Main Theorem, p. 2; not to be confused with their Theorem 1, the `q = 1, δ = 1`
  slice, which for rational `α` is Mahler 1957.)
-/

namespace CZ

/-- The absolute Weil height of `2^x·3^y ∈ ℚ*`: `max(numerator, denominator)` of
the reduced fraction, explicitly `max (2^{x⁺}·3^{y⁺}) (2^{x⁻}·3^{y⁻})`.
E.g. `H((3/2)^a) = max (3^a) (2^a) = 3^a` (`height23_neg_natCast`). -/
def height23 (x y : ℤ) : ℕ :=
  max (2 ^ x.toNat * 3 ^ y.toNat) (2 ^ (-x).toNat * 3 ^ (-y).toNat)

/-- The value `δ·q·u` of the Main Theorem under the exponent encoding
`u = 2^x·3^y` of `Γ = ⟨2, 3⟩`. -/
def sval (δ : ℚ) (q : ℕ) (x y : ℤ) : ℚ := δ * q * ((2 : ℚ) ^ x * (3 : ℚ) ^ y)

/-- Discharge of the spelled-out pseudo-Pisot clause of the Main Theorem
(`pseudoPisot_approx_of_subspace`, `CITED/CorvajaZannierProof.lean`):
over `ℚ`, a value with `‖v‖ > 0` is not an integer, hence (given `|v| > 1`) not
pseudo-Pisot.  [CZ04] Definition p. 2, specialized as in the module doc. -/
lemma not_intCast_of_distToNearestInt_pos {x : ℚ} (h : 0 < x.distToNearestInt) :
    ¬ ∃ n : ℤ, x = n :=
  Rat.not_exists_intCast_eq_of_distToNearestInt_pos h

/-- Height normalization for both consumers: `H(2^{-a}·3^a) = H((3/2)^a) = 3^a`. -/
lemma height23_neg_natCast (a : ℕ) : height23 (-(a : ℤ)) a = 3 ^ a := by
  unfold height23
  rw [Int.toNat_of_nonpos (by omega), neg_neg, Int.toNat_natCast]
  simp only [pow_zero, one_mul, mul_one]
  exact Nat.max_eq_left (Nat.pow_le_pow_left (by norm_num) a)

end CZ

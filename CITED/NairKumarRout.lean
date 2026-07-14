/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Finite.Basic
import ForMathlib.Data.Rat.NearestInt
import CITED.CorvajaZannier

/-!
# The Nair–Kumar–Rout S-unit tuple theorem (arXiv 2506.02898), ℚ-specialization

**⚠ PREPRINT STATUS**: [NKR25] is an **unrefereed arXiv preprint** (2506.02898,
v3, 18 Nov 2025).  Per the layered-QA policy this axiom is recorded as cited
with the preprint status prominently flagged; every consumer's axiom footprint
names it (`NKR.sUnit_pair_integrality`), and the NKR-free *conditional*
capstone (`TH.superlinear_of_middleBand`, middle band as a named hypothesis)
remains in place as the refereed-only fallback.  If the preprint fails review,
delete this file and the program falls back to that capstone unharmed.

**Theorem 1.3** of Nair–Kumar–Rout ([NKR25], p. 2; statement verified against
the paper 2026-07-06, including the §4.1 proof structure):

> Let `Γ ⊂ 𝔸*` be a finitely generated multiplicative group of algebraic
> numbers, `α₁, …, α_m` non-zero algebraic numbers, `ε₁ > 0`.  Let `𝒩₁'` be an
> **infinite** set of tuples `(u₁, …, u_m) ∈ Γ^m` with `|u_i| ≥ 1`, such that
> any two tuples have `u_i/u_j ≠ u_i'/u_j'` for `1 ≤ i ≠ j ≤ m`, each tuple
> satisfies properties (P1), (P2), and
>
>   `‖∑ α_i u_i‖ < (∏ H(u_i))^{-ε₁}`.                                     (1)
>
> Then there is an infinite subset of `𝒩₁'` on which (i) every `u_i` is an
> algebraic integer; (ii)–(iv) [conjugate size, pseudo-Pisot, Galois rigidity].

`‖·‖` is the distance to the nearest integer, `H` the absolute Weil height;
(P1): no nontrivial Galois conjugate of an entry differs from it by a root of
unity; (P2): entries equivalent modulo roots of unity are Galois conjugate.

## Statement conventions (the ℚ-specialization — all uses in this corpus)

Each direction *weakens* the source statement (safe):

* **Group**: `Γ = ⟨2, 3⟩ ≤ ℚ*`, exponent-encoded — `NKR.uval x y = 2^x·3^y`
  (a bijection onto `Γ`, so an infinite encoded set is an infinite tuple set).
* **Tuple length**: `m = 2` (all our uses), coefficients `α₁, α₂ ∈ ℚ*`
  (the source allows algebraic coefficients).
* **(P1)** is vacuous over `ℚ` (a rational has no Galois conjugate besides
  itself), hence dropped.  **(P2)** over `ℚ`: `μ ∩ ℚ = {±1}` and Galois
  conjugacy is equality, so the only nontrivial instance is `u₁ ≠ -u₂`
  (`u_i = -u_i` is excluded by `|u_i| ≥ 1`); spelled out as such.
* **Ratio condition**: both index orders `(1,2)` and `(2,1)` spelled out
  (they are equivalent over a group; kept for fidelity).
* **Height**: `H(2^x·3^y)` is the explicit `CZ.height23` (reused from the
  Corvaja–Zannier transcription); `‖·‖ = Rat.distToNearestInt`; the threshold
  `(H(u₁)H(u₂))^{-ε₁}` lives in `ℝ` via `rpow` with `ε₁ : ℝ` free.
* **Conclusion weakened twice**: only conclusion (i) (integrality) is
  transcribed, and "an infinite subset satisfies (i)" is weakened to "some
  element satisfies (i)" (infinite sets are nonempty).  Over `ℚ`, "algebraic
  integer" means "integer", transcribed as `∃ n : ℤ, u = n`.

The finiteness/existence is **ineffective** (Subspace-based).

Consumer ([M4A3] §6.3 route 1, formalized in `TH/GapDichotomy.lean`): the
infinitely-many-gaps branch of the middle-band dichotomy — one (K)-violating
pair per gap gives tuples `((3/2)^c, (3/2)^a)` with pairwise-distinct ratios
`(3/2)^{c-a}` and `‖u₁ − u₂‖ ≤ θ^c < (H(u₁)H(u₂))^{-ε₁}` for
`ε₁ = log θ⁻¹/(2 log 3)`; conclusion (i) forces `(3/2)^c ∈ ℤ`, absurd.

## Contents

* `NKR.uval` — the value `2^x·3^y` under the exponent encoding of `Γ = ⟨2,3⟩`.
* `NKR.uval_neg_natCast` — the consumer's instance `uval (-n) n = (3/2)^n`.
* `NKR.sUnit_pair_integrality` — **Theorem 1.3(i)** of [NKR25], ℚ-specialized;
  a cited Subspace-theorem consequence recorded as an `axiom` (preprint!).

## References

* [NKR25] Nair, Parvathi S., Veekesh Kumar, and S. S. Rout. "Algebraic
  approximations to linear combinations of S-units." arXiv:2506.02898
  (v3, 18 Nov 2025). **Unrefereed preprint.**  (Theorem 1.3; proof in §4 via
  the Evertse–Schlickewei Subspace theorem, adapting Kulkarni–Mavraki–Nguyen.)
* [M4A3] `plan-M4A3.html` (this repository, 2026-07): §6.3 (Stage 2c, primary
  route), §10.1 (M-0 verdict and caveat).
-/

namespace NKR

/-- The value `u = 2^x·3^y` of the Main-Theorem tuples under the exponent
encoding of `Γ = ⟨2, 3⟩`. -/
def uval (x y : ℤ) : ℚ := (2 : ℚ) ^ x * (3 : ℚ) ^ y

/-- The consumer's instance of the encoding: `uval (-n) n = (3/2)^n`. -/
lemma uval_neg_natCast (n : ℕ) : uval (-(n : ℤ)) n = (3 / 2 : ℚ) ^ n := by
  unfold uval
  rw [zpow_neg, zpow_natCast, zpow_natCast, div_pow, inv_mul_eq_div]

/-- **Theorem 1.3(i) of [NKR25]** (⚠ unrefereed preprint, v3 Nov 2025),
ℚ-specialized to pairs from `Γ = ⟨2, 3⟩` (see the module doc for the
specialization directions, all of which weaken the source): given nonzero
rationals `α₁, α₂` and `ε₁ > 0`, an **infinite** family `𝒩` of exponent-encoded
pairs `(u₁, u₂) ∈ Γ²` with `|u_i| ≥ 1`, `u₁ ≠ -u₂` (= property (P2) over `ℚ`;
(P1) is vacuous), pairwise-distinct ratios in both index orders, and

  `‖α₁u₁ + α₂u₂‖ < (H(u₁)·H(u₂))^{-ε₁}`

contains an element whose entries are both integers.  Recorded as a cited
`axiom` on the authority of [NKR25] — a Subspace-theorem argument
(their §4, via Prop. 4.1/4.2 and the Evertse S-unit equation theorem) we do
not re-derive.  Ineffective. -/
axiom sUnit_pair_integrality
    (α₁ α₂ : ℚ) (hα₁ : α₁ ≠ 0) (hα₂ : α₂ ≠ 0) (ε₁ : ℝ) (hε₁ : 0 < ε₁)
    (𝒩 : Set ((ℤ × ℤ) × (ℤ × ℤ))) (hinf : 𝒩.Infinite)
    (habs : ∀ q ∈ 𝒩, 1 ≤ |uval q.1.1 q.1.2| ∧ 1 ≤ |uval q.2.1 q.2.2|)
    (hP2 : ∀ q ∈ 𝒩, uval q.1.1 q.1.2 ≠ -uval q.2.1 q.2.2)
    (hratio : ∀ q ∈ 𝒩, ∀ q' ∈ 𝒩, q ≠ q' →
      uval q.1.1 q.1.2 / uval q.2.1 q.2.2 ≠ uval q'.1.1 q'.1.2 / uval q'.2.1 q'.2.2 ∧
      uval q.2.1 q.2.2 / uval q.1.1 q.1.2 ≠ uval q'.2.1 q'.2.2 / uval q'.1.1 q'.1.2)
    (happrox : ∀ q ∈ 𝒩,
      ((α₁ * uval q.1.1 q.1.2 + α₂ * uval q.2.1 q.2.2).distToNearestInt : ℝ)
        < ((CZ.height23 q.1.1 q.1.2 * CZ.height23 q.2.1 q.2.2 : ℕ) : ℝ) ^ (-ε₁)) :
    ∃ q ∈ 𝒩, (∃ n : ℤ, uval q.1.1 q.1.2 = n) ∧ (∃ n : ℤ, uval q.2.1 q.2.2 = n)

end NKR

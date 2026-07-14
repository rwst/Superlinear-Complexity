/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic



/-!
# The Subspace Theorem (Schmidt / Evertse–Schlickewei), cited

The `S`-arithmetic **Subspace Theorem** — Schmidt's Theorem 1D′ in the
Evertse–Schlickewei number-field form — recorded here as *one* canonical cited
`axiom`, the single deepest Diophantine engine behind the `(3/2)ⁿ` complexity
program.  It is the black box that **both** currently-bespoke axioms of the
program bottom out at:

* the [CZ04] Main Theorem is this theorem at `n = 2` with a *fixed* linear
  form — i.e. **Ridout's theorem** — applied once; **derivation complete**:
  `CZ.pseudoPisot_approx_of_subspace` (`CITED/CorvajaZannierProof.lean`,
  sorry-free 2026-07-14), the bespoke axiom retired.
* `NKR.sUnit_pair_integrality` (`CITED/NairKumarRout.lean`) is this theorem at
  `n = 3` over `ℚ`, via [NKR25] Proposition 4.1 (`report-formalize-subspace.html` §4).

Recording it once, and *deriving* those two consequences in Lean, collapses the
program's Mahler-problem / `S`-unit Diophantine backbone to a single famous
axiom (Ridout is itself a corollary of the Subspace Theorem, so the whole
`Roth → Ridout → Subspace` tower reduces to this one statement).  Until those
derivations are formalized this file **coexists** with the two bespoke axioms;
it does not yet replace them.

## The theorem

> Let `K` be a number field, `n ≥ 2`, and `S` a finite set of places of `K`
> containing the archimedean ones.  For each `v ∈ S` let `L_{v,1}, …, L_{v,n}`
> be `n` linearly independent linear forms in `X_1, …, X_n` with coefficients in
> `K`.  For every `ε > 0`, the nonzero solutions `x ∈ Kⁿ` of
> $$ \prod_{v \in S} \prod_{i=1}^n \frac{|L_{v,i}(x)|_v}{\lVert x\rVert_v}
>     \ \le\ H(x)^{-n-\varepsilon} $$
> lie in **finitely many proper linear subspaces** of `Kⁿ`.

Here `‖x‖_v = maxᵢ |x_i|_v` is the local sup-norm and `H(x) = ∏_v ‖x‖_v` the
absolute (projective) multiplicative height — exactly Mathlib's
`Height.mulHeight`, whose definition uses the *same* local norm `⨆ i, v (x i)`
over the admissible family `Height.AdmissibleAbsValues`.

## Encoding conventions (and safe weakenings)

Recorded on the authority of [S] / [BG06]; a faithful transcription, with the
following documented choices (each of which a consumer may only *weaken*):

* **Field**: stated for a general `[NumberField K]`.  Every consumer specializes
  `K := ℚ` (degree 1); the ready-made `Subspace.evertseSchlickewei_rat` is that
  instantiation.
* **Places**: `S : Finset (AbsoluteValue K ℝ)`.  In use `S` is a finite set of
  the admissible places (the members of `Height.AdmissibleAbsValues.archAbsVal`
  and `.nonarchAbsVal`) containing all archimedean ones — e.g. `{∞, 2, 3}` over
  `ℚ`.  As with the sibling cited axioms this membership is documented, not
  enforced structurally.
* **Forms**: `L v : Fin n → ((Fin n → K) →ₗ[K] K)`, `K`-linear forms with
  coefficients in `K`, required linearly independent per place (`hL`).  For the
  `ℚ`-consumers the forms have *rational* coefficients (e.g. `x₀ − δ·x₁` with
  `δ ∈ ℚ`, and coordinate forms), a special case of the general statement.
* **Norm / threshold**: the local norm is `⨆ i, v (x i)` (Mathlib's), the
  double product is `Subspace.approxProduct`, and `H(x)^{-n-ε}` lives in `ℝ` via
  `rpow` with `ε : ℝ` free.  Matches [NKR25] Theorem 2.1 verbatim.
* **Conclusion**: `∃ T : Finset (Submodule K (Fin n → K))`, all members proper
  (`W ≠ ⊤`), covering every solution.  The finiteness is **ineffective**
  (Subspace-based): no bound on the number or the height of the subspaces.

## Contents

* `Subspace.localNorm` — the local sup-norm `‖x‖_v = ⨆ i |x_i|_v`.
* `Subspace.approxProduct` — the double product `∏_{v∈S} ∏_i |L_{v,i}(x)|_v/‖x‖_v`.
* `Subspace.evertseSchlickewei` — **the Subspace Theorem** ([S] Thm 1D′), a cited
  `axiom`; finitely many proper subspaces contain all solutions.
* `Subspace.evertseSchlickewei_rat` — the `K := ℚ` specialization consumers use.

## References

* [S] W. M. Schmidt, *Diophantine Approximation and Diophantine Equations*,
  Lecture Notes in Math. **1467**, Springer 1991 — Theorem 1D′ (`S`-arithmetic
  Subspace) and Theorem 2A (Roth); the sole external input of [CZ04]'s Main
  Theorem.
* [BG06] E. Bombieri, W. Gubler, *Heights in Diophantine Geometry*, Cambridge
  2006, Ch. 7 — the form of the Subspace Theorem quoted by [NKR25] (their
  Theorem 2.1).
* [CZ04] Corvaja–Zannier, Acta Math. **193** (2004), 175–191 (`CITED/CorvajaZannier.lean`).
* [NKR25] Nair–Kumar–Rout, arXiv:2506.02898v3 (`CITED/NairKumarRout.lean`).
* `report-formalize-subspace.html` (this repository, 2026-07): the dependency
  analysis and effort estimate that motivates this file; §3 (CZ → Ridout),
  §4 (NKR → Subspace n = 3), §6 (the one-axiom refactor).
* [M4A3] `plan-M4A3.html`, §5–6.
-/

namespace Subspace

variable {K : Type*} [Field K] [NumberField K]

/-- The local sup-norm `‖x‖_v = maxᵢ |x_i|_v` at a place `v`, as an `ℝ`-value.
This is the very quantity Mathlib's `Height.mulHeight` maximizes over the
coordinates at each place. -/
noncomputable def localNorm {n : ℕ} (v : AbsoluteValue K ℝ) (x : Fin n → K) : ℝ :=
  ⨆ i, v (x i)

/-- The Subspace-Theorem double product `∏_{v∈S} ∏_i |L_{v,i}(x)|_v / ‖x‖_v`
whose smallness (below `H(x)^{-n-ε}`) confines `x` to finitely many subspaces. -/
noncomputable def approxProduct {n : ℕ} (S : Finset (AbsoluteValue K ℝ))
    (L : AbsoluteValue K ℝ → Fin n → ((Fin n → K) →ₗ[K] K)) (x : Fin n → K) : ℝ :=
  ∏ v ∈ S, ∏ i, v (L v i x) / localNorm v x

/-- **The Subspace Theorem** ([S], Theorem 1D′; Evertse–Schlickewei
`S`-arithmetic form, [BG06] Ch. 7): for a number field `K`, `n ≥ 2`, a finite
place set `S`, per-place linearly independent linear forms `L`, and `ε > 0`, the
nonzero `x ∈ Kⁿ` with `approxProduct S L x ≤ H(x)^{-n-ε}` lie in finitely many
proper subspaces of `Kⁿ`.

Recorded as a cited `axiom` on the authority of [S] — a geometry-of-numbers +
heights-of-subspaces argument (successive minima, twisted heights, the
generalized Roth machinery) that we do not re-derive.  The finiteness is
ineffective.  See the module doc for the encoding conventions and the two
`ℚ`-consumers (the derived `CZ.pseudoPisot_approx_of_subspace` at `n = 2`,
`NKR.sUnit_pair_integrality` at `n = 3`). -/
axiom evertseSchlickewei {n : ℕ} (hn : 2 ≤ n)
    (S : Finset (AbsoluteValue K ℝ))
    (L : AbsoluteValue K ℝ → Fin n → ((Fin n → K) →ₗ[K] K))
    (hL : ∀ v ∈ S, LinearIndependent K (L v))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (Fin n → K)),
      (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : Fin n → K, x ≠ 0 →
        approxProduct S L x ≤ Height.mulHeight x ^ (-(n : ℝ) - ε) →
        ∃ W ∈ T, x ∈ W

/-- The `K := ℚ` specialization of `evertseSchlickewei` — the form the program's
consumers use (`Γ = ⟨2,3⟩ ⊂ ℚ*`, places `{∞, 2, 3}`, rational-coefficient
forms).  A direct instantiation of the cited axiom, hence itself axiom-clean. -/
theorem evertseSchlickewei_rat {n : ℕ} (hn : 2 ≤ n)
    (S : Finset (AbsoluteValue ℚ ℝ))
    (L : AbsoluteValue ℚ ℝ → Fin n → ((Fin n → ℚ) →ₗ[ℚ] ℚ))
    (hL : ∀ v ∈ S, LinearIndependent ℚ (L v))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : Finset (Submodule ℚ (Fin n → ℚ)),
      (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : Fin n → ℚ, x ≠ 0 →
        approxProduct S L x ≤ Height.mulHeight x ^ (-(n : ℝ) - ε) →
        ∃ W ∈ T, x ∈ W :=
  evertseSchlickewei hn S L hL ε hε

end Subspace

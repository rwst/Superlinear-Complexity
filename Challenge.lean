/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib

/-!
# The comparator challenge: what this repository claims, stated against Mathlib alone

This file is the **trusted statement of record** for `leanprover/comparator`
(see `comparator/kernel.json`, `comparator/capstone.json`, and `lake test`).

It imports *nothing but Mathlib*, and it re-declares — verbatim — every definition that
occurs in the two theorems being certified, followed by those two theorems with `sorry`
proofs.  `Solution.lean` merely imports the real development.  Comparator then checks that

1. every constant in the transitive closure of these statements is **identical** in the
   challenge and the solution environments (so the definitions below really are the ones
   the repository proves things about — a divergent `complexity` or `kernelViolators`
   would be caught here),
2. the solution's proofs use **no axioms beyond those permitted** by the config, and
3. the solution's environment is **re-accepted by the Lean kernel** from a fresh export.

Consequently, auditing this repository's headline claims reduces to reading *this file*:
if the definitions below say what you think they say, comparator has verified the rest.

## The two configurations, and why there are two

The repository's docstrings claim a specific *axiom stratification*, and the two configs
pin it down mechanically:

* `comparator/kernel.json` certifies `TH.superlinear_of_kernel` — the Stage-1 reduction
  (K) ⟹ M4 — under the three standard axioms **only**: `propext`, `Quot.sound`,
  `Classical.choice`.  No cited literature enters here.
* `comparator/capstone.json` certifies `TH.superlinear_of_middleBand` — the conditional
  capstone — under those three **plus** the single cited axiom
  `Subspace.evertseSchlickewei` (the Subspace Theorem, Evertse–Schlickewei
  `S`-arithmetic form), which is therefore also declared below, verbatim, so that a
  reader sees exactly what is being taken on faith.

Note that permitting an axiom by name is *not* a loophole: comparator compares the types
of permitted axioms across the two environments too, so the solution cannot smuggle in a
`Subspace.evertseSchlickewei : False`.

Nothing here is proved; the `sorry`s are the point.  The proofs live in `TH.KernelReduction`
and `TH.CapstoneM4`.
-/

namespace Rat

/-- The distance from a rational number to the nearest integer. -/
def distToNearestInt (x : ℚ) : ℚ := |x - round x|

end Rat

namespace TH

/-- `m n` is the nearest integer to `(3/2)^n`. -/
def m (n : ℕ) : ℤ := round ((3 / 2 : ℚ) ^ n)

/-- The steering letter `t n = 2·m (n+1) − 3·m n`. -/
def t (n : ℕ) : ℤ := 2 * m (n + 1) - 3 * m n

/-- The length-`k` factor (window) of the steering word at position `a`. -/
def factor (a k : ℕ) : Fin k → ℤ := fun i => t (a + i)

/-- `p_T(k)`: the subword complexity of the steering word — the number of distinct
length-`k` factors. -/
noncomputable def complexity (k : ℕ) : ℕ :=
  (Set.range fun a : ℕ => factor a k).ncard

/-- The (K)-violating pairs at scale `θ`: `2 ≤ a < c` with
`‖(3/2)^c − (3/2)^a‖ ≤ θ^c`. -/
def kernelViolators (θ : ℚ) : Set (ℕ × ℕ) :=
  {p | 2 ≤ p.1 ∧ p.1 < p.2 ∧
    ((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1).distToNearestInt ≤ θ ^ p.2}

/-- **Exponential pair repulsion at scale `θ`**: only finitely many (K)-violating pairs. -/
def PairRepulsion (θ : ℚ) : Prop := (kernelViolators θ).Finite

/-- **The Diophantine kernel (K)**: pair repulsion at every rational scale `θ ∈ (0, 1)`. -/
def Kernel : Prop := ∀ θ : ℚ, 0 < θ → θ < 1 → PairRepulsion θ

/-- **M4**: the subword complexity of the steering word is superlinear, `p_T(k)/k → ∞`. -/
def Superlinear : Prop := ∀ C : ℕ, ∃ K : ℕ, ∀ k, K ≤ k → C * k < complexity k

/-- The **middle band** of the kernel at scale `θ`: (K)-violating pairs with late earlier
occurrence (`ε′·c ≤ a`) and gap at least `S`. -/
def middleBandViolators (θ ε' : ℚ) (S : ℕ) : Set (ℕ × ℕ) :=
  {p ∈ kernelViolators θ | ε' * p.2 ≤ (p.1 : ℚ) ∧ p.1 + S ≤ p.2}

/-- **Stage 1 reduction, (K) ⟹ M4**: exponential pair repulsion at every rational scale
forces superlinear subword complexity of the steering word.

Certified by `comparator/kernel.json` under the standard axioms only. -/
theorem superlinear_of_kernel (hK : Kernel) : Superlinear := sorry

/-- **The conditional capstone (M4 from the middle-band kernel)**: if for every rational
scale `θ ∈ (0, 1)` and every `ε′ > 0` there is a gap threshold `S` making the middle band
finite, then the steering word has superlinear subword complexity, `p_T(k)/k → ∞`.

Certified by `comparator/capstone.json` under the standard axioms plus the cited
`Subspace.evertseSchlickewei`. -/
theorem superlinear_of_middleBand
    (hmid : ∀ θ : ℚ, 0 < θ → θ < 1 → ∀ ε' : ℚ, 0 < ε' →
      ∃ S : ℕ, (middleBandViolators θ ε' S).Finite) :
    Superlinear := sorry

end TH

namespace Subspace

variable {K : Type*} [Field K] [NumberField K]

/-- The local sup-norm `‖x‖_v = maxᵢ |x_i|_v` at a place `v`, as an `ℝ`-value. -/
noncomputable def localNorm {n : ℕ} (v : AbsoluteValue K ℝ) (x : Fin n → K) : ℝ :=
  ⨆ i, v (x i)

/-- The Subspace-Theorem double product `∏_{v∈S} ∏_i |L_{v,i}(x)|_v / ‖x‖_v`. -/
noncomputable def approxProduct {n : ℕ} (S : Finset (AbsoluteValue K ℝ))
    (L : AbsoluteValue K ℝ → Fin n → ((Fin n → K) →ₗ[K] K)) (x : Fin n → K) : ℝ :=
  ∏ v ∈ S, ∏ i, v (L v i x) / localNorm v x

/-- **The Subspace Theorem** (Schmidt, Theorem 1D′; Evertse–Schlickewei `S`-arithmetic
form): for a number field `K`, `n ≥ 2`, a finite place set `S`, per-place linearly
independent linear forms `L`, and `ε > 0`, the nonzero `x ∈ Kⁿ` with
`approxProduct S L x ≤ H(x)^{-n-ε}` lie in finitely many proper subspaces of `Kⁿ`.

**This is the one piece of cited literature the capstone rests on.**  It is *not* proved
in this repository and is not intended to be; it is recorded here so that
`comparator/capstone.json` may permit it by name while comparator simultaneously pins its
statement — the solution must declare an axiom of exactly this type. -/
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

end Subspace

/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TH.GapSlices

/-!
# The conditional capstone: M4 from the middle-band kernel

Milestone M-5 of the M4/A3 program ([M4A3] §9): the conditional capstone in the
house `hexc` pattern (mirroring `paradoxical/BakerReduction.lean`).

After Stage 2b and 2b′ (`TH.GapSlices`), what remains open of the kernel (K) is
exactly the **middle band**: (K)-violating pairs `(a, c)` whose earlier
occurrence sits *late* (`a ≥ ε′·c`) *and* whose gap grows (`c − a ≥ S`).  The
bounded-gap part (`c − a ≤ S`) and the huge-gap band (`a ≤ ε′·c`) are theorems
modulo the cited CZ 2004 axiom.  So:

* `pairRepulsion_of_middleBand` — pair repulsion at scale `θ` follows from
  finiteness of the middle band alone, by the three-way decomposition
  `kernelViolators θ ⊆ hugeGap ∪ gapBounded ∪ middleBand`.
* `superlinear_of_middleBand` — **the capstone**: the middle-band hypothesis
  (for every scale `θ` and every `ε′ > 0`, some gap threshold `S` makes the
  middle band finite) implies M4, `p_T(k)/k → ∞`.

The middle-band hypothesis `hmid` is the open Stage-2c kernel — consumed as a
named HYPOTHESIS, never an axiom, per the layered-QA policy (open conjectures
are never axiomatized).  Stage 2c ([M4A3] §6.3) attacks it: primary route the
NKR gap dichotomy (arXiv:2506.02898 Thm 1.3 + CZ 2004), fallback the
`λ_s`-as-coordinate Subspace form system.  Note the quantifier order: the
prover of `hmid` receives `ε′` (so may assume it as small as convenient) and
chooses `S` — the weakest form the decomposition supports, since 2b′ supplies
only *some* `ε′(θ) > 0`.

Axiom footprint: std3 + `CZ.pseudoPisot_approx` ([CZ04]).  With this file, the
Lean side of the program is complete modulo Stage 2c ([M4A3] §9, M-5).

## Contents

* `TH.middleBandViolators` — the middle band of the kernel at scale `θ`.
* `TH.pairRepulsion_of_middleBand` — (K) at scale `θ` from its middle band.
* `TH.superlinear_of_middleBand` — **the conditional capstone**: middle-band
  repulsion ⟹ M4.

## References

* [M4A3] `plan-M4A3.html` (this repository, 2026-07): §6.3 (Stage 2c), §9
  (architecture, milestone M-5).
* [CZ04] Corvaja, Zannier. *On the rational approximations to the powers of an
  algebraic number.* Acta Math. **193** (2004), 175–191.
-/

namespace TH

/-- The **middle band** of the kernel at scale `θ`: (K)-violating pairs with
late earlier occurrence (`ε′·c ≤ a`) and gap at least `S`.  After the CZ slices
of `TH.GapSlices`, this is all that remains of (K) — the open Stage-2c target
([M4A3] §6.3). -/
def middleBandViolators (θ ε' : ℚ) (S : ℕ) : Set (ℕ × ℕ) :=
  {p ∈ kernelViolators θ | ε' * p.2 ≤ (p.1 : ℚ) ∧ p.1 + S ≤ p.2}

/-- Pair repulsion at scale `θ` from middle-band repulsion: the huge-gap band is
finite (Stage 2b′) and the gap-bounded part is finite (Stage 2b), so the middle
band is all that (K) still needs.  [M4A3] §6.2′/§9.  Footprint std3 + [CZ04]. -/
theorem pairRepulsion_of_middleBand (θ : ℚ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hmid : ∀ ε' : ℚ, 0 < ε' → ∃ S : ℕ, (middleBandViolators θ ε' S).Finite) :
    PairRepulsion θ := by
  obtain ⟨ε', hε'0, hhuge⟩ := hugeGap_slice_finite θ hθ0 hθ1
  obtain ⟨S, hmidfin⟩ := hmid ε' hε'0
  have hsub : kernelViolators θ ⊆
      {p ∈ kernelViolators θ | (p.1 : ℚ) ≤ ε' * p.2}
      ∪ {p ∈ kernelViolators θ | p.2 ≤ p.1 + S}
      ∪ middleBandViolators θ ε' S := by
    intro p hp
    rcases le_total (p.1 : ℚ) (ε' * p.2) with h | h
    · exact Or.inl (Or.inl ⟨hp, h⟩)
    · rcases le_total p.2 (p.1 + S) with h2 | h2
      · exact Or.inl (Or.inr ⟨hp, h2⟩)
      · exact Or.inr ⟨hp, h, h2⟩
  exact Set.Finite.subset
    ((hhuge.union (gapBounded_slice_finite S θ hθ0 hθ1)).union hmidfin) hsub

/-- **The conditional capstone (M4 from the middle-band kernel)** ([M4A3] §9):
if for every rational scale `θ ∈ (0, 1)` and every `ε′ > 0` there is a gap
threshold `S` making the middle band finite, then the steering word has
superlinear subword complexity, `p_T(k)/k → ∞`.

The hypothesis is the open Stage-2c kernel, consumed in the house `hexc`
pattern (a named hypothesis, never an axiom); the bounded-gap and huge-gap
parts of (K) are discharged via the cited CZ 2004 Main Theorem, and the
reduction to (K) is the std3 Stage-1 pigeonhole.  Footprint std3 + [CZ04]. -/
theorem superlinear_of_middleBand
    (hmid : ∀ θ : ℚ, 0 < θ → θ < 1 → ∀ ε' : ℚ, 0 < ε' →
      ∃ S : ℕ, (middleBandViolators θ ε' S).Finite) :
    Superlinear :=
  superlinear_of_kernel fun θ hθ0 hθ1 =>
    pairRepulsion_of_middleBand θ hθ0 hθ1 (hmid θ hθ0 hθ1)

end TH

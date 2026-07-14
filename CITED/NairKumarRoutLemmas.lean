/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import CITED.NairKumarRout
import CITED.CorvajaZannierProof



/-!
# Machinery for deriving the Nair–Kumar–Rout pair theorem from the Subspace Theorem

Support lemmas for `CITED/NairKumarRoutProof.lean` (the `n = 3` half of the one-axiom
refactor, `report-formalize-subspace.html` §4/§6): the `S`-unit `uval = 2^x·3^y` API
(product formula at `S = {∞,2,3}`, numerator/denominator, exact `mulHeight₁`),
sub-multiplicativity of `height23` under exponent differences, the `n = 3` linear
forms `Lforms3` with their closed-form Subspace product on gcd-1 integer triples,
**`member_solves`** (a member's triple `(p₀, u₁, u₂)` solves the Subspace inequality
`approxProduct ≤ mulHeight^{-3-ε₁/4}`), and the two Diophantine finiteness leaves:
`sUnit_near_ratio_finite` (`S`-units approaching a fixed positive rational — the
`q = 1` Corvaja–Zannier instance, via `CZ.pseudoPisot_approx_of_subspace`) and the
opposite-sign case `opposite_case_finite`.

Everything here is **sorry-free**; axiom footprint `std3 + Subspace.evertseSchlickewei`
(through the derived CZ theorem — no bespoke axiom).

## References

* [NKR25] Nair–Kumar–Rout, arXiv:2506.02898v3 (`CITED/NairKumarRout.lean`).
* [CZ04] Corvaja–Zannier, Acta Math. **193** (2004) (`CITED/CorvajaZannierProof.lean`).
* [S] W. M. Schmidt, LNM **1467**, Theorem 1D′ (`CITED/SubspaceTheorem.lean`).
* `report-formalize-subspace.html` §4, §6 (this repository).
-/

namespace NKR

open Subspace Rat.AbsoluteValue Height CZ

/-! ### Stage 1: `S`-unit helpers -/

lemma uval_pos (x y : ℤ) : 0 < uval x y := by
  unfold NKR.uval
  positivity

lemma uval_ne_zero (x y : ℤ) : uval x y ≠ 0 := (uval_pos x y).ne'

lemma uval_div (x₁ y₁ x₂ y₂ : ℤ) :
    uval x₁ y₁ / uval x₂ y₂ = uval (x₁ - x₂) (y₁ - y₂) := by
  unfold NKR.uval
  rw [zpow_sub₀ (by norm_num : (2:ℚ) ≠ 0), zpow_sub₀ (by norm_num : (3:ℚ) ≠ 0)]
  field_simp

lemma uval_injective {x y x' y' : ℤ} (h : uval x y = uval x' y') : x = x' ∧ y = y' := by
  have h2 := congrArg (padic 2) h
  have h3 := congrArg (padic 3) h
  rw [show uval x y = (2:ℚ)^x * (3:ℚ)^y from rfl,
    show uval x' y' = (2:ℚ)^x' * (3:ℚ)^y' from rfl] at h2 h3
  rw [padic_two_sUnit, padic_two_sUnit] at h2
  rw [padic_three_sUnit, padic_three_sUnit] at h3
  constructor
  · have := zpow_right_injective₀ (by norm_num : (0:ℝ) < 2) (by norm_num) h2
    omega
  · have := zpow_right_injective₀ (by norm_num : (0:ℝ) < 3) (by norm_num) h3
    omega

/-- **Product formula for the `S`-unit** at `S = {∞, 2, 3}`:
`|u|·|u|₂·|u|₃ = 1` for `u = 2^x·3^y`. -/
lemma real_padic_uval (x y : ℤ) :
    real (uval x y) * (padic 2 (uval x y) * padic 3 (uval x y)) = 1 := by
  have hu : uval x y = (2:ℚ)^x * (3:ℚ)^y := rfl
  rw [hu, padic_two_sUnit, padic_three_sUnit, real_eq_abs,
    abs_of_pos (by positivity : (0:ℚ) < (2:ℚ)^x * (3:ℚ)^y)]
  push_cast
  rw [show ((2:ℝ)^x * (3:ℝ)^y) * ((2:ℝ)^(-x) * (3:ℝ)^(-y))
      = ((2:ℝ)^x * (2:ℝ)^(-x)) * ((3:ℝ)^y * (3:ℝ)^(-y)) by ring,
    ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), ← zpow_add₀ (by norm_num : (3:ℝ) ≠ 0)]
  simp

/-- Sub-multiplicativity of `height23` under exponent differences:
`H(u₁/u₂) ≤ H(u₁)·H(u₂)`. -/
lemma height23_sub_le (x₁ y₁ x₂ y₂ : ℤ) :
    height23 (x₁ - x₂) (y₁ - y₂) ≤ height23 x₁ y₁ * height23 x₂ y₂ := by
  unfold CZ.height23
  have hN : 2 ^ (x₁ - x₂).toNat * 3 ^ (y₁ - y₂).toNat
      ≤ (2 ^ x₁.toNat * 3 ^ y₁.toNat) * (2 ^ (-x₂).toNat * 3 ^ (-y₂).toNat) := by
    have e2 : (x₁ - x₂).toNat ≤ x₁.toNat + (-x₂).toNat := by omega
    have e3 : (y₁ - y₂).toNat ≤ y₁.toNat + (-y₂).toNat := by omega
    calc 2 ^ (x₁ - x₂).toNat * 3 ^ (y₁ - y₂).toNat
        ≤ 2 ^ (x₁.toNat + (-x₂).toNat) * 3 ^ (y₁.toNat + (-y₂).toNat) :=
          Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) e2)
            (Nat.pow_le_pow_right (by norm_num) e3)
      _ = (2 ^ x₁.toNat * 3 ^ y₁.toNat) * (2 ^ (-x₂).toNat * 3 ^ (-y₂).toNat) := by
          rw [pow_add, pow_add]; ring
  have hD : 2 ^ (-(x₁ - x₂)).toNat * 3 ^ (-(y₁ - y₂)).toNat
      ≤ (2 ^ (-x₁).toNat * 3 ^ (-y₁).toNat) * (2 ^ x₂.toNat * 3 ^ y₂.toNat) := by
    have e2 : (-(x₁ - x₂)).toNat ≤ (-x₁).toNat + x₂.toNat := by omega
    have e3 : (-(y₁ - y₂)).toNat ≤ (-y₁).toNat + y₂.toNat := by omega
    calc 2 ^ (-(x₁ - x₂)).toNat * 3 ^ (-(y₁ - y₂)).toNat
        ≤ 2 ^ ((-x₁).toNat + x₂.toNat) * 3 ^ ((-y₁).toNat + y₂.toNat) :=
          Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) e2)
            (Nat.pow_le_pow_right (by norm_num) e3)
      _ = (2 ^ (-x₁).toNat * 3 ^ (-y₁).toNat) * (2 ^ x₂.toNat * 3 ^ y₂.toNat) := by
          rw [pow_add, pow_add]; ring
  apply Nat.max_le.mpr
  constructor
  · exact hN.trans (Nat.mul_le_mul (le_max_left _ _) (le_max_right _ _))
  · exact hD.trans (Nat.mul_le_mul (le_max_right _ _) (le_max_left _ _))

/-- The numerator and denominator of `2^x·3^y` are coprime. -/
lemma coprime_N_D (x y : ℤ) :
    Nat.Coprime (2 ^ x.toNat * 3 ^ y.toNat) (2 ^ (-x).toNat * 3 ^ (-y).toNat) := by
  have h23 : Nat.Coprime 2 3 := by norm_num
  have h2 : Nat.Coprime (2 ^ x.toNat) (2 ^ (-x).toNat) := by
    rcases le_or_gt 0 x with hx | hx
    · rw [show (-x).toNat = 0 by omega, pow_zero]
      exact Nat.coprime_one_right _
    · rw [show x.toNat = 0 by omega, pow_zero]
      exact Nat.coprime_one_left _
  have h3 : Nat.Coprime (3 ^ y.toNat) (3 ^ (-y).toNat) := by
    rcases le_or_gt 0 y with hy | hy
    · rw [show (-y).toNat = 0 by omega, pow_zero]
      exact Nat.coprime_one_right _
    · rw [show y.toNat = 0 by omega, pow_zero]
      exact Nat.coprime_one_left _
  exact Nat.Coprime.mul_left
    (Nat.Coprime.mul_right h2 (Nat.Coprime.pow _ _ h23))
    (Nat.Coprime.mul_right (Nat.Coprime.pow _ _ h23.symm) h3)

/-- `u·D = N`: clearing the denominator of the `S`-unit. -/
lemma uval_mul_D_eq_N (x y : ℤ) :
    uval x y * ((2 ^ (-x).toNat * 3 ^ (-y).toNat : ℕ) : ℚ)
      = ((2 ^ x.toNat * 3 ^ y.toNat : ℕ) : ℚ) := by
  unfold NKR.uval
  push_cast
  rw [show ((2:ℚ) ^ ((-x).toNat)) = (2:ℚ) ^ (((-x).toNat : ℤ)) from (zpow_natCast _ _).symm,
    show ((3:ℚ) ^ ((-y).toNat)) = (3:ℚ) ^ (((-y).toNat : ℤ)) from (zpow_natCast _ _).symm,
    show ((2:ℚ) ^ (x.toNat)) = (2:ℚ) ^ ((x.toNat : ℤ)) from (zpow_natCast _ _).symm,
    show ((3:ℚ) ^ (y.toNat)) = (3:ℚ) ^ ((y.toNat : ℤ)) from (zpow_natCast _ _).symm,
    show (2:ℚ)^x * (3:ℚ)^y * ((2:ℚ) ^ (((-x).toNat : ℤ)) * (3:ℚ) ^ (((-y).toNat : ℤ)))
      = ((2:ℚ)^x * (2:ℚ) ^ (((-x).toNat : ℤ))) * ((3:ℚ)^y * (3:ℚ) ^ (((-y).toNat : ℤ))) by ring,
    ← zpow_add₀ (by norm_num : (2:ℚ) ≠ 0), ← zpow_add₀ (by norm_num : (3:ℚ) ≠ 0)]
  congr 1
  · congr 1
    omega
  · congr 1
    omega

/-- The `S`-unit as a reduced fraction: `uval x y = N / D`. -/
lemma uval_eq_N_div_D (x y : ℤ) :
    uval x y = ((2 ^ x.toNat * 3 ^ y.toNat : ℕ) : ℚ) / ((2 ^ (-x).toNat * 3 ^ (-y).toNat : ℕ) : ℚ) := by
  have hD : ((2 ^ (-x).toNat * 3 ^ (-y).toNat : ℕ) : ℚ) ≠ 0 := by positivity
  rw [eq_div_iff hD]
  exact uval_mul_D_eq_N x y

/-- The numerator of the `S`-unit `2^x·3^y` is `N = 2^{x⁺}·3^{y⁺}`. -/
lemma uval_num (x y : ℤ) : (uval x y).num = ((2 ^ x.toNat * 3 ^ y.toNat : ℕ) : ℤ) := by
  rw [uval_eq_N_div_D x y,
    show ((2 ^ x.toNat * 3 ^ y.toNat : ℕ) : ℚ) = (((2 ^ x.toNat * 3 ^ y.toNat : ℕ) : ℤ) : ℚ) by
      push_cast; ring,
    show ((2 ^ (-x).toNat * 3 ^ (-y).toNat : ℕ) : ℚ)
      = (((2 ^ (-x).toNat * 3 ^ (-y).toNat : ℕ) : ℤ) : ℚ) by push_cast; ring]
  apply Rat.num_div_eq_of_coprime
  · exact_mod_cast Nat.pos_of_ne_zero (by positivity)
  · rw [Int.natAbs_natCast, Int.natAbs_natCast]
    exact coprime_N_D x y

/-- The denominator of the `S`-unit `2^x·3^y` is `D = 2^{x⁻}·3^{y⁻}`. -/
lemma uval_den (x y : ℤ) : (uval x y).den = 2 ^ (-x).toNat * 3 ^ (-y).toNat := by
  have hb0 : (0:ℤ) < ((2 ^ (-x).toNat * 3 ^ (-y).toNat : ℕ) : ℤ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by positivity)
  have hcop : Nat.Coprime (((2 ^ x.toNat * 3 ^ y.toNat : ℕ) : ℤ)).natAbs
      (((2 ^ (-x).toNat * 3 ^ (-y).toNat : ℕ) : ℤ)).natAbs := by
    rw [Int.natAbs_natCast, Int.natAbs_natCast]
    exact coprime_N_D x y
  have h := Rat.den_div_eq_of_coprime hb0 hcop
  have huv : uval x y = (((2 ^ x.toNat * 3 ^ y.toNat : ℕ) : ℤ) : ℚ)
      / (((2 ^ (-x).toNat * 3 ^ (-y).toNat : ℕ) : ℤ) : ℚ) := by
    rw [uval_eq_N_div_D x y]
    push_cast
    ring
  rw [huv]
  exact_mod_cast h

/-- **`mulHeight₁` of the `S`-unit is exactly `height23`.** -/
lemma mulHeight₁_uval (x y : ℤ) :
    mulHeight₁ (uval x y) = ((height23 x y : ℕ) : ℝ) := by
  rw [Rat.mulHeight₁_eq_max, uval_num, uval_den, Int.natAbs_natCast]
  unfold CZ.height23
  push_cast
  rfl

/-! ### Stage 2: the linear forms, local norms, and integer-representative tooling -/

private lemma padic_int_zpow' (p : ℕ) [Fact p.Prime] (m : ℤ) (hm : m ≠ 0) :
    padic p (m : ℚ) = (p : ℝ) ^ (-(padicValNat p m.natAbs : ℤ)) := by
  rw [padic_eq_padicNorm, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hm),
    padicValRat.of_int]
  push_cast [padicValInt]
  norm_num

/-- The `S = {∞,2,3}` product of a nonzero integer is at least `1` (it equals the
prime-to-6 part). -/
lemma one_le_real_padic23_int (g : ℤ) (hg : g ≠ 0) :
    1 ≤ real (g : ℚ) * (padic 2 (g : ℚ) * padic 3 (g : ℚ)) := by
  set a := padicValNat 2 g.natAbs with ha
  set b := padicValNat 3 g.natAbs with hb
  have hdvd : 2 ^ a * 3 ^ b ∣ g.natAbs :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow _ _ (by norm_num))
      pow_padicValNat_dvd pow_padicValNat_dvd
  have hle : 2 ^ a * 3 ^ b ≤ g.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hg) hdvd
  have h2 : padic 2 (g : ℚ) = (2 : ℝ) ^ (-(a : ℤ)) := padic_int_zpow' 2 g hg
  have h3 : padic 3 (g : ℚ) = (3 : ℝ) ^ (-(b : ℤ)) := padic_int_zpow' 3 g hg
  have hre : real (g : ℚ) = (g.natAbs : ℝ) := by
    rw [real_eq_abs, Nat.cast_natAbs g, ← Int.cast_abs]
    norm_cast
  rw [hre, h2, h3, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast,
    show ((g.natAbs : ℝ) * (((2:ℝ) ^ a)⁻¹ * ((3:ℝ) ^ b)⁻¹))
      = (g.natAbs : ℝ) / ((2:ℝ) ^ a * (3:ℝ) ^ b) by field_simp,
    le_div_iff₀ (by positivity), one_mul]
  exact_mod_cast hle

/-- The `S = {∞,2,3}` product of a nonzero integer is at most its absolute value. -/
lemma padic23_int_le_one (g : ℤ) :
    padic 2 (g : ℚ) * padic 3 (g : ℚ) ≤ 1 := by
  have h2 : padic 2 (g : ℚ) ≤ 1 := by
    rw [padic_eq_padicNorm]
    exact_mod_cast padicNorm.of_int g
  have h3 : padic 3 (g : ℚ) ≤ 1 := by
    rw [padic_eq_padicNorm]
    exact_mod_cast padicNorm.of_int g
  calc padic 2 (g : ℚ) * padic 3 (g : ℚ) ≤ 1 * 1 :=
        mul_le_mul h2 h3 (by positivity) (by norm_num)
    _ = 1 := by norm_num

attribute [local instance] Classical.propDecidable

/-- The per-place linear forms of the NKR `n = 3` Subspace application: at the real
place `(α₁X₁ + α₂X₂ − X₀, X₁, X₂)` (the first form measures `‖α₁u₁ + α₂u₂‖`), at every
other place the coordinate forms `(X₀, X₁, X₂)`. -/
noncomputable def Lforms3 (α₁ α₂ : ℚ) (v : AbsoluteValue ℚ ℝ) :
    Fin 3 → ((Fin 3 → ℚ) →ₗ[ℚ] ℚ) :=
  if v = Rat.AbsoluteValue.real
  then ![α₁ • LinearMap.proj 1 + α₂ • LinearMap.proj 2 - LinearMap.proj 0,
        LinearMap.proj 1, LinearMap.proj 2]
  else ![LinearMap.proj 0, LinearMap.proj 1, LinearMap.proj 2]

lemma lforms3_linearIndependent (α₁ α₂ : ℚ) (v : AbsoluteValue ℚ ℝ) :
    LinearIndependent ℚ (Lforms3 α₁ α₂ v) := by
  unfold Lforms3
  by_cases h : v = Rat.AbsoluteValue.real
  · rw [if_pos h]
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 := LinearMap.congr_fun hg ![1, 0, 0]
    have h1 := LinearMap.congr_fun hg ![0, 1, 0]
    have h2 := LinearMap.congr_fun hg ![0, 0, 1]
    simp [Fin.sum_univ_three] at h0 h1 h2
    have hg0 : g 0 = 0 := h0
    have hg1 : g 1 = 0 := by
      rw [hg0] at h1
      simpa using h1
    have hg2 : g 2 = 0 := by
      rw [hg0] at h2
      simpa using h2
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2
  · rw [if_neg h]
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 := LinearMap.congr_fun hg ![1, 0, 0]
    have h1 := LinearMap.congr_fun hg ![0, 1, 0]
    have h2 := LinearMap.congr_fun hg ![0, 0, 1]
    simp [Fin.sum_univ_three] at h0 h1 h2
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2

/-- `iSup` over `Fin 3` as an iterated `max`. -/
lemma ciSup_fin3 {α : Type*} [ConditionallyCompleteLinearOrder α] (f : Fin 3 → α) :
    (⨆ i, f i) = max (max (f 0) (f 1)) (f 2) := by
  apply le_antisymm
  · apply ciSup_le
    intro i
    fin_cases i
    · exact le_max_of_le_left (le_max_left _ _)
    · exact le_max_of_le_left (le_max_right _ _)
    · exact le_max_right _ _
  · apply max_le
    · apply max_le
      · exact le_ciSup (Finite.bddAbove_range f) 0
      · exact le_ciSup (Finite.bddAbove_range f) 1
    · exact le_ciSup (Finite.bddAbove_range f) 2

/-- The local sup-norm of a triple. -/
lemma localNorm_triple (v : AbsoluteValue ℚ ℝ) (a b c : ℚ) :
    localNorm v ![a, b, c] = max (max (v a) (v b)) (v c) := by
  unfold Subspace.localNorm
  have hcoe : ∀ i : Fin 3, v (![a, b, c] i) = ![v a, v b, v c] i := by
    intro i
    fin_cases i <;> simp
  rw [show (⨆ i, v (![a, b, c] i)) = ⨆ i, ![v a, v b, v c] i from iSup_congr hcoe,
    ciSup_fin3]
  simp

/-- On a gcd-1 integer triple every non-archimedean local norm is `1`. -/
lemma padic_max3_of_gcd_eq_one (p : ℕ) [Fact p.Prime] (Z : Fin 3 → ℤ)
    (hZ : Finset.univ.gcd Z = 1) :
    max (max (padic p ((Z 0 : ℤ) : ℚ)) (padic p ((Z 1 : ℤ) : ℚ))) (padic p ((Z 2 : ℤ) : ℚ))
      = 1 := by
  have hple : ∀ i : Fin 3, padic p ((Z i : ℤ) : ℚ) ≤ 1 := fun i => by
    rw [padic_eq_padicNorm]
    exact_mod_cast padicNorm.of_int (Z i)
  have hex : ∃ i : Fin 3, ¬ (p : ℤ) ∣ Z i := by
    by_contra hall
    push Not at hall
    have hdvd : (p : ℤ) ∣ Finset.univ.gcd Z :=
      Finset.dvd_gcd (fun i _ => hall i)
    rw [hZ] at hdvd
    have hp1 : (p : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) hdvd
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  obtain ⟨i, hi⟩ := hex
  have h1 : padic p ((Z i : ℤ) : ℚ) = 1 := by
    rw [padic_eq_padicNorm]
    exact_mod_cast (padicNorm.int_eq_one_iff (Z i)).mpr hi
  apply le_antisymm
  · exact max_le (max_le (hple 0) (hple 1)) (hple 2)
  · rw [← h1]
    fin_cases i
    · exact le_max_of_le_left (le_max_left _ _)
    · exact le_max_of_le_left (le_max_right _ _)
    · exact le_max_right _ _

/-- `|m|` as the real value of the rational cast. -/
lemma real_intCast_natAbs (m : ℤ) : real (m : ℚ) = (m.natAbs : ℝ) := by
  rw [real_eq_abs, Nat.cast_natAbs m, ← Int.cast_abs]
  norm_cast

/-- **The `n = 3` Subspace product on a gcd-1 integer triple, in closed form** (the
triple analogue of `CZ.approxProduct_pair_eq`): all finite local norms are `1`, so the
double product collapses to explicit archimedean and `p`-adic factors. -/
lemma approxProduct_triple_eq (α₁ α₂ : ℚ) (a b c : ℤ)
    (h : Finset.univ.gcd ![a, b, c] = 1) :
    approxProduct {Rat.AbsoluteValue.real, padic 2, padic 3} (Lforms3 α₁ α₂)
      ![(a : ℚ), (b : ℚ), (c : ℚ)]
    = real (α₁ * (b : ℚ) + α₂ * (c : ℚ) - (a : ℚ)) * real ((b : ℤ) : ℚ) * real ((c : ℤ) : ℚ)
        / (max (max (real ((a : ℤ) : ℚ)) (real ((b : ℤ) : ℚ))) (real ((c : ℤ) : ℚ))) ^ 3
      * (padic 2 ((a : ℤ) : ℚ) * (padic 2 ((b : ℤ) : ℚ) * padic 2 ((c : ℤ) : ℚ)))
      * (padic 3 ((a : ℤ) : ℚ) * (padic 3 ((b : ℤ) : ℚ) * padic 3 ((c : ℤ) : ℚ))) := by
  have hLNr : localNorm Rat.AbsoluteValue.real ![(a : ℚ), (b : ℚ), (c : ℚ)]
      = max (max (real ((a : ℤ) : ℚ)) (real ((b : ℤ) : ℚ))) (real ((c : ℤ) : ℚ)) :=
    localNorm_triple _ _ _ _
  have hLN2 : localNorm (padic 2) ![(a : ℚ), (b : ℚ), (c : ℚ)] = 1 := by
    rw [localNorm_triple]
    simpa using padic_max3_of_gcd_eq_one 2 ![a, b, c] h
  have hLN3 : localNorm (padic 3) ![(a : ℚ), (b : ℚ), (c : ℚ)] = 1 := by
    rw [localNorm_triple]
    simpa using padic_max3_of_gcd_eq_one 3 ![a, b, c] h
  unfold Subspace.approxProduct
  rw [show ({Rat.AbsoluteValue.real, padic 2, padic 3} : Finset (AbsoluteValue ℚ ℝ))
      = insert Rat.AbsoluteValue.real (insert (padic 2) {padic 3}) from rfl,
    Finset.prod_insert (by simp [real_ne_padic2, real_ne_padic3]),
    Finset.prod_insert (by simp [padic2_ne_padic3]), Finset.prod_singleton]
  rw [hLNr, hLN2, hLN3]
  simp only [Lforms3, if_true, if_neg real_ne_padic2.symm, if_neg real_ne_padic3.symm,
    Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  ring

/-- **`mulHeight` of a gcd-1 integer triple = max of absolute values.** -/
lemma mulHeight_triple_int (a b c : ℤ) (h : Finset.univ.gcd ![a, b, c] = 1) :
    mulHeight ![(a : ℚ), (b : ℚ), (c : ℚ)]
      = ((max (max |a| |b|) |c| : ℤ) : ℝ) := by
  have hvec : (((↑) : ℤ → ℚ) ∘ ![a, b, c]) = ![(a : ℚ), (b : ℚ), (c : ℚ)] := by
    funext i
    fin_cases i <;> rfl
  have hm := Rat.mulHeight_eq_max_abs_of_gcd_eq_one (x := ![a, b, c]) h
  rw [hvec] at hm
  rw [hm, show (⨆ i, |![a, b, c] i|) = max (max |a| |b|) |c| by
    rw [ciSup_fin3]
    simp]

/-! ### Stage 3b: the membership lemma — the member's triple solves the Subspace inequality -/

set_option maxHeartbeats 1000000 in
/-- **The NKR triple solves the `n = 3` Subspace inequality.**  For a member with
`‖α₁u₁ + α₂u₂‖ < (H(u₁)H(u₂))^{-ε₁}` and ratio height `H(u₁/u₂) ≥ (|α₁|+|α₂|+1)²`, the
point `(p₀, u₁, u₂)` (`p₀` the nearest integer) satisfies
`approxProduct ≤ mulHeight^{-3-ε₁/4}`.  The proof works on the gcd-reduced integer
representative `Z = W/gcd(W)`, where the finite local norms are `1` and the `S`-unit
product formula collapses the numerator to `‖α₁u₁+α₂u₂‖` (times a prime-to-6 factor
`≤ 1`); the ratio-height hypothesis feeds the height comparison `M ≤ H⁴`. -/
lemma member_solves (α₁ α₂ : ℚ) (ε₁ : ℝ) (hε₁ : 0 < ε₁) (x₁ y₁ x₂ y₂ : ℤ)
    (hd : ((α₁ * uval x₁ y₁ + α₂ * uval x₂ y₂).distToNearestInt : ℝ)
        < ((height23 x₁ y₁ * height23 x₂ y₂ : ℕ) : ℝ) ^ (-ε₁))
    (hbig : (((|α₁| + |α₂| + 1 : ℚ) : ℝ)) ^ 2
        ≤ ((height23 (x₁ - x₂) (y₁ - y₂) : ℕ) : ℝ)) :
    approxProduct {Rat.AbsoluteValue.real, padic 2, padic 3} (Lforms3 α₁ α₂)
        ![((round (α₁ * uval x₁ y₁ + α₂ * uval x₂ y₂) : ℤ) : ℚ), uval x₁ y₁, uval x₂ y₂]
      ≤ mulHeight ![((round (α₁ * uval x₁ y₁ + α₂ * uval x₂ y₂) : ℤ) : ℚ),
          uval x₁ y₁, uval x₂ y₂] ^ (-(3 : ℝ) - ε₁ / 4) := by
  have hu₁0 : (0 : ℚ) < uval x₁ y₁ := uval_pos x₁ y₁
  have hu₂0 : (0 : ℚ) < uval x₂ y₂ := uval_pos x₂ y₂
  set u₁ := uval x₁ y₁ with hu₁def
  set u₂ := uval x₂ y₂ with hu₂def
  set val := α₁ * u₁ + α₂ * u₂ with hvaldef
  set p₀ : ℤ := round val with hp₀def
  set N₁ : ℕ := 2 ^ x₁.toNat * 3 ^ y₁.toNat with hN₁def
  set D₁ : ℕ := 2 ^ (-x₁).toNat * 3 ^ (-y₁).toNat with hD₁def
  set N₂ : ℕ := 2 ^ x₂.toNat * 3 ^ y₂.toNat with hN₂def
  set D₂ : ℕ := 2 ^ (-x₂).toNat * 3 ^ (-y₂).toNat with hD₂def
  set H₁ : ℕ := height23 x₁ y₁ with hH₁def
  set H₂ : ℕ := height23 x₂ y₂ with hH₂def
  set W : Fin 3 → ℤ :=
    ![p₀ * ((D₁ * D₂ : ℕ) : ℤ), ((N₁ * D₂ : ℕ) : ℤ), ((N₂ * D₁ : ℕ) : ℤ)] with hWdef
  set g : ℤ := Finset.univ.gcd W with hgdef
  set Z : Fin 3 → ℤ := fun j => W j / g with hZdef
  -- basic positivity / nonvanishing
  have hW1 : W 1 = ((N₁ * D₂ : ℕ) : ℤ) := rfl
  have hW2 : W 2 = ((N₂ * D₁ : ℕ) : ℤ) := rfl
  have hW0 : W 0 = p₀ * ((D₁ * D₂ : ℕ) : ℤ) := rfl
  have hN₁pos : 0 < N₁ := by rw [hN₁def]; positivity
  have hD₁pos : 0 < D₁ := by rw [hD₁def]; positivity
  have hN₂pos : 0 < N₂ := by rw [hN₂def]; positivity
  have hD₂pos : 0 < D₂ := by rw [hD₂def]; positivity
  have hW1pos : (0 : ℤ) < W 1 := by rw [hW1]; exact_mod_cast Nat.mul_pos hN₁pos hD₂pos
  have hW2pos : (0 : ℤ) < W 2 := by rw [hW2]; exact_mod_cast Nat.mul_pos hN₂pos hD₁pos
  have hgne : g ≠ 0 := by
    intro h0
    rw [hgdef] at h0
    exact hW1pos.ne' (Finset.gcd_eq_zero_iff.mp h0 1 (Finset.mem_univ 1))
  have hdvd : ∀ i, g ∣ W i := fun i => hgdef ▸ Finset.gcd_dvd (Finset.mem_univ i)
  -- the rational scaling identities
  have hgQ : ((g : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hgne
  have hZQ : ∀ i, ((Z i : ℤ) : ℚ) = (W i : ℚ) / (g : ℚ) := by
    intro i
    obtain ⟨k, hk⟩ := hdvd i
    have hZi : Z i = k := by
      rw [hZdef]
      simp only
      rw [hk, Int.mul_ediv_cancel_left k hgne]
    rw [hZi, hk]
    push_cast
    rw [mul_div_cancel_left₀ _ hgQ]
  have hDDQ : ((D₁ * D₂ : ℕ) : ℚ) ≠ 0 := by positivity
  -- the un-normalized triple is (D₁D₂)·(p₀, u₁, u₂)
  have hND₁ : u₁ * (D₁ : ℚ) = (N₁ : ℚ) := by
    have := uval_mul_D_eq_N x₁ y₁
    rw [← hu₁def, ← hD₁def, ← hN₁def] at this
    exact_mod_cast this
  have hND₂ : u₂ * (D₂ : ℚ) = (N₂ : ℚ) := by
    have := uval_mul_D_eq_N x₂ y₂
    rw [← hu₂def, ← hD₂def, ← hN₂def] at this
    exact_mod_cast this
  have hWQ0 : (W 0 : ℚ) = ((D₁ * D₂ : ℕ) : ℚ) * ((p₀ : ℤ) : ℚ) := by
    rw [hW0]
    push_cast
    ring
  have hWQ1 : (W 1 : ℚ) = ((D₁ * D₂ : ℕ) : ℚ) * u₁ := by
    rw [hW1]
    push_cast
    nlinarith [hND₁]
  have hWQ2 : (W 2 : ℚ) = ((D₁ * D₂ : ℕ) : ℚ) * u₂ := by
    rw [hW2]
    push_cast
    nlinarith [hND₂]
  -- the scale factor
  set cz : ℚ := ((D₁ * D₂ : ℕ) : ℚ) / (g : ℚ) with hczdef
  have hcz0 : cz ≠ 0 := div_ne_zero hDDQ hgQ
  have hZQ0 : ((Z 0 : ℤ) : ℚ) = cz * ((p₀ : ℤ) : ℚ) := by
    rw [hZQ 0, hWQ0, hczdef]
    ring
  have hZQ1 : ((Z 1 : ℤ) : ℚ) = cz * u₁ := by
    rw [hZQ 1, hWQ1, hczdef]
    ring
  have hZQ2 : ((Z 2 : ℤ) : ℚ) = cz * u₂ := by
    rw [hZQ 2, hWQ2, hczdef]
    ring
  have hZ1ne : Z 1 ≠ 0 := by
    intro h0
    have := hZQ1
    rw [h0] at this
    simp only [Int.cast_zero] at this
    exact (mul_ne_zero hcz0 hu₁0.ne') this.symm
  have hZ2ne : Z 2 ≠ 0 := by
    intro h0
    have := hZQ2
    rw [h0] at this
    simp only [Int.cast_zero] at this
    exact (mul_ne_zero hcz0 hu₂0.ne') this.symm
  -- gcd-1 for the reduced triple
  have hgcd1 : Finset.univ.gcd Z = 1 := by
    rw [hZdef, hgdef]
    exact Finset.gcd_div_eq_one (Finset.mem_univ (1 : Fin 3)) hW1pos.ne'
  have hZfun : ![Z 0, Z 1, Z 2] = Z := by
    funext i
    fin_cases i <;> rfl
  have hgcdZ : Finset.univ.gcd ![Z 0, Z 1, Z 2] = 1 := by rw [hZfun]; exact hgcd1
  -- the smul bridge for approxProduct and mulHeight
  have hvecZ : ![((Z 0 : ℤ) : ℚ), ((Z 1 : ℤ) : ℚ), ((Z 2 : ℤ) : ℚ)]
      = cz • ![((p₀ : ℤ) : ℚ), u₁, u₂] := by
    funext i
    fin_cases i
    · simpa using hZQ0
    · simpa using hZQ1
    · simpa using hZQ2
  have happrox_eq : approxProduct {Rat.AbsoluteValue.real, padic 2, padic 3}
        (Lforms3 α₁ α₂) ![((p₀ : ℤ) : ℚ), u₁, u₂]
      = approxProduct {Rat.AbsoluteValue.real, padic 2, padic 3} (Lforms3 α₁ α₂)
        ![((Z 0 : ℤ) : ℚ), ((Z 1 : ℤ) : ℚ), ((Z 2 : ℤ) : ℚ)] := by
    rw [hvecZ, approxProduct_smul _ _ cz hcz0]
  set MZ : ℤ := max (max |Z 0| |Z 1|) |Z 2| with hMZdef
  have hmh_eq : mulHeight ![((p₀ : ℤ) : ℚ), u₁, u₂] = ((MZ : ℤ) : ℝ) := by
    have h1 : mulHeight ![((Z 0 : ℤ) : ℚ), ((Z 1 : ℤ) : ℚ), ((Z 2 : ℤ) : ℚ)]
        = ((MZ : ℤ) : ℝ) := mulHeight_triple_int (Z 0) (Z 1) (Z 2) hgcdZ
    rw [← h1, hvecZ, mulHeight_smul_eq_mulHeight _ hcz0]
  -- ℝ-positivity bookkeeping
  have hMZ1 : (1 : ℤ) ≤ MZ := by
    have h1 : (1 : ℤ) ≤ |Z 1| := Int.one_le_abs hZ1ne
    rw [hMZdef]
    exact le_trans h1 (le_max_of_le_left (le_max_right _ _))
  have hMZ1R : (1 : ℝ) ≤ ((MZ : ℤ) : ℝ) := by exact_mod_cast hMZ1
  have hMZ0R : (0 : ℝ) < ((MZ : ℤ) : ℝ) := lt_of_lt_of_le one_pos hMZ1R
  -- ===== (A) the closed form and the numerator bound =====
  have hclosed := approxProduct_triple_eq α₁ α₂ (Z 0) (Z 1) (Z 2) hgcdZ
  set dR : ℝ := (val.distToNearestInt : ℝ) with hdRdef
  have hdR0 : (0 : ℝ) ≤ dR := by
    rw [hdRdef]
    exact_mod_cast Rat.distToNearestInt_nonneg val
  set Θ : ℝ := real cz * (padic 2 cz * padic 3 cz) with hΘdef
  have hΘnonneg : 0 ≤ Θ := by
    rw [hΘdef]
    exact mul_nonneg (apply_nonneg _ _) (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
  have hΘ1 : Θ ≤ 1 := by
    have hDD1 : real ((D₁ * D₂ : ℕ) : ℚ)
        * (padic 2 ((D₁ * D₂ : ℕ) : ℚ) * padic 3 ((D₁ * D₂ : ℕ) : ℚ)) = 1 := by
      have hDD : ((D₁ * D₂ : ℕ) : ℚ)
          = uval ((((-x₁).toNat + (-x₂).toNat : ℕ)) : ℤ)
              ((((-y₁).toNat + (-y₂).toNat : ℕ)) : ℤ) := by
        unfold NKR.uval
        rw [zpow_natCast, zpow_natCast, hD₁def, hD₂def]
        push_cast
        ring
      rw [hDD]
      exact real_padic_uval _ _
    have hg1 : 1 ≤ real ((g : ℤ) : ℚ) * (padic 2 ((g : ℤ) : ℚ) * padic 3 ((g : ℤ) : ℚ)) :=
      one_le_real_padic23_int g hgne
    have hgpos : 0 < real ((g : ℤ) : ℚ) * (padic 2 ((g : ℤ) : ℚ) * padic 3 ((g : ℤ) : ℚ)) :=
      lt_of_lt_of_le one_pos hg1
    have hΘeq : Θ = (real ((D₁ * D₂ : ℕ) : ℚ)
        * (padic 2 ((D₁ * D₂ : ℕ) : ℚ) * padic 3 ((D₁ * D₂ : ℕ) : ℚ)))
        / (real ((g : ℤ) : ℚ) * (padic 2 ((g : ℤ) : ℚ) * padic 3 ((g : ℤ) : ℚ))) := by
      rw [hΘdef, hczdef, map_div₀, map_div₀, map_div₀]
      field_simp
    rw [hΘeq, hDD1]
    exact (div_le_one hgpos).mpr hg1
  have hdist_eq : real (α₁ * ((Z 1 : ℤ) : ℚ) + α₂ * ((Z 2 : ℤ) : ℚ) - ((Z 0 : ℤ) : ℚ))
      = real cz * dR := by
    have harg : α₁ * ((Z 1 : ℤ) : ℚ) + α₂ * ((Z 2 : ℤ) : ℚ) - ((Z 0 : ℤ) : ℚ)
        = cz * (val - ((p₀ : ℤ) : ℚ)) := by
      rw [hZQ1, hZQ2, hZQ0, hvaldef]
      ring
    rw [harg, map_mul, hdRdef]
    congr 1
    rw [real_eq_abs]
    norm_cast
  have hreal1 : real ((Z 1 : ℤ) : ℚ) = real cz * real u₁ := by rw [hZQ1, map_mul]
  have hreal2 : real ((Z 2 : ℤ) : ℚ) = real cz * real u₂ := by rw [hZQ2, map_mul]
  have hpad2 : padic 2 ((Z 0 : ℤ) : ℚ) * (padic 2 ((Z 1 : ℤ) : ℚ) * padic 2 ((Z 2 : ℤ) : ℚ))
      = (padic 2 cz) ^ 3 * (padic 2 ((p₀ : ℤ) : ℚ) * (padic 2 u₁ * padic 2 u₂)) := by
    rw [hZQ0, hZQ1, hZQ2, map_mul, map_mul, map_mul]
    ring
  have hpad3 : padic 3 ((Z 0 : ℤ) : ℚ) * (padic 3 ((Z 1 : ℤ) : ℚ) * padic 3 ((Z 2 : ℤ) : ℚ))
      = (padic 3 cz) ^ 3 * (padic 3 ((p₀ : ℤ) : ℚ) * (padic 3 u₁ * padic 3 u₂)) := by
    rw [hZQ0, hZQ1, hZQ2, map_mul, map_mul, map_mul]
    ring
  have hu₁prod : real u₁ * (padic 2 u₁ * padic 3 u₁) = 1 := by
    rw [hu₁def]
    exact real_padic_uval x₁ y₁
  have hu₂prod : real u₂ * (padic 2 u₂ * padic 3 u₂) = 1 := by
    rw [hu₂def]
    exact real_padic_uval x₂ y₂
  have hp₀23 : padic 2 ((p₀ : ℤ) : ℚ) * padic 3 ((p₀ : ℤ) : ℚ) ≤ 1 := padic23_int_le_one p₀
  have hp₀23nonneg : 0 ≤ padic 2 ((p₀ : ℤ) : ℚ) * padic 3 ((p₀ : ℤ) : ℚ) :=
    mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
  have hnum : real (α₁ * ((Z 1 : ℤ) : ℚ) + α₂ * ((Z 2 : ℤ) : ℚ) - ((Z 0 : ℤ) : ℚ))
      * real ((Z 1 : ℤ) : ℚ) * real ((Z 2 : ℤ) : ℚ)
      * (padic 2 ((Z 0 : ℤ) : ℚ) * (padic 2 ((Z 1 : ℤ) : ℚ) * padic 2 ((Z 2 : ℤ) : ℚ)))
      * (padic 3 ((Z 0 : ℤ) : ℚ) * (padic 3 ((Z 1 : ℤ) : ℚ) * padic 3 ((Z 2 : ℤ) : ℚ)))
      ≤ dR := by
    rw [hdist_eq, hreal1, hreal2, hpad2, hpad3]
    calc (real cz * dR) * (real cz * real u₁) * (real cz * real u₂)
          * ((padic 2 cz) ^ 3 * (padic 2 ((p₀ : ℤ) : ℚ) * (padic 2 u₁ * padic 2 u₂)))
          * ((padic 3 cz) ^ 3 * (padic 3 ((p₀ : ℤ) : ℚ) * (padic 3 u₁ * padic 3 u₂)))
        = (real cz * (padic 2 cz * padic 3 cz)) ^ 3
            * ((real u₁ * (padic 2 u₁ * padic 3 u₁)) * ((real u₂ * (padic 2 u₂ * padic 3 u₂))
              * ((padic 2 ((p₀ : ℤ) : ℚ) * padic 3 ((p₀ : ℤ) : ℚ)) * dR))) := by
          ring
      _ = Θ ^ 3 * (1 * (1 * ((padic 2 ((p₀ : ℤ) : ℚ) * padic 3 ((p₀ : ℤ) : ℚ)) * dR))) := by
          rw [← hΘdef, hu₁prod, hu₂prod]
      _ = (Θ ^ 3 * (padic 2 ((p₀ : ℤ) : ℚ) * padic 3 ((p₀ : ℤ) : ℚ))) * dR := by
          ring
      _ ≤ 1 * dR := by
          refine mul_le_mul_of_nonneg_right ?_ hdR0
          exact mul_le_one₀ (pow_le_one₀ hΘnonneg hΘ1) hp₀23nonneg hp₀23
      _ = dR := one_mul _
  -- ===== (B) the ratio height is below MZ =====
  set w : ℚ := u₁ / u₂ with hwdef
  have hwuval : w = uval (x₁ - x₂) (y₁ - y₂) := by
    rw [hwdef, hu₁def, hu₂def, uval_div]
  have hcross : (w.den : ℤ) * Z 1 = w.num * Z 2 := by
    have h1 : w * ((Z 2 : ℤ) : ℚ) = ((Z 1 : ℤ) : ℚ) := by
      rw [hZQ1, hZQ2, hwdef]
      field_simp
    have hden : ((w.den : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.pos_of_ne_zero w.den_nz).ne'
    have hwd : (w.num : ℚ) = w * ((w.den : ℕ) : ℚ) :=
      (div_eq_iff hden).mp (Rat.num_div_den w)
    have h2 : ((w.den : ℕ) : ℚ) * ((Z 1 : ℤ) : ℚ) = (w.num : ℚ) * ((Z 2 : ℤ) : ℚ) := by
      calc ((w.den : ℕ) : ℚ) * ((Z 1 : ℤ) : ℚ)
          = ((w.den : ℕ) : ℚ) * (w * ((Z 2 : ℤ) : ℚ)) := by rw [h1]
        _ = (w * ((w.den : ℕ) : ℚ)) * ((Z 2 : ℤ) : ℚ) := by ring
        _ = (w.num : ℚ) * ((Z 2 : ℤ) : ℚ) := by rw [← hwd]
    exact_mod_cast h2
  have hcopw : IsCoprime w.num (w.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Int.natAbs_natCast] using w.reduced
  have hnum_dvd : w.num ∣ Z 1 := by
    apply hcopw.dvd_of_dvd_mul_left
    exact ⟨Z 2, by linarith [hcross]⟩
  have hden_dvd : (w.den : ℤ) ∣ Z 2 := by
    apply hcopw.symm.dvd_of_dvd_mul_left
    exact ⟨Z 1, by linarith [hcross]⟩
  have hwnum_le : (w.num.natAbs : ℤ) ≤ |Z 1| := by
    have h := Nat.le_of_dvd (Int.natAbs_pos.mpr hZ1ne) (Int.natAbs_dvd_natAbs.mpr hnum_dvd)
    have habs : |Z 1| = ((Z 1).natAbs : ℤ) := by
      rw [Int.natCast_natAbs]
    rw [habs]
    exact_mod_cast h
  have hwden_le : ((w.den : ℕ) : ℤ) ≤ |Z 2| := by
    have h := Nat.le_of_dvd (Int.natAbs_pos.mpr hZ2ne) (Int.natAbs_dvd_natAbs.mpr hden_dvd)
    have habs : |Z 2| = ((Z 2).natAbs : ℤ) := by
      rw [Int.natCast_natAbs]
    rw [habs]
    have h2 : ((w.den : ℤ)).natAbs = w.den := Int.natAbs_natCast _
    rw [← h2] at h ⊢
    exact_mod_cast h
  have hhw_le_MZ : ((height23 (x₁ - x₂) (y₁ - y₂) : ℕ) : ℝ) ≤ ((MZ : ℤ) : ℝ) := by
    have hid : ((max w.num.natAbs w.den : ℕ) : ℝ)
        = ((height23 (x₁ - x₂) (y₁ - y₂) : ℕ) : ℝ) := by
      rw [← Rat.mulHeight₁_eq_max w, hwuval, mulHeight₁_uval]
    rw [← hid]
    have hmaxZ : ((max w.num.natAbs w.den : ℕ) : ℤ) ≤ MZ := by
      rw [Nat.cast_max, hMZdef]
      apply max_le
      · exact le_trans hwnum_le (le_max_of_le_left (le_max_right _ _))
      · exact le_trans hwden_le (le_max_right _ _)
    calc ((max w.num.natAbs w.den : ℕ) : ℝ)
        = (((max w.num.natAbs w.den : ℕ) : ℤ) : ℝ) := by norm_cast
      _ ≤ ((MZ : ℤ) : ℝ) := Int.cast_le.mpr hmaxZ
  -- ===== (C) MZ is at most Cα·(H₁H₂)² =====
  set CQ : ℚ := |α₁| + |α₂| + 1 with hCQdef
  have hCQ1 : (1 : ℚ) ≤ CQ := by
    rw [hCQdef]
    have := abs_nonneg α₁
    have := abs_nonneg α₂
    linarith
  have hHQ1 : (1 : ℚ) ≤ ((H₁ * H₂ : ℕ) : ℚ) := by
    have h1 := one_le_height23 x₁ y₁
    have h2 := one_le_height23 x₂ y₂
    rw [← hH₁def] at h1
    rw [← hH₂def] at h2
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hu₁H : u₁ ≤ ((H₁ * H₂ : ℕ) : ℚ) := by
    have h1 : u₁ ≤ (H₁ : ℚ) := by
      rw [hu₁def, hH₁def]
      exact u_le_height23 x₁ y₁
    have h2 : (H₁ : ℚ) ≤ ((H₁ * H₂ : ℕ) : ℚ) := by
      have h3 := one_le_height23 x₂ y₂
      rw [← hH₂def] at h3
      exact_mod_cast Nat.le_mul_of_pos_right H₁ (by omega)
    linarith
  have hu₂H : u₂ ≤ ((H₁ * H₂ : ℕ) : ℚ) := by
    have h1 : u₂ ≤ (H₂ : ℚ) := by
      rw [hu₂def, hH₂def]
      exact u_le_height23 x₂ y₂
    have h2 : (H₂ : ℚ) ≤ ((H₁ * H₂ : ℕ) : ℚ) := by
      have h3 := one_le_height23 x₁ y₁
      rw [← hH₁def] at h3
      exact_mod_cast Nat.le_mul_of_pos_left H₂ (by omega)
    linarith
  have hp₀_abs : |((p₀ : ℤ) : ℚ)| ≤ CQ * ((H₁ * H₂ : ℕ) : ℚ) := by
    have hround : |val - ((p₀ : ℤ) : ℚ)| ≤ 1 / 2 := by
      rw [hp₀def]
      exact_mod_cast abs_sub_round val
    have htri : |((p₀ : ℤ) : ℚ)| ≤ |val| + 1 / 2 := by
      calc |((p₀ : ℤ) : ℚ)| = |val - (val - ((p₀ : ℤ) : ℚ))| := by ring_nf
        _ ≤ |val| + |val - ((p₀ : ℤ) : ℚ)| := abs_sub _ _
        _ ≤ |val| + 1 / 2 := by linarith
    have hval_abs : |val| ≤ (|α₁| + |α₂|) * ((H₁ * H₂ : ℕ) : ℚ) := by
      calc |val| = |α₁ * u₁ + α₂ * u₂| := by rw [hvaldef]
        _ ≤ |α₁ * u₁| + |α₂ * u₂| := abs_add_le _ _
        _ = |α₁| * u₁ + |α₂| * u₂ := by
            rw [abs_mul, abs_mul, abs_of_pos hu₁0, abs_of_pos hu₂0]
        _ ≤ |α₁| * ((H₁ * H₂ : ℕ) : ℚ) + |α₂| * ((H₁ * H₂ : ℕ) : ℚ) := by
            gcongr
        _ = (|α₁| + |α₂|) * ((H₁ * H₂ : ℕ) : ℚ) := by ring
    rw [hCQdef]
    nlinarith [hHQ1, htri, hval_abs]
  have hDD_H : ((D₁ * D₂ : ℕ) : ℚ) ≤ ((H₁ * H₂ : ℕ) : ℚ) := by
    have h1 : D₁ ≤ H₁ := by
      rw [hD₁def, hH₁def]
      unfold CZ.height23
      exact le_max_right _ _
    have h2 : D₂ ≤ H₂ := by
      rw [hD₂def, hH₂def]
      unfold CZ.height23
      exact le_max_right _ _
    exact_mod_cast Nat.mul_le_mul h1 h2
  have hND_H1 : ((N₁ * D₂ : ℕ) : ℚ) ≤ ((H₁ * H₂ : ℕ) : ℚ) := by
    have h1 : N₁ ≤ H₁ := by
      rw [hN₁def, hH₁def]
      unfold CZ.height23
      exact le_max_left _ _
    have h2 : D₂ ≤ H₂ := by
      rw [hD₂def, hH₂def]
      unfold CZ.height23
      exact le_max_right _ _
    exact_mod_cast Nat.mul_le_mul h1 h2
  have hND_H2 : ((N₂ * D₁ : ℕ) : ℚ) ≤ ((H₁ * H₂ : ℕ) : ℚ) := by
    have h1 : N₂ ≤ H₂ := by
      rw [hN₂def, hH₂def]
      unfold CZ.height23
      exact le_max_left _ _
    have h2 : D₁ ≤ H₁ := by
      rw [hD₁def, hH₁def]
      unfold CZ.height23
      exact le_max_right _ _
    have h3 : N₂ * D₁ ≤ H₂ * H₁ := Nat.mul_le_mul h1 h2
    have h4 : H₂ * H₁ = H₁ * H₂ := Nat.mul_comm _ _
    exact_mod_cast h4 ▸ h3
  have hZW : ∀ i, |((Z i : ℤ) : ℚ)| ≤ |((W i : ℤ) : ℚ)| := by
    intro i
    rw [hZQ i, abs_div]
    have hg1 : (1 : ℚ) ≤ |((g : ℤ) : ℚ)| := by
      have := abs_pos.mpr hgne
      have h2 : (1 : ℤ) ≤ |g| := by omega
      calc (1 : ℚ) ≤ ((|g| : ℤ) : ℚ) := by exact_mod_cast h2
        _ = |((g : ℤ) : ℚ)| := by rw [Int.cast_abs]
    calc |((W i : ℤ) : ℚ)| / |((g : ℤ) : ℚ)| ≤ |((W i : ℤ) : ℚ)| / 1 :=
          div_le_div_of_nonneg_left (abs_nonneg _) one_pos hg1
      _ = |((W i : ℤ) : ℚ)| := div_one _
  have hCQ0 : (0 : ℚ) ≤ CQ := le_trans zero_le_one hCQ1
  have hHQ0 : (0 : ℚ) ≤ ((H₁ * H₂ : ℕ) : ℚ) := by positivity
  have hMZle : ((MZ : ℤ) : ℝ) ≤ ((CQ : ℚ) : ℝ) * (((H₁ * H₂ : ℕ)) : ℝ) ^ 2 := by
    have hb0 : |((W 0 : ℤ) : ℚ)| ≤ CQ * ((H₁ * H₂ : ℕ) : ℚ) ^ 2 := by
      have hW0Q : ((W 0 : ℤ) : ℚ) = ((p₀ : ℤ) : ℚ) * ((D₁ * D₂ : ℕ) : ℚ) := by
        rw [hW0]
        push_cast
        ring
      rw [hW0Q, abs_mul,
        abs_of_nonneg (show (0 : ℚ) ≤ ((D₁ * D₂ : ℕ) : ℚ) by positivity)]
      calc |((p₀ : ℤ) : ℚ)| * ((D₁ * D₂ : ℕ) : ℚ)
          ≤ (CQ * ((H₁ * H₂ : ℕ) : ℚ)) * ((H₁ * H₂ : ℕ) : ℚ) :=
            mul_le_mul hp₀_abs hDD_H (by positivity) (mul_nonneg hCQ0 hHQ0)
        _ = CQ * ((H₁ * H₂ : ℕ) : ℚ) ^ 2 := by ring
    have hstep2 : ((H₁ * H₂ : ℕ) : ℚ) ≤ CQ * ((H₁ * H₂ : ℕ) : ℚ) ^ 2 := by
      calc ((H₁ * H₂ : ℕ) : ℚ)
          ≤ ((H₁ * H₂ : ℕ) : ℚ) * ((H₁ * H₂ : ℕ) : ℚ) :=
            le_mul_of_one_le_right hHQ0 hHQ1
        _ ≤ CQ * (((H₁ * H₂ : ℕ) : ℚ) * ((H₁ * H₂ : ℕ) : ℚ)) :=
            le_mul_of_one_le_left (mul_nonneg hHQ0 hHQ0) hCQ1
        _ = CQ * ((H₁ * H₂ : ℕ) : ℚ) ^ 2 := by ring
    have hb1 : |((W 1 : ℤ) : ℚ)| ≤ CQ * ((H₁ * H₂ : ℕ) : ℚ) ^ 2 := by
      rw [hW1, show |(((N₁ * D₂ : ℕ) : ℤ) : ℚ)| = (((N₁ * D₂ : ℕ)) : ℚ) from
        abs_of_nonneg (by positivity)]
      exact le_trans hND_H1 hstep2
    have hb2 : |((W 2 : ℤ) : ℚ)| ≤ CQ * ((H₁ * H₂ : ℕ) : ℚ) ^ 2 := by
      rw [hW2, show |(((N₂ * D₁ : ℕ) : ℤ) : ℚ)| = (((N₂ * D₁ : ℕ)) : ℚ) from
        abs_of_nonneg (by positivity)]
      exact le_trans hND_H2 hstep2
    have hMZQ : ((MZ : ℤ) : ℚ) ≤ CQ * ((H₁ * H₂ : ℕ) : ℚ) ^ 2 := by
      have hcast : ((MZ : ℤ) : ℚ)
          = max (max |((Z 0 : ℤ) : ℚ)| |((Z 1 : ℤ) : ℚ)|) |((Z 2 : ℤ) : ℚ)| := by
        rw [hMZdef]
        norm_cast
      rw [hcast]
      apply max_le
      · apply max_le
        · exact le_trans (hZW 0) hb0
        · exact le_trans (hZW 1) hb1
      · exact le_trans (hZW 2) hb2
    exact_mod_cast hMZQ
  -- ===== (D) the rpow finale =====
  have hHR1 : (1 : ℝ) ≤ (((H₁ * H₂ : ℕ)) : ℝ) := by exact_mod_cast hHQ1
  have hHR0 : (0 : ℝ) < (((H₁ * H₂ : ℕ)) : ℝ) := lt_of_lt_of_le one_pos hHR1
  have hC2M : (((CQ : ℚ)) : ℝ) ^ 2 ≤ ((MZ : ℤ) : ℝ) := by
    refine le_trans ?_ hhw_le_MZ
    rw [hCQdef]
    exact_mod_cast hbig
  have hM_H4 : ((MZ : ℤ) : ℝ) ≤ (((H₁ * H₂ : ℕ)) : ℝ) ^ 4 := by
    have hCR0 : (0 : ℝ) < ((CQ : ℚ) : ℝ) := by
      have : (1 : ℝ) ≤ ((CQ : ℚ) : ℝ) := by exact_mod_cast hCQ1
      linarith
    nlinarith [hMZle, hC2M, hMZ0R, hHR0, sq_nonneg (((H₁ * H₂ : ℕ)) : ℝ)]
  have hfinal_exp : (((H₁ * H₂ : ℕ)) : ℝ) ^ (-ε₁) ≤ ((MZ : ℤ) : ℝ) ^ (-(ε₁ / 4)) := by
    have hstep : ((MZ : ℤ) : ℝ) ^ (ε₁ / 4) ≤ ((((H₁ * H₂ : ℕ)) : ℝ) ^ 4) ^ (ε₁ / 4) :=
      Real.rpow_le_rpow hMZ0R.le hM_H4 (by positivity)
    have hH4 : ((((H₁ * H₂ : ℕ)) : ℝ) ^ 4 : ℝ) ^ (ε₁ / 4) = (((H₁ * H₂ : ℕ)) : ℝ) ^ ε₁ := by
      rw [← Real.rpow_natCast (((H₁ * H₂ : ℕ)) : ℝ) 4, ← Real.rpow_mul hHR0.le]
      congr 1
      push_cast
      ring
    rw [Real.rpow_neg hHR0.le, Real.rpow_neg hMZ0R.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hMZ0R _) (hH4 ▸ hstep)
  -- ===== assembly =====
  rw [happrox_eq, hclosed, hmh_eq]
  have hmax_eq : max (max (real ((Z 0 : ℤ) : ℚ)) (real ((Z 1 : ℤ) : ℚ)))
      (real ((Z 2 : ℤ) : ℚ)) = ((MZ : ℤ) : ℝ) := by
    have habs : ∀ i : Fin 3, real ((Z i : ℤ) : ℚ) = ((|Z i| : ℤ) : ℝ) := fun i => by
      rw [real_intCast_natAbs, Nat.cast_natAbs]
    have hcm : ∀ a b : ℤ, ((max a b : ℤ) : ℝ) = max ((a : ℤ) : ℝ) ((b : ℤ) : ℝ) :=
      fun a b => Int.cast_mono.map_max
    rw [habs 0, habs 1, habs 2, hMZdef, hcm, hcm]
  rw [hmax_eq]
  have hRHS : ((MZ : ℤ) : ℝ) ^ (-(3 : ℝ) - ε₁ / 4)
      = ((MZ : ℤ) : ℝ) ^ (-(ε₁ / 4)) / ((MZ : ℤ) : ℝ) ^ (3 : ℕ) := by
    rw [eq_div_iff (ne_of_gt (pow_pos hMZ0R 3)), ← Real.rpow_natCast ((MZ : ℤ) : ℝ) 3,
      ← Real.rpow_add hMZ0R]
    congr 1
    push_cast
    ring
  rw [hRHS, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_mul_inv, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (by positivity))
  calc real (α₁ * ((Z 1 : ℤ) : ℚ) + α₂ * ((Z 2 : ℤ) : ℚ) - ((Z 0 : ℤ) : ℚ))
        * real ((Z 1 : ℤ) : ℚ) * real ((Z 2 : ℤ) : ℚ)
        * (padic 2 ((Z 0 : ℤ) : ℚ) * (padic 2 ((Z 1 : ℤ) : ℚ) * padic 2 ((Z 2 : ℤ) : ℚ)))
        * (padic 3 ((Z 0 : ℤ) : ℚ) * (padic 3 ((Z 1 : ℤ) : ℚ) * padic 3 ((Z 2 : ℤ) : ℚ)))
      ≤ dR := hnum
    _ ≤ (((H₁ * H₂ : ℕ)) : ℝ) ^ (-ε₁) := by
        rw [hdRdef]
        exact hd.le
    _ ≤ ((MZ : ℤ) : ℝ) ^ (-(ε₁ / 4)) := hfinal_exp

/-! ### Stage 4a: `S`-units near a fixed positive rational (the CZ reduction) -/

/-- **Finitely many `S`-units approach a fixed positive rational** — the `q = 1`
instance of the Corvaja–Zannier Main Theorem, reached through the nearest-integer
trick at `δ = 2·den(ρ)`: only finitely many `(s, t) ∈ ℤ²` satisfy
`2^s·3^t ≠ ρ` and `|2^s·3^t − ρ| < K·height23^{-ε}`. -/
lemma sUnit_near_ratio_finite (ρ : ℚ) (hρ : 0 < ρ) (K : ℝ) (ε : ℝ) (hε : 0 < ε) :
    {st : ℤ × ℤ | uval st.1 st.2 ≠ ρ ∧
      ((|uval st.1 st.2 - ρ| : ℚ) : ℝ)
        < K * ((height23 st.1 st.2 : ℕ) : ℝ) ^ (-ε)}.Finite := by
  rcases le_or_gt K 0 with hK | hK
  · apply Set.Finite.subset Set.finite_empty
    rintro ⟨s, t⟩ ⟨hne, hlt⟩
    exfalso
    have h1 : (0 : ℝ) ≤ ((|uval s t - ρ| : ℚ) : ℝ) := by positivity
    have h2 : K * ((height23 s t : ℕ) : ℝ) ^ (-ε) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hK (Real.rpow_nonneg (by positivity) _)
    linarith
  set e : ℕ := ρ.den with hedef
  set c : ℤ := ρ.num with hcdef
  have hc1 : 1 ≤ c := Rat.num_pos.mpr hρ
  have he1 : 1 ≤ e := Nat.pos_of_ne_zero ρ.den_nz
  set δ : ℚ := 2 * (e : ℚ) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    have : (0 : ℚ) < (e : ℚ) := by exact_mod_cast he1
    linarith
  set KE : ℝ := 2 * (e : ℝ) * K with hKEdef
  have hKE : 0 < KE := by
    rw [hKEdef]
    have : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he1
    positivity
  set Bval : ℝ := max ((2 * KE) ^ ε⁻¹) (KE ^ (2 / ε)) with hBdef
  have hCZ := CZ.pseudoPisot_approx_of_subspace δ hδpos.ne' (ε / 2) (by positivity)
  have himg : {st : ℤ × ℤ | (uval st.1 st.2 ≠ ρ ∧
      ((|uval st.1 st.2 - ρ| : ℚ) : ℝ) < K * ((height23 st.1 st.2 : ℕ) : ℝ) ^ (-ε)) ∧
      Bval < ((height23 st.1 st.2 : ℕ) : ℝ)}.Finite := by
    apply Set.Finite.of_finite_image (f := fun st : ℤ × ℤ => ((1 : ℕ), st.1, st.2))
    swap
    · intro a _ b _ hab
      simpa [Prod.ext_iff] using hab
    apply Set.Finite.subset hCZ
    rintro p ⟨⟨s, t⟩, ⟨⟨hne, hlt⟩, hbig⟩, rfl⟩
    have hh1 : (1 : ℕ) ≤ height23 s t := one_le_height23 s t
    have hhR0 : (0 : ℝ) < ((height23 s t : ℕ) : ℝ) := by exact_mod_cast hh1
    have hw0 : (0 : ℚ) < uval s t := uval_pos s t
    set w : ℚ := uval s t with hwdef
    -- `sval δ 1 s t = δ·w`
    have hsval : sval δ 1 s t = δ * w := by
      unfold CZ.sval
      rw [hwdef]
      show δ * ((1 : ℕ) : ℚ) * ((2 : ℚ) ^ s * (3 : ℚ) ^ t) = δ * uval s t
      unfold NKR.uval
      push_cast
      ring
    -- `c = ρ·e`
    have hce : (c : ℚ) = ρ * (e : ℚ) := by
      rw [hcdef, hedef]
      have hden : ((ρ.den : ℕ) : ℚ) ≠ 0 := by exact_mod_cast ρ.den_nz
      exact (div_eq_iff hden).mp (Rat.num_div_den ρ)
    -- the exact distance identity `|δw − 2c| = 2e·|w − ρ|`
    have hid : |δ * w - ((2 * c : ℤ) : ℚ)| = 2 * (e : ℚ) * |w - ρ| := by
      have harg : δ * w - ((2 * c : ℤ) : ℚ) = 2 * (e : ℚ) * (w - ρ) := by
        push_cast
        rw [hδdef, hce]
        ring
      rw [harg, abs_mul, abs_of_pos (show (0:ℚ) < 2 * (e:ℚ) by
        have : (0 : ℚ) < (e : ℚ) := by exact_mod_cast he1
        linarith)]
    -- the real bound `|δw − 2c| < KE·h^{-ε}`
    have hlt' : ((|δ * w - ((2 * c : ℤ) : ℚ)| : ℚ) : ℝ)
        < KE * ((height23 s t : ℕ) : ℝ) ^ (-ε) := by
      have hltR : |(w : ℝ) - (ρ : ℝ)| < K * ((height23 s t : ℕ) : ℝ) ^ (-ε) := by
        have h := hlt
        push_cast at h
        exact h
      have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he1
      rw [hid]
      push_cast
      calc (2 : ℝ) * (e : ℝ) * |(w : ℝ) - (ρ : ℝ)|
          < 2 * (e : ℝ) * (K * ((height23 s t : ℕ) : ℝ) ^ (-ε)) :=
            mul_lt_mul_of_pos_left hltR (by linarith)
        _ = KE * ((height23 s t : ℕ) : ℝ) ^ (-ε) := by rw [hKEdef]; ring
    -- the two rpow thresholds from `Bval < h`
    have hKE2 : 2 * KE ≤ ((height23 s t : ℕ) : ℝ) ^ ε := by
      have h1 : (2 * KE) ^ ε⁻¹ ≤ Bval := le_max_left _ _
      have h2 : (2 * KE) ^ ε⁻¹ < ((height23 s t : ℕ) : ℝ) := lt_of_le_of_lt h1 hbig
      have h3 : ((2 * KE) ^ ε⁻¹) ^ ε ≤ ((height23 s t : ℕ) : ℝ) ^ ε :=
        Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) h2.le hε.le
      rwa [← Real.rpow_mul (by linarith : (0:ℝ) ≤ 2 * KE), inv_mul_cancel₀ hε.ne',
        Real.rpow_one] at h3
    have hKEhalf : KE ≤ ((height23 s t : ℕ) : ℝ) ^ (ε / 2) := by
      have h1 : KE ^ (2 / ε) ≤ Bval := le_max_right _ _
      have h2 : KE ^ (2 / ε) < ((height23 s t : ℕ) : ℝ) := lt_of_le_of_lt h1 hbig
      have h3 : (KE ^ (2 / ε)) ^ (ε / 2) ≤ ((height23 s t : ℕ) : ℝ) ^ (ε / 2) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hKE.le _) h2.le (by positivity)
      rwa [← Real.rpow_mul hKE.le, div_mul_div_comm, mul_comm (2:ℝ) ε,
        div_self (by positivity : ε * 2 ≠ 0), Real.rpow_one] at h3
    have hrp0 : (0 : ℝ) < ((height23 s t : ℕ) : ℝ) ^ (-ε) := Real.rpow_pos_of_pos hhR0 _
    have hhalf : KE * ((height23 s t : ℕ) : ℝ) ^ (-ε) ≤ 1 / 2 := by
      have h1 : 2 * (KE * ((height23 s t : ℕ) : ℝ) ^ (-ε)) ≤ 1 := by
        calc 2 * (KE * ((height23 s t : ℕ) : ℝ) ^ (-ε))
            = (2 * KE) * ((height23 s t : ℕ) : ℝ) ^ (-ε) := by ring
          _ ≤ ((height23 s t : ℕ) : ℝ) ^ ε * ((height23 s t : ℕ) : ℝ) ^ (-ε) :=
              mul_le_mul_of_nonneg_right hKE2 hrp0.le
          _ = 1 := by
              rw [← Real.rpow_add hhR0]
              norm_num
      linarith
    -- ℚ-version of the half-bound
    have hhalfQ : |δ * w - ((2 * c : ℤ) : ℚ)| < 1 / 2 := by
      have h1 : ((|δ * w - ((2 * c : ℤ) : ℚ)| : ℚ) : ℝ) < 1 / 2 :=
        lt_of_lt_of_le hlt' hhalf
      rw [show ((1 : ℝ) / 2) = (((1 / 2 : ℚ) : ℚ) : ℝ) by norm_num] at h1
      exact_mod_cast h1
    -- `δw ≠ 2c` (else `w = ρ`)
    have hne2c : δ * w ≠ ((2 * c : ℤ) : ℚ) := by
      intro h0
      apply hne
      have : 2 * (e : ℚ) * (w - ρ) = 0 := by
        have harg : δ * w - ((2 * c : ℤ) : ℚ) = 2 * (e : ℚ) * (w - ρ) := by
          push_cast
          rw [hδdef, hce]
          ring
        rw [← harg, h0]
        ring
      have he0 : (0 : ℚ) < 2 * (e : ℚ) := by
        have : (0 : ℚ) < (e : ℚ) := by exact_mod_cast he1
        linarith
      have := mul_eq_zero.mp this
      rcases this with h | h
      · exact absurd h he0.ne'
      · linarith [sub_eq_zero.mp h]
    -- not an integer
    have hnotint : ¬ ∃ n : ℤ, δ * w = (n : ℚ) := by
      rintro ⟨n, hn⟩
      rcases eq_or_ne n (2 * c) with rfl | hne_n
      · exact hne2c hn
      · have h1 : (1 : ℚ) ≤ |(n : ℚ) - ((2 * c : ℤ) : ℚ)| := by
          have h2 : n - 2 * c ≠ 0 := sub_ne_zero.mpr hne_n
          have h2' := abs_pos.mpr h2
          have h3 : (1 : ℤ) ≤ |n - 2 * c| := by omega
          calc (1 : ℚ) ≤ ((|n - 2 * c| : ℤ) : ℚ) := by exact_mod_cast h3
            _ = |(n : ℚ) - ((2 * c : ℤ) : ℚ)| := by
                rw [Int.cast_abs]
                push_cast
                ring_nf
        rw [hn] at hhalfQ
        linarith
    -- positive distance
    have hdistpos : 0 < (δ * w).distToNearestInt := by
      rcases lt_or_eq_of_le (Rat.distToNearestInt_nonneg (δ * w)) with h | h
      · exact h
      · exfalso
        exact hnotint (Rat.distToNearestInt_eq_zero_iff.mp h.symm)
    -- 1 < |sval|
    have honelt : 1 < |sval δ 1 s t| := by
      rw [hsval]
      have hc2 : (2 : ℚ) ≤ ((2 * c : ℤ) : ℚ) := by
        push_cast
        have : (1 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc1
        linarith
      have hlow : (3 : ℚ) / 2 < δ * w := by
        have h1 : ((2 * c : ℤ) : ℚ) - δ * w ≤ |δ * w - ((2 * c : ℤ) : ℚ)| := by
          rw [abs_sub_comm]
          exact le_abs_self _
        linarith
      rw [abs_of_pos (by linarith : (0 : ℚ) < δ * w)]
      linarith
    -- the distance bound at exponent ε/2
    have hdlt : (((sval δ 1 s t).distToNearestInt : ℚ) : ℝ)
        < ((height23 s t : ℕ) : ℝ) ^ (-(ε / 2)) * ((1 : ℕ) : ℝ) ^ (-1 - ε / 2) := by
      have hd1 : (sval δ 1 s t).distToNearestInt ≤ |δ * w - ((2 * c : ℤ) : ℚ)| := by
        rw [hsval]
        exact Rat.distToNearestInt_le_abs_sub_intCast _ _
      have hd2 : (((sval δ 1 s t).distToNearestInt : ℚ) : ℝ)
          ≤ ((|δ * w - ((2 * c : ℤ) : ℚ)| : ℚ) : ℝ) := by exact_mod_cast hd1
      have hd3 : KE * ((height23 s t : ℕ) : ℝ) ^ (-ε)
          ≤ ((height23 s t : ℕ) : ℝ) ^ (-(ε / 2)) := by
        calc KE * ((height23 s t : ℕ) : ℝ) ^ (-ε)
            ≤ ((height23 s t : ℕ) : ℝ) ^ (ε / 2) * ((height23 s t : ℕ) : ℝ) ^ (-ε) :=
              mul_le_mul_of_nonneg_right hKEhalf hrp0.le
          _ = ((height23 s t : ℕ) : ℝ) ^ (-(ε / 2)) := by
              rw [← Real.rpow_add hhR0]
              congr 1
              ring
      have hrhs : ((height23 s t : ℕ) : ℝ) ^ (-(ε / 2)) * ((1 : ℕ) : ℝ) ^ (-1 - ε / 2)
          = ((height23 s t : ℕ) : ℝ) ^ (-(ε / 2)) := by
        rw [Nat.cast_one, Real.one_rpow, mul_one]
      rw [hrhs]
      exact lt_of_le_of_lt hd2 (lt_of_lt_of_le hlt' hd3)
    exact ⟨le_refl 1, honelt, by rw [hsval]; exact hnotint, by rw [hsval]; exact hdistpos, hdlt⟩
  apply Set.Finite.subset ((finite_height23_le Bval).union himg)
  rintro ⟨s, t⟩ hst
  rcases le_or_gt ((height23 s t : ℕ) : ℝ) Bval with hsmall | hbig
  · exact Or.inl hsmall
  · exact Or.inr ⟨hst, hbig⟩

/-- The **opposite-sign sub-case** of the relation analysis: if along a family
with injective exponent-differences the distance equals `|b₁u₁ + b₂u₂|` with
`b₁ > 0 > b₂`, the family is finite — the ratios `u₁/u₂` approximate `ρ = -b₂/b₁`
and `sUnit_near_ratio_finite` applies. -/
lemma opposite_case_finite (α₁ α₂ b₁ b₂ : ℚ) (ε₁ : ℝ) (hε₁ : 0 < ε₁)
    (hb₁ : 0 < b₁) (hb₂ : b₂ < 0) (F : Set ((ℤ × ℤ) × (ℤ × ℤ)))
    (habs₂ : ∀ q ∈ F, 1 ≤ uval q.2.1 q.2.2)
    (hinjF : Set.InjOn (fun q : (ℤ × ℤ) × (ℤ × ℤ) => (q.1.1 - q.2.1, q.1.2 - q.2.2)) F)
    (hdeq : ∀ q ∈ F, (α₁ * uval q.1.1 q.1.2 + α₂ * uval q.2.1 q.2.2).distToNearestInt
        = |b₁ * uval q.1.1 q.1.2 + b₂ * uval q.2.1 q.2.2|)
    (hposF : ∀ q ∈ F,
        0 < (α₁ * uval q.1.1 q.1.2 + α₂ * uval q.2.1 q.2.2).distToNearestInt)
    (happroxF : ∀ q ∈ F,
        ((α₁ * uval q.1.1 q.1.2 + α₂ * uval q.2.1 q.2.2).distToNearestInt : ℝ)
        < ((height23 q.1.1 q.1.2 * height23 q.2.1 q.2.2 : ℕ) : ℝ) ^ (-ε₁)) :
    F.Finite := by
  set ρ : ℚ := -b₂ / b₁ with hρdef
  have hρ : 0 < ρ := by
    rw [hρdef]
    exact div_pos (by linarith) hb₁
  have hb₁R : (0 : ℝ) < ((b₁ : ℚ) : ℝ) := by exact_mod_cast hb₁
  have hfin := sUnit_near_ratio_finite ρ hρ (((b₁ : ℚ) : ℝ)⁻¹) ε₁ hε₁
  apply Set.Finite.of_finite_image
    (f := fun q : (ℤ × ℤ) × (ℤ × ℤ) => (q.1.1 - q.2.1, q.1.2 - q.2.2))
  swap
  · exact hinjF
  apply Set.Finite.subset hfin
  rintro st ⟨q, hqF, rfl⟩
  have hu₁0 : (0 : ℚ) < uval q.1.1 q.1.2 := uval_pos _ _
  have hu₂0 : (0 : ℚ) < uval q.2.1 q.2.2 := uval_pos _ _
  have hu₂1 : 1 ≤ uval q.2.1 q.2.2 := habs₂ q hqF
  have hw : uval (q.1.1 - q.2.1) (q.1.2 - q.2.2)
      = uval q.1.1 q.1.2 / uval q.2.1 q.2.2 := (uval_div _ _ _ _).symm
  have hkey : b₁ * uval q.1.1 q.1.2 + b₂ * uval q.2.1 q.2.2
      = b₁ * uval q.2.1 q.2.2 * (uval q.1.1 q.1.2 / uval q.2.1 q.2.2 - ρ) := by
    rw [hρdef]
    field_simp
    ring
  have hdq := hdeq q hqF
  have hwne : uval q.1.1 q.1.2 / uval q.2.1 q.2.2 ≠ ρ := by
    intro h0
    have hp := hposF q hqF
    rw [hdq, hkey, h0, sub_self, mul_zero, abs_zero] at hp
    exact lt_irrefl 0 hp
  have habs_eq : |b₁ * uval q.1.1 q.1.2 + b₂ * uval q.2.1 q.2.2|
      = b₁ * uval q.2.1 q.2.2 * |uval q.1.1 q.1.2 / uval q.2.1 q.2.2 - ρ| := by
    rw [hkey, abs_mul, abs_of_pos (mul_pos hb₁ hu₂0)]
  have hge : b₁ * |uval q.1.1 q.1.2 / uval q.2.1 q.2.2 - ρ|
      ≤ (α₁ * uval q.1.1 q.1.2 + α₂ * uval q.2.1 q.2.2).distToNearestInt := by
    rw [hdq, habs_eq]
    have h0 : (0 : ℚ) ≤ |uval q.1.1 q.1.2 / uval q.2.1 q.2.2 - ρ| := abs_nonneg _
    have h1 : b₁ * 1 ≤ b₁ * uval q.2.1 q.2.2 := mul_le_mul_of_nonneg_left hu₂1 hb₁.le
    have h2 := mul_le_mul_of_nonneg_right h1 h0
    calc b₁ * |uval q.1.1 q.1.2 / uval q.2.1 q.2.2 - ρ|
        = b₁ * 1 * |uval q.1.1 q.1.2 / uval q.2.1 q.2.2 - ρ| := by ring
      _ ≤ b₁ * uval q.2.1 q.2.2 * |uval q.1.1 q.1.2 / uval q.2.1 q.2.2 - ρ| := h2
  -- pass to ℝ and weaken the height
  have hh_w0 : (0 : ℝ) < ((height23 (q.1.1 - q.2.1) (q.1.2 - q.2.2) : ℕ) : ℝ) := by
    have := one_le_height23 (q.1.1 - q.2.1) (q.1.2 - q.2.2)
    exact_mod_cast lt_of_lt_of_le zero_lt_one (by exact_mod_cast this)
  have hHH0 : (0 : ℝ) < ((height23 q.1.1 q.1.2 * height23 q.2.1 q.2.2 : ℕ) : ℝ) := by
    have h1 := one_le_height23 q.1.1 q.1.2
    have h2 := one_le_height23 q.2.1 q.2.2
    exact_mod_cast Nat.mul_pos h1 h2
  have hanti : ((height23 q.1.1 q.1.2 * height23 q.2.1 q.2.2 : ℕ) : ℝ) ^ (-ε₁)
      ≤ ((height23 (q.1.1 - q.2.1) (q.1.2 - q.2.2) : ℕ) : ℝ) ^ (-ε₁) := by
    rw [Real.rpow_neg hHH0.le, Real.rpow_neg hh_w0.le]
    apply inv_anti₀ (Real.rpow_pos_of_pos hh_w0 _)
    apply Real.rpow_le_rpow hh_w0.le _ hε₁.le
    exact_mod_cast height23_sub_le q.1.1 q.1.2 q.2.1 q.2.2
  have hlt : ((|uval q.1.1 q.1.2 / uval q.2.1 q.2.2 - ρ| : ℚ) : ℝ)
      < ((b₁ : ℚ) : ℝ)⁻¹
        * ((height23 (q.1.1 - q.2.1) (q.1.2 - q.2.2) : ℕ) : ℝ) ^ (-ε₁) := by
    have h1 : ((b₁ : ℚ) : ℝ) * ((|uval q.1.1 q.1.2 / uval q.2.1 q.2.2 - ρ| : ℚ) : ℝ)
        < ((height23 (q.1.1 - q.2.1) (q.1.2 - q.2.2) : ℕ) : ℝ) ^ (-ε₁) := by
      have h2 : ((b₁ : ℚ) : ℝ) * ((|uval q.1.1 q.1.2 / uval q.2.1 q.2.2 - ρ| : ℚ) : ℝ)
          ≤ (((α₁ * uval q.1.1 q.1.2 + α₂ * uval q.2.1 q.2.2).distToNearestInt : ℚ) : ℝ) := by
        exact_mod_cast hge
      exact lt_of_le_of_lt h2 (lt_of_lt_of_le (happroxF q hqF) hanti)
    rw [inv_mul_eq_div, lt_div_iff₀' hb₁R]
    exact h1
  exact ⟨by rw [hw]; exact hwne, by rw [hw]; exact hlt⟩

end NKR


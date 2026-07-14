/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TH.CapstoneM4
import CITED.NairKumarRoutProof
import Mathlib.Data.Set.Function

/-!
# Stage 2c: the gap dichotomy — the kernel (K) and M4, modulo two cited results

The middle-band kernel falls to the **gap dichotomy** — an unpublished one-page
argument, formalized here for the first time.  Neither (K) itself nor the
NKR + CZ derivation below is in print:

Suppose (K) fails at a rational scale `θ ∈ (0, 1)`: infinitely many pairs
`2 ≤ a < c` with `‖(3/2)^c − (3/2)^a‖ ≤ θ^c`.  Look at the gaps `s = c − a`.

* **Finitely many distinct gaps**: then all violators have gap `≤ S` for some
  `S`, and the gap-bounded slice of the kernel is finite by Stage 2b
  (`gapBounded_slice_finite`, from the CZ 2004 Main Theorem) — contradiction.
* **Infinitely many distinct gaps**: choose *one* violating pair per gap
  (`Function.invFunOn` section).  The tuples `(u₁, u₂) = ((3/2)^c, (3/2)^a)`
  then have pairwise-distinct ratios `u₁/u₂ = (3/2)^{c-a}` — exactly the
  tuple-family hypothesis of the Nair–Kumar–Rout theorem — and satisfy
  `0 < ‖u₁ − u₂‖ ≤ θ^c < (H(u₁)H(u₂))^{-ε₁}` for `ε₁ = log θ⁻¹/(2 log 3)`
  (since `H(u₁)H(u₂) = 3^{c+a}` and `a < c`; positivity because
  `(3/2)^c − (3/2)^a = odd/2^c ∉ ℤ`).  The **repaired and derived** [NKR25]
  Theorem 1.3(i) (`NKR.sUnit_pair_integrality_of_subspace`,
  `CITED/NairKumarRoutProof.lean`) makes some `(3/2)^c` an integer — absurd,
  as `2^c·(3/2)^c = 3^c` is odd.

Hence **(K) holds at every rational scale** (`pairRepulsion_all`,
`kernel_holds`), and with the Stage-1 reduction the program's target follows:

* `complexity_superlinear` — **M4**: the steering word of the `(3/2)^n` orbit
  has superlinear subword complexity, `p_T(k)/k → ∞`.

**Axiom footprint**: **std3 + `Subspace.evertseSchlickewei` ([S]) — the single
canonical axiom** (2026-07-14).  Both Diophantine inputs are now *derived* from
it: the [CZ04] Main Theorem (`CITED/CorvajaZannierProof.lean`, `n = 2`) and the
[NKR25] pair theorem (`CITED/NairKumarRoutProof.lean`, `n = 3`; the preprint's
Theorem 1.3(i) was **false as stated** — see `NKR.thm13i_unrepaired_false` —
and is used here in its repaired, proved form, with the strict positivity
discharged by parity).  The conditional capstone `superlinear_of_middleBand`
(`TH.CapstoneM4`, middle band as a named hypothesis) remains as the
axiom-input-free statement of record.

Everything is ineffective (Subspace-based).

## Contents

* `finite_of_gap_injOn` — the NKR branch: a gap-injective family of
  (K)-violators is finite.
* `pairRepulsion_all` — **(K) at every rational scale** (the gap dichotomy).
* `kernel_holds` — the kernel (K), quantified.
* `complexity_superlinear` — **M4**: `p_T(k)/k → ∞`.
* `middleBandViolators_finite` — the Stage-2c middle band is finite (the
  `hexc`-style hypothesis of `TH.CapstoneM4`, discharged mod [NKR25]).

## References

* [NKR25] Nair, Kumar, Rout. *Algebraic approximations to linear combinations
  of S-units.* arXiv:2506.02898 (v3, 2025, unrefereed preprint).
* [CZ04] Corvaja, Zannier. *On the rational approximations to the powers of an
  algebraic number.* Acta Math. **193** (2004), 175–191.
-/

namespace TH

/-! ## Helpers -/

/-- The exponent encoding of the violating pair `(a, c)` as an NKR tuple
`(u₁, u₂) = ((3/2)^c, (3/2)^a)`. -/
private def enc (p : ℕ × ℕ) : (ℤ × ℤ) × (ℤ × ℤ) :=
  ((-(p.2 : ℤ), (p.2 : ℤ)), (-(p.1 : ℤ), (p.1 : ℤ)))

private lemma enc_fst_fst (p : ℕ × ℕ) : (enc p).1.1 = -(p.2 : ℤ) := rfl
private lemma enc_fst_snd (p : ℕ × ℕ) : (enc p).1.2 = (p.2 : ℤ) := rfl
private lemma enc_snd_fst (p : ℕ × ℕ) : (enc p).2.1 = -(p.1 : ℤ) := rfl
private lemma enc_snd_snd (p : ℕ × ℕ) : (enc p).2.2 = (p.1 : ℤ) := rfl

private lemma enc_injective : Function.Injective enc := by
  intro p p' h
  have h1 : ((p.2 : ℤ)) = (p'.2 : ℤ) := congrArg (fun q => q.1.2) h
  have h2 : ((p.1 : ℤ)) = (p'.1 : ℤ) := congrArg (fun q => q.2.2) h
  have e2 : p.2 = p'.2 := by exact_mod_cast h1
  have e1 : p.1 = p'.1 := by exact_mod_cast h2
  exact Prod.ext e1 e2

private lemma three_halves_pow_injective :
    Function.Injective (fun n : ℕ => (3 / 2 : ℚ) ^ n) := by
  have h : StrictMono (fun n : ℕ => (3 / 2 : ℚ) ^ n) := fun m n hmn => by
    exact pow_lt_pow_right₀ (by norm_num) hmn
  exact h.injective

private lemma three_halves_div_pow {a c : ℕ} (hac : a ≤ c) :
    (3 / 2 : ℚ) ^ c / (3 / 2 : ℚ) ^ a = (3 / 2 : ℚ) ^ (c - a) := by
  rw [pow_sub₀ (3 / 2 : ℚ) (by norm_num) hac]
  exact (div_eq_mul_inv _ _)

/-- `(3/2)^c` is never an integer for `c ≥ 1`: `2^c·(3/2)^c = 3^c` is odd. -/
private lemma three_halves_pow_not_int {c : ℕ} (hc : 1 ≤ c) (n : ℤ)
    (h : (3 / 2 : ℚ) ^ c = n) : False := by
  have key : ((3 : ℤ) ^ c : ℚ) = ((2 ^ c * n : ℤ) : ℚ) := by
    push_cast
    rw [← h, div_pow]
    field_simp
  have keyZ : (3 : ℤ) ^ c = 2 ^ c * n := by exact_mod_cast key
  have h3 : (3 : ℤ) ^ c % 2 = 1 :=
    Int.odd_iff.mp ((Int.odd_iff.mpr (by norm_num)).pow)
  have h2 : ((2 : ℤ) ^ c * n) % 2 = 0 := by
    obtain ⟨j, rfl⟩ : ∃ j, c = j + 1 := ⟨c - 1, by omega⟩
    rw [show (2 : ℤ) ^ (j + 1) * n = 2 * (2 ^ j * n) by ring]
    exact Int.mul_emod_right 2 _
  omega

/-- `(3/2)^c − (3/2)^a` is never an integer for `1 ≤ a < c`: clearing `2^c`
gives `3^c − 2^{c-a}·3^a = 2^c·n`, odd = even.  Discharges the strict-positivity
hypothesis of the repaired NKR theorem. -/
private lemma three_halves_pow_sub_not_int {a c : ℕ} (ha : 1 ≤ a) (hac : a < c)
    (n : ℤ) (h : (3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a = n) : False := by
  have h2c : ((2 : ℚ) ^ c) ≠ 0 := by positivity
  have h2a : ((2 : ℚ) ^ a) ≠ 0 := by positivity
  have e1 : (2 : ℚ) ^ c * (3 / 2 : ℚ) ^ c = 3 ^ c := by
    rw [div_pow]
    field_simp
  have e2 : (2 : ℚ) ^ c * (3 / 2 : ℚ) ^ a = 2 ^ (c - a) * 3 ^ a := by
    have hsplit : (2 : ℚ) ^ c = 2 ^ (c - a) * 2 ^ a := by
      rw [← pow_add]; congr 1; omega
    calc (2 : ℚ) ^ c * (3 / 2 : ℚ) ^ a
        = 2 ^ (c - a) * (2 * (3 / 2)) ^ a := by rw [hsplit, mul_pow]; ring
      _ = 2 ^ (c - a) * 3 ^ a := by norm_num
  have key : (3 : ℚ) ^ c - 2 ^ (c - a) * 3 ^ a = 2 ^ c * (n : ℚ) := by
    have hm := congrArg (fun z : ℚ => (2 : ℚ) ^ c * z) h
    simp only [mul_sub] at hm
    rw [e1, e2] at hm
    exact hm
  have keyZ : (3 : ℤ) ^ c - 2 ^ (c - a) * 3 ^ a = 2 ^ c * n := by exact_mod_cast key
  have h3odd : (3 : ℤ) ^ c % 2 = 1 := Int.odd_iff.mp (Odd.pow (by decide))
  obtain ⟨d, hd⟩ : ∃ d, c - a = d + 1 := ⟨c - a - 1, by omega⟩
  obtain ⟨e, he⟩ : ∃ e, c = e + 1 := ⟨c - 1, by omega⟩
  have hev1 : ((2 : ℤ) ^ (c - a) * 3 ^ a) % 2 = 0 := by
    rw [hd, show (2 : ℤ) ^ (d + 1) * 3 ^ a = 2 * (2 ^ d * 3 ^ a) by ring]
    exact Int.mul_emod_right 2 _
  have hev2 : ((2 : ℤ) ^ c * n) % 2 = 0 := by
    rw [he, show (2 : ℤ) ^ (e + 1) * n = 2 * (2 ^ e * n) by ring]
    exact Int.mul_emod_right 2 _
  omega

/-- The ε₁-window of the NKR application: for `a < c`,
`θ^c < (3^c·3^a)^{-ε₁}` with `ε₁ = log θ⁻¹/(2 log 3)`. -/
private lemma theta_pow_lt_height_rpow {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {a c : ℕ} (hac : a < c) :
    θ ^ c < (((3 ^ c * 3 ^ a : ℕ)) : ℝ)
      ^ (-(Real.log θ⁻¹ / (2 * Real.log 3))) := by
  have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hlogθ : Real.log θ < 0 := Real.log_neg hθ0 hθ1
  have hcast : (((3 ^ c * 3 ^ a : ℕ)) : ℝ) = (3 : ℝ) ^ c * 3 ^ a := by
    push_cast
    ring
  have hpos : (0 : ℝ) < (3 : ℝ) ^ c * 3 ^ a := by positivity
  have hθc : (0 : ℝ) < θ ^ c := by positivity
  have hLHS : θ ^ c = Real.exp ((c : ℝ) * Real.log θ) := by
    rw [← Real.log_pow, Real.exp_log hθc]
  have hRHS : ((3 : ℝ) ^ c * 3 ^ a) ^ (-(Real.log θ⁻¹ / (2 * Real.log 3)))
      = Real.exp (((c : ℝ) * Real.log 3 + (a : ℝ) * Real.log 3)
          * (-(Real.log θ⁻¹ / (2 * Real.log 3)))) := by
    rw [Real.rpow_def_of_pos hpos]
    congr 1
    rw [Real.log_mul (by positivity : (0 : ℝ) < (3 : ℝ) ^ c).ne'
      (by positivity : (0 : ℝ) < (3 : ℝ) ^ a).ne', Real.log_pow, Real.log_pow]
  rw [hcast, hLHS, hRHS, Real.exp_lt_exp, Real.log_inv]
  have hkey : ((c : ℝ) * Real.log 3 + (a : ℝ) * Real.log 3)
      * (-(-Real.log θ / (2 * Real.log 3))) = ((c : ℝ) + a) * Real.log θ / 2 := by
    field_simp
  rw [hkey]
  have hca : (a : ℝ) < (c : ℝ) := by exact_mod_cast hac
  nlinarith [mul_neg_of_pos_of_neg (show (0 : ℝ) < (c : ℝ) - a by linarith) hlogθ]

/-! ## The NKR branch of the dichotomy -/

/-- **The infinitely-many-gaps branch**: a family of (K)-violating pairs with
pairwise-distinct gaps is finite.  One tuple `((3/2)^c, (3/2)^a)` per pair
satisfies all hypotheses of [NKR25] Thm 1.3, whose integrality conclusion is
absurd for `(3/2)^c`.  Footprint std3 + [NKR25]. -/
private lemma finite_of_gap_injOn (θ : ℚ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {T : Set (ℕ × ℕ)} (hTsub : T ⊆ kernelViolators θ)
    (hinj : Set.InjOn (fun p : ℕ × ℕ => p.2 - p.1) T) : T.Finite := by
  by_contra hTfin
  have hTinf : T.Infinite := hTfin
  have hθ0' : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ0
  have hθ1' : (θ : ℝ) < 1 := by exact_mod_cast hθ1
  have hεpos : 0 < Real.log (θ : ℝ)⁻¹ / (2 * Real.log 3) := by
    apply div_pos
    · rw [Real.log_inv]
      have := Real.log_neg hθ0' hθ1'
      linarith
    · have := Real.log_pos (show (1 : ℝ) < 3 by norm_num)
      linarith
  -- the NKR hypotheses for 𝒩 := enc '' T
  have habs : ∀ q ∈ enc '' T,
      1 ≤ |NKR.uval q.1.1 q.1.2| ∧ 1 ≤ |NKR.uval q.2.1 q.2.2| := by
    rintro q ⟨p, -, rfl⟩
    simp only [enc_fst_fst, enc_fst_snd, enc_snd_fst, enc_snd_snd,
      NKR.uval_neg_natCast]
    rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
    exact ⟨one_le_pow₀ (by norm_num), one_le_pow₀ (by norm_num)⟩
  have hP2 : ∀ q ∈ enc '' T,
      NKR.uval q.1.1 q.1.2 ≠ -NKR.uval q.2.1 q.2.2 := by
    rintro q ⟨p, -, rfl⟩
    simp only [enc_fst_fst, enc_fst_snd, enc_snd_fst, enc_snd_snd,
      NKR.uval_neg_natCast]
    have h1 : (0 : ℚ) < (3 / 2) ^ p.2 := by positivity
    have h2 : (0 : ℚ) < (3 / 2) ^ p.1 := by positivity
    intro h
    rw [h] at h1
    linarith
  have hratio : ∀ q ∈ enc '' T, ∀ q' ∈ enc '' T, q ≠ q' →
      NKR.uval q.1.1 q.1.2 / NKR.uval q.2.1 q.2.2
        ≠ NKR.uval q'.1.1 q'.1.2 / NKR.uval q'.2.1 q'.2.2 ∧
      NKR.uval q.2.1 q.2.2 / NKR.uval q.1.1 q.1.2
        ≠ NKR.uval q'.2.1 q'.2.2 / NKR.uval q'.1.1 q'.1.2 := by
    rintro q ⟨p, hpT, rfl⟩ q' ⟨p', hp'T, rfl⟩ hqq'
    have hpp' : p ≠ p' := fun h => hqq' (congrArg enc h)
    obtain ⟨-, hac, -⟩ := hTsub hpT
    obtain ⟨-, hac', -⟩ := hTsub hp'T
    have hgap : p.2 - p.1 ≠ p'.2 - p'.1 := fun h => hpp' (hinj hpT hp'T h)
    have hne : (3 / 2 : ℚ) ^ (p.2 - p.1) ≠ (3 / 2 : ℚ) ^ (p'.2 - p'.1) :=
      fun h => hgap (three_halves_pow_injective h)
    simp only [enc_fst_fst, enc_fst_snd, enc_snd_fst, enc_snd_snd,
      NKR.uval_neg_natCast]
    constructor
    · rw [three_halves_div_pow hac.le, three_halves_div_pow hac'.le]
      exact hne
    · intro h
      apply hne
      have h' := congrArg (·⁻¹) h
      simp only [inv_div] at h'
      rwa [three_halves_div_pow hac.le, three_halves_div_pow hac'.le] at h'
  have happrox : ∀ q ∈ enc '' T,
      (((1 : ℚ) * NKR.uval q.1.1 q.1.2
          + (-1 : ℚ) * NKR.uval q.2.1 q.2.2).distToNearestInt : ℝ)
        < ((CZ.height23 q.1.1 q.1.2 * CZ.height23 q.2.1 q.2.2 : ℕ) : ℝ)
            ^ (-(Real.log (θ : ℝ)⁻¹ / (2 * Real.log 3))) := by
    rintro q ⟨p, hpT, rfl⟩
    obtain ⟨ha2, hac, hdist⟩ := hTsub hpT
    simp only [enc_fst_fst, enc_fst_snd, enc_snd_fst, enc_snd_snd,
      NKR.uval_neg_natCast, CZ.height23_neg_natCast, one_mul, neg_one_mul,
      ← sub_eq_add_neg]
    calc (((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1).distToNearestInt : ℝ)
        ≤ ((θ ^ p.2 : ℚ) : ℝ) := by exact_mod_cast hdist
      _ = (θ : ℝ) ^ p.2 := by push_cast; ring
      _ < _ := theta_pow_lt_height_rpow hθ0' hθ1' hac
  -- strict positivity: `(3/2)^c − (3/2)^a` is not an integer (parity)
  have hposd : ∀ q ∈ enc '' T,
      0 < ((1 : ℚ) * NKR.uval q.1.1 q.1.2
        + (-1 : ℚ) * NKR.uval q.2.1 q.2.2).distToNearestInt := by
    rintro q ⟨p, hpT, rfl⟩
    obtain ⟨ha2, hac, -⟩ := hTsub hpT
    simp only [enc_fst_fst, enc_fst_snd, enc_snd_fst, enc_snd_snd,
      NKR.uval_neg_natCast, one_mul, neg_one_mul, ← sub_eq_add_neg]
    rcases lt_or_eq_of_le
      (Rat.distToNearestInt_nonneg ((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1)) with h | h
    · exact h
    · exfalso
      obtain ⟨n, hn⟩ := Rat.distToNearestInt_eq_zero_iff.mp h.symm
      exact three_halves_pow_sub_not_int (by omega) hac n hn
  -- apply the repaired-and-derived [NKR25] Thm 1.3(i); contradict integrality of (3/2)^c
  obtain ⟨q, hq𝒩, ⟨n, hn⟩, -⟩ := NKR.sUnit_pair_integrality_of_subspace 1 (-1) one_ne_zero
    (by norm_num) (Real.log (θ : ℝ)⁻¹ / (2 * Real.log 3)) hεpos (enc '' T)
    (hTinf.image enc_injective.injOn) habs hP2 hratio hposd happrox
  obtain ⟨p, hpT, rfl⟩ := hq𝒩
  obtain ⟨ha2, hac, -⟩ := hTsub hpT
  rw [enc_fst_fst, enc_fst_snd, NKR.uval_neg_natCast] at hn
  exact three_halves_pow_not_int (by omega) n hn

/-! ## The gap dichotomy and M4 -/

/-- **The kernel (K) at every rational scale** (the gap
dichotomy): for every rational `θ ∈ (0, 1)`, only finitely many pairs
`2 ≤ a < c` satisfy `‖(3/2)^c − (3/2)^a‖ ≤ θ^c`.  Bounded-gap violators are
finite by the CZ 2004 slices (Stage 2b); an infinite family with unbounded
gaps contains a gap-injective infinite subfamily (one violator per gap),
which [NKR25] Thm 1.3 forbids.  Ineffective.  Footprint std3 + [CZ04] +
[NKR25] (**preprint**). -/
theorem pairRepulsion_all (θ : ℚ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    PairRepulsion θ := by
  by_contra hV
  have hVinf : (kernelViolators θ).Infinite := hV
  set gap : ℕ × ℕ → ℕ := fun p => p.2 - p.1 with hgapdef
  by_cases hg : (gap '' kernelViolators θ).Finite
  · -- bounded gaps: contradiction with the CZ gap-bounded slice
    obtain ⟨S, hS⟩ := hg.bddAbove
    apply hVinf
    apply Set.Finite.subset (gapBounded_slice_finite S θ hθ0 hθ1)
    intro p hp
    refine ⟨hp, ?_⟩
    have h1 := hS (Set.mem_image_of_mem gap hp)
    obtain ⟨-, hac, -⟩ := hp
    have h2 : gap p = p.2 - p.1 := rfl
    omega
  · -- unbounded gaps: extract a gap-injective section and apply NKR
    have hginf : (gap '' kernelViolators θ).Infinite := hg
    have hsec : ∀ y ∈ gap '' kernelViolators θ,
        ∃ a ∈ kernelViolators θ, gap a = y := by
      rintro y ⟨p, hp, rfl⟩
      exact ⟨p, hp, rfl⟩
    have hgapinv : ∀ y ∈ gap '' kernelViolators θ,
        gap (Function.invFunOn gap (kernelViolators θ) y) = y :=
      fun y hy => Function.invFunOn_eq (hsec y hy)
    have hTsub : Function.invFunOn gap (kernelViolators θ)
        '' (gap '' kernelViolators θ) ⊆ kernelViolators θ := by
      rintro t ⟨y, hy, rfl⟩
      exact Function.invFunOn_mem (hsec y hy)
    have hinvinj : Set.InjOn (Function.invFunOn gap (kernelViolators θ))
        (gap '' kernelViolators θ) := by
      intro y1 hy1 y2 hy2 h
      rw [← hgapinv y1 hy1, ← hgapinv y2 hy2, h]
    have hTinf : (Function.invFunOn gap (kernelViolators θ)
        '' (gap '' kernelViolators θ)).Infinite := hginf.image hinvinj
    have hinjT : Set.InjOn gap (Function.invFunOn gap (kernelViolators θ)
        '' (gap '' kernelViolators θ)) := by
      rintro t1 ⟨y1, hy1, rfl⟩ t2 ⟨y2, hy2, rfl⟩ h
      rw [hgapinv y1 hy1, hgapinv y2 hy2] at h
      rw [h]
    exact hTinf (finite_of_gap_injOn θ hθ0 hθ1 hTsub hinjT)

/-- **The Diophantine kernel (K) holds**: exponential pair
repulsion for the orbit of `(3/2)^n` at every rational scale.  Footprint
std3 + [CZ04] + [NKR25] (**preprint**). -/
theorem kernel_holds : Kernel := fun θ hθ0 hθ1 => pairRepulsion_all θ hθ0 hθ1

/-- **M4: the steering word has superlinear subword complexity**,
`p_T(k)/k → ∞` — the target of the development, reached
through: Lemma R (Stage 0) → the pigeonhole reduction to (K) (Stage 1) →
the CZ 2004 gap slices (Stage 2b/2b′) → the NKR gap dichotomy (Stage 2c).
Ineffective.  Footprint std3 + [CZ04] (refereed) + [NKR25] (**unrefereed
preprint**; the preprint-free conditional form is
`TH.superlinear_of_middleBand`). -/
theorem complexity_superlinear : Superlinear := superlinear_of_kernel kernel_holds

/-- The Stage-2c **middle band is finite** at every scale, gap threshold and
band parameter — the named `hexc`-style hypothesis of
`TH.superlinear_of_middleBand`, discharged modulo [NKR25]. -/
theorem middleBandViolators_finite (θ ε' : ℚ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (S : ℕ) : (middleBandViolators θ ε' S).Finite :=
  Set.Finite.subset (pairRepulsion_all θ hθ0 hθ1) (Set.sep_subset _ _)

end TH

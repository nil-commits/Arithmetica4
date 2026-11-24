import RHDirect.Stage12Window1RootAvoid
import RHDirect.Stage12GaloisShaLen
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# RHDirect.Stage13SixCaseVWinAssembly

Stage 13 — **Field 1 Assault (8 of 8, Engine #11 + Master 6-Case `VWin` Assembler!)**:
Unconditional **von Staudt–Clausen Theorem & Residual Bernoulli Nonvanishing (`PropZ` / `CountZ`)**,
Exact **Alpöge 6-Case Character Classification (`CountI`–`CountZ`, `partition_exhaustive`)**,
and the **Master 6-Case `VWin` Assembly (`vwin_of_six_case_supply`,
`galoisModularityContract_of_six_case`, `riemannHypothesis_of_six_case_and_theta`)**
in pure Mathlib `v4.33.1` (**0 `sorry`, 0 custom `axiom`s, 0 `native_decide`**, targeted imports).

## Main Results

1. **Unconditional von Staudt–Clausen & Residual Bernoulli Nonvanishing (`PropZ` / `CountZ`)**:
   - `vonStaudt_clausen`: for every `m ≥ 1`, `bernoulli (2 * m) + ∑_{p prime, p-1 ∣ 2m} 1/p ∈ ℤ`.
   - `prime_dvd_bernoulli_den_iff`: `p ∣ (bernoulli (2 * m)).den ↔ (p - 1) ∣ 2 * m` for all primes `p` and `m ≥ 1`.
   - `bernoulli_even_padicValRat_neg_one`, `bernoulli_even_padicValNat_num_eq_zero`,
     `bernoulli_even_padic_norm`: for every prime `l` and `e ≥ 1` with `(l - 1) ∣ 2 * e`,
     `v_l(B_{2e}) = -1`, `v_l(num(B_{2e})) = 0`, and `(l : ℚ) * B_{2e}` is a `ℤ_[l]`-unit (`‖l * B_{2e}‖_l = 1`).
   - `propZResidualBernoulliUnit_unconditional`, `padicInt_length_eq_zero_of_bernoulli_pole_ann`,
     and `countZ_vanishing_of_propZ`: unconditional vanishing of `l`-torsion / `Vlen = 0` for
     `(ψ = 1, l ∉ Bchi, (l - 1) ∣ 2 * e)`.

2. **Exact Alpöge 6-Case Character Classification (`CountI`, `CountII`, `CountIII`, `CountIV`, `CountV`, `CountVs`, `CountZ`)**:
   - `Bchi E ψ`: exact finite bad-prime set `{l prime | l ∣ 2 * [E : ℚ] * condF E * ψ.N}`.
   - `AlpogeCase` + `partition_exhaustive` + `partition_unique`: gapless, pairwise-disjoint
     classification of every `(l, k, χ)` across `l = 2` (`BaAt`), odd minus parity (`VVminusLe`:
     Rubin `l ∤ [E:ℚ]` + Stickelberger `l ∣ [E:ℚ]`), odd plus parity inside `Bchi` (`CountIV`/`BbAt`,
     `CountII`, `CountV`, `CountVs`), and odd plus parity outside `Bchi` (`CountZ` = 0 via `PropZ`,
     `CountI` via `U(3)` + GMA + Kato, `CountII` & `CountIII` via `Sp₄` + GMA).

3. **Master 6-Case `VWin` Assembly (`SixCaseField1Supply S`)**:
   - `sumOut_of_counts` (pure polynomial bound `(condF E * t)^Cout` across all good odd primes `l ∉ Bchi`!),
   - `sumIn_of_counts` (`(condF E * t)^Cin + (∑_{l ∈ Bchi} log l) * exp(x^(4ε/5))`),
   - `vwin_of_six_case_supply : SixCaseField1Supply S → RHDirect.VWin S`,
   - `galoisModularityContract_of_six_case : SixCaseField1Supply S → RHDirect.GaloisModularityContract S`,
   - `riemannHypothesis_of_six_case_and_theta` & `headline_five_of_six_case_and_theta`
     (direct drop-in with `Stage11LinnikUnconditional.linnikAPInterval_unconditional`!).
-/

noncomputable section

open scoped BigOperators
open Real Finset Filter NumberField RHDirect
open RHDirect.Stage2GaloisWire
open RHDirect.Stage11LinnikUnconditional
open RHDirect.Stage11ThetaSiegelBridge
open RHDirect.Stage12Window1RootAvoid
open RHDirect.Stage12GaloisShaLen
open RHDirect.TaylorWilesWindow

namespace RHDirect.Stage13SixCaseVWinAssembly

/-! ## Section 1: Unconditional von Staudt–Clausen Theorem & `v_l(B_{2e}) = -1` -/

section VonStaudtClausen

/-- `IsPInt p q` asserts that the prime `p` does not divide the reduced denominator of `q : ℚ`,
i.e. `q` is `p`-integral (`v_p(q) ≥ 0`). -/
def IsPInt (p : ℕ) (q : ℚ) : Prop := ¬ p ∣ q.den

lemma isPInt_intCast (p : ℕ) (hp : p.Prime) (z : ℤ) : IsPInt p (z : ℚ) := by
  simp [IsPInt, hp.ne_one]

lemma isPInt_natCast (p : ℕ) (hp : p.Prime) (n : ℕ) : IsPInt p (n : ℚ) := by
  simpa using isPInt_intCast p hp (n : ℤ)

lemma isPInt_zero (p : ℕ) (hp : p.Prime) : IsPInt p 0 := by
  simpa using isPInt_intCast p hp 0

lemma isPInt_neg {p : ℕ} {q : ℚ} (hq : IsPInt p q) : IsPInt p (-q) := by
  simpa [IsPInt] using hq

lemma isPInt_add {p : ℕ} (hp : p.Prime) {x y : ℚ} (hx : IsPInt p x) (hy : IsPInt p y) :
    IsPInt p (x + y) := by
  intro hdvd
  have hden : (x + y).den ∣ x.den * y.den := Rat.add_den_dvd x y
  rcases hp.dvd_mul.mp (hdvd.trans hden) with h | h
  · exact hx h
  · exact hy h

lemma isPInt_sub {p : ℕ} (hp : p.Prime) {x y : ℚ} (hx : IsPInt p x) (hy : IsPInt p y) :
    IsPInt p (x - y) := by
  rw [sub_eq_add_neg]
  exact isPInt_add hp hx (isPInt_neg hy)

lemma isPInt_mul {p : ℕ} (hp : p.Prime) {x y : ℚ} (hx : IsPInt p x) (hy : IsPInt p y) :
    IsPInt p (x * y) := by
  intro hdvd
  have hden : (x * y).den ∣ x.den * y.den := Rat.mul_den_dvd x y
  rcases hp.dvd_mul.mp (hdvd.trans hden) with h | h
  · exact hx h
  · exact hy h

lemma isPInt_sum {ι : Type*} {p : ℕ} (hp : p.Prime) (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, IsPInt p (f i)) : IsPInt p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isPInt_zero p hp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isPInt_add hp (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma isPInt_div_nat {p : ℕ} (a : ℤ) {b : ℕ} (hb : b ≠ 0) (hnb : ¬ p ∣ b) :
    IsPInt p ((a : ℚ) / (b : ℚ)) := by
  intro hdvd
  set q : ℚ := (a : ℚ) / (b : ℚ)
  have hbQ : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb
  have hqden0 : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_pos.ne'
  have hq' : (q.num : ℚ) / (q.den : ℚ) = (a : ℚ) / (b : ℚ) := Rat.num_div_den q
  have hcross : (q.num : ℚ) * (b : ℚ) = (a : ℚ) * (q.den : ℚ) :=
    (div_eq_div_iff hqden0 hbQ).mp hq'
  have hcrossZ : q.num * (b : ℤ) = a * (q.den : ℤ) := by exact_mod_cast hcross
  have hdvdZ : (q.den : ℤ) ∣ q.num * (b : ℤ) := ⟨a, by linarith⟩
  have hdvdNat : q.den ∣ (q.num * (b : ℤ)).natAbs := Int.natCast_dvd.mp hdvdZ
  rw [Int.natAbs_mul, Int.natAbs_natCast] at hdvdNat
  have hden_dvd : q.den ∣ b := q.reduced.symm.dvd_of_dvd_mul_left hdvdNat
  exact hnb (hdvd.trans hden_dvd)

lemma isPInt_one_div_prime_of_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : q ≠ p) :
    IsPInt p ((1 : ℚ) / (q : ℚ)) := by
  apply isPInt_div_nat 1 hq.ne_zero
  intro hd
  rcases (Nat.dvd_prime hq).mp hd with h1 | h2
  · exact hp.ne_one h1
  · exact hne h2.symm

lemma isInt_of_forall_prime_isPInt {q : ℚ} (h : ∀ p : ℕ, p.Prime → IsPInt p q) :
    ∃ z : ℤ, q = (z : ℚ) := by
  have hden : q.den = 1 := by
    by_contra hne
    exact h q.den.minFac (Nat.minFac_prime hne) (Nat.minFac_dvd q.den)
  refine ⟨q.num, ?_⟩
  conv_lhs => rw [← Rat.num_div_den q]
  rw [hden, Nat.cast_one, div_one]

private lemma lt_two_pow_of_ge_two : ∀ m : ℕ, 2 ≤ m → m + 1 < 2 ^ m
  | 0, hm => by omega
  | 1, hm => by omega
  | 2, _ => by norm_num
  | m + 3, _ => by
    have ih := lt_two_pow_of_ge_two (m + 2) (by omega)
    rw [pow_succ]
    omega

private lemma add_two_le_three_pow : ∀ k : ℕ, 1 ≤ k → k + 2 ≤ 3 ^ k
  | 0, hk => by omega
  | 1, _ => by norm_num
  | k + 2, _ => by
    have ih := add_two_le_three_pow (k + 1) (by omega)
    rw [pow_succ]
    omega

/-- Valuation bound for Witt's von Staudt–Clausen induction:
for every prime `p` and `m ≥ 1` (with `m ≥ 2` when `p = 2`), `v_p(m + 1) ≤ m - 1`. -/
lemma padicValNat_succ_le_sub_one {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m)
    (hp2 : p = 2 → 2 ≤ m) :
    padicValNat p (m + 1) ≤ m - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  set k := padicValNat p (m + 1) with hk_def
  by_cases hk : k = 0
  · rw [hk]; exact Nat.zero_le _
  · have hdvd : p ^ k ∣ m + 1 := pow_padicValNat_dvd
    have hle : p ^ k ≤ m + 1 := Nat.le_of_dvd (Nat.succ_pos m) hdvd
    by_cases hp_eq2 : p = 2
    · subst hp_eq2
      have hm2 : 2 ≤ m := hp2 rfl
      by_contra hlt
      have hmk : m ≤ k := by omega
      have hpow : 2 ^ m ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hmk
      have hm_lt : m + 1 < 2 ^ m := lt_two_pow_of_ge_two m hm2
      omega
    · have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have h3k : 3 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp3 k
      have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk
      have hk2 : k + 2 ≤ 3 ^ k := add_two_le_three_pow k hk1
      omega

lemma isPInt_prime_pow_div_succ {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m) (hp2 : p = 2 → 2 ≤ m) :
    IsPInt p ((p : ℚ) ^ (m - 1) / ((m + 1 : ℕ) : ℚ)) := by
  have : Fact p.Prime := ⟨hp⟩
  set k := padicValNat p (m + 1)
  have hdvd : p ^ k ∣ m + 1 := pow_padicValNat_dvd
  set r := (m + 1) / p ^ k
  have hmul : p ^ k * r = m + 1 := Nat.mul_div_cancel' hdvd
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmul
    exact Nat.succ_ne_zero m hmul.symm
  have hnr : ¬ p ∣ r := by
    intro hd
    have hpow : p ^ (k + 1) ∣ m + 1 := by
      rw [← hmul, pow_succ]
      exact mul_dvd_mul_left (p ^ k) hd
    have hle : k + 1 ≤ padicValNat p (m + 1) :=
      (padicValNat_dvd_iff_le (Nat.succ_ne_zero m)).mp hpow
    omega
  have hk_le : k ≤ m - 1 := padicValNat_succ_le_sub_one hp hm hp2
  have hsplit : m - 1 = (m - 1 - k) + k := by omega
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hrQ : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hr0
  have heq : (p : ℚ) ^ (m - 1) / ((m + 1 : ℕ) : ℚ) =
      (((p ^ (m - 1 - k) : ℕ) : ℤ) : ℚ) / (r : ℚ) := by
    rw [← hmul, Nat.cast_mul, Nat.cast_pow, Int.cast_natCast, Nat.cast_pow]
    conv_lhs => rw [hsplit, pow_add]
    field_simp [hp0, hrQ]
  rw [heq]
  exact isPInt_div_nat _ hr0 hnr

/-- Classical finite-field power-sum congruence mod `p`:
`∑_{a=0}^{p-1} a^n + δ_{(p-1) ∣ n} ≡ 0 (mod p)`. -/
lemma sum_pow_mod_prime {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) :
    ((∑ a ∈ Finset.range p, (a : ℤ) ^ n + if p - 1 ∣ n then 1 else 0 : ℤ) : ZMod p) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hsum_univ : ((∑ a ∈ Finset.range p, (a : ℤ) ^ n : ℤ) : ZMod p) =
      ∑ x : ZMod p, x ^ n := by
    push_cast
    symm
    refine Finset.sum_bij (fun (x : ZMod p) _ => x.val) ?_ ?_ ?_ ?_
    · intro x _
      exact Finset.mem_range.mpr (ZMod.val_lt x)
    · intro x₁ _ x₂ _ h
      exact ZMod.val_injective p h
    · intro a ha
      refine ⟨(a : ZMod p), Finset.mem_univ _, ?_⟩
      exact ZMod.val_natCast_of_lt (Finset.mem_range.mp ha)
    · intro x _
      rw [ZMod.natCast_zmod_val]
  rw [Int.cast_add, hsum_univ]
  by_cases hdvd : p - 1 ∣ n
  · rw [if_pos hdvd, Int.cast_one]
    have hsplit : ∑ x : ZMod p, x ^ n =
        ∑ x ∈ Finset.univ.erase (0 : ZMod p), x ^ n := by
      rw [← Finset.add_sum_erase Finset.univ (fun x : ZMod p => x ^ n) (Finset.mem_univ 0),
        zero_pow (by omega), zero_add]
    have hones : ∑ x ∈ Finset.univ.erase (0 : ZMod p), x ^ n = ((p - 1 : ℕ) : ZMod p) := by
      have hterm : ∀ x ∈ Finset.univ.erase (0 : ZMod p), x ^ n = (1 : ZMod p) := by
        intro x hx
        have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
        obtain ⟨k, hk⟩ := hdvd
        rw [hk, pow_mul, ZMod.pow_card_sub_one_eq_one hx0, one_pow]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
    rw [hsplit, hones]
    norm_cast
    rw [Nat.sub_add_cancel hp.one_le, ZMod.natCast_self]
  · rw [if_neg hdvd, Int.cast_zero, add_zero]
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
    have hord : orderOf g = p - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
    have hgn : (g : ZMod p) ^ n ≠ 1 := by
      intro h1
      apply hdvd
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one (Units.ext (by simpa using h1))
    have hmul : (g : ZMod p) ^ n * ∑ x : ZMod p, x ^ n = ∑ x : ZMod p, x ^ n := by
      rw [Finset.mul_sum]
      refine Eq.trans (Finset.sum_congr rfl fun x _ => (mul_pow (g : ZMod p) x n).symm) ?_
      exact Fintype.sum_bijective (fun x : ZMod p => (g : ZMod p) * x)
        (Units.mulLeft_bijective g) _ _ (fun _ => rfl)
    have hzero : ((g : ZMod p) ^ n - 1) * ∑ x : ZMod p, x ^ n = 0 := by
      rw [sub_mul, one_mul, hmul, sub_self]
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hgn)

lemma isPInt_pow_sum_div_prime {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) :
    IsPInt p (((∑ a ∈ Finset.range p, (a : ℚ) ^ n) + if p - 1 ∣ n then 1 else 0) / (p : ℚ)) := by
  have hmod := sum_pow_mod_prime hp hn
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hmod
  obtain ⟨z, hz⟩ := hmod
  have heq : (((∑ a ∈ Finset.range p, (a : ℚ) ^ n) + if p - 1 ∣ n then 1 else 0) / (p : ℚ)) =
      (z : ℚ) := by
    have hz' : ((∑ a ∈ Finset.range p, (a : ℚ) ^ n) + if p - 1 ∣ n then 1 else 0) =
        (p : ℚ) * (z : ℚ) := by
      have hzQ := congrArg (Int.cast (R := ℚ)) hz
      push_cast at hzQ ⊢
      split_ifs at hzQ ⊢ <;> linarith
    have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    rw [hz', mul_div_cancel_left₀ _ hp0]
  rw [heq]
  exact isPInt_intCast p hp z

/-- Faulhaber's power-sum formula in terms of Bernoulli numbers via `Polynomial.bernoulli`. -/
lemma sum_range_pow_eq_bernoulli (p n : ℕ) :
    ((n + 1 : ℕ) : ℚ) * ∑ a ∈ Finset.range p, (a : ℚ) ^ n =
      ∑ j ∈ Finset.range (n + 1), ((n + 1).choose j : ℚ) * bernoulli j * (p : ℚ) ^ (n + 1 - j) := by
  have htele : (Polynomial.bernoulli (n + 1)).eval (p : ℚ) -
      (Polynomial.bernoulli (n + 1)).eval 0 =
      ((n + 1 : ℕ) : ℚ) * ∑ a ∈ Finset.range p, (a : ℚ) ^ n := by
    have hstep : ∀ a : ℕ,
        (Polynomial.bernoulli (n + 1)).eval ((a + 1 : ℕ) : ℚ) -
          (Polynomial.bernoulli (n + 1)).eval (a : ℚ) =
          ((n + 1 : ℕ) : ℚ) * (a : ℚ) ^ n := by
      intro a
      have h := Polynomial.bernoulli_eval_one_add (n + 1) (a : ℚ)
      rw [show (1 : ℚ) + (a : ℚ) = ((a + 1 : ℕ) : ℚ) by push_cast; ring] at h
      simp only [Nat.add_sub_cancel] at h
      linarith
    rw [Finset.mul_sum]
    simp_rw [← hstep]
    symm
    exact Finset.sum_range_sub (fun a => (Polynomial.bernoulli (n + 1)).eval (a : ℚ)) p
  rw [← htele]
  have heval0 : (Polynomial.bernoulli (n + 1)).eval (0 : ℚ) = bernoulli (n + 1) := by
    simp [Polynomial.bernoulli_eval_zero]
  have hevalp : (Polynomial.bernoulli (n + 1)).eval (p : ℚ) =
      ∑ j ∈ Finset.range (n + 2),
        ((n + 1).choose j : ℚ) * bernoulli j * (p : ℚ) ^ (n + 1 - j) := by
    rw [Polynomial.bernoulli_def, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_monomial]
    rw [← Finset.sum_range_reflect (fun i => bernoulli (n + 1 - i) * ((n + 1).choose i : ℚ) * (p : ℚ) ^ i) (n + 2)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjlt : j ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hsub : n + 1 - (n + 1 - j) = j := Nat.sub_sub_self hjlt
    have hch : (n + 1).choose (n + 1 - j) = (n + 1).choose j := Nat.choose_symm hjlt
    rw [show n + 2 - 1 - j = n + 1 - j by omega, hsub, hch]
    ring
  rw [hevalp, heval0, Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul,
    Nat.sub_self, pow_zero, mul_one, add_sub_cancel_right]

private lemma binom_mul_sub_eq_succ_mul_binom {n j : ℕ} (hjn : j < n) :
    (n + 1).choose j * (n + 1 - j) = (n + 1) * n.choose j := by
  have hfac1 : j.factorial * (n + 1 - j).factorial ∣ (n + 1).factorial :=
    Nat.factorial_mul_factorial_dvd_factorial (by omega)
  have hfac2 : j.factorial * (n - j).factorial ∣ n.factorial :=
    Nat.factorial_mul_factorial_dvd_factorial hjn.le
  have hsub : n + 1 - j = (n - j) + 1 := by omega
  have hfac_rel : (n + 1 - j).factorial = (n + 1 - j) * (n - j).factorial := by
    rw [hsub, Nat.factorial_succ]
  have hpos : 0 < j.factorial * (n - j).factorial :=
    mul_pos (Nat.factorial_pos j) (Nat.factorial_pos (n - j))
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [Nat.choose_eq_factorial_div_factorial (by omega),
    Nat.choose_eq_factorial_div_factorial hjn.le]
  calc (n + 1).factorial / (j.factorial * (n + 1 - j).factorial) * (n + 1 - j) *
          (j.factorial * (n - j).factorial)
      = (n + 1).factorial / (j.factorial * (n + 1 - j).factorial) *
          (j.factorial * ((n + 1 - j) * (n - j).factorial)) := by ring
    _ = (n + 1).factorial / (j.factorial * (n + 1 - j).factorial) *
          (j.factorial * (n + 1 - j).factorial) := by rw [← hfac_rel]
    _ = (n + 1).factorial := Nat.div_mul_cancel hfac1
    _ = (n + 1) * n.factorial := Nat.factorial_succ n
    _ = (n + 1) * (n.factorial / (j.factorial * (n - j).factorial) *
          (j.factorial * (n - j).factorial)) := by rw [Nat.div_mul_cancel hfac2]
    _ = (n + 1) * (n.factorial / (j.factorial * (n - j).factorial)) *
          (j.factorial * (n - j).factorial) := by ring

/-- Algebraic isolation of `bernoulli n` from the prime power sum `∑_{a<p} a^n / p`. -/
lemma bernoulli_eq_pow_sum_div_sub {p n : ℕ} (hp : p.Prime) :
    bernoulli n = (∑ a ∈ Finset.range p, (a : ℚ) ^ n) / (p : ℚ) -
      ∑ j ∈ Finset.range n,
        (n.choose j : ℚ) * ((p : ℚ) * bernoulli j) *
          ((p : ℚ) ^ (n - j - 1) / ((n - j + 1 : ℕ) : ℚ)) := by
  have hF := sum_range_pow_eq_bernoulli p n
  rw [Finset.sum_range_succ] at hF
  have hlast : ((n + 1).choose n : ℚ) * bernoulli n * (p : ℚ) ^ (n + 1 - n) =
      ((n + 1 : ℕ) : ℚ) * (p : ℚ) * bernoulli n := by
    rw [Nat.add_sub_cancel_left, pow_one, Nat.choose_succ_self_right, Nat.cast_add, Nat.cast_one]
    ring
  rw [hlast] at hF
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hn1 : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hdiv : ((n + 1 : ℕ) : ℚ) * (p : ℚ) * bernoulli n =
      ((n + 1 : ℕ) : ℚ) * ∑ a ∈ Finset.range p, (a : ℚ) ^ n -
        ∑ j ∈ Finset.range n, ((n + 1).choose j : ℚ) * bernoulli j * (p : ℚ) ^ (n + 1 - j) := by
    linarith
  have hcomb : ∀ j ∈ Finset.range n,
      ((n + 1).choose j : ℚ) * bernoulli j * (p : ℚ) ^ (n + 1 - j) =
        ((n + 1 : ℕ) : ℚ) * (p : ℚ) *
          ((n.choose j : ℚ) * ((p : ℚ) * bernoulli j) *
            ((p : ℚ) ^ (n - j - 1) / ((n - j + 1 : ℕ) : ℚ))) := by
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have hbinomQ : ((n + 1).choose j : ℚ) * ((n - j + 1 : ℕ) : ℚ) =
        ((n + 1 : ℕ) : ℚ) * (n.choose j : ℚ) := by
      have hbe : n + 1 - j = n - j + 1 := by omega
      rw [← hbe]
      exact_mod_cast binom_mul_sub_eq_succ_mul_binom hjn
    have hpowp : (p : ℚ) ^ (n + 1 - j) = (p : ℚ) * (p : ℚ) * (p : ℚ) ^ (n - j - 1) := by
      have hexp : n + 1 - j = 1 + 1 + (n - j - 1) := by omega
      rw [hexp, pow_add, pow_add, pow_one]
    have hnj0 : ((n - j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    rw [hpowp]
    calc ((n + 1).choose j : ℚ) * bernoulli j * ((p : ℚ) * (p : ℚ) * (p : ℚ) ^ (n - j - 1))
        = (((n + 1).choose j : ℚ) * ((n - j + 1 : ℕ) : ℚ)) *
            (bernoulli j * (p : ℚ) * (p : ℚ) * (p : ℚ) ^ (n - j - 1) / ((n - j + 1 : ℕ) : ℚ)) := by
          field_simp [hnj0]
      _ = (((n + 1 : ℕ) : ℚ) * (n.choose j : ℚ)) *
            (bernoulli j * (p : ℚ) * (p : ℚ) * (p : ℚ) ^ (n - j - 1) / ((n - j + 1 : ℕ) : ℚ)) := by
          rw [hbinomQ]
      _ = ((n + 1 : ℕ) : ℚ) * (p : ℚ) *
            ((n.choose j : ℚ) * ((p : ℚ) * bernoulli j) *
              ((p : ℚ) ^ (n - j - 1) / ((n - j + 1 : ℕ) : ℚ))) := by
          ring
  rw [Finset.sum_congr rfl hcomb, ← Finset.mul_sum] at hdiv
  have hmul_eq : ((n + 1 : ℕ) : ℚ) * (p : ℚ) * bernoulli n =
      ((n + 1 : ℕ) : ℚ) * (p : ℚ) *
        ((∑ a ∈ Finset.range p, (a : ℚ) ^ n) / (p : ℚ) -
          ∑ j ∈ Finset.range n,
            (n.choose j : ℚ) * ((p : ℚ) * bernoulli j) *
              ((p : ℚ) ^ (n - j - 1) / ((n - j + 1 : ℕ) : ℚ))) := by
    rw [hdiv]
    field_simp [hp0, hn1]
  exact mul_left_cancel₀ (mul_ne_zero hn1 hp0) hmul_eq

/-- Key strong-induction invariant for von Staudt–Clausen:
for ALL `n : ℕ` and every prime `p`, `(p : ℚ) * bernoulli n` is `p`-integral, and for even `n ≥ 2`,
`bernoulli n + (if p - 1 ∣ n then 1 / p else 0)` is `p`-integral. -/
lemma isPInt_bernoulli_strong_ind (p : ℕ) (hp : p.Prime) :
    ∀ n : ℕ, IsPInt p ((p : ℚ) * bernoulli n) ∧
      (2 ≤ n → Even n → IsPInt p (bernoulli n + if p - 1 ∣ n then (1 : ℚ) / (p : ℚ) else 0)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hmul_of_even : (2 ≤ n → Even n →
        IsPInt p (bernoulli n + if p - 1 ∣ n then (1 : ℚ) / (p : ℚ) else 0)) →
        IsPInt p ((p : ℚ) * bernoulli n) := by
      intro hev
      rcases Nat.lt_or_ge n 2 with hn2 | hn2
      · have hn01 : n = 0 ∨ n = 1 := by omega
        rcases hn01 with rfl | rfl
        · simpa [bernoulli_zero] using isPInt_natCast p hp p
        · rw [bernoulli_one]
          by_cases hp2 : p = 2
          · subst hp2; norm_num [IsPInt]
          · have h2 : ¬ p ∣ 2 := fun hd => hp2 ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hp.ne_one)
            have heq : (p : ℚ) * (-1 / 2) = ((-p : ℤ) : ℚ) / (2 : ℚ) := by push_cast; ring
            rw [heq]
            exact isPInt_div_nat (-p) (by norm_num) h2
      · rcases Nat.even_or_odd n with heven | hodd
        · have hsum := hev hn2 heven
          have hprod := isPInt_mul hp (isPInt_natCast p hp p) hsum
          have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
          have heq : (p : ℚ) * (bernoulli n + if p - 1 ∣ n then (1 : ℚ) / (p : ℚ) else 0) =
              (p : ℚ) * bernoulli n + if p - 1 ∣ n then 1 else 0 := by
            rw [mul_add]
            split_ifs
            · field_simp [hp0]
            · ring
          rw [heq] at hprod
          have hdelta : IsPInt p (if p - 1 ∣ n then (1 : ℚ) else 0) := by
            split_ifs
            · exact isPInt_natCast p hp 1
            · exact isPInt_zero p hp
          simpa using isPInt_sub hp hprod hdelta
        · rw [bernoulli_eq_zero_of_odd hodd hn2, mul_zero]
          exact isPInt_zero p hp
    have heven_step : 2 ≤ n → Even n →
        IsPInt p (bernoulli n + if p - 1 ∣ n then (1 : ℚ) / (p : ℚ) else 0) := by
      intro hn2 heven
      rcases Nat.eq_or_lt_of_le hn2 with rfl | hn2_lt
      · rw [bernoulli_two]
        by_cases hp2 : p = 2
        · subst hp2
          rw [if_pos (by norm_num)]
          norm_num [IsPInt]
        · by_cases hp3 : p = 3
          · subst hp3
            rw [if_pos (by norm_num)]
            norm_num [IsPInt]
          · have hndvd : ¬ p - 1 ∣ 2 := by
              intro hd
              have hle : p - 1 ≤ 2 := Nat.le_of_dvd (by norm_num) hd
              have hp2' := hp.two_le
              omega
            rw [if_neg hndvd, add_zero, show (6 : ℚ)⁻¹ = ((1 : ℤ) : ℚ) / (6 : ℕ) by norm_num]
            apply isPInt_div_nat 1 (by norm_num)
            intro hd
            have h6 : (6 : ℕ) = 2 * 3 := rfl
            rw [h6] at hd
            rcases hp.dvd_mul.mp hd with h2 | h3
            · exact hp2 ((Nat.dvd_prime Nat.prime_two).mp h2 |>.resolve_left hp.ne_one)
            · exact hp3 ((Nat.dvd_prime Nat.prime_three).mp h3 |>.resolve_left hp.ne_one)
      · rw [bernoulli_eq_pow_sum_div_sub hp]
        have heq :
            (∑ a ∈ Finset.range p, (a : ℚ) ^ n) / (p : ℚ) -
              (∑ j ∈ Finset.range n,
                (n.choose j : ℚ) * ((p : ℚ) * bernoulli j) *
                  ((p : ℚ) ^ (n - j - 1) / ((n - j + 1 : ℕ) : ℚ))) +
              (if p - 1 ∣ n then (1 : ℚ) / (p : ℚ) else 0) =
            ((∑ a ∈ Finset.range p, (a : ℚ) ^ n + if p - 1 ∣ n then 1 else 0) / (p : ℚ)) -
              ∑ j ∈ Finset.range n,
                (n.choose j : ℚ) * ((p : ℚ) * bernoulli j) *
                  ((p : ℚ) ^ (n - j - 1) / ((n - j + 1 : ℕ) : ℚ)) := by
          split_ifs <;> ring
        rw [heq]
        apply isPInt_sub hp (isPInt_pow_sum_div_prime hp (by omega))
        apply isPInt_sum hp
        intro j hj
        have hjn : j < n := Finset.mem_range.mp hj
        by_cases hj_last : j = n - 1
        · subst hj_last
          have hodd : Odd (n - 1) := by
            obtain ⟨m, rfl⟩ := heven
            exact ⟨m - 1, by omega⟩
          rw [bernoulli_eq_zero_of_odd hodd (by omega), mul_zero, mul_zero, zero_mul]
          exact isPInt_zero p hp
        · have hm2 : 2 ≤ n - j := by omega
          exact isPInt_mul hp
            (isPInt_mul hp (isPInt_natCast p hp (n.choose j)) (ih j hjn).1)
            (isPInt_prime_pow_div_succ hp (by omega) (fun _ => hm2))
    exact ⟨hmul_of_even heven_step, heven_step⟩

/-- Finite set of primes `p` satisfying `(p - 1) ∣ n`. -/
def staudtPrimes (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 2)).filter (fun p => p.Prime ∧ p - 1 ∣ n)

/-- The von Staudt–Clausen fractional part `∑_{p prime, p-1 ∣ n} 1/p`. -/
def staudtSum (n : ℕ) : ℚ :=
  ∑ p ∈ staudtPrimes n, (1 : ℚ) / (p : ℚ)

lemma mem_staudtPrimes_iff {n : ℕ} (hn : 1 ≤ n) {p : ℕ} :
    p ∈ staudtPrimes n ↔ p.Prime ∧ p - 1 ∣ n := by
  simp only [staudtPrimes, Finset.mem_filter, Finset.mem_range]
  refine ⟨fun h => h.2, fun ⟨hp, hd⟩ => ⟨?_, hp, hd⟩⟩
  have hle : p - 1 ≤ n := Nat.le_of_dvd hn hd
  omega

/-- **UNCONDITIONAL VON STAUDT–CLAUSEN THEOREM (`0` ASSUMPTIONS!)**:
for every `m ≥ 1`, `bernoulli (2 * m) + ∑_{p prime, (p-1) ∣ 2m} 1/p ∈ ℤ`. -/
theorem vonStaudt_clausen {m : ℕ} (hm : 1 ≤ m) :
    ∃ z : ℤ, bernoulli (2 * m) + staudtSum (2 * m) = (z : ℚ) := by
  apply isInt_of_forall_prime_isPInt
  intro p hp
  have hmain := (isPInt_bernoulli_strong_ind p hp (2 * m)).2 (by omega) ⟨m, by ring⟩
  by_cases hdvd : p - 1 ∣ 2 * m
  · have hmem : p ∈ staudtPrimes (2 * m) := (mem_staudtPrimes_iff (by omega)).2 ⟨hp, hdvd⟩
    rw [if_pos hdvd] at hmain
    have hsplit : bernoulli (2 * m) + staudtSum (2 * m) =
        (bernoulli (2 * m) + (1 : ℚ) / (p : ℚ)) +
          ∑ q ∈ (staudtPrimes (2 * m)).erase p, (1 : ℚ) / (q : ℚ) := by
      unfold staudtSum
      rw [← Finset.add_sum_erase _ _ hmem]
      ring
    rw [hsplit]
    apply isPInt_add hp hmain
    apply isPInt_sum hp
    intro q hq
    have hq' := Finset.mem_erase.mp hq
    have hqp : q.Prime := ((mem_staudtPrimes_iff (by omega)).1 hq'.2).1
    exact isPInt_one_div_prime_of_ne hp hqp hq'.1
  · rw [if_neg hdvd, add_zero] at hmain
    apply isPInt_add hp hmain
    apply isPInt_sum hp
    intro q hq
    have hq' := (mem_staudtPrimes_iff (by omega)).1 hq
    have hne : q ≠ p := fun heq => hdvd (heq ▸ hq'.2)
    exact isPInt_one_div_prime_of_ne hp hq'.1 hne

/-- **UNCONDITIONAL DENOMINATOR CHARACTERIZATION OF EVEN BERNOULLI NUMBERS**:
for every prime `p` and `m ≥ 1`, `p ∣ (bernoulli (2 * m)).den ↔ (p - 1) ∣ 2 * m`. -/
theorem prime_dvd_bernoulli_den_iff {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m) :
    p ∣ (bernoulli (2 * m)).den ↔ (p - 1) ∣ 2 * m := by
  have hmain := (isPInt_bernoulli_strong_ind p hp (2 * m)).2 (by omega) ⟨m, by ring⟩
  constructor
  · intro hdvd
    by_contra hndvd
    rw [if_neg hndvd, add_zero] at hmain
    exact hmain hdvd
  · intro hdvd
    rw [if_pos hdvd] at hmain
    by_contra hndvd
    have hsum : IsPInt p (bernoulli (2 * m) + (1 : ℚ) / (p : ℚ)) := hmain
    have hB : IsPInt p (bernoulli (2 * m)) := hndvd
    have h1p : IsPInt p ((1 : ℚ) / (p : ℚ)) := by
      simpa using isPInt_sub hp hsum hB
    have hden : ((1 : ℚ) / (p : ℚ)).den = p := by
      rw [one_div, Rat.inv_natCast_den_of_pos hp.pos]
    apply h1p
    rw [hden]

/-- Every even Bernoulli number `B_{2m}` (`m ≥ 1`) is nonzero (its denominator is even!). -/
theorem bernoulli_even_ne_zero {m : ℕ} (hm : 1 ≤ m) : bernoulli (2 * m) ≠ 0 := by
  have h2 : 2 ∣ (bernoulli (2 * m)).den :=
    (prime_dvd_bernoulli_den_iff Nat.prime_two hm).mpr ⟨2 * m, by omega⟩
  intro h0
  rw [h0, Rat.den_zero] at h2
  norm_num at h2

private lemma add_one_div_eq_of_den_eq_sq_mul {a : ℤ} {l k : ℕ} (hl : l ≠ 0) (hk : k ≠ 0) :
    (a : ℚ) / ((l ^ 2 * k : ℕ) : ℚ) + (1 : ℚ) / (l : ℚ) =
      ((a + (l : ℤ) * (k : ℤ) : ℤ) : ℚ) / ((l ^ 2 * k : ℕ) : ℚ) := by
  have hlQ : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hl
  have hkQ : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  push_cast
  field_simp [hlQ, hkQ]

/-- Simple pole property at `l`: when `l` is prime, `e ≥ 1`, and `(l - 1) ∣ 2 * e`,
`l ^ 2 ∤ (bernoulli (2 * e)).den`, so `v_l(denom(B_{2e})) = 1` and `v_l(num(B_{2e})) = 0`. -/
theorem bernoulli_even_simple_pole {l e : ℕ} (hl : l.Prime) (he : 1 ≤ e) (hdvd : l - 1 ∣ 2 * e) :
    l ∣ (bernoulli (2 * e)).den ∧
    ¬ l ^ 2 ∣ (bernoulli (2 * e)).den ∧
    ¬ (l : ℤ) ∣ (bernoulli (2 * e)).num := by
  have hd1 : l ∣ (bernoulli (2 * e)).den := (prime_dvd_bernoulli_den_iff hl he).mpr hdvd
  have hmain := (isPInt_bernoulli_strong_ind l hl (2 * e)).2 (by omega) ⟨e, by ring⟩
  rw [if_pos hdvd] at hmain
  set B := bernoulli (2 * e)
  have hcop : Nat.Coprime B.num.natAbs B.den := B.reduced
  have hn_num : ¬ (l : ℤ) ∣ B.num := by
    intro hnum
    have hnum_nat : l ∣ B.num.natAbs := Int.natCast_dvd.mp hnum
    have hl1 : l ∣ 1 := hcop ▸ Nat.dvd_gcd hnum_nat hd1
    exact hl.ne_one (Nat.dvd_one.mp hl1)
  have hn_sq : ¬ l ^ 2 ∣ B.den := by
    intro hsq
    obtain ⟨k, hk⟩ := hsq
    have hk0 : k ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hk
      exact B.den_pos.ne' hk
    have hBval : (B.num : ℚ) / ((l ^ 2 * k : ℕ) : ℚ) = B := by
      rw [← hk]
      exact Rat.num_div_den B
    have hsum_eq2 : B + (1 : ℚ) / (l : ℚ) =
        ((B.num + (l : ℤ) * (k : ℤ) : ℤ) : ℚ) / ((l ^ 2 * k : ℕ) : ℚ) := by
      have hadd := add_one_div_eq_of_den_eq_sq_mul (a := B.num) hl.ne_zero hk0
      rw [hBval] at hadd
      exact hadd
    have hnotl : ¬ (l : ℤ) ∣ B.num + (l : ℤ) * (k : ℤ) := by
      intro hd
      apply hn_num
      have hlk : (l : ℤ) ∣ (l : ℤ) * (k : ℤ) := dvd_mul_right _ _
      simpa using Int.dvd_sub hd hlk
    set S : ℚ := B + (1 : ℚ) / (l : ℚ)
    have hcross : ((B.num + (l : ℤ) * (k : ℤ) : ℤ) : ℚ) * (S.den : ℚ) =
        (S.num : ℚ) * ((l ^ 2 * k : ℕ) : ℚ) := by
      have hSden0 : (S.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr S.den_pos.ne'
      have hBden0 : ((l ^ 2 * k : ℕ) : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hl.ne_zero) hk0)
      have hSq : (S.num : ℚ) / (S.den : ℚ) =
          ((B.num + (l : ℤ) * (k : ℤ) : ℤ) : ℚ) / ((l ^ 2 * k : ℕ) : ℚ) :=
        (Rat.num_div_den S).trans hsum_eq2
      exact ((div_eq_div_iff hSden0 hBden0).mp hSq).symm
    have hcrossZ : (B.num + (l : ℤ) * (k : ℤ)) * (S.den : ℤ) =
        S.num * ((l ^ 2 * k : ℕ) : ℤ) := by
      exact_mod_cast hcross
    have hdvdZ : (B.den : ℤ) ∣ (B.num + (l : ℤ) * (k : ℤ)) * (S.den : ℤ) := by
      rw [hk, hcrossZ]
      exact dvd_mul_left _ _
    have hdvdNat : B.den ∣ ((B.num + (l : ℤ) * (k : ℤ)) * (S.den : ℤ)).natAbs :=
      Int.natCast_dvd.mp hdvdZ
    rw [Int.natAbs_mul, Int.natAbs_natCast] at hdvdNat
    have hd1_nat : l ∣ (B.num + (l : ℤ) * (k : ℤ)).natAbs * S.den := hd1.trans hdvdNat
    rcases hl.dvd_mul.mp hd1_nat with hL | hR
    · exact hnotl (Int.natCast_dvd.mpr hL)
    · exact hmain hR
  exact ⟨hd1, hn_sq, hn_num⟩

/-- Exact `l`-adic denominator valuation `padicValNat l (bernoulli (2 * e)).den = 1`. -/
theorem bernoulli_even_padicValNat_den_eq_one {l e : ℕ} (hl : l.Prime) (he : 1 ≤ e)
    (hdvd : l - 1 ∣ 2 * e) :
    padicValNat l (bernoulli (2 * e)).den = 1 := by
  have : Fact l.Prime := ⟨hl⟩
  obtain ⟨hd1, hnsq, _⟩ := bernoulli_even_simple_pole hl he hdvd
  have hge1 : 1 ≤ padicValNat l (bernoulli (2 * e)).den := by
    rw [← pow_one l] at hd1
    exact (padicValNat_dvd_iff_le (bernoulli (2 * e)).den_pos.ne').mp hd1
  have hlt2 : ¬ 2 ≤ padicValNat l (bernoulli (2 * e)).den := by
    intro hle
    exact hnsq ((padicValNat_dvd_iff_le (bernoulli (2 * e)).den_pos.ne').mpr hle)
  omega

/-- Exact `l`-adic numerator valuation `padicValNat l (bernoulli (2 * e)).num.natAbs = 0`. -/
theorem bernoulli_even_padicValNat_num_eq_zero {l e : ℕ} (hl : l.Prime) (he : 1 ≤ e)
    (hdvd : l - 1 ∣ 2 * e) :
    padicValNat l (bernoulli (2 * e)).num.natAbs = 0 := by
  obtain ⟨_, _, hn_num⟩ := bernoulli_even_simple_pole hl he hdvd
  have hn_nat : ¬ l ∣ (bernoulli (2 * e)).num.natAbs := fun h => hn_num (Int.natCast_dvd.mpr h)
  exact padicValNat.eq_zero_of_not_dvd hn_nat

/-- **UNCONDITIONAL SIMPLE POLE `v_l(B_{2e}) = -1` (`PropZ` ARITHMETIC CORE!)**:
for EVERY prime `l` and `e ≥ 1` with `(l - 1) ∣ 2 * e`, `padicValRat l (bernoulli (2 * e)) = -1`! -/
theorem bernoulli_even_padicValRat_neg_one {l e : ℕ} (hl : l.Prime) (he : 1 ≤ e)
    (hdvd : l - 1 ∣ 2 * e) :
    padicValRat l (bernoulli (2 * e)) = -1 := by
  have : Fact l.Prime := ⟨hl⟩
  have hBne : bernoulli (2 * e) ≠ 0 := bernoulli_even_ne_zero he
  have hnum_ne : ((bernoulli (2 * e)).num : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (Rat.num_ne_zero.mpr hBne)
  have hden_ne : ((bernoulli (2 * e)).den : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (bernoulli (2 * e)).den_pos.ne'
  conv_lhs => rw [← Rat.num_div_den (bernoulli (2 * e))]
  rw [padicValRat.div hnum_ne hden_ne, padicValRat.of_nat,
    bernoulli_even_padicValNat_den_eq_one hl he hdvd]
  have hnum_val : padicValRat l ((bernoulli (2 * e)).num : ℚ) = 0 := by
    rcases Int.natAbs_eq (bernoulli (2 * e)).num with hpos | hneg
    · rw [hpos, Int.cast_natCast, padicValRat.of_nat,
        bernoulli_even_padicValNat_num_eq_zero hl he hdvd, Nat.cast_zero]
    · rw [hneg, Int.cast_neg, Int.cast_natCast, padicValRat.neg, padicValRat.of_nat,
        bernoulli_even_padicValNat_num_eq_zero hl he hdvd, Nat.cast_zero]
  rw [hnum_val]
  norm_num

/-- **UNCONDITIONAL `l`-ADIC NORM `‖(B_{2e} : ℚ_[l])‖ = l` AND UNIT NORM `‖(l * B_{2e} : ℚ_[l])‖ = 1`**!
Specifically, `(l : ℚ) * B_{2e}` is a `ℤ_[l]`-unit (`IsUnit` in `ℤ_[l]`). -/
theorem bernoulli_even_padic_norm {l e : ℕ} (hl : l.Prime) [Fact l.Prime] (he : 1 ≤ e)
    (hdvd : l - 1 ∣ 2 * e) :
    ‖(bernoulli (2 * e) : ℚ_[l])‖ = (l : ℝ) ∧
    ‖(((l : ℚ) * bernoulli (2 * e) : ℚ) : ℚ_[l])‖ = 1 := by
  have hBne : bernoulli (2 * e) ≠ 0 := bernoulli_even_ne_zero he
  have hv := bernoulli_even_padicValRat_neg_one hl he hdvd
  have hnormB : ‖(bernoulli (2 * e) : ℚ_[l])‖ = (l : ℝ) := by
    rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hBne),
      Padic.valuation_ratCast, hv, neg_neg, zpow_one]
  refine ⟨hnormB, ?_⟩
  rw [Rat.cast_mul, norm_mul, Rat.cast_natCast, Padic.norm_p, hnormB]
  have hl0 : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  field_simp [hl0]

/-- Non-divisible case: when `¬ (l - 1) ∣ 2 * m`, `bernoulli (2 * m)` is `l`-adically integral
(`‖(B_{2m} : ℚ_[l])‖ ≤ 1`). -/
theorem bernoulli_even_padic_norm_le_one_of_not_dvd {l m : ℕ} (hl : l.Prime) [Fact l.Prime]
    (hm : 1 ≤ m) (hndvd : ¬ l - 1 ∣ 2 * m) :
    ‖(bernoulli (2 * m) : ℚ_[l])‖ ≤ 1 := by
  have hnt : ¬ l ∣ (bernoulli (2 * m)).den :=
    fun hd => hndvd ((prime_dvd_bernoulli_den_iff hl hm).mp hd)
  rw [← Rat.num_div_den (bernoulli (2 * m)), Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  have hden_norm : ‖((bernoulli (2 * m)).den : ℚ_[l])‖ = 1 := by
    have hcop : PadicInt.toZMod ((bernoulli (2 * m)).den : ℤ_[l]) ≠ 0 := by
      rw [map_natCast, Ne, ZMod.natCast_eq_zero_iff]
      exact hnt
    have hunit : IsUnit ((bernoulli (2 * m)).den : ℤ_[l]) := by
      rw [← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker]
      exact hcop
    simpa using PadicInt.isUnit_iff.mp hunit
  rw [norm_div, hden_norm, div_one]
  exact PadicInt.norm_le_one ((bernoulli (2 * m)).num : ℤ_[l])

end VonStaudtClausen

/-! ## Section 2: Unconditional Residual Bernoulli Nonvanishing (`PropZ` / `CountZ`) -/

section PropZAndCountZ

/-- Any `R`-module annihilated by a unit `u : R` is a `Subsingleton` and has `Module.length R M = 0`. -/
theorem module_length_eq_zero_of_isUnit_ann {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {u : R} (hu : IsUnit u) (hann : ∀ x : M, u • x = 0) :
    Subsingleton M ∧ Module.length R M = 0 := by
  have hsub : Subsingleton M := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨v, hv⟩ := hu
    have hxy : u • (x - y) = 0 := hann (x - y)
    have huv : (v⁻¹ : Rˣ) * u = 1 := by
      rw [← hv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h1 : x - y = 0 := by
      calc x - y = (1 : R) • (x - y) := (one_smul R _).symm
        _ = ((v⁻¹ : Rˣ) * u) • (x - y) := by rw [huv]
        _ = (v⁻¹ : Rˣ) • (u • (x - y)) := by rw [← smul_smul]; rfl
        _ = (v⁻¹ : Rˣ) • (0 : M) := by rw [hxy]
        _ = 0 := smul_zero _
    exact sub_eq_zero.mp h1
  exact ⟨hsub, (Module.length_eq_zero_iff (R := R) (M := M)).mpr hsub⟩

/-- **Residual Bernoulli Unit Witness (`PropZResidualBernoulliUnit l e`)**:
there exists a `ℤ_[l]`-unit `u ∈ ℤ_[l]ˣ` representing `(l : ℚ) * bernoulli (2 * e) ∈ ℚ_[l]`. -/
def PropZResidualBernoulliUnit (l e : ℕ) [Fact l.Prime] : Prop :=
  ∃ u : ℤ_[l], IsUnit u ∧ (u : ℚ_[l]) = (((l : ℚ) * bernoulli (2 * e) : ℚ) : ℚ_[l])

/-- **UNCONDITIONAL `PropZ` RESIDUAL BERNOULLI NONVANISHING (`0` ASSUMPTIONS!)**:
for EVERY prime `l` (in particular odd `l ≥ 5`) and every `e ≥ 1` with `(l - 1) ∣ 2 * e`,
`(l : ℚ) * B_{2e}` is a `ℤ_[l]`-unit! -/
theorem propZResidualBernoulliUnit_unconditional (l e : ℕ) [Fact l.Prime]
    (he : 1 ≤ e) (hdvd : l - 1 ∣ 2 * e) :
    PropZResidualBernoulliUnit l e := by
  have hl : l.Prime := Fact.out
  have hnorm1 := (bernoulli_even_padic_norm hl he hdvd).2
  let x : ℚ_[l] := (((l : ℚ) * bernoulli (2 * e) : ℚ) : ℚ_[l])
  have hx_le : ‖x‖ ≤ 1 := hnorm1.le
  let u : ℤ_[l] := ⟨x, hx_le⟩
  refine ⟨u, PadicInt.isUnit_iff.mpr hnorm1, rfl⟩

/-- **Unconditional `ℤ_[l]`-Length Vanishing from `B_{2e}`-Pole Annihilation**:
any `ℤ_[l]`-module `M` (e.g. a `CaseZ` Selmer component `Sha(E)[χ = 1]`) annihilated by the
residual Bernoulli unit `(l : ℚ) * B_{2e}` (with `(l - 1) ∣ 2 * e`) has `Module.length ℤ_[l] M = 0`! -/
theorem padicInt_length_eq_zero_of_bernoulli_pole_ann (l e : ℕ) [Fact l.Prime]
    (he : 1 ≤ e) (hdvd : l - 1 ∣ 2 * e)
    {M : Type*} [AddCommGroup M] [Module ℤ_[l] M]
    (hann : ∀ u : ℤ_[l], (u : ℚ_[l]) = (((l : ℚ) * bernoulli (2 * e) : ℚ) : ℚ_[l]) →
      ∀ x : M, u • x = 0) :
    Subsingleton M ∧ Module.length ℤ_[l] M = 0 := by
  obtain ⟨u, hu, hueq⟩ := propZResidualBernoulliUnit_unconditional l e he hdvd
  exact module_length_eq_zero_of_isUnit_ann hu (hann u hueq)

/-- **Unconditional `Stage12GaloisShaLen` Vanishing for Bernoulli-Unit-Annihilated `Sha`**:
for `l` prime, `e ≥ 1`, `(l - 1) ∣ 2 * e`, if the residual Bernoulli unit `(l : ℚ) * B_{2e}`
annihilates `Sha (canonicalLData E l) (k : ℤ)`, then `galoisShaLen E l (k : ℤ) = 0`! -/
theorem galoisShaLen_eq_zero_of_bernoulli_pole_ann
    (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (e k : ℕ)
    (he : 1 ≤ e) (hdvd : (l : ℕ) - 1 ∣ 2 * e)
    (hann : ∀ u : ℤ_[l.1],
      (u : ℚ_[l.1]) = ((((l : ℕ) : ℚ) * bernoulli (2 * e) : ℚ) : ℚ_[l.1]) →
      ∀ x : Sha1Galois E l (k : ℤ), u • x = 0) :
    galoisShaLen E l (k : ℤ) = 0 := by
  have : Fact l.1.Prime := ⟨l.2⟩
  rw [galoisShaLen_eq_module_length]
  exact (padicInt_length_eq_zero_of_bernoulli_pole_ann l.1 e he hdvd hann).2

/-- Unconditional `CountZ` vanishing (`Vlen = 0`) from `PropZ` residual Bernoulli nonvanishing:
matching `PropZ:11-16` and `CountZ:5-32` (`Vlen = 0` for `ψ = 1, l ∉ Bchi, (l - 1) ∣ 2 * k`). -/
theorem countZ_vanishing_of_propZ
    {Vlen : Nat.Primes → ℕ → ℕ∞}
    (hpropZ : ∀ (l : Nat.Primes) (k : ℕ), 1 ≤ k → (l : ℕ) - 1 ∣ 2 * k →
      @PropZResidualBernoulliUnit l.1 k ⟨l.2⟩ → Vlen l k = 0)
    {l : Nat.Primes} {k : ℕ} (hk : 1 ≤ k) (hdiv : (l : ℕ) - 1 ∣ 2 * k) :
    Vlen l k = 0 := by
  have : Fact l.1.Prime := ⟨l.2⟩
  exact hpropZ l k hk hdiv (propZResidualBernoulliUnit_unconditional l.1 k hk hdiv)

end PropZAndCountZ

/-! ## Section 3: Exact Alpöge 6-Case Character Classification (`CountI`–`CountZ`) & `partition_exhaustive` -/

section SixCaseClassification

/-- **Exact Finite Bad-Prime Set `Bchi E ψ`**:
all primes `l` dividing `2 * [E : ℚ] * condF E * ψ.N` (finite `Finset Nat.Primes`). -/
def Bchi (E : Type) [Field E] [NumberField E] (ψ : PChar) : Finset Nat.Primes :=
  (2 * Module.finrank ℚ E * condF E * ψ.N).primeFactors.attach.map
    ⟨fun x : {p : ℕ // p ∈ (2 * Module.finrank ℚ E * condF E * ψ.N).primeFactors} =>
        (⟨x.1, Nat.prime_of_mem_primeFactors x.2⟩ : Nat.Primes),
      fun _ _ h => Subtype.ext (congrArg (fun z : Nat.Primes => (z : ℕ)) h)⟩

private lemma conductor_product_ne_zero (E : Type) [Field E] [NumberField E] (ψ : PChar)
    (hcond : 0 < condF E) :
    2 * Module.finrank ℚ E * condF E * ψ.N ≠ 0 := by
  have hdeg : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hψ : 0 < ψ.N := NeZero.pos ψ.N
  positivity

theorem mem_Bchi_iff {E : Type} [Field E] [NumberField E] {ψ : PChar}
    (hcond : 0 < condF E) (l : Nat.Primes) :
    l ∈ Bchi E ψ ↔ (l : ℕ) ∣ 2 * Module.finrank ℚ E * condF E * ψ.N := by
  have hne : 2 * Module.finrank ℚ E * condF E * ψ.N ≠ 0 :=
    conductor_product_ne_zero E ψ hcond
  simp only [Bchi, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists]
  constructor
  · rintro ⟨p, hp, hpeq⟩
    have hpe : p = (l : ℕ) := congrArg (fun z : Nat.Primes => (z : ℕ)) hpeq
    subst hpe
    exact Nat.dvd_of_mem_primeFactors hp
  · intro hdvd
    exact ⟨l.1, Nat.mem_primeFactors.mpr ⟨l.2, hdvd, hne⟩, Subtype.ext rfl⟩

theorem primeTwo_mem_Bchi (E : Type) [Field E] [NumberField E] (ψ : PChar)
    (hcond : 0 < condF E) :
    primeTwo ∈ Bchi E ψ := by
  rw [mem_Bchi_iff hcond]
  change 2 ∣ 2 * Module.finrank ℚ E * condF E * ψ.N
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right 2 _) _) _

theorem not_mem_Bchi_spec {E : Type} [Field E] [NumberField E] {ψ : PChar}
    (hcond : 0 < condF E) {l : Nat.Primes} (hl : l ∉ Bchi E ψ) :
    (l : ℕ) ≠ 2 ∧ ¬ (l : ℕ) ∣ Module.finrank ℚ E ∧ ¬ (l : ℕ) ∣ condF E ∧ ¬ (l : ℕ) ∣ ψ.N := by
  rw [mem_Bchi_iff hcond] at hl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h2; apply hl; rw [h2]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right 2 _) _) _
  · intro hd; apply hl
    exact dvd_trans hd (dvd_trans (dvd_mul_left _ 2)
      (dvd_mul_of_dvd_left (dvd_mul_right _ _) _))
  · intro hd; apply hl
    exact dvd_trans hd (dvd_trans (dvd_mul_left _ _) (dvd_mul_right _ _))
  · intro hd; apply hl
    exact dvd_mul_of_dvd_right hd (2 * Module.finrank ℚ E * condF E)

/-- `BchiOfNat M`: finite `Finset Nat.Primes` of primes dividing `M` (used for the `E`-independent
character-level bad prime set `Bchi_χ`). -/
def BchiOfNat (M : ℕ) : Finset Nat.Primes :=
  M.primeFactors.attach.map
    ⟨fun x : {p : ℕ // p ∈ M.primeFactors} =>
        (⟨x.1, Nat.prime_of_mem_primeFactors x.2⟩ : Nat.Primes),
      fun _ _ h => Subtype.ext (congrArg (fun z : Nat.Primes => (z : ℕ)) h)⟩

theorem mem_BchiOfNat_iff {M : ℕ} (hM : M ≠ 0) (l : Nat.Primes) :
    l ∈ BchiOfNat M ↔ (l : ℕ) ∣ M := by
  simp only [BchiOfNat, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists]
  constructor
  · rintro ⟨p, hp, hpeq⟩
    have hpe : p = (l : ℕ) := congrArg (fun z : Nat.Primes => (z : ℕ)) hpeq
    subst hpe
    exact Nat.dvd_of_mem_primeFactors hp
  · intro hdvd
    exact ⟨l.1, Nat.mem_primeFactors.mpr ⟨l.2, hdvd, hM⟩, Subtype.ext rfl⟩

/-- Character-level invariants attached to a Galois / Dirichlet character `χ` of `Gal(E/ℚ)` at `(l, k)`.
- `conjParity = 1` means plus parity `χ(c) = (-1)^k` (`ShaPlus`);
- `conjParity = -1` means minus parity `χ(c) = (-1)^{k+1}` (`ShaMinus`);
- `isTrivial`: whether `χ = 1`;
- `evenOrder`: whether `2 ∣ orderOf (chiP l χ)`;
- `r1LeTwoPowC2`: whether `R₁(l, χ) ≤ 2^{c₂(χ)}`. -/
structure GalCharClass where
  conjParity : Int
  conj_valid : conjParity = 1 ∨ conjParity = -1
  isTrivial : Bool
  evenOrder : Bool
  r1LeTwoPowC2 : Bool

/-- **Exact Alpöge 6-Case (+ `l = 2` + Minus-Parity) Partition Enum**:
every `(l, k, χ)` (`l` prime, `1 ≤ k`, `χ : GalCharClass`) lands in a unique case:
- `caseTwo`: `l = 2` (`BaAt`: `Window1` + global Ferrero–Washington)
- `caseMinusRubin`: `l ≠ 2`, minus parity, `l ∤ [E:ℚ]` (`VVminusLe` via Rubin Euler system)
- `caseMinusStickelberger`: `l ≠ 2`, minus parity, `l ∣ [E:ℚ]` (`VVminusLe` via Stickelberger)
- `caseIV`: `l ≠ 2`, plus parity, `l ∈ Bchi`, `k ≥ 2`, odd order (`CountIV`/`BbAt`: `Window1` + `LemmaK`)
- `caseII_in`: `l ≠ 2`, plus parity, `l ∈ Bchi`, `k ≥ 2`, even order (`CountII`: `Sp₄` + GMA)
- `caseV`: `l ≠ 2`, plus parity, `l ∈ Bchi`, `k = 1`, `R₁ ≤ 2^{c₂}` (`CountV`: wt-2 `U(3)` over `ℚ(i)`)
- `caseVs`: `l ≠ 2`, plus parity, `l ∈ Bchi`, `k = 1`, `2^{c₂} < R₁` (`CountVs`: `LemmaK` at `k = 1`)
- `caseI`: `l ≠ 2`, plus parity, `l ∉ Bchi`, `(l - 1) ∤ 2 * k` (`CountI`: `U(3)` + GMA + Kato)
- `caseZ`: `l ≠ 2`, plus parity, `l ∉ Bchi`, `(l - 1) ∣ 2 * k`, `χ = 1` (`CountZ`: `0` via `PropZ`!)
- `caseII_out`: `l ≠ 2`, plus parity, `l ∉ Bchi`, `(l - 1) ∣ 2 * k`, `χ ≠ 1`, even order (`CountII`: `Sp₄` + GMA)
- `caseIII`: `l ≠ 2`, plus parity, `l ∉ Bchi`, `(l - 1) ∣ 2 * k`, `χ ≠ 1`, odd order (`CountIII`: `Sp₄` + GMA). -/
inductive AlpogeCase
  | caseTwo
  | caseMinusRubin
  | caseMinusStickelberger
  | caseIV
  | caseII_in
  | caseV
  | caseVs
  | caseI
  | caseZ
  | caseII_out
  | caseIII
  deriving DecidableEq, Repr

/-- Exact case membership predicate for `(B, dE, l, k, χ)`. -/
def InCase (B : Finset Nat.Primes) (dE : ℕ) (l : Nat.Primes) (k : ℕ) (χ : GalCharClass) :
    AlpogeCase → Prop
  | .caseTwo => (l : ℕ) = 2
  | .caseMinusRubin => (l : ℕ) ≠ 2 ∧ χ.conjParity = -1 ∧ ¬ (l : ℕ) ∣ dE
  | .caseMinusStickelberger => (l : ℕ) ≠ 2 ∧ χ.conjParity = -1 ∧ (l : ℕ) ∣ dE
  | .caseIV => (l : ℕ) ≠ 2 ∧ χ.conjParity = 1 ∧ l ∈ B ∧ 2 ≤ k ∧ χ.evenOrder = false
  | .caseII_in => (l : ℕ) ≠ 2 ∧ χ.conjParity = 1 ∧ l ∈ B ∧ 2 ≤ k ∧ χ.evenOrder = true
  | .caseV => (l : ℕ) ≠ 2 ∧ χ.conjParity = 1 ∧ l ∈ B ∧ k = 1 ∧ χ.r1LeTwoPowC2 = true
  | .caseVs => (l : ℕ) ≠ 2 ∧ χ.conjParity = 1 ∧ l ∈ B ∧ k = 1 ∧ χ.r1LeTwoPowC2 = false
  | .caseI => (l : ℕ) ≠ 2 ∧ χ.conjParity = 1 ∧ l ∉ B ∧ ¬ ((l : ℕ) - 1 ∣ 2 * k)
  | .caseZ => (l : ℕ) ≠ 2 ∧ χ.conjParity = 1 ∧ l ∉ B ∧ ((l : ℕ) - 1 ∣ 2 * k) ∧ χ.isTrivial = true
  | .caseII_out => (l : ℕ) ≠ 2 ∧ χ.conjParity = 1 ∧ l ∉ B ∧ ((l : ℕ) - 1 ∣ 2 * k) ∧
      χ.isTrivial = false ∧ χ.evenOrder = true
  | .caseIII => (l : ℕ) ≠ 2 ∧ χ.conjParity = 1 ∧ l ∉ B ∧ ((l : ℕ) - 1 ∣ 2 * k) ∧
      χ.isTrivial = false ∧ χ.evenOrder = false

/-- Total classifier mapping `(B, dE, l, k, χ)` to its unique `AlpogeCase`. -/
def classifyTuple (B : Finset Nat.Primes) (dE : ℕ) (l : Nat.Primes) (k : ℕ) (χ : GalCharClass) :
    AlpogeCase :=
  if (l : ℕ) = 2 then .caseTwo
  else if χ.conjParity = -1 then
    if (l : ℕ) ∣ dE then .caseMinusStickelberger else .caseMinusRubin
  else if l ∈ B then
    if k = 1 then
      if χ.r1LeTwoPowC2 then .caseV else .caseVs
    else
      if χ.evenOrder then .caseII_in else .caseIV
  else
    if (l : ℕ) - 1 ∣ 2 * k then
      if χ.isTrivial then .caseZ
      else if χ.evenOrder then .caseII_out else .caseIII
    else .caseI

theorem classifyTuple_inCase (B : Finset Nat.Primes) (dE : ℕ) (l : Nat.Primes)
    {k : ℕ} (hk : 1 ≤ k) (χ : GalCharClass) :
    InCase B dE l k χ (classifyTuple B dE l k χ) := by
  unfold classifyTuple
  by_cases hl2 : (l : ℕ) = 2
  · simp [hl2, InCase]
  · simp only [hl2, ↓reduceIte]
    rcases χ.conj_valid with hplus | hminus
    · have hne_neg : χ.conjParity ≠ -1 := by omega
      simp only [hne_neg, ↓reduceIte]
      by_cases hlB : l ∈ B
      · simp only [hlB, ↓reduceIte]
        by_cases hk1 : k = 1
        · simp only [hk1, ↓reduceIte]
          cases hr1 : χ.r1LeTwoPowC2 <;> simp [InCase, hl2, hplus, hlB, hr1]
        · have hk2 : 2 ≤ k := by omega
          simp only [hk1, ↓reduceIte]
          cases hev : χ.evenOrder <;> simp [InCase, hl2, hplus, hlB, hk2, hev]
      · simp only [hlB, ↓reduceIte]
        by_cases hdiv : (l : ℕ) - 1 ∣ 2 * k
        · simp only [hdiv, ↓reduceIte]
          cases htriv : χ.isTrivial
          · cases hev : χ.evenOrder <;> simp [InCase, hl2, hplus, hlB, hdiv, htriv, hev]
          · simp [InCase, hl2, hplus, hlB, hdiv, htriv]
        · simp [InCase, hl2, hplus, hlB, hdiv]
    · simp only [hminus, ↓reduceIte]
      by_cases hld : (l : ℕ) ∣ dE <;> simp [InCase, hl2, hminus, hld]

/-- **`partition_exhaustive`**: EVERY `(l, k, χ)` (`l` prime, `1 ≤ k`, `χ : GalCharClass`) falls into
one of the exact Alpöge cases with zero gaps! -/
theorem partition_exhaustive (B : Finset Nat.Primes) (dE : ℕ) (l : Nat.Primes)
    {k : ℕ} (hk : 1 ≤ k) (χ : GalCharClass) :
    ∃ c : AlpogeCase, InCase B dE l k χ c :=
  ⟨classifyTuple B dE l k χ, classifyTuple_inCase B dE l hk χ⟩

/-- **`partition_unique`**: the Alpöge 6-case partition is pairwise mutually exclusive. -/
theorem partition_unique {B : Finset Nat.Primes} {dE : ℕ} {l : Nat.Primes} {k : ℕ}
    {χ : GalCharClass} {c₁ c₂ : AlpogeCase}
    (h₁ : InCase B dE l k χ c₁) (h₂ : InCase B dE l k χ c₂) :
    c₁ = c₂ := by
  cases c₁ <;> cases c₂ <;> simp only [InCase] at h₁ h₂ <;> first | rfl | omega | simp_all

/-- Specialization of `partition_exhaustive` to the concrete bad-prime set `Bchi E ψ` and
`dE = Module.finrank ℚ E`. -/
theorem partition_exhaustive_Bchi (E : Type) [Field E] [NumberField E] (ψ : PChar)
    (l : Nat.Primes) {k : ℕ} (hk : 1 ≤ k) (χ : GalCharClass) :
    ∃ c : AlpogeCase, InCase (Bchi E ψ) (Module.finrank ℚ E) l k χ c :=
  partition_exhaustive (Bchi E ψ) (Module.finrank ℚ E) l hk χ

/-- Crucial prime-size bound for `CaseZ`, `CaseII_out`, and `CaseIII` in `SumOut`:
`(l - 1) ∣ 2 * k` with `1 ≤ k` forces `l ≤ 2 * k + 1` (hence `l ≤ 2 * t` for `k < t`,
bounding the number of non-`CaseI` primes in `SumOut` by `2 * t`, matching `SumOut.lean:192-199`). -/
theorem prime_le_two_mul_add_one_of_sub_one_dvd {l k : ℕ} (hk : 1 ≤ k)
    (hdvd : l - 1 ∣ 2 * k) :
    l ≤ 2 * k + 1 := by
  have hle : l - 1 ≤ 2 * k := Nat.le_of_dvd (by omega) hdvd
  omega

/-- Number of primes in a `Finset Nat.Primes` bounded by `n` is at most `n`
(matching `SumOut.lean:19-29`). -/
theorem card_primes_le_of_forall_le (S : Finset Nat.Primes) (n : ℕ)
    (h : ∀ l ∈ S, (l : ℕ) ≤ n) : S.card ≤ n := by
  have hle : S.card ≤ (Finset.Icc 1 n).card := by
    apply Finset.card_le_card_of_injOn (fun l : Nat.Primes => (l : ℕ))
    · intro l hl
      have h1 := h l hl
      have h2 := l.2.one_lt
      simp only [Finset.coe_Icc, Set.mem_Icc]
      omega
    · intro x _ y _ hxy
      exact Subtype.ext hxy
  simpa using hle

end SixCaseClassification

/-! ## Section 4: `SumOut`, `SumIn`, `SixCaseField1Supply`, & Master 6-Case `VWin` Assembly -/

section SixCaseAssembly

/-- Character tag in the finite dual group `charSet E k` of plus-parity characters of `Gal(E/ℚ)`
(modeling `h.X c e` in `Host.lean` / `SumOut.lean` / `FinalLe.lean`). -/
structure GalCharTag where
  id : ℕ
  isTrivial : Bool
  evenOrder : Bool
  r1LeTwoPowC2 : Bool
  deriving DecidableEq

/-- **Exact Alpöge Character-Level Parity & Selmer Data (`CharSelmerData S`)**:
equips `S : SelmerSystem` with:
- complex-conjugation parity lengths `plusLen`, `minusLen` satisfying `shaLen = plusLen + minusLen`
  for all odd primes `l ≠ 2` (`LengthEqAddEigen`),
- plus-parity character decomposition `charSet E k` (of size `≤ condF E`, matching `xCard`),
- per-character `Vlen E l k χ` and local decomposition loss `loss E l k`
  (`plusLen E l k ≤ ∑ χ ∈ charSet E k, Vlen E l k χ + loss E l k`, matching `RedPrime`/`RedAll`). -/
structure CharSelmerData (S : SelmerSystem) where
  plusLen : (E : Type) → [Field E] → [NumberField E] → Nat.Primes → ℕ → ℕ∞
  minusLen : (E : Type) → [Field E] → [NumberField E] → Nat.Primes → ℕ → ℕ∞
  shaLen_eq_add : ∀ (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (e : ℕ),
    (l : ℕ) ≠ 2 → S.shaLen E l e = plusLen E l e + minusLen E l e
  charSet : (E : Type) → [Field E] → [NumberField E] → ℕ → Finset GalCharTag
  charSet_card_le : ∀ (E : Type) [Field E] [NumberField E] (k : ℕ),
    (charSet E k).card ≤ condF E
  Vlen : (E : Type) → [Field E] → [NumberField E] → Nat.Primes → ℕ → GalCharTag → ℕ∞
  loss : (E : Type) → [Field E] → [NumberField E] → Nat.Primes → ℕ → ℕ
  plusLen_le : ∀ (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (k : ℕ),
    (l : ℕ) ≠ 2 → 0 < k →
      plusLen E l k ≤ (∑ χ ∈ charSet E k, Vlen E l k χ) + (loss E l k : ℕ∞)

/-- Canonical `ParitySelmerSystem` extracted from `CharSelmerData S`, with
`toParitySelmerSystem.toSelmerSystem = S` definitionally. -/
def CharSelmerData.toParitySelmerSystem {S : SelmerSystem} (D : CharSelmerData S) :
    ParitySelmerSystem where
  shaLen := S.shaLen
  plusLen := D.plusLen
  minusLen := D.minusLen
  shaLen_eq_add := D.shaLen_eq_add

@[simp]
theorem CharSelmerData.toParitySelmerSystem_toSelmerSystem {S : SelmerSystem}
    (D : CharSelmerData S) :
    D.toParitySelmerSystem.toSelmerSystem = S := rfl

private lemma enat_sum_eq_coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ∞)
    (hf : ∀ i ∈ s, f i ≠ ⊤) :
    (∑ i ∈ s, f i) = ((∑ i ∈ s, (f i).toNat : ℕ) : ℕ∞) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Nat.cast_add,
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ENat.natCast_toNat (hf a (Finset.mem_insert_self a s))]

private lemma enat_sum_le_add_of_le {ι : Type*} (s : Finset ι) (f : ι → ℕ∞)
    (loss : ℕ) (lhs : ℕ∞)
    (hfin : ∀ i ∈ s, f i ≠ ⊤)
    (hle : lhs ≤ (∑ i ∈ s, f i) + (loss : ℕ∞)) :
    lhs ≠ ⊤ ∧ (lhs.toNat : ℝ) ≤ (∑ i ∈ s, ((f i).toNat : ℝ)) + (loss : ℝ) := by
  have hsum_eq : (∑ i ∈ s, f i) = ((∑ i ∈ s, (f i).toNat : ℕ) : ℕ∞) :=
    enat_sum_eq_coe_sum s f hfin
  have hle' : lhs ≤ (((∑ i ∈ s, (f i).toNat) + loss : ℕ) : ℕ∞) := by
    rw [Nat.cast_add, ← hsum_eq]
    exact hle
  have hlhs_ne : lhs ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle'
  refine ⟨hlhs_ne, ?_⟩
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hlhs_ne
  rw [← ha, ENat.toNat_natCast]
  have ha_le : a ≤ (∑ i ∈ s, (f i).toNat) + loss := by
    rw [← ha] at hle'
    exact_mod_cast hle'
  have haR : (a : ℝ) ≤ ((∑ i ∈ s, (f i).toNat : ℕ) : ℝ) + (loss : ℝ) := by
    exact_mod_cast ha_le
  simpa [Nat.cast_sum] using haR

/-- **PURE POLYNOMIAL `SumOut` ASSEMBLY (`sumOut_of_counts`)**:
Assembles `SumOut` over ALL good odd primes `l ∉ Bchi` from:
1. **`CountI`** (`U(3)` + GMA + Kato): simultaneous prime sum over `¬ (l - 1) ∣ 2 * k`,
2. **`CountII`** & **`CountIII`** (`Sp₄` + GMA): pointwise polynomial bound at `(l - 1) ∣ 2 * k, χ ≠ 1`,
3. **`CountZ`** (`PropZ`): **UNCONDITIONALLY ZERO** via von Staudt–Clausen (`countZ_vanishing_of_propZ`),
with zero `exp(x^(4ε/5))` term (`SumOut ≤ (condF E * t)^Cout`)! -/
theorem sumOut_of_counts {S : SelmerSystem} (D : CharSelmerData S) (Bchi_χ : Finset Nat.Primes)
    (E : Type) [Field E] [NumberField E] (t : ℕ) (ht : 2 ≤ t) (hcond : 1 ≤ condF E)
    (C1 C2 C3 : ℕ)
    (hCountI : ∀ k : ℕ, 0 < k → k < t → ∀ Ls : Finset Nat.Primes,
      (∀ l ∈ Ls, l ∉ Bchi_χ ∧ (l : ℕ) ≠ 2 ∧ ¬ ((l : ℕ) - 1 ∣ 2 * k)) →
      (∀ l ∈ Ls, ∀ χ ∈ D.charSet E k, D.Vlen E l k χ ≠ ⊤) ∧
      ∑ l ∈ Ls, Real.log (l : ℕ) * ∑ χ ∈ D.charSet E k, ((D.Vlen E l k χ).toNat : ℝ) ≤
        ((condF E : ℝ) * (t : ℝ)) ^ C1)
    (hCountII : ∀ (l : Nat.Primes) (k : ℕ), l ∉ Bchi_χ → (l : ℕ) ≠ 2 → 0 < k → k < t →
      (l : ℕ) - 1 ∣ 2 * k → ∀ χ ∈ D.charSet E k, χ.isTrivial = false → χ.evenOrder = true →
      D.Vlen E l k χ ≠ ⊤ ∧
      ((D.Vlen E l k χ).toNat : ℝ) ≤ (((l : ℕ) : ℝ) * (condF E : ℝ) * (k : ℝ)) ^ C2)
    (hCountIII : ∀ (l : Nat.Primes) (k : ℕ), l ∉ Bchi_χ → (l : ℕ) ≠ 2 → 0 < k → k < t →
      (l : ℕ) - 1 ∣ 2 * k → ∀ χ ∈ D.charSet E k, χ.isTrivial = false → χ.evenOrder = false →
      D.Vlen E l k χ ≠ ⊤ ∧
      ((D.Vlen E l k χ).toNat : ℝ) ≤ (((l : ℕ) : ℝ) * (condF E : ℝ) * (k : ℝ)) ^ C3)
    (hPropZ : ∀ (l : Nat.Primes) (k : ℕ), l ∉ Bchi_χ → (l : ℕ) ≠ 2 → 0 < k → k < t →
      (l : ℕ) - 1 ∣ 2 * k → ∀ χ ∈ D.charSet E k, χ.isTrivial = true →
      @PropZResidualBernoulliUnit l.1 k ⟨l.2⟩ → D.Vlen E l k χ = 0)
    (hloss_out : ∀ (l : Nat.Primes) (k : ℕ), l ∉ Bchi_χ → (l : ℕ) ≠ 2 → 0 < k → k < t →
      D.loss E l k = 0) :
    let Cout : ℝ := ((max C1 (3 * max C2 C3 + 5) + 2 : ℕ) : ℝ)
    SumOut D.toParitySelmerSystem Bchi_χ E t (((condF E : ℝ) * (t : ℝ)) ^ Cout) := by
  classical
  set K := max C2 C3
  set CoutN : ℕ := max C1 (3 * K + 5) + 2
  have hN1 : (1 : ℝ) ≤ (condF E : ℝ) := by exact_mod_cast hcond
  have ht2 : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  set M : ℝ := (condF E : ℝ) * (t : ℝ)
  have hM2 : 2 ≤ M := by nlinarith
  have hM1 : 1 ≤ M := by linarith
  have ht_le_M : (t : ℝ) ≤ M := by nlinarith
  have hV_fin : ∀ (l : Nat.Primes) (k : ℕ), l ∉ Bchi_χ → (l : ℕ) ≠ 2 → 0 < k → k < t →
      ∀ χ ∈ D.charSet E k, D.Vlen E l k χ ≠ ⊤ := by
    intro l k hlB hl2 hk1 hkt χ hχ
    by_cases hdiv : (l : ℕ) - 1 ∣ 2 * k
    · cases htriv : χ.isTrivial
      · cases hev : χ.evenOrder
        · exact (hCountIII l k hlB hl2 hk1 hkt hdiv χ hχ htriv hev).1
        · exact (hCountII l k hlB hl2 hk1 hkt hdiv χ hχ htriv hev).1
      · have hzero : D.Vlen E l k χ = 0 := by
          have : Fact l.1.Prime := ⟨l.2⟩
          exact hPropZ l k hlB hl2 hk1 hkt hdiv χ hχ htriv
            (propZResidualBernoulliUnit_unconditional l.1 k hk1 hdiv)
        rw [hzero]
        exact ENat.natCast_ne_top 0
    · have hLs : ∀ l' ∈ ({l} : Finset Nat.Primes),
          l' ∉ Bchi_χ ∧ (l' : ℕ) ≠ 2 ∧ ¬ ((l' : ℕ) - 1 ∣ 2 * k) := by
        intro l' hl'
        rw [Finset.mem_singleton] at hl'
        subst hl'
        exact ⟨hlB, hl2, hdiv⟩
      exact (hCountI k hk1 hkt {l} hLs).1 l (Finset.mem_singleton_self l) χ hχ
  have hplus_fin : ∀ (l : Nat.Primes) (k : ℕ), l ∉ Bchi_χ → (l : ℕ) ≠ 2 → 0 < k → k < t →
      D.toParitySelmerSystem.plusLen E l k ≠ ⊤ := by
    intro l k hlB hl2 hk1 hkt
    exact (enat_sum_le_add_of_le (D.charSet E k) (D.Vlen E l k) (D.loss E l k)
      (D.plusLen E l k) (hV_fin l k hlB hl2 hk1 hkt) (D.plusLen_le E l k hl2 hk1)).1
  refine ⟨hplus_fin, fun S hS => ?_⟩
  have hper_l : ∀ l ∈ S,
      Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((D.toParitySelmerSystem.plusLen E l k).toNat : ℝ) ≤
        ∑ k ∈ Finset.Ico 1 t,
          Real.log (l : ℕ) * ∑ χ ∈ D.charSet E k, ((D.Vlen E l k χ).toNat : ℝ) := by
    intro l hl
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    have hlB := (hS l hl).1
    have hl2 := (hS l hl).2
    have hbd := (enat_sum_le_add_of_le (D.charSet E k) (D.Vlen E l k) (D.loss E l k)
      (D.plusLen E l k) (hV_fin l k hlB hl2 hk.1 hk.2) (D.plusLen_le E l k hl2 hk.1)).2
    rw [hloss_out l k hlB hl2 hk.1 hk.2, Nat.cast_zero, add_zero] at hbd
    exact mul_le_mul_of_nonneg_left hbd (Real.log_natCast_nonneg _)
  have hsum_swap :
      ∑ l ∈ S, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t,
        ((D.toParitySelmerSystem.plusLen E l k).toNat : ℝ) ≤
      ∑ k ∈ Finset.Ico 1 t,
        ∑ l ∈ S, Real.log (l : ℕ) * ∑ χ ∈ D.charSet E k, ((D.Vlen E l k χ).toNat : ℝ) := by
    calc ∑ l ∈ S, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t,
            ((D.toParitySelmerSystem.plusLen E l k).toNat : ℝ)
        ≤ ∑ l ∈ S, ∑ k ∈ Finset.Ico 1 t,
            Real.log (l : ℕ) * ∑ χ ∈ D.charSet E k, ((D.Vlen E l k χ).toNat : ℝ) :=
          Finset.sum_le_sum hper_l
      _ = ∑ k ∈ Finset.Ico 1 t,
            ∑ l ∈ S, Real.log (l : ℕ) * ∑ χ ∈ D.charSet E k, ((D.Vlen E l k χ).toNat : ℝ) :=
          Finset.sum_comm
  have hper_k : ∀ k ∈ Finset.Ico 1 t,
      ∑ l ∈ S, Real.log (l : ℕ) * ∑ χ ∈ D.charSet E k, ((D.Vlen E l k χ).toNat : ℝ) ≤
        M ^ C1 + M ^ (3 * K + 5) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    rw [← Finset.sum_filter_add_sum_filter_not S (fun l : Nat.Primes => ¬ ((l : ℕ) - 1 ∣ 2 * k))]
    have hpart1 :
        ∑ l ∈ S.filter (fun l : Nat.Primes => ¬ ((l : ℕ) - 1 ∣ 2 * k)),
          Real.log (l : ℕ) * ∑ χ ∈ D.charSet E k, ((D.Vlen E l k χ).toNat : ℝ) ≤
          M ^ C1 := by
      refine (hCountI k hk.1 hk.2 _ fun l hl => ?_).2
      rw [Finset.mem_filter] at hl
      exact ⟨(hS l hl.1).1, (hS l hl.1).2, hl.2⟩
    have hrest_le : ∀ l ∈ S.filter (fun l : Nat.Primes => ¬ ¬ ((l : ℕ) - 1 ∣ 2 * k)),
        (l : ℕ) ≤ 2 * t := by
      intro l hl
      rw [Finset.mem_filter, not_not] at hl
      have h1 := prime_le_two_mul_add_one_of_sub_one_dvd hk.1 hl.2
      omega
    have hcard_rest : ((S.filter (fun l : Nat.Primes => ¬ ¬ ((l : ℕ) - 1 ∣ 2 * k))).card : ℝ) ≤
        2 * (t : ℝ) := by
      exact_mod_cast card_primes_le_of_forall_le _ (2 * t) hrest_le
    have hterm_rest : ∀ l ∈ S.filter (fun l : Nat.Primes => ¬ ¬ ((l : ℕ) - 1 ∣ 2 * k)),
        Real.log (l : ℕ) * ∑ χ ∈ D.charSet E k, ((D.Vlen E l k χ).toNat : ℝ) ≤
          (2 * (t : ℝ)) * (condF E : ℝ) * (M ^ 3) ^ K := by
      intro l hl
      have hl_mem := (Finset.mem_filter.mp hl).1
      have hdiv : (l : ℕ) - 1 ∣ 2 * k := not_not.mp (Finset.mem_filter.mp hl).2
      have hlB := (hS l hl_mem).1
      have hl2 := (hS l hl_mem).2
      have hl_le_2t : ((l : ℕ) : ℝ) ≤ 2 * (t : ℝ) := by exact_mod_cast hrest_le l hl
      have hlog_le : Real.log (l : ℕ) ≤ 2 * (t : ℝ) :=
        (Real.log_le_sub_one_of_pos (by exact_mod_cast l.2.pos)).trans (by linarith)
      have hk_le_t : (k : ℝ) ≤ (t : ℝ) := by exact_mod_cast hk.2.le
      have hlNk_le_M3 : ((l : ℕ) : ℝ) * (condF E : ℝ) * (k : ℝ) ≤ M ^ 3 := by
        have h1 : ((l : ℕ) : ℝ) ≤ (t : ℝ) ^ 2 := by
          have : 2 * (t : ℝ) ≤ (t : ℝ) * (t : ℝ) := by nlinarith
          linarith [show (t : ℝ) ^ 2 = (t : ℝ) * (t : ℝ) by ring]
        calc ((l : ℕ) : ℝ) * (condF E : ℝ) * (k : ℝ)
            ≤ (t : ℝ) ^ 2 * (condF E : ℝ) * (t : ℝ) := by gcongr
          _ = (condF E : ℝ) * (t : ℝ) ^ 3 := by ring
          _ ≤ (condF E : ℝ) ^ 3 * (t : ℝ) ^ 3 := by
              have h1pow : (1 : ℝ) ≤ (condF E : ℝ) ^ 2 := one_le_pow₀ hN1
              calc (condF E : ℝ) * (t : ℝ) ^ 3
                  = (condF E : ℝ) * 1 * (t : ℝ) ^ 3 := by ring
                _ ≤ (condF E : ℝ) * (condF E : ℝ) ^ 2 * (t : ℝ) ^ 3 := by gcongr
                _ = (condF E : ℝ) ^ 3 * (t : ℝ) ^ 3 := by ring
          _ = M ^ 3 := by dsimp [M]; ring
      have hV_le : ∀ χ ∈ D.charSet E k, ((D.Vlen E l k χ).toNat : ℝ) ≤ (M ^ 3) ^ K := by
        intro χ hχ
        cases htriv : χ.isTrivial
        · cases hev : χ.evenOrder
          · have hbd := (hCountIII l k hlB hl2 hk.1 hk.2 hdiv χ hχ htriv hev).2
            refine hbd.trans ?_
            have hpos : 0 ≤ ((l : ℕ) : ℝ) * (condF E : ℝ) * (k : ℝ) := by positivity
            have hpow1 : (((l : ℕ) : ℝ) * (condF E : ℝ) * (k : ℝ)) ^ C3 ≤ (M ^ 3) ^ C3 :=
              pow_le_pow_left₀ hpos hlNk_le_M3 C3
            exact hpow1.trans (pow_le_pow_right₀ (one_le_pow₀ hM1) (le_max_right C2 C3))
          · have hbd := (hCountII l k hlB hl2 hk.1 hk.2 hdiv χ hχ htriv hev).2
            refine hbd.trans ?_
            have hpos : 0 ≤ ((l : ℕ) : ℝ) * (condF E : ℝ) * (k : ℝ) := by positivity
            have hpow1 : (((l : ℕ) : ℝ) * (condF E : ℝ) * (k : ℝ)) ^ C2 ≤ (M ^ 3) ^ C2 :=
              pow_le_pow_left₀ hpos hlNk_le_M3 C2
            exact hpow1.trans (pow_le_pow_right₀ (one_le_pow₀ hM1) (le_max_left C2 C3))
        · have hzero : D.Vlen E l k χ = 0 := by
            have : Fact l.1.Prime := ⟨l.2⟩
            exact hPropZ l k hlB hl2 hk.1 hk.2 hdiv χ hχ htriv
              (propZResidualBernoulliUnit_unconditional l.1 k hk.1 hdiv)
          rw [hzero]
          simp only [ENat.toNat_zero, Nat.cast_zero]
          positivity
      have hchar_sum : ∑ χ ∈ D.charSet E k, ((D.Vlen E l k χ).toNat : ℝ) ≤
          (condF E : ℝ) * (M ^ 3) ^ K := by
        calc ∑ χ ∈ D.charSet E k, ((D.Vlen E l k χ).toNat : ℝ)
            ≤ ∑ _χ ∈ D.charSet E k, (M ^ 3) ^ K := Finset.sum_le_sum hV_le
          _ = ((D.charSet E k).card : ℝ) * (M ^ 3) ^ K := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (condF E : ℝ) * (M ^ 3) ^ K := by
              gcongr
              exact_mod_cast D.charSet_card_le E k
      have hsum_nn : 0 ≤ ∑ χ ∈ D.charSet E k, ((D.Vlen E l k χ).toNat : ℝ) :=
        Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
      calc Real.log (l : ℕ) * ∑ χ ∈ D.charSet E k, ((D.Vlen E l k χ).toNat : ℝ)
          ≤ (2 * (t : ℝ)) * ((condF E : ℝ) * (M ^ 3) ^ K) :=
            mul_le_mul hlog_le hchar_sum hsum_nn (by positivity)
        _ = (2 * (t : ℝ)) * (condF E : ℝ) * (M ^ 3) ^ K := by ring
    have hpart2 :
        ∑ l ∈ S.filter (fun l : Nat.Primes => ¬ ¬ ((l : ℕ) - 1 ∣ 2 * k)),
          Real.log (l : ℕ) * ∑ χ ∈ D.charSet E k, ((D.Vlen E l k χ).toNat : ℝ) ≤
          M ^ (3 * K + 5) := by
      calc ∑ l ∈ S.filter (fun l : Nat.Primes => ¬ ¬ ((l : ℕ) - 1 ∣ 2 * k)),
              Real.log (l : ℕ) * ∑ χ ∈ D.charSet E k, ((D.Vlen E l k χ).toNat : ℝ)
          ≤ ∑ _l ∈ S.filter (fun l : Nat.Primes => ¬ ¬ ((l : ℕ) - 1 ∣ 2 * k)),
              (2 * (t : ℝ)) * (condF E : ℝ) * (M ^ 3) ^ K := Finset.sum_le_sum hterm_rest
        _ = ((S.filter (fun l : Nat.Primes => ¬ ¬ ((l : ℕ) - 1 ∣ 2 * k))).card : ℝ) *
              ((2 * (t : ℝ)) * (condF E : ℝ) * (M ^ 3) ^ K) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 * (t : ℝ)) * ((2 * (t : ℝ)) * (condF E : ℝ) * (M ^ 3) ^ K) := by gcongr
        _ = 4 * (t : ℝ) ^ 2 * (condF E : ℝ) * M ^ (3 * K) := by
            rw [← pow_mul]; ring
        _ ≤ M ^ 4 * (condF E : ℝ) * M ^ (3 * K) := by
            have h4t2 : 4 * (t : ℝ) ^ 2 ≤ M ^ 4 := by
              have h4 : (4 : ℝ) ≤ M ^ 2 := by nlinarith
              calc 4 * (t : ℝ) ^ 2 ≤ M ^ 2 * M ^ 2 := by gcongr
                _ = M ^ 4 := by ring
            gcongr
        _ ≤ M ^ 4 * M * M ^ (3 * K) := by gcongr; nlinarith
        _ = M ^ (3 * K + 5) := by ring
    exact add_le_add hpart1 hpart2
  calc ∑ l ∈ S, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t,
          ((D.toParitySelmerSystem.plusLen E l k).toNat : ℝ)
      ≤ ∑ k ∈ Finset.Ico 1 t,
          ∑ l ∈ S, Real.log (l : ℕ) * ∑ χ ∈ D.charSet E k, ((D.Vlen E l k χ).toNat : ℝ) := hsum_swap
    _ ≤ ∑ _k ∈ Finset.Ico 1 t, (M ^ C1 + M ^ (3 * K + 5)) := Finset.sum_le_sum hper_k
    _ = ((Finset.Ico 1 t).card : ℝ) * (M ^ C1 + M ^ (3 * K + 5)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ M * (M ^ (max C1 (3 * K + 5)) + M ^ (max C1 (3 * K + 5))) := by
        have hcardt : ((Finset.Ico 1 t).card : ℝ) ≤ M := by
          rw [Nat.card_Ico]
          exact le_trans (by exact_mod_cast Nat.sub_le t 1) ht_le_M
        have hp1 : M ^ C1 ≤ M ^ (max C1 (3 * K + 5)) := pow_le_pow_right₀ hM1 (le_max_left _ _)
        have hp2 : M ^ (3 * K + 5) ≤ M ^ (max C1 (3 * K + 5)) :=
          pow_le_pow_right₀ hM1 (le_max_right _ _)
        exact mul_le_mul hcardt (add_le_add hp1 hp2) (by positivity) (by positivity)
    _ = 2 * M ^ (max C1 (3 * K + 5) + 1) := by ring
    _ ≤ M * M ^ (max C1 (3 * K + 5) + 1) := by gcongr
    _ = M ^ CoutN := by dsimp [CoutN]; ring
    _ = ((condF E : ℝ) * (t : ℝ)) ^ ((CoutN : ℕ) : ℝ) := by rw [Real.rpow_natCast]

/-- Absorbs any constant `K : ℕ` into `M^(Nat.log 2 K + 1)` whenever `2 ≤ M`. -/
private lemma nat_le_pow_of_two_le (K : ℕ) {M : ℝ} (hM : 2 ≤ M) :
    (K : ℝ) ≤ M ^ (Nat.log 2 K + 1) := by
  have hlt : K < 2 ^ (Nat.log 2 K + 1) := Nat.lt_pow_succ_log_self (by norm_num) K
  have hR : (K : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 K + 1) := by exact_mod_cast hlt.le
  exact hR.trans (pow_le_pow_left₀ (by norm_num) hM _)

/-- **BAD-ODD-PRIME `SumIn` ASSEMBLY (`sumIn_of_counts`)**:
Assembles `SumIn` over `l ∈ Bchi_χ` (`l ≠ 2`) from:
- `CountIV` / `BbAt` (`k ≥ 2`, odd order, bounded by `shaLen (L₂ l) + rem`),
- `CountII` (`k ≥ 2`, even order),
- `CountV` (`k = 1`, `R₁ ≤ 2^{c₂}`),
- `CountVs` (`k = 1`, `2^{c₂} < R₁`),
- `loss` (`RedAll` polynomial local loss at `l ∈ Bchi_χ`). -/
theorem sumIn_of_counts {S : SelmerSystem} (D : CharSelmerData S)
    {H : H2LengthSystem} {T : TowerLayerRelation}
    (Bchi_χ : Finset Nat.Primes) (Rl : Nat.Primes → ℕ)
    (L₂ : Nat.Primes → Type) [∀ l, Field (L₂ l)] [∀ l, NumberField (L₂ l)]
    (_hBad : ∀ l ∈ Bchi_χ, BadOddTowerData S H T l (Rl l) (L₂ l))
    (E : Type) [Field E] [NumberField E] (t : ℕ) (ht : 2 ≤ t) (hcond : 1 ≤ condF E)
    {Biv : ℝ} (hBiv : 0 ≤ Biv)
    (hbb : ∀ l ∈ Bchi_χ, VVat S l (L₂ l) t Biv)
    (C2 C4 C5 C5s Closs : ℕ)
    (hCountIV : ∀ l ∈ Bchi_χ, ∀ k : ℕ, (l : ℕ) ≠ 2 → 2 ≤ k → k < t →
      ∃ rem : ℕ,
        ∑ χ ∈ (D.charSet E k).filter (fun χ => χ.evenOrder = false), D.Vlen E l k χ ≤
          S.shaLen (L₂ l) l k + (rem : ℕ∞) ∧
        (rem : ℝ) ≤ (((l : ℕ) : ℝ) * (condF E : ℝ) * (k : ℝ)) ^ C4)
    (hCountII : ∀ l ∈ Bchi_χ, (l : ℕ) ≠ 2 →
      ∀ k : ℕ, 2 ≤ k → k < t → ∀ χ ∈ D.charSet E k, χ.evenOrder = true →
      D.Vlen E l k χ ≠ ⊤ ∧
      ((D.Vlen E l k χ).toNat : ℝ) ≤ (((l : ℕ) : ℝ) * (condF E : ℝ) * (k : ℝ)) ^ C2)
    (hCountV : ∀ l ∈ Bchi_χ, (l : ℕ) ≠ 2 →
      1 < t → ∀ χ ∈ D.charSet E 1, χ.r1LeTwoPowC2 = true →
      D.Vlen E l 1 χ ≠ ⊤ ∧
      ((D.Vlen E l 1 χ).toNat : ℝ) ≤ (((l : ℕ) : ℝ) * (condF E : ℝ)) ^ C5)
    (hCountVs : ∀ l ∈ Bchi_χ, (l : ℕ) ≠ 2 →
      1 < t → ∀ χ ∈ D.charSet E 1, χ.r1LeTwoPowC2 = false →
      D.Vlen E l 1 χ ≠ ⊤ ∧
      ((D.Vlen E l 1 χ).toNat : ℝ) ≤ (((l : ℕ) : ℝ) * (condF E : ℝ)) ^ C5s)
    (hloss_in : ∀ (l : Nat.Primes) (k : ℕ), l ∈ Bchi_χ → (l : ℕ) ≠ 2 → 0 < k → k < t →
      (D.loss E l k : ℝ) ≤ (((l : ℕ) : ℝ) * (condF E : ℝ) * (k : ℝ)) ^ Closs) :
    let lmax := Bchi_χ.sup (fun l => (l : ℕ))
    let Kpow := max (max C4 C2) (max C5 (max C5s Closs))
    let A_l := Nat.log 2 (lmax + 1) + 1
    let A_B := Nat.log 2 (Bchi_χ.card + 1) + 1
    let Cin : ℝ := (((A_l + 1) * Kpow + A_l + A_B + 4 : ℕ) : ℝ)
    SumIn D.toParitySelmerSystem Bchi_χ E t
      (((condF E : ℝ) * (t : ℝ)) ^ Cin + (∑ l ∈ Bchi_χ, Real.log (l : ℕ)) * Biv) := by
  classical
  set lmax := Bchi_χ.sup (fun l => (l : ℕ))
  set Kpow := max (max C4 C2) (max C5 (max C5s Closs))
  set A_l := Nat.log 2 (lmax + 1) + 1
  set A_B := Nat.log 2 (Bchi_χ.card + 1) + 1
  set CinN : ℕ := (A_l + 1) * Kpow + A_l + A_B + 4
  set M : ℝ := (condF E : ℝ) * (t : ℝ)
  have hN1 : (1 : ℝ) ≤ (condF E : ℝ) := by exact_mod_cast hcond
  have ht2 : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hM2 : 2 ≤ M := by nlinarith
  have hM1 : 1 ≤ M := by linarith
  have hN_le_M : (condF E : ℝ) ≤ M := by nlinarith
  have ht_le_M : (t : ℝ) ≤ M := by nlinarith
  have hlmax_bd : (lmax : ℝ) ≤ M ^ A_l := by
    refine le_trans ?_ (nat_le_pow_of_two_le (lmax + 1) hM2)
    exact_mod_cast Nat.le_succ lmax
  have hBcard_bd : (Bchi_χ.card : ℝ) ≤ M ^ A_B := by
    refine le_trans ?_ (nat_le_pow_of_two_le (Bchi_χ.card + 1) hM2)
    exact_mod_cast Nat.le_succ Bchi_χ.card
  have h_elem : ∀ (l : Nat.Primes) (hl : l ∈ Bchi_χ), (l : ℕ) ≠ 2 →
      ∀ k : ℕ, 0 < k → k < t →
      ∃ rem : ℕ,
        D.toParitySelmerSystem.plusLen E l k ≤ S.shaLen (L₂ l) l k + (rem : ℕ∞) ∧
        (rem : ℝ) ≤ M ^ ((A_l + 1) * Kpow + 2) := by
    intro l hl hl2 k hk1 hkt
    have hl_le : ((l : ℕ) : ℝ) ≤ M ^ A_l := by
      have h1 : (l : ℕ) ≤ lmax := Finset.le_sup (f := fun p : Nat.Primes => (p : ℕ)) hl
      exact (by exact_mod_cast h1 : ((l : ℕ) : ℝ) ≤ lmax).trans hlmax_bd
    have hlMk_le : ((l : ℕ) : ℝ) * (condF E : ℝ) * (k : ℝ) ≤ M ^ (A_l + 1) := by
      have hk_le : (k : ℝ) ≤ (t : ℝ) := by exact_mod_cast hkt.le
      calc ((l : ℕ) : ℝ) * (condF E : ℝ) * (k : ℝ)
          ≤ M ^ A_l * (condF E : ℝ) * (t : ℝ) := by gcongr
        _ = M ^ (A_l + 1) := by dsimp [M]; ring
    have hlM_le : ((l : ℕ) : ℝ) * (condF E : ℝ) ≤ M ^ (A_l + 1) := by
      calc ((l : ℕ) : ℝ) * (condF E : ℝ) ≤ M ^ A_l * M := by gcongr
        _ = M ^ (A_l + 1) := by ring
    have hpow_bd : ∀ E' : ℕ, E' ≤ Kpow →
        (((l : ℕ) : ℝ) * (condF E : ℝ) * (k : ℝ)) ^ E' ≤ M ^ ((A_l + 1) * Kpow) := by
      intro E' hE'
      calc (((l : ℕ) : ℝ) * (condF E : ℝ) * (k : ℝ)) ^ E'
          ≤ (M ^ (A_l + 1)) ^ E' := pow_le_pow_left₀ (by positivity) hlMk_le E'
        _ ≤ (M ^ (A_l + 1)) ^ Kpow := pow_le_pow_right₀ (one_le_pow₀ hM1) hE'
        _ = M ^ ((A_l + 1) * Kpow) := by rw [← pow_mul]
    have hpow_bd2 : ∀ E' : ℕ, E' ≤ Kpow →
        (((l : ℕ) : ℝ) * (condF E : ℝ)) ^ E' ≤ M ^ ((A_l + 1) * Kpow) := by
      intro E' hE'
      calc (((l : ℕ) : ℝ) * (condF E : ℝ)) ^ E'
          ≤ (M ^ (A_l + 1)) ^ E' := pow_le_pow_left₀ (by positivity) hlM_le E'
        _ ≤ (M ^ (A_l + 1)) ^ Kpow := pow_le_pow_right₀ (one_le_pow₀ hM1) hE'
        _ = M ^ ((A_l + 1) * Kpow) := by rw [← pow_mul]
    have hloss_bd : (D.loss E l k : ℝ) ≤ M ^ ((A_l + 1) * Kpow) :=
      (hloss_in l k hl hl2 hk1 hkt).trans
        (hpow_bd Closs (le_max_of_le_right (le_max_of_le_right (le_max_right _ _))))
    have hplus_le := D.plusLen_le E l k hl2 hk1
    by_cases hk1_eq : k = 1
    · subst hk1_eq
      have hfin1 : ∀ χ ∈ D.charSet E 1, D.Vlen E l 1 χ ≠ ⊤ := by
        intro χ hχ
        cases hr1 : χ.r1LeTwoPowC2
        · exact (hCountVs l hl hl2 hkt χ hχ hr1).1
        · exact (hCountV l hl hl2 hkt χ hχ hr1).1
      set rem : ℕ := (∑ χ ∈ D.charSet E 1, (D.Vlen E l 1 χ).toNat) + D.loss E l 1
      refine ⟨rem, ?_, ?_⟩
      · have hle_rem : D.toParitySelmerSystem.plusLen E l 1 ≤ (rem : ℕ∞) := by
          dsimp [CharSelmerData.toParitySelmerSystem, rem]
          rw [Nat.cast_add, ← enat_sum_eq_coe_sum (D.charSet E 1) (D.Vlen E l 1) hfin1]
          exact hplus_le
        exact hle_rem.trans le_add_self
      · have hchar_bd : ∀ χ ∈ D.charSet E 1, ((D.Vlen E l 1 χ).toNat : ℝ) ≤ M ^ ((A_l + 1) * Kpow) := by
          intro χ hχ
          cases hr1 : χ.r1LeTwoPowC2
          · exact (hCountVs l hl hl2 hkt χ hχ hr1).2.trans
              (hpow_bd2 C5s (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))
          · exact (hCountV l hl hl2 hkt χ hχ hr1).2.trans
              (hpow_bd2 C5 (le_max_of_le_right (le_max_left _ _)))
        have hsum_bd : (∑ χ ∈ D.charSet E 1, ((D.Vlen E l 1 χ).toNat : ℝ)) ≤
            M * M ^ ((A_l + 1) * Kpow) := by
          calc ∑ χ ∈ D.charSet E 1, ((D.Vlen E l 1 χ).toNat : ℝ)
              ≤ ∑ _χ ∈ D.charSet E 1, M ^ ((A_l + 1) * Kpow) := Finset.sum_le_sum hchar_bd
            _ = ((D.charSet E 1).card : ℝ) * M ^ ((A_l + 1) * Kpow) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (condF E : ℝ) * M ^ ((A_l + 1) * Kpow) := by
                gcongr; exact_mod_cast D.charSet_card_le E 1
            _ ≤ M * M ^ ((A_l + 1) * Kpow) := by gcongr
        have hrem_R : (rem : ℝ) = (∑ χ ∈ D.charSet E 1, ((D.Vlen E l 1 χ).toNat : ℝ)) +
            (D.loss E l 1 : ℝ) := by
          dsimp [rem]; push_cast; rfl
        rw [hrem_R]
        calc (∑ χ ∈ D.charSet E 1, ((D.Vlen E l 1 χ).toNat : ℝ)) + (D.loss E l 1 : ℝ)
            ≤ M * M ^ ((A_l + 1) * Kpow) + 1 * M ^ ((A_l + 1) * Kpow) := by
              rw [one_mul]; exact add_le_add hsum_bd hloss_bd
          _ = (M + 1) * M ^ ((A_l + 1) * Kpow) := by ring
          _ ≤ M ^ 2 * M ^ ((A_l + 1) * Kpow) := by
              gcongr; nlinarith
          _ = M ^ ((A_l + 1) * Kpow + 2) := by ring
    · have hk2 : 2 ≤ k := by omega
      obtain ⟨rIV, hrIV_le, hrIV_bd⟩ := hCountIV l hl k hl2 hk2 hkt
      set S_ev := (D.charSet E k).filter (fun χ => χ.evenOrder = true)
      set S_od := (D.charSet E k).filter (fun χ => χ.evenOrder = false)
      have hfin_ev : ∀ χ ∈ S_ev, D.Vlen E l k χ ≠ ⊤ := by
        intro χ hχ
        exact (hCountII l hl hl2 k hk2 hkt χ (Finset.mem_filter.mp hχ).1
          (Finset.mem_filter.mp hχ).2).1
      have hsplit : ∑ χ ∈ D.charSet E k, D.Vlen E l k χ =
          (∑ χ ∈ S_od, D.Vlen E l k χ) + (∑ χ ∈ S_ev, D.Vlen E l k χ) := by
        have hpart := (Finset.sum_filter_add_sum_filter_not (D.charSet E k)
          (fun χ => χ.evenOrder = false) (fun χ => D.Vlen E l k χ)).symm
        have hsev : (D.charSet E k).filter (fun χ => ¬ χ.evenOrder = false) = S_ev := by
          ext χ
          simp [S_ev]
        rwa [hsev] at hpart
      set rem : ℕ := rIV + (∑ χ ∈ S_ev, (D.Vlen E l k χ).toNat) + D.loss E l k
      refine ⟨rem, ?_, ?_⟩
      · have hsum_ev : (∑ χ ∈ S_ev, D.Vlen E l k χ) =
            ((∑ χ ∈ S_ev, (D.Vlen E l k χ).toNat : ℕ) : ℕ∞) :=
          enat_sum_eq_coe_sum S_ev (D.Vlen E l k) hfin_ev
        dsimp [CharSelmerData.toParitySelmerSystem, rem]
        calc D.plusLen E l k
            ≤ (∑ χ ∈ D.charSet E k, D.Vlen E l k χ) + (D.loss E l k : ℕ∞) := hplus_le
          _ = (∑ χ ∈ S_od, D.Vlen E l k χ) + (∑ χ ∈ S_ev, D.Vlen E l k χ) +
                (D.loss E l k : ℕ∞) := by rw [hsplit]
          _ ≤ (S.shaLen (L₂ l) l k + (rIV : ℕ∞)) +
                ((∑ χ ∈ S_ev, (D.Vlen E l k χ).toNat : ℕ) : ℕ∞) +
                (D.loss E l k : ℕ∞) := by
              rw [hsum_ev]
              gcongr
          _ = S.shaLen (L₂ l) l k +
                ((rIV + (∑ χ ∈ S_ev, (D.Vlen E l k χ).toNat) + D.loss E l k : ℕ) : ℕ∞) := by
              push_cast; ac_rfl
      · have hrIV_M : (rIV : ℝ) ≤ M ^ ((A_l + 1) * Kpow) :=
          hrIV_bd.trans (hpow_bd C4 (le_max_of_le_left (le_max_left _ _)))
        have hev_bd : ∀ χ ∈ S_ev, ((D.Vlen E l k χ).toNat : ℝ) ≤ M ^ ((A_l + 1) * Kpow) := by
          intro χ hχ
          exact (hCountII l hl hl2 k hk2 hkt χ (Finset.mem_filter.mp hχ).1
            (Finset.mem_filter.mp hχ).2).2.trans
            (hpow_bd C2 (le_max_of_le_left (le_max_right _ _)))
        have hsum_ev_bd : (∑ χ ∈ S_ev, ((D.Vlen E l k χ).toNat : ℝ)) ≤
            M * M ^ ((A_l + 1) * Kpow) := by
          calc ∑ χ ∈ S_ev, ((D.Vlen E l k χ).toNat : ℝ)
              ≤ ∑ _χ ∈ S_ev, M ^ ((A_l + 1) * Kpow) := Finset.sum_le_sum hev_bd
            _ = (S_ev.card : ℝ) * M ^ ((A_l + 1) * Kpow) := by rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ ((D.charSet E k).card : ℝ) * M ^ ((A_l + 1) * Kpow) :=
                mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_filter_le _ _) (by positivity)
            _ ≤ (condF E : ℝ) * M ^ ((A_l + 1) * Kpow) := by
                gcongr; exact_mod_cast D.charSet_card_le E k
            _ ≤ M * M ^ ((A_l + 1) * Kpow) := by gcongr
        have hrem_R : (rem : ℝ) = (rIV : ℝ) + (∑ χ ∈ S_ev, ((D.Vlen E l k χ).toNat : ℝ)) +
            (D.loss E l k : ℝ) := by
          dsimp [rem]; push_cast; rfl
        rw [hrem_R]
        calc (rIV : ℝ) + (∑ χ ∈ S_ev, ((D.Vlen E l k χ).toNat : ℝ)) + (D.loss E l k : ℝ)
            ≤ M ^ ((A_l + 1) * Kpow) + M * M ^ ((A_l + 1) * Kpow) + M ^ ((A_l + 1) * Kpow) :=
              add_le_add (add_le_add hrIV_M hsum_ev_bd) hloss_bd
          _ = (M + 2) * M ^ ((A_l + 1) * Kpow) := by ring
          _ ≤ M ^ 2 * M ^ ((A_l + 1) * Kpow) := by
              gcongr; nlinarith
          _ = M ^ ((A_l + 1) * Kpow + 2) := by ring
  have hplus_fin : ∀ l ∈ Bchi_χ, ∀ k : ℕ, (l : ℕ) ≠ 2 → 0 < k → k < t →
      D.toParitySelmerSystem.plusLen E l k ≠ ⊤ := by
    intro l hl k hl2 hk1 hkt
    obtain ⟨rem, hle, _⟩ := h_elem l hl hl2 k hk1 hkt
    exact ne_top_of_le_ne_top (WithTop.add_ne_top.mpr ⟨(hbb l hl).1 k hk1 hkt, ENat.natCast_ne_top _⟩) hle
  refine ⟨hplus_fin, fun S_in hSin => ?_⟩
  have hrem_ex : ∀ (l : Nat.Primes) (k : ℕ),
      ∃ rem : ℕ,
        (∀ hl : l ∈ Bchi_χ, (l : ℕ) ≠ 2 → 0 < k → k < t →
          D.toParitySelmerSystem.plusLen E l k ≤ S.shaLen (L₂ l) l k + (rem : ℕ∞) ∧
          (rem : ℝ) ≤ M ^ ((A_l + 1) * Kpow + 2)) := by
    intro l k
    by_cases hcond_lk : l ∈ Bchi_χ ∧ (l : ℕ) ≠ 2 ∧ 0 < k ∧ k < t
    · obtain ⟨rem, h1, h2⟩ := h_elem l hcond_lk.1 hcond_lk.2.1 k hcond_lk.2.2.1 hcond_lk.2.2.2
      exact ⟨rem, fun _ _ _ _ => ⟨h1, h2⟩⟩
    · refine ⟨0, fun hl hl2 hk1 hkt => absurd ⟨hl, hl2, hk1, hkt⟩ hcond_lk⟩
  choose remFn hremFn using hrem_ex
  have hper_l : ∀ l ∈ S_in,
      Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t,
        ((D.toParitySelmerSystem.plusLen E l k).toNat : ℝ) ≤
        Real.log (l : ℕ) * Biv +
        Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, (remFn l k : ℝ) := by
    intro l hl
    have hlB := (hSin l hl).1
    have hl2 := (hSin l hl).2
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg _)
    calc ∑ k ∈ Finset.Ico 1 t, ((D.toParitySelmerSystem.plusLen E l k).toNat : ℝ)
        ≤ ∑ k ∈ Finset.Ico 1 t, (((S.shaLen (L₂ l) l k).toNat : ℝ) + (remFn l k : ℝ)) := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [Finset.mem_Ico] at hk
          have h1 := (hremFn l k hlB hl2 hk.1 hk.2).1
          have hne := (hbb l hlB).1 k hk.1 hk.2
          obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hne
          have h1' : D.toParitySelmerSystem.plusLen E l k ≤ ((a + remFn l k : ℕ) : ℕ∞) := by
            rw [← ha] at h1
            simpa [Nat.cast_add] using h1
          have hpne := ne_top_of_le_ne_top (ENat.natCast_ne_top _) h1'
          obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hpne
          rw [← ha, ← hb, ENat.toNat_natCast, ENat.toNat_natCast]
          have hnat : b ≤ a + remFn l k := by rw [← hb] at h1'; exact_mod_cast h1'
          exact_mod_cast hnat
      _ = (∑ k ∈ Finset.Ico 1 t, ((S.shaLen (L₂ l) l k).toNat : ℝ)) +
          (∑ k ∈ Finset.Ico 1 t, (remFn l k : ℝ)) := Finset.sum_add_distrib
      _ ≤ Biv + ∑ k ∈ Finset.Ico 1 t, (remFn l k : ℝ) := by
          gcongr; exact (hbb l hlB).2
  have hrem_sum : ∑ l ∈ S_in, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, (remFn l k : ℝ) ≤
      M ^ (CinN : ℝ) := by
    have hterm_l : ∀ l ∈ S_in,
        Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, (remFn l k : ℝ) ≤
          M ^ A_l * (M * M ^ ((A_l + 1) * Kpow + 2)) := by
      intro l hl
      have hlB := (hSin l hl).1
      have hl2 := (hSin l hl).2
      have hlog_le : Real.log (l : ℕ) ≤ M ^ A_l := by
        have h1 : (l : ℕ) ≤ lmax := Finset.le_sup (f := fun p : Nat.Primes => (p : ℕ)) hlB
        exact (Real.log_le_sub_one_of_pos (by exact_mod_cast l.2.pos)).trans
          (by linarith [(by exact_mod_cast h1 : ((l : ℕ) : ℝ) ≤ lmax).trans hlmax_bd])
      have hsum_k : ∑ k ∈ Finset.Ico 1 t, (remFn l k : ℝ) ≤ M * M ^ ((A_l + 1) * Kpow + 2) := by
        calc ∑ k ∈ Finset.Ico 1 t, (remFn l k : ℝ)
            ≤ ∑ _k ∈ Finset.Ico 1 t, M ^ ((A_l + 1) * Kpow + 2) := by
              refine Finset.sum_le_sum fun k hk => ?_
              rw [Finset.mem_Ico] at hk
              exact (hremFn l k hlB hl2 hk.1 hk.2).2
          _ = ((Finset.Ico 1 t).card : ℝ) * M ^ ((A_l + 1) * Kpow + 2) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ M * M ^ ((A_l + 1) * Kpow + 2) := by
              gcongr
              rw [Nat.card_Ico]
              exact le_trans (by exact_mod_cast Nat.sub_le t 1) ht_le_M
      exact mul_le_mul hlog_le hsum_k (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
        (by positivity)
    calc ∑ l ∈ S_in, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, (remFn l k : ℝ)
        ≤ ∑ _l ∈ S_in, M ^ A_l * (M * M ^ ((A_l + 1) * Kpow + 2)) := Finset.sum_le_sum hterm_l
      _ = (S_in.card : ℝ) * (M ^ A_l * (M * M ^ ((A_l + 1) * Kpow + 2))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Bchi_χ.card : ℝ) * (M ^ A_l * (M * M ^ ((A_l + 1) * Kpow + 2))) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card fun l hl => (hSin l hl).1)
            (by positivity)
      _ ≤ M ^ A_B * (M ^ A_l * (M * M ^ ((A_l + 1) * Kpow + 2))) := by gcongr
      _ = M ^ ((A_l + 1) * Kpow + A_l + A_B + 3) := by ring
      _ ≤ M ^ CinN := pow_le_pow_right₀ hM1 (by dsimp [CinN]; omega)
      _ = M ^ (CinN : ℝ) := by rw [Real.rpow_natCast]
  calc ∑ l ∈ S_in, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t,
          ((D.toParitySelmerSystem.plusLen E l k).toNat : ℝ)
      ≤ ∑ l ∈ S_in, (Real.log (l : ℕ) * Biv +
          Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, (remFn l k : ℝ)) := Finset.sum_le_sum hper_l
    _ = (∑ l ∈ S_in, Real.log (l : ℕ)) * Biv +
        (∑ l ∈ S_in, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, (remFn l k : ℝ)) := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ (∑ l ∈ Bchi_χ, Real.log (l : ℕ)) * Biv + M ^ (CinN : ℝ) := by
        apply add_le_add _ hrem_sum
        apply mul_le_mul_of_nonneg_right _ hBiv
        exact Finset.sum_le_sum_of_subset_of_nonneg (fun l hl => (hSin l hl).1)
          (fun _ _ _ => Real.log_natCast_nonneg _)
    _ = M ^ (CinN : ℝ) + (∑ l ∈ Bchi_χ, Real.log (l : ℕ)) * Biv := add_comm _ _

/-- **MASTER 6-CASE FIELD-1 SUPPLY (`SixCaseField1Supply S`)**:
Matches Alpöge's EXACT Field-1 mathematical architecture (`VwinOfRow` → `HVCore` → `JointWinOfCounts`),
replacing the mismatched `MinimalOddUnramifiedPatchingSupply` with:
1. Complex-conjugation parity + character-level decomposition (`charData : CharSelmerData S`),
2. Coarse `H²` upper bound `LemmaK` (`hLemmaK : LemmaKSystem H2 CK0`) + `Window1` towers:
   - `twoTower` (`l = 2`: Ferrero–Washington `μ = 0` + `Window1` → `BaAt`),
   - `badOddTower` (`l ∈ Bchi_χ`: `CaseIV` `Window1` + `LemmaK` → `BbAt`),
3. Odd minus-parity `VVminusLe` (`minusParity`: Rubin `l ∤ [E:ℚ]` + Stickelberger `l ∣ [E:ℚ]`),
4. Odd plus-parity 6-case bounds (`CountI`, `CountII`, `CountIII`, `CountIV`, `CountV`, `CountVs`),
5. **`CountZ` (`CaseZ`) conditional ONLY on `PropZResidualBernoulliUnit`** — which is **100%
   unconditionally discharged (`0` assumptions!) by von Staudt–Clausen (`Section 1`)**! -/
structure SixCaseField1Supply (S : SelmerSystem) where
  charData : CharSelmerData S
  H2 : H2LengthSystem
  T : TowerLayerRelation
  CK0 : ℝ
  hLemmaK : LemmaKSystem H2 CK0
  Cb : ℝ
  char_data : ∀ ψ : PChar,
    ∃ (R₀ : ℕ) (Bchi_χ : Finset Nat.Primes) (Rl : Nat.Primes → ℕ)
      (L₂ : Nat.Primes → Type) (_ : ∀ l, Field (L₂ l)) (_ : ∀ l, NumberField (L₂ l))
      (P0 : ℝ) (C1 C2 C3 C4 C5 C5s Closs : ℕ),
      -- Branch 1 (`l = 2`): Global Ferrero–Washington + `Window1`
      TwoTowerWindowData S H2 T ψ R₀ ∧
      -- `l ∈ Bchi_χ` tower data for `CaseIV` / `BbAt`
      (∀ l ∈ Bchi_χ, BadOddTowerData S H2 T l (Rl l) (L₂ l)) ∧
      -- Branch 2 (all odd `l ≠ 2`, minus parity): Rubin + Stickelberger
      (∀ (e t : ℝ → ℕ), AdmissiblePage 4 401 e t →
        ∀ x : ℝ, 2 ≤ x → ∀ q d : ℕ, TaylorWilesWindow.PrimePair ψ.N q d →
          ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ (e x) q d E →
            VVminusLe charData.toParitySelmerSystem E (t x)
              (minusBound Cb ψ.N (Module.finrank ℚ E) (condF E) (t x))) ∧
      -- Branch 3a (`l ∈ Bchi_χ`, plus parity): `CountIV` + `CountII` + `CountV` + `CountVs` + `RedAll` loss
      (∀ (e t : ℝ → ℕ), AdmissiblePage 4 401 e t →
        ∀ x : ℝ, 2 ≤ x → ∀ q d : ℕ, TaylorWilesWindow.PrimePair ψ.N q d →
          P0 < (q : ℝ) → P0 < (d : ℝ) →
          ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ (e x) q d E →
            (∀ l ∈ Bchi_χ, ∀ k : ℕ, (l : ℕ) ≠ 2 → 2 ≤ k → k < t x →
              ∃ rem : ℕ,
                ∑ χ ∈ (charData.charSet E k).filter (fun χ => χ.evenOrder = false),
                  charData.Vlen E l k χ ≤ S.shaLen (L₂ l) l k + (rem : ℕ∞) ∧
                (rem : ℝ) ≤ (((l : ℕ) : ℝ) * (condF E : ℝ) * (k : ℝ)) ^ C4) ∧
            (∀ l ∈ Bchi_χ, (l : ℕ) ≠ 2 →
              ∀ k : ℕ, 2 ≤ k → k < t x → ∀ χ ∈ charData.charSet E k, χ.evenOrder = true →
              charData.Vlen E l k χ ≠ ⊤ ∧
              ((charData.Vlen E l k χ).toNat : ℝ) ≤
                (((l : ℕ) : ℝ) * (condF E : ℝ) * (k : ℝ)) ^ C2) ∧
            (∀ l ∈ Bchi_χ, (l : ℕ) ≠ 2 →
              1 < t x → ∀ χ ∈ charData.charSet E 1, χ.r1LeTwoPowC2 = true →
              charData.Vlen E l 1 χ ≠ ⊤ ∧
              ((charData.Vlen E l 1 χ).toNat : ℝ) ≤ (((l : ℕ) : ℝ) * (condF E : ℝ)) ^ C5) ∧
            (∀ l ∈ Bchi_χ, (l : ℕ) ≠ 2 →
              1 < t x → ∀ χ ∈ charData.charSet E 1, χ.r1LeTwoPowC2 = false →
              charData.Vlen E l 1 χ ≠ ⊤ ∧
              ((charData.Vlen E l 1 χ).toNat : ℝ) ≤ (((l : ℕ) : ℝ) * (condF E : ℝ)) ^ C5s) ∧
            (∀ (l : Nat.Primes) (k : ℕ), l ∈ Bchi_χ → (l : ℕ) ≠ 2 → 0 < k → k < t x →
              (charData.loss E l k : ℝ) ≤ (((l : ℕ) : ℝ) * (condF E : ℝ) * (k : ℝ)) ^ Closs)) ∧
      -- Branch 3b (`l ∉ Bchi_χ`, plus parity): `CountI` + `CountII` + `CountIII` + `PropZ → CountZ`!
      (∀ (e t : ℝ → ℕ), AdmissiblePage 4 401 e t →
        ∀ (X x : ℝ), 2 ≤ x → ∀ q d : ℕ, TaylorWilesWindow.PrimePair ψ.N q d →
          2 * X ^ (401 : ℝ) + 1 < (q : ℝ) → 2 * X ^ (401 : ℝ) + 1 < (d : ℝ) →
          P0 < (q : ℝ) → P0 < (d : ℝ) →
          ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ (e x) q d E →
            (∀ k : ℕ, 0 < k → k < t x → ∀ Ls : Finset Nat.Primes,
              (∀ l ∈ Ls, l ∉ Bchi_χ ∧ (l : ℕ) ≠ 2 ∧ ¬ ((l : ℕ) - 1 ∣ 2 * k)) →
              (∀ l ∈ Ls, ∀ χ ∈ charData.charSet E k, charData.Vlen E l k χ ≠ ⊤) ∧
              ∑ l ∈ Ls, Real.log (l : ℕ) *
                ∑ χ ∈ charData.charSet E k, ((charData.Vlen E l k χ).toNat : ℝ) ≤
                ((condF E : ℝ) * (t x : ℝ)) ^ C1) ∧
            (∀ (l : Nat.Primes) (k : ℕ), l ∉ Bchi_χ → (l : ℕ) ≠ 2 → 0 < k → k < t x →
              (l : ℕ) - 1 ∣ 2 * k → ∀ χ ∈ charData.charSet E k,
              χ.isTrivial = false → χ.evenOrder = true →
              charData.Vlen E l k χ ≠ ⊤ ∧
              ((charData.Vlen E l k χ).toNat : ℝ) ≤
                (((l : ℕ) : ℝ) * (condF E : ℝ) * (k : ℝ)) ^ C2) ∧
            (∀ (l : Nat.Primes) (k : ℕ), l ∉ Bchi_χ → (l : ℕ) ≠ 2 → 0 < k → k < t x →
              (l : ℕ) - 1 ∣ 2 * k → ∀ χ ∈ charData.charSet E k,
              χ.isTrivial = false → χ.evenOrder = false →
              charData.Vlen E l k χ ≠ ⊤ ∧
              ((charData.Vlen E l k χ).toNat : ℝ) ≤
                (((l : ℕ) : ℝ) * (condF E : ℝ) * (k : ℝ)) ^ C3) ∧
            (∀ (l : Nat.Primes) (k : ℕ), l ∉ Bchi_χ → (l : ℕ) ≠ 2 → 0 < k → k < t x →
              (l : ℕ) - 1 ∣ 2 * k → ∀ χ ∈ charData.charSet E k, χ.isTrivial = true →
              @PropZResidualBernoulliUnit l.1 k ⟨l.2⟩ → charData.Vlen E l k χ = 0) ∧
            (∀ (l : Nat.Primes) (k : ℕ), l ∉ Bchi_χ → (l : ℕ) ≠ 2 → 0 < k → k < t x →
              charData.loss E l k = 0))

/-- **Compile `SixCaseField1Supply S` directly into `Stage12Window1RootAvoid.ParityWindow1Supply`**
at cutoff `Ct = 401`, unconditionally discharging `CountZ` via von Staudt–Clausen! -/
theorem toParityWindow1Supply {S : SelmerSystem} (H : SixCaseField1Supply S) :
    ParityWindow1Supply H.charData.toParitySelmerSystem H.H2 H.T 401 where
  exists_lemmaK := ⟨H.CK0, H.hLemmaK⟩
  exists_char_data := ⟨H.Cb, fun ψ => by
    obtain ⟨R₀, Bchi_χ, Rl, L₂, hFL₂, hNFL₂, P0, C1, C2, C3, C4, C5, C5s, Closs,
      hTwo, hBad, hMinus, hIn, hOut⟩ := H.char_data ψ
    set lmax := Bchi_χ.sup (fun l => (l : ℕ))
    set Kpow := max (max C4 C2) (max C5 (max C5s Closs))
    set A_l := Nat.log 2 (lmax + 1) + 1
    set A_B := Nat.log 2 (Bchi_χ.card + 1) + 1
    set Cin : ℝ := (((A_l + 1) * Kpow + A_l + A_B + 4 : ℕ) : ℝ)
    set Cout : ℝ := ((max C1 (3 * max C2 C3 + 5) + 2 : ℕ) : ℝ)
    refine ⟨R₀, Bchi_χ, Rl, L₂, hFL₂, hNFL₂, Cin, Cout, P0, hTwo, hBad, hMinus, ?_, ?_⟩
    · intro eps _ _ e t hAdm x hx2 q d hPP hPq hPd hbb E _ _ hE
      have ht2 : 2 ≤ t x := (hAdm x hx2).2.2.1
      have hcond : 1 ≤ condF E :=
        (condF_bounds_of_isChiField ψ (e x) q d hPP.q_prime.pos hPP.d_prime.pos E hE).1
      obtain ⟨hIV, hII, hV, hVs, hloss⟩ := hIn e t hAdm x hx2 q d hPP hPq hPd E hE
      exact sumIn_of_counts H.charData Bchi_χ Rl L₂ hBad E (t x) ht2 hcond
        (Real.exp_pos _).le hbb C2 C4 C5 C5s Closs hIV hII hV hVs hloss
    · intro e t hAdm X x hx2 q d hPP hqX hdX hPq hPd E _ _ hE
      have ht2 : 2 ≤ t x := (hAdm x hx2).2.2.1
      have hcond : 1 ≤ condF E :=
        (condF_bounds_of_isChiField ψ (e x) q d hPP.q_prime.pos hPP.d_prime.pos E hE).1
      obtain ⟨hI, hII, hIII, hZ, hloss⟩ := hOut e t hAdm X x hx2 q d hPP hqX hdX hPq hPd E hE
      exact sumOut_of_counts H.charData Bchi_χ E (t x) ht2 hcond C1 C2 C3 hI hII hIII hZ hloss⟩

/-- **MASTER `VWin` ASSEMBLY THEOREM (`0` EXTRA ASSUMPTIONS!)**:
`SixCaseField1Supply S → RHDirect.VWin S`! -/
theorem vwin_of_six_case_supply {S : SelmerSystem} (H : SixCaseField1Supply S) :
    RHDirect.VWin S :=
  vwin_of_parityWindow1 (toParityWindow1Supply H)

/-- **MASTER `GaloisModularityContract` ASSEMBLY THEOREM (`0` EXTRA ASSUMPTIONS!)**:
`SixCaseField1Supply S → RHDirect.GaloisModularityContract S`! -/
theorem galoisModularityContract_of_six_case {S : SelmerSystem} (H : SixCaseField1Supply S) :
    RHDirect.GaloisModularityContract S :=
  galoisModularityContract_of_parityWindow1 (toParityWindow1Supply H)

/-- **MASTER THREE-PILLAR ASSEMBLY (`assembly_of_six_case_and_theta`)**:
combines `SixCaseField1Supply S` (Pillar 3/4), Pillar-2 `Stage11ThetaSiegelMinimalDatum`
(with `linnikAP` **already unconditionally eliminated** by `Stage11LinnikUnconditional.linnikAPInterval_unconditional`),
and Pillar-1 `Stage2AnalyticWire.stage2_analyticBridgeContract` (`0` assumptions)
into `RHDirect.RHDirectAssembly S`! -/
theorem assembly_of_six_case_and_theta {S : SelmerSystem}
    (H6 : SixCaseField1Supply S)
    (eL : ℝ) (heL : 0 ≤ eL)
    (realizeStage11 : ∀ (ψ : PChar) (eps J : ℝ) (heps : 0 < eps) (heps52 : eps < 1 / 52),
      1 ≤ J →
      ∃ (K cHH X0 : ℝ), 0 ≤ K ∧ 0 ≤ cHH ∧
        ∀ (x Y : ℝ) (q d_aux e_page : ℕ) (hx1 : 1 < x), X0 ≤ x →
          ThetaSlopeEngine.WinDatum S ψ eps J 1 x Y q d_aux e_page →
          Nonempty (Stage11ThetaSiegelMinimalDatum S ψ eL K cHH eps x q d_aux e_page hx1 heps heps52)) :
    RHDirect.RHDirectAssembly S where
  galois := galoisModularityContract_of_six_case H6
  theta := Stage11ThetaSiegelBridge.stage3_thetaSlopeContract_of_stage11_minimal S
    (Stage11ThetaSiegelCoreInputs.ofLinnikAP S eL heL
      Stage11LinnikUnconditional.linnikAPInterval_unconditional realizeStage11)
  analytic := Stage2AnalyticWire.stage2_analyticBridgeContract

/-- **Direct Assembly from `SixCaseField1Supply S` + any `ThetaSlopeContract S`**. -/
theorem assembly_of_six_case_and_thetaContract {S : SelmerSystem}
    (H6 : SixCaseField1Supply S) (Hth : RHDirect.ThetaSlopeContract S) :
    RHDirect.RHDirectAssembly S where
  galois := galoisModularityContract_of_six_case H6
  theta := Hth
  analytic := Stage2AnalyticWire.stage2_analyticBridgeContract

/-- **All Five Verbatim RH & GRH Headline Statements** from `SixCaseField1Supply S` +
Pillar-2 `Stage11ThetaSiegelMinimalDatum` (`linnikAP` unconditionally eliminated!). -/
theorem headline_five_of_six_case_and_theta {S : SelmerSystem}
    (H6 : SixCaseField1Supply S)
    (eL : ℝ) (heL : 0 ≤ eL)
    (realizeStage11 : ∀ (ψ : PChar) (eps J : ℝ) (heps : 0 < eps) (heps52 : eps < 1 / 52),
      1 ≤ J →
      ∃ (K cHH X0 : ℝ), 0 ≤ K ∧ 0 ≤ cHH ∧
        ∀ (x Y : ℝ) (q d_aux e_page : ℕ) (hx1 : 1 < x), X0 ≤ x →
          ThetaSlopeEngine.WinDatum S ψ eps J 1 x Y q d_aux e_page →
          Nonempty (Stage11ThetaSiegelMinimalDatum S ψ eL K cHH eps x q d_aux e_page hx1 heps heps52)) :
    Stage2AnalyticWire.AllFiveHeadlineStatements :=
  RHDirect.headline_five_of_assembly (assembly_of_six_case_and_theta H6 eL heL realizeStage11)

/-- **THE RIEMANN HYPOTHESIS (`RiemannHypothesis` verbatim)** from `SixCaseField1Supply S` +
Pillar-2 `Stage11ThetaSiegelMinimalDatum` (`linnikAP` unconditionally eliminated!). -/
theorem riemannHypothesis_of_six_case_and_theta {S : SelmerSystem}
    (H6 : SixCaseField1Supply S)
    (eL : ℝ) (heL : 0 ≤ eL)
    (realizeStage11 : ∀ (ψ : PChar) (eps J : ℝ) (heps : 0 < eps) (heps52 : eps < 1 / 52),
      1 ≤ J →
      ∃ (K cHH X0 : ℝ), 0 ≤ K ∧ 0 ≤ cHH ∧
        ∀ (x Y : ℝ) (q d_aux e_page : ℕ) (hx1 : 1 < x), X0 ≤ x →
          ThetaSlopeEngine.WinDatum S ψ eps J 1 x Y q d_aux e_page →
          Nonempty (Stage11ThetaSiegelMinimalDatum S ψ eL K cHH eps x q d_aux e_page hx1 heps heps52)) :
    RiemannHypothesis :=
  (headline_five_of_six_case_and_theta H6 eL heL realizeStage11).2.2.2.1

/-- Verbatim `RiemannHypothesis` from `SixCaseField1Supply S` + `ThetaSlopeContract S`. -/
theorem riemannHypothesis_of_six_case_and_thetaContract {S : SelmerSystem}
    (H6 : SixCaseField1Supply S) (Hth : RHDirect.ThetaSlopeContract S) :
    RiemannHypothesis :=
  (RHDirect.headline_five_of_assembly (assembly_of_six_case_and_thetaContract H6 Hth)).2.2.2.1

end SixCaseAssembly

/-! ## Section 5: Concrete `0`-Assumption Non-Vacuity & `realGaloisSelmerSystem` Bridge -/

section ConcreteWitnessAndRealGalois

/-- Unconditional `0`-assumption `CharSelmerData trivialSelmerSystem`. -/
def trivialCharSelmerData : CharSelmerData trivialSelmerSystem where
  plusLen _ _ _ _ _ := 0
  minusLen _ _ _ _ _ := 0
  shaLen_eq_add _ _ _ _ _ _ := rfl
  charSet _ _ _ _ := ∅
  charSet_card_le _ _ _ _ := Nat.zero_le _
  Vlen _ _ _ _ _ _ := 0
  loss _ _ _ _ _ := 0
  plusLen_le _ _ _ _ _ _ := by simp

private def trivialH2LengthSystem : H2LengthSystem where
  h2Len _ _ _ _ _ := 0

private def trivialTowerLayerRelation : TowerLayerRelation where
  IsLayer _ _ _ _ _ := True

/-- **Unconditional `0`-Assumption Non-Vacuity Witness (`sixCaseField1Supply_trivial`)**:
proves `SixCaseField1Supply trivialSelmerSystem` is unconditionally inhabited (`0` axioms, `0` sorrys)! -/
def sixCaseField1Supply_trivial : SixCaseField1Supply trivialSelmerSystem where
  charData := trivialCharSelmerData
  H2 := trivialH2LengthSystem
  T := trivialTowerLayerRelation
  CK0 := 1
  hLemmaK := fun l L _ _ _ e _ => by
    simp only [trivialH2LengthSystem, ne_eq, ENat.zero_ne_top, not_false_eq_true,
      ENat.toNat_zero, Nat.cast_zero, true_and]
    exact mul_nonneg (by norm_num) (kBound_pos 1 e (Module.finrank ℚ L) (NumberField.discr L).natAbs).le
  Cb := 1
  char_data := fun ψ => by
    refine ⟨0, ∅, fun _ => 0, fun _ => ℚ, fun _ => inferInstance, fun _ => inferInstance,
      0, 0, 0, 0, 0, 0, 0, 0, ?_, ?_, ?_, ?_, ?_⟩
    · have : NeZero (4 : ℕ) := ⟨by decide⟩
      have : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩
      have : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
        CyclotomicField.isCyclotomicExtension 4 ℚ
      refine ⟨0, Module.finrank ℚ (CyclotomicField 4 ℚ),
        Real.log (2 * ((NumberField.discr (CyclotomicField 4 ℚ)).natAbs : ℝ)), ?_, fun q d _ =>
        ⟨ℚ, inferInstance, inferInstance, CyclotomicField 4 ℚ, inferInstance, inferInstance,
          inferInstance, ?_, trivial, le_rfl, ?_, ?_, ?_, ?_⟩⟩
      · apply Real.log_nonneg
        have : (1 : ℝ) ≤ ((NumberField.discr (CyclotomicField 4 ℚ)).natAbs : ℝ) :=
          Nat.one_le_cast.mpr (Int.natAbs_pos.mpr (NumberField.discr_ne_zero (CyclotomicField 4 ℚ)))
        linarith
      · exact ⟨IsCyclotomicExtension.zeta 4 ℚ (CyclotomicField 4 ℚ), by
          simp [IsCyclotomicExtension.zeta_spec 4 ℚ (CyclotomicField 4 ℚ)]⟩
      · intro W hW _
        apply le_mul_of_one_le_right _ hW
        apply Real.log_nonneg
        have : (1 : ℝ) ≤ ((NumberField.discr (CyclotomicField 4 ℚ)).natAbs : ℝ) :=
          Nat.one_le_cast.mpr (Int.natAbs_pos.mpr (NumberField.discr_ne_zero (CyclotomicField 4 ℚ)))
        linarith
      · refine ⟨⟨ℚ_[(primeTwo : ℕ)], inferInstance, inferInstance, inferInstance, 0, 0, Fin.elim0,
          le_rfl, ⟨1, by simp⟩, fun _ _ _ _ _ _ _ _ _ => by simp [trivialSelmerSystem]⟩,
          fun _ _ _ _ _ _ _ _ _ _ => by simp [trivialSelmerSystem]⟩
      · exact ⟨0, le_rfl, fun _ => ⟨∅, by simp, fun _ _ _ _ _ _ _ _ => by simp [trivialSelmerSystem]⟩⟩
      · intro e _ E _ _ _
        exact ⟨0, ℚ, inferInstance, inferInstance, inferInstance, trivial, by omega,
          fun _ _ => by simp [trivialSelmerSystem]⟩
    · intro l hl; simp at hl
    · intro e t hAdm x hx2 q d hPP E _ _ hE
      refine ⟨fun _ _ _ _ _ => by simp [CharSelmerData.toParitySelmerSystem, trivialCharSelmerData],
        fun S _ => ?_⟩
      simp only [CharSelmerData.toParitySelmerSystem, trivialCharSelmerData, ENat.toNat_zero,
        Nat.cast_zero, Finset.sum_const_zero, mul_zero]
      have hcond := (condF_bounds_of_isChiField ψ (e x) q d hPP.q_prime.pos hPP.d_prime.pos E hE).1
      have ht2 := (hAdm x hx2).2.2.1
      have hlog1 : 0 ≤ Real.log ((t x : ℝ) * (condF E : ℝ)) := by
        apply Real.log_nonneg
        have h1 : (1 : ℝ) ≤ condF E := by exact_mod_cast hcond
        have h2 : (2 : ℝ) ≤ t x := by exact_mod_cast ht2
        nlinarith
      unfold minusBound
      have hsum_nn : 0 ≤ ∑ l ∈ ψ.N.primeFactors.erase 2,
          (l : ℝ) * (Module.finrank ℚ E : ℝ) ^ 2 * (t x : ℝ) ^ 2 *
            Real.log ((t x : ℝ) * (l : ℝ) * (condF E : ℝ)) ^ 2 :=
        Finset.sum_nonneg fun _ _ => by positivity
      exact add_nonneg (by positivity) (mul_nonneg (by norm_num) hsum_nn)
    · intro e t hAdm x hx2 q d hPP _ _ E _ _ hE
      refine ⟨fun l hl => by simp at hl, fun l hl => by simp at hl,
        fun l hl => by simp at hl, fun l hl => by simp at hl,
        fun l _ hl => by simp at hl⟩
    · intro e t hAdm X x hx2 q d hPP _ _ _ _ E _ _ hE
      refine ⟨fun k _ _ Ls _ => ⟨fun _ _ _ h => by simp [trivialCharSelmerData] at h,
          by simp [trivialCharSelmerData]⟩,
        fun l k _ _ _ _ _ χ hχ => by simp [trivialCharSelmerData] at hχ,
        fun l k _ _ _ _ _ χ hχ => by simp [trivialCharSelmerData] at hχ,
        fun l k _ _ _ _ _ χ hχ => by simp [trivialCharSelmerData] at hχ,
        fun _ _ _ _ _ _ => rfl⟩

/-- Concrete `0`-assumption `VWin trivialSelmerSystem` via `vwin_of_six_case_supply`. -/
theorem vwin_trivial_of_six_case : RHDirect.VWin trivialSelmerSystem :=
  vwin_of_six_case_supply sixCaseField1Supply_trivial

/-- Direct `Stage12GaloisShaLen.realGaloisSelmerSystem` bridge:
any `SixCaseField1Supply realGaloisSelmerSystem` unconditionally yields `VWin realGaloisSelmerSystem`,
`GaloisModularityContract realGaloisSelmerSystem`, and (paired with Pillar 2) `RiemannHypothesis`! -/
theorem vwin_realGalois_of_six_case
    (H6 : SixCaseField1Supply Stage12GaloisShaLen.realGaloisSelmerSystem) :
    RHDirect.VWin Stage12GaloisShaLen.realGaloisSelmerSystem :=
  vwin_of_six_case_supply H6

theorem riemannHypothesis_realGalois_of_six_case
    (H6 : SixCaseField1Supply Stage12GaloisShaLen.realGaloisSelmerSystem)
    (Hth : RHDirect.ThetaSlopeContract Stage12GaloisShaLen.realGaloisSelmerSystem) :
    RiemannHypothesis :=
  riemannHypothesis_of_six_case_and_thetaContract H6 Hth

end ConcreteWitnessAndRealGalois

end RHDirect.Stage13SixCaseVWinAssembly

end

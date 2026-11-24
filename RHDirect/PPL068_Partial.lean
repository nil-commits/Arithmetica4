import Mathlib.Computability.DFA
import Mathlib.Computability.NFA
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# PPL 068 (Shallit Open Problem #14 — Divisibility and Automata): Partial Structural Milestone

**Scope Notice (Partial Milestone — NOT a full resolution of the £50 open problem):**
Shallit's Open Problem #14 (whether it is decidable, given a base-`k` DFA `M` over `Fin k × Fin k`,
if `M` accepts a pair `(x, y)` with `x ∣ y`) remains **OPEN**.
This file formalizes the unconditionally proved structural reductions, bounded-ratio decidability,
exponential-growth collapse, `DLOG-DFA(k)` reduction, and modular barrier theorems documented in
`scripts/ppl068_findings.md`, strictly using pure Mathlib types (`DFA`, `Fin k`, `List`, `padicValNat`,
`ZMod`, etc.) with **`0` custom or `private` definitions in any public theorem signature**:

1. **MSD/LSD Reversal & Exact Prefix–Suffix Split (Section 1):**
   - `ppl068_msd_lsd_reversal_regular`: Every `DFA` language has an effective reversal `DFA`.
   - `ppl068_exact_prefix_suffix_split`: Every accepting divisible pair `(x, y)` with `0 < x` splits
     uniquely at the first nonzero Track-1 digit into an independent prefix `u ∈ U_s` and suffix
     `(x, y_bot) ∈ V_s` with `x ∣ (val_k(u) * k^L + y_bot)`.
2. **Bounded-Ratio / Finite-`U_s` Decidability (Section 2):**
   - `ppl068_bounded_quotient_bound`: Bounding `val_k(u) ≤ U_max` forces `q = y/x < (U_max + 1) * k`.
   - `ppl068_ratio_dfa_automatic`: Explicit `(q + 1)`-state carry DFA `R_q` accepting `(x, y)` iff
     `y = q * x`, plus product DFA `M ∩ R_q` for every fixed `q ≥ 1`.
3. **Exponential-Growth Collapse Theorem in Prime Base `k` (Section 3):**
   - `ppl068_exponential_growth_collapse`: For prime `k` and any exponential-growth SCC of `U_s`
     witnessed by two same-length distinct cycles `w₁ ≠ w₂` at `q`, divisibility collapses to the
     finite-modulus characterization `k^{v_k(x)} ∣ y_bot ∧ gcd(x_cop, |Δ_C|) ∣ (val_k(u) * k^L + y_bot)`
     (both directions `↔`, explicitly constructing the valid pumped word `u'` via Euler's totient and Bézout).
4. **Bounded-Prefix Reduction, `DLOG-DFA(k)` Reduction & Spurious-Divisibility Barrier (Section 4):**
   - `ppl068_bounded_prefix_linear_exp_sum`: Linear exponential-sum identity for bounded loops
     `α₀ β^m α₁` and general `r`-loop bounded languages `α₀ β₁^{n₁} α₁ ⋯ βᵣ^{nᵣ} αᵣ`.
   - `ppl068_dlog_dfa_reduction`: Exact reduction from `DLOG-DFA(k)` (`∃ (x, z) ∈ L(V), ∃ e, k^e ≡ z [MOD x]`)
     to divisibility in a constructed `DFA` `M_V` (via `1 0*` prefix + 2-state MSD borrow subtractor + `NFA.toDFA`).
   - `ppl068_spurious_divisibility_euler_barrier`: Euler-totient pumping showing that for any fixed
     coprime suffix `(x₀, y_bot₀)` whose residue `-y_bot₀` lies in `⟨k⟩ mod x₀`, infinitely many
     loop counts `m` satisfy `x₀ ∣ (k^{L+m} + y_bot₀)`.
-/

namespace PPL068

section MSDBaseAlgebra

private def msdVal (k : ℕ) (w : List (Fin k)) : ℕ :=
  w.foldl (fun acc d => k * acc + d.1) 0

private lemma msdVal_nil (k : ℕ) : msdVal k [] = 0 := rfl

private lemma msdVal_cons (k : ℕ) (d : Fin k) (w : List (Fin k)) :
    msdVal k (d :: w) = d.1 * k ^ w.length + msdVal k w := by
  have hgen : ∀ (a : ℕ) (l : List (Fin k)),
      l.foldl (fun acc x => k * acc + x.1) a = a * k ^ l.length + msdVal k l := by
    intro a l
    induction l generalizing a with
    | nil => simp [msdVal]
    | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih (k * a + x.1)]
      conv_rhs => unfold msdVal; rw [List.foldl_cons, ih (k * 0 + x.1)]
      simp only [Nat.mul_zero, Nat.zero_add, pow_succ']
      ring
  change (d :: w).foldl (fun acc x => k * acc + x.1) 0 = _
  rw [List.foldl_cons, hgen (k * 0 + d.1) w]
  simp

private lemma msdVal_append (k : ℕ) (u v : List (Fin k)) :
    msdVal k (u ++ v) = msdVal k u * k ^ v.length + msdVal k v := by
  induction u with
  | nil => simp [msdVal_nil]
  | cons d ds ih =>
    rw [List.cons_append, msdVal_cons, msdVal_cons, ih, List.length_append, pow_add]
    ring

private lemma msdVal_lt_pow {k : ℕ} (_hk : 1 ≤ k) (w : List (Fin k)) :
    msdVal k w < k ^ w.length := by
  induction w with
  | nil => simp [msdVal_nil]
  | cons d ds ih =>
    rw [msdVal_cons, List.length_cons, pow_succ']
    calc d.1 * k ^ ds.length + msdVal k ds
        < d.1 * k ^ ds.length + k ^ ds.length := Nat.add_lt_add_left ih _
      _ = (d.1 + 1) * k ^ ds.length := by ring
      _ ≤ k * k ^ ds.length := Nat.mul_le_mul_right _ d.2

private lemma msdVal_nonzero_head_ge {k : ℕ} (d : Fin k) (hd : d.1 ≠ 0) (ds : List (Fin k)) :
    k ^ ds.length ≤ msdVal k (d :: ds) := by
  rw [msdVal_cons]
  have hd1 : 1 ≤ d.1 := Nat.one_le_iff_ne_zero.mpr hd
  calc k ^ ds.length = 1 * k ^ ds.length := (one_mul _).symm
    _ ≤ d.1 * k ^ ds.length := Nat.mul_le_mul_right _ hd1
    _ ≤ d.1 * k ^ ds.length + msdVal k ds := Nat.le_add_right _ _

private lemma msdVal_replicate_zero_of_pos {k : ℕ} (hk : 0 < k) (m : ℕ) :
    msdVal k (List.replicate m ⟨0, hk⟩) = 0 := by
  induction m with
  | zero => simp [msdVal_nil]
  | succ m ih =>
    rw [List.replicate_succ, msdVal_cons, ih]
    simp

private lemma msdVal_eq_zero_iff_all_zero {k : ℕ} {w : List (Fin k)} :
    msdVal k w = 0 ↔ ∀ d ∈ w, d.1 = 0 := by
  induction w with
  | nil => simp [msdVal_nil]
  | cons d ds ih =>
    rw [msdVal_cons]
    have hpow : 0 < k ^ ds.length := Nat.pow_pos d.pos
    constructor
    · intro h x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · by_contra hx0
        have h1 : 1 ≤ x.1 := Nat.one_le_iff_ne_zero.mpr hx0
        have hge : k ^ ds.length ≤ x.1 * k ^ ds.length + msdVal k ds :=
          le_trans (by simpa using Nat.mul_le_mul_right (k ^ ds.length) h1) (Nat.le_add_right _ _)
        omega
      · exact ih.mp (by omega) x hx'
    · intro h
      have hd0 : d.1 = 0 := h d List.mem_cons_self
      have hds0 : msdVal k ds = 0 := ih.mpr fun x hx => h x (List.mem_cons_of_mem d hx)
      rw [hd0, hds0]; simp

private lemma msdVal_inj_of_eq_length {k : ℕ} (hk : 1 ≤ k) {u v : List (Fin k)}
    (hlen : u.length = v.length) (hval : msdVal k u = msdVal k v) : u = v := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons a as ih =>
    cases v with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [msdVal_cons, msdVal_cons, hlen] at hval
      have has : msdVal k as < k ^ bs.length := by rw [← hlen]; exact msdVal_lt_pow hk as
      have hbs : msdVal k bs < k ^ bs.length := msdVal_lt_pow hk bs
      have hab : a.1 = b.1 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have : a.1 + 1 ≤ b.1 := hlt
          nlinarith
        · have : b.1 + 1 ≤ a.1 := hgt
          nlinarith
      have htail : msdVal k as = msdVal k bs := by rw [hab] at hval; omega
      rw [Fin.ext hab, ih hlen htail]

private lemma msdVal_append_const_replicate {k : ℕ} (hk : 2 ≤ k) (β : List (Fin k)) (m : ℕ) :
    ((k ^ β.length - 1 : ℕ) : ℤ) * msdVal k (List.replicate m β).flatten =
      (msdVal k β : ℤ) * ((k : ℤ) ^ (m * β.length) - 1) := by
  induction m with
  | zero => simp [msdVal_nil]
  | succ m ih =>
    rw [List.replicate_succ, List.flatten_cons, msdVal_append, List.length_flatten,
      List.map_replicate, List.sum_replicate, smul_eq_mul]
    have hpow_ge : 1 ≤ k ^ β.length := Nat.one_le_pow _ _ (by omega)
    rw [Nat.cast_sub hpow_ge, Nat.cast_pow, Nat.cast_one] at ih ⊢
    push_cast at ih ⊢
    have hid : ((k : ℤ) ^ β.length - 1) *
          ((msdVal k β : ℤ) * (k : ℤ) ^ (m * β.length) +
            (msdVal k (List.replicate m β).flatten : ℤ)) =
        (msdVal k β : ℤ) * ((k : ℤ) ^ β.length - 1) * (k : ℤ) ^ (m * β.length) +
          ((k : ℤ) ^ β.length - 1) * (msdVal k (List.replicate m β).flatten : ℤ) := by ring
    rw [hid, ih, Nat.succ_mul, pow_add]
    ring

private lemma nat_digits_of_lt_pow {k : ℕ} (hk : 1 ≤ k) (L y : ℕ) (hy : y < k ^ L) :
    ∃ ys : List (Fin k), ys.length = L ∧ msdVal k ys = y := by
  induction L generalizing y with
  | zero =>
    have hy0 : y = 0 := by simpa using hy
    subst hy0
    exact ⟨[], rfl, rfl⟩
  | succ L ih =>
    have hk0 : 0 < k := by omega
    have hpow_pos : 0 < k ^ L := Nat.pow_pos hk0
    have hy_div : y / k ^ L < k := by
      rw [Nat.div_lt_iff_lt_mul hpow_pos]
      simpa [pow_succ'] using hy
    have hy_mod : y % k ^ L < k ^ L := Nat.mod_lt y hpow_pos
    obtain ⟨ys, hlen, hval⟩ := ih (y % k ^ L) hy_mod
    refine ⟨⟨y / k ^ L, hy_div⟩ :: ys, by simp [hlen], ?_⟩
    rw [msdVal_cons, hlen, hval]
    exact Nat.div_add_mod' y (k ^ L)

/-- Theorem 1a (MSD / LSD Reversal Regularity):
Every `DFA α Q` has a reversal `DFA α (Set Q)` accepting `w.reverse` iff `w ∈ M.accepts`
(so MSD-first and LSD-first representations are effectively equivalent). -/
theorem ppl068_msd_lsd_reversal_regular {α Q : Type*} (M : DFA α Q) :
    ∃ M_rev : DFA α (Set Q), ∀ w : List α, w ∈ M_rev.accepts ↔ w.reverse ∈ M.accepts := by
  classical
  let N : NFA α Q :=
    { step := fun s a => { q | M.step q a = s }
      start := M.accept
      accept := { M.start } }
  refine ⟨N.toDFA, fun w => ?_⟩
  rw [NFA.toDFA_correct]
  have hN_append : ∀ (S : Set Q) (u v : List α),
      N.evalFrom S (u ++ v) = N.evalFrom (N.evalFrom S u) v := by
    intro S u v
    induction u generalizing S with
    | nil => rfl
    | cons a as ih => rw [List.cons_append, NFA.evalFrom_cons, NFA.evalFrom_cons, ih]
  have heval : ∀ (l : List α) (q_start : Q) (S : Set Q),
      M.evalFrom q_start l ∈ S ↔ q_start ∈ N.evalFrom S l.reverse := by
    intro l
    induction l with
    | nil =>
      intro q_start S
      simp [NFA.evalFrom_nil]
    | cons a as ih =>
      intro q_start S
      rw [DFA.evalFrom_cons, List.reverse_cons, hN_append,
        NFA.evalFrom_cons, NFA.evalFrom_nil, NFA.mem_stepSet]
      rw [ih (M.step q_start a) S]
      constructor
      · intro h
        exact ⟨M.step q_start a, h, rfl⟩
      · rintro ⟨s, hs, hstep⟩
        change M.step q_start a = s at hstep
        rwa [hstep]
  rw [DFA.mem_accepts, DFA.eval, heval w.reverse M.start M.accept, List.reverse_reverse,
    NFA.mem_accepts]
  change (∃ q ∈ N.accept, q ∈ N.evalFrom N.start w) ↔ M.start ∈ N.evalFrom M.accept w
  dsimp [N]
  constructor
  · rintro ⟨q, hq, hq'⟩
    simp only [Set.mem_singleton_iff] at hq
    rwa [← hq]
  · intro h
    exact ⟨M.start, rfl, h⟩

/-- Theorem 1b (Exact Prefix–Suffix Split):
For any `k ≥ 2` and `M : DFA (Fin k × Fin k) Q`, an accepting run on `(x, y)` with `0 < x`
splits uniquely at the first nonzero Track-1 digit into a Track-1-zero prefix `u ∈ U_s` and a
nonzero-head suffix `(x, y_bot) ∈ V_s` of length `L = v'.length + 1`, giving `x ∣ (val_k(u) * k^L + y_bot)`. -/
theorem ppl068_exact_prefix_suffix_split {k : ℕ} (hk : 2 ≤ k) {Q : Type*}
    (M : DFA (Fin k × Fin k) Q) :
    (∃ w ∈ M.accepts,
        0 < (w.map Prod.fst).foldl (fun acc d => k * acc + d.1) 0 ∧
        (w.map Prod.fst).foldl (fun acc d => k * acc + d.1) 0 ∣
          (w.map Prod.snd).foldl (fun acc d => k * acc + d.1) 0) ↔
      ∃ s : Q, ∃ u : List (Fin k), ∃ p₀ : Fin k × Fin k, ∃ v' : List (Fin k × Fin k),
        M.eval (u.map fun d => (⟨0, by omega⟩, d)) = s ∧
        p₀.1.1 ≠ 0 ∧
        M.evalFrom s (p₀ :: v') ∈ M.accept ∧
        k ^ v'.length ≤ ((p₀ :: v').map Prod.fst).foldl (fun acc d => k * acc + d.1) 0 ∧
        ((p₀ :: v').map Prod.fst).foldl (fun acc d => k * acc + d.1) 0 < k ^ (v'.length + 1) ∧
        ((p₀ :: v').map Prod.snd).foldl (fun acc d => k * acc + d.1) 0 < k ^ (v'.length + 1) ∧
        ((p₀ :: v').map Prod.fst).foldl (fun acc d => k * acc + d.1) 0 ∣
          (u.foldl (fun acc d => k * acc + d.1) 0 * k ^ (v'.length + 1) +
            ((p₀ :: v').map Prod.snd).foldl (fun acc d => k * acc + d.1) 0) := by
  have hk0 : 0 < k := by omega
  have hsplit_aux : ∀ w : List (Fin k × Fin k),
      0 < msdVal k (w.map Prod.fst) →
      ∃ u : List (Fin k), ∃ p₀ : Fin k × Fin k, ∃ v' : List (Fin k × Fin k),
        p₀.1.1 ≠ 0 ∧ w = u.map (fun d => (⟨0, hk0⟩, d)) ++ (p₀ :: v') := by
    intro w hw
    induction w with
    | nil => simp [msdVal_nil] at hw
    | cons a as ih =>
      by_cases ha : a.1.1 = 0
      · have has : 0 < msdVal k (as.map Prod.fst) := by
          rw [List.map_cons, msdVal_cons, ha, zero_mul, zero_add] at hw
          exact hw
        obtain ⟨u, p₀, v', hp₀, hweq⟩ := ih has
        refine ⟨a.2 :: u, p₀, v', hp₀, ?_⟩
        rw [List.map_cons, List.cons_append, ← hweq]
        congr 1
        ext <;> simp [ha]
      · exact ⟨[], a, as, ha, by simp⟩
  constructor
  · rintro ⟨w, hw_acc, hx_pos, hdvd⟩
    obtain ⟨u, p₀, v', hp₀, rfl⟩ := hsplit_aux w hx_pos
    set s := M.eval (u.map fun d => (⟨0, hk0⟩, d))
    have hacc : M.evalFrom s (p₀ :: v') ∈ M.accept := by
      rw [DFA.mem_accepts, DFA.eval, DFA.evalFrom_of_append] at hw_acc
      exact hw_acc
    have hfst_u : msdVal k ((u.map fun d => ((⟨0, hk0⟩ : Fin k), d)).map Prod.fst) = 0 := by
      rw [msdVal_eq_zero_iff_all_zero]
      intro d hd
      rcases List.mem_map.mp hd with ⟨p, hp, rfl⟩
      rcases List.mem_map.mp hp with ⟨_, _, rfl⟩
      rfl
    have hfst_eq : msdVal k ((u.map (fun d => ((⟨0, hk0⟩ : Fin k), d)) ++ (p₀ :: v')).map Prod.fst) =
        msdVal k ((p₀ :: v').map Prod.fst) := by
      rw [List.map_append, msdVal_append, hfst_u, zero_mul, zero_add]
    have hsnd_u : (u.map fun d => ((⟨0, hk0⟩ : Fin k), d)).map Prod.snd = u := by
      rw [List.map_map]; simp
    have hsnd_eq : msdVal k ((u.map (fun d => ((⟨0, hk0⟩ : Fin k), d)) ++ (p₀ :: v')).map Prod.snd) =
        msdVal k u * k ^ (v'.length + 1) + msdVal k ((p₀ :: v').map Prod.snd) := by
      rw [List.map_append, msdVal_append, hsnd_u, List.length_map, List.length_cons]
    refine ⟨s, u, p₀, v', rfl, hp₀, hacc, ?_, ?_, ?_, ?_⟩
    · change k ^ v'.length ≤ msdVal k ((p₀ :: v').map Prod.fst)
      simpa [List.map_cons, List.length_map] using
        msdVal_nonzero_head_ge p₀.1 hp₀ (v'.map Prod.fst)
    · change msdVal k ((p₀ :: v').map Prod.fst) < k ^ (v'.length + 1)
      simpa [List.length_map, List.length_cons] using
        msdVal_lt_pow (by omega) ((p₀ :: v').map Prod.fst)
    · change msdVal k ((p₀ :: v').map Prod.snd) < k ^ (v'.length + 1)
      simpa [List.length_map, List.length_cons] using
        msdVal_lt_pow (by omega) ((p₀ :: v').map Prod.snd)
    · change msdVal k ((p₀ :: v').map Prod.fst) ∣
        msdVal k u * k ^ (v'.length + 1) + msdVal k ((p₀ :: v').map Prod.snd)
      rw [← hfst_eq, ← hsnd_eq]
      exact hdvd
  · rintro ⟨s, u, p₀, v', heval, hp₀, hacc, hx_ge, _, _, hdvd⟩
    refine ⟨u.map (fun d => (⟨0, hk0⟩, d)) ++ (p₀ :: v'), ?_, ?_, ?_⟩
    · rw [DFA.mem_accepts, DFA.eval, DFA.evalFrom_of_append, ← DFA.eval, heval]
      exact hacc
    · have hfst_u : msdVal k ((u.map fun d => ((⟨0, hk0⟩ : Fin k), d)).map Prod.fst) = 0 := by
        rw [msdVal_eq_zero_iff_all_zero]
        intro d hd
        rcases List.mem_map.mp hd with ⟨p, hp, rfl⟩
        rcases List.mem_map.mp hp with ⟨_, _, rfl⟩
        rfl
      change 0 < msdVal k ((u.map (fun d => ((⟨0, hk0⟩ : Fin k), d)) ++ (p₀ :: v')).map Prod.fst)
      rw [List.map_append, msdVal_append, hfst_u, zero_mul, zero_add]
      have hpow : 0 < k ^ v'.length := Nat.pow_pos hk0
      change k ^ v'.length ≤ msdVal k ((p₀ :: v').map Prod.fst) at hx_ge
      linarith
    · have hfst_u : msdVal k ((u.map fun d => ((⟨0, hk0⟩ : Fin k), d)).map Prod.fst) = 0 := by
        rw [msdVal_eq_zero_iff_all_zero]
        intro d hd
        rcases List.mem_map.mp hd with ⟨p, hp, rfl⟩
        rcases List.mem_map.mp hp with ⟨_, _, rfl⟩
        rfl
      have hsnd_u : (u.map fun d => ((⟨0, hk0⟩ : Fin k), d)).map Prod.snd = u := by
        rw [List.map_map]; simp
      change msdVal k ((u.map (fun d => ((⟨0, hk0⟩ : Fin k), d)) ++ (p₀ :: v')).map Prod.fst) ∣
        msdVal k ((u.map (fun d => ((⟨0, hk0⟩ : Fin k), d)) ++ (p₀ :: v')).map Prod.snd)
      rw [List.map_append, msdVal_append, hfst_u, zero_mul, zero_add,
        List.map_append, msdVal_append, hsnd_u, List.length_map, List.length_cons]
      exact hdvd

end MSDBaseAlgebra

section BoundedRatioDecidability

/-- Theorem 2a (Bounded-Quotient Upper Bound for Finite `U_s`):
Whenever `val_k(u) ≤ U_max` and `(p₀ :: v')` has nonzero Track-1 head (`p₀.1.1 ≠ 0`), any
integer quotient `q` with `q * x = val_k(u) * k^(v'.length + 1) + y_bot` satisfies `q < (U_max + 1) * k`. -/
theorem ppl068_bounded_quotient_bound {k U_max q : ℕ} (hk : 2 ≤ k)
    (u : List (Fin k)) (hu : u.foldl (fun acc d => k * acc + d.1) 0 ≤ U_max)
    (p₀ : Fin k × Fin k) (v' : List (Fin k × Fin k)) (hp₀ : p₀.1.1 ≠ 0)
    (hq : q * ((p₀ :: v').map Prod.fst).foldl (fun acc d => k * acc + d.1) 0 =
      u.foldl (fun acc d => k * acc + d.1) 0 * k ^ (v'.length + 1) +
        ((p₀ :: v').map Prod.snd).foldl (fun acc d => k * acc + d.1) 0) :
    q < (U_max + 1) * k := by
  have hx_ge : k ^ v'.length ≤ msdVal k ((p₀ :: v').map Prod.fst) := by
    simpa [List.map_cons, List.length_map] using
      msdVal_nonzero_head_ge p₀.1 hp₀ (v'.map Prod.fst)
  have hy_lt : msdVal k ((p₀ :: v').map Prod.snd) < k ^ (v'.length + 1) := by
    simpa [List.length_map, List.length_cons] using
      msdVal_lt_pow (by omega) ((p₀ :: v').map Prod.snd)
  have hpow_pos : 0 < k ^ v'.length := Nat.pow_pos (by omega)
  have h1 : q * k ^ v'.length ≤ q * msdVal k ((p₀ :: v').map Prod.fst) :=
    Nat.mul_le_mul_left q hx_ge
  have h2 : msdVal k u * k ^ (v'.length + 1) + msdVal k ((p₀ :: v').map Prod.snd) <
      (U_max + 1) * k * k ^ v'.length := by
    calc msdVal k u * k ^ (v'.length + 1) + msdVal k ((p₀ :: v').map Prod.snd)
        < U_max * k ^ (v'.length + 1) + k ^ (v'.length + 1) := by
          have hmul : msdVal k u * k ^ (v'.length + 1) ≤ U_max * k ^ (v'.length + 1) :=
            Nat.mul_le_mul_right _ hu
          linarith
      _ = (U_max + 1) * k * k ^ v'.length := by rw [pow_succ]; ring
  have hq' : q * msdVal k ((p₀ :: v').map Prod.fst) =
      msdVal k u * k ^ (v'.length + 1) + msdVal k ((p₀ :: v').map Prod.snd) := hq
  have hmul_lt : q * k ^ v'.length < (U_max + 1) * k * k ^ v'.length := by linarith
  exact Nat.lt_of_mul_lt_mul_right hmul_lt

/-- Theorem 2b (`R_q = {(x, y) : y = q * x}` Is `k`-Automatic via a `(q + 1)`-State Carry DFA):
For every base `k ≥ 2` and quotient `q ≥ 1`, there exists an explicit `(q + 1)`-state DFA
`R_q : DFA (Fin k × Fin k) (Option (Fin q))` accepting `w` iff `val_k(snd w) = q * val_k(fst w)`,
and for any `M : DFA (Fin k × Fin k) Q`, their product DFA accepts `M.accepts ∩ R_q.accepts`. -/
theorem ppl068_ratio_dfa_automatic {k q : ℕ} (hk : 2 ≤ k) (hq : 1 ≤ q) :
    ∃ R_q : DFA (Fin k × Fin k) (Option (Fin q)),
      (∀ w : List (Fin k × Fin k),
        w ∈ R_q.accepts ↔
          (w.map Prod.snd).foldl (fun acc d => k * acc + d.1) 0 =
            q * (w.map Prod.fst).foldl (fun acc d => k * acc + d.1) 0) ∧
      (∀ {Q : Type*} (M : DFA (Fin k × Fin k) Q),
        ∃ M_int : DFA (Fin k × Fin k) (Q × Option (Fin q)),
          ∀ w : List (Fin k × Fin k),
            w ∈ M_int.accepts ↔
              w ∈ M.accepts ∧
              (w.map Prod.snd).foldl (fun acc d => k * acc + d.1) 0 =
                q * (w.map Prod.fst).foldl (fun acc d => k * acc + d.1) 0) := by
  let stepFn : Option (Fin q) → Fin k × Fin k → Option (Fin q)
    | none, _ => none
    | some d, (a, b) =>
      let v : ℤ := (k : ℤ) * (d.1 : ℤ) + (b.1 : ℤ) - (q : ℤ) * (a.1 : ℤ)
      if h : 0 ≤ v ∧ v < q then some ⟨v.toNat, by omega⟩ else none
  let R_q : DFA (Fin k × Fin k) (Option (Fin q)) :=
    { step := stepFn
      start := some ⟨0, hq⟩
      accept := { some ⟨0, hq⟩ } }
  have hsound : ∀ (w : List (Fin k × Fin k)) (d₀ d₁ : Fin q),
      R_q.evalFrom (some d₀) w = some d₁ →
      (msdVal k (w.map Prod.snd) : ℤ) + (d₀.1 : ℤ) * (k : ℤ) ^ w.length =
        (q : ℤ) * (msdVal k (w.map Prod.fst) : ℤ) + (d₁.1 : ℤ) := by
    intro w
    induction w with
    | nil =>
      intro d₀ d₁ heval
      simp only [DFA.evalFrom_nil, Option.some.injEq] at heval
      subst heval
      simp [msdVal_nil]
    | cons p ps ih =>
      intro d₀ d₁ heval
      rw [DFA.evalFrom_cons] at heval
      cases hstep : R_q.step (some d₀) p with
      | none =>
        have hnone : ∀ l : List (Fin k × Fin k), R_q.evalFrom none l = none := fun l => by
          induction l with
          | nil => rfl
          | cons _ _ ih' => exact ih'
        rw [hstep, hnone] at heval
        cases heval
      | some d_mid =>
        rw [hstep] at heval
        have ih' := ih d_mid d₁ heval
        have hstep' : stepFn (some d₀) p = some d_mid := hstep
        rcases p with ⟨a, b⟩
        dsimp [stepFn] at hstep'
        split_ifs at hstep' with hv
        · obtain ⟨h0, hlt⟩ := hv
          have hdmid : (d_mid.1 : ℤ) = (k : ℤ) * (d₀.1 : ℤ) + (b.1 : ℤ) - (q : ℤ) * (a.1 : ℤ) := by
            have := Option.some.inj hstep'
            subst this
            simp only [Int.toNat_of_nonneg h0]
          rw [List.map_cons, List.map_cons, msdVal_cons, msdVal_cons, List.length_cons,
            List.length_map, List.length_map]
          push_cast
          rw [pow_succ']
          rw [hdmid] at ih'
          linarith
  have hcomplete : ∀ (w : List (Fin k × Fin k)) (d₀ : Fin q),
      (msdVal k (w.map Prod.snd) : ℤ) + (d₀.1 : ℤ) * (k : ℤ) ^ w.length =
        (q : ℤ) * (msdVal k (w.map Prod.fst) : ℤ) →
      R_q.evalFrom (some d₀) w = some ⟨0, hq⟩ := by
    intro w
    induction w with
    | nil =>
      intro d₀ h
      simp only [msdVal_nil, List.map_nil, List.length_nil, pow_zero, mul_one,
        CharP.cast_eq_zero, zero_add, mul_zero] at h
      have hd0 : d₀ = ⟨0, hq⟩ := Fin.ext (by exact_mod_cast h)
      subst hd0
      rfl
    | cons p ps ih =>
      intro d₀ h
      rcases p with ⟨a, b⟩
      rw [List.map_cons, List.map_cons, msdVal_cons, msdVal_cons, List.length_cons,
        List.length_map, List.length_map] at h
      set d_val : ℤ := (k : ℤ) * (d₀.1 : ℤ) + (b.1 : ℤ) - (q : ℤ) * (a.1 : ℤ)
      have hid : (msdVal k (ps.map Prod.snd) : ℤ) + d_val * (k : ℤ) ^ ps.length =
          (q : ℤ) * (msdVal k (ps.map Prod.fst) : ℤ) := by
        push_cast at h
        rw [pow_succ'] at h
        dsimp [d_val]
        linarith
      have hx_lt : (msdVal k (ps.map Prod.fst) : ℤ) < (k : ℤ) ^ ps.length := by
        have := msdVal_lt_pow (by omega : 1 ≤ k) (ps.map Prod.fst)
        rw [List.length_map] at this
        exact_mod_cast this
      have hy_lt : (msdVal k (ps.map Prod.snd) : ℤ) < (k : ℤ) ^ ps.length := by
        have := msdVal_lt_pow (by omega : 1 ≤ k) (ps.map Prod.snd)
        rw [List.length_map] at this
        exact_mod_cast this
      have hpow_pos : (0 : ℤ) < (k : ℤ) ^ ps.length := by positivity
      have hd_mul_ge : -(k : ℤ) ^ ps.length < d_val * (k : ℤ) ^ ps.length := by
        have hx0 : (0 : ℤ) ≤ msdVal k (ps.map Prod.fst) := by positivity
        have hq0 : (0 : ℤ) ≤ q := by positivity
        have hqx0 : (0 : ℤ) ≤ (q : ℤ) * msdVal k (ps.map Prod.fst) := mul_nonneg hq0 hx0
        linarith
      have hd_mul_lt : d_val * (k : ℤ) ^ ps.length < (q : ℤ) * (k : ℤ) ^ ps.length := by
        have hy0 : (0 : ℤ) ≤ msdVal k (ps.map Prod.snd) := by positivity
        have hq1 : (q : ℤ) * (msdVal k (ps.map Prod.fst) : ℤ) ≤ (q : ℤ) * ((k : ℤ) ^ ps.length - 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        have hq_pos : (0 : ℤ) < q := by exact_mod_cast hq
        linarith
      have hd_ge0 : 0 ≤ d_val := by
        by_contra hneg
        push Not at hneg
        have hle : d_val ≤ -1 := by omega
        have hmul_le : d_val * (k : ℤ) ^ ps.length ≤ (-1) * (k : ℤ) ^ ps.length :=
          mul_le_mul_of_nonneg_right hle hpow_pos.le
        linarith
      have hd_ltq : d_val < q := by
        by_contra hge
        push Not at hge
        have hmul_ge : (q : ℤ) * (k : ℤ) ^ ps.length ≤ d_val * (k : ℤ) ^ ps.length :=
          mul_le_mul_of_nonneg_right hge hpow_pos.le
        linarith
      rw [DFA.evalFrom_cons]
      have hstep : R_q.step (some d₀) (a, b) = some ⟨d_val.toNat, by omega⟩ := by
        change stepFn (some d₀) (a, b) = _
        dsimp [stepFn]
        rw [dif_pos ⟨hd_ge0, hd_ltq⟩]
      rw [hstep]
      apply ih
      simpa [Int.toNat_of_nonneg hd_ge0] using hid
  have hiff : ∀ w : List (Fin k × Fin k),
      w ∈ R_q.accepts ↔
        (w.map Prod.snd).foldl (fun acc d => k * acc + d.1) 0 =
          q * (w.map Prod.fst).foldl (fun acc d => k * acc + d.1) 0 := by
    intro w
    rw [DFA.mem_accepts, DFA.eval]
    change R_q.evalFrom (some ⟨0, hq⟩) w ∈ ({some ⟨0, hq⟩} : Set (Option (Fin q))) ↔ _
    rw [Set.mem_singleton_iff]
    constructor
    · intro h
      have hs := hsound w ⟨0, hq⟩ ⟨0, hq⟩ h
      simp only [Nat.cast_zero, zero_mul, add_zero] at hs
      exact_mod_cast hs
    · intro heq
      apply hcomplete w ⟨0, hq⟩
      simp only [Nat.cast_zero, zero_mul, add_zero]
      exact_mod_cast heq
  refine ⟨R_q, hiff, fun {Q} M => ?_⟩
  let M_int : DFA (Fin k × Fin k) (Q × Option (Fin q)) :=
    { step := fun sq a => (M.step sq.1 a, R_q.step sq.2 a)
      start := (M.start, R_q.start)
      accept := M.accept ×ˢ R_q.accept }
  have heval_prod : ∀ (s : Q) (r : Option (Fin q)) (w : List (Fin k × Fin k)),
      M_int.evalFrom (s, r) w = (M.evalFrom s w, R_q.evalFrom r w) := fun s r w => by
    induction w generalizing s r with
    | nil => rfl
    | cons a as ih =>
      simp only [DFA.evalFrom_cons]
      exact ih (M.step s a) (R_q.step r a)
  refine ⟨M_int, fun w => ?_⟩
  rw [DFA.mem_accepts, DFA.eval, heval_prod, Set.mem_prod, ← DFA.eval, ← DFA.eval,
    ← DFA.mem_accepts, ← DFA.mem_accepts, hiff w]

end BoundedRatioDecidability

section PrimeBaseExponentialCollapse

private lemma msdVal_map_loop_eval {k : ℕ} {Q : Type*} (M : DFA (Fin k × Fin k) Q)
    (hk : 0 < k) (q : Q) (w : List (Fin k))
    (hw : M.evalFrom q (w.map fun d => (⟨0, hk⟩, d)) = q) (t : ℕ) :
    M.evalFrom q ((List.replicate t w).flatten.map fun d => (⟨0, hk⟩, d)) = q := by
  induction t with
  | zero => simp [DFA.evalFrom_nil]
  | succ t ih =>
    rw [List.replicate_succ, List.flatten_cons, List.map_append, DFA.evalFrom_of_append, hw, ih]

private lemma msdVal_list_blocks_eval {k : ℕ} {Q : Type*} (M : DFA (Fin k × Fin k) Q)
    (hk : 0 < k) (q : Q) (w₁ w₂ : List (Fin k))
    (hw₁ : M.evalFrom q (w₁.map fun d => (⟨0, hk⟩, d)) = q)
    (hw₂ : M.evalFrom q (w₂.map fun d => (⟨0, hk⟩, d)) = q)
    (blocks : List (List (Fin k)))
    (hb : ∀ z ∈ blocks, z = w₁ ∨ z = w₂) :
    M.evalFrom q (blocks.flatten.map fun d => (⟨0, hk⟩, d)) = q := by
  induction blocks with
  | nil => simp [DFA.evalFrom_nil]
  | cons z zs ih =>
    rw [List.flatten_cons, List.map_append, DFA.evalFrom_of_append]
    have hz : M.evalFrom q (z.map fun d => (⟨0, hk⟩, d)) = q := by
      rcases hb z List.mem_cons_self with rfl | rfl <;> assumption
    rw [hz]
    exact ih fun z' hz' => hb z' (List.mem_cons_of_mem z hz')

private lemma msdVal_zlist_diff {k p : ℕ} (w₁ w₂ : List (Fin k))
    (hp₁ : w₁.length = p) (hp₂ : w₂.length = p) (t : ℕ) (S : Finset ℕ) (hS : ∀ r ∈ S, r < t) :
    let blocks : List (List (Fin k)) :=
      List.ofFn (fun i : Fin t => if (t - 1 - i.1) ∈ S then w₂ else w₁)
    (msdVal k blocks.flatten : ℤ) - (msdVal k (List.replicate t w₁).flatten : ℤ) =
      ((msdVal k w₂ : ℤ) - (msdVal k w₁ : ℤ)) * ∑ r ∈ S, (k : ℤ) ^ (r * p) := by
  intro blocks
  have hgen : ∀ (m : ℕ) (Sm : Finset ℕ) (_hSm : ∀ r ∈ Sm, r < m),
      (msdVal k (List.ofFn (fun i : Fin m => if (m - 1 - i.1) ∈ Sm then w₂ else w₁)).flatten : ℤ) -
        (msdVal k (List.replicate m w₁).flatten : ℤ) =
      ((msdVal k w₂ : ℤ) - (msdVal k w₁ : ℤ)) * ∑ r ∈ Sm, (k : ℤ) ^ (r * p) := by
    intro m
    induction m with
    | zero =>
      intro Sm hSm
      have hempty : Sm = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun r hr => by
        have := hSm r hr; omega
      subst hempty
      simp [msdVal_nil]
    | succ m ih =>
      intro Sm hSm
      let Sm' : Finset ℕ := Sm.filter (fun r => r < m)
      have hSm'_sub : ∀ r ∈ Sm', r < m := fun r hr => (Finset.mem_filter.mp hr).2
      have hlen_tail : (List.ofFn (fun i : Fin m =>
          if (m - 1 - i.1) ∈ Sm' then w₂ else w₁)).flatten.length = m * p := by
        rw [List.length_flatten, List.map_ofFn]
        have hlen_fn : ∀ i : Fin m, (if (m - 1 - i.1) ∈ Sm' then w₂ else w₁).length = p := by
          intro i; split_ifs <;> assumption
        simp_rw [Function.comp_def, hlen_fn, List.sum_ofFn, Finset.sum_const, Finset.card_fin,
          smul_eq_mul]
      have hlen_rep : (List.replicate m w₁).flatten.length = m * p := by
        rw [List.length_flatten, List.map_replicate, List.sum_replicate, smul_eq_mul, hp₁]
      have hofFn_succ :
          List.ofFn (fun i : Fin (m + 1) => if (m + 1 - 1 - i.1) ∈ Sm then w₂ else w₁) =
          (if m ∈ Sm then w₂ else w₁) ::
            List.ofFn (fun i : Fin m => if (m - 1 - i.1) ∈ Sm' then w₂ else w₁) := by
        rw [List.ofFn_succ]
        refine congrArg₂ List.cons ?_ (congrArg List.ofFn (funext fun i => ?_))
        · simp
        · have hi : i.1 < m := i.2
          have heq1 : m + 1 - 1 - (i.1 + 1) = m - 1 - i.1 := by omega
          have hlt_m : m - 1 - i.1 < m := by omega
          simp only [Fin.val_succ, heq1, Sm', Finset.mem_filter, hlt_m, and_true]
      rw [hofFn_succ, List.flatten_cons, List.replicate_succ, List.flatten_cons,
        msdVal_append, msdVal_append, hlen_tail, hlen_rep]
      have ih_m := ih Sm' hSm'_sub
      by_cases hm_mem : m ∈ Sm
      · have hSm_eq : Sm = insert m Sm' := by
          ext r; simp only [Finset.mem_insert, Sm', Finset.mem_filter]
          constructor
          · intro hr
            have hrm := hSm r hr
            rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hrm) with hlt | rfl
            · exact Or.inr ⟨hr, hlt⟩
            · exact Or.inl rfl
          · rintro (rfl | ⟨hr, _⟩) <;> assumption
        have hm_not : m ∉ Sm' := fun h => by
          rw [Finset.mem_filter] at h; omega
        rw [if_pos hm_mem]
        push_cast
        have hsum_split : ∑ r ∈ Sm, (k : ℤ) ^ (r * p) =
            (k : ℤ) ^ (m * p) + ∑ r ∈ Sm', (k : ℤ) ^ (r * p) := by
          rw [hSm_eq, Finset.sum_insert hm_not]
        rw [hsum_split]
        linarith
      · have hSm_eq : Sm = Sm' := by
          ext r; simp only [Sm', Finset.mem_filter]
          constructor
          · intro hr
            refine ⟨hr, ?_⟩
            have hrm := hSm r hr
            exact lt_of_le_of_ne (Nat.lt_succ_iff.mp hrm) (fun h => hm_mem (h ▸ hr))
          · exact fun h => h.1
        rw [if_neg hm_mem, hSm_eq]
        push_cast
        linarith
  exact hgen t S hS

/-- Theorem 3 (Exponential-Growth Collapse Theorem in Prime Base `k`):
Let `k` be prime, `M : DFA (Fin k × Fin k) Q`, and suppose an SCC of `U_s` contains a state `q`
reached from `q_start` by `α`, returning to `s` by `γ`, with two equal-length distinct cycles
`w₁ ≠ w₂` at `q` (`Δ_C = val_k(w₂) - val_k(w₁) ≠ 0`). For any `(x, y_bot)` with `0 < x < k^L`
(`x = k^v * x_cop`, `v = padicValNat k x`, `¬ k ∣ x_cop`, `g = gcd x_cop |Δ_C|`):
1. `Δ_C ≠ 0` (`g ∣ |Δ_C|`),
2. (`→`) If `x ∣ (val_k(α ++ γ) * k^L + y_bot)`, then `k^v ∣ y_bot ∧ g ∣ (val_k(α ++ γ) * k^L + y_bot)`,
3. (`←`) Conversely, if `k^v ∣ y_bot ∧ g ∣ (val_k(α ++ γ) * k^L + y_bot)`, there exists a valid
   pumped word `u' : List (Fin k)` reaching `s` (`M.evalFrom q_start (u'.map (0, ·)) = s`) with
   `x ∣ (val_k(u') * k^L + y_bot)`. -/
theorem ppl068_exponential_growth_collapse {k : ℕ} (hk : Nat.Prime k) {Q : Type*}
    (M : DFA (Fin k × Fin k) Q) (q_start q s : Q) (α γ w₁ w₂ : List (Fin k))
    (hlen : w₁.length = w₂.length) (hne : w₁ ≠ w₂)
    (hα : M.evalFrom q_start (α.map fun d => (⟨0, hk.pos⟩, d)) = q)
    (hw₁ : M.evalFrom q (w₁.map fun d => (⟨0, hk.pos⟩, d)) = q)
    (hw₂ : M.evalFrom q (w₂.map fun d => (⟨0, hk.pos⟩, d)) = q)
    (hγ : M.evalFrom q (γ.map fun d => (⟨0, hk.pos⟩, d)) = s)
    {L x y_bot : ℕ} (hx_pos : 0 < x) (hx_lt : x < k ^ L) :
    let v := padicValNat k x
    let x_cop := x / k ^ v
    let Δ : ℤ := ((w₂.foldl (fun acc d => k * acc + d.1) 0 : ℕ) : ℤ) -
      ((w₁.foldl (fun acc d => k * acc + d.1) 0 : ℕ) : ℤ)
    let g := Nat.gcd x_cop Δ.natAbs
    Δ ≠ 0 ∧
    (x = k ^ v * x_cop ∧ ¬ k ∣ x_cop ∧ v < L) ∧
    (x ∣ (α ++ γ).foldl (fun acc d => k * acc + d.1) 0 * k ^ L + y_bot →
      k ^ v ∣ y_bot ∧
      g ∣ (α ++ γ).foldl (fun acc d => k * acc + d.1) 0 * k ^ L + y_bot) ∧
    (k ^ v ∣ y_bot →
      g ∣ (α ++ γ).foldl (fun acc d => k * acc + d.1) 0 * k ^ L + y_bot →
      ∃ u' : List (Fin k),
        M.evalFrom q_start (u'.map fun d => (⟨0, hk.pos⟩, d)) = s ∧
        x ∣ u'.foldl (fun acc d => k * acc + d.1) 0 * k ^ L + y_bot) := by
  intro v x_cop Δ g
  have hk2 : 2 ≤ k := hk.two_le
  have hk1 : 1 ≤ k := by omega
  let _ : Fact (Nat.Prime k) := ⟨hk⟩
  have hΔ_ne : Δ ≠ 0 := by
    intro h0
    have hval : msdVal k w₂ = msdVal k w₁ := by
      dsimp [Δ] at h0
      change (msdVal k w₂ : ℤ) - (msdVal k w₁ : ℤ) = 0 at h0
      have h0' : (msdVal k w₂ : ℤ) = (msdVal k w₁ : ℤ) := sub_eq_zero.mp h0
      exact_mod_cast h0'
    exact hne (msdVal_inj_of_eq_length hk1 hlen hval.symm)
  have hkv_dvd : k ^ v ∣ x := pow_padicValNat_dvd
  have hx_fac : x = k ^ v * x_cop := (Nat.mul_div_cancel' hkv_dvd).symm
  have hxcop_pos : 0 < x_cop := by
    by_contra h0
    have hx0 : x_cop = 0 := Nat.eq_zero_of_not_pos h0
    rw [hx0, mul_zero] at hx_fac; omega
  have hx_ncop : ¬ k ∣ x_cop := by
    intro hdvd
    have hkv1 : k ^ (v + 1) ∣ x := by
      rw [pow_succ, hx_fac]
      rcases hdvd with ⟨t, ht⟩
      exact ⟨t, by rw [ht]; ring⟩
    have hv1_le : v + 1 ≤ v := (padicValNat_dvd_iff_le hx_pos.ne').mp hkv1
    omega
  have hv_lt : v < L := by
    by_contra hge; push Not at hge
    have hpow_le : k ^ L ≤ k ^ v := Nat.pow_le_pow_right hk1 hge
    have : k ^ L ≤ x := by
      calc k ^ L ≤ k ^ v := hpow_le
        _ ≤ k ^ v * x_cop := Nat.le_mul_of_pos_right _ hxcop_pos
        _ = x := hx_fac.symm
    omega
  refine ⟨hΔ_ne, ⟨hx_fac, hx_ncop, hv_lt⟩, ?_, ?_⟩
  · intro hdvd
    have hkv_all : k ^ v ∣ msdVal k (α ++ γ) * k ^ L + y_bot :=
      dvd_trans hkv_dvd hdvd
    have hkv_kL : k ^ v ∣ msdVal k (α ++ γ) * k ^ L :=
      dvd_mul_of_dvd_right (Nat.pow_dvd_pow k hv_lt.le) _
    have hkv_y : k ^ v ∣ y_bot := (Nat.dvd_add_right hkv_kL).mp hkv_all
    have hxcop_all : x_cop ∣ msdVal k (α ++ γ) * k ^ L + y_bot :=
      dvd_trans ⟨k ^ v, by rw [hx_fac]; ring⟩ hdvd
    have hg_x : g ∣ x_cop := Nat.gcd_dvd_left _ _
    exact ⟨hkv_y, dvd_trans hg_x hxcop_all⟩
  · intro hkv_y hg_div
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hxcop_pos) with h1 | hxcop2
    · refine ⟨α ++ γ, ?_, ?_⟩
      · rw [List.map_append, DFA.evalFrom_of_append, hα, hγ]
      · have hx_eq : x = k ^ v := by simpa [← h1] using hx_fac
        rw [hx_eq]
        exact dvd_add (dvd_mul_of_dvd_right (Nat.pow_dvd_pow k hv_lt.le) _) hkv_y
    · set p := w₁.length
      have hp_pos : 1 ≤ p := by
        by_contra hp0; push Not at hp0
        have hw1_nil : w₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
        have hw2_nil : w₂ = [] := List.eq_nil_of_length_eq_zero (by omega)
        exact hne (hw1_nil.trans hw2_nil.symm)
      have hkp_gt1 : 1 < k ^ p := Nat.one_lt_pow (by omega) hk.one_lt
      have hkpm1_pos : 0 < k ^ p - 1 := by omega
      have hcop_k_xcop : Nat.Coprime k x_cop := hk.coprime_iff_not_dvd.mpr hx_ncop
      have hcop_kp_xcop : Nat.Coprime (k ^ p) x_cop := hcop_k_xcop.pow_left p
      have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left _ hxcop_pos
      have hg_dvd_x : g ∣ x_cop := Nat.gcd_dvd_left _ _
      have hg_dvd_Δ : g ∣ Δ.natAbs := Nat.gcd_dvd_right _ _
      have hcop_kp_g : Nat.Coprime (k ^ p) g := hcop_kp_xcop.coprime_dvd_right hg_dvd_x
      have hcop_kp_m : Nat.Coprime (k ^ p) ((k ^ p - 1) * g) := by
        refine Nat.Coprime.mul_right ?_ hcop_kp_g
        exact Nat.coprime_of_dvd' fun q hq h1 h2 => by
          have hd : q ∣ k ^ p - (k ^ p - 1) := Nat.dvd_sub h1 h2
          rw [show k ^ p - (k ^ p - 1) = 1 by omega] at hd
          exact absurd hd hq.not_dvd_one
      let E := x_cop.totient
      have hE_pos : 1 ≤ E := Nat.totient_pos.mpr hxcop_pos
      let Φ := ((k ^ p - 1) * g).totient
      have hΦ_pos : 1 ≤ Φ := Nat.totient_pos.mpr (mul_pos hkpm1_pos hg_pos)
      let t := x_cop * E * Φ
      have ht_ge : x_cop * E ≤ t := Nat.le_mul_of_pos_right _ hΦ_pos
      have h_kpE_mod : (k ^ p) ^ E ≡ 1 [MOD x_cop] := Nat.ModEq.pow_totient hcop_kp_xcop
      have h_kpt_mod : (k ^ p) ^ t ≡ 1 [MOD ((k ^ p - 1) * g)] := by
        dsimp [t]
        rw [mul_comm (x_cop * E) Φ, pow_mul]
        simpa [Φ] using (Nat.ModEq.pow_totient hcop_kp_m).pow (x_cop * E)
      have hm_dvd_kpt : ((k ^ p - 1) * g) ∣ (k ^ (t * p) - 1) := by
        have h1_le_kpt : 1 ≤ k ^ (t * p) := Nat.one_le_pow _ _ hk.pos
        have hmod_Z : ((k : ℤ) ^ (t * p)) ≡ 1 [ZMOD (((k ^ p - 1) * g : ℕ) : ℤ)] := by
          rw [mul_comm t p, pow_mul]
          exact_mod_cast h_kpt_mod
        obtain ⟨c, hc⟩ := Int.modEq_iff_dvd.mp hmod_Z.symm
        have hcZ : ((k ^ (t * p) - 1 : ℕ) : ℤ) = (((k ^ p - 1) * g : ℕ) : ℤ) * c := by
          rw [Nat.cast_sub h1_le_kpt, Nat.cast_pow, Nat.cast_one]
          exact hc
        exact Int.ofNat_dvd.mp ⟨c, hcZ⟩
      have hkpt_mod_g : k ^ (t * p) ≡ 1 [MOD g] := by
        have h1_le : 1 ≤ k ^ (t * p) := Nat.one_le_pow _ _ hk.pos
        have hg_dvd : g ∣ k ^ (t * p) - 1 := dvd_trans (dvd_mul_left g (k ^ p - 1)) hm_dvd_kpt
        rw [Nat.ModEq]
        by_cases hg1 : g = 1
        · simp [hg1, Nat.mod_one]
        · rcases hg_dvd with ⟨c, hc⟩
          have : k ^ (t * p) = 1 + g * c := by omega
          rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      have hgeom_mod_g : (k ^ p - 1) * msdVal k (List.replicate t w₁).flatten ≡ 0 [MOD g] := by
        have hidZ := msdVal_append_const_replicate hk2 w₁ t
        rw [show w₁.length = p from rfl] at hidZ
        have hsub_dvd : ((k ^ p - 1) * g) ∣ k ^ (t * p) - 1 := hm_dvd_kpt
        rcases hsub_dvd with ⟨c, hc⟩
        have h1_le : 1 ≤ k ^ (t * p) := Nat.one_le_pow _ _ hk.pos
        have hcZ : (k : ℤ) ^ (t * p) - 1 = (((k ^ p - 1 : ℕ) : ℤ) * (g : ℤ)) * (c : ℤ) := by
          have hc' : ((k ^ (t * p) - 1 : ℕ) : ℤ) = (((k ^ p - 1) * g * c : ℕ) : ℤ) := by
            exact_mod_cast hc
          rw [Nat.cast_sub h1_le, Nat.cast_pow] at hc'
          push_cast at hc'
          simpa [mul_assoc] using hc'
        rw [hcZ] at hidZ
        have hidZ2 : ((k ^ p - 1 : ℕ) : ℤ) * ((msdVal k (List.replicate t w₁).flatten : ℤ) -
            (msdVal k w₁ : ℤ) * (g : ℤ) * (c : ℤ)) = 0 := by
          linarith
        have hkp1_ne0 : ((k ^ p - 1 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hkpm1_pos.ne'
        have hdiff0 := mul_eq_zero.mp hidZ2 |>.resolve_left hkp1_ne0
        have hval_eq : msdVal k (List.replicate t w₁).flatten = msdVal k w₁ * g * c := by
          have : (msdVal k (List.replicate t w₁).flatten : ℤ) = ((msdVal k w₁ * g * c : ℕ) : ℤ) := by
            push_cast; linarith
          exact_mod_cast this
        rw [hval_eq, Nat.ModEq]
        have : (k ^ p - 1) * (msdVal k w₁ * g * c) = g * ((k ^ p - 1) * msdVal k w₁ * c) := by ring
        rw [this, Nat.mul_mod_right, Nat.zero_mod]
      --Wait: we need `msdVal k (List.replicate t w₁).flatten ≡ 0 [MOD g]` OR directly `(α ++ w₁^t ++ γ) ≡ (α ++ γ) [MOD g]`!
      -- Notice `k^p - 1` might share a factor with `g`, which is why dividing `(k^p - 1)` FIRST is crucial (`msdVal_append_const_replicate` had `(k^p - 1)` on BOTH sides)!
      have hrep_mod_g : g ∣ msdVal k (List.replicate t w₁).flatten := by
        have hidZ := msdVal_append_const_replicate hk2 w₁ t
        rw [show w₁.length = p from rfl] at hidZ
        rcases hm_dvd_kpt with ⟨c, hc⟩
        have h1_le : 1 ≤ k ^ (t * p) := Nat.one_le_pow _ _ hk.pos
        have hcZ : (k : ℤ) ^ (t * p) - 1 = (((k ^ p - 1 : ℕ) : ℤ) * (g : ℤ)) * (c : ℤ) := by
          have hc' : ((k ^ (t * p) - 1 : ℕ) : ℤ) = (((k ^ p - 1) * g * c : ℕ) : ℤ) := by
            exact_mod_cast hc
          rw [Nat.cast_sub h1_le, Nat.cast_pow] at hc'
          push_cast at hc'
          simpa [mul_assoc] using hc'
        rw [hcZ] at hidZ
        have hidZ2 : ((k ^ p - 1 : ℕ) : ℤ) * ((msdVal k (List.replicate t w₁).flatten : ℤ) -
            (msdVal k w₁ : ℤ) * (g : ℤ) * (c : ℤ)) = 0 := by
          linarith
        have hkp1_ne0 : ((k ^ p - 1 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hkpm1_pos.ne'
        have hdiff0 := mul_eq_zero.mp hidZ2 |>.resolve_left hkp1_ne0
        have hval_eq : msdVal k (List.replicate t w₁).flatten = msdVal k w₁ * g * c := by
          have : (msdVal k (List.replicate t w₁).flatten : ℤ) = ((msdVal k w₁ * g * c : ℕ) : ℤ) := by
            push_cast; linarith
          exact_mod_cast this
        exact ⟨msdVal k w₁ * c, by rw [hval_eq]; ring⟩
      have hbase_mod_g : (msdVal k (α ++ (List.replicate t w₁).flatten ++ γ) : ℤ) ≡
          (msdVal k (α ++ γ) : ℤ) [ZMOD g] := by
        have hlen_rep : (List.replicate t w₁).flatten.length = t * p := by
          rw [List.length_flatten, List.map_replicate, List.sum_replicate, smul_eq_mul]
        rw [msdVal_append, msdVal_append, hlen_rep, msdVal_append]
        push_cast
        have h1 : ((k : ℤ) ^ (t * p)) ≡ 1 [ZMOD g] := by exact_mod_cast hkpt_mod_g
        have h2 : (msdVal k (List.replicate t w₁).flatten : ℤ) ≡ 0 [ZMOD g] := by
          rcases hrep_mod_g with ⟨c, hc⟩
          rw [hc]
          exact Int.modEq_zero_iff_dvd.mpr ⟨c, by push_cast; ring⟩
        have hcomb : (msdVal k α : ℤ) * ((k : ℤ) ^ (t * p) * (k : ℤ) ^ γ.length) +
            (msdVal k (List.replicate t w₁).flatten : ℤ) * (k : ℤ) ^ γ.length +
            (msdVal k γ : ℤ) ≡
            (msdVal k α : ℤ) * (1 * (k : ℤ) ^ γ.length) + 0 * (k : ℤ) ^ γ.length +
            (msdVal k γ : ℤ) [ZMOD g] :=
          (((Int.ModEq.rfl.mul (h1.mul Int.ModEq.rfl)).add (h2.mul Int.ModEq.rfl)).add Int.ModEq.rfl)
        simpa [add_mul, mul_assoc] using hcomb
      have hg_R : (g : ℤ) ∣
          ((msdVal k (α ++ (List.replicate t w₁).flatten ++ γ) : ℤ) * (k : ℤ) ^ L + (y_bot : ℤ)) := by
        have hg_orig : (g : ℤ) ∣ ((msdVal k (α ++ γ) : ℤ) * (k : ℤ) ^ L + (y_bot : ℤ)) := by
          exact_mod_cast hg_div
        have hmod_R : ((msdVal k (α ++ (List.replicate t w₁).flatten ++ γ) : ℤ) * (k : ℤ) ^ L + (y_bot : ℤ)) ≡
            ((msdVal k (α ++ γ) : ℤ) * (k : ℤ) ^ L + (y_bot : ℤ)) [ZMOD g] :=
          (hbase_mod_g.mul Int.ModEq.rfl).add Int.ModEq.rfl
        rw [← Int.modEq_zero_iff_dvd] at hg_orig ⊢
        exact hmod_R.trans hg_orig
      let R : ℤ := (msdVal k (α ++ (List.replicate t w₁).flatten ++ γ) : ℤ) * (k : ℤ) ^ L + (y_bot : ℤ)
      let B : ℤ := Δ * (k : ℤ) ^ (γ.length + L)
      have hcop_kpow_x : Nat.Coprime (k ^ (γ.length + L)) x_cop := hcop_k_xcop.pow_left _
      have hg_B : Nat.gcd x_cop B.natAbs = g := by
        have hB_abs : B.natAbs = Δ.natAbs * k ^ (γ.length + L) := by
          dsimp [B]
          rw [Int.natAbs_mul, show ((k : ℤ) ^ (γ.length + L)).natAbs = k ^ (γ.length + L) by
            exact_mod_cast Int.natAbs_natCast (k ^ (γ.length + L))]
        rw [hB_abs]
        apply Nat.dvd_antisymm
        · refine Nat.dvd_gcd (Nat.gcd_dvd_left _ _) ?_
          have hg1 : Nat.gcd x_cop (Δ.natAbs * k ^ (γ.length + L)) ∣ Δ.natAbs * k ^ (γ.length + L) :=
            Nat.gcd_dvd_right _ _
          have hcop_gcd : Nat.Coprime (Nat.gcd x_cop (Δ.natAbs * k ^ (γ.length + L))) (k ^ (γ.length + L)) :=
            hcop_kpow_x.symm.coprime_dvd_left (Nat.gcd_dvd_left _ _)
          exact hcop_gcd.dvd_of_dvd_mul_right hg1
        · exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _) (dvd_mul_of_dvd_left (Nat.gcd_dvd_right _ _) _)
      have hbez : ∃ u₀ v₀ : ℤ, B * u₀ + (x_cop : ℤ) * v₀ = (g : ℤ) := by
        have hb := Int.gcd_eq_gcd_ab B (x_cop : ℤ)
        have hgcd_eq : (Int.gcd B (x_cop : ℤ) : ℤ) = (g : ℤ) := by
          have : Int.gcd B (x_cop : ℤ) = Nat.gcd x_cop B.natAbs := by
            rw [Int.gcd_def, Nat.gcd_comm]
            simp
          rw [this, hg_B]
        refine ⟨Int.gcdA B (x_cop : ℤ), Int.gcdB B (x_cop : ℤ), ?_⟩
        linarith
      obtain ⟨u₀, v₀, huv⟩ := hbez
      obtain ⟨q₀, hq₀⟩ := hg_R
      let jZ : ℤ := (-u₀ * q₀) % (x_cop : ℤ)
      have hjZ_nn : 0 ≤ jZ := Int.emod_nonneg _ (by exact_mod_cast hxcop_pos.ne')
      have hjZ_lt : jZ < (x_cop : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hxcop_pos)
      let j : ℕ := jZ.toNat
      have hj_lt : j < x_cop := by
        have hltZ : (j : ℤ) < (x_cop : ℤ) := by simpa [j, Int.toNat_of_nonneg hjZ_nn] using hjZ_lt
        exact_mod_cast hltZ
      have hj_cong : (R + (j : ℤ) * B) ≡ 0 [ZMOD x_cop] := by
        have hj_mod : (j : ℤ) ≡ -u₀ * q₀ [ZMOD x_cop] := by
          have : (j : ℤ) = jZ := by simp [j, Int.toNat_of_nonneg hjZ_nn]
          rw [this]
          exact Int.mod_modEq _ _
        have h1 : R + (j : ℤ) * B ≡ R + (-u₀ * q₀) * B [ZMOD x_cop] :=
          Int.ModEq.rfl.add (hj_mod.mul Int.ModEq.rfl)
        have hq₀' : R = (g : ℤ) * q₀ := hq₀
        have h2 : R + (-u₀ * q₀) * B = (x_cop : ℤ) * (q₀ * v₀) := by
          calc R + (-u₀ * q₀) * B
              = (g : ℤ) * q₀ - q₀ * (B * u₀) := by rw [hq₀']; ring
            _ = q₀ * ((g : ℤ) - B * u₀) := by ring
            _ = q₀ * ((x_cop : ℤ) * v₀) := by rw [← huv]; ring
            _ = (x_cop : ℤ) * (q₀ * v₀) := by ring
        rw [h2] at h1
        exact h1.trans (Int.modEq_zero_iff_dvd.mpr ⟨q₀ * v₀, rfl⟩)
      let S : Finset ℕ := (Finset.range j).image (fun r => r * E)
      have hS_inj : Function.Injective (fun r : ℕ => r * E) := fun r₁ r₂ heq =>
        mul_right_cancel₀ (by omega : E ≠ 0) heq
      have hS_lt : ∀ r ∈ S, r < t := by
        intro r hr
        rcases Finset.mem_image.mp hr with ⟨a, ha, rfl⟩
        have ha_lt : a < j := Finset.mem_range.mp ha
        have h1 : a * E < x_cop * E := Nat.mul_lt_mul_of_pos_right (lt_trans ha_lt hj_lt) hE_pos
        exact lt_of_lt_of_le h1 ht_ge
      let blocks : List (List (Fin k)) :=
        List.ofFn (fun i : Fin t => if (t - 1 - i.1) ∈ S then w₂ else w₁)
      let u' := α ++ blocks.flatten ++ γ
      refine ⟨u', ?_, ?_⟩
      · have hblocks_mem : ∀ z ∈ blocks, z = w₁ ∨ z = w₂ := fun z hz => by
          rcases List.mem_ofFn.mp hz with ⟨i, rfl⟩
          split_ifs
          · right; rfl
          · left; rfl
        have hbl_eval : M.evalFrom q (blocks.flatten.map fun d => (⟨0, hk.pos⟩, d)) = q :=
          msdVal_list_blocks_eval M hk.pos q w₁ w₂ hw₁ hw₂ blocks hblocks_mem
        dsimp [u']
        rw [List.map_append, List.map_append, DFA.evalFrom_of_append, DFA.evalFrom_of_append]
        change M.evalFrom (M.evalFrom (M.evalFrom q_start (α.map fun d => (⟨0, hk.pos⟩, d)))
          (blocks.flatten.map fun d => (⟨0, hk.pos⟩, d)))
          (γ.map fun d => (⟨0, hk.pos⟩, d)) = s
        rw [hα, hbl_eval, hγ]
      · have h_len_blocks : blocks.flatten.length = t * p := by
          dsimp [blocks]
          rw [List.length_flatten, List.map_ofFn]
          have hlen_fn : ∀ i : Fin t,
              (if (t - 1 - i.1) ∈ S then w₂ else w₁).length = p := by
            intro i; split_ifs <;> [exact hlen.symm; rfl]
          simp_rw [Function.comp_def, hlen_fn, List.sum_ofFn, Finset.sum_const, Finset.card_fin,
            smul_eq_mul]
        have h_len_rep : (List.replicate t w₁).flatten.length = t * p := by
          rw [List.length_flatten, List.map_replicate, List.sum_replicate, smul_eq_mul]
        have h_diff_blocks := msdVal_zlist_diff w₁ w₂ (rfl : w₁.length = p) hlen.symm t S hS_lt
        have h_u_diff : (msdVal k u' : ℤ) * (k : ℤ) ^ L + (y_bot : ℤ) - R =
            Δ * (∑ r ∈ S, (k : ℤ) ^ (r * p)) * (k : ℤ) ^ (γ.length + L) := by
          dsimp [u', R]
          rw [msdVal_append, msdVal_append, h_len_blocks, msdVal_append, msdVal_append, h_len_rep]
          push_cast
          have hpow_gL : (k : ℤ) ^ γ.length * (k : ℤ) ^ L = (k : ℤ) ^ (γ.length + L) := by
            rw [pow_add]
          have hΔ_eq : Δ = (msdVal k w₂ : ℤ) - (msdVal k w₁ : ℤ) := rfl
          have hbl' : (msdVal k blocks.flatten : ℤ) -
              (msdVal k (List.replicate t w₁).flatten : ℤ) =
              Δ * ∑ r ∈ S, (k : ℤ) ^ (r * p) := by simpa [p, hΔ_eq] using h_diff_blocks
          calc (((msdVal k α : ℤ) * (k : ℤ) ^ (t * p) + (msdVal k blocks.flatten : ℤ)) *
                  (k : ℤ) ^ γ.length + (msdVal k γ : ℤ)) * (k : ℤ) ^ L + (y_bot : ℤ) -
                ((((msdVal k α : ℤ) * (k : ℤ) ^ (t * p) +
                  (msdVal k (List.replicate t w₁).flatten : ℤ)) * (k : ℤ) ^ γ.length +
                  (msdVal k γ : ℤ)) * (k : ℤ) ^ L + (y_bot : ℤ))
              = ((msdVal k blocks.flatten : ℤ) - (msdVal k (List.replicate t w₁).flatten : ℤ)) *
                  ((k : ℤ) ^ γ.length * (k : ℤ) ^ L) := by ring
            _ = Δ * (∑ r ∈ S, (k : ℤ) ^ (r * p)) * (k : ℤ) ^ (γ.length + L) := by
                rw [hbl', hpow_gL]
        have hS_sum : ∑ r ∈ S, (k : ℤ) ^ (r * p) ≡ (j : ℤ) [ZMOD x_cop] := by
          dsimp [S]
          rw [Finset.sum_image (fun x _ y _ h => hS_inj h)]
          have hterm_mod : ∀ a : ℕ, (k : ℤ) ^ (a * E * p) ≡ 1 [ZMOD x_cop] := fun a => by
            rw [show a * E * p = p * E * a by ring, pow_mul, pow_mul]
            have hE' : ((k ^ p) ^ E : ℤ) ≡ 1 [ZMOD x_cop] := by exact_mod_cast h_kpE_mod
            simpa using hE'.pow a
          have hsum_range : ∀ n : ℕ, ∑ a ∈ Finset.range n, (k : ℤ) ^ (a * E * p) ≡
              ∑ _a ∈ Finset.range n, (1 : ℤ) [ZMOD x_cop] := by
            intro n
            induction n with
            | zero => rfl
            | succ n ihn =>
              rw [Finset.sum_range_succ, Finset.sum_range_succ]
              exact ihn.add (hterm_mod n)
          calc ∑ a ∈ Finset.range j, (k : ℤ) ^ (a * E * p)
              ≡ ∑ _a ∈ Finset.range j, (1 : ℤ) [ZMOD x_cop] := hsum_range j
            _ = (j : ℤ) := by simp
        have h_u_mod : ((msdVal k u' : ℤ) * (k : ℤ) ^ L + (y_bot : ℤ)) ≡ 0 [ZMOD x_cop] := by
          have h1 : (msdVal k u' : ℤ) * (k : ℤ) ^ L + (y_bot : ℤ) =
              R + Δ * (∑ r ∈ S, (k : ℤ) ^ (r * p)) * (k : ℤ) ^ (γ.length + L) := by linarith [h_u_diff]
          rw [h1]
          have h2 : R + Δ * (∑ r ∈ S, (k : ℤ) ^ (r * p)) * (k : ℤ) ^ (γ.length + L) ≡
              R + Δ * (j : ℤ) * (k : ℤ) ^ (γ.length + L) [ZMOD x_cop] :=
            Int.ModEq.rfl.add ((Int.ModEq.rfl.mul hS_sum).mul Int.ModEq.rfl)
          have h3 : R + Δ * (j : ℤ) * (k : ℤ) ^ (γ.length + L) = R + (j : ℤ) * B := by
            dsimp [B]; ring
          rw [h3] at h2
          exact h2.trans hj_cong
        have hxcop_dvd : x_cop ∣ msdVal k u' * k ^ L + y_bot := by
          have hZ : (x_cop : ℤ) ∣ ((msdVal k u' * k ^ L + y_bot : ℕ) : ℤ) := by
            push_cast
            exact Int.modEq_zero_iff_dvd.mp h_u_mod
          exact_mod_cast hZ
        have hkv_dvd_u : k ^ v ∣ msdVal k u' * k ^ L + y_bot :=
          dvd_add (dvd_mul_of_dvd_right (Nat.pow_dvd_pow k hv_lt.le) _) hkv_y
        have hcop_vx : Nat.Coprime (k ^ v) x_cop := hcop_k_xcop.pow_left v
        rw [hx_fac]
        exact hcop_vx.mul_dvd_of_dvd_of_dvd hkv_dvd_u hxcop_dvd

end PrimeBaseExponentialCollapse

section BoundedAndDLOGReduction

/-- Theorem 4a (Bounded-Prefix Linear Exponential-Sum Reduction):
For a single-loop bounded prefix `α₀ β^m α₁` in base `k ≥ 2`, multiplying `val_k` by
`D = k ^ |β| - 1` (`Nat.Coprime D k`) collapses the iteration to an exact linear combination
of `k ^ (m * |β| + |α₁|)` and `1`:
`D * val_k(α₀ β^m α₁) = (D * val_k(α₀) + val_k(β)) * k^(m * |β| + |α₁|) + (D * val_k(α₁) - val_k(β) * k^|α₁|)`.
More generally, for ANY `r`-loop bounded word `α₀ β₁^{n₁} α₁ ⋯ βᵣ^{nᵣ} αᵣ`, multiplying `val_k`
by `∏_{i < r} (k^|β_i| - 1)` produces a `ℤ`-linear combination of exponentials `k^{e_i}` and `1`. -/
theorem ppl068_bounded_prefix_linear_exp_sum {k : ℕ} (hk : 2 ≤ k)
    (α₀ β α₁ : List (Fin k)) (hβ : 0 < β.length) (m : ℕ) :
    let D : ℕ := k ^ β.length - 1
    Nat.Coprime D k ∧
    ((D : ℤ) * ((α₀ ++ (List.replicate m β).flatten ++ α₁).foldl (fun acc d => k * acc + d.1) 0 : ℕ) =
      ((D : ℤ) * ((α₀.foldl (fun acc d => k * acc + d.1) 0 : ℕ) : ℤ) +
        ((β.foldl (fun acc d => k * acc + d.1) 0 : ℕ) : ℤ)) * (k : ℤ) ^ (m * β.length + α₁.length) +
      ((D : ℤ) * ((α₁.foldl (fun acc d => k * acc + d.1) 0 : ℕ) : ℤ) -
        ((β.foldl (fun acc d => k * acc + d.1) 0 : ℕ) : ℤ) * (k : ℤ) ^ α₁.length)) := by
  intro D
  have hpow_pos : 1 ≤ k ^ β.length := Nat.one_le_pow _ _ (by omega)
  have hcop : Nat.Coprime D k := by
    have hk_dvd : k ∣ k ^ β.length := dvd_pow_self k hβ.ne'
    rw [Nat.coprime_comm, Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    have hd_gt1 : 1 < Nat.gcd k D := by
      have hpos : 0 < Nat.gcd k D := Nat.gcd_pos_of_pos_left _ (by omega)
      omega
    have hd1 : Nat.gcd k D ∣ k := Nat.gcd_dvd_left _ _
    have hd2 : Nat.gcd k D ∣ D := Nat.gcd_dvd_right _ _
    have hd_kp : Nat.gcd k D ∣ k ^ β.length := dvd_trans hd1 hk_dvd
    have hd_one : Nat.gcd k D ∣ 1 := by
      have : k ^ β.length = D + 1 := by dsimp [D]; omega
      rw [this] at hd_kp
      exact (Nat.dvd_add_right hd2).mp hd_kp
    have := Nat.le_of_dvd Nat.one_pos hd_one
    omega
  refine ⟨hcop, ?_⟩
  have hlen_rep : (List.replicate m β).flatten.length = m * β.length := by
    rw [List.length_flatten, List.map_replicate, List.sum_replicate, smul_eq_mul]
  change (D : ℤ) * (msdVal k (α₀ ++ (List.replicate m β).flatten ++ α₁) : ℤ) =
    ((D : ℤ) * (msdVal k α₀ : ℤ) + (msdVal k β : ℤ)) * (k : ℤ) ^ (m * β.length + α₁.length) +
      ((D : ℤ) * (msdVal k α₁ : ℤ) - (msdVal k β : ℤ) * (k : ℤ) ^ α₁.length)
  rw [msdVal_append, msdVal_append, hlen_rep]
  have hid := msdVal_append_const_replicate hk β m
  change (D : ℤ) * (msdVal k (List.replicate m β).flatten : ℤ) =
    (msdVal k β : ℤ) * ((k : ℤ) ^ (m * β.length) - 1) at hid
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  rw [pow_add]
  calc (D : ℤ) * (((msdVal k α₀ : ℤ) * (k : ℤ) ^ (m * β.length) +
          (msdVal k (List.replicate m β).flatten : ℤ)) * (k : ℤ) ^ α₁.length +
          (msdVal k α₁ : ℤ))
      = (D : ℤ) * (msdVal k α₀ : ℤ) * (k : ℤ) ^ (m * β.length) * (k : ℤ) ^ α₁.length +
          ((D : ℤ) * (msdVal k (List.replicate m β).flatten : ℤ)) * (k : ℤ) ^ α₁.length +
          (D : ℤ) * (msdVal k α₁ : ℤ) := by ring
    _ = (D : ℤ) * (msdVal k α₀ : ℤ) * (k : ℤ) ^ (m * β.length) * (k : ℤ) ^ α₁.length +
          (msdVal k β : ℤ) * ((k : ℤ) ^ (m * β.length) - 1) * (k : ℤ) ^ α₁.length +
          (D : ℤ) * (msdVal k α₁ : ℤ) := by rw [hid]
    _ = ((D : ℤ) * (msdVal k α₀ : ℤ) + (msdVal k β : ℤ)) *
          ((k : ℤ) ^ (m * β.length) * (k : ℤ) ^ α₁.length) +
          ((D : ℤ) * (msdVal k α₁ : ℤ) - (msdVal k β : ℤ) * (k : ℤ) ^ α₁.length) := by ring

private lemma borrow_sub_exists {k : ℕ} (hk : 2 ≤ k) (xs zs ys : List (Fin k))
    (hlen1 : xs.length = zs.length) (hlen2 : xs.length = ys.length)
    (heq : msdVal k xs = msdVal k zs + msdVal k ys) :
    ∃ bs : List Bool, bs.length = xs.length + 1 ∧ bs.head? = some false ∧ bs.getLast? = some false ∧
      ∀ i : Fin xs.length,
        (if bs.getD i.1 false then k else 0) + (xs.get i).1 =
          (zs.getD i.1 ⟨0, by omega⟩).1 + (ys.getD i.1 ⟨0, by omega⟩).1 +
            (if bs.getD (i.1 + 1) false then 1 else 0) := by
  have hk1 : 1 ≤ k := by omega
  let d0 : Fin k := ⟨0, by omega⟩
  have hgen : ∀ (b_in : Bool) (xs' zs' ys' : List (Fin k)),
      xs'.length = zs'.length → xs'.length = ys'.length →
      (if b_in then 1 else 0) * k ^ xs'.length + msdVal k xs' = msdVal k zs' + msdVal k ys' →
      ∃ bs : List Bool, bs.length = xs'.length + 1 ∧ bs.head? = some b_in ∧ bs.getLast? = some false ∧
        ∀ i : Fin xs'.length,
          (if bs.getD i.1 false then k else 0) + (xs'.get i).1 =
            (zs'.getD i.1 d0).1 + (ys'.getD i.1 d0).1 +
              (if bs.getD (i.1 + 1) false then 1 else 0) := by
    intro b_in xs'
    induction xs' generalizing b_in with
    | nil =>
      intro zs' ys' hl1 hl2 hsum
      have hzn : zs' = [] := List.eq_nil_of_length_eq_zero hl1.symm
      have hyn : ys' = [] := List.eq_nil_of_length_eq_zero hl2.symm
      subst hzn hyn
      simp only [msdVal_nil, List.length_nil, pow_zero, mul_one, add_zero] at hsum
      have hb0 : b_in = false := by cases b_in <;> simp_all
      subst hb0
      exact ⟨[false], rfl, rfl, rfl, fun i => absurd i.2 (Nat.not_lt_zero i.1)⟩
    | cons a as ih =>
      intro zs' ys' hl1 hl2 hsum
      cases zs' with
      | nil => simp at hl1
      | cons z zs =>
        cases ys' with
        | nil => simp at hl2
        | cons y ys =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hl1 hl2
          rw [msdVal_cons, msdVal_cons, msdVal_cons, List.length_cons, ← hl1, ← hl2] at hsum
          set diff : ℤ := (if b_in then (k : ℤ) else 0) + (a.1 : ℤ) - (z.1 : ℤ) - (y.1 : ℤ)
          have hpow_pos : (0 : ℤ) < (k : ℤ) ^ as.length := by positivity
          have has_lt : (msdVal k as : ℤ) < (k : ℤ) ^ as.length := by
            have := msdVal_lt_pow hk1 as; exact_mod_cast this
          have hzs_lt : (msdVal k zs : ℤ) < (k : ℤ) ^ as.length := by
            have := msdVal_lt_pow hk1 zs; rw [← hl1] at this; exact_mod_cast this
          have hys_lt : (msdVal k ys : ℤ) < (k : ℤ) ^ as.length := by
            have := msdVal_lt_pow hk1 ys; rw [← hl2] at this; exact_mod_cast this
          have hsumZ : diff * (k : ℤ) ^ as.length + (msdVal k as : ℤ) =
              (msdVal k zs : ℤ) + (msdVal k ys : ℤ) := by
            have hZ : ((if b_in then 1 else 0 : ℕ) : ℤ) * (k : ℤ) ^ (as.length + 1) +
                ((a.1 : ℤ) * (k : ℤ) ^ as.length + (msdVal k as : ℤ)) =
                ((z.1 : ℤ) * (k : ℤ) ^ as.length + (msdVal k zs : ℤ)) +
                ((y.1 : ℤ) * (k : ℤ) ^ as.length + (msdVal k ys : ℤ)) := by exact_mod_cast hsum
            rw [pow_succ'] at hZ
            have hb_cast : ((if b_in then 1 else 0 : ℕ) : ℤ) * (k : ℤ) =
                if b_in then (k : ℤ) else 0 := by cases b_in <;> simp
            rw [← mul_assoc, hb_cast] at hZ
            dsimp [diff]
            linarith
          have hdiff_ge0 : 0 ≤ diff := by
            by_contra hneg; push Not at hneg
            have h1 : diff * (k : ℤ) ^ as.length ≤ (-1) * (k : ℤ) ^ as.length :=
              mul_le_mul_of_nonneg_right (by omega) hpow_pos.le
            linarith
          have hdiff_le1 : diff ≤ 1 := by
            by_contra hgt; push Not at hgt
            have h1 : 2 * (k : ℤ) ^ as.length ≤ diff * (k : ℤ) ^ as.length :=
              mul_le_mul_of_nonneg_right (by omega) hpow_pos.le
            linarith
          let b_out : Bool := decide (diff = 1)
          have hbout_val : (if b_out then (1 : ℤ) else 0) = diff := by
            dsimp [b_out]; rcases (by omega : diff = 0 ∨ diff = 1) with h | h <;> simp [h]
          have hstep_eq : (if b_in then k else 0) + a.1 = z.1 + y.1 + (if b_out then 1 else 0) := by
            have : (if b_in then (k : ℤ) else 0) + (a.1 : ℤ) =
                (z.1 : ℤ) + (y.1 : ℤ) + (if b_out then 1 else 0) := by
              rw [hbout_val]; dsimp [diff]; ring
            exact_mod_cast this
          have ih_nat : (if b_out then 1 else 0) * k ^ as.length + msdVal k as =
              msdVal k zs + msdVal k ys := by
            have : ((if b_out then 1 else 0 : ℕ) : ℤ) * (k : ℤ) ^ as.length + (msdVal k as : ℤ) =
                (msdVal k zs : ℤ) + (msdVal k ys : ℤ) := by
              have hbv : ((if b_out then 1 else 0 : ℕ) : ℤ) = diff := by
                rw [← hbout_val]
                cases b_out <;> simp
              rw [hbv]; exact hsumZ
            exact_mod_cast this
          obtain ⟨bs', hbs_len, hbs_hd, hbs_last, hbs_eq⟩ := ih b_out zs ys hl1 hl2 ih_nat
          refine ⟨b_in :: bs', by simp [hbs_len], rfl, ?_, fun i => ?_⟩
          · cases bs' with
            | nil => simp at hbs_len
            | cons b₁ bs₁ => simpa [List.getLast?_cons_cons] using hbs_last
          · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
            · simp only [Fin.val_zero, zero_add, List.get_eq_getElem, List.getElem_cons_zero,
                List.getD_cons_zero, List.getD_cons_succ]
              cases bs' with
              | nil => simp at hbs_len
              | cons b₁ bs₁ =>
                simp only [List.head?_cons, Option.some.injEq] at hbs_hd
                subst hbs_hd
                simpa [List.getD_cons_zero] using hstep_eq
            · simpa only [Fin.val_succ, List.get_eq_getElem, List.getElem_cons_succ, List.getD_cons_succ]
                using hbs_eq j
  exact hgen false xs zs ys hlen1 hlen2 (by simp [heq]) |> fun ⟨bs, h1, h2, h3, h4⟩ =>
    ⟨bs, h1, h2, h3, h4⟩

/-- Theorem 4b (Reduction from `DLOG-DFA(k)` to DFA Divisibility):
1. Number-theoretic core: for `k ≥ 2`, `0 < z < x`, `Nat.Coprime x k`, and any `L : ℕ`,
   `(∃ m : ℕ, x ∣ (k ^ (L + m) + (x - z))) ↔ (∃ e : ℕ, k ^ e ≡ z [MOD x])`.
2. Automata-theoretic reduction: for ANY `k ≥ 2` and any binary DFA `V : DFA (Fin k × Fin k) Q`
   whose accepted words start with a nonzero Track-1 digit (`p₀.1.1 ≠ 0`) and represent pairs
   `(x, z)` with `0 < z < x` and `Nat.Coprime x k`, there exists an explicitly constructed DFA `M_V`
   (combining the `1 0*` prefix with the `2`-state borrow subtractor `y_bot = x - z` via `NFA.toDFA`)
   such that:
   `(∃ w ∈ M_V.accepts, 0 < val₁ w ∧ val₁ w ∣ val₂ w) ↔ (∃ w ∈ V.accepts, ∃ e : ℕ, k ^ e ≡ val₂ w [MOD val₁ w])`. -/
theorem ppl068_dlog_dfa_reduction {k : ℕ} (hk : 2 ≤ k) :
    (∀ (x z L : ℕ), 0 < z → z < x → Nat.Coprime x k →
      ((∃ m : ℕ, x ∣ (k ^ (L + m) + (x - z))) ↔ (∃ e : ℕ, k ^ e ≡ z [MOD x]))) ∧
    (∀ {Q : Type} (V : DFA (Fin k × Fin k) Q),
      (∀ w ∈ V.accepts,
        (∃ p₀ : Fin k × Fin k, ∃ v' : List (Fin k × Fin k), w = p₀ :: v' ∧ p₀.1.1 ≠ 0) ∧
        0 < (w.map Prod.snd).foldl (fun acc d => k * acc + d.1) 0 ∧
        (w.map Prod.snd).foldl (fun acc d => k * acc + d.1) 0 <
          (w.map Prod.fst).foldl (fun acc d => k * acc + d.1) 0 ∧
        Nat.Coprime ((w.map Prod.fst).foldl (fun acc d => k * acc + d.1) 0) k) →
      ∃ M_V : DFA (Fin k × Fin k) (Set (Fin 2 ⊕ Q × Bool)),
        (∃ w ∈ M_V.accepts,
          0 < (w.map Prod.fst).foldl (fun acc d => k * acc + d.1) 0 ∧
          (w.map Prod.fst).foldl (fun acc d => k * acc + d.1) 0 ∣
            (w.map Prod.snd).foldl (fun acc d => k * acc + d.1) 0) ↔
        (∃ w ∈ V.accepts, ∃ e : ℕ,
          k ^ e ≡ (w.map Prod.snd).foldl (fun acc d => k * acc + d.1) 0
            [MOD (w.map Prod.fst).foldl (fun acc d => k * acc + d.1) 0])) := by
  have hdlog_num : ∀ (x z L : ℕ), 0 < z → z < x → Nat.Coprime x k →
      ((∃ m : ℕ, x ∣ (k ^ (L + m) + (x - z))) ↔ (∃ e : ℕ, k ^ e ≡ z [MOD x])) := by
    intro x z L _ hzx hcop
    have hmod_iff : ∀ e : ℕ, x ∣ (k ^ e + (x - z)) ↔ k ^ e ≡ z [MOD x] := fun e => by
      constructor
      · intro hdvd
        rcases hdvd with ⟨c, hc⟩
        have hZ : (k : ℤ) ^ e - (z : ℤ) = (x : ℤ) * ((c : ℤ) - 1) := by
          have hc' : (k : ℤ) ^ e + ((x : ℤ) - (z : ℤ)) = (x : ℤ) * (c : ℤ) := by
            have : ((k ^ e + (x - z) : ℕ) : ℤ) = ((x * c : ℕ) : ℤ) := by exact_mod_cast hc
            rw [Nat.cast_add, Nat.cast_pow, Nat.cast_sub hzx.le, Nat.cast_mul] at this
            exact this
          linarith
        rw [← Int.natCast_modEq_iff]
        exact (Int.modEq_iff_dvd.mpr ⟨(c : ℤ) - 1, by push_cast; linarith⟩).symm
      · intro hmodeq
        have hZ : (k : ℤ) ^ e ≡ (z : ℤ) [ZMOD x] := by exact_mod_cast hmodeq
        obtain ⟨c, hc⟩ := Int.modEq_iff_dvd.mp hZ.symm
        have hc' : (k : ℤ) ^ e + ((x : ℤ) - (z : ℤ)) = (x : ℤ) * (c + 1) := by linarith
        have hx_dvdZ : (x : ℤ) ∣ ((k ^ e + (x - z) : ℕ) : ℤ) := by
          rw [Nat.cast_add, Nat.cast_pow, Nat.cast_sub hzx.le]
          exact ⟨c + 1, hc'⟩
        exact_mod_cast hx_dvdZ
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨L + m, (hmod_iff (L + m)).mp hm⟩
    · rintro ⟨e, he⟩
      have hx_pos : 0 < x := by omega
      have hΦ_pos : 0 < x.totient := Nat.totient_pos.mpr hx_pos
      have htot : k ^ x.totient ≡ 1 [MOD x] := Nat.ModEq.pow_totient hcop.symm
      let t := L
      have hm_ge : L ≤ e + t * x.totient := by
        have : L ≤ t * x.totient := Nat.le_mul_of_pos_right t hΦ_pos
        omega
      refine ⟨e + t * x.totient - L, (hmod_iff _).mpr ?_⟩
      rw [show L + (e + t * x.totient - L) = e + t * x.totient by omega, pow_add,
        mul_comm t x.totient, pow_mul]
      have hmul := he.mul (htot.pow t)
      simpa using hmul
  refine ⟨hdlog_num, fun {Q} V hV_spec => ?_⟩
  classical
  let d0 : Fin k := ⟨0, by omega⟩
  let d1 : Fin k := ⟨1, by omega⟩
  let N : NFA (Fin k × Fin k) (Fin 2 ⊕ Q × Bool) :=
    { step := fun s a => match s with
        | Sum.inl 0 => if a = (d0, d1) then { Sum.inl 1 } else ∅
        | Sum.inl 1 =>
          (if a = (d0, d0) then { Sum.inl 1 } else ∅) ∪
          (if a.1.1 ≠ 0 then
            { st | ∃ (z : Fin k) (b_out : Bool),
                st = Sum.inr (V.step V.start (a.1, z), b_out) ∧
                a.1.1 = z.1 + a.2.1 + (if b_out then 1 else 0) }
          else ∅)
        | Sum.inr (q, b_in) =>
          { st | ∃ (z : Fin k) (b_out : Bool),
              st = Sum.inr (V.step q (a.1, z), b_out) ∧
              (if b_in then k else 0) + a.1.1 = z.1 + a.2.1 + (if b_out then 1 else 0) }
      start := { Sum.inl 0 }
      accept := { st | ∃ q ∈ V.accept, st = Sum.inr (q, false) } }
  have hN_mono : ∀ (l : List (Fin k × Fin k)) {S₁ S₂ : Set (Fin 2 ⊕ Q × Bool)},
      S₁ ⊆ S₂ → N.evalFrom S₁ l ⊆ N.evalFrom S₂ l := by
    intro l
    induction l with
    | nil => intro _ _ hSub; exact hSub
    | cons a l' ih =>
      intro S₁ S₂ hSub
      rw [NFA.evalFrom_cons, NFA.evalFrom_cons]
      exact ih fun u hu => by
        rw [NFA.mem_stepSet] at hu ⊢
        rcases hu with ⟨s, hs, hus⟩
        exact ⟨s, hSub hs, hus⟩
  have hN_step : ∀ (s u t : Fin 2 ⊕ Q × Bool) (a : Fin k × Fin k) (l : List (Fin k × Fin k)),
      t ∈ N.evalFrom {u} l → u ∈ N.step s a → t ∈ N.evalFrom {s} (a :: l) := by
    intro s u t a l ht hu
    rw [NFA.evalFrom_cons, NFA.stepSet_singleton]
    exact hN_mono l (Set.singleton_subset_iff.mpr hu) ht
  have hN_split : ∀ (l : List (Fin k × Fin k)) (S : Set (Fin 2 ⊕ Q × Bool)) (y : Fin 2 ⊕ Q × Bool),
      y ∈ N.evalFrom S l → ∃ s ∈ S, y ∈ N.evalFrom {s} l := by
    intro l
    induction l with
    | nil => intro _ y hy; exact ⟨y, hy, rfl⟩
    | cons a l' ih =>
      intro S y hy
      rw [NFA.evalFrom_cons] at hy
      rcases ih (N.stepSet S a) y hy with ⟨u, hu, hyu⟩
      rw [NFA.mem_stepSet] at hu
      rcases hu with ⟨s, hs, hus⟩
      exact ⟨s, hs, hN_step s u y a l' hyu hus⟩
  have hN_cons : ∀ (s y : Fin 2 ⊕ Q × Bool) (a : Fin k × Fin k) (l : List (Fin k × Fin k)),
      y ∈ N.evalFrom {s} (a :: l) → ∃ u ∈ N.step s a, y ∈ N.evalFrom {u} l := by
    intro s y a l hy
    rw [NFA.evalFrom_cons, NFA.stepSet_singleton] at hy
    exact hN_split l (N.step s a) y hy
  have hN_sound : ∀ w : List (Fin k × Fin k), w ∈ N.accepts →
      ∃ m : ℕ, ∃ v : List (Fin k × Fin k), ∃ zs : List (Fin k),
        v.length = zs.length ∧ 1 ≤ v.length ∧
        w = (d0, d1) :: List.replicate m (d0, d0) ++ v ∧
        (∀ p ∈ v.take 1, p.1.1 ≠ 0) ∧
        (v.zip zs).map (fun pz => (pz.1.1, pz.2)) ∈ V.accepts ∧
        msdVal k (v.map Prod.fst) = msdVal k zs + msdVal k (v.map Prod.snd) := by
    intro w hw
    rw [NFA.mem_accepts] at hw
    rcases hw with ⟨sf, ⟨qf, hqf_acc, rfl⟩, hsf_eval⟩
    -- Helper describing reachability from `Sum.inr (q, b_in)` to `Sum.inr (qf, false)`
    have hinr : ∀ (v : List (Fin k × Fin k)) (q : Q) (b_in : Bool),
        Sum.inr (qf, false) ∈ N.evalFrom { Sum.inr (q, b_in) } v →
        ∃ zs : List (Fin k), ∃ bs : List Bool,
          zs.length = v.length ∧ bs.length = v.length + 1 ∧
          bs.head? = some b_in ∧ bs.getLast? = some false ∧
          V.evalFrom q ((v.zip zs).map fun pz => (pz.1.1, pz.2)) = qf ∧
          ∀ i : Fin v.length,
            (if bs.getD i.1 false then k else 0) + (v.get i).1.1 =
              (zs.getD i.1 d0).1 + (v.get i).2.1 +
                (if bs.getD (i.1 + 1) false then 1 else 0) := by
      intro v
      induction v with
      | nil =>
        intro q b_in h
        simp only [NFA.evalFrom_nil, Set.mem_singleton_iff, Sum.inr.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨[], [false], rfl, rfl, rfl, rfl, rfl, fun i => absurd i.2 (Nat.not_lt_zero i.1)⟩
      | cons p ps ih =>
        intro q b_in h
        obtain ⟨st_mid, hstep, hmem_mid⟩ := hN_cons _ _ p ps h
        dsimp [N] at hstep
        rcases hstep with ⟨z₀, b_mid, rfl, hdig⟩
        obtain ⟨zs', bs', hzl, hbl, hbhd, hblast, hV, heqs⟩ := ih _ b_mid hmem_mid
        refine ⟨z₀ :: zs', b_in :: bs', by simp [hzl], by simp [hbl], rfl, ?_, ?_, fun i => ?_⟩
        · cases bs' with
          | nil => simp at hbl
          | cons _ _ => simpa [List.getLast?_cons_cons] using hblast
        · simpa [List.zip_cons_cons, List.map_cons, DFA.evalFrom_cons] using hV
        · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
          · simp only [Fin.val_zero, zero_add, List.get_eq_getElem, List.getElem_cons_zero,
              List.getD_cons_zero, List.getD_cons_succ]
            cases bs' with
            | nil => simp at hbl
            | cons b₁ bs₁ =>
              simp only [List.head?_cons, Option.some.injEq] at hbhd
              subst hbhd
              exact hdig
          · simpa only [Fin.val_succ, List.get_eq_getElem, List.getElem_cons_succ, List.getD_cons_succ]
              using heqs j
    -- Helper summarizing digit equation -> `msdVal` sum identity
    have hsum_eq : ∀ (v : List (Fin k × Fin k)) (zs : List (Fin k)) (bs : List Bool) (b_in : Bool),
        zs.length = v.length → bs.length = v.length + 1 →
        bs.head? = some b_in → bs.getLast? = some false →
        (∀ i : Fin v.length,
          (if bs.getD i.1 false then k else 0) + (v.get i).1.1 =
            (zs.getD i.1 d0).1 + (v.get i).2.1 +
              (if bs.getD (i.1 + 1) false then 1 else 0)) →
        (if b_in then 1 else 0) * k ^ v.length + msdVal k (v.map Prod.fst) =
          msdVal k zs + msdVal k (v.map Prod.snd) := by
      intro v
      induction v with
      | nil =>
        intro zs bs b_in hzl hbl hbhd hblast _
        have hzn : zs = [] := List.eq_nil_of_length_eq_zero hzl
        subst hzn
        cases bs with
        | nil => simp at hbl
        | cons b₀ bs₀ =>
          have hbs0 : bs₀ = [] := List.eq_nil_of_length_eq_zero (by simpa using hbl)
          subst hbs0
          simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at hbhd hblast
          subst hbhd
          rw [hblast]
          simp [msdVal_nil]
      | cons p ps ih =>
        intro zs bs b_in hzl hbl hbhd hblast heqs
        cases zs with
        | nil => simp at hzl
        | cons z zs' =>
          cases bs with
          | nil => simp at hbl
          | cons b₀ bs' =>
            cases bs' with
            | nil => simp at hbl
            | cons b₁ bs₁ =>
              simp only [List.length_cons, Nat.add_right_cancel_iff] at hzl hbl
              simp only [List.head?_cons, Option.some.injEq] at hbhd
              subst hbhd
              have heq0 := heqs ⟨0, by simp⟩
              simp only [zero_add, List.get_eq_getElem, List.getElem_cons_zero,
                List.getD_cons_zero, List.getD_cons_succ] at heq0
              have hblast' : (b₁ :: bs₁).getLast? = some false := by
                simpa [List.getLast?_cons_cons] using hblast
              have ih' := ih zs' (b₁ :: bs₁) b₁ hzl (by simpa using hbl) rfl hblast'
                (fun j => by
                  simpa only [Fin.val_succ, List.get_eq_getElem, List.getElem_cons_succ,
                    List.getD_cons_succ] using heqs j.succ)
              rw [List.map_cons, List.map_cons, msdVal_cons, msdVal_cons, msdVal_cons,
                List.length_cons, List.length_map, List.length_map, hzl]
              have hpow : (if b₀ then 1 else 0) * k ^ (ps.length + 1) + p.1.1 * k ^ ps.length =
                  z.1 * k ^ ps.length + p.2.1 * k ^ ps.length + (if b₁ then 1 else 0) * k ^ ps.length := by
                rw [pow_succ]
                calc (if b₀ then 1 else 0) * (k ^ ps.length * k) + p.1.1 * k ^ ps.length
                    = ((if b₀ then k else 0) + p.1.1) * k ^ ps.length := by
                      (cases b₀ <;> simp); all_goals ring
                  _ = (z.1 + p.2.1 + (if b₁ then 1 else 0)) * k ^ ps.length := by rw [heq0]
                  _ = z.1 * k ^ ps.length + p.2.1 * k ^ ps.length +
                        (if b₁ then 1 else 0) * k ^ ps.length := by ring
              linarith
    -- Analyze `Sum.inl 0` path
    cases w with
    | nil =>
      dsimp [N] at hsf_eval
      simp only [Set.mem_singleton_iff] at hsf_eval
      cases hsf_eval
    | cons p₀ w' =>
      have hsf0 : Sum.inr (qf, false) ∈ N.evalFrom { Sum.inl 0 } (p₀ :: w') := hsf_eval
      obtain ⟨st₁, hstep₀, hmem₁⟩ := hN_cons _ _ p₀ w' hsf0
      dsimp [N] at hstep₀
      split_ifs at hstep₀ with hp₀
      · subst hp₀
        simp only [Set.mem_singleton_iff] at hstep₀
        subst hstep₀
        -- Induct on `w'` starting from `Sum.inl 1`
        have hinl1 : ∀ (l : List (Fin k × Fin k)),
            Sum.inr (qf, false) ∈ N.evalFrom { Sum.inl 1 } l →
            ∃ m : ℕ, ∃ v : List (Fin k × Fin k), ∃ zs : List (Fin k),
              v.length = zs.length ∧ 1 ≤ v.length ∧
              l = List.replicate m (d0, d0) ++ v ∧
              (∀ p ∈ v.take 1, p.1.1 ≠ 0) ∧
              (v.zip zs).map (fun pz => (pz.1.1, pz.2)) ∈ V.accepts ∧
              msdVal k (v.map Prod.fst) = msdVal k zs + msdVal k (v.map Prod.snd) := by
          intro l hl
          induction l with
          | nil => simp [NFA.evalFrom_nil] at hl
          | cons a as ihl =>
            obtain ⟨st_next, hstep1, hmem_next⟩ := hN_cons _ _ a as hl
            dsimp [N] at hstep1
            rcases hstep1 with hloop | hbranch
            · split_ifs at hloop with ha0
              · subst ha0
                simp only [Set.mem_singleton_iff] at hloop
                subst hloop
                obtain ⟨m, v, zs, hvl, hv1, rfl, htake, hVacc, hmsd⟩ := ihl hmem_next
                exact ⟨m + 1, v, zs, hvl, hv1, by rw [List.replicate_succ, List.cons_append], htake, hVacc, hmsd⟩
              · cases hloop
            · by_cases ha1 : a.1.1 = 0
              · simp [ha1] at hbranch
              · rw [if_pos ha1] at hbranch
                rcases hbranch with ⟨z₀, b_out, rfl, hdig⟩
                obtain ⟨zs', bs', hzl, hbl, hbhd, hblast, hV, heqs⟩ := hinr as _ b_out hmem_next
                have hsum := hsum_eq (a :: as) (z₀ :: zs') (false :: bs') false
                  (by simp [hzl]) (by simp [hbl]) rfl (by
                    cases bs' with
                    | nil => simp at hbl
                    | cons _ _ => simpa [List.getLast?_cons_cons] using hblast)
                  (fun i => by
                    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
                    · simp only [Fin.val_zero, zero_add, List.get_eq_getElem, List.getElem_cons_zero,
                        List.getD_cons_zero, List.getD_cons_succ]
                      cases bs' with
                      | nil => simp at hbl
                      | cons b₁ bs₁ =>
                        simp only [List.head?_cons, Option.some.injEq] at hbhd
                        subst hbhd
                        simpa [List.getD_cons_zero] using hdig
                    · simpa only [Fin.val_succ, List.get_eq_getElem, List.getElem_cons_succ,
                        List.getD_cons_succ] using heqs j)
                simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, zero_add] at hsum
                refine ⟨0, a :: as, z₀ :: zs', by simp [hzl], by simp, rfl, fun p hp => ?_, ?_, hsum⟩
                · simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hp
                  subst hp; exact ha1
                · rw [DFA.mem_accepts, DFA.eval]
                  simpa [List.zip_cons_cons, List.map_cons, DFA.evalFrom_cons] using
                    (hV.symm ▸ hqf_acc : V.evalFrom (V.step V.start (a.1, z₀))
                      ((as.zip zs').map fun pz => (pz.1.1, pz.2)) ∈ V.accept)
        obtain ⟨m, v, zs, hvl, hv1, rfl, htake, hVacc, hmsd⟩ := hinl1 w' hmem₁
        exact ⟨m, v, zs, hvl, hv1, rfl, htake, hVacc, hmsd⟩
      · cases hstep₀
  refine ⟨N.toDFA, ?_⟩
  rw [NFA.toDFA_correct]
  constructor
  · rintro ⟨w, hw_acc, hx_pos, hdvd⟩
    obtain ⟨m, v, zs, hvl, hv1, rfl, htake, hVacc, hmsd⟩ := hN_sound w hw_acc
    let wV := (v.zip zs).map fun pz => (pz.1.1, pz.2)
    have hV_len : wV.length = v.length := by
      dsimp [wV]; rw [List.length_map, List.length_zip, ← hvl, min_self]
    have hV_fst : wV.map Prod.fst = v.map Prod.fst := by
      dsimp [wV]
      suffices h : ∀ (l₁ : List (Fin k × Fin k)) (l₂ : List (Fin k)),
          l₁.length = l₂.length → ((l₁.zip l₂).map fun pz => (pz.1.1, pz.2)).map Prod.fst = l₁.map Prod.fst from
        h v zs hvl
      intro l₁
      induction l₁ with
      | nil => intro _ _; simp
      | cons a as ih =>
        intro l₂ hl
        cases l₂ with
        | nil => simp at hl
        | cons z zs' =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
          rw [List.zip_cons_cons, List.map_cons, List.map_cons, List.map_cons, ih zs' hl]
    have hV_snd : wV.map Prod.snd = zs := by
      dsimp [wV]
      suffices h : ∀ (l₁ : List (Fin k × Fin k)) (l₂ : List (Fin k)),
          l₁.length = l₂.length → ((l₁.zip l₂).map fun pz => (pz.1.1, pz.2)).map Prod.snd = l₂ from
        h v zs hvl
      intro l₁
      induction l₁ with
      | nil =>
        intro l₂ hl
        cases l₂ with
        | nil => simp
        | cons _ _ => simp at hl
      | cons a as ih =>
        intro l₂ hl
        cases l₂ with
        | nil => simp at hl
        | cons z zs' =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
          rw [List.zip_cons_cons, List.map_cons, List.map_cons, ih zs' hl]
    have hspec := hV_spec wV hVacc
    obtain ⟨_, hz_pos, hzx, hcop⟩ := hspec
    change 0 < msdVal k (wV.map Prod.snd) at hz_pos
    change msdVal k (wV.map Prod.snd) < msdVal k (wV.map Prod.fst) at hzx
    change Nat.Coprime (msdVal k (wV.map Prod.fst)) k at hcop
    rw [hV_fst] at hzx hcop
    rw [hV_snd] at hz_pos hzx
    have hfst_pre : msdVal k (((d0, d1) :: List.replicate m (d0, d0)).map Prod.fst) = 0 := by
      rw [msdVal_eq_zero_iff_all_zero]
      intro d hd
      rcases List.mem_map.mp hd with ⟨p, hp, rfl⟩
      rcases List.mem_cons.mp hp with rfl | hp'
      · rfl
      · rcases List.mem_replicate.mp hp' with ⟨_, rfl⟩; rfl
    have hsnd_pre : msdVal k (((d0, d1) :: List.replicate m (d0, d0)).map Prod.snd) = k ^ m := by
      rw [List.map_cons, msdVal_cons, List.length_map, List.length_replicate,
        List.map_replicate, msdVal_replicate_zero_of_pos, add_zero, one_mul]
    have hfst_w : msdVal k (((d0, d1) :: List.replicate m (d0, d0) ++ v).map Prod.fst) =
        msdVal k (v.map Prod.fst) := by
      rw [List.map_append, msdVal_append, hfst_pre, zero_mul, zero_add]
    have hsnd_w : msdVal k (((d0, d1) :: List.replicate m (d0, d0) ++ v).map Prod.snd) =
        k ^ (v.length + m) + msdVal k (v.map Prod.snd) := by
      rw [List.map_append, msdVal_append, List.length_map, hsnd_pre, pow_add, mul_comm (k ^ v.length)]
    change msdVal k _ ∣ msdVal k _ at hdvd
    rw [hfst_w, hsnd_w] at hdvd
    have hy_sub : msdVal k (v.map Prod.snd) = msdVal k (v.map Prod.fst) - msdVal k zs := by omega
    rw [hy_sub] at hdvd
    have he := (hdlog_num (msdVal k (v.map Prod.fst)) (msdVal k zs) v.length hz_pos hzx hcop).mp
      ⟨m, hdvd⟩
    refine ⟨wV, hVacc, ?_⟩
    change ∃ e, k ^ e ≡ msdVal k (wV.map Prod.snd) [MOD msdVal k (wV.map Prod.fst)]
    simpa [hV_fst, hV_snd] using he
  · rintro ⟨wV, hVacc, e, he⟩
    obtain ⟨⟨p₀, v', rfl, hp₀⟩, hz_pos, hzx, hcop⟩ := hV_spec wV hVacc
    set xs := (p₀ :: v').map Prod.fst
    set zs := (p₀ :: v').map Prod.snd
    set L := (p₀ :: v').length
    have hx_pos : 0 < msdVal k xs := by
      have hpow0 : 0 < k ^ v'.length := Nat.pow_pos (by omega)
      have hge := msdVal_nonzero_head_ge p₀.1 hp₀ (v'.map Prod.fst)
      have hge' : k ^ v'.length ≤ msdVal k xs := by
        simpa [xs, List.map_cons, List.length_map] using hge
      exact lt_of_lt_of_le hpow0 hge'
    have hzx' : msdVal k zs < msdVal k xs := hzx
    have hz_pos' : 0 < msdVal k zs := hz_pos
    have hcop' : Nat.Coprime (msdVal k xs) k := hcop
    obtain ⟨m, hm⟩ := (hdlog_num (msdVal k xs) (msdVal k zs) L hz_pos' hzx' hcop').mpr ⟨e, he⟩
    have hy_lt : msdVal k xs - msdVal k zs < k ^ L := by
      have hx_lt : msdVal k xs < k ^ L := by
        simpa [xs, L, List.length_map] using msdVal_lt_pow (by omega) xs
      omega
    obtain ⟨ys, hys_len, hys_val⟩ := nat_digits_of_lt_pow (by omega) L (msdVal k xs - msdVal k zs) hy_lt
    have hsum_xs : msdVal k xs = msdVal k zs + msdVal k ys := by rw [hys_val]; omega
    have hxs_len : xs.length = L := by simp [xs, L]
    have hzs_len : zs.length = L := by simp [zs, L]
    obtain ⟨bs, hbs_len, hbs_hd, hbs_last, hbs_eq⟩ :=
      borrow_sub_exists hk xs zs ys (by omega) (by omega) hsum_xs
    let v := xs.zip ys
    let w := (d0, d1) :: List.replicate m (d0, d0) ++ v
    have hv_len : v.length = L := by dsimp [v]; rw [List.length_zip, hxs_len, hys_len, min_self]
    have hv_fst : v.map Prod.fst = xs := by
      dsimp [v]
      suffices h : ∀ (l₁ l₂ : List (Fin k)), l₁.length = l₂.length → (l₁.zip l₂).map Prod.fst = l₁ from
        h xs ys (by omega)
      intro l₁
      induction l₁ with
      | nil => intro _ _; simp
      | cons a as ih =>
        intro l₂ hl
        cases l₂ with
        | nil => simp at hl
        | cons b bs' =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
          rw [List.zip_cons_cons, List.map_cons, ih bs' hl]
    have hv_snd : v.map Prod.snd = ys := by
      dsimp [v]
      suffices h : ∀ (l₁ l₂ : List (Fin k)), l₁.length = l₂.length → (l₁.zip l₂).map Prod.snd = l₂ from
        h xs ys (by omega)
      intro l₁
      induction l₁ with
      | nil =>
        intro l₂ hl
        cases l₂ with
        | nil => simp
        | cons _ _ => simp at hl
      | cons a as ih =>
        intro l₂ hl
        cases l₂ with
        | nil => simp at hl
        | cons b bs' =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
          rw [List.zip_cons_cons, List.map_cons, ih bs' hl]
    have hw_acc : w ∈ N.accepts := by
      -- Walk `inl 0 → inl 1` on `(d0, d1)`, stay in `inl 1` for `replicate m (d0, d0)`,
      -- branch on head of `v` into `inr`, then match `V` + `bs` to `inr (V.eval (p₀ :: v'), false)`.
      rw [NFA.mem_accepts]
      have hL_pos : 1 ≤ L := by dsimp [L]; simp
      have hv_pos : 1 ≤ v.length := by rw [hv_len]; exact hL_pos
      have hinr_path : ∀ (i : ℕ) (hi : i ≤ L) (q_cur : Q) (b_cur : Bool),
          q_cur = V.eval ((p₀ :: v').take i) →
          b_cur = bs.getD i false →
          ∃ qf ∈ V.accept, Sum.inr (qf, false) ∈ N.evalFrom { Sum.inr (q_cur, b_cur) } (v.drop i) := by
        intro i hi
        obtain ⟨d, hd⟩ : ∃ d, L - i = d := ⟨L - i, rfl⟩
        induction d generalizing i with
        | zero =>
          intro q_cur b_cur hq hb
          have hiL : i = L := by omega
          subst hiL
          have hdrop : v.drop L = [] := List.drop_eq_nil_of_le (by omega)
          have htake : (p₀ :: v').take L = p₀ :: v' := List.take_of_length_le (le_refl _)
          rw [htake] at hq
          have hb_false : b_cur = false := by
            rw [hb]
            have hlast : bs.getD L false = false := by
              have hl := hbs_last
              rw [List.getLast?_eq_getElem?] at hl
              have hbsL : bs.length - 1 = L := by omega
              rw [hbsL, List.getElem?_eq_getElem (by omega)] at hl
              have hval : bs[L] = false := Option.some.inj hl
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
              simpa using hval
            exact hlast
          subst hq hb_false
          refine ⟨V.eval (p₀ :: v'), ?_, ?_⟩
          · rwa [← DFA.mem_accepts]
          · rw [hdrop, NFA.evalFrom_nil]; rfl
        | succ d ihd =>
          intro q_cur b_cur hq hb
          have hi_lt : i < L := by omega
          let a_v := v.get ⟨i, by omega⟩
          let z_i := zs.get ⟨i, by omega⟩
          let b_next := bs.getD (i + 1) false
          have hdrop_eq : v.drop i = a_v :: v.drop (i + 1) := List.drop_eq_getElem_cons (by omega)
          have haz : (a_v.1, z_i) = (p₀ :: v').get ⟨i, by omega⟩ := by
            have ha1 : a_v.1 = ((p₀ :: v').get ⟨i, by omega⟩).1 := by
              dsimp [a_v, v, xs]
              simp only [List.getElem_zip, List.getElem_map]
            have hz1 : z_i = ((p₀ :: v').get ⟨i, by omega⟩).2 := by
              dsimp [z_i, zs]
              simp only [List.getElem_map]
            exact Prod.ext ha1 hz1
          have htake_next : (p₀ :: v').take (i + 1) = (p₀ :: v').take i ++ [(a_v.1, z_i)] := by
            rw [List.take_add_one, haz, List.getElem?_eq_getElem hi_lt]
            simp
          have hq_next : V.step q_cur (a_v.1, z_i) = V.eval ((p₀ :: v').take (i + 1)) := by
            rw [htake_next, DFA.eval, DFA.evalFrom_of_append, DFA.evalFrom_singleton, ← DFA.eval, hq]
          obtain ⟨qf, hqf_acc, hmem⟩ := ihd (i + 1) (by omega) (by omega)
            (V.step q_cur (a_v.1, z_i)) b_next hq_next rfl
          refine ⟨qf, hqf_acc, ?_⟩
          rw [hdrop_eq]
          apply hN_step _ (Sum.inr (V.step q_cur (a_v.1, z_i), b_next)) _ _ _ hmem
          dsimp [N]
          refine ⟨z_i, b_next, rfl, ?_⟩
          have hdig := hbs_eq ⟨i, by omega⟩
          have hget_x : xs.get ⟨i, by omega⟩ = a_v.1 := by dsimp [a_v, v]; simp
          have hget_y : ys.get ⟨i, by omega⟩ = a_v.2 := by dsimp [a_v, v]; simp
          have hzd : zs.getD i ⟨0, by omega⟩ = z_i := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
            rfl
          have hyd : ys.getD i ⟨0, by omega⟩ = ys.get ⟨i, by omega⟩ := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
            rfl
          rw [List.get_eq_getElem] at hget_x hget_y
          simp only [List.get_eq_getElem] at hdig
          rw [← hb, hzd, hyd, hget_x] at hdig
          rw [List.get_eq_getElem, hget_y] at hdig
          exact hdig
      -- Start from `Sum.inl 0`
      have hv_cons : v = (v.get ⟨0, by omega⟩) :: v.drop 1 := by
        simpa using (List.drop_eq_getElem_cons (l := v) (i := 0) (by omega))
      have hb0_false : bs.getD 0 false = false := by
        cases bs with
        | nil => simp at hbs_len
        | cons b₀ _ => simpa using hbs_hd
      obtain ⟨qf, hqf_acc, hdrop1⟩ := hinr_path 1 hL_pos
        (V.step V.start ((v.get ⟨0, by omega⟩).1, zs.get ⟨0, by omega⟩))
        (bs.getD 1 false) (by
          have hv0 : v[0].1 = p₀.1 := by dsimp [v, xs]; simp
          simp only [zs, DFA.eval, List.take_succ_cons, List.take_zero, DFA.evalFrom_singleton,
            List.get_eq_getElem, List.getElem_map, List.getElem_cons_zero]
          congr 1; ext
          · exact congrArg Fin.val hv0
          · rfl) rfl
      have hhead_step : Sum.inr (V.step V.start ((v.get ⟨0, by omega⟩).1, zs.get ⟨0, by omega⟩),
          bs.getD 1 false) ∈ N.step (Sum.inl 1) (v.get ⟨0, by omega⟩) := by
        dsimp [N]
        right
        have hv0_nz : (v.get ⟨0, by omega⟩).1.1 ≠ 0 := by
          have : (v.get ⟨0, by omega⟩).1 = p₀.1 := by dsimp [v, xs]; simp
          rw [this]; exact hp₀
        have h0' : (v.get ⟨0, by omega⟩).1.1 ≠ 0 := hv0_nz
        rw [if_pos (by simpa [List.get_eq_getElem] using h0')]
        refine ⟨zs.get ⟨0, by omega⟩, bs.getD 1 false, rfl, ?_⟩
        have hdig0 := hbs_eq ⟨0, by omega⟩
        simp only [zero_add, List.get_eq_getElem] at hdig0
        rw [hb0_false] at hdig0
        have hget_x0 : xs[0] = (v.get ⟨0, by omega⟩).1 := by dsimp [v]; simp
        have hget_y0 : ys[0] = (v.get ⟨0, by omega⟩).2 := by dsimp [v]; simp
        have hzd0 : zs.getD 0 ⟨0, by omega⟩ = zs.get ⟨0, by omega⟩ := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
          rfl
        have hyd0 : ys.getD 0 ⟨0, by omega⟩ = ys[0] := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
          rfl
        rw [hzd0, hyd0, hget_x0, hget_y0] at hdig0
        simpa [List.get_eq_getElem] using hdig0
      have hinl1_end : Sum.inr (qf, false) ∈ N.evalFrom { Sum.inl 1 } v := by
        rw [hv_cons]
        exact hN_step _ _ _ _ _ hdrop1 hhead_step
      have hjoin_gen : ∀ r : ℕ, Sum.inr (qf, false) ∈ N.evalFrom { Sum.inl 1 } (List.replicate r (d0, d0) ++ v) := by
        intro r
        induction r with
        | zero => simpa using hinl1_end
        | succ r ihr =>
          rw [List.replicate_succ, List.cons_append]
          exact hN_step _ (Sum.inl 1) _ _ _ ihr (by left; simp)
      have hjoin : Sum.inr (qf, false) ∈ N.evalFrom { Sum.inl 1 } (List.replicate m (d0, d0) ++ v) :=
        hjoin_gen m
      have hw_eval : Sum.inr (qf, false) ∈ N.eval w := by
        dsimp [w]
        change Sum.inr (qf, false) ∈ N.evalFrom { Sum.inl 0 } ((d0, d1) :: (List.replicate m (d0, d0) ++ v))
        exact hN_step _ (Sum.inl 1) _ _ _ hjoin (by dsimp [N]; simp)
      exact ⟨Sum.inr (qf, false), ⟨qf, hqf_acc, rfl⟩, hw_eval⟩
    refine ⟨w, hw_acc, ?_, ?_⟩
    · have hfst_pre : msdVal k (((d0, d1) :: List.replicate m (d0, d0)).map Prod.fst) = 0 := by
        rw [msdVal_eq_zero_iff_all_zero]
        intro d hd
        rcases List.mem_map.mp hd with ⟨p, hp, rfl⟩
        rcases List.mem_cons.mp hp with rfl | hp'
        · rfl
        · rcases List.mem_replicate.mp hp' with ⟨_, rfl⟩; rfl
      change 0 < msdVal k (w.map Prod.fst)
      dsimp [w]
      rw [← List.cons_append, List.map_append, msdVal_append, hfst_pre,
        zero_mul, zero_add, hv_fst]
      exact hx_pos
    · have hfst_pre : msdVal k (((d0, d1) :: List.replicate m (d0, d0)).map Prod.fst) = 0 := by
        rw [msdVal_eq_zero_iff_all_zero]
        intro d hd
        rcases List.mem_map.mp hd with ⟨p, hp, rfl⟩
        rcases List.mem_cons.mp hp with rfl | hp'
        · rfl
        · rcases List.mem_replicate.mp hp' with ⟨_, rfl⟩; rfl
      have hsnd_pre : msdVal k (((d0, d1) :: List.replicate m (d0, d0)).map Prod.snd) = k ^ m := by
        rw [List.map_cons, msdVal_cons, List.length_map, List.length_replicate,
          List.map_replicate, msdVal_replicate_zero_of_pos, add_zero, one_mul]
      change msdVal k (w.map Prod.fst) ∣ msdVal k (w.map Prod.snd)
      dsimp [w]
      rw [← List.cons_append, List.map_append, msdVal_append, hfst_pre,
        zero_mul, zero_add, hv_fst, List.map_append, msdVal_append, List.length_map,
        hv_len, hv_snd, hys_val, hsnd_pre]
      rw [pow_add, mul_comm (k ^ L)] at hm
      exact hm

/-- Theorem 4c (Spurious-Divisibility / Euler-Totient Small-Suffix Barrier):
For any fixed coprime suffix `(x₀, y_bot₀)` of length `L` with `0 < x₀`, `Nat.Coprime x₀ k`, and
any starting exponent `e` satisfying `x₀ ∣ (k ^ (L + e) + y_bot₀)`, pumping the prefix loop
count by arbitrary multiples `t * x₀.totient` preserves `x₀ ∣ (k ^ (L + e + t * x₀.totient) + y_bot₀)`. -/
theorem ppl068_spurious_divisibility_euler_barrier {k x₀ y_bot₀ L e : ℕ}
    (_hx₀ : 0 < x₀) (hcop : Nat.Coprime x₀ k) (hdvd : x₀ ∣ k ^ (L + e) + y_bot₀) (t : ℕ) :
    x₀ ∣ k ^ (L + e + t * x₀.totient) + y_bot₀ := by
  have htot : k ^ x₀.totient ≡ 1 [MOD x₀] := Nat.ModEq.pow_totient hcop.symm
  have hpow : k ^ (L + e + t * x₀.totient) ≡ k ^ (L + e) [MOD x₀] := by
    rw [pow_add, mul_comm t x₀.totient, pow_mul]
    simpa using Nat.ModEq.rfl.mul (htot.pow t)
  have hadd : k ^ (L + e + t * x₀.totient) + y_bot₀ ≡ k ^ (L + e) + y_bot₀ [MOD x₀] :=
    hpow.add Nat.ModEq.rfl
  rw [← Nat.modEq_zero_iff_dvd] at hdvd ⊢
  exact hadd.trans hdvd

end BoundedAndDLOGReduction

end PPL068

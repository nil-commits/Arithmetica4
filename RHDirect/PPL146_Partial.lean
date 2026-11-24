import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# PPL 146 (Shallit #2 — Tight Bounds for CFG Word Separation): Partial Structural Milestones

**Scope Notice (Partial Milestones — NOT the full open conjecture):**
PPL 146 (Shallit Open Problem 2, `bc4.pdf` Slide 19, £10, OPEN since Currie–Petersen–Robson–Shallit
1999) asks for matching upper and lower bounds on the worst-case number of productions of a
Chomsky-normal-form (CNF) context-free grammar separating two distinct equal-length binary words
of length `n` (known gap: `Ω(log n / log log n)` vs `O(log n)`). The full worst-case problem
remains OPEN.

This file proves three unconditional partial structural milestones and exports 7 headline
**zero-custom-definition pure-Mathlib** public theorems in Section 5 (using the impredicative
Knaster–Tarski least-fixpoint encoding of strict CNF derivation, proven equivalent to
`CNFGrammar.Derives` in `derives_iff_least_fixpoint`):

1. **Theorem A (Almost-All Tight `Θ(log n / log log n)` Separation — Section 2):**
   - `ppl146_uniq_factor_cnf_separation_pure`: Every length-`n` binary word with no repeated
     length-`r` factor is separated from every distinct equal-length word in
     `≤ 2^(b + 1) + (r + 1) / b + 8` strict CNF productions (giving `(3 + o(1)) log n / log log n`).
   - `ppl146_uniq_factor_density_pure`: Exact overlap density bound
     `2^n ≤ |W_uniq(n, r)| + n.choose 2 * 2^(n - r)` (valid for all `r ≥ 1`, including overlaps).
   - `ppl146_cnf_lower_bound_pure` & `ppl146_uniq_factor_lower_bound_pure`: Matching CPRS
     counting lower bounds `n ≤ (p + 1) * (p^3 + 2*p + 1)^p` on `{0,1}^n` and
     `n - 1 ≤ (p + 1) * (p^3 + 2*p + 1)^p` on `W_uniq(n, r)` whenever `2 * n.choose 2 ≤ 2^r`.
2. **Theorem B (Modular-Parity & Hamming-Distance Strict CNF Separator — Section 3):**
   - `ppl146_hamming_isolating_modulus_pure`: Any two equal-length words differing at `j₀`
     isolated modulo `p ≥ 2` from all other differing indices are separated in
     `≤ 6 * Nat.log 2 p + 14` strict CNF productions.
3. **Theorem C (Exact Single-Bit Detector `Ω(log n)` Lower Bound — Section 4):**
   - `ppl146_single_bit_detector_lower_bound_pure` &
     `ppl146_single_bit_detector_prodCount_lower_bound_pure`: For all `s` and `n ≥ 2^(8*s + 5)`,
     some `j < n` admits no strict CNF grammar with `≤ s` active variables (hence `≤ s`
     productions) accepting `0^j 1 0^(n - 1 - j)` and rejecting all `0^k 1 0^(n - 1 - k)` (`k ≠ j`).
-/

namespace PPL146

/-! ## Section 1: Strict CNF Context-Free Grammars & Pure-Mathlib Equivalence -/

/-- A context-free grammar in strict Chomsky Normal Form (CNF) over the binary alphabet `Bool`:
every production is either terminal `A → a` or binary `A → B C`. -/
structure CNFGrammar where
  start : ℕ
  termRules : Finset (ℕ × Bool)
  binRules : Finset (ℕ × ℕ × ℕ)

/-- Exact production count of a strict CNF grammar (Shallit `bc4.pdf` Slides 18–19). -/
def CNFGrammar.prodCount (G : CNFGrammar) : ℕ :=
  G.termRules.card + G.binRules.card

/-- Derivation relation `A ⇒* w` in a strict CNF grammar. -/
inductive CNFGrammar.Derives (G : CNFGrammar) : ℕ → List Bool → Prop where
  | term {A : ℕ} {a : Bool} : (A, a) ∈ G.termRules → G.Derives A [a]
  | bin {A B C : ℕ} {u v : List Bool} :
      (A, B, C) ∈ G.binRules → G.Derives B u → G.Derives C v → G.Derives A (u ++ v)

/-- Acceptance of a binary word `w` by a strict CNF grammar `G`. -/
def CNFGrammar.Accepts (G : CNFGrammar) (w : List Bool) : Prop :=
  G.Derives G.start w

/-- Separation of two binary words `w, x` by a strict CNF grammar `G`. -/
def CNFGrammar.Separates (G : CNFGrammar) (w x : List Bool) : Prop :=
  (G.Accepts w ∧ ¬ G.Accepts x) ∨ (G.Accepts x ∧ ¬ G.Accepts w)

/-- Exact equivalence between `CNFGrammar.Derives` and the zero-custom-definition
pure-Mathlib impredicative least-fixpoint encoding. -/
theorem derives_iff_least_fixpoint (G : CNFGrammar) (A : ℕ) (w : List Bool) :
    G.Derives A w ↔
      ∀ P : ℕ → List Bool → Prop,
        (∀ X a, (X, a) ∈ G.termRules → P X [a]) →
        (∀ X Y Z u v, (X, Y, Z) ∈ G.binRules → P Y u → P Z v → P X (u ++ v)) →
        P A w := by
  constructor
  · intro h P hT hB
    induction h with
    | term hmem => exact hT _ _ hmem
    | bin hmem _ _ ih1 ih2 => exact hB _ _ _ _ _ hmem ih1 ih2
  · intro h
    exact h G.Derives (fun _ _ hm => .term hm) (fun _ _ _ _ _ hm h1 h2 => .bin hm h1 h2)

theorem derives_nonempty (G : CNFGrammar) {A : ℕ} {w : List Bool} (h : G.Derives A w) :
    w ≠ [] := by
  induction h with
  | term _ => simp
  | bin _ _ _ ih1 _ => simp [ih1]

theorem derives_mono {G₁ G₂ : CNFGrammar}
    (ht : G₁.termRules ⊆ G₂.termRules) (hb : G₁.binRules ⊆ G₂.binRules)
    {A : ℕ} {w : List Bool} (h : G₁.Derives A w) : G₂.Derives A w := by
  induction h with
  | term hm => exact .term (ht hm)
  | bin hm _ _ ih1 ih2 => exact .bin (hb hm) ih1 ih2

theorem separates_symm (G : CNFGrammar) {w x : List Bool} :
    G.Separates w x ↔ G.Separates x w := by
  unfold CNFGrammar.Separates
  tauto

theorem separates_irrefl (G : CNFGrammar) (w : List Bool) : ¬ G.Separates w w := by
  unfold CNFGrammar.Separates
  tauto

/-! ## Section 2: Theorem A — Four-Russians Strict CNF Separator on Factor-Unique Words -/

section FourRussians

/-- Binary word `w` has no repeated contiguous factor of length `r`. -/
def HasNoRepeatedFactor (w : List Bool) (r : ℕ) : Prop :=
  ∀ i j : ℕ, i < j → j + r ≤ w.length → (w.drop i).take r ≠ (w.drop j).take r

/-- Injectively encode a `List Bool` as a positive natural number (`encodeBits [] = 1`,
`encodeBits [false] = 2`, `encodeBits [true] = 3`, and `2^|s| ≤ encodeBits s < 2^(|s|+1)`). -/
def encodeBits : List Bool → ℕ
  | [] => 1
  | a :: s => 2 * encodeBits s + (if a then 1 else 0)

theorem encodeBits_pos (s : List Bool) : 1 ≤ encodeBits s := by
  induction s with
  | nil => simp [encodeBits]
  | cons a s ih =>
    simp only [encodeBits]
    split_ifs <;> omega

theorem encodeBits_ge_pow (s : List Bool) : 2 ^ s.length ≤ encodeBits s := by
  induction s with
  | nil => simp [encodeBits]
  | cons a s ih =>
    simp only [encodeBits, List.length_cons, pow_succ]
    split_ifs <;> omega

theorem encodeBits_lt_pow (s : List Bool) : encodeBits s < 2 ^ (s.length + 1) := by
  induction s with
  | nil => simp [encodeBits]
  | cons a s ih =>
    simp only [encodeBits, List.length_cons, pow_succ]
    split_ifs <;> omega

theorem encodeBits_inj {s t : List Bool} (h : encodeBits s = encodeBits t) : s = t := by
  induction s generalizing t with
  | nil =>
    cases t with
    | nil => rfl
    | cons b t =>
      have ht := encodeBits_pos t
      simp only [encodeBits] at h
      split_ifs at h <;> omega
  | cons a s ih =>
    cases t with
    | nil =>
      have hs := encodeBits_pos s
      simp only [encodeBits] at h
      split_ifs at h <;> omega
    | cons b t =>
      simp only [encodeBits] at h
      have hab : a = b := by
        cases a <;> cases b <;> simp at h ⊢ <;> omega
      subst hab
      have hst : encodeBits s = encodeBits t := by
        cases a <;> simp at h <;> omega
      rw [ih hst]

/-- Split a list `u` into nonempty chunks of length at most `b` (`b ≥ 1`). -/
def splitChunks (b : ℕ) (hb : 1 ≤ b) : List Bool → List (List Bool)
  | [] => []
  | a :: rest =>
    have hlen : ((a :: rest).drop b).length < (a :: rest).length := by
      simp only [List.length_drop, List.length_cons]
      omega
    (a :: rest).take b :: splitChunks b hb ((a :: rest).drop b)
termination_by u => u.length

theorem splitChunks_flatten (b : ℕ) (hb : 1 ≤ b) (u : List Bool) :
    (splitChunks b hb u).flatten = u := by
  induction u using splitChunks.induct b hb with
  | case1 => simp [splitChunks]
  | case2 a rest hlen ih =>
    rw [splitChunks, List.flatten_cons, ih, List.take_append_drop]

theorem splitChunks_mem_bounds (b : ℕ) (hb : 1 ≤ b) (u : List Bool) :
    ∀ c ∈ splitChunks b hb u, 1 ≤ c.length ∧ c.length ≤ b := by
  induction u using splitChunks.induct b hb with
  | case1 => simp [splitChunks]
  | case2 a rest hlen ih =>
    intro c hc
    rw [splitChunks] at hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc'
    · refine ⟨?_, ?_⟩
      · simp only [List.length_take, List.length_cons]
        omega
      · simp [List.length_take]
    · exact ih c hc'

theorem splitChunks_length_le (b : ℕ) (hb : 1 ≤ b) (u : List Bool) :
    (splitChunks b hb u).length ≤ (u.length + b - 1) / b := by
  induction u using splitChunks.induct b hb with
  | case1 => simp [splitChunks]
  | case2 a rest hlen ih =>
    rw [splitChunks, List.length_cons]
    by_cases hle : (a :: rest).length ≤ b
    · have hdrop : (a :: rest).drop b = [] := List.drop_eq_nil_of_le hle
      rw [hdrop, splitChunks]
      simp only [List.length_nil, Nat.zero_add]
      rw [Nat.le_div_iff_mul_le (by omega)]
      simp only [List.length_cons]
      omega
    · have hdrop_len : ((a :: rest).drop b).length = (a :: rest).length - b := List.length_drop
      rw [hdrop_len] at ih
      have h1 : ((a :: rest).length - b + b - 1) / b + 1 = ((a :: rest).length + b - 1) / b := by
        have hEq : (a :: rest).length - b + b - 1 + b = (a :: rest).length + b - 1 := by omega
        rw [← hEq, Nat.add_div_right _ (by omega)]
      omega

theorem splitChunks_nonempty (b : ℕ) (hb : 1 ≤ b) {u : List Bool} (hu : u ≠ []) :
    splitChunks b hb u ≠ [] := by
  cases u with
  | nil => exact (hu rfl).elim
  | cons a rest =>
    rw [splitChunks]
    simp

/-- Dictionary terminal rules: `2 → false`, `3 → true`. -/
def dictTermRules : Finset (ℕ × Bool) :=
  {(2, false), (3, true)}

/-- Dictionary binary rules for all `m ∈ [4, 2^(b+1))`: `m → (2 + m % 2) (m / 2)`. -/
def dictBinRules (b : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Ico 4 (2 ^ (b + 1))).image (fun m => (m, 2 + m % 2, m / 2))

theorem dictTermRules_card : dictTermRules.card ≤ 2 := by
  unfold dictTermRules
  decide

theorem dictBinRules_card (b : ℕ) : (dictBinRules b).card ≤ 2 ^ (b + 1) - 4 := by
  unfold dictBinRules
  calc
    ((Finset.Ico 4 (2 ^ (b + 1))).image _).card ≤ (Finset.Ico 4 (2 ^ (b + 1))).card :=
      Finset.card_image_le
    _ = 2 ^ (b + 1) - 4 := Nat.card_Ico 4 (2 ^ (b + 1))

/-- Structurally recursive chain binary rules concatenating `cur` with a list `zs` of IDs
using fresh LHS IDs `base + idx, base + idx + 1, ...`. -/
def chainBinRulesAux (base : ℕ) : ℕ → ℕ → List ℕ → Finset (ℕ × ℕ × ℕ)
  | _, _, [] => ∅
  | idx, cur, y :: zs =>
    insert (base + idx, cur, y) (chainBinRulesAux base (idx + 1) (base + idx) zs)

/-- Start variable of the structurally recursive chain. -/
def chainStartAux (base : ℕ) : ℕ → ℕ → List ℕ → ℕ
  | _, cur, [] => cur
  | idx, _, _ :: zs => chainStartAux base (idx + 1) (base + idx) zs

theorem chainBinRulesAux_card (base : ℕ) :
    ∀ (zs : List ℕ) (idx cur : ℕ), (chainBinRulesAux base idx cur zs).card ≤ zs.length
  | [], _, _ => by simp [chainBinRulesAux]
  | y :: zs, idx, cur => by
    simp only [chainBinRulesAux, List.length_cons]
    exact (Finset.card_insert_le _ _).trans
      (Nat.add_le_add_right (chainBinRulesAux_card base zs (idx + 1) (base + idx)) 1)

theorem mem_chainBinRulesAux_lhs (base : ℕ) :
    ∀ (zs : List ℕ) (idx cur A B C : ℕ),
      (A, B, C) ∈ chainBinRulesAux base idx cur zs → base + idx ≤ A
  | [], _, _, _, _, _, h => by simp [chainBinRulesAux] at h
  | y :: zs, idx, cur, A, B, C, h => by
    simp only [chainBinRulesAux, Finset.mem_insert, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _, _⟩ | h2
    · omega
    · have := mem_chainBinRulesAux_lhs base zs (idx + 1) (base + idx) A B C h2
      omega

theorem chainBinRulesAux_unique_lhs (base : ℕ) :
    ∀ (zs : List ℕ) (idx cur A B₁ C₁ B₂ C₂ : ℕ),
      (A, B₁, C₁) ∈ chainBinRulesAux base idx cur zs →
      (A, B₂, C₂) ∈ chainBinRulesAux base idx cur zs →
      B₁ = B₂ ∧ C₁ = C₂
  | [], _, _, _, _, _, _, _, h1, _ => by simp [chainBinRulesAux] at h1
  | y :: zs, idx, cur, A, B₁, C₁, B₂, C₂, h1, h2 => by
    simp only [chainBinRulesAux, Finset.mem_insert, Prod.mk.injEq] at h1 h2
    rcases h1 with ⟨rfl, rfl, rfl⟩ | h1'
    · rcases h2 with ⟨_, rfl, rfl⟩ | h2'
      · exact ⟨rfl, rfl⟩
      · have := mem_chainBinRulesAux_lhs base zs (idx + 1) (base + idx) _ _ _ h2'
        omega
    · rcases h2 with ⟨rfl, _, _⟩ | h2'
      · have := mem_chainBinRulesAux_lhs base zs (idx + 1) (base + idx) _ _ _ h1'
        omega
      · exact chainBinRulesAux_unique_lhs base zs (idx + 1) (base + idx) A B₁ C₁ B₂ C₂ h1' h2'

theorem chainStartAux_mem_rule (base : ℕ) :
    ∀ (zs : List ℕ) (idx cur y : ℕ),
      ∃ B C, (chainStartAux base idx cur (y :: zs), B, C) ∈
        chainBinRulesAux base idx cur (y :: zs)
  | [], idx, cur, y => ⟨cur, y, by simp [chainStartAux, chainBinRulesAux]⟩
  | z :: zs, idx, cur, y => by
    rcases chainStartAux_mem_rule base zs (idx + 1) (base + idx) z with ⟨B, C, hm⟩
    exact ⟨B, C, Finset.mem_insert_of_mem hm⟩

theorem chainStartAux_ge (base : ℕ) :
    ∀ (zs : List ℕ) (idx cur y : ℕ), base + idx ≤ chainStartAux base idx cur (y :: zs)
  | [], idx, cur, y => by simp [chainStartAux]
  | z :: zs, idx, cur, y => by
    have h := chainStartAux_ge base zs (idx + 1) (base + idx) z
    change base + idx ≤ chainStartAux base (idx + 1) (base + idx) (z :: zs)
    omega

/-- Exact derivation of any dictionary word `s` (`1 ≤ s.length ≤ b`) from `encodeBits s`. -/
theorem dict_derives_self (G : CNFGrammar) (b : ℕ)
    (hT : dictTermRules ⊆ G.termRules) (hB : dictBinRules b ⊆ G.binRules)
    (s : List Bool) (hs1 : 1 ≤ s.length) (hsb : s.length ≤ b) :
    G.Derives (encodeBits s) s := by
  induction s with
  | nil => simp at hs1
  | cons a rest ih =>
    cases rest with
    | nil =>
      cases a
      · exact .term (hT (by simp [dictTermRules, encodeBits]))
      · exact .term (hT (by simp [dictTermRules, encodeBits]))
    | cons a2 rest2 =>
      have hlen_sub : (a2 :: rest2).length ≤ b := by
        simp only [List.length_cons] at hsb ⊢
        omega
      have hsub : G.Derives (encodeBits (a2 :: rest2)) (a2 :: rest2) :=
        ih (by simp) hlen_sub
      have hhead : G.Derives (2 + encodeBits (a :: a2 :: rest2) % 2) [a] := by
        cases a
        · have : 2 + encodeBits (false :: a2 :: rest2) % 2 = 2 := by
            change 2 + (2 * encodeBits (a2 :: rest2) + 0) % 2 = 2
            omega
          rw [this]; exact .term (hT (by simp [dictTermRules]))
        · have : 2 + encodeBits (true :: a2 :: rest2) % 2 = 3 := by
            change 2 + (2 * encodeBits (a2 :: rest2) + 1) % 2 = 3
            omega
          rw [this]; exact .term (hT (by simp [dictTermRules]))
      have hge4 : 4 ≤ encodeBits (a :: a2 :: rest2) := by
        have := encodeBits_ge_pow (a :: a2 :: rest2)
        have hpow : 4 ≤ 2 ^ (a :: a2 :: rest2).length := by
          have h1 : 2 ≤ (a :: a2 :: rest2).length := by simp
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (a :: a2 :: rest2).length := Nat.pow_le_pow_right (by norm_num) h1
        omega
      have hlt : encodeBits (a :: a2 :: rest2) < 2 ^ (b + 1) := by
        have h1 := encodeBits_lt_pow (a :: a2 :: rest2)
        have h2 : 2 ^ ((a :: a2 :: rest2).length + 1) ≤ 2 ^ (b + 1) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hdiv : encodeBits (a :: a2 :: rest2) / 2 = encodeBits (a2 :: rest2) := by
        cases a
        · change (2 * encodeBits (a2 :: rest2) + 0) / 2 = encodeBits (a2 :: rest2); omega
        · change (2 * encodeBits (a2 :: rest2) + 1) / 2 = encodeBits (a2 :: rest2); omega
      have hrule : (encodeBits (a :: a2 :: rest2),
          2 + encodeBits (a :: a2 :: rest2) % 2,
          encodeBits (a :: a2 :: rest2) / 2) ∈ G.binRules := by
        apply hB
        unfold dictBinRules
        exact Finset.mem_image.mpr ⟨encodeBits (a :: a2 :: rest2),
          Finset.mem_Ico.mpr ⟨hge4, hlt⟩, rfl⟩
      rw [hdiv] at hrule
      exact .bin hrule hhead hsub

/-- Uniqueness of derivation for any dictionary nonterminal `m ∈ [2, 2^(b+1))` in any grammar
that adds no extra rules with LHS in `[2, 2^(b+1))`. -/
theorem dict_derives_unique (G : CNFGrammar) (b : ℕ)
    (hT : ∀ A a, (A, a) ∈ G.termRules → 2 ≤ A → A < 2 ^ (b + 1) → (A, a) ∈ dictTermRules)
    (hB : ∀ A B C, (A, B, C) ∈ G.binRules → 2 ≤ A → A < 2 ^ (b + 1) → (A, B, C) ∈ dictBinRules b) :
    ∀ m, 2 ≤ m → m < 2 ^ (b + 1) → ∀ w, G.Derives m w → encodeBits w = m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm2 hmlt w hder
    cases hder with
    | term hmem =>
      have hd := hT _ _ hmem hm2 hmlt
      simp only [dictTermRules, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hd
      rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [encodeBits]
    | @bin _ B C u v hmem hB1 hC1 =>
      have hd := hB _ _ _ hmem hm2 hmlt
      simp only [dictBinRules, Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq] at hd
      rcases hd with ⟨m', ⟨hm4, hm'lt⟩, hmEq, hBEq, hCEq⟩
      subst hmEq hBEq hCEq
      have hlt_bit : 2 + m' % 2 < 2 ^ (b + 1) := by omega
      have hu : encodeBits u = 2 + m' % 2 := ih (2 + m' % 2) (by omega) (by omega) hlt_bit u hB1
      have hv : encodeBits v = m' / 2 := ih (m' / 2) (by omega) (by omega) (by omega) v hC1
      have hu_eq : ∃ a : Bool, u = [a] ∧ (if a then 1 else 0) = m' % 2 := by
        by_cases hmod : m' % 2 = 0
        · rw [hmod] at hu
          have : u = [false] := encodeBits_inj (by simpa [encodeBits] using hu)
          exact ⟨false, this, by simp [hmod]⟩
        · have hmod1 : m' % 2 = 1 := by omega
          rw [hmod1] at hu
          have : u = [true] := encodeBits_inj (by simpa [encodeBits] using hu)
          exact ⟨true, this, by simp [hmod1]⟩
      rcases hu_eq with ⟨a, hua, hbit⟩
      rw [hua, List.singleton_append]
      simp only [encodeBits, hv, hbit]
      omega

/-- Exact language of `chainStartAux` when every list element derives a unique word. -/
theorem chain_derives_iff (G : CNFGrammar) (base : ℕ)
    (hNoTerm : ∀ A a, (A, a) ∈ G.termRules → A < base) :
    ∀ (zs : List ℕ) (idx cur : ℕ),
      chainBinRulesAux base idx cur zs ⊆ G.binRules →
      (∀ A B C, (A, B, C) ∈ G.binRules → base + idx ≤ A →
        (A, B, C) ∈ chainBinRulesAux base idx cur zs) →
      ∀ (ws : List (List Bool)) (w0 : List Bool) (hlen : ws.length = zs.length),
        (∀ w, G.Derives cur w ↔ w = w0) →
        (∀ i (hi : i < zs.length), ∀ w, G.Derives (zs[i]'hi) w ↔ w = ws[i]'(by omega)) →
        ∀ w, G.Derives (chainStartAux base idx cur zs) w ↔ w = w0 ++ ws.flatten := by
  intro zs
  induction zs with
  | nil =>
    intro idx cur _ _ ws w0 hlen hx _ w
    cases ws with
    | nil => simpa [chainStartAux] using hx w
    | cons _ _ => simp at hlen
  | cons y zs ih =>
    intro idx cur hsub honly ws w0 hlen hx hzs w
    cases ws with
    | nil => simp at hlen
    | cons wy ws' =>
      have hlen' : ws'.length = zs.length := by
        simp only [List.length_cons] at hlen; omega
      have hrule_xy : (base + idx, cur, y) ∈ G.binRules :=
        hsub (by simp [chainBinRulesAux])
      have hy : ∀ w', G.Derives y w' ↔ w' = wy := by
        intro w'
        have h0 := hzs 0 (by simp) w'
        simpa using h0
      have hbase_iff : ∀ w', G.Derives (base + idx) w' ↔ w' = w0 ++ wy := by
        intro w'
        constructor
        · intro hder
          cases hder with
          | term hm =>
            have := hNoTerm _ _ hm
            omega
          | bin hm hB hC =>
            have hmem := honly _ _ _ hm (le_refl _)
            have hmem0 : (base + idx, cur, y) ∈ chainBinRulesAux base idx cur (y :: zs) := by
              simp [chainBinRulesAux]
            have ⟨h1, h2⟩ := chainBinRulesAux_unique_lhs base (y :: zs) idx cur
              (base + idx) _ _ cur y hmem hmem0
            subst h1 h2
            rw [(hx _).mp hB, (hy _).mp hC]
        · intro hw'
          subst hw'
          exact .bin hrule_xy ((hx w0).mpr rfl) ((hy wy).mpr rfl)
      have hsub' : chainBinRulesAux base (idx + 1) (base + idx) zs ⊆ G.binRules := by
        intro r hr
        exact hsub (by simp [chainBinRulesAux, hr])
      have honly' : ∀ A B C, (A, B, C) ∈ G.binRules → base + (idx + 1) ≤ A →
          (A, B, C) ∈ chainBinRulesAux base (idx + 1) (base + idx) zs := by
        intro A B C hm hge
        have hmem := honly A B C hm (by omega)
        simp only [chainBinRulesAux, Finset.mem_insert, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, _, _⟩ | hrest
        · omega
        · exact hrest
      have hzs' : ∀ i (hi : i < zs.length), ∀ w',
          G.Derives (zs[i]'hi) w' ↔ w' = ws'[i]'(by omega) := by
        intro i hi w'
        have hstep := hzs (i + 1) (by simp [hi]) w'
        simpa using hstep
      have hres := ih (idx + 1) (base + idx) hsub' honly' ws' (w0 ++ wy) hlen' hbase_iff hzs' w
      simpa [chainStartAux, List.flatten_cons, List.append_assoc] using hres

/-- Wrapper around `chainBinRulesAux` / `chainStartAux` for a nonempty chunk list. -/
theorem fourRussians_core_spec (u : List Bool) (b : ℕ) (hb : 1 ≤ b) (hu : 2 ≤ u.length) :
    ∃ (uStart Bu Cu : ℕ) (cRules : Finset (ℕ × ℕ × ℕ)),
      cRules.card ≤ u.length / b ∧
      (∀ A B C, (A, B, C) ∈ cRules → 2 ^ (b + 1) + 1 ≤ A) ∧
      (∀ A B₁ C₁ B₂ C₂, (A, B₁, C₁) ∈ cRules → (A, B₂, C₂) ∈ cRules → B₁ = B₂ ∧ C₁ = C₂) ∧
      (uStart, Bu, Cu) ∈ dictBinRules b ∪ cRules ∧
      2 ≤ uStart ∧
      uStart ≠ 2 ^ (b + 1) ∧
      (∀ G : CNFGrammar,
        dictTermRules ⊆ G.termRules →
        dictBinRules b ∪ cRules ⊆ G.binRules →
        (∀ A a, (A, a) ∈ G.termRules → 2 ≤ A → A < 2 ^ (b + 1) → (A, a) ∈ dictTermRules) →
        (∀ A B C, (A, B, C) ∈ G.binRules → 2 ≤ A → A < 2 ^ (b + 1) → (A, B, C) ∈ dictBinRules b) →
        (∀ A a, (A, a) ∈ G.termRules → A < 2 ^ (b + 1) + 1) →
        (∀ A B C, (A, B, C) ∈ G.binRules → 2 ^ (b + 1) + 1 ≤ A → (A, B, C) ∈ cRules) →
        (∀ w, G.Derives uStart w ↔ w = u) ∧
        (∃ w1 w2, G.Derives Bu w1 ∧ G.Derives Cu w2 ∧ w1 ++ w2 = u)) := by
  let base := 2 ^ (b + 1) + 1
  have hcs_ne : splitChunks b hb u ≠ [] := splitChunks_nonempty b hb (by intro h; simp [h] at hu)
  have hcs_len := splitChunks_length_le b hb u
  have hcs_flat := splitChunks_flatten b hb u
  have hcs_bnds := splitChunks_mem_bounds b hb u
  generalize hcs_eq : splitChunks b hb u = cs at hcs_ne hcs_len hcs_flat hcs_bnds
  cases cs with
  | nil => exact (hcs_ne rfl).elim
  | cons c0 cs' =>
    let zs := cs'.map encodeBits
    let cRules := chainBinRulesAux base 0 (encodeBits c0) zs
    let uStart := chainStartAux base 0 (encodeBits c0) zs
    have hcRules_card : cRules.card ≤ u.length / b := by
      have h1 : cRules.card ≤ zs.length := chainBinRulesAux_card base zs 0 (encodeBits c0)
      have h2 : zs.length = cs'.length := List.length_map _
      have hcs_len' : cs'.length + 1 ≤ (u.length + b - 1) / b := by
        simpa only [List.length_cons] using hcs_len
      have h4 : (u.length + b - 1) / b = (u.length - 1) / b + 1 := by
        rw [show u.length + b - 1 = (u.length - 1) + b by omega, Nat.add_div_right _ (by omega)]
      have h5 : (u.length - 1) / b ≤ u.length / b := Nat.div_le_div_right (by omega)
      omega
    have hcRules_lhs : ∀ A B C, (A, B, C) ∈ cRules → 2 ^ (b + 1) + 1 ≤ A := by
      intro A B C hm
      have := mem_chainBinRulesAux_lhs base zs 0 (encodeBits c0) A B C hm
      dsimp only [base] at this
      omega
    have hcRules_uniq : ∀ A B₁ C₁ B₂ C₂,
        (A, B₁, C₁) ∈ cRules → (A, B₂, C₂) ∈ cRules → B₁ = B₂ ∧ C₁ = C₂ :=
      chainBinRulesAux_unique_lhs base zs 0 (encodeBits c0)
    have hpow4 : 4 ≤ 2 ^ (b + 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hbin_ex : ∃ Bu Cu, (uStart, Bu, Cu) ∈ dictBinRules b ∪ cRules ∧ 2 ≤ uStart ∧ uStart ≠ 2 ^ (b + 1) := by
      cases cs' with
      | nil =>
        have hc0 : c0 = u := by simpa using hcs_flat
        have ⟨_, hcb⟩ := hcs_bnds c0 (by simp)
        rw [hc0] at hcb
        have hge4 : 4 ≤ encodeBits u := by
          have := encodeBits_ge_pow u
          have : 4 ≤ 2 ^ u.length := by
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ u.length := Nat.pow_le_pow_right (by norm_num) hu
          omega
        have hlt : encodeBits u < 2 ^ (b + 1) := by
          have h1 := encodeBits_lt_pow u
          have h2 : 2 ^ (u.length + 1) ≤ 2 ^ (b + 1) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have huStart_eq : uStart = encodeBits u := by
          simp only [uStart, zs, List.map_nil, chainStartAux, hc0]
        refine ⟨2 + encodeBits u % 2, encodeBits u / 2, ?_, ?_, ?_⟩
        · apply Finset.mem_union_left
          rw [huStart_eq]
          unfold dictBinRules
          exact Finset.mem_image.mpr ⟨encodeBits u, Finset.mem_Ico.mpr ⟨hge4, hlt⟩, rfl⟩
        · omega
        · omega
      | cons c1 cs'' =>
        rcases chainStartAux_mem_rule base (cs''.map encodeBits) 0 (encodeBits c0) (encodeBits c1) with ⟨Bu, Cu, hm⟩
        have hge := chainStartAux_ge base (cs''.map encodeBits) 0 (encodeBits c0) (encodeBits c1)
        have hge' : 2 ^ (b + 1) + 1 ≤ uStart := by
          change 2 ^ (b + 1) + 1 ≤ chainStartAux base 0 (encodeBits c0) (encodeBits c1 :: cs''.map encodeBits)
          dsimp only [base] at hge ⊢
          omega
        refine ⟨Bu, Cu, Finset.mem_union_right _ hm, ?_, ?_⟩
        · omega
        · omega
    rcases hbin_ex with ⟨Bu, Cu, hBuCu, huStart_ge2, huStart_neR⟩
    refine ⟨uStart, Bu, Cu, cRules, hcRules_card, hcRules_lhs, hcRules_uniq, hBuCu, huStart_ge2, huStart_neR, ?_⟩
    intro G hTsub hBsub hTdict hBdict hNoTermChain hOnlyChain
    have hchunk_iff : ∀ c ∈ c0 :: cs', ∀ w, G.Derives (encodeBits c) w ↔ w = c := by
      intro c hc w
      have ⟨hc1, hcb⟩ := hcs_bnds c hc
      constructor
      · intro hder
        have hge2 : 2 ≤ encodeBits c := by
          have := encodeBits_ge_pow c
          have : 2 ≤ 2 ^ c.length := by
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ c.length := Nat.pow_le_pow_right (by norm_num) hc1
          omega
        have hlt : encodeBits c < 2 ^ (b + 1) := by
          have h1 := encodeBits_lt_pow c
          have h2 : 2 ^ (c.length + 1) ≤ 2 ^ (b + 1) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        exact encodeBits_inj (dict_derives_unique G b hTdict hBdict (encodeBits c) hge2 hlt w hder)
      · intro hw; subst hw
        exact dict_derives_self G b hTsub (Finset.union_subset_left hBsub) w hc1 hcb
    have huStart_iff : ∀ w, G.Derives uStart w ↔ w = u := by
      intro w
      have hres := chain_derives_iff G base hNoTermChain zs 0 (encodeBits c0)
        (Finset.union_subset_right hBsub) (by simpa only [base, Nat.add_zero] using hOnlyChain)
        cs' c0 (by simp [zs])
        (hchunk_iff c0 (by simp))
        (fun i hi => by
          intro w'
          have hi' : i < cs'.length := by simpa [zs] using hi
          have hget : zs[i]'hi = encodeBits (cs'[i]'hi') := List.getElem_map (f := encodeBits)
          rw [hget]
          exact hchunk_iff (cs'[i]'hi') (List.mem_cons_of_mem c0 (List.getElem_mem hi')) w')
        w
      rw [List.flatten_cons] at hcs_flat
      simpa only [uStart, hcs_flat] using hres
    refine ⟨huStart_iff, ?_⟩
    have hder_u : G.Derives uStart u := (huStart_iff u).mpr rfl
    cases hder_u with
    | term _ => simp at hu
    | @bin _ B1 C1 u1 v1 hm hB1 hC1 =>
      have huniq : B1 = Bu ∧ C1 = Cu := by
        by_cases hlt : uStart < 2 ^ (b + 1)
        · have h1 := hBdict _ _ _ hm huStart_ge2 hlt
          have h2 := hBdict _ _ _ (hBsub hBuCu) huStart_ge2 hlt
          simp only [dictBinRules, Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq] at h1 h2
          rcases h1 with ⟨m1, _, rfl, rfl, rfl⟩
          rcases h2 with ⟨m2, _, hmEq, rfl, rfl⟩
          subst hmEq; exact ⟨rfl, rfl⟩
        · have hge : 2 ^ (b + 1) + 1 ≤ uStart := by omega
          exact hcRules_uniq uStart B1 C1 Bu Cu (hOnlyChain _ _ _ hm hge) (hOnlyChain _ _ _ (hBsub hBuCu) hge)
      rcases huniq with ⟨rfl, rfl⟩
      exact ⟨u1, v1, hB1, hC1, rfl⟩

/-- Strict CNF grammar accepting `u ++ Σ*` (prefix `u`) for any `u` with `2 ≤ u.length`,
using at most `2^(b+1) + u.length / b + 5` productions. -/
theorem prefix_cnf_exists (u : List Bool) (b : ℕ) (hb : 1 ≤ b) (hu : 2 ≤ u.length) :
    ∃ G : CNFGrammar,
      (∀ w, G.Accepts w ↔ u <+: w) ∧
      G.prodCount ≤ 2 ^ (b + 1) + u.length / b + 5 := by
  rcases fourRussians_core_spec u b hb hu with
    ⟨uStart, Bu, Cu, cRules, hcCard, hcLhs, _, hBuCu, _, _, hCore⟩
  have hpow4 : 4 ≤ 2 ^ (b + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  let G : CNFGrammar :=
    { start := 1
      termRules := dictTermRules ∪ {(0, false), (0, true)}
      binRules := (dictBinRules b ∪ cRules) ∪ {(0, 0, 0), (1, Bu, Cu), (1, uStart, 0)} }
  have hTdict : ∀ A a, (A, a) ∈ G.termRules → 2 ≤ A → A < 2 ^ (b + 1) → (A, a) ∈ dictTermRules := by
    intro A a hm h2 _
    simp only [G, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
    rcases hm with hd | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hd
    · omega
    · omega
  have hBdict : ∀ A B C, (A, B, C) ∈ G.binRules → 2 ≤ A → A < 2 ^ (b + 1) → (A, B, C) ∈ dictBinRules b := by
    intro A B C hm h2 hlt
    simp only [G, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
    rcases hm with (hd | hc) | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hd
    · have := hcLhs A B C hc; omega
    · omega
    · omega
    · omega
  have hNoTermChain : ∀ A a, (A, a) ∈ G.termRules → A < 2 ^ (b + 1) + 1 := by
    intro A a hm
    simp only [G, dictTermRules, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
    rcases hm with (⟨rfl, _⟩ | ⟨rfl, _⟩) | (⟨rfl, _⟩ | ⟨rfl, _⟩) <;> omega
  have hOnlyChain : ∀ A B C, (A, B, C) ∈ G.binRules → 2 ^ (b + 1) + 1 ≤ A → (A, B, C) ∈ cRules := by
    intro A B C hm hge
    simp only [G, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
    rcases hm with (hd | hc) | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · simp only [dictBinRules, Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq] at hd
      rcases hd with ⟨m, ⟨_, hmlt⟩, rfl, _, _⟩; omega
    · exact hc
    · omega
    · omega
    · omega
  have ⟨huStart_iff, hBuCu_ex⟩ := hCore G Finset.subset_union_left Finset.subset_union_left
    hTdict hBdict hNoTermChain hOnlyChain
  have hALL_iff : ∀ w, G.Derives 0 w ↔ w ≠ [] := by
    intro w; constructor
    · exact derives_nonempty G
    · intro hne
      induction w with
      | nil => exact (hne rfl).elim
      | cons a rest ih =>
        cases rest with
        | nil => cases a <;> exact .term (by simp [G])
        | cons a2 r2 =>
          have h1 : G.Derives 0 [a] := by cases a <;> exact .term (by simp [G])
          exact .bin (by simp [G]) h1 (ih (by simp))
  have hBuCu_der : ∀ w, G.Derives Bu w → ∀ v, G.Derives Cu v → w ++ v = u := by
    intro w hw v hv
    exact (huStart_iff (w ++ v)).mp (.bin (Finset.mem_union_left _ hBuCu) hw hv)
  refine ⟨G, ?_, ?_⟩
  · intro w; constructor
    · intro hacc
      cases hacc with
      | term hm =>
        simp only [G, dictTermRules, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
        rcases hm with (⟨h, _⟩ | ⟨h, _⟩) | (⟨h, _⟩ | ⟨h, _⟩) <;> omega
      | @bin _ B1 C1 u1 v1 hm hB1 hC1 =>
        simp only [G, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
        rcases hm with (hd | hc) | ⟨h0, _⟩ | ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩
        · simp only [dictBinRules, Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq] at hd
          rcases hd with ⟨m, ⟨hm4, _⟩, h1, _, _⟩; omega
        · have := hcLhs 1 B1 C1 hc; omega
        · omega
        · rw [hBuCu_der u1 hB1 v1 hC1]
        · rw [(huStart_iff u1).mp hB1]; exact ⟨v1, rfl⟩
    · rintro ⟨v, rfl⟩
      cases v with
      | nil =>
        rcases hBuCu_ex with ⟨w1, w2, hw1, hw2, heq⟩
        rw [List.append_nil, ← heq]
        exact .bin (by simp [G]) hw1 hw2
      | cons c rest =>
        exact .bin (by simp [G]) ((huStart_iff u).mpr rfl) ((hALL_iff (c :: rest)).mpr (by simp))
  · have hTcard : G.termRules.card ≤ 4 := by
      calc G.termRules.card ≤ dictTermRules.card + ({(0, false), (0, true)} : Finset _).card :=
            Finset.card_union_le _ _
        _ ≤ 2 + 2 := Nat.add_le_add dictTermRules_card (by decide)
        _ = 4 := by norm_num
    have hBcard : G.binRules.card ≤ (2 ^ (b + 1) - 4) + u.length / b + 3 := by
      have hc1 : (dictBinRules b ∪ cRules).card ≤ (dictBinRules b).card + cRules.card :=
        Finset.card_union_le _ _
      have hc2 : ({(0, 0, 0), (1, Bu, Cu), (1, uStart, 0)} : Finset (ℕ × ℕ × ℕ)).card ≤ 3 := by
        calc ({(0, 0, 0), (1, Bu, Cu), (1, uStart, 0)} : Finset (ℕ × ℕ × ℕ)).card
            ≤ ({(1, Bu, Cu), (1, uStart, 0)} : Finset (ℕ × ℕ × ℕ)).card + 1 := Finset.card_insert_le _ _
          _ ≤ (({(1, uStart, 0)} : Finset (ℕ × ℕ × ℕ)).card + 1) + 1 :=
              Nat.add_le_add_right (Finset.card_insert_le _ _) 1
          _ = 3 := by simp
      have hc3 : G.binRules.card ≤ (dictBinRules b ∪ cRules).card +
          ({(0, 0, 0), (1, Bu, Cu), (1, uStart, 0)} : Finset (ℕ × ℕ × ℕ)).card :=
        Finset.card_union_le _ _
      have hd := dictBinRules_card b
      omega
    unfold CNFGrammar.prodCount
    omega

/-- Strict CNF grammar accepting `Σ* ++ u ++ Σ*` (contiguous factor `u`) for any `u` with
`2 ≤ u.length`, using at most `2^(b+1) + u.length / b + 8` productions. -/
theorem factor_cnf_exists (u : List Bool) (b : ℕ) (hb : 1 ≤ b) (hu : 2 ≤ u.length) :
    ∃ G : CNFGrammar,
      (∀ w, G.Accepts w ↔ u <:+: w) ∧
      G.prodCount ≤ 2 ^ (b + 1) + u.length / b + 8 := by
  rcases fourRussians_core_spec u b hb hu with
    ⟨uStart, Bu, Cu, cRules, hcCard, hcLhs, _, hBuCu, _, _, hCore⟩
  let R := 2 ^ (b + 1)
  have hpow4 : 4 ≤ R := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  let G : CNFGrammar :=
    { start := 1
      termRules := dictTermRules ∪ {(0, false), (0, true)}
      binRules := (dictBinRules b ∪ cRules) ∪
        {(0, 0, 0), (R, uStart, 0), (1, Bu, Cu), (1, 0, uStart), (1, uStart, 0), (1, 0, R)} }
  have hTdict : ∀ A a, (A, a) ∈ G.termRules → 2 ≤ A → A < R → (A, a) ∈ dictTermRules := by
    intro A a hm h2 _
    simp only [G, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
    rcases hm with hd | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hd
    · omega
    · omega
  have hBdict : ∀ A B C, (A, B, C) ∈ G.binRules → 2 ≤ A → A < R → (A, B, C) ∈ dictBinRules b := by
    intro A B C hm h2 hlt
    simp only [G, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
    rcases hm with (hd | hc) | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hd
    · have := hcLhs A B C hc; dsimp only [R] at hlt; omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have hNoTermChain : ∀ A a, (A, a) ∈ G.termRules → A < R + 1 := by
    intro A a hm
    simp only [G, dictTermRules, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
    rcases hm with (⟨rfl, _⟩ | ⟨rfl, _⟩) | (⟨rfl, _⟩ | ⟨rfl, _⟩) <;> omega
  have hOnlyChain : ∀ A B C, (A, B, C) ∈ G.binRules → R + 1 ≤ A → (A, B, C) ∈ cRules := by
    intro A B C hm hge
    simp only [G, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
    rcases hm with (hd | hc) | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · simp only [dictBinRules, Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq] at hd
      rcases hd with ⟨m, ⟨_, hmlt⟩, rfl, _, _⟩; dsimp only [R] at hge; omega
    · exact hc
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have ⟨huStart_iff, hBuCu_ex⟩ := hCore G Finset.subset_union_left Finset.subset_union_left
    hTdict hBdict hNoTermChain hOnlyChain
  have hALL_iff : ∀ w, G.Derives 0 w ↔ w ≠ [] := by
    intro w; constructor
    · exact derives_nonempty G
    · intro hne
      induction w with
      | nil => exact (hne rfl).elim
      | cons a rest ih =>
        cases rest with
        | nil => cases a <;> exact .term (by simp [G])
        | cons a2 r2 =>
          have h1 : G.Derives 0 [a] := by cases a <;> exact .term (by simp [G])
          exact .bin (by simp [G]) h1 (ih (by simp))
  have hR_iff : ∀ w, G.Derives R w ↔ ∃ s, s ≠ [] ∧ w = u ++ s := by
    intro w; constructor
    · intro hder
      cases hder with
      | term hm =>
        simp only [G, dictTermRules, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
        rcases hm with (⟨h, _⟩ | ⟨h, _⟩) | (⟨h, _⟩ | ⟨h, _⟩) <;> omega
      | @bin _ B1 C1 u1 v1 hm hB1 hC1 =>
        simp only [G, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
        rcases hm with (hd | hc) | ⟨h0, _⟩ | ⟨_, rfl, rfl⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩
        · simp only [dictBinRules, Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq] at hd
          rcases hd with ⟨m, ⟨_, hmlt⟩, hEq, _, _⟩; dsimp only [R] at hEq; omega
        · have := hcLhs R B1 C1 hc; dsimp only [R] at this; omega
        · omega
        · exact ⟨v1, (hALL_iff v1).mp hC1, by rw [(huStart_iff u1).mp hB1]⟩
        · omega
        · omega
        · omega
        · omega
    · rintro ⟨s, hs, rfl⟩
      exact .bin (by simp [G]) ((huStart_iff u).mpr rfl) ((hALL_iff s).mpr hs)
  have hBuCu_der : ∀ w, G.Derives Bu w → ∀ v, G.Derives Cu v → w ++ v = u := by
    intro w hw v hv
    exact (huStart_iff (w ++ v)).mp (.bin (Finset.mem_union_left _ hBuCu) hw hv)
  refine ⟨G, ?_, ?_⟩
  · intro w; constructor
    · intro hacc
      cases hacc with
      | term hm =>
        simp only [G, dictTermRules, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
        rcases hm with (⟨h, _⟩ | ⟨h, _⟩) | (⟨h, _⟩ | ⟨h, _⟩) <;> omega
      | @bin _ B1 C1 u1 v1 hm hB1 hC1 =>
        simp only [G, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
        rcases hm with (hd | hc) | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩
        · simp only [dictBinRules, Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq] at hd
          rcases hd with ⟨m, ⟨hm4, _⟩, h1, _, _⟩; omega
        · have := hcLhs 1 B1 C1 hc; dsimp only [R] at hpow4; omega
        · omega
        · omega
        · rw [hBuCu_der u1 hB1 v1 hC1]
        · rw [(huStart_iff v1).mp hC1]; exact ⟨u1, [], by simp⟩
        · rw [(huStart_iff u1).mp hB1]; exact ⟨[], v1, by simp⟩
        · rcases (hR_iff v1).mp hC1 with ⟨s, _, heq⟩
          rw [heq]
          exact ⟨u1, s, by simp [List.append_assoc]⟩
    · rintro ⟨p, s, rfl⟩
      cases p with
      | nil =>
        cases s with
        | nil =>
          rcases hBuCu_ex with ⟨w1, w2, hw1, hw2, heq⟩
          simp only [List.nil_append, List.append_nil]
          rw [← heq]
          exact .bin (by simp [G]) hw1 hw2
        | cons cs rs =>
          simp only [List.nil_append]
          exact .bin (by simp [G]) ((huStart_iff u).mpr rfl) ((hALL_iff (cs :: rs)).mpr (by simp))
      | cons cp rp =>
        cases s with
        | nil =>
          simp only [List.append_nil]
          exact .bin (by simp [G]) ((hALL_iff (cp :: rp)).mpr (by simp)) ((huStart_iff u).mpr rfl)
        | cons cs rs =>
          rw [List.append_assoc]
          exact .bin (by simp [G]) ((hALL_iff (cp :: rp)).mpr (by simp))
            ((hR_iff (u ++ cs :: rs)).mpr ⟨cs :: rs, by simp, rfl⟩)
  · have hTcard : G.termRules.card ≤ 4 := by
      calc G.termRules.card ≤ dictTermRules.card + ({(0, false), (0, true)} : Finset _).card :=
            Finset.card_union_le _ _
        _ ≤ 2 + 2 := Nat.add_le_add dictTermRules_card (by decide)
        _ = 4 := by norm_num
    have hBcard : G.binRules.card ≤ (2 ^ (b + 1) - 4) + u.length / b + 6 := by
      have hc1 : (dictBinRules b ∪ cRules).card ≤ (dictBinRules b).card + cRules.card :=
        Finset.card_union_le _ _
      have hc2 : ({(0, 0, 0), (R, uStart, 0), (1, Bu, Cu), (1, 0, uStart), (1, uStart, 0), (1, 0, R)} :
          Finset (ℕ × ℕ × ℕ)).card ≤ 6 := by
        refine (Finset.card_insert_le _ _).trans ?_
        refine Nat.add_le_add_right ((Finset.card_insert_le _ _).trans ?_) 1
        refine Nat.add_le_add_right ((Finset.card_insert_le _ _).trans ?_) 1
        refine Nat.add_le_add_right ((Finset.card_insert_le _ _).trans ?_) 1
        refine Nat.add_le_add_right ((Finset.card_insert_le _ _).trans ?_) 1
        simp
      have hc3 : G.binRules.card ≤ (dictBinRules b ∪ cRules).card +
          ({(0, 0, 0), (R, uStart, 0), (1, Bu, Cu), (1, 0, uStart), (1, uStart, 0), (1, 0, R)} :
            Finset (ℕ × ℕ × ℕ)).card :=
        Finset.card_union_le _ _
      have hd := dictBinRules_card b
      omega
    unfold CNFGrammar.prodCount
    dsimp only [R] at hpow4
    omega

/-- **Theorem A (Upper Bound):** Every binary word `w` of length `n` with no repeated factor
of length `r` (`r ≥ 1`) is separated from EVERY distinct equal-length word `x` by a strict CNF
grammar with at most `2^(b + 1) + (r + 1) / b + 8` productions (for any `b ≥ 1`). -/
theorem uniq_factor_cnf_separation {n r b : ℕ} (hr : 1 ≤ r) (hb : 1 ≤ b)
    {w x : List Bool} (hw : w.length = n) (hx : x.length = n) (hne : w ≠ x)
    (huniq : HasNoRepeatedFactor w r) :
    ∃ G : CNFGrammar, G.Separates w x ∧ G.prodCount ≤ 2 ^ (b + 1) + (r + 1) / b + 8 := by
  have hex : ∃ i, i < n ∧ w[i]? ≠ x[i]? := by
    by_contra h
    push Not at h
    apply hne
    apply List.ext_getElem?
    intro i
    by_cases hi : i < n
    · exact h i hi
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  let t := Nat.find hex
  have ht_spec : t < n ∧ w[t]? ≠ x[t]? := Nat.find_spec hex
  have ht_min : ∀ i < t, w[i]? = x[i]? := by
    intro i hi
    by_contra hne_i
    exact Nat.find_min hex hi ⟨by omega, hne_i⟩
  have hprefix_eq : w.take t = x.take t := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < t
    · simp only [List.getElem?_take_of_lt hi]
      exact ht_min i hi
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  have hpow4 : 4 ≤ 2 ^ (b + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  by_cases ht0 : t = 0
  · have h0ne : w[0]'(by omega) ≠ x[0]'(by omega) := by
      have := ht_spec.2
      rw [ht0, List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at this
      intro heq; exact this (congrArg some heq)
    let a0 := w[0]'(by omega)
    let G : CNFGrammar :=
      { start := 1
        termRules := {(1, a0), (2, a0), (0, false), (0, true)}
        binRules := {(0, 0, 0), (1, 2, 0)} }
    have hALL : ∀ v, G.Derives 0 v ↔ v ≠ [] := by
      intro v; constructor
      · exact derives_nonempty G
      · intro hv
        induction v with
        | nil => exact (hv rfl).elim
        | cons c rest ih =>
          cases rest with
          | nil => cases c <;> exact .term (by simp [G])
          | cons c2 r2 =>
            have h1 : G.Derives 0 [c] := by cases c <;> exact .term (by simp [G])
            exact .bin (by simp [G]) h1 (ih (by simp))
    have h2 : ∀ v, G.Derives 2 v ↔ v = [a0] := by
      intro v; constructor
      · intro hd; cases hd with
        | term hm =>
          simp only [G, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
          rcases hm with ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩
          · omega
          · rfl
          · omega
          · omega
        | bin hm _ _ =>
          simp only [G, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
          rcases hm with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
      · intro hv; subst hv; exact .term (by simp [G])
    have hacc_iff : ∀ v, G.Accepts v ↔ ∃ rest, v = a0 :: rest := by
      intro v; constructor
      · intro hd; cases hd with
        | term hm =>
          simp only [G, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
          rcases hm with ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
          · exact ⟨[], rfl⟩
          · omega
          · omega
          · omega
        | @bin _ _ _ u1 v1 hm hB hC =>
          simp only [G, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
          rcases hm with ⟨h, _⟩ | ⟨_, rfl, rfl⟩
          · omega
          · rw [(h2 u1).mp hB]; exact ⟨v1, rfl⟩
      · rintro ⟨rest, rfl⟩
        cases rest with
        | nil => exact .term (by simp [G])
        | cons c rs => exact .bin (by simp [G]) ((h2 [a0]).mpr rfl) ((hALL _).mpr (by simp))
    refine ⟨G, Or.inl ⟨?_, ?_⟩, ?_⟩
    · rw [hacc_iff]
      cases hw' : w with
      | nil => simp [hw'] at hw; omega
      | cons c rs =>
        have : c = a0 := by simp [a0, hw']
        exact ⟨rs, by rw [this]⟩
    · rw [hacc_iff]
      rintro ⟨rs, hxeq⟩
      apply h0ne
      have : x[0]'(by omega) = a0 := by simp [hxeq]
      exact this.symm
    · unfold CNFGrammar.prodCount
      have hc1 : G.termRules.card ≤ 4 := by
        refine (Finset.card_insert_le _ _).trans ?_
        refine Nat.add_le_add_right ((Finset.card_insert_le _ _).trans ?_) 1
        refine Nat.add_le_add_right ((Finset.card_insert_le _ _).trans ?_) 1
        simp
      have hc2 : G.binRules.card ≤ 2 := by
        refine (Finset.card_insert_le _ _).trans ?_
        simp
      have h0 : 0 ≤ (r + 1) / b := Nat.zero_le _
      omega
  · by_cases htr : t < r
    · let u := w.take (t + 1)
      have hu_len : u.length = t + 1 := by simp [u]; omega
      rcases prefix_cnf_exists u b hb (by omega) with ⟨G, hG, hcard⟩
      refine ⟨G, Or.inl ⟨(hG w).mpr (List.take_prefix (t + 1) w), ?_⟩, ?_⟩
      · intro hacc
        have hpref : u <+: x := (hG x).mp hacc
        rcases hpref with ⟨s, hxs⟩
        have hwt : u[t]'(by omega) = w[t]'(by omega) := by simp [u]
        have hxt : u[t]'(by omega) = x[t]'(by omega) := by
          have : x[t]'(by omega) = (u ++ s)[t]'(by rw [hxs]; omega) := by simp [hxs]
          rw [this, List.getElem_append_left (by omega)]
        apply ht_spec.2
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
        exact congrArg some (hwt.symm.trans hxt)
      · have hdiv : u.length / b ≤ (r + 1) / b := Nat.div_le_div_right (by omega)
        omega
    · let v := (w.drop (t - r)).take r
      let u' := v ++ [x[t]'(by omega)]
      have hv_len : v.length = r := by simp [v]; omega
      have hu'_len : u'.length = r + 1 := by simp [u', hv_len]
      have hv_eq_x : v = (x.drop (t - r)).take r := by
        have h1 : (w.take t).drop (t - r) = v := by
          rw [List.drop_take]
          have : t - (t - r) = r := by omega
          rw [this]
        have h2 : (x.take t).drop (t - r) = (x.drop (t - r)).take r := by
          rw [List.drop_take]
          have : t - (t - r) = r := by omega
          rw [this]
        rw [← h1, hprefix_eq, h2]
      have hu'_in_x : u' <:+: x := by
        refine ⟨x.take (t - r), x.drop (t + 1), ?_⟩
        have hsplit1 : x.take (t - r) ++ x.drop (t - r) = x := List.take_append_drop _ _
        have hsplit2 : (x.drop (t - r)).take (r + 1) ++ (x.drop (t - r)).drop (r + 1) = x.drop (t - r) :=
          List.take_append_drop _ _
        have htake : (x.drop (t - r)).take (r + 1) = u' := by
          rw [List.take_add_one, List.getElem?_drop]
          have hidx : t - r + r = t := by omega
          rw [hidx, List.getElem?_eq_getElem (by omega)]
          simp [u', hv_eq_x]
        have hdrop : (x.drop (t - r)).drop (r + 1) = x.drop (t + 1) := by
          rw [List.drop_drop]
          congr 1; omega
        rw [htake, hdrop] at hsplit2
        rw [List.append_assoc, hsplit2, hsplit1]
      have hu'_not_in_w : ¬ u' <:+: w := by
        rintro ⟨p, s, hpw⟩
        have hp_len : p.length + r + 1 ≤ w.length := by
          have := congrArg List.length hpw
          simp only [List.length_append, hu'_len] at this
          omega
        have hv_at_p : (w.drop p.length).take r = v := by
          rw [← hpw, List.append_assoc, List.drop_left, List.take_append_of_le_length (by simp [u', hv_len]),
            List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
        have hp_eq : p.length = t - r := by
          rcases lt_trichotomy p.length (t - r) with hlt | heq | hgt
          · exact (huniq p.length (t - r) hlt (by omega) hv_at_p).elim
          · exact heq
          · exact (huniq (t - r) p.length hgt (by omega) hv_at_p.symm).elim
        have hw_bit : w[t]? = x[t]? := by
          rw [← hpw, List.append_assoc,
            List.getElem?_append_right (by omega : p.length ≤ t),
            List.getElem?_append_left (by simp [u', hv_len]; omega)]
          dsimp only [u']
          rw [List.getElem?_append_right (by omega : v.length ≤ t - p.length)]
          have hsub : t - p.length - v.length = 0 := by omega
          rw [hsub, List.getElem?_eq_getElem (by omega : t < x.length)]
          rfl
        exact ht_spec.2 hw_bit
      rcases factor_cnf_exists u' b hb (by omega) with ⟨G, hG, hcard⟩
      refine ⟨G, Or.inr ⟨(hG x).mpr hu'_in_x, fun hacc => hu'_not_in_w ((hG w).mp hacc)⟩, ?_⟩
      simpa [hu'_len] using hcard

/-! ### Exact Overlap Identity & Density of `W_uniq(n, r)` -/

/-- Set of `Fin n → Bool` words whose length-`r` factors at `i` and `j` coincide. -/
def SameFactor (n r i j : ℕ) (w : Fin n → Bool) : Prop :=
  ∀ k : ℕ, (hk : k < r) → (hi : i + k < n) → (hj : j + k < n) → w ⟨i + k, hi⟩ = w ⟨j + k, hj⟩

instance (n r i j : ℕ) : DecidablePred (SameFactor n r i j) := by
  intro w
  unfold SameFactor
  infer_instance

/-- Extend any free-coordinate assignment outside `[j, j + r)` uniquely to a word in
`SameFactor n r i j` by strong recursion when `i < j`. -/
def extendSameFactor (n r i j : ℕ) (hij : i < j)
    (f : { m : Fin n // ¬ (j ≤ m.val ∧ m.val < j + r) } → Bool) :
    ∀ m : ℕ, m < n → Bool
  | m, hm =>
    if h : j ≤ m ∧ m < j + r then
      have hlt : i + (m - j) < m := by omega
      extendSameFactor n r i j hij f (i + (m - j)) (by omega)
    else
      f ⟨⟨m, hm⟩, h⟩
termination_by m => m

theorem extendSameFactor_outside (n r i j : ℕ) (hij : i < j)
    (f : { m : Fin n // ¬ (j ≤ m.val ∧ m.val < j + r) } → Bool)
    (m : Fin n) (hm : ¬ (j ≤ m.val ∧ m.val < j + r)) :
    extendSameFactor n r i j hij f m.val m.isLt = f ⟨m, hm⟩ := by
  rw [extendSameFactor]
  exact dif_neg hm

theorem extendSameFactor_same (n r i j : ℕ) (hij : i < j)
    (f : { m : Fin n // ¬ (j ≤ m.val ∧ m.val < j + r) } → Bool) :
    SameFactor n r i j (fun m => extendSameFactor n r i j hij f m.val m.isLt) := by
  intro k hk hi hj
  have hcond : j ≤ j + k ∧ j + k < j + r := by omega
  have hrhs : extendSameFactor n r i j hij f (j + k) hj =
      extendSameFactor n r i j hij f (i + (j + k - j)) (by omega) := by
    rw [extendSameFactor]
    exact dif_pos hcond
  have hsub : j + k - j = k := by omega
  simpa [hsub] using hrhs.symm

theorem extendSameFactor_unique (n r i j : ℕ) (hij : i < j) (hjr : j + r ≤ n)
    (w : Fin n → Bool) (hw : SameFactor n r i j w) :
    ∀ m (hm : m < n),
      extendSameFactor n r i j hij (fun x => w x.val) m hm = w ⟨m, hm⟩ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rw [extendSameFactor]
    by_cases hcond : j ≤ m ∧ m < j + r
    · rw [dif_pos hcond]
      rw [ih (i + (m - j)) (by omega) (by omega)]
      have hEq := hw (m - j) (by omega) (by omega) (by omega)
      have hmEq : j + (m - j) = m := by omega
      simpa [hmEq] using hEq
    · rw [dif_neg hcond]

/-- **Exact Overlap Identity:** For EVERY `0 ≤ i < j` with `j + r ≤ n` (whether the two
factors `[i, i+r)` and `[j, j+r)` overlap or are disjoint!), the number of `w : Fin n → Bool`
agreeing on `[i, i+r)` and `[j, j+r)` is EXACTLY `2 ^ (n - r)`. -/
theorem eq_factor_card (n r i j : ℕ) (hij : i < j) (hjr : j + r ≤ n) :
    (Finset.univ.filter (SameFactor n r i j)).card = 2 ^ (n - r) := by
  let S_free := { m : Fin n // ¬ (j ≤ m.val ∧ m.val < j + r) }
  let e : { w : Fin n → Bool // SameFactor n r i j w } ≃ (S_free → Bool) :=
    { toFun := fun w x => w.val x.val
      invFun := fun f =>
        ⟨fun m => extendSameFactor n r i j hij f m.val m.isLt,
         extendSameFactor_same n r i j hij f⟩
      left_inv := fun w => by
        ext m
        exact extendSameFactor_unique n r i j hij hjr w.val w.property m.val m.isLt
      right_inv := fun f => by
        ext x
        exact extendSameFactor_outside n r i j hij f x.val x.property }
  have hcard_free : Fintype.card S_free = n - r := by
    have hsub : (Finset.univ.filter (fun m : Fin n => j ≤ m.val ∧ m.val < j + r)).card = r := by
      have himg : Finset.univ.filter (fun m : Fin n => j ≤ m.val ∧ m.val < j + r) =
          (Finset.range r).attach.image
            (fun k => (⟨j + k.val, by have := Finset.mem_range.mp k.property; omega⟩ : Fin n)) := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_attach,
          true_and, Subtype.exists, Finset.mem_range]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨m.val - j, by omega, by ext; dsimp; omega⟩
        · rintro ⟨k, hk, rfl⟩
          exact ⟨by dsimp; omega, by dsimp; omega⟩
      rw [himg, Finset.card_image_of_injective]
      · simp
      · intro a b hab
        ext
        have := congrArg Fin.val hab
        dsimp at this
        omega
    have hcomp : Fintype.card S_free =
        (Finset.univ.filter (fun m : Fin n => ¬ (j ≤ m.val ∧ m.val < j + r))).card :=
      Fintype.card_subtype _
    have hsum := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun m : Fin n => j ≤ m.val ∧ m.val < j + r)
    rw [Finset.card_univ, Fintype.card_fin, hsub] at hsum
    omega
  calc
    (Finset.univ.filter (SameFactor n r i j)).card
        = Fintype.card { w : Fin n → Bool // SameFactor n r i j w } := (Fintype.card_subtype _).symm
    _ = Fintype.card (S_free → Bool) := Fintype.card_congr e
    _ = 2 ^ Fintype.card S_free := by simp
    _ = 2 ^ (n - r) := by rw [hcard_free]

/-- The set of all binary words of length `n` (`Fin n → Bool`) with no repeated length-`r` factor. -/
noncomputable def WUniq (n r : ℕ) : Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.filter (fun w => HasNoRepeatedFactor (List.ofFn w) r)

/-- Conversion between `SameFactor` on `w : Fin n → Bool` and factor equality on `List.ofFn w`. -/
theorem sameFactor_iff_ofFn (n r i j : ℕ) (hjr : j + r ≤ n) (hij : i < j) (w : Fin n → Bool) :
    SameFactor n r i j w ↔
      ((List.ofFn w).drop i).take r = ((List.ofFn w).drop j).take r := by
  constructor
  · intro hsf
    apply List.ext_getElem
    · simp; omega
    · intro k hk1 hk2
      simp only [List.length_take, List.length_drop, List.length_ofFn] at hk1
      have hkr : k < r := by omega
      simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
      exact hsf k hkr (by omega) (by omega)
  · intro heq k hk hi hj
    have hget := congrArg (fun l => l[k]?) heq
    have h1 : (((List.ofFn w).drop i).take r)[k]? = some (w ⟨i + k, hi⟩) := by
      rw [List.getElem?_take_of_lt hk, List.getElem?_drop, List.getElem?_ofFn]
      simp [hi]
    have h2 : (((List.ofFn w).drop j).take r)[k]? = some (w ⟨j + k, hj⟩) := by
      rw [List.getElem?_take_of_lt hk, List.getElem?_drop, List.getElem?_ofFn]
      simp [hj]
    rw [h1, h2] at hget
    exact Option.some.inj hget

/-- **Theorem A (Density Bound):** For all `n` and `r ≥ 1`,
`2^n ≤ (WUniq n r).card + n.choose 2 * 2^(n - r)`. -/
theorem uniq_factor_card_lower (n r : ℕ) (hr : 1 ≤ r) :
    2 ^ n ≤ (WUniq n r).card + n.choose 2 * 2 ^ (n - r) := by
  classical
  let pairs := ((Finset.range n ×ˢ Finset.range n).filter (fun p => p.1 < p.2 ∧ p.2 + r ≤ n))
  have hpairs_card : pairs.card ≤ n.choose 2 := by
    have hsub : pairs ⊆ ((Finset.range n).powersetCard 2).image (fun s =>
        if h : s.Nonempty then (s.min' h, s.max' h) else (0, 0)) := by
      intro p hp
      simp only [pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      rcases hp with ⟨⟨hp1, hp2⟩, hlt, _⟩
      simp only [Finset.mem_image, Finset.mem_powersetCard]
      refine ⟨{p.1, p.2}, ⟨?_, Finset.card_pair (by omega)⟩, ?_⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
      · have hne : ({p.1, p.2} : Finset ℕ).Nonempty := ⟨p.1, by simp⟩
        rw [dif_pos hne]
        ext
        · simp [le_of_lt hlt]
        · simp [le_of_lt hlt]
    calc pairs.card
        ≤ (((Finset.range n).powersetCard 2).image _).card := Finset.card_le_card hsub
      _ ≤ ((Finset.range n).powersetCard 2).card := Finset.card_image_le
      _ = n.choose 2 := by simp
  let bad := pairs.biUnion (fun p => Finset.univ.filter (SameFactor n r p.1 p.2))
  have hcover : (Finset.univ : Finset (Fin n → Bool)) ⊆ WUniq n r ∪ bad := by
    intro w _
    by_cases hw : HasNoRepeatedFactor (List.ofFn w) r
    · exact Finset.mem_union_left _ (by simp [WUniq, hw])
    · apply Finset.mem_union_right
      unfold HasNoRepeatedFactor at hw
      push Not at hw
      rcases hw with ⟨i, j, hij, hjr, heq⟩
      simp only [List.length_ofFn] at hjr
      simp only [bad, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨(i, j), ?_, (sameFactor_iff_ofFn n r i j hjr hij w).mpr heq⟩
      simp only [pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨by omega, by omega⟩, hij, hjr⟩
  have hbad_card : bad.card ≤ n.choose 2 * 2 ^ (n - r) := by
    calc bad.card
        ≤ ∑ p ∈ pairs, (Finset.univ.filter (SameFactor n r p.1 p.2)).card := Finset.card_biUnion_le
      _ = ∑ _p ∈ pairs, 2 ^ (n - r) := by
          apply Finset.sum_congr rfl
          intro p hp
          simp only [pairs, Finset.mem_filter] at hp
          exact eq_factor_card n r p.1 p.2 hp.2.1 hp.2.2
      _ = pairs.card * 2 ^ (n - r) := by simp
      _ ≤ n.choose 2 * 2 ^ (n - r) := Nat.mul_le_mul_right _ hpairs_card
  have htot : 2 ^ n = (Finset.univ : Finset (Fin n → Bool)).card := by simp
  rw [htot]
  calc (Finset.univ : Finset (Fin n → Bool)).card
      ≤ (WUniq n r ∪ bad).card := Finset.card_le_card hcover
    _ ≤ (WUniq n r).card + bad.card := Finset.card_union_le _ _
    _ ≤ (WUniq n r).card + n.choose 2 * 2 ^ (n - r) := Nat.add_le_add_left hbad_card _

/-! ### Lemma 3 (Separating Collection) & Strict CNF Counting Lower Bound -/

/-- **CPRS Lemma 3 (Separating Collection Lower Bound):** If a finite family `U` of subsets
separates every pair of distinct elements in `S`, then `S.card ≤ 2 ^ U.card`. -/
theorem separating_collection_card {α : Type*} [DecidableEq α]
    (S : Finset α) (U : Finset (Finset α))
    (hsep : ∀ w ∈ S, ∀ x ∈ S, w ≠ x → ∃ L ∈ U, (w ∈ L ∧ x ∉ L) ∨ (x ∈ L ∧ w ∉ L)) :
    S.card ≤ 2 ^ U.card := by
  let sig : α → Finset (Finset α) := fun w => U.filter (fun L => w ∈ L)
  have hinj : Set.InjOn sig S := by
    intro w hw x hx hEq
    by_contra hne
    rcases hsep w hw x hx hne with ⟨L, hLU, ⟨hwL, hxL⟩ | ⟨hxL, hwL⟩⟩
    · have : L ∈ sig w := Finset.mem_filter.mpr ⟨hLU, hwL⟩
      rw [hEq] at this
      exact hxL (Finset.mem_filter.mp this).2
    · have : L ∈ sig x := Finset.mem_filter.mpr ⟨hLU, hxL⟩
      rw [← hEq] at this
      exact hwL (Finset.mem_filter.mp this).2
  have hsub : S.image sig ⊆ U.powerset := by
    intro T hT
    rcases Finset.mem_image.mp hT with ⟨w, _, rfl⟩
    exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  calc S.card
      = (S.image sig).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ U.powerset.card := Finset.card_le_card hsub
    _ = 2 ^ U.card := Finset.card_powerset U

/-- Active (LHS) nonterminals of a strict CNF grammar. -/
def CNFGrammar.activeVars (G : CNFGrammar) : Finset ℕ :=
  G.termRules.image Prod.fst ∪ G.binRules.image Prod.fst

/-- Renaming a strict CNF grammar along a function `f : ℕ → ℕ` that is injective on
active (LHS) nonterminals preserves the accepted language. -/
def CNFGrammar.pruneAndRename (G : CNFGrammar) (V : Finset ℕ) (f : ℕ → ℕ) : CNFGrammar where
  start := f G.start
  termRules := (G.termRules.filter (fun r => r.1 ∈ V)).image (fun r => (f r.1, r.2))
  binRules := (G.binRules.filter (fun r => r.1 ∈ V ∧ r.2.1 ∈ V ∧ r.2.2 ∈ V)).image
    (fun r => (f r.1, f r.2.1, f r.2.2))

theorem derives_lhs_mem (G : CNFGrammar) {A : ℕ} {w : List Bool} (h : G.Derives A w) :
    A ∈ G.activeVars := by
  cases h with
  | term hm => exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, hm, rfl⟩)
  | bin hm _ _ => exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hm, rfl⟩)

theorem pruneAndRename_derives_iff (G : CNFGrammar) (f : ℕ → ℕ)
    (hinj : Set.InjOn f (G.activeVars : Set ℕ)) :
    ∀ A ∈ G.activeVars, ∀ w, (G.pruneAndRename G.activeVars f).Derives (f A) w ↔ G.Derives A w := by
  intro A hAV w
  constructor
  · intro hder
    suffices ∀ X w, (G.pruneAndRename G.activeVars f).Derives X w →
        ∀ A ∈ G.activeVars, f A = X → G.Derives A w from
      this (f A) w hder A hAV rfl
    intro X w hder
    induction hder with
    | term hm =>
      intro A hAV hEq
      simp only [CNFGrammar.pruneAndRename, Finset.mem_image, Finset.mem_filter, Prod.mk.injEq] at hm
      rcases hm with ⟨⟨A', a'⟩, ⟨hr, hA'V⟩, hfeq, rfl⟩
      have hAA' : A = A' := hinj hAV hA'V (hEq.trans hfeq.symm)
      subst hAA'
      exact .term hr
    | bin hm h1 h2 ih1 ih2 =>
      intro A hAV hEq
      simp only [CNFGrammar.pruneAndRename, Finset.mem_image, Finset.mem_filter, Prod.mk.injEq] at hm
      rcases hm with ⟨⟨A', B', C'⟩, ⟨hr, hA'V, hB'V, hC'V⟩, hfeqA, hfeqB, hfeqC⟩
      have hAA' : A = A' := hinj hAV hA'V (hEq.trans hfeqA.symm)
      subst hAA'
      exact .bin hr (ih1 B' hB'V hfeqB) (ih2 C' hC'V hfeqC)
  · intro hder
    induction hder with
    | term hm =>
      have hAV' : _ ∈ G.activeVars := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, hm, rfl⟩)
      exact .term (Finset.mem_image.mpr ⟨_, Finset.mem_filter.mpr ⟨hm, hAV'⟩, rfl⟩)
    | bin hm hB hC ih1 ih2 =>
      have hAV' : _ ∈ G.activeVars := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hm, rfl⟩)
      have hBV' : _ ∈ G.activeVars := derives_lhs_mem G hB
      have hCV' : _ ∈ G.activeVars := derives_lhs_mem G hC
      exact .bin (Finset.mem_image.mpr ⟨_, Finset.mem_filter.mpr ⟨hm, hAV', hBV', hCV'⟩, rfl⟩)
        (ih1 hBV') (ih2 hCV')

/-- **Strict CNF Counting Bound:** Every language `{w : Fin n → Bool | G.Accepts (List.ofFn w)}`
generated by a strict CNF grammar with `G.prodCount ≤ p` equals some member of a fixed finite
family `U` of cardinality `≤ (p + 1) * (p^3 + 2*p + 1)^p`. -/
theorem cnf_languages_card_bound (n p : ℕ) :
    ∃ U : Finset (Finset (Fin n → Bool)),
      U.card ≤ (p + 1) * (p ^ 3 + 2 * p + 1) ^ p ∧
      ∀ G : CNFGrammar, G.prodCount ≤ p →
        ∃ L ∈ U, ∀ w : Fin n → Bool, w ∈ L ↔ G.Accepts (List.ofFn w) := by
  classical
  let RuleType := (Fin p × Bool) ⊕ (Fin p × Fin p × Fin p)
  let CodeType := Option (Fin p) × (Fin p → Option RuleType)
  let decodeGrammar : CodeType → Finset (Fin n → Bool) := fun code =>
    match code.1 with
    | none => ∅
    | some s =>
      let tRules : Finset (ℕ × Bool) :=
        (Finset.univ.biUnion fun i : Fin p =>
          match code.2 i with
          | some (Sum.inl (A, a)) => {(A.val, a)}
          | _ => ∅)
      let bRules : Finset (ℕ × ℕ × ℕ) :=
        (Finset.univ.biUnion fun i : Fin p =>
          match code.2 i with
          | some (Sum.inr (A, B, C)) => {(A.val, B.val, C.val)}
          | _ => ∅)
      let G : CNFGrammar := { start := s.val, termRules := tRules, binRules := bRules }
      Finset.univ.filter (fun w : Fin n → Bool => G.Accepts (List.ofFn w))
  let U : Finset (Finset (Fin n → Bool)) := Finset.univ.image decodeGrammar
  refine ⟨U, ?_, ?_⟩
  · have hcardCode : Fintype.card CodeType = (p + 1) * (p ^ 3 + 2 * p + 1) ^ p := by
      simp only [CodeType, RuleType, Fintype.card_prod, Fintype.card_option, Fintype.card_fin,
        Fintype.card_pi, Fintype.card_sum, Fintype.card_bool, Finset.prod_const, Finset.card_univ]
      ring
    calc U.card
        ≤ (Finset.univ : Finset CodeType).card := Finset.card_image_le
      _ = Fintype.card CodeType := Finset.card_univ
      _ = (p + 1) * (p ^ 3 + 2 * p + 1) ^ p := hcardCode
  · intro G hG
    let V := G.activeVars
    have hVcard : V.card ≤ p := by
      calc V.card
          ≤ (G.termRules.image Prod.fst).card + (G.binRules.image Prod.fst).card :=
            Finset.card_union_le _ _
        _ ≤ G.termRules.card + G.binRules.card :=
            Nat.add_le_add Finset.card_image_le Finset.card_image_le
        _ = G.prodCount := rfl
        _ ≤ p := hG
    by_cases hstart : G.start ∈ V
    · let eV : V ↪ Fin p :=
        (Fintype.equivFinOfCardEq (Fintype.card_coe V)).toEmbedding.trans
          (Fin.castLEEmb hVcard)
      let f : ℕ → ℕ := fun A => if h : A ∈ V then (eV ⟨A, h⟩).val else 0
      have hfinj : Set.InjOn f (G.activeVars : Set ℕ) := by
        intro A hA B hB hEq
        have hA' : A ∈ V := hA
        have hB' : B ∈ V := hB
        change (if h : A ∈ V then (eV ⟨A, h⟩).val else 0) =
          (if h : B ∈ V then (eV ⟨B, h⟩).val else 0) at hEq
        rw [dif_pos hA', dif_pos hB'] at hEq
        have hfin : eV ⟨A, hA'⟩ = eV ⟨B, hB'⟩ := Fin.ext hEq
        exact congrArg Subtype.val (eV.injective hfin)
      let G' := G.pruneAndRename G.activeVars f
      have hG'_acc : ∀ w, G'.Accepts w ↔ G.Accepts w := fun w =>
        pruneAndRename_derives_iff G f hfinj G.start hstart w
      let tFin : Finset RuleType :=
        (G.termRules.filter (fun r => r.1 ∈ V)).attach.image (fun r =>
          Sum.inl (eV ⟨r.val.1, (Finset.mem_filter.mp r.property : r.val ∈ G.termRules ∧ r.val.1 ∈ V).2⟩, r.val.2))
      let bFin : Finset RuleType :=
        (G.binRules.filter (fun r => r.1 ∈ V ∧ r.2.1 ∈ V ∧ r.2.2 ∈ V)).attach.image (fun r =>
          let h := (Finset.mem_filter.mp r.property : r.val ∈ G.binRules ∧ r.val.1 ∈ V ∧ r.val.2.1 ∈ V ∧ r.val.2.2 ∈ V).2
          Sum.inr (eV ⟨r.val.1, h.1⟩, eV ⟨r.val.2.1, h.2.1⟩, eV ⟨r.val.2.2, h.2.2⟩))
      let allRules : Finset RuleType := tFin ∪ bFin
      have hall_card : allRules.card ≤ p := by
        have ht1 : tFin.card ≤ G.termRules.card := by
          calc tFin.card ≤ (G.termRules.filter _).attach.card := Finset.card_image_le
            _ = (G.termRules.filter _).card := Finset.card_attach
            _ ≤ G.termRules.card := Finset.card_filter_le _ _
        have hb1 : bFin.card ≤ G.binRules.card := by
          calc bFin.card ≤ (G.binRules.filter _).attach.card := Finset.card_image_le
            _ = (G.binRules.filter _).card := Finset.card_attach
            _ ≤ G.binRules.card := Finset.card_filter_le _ _
        calc allRules.card ≤ tFin.card + bFin.card := Finset.card_union_le _ _
          _ ≤ G.termRules.card + G.binRules.card := Nat.add_le_add ht1 hb1
          _ ≤ p := hG
      let ruleList := allRules.toList
      have hrl_len : ruleList.length ≤ p := by simpa [ruleList] using hall_card
      let slots : Fin p → Option RuleType := fun i => ruleList[i.val]?
      let code : CodeType := (some (eV ⟨G.start, hstart⟩), slots)
      refine ⟨decodeGrammar code, Finset.mem_image.mpr ⟨code, Finset.mem_univ _, rfl⟩, ?_⟩
      have hT_eq : (Finset.univ.biUnion fun i : Fin p =>
          match slots i with
          | some (Sum.inl (A, a)) => ({(A.val, a)} : Finset (ℕ × Bool))
          | _ => ∅) = G'.termRules := by
        ext ⟨A, a⟩
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, G', CNFGrammar.pruneAndRename,
          Finset.mem_image, Finset.mem_filter, Prod.mk.injEq]
        constructor
        · rintro ⟨i, hi⟩
          cases hsi : slots i with
          | none => simp [hsi] at hi
          | some r =>
            rw [hsi] at hi
            cases r with
            | inr _ => simp at hi
            | inl p1 =>
              simp only [Finset.mem_singleton, Prod.mk.injEq] at hi
              have hmem_list : Sum.inl p1 ∈ ruleList := List.mem_of_getElem? hsi
              have hmem_all : Sum.inl p1 ∈ allRules := Finset.mem_toList.mp hmem_list
              simp only [allRules, Finset.mem_union, tFin, bFin, Finset.mem_image, Finset.mem_attach,
                true_and, Subtype.exists, Finset.mem_filter] at hmem_all
              rcases hmem_all with ⟨r0, ⟨hr0, hr0V⟩, hEq⟩ | ⟨_, _, hEq⟩
              · cases hEq
                refine ⟨r0, ⟨hr0, hr0V⟩, ?_, hi.2.symm⟩
                simp [f, dif_pos hr0V, hi.1]
              · cases hEq
        · rintro ⟨⟨A0, a0⟩, ⟨hr0, hA0V⟩, hfeq, rfl⟩
          have hmem_all : Sum.inl (eV ⟨A0, hA0V⟩, a0) ∈ allRules := by
            apply Finset.mem_union_left
            simp only [tFin, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, Finset.mem_filter]
            exact ⟨(A0, a0), ⟨hr0, hA0V⟩, rfl⟩
          have hmem_list : Sum.inl (eV ⟨A0, hA0V⟩, a0) ∈ ruleList := Finset.mem_toList.mpr hmem_all
          rcases List.getElem_of_mem hmem_list with ⟨idx, hidx, hget⟩
          refine ⟨⟨idx, by omega⟩, ?_⟩
          have hsi : slots ⟨idx, by omega⟩ = some (Sum.inl (eV ⟨A0, hA0V⟩, a0)) := by
            simp [slots, List.getElem?_eq_getElem hidx, hget]
          rw [hsi]
          change (if h : A0 ∈ V then (eV ⟨A0, h⟩).val else 0) = A at hfeq
          rw [dif_pos hA0V] at hfeq
          simpa using hfeq.symm
      have hB_eq : (Finset.univ.biUnion fun i : Fin p =>
          match slots i with
          | some (Sum.inr (A, B, C)) => ({(A.val, B.val, C.val)} : Finset (ℕ × ℕ × ℕ))
          | _ => ∅) = G'.binRules := by
        ext ⟨A, B, C⟩
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, G', CNFGrammar.pruneAndRename,
          Finset.mem_image, Finset.mem_filter, Prod.mk.injEq]
        constructor
        · rintro ⟨i, hi⟩
          cases hsi : slots i with
          | none => simp [hsi] at hi
          | some r =>
            rw [hsi] at hi
            cases r with
            | inl _ => simp at hi
            | inr p1 =>
              simp only [Finset.mem_singleton, Prod.mk.injEq] at hi
              have hmem_list : Sum.inr p1 ∈ ruleList := List.mem_of_getElem? hsi
              have hmem_all : Sum.inr p1 ∈ allRules := Finset.mem_toList.mp hmem_list
              simp only [allRules, Finset.mem_union, tFin, bFin, Finset.mem_image, Finset.mem_attach,
                true_and, Subtype.exists, Finset.mem_filter] at hmem_all
              rcases hmem_all with ⟨_, _, hEq⟩ | ⟨r0, ⟨hr0, h1, h2, h3⟩, hEq⟩
              · cases hEq
              · cases hEq
                refine ⟨r0, ⟨hr0, h1, h2, h3⟩, ?_, ?_, ?_⟩
                · simp [f, dif_pos h1, hi.1]
                · simp [f, dif_pos h2, hi.2.1]
                · simp [f, dif_pos h3, hi.2.2]
        · rintro ⟨⟨A0, B0, C0⟩, ⟨hr0, h1, h2, h3⟩, hf1, hf2, hf3⟩
          have hmem_all : Sum.inr (eV ⟨A0, h1⟩, eV ⟨B0, h2⟩, eV ⟨C0, h3⟩) ∈ allRules := by
            apply Finset.mem_union_right
            simp only [bFin, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, Finset.mem_filter]
            exact ⟨(A0, B0, C0), ⟨hr0, h1, h2, h3⟩, rfl⟩
          have hmem_list : Sum.inr (eV ⟨A0, h1⟩, eV ⟨B0, h2⟩, eV ⟨C0, h3⟩) ∈ ruleList :=
            Finset.mem_toList.mpr hmem_all
          rcases List.getElem_of_mem hmem_list with ⟨idx, hidx, hget⟩
          refine ⟨⟨idx, by omega⟩, ?_⟩
          have hsi : slots ⟨idx, by omega⟩ = some (Sum.inr (eV ⟨A0, h1⟩, eV ⟨B0, h2⟩, eV ⟨C0, h3⟩)) := by
            simp [slots, List.getElem?_eq_getElem hidx, hget]
          rw [hsi]
          change (if h : A0 ∈ V then (eV ⟨A0, h⟩).val else 0) = A at hf1
          change (if h : B0 ∈ V then (eV ⟨B0, h⟩).val else 0) = B at hf2
          change (if h : C0 ∈ V then (eV ⟨C0, h⟩).val else 0) = C at hf3
          rw [dif_pos h1] at hf1
          rw [dif_pos h2] at hf2
          rw [dif_pos h3] at hf3
          simpa using ⟨hf1.symm, hf2.symm, hf3.symm⟩
      have hstart_eq : (eV ⟨G.start, hstart⟩).val = G'.start := by
        simp [G', CNFGrammar.pruneAndRename, f, dif_pos hstart]
      intro w
      simp only [decodeGrammar, code, hT_eq, hB_eq, hstart_eq, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hG'_acc (List.ofFn w)
    · refine ⟨∅, Finset.mem_image.mpr ⟨(none, fun _ => none), Finset.mem_univ _, rfl⟩, ?_⟩
      intro w
      simp only [Finset.notMem_empty, false_iff]
      intro hacc
      exact hstart (derives_lhs_mem G hacc)

/-- **Theorem A (Counting Lower Bound on Any Subset `S`):** If every pair of distinct words in
`S ⊆ (Fin n → Bool)` can be separated by a strict CNF grammar with `≤ p` productions, then
`S.card ≤ 2 ^ ((p + 1) * (p^3 + 2*p + 1)^p)`. -/
theorem cnf_separation_lower_bound_subset (n p : ℕ) (S : Finset (Fin n → Bool))
    (hsep : ∀ w ∈ S, ∀ x ∈ S, w ≠ x →
      ∃ G : CNFGrammar, G.Separates (List.ofFn w) (List.ofFn x) ∧ G.prodCount ≤ p) :
    S.card ≤ 2 ^ ((p + 1) * (p ^ 3 + 2 * p + 1) ^ p) := by
  classical
  rcases cnf_languages_card_bound n p with ⟨U, hUcard, hUmem⟩
  have hsepU : ∀ w ∈ S, ∀ x ∈ S, w ≠ x →
      ∃ L ∈ U, (w ∈ L ∧ x ∉ L) ∨ (x ∈ L ∧ w ∉ L) := by
    intro w hw x hx hne
    rcases hsep w hw x hx hne with ⟨G, hGsep, hGp⟩
    rcases hUmem G hGp with ⟨L, hLU, hLiff⟩
    refine ⟨L, hLU, ?_⟩
    simpa [CNFGrammar.Separates, hLiff] using hGsep
  calc S.card
      ≤ 2 ^ U.card := separating_collection_card S U hsepU
    _ ≤ 2 ^ ((p + 1) * (p ^ 3 + 2 * p + 1) ^ p) := Nat.pow_le_pow_right (by norm_num) hUcard

/-- **Theorem A (CPRS Theorem 4 — Full `{0,1}^n` Lower Bound):**
If every pair of distinct words in `{0,1}^n` is separated by a strict CNF grammar with `≤ p`
productions, then `n ≤ (p + 1) * (p^3 + 2*p + 1)^p` (giving `p = Ω(log n / log log n)`). -/
theorem cnf_separation_lower_bound (n p : ℕ)
    (hsep : ∀ w x : Fin n → Bool, w ≠ x →
      ∃ G : CNFGrammar, G.Separates (List.ofFn w) (List.ofFn x) ∧ G.prodCount ≤ p) :
    n ≤ (p + 1) * (p ^ 3 + 2 * p + 1) ^ p := by
  have hcard := cnf_separation_lower_bound_subset n p Finset.univ
    (fun w _ x _ hne => hsep w x hne)
  have h2n : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by simp
  rw [h2n] at hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcard

/-- **Theorem A (Matching Lower Bound on `W_uniq(n, r)`):**
Whenever `1 ≤ r ≤ n` and `2 * n.choose 2 ≤ 2^r`, `|W_uniq(n, r)| ≥ 2^(n - 1)`,
so separating all pairs in `W_uniq(n, r)` with `≤ p` CNF productions requires
`n - 1 ≤ (p + 1) * (p^3 + 2*p + 1)^p` — matching `uniq_factor_cnf_separation`'s
`O(log n / log log n)` upper bound on the exact same `(1 - o(1))`-density set! -/
theorem uniq_factor_lower_bound (n r p : ℕ) (hn : 1 ≤ n) (hr1 : 1 ≤ r) (hr : r ≤ n)
    (hdense : 2 * n.choose 2 ≤ 2 ^ r)
    (hsep : ∀ w ∈ WUniq n r, ∀ x ∈ WUniq n r, w ≠ x →
      ∃ G : CNFGrammar, G.Separates (List.ofFn w) (List.ofFn x) ∧ G.prodCount ≤ p) :
    n - 1 ≤ (p + 1) * (p ^ 3 + 2 * p + 1) ^ p := by
  have hlow := uniq_factor_card_lower n r hr1
  have hhalf : 2 ^ (n - 1) ≤ (WUniq n r).card := by
    have hpow : n.choose 2 * 2 ^ (n - r) ≤ 2 ^ (n - 1) := by
      have h1 : 2 * (n.choose 2 * 2 ^ (n - r)) ≤ 2 ^ r * 2 ^ (n - r) := by
        calc 2 * (n.choose 2 * 2 ^ (n - r))
            = (2 * n.choose 2) * 2 ^ (n - r) := by ring
          _ ≤ 2 ^ r * 2 ^ (n - r) := Nat.mul_le_mul_right _ hdense
      rw [← pow_add, Nat.add_sub_of_le hr] at h1
      have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ']
      omega
    have h2n : 2 ^ n = 2 ^ (n - 1) + 2 ^ (n - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ']
      ring
    omega
  have hup := cnf_separation_lower_bound_subset n p (WUniq n r) hsep
  have hle : 2 ^ (n - 1) ≤ 2 ^ ((p + 1) * (p ^ 3 + 2 * p + 1) ^ p) := hhalf.trans hup
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle

end FourRussians

/-! ## Section 3: Theorem B — Modular-Parity & Hamming-Distance Strict CNF Separator -/

section ModularParity

/-- Canonical binary-doubling rules generating `Σ^k` (`k ≥ 1`) at nonterminal ID `10 + k`,
using terminal variable `11 = 10 + 1` for `Σ^1`. -/
def powBinRules : ℕ → Finset (ℕ × ℕ × ℕ)
  | k =>
    if hk : k ≤ 1 then ∅
    else if k % 2 = 0 then
      have _ : k / 2 < k := Nat.div_lt_self (by omega) (by norm_num)
      insert (10 + k, 10 + k / 2, 10 + k / 2) (powBinRules (k / 2))
    else
      have _ : k - 1 < k := by omega
      insert (10 + k, 11, 10 + (k - 1)) (powBinRules (k - 1))
termination_by k => k

theorem powBinRules_card_le (k : ℕ) : (powBinRules k).card ≤ 2 * Nat.log 2 k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [powBinRules]
    by_cases hk : k ≤ 1
    · simp [hk]
    · rw [dif_neg hk]
      by_cases hev : k % 2 = 0
      · rw [if_pos hev]
        have h1 := ih (k / 2) (Nat.div_lt_self (by omega) (by norm_num))
        have hlog : Nat.log 2 (k / 2) + 1 = Nat.log 2 k := by
          have hk2 : 2 ≤ k := by omega
          rw [Nat.log_div_base 2 k]
          have : 0 < Nat.log 2 k := Nat.log_pos (by norm_num) hk2
          omega
        calc (insert (10 + k, 10 + k / 2, 10 + k / 2) (powBinRules (k / 2))).card
            ≤ (powBinRules (k / 2)).card + 1 := Finset.card_insert_le _ _
          _ ≤ 2 * Nat.log 2 (k / 2) + 1 := Nat.add_le_add_right h1 1
          _ ≤ 2 * Nat.log 2 k := by omega
      · rw [if_neg hev]
        -- `k ≥ 3` is odd, so `k - 1 ≥ 2` is even and `(k - 1) / 2 = k / 2`!
        have hkm1_gt1 : ¬ (k - 1 ≤ 1) := by omega
        have hkm1_ev : (k - 1) % 2 = 0 := by omega
        have hstep : powBinRules (k - 1) =
            insert (10 + (k - 1), 10 + (k - 1) / 2, 10 + (k - 1) / 2) (powBinRules ((k - 1) / 2)) := by
          rw [powBinRules, dif_neg hkm1_gt1, if_pos hkm1_ev]
        rw [hstep]
        have h1 := ih ((k - 1) / 2) (by omega)
        have hdiv_eq : (k - 1) / 2 = k / 2 := by omega
        have hlog : Nat.log 2 ((k - 1) / 2) + 1 = Nat.log 2 k := by
          rw [hdiv_eq]
          have hk2 : 2 ≤ k := by omega
          rw [Nat.log_div_base 2 k]
          have : 0 < Nat.log 2 k := Nat.log_pos (by norm_num) hk2
          omega
        calc (insert (10 + k, 11, 10 + (k - 1))
              (insert (10 + (k - 1), 10 + (k - 1) / 2, 10 + (k - 1) / 2)
                (powBinRules ((k - 1) / 2)))).card
            ≤ (insert (10 + (k - 1), 10 + (k - 1) / 2, 10 + (k - 1) / 2)
                (powBinRules ((k - 1) / 2))).card + 1 := Finset.card_insert_le _ _
          _ ≤ ((powBinRules ((k - 1) / 2)).card + 1) + 1 :=
              Nat.add_le_add_right (Finset.card_insert_le _ _) 1
          _ ≤ (2 * Nat.log 2 ((k - 1) / 2) + 1) + 1 := by omega
          _ = 2 * Nat.log 2 k := by omega

/-- Every binary rule in `powBinRules k` has canonical LHS `10 + m` (`m ≥ 2`) whose RHS
yield-lengths sum to `m`. -/
def isCanonicalPowRule (A B C : ℕ) : Prop :=
  12 ≤ A ∧ 11 ≤ B ∧ 11 ≤ C ∧ (B - 10) + (C - 10) = A - 10

theorem mem_powBinRules_canonical {k A B C : ℕ} (h : (A, B, C) ∈ powBinRules k) :
    isCanonicalPowRule A B C := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [powBinRules] at h
    by_cases hk : k ≤ 1
    · simp [hk] at h
    · rw [dif_neg hk] at h
      by_cases hev : k % 2 = 0
      · rw [if_pos hev, Finset.mem_insert, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl, rfl⟩ | h'
        · unfold isCanonicalPowRule; omega
        · exact ih (k / 2) (Nat.div_lt_self (by omega) (by norm_num)) h'
      · rw [if_neg hev, Finset.mem_insert, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl, rfl⟩ | h'
        · unfold isCanonicalPowRule; omega
        · exact ih (k - 1) (by omega) h'

theorem pow_derives_length (G : CNFGrammar)
    (hT11 : ∀ A a, (A, a) ∈ G.termRules → 11 ≤ A → A = 11)
    (hB11 : ∀ A B C, (A, B, C) ∈ G.binRules → 11 ≤ A → isCanonicalPowRule A B C)
    {A : ℕ} {w : List Bool} (hA : 11 ≤ A) (hder : G.Derives A w) :
    w.length = A - 10 := by
  induction hder with
  | @term X a hm =>
    have hX := hT11 X a hm hA
    subst hX; simp
  | @bin X Y Z u v hm _ _ ih1 ih2 =>
    have ⟨_, hY, hZ, hsum⟩ := hB11 X Y Z hm hA
    rw [List.length_append, ih1 hY, ih2 hZ, hsum]

theorem pow_derives_of_length (G : CNFGrammar)
    (hT11 : (11, false) ∈ G.termRules ∧ (11, true) ∈ G.termRules)
    {k : ℕ} (hk : 1 ≤ k) (hB : powBinRules k ⊆ G.binRules)
    {w : List Bool} (hw : w.length = k) :
    G.Derives (10 + k) w := by
  induction k using Nat.strong_induction_on generalizing w with
  | _ k ih =>
    by_cases hk1 : k = 1
    · subst hk1
      cases w with
      | nil => simp at hw
      | cons a rest =>
        cases rest with
        | nil => cases a <;> exact .term (by tauto)
        | cons _ _ => simp at hw
    · have hkgt : ¬ (k ≤ 1) := by omega
      by_cases hev : k % 2 = 0
      · have hrule : (10 + k, 10 + k / 2, 10 + k / 2) ∈ G.binRules := by
          apply hB; rw [powBinRules, dif_neg hkgt, if_pos hev]; simp
        have hsub : powBinRules (k / 2) ⊆ G.binRules := by
          intro r hr; apply hB; rw [powBinRules, dif_neg hkgt, if_pos hev]
          exact Finset.mem_insert_of_mem hr
        have h1 := ih (k / 2) (Nat.div_lt_self (by omega) (by norm_num)) (by omega) hsub
          (w := w.take (k / 2)) (by simp; omega)
        have h2 := ih (k / 2) (Nat.div_lt_self (by omega) (by norm_num)) (by omega) hsub
          (w := w.drop (k / 2)) (by simp; omega)
        rw [← List.take_append_drop (k / 2) w]
        exact .bin hrule h1 h2
      · have hrule : (10 + k, 11, 10 + (k - 1)) ∈ G.binRules := by
          apply hB; rw [powBinRules, dif_neg hkgt, if_neg hev]; simp
        have hsub : powBinRules (k - 1) ⊆ G.binRules := by
          intro r hr; apply hB; rw [powBinRules, dif_neg hkgt, if_neg hev]
          exact Finset.mem_insert_of_mem hr
        cases w with
        | nil => simp at hw; omega
        | cons a rest =>
          have hhead : G.Derives 11 [a] := by cases a <;> exact .term (by tauto)
          have htail := ih (k - 1) (by omega) (by omega) hsub
            (w := rest) (by simp at hw; omega)
          exact .bin hrule hhead htail

/-- XOR-parity of the bits of `w` at positions `0, p, 2p, ...` (`p ≥ 2`). -/
def parityAtStep (p : ℕ) (hp : 2 ≤ p) : List Bool → Bool
  | [] => false
  | a :: rest =>
    have _ : ((a :: rest).drop p).length < (a :: rest).length := by
      simp only [List.length_drop, List.length_cons]; omega
    xor a (parityAtStep p hp ((a :: rest).drop p))
termination_by w => w.length

/-- XOR-parity of the bits of `w` at positions `k ≡ r (mod p)` (`r < p`, `p ≥ 2`). -/
def parityAtResidue (p r : ℕ) (hp : 2 ≤ p) (w : List Bool) : Bool :=
  parityAtStep p hp (w.drop r)

theorem parityAtStep_append_short (p : ℕ) (hp : 2 ≤ p) (m : ℕ) :
    ∀ (v tail : List Bool), v.length = m * p + 1 → tail.length < p →
      parityAtStep p hp (v ++ tail) = parityAtStep p hp v := by
  induction m with
  | zero =>
    intro v tail hv htail
    cases v with
    | nil => simp at hv
    | cons a rest =>
      cases rest with
      | nil =>
        have hdrop1 : ([a] ++ tail).drop p = [] := List.drop_eq_nil_of_le (by simp; omega)
        have hdrop2 : ([a] : List Bool).drop p = [] := List.drop_eq_nil_of_le (by simp; omega)
        conv_lhs => rw [List.singleton_append, parityAtStep]
        conv_rhs => rw [parityAtStep]
        rw [show (a :: tail).drop p = [] from hdrop1, hdrop2]
      | cons _ _ => simp at hv
  | succ m ih =>
    intro v tail hv htail
    cases v with
    | nil => simp at hv
    | cons a rest =>
      conv_lhs => rw [List.cons_append, parityAtStep]
      conv_rhs => rw [parityAtStep]
      have hdrop_eq : (a :: (rest ++ tail)).drop p = (a :: rest).drop p ++ tail := by
        have hpm : p ≤ (m + 1) * p := Nat.le_mul_of_pos_left p (by omega)
        rw [← List.cons_append, List.drop_append_of_le_length (by omega)]
      rw [hdrop_eq]
      have hv' : ((a :: rest).drop p).length = m * p + 1 := by
        rw [List.length_drop, hv, Nat.succ_mul]; omega
      rw [ih ((a :: rest).drop p) tail hv' htail]

theorem parityAtStep_append_block (p : ℕ) (hp : 2 ≤ p) (a : Bool) (u v : List Bool)
    (hu : (a :: u).length = p) :
    parityAtStep p hp ((a :: u) ++ v) = xor a (parityAtStep p hp v) := by
  conv_lhs => rw [List.cons_append, parityAtStep]
  have hdrop : (a :: (u ++ v)).drop p = v := by
    rw [← List.cons_append, ← hu, List.drop_left]
  rw [hdrop]

/-- **Theorem B (Modular-Parity Strict CNF Separator):**
For any `n ≥ 1`, modulus `p ≥ 2`, residue `r < p`, and `w, x : List Bool` of length `n`
whose parities on positions `k ≡ r (mod p)` differ, there exists a strict CNF grammar `G`
separating `w` and `x` with `G.prodCount ≤ 6 * Nat.log 2 p + 14`. -/
theorem mod_parity_cnf_separation {n p r : ℕ} (_hn : 1 ≤ n) (hp : 2 ≤ p) (hr : r < p)
    {w x : List Bool} (hw : w.length = n) (hx : x.length = n)
    (hpar : parityAtResidue p r hp w ≠ parityAtResidue p r hp x) :
    ∃ G : CNFGrammar, G.Separates w x ∧ G.prodCount ≤ 6 * Nat.log 2 p + 14 := by
  by_cases hnr : n ≤ r
  · exfalso; apply hpar
    unfold parityAtResidue
    rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]
  · push Not at hnr
    let t := (n - 1 - r) % p
    have ht_lt : t < p := Nat.mod_lt _ (by omega)
    let want := parityAtResidue p r hp w
    let coreVar := if want then 5 else 4
    let powB := powBinRules (p - 1) ∪ powBinRules r ∪ powBinRules t
    let coreB : Finset (ℕ × ℕ × ℕ) :=
      {(2, 0, 10 + (p - 1)), (3, 1, 10 + (p - 1)),
       (4, 2, 4), (4, 3, 5), (5, 2, 5), (5, 3, 4)}
    let baseT : Finset (ℕ × Bool) :=
      {(0, false), (1, true), (4, false), (5, true), (11, false), (11, true)}
    -- Assemble top start rule depending on `(r = 0, t = 0)` with zero ε-rules and zero unit rules:
    let topB : Finset (ℕ × ℕ × ℕ) :=
      if r = 0 ∧ t = 0 then ∅
      else if r > 0 ∧ t = 0 then {(7, 10 + r, coreVar)}
      else if r = 0 ∧ t > 0 then {(7, coreVar, 10 + t)}
      else {(6, coreVar, 10 + t), (7, 10 + r, 6)}
    let startVar : ℕ := if r = 0 ∧ t = 0 then coreVar else 7
    let G : CNFGrammar :=
      { start := startVar
        termRules := baseT
        binRules := powB ∪ coreB ∪ topB }
    have hT11 : ∀ A a, (A, a) ∈ G.termRules → 11 ≤ A → A = 11 := by
      intro A a hm h11
      simp only [G, baseT, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
    have hB11 : ∀ A B C, (A, B, C) ∈ G.binRules → 11 ≤ A → isCanonicalPowRule A B C := by
      intro A B C hm h11
      simp only [G, powB, coreB, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
      rcases hm with (((hp1 | hp2) | hp3) | (⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩)) | htop
      · exact mem_powBinRules_canonical hp1
      · exact mem_powBinRules_canonical hp2
      · exact mem_powBinRules_canonical hp3
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · -- every LHS in `topB` is `6` or `7 < 11`
        dsimp only [topB] at htop
        split_ifs at htop <;>
          simp only [Finset.notMem_empty, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at htop
        · rcases htop with ⟨rfl, _⟩; omega
        · rcases htop with ⟨rfl, _⟩; omega
        · rcases htop with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
    have hT11_mem : (11, false) ∈ G.termRules ∧ (11, true) ∈ G.termRules := by simp [G, baseT]
    have hpow_iff : ∀ k, 1 ≤ k → powBinRules k ⊆ G.binRules →
        ∀ u, G.Derives (10 + k) u ↔ u.length = k := by
      intro k hk hsub u
      constructor
      · intro hd; have := pow_derives_length G hT11 hB11 (by omega) hd; omega
      · intro hlen; exact pow_derives_of_length G hT11_mem hk hsub hlen
    have hpow_not_lt11 : ∀ A B C, (A, B, C) ∈ powB → 12 ≤ A := by
      intro A B C hm
      simp only [powB, Finset.mem_union] at hm
      rcases hm with (h1 | h2) | h3
      · exact (mem_powBinRules_canonical h1).1
      · exact (mem_powBinRules_canonical h2).1
      · exact (mem_powBinRules_canonical h3).1
    have htop_ge6 : ∀ A B C, (A, B, C) ∈ topB → 6 ≤ A := by
      intro A B C hm
      dsimp only [topB] at hm
      split_ifs at hm <;>
        simp only [Finset.notMem_empty, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
      · rcases hm with ⟨rfl, _⟩; omega
      · rcases hm with ⟨rfl, _⟩; omega
      · rcases hm with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
    have h0_iff : ∀ u, G.Derives 0 u ↔ u = [false] := by
      intro u; constructor
      · intro hd; cases hd with
        | term hm =>
          simp only [G, baseT, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
          rcases hm with ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
          · rfl
          · omega
          · omega
          · omega
          · omega
          · omega
        | bin hm _ _ =>
          simp only [G, coreB, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
          rcases hm with (hp0 | (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩)) | htop
          · have := hpow_not_lt11 0 _ _ hp0; omega
          · omega
          · omega
          · omega
          · omega
          · omega
          · omega
          · have := htop_ge6 0 _ _ htop; omega
      · rintro rfl; exact .term (by simp [G, baseT])
    have h1_iff : ∀ u, G.Derives 1 u ↔ u = [true] := by
      intro u; constructor
      · intro hd; cases hd with
        | term hm =>
          simp only [G, baseT, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
          rcases hm with ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
          · omega
          · rfl
          · omega
          · omega
          · omega
          · omega
        | bin hm _ _ =>
          simp only [G, coreB, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
          rcases hm with (hp0 | (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩)) | htop
          · have := hpow_not_lt11 1 _ _ hp0; omega
          · omega
          · omega
          · omega
          · omega
          · omega
          · omega
          · have := htop_ge6 1 _ _ htop; omega
      · rintro rfl; exact .term (by simp [G, baseT])
    have hpow_pm1 : powBinRules (p - 1) ⊆ G.binRules := by
      intro q hq; exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hq)))
    have h2_iff : ∀ u, G.Derives 2 u ↔ ∃ rest, u = false :: rest ∧ rest.length = p - 1 := by
      intro u; constructor
      · intro hd; cases hd with
        | term hm =>
          simp only [G, baseT, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
          rcases hm with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
        | @bin _ _ _ u1 v1 hm hB hC =>
          simp only [G, coreB, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
          rcases hm with (hp0 | (⟨_, rfl, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩)) | htop
          · have := hpow_not_lt11 2 _ _ hp0; omega
          · rw [(h0_iff u1).mp hB]
            exact ⟨v1, rfl, (hpow_iff (p - 1) (by omega) hpow_pm1 v1).mp hC⟩
          · omega
          · omega
          · omega
          · omega
          · omega
          · have := htop_ge6 2 _ _ htop; omega
      · rintro ⟨rest, rfl, hlen⟩
        exact .bin (by simp [G, coreB]) ((h0_iff [false]).mpr rfl)
          ((hpow_iff (p - 1) (by omega) hpow_pm1 rest).mpr hlen)
    have h3_iff : ∀ u, G.Derives 3 u ↔ ∃ rest, u = true :: rest ∧ rest.length = p - 1 := by
      intro u; constructor
      · intro hd; cases hd with
        | term hm =>
          simp only [G, baseT, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
          rcases hm with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
        | @bin _ _ _ u1 v1 hm hB hC =>
          simp only [G, coreB, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
          rcases hm with (hp0 | (⟨h, _⟩ | ⟨_, rfl, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩)) | htop
          · have := hpow_not_lt11 3 _ _ hp0; omega
          · omega
          · rw [(h1_iff u1).mp hB]
            exact ⟨v1, rfl, (hpow_iff (p - 1) (by omega) hpow_pm1 v1).mp hC⟩
          · omega
          · omega
          · omega
          · omega
          · have := htop_ge6 3 _ _ htop; omega
      · rintro ⟨rest, rfl, hlen⟩
        exact .bin (by simp [G, coreB]) ((h1_iff [true]).mpr rfl)
          ((hpow_iff (p - 1) (by omega) hpow_pm1 rest).mpr hlen)
    -- Exact characterization of `C_0` (var 4) and `C_1` (var 5):
    have h45_sound : ∀ A u, G.Derives A u →
        (A = 4 → (∃ m, u.length = m * p + 1) ∧ parityAtStep p hp u = false) ∧
        (A = 5 → (∃ m, u.length = m * p + 1) ∧ parityAtStep p hp u = true) := by
      intro A u hder
      induction hder with
      | @term X a hm =>
        simp only [G, baseT, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
        constructor
        · intro hX; subst hX
          rcases hm with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
          · omega
          · omega
          · refine ⟨⟨0, by simp⟩, ?_⟩
            rw [parityAtStep, List.drop_eq_nil_of_le (by simp; omega), parityAtStep]; rfl
          · omega
          · omega
          · omega
        · intro hX; subst hX
          rcases hm with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩
          · omega
          · omega
          · omega
          · refine ⟨⟨0, by simp⟩, ?_⟩
            rw [parityAtStep, List.drop_eq_nil_of_le (by simp; omega), parityAtStep]; rfl
          · omega
          · omega
      | @bin X Y Z u1 v1 hm hB hC _ ih2 =>
        simp only [G, coreB, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
        constructor
        · intro hX; subst hX
          rcases hm with (hp0 | (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩)) | htop
          · have := hpow_not_lt11 4 _ _ hp0; omega
          · omega
          · omega
          · rcases (h2_iff u1).mp hB with ⟨rest, rfl, hlen⟩
            rcases ih2.1 rfl with ⟨⟨m, hm_len⟩, hpar2⟩
            have hbl : (false :: rest).length = p := by
              rw [List.length_cons, hlen, Nat.sub_add_cancel (by omega)]
            refine ⟨⟨m + 1, ?_⟩, ?_⟩
            · rw [List.length_append, hbl, hm_len, Nat.succ_mul]; omega
            · rw [parityAtStep_append_block p hp false rest v1 hbl, hpar2]; rfl
          · rcases (h3_iff u1).mp hB with ⟨rest, rfl, hlen⟩
            rcases ih2.2 rfl with ⟨⟨m, hm_len⟩, hpar2⟩
            have hbl : (true :: rest).length = p := by
              rw [List.length_cons, hlen, Nat.sub_add_cancel (by omega)]
            refine ⟨⟨m + 1, ?_⟩, ?_⟩
            · rw [List.length_append, hbl, hm_len, Nat.succ_mul]; omega
            · rw [parityAtStep_append_block p hp true rest v1 hbl, hpar2]; rfl
          · omega
          · omega
          · have := htop_ge6 4 _ _ htop; omega
        · intro hX; subst hX
          rcases hm with (hp0 | (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩)) | htop
          · have := hpow_not_lt11 5 _ _ hp0; omega
          · omega
          · omega
          · omega
          · omega
          · rcases (h2_iff u1).mp hB with ⟨rest, rfl, hlen⟩
            rcases ih2.2 rfl with ⟨⟨m, hm_len⟩, hpar2⟩
            have hbl : (false :: rest).length = p := by
              rw [List.length_cons, hlen, Nat.sub_add_cancel (by omega)]
            refine ⟨⟨m + 1, ?_⟩, ?_⟩
            · rw [List.length_append, hbl, hm_len, Nat.succ_mul]; omega
            · rw [parityAtStep_append_block p hp false rest v1 hbl, hpar2]; rfl
          · rcases (h3_iff u1).mp hB with ⟨rest, rfl, hlen⟩
            rcases ih2.1 rfl with ⟨⟨m, hm_len⟩, hpar2⟩
            have hbl : (true :: rest).length = p := by
              rw [List.length_cons, hlen, Nat.sub_add_cancel (by omega)]
            refine ⟨⟨m + 1, ?_⟩, ?_⟩
            · rw [List.length_append, hbl, hm_len, Nat.succ_mul]; omega
            · rw [parityAtStep_append_block p hp true rest v1 hbl, hpar2]; rfl
          · have := htop_ge6 5 _ _ htop; omega
    have h45_complete : ∀ m u, u.length = m * p + 1 →
        (parityAtStep p hp u = false → G.Derives 4 u) ∧
        (parityAtStep p hp u = true → G.Derives 5 u) := by
      intro m
      induction m with
      | zero =>
        intro u hu
        cases u with
        | nil => simp at hu
        | cons a rest =>
          cases rest with
          | nil =>
            have hpa : parityAtStep p hp [a] = a := by
              rw [parityAtStep, List.drop_eq_nil_of_le (by simp; omega), parityAtStep]; cases a <;> rfl
            rw [hpa]
            constructor
            · intro ha; subst ha; exact .term (by simp [G, baseT])
            · intro ha; subst ha; exact .term (by simp [G, baseT])
          | cons _ _ => simp at hu
      | succ m ih =>
        intro u hu
        have hpm : p ≤ (m + 1) * p := Nat.le_mul_of_pos_left p (by omega)
        have htake_len : (u.take p).length = p := by simp; omega
        have hdrop_len : (u.drop p).length = m * p + 1 := by
          rw [List.length_drop, hu, Nat.succ_mul]; omega
        cases htk : u.take p with
        | nil => simp [htk] at htake_len; omega
        | cons a rest =>
          have hrest_len : rest.length = p - 1 := by
            rw [htk] at htake_len; simp at htake_len; omega
          have hsplit : u = (a :: rest) ++ u.drop p := by rw [← htk, List.take_append_drop]
          have hpar_eq : parityAtStep p hp ((a :: rest) ++ u.drop p) =
              xor a (parityAtStep p hp (u.drop p)) :=
            parityAtStep_append_block p hp a rest (u.drop p) (by simp [hrest_len]; omega)
          have hih := ih (u.drop p) hdrop_len
          rw [hsplit]
          constructor
          · intro hpf
            rw [hpar_eq] at hpf
            cases a
            · have hsub : parityAtStep p hp (u.drop p) = false := by cases hq : parityAtStep p hp (u.drop p) <;> simp [hq] at hpf ⊢
              exact .bin (by simp [G, coreB]) ((h2_iff (false :: rest)).mpr ⟨rest, rfl, hrest_len⟩) (hih.1 hsub)
            · have hsub : parityAtStep p hp (u.drop p) = true := by cases hq : parityAtStep p hp (u.drop p) <;> simp [hq] at hpf ⊢
              exact .bin (by simp [G, coreB]) ((h3_iff (true :: rest)).mpr ⟨rest, rfl, hrest_len⟩) (hih.2 hsub)
          · intro hpt
            rw [hpar_eq] at hpt
            cases a
            · have hsub : parityAtStep p hp (u.drop p) = true := by cases hq : parityAtStep p hp (u.drop p) <;> simp [hq] at hpt ⊢
              exact .bin (by simp [G, coreB]) ((h2_iff (false :: rest)).mpr ⟨rest, rfl, hrest_len⟩) (hih.2 hsub)
            · have hsub : parityAtStep p hp (u.drop p) = false := by cases hq : parityAtStep p hp (u.drop p) <;> simp [hq] at hpt ⊢
              exact .bin (by simp [G, coreB]) ((h3_iff (true :: rest)).mpr ⟨rest, rfl, hrest_len⟩) (hih.1 hsub)
    have hcore_iff : ∀ u, G.Derives coreVar u ↔ (∃ m, u.length = m * p + 1) ∧ parityAtStep p hp u = want := by
      intro u
      dsimp only [coreVar]
      cases hwant : want
      · simp only [Bool.false_eq_true, ↓reduceIte]
        constructor
        · intro hd; exact (h45_sound 4 u hd).1 rfl
        · rintro ⟨⟨m, hm⟩, hpf⟩; exact (h45_complete m u hm).1 hpf
      · simp only [↓reduceIte]
        constructor
        · intro hd; exact (h45_sound 5 u hd).2 rfl
        · rintro ⟨⟨m, hm⟩, hpt⟩; exact (h45_complete m u hm).2 hpt
    -- Show that for any word `y` of length `n`, `G.Accepts y ↔ parityAtResidue p r hp y = want`:
    have hpow_r : powBinRules r ⊆ G.binRules := by
      intro q hq; exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hq)))
    have hpow_t : powBinRules t ⊆ G.binRules := by
      intro q hq; exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hq))
    have hacc_len_n : ∀ y : List Bool, y.length = n →
        (G.Accepts y ↔ parityAtResidue p r hp y = want) := by
      intro y hy
      -- Note `n - r = m * p + 1 + t` where `m = (n - 1 - r) / p`
      let m0 := (n - 1 - r) / p
      have hm0_eq : n = r + (m0 * p + 1) + t := by
        have hdm := Nat.div_add_mod (n - 1 - r) p
        dsimp only [m0, t]
        have : p * ((n - 1 - r) / p) = ((n - 1 - r) / p) * p := Nat.mul_comm _ _
        omega
      by_cases hr0 : r = 0
      · by_cases ht0 : t = 0
        · have hst : startVar = coreVar := by simp [startVar, hr0, ht0]
          have hny : y.length = m0 * p + 1 := by omega
          unfold CNFGrammar.Accepts
          rw [show G.start = coreVar from hst, hcore_iff]
          simp only [parityAtResidue, hr0, List.drop_zero]
          exact ⟨fun h => h.2, fun h => ⟨⟨m0, hny⟩, h⟩⟩
        · have hst : startVar = 7 := by simp [startVar, hr0, ht0]
          have htop_eq : topB = {(7, coreVar, 10 + t)} := by
            have : ¬ (r = 0 ∧ t = 0) := by omega
            have : ¬ (r > 0 ∧ t = 0) := by omega
            have : r = 0 ∧ t > 0 := by omega
            simp [topB, *]
          unfold CNFGrammar.Accepts
          rw [show G.start = 7 from hst]
          constructor
          · intro hder; cases hder with
            | term hm =>
              simp only [G, baseT, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
              rcases hm with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
            | @bin _ _ _ u1 v1 hm hB hC =>
              simp only [G, coreB, htop_eq, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
              rcases hm with (hp0 | (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩)) | ⟨_, rfl, rfl⟩
              · have := hpow_not_lt11 7 _ _ hp0; omega
              · omega
              · omega
              · omega
              · omega
              · omega
              · omega
              · rcases (hcore_iff u1).mp hB with ⟨⟨m, hm_len⟩, hpar1⟩
                have hv_len := (hpow_iff t (by omega) hpow_t v1).mp hC
                simp only [parityAtResidue, hr0, List.drop_zero]
                rw [parityAtStep_append_short p hp m u1 v1 hm_len (by omega), hpar1]
          · intro hpy
            rw [← List.take_append_drop (m0 * p + 1) y]
            have hrule : (7, coreVar, 10 + t) ∈ G.binRules := by
              apply Finset.mem_union_right; rw [htop_eq]; simp
            have h1 : G.Derives coreVar (y.take (m0 * p + 1)) := by
              rw [hcore_iff]
              refine ⟨⟨m0, by simp; omega⟩, ?_⟩
              have hEq := parityAtStep_append_short p hp m0 (y.take (m0 * p + 1)) (y.drop (m0 * p + 1))
                (by simp; omega) (by simp; omega)
              rw [List.take_append_drop] at hEq
              simp only [parityAtResidue, hr0, List.drop_zero] at hpy
              rw [← hEq, hpy]
            have h2 : G.Derives (10 + t) (y.drop (m0 * p + 1)) :=
              (hpow_iff t (by omega) hpow_t _).mpr (by simp; omega)
            exact .bin hrule h1 h2
      · by_cases ht0 : t = 0
        · have hst : startVar = 7 := by simp [startVar, hr0, ht0]
          have htop_eq : topB = {(7, 10 + r, coreVar)} := by
            have : ¬ (r = 0 ∧ t = 0) := by omega
            have : r > 0 ∧ t = 0 := by omega
            simp [topB, *]
          unfold CNFGrammar.Accepts
          rw [show G.start = 7 from hst]
          constructor
          · intro hder; cases hder with
            | term hm =>
              simp only [G, baseT, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
              rcases hm with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
            | @bin _ _ _ u1 v1 hm hB hC =>
              simp only [G, coreB, htop_eq, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
              rcases hm with (hp0 | (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩)) | ⟨_, rfl, rfl⟩
              · have := hpow_not_lt11 7 _ _ hp0; omega
              · omega
              · omega
              · omega
              · omega
              · omega
              · omega
              · have hu_len := (hpow_iff r (by omega) hpow_r u1).mp hB
                rcases (hcore_iff v1).mp hC with ⟨_, hpar2⟩
                simp only [parityAtResidue, ← hu_len, List.drop_left]
                exact hpar2
          · intro hpy
            rw [← List.take_append_drop r y]
            have hrule : (7, 10 + r, coreVar) ∈ G.binRules := by
              apply Finset.mem_union_right; rw [htop_eq]; simp
            have h1 : G.Derives (10 + r) (y.take r) :=
              (hpow_iff r (by omega) hpow_r _).mpr (by simp; omega)
            have h2 : G.Derives coreVar (y.drop r) :=
              (hcore_iff _).mpr ⟨⟨m0, by simp; omega⟩, hpy⟩
            exact .bin hrule h1 h2
        · have hst : startVar = 7 := by simp [startVar, hr0, ht0]
          have htop_eq : topB = {(6, coreVar, 10 + t), (7, 10 + r, 6)} := by
            have : ¬ (r = 0 ∧ t = 0) := by omega
            have : ¬ (r > 0 ∧ t = 0) := by omega
            have : ¬ (r = 0 ∧ t > 0) := by omega
            simp [topB, *]
          have h6_iff : ∀ u, G.Derives 6 u ↔
              ∃ v1 v2, (∃ m, v1.length = m * p + 1) ∧ parityAtStep p hp v1 = want ∧
                v2.length = t ∧ u = v1 ++ v2 := by
            intro u; constructor
            · intro hder; cases hder with
              | term hm =>
                simp only [G, baseT, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
                rcases hm with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
              | @bin _ _ _ v1 v2 hm hB hC =>
                simp only [G, coreB, htop_eq, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
                rcases hm with (hp0 | (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩)) | (⟨_, rfl, rfl⟩ | ⟨h, _⟩)
                · have := hpow_not_lt11 6 _ _ hp0; omega
                · omega
                · omega
                · omega
                · omega
                · omega
                · omega
                · rcases (hcore_iff v1).mp hB with ⟨hm1, hpar1⟩
                  exact ⟨v1, v2, hm1, hpar1, (hpow_iff t (by omega) hpow_t v2).mp hC, rfl⟩
                · omega
            · rintro ⟨v1, v2, hm1, hpar1, hv2, rfl⟩
              have hrule : (6, coreVar, 10 + t) ∈ G.binRules := by
                apply Finset.mem_union_right; rw [htop_eq]; simp
              exact .bin hrule ((hcore_iff v1).mpr ⟨hm1, hpar1⟩)
                ((hpow_iff t (by omega) hpow_t v2).mpr hv2)
          unfold CNFGrammar.Accepts
          rw [show G.start = 7 from hst]
          constructor
          · intro hder; cases hder with
            | term hm =>
              simp only [G, baseT, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
              rcases hm with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
            | @bin _ _ _ u1 v_all hm hB hC =>
              simp only [G, coreB, htop_eq, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
              rcases hm with (hp0 | (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩)) | (⟨h, _⟩ | ⟨_, rfl, rfl⟩)
              · have := hpow_not_lt11 7 _ _ hp0; omega
              · omega
              · omega
              · omega
              · omega
              · omega
              · omega
              · omega
              · have hu_len := (hpow_iff r (by omega) hpow_r u1).mp hB
                rcases (h6_iff v_all).mp hC with ⟨v1, v2, ⟨m, hm1⟩, hpar1, hv2, rfl⟩
                simp only [parityAtResidue, ← hu_len, List.drop_left]
                rw [parityAtStep_append_short p hp m v1 v2 hm1 (by omega), hpar1]
          · intro hpy
            rw [← List.take_append_drop r y]
            have hrule : (7, 10 + r, 6) ∈ G.binRules := by
              apply Finset.mem_union_right; rw [htop_eq]; simp
            have h1 : G.Derives (10 + r) (y.take r) :=
              (hpow_iff r (by omega) hpow_r _).mpr (by simp; omega)
            have h2 : G.Derives 6 (y.drop r) := by
              rw [h6_iff]
              let yd := y.drop r
              refine ⟨yd.take (m0 * p + 1), yd.drop (m0 * p + 1), ⟨m0, by simp [yd]; omega⟩, ?_,
                by simp [yd]; omega, (List.take_append_drop _ yd).symm⟩
              have hEq := parityAtStep_append_short p hp m0 (yd.take (m0 * p + 1)) (yd.drop (m0 * p + 1))
                (by simp [yd]; omega) (by simp [yd]; omega)
              rw [List.take_append_drop] at hEq
              rw [← hEq]; exact hpy
            exact .bin hrule h1 h2
    refine ⟨G, Or.inl ⟨(hacc_len_n w hw).mpr rfl, fun hacc => hpar ((hacc_len_n x hx).mp hacc).symm⟩, ?_⟩
    -- Production count bound: `≤ 6 * Nat.log 2 p + 14`
    have hTcard : G.termRules.card ≤ 6 := by
      dsimp only [G, baseT]
      repeat (apply (Finset.card_insert_le _ _).trans; apply Nat.add_le_add_right)
      simp
    have hcoreCard : coreB.card ≤ 6 := by
      dsimp only [coreB]
      repeat (apply (Finset.card_insert_le _ _).trans; apply Nat.add_le_add_right)
      simp
    have htopCard : topB.card ≤ 2 := by
      dsimp only [topB]
      split_ifs
      · simp
      · simp
      · simp
      · refine (Finset.card_insert_le _ _).trans ?_; simp
    have hpowCard : powB.card ≤ 6 * Nat.log 2 p := by
      have h1 := powBinRules_card_le (p - 1)
      have h2 := powBinRules_card_le r
      have h3 := powBinRules_card_le t
      have hl1 : Nat.log 2 (p - 1) ≤ Nat.log 2 p := Nat.log_mono_right (by omega)
      have hl2 : Nat.log 2 r ≤ Nat.log 2 p := Nat.log_mono_right (by omega)
      have hl3 : Nat.log 2 t ≤ Nat.log 2 p := Nat.log_mono_right (by omega)
      have hu1 : powB.card ≤ (powBinRules (p - 1) ∪ powBinRules r).card + (powBinRules t).card :=
        Finset.card_union_le _ _
      have hu2 : (powBinRules (p - 1) ∪ powBinRules r).card ≤ (powBinRules (p - 1)).card + (powBinRules r).card :=
        Finset.card_union_le _ _
      omega
    have hBcard : G.binRules.card ≤ powB.card + coreB.card + topB.card := by
      have hu1 := Finset.card_union_le (powB ∪ coreB) topB
      have hu2 := Finset.card_union_le powB coreB
      dsimp only [G]
      omega
    unfold CNFGrammar.prodCount
    omega

/-- If `w, x : List Bool` of equal length `n` differ at index `j₀ < n` and agree at every other
index `j ≡ j₀ (mod p)` (`p ≥ 2`), then `parityAtResidue p (j₀ % p) hp w ≠ parityAtResidue p (j₀ % p) hp x`. -/
theorem parityAtStep_ne_of_unique_diff (p : ℕ) (hp : 2 ≤ p) :
    ∀ (m : ℕ) (u v : List Bool), u.length = v.length → u.length ≤ m →
      (∃ k₀, k₀ * p < u.length ∧ u[k₀ * p]? ≠ v[k₀ * p]? ∧
        ∀ k, k ≠ k₀ → u[k * p]? = v[k * p]?) →
      parityAtStep p hp u ≠ parityAtStep p hp v := by
  intro m
  induction m with
  | zero =>
    intro u v _ hle ⟨k₀, hk0, _⟩; omega
  | succ m ih =>
    intro u v hlen hle ⟨k₀, hk0, hne0, hall⟩
    cases u with
    | nil => simp at hk0
    | cons a ru =>
      cases v with
      | nil => simp at hlen
      | cons b rv =>
        conv_lhs => rw [parityAtStep]
        conv_rhs => rw [parityAtStep]
        by_cases hk0_zero : k₀ = 0
        · subst hk0_zero
          have hab : a ≠ b := by
            simp only [Nat.zero_mul, List.getElem?_cons_zero] at hne0
            intro h; exact hne0 (congrArg some h)
          have hdrop_eq : parityAtStep p hp ((a :: ru).drop p) = parityAtStep p hp ((b :: rv).drop p) := by
            suffices ∀ (d : ℕ) (u' v' : List Bool), u'.length = v'.length → u'.length ≤ d →
                (∀ k, u'[k * p]? = v'[k * p]?) →
                parityAtStep p hp u' = parityAtStep p hp v' by
              apply this m ((a :: ru).drop p) ((b :: rv).drop p) (by simp [hlen])
                (by simp only [List.length_drop, List.length_cons] at hle ⊢; omega)
              intro k
              rw [List.getElem?_drop, List.getElem?_drop]
              have hidx : p + k * p = (k + 1) * p := by ring
              rw [hidx]
              exact hall (k + 1) (by omega)
            intro d
            induction d with
            | zero =>
              intro u' v' hl' hle' _
              have hu0 : u' = [] := List.eq_nil_of_length_eq_zero (by omega)
              have hv0 : v' = [] := List.eq_nil_of_length_eq_zero (by omega)
              rw [hu0, hv0]
            | succ d ihd =>
              intro u' v' hl' hle' hsame
              cases u' with
              | nil =>
                have hv0 : v' = [] := List.eq_nil_of_length_eq_zero (by simpa using hl'.symm)
                rw [hv0]
              | cons a' ru' =>
                cases v' with
                | nil => simp at hl'
                | cons b' rv' =>
                  rw [parityAtStep, parityAtStep]
                  have ha'b' : a' = b' := by
                    have h0 := hsame 0
                    simpa using h0
                  subst ha'b'
                  congr 1
                  apply ihd ((a' :: ru').drop p) ((a' :: rv').drop p) (by simp [hl'])
                    (by simp only [List.length_drop, List.length_cons] at hle' ⊢; omega)
                  intro k
                  rw [List.getElem?_drop, List.getElem?_drop]
                  have hidx : p + k * p = (k + 1) * p := by ring
                  rw [hidx]
                  exact hsame (k + 1)
          rw [hdrop_eq]
          generalize parityAtStep p hp ((b :: rv).drop p) = q
          cases a <;> cases b <;> cases q <;> simp_all
        · have hab : a = b := by
            have h0 := hall 0 (by omega)
            simpa using h0
          subst hab
          have hsub_ne : parityAtStep p hp ((a :: ru).drop p) ≠ parityAtStep p hp ((a :: rv).drop p) := by
            apply ih ((a :: ru).drop p) ((a :: rv).drop p) (by simp [hlen])
              (by simp only [List.length_drop, List.length_cons] at hle ⊢; omega)
            refine ⟨k₀ - 1, ?_, ?_, ?_⟩
            · rw [List.length_drop]
              have hEq : (k₀ - 1) * p + p = k₀ * p := by
                rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
              omega
            · rw [List.getElem?_drop, List.getElem?_drop]
              have hEq : p + (k₀ - 1) * p = k₀ * p := by
                rw [Nat.add_comm, ← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
              rw [hEq]; exact hne0
            · intro k hk
              rw [List.getElem?_drop, List.getElem?_drop]
              have hEq : p + k * p = (k + 1) * p := by ring
              rw [hEq]
              exact hall (k + 1) (by omega)
          cases a
          · simpa using hsub_ne
          · intro hEq; apply hsub_ne
            cases hx1 : parityAtStep p hp ((true :: ru).drop p) <;>
              cases hx2 : parityAtStep p hp ((true :: rv).drop p) <;> simp_all

/-- **Theorem B (Hamming-Distance Isolating Modulus Corollary):**
If `w, x : List Bool` of length `n` differ at `j₀ < n`, and `p ≥ 2` isolates `j₀` modulo `p`
from all other differing indices (`∀ j < n, j ≠ j₀ → j % p = j₀ % p → w[j]? = x[j]?`), then
there exists a strict CNF grammar separating `w` and `x` with `≤ 6 * Nat.log 2 p + 14` productions. -/
theorem hamming_isolating_modulus_cnf_separation {n p j₀ : ℕ} (hp : 2 ≤ p) (hj₀ : j₀ < n)
    {w x : List Bool} (hw : w.length = n) (hx : x.length = n)
    (hdiff : w[j₀]? ≠ x[j₀]?)
    (hisol : ∀ j < n, j ≠ j₀ → j % p = j₀ % p → w[j]? = x[j]?) :
    ∃ G : CNFGrammar, G.Separates w x ∧ G.prodCount ≤ 6 * Nat.log 2 p + 14 := by
  let r := j₀ % p
  have hr : r < p := Nat.mod_lt _ (by omega)
  have hpar : parityAtResidue p r hp w ≠ parityAtResidue p r hp x := by
    unfold parityAtResidue
    apply parityAtStep_ne_of_unique_diff p hp n (w.drop r) (x.drop r) (by simp [hw, hx]) (by simp [hw])
    refine ⟨j₀ / p, ?_, ?_, ?_⟩
    · rw [List.length_drop, hw]
      have hdm := Nat.div_add_mod j₀ p
      have : p * (j₀ / p) = (j₀ / p) * p := Nat.mul_comm _ _
      dsimp only [r]; omega
    · rw [List.getElem?_drop, List.getElem?_drop]
      have hdm := Nat.div_add_mod j₀ p
      have hEq : r + j₀ / p * p = j₀ := by
        dsimp only [r]; have := Nat.mul_comm p (j₀ / p); omega
      rw [hEq]; exact hdiff
    · intro k hk
      rw [List.getElem?_drop, List.getElem?_drop]
      by_cases hlt : r + k * p < n
      · apply hisol (r + k * p) hlt
        · intro hEq
          have hdiv : (r + k * p) / p = k := by
            rw [Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr, Nat.zero_add]
          rw [hEq] at hdiv
          exact hk hdiv.symm
        · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  exact mod_parity_cnf_separation (by omega) hp hr hw hx hpar

end ModularParity

/-! ## Section 4: Theorem C — Exact Single-Bit Detector `Ω(log n)` Lower Bound -/

section SingleBitDetector

/-- Single-one binary word `0^j 1 0^k`. -/
def singleOne (j k : ℕ) : List Bool :=
  List.replicate j false ++ [true] ++ List.replicate k false

theorem singleOne_length (j k : ℕ) : (singleOne j k).length = j + 1 + k := by
  simp [singleOne]; omega

theorem singleOne_count_true (j k : ℕ) : (singleOne j k).count true = 1 := by
  simp [singleOne, List.count_append, List.count_replicate]

theorem count_true_eq_zero_iff {w : List Bool} :
    w.count true = 0 ↔ w = List.replicate w.length false := by
  induction w with
  | nil => simp
  | cons a rest ih =>
    cases a
    · simp only [List.count_cons_of_ne (by decide : false ≠ true), List.length_cons,
        List.replicate_succ]
      constructor
      · intro h; rw [ih.mp h, List.length_replicate]
      · intro h; exact ih.mpr (List.cons.inj h).2
    · simp [List.replicate_succ]

theorem singleOne_of_count_true_eq_one {w : List Bool} (h : w.count true = 1) :
    ∃ j k, w = singleOne j k := by
  induction w with
  | nil => simp at h
  | cons a rest ih =>
    cases a
    · simp only [List.count_cons_of_ne (by decide : false ≠ true)] at h
      rcases ih h with ⟨j, k, hr⟩
      refine ⟨j + 1, k, ?_⟩
      simp [singleOne, hr, List.replicate_succ]
    · simp only [List.count_cons_self] at h
      have h0 : rest.count true = 0 := by omega
      refine ⟨0, rest.length, ?_⟩
      rw [singleOne, List.replicate_zero, List.nil_append, List.singleton_append,
        ← count_true_eq_zero_iff.mp h0]

theorem singleOne_inj {j₁ k₁ j₂ k₂ : ℕ} (h : singleOne j₁ k₁ = singleOne j₂ k₂) :
    j₁ = j₂ ∧ k₁ = k₂ := by
  have hlen : j₁ + 1 + k₁ = j₂ + 1 + k₂ := by
    have := congrArg List.length h
    simpa [singleOne_length] using this
  have hj : j₁ = j₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hget := congrArg (fun l => l[j₁]?) h
      have h1 : (singleOne j₁ k₁)[j₁]? = some true := by
        simp [singleOne, List.append_assoc]
      have h2 : (singleOne j₂ k₂)[j₁]? = some false := by
        simp only [singleOne, List.append_assoc]
        rw [List.getElem?_append_left (by simp; omega), List.getElem?_replicate]
        simp [hlt]
      rw [h1, h2] at hget; simp at hget
    · have hget := congrArg (fun l => l[j₂]?) h
      have h1 : (singleOne j₂ k₂)[j₂]? = some true := by
        simp [singleOne, List.append_assoc]
      have h2 : (singleOne j₁ k₁)[j₂]? = some false := by
        simp only [singleOne, List.append_assoc]
        rw [List.getElem?_append_left (by simp; omega), List.getElem?_replicate]
        simp [hgt]
      rw [h1, h2] at hget; simp at hget
  exact ⟨hj, by omega⟩

theorem append_singleOne_of_zeros {u v : List Bool} {j k : ℕ}
    (hu : u.count true = 0) (hv : v = singleOne j k) :
    u ++ v = singleOne (u.length + j) k := by
  rw [count_true_eq_zero_iff.mp hu, hv, singleOne, singleOne,
    ← List.append_assoc, ← List.append_assoc, List.replicate_append_replicate,
    List.length_replicate]

theorem singleOne_append_of_zeros {u v : List Bool} {j k : ℕ}
    (hu : u = singleOne j k) (hv : v.count true = 0) :
    u ++ v = singleOne j (k + v.length) := by
  rw [hu, count_true_eq_zero_iff.mp hv, singleOne, singleOne,
    List.append_assoc, List.replicate_append_replicate, List.length_replicate]

/-- Concrete binary parse tree for a strict CNF grammar `G`. -/
inductive ParseTree (G : CNFGrammar) : ℕ → Type where
  | leaf (A : ℕ) (a : Bool) (h : (A, a) ∈ G.termRules) : ParseTree G A
  | node (A B C : ℕ) (h : (A, B, C) ∈ G.binRules)
      (l : ParseTree G B) (r : ParseTree G C) : ParseTree G A

def ParseTree.yield {G : CNFGrammar} : ∀ {A : ℕ}, ParseTree G A → List Bool
  | _, .leaf _ a _ => [a]
  | _, .node _ _ _ _ l r => l.yield ++ r.yield

def ParseTree.height {G : CNFGrammar} : ∀ {A : ℕ}, ParseTree G A → ℕ
  | _, .leaf _ _ _ => 0
  | _, .node _ _ _ _ l r => 1 + max l.height r.height

def ParseTree.size {G : CNFGrammar} : ∀ {A : ℕ}, ParseTree G A → ℕ
  | _, .leaf _ _ _ => 1
  | _, .node _ _ _ _ l r => 1 + l.size + r.size

theorem ParseTree.yield_length_pos {G : CNFGrammar} :
    ∀ {A : ℕ} (T : ParseTree G A), 1 ≤ T.yield.length
  | _, .leaf _ _ _ => by simp [ParseTree.yield]
  | _, .node _ _ _ _ l r => by
    simp only [ParseTree.yield, List.length_append]
    have := l.yield_length_pos; omega

theorem ParseTree.yield_length_le_pow_height {G : CNFGrammar} :
    ∀ {A : ℕ} (T : ParseTree G A), T.yield.length ≤ 2 ^ T.height
  | _, .leaf _ _ _ => by simp [ParseTree.yield, ParseTree.height]
  | _, .node _ _ _ _ l r => by
    simp only [ParseTree.yield, ParseTree.height, List.length_append]
    have hl := l.yield_length_le_pow_height
    have hr := r.yield_length_le_pow_height
    have h1 : 2 ^ l.height ≤ 2 ^ max l.height r.height :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    have h2 : 2 ^ r.height ≤ 2 ^ max l.height r.height :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    rw [show 1 + max l.height r.height = max l.height r.height + 1 by omega, pow_succ']
    omega

theorem ParseTree.toDerives {G : CNFGrammar} :
    ∀ {A : ℕ} (T : ParseTree G A), G.Derives A T.yield
  | _, .leaf _ _ h => .term h
  | _, .node _ _ _ h l r => .bin h l.toDerives r.toDerives

theorem derives_to_parseTree {G : CNFGrammar} {A : ℕ} {w : List Bool} (h : G.Derives A w) :
    ∃ T : ParseTree G A, T.yield = w := by
  induction h with
  | term hm => exact ⟨.leaf _ _ hm, rfl⟩
  | bin hm _ _ ih1 ih2 =>
    rcases ih1 with ⟨l, rfl⟩
    rcases ih2 with ⟨r, rfl⟩
    exact ⟨.node _ _ _ hm l r, rfl⟩

/-- One-hole context in a strict CNF grammar `G`, with root `A` and hole `B`. -/
inductive Context (G : CNFGrammar) : ℕ → ℕ → Type where
  | hole (A : ℕ) : Context G A A
  | left (A B C D : ℕ) (h : (A, B, C) ∈ G.binRules)
      (c : Context G B D) (r : ParseTree G C) : Context G A D
  | right (A B C D : ℕ) (h : (A, B, C) ∈ G.binRules)
      (l : ParseTree G B) (c : Context G C D) : Context G A D

def Context.plug {G : CNFGrammar} : ∀ {A B : ℕ}, Context G A B → ParseTree G B → ParseTree G A
  | _, _, .hole _, t => t
  | _, _, .left A B C _ h c r, t => .node A B C h (c.plug t) r
  | _, _, .right A B C _ h l c, t => .node A B C h l (c.plug t)

def Context.leftYield {G : CNFGrammar} : ∀ {A B : ℕ}, Context G A B → List Bool
  | _, _, .hole _ => []
  | _, _, .left _ _ _ _ _ c _ => c.leftYield
  | _, _, .right _ _ _ _ _ l c => l.yield ++ c.leftYield

def Context.rightYield {G : CNFGrammar} : ∀ {A B : ℕ}, Context G A B → List Bool
  | _, _, .hole _ => []
  | _, _, .left _ _ _ _ _ c r => c.rightYield ++ r.yield
  | _, _, .right _ _ _ _ _ _ c => c.rightYield

def Context.ctxSize {G : CNFGrammar} : ∀ {A B : ℕ}, Context G A B → ℕ
  | _, _, .hole _ => 0
  | _, _, .left _ _ _ _ _ c r => 1 + c.ctxSize + r.size
  | _, _, .right _ _ _ _ _ l c => 1 + l.size + c.ctxSize

theorem Context.plug_yield {G : CNFGrammar} :
    ∀ {A B : ℕ} (c : Context G A B) (t : ParseTree G B),
      (c.plug t).yield = c.leftYield ++ t.yield ++ c.rightYield
  | _, _, .hole _, _ => by simp [Context.plug, Context.leftYield, Context.rightYield]
  | _, _, .left _ _ _ _ _ c r, t => by
    simp only [Context.plug, ParseTree.yield, Context.leftYield, Context.rightYield,
      Context.plug_yield c t, List.append_assoc]
  | _, _, .right _ _ _ _ _ l c, t => by
    simp only [Context.plug, ParseTree.yield, Context.leftYield, Context.rightYield,
      Context.plug_yield c t, List.append_assoc]

theorem Context.plug_size {G : CNFGrammar} :
    ∀ {A B : ℕ} (c : Context G A B) (t : ParseTree G B),
      (c.plug t).size = c.ctxSize + t.size
  | _, _, .hole _, _ => by simp [Context.plug, Context.ctxSize]
  | _, _, .left _ _ _ _ _ c r, t => by
    simp only [Context.plug, ParseTree.size, Context.ctxSize, Context.plug_size c t]; omega
  | _, _, .right _ _ _ _ _ l c, t => by
    simp only [Context.plug, ParseTree.size, Context.ctxSize, Context.plug_size c t]; omega

theorem Context.nonempty_of_ctxSize_pos {G : CNFGrammar} :
    ∀ {A B : ℕ} (c : Context G A B), 0 < c.ctxSize → 1 ≤ c.leftYield.length + c.rightYield.length
  | _, _, .hole _, h => by simp [Context.ctxSize] at h
  | _, _, .left _ _ _ _ _ _ r, _ => by
    simp only [Context.rightYield, List.length_append]
    have := r.yield_length_pos; omega
  | _, _, .right _ _ _ _ _ l _, _ => by
    simp only [Context.leftYield, List.length_append]
    have := l.yield_length_pos; omega

/-- Position-typed nonterminals occurring in a zero-subtree (all nodes have type `pos ∈ {0, 1}`). -/
def typedNodesOfZero {G : CNFGrammar} (pos : Fin 3) : ∀ {A : ℕ}, ParseTree G A → Finset (Fin 3 × ℕ)
  | A, .leaf _ _ _ => {(pos, A)}
  | A, .node _ _ _ _ l r => insert (pos, A) (typedNodesOfZero pos l ∪ typedNodesOfZero pos r)

/-- Position-typed nonterminals occurring in a single-one parse tree (`0 = Left`, `1 = Right`, `2 = Spine`). -/
def typedNodesSpine {G : CNFGrammar} : ∀ {A : ℕ}, ParseTree G A → Finset (Fin 3 × ℕ)
  | A, .leaf _ _ _ => {(2, A)}
  | A, .node _ _ _ _ l r =>
    if l.yield.count true = 1 then
      insert (2, A) (typedNodesSpine l ∪ typedNodesOfZero 1 r)
    else
      insert (2, A) (typedNodesOfZero 0 l ∪ typedNodesSpine r)

theorem typedNodesOfZero_subset {G : CNFGrammar} (pos : Fin 3) :
    ∀ {A : ℕ} (T : ParseTree G A), typedNodesOfZero pos T ⊆ Finset.univ ×ˢ G.activeVars
  | A, .leaf _ _ h => by
    intro x hx; simp only [typedNodesOfZero, Finset.mem_singleton] at hx; subst hx
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, derives_lhs_mem G (.term h)⟩
  | A, .node _ _ _ h l r => by
    intro x hx
    simp only [typedNodesOfZero, Finset.mem_insert, Finset.mem_union] at hx
    rcases hx with rfl | hl | hr
    · exact Finset.mem_product.mpr ⟨Finset.mem_univ _, derives_lhs_mem G (.bin h l.toDerives r.toDerives)⟩
    · exact typedNodesOfZero_subset pos l hl
    · exact typedNodesOfZero_subset pos r hr

theorem typedNodesSpine_subset {G : CNFGrammar} :
    ∀ {A : ℕ} (T : ParseTree G A), typedNodesSpine T ⊆ Finset.univ ×ˢ G.activeVars
  | A, .leaf _ _ h => by
    intro x hx; simp only [typedNodesSpine, Finset.mem_singleton] at hx; subst hx
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, derives_lhs_mem G (.term h)⟩
  | A, .node _ _ _ h l r => by
    intro x hx
    simp only [typedNodesSpine] at hx
    split_ifs at hx
    · simp only [Finset.mem_insert, Finset.mem_union] at hx
      rcases hx with rfl | hl | hr
      · exact Finset.mem_product.mpr ⟨Finset.mem_univ _, derives_lhs_mem G (.bin h l.toDerives r.toDerives)⟩
      · exact typedNodesSpine_subset l hl
      · exact typedNodesOfZero_subset 1 r hr
    · simp only [Finset.mem_insert, Finset.mem_union] at hx
      rcases hx with rfl | hl | hr
      · exact Finset.mem_product.mpr ⟨Finset.mem_univ _, derives_lhs_mem G (.bin h l.toDerives r.toDerives)⟩
      · exact typedNodesOfZero_subset 0 l hl
      · exact typedNodesSpine_subset r hr

theorem typedNodesSpine_card_le {G : CNFGrammar} {A : ℕ} (T : ParseTree G A) :
    (typedNodesSpine T).card ≤ 3 * G.activeVars.card := by
  calc (typedNodesSpine T).card
      ≤ (Finset.univ ×ˢ G.activeVars : Finset (Fin 3 × ℕ)).card :=
        Finset.card_le_card (typedNodesSpine_subset T)
    _ = 3 * G.activeVars.card := by simp

/-- Context-internal typed nodes contributed by a context `c` inserted at position type `pos`. -/
def ctxTypedNodes {G : CNFGrammar} (pos : Fin 3) : ∀ {A B : ℕ}, Context G A B → Finset (Fin 3 × ℕ)
  | _, _, .hole _ => ∅
  | A, _, .left _ _ _ _ _ c r =>
    if pos = 2 then
      insert (2, A) (ctxTypedNodes 2 c ∪ typedNodesOfZero 1 r)
    else
      insert (pos, A) (ctxTypedNodes pos c ∪ typedNodesOfZero pos r)
  | A, _, .right _ _ _ _ _ l c =>
    if pos = 2 then
      insert (2, A) (typedNodesOfZero 0 l ∪ ctxTypedNodes 2 c)
    else
      insert (pos, A) (typedNodesOfZero pos l ∪ ctxTypedNodes pos c)

theorem typedNodesOfZero_plug {G : CNFGrammar} (pos : Fin 3) :
    ∀ {A B : ℕ} (c : Context G A B) (t : ParseTree G B), pos ≠ 2 →
      typedNodesOfZero pos (c.plug t) = typedNodesOfZero pos t ∪ ctxTypedNodes pos c
  | _, _, .hole _, t, _ => by simp [Context.plug, ctxTypedNodes]
  | A, _, .left _ _ _ _ _ c r, t, hne => by
    simp only [Context.plug, typedNodesOfZero, ctxTypedNodes, hne, ↓reduceIte,
      typedNodesOfZero_plug pos c t hne]
    ext x; simp only [Finset.mem_insert, Finset.mem_union]; tauto
  | A, _, .right _ _ _ _ _ l c, t, hne => by
    simp only [Context.plug, typedNodesOfZero, ctxTypedNodes, hne, ↓reduceIte,
      typedNodesOfZero_plug pos c t hne]
    ext x; simp only [Finset.mem_insert, Finset.mem_union]; tauto

theorem typedNodesSpine_plug {G : CNFGrammar} :
    ∀ {A B : ℕ} (c : Context G A B) (t : ParseTree G B),
      c.leftYield.count true = 0 → c.rightYield.count true = 0 →
      t.yield.count true = 1 →
      typedNodesSpine (c.plug t) = typedNodesSpine t ∪ ctxTypedNodes 2 c
  | _, _, .hole _, t, _, _, _ => by simp [Context.plug, ctxTypedNodes]
  | A, _, .left _ _ _ _ _ c r, t, hcL, hcR, ht => by
    simp only [Context.leftYield, Context.rightYield, List.count_append] at hcL hcR
    have hcR1 : c.rightYield.count true = 0 := by omega
    have hcnt : (c.plug t).yield.count true = 1 := by
      rw [Context.plug_yield, List.count_append, List.count_append, hcL, hcR1, ht]
    simp only [Context.plug, typedNodesSpine, hcnt, ↓reduceIte, ctxTypedNodes,
      typedNodesSpine_plug c t hcL hcR1 ht]
    ext x; simp only [Finset.mem_insert, Finset.mem_union]; tauto
  | A, _, .right _ _ _ _ _ l c, t, hcL, hcR, ht => by
    simp only [Context.leftYield, Context.rightYield, List.count_append] at hcL hcR
    have hl0 : l.yield.count true = 0 := by omega
    have hcL1 : c.leftYield.count true = 0 := by omega
    have hnot1 : ¬ (l.yield.count true = 1) := by omega
    simp only [Context.plug, typedNodesSpine, hnot1, ↓reduceIte, ctxTypedNodes,
      typedNodesSpine_plug c t hcL1 hcR ht]
    ext x; simp only [Finset.mem_insert, Finset.mem_union]; tauto

/-- A record of a single basic cut `(pos, var, a, b)` together with its context `ctx` and
context-internal typed nodes `nodes`. -/
structure BasicCut (G : CNFGrammar) where
  pos : Fin 3
  var : ℕ
  a : ℕ
  b : ℕ
  ctx : Context G var var
  ctxL0 : ctx.leftYield.count true = 0
  ctxR0 : ctx.rightYield.count true = 0
  shiftSpec :
    (pos = 0 ∧ b = 0 ∧ ctx.leftYield.length + ctx.rightYield.length = a) ∨
    (pos = 1 ∧ a = 0 ∧ ctx.leftYield.length + ctx.rightYield.length = b) ∨
    (pos = 2 ∧ ctx.leftYield.length = a ∧ ctx.rightYield.length = b)
  posSum : 1 ≤ a + b
  small : a + b < 2 ^ (2 * G.activeVars.card + 1)

def BasicCut.nodes {G : CNFGrammar} (c : BasicCut G) : Finset (Fin 3 × ℕ) :=
  ctxTypedNodes c.pos c.ctx

/-- Helper: pasting a zero-context `c_loop` into a zero-tree at `pos ≠ 2` preserves `ctxTypedNodes`. -/
theorem paste_into_zeroTree_nodes {G : CNFGrammar} (pos : Fin 3) (hpos : pos ≠ 2) {A X : ℕ}
    (c : Context G X X) (hcL : c.leftYield.count true = 0) (hcR : c.rightYield.count true = 0) :
    ∀ (T : ParseTree G A), T.yield.count true = 0 → (pos, X) ∈ typedNodesOfZero pos T →
      ∃ T' : ParseTree G A,
        T'.yield.count true = 0 ∧
        T'.yield.length = T.yield.length + c.leftYield.length + c.rightYield.length ∧
        typedNodesOfZero pos T ∪ ctxTypedNodes pos c ⊆ typedNodesOfZero pos T' := by
  intro T
  induction T with
  | leaf A a0 h0 =>
    intro ht0 htm
    simp only [typedNodesOfZero, Finset.mem_singleton, Prod.mk.injEq] at htm
    rcases htm with ⟨_, rfl⟩
    refine ⟨c.plug (.leaf X a0 h0), ?_, ?_, ?_⟩
    · rw [Context.plug_yield, List.count_append, List.count_append, hcL, hcR, ht0]
    · rw [Context.plug_yield, List.length_append, List.length_append]; omega
    · rw [typedNodesOfZero_plug pos c (.leaf X a0 h0) hpos]
  | node A B0 C0 h0 tl tr ihtl ihtr =>
    intro ht0 htm
    have htl0 : tl.yield.count true = 0 := by simp only [ParseTree.yield, List.count_append] at ht0; omega
    have htr0 : tr.yield.count true = 0 := by simp only [ParseTree.yield, List.count_append] at ht0; omega
    simp only [typedNodesOfZero, Finset.mem_insert, Finset.mem_union, Prod.mk.injEq] at htm
    rcases htm with ⟨_, rfl⟩ | hml' | hmr'
    · refine ⟨c.plug (.node X B0 C0 h0 tl tr), ?_, ?_, ?_⟩
      · rw [Context.plug_yield, List.count_append, List.count_append, hcL, hcR, ht0]
      · rw [Context.plug_yield, List.length_append, List.length_append]; omega
      · rw [typedNodesOfZero_plug pos c (.node X B0 C0 h0 tl tr) hpos]
    · rcases ihtl htl0 hml' with ⟨tl', h1, h2, h3⟩
      refine ⟨.node A B0 C0 h0 tl' tr, by simp [ParseTree.yield, List.count_append, h1, htr0],
        by simp [ParseTree.yield, List.length_append, h2]; omega, ?_⟩
      intro q hq
      simp only [typedNodesOfZero, Finset.mem_union, Finset.mem_insert] at hq ⊢
      rcases hq with (rfl | hql | hqr) | hcn
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (h3 (Finset.mem_union_left _ hql)))
      · exact Or.inr (Or.inr hqr)
      · exact Or.inr (Or.inl (h3 (Finset.mem_union_right _ hcn)))
    · rcases ihtr htr0 hmr' with ⟨tr', h1, h2, h3⟩
      refine ⟨.node A B0 C0 h0 tl tr', by simp [ParseTree.yield, List.count_append, htl0, h1],
        by simp [ParseTree.yield, List.length_append, h2]; omega, ?_⟩
      intro q hq
      simp only [typedNodesOfZero, Finset.mem_union, Finset.mem_insert] at hq ⊢
      rcases hq with (rfl | hql | hqr) | hcn
      · exact Or.inl rfl
      · exact Or.inr (Or.inl hql)
      · exact Or.inr (Or.inr (h3 (Finset.mem_union_left _ hqr)))
      · exact Or.inr (Or.inr (h3 (Finset.mem_union_right _ hcn)))

theorem typedNodesOfZero_fst {G : CNFGrammar} (pos : Fin 3) :
    ∀ {U : ℕ} (t : ParseTree G U) (p : Fin 3 × ℕ), p ∈ typedNodesOfZero pos t → p.1 = pos
  | _, .leaf _ _ _, p, hp => by simp only [typedNodesOfZero, Finset.mem_singleton] at hp; rw [hp]
  | _, .node _ _ _ _ tl tr, p, hp => by
    simp only [typedNodesOfZero, Finset.mem_insert, Finset.mem_union] at hp
    rcases hp with rfl | h1 | h2
    · rfl
    · exact typedNodesOfZero_fst pos tl p h1
    · exact typedNodesOfZero_fst pos tr p h2

/-- Pasting a `BasicCut` at `(c.pos, c.var) ∈ typedNodesSpine T` adds `(c.a, c.b)` to `(j, k)`
and adds `c.nodes` to `typedNodesSpine T`. -/
theorem paste_basicCut {G : CNFGrammar} (c : BasicCut G) :
    ∀ {A j k : ℕ} (T : ParseTree G A),
      T.yield = singleOne j k → (c.pos, c.var) ∈ typedNodesSpine T →
      ∃ T' : ParseTree G A,
        T'.yield = singleOne (j + c.a) (k + c.b) ∧
        typedNodesSpine T ∪ c.nodes ⊆ typedNodesSpine T' := by
  intro A j k T
  induction T generalizing j k with
  | leaf A ch h =>
    intro hy hmem
    simp only [typedNodesSpine, Finset.mem_singleton, Prod.mk.injEq] at hmem
    rcases hmem with ⟨hpos2, hvar⟩
    rcases c.shiftSpec with ⟨h0, _⟩ | ⟨h1, _⟩ | ⟨h2, ha, hb⟩
    · rw [h0] at hpos2; simp at hpos2
    · rw [h1] at hpos2; simp at hpos2
    · cases c with
      | mk pos var a b ctx ctxL0 ctxR0 shiftSpec posSum small =>
        dsimp only at hpos2 hvar ha hb
        subst hpos2 hvar
        refine ⟨ctx.plug (.leaf var ch h), ?_, ?_⟩
        · rw [Context.plug_yield, hy]
          have h1 := append_singleOne_of_zeros ctxL0 (rfl : singleOne j k = singleOne j k)
          rw [h1, singleOne_append_of_zeros rfl ctxR0, ha, hb]
          dsimp only; congr 1; omega
        · rw [typedNodesSpine_plug ctx (.leaf var ch h) ctxL0 ctxR0
            (by rw [hy]; exact singleOne_count_true j k)]
          dsimp only [BasicCut.nodes]; exact Finset.Subset.refl _
  | node A B C h l r ihl ihr =>
    intro hy hmem
    have hcnt_tot : l.yield.count true + r.yield.count true = 1 := by
      have := congrArg (List.count true) hy
      rw [ParseTree.yield, List.count_append, singleOne_count_true] at this
      exact this
    by_cases hl1 : l.yield.count true = 1
    · have hr0 : r.yield.count true = 0 := by omega
      rcases singleOne_of_count_true_eq_one hl1 with ⟨jl, kl, hl_eq⟩
      have hy_eq : singleOne j k = singleOne jl (kl + r.yield.length) := by
        rw [← hy, ParseTree.yield, singleOne_append_of_zeros hl_eq hr0]
      have ⟨hjeq, hkeq⟩ := singleOne_inj hy_eq
      simp only [typedNodesSpine, hl1, ↓reduceIte, Finset.mem_insert, Finset.mem_union, Prod.mk.injEq] at hmem
      rcases hmem with ⟨hpos2, hvar⟩ | hml | hmr
      · rcases c.shiftSpec with ⟨h0, _⟩ | ⟨h1, _⟩ | ⟨h2, ha, hb⟩
        · rw [h0] at hpos2; simp at hpos2
        · rw [h1] at hpos2; simp at hpos2
        · cases c with
          | mk pos var a b ctx ctxL0 ctxR0 shiftSpec posSum small =>
            dsimp only at hpos2 hvar ha hb
            subst hpos2 hvar
            refine ⟨ctx.plug (.node var B C h l r), ?_, ?_⟩
            · rw [Context.plug_yield, hy]
              have h1 := append_singleOne_of_zeros ctxL0 (rfl : singleOne j k = singleOne j k)
              rw [h1, singleOne_append_of_zeros rfl ctxR0, ha, hb]
              dsimp only; congr 1; omega
            · rw [typedNodesSpine_plug ctx (.node var B C h l r) ctxL0 ctxR0
                (by rw [hy]; exact singleOne_count_true j k)]
              dsimp only [BasicCut.nodes]; exact Finset.Subset.refl _
      · rcases ihl hl_eq hml with ⟨l', hl'y, hl'sub⟩
        have hl'1 : l'.yield.count true = 1 := by rw [hl'y]; exact singleOne_count_true _ _
        refine ⟨.node A B C h l' r, ?_, ?_⟩
        · rw [ParseTree.yield, singleOne_append_of_zeros hl'y hr0]
          congr 1 <;> omega
        · intro q hq
          simp only [typedNodesSpine, hl1, hl'1, ↓reduceIte, Finset.mem_union, Finset.mem_insert] at hq ⊢
          rcases hq with (rfl | hql | hqr) | hcn
          · exact Or.inl rfl
          · exact Or.inr (Or.inl (hl'sub (Finset.mem_union_left _ hql)))
          · exact Or.inr (Or.inr hqr)
          · exact Or.inr (Or.inl (hl'sub (Finset.mem_union_right _ hcn)))
      · have hpos1 : c.pos = 1 := typedNodesOfZero_fst 1 r (c.pos, c.var) hmr
        rcases c.shiftSpec with ⟨h0, _⟩ | ⟨_, ha0, hcb⟩ | ⟨h2, _⟩
        · rw [h0] at hpos1; simp at hpos1
        · rcases paste_into_zeroTree_nodes 1 (by decide) c.ctx c.ctxL0 c.ctxR0 r hr0 (hpos1 ▸ hmr) with
            ⟨r', hr'0, hr'len, hr'sub⟩
          refine ⟨.node A B C h l r', ?_, ?_⟩
          · rw [ParseTree.yield, singleOne_append_of_zeros hl_eq hr'0, hr'len]
            congr 1 <;> omega
          · intro q hq
            simp only [typedNodesSpine, hl1, ↓reduceIte, BasicCut.nodes, hpos1,
              Finset.mem_union, Finset.mem_insert] at hq ⊢
            rcases hq with (rfl | hql | hqr) | hcn
            · exact Or.inl rfl
            · exact Or.inr (Or.inl hql)
            · exact Or.inr (Or.inr (hr'sub (Finset.mem_union_left _ hqr)))
            · exact Or.inr (Or.inr (hr'sub (Finset.mem_union_right _ hcn)))
        · rw [h2] at hpos1; simp at hpos1
    · have hl0 : l.yield.count true = 0 := by omega
      have hr1 : r.yield.count true = 1 := by omega
      rcases singleOne_of_count_true_eq_one hr1 with ⟨jr, kr, hr_eq⟩
      have hy_eq : singleOne j k = singleOne (l.yield.length + jr) kr := by
        rw [← hy, ParseTree.yield, append_singleOne_of_zeros hl0 hr_eq]
      have ⟨hjeq, hkeq⟩ := singleOne_inj hy_eq
      simp only [typedNodesSpine, hl1, ↓reduceIte, Finset.mem_insert, Finset.mem_union, Prod.mk.injEq] at hmem
      rcases hmem with ⟨hpos2, hvar⟩ | hml | hmr
      · rcases c.shiftSpec with ⟨h0, _⟩ | ⟨h1, _⟩ | ⟨h2, ha, hb⟩
        · rw [h0] at hpos2; simp at hpos2
        · rw [h1] at hpos2; simp at hpos2
        · cases c with
          | mk pos var a b ctx ctxL0 ctxR0 shiftSpec posSum small =>
            dsimp only at hpos2 hvar ha hb
            subst hpos2 hvar
            refine ⟨ctx.plug (.node var B C h l r), ?_, ?_⟩
            · rw [Context.plug_yield, hy]
              have h1 := append_singleOne_of_zeros ctxL0 (rfl : singleOne j k = singleOne j k)
              rw [h1, singleOne_append_of_zeros rfl ctxR0, ha, hb]
              dsimp only; congr 1; omega
            · rw [typedNodesSpine_plug ctx (.node var B C h l r) ctxL0 ctxR0
                (by rw [hy]; exact singleOne_count_true j k)]
              dsimp only [BasicCut.nodes]; exact Finset.Subset.refl _
      · have hpos0 : c.pos = 0 := typedNodesOfZero_fst 0 l (c.pos, c.var) hml
        rcases c.shiftSpec with ⟨_, hb0, hca⟩ | ⟨h1, _⟩ | ⟨h2, _⟩
        · rcases paste_into_zeroTree_nodes 0 (by decide) c.ctx c.ctxL0 c.ctxR0 l hl0 (hpos0 ▸ hml) with
            ⟨l', hl'0, hl'len, hl'sub⟩
          have hl'not1 : ¬ (l'.yield.count true = 1) := by omega
          refine ⟨.node A B C h l' r, ?_, ?_⟩
          · rw [ParseTree.yield, append_singleOne_of_zeros hl'0 hr_eq, hl'len]
            congr 1 <;> omega
          · intro q hq
            simp only [typedNodesSpine, hl1, hl'not1, ↓reduceIte, BasicCut.nodes, hpos0,
              Finset.mem_union, Finset.mem_insert] at hq ⊢
            rcases hq with (rfl | hql | hqr) | hcn
            · exact Or.inl rfl
            · exact Or.inr (Or.inl (hl'sub (Finset.mem_union_left _ hql)))
            · exact Or.inr (Or.inr hqr)
            · exact Or.inr (Or.inl (hl'sub (Finset.mem_union_right _ hcn)))
        · rw [h1] at hpos0; simp at hpos0
        · rw [h2] at hpos0; simp at hpos0
      · rcases ihr hr_eq hmr with ⟨r', hr'y, hr'sub⟩
        refine ⟨.node A B C h l r', ?_, ?_⟩
        · rw [ParseTree.yield, append_singleOne_of_zeros hl0 hr'y]
          congr 1 <;> omega
        · intro q hq
          simp only [typedNodesSpine, hl1, ↓reduceIte, Finset.mem_union, Finset.mem_insert] at hq ⊢
          rcases hq with (rfl | hql | hqr) | hcn
          · exact Or.inl rfl
          · exact Or.inr (Or.inl hql)
          · exact Or.inr (Or.inr (hr'sub (Finset.mem_union_left _ hqr)))
          · exact Or.inr (Or.inr (hr'sub (Finset.mem_union_right _ hcn)))

/-- Pasting a list of `BasicCut`s whose attachment points all lie in `typedNodesSpine T`. -/
theorem paste_many_cuts {G : CNFGrammar} (cs : List (BasicCut G)) :
    ∀ {A j k : ℕ} (T : ParseTree G A),
      T.yield = singleOne j k →
      (∀ c ∈ cs, (c.pos, c.var) ∈ typedNodesSpine T) →
      ∃ T' : ParseTree G A,
        T'.yield = singleOne (j + (cs.map (·.a)).sum) (k + (cs.map (·.b)).sum) ∧
        typedNodesSpine T ⊆ typedNodesSpine T' := by
  induction cs with
  | nil =>
    intro A j k T hy _
    exact ⟨T, by simpa using hy, Finset.Subset.refl _⟩
  | cons c rest ih =>
    intro A j k T hy hall
    rcases paste_basicCut c T hy (hall c (by simp)) with ⟨T1, hT1y, hT1sub⟩
    have hsub1 : typedNodesSpine T ⊆ typedNodesSpine T1 :=
      (Finset.subset_union_left).trans hT1sub
    rcases ih T1 hT1y (fun c' hc' => hsub1 (hall c' (List.mem_cons_of_mem c hc'))) with ⟨T2, hT2y, hT2sub⟩
    refine ⟨T2, ?_, hsub1.trans hT2sub⟩
    simp only [List.map_cons, List.sum_cons]
    rw [hT2y]; congr 1 <;> omega

/-- Pigeonhole on any parse tree: if `G.activeVars.card ≤ seen.card + T.height` for a set
`seen ⊆ G.activeVars`, then either some node in `T` lies in `seen`, or `T` contains an internal
non-empty loop `c_out.plug (c_loop.plug t) = T`. -/
theorem parseTree_pigeonhole {G : CNFGrammar} :
    ∀ {A : ℕ} (T : ParseTree G A) (seen : Finset ℕ),
      seen ⊆ G.activeVars →
      G.activeVars.card ≤ seen.card + T.height →
      (∃ X ∈ seen, ∃ c : Context G A X, ∃ t : ParseTree G X, c.plug t = T) ∨
      (∃ X, ∃ c_out : Context G A X, ∃ c_loop : Context G X X, ∃ t : ParseTree G X,
        c_out.plug (c_loop.plug t) = T ∧ 0 < c_loop.ctxSize) := by
  intro A T
  induction T with
  | leaf A a h =>
    intro seen hseen hcard
    have hA : A ∈ G.activeVars := derives_lhs_mem G (.term h)
    have hmem : A ∈ seen := by
      by_contra hnot
      have hins : (insert A seen).card = seen.card + 1 := Finset.card_insert_of_notMem hnot
      have hsub : insert A seen ⊆ G.activeVars := by
        intro x hx; simp only [Finset.mem_insert] at hx
        rcases hx with rfl | hx'; exact hA; exact hseen hx'
      have hle := Finset.card_le_card hsub
      simp only [ParseTree.height] at hcard; omega
    exact Or.inl ⟨A, hmem, .hole A, .leaf A a h, rfl⟩
  | node A B C h l r ihl ihr =>
    intro seen hseen hcard
    by_cases hA : A ∈ seen
    · exact Or.inl ⟨A, hA, .hole A, .node A B C h l r, rfl⟩
    · have hAv : A ∈ G.activeVars := derives_lhs_mem G (.bin h l.toDerives r.toDerives)
      let seen' := insert A seen
      have hseen' : seen' ⊆ G.activeVars := by
        intro x hx; simp only [seen', Finset.mem_insert] at hx
        rcases hx with rfl | hx'; exact hAv; exact hseen hx'
      have hcard' : seen'.card = seen.card + 1 := Finset.card_insert_of_notMem hA
      simp only [ParseTree.height] at hcard
      by_cases hlr : r.height ≤ l.height
      · have hle : G.activeVars.card ≤ seen'.card + l.height := by
          have : max l.height r.height = l.height := max_eq_left hlr; omega
        rcases ihl seen' hseen' hle with ⟨X, hX, c, t, hc⟩ | ⟨X, c_out, c_loop, t, hc, hpos⟩
        · simp only [seen', Finset.mem_insert] at hX
          rcases hX with rfl | hX0
          · exact Or.inr ⟨X, .hole X, .left X B C X h c r, t,
              by simp [Context.plug, hc], by simp [Context.ctxSize]⟩
          · exact Or.inl ⟨X, hX0, .left A B C X h c r, t, by simp [Context.plug, hc]⟩
        · exact Or.inr ⟨X, .left A B C X h c_out r, c_loop, t, by simp [Context.plug, hc], hpos⟩
      · have hle : G.activeVars.card ≤ seen'.card + r.height := by
          have : max l.height r.height = r.height := max_eq_right (by omega); omega
        rcases ihr seen' hseen' hle with ⟨X, hX, c, t, hc⟩ | ⟨X, c_out, c_loop, t, hc, hpos⟩
        · simp only [seen', Finset.mem_insert] at hX
          rcases hX with rfl | hX0
          · exact Or.inr ⟨X, .hole X, .right X B C X h l c, t,
              by simp [Context.plug, hc], by simp [Context.ctxSize]⟩
          · exact Or.inl ⟨X, hX0, .right A B C X h l c, t, by simp [Context.plug, hc]⟩
        · exact Or.inr ⟨X, .right A B C X h l c_out, c_loop, t, by simp [Context.plug, hc], hpos⟩

/-- Length of the spine (root to unique `true` leaf) in a single-one parse tree. -/
def spineHeight {G : CNFGrammar} : ∀ {A : ℕ}, ParseTree G A → ℕ
  | _, .leaf _ _ _ => 0
  | _, .node _ _ _ _ l r =>
    if l.yield.count true = 1 then 1 + spineHeight l else 1 + spineHeight r

/-- Spine-preserving pigeonhole on a single-one parse tree. -/
theorem spine_pigeonhole {G : CNFGrammar} :
    ∀ {A : ℕ} (T : ParseTree G A), T.yield.count true = 1 →
      ∀ (seen : Finset ℕ), seen ⊆ G.activeVars →
      G.activeVars.card ≤ seen.card + spineHeight T →
      (∃ X ∈ seen, ∃ c : Context G A X, ∃ t : ParseTree G X,
        c.plug t = T ∧ c.leftYield.count true = 0 ∧ c.rightYield.count true = 0 ∧ t.yield.count true = 1) ∨
      (∃ X, ∃ c_out : Context G A X, ∃ c_loop : Context G X X, ∃ t : ParseTree G X,
        c_out.plug (c_loop.plug t) = T ∧ 0 < c_loop.ctxSize ∧
        c_out.leftYield.count true = 0 ∧ c_out.rightYield.count true = 0 ∧
        c_loop.leftYield.count true = 0 ∧ c_loop.rightYield.count true = 0 ∧
        t.yield.count true = 1) := by
  intro A T
  induction T with
  | leaf A a h =>
    intro h1 seen hseen hcard
    have hA : A ∈ G.activeVars := derives_lhs_mem G (.term h)
    have hmem : A ∈ seen := by
      by_contra hnot
      have hins : (insert A seen).card = seen.card + 1 := Finset.card_insert_of_notMem hnot
      have hsub : insert A seen ⊆ G.activeVars := by
        intro x hx; simp only [Finset.mem_insert] at hx
        rcases hx with rfl | hx'; exact hA; exact hseen hx'
      have hle := Finset.card_le_card hsub
      simp only [spineHeight] at hcard; omega
    exact Or.inl ⟨A, hmem, .hole A, .leaf A a h, rfl, rfl, rfl, h1⟩
  | node A B C h l r ihl ihr =>
    intro h1 seen hseen hcard
    have htot : l.yield.count true + r.yield.count true = 1 := by
      simpa [ParseTree.yield, List.count_append] using h1
    by_cases hA : A ∈ seen
    · exact Or.inl ⟨A, hA, .hole A, .node A B C h l r, rfl, rfl, rfl, h1⟩
    · have hAv : A ∈ G.activeVars := derives_lhs_mem G (.bin h l.toDerives r.toDerives)
      let seen' := insert A seen
      have hseen' : seen' ⊆ G.activeVars := by
        intro x hx; simp only [seen', Finset.mem_insert] at hx
        rcases hx with rfl | hx'; exact hAv; exact hseen hx'
      have hcard' : seen'.card = seen.card + 1 := Finset.card_insert_of_notMem hA
      by_cases hl1 : l.yield.count true = 1
      · have hr0 : r.yield.count true = 0 := by omega
        simp only [spineHeight, hl1, ↓reduceIte] at hcard
        rcases ihl hl1 seen' hseen' (by omega) with
          ⟨X, hX, c, t, hc, hcL, hcR, ht1⟩ |
          ⟨X, c_out, c_loop, t, hc, hpos, hoL, hoR, hlL, hlR, ht1⟩
        · simp only [seen', Finset.mem_insert] at hX
          rcases hX with rfl | hX0
          · exact Or.inr ⟨X, .hole X, .left X B C X h c r, t,
              by simp [Context.plug, hc], by simp [Context.ctxSize],
              rfl, rfl, hcL, by simp [Context.rightYield, List.count_append, hcR, hr0], ht1⟩
          · exact Or.inl ⟨X, hX0, .left A B C X h c r, t,
              by simp [Context.plug, hc], hcL,
              by simp [Context.rightYield, List.count_append, hcR, hr0], ht1⟩
        · exact Or.inr ⟨X, .left A B C X h c_out r, c_loop, t,
            by simp [Context.plug, hc], hpos, hoL,
            by simp [Context.rightYield, List.count_append, hoR, hr0], hlL, hlR, ht1⟩
      · have hl0 : l.yield.count true = 0 := by omega
        have hr1 : r.yield.count true = 1 := by omega
        simp only [spineHeight, hl1, ↓reduceIte] at hcard
        rcases ihr hr1 seen' hseen' (by omega) with
          ⟨X, hX, c, t, hc, hcL, hcR, ht1⟩ |
          ⟨X, c_out, c_loop, t, hc, hpos, hoL, hoR, hlL, hlR, ht1⟩
        · simp only [seen', Finset.mem_insert] at hX
          rcases hX with rfl | hX0
          · exact Or.inr ⟨X, .hole X, .right X B C X h l c, t,
              by simp [Context.plug, hc], by simp [Context.ctxSize],
              rfl, rfl, by simp [Context.leftYield, List.count_append, hl0, hcL], hcR, ht1⟩
          · exact Or.inl ⟨X, hX0, .right A B C X h l c, t,
              by simp [Context.plug, hc],
              by simp [Context.leftYield, List.count_append, hl0, hcL], hcR, ht1⟩
        · exact Or.inr ⟨X, .right A B C X h l c_out, c_loop, t,
            by simp [Context.plug, hc], hpos,
            by simp [Context.leftYield, List.count_append, hl0, hoL], hoR, hlL, hlR, ht1⟩

/-- Helper: given any zero-tree of height `≥ s` and yield length `< 2^(2s + 1)`, cut out a loop. -/
theorem zeroTree_cut_of_height_small {G : CNFGrammar} (pos : Fin 3) (hpos : pos ≠ 2)
    {A : ℕ} (T : ParseTree G A) (h0 : T.yield.count true = 0)
    (hh : G.activeVars.card ≤ T.height) (hsmall : T.yield.length < 2 ^ (2 * G.activeVars.card + 1)) :
    ∃ (T' : ParseTree G A) (X : ℕ) (c_loop : Context G X X),
      T'.size < T.size ∧
      T'.yield.count true = 0 ∧
      (pos, X) ∈ typedNodesOfZero pos T' ∧
      c_loop.leftYield.count true = 0 ∧
      c_loop.rightYield.count true = 0 ∧
      1 ≤ c_loop.leftYield.length + c_loop.rightYield.length ∧
      c_loop.leftYield.length + c_loop.rightYield.length < 2 ^ (2 * G.activeVars.card + 1) ∧
      T.yield.length = T'.yield.length + c_loop.leftYield.length + c_loop.rightYield.length ∧
      typedNodesOfZero pos T = typedNodesOfZero pos T' ∪ ctxTypedNodes pos c_loop := by
  rcases parseTree_pigeonhole T ∅ (Finset.empty_subset _) (by simpa using hh) with
    ⟨_, hm, _⟩ | ⟨X, c_out, c_loop, t, hplug, hctxPos⟩
  · simp at hm
  · let T' := c_out.plug t
    have hT0 : (c_out.plug (c_loop.plug t)).yield.count true = 0 := by rw [hplug]; exact h0
    rw [Context.plug_yield, Context.plug_yield] at hT0
    simp only [List.count_append] at hT0
    have hcL : c_loop.leftYield.count true = 0 := by omega
    have hcR : c_loop.rightYield.count true = 0 := by omega
    have hT'0 : T'.yield.count true = 0 := by
      dsimp only [T']; rw [Context.plug_yield]; simp only [List.count_append]; omega
    have hsz : T'.size < T.size := by
      dsimp only [T']
      rw [← hplug, Context.plug_size, Context.plug_size, Context.plug_size]; omega
    have hXmem : (pos, X) ∈ typedNodesOfZero pos T' := by
      dsimp only [T']
      rw [typedNodesOfZero_plug pos c_out t hpos]
      apply Finset.mem_union_left
      cases t with
      | leaf _ _ _ => simp [typedNodesOfZero]
      | node _ _ _ _ _ _ => simp [typedNodesOfZero]
    have h1 := c_loop.nonempty_of_ctxSize_pos hctxPos
    have hlenEq : T.yield.length =
        T'.yield.length + c_loop.leftYield.length + c_loop.rightYield.length := by
      rw [← hplug, Context.plug_yield, Context.plug_yield]
      dsimp only [T']; rw [Context.plug_yield]
      simp only [List.length_append]; omega
    have hnodes : typedNodesOfZero pos T = typedNodesOfZero pos T' ∪ ctxTypedNodes pos c_loop := by
      rw [← hplug]
      dsimp only [T']
      rw [typedNodesOfZero_plug pos c_out (c_loop.plug t) hpos,
        typedNodesOfZero_plug pos c_loop t hpos,
        typedNodesOfZero_plug pos c_out t hpos]
      ext q; simp only [Finset.mem_union]; tauto
    exact ⟨T', X, c_loop, hsz, hT'0, hXmem, hcL, hcR, h1, by omega, hlenEq, hnodes⟩

/-- For any single-one parse tree of yield length `< 2^(2s + 1)`, either `T.height ≤ spineHeight T + s`
or `T` admits a zero-subtree `BasicCut`. -/
theorem singleOne_height_le_or_zero_cut {G : CNFGrammar} :
    ∀ {A j k : ℕ} (T : ParseTree G A),
      T.yield = singleOne j k →
      T.yield.length < 2 ^ (2 * G.activeVars.card + 1) →
      T.height ≤ spineHeight T + G.activeVars.card ∨
      ∃ (T' : ParseTree G A) (j' k' : ℕ) (c : BasicCut G),
        T'.size < T.size ∧
        T'.yield = singleOne j' k' ∧
        j = j' + c.a ∧
        k = k' + c.b ∧
        (c.pos, c.var) ∈ typedNodesSpine T' ∧
        typedNodesSpine T = typedNodesSpine T' ∪ c.nodes := by
  intro A j k T
  induction T generalizing j k with
  | leaf A a h =>
    intro _ _; exact Or.inl (by simp [ParseTree.height, spineHeight])
  | node A B C h l r ihl ihr =>
    intro hy hsmall
    have hcnt_tot : l.yield.count true + r.yield.count true = 1 := by
      have := congrArg (List.count true) hy
      rw [ParseTree.yield, List.count_append, singleOne_count_true] at this
      exact this
    have hsmall_l : l.yield.length < 2 ^ (2 * G.activeVars.card + 1) := by
      simp only [ParseTree.yield, List.length_append] at hsmall; omega
    have hsmall_r : r.yield.length < 2 ^ (2 * G.activeVars.card + 1) := by
      simp only [ParseTree.yield, List.length_append] at hsmall; omega
    by_cases hl1 : l.yield.count true = 1
    · have hr0 : r.yield.count true = 0 := by omega
      rcases singleOne_of_count_true_eq_one hl1 with ⟨jl, kl, hl_eq⟩
      have hy_eq : singleOne j k = singleOne jl (kl + r.yield.length) := by
        rw [← hy, ParseTree.yield, singleOne_append_of_zeros hl_eq hr0]
      have ⟨hjeq, hkeq⟩ := singleOne_inj hy_eq
      by_cases hrh : G.activeVars.card ≤ r.height
      · rcases zeroTree_cut_of_height_small 1 (by decide) r hr0 hrh hsmall_r with
          ⟨r', X, c_loop, hsz, hr'0, hmem, hcL, hcR, h1, hlt, hlenEq, hnodes⟩
        let c : BasicCut G :=
          { pos := 1, var := X, a := 0, b := c_loop.leftYield.length + c_loop.rightYield.length
            ctx := c_loop, ctxL0 := hcL, ctxR0 := hcR
            shiftSpec := Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
            posSum := by omega, small := by omega }
        refine Or.inr ⟨.node A B C h l r', jl, kl + r'.yield.length, c,
          by simp [ParseTree.size]; omega,
          by rw [ParseTree.yield, singleOne_append_of_zeros hl_eq hr'0],
          by omega, by dsimp only [c]; omega,
          by simp [typedNodesSpine, hl1, c, hmem], ?_⟩
        simp only [typedNodesSpine, hl1, ↓reduceIte, hnodes, BasicCut.nodes, c]
        ext q; simp only [Finset.mem_insert, Finset.mem_union]; tauto
      · rcases ihl hl_eq hsmall_l with hle | ⟨l', jl', kl', c, hsz, hl'y, hjl, hkl, hmem, hnodes⟩
        · left
          simp only [ParseTree.height, spineHeight, hl1, ↓reduceIte]
          omega
        · have hl'1 : l'.yield.count true = 1 := by rw [hl'y]; exact singleOne_count_true _ _
          refine Or.inr ⟨.node A B C h l' r, jl', kl' + r.yield.length, c,
            by simp [ParseTree.size]; omega,
            by rw [ParseTree.yield, singleOne_append_of_zeros hl'y hr0],
            by omega, by omega,
            by simp [typedNodesSpine, hl'1, hmem], ?_⟩
          simp only [typedNodesSpine, hl1, hl'1, ↓reduceIte, hnodes]
          ext q; simp only [Finset.mem_insert, Finset.mem_union]; tauto
    · have hl0 : l.yield.count true = 0 := by omega
      have hr1 : r.yield.count true = 1 := by omega
      rcases singleOne_of_count_true_eq_one hr1 with ⟨jr, kr, hr_eq⟩
      have hy_eq : singleOne j k = singleOne (l.yield.length + jr) kr := by
        rw [← hy, ParseTree.yield, append_singleOne_of_zeros hl0 hr_eq]
      have ⟨hjeq, hkeq⟩ := singleOne_inj hy_eq
      by_cases hlh : G.activeVars.card ≤ l.height
      · rcases zeroTree_cut_of_height_small 0 (by decide) l hl0 hlh hsmall_l with
          ⟨l', X, c_loop, hsz, hl'0, hmem, hcL, hcR, h1, hlt, hlenEq, hnodes⟩
        have hl'not1 : ¬ (l'.yield.count true = 1) := by omega
        let c : BasicCut G :=
          { pos := 0, var := X, a := c_loop.leftYield.length + c_loop.rightYield.length, b := 0
            ctx := c_loop, ctxL0 := hcL, ctxR0 := hcR
            shiftSpec := Or.inl ⟨rfl, rfl, rfl⟩
            posSum := by omega, small := by omega }
        refine Or.inr ⟨.node A B C h l' r, l'.yield.length + jr, kr, c,
          by simp [ParseTree.size]; omega,
          by rw [ParseTree.yield, append_singleOne_of_zeros hl'0 hr_eq],
          by dsimp only [c]; omega, by omega,
          by simp [typedNodesSpine, hl'not1, c, hmem], ?_⟩
        simp only [typedNodesSpine, hl1, hl'not1, ↓reduceIte, hnodes, BasicCut.nodes, c]
        ext q; simp only [Finset.mem_insert, Finset.mem_union]; tauto
      · rcases ihr hr_eq hsmall_r with hle | ⟨r', jr', kr', c, hsz, hr'y, hjr, hkr, hmem, hnodes⟩
        · left
          simp only [ParseTree.height, spineHeight, hl1, ↓reduceIte]
          omega
        · refine Or.inr ⟨.node A B C h l r', l.yield.length + jr', kr', c,
            by simp [ParseTree.size]; omega,
            by rw [ParseTree.yield, append_singleOne_of_zeros hl0 hr'y],
            by omega, by omega,
            by simp [typedNodesSpine, hl1, hmem], ?_⟩
          simp only [typedNodesSpine, hl1, ↓reduceIte, hnodes]
          ext q; simp only [Finset.mem_insert, Finset.mem_union]; tauto

/-- Any zero-tree of yield length `≥ 2^s` admits a basic cut of removed length `< 2^(s + 1)`. -/
theorem zeroTree_basic_cut {G : CNFGrammar} (pos : Fin 3) (hpos : pos ≠ 2) :
    ∀ {A : ℕ} (T : ParseTree G A),
      T.yield.count true = 0 →
      2 ^ G.activeVars.card ≤ T.yield.length →
      ∃ (T' : ParseTree G A) (X : ℕ) (c_loop : Context G X X),
        T'.size < T.size ∧
        T'.yield.count true = 0 ∧
        (pos, X) ∈ typedNodesOfZero pos T' ∧
        c_loop.leftYield.count true = 0 ∧
        c_loop.rightYield.count true = 0 ∧
        1 ≤ c_loop.leftYield.length + c_loop.rightYield.length ∧
        c_loop.leftYield.length + c_loop.rightYield.length < 2 ^ (2 * G.activeVars.card + 1) ∧
        T.yield.length = T'.yield.length + c_loop.leftYield.length + c_loop.rightYield.length ∧
        typedNodesOfZero pos T = typedNodesOfZero pos T' ∪ ctxTypedNodes pos c_loop := by
  intro A T
  induction T with
  | leaf A a h =>
    intro _ hlen
    have hA : A ∈ G.activeVars := derives_lhs_mem G (.term h)
    have hpos_card : 1 ≤ G.activeVars.card := Finset.card_pos.mpr ⟨A, hA⟩
    have h2 : 2 ≤ 2 ^ G.activeVars.card := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ G.activeVars.card := Nat.pow_le_pow_right (by norm_num) hpos_card
    have : (ParseTree.leaf A a h).yield.length = 1 := rfl
    omega
  | node A B C h l r ihl ihr =>
    intro h0 hlen
    have hl0 : l.yield.count true = 0 := by simp only [ParseTree.yield, List.count_append] at h0; omega
    have hr0 : r.yield.count true = 0 := by simp only [ParseTree.yield, List.count_append] at h0; omega
    by_cases hll : 2 ^ G.activeVars.card ≤ l.yield.length
    · rcases ihl hl0 hll with ⟨l', X, c_loop, hsz, hl'0, hmem, hcL, hcR, h1, hlt, hlenEq, hnodes⟩
      refine ⟨.node A B C h l' r, X, c_loop,
        by simp [ParseTree.size]; omega,
        by simp [ParseTree.yield, List.count_append, hl'0, hr0],
        by simp [typedNodesOfZero, hmem], hcL, hcR, h1, hlt,
        by simp [ParseTree.yield, List.length_append, hlenEq]; omega, ?_⟩
      simp only [typedNodesOfZero, hnodes]
      ext q; simp only [Finset.mem_insert, Finset.mem_union]; tauto
    · by_cases hrl : 2 ^ G.activeVars.card ≤ r.yield.length
      · rcases ihr hr0 hrl with ⟨r', X, c_loop, hsz, hr'0, hmem, hcL, hcR, h1, hlt, hlenEq, hnodes⟩
        refine ⟨.node A B C h l r', X, c_loop,
          by simp [ParseTree.size]; omega,
          by simp [ParseTree.yield, List.count_append, hl0, hr'0],
          by simp [typedNodesOfZero, hmem], hcL, hcR, h1, hlt,
          by simp [ParseTree.yield, List.length_append, hlenEq]; omega, ?_⟩
        simp only [typedNodesOfZero, hnodes]
        ext q; simp only [Finset.mem_insert, Finset.mem_union]; tauto
      · have hpow_le : 2 ^ (G.activeVars.card + 1) ≤ 2 ^ (2 * G.activeVars.card + 1) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        have htot_lt : (ParseTree.node A B C h l r).yield.length < 2 ^ (2 * G.activeVars.card + 1) := by
          simp only [ParseTree.yield, List.length_append]
          have : 2 ^ (G.activeVars.card + 1) = 2 * 2 ^ G.activeVars.card := pow_succ' 2 _
          omega
        have hheight : G.activeVars.card ≤ (ParseTree.node A B C h l r).height := by
          have hph := (ParseTree.node A B C h l r).yield_length_le_pow_height
          exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (hlen.trans hph)
        exact zeroTree_cut_of_height_small pos hpos (.node A B C h l r) h0 hheight htot_lt

/-- **Basic Position-Preserving Cut Lemma:** Any single-one parse tree of yield length
`≥ 2^(2 * s)` admits a `BasicCut` strictly reducing `T.size`. -/
theorem singleOne_basic_cut {G : CNFGrammar} :
    ∀ {A j k : ℕ} (T : ParseTree G A),
      T.yield = singleOne j k →
      2 ^ (2 * G.activeVars.card) ≤ T.yield.length →
      ∃ (T' : ParseTree G A) (j' k' : ℕ) (c : BasicCut G),
        T'.size < T.size ∧
        T'.yield = singleOne j' k' ∧
        j = j' + c.a ∧
        k = k' + c.b ∧
        (c.pos, c.var) ∈ typedNodesSpine T' ∧
        typedNodesSpine T = typedNodesSpine T' ∪ c.nodes := by
  intro A j k T
  induction T generalizing j k with
  | leaf A a h =>
    intro _ hlen
    have hA : A ∈ G.activeVars := derives_lhs_mem G (.term h)
    have hpos_card : 1 ≤ G.activeVars.card := Finset.card_pos.mpr ⟨A, hA⟩
    have h2 : 2 ≤ 2 ^ (2 * G.activeVars.card) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * G.activeVars.card) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (ParseTree.leaf A a h).yield.length = 1 := rfl
    omega
  | node A B C h l r ihl ihr =>
    intro hy hlen
    have hcnt_tot : l.yield.count true + r.yield.count true = 1 := by
      have := congrArg (List.count true) hy
      rw [ParseTree.yield, List.count_append, singleOne_count_true] at this
      exact this
    have hpow_mono : 2 ^ G.activeVars.card ≤ 2 ^ (2 * G.activeVars.card) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    by_cases hl1 : l.yield.count true = 1
    · have hr0 : r.yield.count true = 0 := by omega
      rcases singleOne_of_count_true_eq_one hl1 with ⟨jl, kl, hl_eq⟩
      have hy_eq : singleOne j k = singleOne jl (kl + r.yield.length) := by
        rw [← hy, ParseTree.yield, singleOne_append_of_zeros hl_eq hr0]
      have ⟨hjeq, hkeq⟩ := singleOne_inj hy_eq
      by_cases hll : 2 ^ (2 * G.activeVars.card) ≤ l.yield.length
      · rcases ihl hl_eq hll with ⟨l', jl', kl', c, hsz, hl'y, hjl, hkl, hmem, hnodes⟩
        have hl'1 : l'.yield.count true = 1 := by rw [hl'y]; exact singleOne_count_true _ _
        refine ⟨.node A B C h l' r, jl', kl' + r.yield.length, c,
          by simp [ParseTree.size]; omega,
          by rw [ParseTree.yield, singleOne_append_of_zeros hl'y hr0],
          by omega, by omega,
          by simp [typedNodesSpine, hl'1, hmem], ?_⟩
        simp only [typedNodesSpine, hl1, hl'1, ↓reduceIte, hnodes]
        ext q; simp only [Finset.mem_insert, Finset.mem_union]; tauto
      · by_cases hrl : 2 ^ G.activeVars.card ≤ r.yield.length
        · rcases zeroTree_basic_cut 1 (by decide) r hr0 hrl with
            ⟨r', X, c_loop, hsz, hr'0, hmem, hcL, hcR, h1, hlt, hlenEq, hnodes⟩
          let c : BasicCut G :=
            { pos := 1, var := X, a := 0, b := c_loop.leftYield.length + c_loop.rightYield.length
              ctx := c_loop, ctxL0 := hcL, ctxR0 := hcR
              shiftSpec := Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
              posSum := by omega, small := by omega }
          refine ⟨.node A B C h l r', jl, kl + r'.yield.length, c,
            by simp [ParseTree.size]; omega,
            by rw [ParseTree.yield, singleOne_append_of_zeros hl_eq hr'0],
            by omega, by dsimp only [c]; omega,
            by simp [typedNodesSpine, hl1, c, hmem], ?_⟩
          simp only [typedNodesSpine, hl1, ↓reduceIte, hnodes, BasicCut.nodes, c]
          ext q; simp only [Finset.mem_insert, Finset.mem_union]; tauto
        · have htot_lt : (ParseTree.node A B C h l r).yield.length < 2 ^ (2 * G.activeVars.card + 1) := by
            simp only [ParseTree.yield, List.length_append, pow_succ']; omega
          rcases singleOne_height_le_or_zero_cut (.node A B C h l r) hy htot_lt with hsh | hcut
          · have hheight : 2 * G.activeVars.card ≤ (ParseTree.node A B C h l r).height := by
              have hph := (ParseTree.node A B C h l r).yield_length_le_pow_height
              exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (hlen.trans hph)
            have h1_cnt : (ParseTree.node A B C h l r).yield.count true = 1 := by
              rw [hy]; exact singleOne_count_true j k
            rcases spine_pigeonhole (.node A B C h l r) h1_cnt ∅ (Finset.empty_subset _) (by simpa using (by omega : G.activeVars.card ≤ spineHeight (.node A B C h l r))) with
              ⟨_, hm, _⟩ | ⟨X, c_out, c_loop, t, hplug, hctxPos, hoL, hoR, hlL, hlR, ht1⟩
            · simp at hm
            · let T' := c_out.plug t
              have hT'cnt : T'.yield.count true = 1 := by
                dsimp only [T']; rw [Context.plug_yield, List.count_append, List.count_append, hoL, hoR, ht1]
              rcases singleOne_of_count_true_eq_one hT'cnt with ⟨j', k', hT'y⟩
              have hjk : j = j' + c_loop.leftYield.length ∧ k = k' + c_loop.rightYield.length := by
                have hy1 : singleOne j k = c_out.leftYield ++ (c_loop.leftYield ++ t.yield ++ c_loop.rightYield) ++ c_out.rightYield := by
                  rw [← hy, ← hplug, Context.plug_yield, Context.plug_yield]
                rcases singleOne_of_count_true_eq_one ht1 with ⟨jt, kt, hty⟩
                have hy2 : singleOne j' k' = c_out.leftYield ++ t.yield ++ c_out.rightYield := by
                  rw [← hT'y]; dsimp only [T']; rw [Context.plug_yield]
                have h2a := append_singleOne_of_zeros hoL hty
                have h2b := singleOne_append_of_zeros h2a hoR
                rw [h2b] at hy2
                have ⟨hj'e, hk'e⟩ := singleOne_inj hy2
                have h1a := append_singleOne_of_zeros hlL hty
                have h1b := singleOne_append_of_zeros h1a hlR
                have h1c := append_singleOne_of_zeros hoL h1b
                have h1d := singleOne_append_of_zeros h1c hoR
                rw [h1d] at hy1
                have ⟨hje, hke⟩ := singleOne_inj hy1
                omega
              have h1pos := c_loop.nonempty_of_ctxSize_pos hctxPos
              have hsz : T'.size < (ParseTree.node A B C h l r).size := by
                dsimp only [T']
                rw [← hplug, Context.plug_size, Context.plug_size, Context.plug_size]; omega
              have hXmem : (2, X) ∈ typedNodesSpine T' := by
                dsimp only [T']
                rw [typedNodesSpine_plug c_out t hoL hoR ht1]
                apply Finset.mem_union_left
                cases t with
                | leaf _ _ _ => simp [typedNodesSpine]
                | node _ _ _ _ tl tr =>
                  simp only [typedNodesSpine]; split_ifs <;> simp
              have hsmall_c : c_loop.leftYield.length + c_loop.rightYield.length < 2 ^ (2 * G.activeVars.card + 1) := by
                rw [hy, singleOne_length] at htot_lt; omega
              let c : BasicCut G :=
                { pos := 2, var := X, a := c_loop.leftYield.length, b := c_loop.rightYield.length
                  ctx := c_loop, ctxL0 := hlL, ctxR0 := hlR
                  shiftSpec := Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)
                  posSum := h1pos, small := hsmall_c }
              have hnodes : typedNodesSpine (.node A B C h l r) = typedNodesSpine T' ∪ c.nodes := by
                rw [← hplug]
                dsimp only [T', c, BasicCut.nodes]
                have hmid_cnt : (c_loop.plug t).yield.count true = 1 := by
                  rw [Context.plug_yield, List.count_append, List.count_append, hlL, hlR, ht1]
                rw [typedNodesSpine_plug c_out (c_loop.plug t) hoL hoR hmid_cnt,
                  typedNodesSpine_plug c_loop t hlL hlR ht1,
                  typedNodesSpine_plug c_out t hoL hoR ht1]
                ext q; simp only [Finset.mem_union]; tauto
              exact ⟨T', j', k', c, hsz, hT'y, hjk.1, hjk.2, hXmem, hnodes⟩
          · exact hcut
    · have hl0 : l.yield.count true = 0 := by omega
      have hr1 : r.yield.count true = 1 := by omega
      rcases singleOne_of_count_true_eq_one hr1 with ⟨jr, kr, hr_eq⟩
      have hy_eq : singleOne j k = singleOne (l.yield.length + jr) kr := by
        rw [← hy, ParseTree.yield, append_singleOne_of_zeros hl0 hr_eq]
      have ⟨hjeq, hkeq⟩ := singleOne_inj hy_eq
      by_cases hrl : 2 ^ (2 * G.activeVars.card) ≤ r.yield.length
      · rcases ihr hr_eq hrl with ⟨r', jr', kr', c, hsz, hr'y, hjr, hkr, hmem, hnodes⟩
        refine ⟨.node A B C h l r', l.yield.length + jr', kr', c,
          by simp [ParseTree.size]; omega,
          by rw [ParseTree.yield, append_singleOne_of_zeros hl0 hr'y],
          by omega, by omega,
          by simp [typedNodesSpine, hl1, hmem], ?_⟩
        simp only [typedNodesSpine, hl1, ↓reduceIte, hnodes]
        ext q; simp only [Finset.mem_insert, Finset.mem_union]; tauto
      · by_cases hll : 2 ^ G.activeVars.card ≤ l.yield.length
        · rcases zeroTree_basic_cut 0 (by decide) l hl0 hll with
            ⟨l', X, c_loop, hsz, hl'0, hmem, hcL, hcR, h1, hlt, hlenEq, hnodes⟩
          have hl'not1 : ¬ (l'.yield.count true = 1) := by omega
          let c : BasicCut G :=
            { pos := 0, var := X, a := c_loop.leftYield.length + c_loop.rightYield.length, b := 0
              ctx := c_loop, ctxL0 := hcL, ctxR0 := hcR
              shiftSpec := Or.inl ⟨rfl, rfl, rfl⟩
              posSum := by omega, small := by omega }
          refine ⟨.node A B C h l' r, l'.yield.length + jr, kr, c,
            by simp [ParseTree.size]; omega,
            by rw [ParseTree.yield, append_singleOne_of_zeros hl'0 hr_eq],
            by dsimp only [c]; omega, by omega,
            by simp [typedNodesSpine, hl'not1, c, hmem], ?_⟩
          simp only [typedNodesSpine, hl1, hl'not1, ↓reduceIte, hnodes, BasicCut.nodes, c]
          ext q; simp only [Finset.mem_insert, Finset.mem_union]; tauto
        · have htot_lt : (ParseTree.node A B C h l r).yield.length < 2 ^ (2 * G.activeVars.card + 1) := by
            simp only [ParseTree.yield, List.length_append, pow_succ']; omega
          rcases singleOne_height_le_or_zero_cut (.node A B C h l r) hy htot_lt with hsh | hcut
          · have hheight : 2 * G.activeVars.card ≤ (ParseTree.node A B C h l r).height := by
              have hph := (ParseTree.node A B C h l r).yield_length_le_pow_height
              exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (hlen.trans hph)
            have h1_cnt : (ParseTree.node A B C h l r).yield.count true = 1 := by
              rw [hy]; exact singleOne_count_true j k
            rcases spine_pigeonhole (.node A B C h l r) h1_cnt ∅ (Finset.empty_subset _) (by simpa using (by omega : G.activeVars.card ≤ spineHeight (.node A B C h l r))) with
              ⟨_, hm, _⟩ | ⟨X, c_out, c_loop, t, hplug, hctxPos, hoL, hoR, hlL, hlR, ht1⟩
            · simp at hm
            · let T' := c_out.plug t
              have hT'cnt : T'.yield.count true = 1 := by
                dsimp only [T']; rw [Context.plug_yield, List.count_append, List.count_append, hoL, hoR, ht1]
              rcases singleOne_of_count_true_eq_one hT'cnt with ⟨j', k', hT'y⟩
              have hjk : j = j' + c_loop.leftYield.length ∧ k = k' + c_loop.rightYield.length := by
                have hy1 : singleOne j k = c_out.leftYield ++ (c_loop.leftYield ++ t.yield ++ c_loop.rightYield) ++ c_out.rightYield := by
                  rw [← hy, ← hplug, Context.plug_yield, Context.plug_yield]
                rcases singleOne_of_count_true_eq_one ht1 with ⟨jt, kt, hty⟩
                have hy2 : singleOne j' k' = c_out.leftYield ++ t.yield ++ c_out.rightYield := by
                  rw [← hT'y]; dsimp only [T']; rw [Context.plug_yield]
                have h2a := append_singleOne_of_zeros hoL hty
                have h2b := singleOne_append_of_zeros h2a hoR
                rw [h2b] at hy2
                have ⟨hj'e, hk'e⟩ := singleOne_inj hy2
                have h1a := append_singleOne_of_zeros hlL hty
                have h1b := singleOne_append_of_zeros h1a hlR
                have h1c := append_singleOne_of_zeros hoL h1b
                have h1d := singleOne_append_of_zeros h1c hoR
                rw [h1d] at hy1
                have ⟨hje, hke⟩ := singleOne_inj hy1
                omega
              have h1pos := c_loop.nonempty_of_ctxSize_pos hctxPos
              have hsz : T'.size < (ParseTree.node A B C h l r).size := by
                dsimp only [T']
                rw [← hplug, Context.plug_size, Context.plug_size, Context.plug_size]; omega
              have hXmem : (2, X) ∈ typedNodesSpine T' := by
                dsimp only [T']
                rw [typedNodesSpine_plug c_out t hoL hoR ht1]
                apply Finset.mem_union_left
                cases t with
                | leaf _ _ _ => simp [typedNodesSpine]
                | node _ _ _ _ tl tr =>
                  simp only [typedNodesSpine]; split_ifs <;> simp
              have hsmall_c : c_loop.leftYield.length + c_loop.rightYield.length < 2 ^ (2 * G.activeVars.card + 1) := by
                rw [hy, singleOne_length] at htot_lt; omega
              let c : BasicCut G :=
                { pos := 2, var := X, a := c_loop.leftYield.length, b := c_loop.rightYield.length
                  ctx := c_loop, ctxL0 := hlL, ctxR0 := hlR
                  shiftSpec := Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)
                  posSum := h1pos, small := hsmall_c }
              have hnodes : typedNodesSpine (.node A B C h l r) = typedNodesSpine T' ∪ c.nodes := by
                rw [← hplug]
                dsimp only [T', c, BasicCut.nodes]
                have hmid_cnt : (c_loop.plug t).yield.count true = 1 := by
                  rw [Context.plug_yield, List.count_append, List.count_append, hlL, hlR, ht1]
                rw [typedNodesSpine_plug c_out (c_loop.plug t) hoL hoR hmid_cnt,
                  typedNodesSpine_plug c_loop t hlL hlR ht1,
                  typedNodesSpine_plug c_out t hoL hoR ht1]
                ext q; simp only [Finset.mem_union]; tauto
              exact ⟨T', j', k', c, hsz, hT'y, hjk.1, hjk.2, hXmem, hnodes⟩
          · exact hcut

/-- **Core-Tree + Basic-Cut Decomposition (Lemma 9' for Single-One Words):**
Every parse tree `T` of `singleOne j k` decomposes into a core tree `T_core` with yield
`singleOne j₀ k₀` of length `< (6*s + 1) * 2^(2*s)` (where `s = G.activeVars.card`) and a list
`L` of `BasicCut`s all attachable inside `typedNodesSpine T_core` such that
`j = j₀ + (L.map (·.a)).sum` and `k = k₀ + (L.map (·.b)).sum`. -/
theorem decompose_singleOne_tree {G : CNFGrammar} {A j k : ℕ} (T : ParseTree G A)
    (hy : T.yield = singleOne j k) :
    ∃ (T_core : ParseTree G A) (j₀ k₀ : ℕ) (L : List (BasicCut G)),
      T_core.yield = singleOne j₀ k₀ ∧
      j₀ + k₀ + 1 < (6 * G.activeVars.card + 1) * 2 ^ (2 * G.activeVars.card) ∧
      j = j₀ + (L.map (·.a)).sum ∧
      k = k₀ + (L.map (·.b)).sum ∧
      (∀ c ∈ L, (c.pos, c.var) ∈ typedNodesSpine T_core) := by
  -- Step 1: Reduce `T` to `T_min` (`|T_min| < 2^(2s)`) + an ordered cut sequence `steps`
  -- such that each cut in `steps` attaches to the cumulative node set of `T_min` plus earlier cuts.
  have hred : ∀ (sz : ℕ) {j1 k1 : ℕ} (T1 : ParseTree G A), T1.size ≤ sz → T1.yield = singleOne j1 k1 →
      ∃ (T_min : ParseTree G A) (jm km : ℕ) (steps : List (BasicCut G)),
        T_min.yield = singleOne jm km ∧
        jm + km + 1 < 2 ^ (2 * G.activeVars.card) ∧
        j1 = jm + (steps.map (·.a)).sum ∧
        k1 = km + (steps.map (·.b)).sum ∧
        typedNodesSpine T1 = typedNodesSpine T_min ∪ steps.foldl (fun acc c => acc ∪ c.nodes) ∅ ∧
        ∀ i (hi : i < steps.length),
          ((steps[i]'hi).pos, (steps[i]'hi).var) ∈
            typedNodesSpine T_min ∪ (steps.take i).foldl (fun acc c => acc ∪ c.nodes) ∅ := by
    intro sz
    induction sz with
    | zero =>
      intro j1 k1 T1 hsz _
      cases T1 <;> simp [ParseTree.size] at hsz
    | succ sz ih =>
      intro j1 k1 T1 hsz hy1
      by_cases hlen : 2 ^ (2 * G.activeVars.card) ≤ T1.yield.length
      · rcases singleOne_basic_cut T1 hy1 hlen with ⟨T', j', k', c, hltSz, hy', hj', hk', hmem, hnodes⟩
        rcases ih T' (by omega) hy' with ⟨T_min, jm, km, steps, hTmy, hTmlt, hjm, hkm, hTnodes, hvalid⟩
        refine ⟨T_min, jm, km, steps ++ [c], hTmy, hTmlt,
          by simp [List.map_append, List.sum_append]; omega,
          by simp [List.map_append, List.sum_append]; omega, ?_, ?_⟩
        · rw [hnodes, hTnodes, List.foldl_append]
          simp only [List.foldl_cons, List.foldl_nil, Finset.union_assoc]
        · intro i hi
          rw [List.length_append, List.length_singleton] at hi
          by_cases hil : i < steps.length
          · rw [List.getElem_append_left hil, List.take_append_of_le_length (by omega)]
            exact hvalid i hil
          · have hieq : i = steps.length := by omega
            subst hieq
            rw [List.getElem_append_right (le_refl _)]
            simp only [Nat.sub_self, List.getElem_cons_zero, List.take_left]
            rw [← hTnodes]; exact hmem
      · refine ⟨T1, j1, k1, [], hy1, ?_, by simp, by simp, by simp, by intro i hi; simp at hi⟩
        rw [hy1, singleOne_length] at hlen; omega
  rcases hred T.size T (le_refl _) hy with ⟨T_min, jm, km, steps, hTmy, hTmlt, hjm, hkm, _, hvalid⟩
  -- Step 2: Walk through `steps`, pasting ONLY cuts that strictly increase `typedNodesSpine T_core`!
  have hbuild : ∀ (pref : List (BasicCut G)),
      (∀ i (hi : i < pref.length),
        ((pref[i]'hi).pos, (pref[i]'hi).var) ∈
          typedNodesSpine T_min ∪ (pref.take i).foldl (fun acc c => acc ∪ c.nodes) ∅) →
      ∃ (T_core : ParseTree G A) (j₀ k₀ : ℕ) (L : List (BasicCut G)),
        T_core.yield = singleOne j₀ k₀ ∧
        typedNodesSpine T_min ∪ pref.foldl (fun acc c => acc ∪ c.nodes) ∅ ⊆ typedNodesSpine T_core ∧
        j₀ + k₀ + 1 ≤ (jm + km + 1) +
          ((typedNodesSpine T_core).card - (typedNodesSpine T_min).card) * 2 ^ (2 * G.activeVars.card + 1) ∧
        (typedNodesSpine T_min).card ≤ (typedNodesSpine T_core).card ∧
        jm + (pref.map (·.a)).sum = j₀ + (L.map (·.a)).sum ∧
        km + (pref.map (·.b)).sum = k₀ + (L.map (·.b)).sum ∧
        (∀ c ∈ L, (c.pos, c.var) ∈ typedNodesSpine T_core) := by
    intro pref
    induction pref using List.reverseRecOn with
    | nil =>
      intro _
      exact ⟨T_min, jm, km, [], hTmy, by simp, by simp, le_refl _, by simp, by simp, by simp⟩
    | append_singleton pref c ih =>
      intro hvp
      have hvp' : ∀ i (hi : i < pref.length),
          ((pref[i]'hi).pos, (pref[i]'hi).var) ∈
            typedNodesSpine T_min ∪ (pref.take i).foldl (fun acc c => acc ∪ c.nodes) ∅ := by
        intro i hi
        have h := hvp i (by simp; omega)
        rw [List.getElem_append_left hi, List.take_append_of_le_length (by omega)] at h
        exact h
      rcases ih hvp' with ⟨T_core, j₀, k₀, L, hTy, hKsub, hlenB, hcardLe, hsumA, hsumB, hLmem⟩
      have hc_in_core : (c.pos, c.var) ∈ typedNodesSpine T_core := by
        have h := hvp pref.length (by simp)
        rw [List.getElem_append_right (le_refl _)] at h
        simp only [Nat.sub_self, List.getElem_cons_zero, List.take_left] at h
        exact hKsub h
      by_cases hcn : c.nodes ⊆ typedNodesSpine T_core
      · -- Don't paste `c`; put `c` into `L`!
        refine ⟨T_core, j₀, k₀, c :: L, hTy, ?_, hlenB, hcardLe,
          by simp [List.map_append, List.sum_append]; omega,
          by simp [List.map_append, List.sum_append]; omega, ?_⟩
        · rw [List.foldl_append]; simp only [List.foldl_cons, List.foldl_nil]
          intro q hq; simp only [Finset.mem_union] at hq
          rcases hq with h1 | h2
          · exact hKsub (Finset.mem_union_left _ h1)
          · rcases h2 with h2a | h2b
            · exact hKsub (Finset.mem_union_right _ h2a)
            · exact hcn h2b
        · intro c' hc'; simp only [List.mem_cons] at hc'
          rcases hc' with rfl | hcL
          · exact hc_in_core
          · exact hLmem c' hcL
      · -- Paste `c` into `T_core`; cardinality of `typedNodesSpine` strictly increases!
        rcases paste_basicCut c T_core hTy hc_in_core with ⟨T_core', hT'y, hT'sub⟩
        have hstrict : (typedNodesSpine T_core).card + 1 ≤ (typedNodesSpine T_core').card := by
          have hss : typedNodesSpine T_core ⊂ typedNodesSpine T_core ∪ c.nodes := by
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨Finset.subset_union_left, fun hEq => hcn ?_⟩
            rw [hEq]; exact Finset.subset_union_right
          have hlt := Finset.card_lt_card hss
          have hle := Finset.card_le_card hT'sub
          omega
        have hsub_core : typedNodesSpine T_core ⊆ typedNodesSpine T_core' :=
          Finset.subset_union_left.trans hT'sub
        refine ⟨T_core', j₀ + c.a, k₀ + c.b, L, hT'y, ?_, ?_, by omega,
          by simp [List.map_append, List.sum_append]; omega,
          by simp [List.map_append, List.sum_append]; omega,
          fun c' hc' => hsub_core (hLmem c' hc')⟩
        · rw [List.foldl_append]; simp only [List.foldl_cons, List.foldl_nil]
          intro q hq; simp only [Finset.mem_union] at hq
          rcases hq with h1 | h2
          · exact hsub_core (hKsub (Finset.mem_union_left _ h1))
          · rcases h2 with h2a | h2b
            · exact hsub_core (hKsub (Finset.mem_union_right _ h2a))
            · exact hT'sub (Finset.mem_union_right _ h2b)
        · have hsm := c.small
          have hdiff : ((typedNodesSpine T_core).card - (typedNodesSpine T_min).card) + 1 ≤
              (typedNodesSpine T_core').card - (typedNodesSpine T_min).card := by omega
          have hmul : (((typedNodesSpine T_core).card - (typedNodesSpine T_min).card) + 1) *
                2 ^ (2 * G.activeVars.card + 1) ≤
              ((typedNodesSpine T_core').card - (typedNodesSpine T_min).card) *
                2 ^ (2 * G.activeVars.card + 1) :=
            Nat.mul_le_mul_right _ hdiff
          rw [Nat.add_mul, Nat.one_mul] at hmul
          omega
  rcases hbuild steps hvalid with ⟨T_core, j₀, k₀, L, hTy, _, hlenB, _, hsumA, hsumB, hLmem⟩
  have hcard_le : (typedNodesSpine T_core).card ≤ 3 * G.activeVars.card := typedNodesSpine_card_le T_core
  have hbound : j₀ + k₀ + 1 < (6 * G.activeVars.card + 1) * 2 ^ (2 * G.activeVars.card) := by
    have hdiff_le : (typedNodesSpine T_core).card - (typedNodesSpine T_min).card ≤ 3 * G.activeVars.card := by
      omega
    have hmul : ((typedNodesSpine T_core).card - (typedNodesSpine T_min).card) * 2 ^ (2 * G.activeVars.card + 1) ≤
        (3 * G.activeVars.card) * 2 ^ (2 * G.activeVars.card + 1) :=
      Nat.mul_le_mul_right _ hdiff_le
    have hpow : (3 * G.activeVars.card) * 2 ^ (2 * G.activeVars.card + 1) =
        (6 * G.activeVars.card) * 2 ^ (2 * G.activeVars.card) := by
      rw [pow_succ']; ring
    rw [Nat.add_mul, Nat.one_mul]
    omega
  exact ⟨T_core, j₀, k₀, L, hTy, hbound, by omega, by omega, hLmem⟩

/-- Helper: removing `q` elements satisfying predicate `P` from a list `L` that has `≥ q` such elements. -/
theorem remove_q_matching {α : Type*} (P : α → Prop) [DecidablePred P] :
    ∀ (L : List α) (q : ℕ), q ≤ (L.filter (fun x => decide (P x))).length →
      ∃ L' R : List α,
        R.length = q ∧
        (∀ x ∈ R, P x) ∧
        (∀ x ∈ L', x ∈ L) ∧
        ∀ (f : α → ℕ), (L.map f).sum = (L'.map f).sum + (R.map f).sum := by
  intro L
  induction L with
  | nil =>
    intro q hq
    simp at hq; subst hq
    exact ⟨[], [], rfl, by simp, by simp, by simp⟩
  | cons x rest ih =>
    intro q hq
    by_cases hPx : P x
    · cases q with
      | zero =>
        exact ⟨x :: rest, [], rfl, by simp, fun _ h => h, by simp⟩
      | succ q' =>
        simp only [List.filter_cons, decide_eq_true hPx, ↓reduceIte, List.length_cons] at hq
        rcases ih q' (by omega) with ⟨L', R, hRlen, hRP, hL'sub, hsum⟩
        refine ⟨L', x :: R, by simp [hRlen], ?_, fun y hy => List.mem_cons_of_mem x (hL'sub y hy), ?_⟩
        · intro y hy; simp only [List.mem_cons] at hy
          rcases hy with rfl | hyR; exact hPx; exact hRP y hyR
        · intro f; simp only [List.map_cons, List.sum_cons, hsum f]; omega
    · simp only [List.filter_cons, decide_eq_false hPx, Bool.false_eq_true, ↓reduceIte] at hq
      rcases ih q hq with ⟨L', R, hRlen, hRP, hL'sub, hsum⟩
      refine ⟨x :: L', R, hRlen, hRP, ?_, ?_⟩
      · intro y hy; simp only [List.mem_cons] at hy
        rcases hy with rfl | hyL; exact List.mem_cons_self; exact List.mem_cons_of_mem x (hL'sub y hyL)
      · intro f; simp only [List.map_cons, List.sum_cons, hsum f]; omega

/-- **Single-Bit Detector Diophantine Approximation Constraint:**
If a strict CNF grammar `G` with `s = G.activeVars.card` accepts `0^j 1 0^(n - 1 - j)` (`j < n`)
and rejects `0^k 1 0^(n - 1 - k)` for every `k < n, k ≠ j`, then either `n < 2^(8*s + 5)`, OR
there exist `a₁, b₁ < 2^(2*s + 1)` with `1 ≤ a₁ + b₁` such that
`|(a₁ + b₁) * j - a₁ * (n - 1)| < (a₁ + b₁) * (6*s + 1) * 2^(2*s)`. -/
theorem single_bit_detector_constraint {G : CNFGrammar} {n j : ℕ} (hj : j < n)
    (hacc : G.Accepts (singleOne j (n - 1 - j)))
    (hrej : ∀ k < n, k ≠ j → ¬ G.Accepts (singleOne k (n - 1 - k))) :
    n < 2 ^ (8 * G.activeVars.card + 5) ∨
    ∃ a₁ b₁ : ℕ, 1 ≤ a₁ + b₁ ∧ a₁ + b₁ < 2 ^ (2 * G.activeVars.card + 1) ∧
      ((a₁ + b₁) * j ≤ a₁ * (n - 1) + (a₁ + b₁) * ((6 * G.activeVars.card + 1) * 2 ^ (2 * G.activeVars.card)) ∧
       a₁ * (n - 1) ≤ (a₁ + b₁) * j + (a₁ + b₁) * ((6 * G.activeVars.card + 1) * 2 ^ (2 * G.activeVars.card))) := by
  let s := G.activeVars.card
  let M := 2 ^ (2 * s + 1)
  let B := (6 * s + 1) * 2 ^ (2 * s)
  rcases derives_to_parseTree hacc with ⟨T, hTy⟩
  rcases decompose_singleOne_tree T hTy with ⟨T_core, j₀, k₀, L, hTcy, hcoreB, hj_sum, hk_sum, hLmem⟩
  -- Check whether some pair `(a₁, b₁) ∈ Finset.range M ×ˢ Finset.range M` appears `≥ M` times in `L`:
  by_cases hheavy : ∃ p ∈ Finset.range M ×ˢ Finset.range M,
      M ≤ (L.filter (fun c => decide (c.a = p.1 ∧ c.b = p.2))).length
  · rcases hheavy with ⟨⟨a₁, b₁⟩, hpMem, hcnt⟩
    dsimp only at hcnt
    have hL_nonempty : (L.filter (fun c => decide (c.a = a₁ ∧ c.b = b₁))).length > 0 := by
      have : 1 ≤ M := Nat.one_le_pow _ _ (by norm_num)
      omega
    have hex1 : ∃ c₁ ∈ L, c₁.a = a₁ ∧ c₁.b = b₁ := by
      have hne : L.filter (fun c => decide (c.a = a₁ ∧ c.b = b₁)) ≠ [] :=
        List.ne_nil_of_length_pos hL_nonempty
      cases hfl : L.filter (fun c => decide (c.a = a₁ ∧ c.b = b₁)) with
      | nil => exact (hne hfl).elim
      | cons c₁ _ =>
        have hm := List.mem_filter.mp (hfl ▸ List.mem_cons_self)
        exact ⟨c₁, hm.1, of_decide_eq_true hm.2⟩
    rcases hex1 with ⟨c₁, _hc1_mem, rfl, rfl⟩
    have hq1_pos : 1 ≤ c₁.a + c₁.b := c₁.posSum
    have hq1_lt : c₁.a + c₁.b < M := c₁.small
    -- Prove EVERY `c₂ ∈ L` has the exact same slope `c₂.a * c₁.b = c₁.a * c₂.b`!
    have hslope : ∀ c₂ ∈ L, c₂.a * c₁.b = c₁.a * c₂.b := by
      intro c₂ hc₂
      by_contra hne_slope
      let q₁ := c₁.a + c₁.b
      let q₂ := c₂.a + c₂.b
      have hq2_lt : q₂ < M := c₂.small
      -- Remove `q₂` elements with `(a, b) = (c₁.a, c₁.b)` from `L` and add `q₁` copies of `c₂`!
      rcases remove_q_matching (fun c : BasicCut G => c.a = c₁.a ∧ c.b = c₁.b) L q₂ (by omega) with
        ⟨L', R, hRlen, hRP, hL'sub, hsum⟩
      have hRa : (R.map (·.a)).sum = q₂ * c₁.a := by
        have hmap : R.map (·.a) = List.replicate q₂ c₁.a := by
          apply List.ext_getElem
          · simp [hRlen]
          · intro i hi1 hi2
            simp only [List.getElem_map, List.getElem_replicate]
            exact (hRP (R[i]'(by simpa using hi1)) (List.getElem_mem _)).1
        rw [hmap, List.sum_replicate, smul_eq_mul]
      have hRb : (R.map (·.b)).sum = q₂ * c₁.b := by
        have hmap : R.map (·.b) = List.replicate q₂ c₁.b := by
          apply List.ext_getElem
          · simp [hRlen]
          · intro i hi1 hi2
            simp only [List.getElem_map, List.getElem_replicate]
            exact (hRP (R[i]'(by simpa using hi1)) (List.getElem_mem _)).2
        rw [hmap, List.sum_replicate, smul_eq_mul]
      let L_new := L' ++ List.replicate q₁ c₂
      have hL_new_mem : ∀ c ∈ L_new, (c.pos, c.var) ∈ typedNodesSpine T_core := by
        intro c hc
        simp only [L_new, List.mem_append, List.mem_replicate] at hc
        rcases hc with hcL' | ⟨_, rfl⟩
        · exact hLmem c (hL'sub c hcL')
        · exact hLmem c hc₂
      rcases paste_many_cuts L_new T_core hTcy hL_new_mem with ⟨T_new, hTny, _⟩
      let j_new := j₀ + (L_new.map (·.a)).sum
      let k_new := k₀ + (L_new.map (·.b)).sum
      have hj_rel : j_new + q₂ * c₁.a = j + q₁ * c₂.a := by
        have h1 := hsum (·.a)
        dsimp only [j_new, L_new]
        rw [List.map_append, List.sum_append, List.map_replicate, List.sum_replicate, smul_eq_mul]
        omega
      have hk_rel : k_new + q₂ * c₁.b = (n - 1 - j) + q₁ * c₂.b := by
        have h1 := hsum (·.b)
        dsimp only [k_new, L_new]
        rw [List.map_append, List.sum_append, List.map_replicate, List.sum_replicate, smul_eq_mul]
        omega
      have htot_eq : j_new + k_new = n - 1 := by
        have hprod : q₂ * (c₁.a + c₁.b) = q₁ * (c₂.a + c₂.b) := by dsimp only [q₁, q₂]; ring
        have : q₂ * c₁.a + q₂ * c₁.b = q₁ * c₂.a + q₁ * c₂.b := by linarith
        omega
      have hj_ne : j_new ≠ j := by
        intro heq
        have hqeq : q₂ * c₁.a = q₁ * c₂.a := by omega
        apply hne_slope
        dsimp only [q₁, q₂] at hqeq
        linarith
      have hacc_new : G.Accepts (singleOne j_new (n - 1 - j_new)) := by
        have hk_eq : k_new = n - 1 - j_new := by omega
        rw [← hk_eq, ← hTny]
        exact T_new.toDerives
      exact hrej j_new (by omega) hj_ne hacc_new
    -- Sum `c.a * (c₁.a + c₁.b) = c₁.a * (c.a + c.b)` over `L`:
    have hsum_eq : (L.map (·.a)).sum * (c₁.a + c₁.b) = c₁.a * ((L.map (·.a)).sum + (L.map (·.b)).sum) := by
      suffices ∀ (L0 : List (BasicCut G)), (∀ c ∈ L0, c.a * c₁.b = c₁.a * c.b) →
          (L0.map (·.a)).sum * (c₁.a + c₁.b) = c₁.a * ((L0.map (·.a)).sum + (L0.map (·.b)).sum) from
        this L hslope
      intro L0 hL0
      induction L0 with
      | nil => simp
      | cons c rest ih =>
        have h1 := hL0 c (by simp)
        have h2 := ih (fun c' hc' => hL0 c' (List.mem_cons_of_mem c hc'))
        simp only [List.map_cons, List.sum_cons]
        linarith
    have hcoreB' : j₀ + k₀ + 1 < B := hcoreB
    right
    refine ⟨c₁.a, c₁.b, hq1_pos, hq1_lt, ?_, ?_⟩
    · change (c₁.a + c₁.b) * j ≤ c₁.a * (n - 1) + (c₁.a + c₁.b) * B
      have h1 : (c₁.a + c₁.b) * j = (c₁.a + c₁.b) * j₀ + c₁.a * ((n - 1) - (j₀ + k₀)) := by
        have hsub1 : (L.map (·.a)).sum + (L.map (·.b)).sum = (n - 1) - (j₀ + k₀) := by omega
        rw [hj_sum, Nat.mul_add, Nat.mul_comm (c₁.a + c₁.b) (L.map (·.a)).sum, hsum_eq, hsub1]
      have hle_sub : c₁.a * ((n - 1) - (j₀ + k₀)) ≤ c₁.a * (n - 1) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      have hj0_le : (c₁.a + c₁.b) * j₀ ≤ (c₁.a + c₁.b) * B := Nat.mul_le_mul_left _ (by omega)
      omega
    · change c₁.a * (n - 1) ≤ (c₁.a + c₁.b) * j + (c₁.a + c₁.b) * B
      have h1 : (c₁.a + c₁.b) * j + c₁.a * (j₀ + k₀) = (c₁.a + c₁.b) * j₀ + c₁.a * (n - 1) := by
        have hsub1 : (L.map (·.a)).sum + (L.map (·.b)).sum + (j₀ + k₀) = n - 1 := by omega
        have h2 : c₁.a * ((L.map (·.a)).sum + (L.map (·.b)).sum) + c₁.a * (j₀ + k₀) = c₁.a * (n - 1) := by
          rw [← Nat.mul_add, hsub1]
        have h3 : (c₁.a + c₁.b) * j = (c₁.a + c₁.b) * j₀ + c₁.a * ((L.map (·.a)).sum + (L.map (·.b)).sum) := by
          rw [hj_sum, Nat.mul_add, Nat.mul_comm (c₁.a + c₁.b) (L.map (·.a)).sum, hsum_eq]
        omega
      have hc1_le : c₁.a * (j₀ + k₀) ≤ (c₁.a + c₁.b) * B := by
        calc c₁.a * (j₀ + k₀) ≤ (c₁.a + c₁.b) * (j₀ + k₀) := Nat.mul_le_mul_right _ (by omega)
          _ ≤ (c₁.a + c₁.b) * B := Nat.mul_le_mul_left _ (by omega)
      omega
  · -- Case 1: Every pair `(a, b) ∈ Finset.range M ×ˢ Finset.range M` appears `< M` times in `L`!
    push Not at hheavy
    left
    change n < 2 ^ (8 * s + 5)
    have hcoreB' : j₀ + k₀ + 1 < B := hcoreB
    -- Bound `L.length ≤ M * M * M`:
    have hLlen : L.length ≤ M * M * M := by
      -- Partition `L` by `(c.a, c.b) ∈ Finset.range M ×ˢ Finset.range M`:
      have hpart : ∀ (L0 : List (BasicCut G)),
          L0.length = ∑ p ∈ Finset.range M ×ˢ Finset.range M,
            (L0.filter (fun c => decide (c.a = p.1 ∧ c.b = p.2))).length := by
        intro L0
        induction L0 with
        | nil => simp
        | cons c rest ih =>
          rw [List.length_cons, ih]
          have hc_mem : (c.a, c.b) ∈ Finset.range M ×ˢ Finset.range M := by
            have hsm : c.a + c.b < M := c.small
            simp only [Finset.mem_product, Finset.mem_range]; omega
          have hstep : ∀ p ∈ Finset.range M ×ˢ Finset.range M,
              ((c :: rest).filter (fun x => decide (x.a = p.1 ∧ x.b = p.2))).length =
              (rest.filter (fun x => decide (x.a = p.1 ∧ x.b = p.2))).length +
                if p = (c.a, c.b) then 1 else 0 := by
            intro p _
            by_cases hEq : p = (c.a, c.b)
            · subst hEq; simp
            · have hne : ¬ (c.a = p.1 ∧ c.b = p.2) := by
                intro h; apply hEq; ext <;> [exact h.1.symm; exact h.2.symm]
              simp [hne, hEq]
          rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_ite_eq',
            if_pos hc_mem]
      rw [hpart L]
      calc ∑ p ∈ Finset.range M ×ˢ Finset.range M,
            (L.filter (fun c => decide (c.a = p.1 ∧ c.b = p.2))).length
          ≤ ∑ _p ∈ Finset.range M ×ˢ Finset.range M, M :=
            Finset.sum_le_sum (fun p hp => le_of_lt (hheavy p hp))
        _ = (Finset.range M ×ˢ Finset.range M).card * M := by simp
        _ = M * M * M := by simp [Finset.card_product]
    have hLsum : (L.map (·.a)).sum + (L.map (·.b)).sum ≤ L.length * M := by
      suffices ∀ (L0 : List (BasicCut G)),
          (L0.map (·.a)).sum + (L0.map (·.b)).sum ≤ L0.length * M from this L
      intro L0
      induction L0 with
      | nil => simp
      | cons c rest ih =>
        have hsm : c.a + c.b < M := c.small
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
        omega
    have htot_sum : (L.map (·.a)).sum + (L.map (·.b)).sum ≤ M * M * M * M :=
      hLsum.trans (Nat.mul_le_mul_right M hLlen)
    have hM4 : M * M * M * M = 2 ^ (8 * s + 4) := by
      dsimp only [M]
      rw [← pow_add, ← pow_add, ← pow_add]
      congr 1; omega
    have hB_lt : B ≤ 2 ^ (8 * s + 4) := by
      dsimp only [B]
      have h6 : 6 * s + 1 ≤ 2 ^ (6 * s + 4) := by
        clear * -
        induction s with
        | zero => norm_num
        | succ s ih =>
          have hpow : 2 ^ (6 * (s + 1) + 4) = 64 * 2 ^ (6 * s + 4) := by
            rw [show 6 * (s + 1) + 4 = (6 * s + 4) + 6 by omega, pow_add]; ring
          omega
      calc (6 * s + 1) * 2 ^ (2 * s)
          ≤ 2 ^ (6 * s + 4) * 2 ^ (2 * s) := Nat.mul_le_mul_right _ h6
        _ = 2 ^ (8 * s + 4) := by rw [← pow_add]; congr 1; omega
    have h8s5 : 2 ^ (8 * s + 5) = 2 ^ (8 * s + 4) + 2 ^ (8 * s + 4) := by
      rw [show 8 * s + 5 = (8 * s + 4) + 1 by omega, pow_succ']; ring
    rw [hM4] at htot_sum
    omega

/-- **Theorem C (Exact Single-Bit Detector `Ω(log n)` Variable Lower Bound):**
For every `s : ℕ` and every `n ≥ 2^(8 * s + 5)`, there exists a position `j < n` such that
NO strict CNF grammar with `≤ s` active nonterminals accepts `0^j 1 0^(n - 1 - j)` while
rejecting `0^k 1 0^(n - 1 - k)` for all `k < n, k ≠ j`. -/
theorem single_bit_detector_lower_bound (s n : ℕ) (hn : 2 ^ (8 * s + 5) ≤ n) :
    ∃ j < n, ∀ G : CNFGrammar, G.activeVars.card ≤ s →
      G.Accepts (singleOne j (n - 1 - j)) →
      ∃ k < n, k ≠ j ∧ G.Accepts (singleOne k (n - 1 - k)) := by
  let M := 2 ^ (2 * s + 1)
  let B := (6 * s + 1) * 2 ^ (2 * s)
  let pairs := (Finset.range M ×ˢ Finset.range M).filter (fun p => 1 ≤ p.1 + p.2)
  let covered : Finset ℕ :=
    pairs.biUnion (fun p =>
      (Finset.range n).filter (fun j =>
        (p.1 + p.2) * j ≤ p.1 * (n - 1) + (p.1 + p.2) * B ∧
        p.1 * (n - 1) ≤ (p.1 + p.2) * j + (p.1 + p.2) * B))
  -- Each pair `(a₁, b₁)` covers at most `2 * B + 1` integers `j`:
  have hpair_card : ∀ p ∈ pairs,
      ((Finset.range n).filter (fun j =>
        (p.1 + p.2) * j ≤ p.1 * (n - 1) + (p.1 + p.2) * B ∧
        p.1 * (n - 1) ≤ (p.1 + p.2) * j + (p.1 + p.2) * B)).card ≤ 2 * B + 1 := by
    intro p hp
    set S := (Finset.range n).filter (fun j =>
        (p.1 + p.2) * j ≤ p.1 * (n - 1) + (p.1 + p.2) * B ∧
        p.1 * (n - 1) ≤ (p.1 + p.2) * j + (p.1 + p.2) * B)
    have hq_pos : 1 ≤ p.1 + p.2 := (Finset.mem_filter.mp hp).2
    by_cases hne : S.Nonempty
    · let jmin := S.min' hne
      have hjmin_mem : jmin ∈ S := Finset.min'_mem S hne
      have hmin_spec := (Finset.mem_filter.mp hjmin_mem).2
      have hsub : S ⊆ Finset.Ico jmin (jmin + (2 * B + 1)) := by
        intro j hj
        have hge : jmin ≤ j := Finset.min'_le S j hj
        have hj_spec := (Finset.mem_filter.mp hj).2
        have hmul : (p.1 + p.2) * j ≤ (p.1 + p.2) * (jmin + 2 * B) := by
          rw [Nat.mul_add]
          linarith [hj_spec.1, hmin_spec.2]
        have hle : j ≤ jmin + 2 * B := Nat.le_of_mul_le_mul_left hmul (by omega)
        exact Finset.mem_Ico.mpr ⟨hge, by omega⟩
      calc S.card ≤ (Finset.Ico jmin (jmin + (2 * B + 1))).card := Finset.card_le_card hsub
        _ = 2 * B + 1 := by simp [Nat.card_Ico]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
  have hcov_card : covered.card < n := by
    have h1 : covered.card ≤ pairs.card * (2 * B + 1) := by
      calc covered.card
          ≤ ∑ p ∈ pairs, ((Finset.range n).filter (fun j =>
              (p.1 + p.2) * j ≤ p.1 * (n - 1) + (p.1 + p.2) * B ∧
              p.1 * (n - 1) ≤ (p.1 + p.2) * j + (p.1 + p.2) * B)).card := Finset.card_biUnion_le
        _ ≤ ∑ _p ∈ pairs, (2 * B + 1) := Finset.sum_le_sum hpair_card
        _ = pairs.card * (2 * B + 1) := by simp
    have hpairs_le : pairs.card ≤ M * M := by
      calc pairs.card ≤ (Finset.range M ×ˢ Finset.range M).card := Finset.card_filter_le _ _
        _ = M * M := by simp [Finset.card_product]
    have h2B1 : 2 * B + 1 < 2 ^ (4 * s + 3) := by
      dsimp only [B]
      have h12 : 12 * s + 3 < 2 ^ (2 * s + 3) := by
        clear * -
        induction s with
        | zero => norm_num
        | succ s ih =>
          have hpow : 2 ^ (2 * (s + 1) + 3) = 4 * 2 ^ (2 * s + 3) := by
            rw [show 2 * (s + 1) + 3 = (2 * s + 3) + 2 by omega, pow_add]; ring
          omega
      have h1_le : 1 ≤ 2 ^ (2 * s) := Nat.one_le_pow _ _ (by norm_num)
      calc 2 * ((6 * s + 1) * 2 ^ (2 * s)) + 1
          ≤ (12 * s + 3) * 2 ^ (2 * s) := by nlinarith
        _ < 2 ^ (2 * s + 3) * 2 ^ (2 * s) := Nat.mul_lt_mul_of_pos_right h12 (by omega)
        _ = 2 ^ (4 * s + 3) := by rw [← pow_add]; congr 1; omega
    have hMM : M * M = 2 ^ (4 * s + 2) := by
      dsimp only [M]; rw [← pow_add]; congr 1; omega
    have hlt_pow : M * M * (2 * B + 1) < 2 ^ (8 * s + 5) := by
      calc M * M * (2 * B + 1)
          = 2 ^ (4 * s + 2) * (2 * B + 1) := by rw [hMM]
        _ < 2 ^ (4 * s + 2) * 2 ^ (4 * s + 3) :=
            Nat.mul_lt_mul_of_pos_left h2B1 (by positivity)
        _ = 2 ^ (8 * s + 5) := by rw [← pow_add]; congr 1; omega
    have hle_m : pairs.card * (2 * B + 1) ≤ M * M * (2 * B + 1) :=
      Nat.mul_le_mul_right _ hpairs_le
    omega
  -- Pick `j ∈ Finset.range n \ covered`!
  have hne_sdiff : (Finset.range n \ covered).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : Finset.range n ⊆ covered := Finset.sdiff_eq_empty_iff_subset.mp hemp
    have hle := Finset.card_le_card hsub
    rw [Finset.card_range] at hle
    omega
  rcases hne_sdiff with ⟨j, hj_sdiff⟩
  rcases Finset.mem_sdiff.mp hj_sdiff with ⟨hj_rng, hj_not_cov⟩
  have hj_lt : j < n := Finset.mem_range.mp hj_rng
  refine ⟨j, hj_lt, ?_⟩
  intro G hGs hacc
  by_contra hno
  push Not at hno
  have hcons := single_bit_detector_constraint hj_lt hacc hno
  rcases hcons with hlt_n | ⟨a₁, b₁, hq1, hq1_lt, hI1, hI2⟩
  · have hpow_mono : 2 ^ (8 * G.activeVars.card + 5) ≤ 2 ^ (8 * s + 5) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · apply hj_not_cov
    simp only [covered, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
    have hpowM : 2 ^ (2 * G.activeVars.card + 1) ≤ M :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpowB : (6 * G.activeVars.card + 1) * 2 ^ (2 * G.activeVars.card) ≤ B := by
      dsimp only [B]
      exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) (by omega))
    refine ⟨(a₁, b₁), ?_, hj_lt, ?_, ?_⟩
    · simp only [pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨by omega, by omega⟩, hq1⟩
    · have hmulB : (a₁ + b₁) * ((6 * G.activeVars.card + 1) * 2 ^ (2 * G.activeVars.card)) ≤
          (a₁ + b₁) * B := Nat.mul_le_mul_left _ hpowB
      dsimp only; omega
    · have hmulB : (a₁ + b₁) * ((6 * G.activeVars.card + 1) * 2 ^ (2 * G.activeVars.card)) ≤
          (a₁ + b₁) * B := Nat.mul_le_mul_left _ hpowB
      dsimp only; omega

/-- **Theorem C (Production-Count Corollary):**
For every `p : ℕ` and every `n ≥ 2^(8 * p + 5)`, there exists a position `j < n` admitting
NO exact single-bit strict CNF detector with `≤ p` productions. -/
theorem single_bit_detector_prodCount_lower_bound (p n : ℕ) (hn : 2 ^ (8 * p + 5) ≤ n) :
    ∃ j < n, ∀ G : CNFGrammar, G.prodCount ≤ p →
      G.Accepts (singleOne j (n - 1 - j)) →
      ∃ k < n, k ≠ j ∧ G.Accepts (singleOne k (n - 1 - k)) := by
  rcases single_bit_detector_lower_bound p n hn with ⟨j, hj, h⟩
  refine ⟨j, hj, fun G hGp hacc => h G ?_ hacc⟩
  calc G.activeVars.card
      ≤ (G.termRules.image Prod.fst).card + (G.binRules.image Prod.fst).card :=
        Finset.card_union_le _ _
    _ ≤ G.termRules.card + G.binRules.card :=
        Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = G.prodCount := rfl
    _ ≤ p := hGp

end SingleBitDetector

/-! ## Section 5: Pure-Mathlib Public Theorem Statements (0 Custom Definitions)

Every theorem in this section uses **zero custom definitions** in its type signature: strict CNF
grammars are represented directly as triples `(start : ℕ, termRules : Finset (ℕ × Bool),
binRules : Finset (ℕ × ℕ × ℕ))` with production count `termRules.card + binRules.card` and
impredicative least-fixpoint derivation (proven equivalent to `CNFGrammar.Derives` in
`derives_iff_least_fixpoint`).
-/

section PureMathlibWrappers

/-- **Pure-Mathlib Theorem A (Upper Bound — 0 Custom Defs):**
Every binary word `w` of length `n` with no repeated contiguous length-`r` factor (`r ≥ 1`) is
separated from every distinct length-`n` word `x` by a strict CNF grammar with at most
`2^(b + 1) + (r + 1) / b + 8` productions (for any `b ≥ 1`). -/
theorem ppl146_uniq_factor_cnf_separation_pure {n r b : ℕ} (hr : 1 ≤ r) (hb : 1 ≤ b)
    {w x : List Bool} (hw : w.length = n) (hx : x.length = n) (hne : w ≠ x)
    (huniq : ∀ i j : ℕ, i < j → j + r ≤ w.length → (w.drop i).take r ≠ (w.drop j).take r) :
    ∃ (start : ℕ) (termRules : Finset (ℕ × Bool)) (binRules : Finset (ℕ × ℕ × ℕ)),
      termRules.card + binRules.card ≤ 2 ^ (b + 1) + (r + 1) / b + 8 ∧
      (((∀ P : ℕ → List Bool → Prop,
          (∀ X a, (X, a) ∈ termRules → P X [a]) →
          (∀ X Y Z u v, (X, Y, Z) ∈ binRules → P Y u → P Z v → P X (u ++ v)) →
          P start w) ∧
        ¬ (∀ P : ℕ → List Bool → Prop,
          (∀ X a, (X, a) ∈ termRules → P X [a]) →
          (∀ X Y Z u v, (X, Y, Z) ∈ binRules → P Y u → P Z v → P X (u ++ v)) →
          P start x)) ∨
       ((∀ P : ℕ → List Bool → Prop,
          (∀ X a, (X, a) ∈ termRules → P X [a]) →
          (∀ X Y Z u v, (X, Y, Z) ∈ binRules → P Y u → P Z v → P X (u ++ v)) →
          P start x) ∧
        ¬ (∀ P : ℕ → List Bool → Prop,
          (∀ X a, (X, a) ∈ termRules → P X [a]) →
          (∀ X Y Z u v, (X, Y, Z) ∈ binRules → P Y u → P Z v → P X (u ++ v)) →
          P start w))) := by
  rcases uniq_factor_cnf_separation hr hb hw hx hne huniq with ⟨G, hsep, hcard⟩
  refine ⟨G.start, G.termRules, G.binRules, hcard, ?_⟩
  simpa only [CNFGrammar.Separates, CNFGrammar.Accepts, derives_iff_least_fixpoint] using hsep

/-- **Pure-Mathlib Theorem A (Density Bound — 0 Custom Defs):**
For all `n` and `r ≥ 1`, the set `S` of length-`n` binary words having no repeated contiguous
length-`r` factor satisfies `2^n ≤ S.card + n.choose 2 * 2^(n - r)`. -/
theorem ppl146_uniq_factor_density_pure (n r : ℕ) (hr : 1 ≤ r) :
    ∃ S : Finset (Fin n → Bool),
      (∀ w, w ∈ S ↔
        ∀ i j : ℕ, i < j → j + r ≤ n →
          ((List.ofFn w).drop i).take r ≠ ((List.ofFn w).drop j).take r) ∧
      2 ^ n ≤ S.card + n.choose 2 * 2 ^ (n - r) := by
  classical
  refine ⟨WUniq n r, ?_, uniq_factor_card_lower n r hr⟩
  intro w
  rw [WUniq, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, HasNoRepeatedFactor, List.length_ofFn]

/-- **Pure-Mathlib Theorem A (CPRS Full `{0,1}^n` Lower Bound — 0 Custom Defs):**
If every pair of distinct binary words of length `n` is separated by a strict CNF grammar with
at most `p` productions, then `n ≤ (p + 1) * (p^3 + 2*p + 1)^p`. -/
theorem ppl146_cnf_lower_bound_pure (n p : ℕ)
    (hsep : ∀ w x : Fin n → Bool, w ≠ x →
      ∃ (start : ℕ) (termRules : Finset (ℕ × Bool)) (binRules : Finset (ℕ × ℕ × ℕ)),
        termRules.card + binRules.card ≤ p ∧
        (((∀ P : ℕ → List Bool → Prop,
            (∀ X a, (X, a) ∈ termRules → P X [a]) →
            (∀ X Y Z u v, (X, Y, Z) ∈ binRules → P Y u → P Z v → P X (u ++ v)) →
            P start (List.ofFn w)) ∧
          ¬ (∀ P : ℕ → List Bool → Prop,
            (∀ X a, (X, a) ∈ termRules → P X [a]) →
            (∀ X Y Z u v, (X, Y, Z) ∈ binRules → P Y u → P Z v → P X (u ++ v)) →
            P start (List.ofFn x))) ∨
         ((∀ P : ℕ → List Bool → Prop,
            (∀ X a, (X, a) ∈ termRules → P X [a]) →
            (∀ X Y Z u v, (X, Y, Z) ∈ binRules → P Y u → P Z v → P X (u ++ v)) →
            P start (List.ofFn x)) ∧
          ¬ (∀ P : ℕ → List Bool → Prop,
            (∀ X a, (X, a) ∈ termRules → P X [a]) →
            (∀ X Y Z u v, (X, Y, Z) ∈ binRules → P Y u → P Z v → P X (u ++ v)) →
            P start (List.ofFn w))))) :
    n ≤ (p + 1) * (p ^ 3 + 2 * p + 1) ^ p := by
  apply cnf_separation_lower_bound n p
  intro w x hne
  rcases hsep w x hne with ⟨s, t, b, hcard, h⟩
  let G : CNFGrammar := ⟨s, t, b⟩
  refine ⟨G, ?_, hcard⟩
  simpa only [CNFGrammar.Separates, CNFGrammar.Accepts, derives_iff_least_fixpoint] using h

/-- **Pure-Mathlib Theorem A (Matching Lower Bound on `W_uniq(n, r)` — 0 Custom Defs):**
Whenever `1 ≤ r ≤ n` and `2 * n.choose 2 ≤ 2^r`, separating all pairs of distinct length-`n`
binary words having no repeated length-`r` factor with `≤ p` strict CNF productions requires
`n - 1 ≤ (p + 1) * (p^3 + 2*p + 1)^p`. -/
theorem ppl146_uniq_factor_lower_bound_pure (n r p : ℕ) (hn : 1 ≤ n) (hr1 : 1 ≤ r) (hr : r ≤ n)
    (hdense : 2 * n.choose 2 ≤ 2 ^ r)
    (hsep : ∀ w x : Fin n → Bool,
      (∀ i j : ℕ, i < j → j + r ≤ n → ((List.ofFn w).drop i).take r ≠ ((List.ofFn w).drop j).take r) →
      (∀ i j : ℕ, i < j → j + r ≤ n → ((List.ofFn x).drop i).take r ≠ ((List.ofFn x).drop j).take r) →
      w ≠ x →
      ∃ (start : ℕ) (termRules : Finset (ℕ × Bool)) (binRules : Finset (ℕ × ℕ × ℕ)),
        termRules.card + binRules.card ≤ p ∧
        (((∀ P : ℕ → List Bool → Prop,
            (∀ X a, (X, a) ∈ termRules → P X [a]) →
            (∀ X Y Z u v, (X, Y, Z) ∈ binRules → P Y u → P Z v → P X (u ++ v)) →
            P start (List.ofFn w)) ∧
          ¬ (∀ P : ℕ → List Bool → Prop,
            (∀ X a, (X, a) ∈ termRules → P X [a]) →
            (∀ X Y Z u v, (X, Y, Z) ∈ binRules → P Y u → P Z v → P X (u ++ v)) →
            P start (List.ofFn x))) ∨
         ((∀ P : ℕ → List Bool → Prop,
            (∀ X a, (X, a) ∈ termRules → P X [a]) →
            (∀ X Y Z u v, (X, Y, Z) ∈ binRules → P Y u → P Z v → P X (u ++ v)) →
            P start (List.ofFn x)) ∧
          ¬ (∀ P : ℕ → List Bool → Prop,
            (∀ X a, (X, a) ∈ termRules → P X [a]) →
            (∀ X Y Z u v, (X, Y, Z) ∈ binRules → P Y u → P Z v → P X (u ++ v)) →
            P start (List.ofFn w))))) :
    n - 1 ≤ (p + 1) * (p ^ 3 + 2 * p + 1) ^ p := by
  classical
  apply uniq_factor_lower_bound n r p hn hr1 hr hdense
  intro w hw x hx hne
  have hw' : ∀ i j : ℕ, i < j → j + r ≤ n →
      ((List.ofFn w).drop i).take r ≠ ((List.ofFn w).drop j).take r := by
    rw [WUniq, Finset.mem_filter] at hw
    simpa only [Finset.mem_univ, true_and, HasNoRepeatedFactor, List.length_ofFn] using hw
  have hx' : ∀ i j : ℕ, i < j → j + r ≤ n →
      ((List.ofFn x).drop i).take r ≠ ((List.ofFn x).drop j).take r := by
    rw [WUniq, Finset.mem_filter] at hx
    simpa only [Finset.mem_univ, true_and, HasNoRepeatedFactor, List.length_ofFn] using hx
  rcases hsep w x hw' hx' hne with ⟨s, t, b, hcard, h⟩
  let G : CNFGrammar := ⟨s, t, b⟩
  refine ⟨G, ?_, hcard⟩
  simpa only [CNFGrammar.Separates, CNFGrammar.Accepts, derives_iff_least_fixpoint] using h

/-- **Pure-Mathlib Theorem B (Hamming-Distance Isolating Modulus — 0 Custom Defs):**
If `w, x : List Bool` of length `n` differ at index `j₀ < n`, and `p ≥ 2` isolates `j₀` modulo `p`
from all other differing indices, then there exists a strict CNF grammar separating `w` and `x`
with at most `6 * Nat.log 2 p + 14` productions. -/
theorem ppl146_hamming_isolating_modulus_pure {n p j₀ : ℕ} (hp : 2 ≤ p) (hj₀ : j₀ < n)
    {w x : List Bool} (hw : w.length = n) (hx : x.length = n)
    (hdiff : w[j₀]? ≠ x[j₀]?)
    (hisol : ∀ j < n, j ≠ j₀ → j % p = j₀ % p → w[j]? = x[j]?) :
    ∃ (start : ℕ) (termRules : Finset (ℕ × Bool)) (binRules : Finset (ℕ × ℕ × ℕ)),
      termRules.card + binRules.card ≤ 6 * Nat.log 2 p + 14 ∧
      (((∀ P : ℕ → List Bool → Prop,
          (∀ X a, (X, a) ∈ termRules → P X [a]) →
          (∀ X Y Z u v, (X, Y, Z) ∈ binRules → P Y u → P Z v → P X (u ++ v)) →
          P start w) ∧
        ¬ (∀ P : ℕ → List Bool → Prop,
          (∀ X a, (X, a) ∈ termRules → P X [a]) →
          (∀ X Y Z u v, (X, Y, Z) ∈ binRules → P Y u → P Z v → P X (u ++ v)) →
          P start x)) ∨
       ((∀ P : ℕ → List Bool → Prop,
          (∀ X a, (X, a) ∈ termRules → P X [a]) →
          (∀ X Y Z u v, (X, Y, Z) ∈ binRules → P Y u → P Z v → P X (u ++ v)) →
          P start x) ∧
        ¬ (∀ P : ℕ → List Bool → Prop,
          (∀ X a, (X, a) ∈ termRules → P X [a]) →
          (∀ X Y Z u v, (X, Y, Z) ∈ binRules → P Y u → P Z v → P X (u ++ v)) →
          P start w))) := by
  rcases hamming_isolating_modulus_cnf_separation hp hj₀ hw hx hdiff hisol with ⟨G, hsep, hcard⟩
  refine ⟨G.start, G.termRules, G.binRules, hcard, ?_⟩
  simpa only [CNFGrammar.Separates, CNFGrammar.Accepts, derives_iff_least_fixpoint] using hsep

/-- **Pure-Mathlib Theorem C (Exact Single-Bit Detector `Ω(log n)` Variable Lower Bound — 0 Custom Defs):**
For every `s : ℕ` and every `n ≥ 2^(8 * s + 5)`, there exists a position `j < n` such that no
strict CNF grammar with `≤ s` active (LHS) nonterminals accepts `0^j 1 0^(n - 1 - j)` while
rejecting `0^k 1 0^(n - 1 - k)` for all `k < n, k ≠ j`. -/
theorem ppl146_single_bit_detector_lower_bound_pure (s n : ℕ) (hn : 2 ^ (8 * s + 5) ≤ n) :
    ∃ j < n, ∀ (start : ℕ) (termRules : Finset (ℕ × Bool)) (binRules : Finset (ℕ × ℕ × ℕ)),
      (termRules.image Prod.fst ∪ binRules.image Prod.fst).card ≤ s →
      (∀ P : ℕ → List Bool → Prop,
        (∀ X a, (X, a) ∈ termRules → P X [a]) →
        (∀ X Y Z u v, (X, Y, Z) ∈ binRules → P Y u → P Z v → P X (u ++ v)) →
        P start (List.replicate j false ++ [true] ++ List.replicate (n - 1 - j) false)) →
      ∃ k < n, k ≠ j ∧
        (∀ P : ℕ → List Bool → Prop,
          (∀ X a, (X, a) ∈ termRules → P X [a]) →
          (∀ X Y Z u v, (X, Y, Z) ∈ binRules → P Y u → P Z v → P X (u ++ v)) →
          P start (List.replicate k false ++ [true] ++ List.replicate (n - 1 - k) false)) := by
  rcases single_bit_detector_lower_bound s n hn with ⟨j, hj, h⟩
  refine ⟨j, hj, ?_⟩
  intro start termRules binRules hvars hacc
  let G : CNFGrammar := ⟨start, termRules, binRules⟩
  have hacc' : G.Accepts (singleOne j (n - 1 - j)) :=
    (derives_iff_least_fixpoint G start _).mpr hacc
  rcases h G hvars hacc' with ⟨k, hk, hne, hkacc⟩
  exact ⟨k, hk, hne, (derives_iff_least_fixpoint G start _).mp hkacc⟩

/-- **Pure-Mathlib Theorem C (Exact Single-Bit Detector `Ω(log n)` Production Lower Bound — 0 Custom Defs):**
For every `p : ℕ` and every `n ≥ 2^(8 * p + 5)`, there exists a position `j < n` such that no
strict CNF grammar with `≤ p` productions accepts `0^j 1 0^(n - 1 - j)` while rejecting
`0^k 1 0^(n - 1 - k)` for all `k < n, k ≠ j`. -/
theorem ppl146_single_bit_detector_prodCount_lower_bound_pure (p n : ℕ) (hn : 2 ^ (8 * p + 5) ≤ n) :
    ∃ j < n, ∀ (start : ℕ) (termRules : Finset (ℕ × Bool)) (binRules : Finset (ℕ × ℕ × ℕ)),
      termRules.card + binRules.card ≤ p →
      (∀ P : ℕ → List Bool → Prop,
        (∀ X a, (X, a) ∈ termRules → P X [a]) →
        (∀ X Y Z u v, (X, Y, Z) ∈ binRules → P Y u → P Z v → P X (u ++ v)) →
        P start (List.replicate j false ++ [true] ++ List.replicate (n - 1 - j) false)) →
      ∃ k < n, k ≠ j ∧
        (∀ P : ℕ → List Bool → Prop,
          (∀ X a, (X, a) ∈ termRules → P X [a]) →
          (∀ X Y Z u v, (X, Y, Z) ∈ binRules → P Y u → P Z v → P X (u ++ v)) →
          P start (List.replicate k false ++ [true] ++ List.replicate (n - 1 - k) false)) := by
  rcases single_bit_detector_prodCount_lower_bound p n hn with ⟨j, hj, h⟩
  refine ⟨j, hj, ?_⟩
  intro start termRules binRules hprods hacc
  let G : CNFGrammar := ⟨start, termRules, binRules⟩
  have hacc' : G.Accepts (singleOne j (n - 1 - j)) :=
    (derives_iff_least_fixpoint G start _).mpr hacc
  rcases h G hprods hacc' with ⟨k, hk, hne, hkacc⟩
  exact ⟨k, hk, hne, (derives_iff_least_fixpoint G start _).mp hkacc⟩

end PureMathlibWrappers

end PPL146

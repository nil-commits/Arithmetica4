import RHDirect.Stage7WeilConjectures

/-!
# RHDirect.Stage8WeilHigherDim

Unconditional (`0` assumptions, `0` `sorry`, `0` custom `axiom`, `0` warnings, `0` info)
formalization of:
1. **Multi-Variable Projective Jacobi Sums `multiJacobiSum χ`** for tuples
   `χ : Fin (n + 2) → MulChar F ℂ` (`∀ i, χ i ≠ 1`, `∏ i, χ i = 1`), the exact
   **Weil–Gauss Product Identity** `multiJacobiSum χ = q⁻¹ * ∏ i, gaussSum (χ i) ψ`,
   **Exact Deligne–Weil Purity** `‖multiJacobiSum χ‖ = q ^ (n / 2)`, and
   **Hasse–Davenport Lifting** over every finite extension `E / F`.
2. **Complete Unconditional Weil Conjectures for Smooth Projective Fermat Hypersurfaces**
   `V_d^n : X_0^d + X_1^d + ... + X_{n+1}^d = 0 ⊂ ℙ^{n+1}(𝔽_q)` of arbitrary dimension `n ≥ 1`
   and degree `d ∣ (q - 1)`:
   - Exact Weil (1949) point-counting formula over `𝔽_q` and over EVERY finite extension `E / 𝔽_q`.
   - Exact middle primitive Betti number formula
     `b_n^{prim}(d) = ((d - 1) / d) * ((d - 1)^{n+1} - (-1)^{n+1})`.
   - **Weil Conjecture I (Rationality)**, **Weil Conjecture II (Functional Equation)**, and
     **Weil Conjecture III (Riemann Hypothesis / Deligne Purity `s.re = n / 2`)**.
   - Explicit specialization to the **Fermat Quartic K3 Surface**
     `X_0^4 + X_1^4 + X_2^4 + X_3^4 = 0` (`b_2^{prim} = 21`, `b_2 = 22`, `χ = 24`,
     `|#S(𝔽_q) - (q² + q + 1)| ≤ 21 q`, `s.re = 1`).
3. **Unconditional Hasse–Weil Bounds & Exact Point Counts for CM Elliptic Curves**:
   - `y² = x³ - x` (CM by `ℤ[i]`): exact Jacobi-sum formula & Hasse bound `|#E(𝔽_q) - (q + 1)| ≤ 2 √q`
     for `q ≡ 1 [MOD 4]`, exact supersingular count `#E(𝔽_q) = q + 1` for `q ≡ 3 [MOD 4]`, and
     combined Hasse bound for all odd `q`.
   - `y² = x³ + 1` (CM by `ℤ[ω]`): exact Jacobi-sum formula & Hasse bound `|#E(𝔽_q) - (q + 1)| ≤ 2 √q`
     for `q ≡ 1 [MOD 6]`, and exact supersingular count `#E(𝔽_q) = q + 1` for `q ≡ 2 [MOD 3]`.
-/

noncomputable section

open Complex Finset
open scoped BigOperators
open RHDirect.Stage7WeilConjectures

namespace RHDirect.Stage8WeilHigherDim

/-! ## Section 1: Multi-Variable Jacobi Sums, Weil–Gauss Product, Purity & Hasse–Davenport -/

section MultiJacobi

variable {F : Type*} [Field F] [Fintype F]

/-- The `(n + 2)`-variable projective Jacobi sum for a tuple of multiplicative characters
`χ : Fin (n + 2) → MulChar F ℂ`:
`multiJacobiSum χ = (q - 1)⁻¹ * ∑_{x : Fin (n + 2) → F, ∑ i, x i = 0} ∏ i, χ i (x i)`. -/
def multiJacobiSum {n : ℕ} (χ : Fin (n + 2) → MulChar F ℂ) : ℂ :=
  letI := Classical.decEq F
  ((Fintype.card F : ℂ) - 1)⁻¹ *
    ∑ x ∈ Finset.univ.filter (fun x : Fin (n + 2) → F => ∑ i, x i = 0), ∏ i, χ i (x i)

/-- Helper: `q - 1 ≠ 0` in `ℂ` for any finite field `F`. -/
theorem card_sub_one_ne_zero_complex (F : Type*) [Field F] [Fintype F] :
    (Fintype.card F : ℂ) - 1 ≠ 0 := by
  have h2 : 2 ≤ Fintype.card F := two_le_card_finiteField (F := F)
  intro h
  have h1 : (Fintype.card F : ℂ) = 1 := sub_eq_zero.mp h
  have hnat : Fintype.card F = 1 := by exact_mod_cast h1
  omega

/-- Helper: the sum of any nontrivial additive character over a finite field vanishes. -/
theorem sum_addChar_eq_zero_of_ne_one {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    ∑ x : F, ψ x = 0 := by
  have hex : ∃ a : F, ψ a ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hψ
    ext x
    exact hall x
  obtain ⟨a, ha⟩ := hex
  have hshift : ψ a * ∑ x : F, ψ x = ∑ x : F, ψ x := by
    rw [Finset.mul_sum]
    have hrew : ∀ x : F, ψ a * ψ x = ψ (a + x) := fun x => (AddChar.map_add_eq_mul ψ a x).symm
    simp_rw [hrew]
    refine Finset.sum_bij (fun x _ => a + x) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
    · intro x₁ _ x₂ _ h; exact add_left_cancel h
    · intro y _; exact ⟨y - a, Finset.mem_univ _, add_sub_cancel a y⟩
  have h0 : (ψ a - 1) * ∑ x : F, ψ x = 0 := by linear_combination hshift
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr ha)

omit [Fintype F] in
/-- Helper: product of `χ i (s * z i)` equals `∏ i, χ i (z i)` when `∏ i, χ i = 1` and `s ≠ 0`. -/
private lemma prod_mulChar_scale {m : ℕ} {χ : Fin m → MulChar F ℂ}
    (hprod : ∏ i, χ i = 1) {s : F} (hs : s ≠ 0) (z : Fin m → F) :
    ∏ i, χ i (s * z i) = ∏ i, χ i (z i) := by
  have hsplit : ∀ i : Fin m, χ i (s * z i) = χ i s * χ i (z i) := fun i => map_mul (χ i) s (z i)
  simp_rw [hsplit, Finset.prod_mul_distrib]
  have h1 : ∏ i : Fin m, χ i s = (∏ i : Fin m, χ i) s := by
    clear hprod hsplit
    suffices ∀ S : Finset (Fin m), ∏ i ∈ S, χ i s = (∏ i ∈ S, χ i) s from this Finset.univ
    intro S
    classical
    induction S using Finset.induction_on with
    | empty => simp [MulChar.one_apply (isUnit_iff_ne_zero.mpr hs)]
    | insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, MulChar.mul_apply, ih]
  rw [h1, hprod, MulChar.one_apply (isUnit_iff_ne_zero.mpr hs), one_mul]

/-- Normalized affine form of the multi-variable Jacobi sum: when `∏ i, χ i = 1`,
`multiJacobiSum χ = ∑_{y : Fin (n + 1) → F, ∑ j, y j = -1} ∏ j, χ j.succ (y j)`. -/
theorem multiJacobiSum_eq_affine_sum {n : ℕ} {χ : Fin (n + 2) → MulChar F ℂ}
    (hprod : ∏ i, χ i = 1) :
    letI := Classical.decEq F
    multiJacobiSum χ =
      ∑ y ∈ Finset.univ.filter (fun y : Fin (n + 1) → F => ∑ j, y j = -1),
        ∏ j : Fin (n + 1), χ j.succ (y j) := by
  classical
  unfold multiJacobiSum
  have hq1 : (Fintype.card F : ℂ) - 1 ≠ 0 := card_sub_one_ne_zero_complex F
  rw [inv_mul_eq_iff_eq_mul₀ hq1]
  set S₀ := Finset.univ.filter (fun x : Fin (n + 2) → F => ∑ i, x i = 0)
  set S₀' := S₀.filter (fun x => x 0 ≠ 0)
  have hdrop : ∑ x ∈ S₀, ∏ i, χ i (x i) = ∑ x ∈ S₀', ∏ i, χ i (x i) := by
    conv_rhs => rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with hx0
    · rfl
    · push Not at hx0
      refine Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (n + 2))) ?_
      rw [hx0, (χ 0).map_nonunit not_isUnit_zero]
  rw [hdrop]
  set A := Finset.univ.filter (fun y : Fin (n + 1) → F => ∑ j, y j = -1)
  have hcardU : ((Finset.univ : Finset Fˣ).card : ℂ) = (Fintype.card F : ℂ) - 1 := by
    rw [Finset.card_univ, Fintype.card_units]
    have h1 : 1 ≤ Fintype.card F := Fintype.card_pos
    rw [Nat.cast_sub h1, Nat.cast_one]
  rw [← hcardU, ← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_product']
  refine Finset.sum_bij (fun x _ => (Units.mk0 (x 0) (by
      have := (Finset.mem_filter.mp ‹_›).2; exact this),
      fun j : Fin (n + 1) => (x 0)⁻¹ * x j.succ)) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx
    rcases hx with ⟨hxS, hx0⟩
    rw [Finset.mem_filter] at hxS
    rw [Finset.mem_product]
    refine ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    have hsum := hxS.2
    rw [Fin.sum_univ_succ] at hsum
    rw [← Finset.mul_sum]
    have htail : ∑ j : Fin (n + 1), x j.succ = -x 0 := eq_neg_of_add_eq_zero_right hsum
    rw [htail, mul_neg, inv_mul_cancel₀ hx0]
  · intro x₁ hx₁ x₂ hx₂ heq
    rw [Finset.mem_filter] at hx₁ hx₂
    simp only [Prod.mk.injEq] at heq
    have hx0eq : x₁ 0 = x₂ 0 := congr_arg Units.val heq.1
    funext i
    cases i using Fin.cases with
    | zero => exact hx0eq
    | succ j =>
      have hj := congr_fun heq.2 j
      rw [hx0eq] at hj
      exact mul_left_cancel₀ (inv_ne_zero hx₂.2) hj
  · intro p hp
    rw [Finset.mem_product, Finset.mem_filter] at hp
    rcases hp with ⟨_, _, hy⟩
    let x : Fin (n + 2) → F := Fin.cons (p.1 : F) (fun j => (p.1 : F) * p.2 j)
    refine ⟨x, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · simp only [x, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ← Finset.mul_sum, hy]
        ring
      · simp [x]
    · ext
      · simp [x]
      · simp only [x, Fin.cons_zero, Fin.cons_succ, inv_mul_cancel_left₀ p.1.ne_zero]
  · intro x hx
    rw [Finset.mem_filter] at hx
    have hx0 : x 0 ≠ 0 := hx.2
    have hscale : x = fun i => x 0 * ((x 0)⁻¹ * x i) := by
      funext i; rw [mul_inv_cancel_left₀ hx0]
    conv_lhs => rw [hscale]
    rw [prod_mulChar_scale hprod hx0 (fun i => (x 0)⁻¹ * x i), Fin.prod_univ_succ,
      inv_mul_cancel₀ hx0, map_one, one_mul]

/-- Complex conjugation of a multi-variable Jacobi sum equals the multi-variable Jacobi sum
of the inverse characters: `starRingEnd ℂ (multiJacobiSum χ) = multiJacobiSum (fun i => (χ i)⁻¹)`. -/
theorem star_multiJacobiSum_eq {n : ℕ} (χ : Fin (n + 2) → MulChar F ℂ) :
    starRingEnd ℂ (multiJacobiSum χ) = multiJacobiSum (fun i => (χ i)⁻¹) := by
  classical
  unfold multiJacobiSum
  simp only [map_mul, map_inv₀, map_sub, map_natCast, map_one, map_sum, map_prod, star_mulChar_apply]

/-- **EXACT WEIL–GAUSS PRODUCT IDENTITY (MULTIPLICATIVE FORM)**:
for ANY `n : ℕ`, any tuple `χ : Fin (n + 2) → MulChar F ℂ` with `∀ i, χ i ≠ 1` and `∏ i, χ i = 1`,
and ANY nontrivial additive character `ψ : AddChar F ℂ`,
`q * multiJacobiSum χ = ∏ i : Fin (n + 2), gaussSum (χ i) ψ`! -/
theorem card_mul_multiJacobiSum_eq_prod_gaussSum {n : ℕ} {χ : Fin (n + 2) → MulChar F ℂ}
    {ψ : AddChar F ℂ} (hχ : ∀ i, χ i ≠ 1) (hprod : ∏ i, χ i = 1) (hψ : ψ ≠ 1) :
    (Fintype.card F : ℂ) * multiJacobiSum χ = ∏ i : Fin (n + 2), gaussSum (χ i) ψ := by
  classical
  set q : ℂ := (Fintype.card F : ℂ)
  have hq1 : q - 1 ≠ 0 := card_sub_one_ne_zero_complex F
  set S : F → ℂ := fun s =>
    ∑ x ∈ Finset.univ.filter (fun x : Fin (n + 2) → F => ∑ i, x i = s), ∏ i, χ i (x i)
  -- Key scaling invariance: `S s = S 1` for every `s ≠ 0`
  have hS_scale : ∀ s : F, s ≠ 0 → S s = S 1 := by
    intro s hs
    unfold S
    refine Finset.sum_bij (fun x _ => fun i => s⁻¹ * x i) ?_ ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← Finset.mul_sum, hx.2, inv_mul_cancel₀ hs]
    · intro x₁ _ x₂ _ h
      funext i
      exact mul_left_cancel₀ (inv_ne_zero hs) (congr_fun h i)
    · intro z hz
      rw [Finset.mem_filter] at hz
      refine ⟨fun i => s * z i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · rw [← Finset.mul_sum, hz.2, mul_one]
      · funext i; rw [inv_mul_cancel_left₀ hs]
    · intro x _
      have hrew : x = fun i => s * (s⁻¹ * x i) := by funext i; rw [mul_inv_cancel_left₀ hs]
      conv_lhs => rw [hrew]
      exact prod_mulChar_scale hprod hs (fun i => s⁻¹ * x i)
  -- Step 1: Total sum over all `x` without `ψ` vanishes (`S 0 + (q - 1) * S 1 = 0`)
  have htot0 : ∑ s : F, S s = 0 := by
    have hfib : ∑ s : F, S s = ∑ x : Fin (n + 2) → F, ∏ i, χ i (x i) :=
      Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
    rw [hfib, ← Fintype.prod_sum]
    refine Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (n + 2))) ?_
    exact MulChar.sum_eq_zero_of_ne_one (hχ 0)
  have hS0_add : S 0 + (q - 1) * S 1 = 0 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F))] at htot0
    have hrest : ∑ s ∈ Finset.univ.erase (0 : F), S s = (q - 1) * S 1 := by
      have hcongr : ∑ s ∈ Finset.univ.erase (0 : F), S s =
          ∑ _s ∈ Finset.univ.erase (0 : F), S 1 :=
        Finset.sum_congr rfl fun s hs => hS_scale s (Finset.mem_erase.mp hs).1
      rw [hcongr, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ (0 : F)),
        Finset.card_univ, nsmul_eq_mul, Nat.cast_sub Fintype.card_pos, Nat.cast_one]
    rw [hrest] at htot0
    exact htot0
  -- Step 2: Expand `∏ i, gaussSum (χ i) ψ` and split by `s = ∑ i, x i`
  have hprod_g : ∏ i : Fin (n + 2), gaussSum (χ i) ψ = S 0 - S 1 := by
    have hψ_sum : ∀ (S_idx : Finset (Fin (n + 2))) (x : Fin (n + 2) → F),
        ∏ i ∈ S_idx, ψ (x i) = ψ (∑ i ∈ S_idx, x i) := by
      intro S_idx x
      induction S_idx using Finset.induction_on with
      | empty => simp [AddChar.map_zero_eq_one]
      | insert a S_idx ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha, AddChar.map_add_eq_mul, ih]
    have hexp : ∏ i : Fin (n + 2), gaussSum (χ i) ψ =
        ∑ x : Fin (n + 2) → F, (∏ i, χ i (x i)) * ψ (∑ i, x i) := by
      simp only [gaussSum]
      rw [Fintype.prod_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.prod_mul_distrib, hψ_sum Finset.univ x]
    rw [hexp, ← Finset.sum_fiberwise_of_maps_to (g := fun x : Fin (n + 2) → F => ∑ i, x i)
      (fun _ _ => Finset.mem_univ _)]
    have hslice : ∀ s : F,
        ∑ x ∈ Finset.univ.filter (fun x : Fin (n + 2) → F => ∑ i, x i = s),
          (∏ i, χ i (x i)) * ψ (∑ i, x i) = S s * ψ s := by
      intro s
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [(Finset.mem_filter.mp hx).2]
    simp_rw [hslice]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F)), AddChar.map_zero_eq_one, mul_one]
    have hrest : ∑ s ∈ Finset.univ.erase (0 : F), S s * ψ s = -S 1 := by
      have hcongr : ∑ s ∈ Finset.univ.erase (0 : F), S s * ψ s =
          S 1 * ∑ s ∈ Finset.univ.erase (0 : F), ψ s := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s hs => by rw [hS_scale s (Finset.mem_erase.mp hs).1]
      have hψ_rest : ∑ s ∈ Finset.univ.erase (0 : F), ψ s = -1 := by
        have h0 := sum_addChar_eq_zero_of_ne_one hψ
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F)), AddChar.map_zero_eq_one] at h0
        exact eq_neg_of_add_eq_zero_right h0
      rw [hcongr, hψ_rest, mul_neg_one]
    rw [hrest, ← sub_eq_add_neg]
  -- Step 3: Combine `S 0 = (q - 1) * multiJacobiSum χ` and `S 1 = -multiJacobiSum χ`
  have hS0 : S 0 = (q - 1) * multiJacobiSum χ := by
    unfold multiJacobiSum
    rw [← mul_assoc, mul_inv_cancel₀ hq1, one_mul]
  have hS1 : S 1 = -multiJacobiSum χ := by
    have hmul : (q - 1) * (S 1 + multiJacobiSum χ) = 0 := by
      linear_combination hS0_add - hS0
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hmul).resolve_left hq1)
  rw [hprod_g, hS0, hS1]
  ring

/-- **EXACT WEIL–GAUSS PRODUCT IDENTITY**:
`multiJacobiSum χ = (Fintype.card F : ℂ)⁻¹ * ∏ i : Fin (n + 2), gaussSum (χ i) ψ`
for every `χ : Fin (n + 2) → MulChar F ℂ` with `∀ i, χ i ≠ 1`, `∏ i, χ i = 1`, and `ψ ≠ 1`. -/
theorem multiJacobiSum_eq_prod_gaussSum {n : ℕ} {χ : Fin (n + 2) → MulChar F ℂ}
    {ψ : AddChar F ℂ} (hχ : ∀ i, χ i ≠ 1) (hprod : ∏ i, χ i = 1) (hψ : ψ ≠ 1) :
    multiJacobiSum χ = ((Fintype.card F : ℂ))⁻¹ * ∏ i : Fin (n + 2), gaussSum (χ i) ψ := by
  have hq : (Fintype.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [← card_mul_multiJacobiSum_eq_prod_gaussSum hχ hprod hψ, inv_mul_cancel_left₀ hq]

/-- **EXACT MULTI-VARIABLE JACOBI-SUM PAIRING PRODUCT**:
`multiJacobiSum χ * multiJacobiSum (fun i => (χ i)⁻¹) = q ^ n`. -/
theorem multiJacobiSum_mul_inv_eq {n : ℕ} {χ : Fin (n + 2) → MulChar F ℂ}
    (hχ : ∀ i, χ i ≠ 1) (hprod : ∏ i, χ i = 1) :
    multiJacobiSum χ * multiJacobiSum (fun i => (χ i)⁻¹) = (Fintype.card F : ℂ) ^ n := by
  obtain ⟨ψ, hψ⟩ := exists_nontrivial_addChar_complex F
  have hχinv : ∀ i, (χ i)⁻¹ ≠ 1 := fun i => inv_ne_one.mpr (hχ i)
  have hprod_inv : ∏ i, (χ i)⁻¹ = 1 := by
    rw [Finset.prod_inv_distrib, hprod, inv_one]
  have h1 := card_mul_multiJacobiSum_eq_prod_gaussSum hχ hprod hψ
  have h2 := card_mul_multiJacobiSum_eq_prod_gaussSum hχinv hprod_inv hψ
  have hq : (Fintype.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hmul : ((Fintype.card F : ℂ) ^ 2) * (multiJacobiSum χ * multiJacobiSum (fun i => (χ i)⁻¹)) =
      (Fintype.card F : ℂ) ^ (n + 2) := by
    calc ((Fintype.card F : ℂ) ^ 2) * (multiJacobiSum χ * multiJacobiSum (fun i => (χ i)⁻¹))
        = ((Fintype.card F : ℂ) * multiJacobiSum χ) *
            ((Fintype.card F : ℂ) * multiJacobiSum (fun i => (χ i)⁻¹)) := by ring
      _ = (∏ i : Fin (n + 2), gaussSum (χ i) ψ) *
            (∏ i : Fin (n + 2), gaussSum (χ i)⁻¹ ψ) := by rw [h1, h2]
      _ = ∏ i : Fin (n + 2), (gaussSum (χ i) ψ * gaussSum (χ i)⁻¹ ψ) := by
            rw [← Finset.prod_mul_distrib]
      _ = ∏ i : Fin (n + 2), (χ i (-1) * (Fintype.card F : ℂ)) := by
            refine Finset.prod_congr rfl fun i _ =>
              gaussSum_mul_gaussSum_inv_finiteField (hχ i) hψ
      _ = (∏ i : Fin (n + 2), χ i (-1)) * (Fintype.card F : ℂ) ^ (n + 2) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = 1 * (Fintype.card F : ℂ) ^ (n + 2) := by
            congr 1
            have heval : ∏ i : Fin (n + 2), χ i (-1) = (∏ i : Fin (n + 2), χ i) (-1) := by
              suffices ∀ S : Finset (Fin (n + 2)), ∏ i ∈ S, χ i (-1) = (∏ i ∈ S, χ i) (-1) from
                this Finset.univ
              intro S
              classical
              induction S using Finset.induction_on with
              | empty =>
                have hneg1 : IsUnit (-1 : F) := isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr one_ne_zero)
                rw [Finset.prod_empty, Finset.prod_empty, MulChar.one_apply hneg1]
              | insert a S ha ih =>
                rw [Finset.prod_insert ha, Finset.prod_insert ha, MulChar.mul_apply, ih]
            rw [heval, hprod,
              MulChar.one_apply (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr (one_ne_zero (α := F))))]
      _ = (Fintype.card F : ℂ) ^ (n + 2) := one_mul _
  have hpow : (Fintype.card F : ℂ) ^ (n + 2) = (Fintype.card F : ℂ) ^ 2 * (Fintype.card F : ℂ) ^ n := by
    rw [← pow_add, add_comm]
  rw [hpow] at hmul
  exact mul_left_cancel₀ (pow_ne_zero 2 hq) hmul

/-- **EXACT SQUARED DELIGNE–WEIL MODULUS**: `‖multiJacobiSum χ‖ ^ 2 = q ^ n`. -/
theorem norm_sq_multiJacobiSum_eq {n : ℕ} {χ : Fin (n + 2) → MulChar F ℂ}
    (hχ : ∀ i, χ i ≠ 1) (hprod : ∏ i, χ i = 1) :
    ‖multiJacobiSum χ‖ ^ 2 = (Fintype.card F : ℝ) ^ n := by
  have hmul := multiJacobiSum_mul_inv_eq hχ hprod
  rw [← star_multiJacobiSum_eq, Complex.mul_conj, Complex.normSq_eq_norm_sq] at hmul
  exact_mod_cast hmul

/-- **EXACT DELIGNE–WEIL PURITY (`‖J‖ = (√q)^n`)**:
`‖multiJacobiSum χ‖ = (Real.sqrt q) ^ n`. -/
theorem norm_multiJacobiSum_eq_sqrt_pow {n : ℕ} {χ : Fin (n + 2) → MulChar F ℂ}
    (hχ : ∀ i, χ i ≠ 1) (hprod : ∏ i, χ i = 1) :
    ‖multiJacobiSum χ‖ = (Real.sqrt (Fintype.card F : ℝ)) ^ n := by
  have hsq : ‖multiJacobiSum χ‖ ^ 2 = ((Real.sqrt (Fintype.card F : ℝ)) ^ n) ^ 2 := by
    rw [norm_sq_multiJacobiSum_eq hχ hprod, ← pow_mul, mul_comm n 2, pow_mul,
      Real.sq_sqrt (Nat.cast_nonneg _)]
  have hnn1 : 0 ≤ ‖multiJacobiSum χ‖ := norm_nonneg _
  have hnn2 : 0 ≤ (Real.sqrt (Fintype.card F : ℝ)) ^ n := pow_nonneg (Real.sqrt_nonneg _) n
  nlinarith

/-- **EXACT DELIGNE–WEIL PURITY (`‖J‖ = q^{n/2}`)**:
`‖multiJacobiSum χ‖ = (Fintype.card F : ℝ) ^ ((n : ℝ) / 2)` for every `n : ℕ` and every
nontrivial tuple `χ : Fin (n + 2) → MulChar F ℂ` with `∏ i, χ i = 1`. -/
theorem norm_multiJacobiSum_eq_rpow {n : ℕ} {χ : Fin (n + 2) → MulChar F ℂ}
    (hχ : ∀ i, χ i ≠ 1) (hprod : ∏ i, χ i = 1) :
    ‖multiJacobiSum χ‖ = (Fintype.card F : ℝ) ^ ((n : ℝ) / 2) := by
  rw [norm_multiJacobiSum_eq_sqrt_pow hχ hprod, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast ((Fintype.card F : ℝ) ^ (1 / 2 : ℝ)) n,
    ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  ring

/-- **HASSE–DAVENPORT LIFTING FOR MULTI-VARIABLE JACOBI SUMS**:
for ANY finite field extension `E / F` of degree `r = Module.finrank F E`, and any
`χ : Fin (n + 2) → MulChar F ℂ` with `∀ i, χ i ≠ 1` and `∏ i, χ i = 1`,
`(-1)^n * multiJacobiSum (liftMulChar E ∘ χ) = ((-1)^n * multiJacobiSum χ) ^ Module.finrank F E`! -/
theorem hasse_davenport_multiJacobiSum {E : Type*} [DecidableEq F]
    [Field E] [Fintype E] [DecidableEq E] [Algebra F E]
    {n : ℕ} {χ : Fin (n + 2) → MulChar F ℂ}
    (hχ : ∀ i, χ i ≠ 1) (hprod : ∏ i, χ i = 1) :
    (-1 : ℂ) ^ n * multiJacobiSum (fun i => liftMulChar E (χ i)) =
      ((-1 : ℂ) ^ n * multiJacobiSum χ) ^ Module.finrank F E := by
  obtain ⟨ψ, hψ⟩ := exists_nontrivial_addChar_complex F
  have hψE : liftAddChar E ψ ≠ 1 := liftAddChar_ne_one hψ
  have hχE : ∀ i, liftMulChar E (χ i) ≠ 1 := fun i => liftMulChar_ne_one (hχ i)
  have hprodE : ∏ i : Fin (n + 2), liftMulChar E (χ i) = 1 := by
    have hlift_prod : ∀ S : Finset (Fin (n + 2)),
        ∏ i ∈ S, liftMulChar E (χ i) = liftMulChar E (∏ i ∈ S, χ i) := by
      intro S
      classical
      induction S using Finset.induction_on with
      | empty => simp [liftMulChar_one]
      | insert a S ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha, liftMulChar_mul, ih]
    rw [hlift_prod Finset.univ, hprod, liftMulChar_one]
  set r := Module.finrank F E
  have hcardE : Fintype.card E = Fintype.card F ^ r := Module.card_eq_pow_finrank
  have hq : (Fintype.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hqr : (Fintype.card F : ℂ) ^ r ≠ 0 := pow_ne_zero r hq
  have hE := card_mul_multiJacobiSum_eq_prod_gaussSum hχE hprodE hψE
  have hF := card_mul_multiJacobiSum_eq_prod_gaussSum hχ hprod hψ
  have hhd_i : ∀ i : Fin (n + 2),
      gaussSum (liftMulChar E (χ i)) (liftAddChar E ψ) = -(-gaussSum (χ i) ψ) ^ r := by
    intro i
    have h := hasse_davenport_gaussSum (E := E) (hχ i) ψ
    linear_combination -h
  have hprod_hd : ∏ i : Fin (n + 2), gaussSum (liftMulChar E (χ i)) (liftAddChar E ψ) =
      (-1 : ℂ) ^ n * (((-1 : ℂ) ^ n * ∏ i : Fin (n + 2), gaussSum (χ i) ψ) ^ r) := by
    simp_rw [hhd_i]
    have hrew1 : ∀ i : Fin (n + 2), -(-gaussSum (χ i) ψ) ^ r = (-1 : ℂ) * (-gaussSum (χ i) ψ) ^ r :=
      fun _ => by ring
    have hrew2 : ∀ i : Fin (n + 2), -gaussSum (χ i) ψ = (-1 : ℂ) * gaussSum (χ i) ψ :=
      fun _ => by ring
    rw [Finset.prod_congr rfl fun i _ => hrew1 i, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Finset.prod_pow]
    rw [Finset.prod_congr rfl fun i _ => hrew2 i, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    have hsign : (-1 : ℂ) ^ (n + 2) = (-1 : ℂ) ^ n := by rw [pow_add]; norm_num
    rw [hsign]
  rw [hcardE, Nat.cast_pow, hprod_hd, ← hF] at hE
  have hmul : (Fintype.card F : ℂ) ^ r * ((-1 : ℂ) ^ n * multiJacobiSum (fun i => liftMulChar E (χ i))) =
      (Fintype.card F : ℂ) ^ r * ((-1 : ℂ) ^ n * multiJacobiSum χ) ^ r := by
    have hsign2 : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
      rw [← mul_pow]; norm_num
    have hinner : (-1 : ℂ) ^ n * ((Fintype.card F : ℂ) * multiJacobiSum χ) =
        (Fintype.card F : ℂ) * ((-1 : ℂ) ^ n * multiJacobiSum χ) := by ring
    calc (Fintype.card F : ℂ) ^ r * ((-1 : ℂ) ^ n * multiJacobiSum (fun i => liftMulChar E (χ i)))
        = (-1 : ℂ) ^ n * ((Fintype.card F : ℂ) ^ r * multiJacobiSum (fun i => liftMulChar E (χ i))) := by ring
      _ = (-1 : ℂ) ^ n * ((-1 : ℂ) ^ n * (((-1 : ℂ) ^ n * ((Fintype.card F : ℂ) * multiJacobiSum χ)) ^ r)) := by
            rw [hE]
      _ = ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) *
            ((Fintype.card F : ℂ) * ((-1 : ℂ) ^ n * multiJacobiSum χ)) ^ r := by
            rw [← mul_assoc, hinner]
      _ = 1 * ((Fintype.card F : ℂ) ^ r * ((-1 : ℂ) ^ n * multiJacobiSum χ) ^ r) := by
            rw [hsign2, mul_pow]
      _ = (Fintype.card F : ℂ) ^ r * ((-1 : ℂ) ^ n * multiJacobiSum χ) ^ r := one_mul _
  exact mul_left_cancel₀ hqr hmul

end MultiJacobi

/-! ## Section 2: Point Counting, Middle Betti Numbers & Complete Weil Conjectures for `V_d^n` -/

section FermatHypersurface

/-- Canonical projective representatives in `ℙ^{m-1}(F)`: tuples `x : Fin m → F` whose first
nonzero coordinate is `1`. Every nonzero `y : Fin m → F` is uniquely `λ • x` with `λ ∈ Fˣ`
and `x ∈ canonProjSet F m`. -/
def canonProjSet (F : Type*) [Field F] [Fintype F] [DecidableEq F] (m : ℕ) :
    Finset (Fin m → F) :=
  Finset.univ.filter fun x : Fin m → F => ∃ i : Fin m, x i = 1 ∧ ∀ j : Fin m, j < i → x j = 0

/-- Number of affine solutions `x : Fin (n + 2) → F` to `∑ i, x i ^ d = 0`. -/
def fermatAffineSolutions (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n d : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin (n + 2) → F => ∑ i, x i ^ d = 0).card

/-- Exact number of projective `F`-rational points on the smooth projective Fermat hypersurface
`V_d^n : X_0^d + X_1^d + ... + X_{n+1}^d = 0` in `ℙ^{n+1}(F)`. -/
def fermatHypersurfacePoints (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n d : ℕ) : ℕ :=
  ((canonProjSet F (n + 2)).filter fun x => ∑ i, x i ^ d = 0).card

/-- Every nonzero tuple `y : Fin m → F` has a least index `i` with `y i ≠ 0`. -/
private lemma exists_least_ne_zero {F : Type*} [Field F] {m : ℕ}
    {y : Fin m → F} (hy : y ≠ 0) :
    ∃ i : Fin m, y i ≠ 0 ∧ ∀ j : Fin m, j < i → y j = 0 := by
  classical
  have hex : ∃ k : ℕ, ∃ h : k < m, y ⟨k, h⟩ ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hy
    funext i
    exact hall i.1 i.2
  let k₀ := Nat.find hex
  have hk₀ := Nat.find_spec hex
  obtain ⟨hlt, hne⟩ := hk₀
  refine ⟨⟨k₀, hlt⟩, hne, fun j hj => ?_⟩
  by_contra hjne
  have hle : k₀ ≤ j.1 := Nat.find_min' hex ⟨j.2, hjne⟩
  exact absurd hj (not_lt.mpr hle)

/-- Exact relation between affine solutions and projective points on `V_d^n`:
`fermatAffineSolutions F n d = (q - 1) * fermatHypersurfacePoints F n d + 1` for `1 ≤ d`. -/
theorem fermatAffineSolutions_eq_mul_proj_add_one {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (n : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    fermatAffineSolutions F n d =
      (Fintype.card F - 1) * fermatHypersurfacePoints F n d + 1 := by
  classical
  set S_aff := Finset.univ.filter (fun x : Fin (n + 2) → F => ∑ i, x i ^ d = 0)
  set S_proj := (canonProjSet F (n + 2)).filter (fun x => ∑ i, x i ^ d = 0)
  have h0_mem : (0 : Fin (n + 2) → F) ∈ S_aff := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simp [zero_pow (by omega : d ≠ 0)]
  have hsplit : S_aff.card = (S_aff.erase 0).card + 1 := (Finset.card_erase_add_one h0_mem).symm
  rw [fermatAffineSolutions, hsplit]
  congr 1
  unfold fermatHypersurfacePoints
  rw [← Fintype.card_units F, ← Finset.card_univ (α := Fˣ), ← Finset.card_product]
  refine Finset.card_bij (fun (p : Fˣ × (Fin (n + 2) → F)) _ => fun i => (p.1 : F) * p.2 i)
    ?_ ?_ ?_ |>.symm
  · intro p hp
    rw [Finset.mem_product] at hp
    rcases hp with ⟨_, hp2⟩
    rw [Finset.mem_filter, canonProjSet, Finset.mem_filter] at hp2
    rcases hp2 with ⟨⟨_, ⟨i₀, hi₀1, _⟩⟩, hsum⟩
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    · intro h0
      have hval := congr_fun h0 i₀
      simp only [hi₀1, mul_one, Pi.zero_apply] at hval
      exact p.1.ne_zero hval
    · simp_rw [mul_pow, ← Finset.mul_sum, hsum, mul_zero]
  · intro p₁ hp₁ p₂ hp₂ heq
    rw [Finset.mem_product] at hp₁ hp₂
    have hp₁' := (Finset.mem_filter.mp hp₁.2).1
    have hp₂' := (Finset.mem_filter.mp hp₂.2).1
    rw [canonProjSet, Finset.mem_filter] at hp₁' hp₂'
    obtain ⟨i₁, hi₁1, hi₁0⟩ := hp₁'.2
    obtain ⟨i₂, hi₂1, hi₂0⟩ := hp₂'.2
    have hi_eq : i₁ = i₂ := by
      rcases lt_trichotomy i₁ i₂ with hlt | he | hgt
      · have hval := congr_fun heq i₁
        rw [hi₁1, mul_one, hi₂0 i₁ hlt, mul_zero] at hval
        exact absurd hval p₁.1.ne_zero
      · exact he
      · have hval := congr_fun heq i₂
        rw [hi₂1, mul_one, hi₁0 i₂ hgt, mul_zero] at hval
        exact absurd hval.symm p₂.1.ne_zero
    subst hi_eq
    have hu : p₁.1 = p₂.1 := by
      apply Units.ext
      have hval := congr_fun heq i₁
      simpa [hi₁1, hi₂1] using hval
    refine Prod.ext hu ?_
    funext i
    have hval := congr_fun heq i
    rw [hu] at hval
    exact mul_left_cancel₀ p₂.1.ne_zero hval
  · intro y hy
    rw [Finset.mem_erase, Finset.mem_filter] at hy
    rcases hy with ⟨hy0, _, hsum⟩
    obtain ⟨i₀, hi₀ne, hi₀0⟩ := exists_least_ne_zero hy0
    let u : Fˣ := Units.mk0 (y i₀) hi₀ne
    let x : Fin (n + 2) → F := fun i => (u : F)⁻¹ * y i
    refine ⟨(u, x), ?_, ?_⟩
    · refine Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨i₀, ?_, ?_⟩⟩
        · simp [x, u, inv_mul_cancel₀ hi₀ne]
        · intro j hj; simp [x, hi₀0 j hj]
      · simp only [x, mul_pow, ← Finset.mul_sum, hsum, mul_zero]
    · funext i
      simp only [x, mul_inv_cancel_left₀ u.ne_zero]

/-- The finite set of primitive Fermat character tuples in dimension `n` and degree `d`:
`primitiveFermatTuples F n d = {χ : Fin (n + 2) → powCharSet F d | (∀ i, χ i ≠ 1) ∧ ∏ i, χ i = 1}`. -/
def primitiveFermatTuples (F : Type*) [Field F] [Fintype F] (n d : ℕ) :
    Finset (Fin (n + 2) → MulChar F ℂ) :=
  letI := Classical.decEq (MulChar F ℂ)
  (Fintype.piFinset (fun _ : Fin (n + 2) => powCharSet F d)).filter fun χ =>
    (∀ i, χ i ≠ 1) ∧ ∏ i, χ i = 1

theorem mem_primitiveFermatTuples {F : Type*} [Field F] [Fintype F] {n d : ℕ}
    {χ : Fin (n + 2) → MulChar F ℂ} :
    χ ∈ primitiveFermatTuples F n d ↔
      (∀ i, χ i ∈ powCharSet F d) ∧ (∀ i, χ i ≠ 1) ∧ ∏ i, χ i = 1 := by
  classical
  simp [primitiveFermatTuples, Fintype.mem_piFinset]

/-- The Frobenius eigenvalue `α(χ) = (-1)^n * multiJacobiSum χ` associated to a primitive
character tuple `χ ∈ primitiveFermatTuples F n d`. -/
def fermatHypersurfaceEigenvalue {F : Type*} [Field F] [Fintype F] {n : ℕ}
    (χ : Fin (n + 2) → MulChar F ℂ) : ℂ :=
  (-1 : ℂ) ^ n * multiJacobiSum χ

/-- Extended character evaluation: `extChar χ u = 1` if `χ = 1`, else `χ u`.
This uniformly gives `#{x : F | x ^ d = u} = ∑ χ ∈ powCharSet F d, extChar χ u` for ALL `u : F`. -/
private def extChar {F : Type*} [Field F] [Fintype F] (χ : MulChar F ℂ) (u : F) : ℂ :=
  letI := Classical.decEq (MulChar F ℂ)
  if χ = 1 then 1 else χ u

private lemma card_pow_eq_sum_extChar {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {d : ℕ} (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1) (u : F) :
    ((Finset.univ.filter fun x : F => x ^ d = u).card : ℂ) =
      ∑ χ ∈ powCharSet F d, extChar χ u := by
  classical
  rw [card_pow_eq_sum_powCharSet_all hd hdvd u]
  have h1 : (1 : MulChar F ℂ) ∈ powCharSet F d := one_mem_powCharSet F d
  rw [← Finset.add_sum_erase _ _ h1, ← Finset.add_sum_erase _ (fun χ => extChar χ u) h1]
  have hrest : ∑ χ ∈ (powCharSet F d).erase 1, extChar χ u =
      ∑ χ ∈ (powCharSet F d).erase 1, χ u :=
    Finset.sum_congr rfl fun χ hχ => by simp [extChar, (Finset.mem_erase.mp hχ).1]
  rw [hrest]
  have hex1 : extChar (1 : MulChar F ℂ) u = 1 := by simp [extChar]
  rw [hex1]
  by_cases hu : u = 0
  · subst hu
    rw [if_pos rfl, (1 : MulChar F ℂ).map_nonunit not_isUnit_zero, zero_add]
  · rw [if_neg hu, zero_add, MulChar.one_apply (isUnit_iff_ne_zero.mpr hu)]

/-- **EXACT WEIL (1949) POINT-COUNTING FORMULA FOR `n`-DIMENSIONAL FERMAT HYPERSURFACES**:
for every `n : ℕ`, `1 ≤ d`, and `d ∣ (q - 1)`:
`#V_d^n(𝔽_q) = ∑_{k=0}^n q^k + (-1)^n * ∑_{χ ∈ primitiveFermatTuples F n d} α(χ)`. -/
theorem fermatHypersurfacePoints_eq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (n : ℕ) {d : ℕ} (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1) :
    (fermatHypersurfacePoints F n d : ℂ) =
      ∑ k ∈ Finset.range (n + 1), (Fintype.card F : ℂ) ^ k +
        (-1 : ℂ) ^ n * ∑ χ ∈ primitiveFermatTuples F n d, fermatHypersurfaceEigenvalue χ := by
  classical
  set q : ℂ := (Fintype.card F : ℂ)
  have hq1 : q - 1 ≠ 0 := card_sub_one_ne_zero_complex F
  -- Step 1: Express `fermatAffineSolutions` as a character-tuple sum over `χ : Fin (n+2) → D`
  set U0 := Finset.univ.filter (fun u : Fin (n + 2) → F => ∑ i, u i = 0)
  have haff_fib : (fermatAffineSolutions F n d : ℂ) =
      ∑ u ∈ U0, ∏ i : Fin (n + 2), ((Finset.univ.filter fun x : F => x ^ d = u i).card : ℂ) := by
    unfold fermatAffineSolutions
    have hcard :
        (Finset.univ.filter fun x : Fin (n + 2) → F => ∑ i, x i ^ d = 0).card =
          ∑ u ∈ U0, (Finset.univ.filter fun x : Fin (n + 2) → F => ∀ i, x i ^ d = u i).card := by
      have hmaps : ∀ x ∈ Finset.univ.filter (fun x : Fin (n + 2) → F => ∑ i, x i ^ d = 0),
          (fun i => x i ^ d) ∈ U0 := by
        intro x hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
      rw [Finset.card_eq_sum_card_fiberwise hmaps]
      refine Finset.sum_congr rfl fun u hu => ?_
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, hfun⟩ i; exact congr_fun hfun i
      · intro hall
        have hfun : (fun i => x i ^ d) = u := funext hall
        refine ⟨?_, hfun⟩
        rw [hfun]
        exact (Finset.mem_filter.mp hu).2
    rw [hcard, Nat.cast_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hpi : (Finset.univ.filter fun x : Fin (n + 2) → F => ∀ i, x i ^ d = u i) =
        Fintype.piFinset (fun i : Fin (n + 2) => Finset.univ.filter fun t : F => t ^ d = u i) := by
      ext x
      simp [Fintype.mem_piFinset]
    rw [hpi, Fintype.card_piFinset, Nat.cast_prod]
  simp_rw [card_pow_eq_sum_extChar hd hdvd] at haff_fib
  have hswap : (fermatAffineSolutions F n d : ℂ) =
      ∑ χ ∈ Fintype.piFinset (fun _ : Fin (n + 2) => powCharSet F d),
        ∑ u ∈ U0, ∏ i : Fin (n + 2), extChar (χ i) (u i) := by
    rw [haff_fib]
    have hexp : ∀ u : Fin (n + 2) → F,
        ∏ i : Fin (n + 2), ∑ c ∈ powCharSet F d, extChar c (u i) =
          ∑ χ ∈ Fintype.piFinset (fun _ : Fin (n + 2) => powCharSet F d),
            ∏ i : Fin (n + 2), extChar (χ i) (u i) := by
      intro u
      have h1 : ∏ i : Fin (n + 2), ∑ c ∈ powCharSet F d, extChar c (u i) =
          ∏ i : Fin (n + 2), ∑ c : {x // x ∈ powCharSet F d}, extChar c.1 (u i) :=
        Finset.prod_congr rfl fun i _ => (Finset.sum_coe_sort (powCharSet F d) (fun c => extChar c (u i))).symm
      rw [h1, Fintype.prod_sum]
      refine Finset.sum_bij (fun f _ => fun i => (f i).1) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro f _; exact Fintype.mem_piFinset.mpr fun i => (f i).2
      · intro f₁ _ f₂ _ h; funext i; exact Subtype.ext (congr_fun h i)
      · intro χ hχ
        exact ⟨fun i => ⟨χ i, Fintype.mem_piFinset.mp hχ i⟩, Finset.mem_univ _, rfl⟩
    simp_rw [hexp]
    rw [Finset.sum_comm]
  -- Step 2: Evaluate the inner sum `I(χ) = ∑_{u ∈ U0} ∏_i extChar (χ i) (u i)`
  set P := Fintype.piFinset (fun _ : Fin (n + 2) => powCharSet F d)
  set χone : Fin (n + 2) → MulChar F ℂ := fun _ => 1
  have hχone_mem : χone ∈ P := by
    rw [Fintype.mem_piFinset]
    intro _; exact one_mem_powCharSet F d
  -- Case 1: `χ = χone` gives `|U0| = q^{n+1}`
  have hI_one : ∑ u ∈ U0, ∏ i : Fin (n + 2), extChar (χone i) (u i) = q ^ (n + 1) := by
    have h1 : ∀ u ∈ U0, ∏ i : Fin (n + 2), extChar (χone i) (u i) = 1 := by
      intro _ _; simp [χone, extChar]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcardU0 : U0.card = Fintype.card F ^ (n + 1) := by
      have hbij : U0.card = Fintype.card (Fin (n + 1) → F) := by
        refine Finset.card_bij (fun u _ => fun j : Fin (n + 1) => u j.succ) ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro u₁ hu₁ u₂ hu₂ h
          have hs₁ := (Finset.mem_filter.mp hu₁).2
          have hs₂ := (Finset.mem_filter.mp hu₂).2
          rw [Fin.sum_univ_succ] at hs₁ hs₂
          funext i
          cases i using Fin.cases with
          | zero =>
            have htail : ∑ j : Fin (n + 1), u₁ j.succ = ∑ j : Fin (n + 1), u₂ j.succ :=
              Finset.sum_congr rfl fun j _ => congr_fun h j
            rw [htail] at hs₁
            linear_combination hs₁ - hs₂
          | succ j => exact congr_fun h j
        · intro v _
          let u : Fin (n + 2) → F := Fin.cons (-∑ j, v j) v
          refine ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · simp [u, Fin.sum_univ_succ]
          · funext j; rfl
      rw [hbij, Fintype.card_fun, Fintype.card_fin]
    rw [hcardU0, Nat.cast_pow]
  -- Case 2: `χ ≠ χone` and `χ ∉ primitiveFermatTuples F n d` gives `0`
  have hI_zero : ∀ χ ∈ P, χ ≠ χone → χ ∉ primitiveFermatTuples F n d →
      ∑ u ∈ U0, ∏ i : Fin (n + 2), extChar (χ i) (u i) = 0 := by
    intro χ hχP hne1 hnotprim
    by_cases hall_ne : ∀ i, χ i ≠ 1
    · -- All `χ i ≠ 1`, so `∏ i, χ i ≠ 1`
      have hprod_ne : ∏ i, χ i ≠ 1 := by
        intro hp1
        apply hnotprim
        exact mem_primitiveFermatTuples.mpr ⟨Fintype.mem_piFinset.mp hχP, hall_ne, hp1⟩
      have hext : ∀ u ∈ U0, ∏ i : Fin (n + 2), extChar (χ i) (u i) = ∏ i, χ i (u i) := by
        intro u _
        refine Finset.prod_congr rfl fun i _ => by simp [extChar, hall_ne i]
      rw [Finset.sum_congr rfl hext]
      obtain ⟨u₀, hu₀⟩ : ∃ u₀ : Fˣ, (∏ i, χ i) (u₀ : F) ≠ 1 := by
        by_contra hall
        push Not at hall
        apply hprod_ne
        ext x
        rw [MulChar.one_apply x.isUnit]
        exact hall x
      have hscale : (∏ i, χ i) (u₀ : F) * ∑ u ∈ U0, ∏ i, χ i (u i) = ∑ u ∈ U0, ∏ i, χ i (u i) := by
        rw [Finset.mul_sum]
        have heval : (∏ i : Fin (n + 2), χ i) (u₀ : F) = ∏ i : Fin (n + 2), χ i (u₀ : F) := by
          suffices ∀ S : Finset (Fin (n + 2)), (∏ i ∈ S, χ i) (u₀ : F) = ∏ i ∈ S, χ i (u₀ : F) from
            this Finset.univ
          intro S
          induction S using Finset.induction_on with
          | empty => simp [MulChar.one_apply u₀.isUnit]
          | insert a S ha ih =>
            rw [Finset.prod_insert ha, Finset.prod_insert ha, MulChar.mul_apply, ih]
        rw [heval]
        refine Finset.sum_bij (fun u _ => fun i => (u₀ : F) * u i) ?_ ?_ ?_ ?_
        · intro u hu
          rw [Finset.mem_filter] at hu ⊢
          exact ⟨Finset.mem_univ _, by rw [← Finset.mul_sum, hu.2, mul_zero]⟩
        · intro u₁ _ u₂ _ h
          funext i; exact mul_left_cancel₀ u₀.ne_zero (congr_fun h i)
        · intro v hv
          rw [Finset.mem_filter] at hv
          refine ⟨fun i => (u₀ : F)⁻¹ * v i,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [← Finset.mul_sum, hv.2, mul_zero]⟩,
            by funext i; rw [mul_inv_cancel_left₀ u₀.ne_zero]⟩
        · intro u _
          rw [← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl fun i _ => (map_mul (χ i) (u₀ : F) (u i)).symm
      have h0 : ((∏ i, χ i) (u₀ : F) - 1) * ∑ u ∈ U0, ∏ i, χ i (u i) = 0 := by
        linear_combination hscale
      exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hu₀)
    · -- Some `i₀` has `χ i₀ = 1`, and since `χ ≠ χone`, some `j₀` has `χ j₀ ≠ 1`
      push Not at hall_ne
      obtain ⟨i₀, hi₀⟩ := hall_ne
      have hj_ex : ∃ j₀ : Fin (n + 2), χ j₀ ≠ 1 := by
        by_contra hall1
        push Not at hall1
        exact hne1 (funext hall1)
      obtain ⟨j₀, hj₀⟩ := hj_ex
      have hjne : j₀ ≠ i₀ := fun h => hj₀ (h ▸ hi₀)
      -- Biject `U0` with functions on `{k : Fin (n+2) // k ≠ i₀}` by dropping coordinate `i₀`
      set Rest := (Finset.univ : Finset (Fin (n + 2))).erase i₀
      have hbij : ∑ u ∈ U0, ∏ i : Fin (n + 2), extChar (χ i) (u i) =
          ∑ v : {k : Fin (n + 2) // k ≠ i₀} → F,
            ∏ k : {k : Fin (n + 2) // k ≠ i₀}, extChar (χ k.1) (v k) := by
        refine Finset.sum_bij (fun u _ => fun k => u k.1) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
        · intro u₁ hu₁ u₂ hu₂ h
          have hs₁ := (Finset.mem_filter.mp hu₁).2
          have hs₂ := (Finset.mem_filter.mp hu₂).2
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)] at hs₁ hs₂
          have hrest_eq : ∑ k ∈ Rest, u₁ k = ∑ k ∈ Rest, u₂ k :=
            Finset.sum_congr rfl fun k hk => congr_fun h ⟨k, (Finset.mem_erase.mp hk).1⟩
          funext i
          by_cases hi : i = i₀
          · subst hi; rw [hrest_eq] at hs₁; linear_combination hs₁ - hs₂
          · exact congr_fun h ⟨i, hi⟩
        · intro v _
          let u : Fin (n + 2) → F := fun i =>
            if h : i = i₀ then -(∑ k : {k : Fin (n + 2) // k ≠ i₀}, v k) else v ⟨i, h⟩
          refine ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
            have hu0 : u i₀ = -(∑ k : {k : Fin (n + 2) // k ≠ i₀}, v k) := by simp [u]
            have hsum_rest : ∑ k ∈ Rest, u k = ∑ k : {k : Fin (n + 2) // k ≠ i₀}, v k := by
              refine Finset.sum_bij (fun k hk => ⟨k, (Finset.mem_erase.mp hk).1⟩)
                (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
              · intro k₁ _ k₂ _ h; exact congr_arg Subtype.val h
              · intro k _; exact ⟨k.1, Finset.mem_erase.mpr ⟨k.2, Finset.mem_univ _⟩, rfl⟩
              · intro k hk; simp [u, (Finset.mem_erase.mp hk).1]
            rw [hu0, hsum_rest, neg_add_cancel]
          · funext k; simp [u, k.2]
        · intro u _
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)]
          have hi₀1 : extChar (χ i₀) (u i₀) = 1 := by simp [extChar, hi₀]
          rw [hi₀1, one_mul]
          refine Finset.prod_bij (fun k hk => ⟨k, (Finset.mem_erase.mp hk).1⟩)
            (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
          · intro k₁ _ k₂ _ h; exact congr_arg Subtype.val h
          · intro k _; exact ⟨k.1, Finset.mem_erase.mpr ⟨k.2, Finset.mem_univ _⟩, rfl⟩
      rw [hbij, ← Fintype.prod_sum]
      refine Finset.prod_eq_zero (Finset.mem_univ ⟨j₀, hjne⟩) ?_
      have hextj : ∀ t : F, extChar (χ j₀) t = χ j₀ t := fun t => by simp [extChar, hj₀]
      simp_rw [hextj]
      exact MulChar.sum_eq_zero_of_ne_one hj₀
  -- Step 3: Split the sum over `P` into `{χone}`, `primitiveFermatTuples`, and the zero remainder
  have hprim_sub : primitiveFermatTuples F n d ⊆ P.erase χone := by
    intro χ hχ
    rw [mem_primitiveFermatTuples] at hχ
    refine Finset.mem_erase.mpr ⟨?_, Fintype.mem_piFinset.mpr hχ.1⟩
    intro heq
    exact hχ.2.1 0 (congr_fun heq 0)
  have haff_eval : (fermatAffineSolutions F n d : ℂ) =
      q ^ (n + 1) + (q - 1) * ∑ χ ∈ primitiveFermatTuples F n d, multiJacobiSum χ := by
    rw [hswap, ← Finset.add_sum_erase _ _ hχone_mem, hI_one]
    congr 1
    rw [← Finset.sum_subset hprim_sub]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun χ hχ => ?_
      rw [mem_primitiveFermatTuples] at hχ
      have hext : ∀ u ∈ U0, ∏ i : Fin (n + 2), extChar (χ i) (u i) = ∏ i, χ i (u i) :=
        fun u _ => Finset.prod_congr rfl fun i _ => by simp [extChar, hχ.2.1 i]
      rw [Finset.sum_congr rfl hext]
      unfold multiJacobiSum
      rw [← mul_assoc, mul_inv_cancel₀ hq1, one_mul]
      exact Finset.sum_congr (by ext x; simp [U0]) fun _ _ => rfl
    · intro χ hχ hnot
      rw [Finset.mem_erase] at hχ
      exact hI_zero χ hχ.2 hχ.1 hnot
  -- Step 4: Divide `(fermatAffineSolutions - 1)` by `(q - 1)`
  have hproj_rel : (fermatAffineSolutions F n d : ℂ) =
      (q - 1) * (fermatHypersurfacePoints F n d : ℂ) + 1 := by
    have hnat := fermatAffineSolutions_eq_mul_proj_add_one (F := F) n hd
    have h1 : 1 ≤ Fintype.card F := Fintype.card_pos
    have hcast := congr_arg (Nat.cast : ℕ → ℂ) hnat
    push_cast [Nat.cast_sub h1] at hcast
    exact hcast
  have hgeom : (q - 1) * ∑ k ∈ Finset.range (n + 1), q ^ k = q ^ (n + 1) - 1 := by
    simpa [mul_comm] using geom_sum_mul q (n + 1)
  have hsign : (-1 : ℂ) ^ n * ∑ χ ∈ primitiveFermatTuples F n d, fermatHypersurfaceEigenvalue χ =
      ∑ χ ∈ primitiveFermatTuples F n d, multiJacobiSum χ := by
    unfold fermatHypersurfaceEigenvalue
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [← mul_assoc, ← mul_pow]
    norm_num
  rw [hsign]
  apply mul_left_cancel₀ hq1
  rw [mul_add, hgeom]
  linear_combination haff_eval - hproj_rel

/-! ### Exact Middle Betti Number Formula `card_primitiveFermatTuples` -/

/-- Helper: count tuples `χ : Fin m → D` with `∀ i, χ i ≠ 1` and `∏ i, χ i = 1`, where
`D = powCharSet F d`. -/
private def primTupleSet (F : Type*) [Field F] [Fintype F] (m d : ℕ) :
    Finset (Fin m → MulChar F ℂ) :=
  letI := Classical.decEq (MulChar F ℂ)
  (Fintype.piFinset (fun _ : Fin m => powCharSet F d)).filter fun χ =>
    (∀ i, χ i ≠ 1) ∧ ∏ i, χ i = 1

/-- Key one-step recurrence: `|primTupleSet m d| + |primTupleSet (m + 1) d| = (d - 1)^m`
for `1 ≤ m`, `1 ≤ d`, `d ∣ q - 1`. -/
private lemma card_primTupleSet_add_succ {F : Type*} [Field F] [Fintype F]
    {m d : ℕ} (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1) :
    (primTupleSet F m d).card + (primTupleSet F (m + 1) d).card = (d - 1) ^ m := by
  classical
  set D' := (powCharSet F d).erase 1
  have hD' : D'.card = d - 1 := by
    rw [Finset.card_erase_of_mem (one_mem_powCharSet F d), card_powCharSet hd hdvd]
  set All := Fintype.piFinset (fun _ : Fin m => D')
  have hAll_card : All.card = (d - 1) ^ m := by
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hD']
  rw [← hAll_card]
  have hpart := Finset.card_filter_add_card_filter_not (s := All)
    (p := fun χ : Fin m → MulChar F ℂ => ∏ i, χ i = 1)
  rw [← hpart]
  congr 1
  · congr 1
    ext χ
    simp only [primTupleSet, All, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_erase, D']
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨fun i => ⟨h2 i, h1 i⟩, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨fun i => (h1 i).2, fun i => (h1 i).1, h3⟩
  · refine Finset.card_bij (fun χ _ => fun i : Fin m => χ i.castSucc) ?_ ?_ ?_
    · intro χ hχ
      simp only [primTupleSet, Finset.mem_filter, Fintype.mem_piFinset] at hχ
      rcases hχ with ⟨hmem, hne, hprod⟩
      rw [Fin.prod_univ_castSucc] at hprod
      refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i =>
        Finset.mem_erase.mpr ⟨hne i.castSucc, hmem i.castSucc⟩, ?_⟩
      intro h1
      rw [h1, one_mul] at hprod
      exact hne (Fin.last m) hprod
    · intro χ₁ hχ₁ χ₂ hχ₂ h
      simp only [primTupleSet, Finset.mem_filter, Fintype.mem_piFinset] at hχ₁ hχ₂
      have hp₁ := hχ₁.2.2; have hp₂ := hχ₂.2.2
      rw [Fin.prod_univ_castSucc] at hp₁ hp₂
      have hinit : ∏ i : Fin m, χ₁ i.castSucc = ∏ i : Fin m, χ₂ i.castSucc :=
        Finset.prod_congr rfl fun i _ => congr_fun h i
      have hlast : χ₁ (Fin.last m) = χ₂ (Fin.last m) := by
        rw [hinit] at hp₁
        exact mul_left_cancel (hp₁.trans hp₂.symm)
      funext i
      cases i using Fin.lastCases with
      | last => exact hlast
      | cast j => exact congr_fun h j
    · intro ψ hψ
      rw [Finset.mem_filter, Fintype.mem_piFinset] at hψ
      rcases hψ with ⟨hmem, hprod_ne⟩
      let χ : Fin (m + 1) → MulChar F ℂ := Fin.snoc ψ (∏ i : Fin m, ψ i)⁻¹
      refine ⟨χ, ?_, ?_⟩
      · simp only [primTupleSet, Finset.mem_filter, Fintype.mem_piFinset]
        have hprod_mem : ∏ i : Fin m, ψ i ∈ powCharSet F d := by
          have : ∀ S : Finset (Fin m), ∏ i ∈ S, ψ i ∈ powCharSet F d := by
            intro S
            induction S using Finset.induction_on with
            | empty => exact one_mem_powCharSet F d
            | insert a S ha ih =>
              rw [Finset.prod_insert ha]
              exact mul_mem_powCharSet (Finset.mem_erase.mp (hmem a)).2 ih
          exact this Finset.univ
        refine ⟨fun i => ?_, fun i => ?_, ?_⟩
        · cases i using Fin.lastCases with
          | last => simpa [χ] using inv_mem_powCharSet hprod_mem
          | cast j => simpa [χ] using (Finset.mem_erase.mp (hmem j)).2
        · cases i using Fin.lastCases with
          | last => simpa [χ] using inv_ne_one.mpr hprod_ne
          | cast j => simpa [χ] using (Finset.mem_erase.mp (hmem j)).1
        · rw [Fin.prod_univ_castSucc]
          simp [χ]
      · funext j; simp [χ]

/-- Exact integer identity for `primTupleSet`:
`d * |primTupleSet F m d| = (d - 1) * ((d - 1)^(m - 1) - (-1)^(m - 1))` for all `m ≥ 1`. -/
private lemma mul_card_primTupleSet_eq {F : Type*} [Field F] [Fintype F]
    {m d : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1) :
    (d : ℤ) * ((primTupleSet F m d).card : ℤ) =
      ((d : ℤ) - 1) * (((d : ℤ) - 1) ^ (m - 1) - (-1 : ℤ) ^ (m - 1)) := by
  induction m with
  | zero => omega
  | succ k ih =>
    rcases k with _ | k
    · -- `m = 1`: `primTupleSet F 1 d = ∅`
      have hemp : primTupleSet F 1 d = ∅ := by
        ext χ
        simp only [primTupleSet, Finset.mem_filter, Finset.notMem_empty, iff_false]
        rintro ⟨_, hne, hprod⟩
        rw [Fin.prod_univ_one] at hprod
        exact hne 0 hprod
      rw [hemp, Finset.card_empty]
      simp
    · -- `m = k + 2`: use recurrence `a_{k+1} + a_{k+2} = (d - 1)^{k+1}`
      have hrec := card_primTupleSet_add_succ (F := F) (m := k + 1) hd hdvd
      have hrecZ : ((primTupleSet F (k + 1) d).card : ℤ) +
          ((primTupleSet F (k + 2) d).card : ℤ) = ((d : ℤ) - 1) ^ (k + 1) := by
        have h := congr_arg (Nat.cast : ℕ → ℤ) hrec
        push_cast [Nat.cast_sub hd] at h
        exact h
      have hih := ih (by omega)
      have hsub1 : k + 1 - 1 = k := by omega
      have hsub2 : k + 2 - 1 = k + 1 := by omega
      rw [hsub1] at hih
      rw [hsub2]
      calc (d : ℤ) * ((primTupleSet F (k + 2) d).card : ℤ)
          = (d : ℤ) * (((d : ℤ) - 1) ^ (k + 1) - ((primTupleSet F (k + 1) d).card : ℤ)) := by
              congr 1; linarith
        _ = (d : ℤ) * ((d : ℤ) - 1) ^ (k + 1) - (d : ℤ) * ((primTupleSet F (k + 1) d).card : ℤ) := by
              ring
        _ = (d : ℤ) * ((d : ℤ) - 1) ^ (k + 1) -
              ((d : ℤ) - 1) * (((d : ℤ) - 1) ^ k - (-1 : ℤ) ^ k) := by rw [hih]
        _ = ((d : ℤ) - 1) * (((d : ℤ) - 1) ^ (k + 1) - (-1 : ℤ) ^ (k + 1)) := by
              rw [pow_succ ((d : ℤ) - 1) k, pow_succ (-1 : ℤ) k]; ring

/-- **EXACT MIDDLE PRIMITIVE BETTI NUMBER FORMULA (INTEGER FORM)**:
for every dimension `n : ℕ` and degree `1 ≤ d` with `d ∣ (q - 1)`:
`d * |primitiveFermatTuples F n d| = (d - 1) * ((d - 1)^{n+1} - (-1)^{n+1})`. -/
theorem mul_card_primitiveFermatTuples {F : Type*} [Field F] [Fintype F]
    (n : ℕ) {d : ℕ} (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1) :
    (d : ℤ) * ((primitiveFermatTuples F n d).card : ℤ) =
      ((d : ℤ) - 1) * (((d : ℤ) - 1) ^ (n + 1) - (-1 : ℤ) ^ (n + 1)) := by
  have h := mul_card_primTupleSet_eq (F := F) (m := n + 2) (by omega) hd hdvd
  simpa [primitiveFermatTuples, primTupleSet] using h

/-- **EXACT MIDDLE PRIMITIVE BETTI NUMBER FORMULA (RATIONAL FORM)**:
`|primitiveFermatTuples F n d| = ((d - 1) / d) * ((d - 1)^{n+1} - (-1)^{n+1})`. -/
theorem card_primitiveFermatTuples {F : Type*} [Field F] [Fintype F]
    (n : ℕ) {d : ℕ} (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1) :
    ((primitiveFermatTuples F n d).card : ℚ) =
      (((d : ℚ) - 1) / (d : ℚ)) * (((d : ℚ) - 1) ^ (n + 1) - (-1 : ℚ) ^ (n + 1)) := by
  have hZ := mul_card_primitiveFermatTuples (F := F) n hd hdvd
  have hQ : (d : ℚ) * ((primitiveFermatTuples F n d).card : ℚ) =
      ((d : ℚ) - 1) * (((d : ℚ) - 1) ^ (n + 1) - (-1 : ℚ) ^ (n + 1)) := by
    exact_mod_cast hZ
  have hd_ne : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hd_ne]
  linarith

/-- Curve specialization (`n = 1`): `b_1 = (d - 1) * (d - 2)`. -/
theorem card_primitiveFermatTuples_curve {F : Type*} [Field F] [Fintype F]
    {d : ℕ} (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1) :
    (primitiveFermatTuples F 1 d).card = (d - 1) * (d - 2) := by
  have hZ := mul_card_primitiveFermatTuples (F := F) 1 hd hdvd
  rcases d with _ | _ | d
  · omega
  · simp at hZ; simp [hZ]
  · have hfac : (d + 2 : ℤ) * ((primitiveFermatTuples F 1 (d + 2)).card : ℤ) =
        (d + 2 : ℤ) * (((d + 1 : ℕ) * d : ℕ) : ℤ) := by
      push_cast at hZ ⊢
      linarith
    have hcancel := mul_left_cancel₀ (by positivity : (d + 2 : ℤ) ≠ 0) hfac
    have hnat : (primitiveFermatTuples F 1 (d + 2)).card = (d + 1) * d := by exact_mod_cast hcancel
    simpa [show d + 2 - 1 = d + 1 by omega, show d + 2 - 2 = d by omega] using hnat

/-- **FERMAT QUARTIC K3 SURFACE (`n = 2, d = 4`) PRIMITIVE BETTI NUMBER**:
`b_2^{prim}(V_4^2) = 21` (so total `b_2 = 1 + 21 = 22` and Euler characteristic `χ = 24`)! -/
theorem card_primitiveFermatTuples_k3 {F : Type*} [Field F] [Fintype F]
    (h4 : 4 ∣ Fintype.card F - 1) :
    (primitiveFermatTuples F 2 4).card = 21 := by
  have hZ := mul_card_primitiveFermatTuples (F := F) 2 (by omega) h4
  norm_num at hZ
  omega

/-! ### Exact Extension-Field Lifting for Fermat Hypersurfaces -/

/-- Exact point-count sequence `N_r(V_d^n) = ∑_{k=0}^n (q^k)^r + (-1)^n ∑_χ α(χ)^r`
over `𝔽_{q^r}` for `r : ℕ`. -/
def fermatHypersurfacePointCountPow (F : Type*) [Field F] [Fintype F] (n d r : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), ((Fintype.card F : ℂ) ^ k) ^ r +
    (-1 : ℂ) ^ n * ∑ χ ∈ primitiveFermatTuples F n d, (fermatHypersurfaceEigenvalue χ) ^ r

/-- At `r = 1`, `fermatHypersurfacePointCountPow F n d 1 = (fermatHypersurfacePoints F n d : ℂ)`. -/
theorem fermatHypersurfacePointCountPow_one {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (n : ℕ) {d : ℕ} (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1) :
    fermatHypersurfacePointCountPow F n d 1 = (fermatHypersurfacePoints F n d : ℂ) := by
  unfold fermatHypersurfacePointCountPow
  simp only [pow_one]
  exact (fermatHypersurfacePoints_eq n hd hdvd).symm

/-- **EXACT EXTENSION-FIELD POINT-COUNTING FORMULA FOR `n`-DIMENSIONAL FERMAT HYPERSURFACES**:
for EVERY finite field extension `E / F` of degree `r = Module.finrank F E`,
`(fermatHypersurfacePoints E n d : ℂ) = fermatHypersurfacePointCountPow F n d (Module.finrank F E)`! -/
theorem fermatHypersurfacePoints_extension_eq {F E : Type*}
    [Field F] [Fintype F] [DecidableEq F] [Field E] [Fintype E] [DecidableEq E] [Algebra F E]
    (n : ℕ) {d : ℕ} (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1) :
    (fermatHypersurfacePoints E n d : ℂ) =
      fermatHypersurfacePointCountPow F n d (Module.finrank F E) := by
  classical
  set q := Fintype.card F
  set r := Module.finrank F E
  have hcardE : Fintype.card E = q ^ r := Module.card_eq_pow_finrank
  have hq2 : 2 ≤ q := two_le_card_finiteField (F := F)
  have hdvdE : d ∣ Fintype.card E - 1 := by
    rw [hcardE]
    have hq_dvd : q - 1 ∣ q ^ r - 1 := by
      have hsub : ((q - 1 : ℕ) : ℤ) ∣ ((q ^ r - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_sub (Nat.one_le_pow r q (by omega)),
          Nat.cast_pow, Nat.cast_one]
        exact ⟨∑ i ∈ Finset.range r, (q : ℤ) ^ i, (mul_geom_sum (q : ℤ) r).symm⟩
      exact Int.ofNat_dvd.mp hsub
    exact hdvd.trans hq_dvd
  rw [fermatHypersurfacePoints_eq n hd hdvdE]
  unfold fermatHypersurfacePointCountPow
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcardE, Nat.cast_pow, ← pow_mul, ← pow_mul, mul_comm r k]
  · congr 1
    -- Bijection `χ ↦ (fun i => liftMulChar E (χ i))` from `primitiveFermatTuples F n d` to `E`
    let L : (Fin (n + 2) → MulChar F ℂ) → (Fin (n + 2) → MulChar E ℂ) :=
      fun χ i => liftMulChar E (χ i)
    have hL_mem : ∀ χ ∈ primitiveFermatTuples F n d, L χ ∈ primitiveFermatTuples E n d := by
      intro χ hχ
      rw [mem_primitiveFermatTuples] at hχ ⊢
      refine ⟨fun i => ?_, fun i => liftMulChar_ne_one (hχ.2.1 i), ?_⟩
      · have hi := hχ.1 i
        rw [mem_powCharSet] at hi ⊢
        rw [← liftMulChar_pow, hi, liftMulChar_one]
      · have hlift_prod : ∀ S : Finset (Fin (n + 2)),
            ∏ i ∈ S, liftMulChar E (χ i) = liftMulChar E (∏ i ∈ S, χ i) := by
          intro S
          induction S using Finset.induction_on with
          | empty => simp [liftMulChar_one]
          | insert a S ha ih =>
            rw [Finset.prod_insert ha, Finset.prod_insert ha, liftMulChar_mul, ih]
        change ∏ i : Fin (n + 2), liftMulChar E (χ i) = 1
        rw [hlift_prod Finset.univ, hχ.2.2, liftMulChar_one]
    have hL_inj : Set.InjOn L (primitiveFermatTuples F n d : Set _) := by
      intro χ₁ _ χ₂ _ h
      funext i
      exact liftMulChar_injective F E (congr_fun h i)
    have hL_img : (primitiveFermatTuples F n d).image L = primitiveFermatTuples E n d := by
      apply Finset.eq_of_subset_of_card_le
      · intro ψ hψ
        obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.mp hψ
        exact hL_mem χ hχ
      · rw [Finset.card_image_of_injOn hL_inj]
        have hF := mul_card_primitiveFermatTuples (F := F) n hd hdvd
        have hE := mul_card_primitiveFermatTuples (F := E) n hd hdvdE
        have hmul_eq : (d : ℤ) * ((primitiveFermatTuples E n d).card : ℤ) =
            (d : ℤ) * ((primitiveFermatTuples F n d).card : ℤ) := hE.trans hF.symm
        have heqZ := mul_left_cancel₀ (by positivity : (d : ℤ) ≠ 0) hmul_eq
        have heqN : (primitiveFermatTuples E n d).card = (primitiveFermatTuples F n d).card := by
          exact_mod_cast heqZ
        exact heqN.le
    rw [← hL_img, Finset.sum_image hL_inj]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [mem_primitiveFermatTuples] at hχ
    exact hasse_davenport_multiJacobiSum hχ.2.1 hχ.2.2

/-! ### Complete Weil Conjectures I, II, III for `Z(V_d^n / 𝔽_q, T)` -/

/-- The primitive middle-cohomology Weil `L`-polynomial
`P_n(T) := ∏_{χ ∈ primitiveFermatTuples F n d} (1 - α(χ) T)` of `V_d^n / 𝔽_q`. -/
def fermatHypersurfaceLPoly (F : Type*) [Field F] [Fintype F] (n d : ℕ) : Polynomial ℂ :=
  ∏ χ ∈ primitiveFermatTuples F n d,
    (1 - Polynomial.C (fermatHypersurfaceEigenvalue χ) * Polynomial.X)

/-- The formal Hasse–Weil Zeta Function
`Z(V_d^n / 𝔽_q, T) = exp(∑_{r ≥ 1} N_r(V_d^n) T^r / r) ∈ ℂ[[T]]`. -/
def fermatHypersurfaceZetaSeries (F : Type*) [Field F] [Fintype F] (n d : ℕ) : PowerSeries ℂ :=
  expSeries (PowerSeries.mk fun r =>
    if r = 0 then 0 else fermatHypersurfacePointCountPow F n d r / (r : ℂ))

/-- The rational evaluation of the Hasse–Weil Zeta Function
`Z_rat(V_d^n / 𝔽_q, T) = P_n(T)^{(-1)^{n+1}} / ∏_{k=0}^n (1 - q^k T)`. -/
def fermatHypersurfaceZetaRat (F : Type*) [Field F] [Fintype F] (n d : ℕ) (T : ℂ) : ℂ :=
  ((fermatHypersurfaceLPoly F n d).eval T) ^ ((-1 : ℤ) ^ (n + 1)) /
    ∏ k ∈ Finset.range (n + 1), (1 - (Fintype.card F : ℂ) ^ k * T)

/-- Exact modulus of every primitive Fermat hypersurface Frobenius eigenvalue:
`‖fermatHypersurfaceEigenvalue χ‖ = q ^ (n / 2)`. -/
theorem norm_fermatHypersurfaceEigenvalue_eq_rpow {F : Type*} [Field F] [Fintype F] {n d : ℕ}
    {χ : Fin (n + 2) → MulChar F ℂ} (hχ : χ ∈ primitiveFermatTuples F n d) :
    ‖fermatHypersurfaceEigenvalue χ‖ = (Fintype.card F : ℝ) ^ ((n : ℝ) / 2) := by
  rw [mem_primitiveFermatTuples] at hχ
  unfold fermatHypersurfaceEigenvalue
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact norm_multiJacobiSum_eq_rpow hχ.2.1 hχ.2.2

theorem fermatHypersurfaceEigenvalue_ne_zero {F : Type*} [Field F] [Fintype F] {n d : ℕ}
    {χ : Fin (n + 2) → MulChar F ℂ} (hχ : χ ∈ primitiveFermatTuples F n d) :
    fermatHypersurfaceEigenvalue χ ≠ 0 := by
  intro h0
  have hnorm := norm_fermatHypersurfaceEigenvalue_eq_rpow hχ
  rw [h0, norm_zero] at hnorm
  have hpos : (0 : ℝ) < (Fintype.card F : ℝ) ^ ((n : ℝ) / 2) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr Fintype.card_pos) _
  linarith

/-- Exact degree of `P_n(T)`: `(fermatHypersurfaceLPoly F n d).natDegree = b_n^{prim}(d)`. -/
theorem natDegree_fermatHypersurfaceLPoly {F : Type*} [Field F] [Fintype F] (n d : ℕ) :
    (fermatHypersurfaceLPoly F n d).natDegree = (primitiveFermatTuples F n d).card := by
  unfold fermatHypersurfaceLPoly
  have hne : ∀ χ ∈ primitiveFermatTuples F n d,
      1 - Polynomial.C (fermatHypersurfaceEigenvalue χ) * Polynomial.X ≠ 0 := by
    intro χ _ h0
    have heval := congr_arg (Polynomial.eval 0) h0
    simp at heval
  rw [Polynomial.natDegree_prod _ _ hne]
  have hdeg : ∀ χ ∈ primitiveFermatTuples F n d,
      (1 - Polynomial.C (fermatHypersurfaceEigenvalue χ) * Polynomial.X).natDegree = 1 := by
    intro χ hχ
    have hα : fermatHypersurfaceEigenvalue χ ≠ 0 := fermatHypersurfaceEigenvalue_ne_zero hχ
    have hrew : 1 - Polynomial.C (fermatHypersurfaceEigenvalue χ) * Polynomial.X =
        Polynomial.C (-fermatHypersurfaceEigenvalue χ) * Polynomial.X + Polynomial.C 1 := by
      simp [sub_eq_add_neg, add_comm]
    rw [hrew, Polynomial.natDegree_add_C, Polynomial.natDegree_C_mul_X _ (neg_ne_zero.mpr hα)]
  rw [Finset.sum_congr rfl hdeg, Finset.sum_const, smul_eq_mul, mul_one]

/-- Helper: formal power series coercion of `P_n(T)` equals `∏ χ, expSeries (-logSeries (α χ))`. -/
private lemma coe_fermatHypersurfaceLPoly_eq_prod_expSeries (F : Type*) [Field F] [Fintype F]
    (n d : ℕ) :
    ((fermatHypersurfaceLPoly F n d : Polynomial ℂ) : PowerSeries ℂ) =
      ∏ χ ∈ primitiveFermatTuples F n d, expSeries (-logSeries (fermatHypersurfaceEigenvalue χ)) := by
  unfold fermatHypersurfaceLPoly
  change Polynomial.coeToPowerSeries.ringHom
      (∏ χ ∈ primitiveFermatTuples F n d,
        (1 - Polynomial.C (fermatHypersurfaceEigenvalue χ) * Polynomial.X)) = _
  rw [map_prod]
  refine Finset.prod_congr rfl fun χ _ => ?_
  rw [expSeries_neg_logSeries]
  simp [Polynomial.coeToPowerSeries.ringHom]

/-- **WEIL CONJECTURE I (RATIONALITY — ODD DIMENSION `n`)**:
for odd `n`, `Z(V_d^n / 𝔽_q, T) * ∏_{k=0}^n (1 - q^k T) = P_n(T)` in `ℂ[[T]]`. -/
theorem fermatHypersurface_weil_rationality_odd (F : Type*) [Field F] [Fintype F]
    {n : ℕ} (hn : Odd n) (d : ℕ) :
    fermatHypersurfaceZetaSeries F n d *
        (∏ k ∈ Finset.range (n + 1), (1 - PowerSeries.C ((Fintype.card F : ℂ) ^ k) * PowerSeries.X)) =
      (fermatHypersurfaceLPoly F n d : PowerSeries ℂ) := by
  unfold fermatHypersurfaceZetaSeries
  have hsign : (-1 : ℂ) ^ n = -1 := hn.neg_one_pow
  have hlog :
      (PowerSeries.mk fun r =>
          if r = 0 then 0 else fermatHypersurfacePointCountPow F n d r / (r : ℂ)) =
        (∑ k ∈ Finset.range (n + 1), logSeries ((Fintype.card F : ℂ) ^ k)) +
          ∑ χ ∈ primitiveFermatTuples F n d, (-logSeries (fermatHypersurfaceEigenvalue χ)) := by
    ext r
    simp only [PowerSeries.coeff_mk, map_add, map_sum, map_neg, coeff_logSeries]
    by_cases hr : r = 0
    · simp [hr]
    · simp only [if_neg hr, fermatHypersurfacePointCountPow, hsign, Finset.sum_neg_distrib,
        ← Finset.sum_div]
      ring
  have h0_triv : PowerSeries.constantCoeff
      (∑ k ∈ Finset.range (n + 1), logSeries ((Fintype.card F : ℂ) ^ k)) = 0 := by
    rw [map_sum]; exact Finset.sum_eq_zero fun _ _ => constantCoeff_logSeries _
  have h0_prim : PowerSeries.constantCoeff
      (∑ χ ∈ primitiveFermatTuples F n d, (-logSeries (fermatHypersurfaceEigenvalue χ))) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun _ _ => by rw [map_neg, constantCoeff_logSeries, neg_zero]
  rw [hlog, expSeries_add h0_triv h0_prim,
    expSeries_sum _ _ (fun _ _ => constantCoeff_logSeries _),
    expSeries_sum _ _ (fun _ _ => by rw [map_neg, constantCoeff_logSeries, neg_zero]),
    ← coe_fermatHypersurfaceLPoly_eq_prod_expSeries]
  have hcancel :
      (∏ k ∈ Finset.range (n + 1), expSeries (logSeries ((Fintype.card F : ℂ) ^ k))) *
        (∏ k ∈ Finset.range (n + 1),
          (1 - PowerSeries.C ((Fintype.card F : ℂ) ^ k) * PowerSeries.X)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [mul_comm]
    exact one_sub_C_mul_X_mul_expSeries_logSeries _
  calc (∏ k ∈ Finset.range (n + 1), expSeries (logSeries ((Fintype.card F : ℂ) ^ k))) *
          (fermatHypersurfaceLPoly F n d : PowerSeries ℂ) *
          (∏ k ∈ Finset.range (n + 1),
            (1 - PowerSeries.C ((Fintype.card F : ℂ) ^ k) * PowerSeries.X))
      = ((∏ k ∈ Finset.range (n + 1), expSeries (logSeries ((Fintype.card F : ℂ) ^ k))) *
          (∏ k ∈ Finset.range (n + 1),
            (1 - PowerSeries.C ((Fintype.card F : ℂ) ^ k) * PowerSeries.X))) *
          (fermatHypersurfaceLPoly F n d : PowerSeries ℂ) := by ring
    _ = 1 * (fermatHypersurfaceLPoly F n d : PowerSeries ℂ) := by rw [hcancel]
    _ = (fermatHypersurfaceLPoly F n d : PowerSeries ℂ) := one_mul _

/-- **WEIL CONJECTURE I (RATIONALITY — EVEN DIMENSION `n`, INCLUDING K3 SURFACES `n = 2`)**:
for even `n`, `Z(V_d^n / 𝔽_q, T) * (∏_{k=0}^n (1 - q^k T)) * P_n(T) = 1` in `ℂ[[T]]`. -/
theorem fermatHypersurface_weil_rationality_even (F : Type*) [Field F] [Fintype F]
    {n : ℕ} (hn : Even n) (d : ℕ) :
    fermatHypersurfaceZetaSeries F n d *
        (∏ k ∈ Finset.range (n + 1), (1 - PowerSeries.C ((Fintype.card F : ℂ) ^ k) * PowerSeries.X)) *
        (fermatHypersurfaceLPoly F n d : PowerSeries ℂ) = 1 := by
  unfold fermatHypersurfaceZetaSeries
  have hsign : (-1 : ℂ) ^ n = 1 := hn.neg_one_pow
  have hlog :
      (PowerSeries.mk fun r =>
          if r = 0 then 0 else fermatHypersurfacePointCountPow F n d r / (r : ℂ)) =
        (∑ k ∈ Finset.range (n + 1), logSeries ((Fintype.card F : ℂ) ^ k)) +
          ∑ χ ∈ primitiveFermatTuples F n d, logSeries (fermatHypersurfaceEigenvalue χ) := by
    ext r
    simp only [PowerSeries.coeff_mk, map_add, map_sum, coeff_logSeries]
    by_cases hr : r = 0
    · simp [hr]
    · simp only [if_neg hr, fermatHypersurfacePointCountPow, hsign, one_mul, ← Finset.sum_div]
      ring
  have h0_triv : PowerSeries.constantCoeff
      (∑ k ∈ Finset.range (n + 1), logSeries ((Fintype.card F : ℂ) ^ k)) = 0 := by
    rw [map_sum]; exact Finset.sum_eq_zero fun _ _ => constantCoeff_logSeries _
  have h0_prim : PowerSeries.constantCoeff
      (∑ χ ∈ primitiveFermatTuples F n d, logSeries (fermatHypersurfaceEigenvalue χ)) = 0 := by
    rw [map_sum]; exact Finset.sum_eq_zero fun _ _ => constantCoeff_logSeries _
  rw [hlog, expSeries_add h0_triv h0_prim,
    expSeries_sum _ _ (fun _ _ => constantCoeff_logSeries _),
    expSeries_sum _ _ (fun _ _ => constantCoeff_logSeries _),
    coe_fermatHypersurfaceLPoly_eq_prod_expSeries]
  have hcancel1 :
      (∏ k ∈ Finset.range (n + 1), expSeries (logSeries ((Fintype.card F : ℂ) ^ k))) *
        (∏ k ∈ Finset.range (n + 1),
          (1 - PowerSeries.C ((Fintype.card F : ℂ) ^ k) * PowerSeries.X)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [mul_comm]; exact one_sub_C_mul_X_mul_expSeries_logSeries _
  have hcancel2 :
      (∏ χ ∈ primitiveFermatTuples F n d, expSeries (logSeries (fermatHypersurfaceEigenvalue χ))) *
        (∏ χ ∈ primitiveFermatTuples F n d,
          expSeries (-logSeries (fermatHypersurfaceEigenvalue χ))) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun χ _ =>
      expSeries_mul_expSeries_neg (constantCoeff_logSeries _)
  calc (∏ k ∈ Finset.range (n + 1), expSeries (logSeries ((Fintype.card F : ℂ) ^ k))) *
          (∏ χ ∈ primitiveFermatTuples F n d,
            expSeries (logSeries (fermatHypersurfaceEigenvalue χ))) *
          (∏ k ∈ Finset.range (n + 1),
            (1 - PowerSeries.C ((Fintype.card F : ℂ) ^ k) * PowerSeries.X)) *
          (∏ χ ∈ primitiveFermatTuples F n d,
            expSeries (-logSeries (fermatHypersurfaceEigenvalue χ)))
      = ((∏ k ∈ Finset.range (n + 1), expSeries (logSeries ((Fintype.card F : ℂ) ^ k))) *
          (∏ k ∈ Finset.range (n + 1),
            (1 - PowerSeries.C ((Fintype.card F : ℂ) ^ k) * PowerSeries.X))) *
          ((∏ χ ∈ primitiveFermatTuples F n d,
            expSeries (logSeries (fermatHypersurfaceEigenvalue χ))) *
          (∏ χ ∈ primitiveFermatTuples F n d,
            expSeries (-logSeries (fermatHypersurfaceEigenvalue χ)))) := by ring
    _ = 1 * 1 := by rw [hcancel1, hcancel2]
    _ = 1 := one_mul 1

/-- **WEIL CONJECTURE I (UNIFIED RATIONALITY FOR ALL DIMENSIONS `n ≥ 1`)**:
`Z(V_d^n / 𝔽_q, T) = P_n(T)^{(-1)^{n+1}} / ∏_{k=0}^n (1 - q^k T)` in `ℂ[[T]]`. -/
theorem fermatHypersurface_weil_rationality (F : Type*) [Field F] [Fintype F] (n d : ℕ) :
    (Odd n →
      fermatHypersurfaceZetaSeries F n d *
        (∏ k ∈ Finset.range (n + 1), (1 - PowerSeries.C ((Fintype.card F : ℂ) ^ k) * PowerSeries.X)) =
        (fermatHypersurfaceLPoly F n d : PowerSeries ℂ)) ∧
    (Even n →
      fermatHypersurfaceZetaSeries F n d *
        (∏ k ∈ Finset.range (n + 1), (1 - PowerSeries.C ((Fintype.card F : ℂ) ^ k) * PowerSeries.X)) *
        (fermatHypersurfaceLPoly F n d : PowerSeries ℂ) = 1) :=
  ⟨fun hn => fermatHypersurface_weil_rationality_odd F hn d,
   fun hn => fermatHypersurface_weil_rationality_even F hn d⟩

/-- General product-of-involution lemma (allowing fixed points!):
if `ι` is an involution on `s` with `f x * f (ι x) = c ^ 2` for all `x ∈ s`, then
`∏ x ∈ s, f x = ε * c ^ s.card` for an explicit sign `ε ∈ {1, -1}`. -/
private lemma prod_eq_sign_mul_pow_of_involution {β : Type*} [DecidableEq β]
    (s : Finset β) (ι : β → β) (f : β → ℂ) (c : ℂ)
    (hmem : ∀ x ∈ s, ι x ∈ s)
    (hinv : ∀ x ∈ s, ι (ι x) = x)
    (hmul : ∀ x ∈ s, f x * f (ι x) = c ^ 2) :
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ ∏ x ∈ s, f x = ε * c ^ s.card := by
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | _ m ih =>
    rcases Finset.eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
    · subst hn; exact ⟨1, Or.inl rfl, by simp⟩
    · by_cases hfix : ι x = x
      · -- Fixed point: `(f x)^2 = c^2`, so `f x = ±c`
        have hfx2 : (f x - c) * (f x + c) = 0 := by
          have := hmul x hx
          rw [hfix] at this
          linear_combination this
        have hfx : ∃ δ : ℂ, (δ = 1 ∨ δ = -1) ∧ f x = δ * c := by
          rcases mul_eq_zero.mp hfx2 with h1 | h2
          · exact ⟨1, Or.inl rfl, by linear_combination h1⟩
          · exact ⟨-1, Or.inr rfl, by linear_combination h2⟩
        obtain ⟨δ, hδ, hfx_eq⟩ := hfx
        set s' := s.erase x
        have hs'_sub : s' ⊆ s := Finset.erase_subset x s
        have hcard_s' : s'.card + 1 = s.card := Finset.card_erase_add_one hx
        have hmem' : ∀ y ∈ s', ι y ∈ s' := by
          intro y hy
          have hys := hs'_sub hy
          have hyne : y ≠ x := (Finset.mem_erase.mp hy).1
          refine Finset.mem_erase.mpr ⟨?_, hmem y hys⟩
          intro heq
          apply hyne
          calc y = ι (ι y) := (hinv y hys).symm
            _ = ι x := by rw [heq]
            _ = x := hfix
        obtain ⟨ε', hε', hih⟩ := ih s'.card (by omega) s' hmem'
          (fun y hy => hinv y (hs'_sub hy)) (fun y hy => hmul y (hs'_sub hy)) rfl
        refine ⟨δ * ε', ?_, ?_⟩
        · rcases hδ with rfl | rfl <;> rcases hε' with rfl | rfl <;> norm_num
        · rw [← Finset.mul_prod_erase s f hx, hfx_eq, hih, ← hn, ← hcard_s', pow_succ']
          ring
      · -- Two-cycle `{x, ι x}`: `f x * f (ι x) = c^2`
        have hix : ι x ∈ s := hmem x hx
        have hix_mem : ι x ∈ s.erase x := Finset.mem_erase.mpr ⟨hfix, hix⟩
        set s' := (s.erase x).erase (ι x)
        have hs'_sub : s' ⊆ s := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
        have hcard_s' : s'.card + 2 = s.card := by
          have h1 : (s.erase x).card + 1 = s.card := Finset.card_erase_add_one hx
          have h2 : s'.card + 1 = (s.erase x).card := Finset.card_erase_add_one hix_mem
          omega
        have hmem' : ∀ y ∈ s', ι y ∈ s' := by
          intro y hy
          have hys := hs'_sub hy
          have hy_ne_ix : y ≠ ι x := (Finset.mem_erase.mp hy).1
          have hy_ne_x : y ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp hy).2).1
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hmem y hys⟩⟩
          · intro heq
            apply hy_ne_x
            calc y = ι (ι y) := (hinv y hys).symm
              _ = ι (ι x) := by rw [heq]
              _ = x := hinv x hx
          · intro heq
            apply hy_ne_ix
            calc y = ι (ι y) := (hinv y hys).symm
              _ = ι x := by rw [heq]
        obtain ⟨ε', hε', hih⟩ := ih s'.card (by omega) s' hmem'
          (fun y hy => hinv y (hs'_sub hy)) (fun y hy => hmul y (hs'_sub hy)) rfl
        refine ⟨ε', hε', ?_⟩
        rw [← Finset.mul_prod_erase s f hx, ← Finset.mul_prod_erase (s.erase x) f hix_mem,
          ← mul_assoc, hmul x hx, hih, ← hn, ← hcard_s', pow_add]
        ring

/-- **WEIL CONJECTURE II (FUNCTIONAL EQUATION FOR `P_n(T)`) — ARBITRARY DIMENSION `n`**:
for EVERY `n : ℕ`, `d : ℕ`, and `T : ℂ` with `T ≠ 0`,
`P_n(1 / (q^n T)) = ε * (q^{n/2} T)^{-b_n^{prim}} * P_n(T)` with `ε ∈ {1, -1}`! -/
theorem fermatHypersurface_weil_functional_equation {F : Type*} [Field F] [Fintype F]
    (n d : ℕ) {T : ℂ} (hT : T ≠ 0) :
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧
      (fermatHypersurfaceLPoly F n d).eval (1 / ((Fintype.card F : ℂ) ^ n * T)) =
        ε * ((((Real.sqrt (Fintype.card F : ℝ) : ℝ) : ℂ) ^ n * T) ^
          (-((primitiveFermatTuples F n d).card : ℤ))) *
          (fermatHypersurfaceLPoly F n d).eval T := by
  classical
  set S := primitiveFermatTuples F n d
  set ι : (Fin (n + 2) → MulChar F ℂ) → (Fin (n + 2) → MulChar F ℂ) := fun χ i => (χ i)⁻¹
  set α := fermatHypersurfaceEigenvalue (F := F) (n := n)
  set c : ℂ := ((Real.sqrt (Fintype.card F : ℝ) : ℝ) : ℂ) ^ n
  have hc2 : c ^ 2 = (Fintype.card F : ℂ) ^ n := by
    unfold c
    rw [← pow_mul, mul_comm n 2, pow_mul]
    have hsq : ((Real.sqrt (Fintype.card F : ℝ) : ℝ) : ℂ) ^ 2 = (Fintype.card F : ℂ) := by
      exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card F))
    rw [hsq]
  have hq : (Fintype.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hqn : (Fintype.card F : ℂ) ^ n ≠ 0 := pow_ne_zero n hq
  have hc_ne : c ≠ 0 := by
    intro h0; rw [h0, zero_pow (by omega : 2 ≠ 0)] at hc2; exact hqn hc2.symm
  have hmem : ∀ χ ∈ S, ι χ ∈ S := by
    intro χ hχ
    rw [mem_primitiveFermatTuples] at hχ ⊢
    refine ⟨fun i => inv_mem_powCharSet (hχ.1 i), fun i => inv_ne_one.mpr (hχ.2.1 i), ?_⟩
    change ∏ i : Fin (n + 2), (χ i)⁻¹ = 1
    rw [Finset.prod_inv_distrib, hχ.2.2, inv_one]
  have hinv : ∀ χ ∈ S, ι (ι χ) = χ := by
    intro χ _; funext i; exact inv_inv (χ i)
  have hpair : ∀ χ ∈ S, α χ * α (ι χ) = c ^ 2 := by
    intro χ hχ
    rw [mem_primitiveFermatTuples] at hχ
    rw [hc2]
    unfold α fermatHypersurfaceEigenvalue
    have hsign : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by rw [← mul_pow]; norm_num
    calc ((-1 : ℂ) ^ n * multiJacobiSum χ) * ((-1 : ℂ) ^ n * multiJacobiSum (ι χ))
        = ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) * (multiJacobiSum χ * multiJacobiSum (ι χ)) := by ring
      _ = 1 * (Fintype.card F : ℂ) ^ n := by rw [hsign, multiJacobiSum_mul_inv_eq hχ.2.1 hχ.2.2]
      _ = (Fintype.card F : ℂ) ^ n := one_mul _
  obtain ⟨ε₀, hε₀, hprod⟩ := prod_eq_sign_mul_pow_of_involution S ι α c hmem hinv hpair
  have hε₀_ne : ε₀ ≠ 0 := by rcases hε₀ with rfl | rfl <;> norm_num
  have hε₀_inv : ε₀⁻¹ = ε₀ := by rcases hε₀ with rfl | rfl <;> norm_num
  set ε : ℂ := (-1 : ℂ) ^ S.card * ε₀
  have hε : ε = 1 ∨ ε = -1 := by
    rcases Nat.even_or_odd S.card with hE | hO
    · rcases hε₀ with rfl | rfl
      · left; simp [ε, hE.neg_one_pow]
      · right; simp [ε, hE.neg_one_pow]
    · rcases hε₀ with rfl | rfl
      · right; simp [ε, hO.neg_one_pow]
      · left; simp [ε, hO.neg_one_pow]
  refine ⟨ε, hε, ?_⟩
  unfold fermatHypersurfaceLPoly
  rw [Polynomial.eval_prod, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  have hα_ne : ∀ χ ∈ S, α χ ≠ 0 := fun _ hχ => fermatHypersurfaceEigenvalue_ne_zero hχ
  have hrew : ∀ χ ∈ S,
      1 - α χ * (1 / ((Fintype.card F : ℂ) ^ n * T)) =
        (-(α (ι χ) * T))⁻¹ * (1 - α (ι χ) * T) := by
    intro χ hχ
    have hι_ne : α (ι χ) ≠ 0 := hα_ne (ι χ) (hmem χ hχ)
    have hdiv : α χ / (Fintype.card F : ℂ) ^ n = (α (ι χ))⁻¹ := by
      rw [div_eq_iff hqn, ← hc2]
      calc α χ = α χ * (α (ι χ) * (α (ι χ))⁻¹) := by rw [mul_inv_cancel₀ hι_ne, mul_one]
        _ = (α χ * α (ι χ)) * (α (ι χ))⁻¹ := by ring
        _ = c ^ 2 * (α (ι χ))⁻¹ := by rw [hpair χ hχ]
        _ = (α (ι χ))⁻¹ * c ^ 2 := mul_comm _ _
    have hleft : 1 - α χ * (1 / ((Fintype.card F : ℂ) ^ n * T)) = 1 - (α (ι χ))⁻¹ * T⁻¹ := by
      have : α χ * (1 / ((Fintype.card F : ℂ) ^ n * T)) =
          (α χ / (Fintype.card F : ℂ) ^ n) * T⁻¹ := by field_simp [hqn, hT]
      rw [this, hdiv]
    rw [hleft]
    field_simp [hι_ne, hT]
    ring
  rw [Finset.prod_congr rfl hrew, Finset.prod_mul_distrib]
  have hreidx : ∀ (G : (Fin (n + 2) → MulChar F ℂ) → ℂ),
      ∏ χ ∈ S, G (ι χ) = ∏ χ ∈ S, G χ := by
    intro G
    refine Finset.prod_bij (fun χ _ => ι χ) (fun χ hχ => hmem χ hχ) ?_ ?_ (fun _ _ => rfl)
    · intro χ₁ hχ₁ χ₂ hχ₂ h
      calc χ₁ = ι (ι χ₁) := (hinv χ₁ hχ₁).symm
        _ = ι (ι χ₂) := by rw [h]
        _ = χ₂ := hinv χ₂ hχ₂
    · intro χ hχ; exact ⟨ι χ, hmem χ hχ, hinv χ hχ⟩
  rw [hreidx (fun χ => (-(α χ * T))⁻¹), hreidx (fun χ => 1 - α χ * T)]
  congr 1
  rw [Finset.prod_inv_distrib]
  have hneg_prod : ∏ χ ∈ S, -(α χ * T) = (-1 : ℂ) ^ S.card * ((∏ χ ∈ S, α χ) * T ^ S.card) := by
    have hrew2 : ∀ χ ∈ S, -(α χ * T) = (-1 : ℂ) * (α χ * T) := fun _ _ => by ring
    rw [Finset.prod_congr rfl hrew2, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.prod_const]
  rw [hneg_prod, hprod, zpow_neg, zpow_natCast, mul_pow]
  have hneg1_inv : ((-1 : ℂ) ^ S.card)⁻¹ = (-1 : ℂ) ^ S.card := by
    rcases Nat.even_or_odd S.card with hE | hO
    · simp [hE.neg_one_pow]
    · simp [hO.neg_one_pow]
  rw [mul_inv, mul_inv, mul_inv, hneg1_inv, hε₀_inv]
  unfold ε
  ring

/-- **WEIL CONJECTURE II (FULL ZETA FUNCTIONAL EQUATION WITH EULER CHARACTERISTIC)**:
for every `n, d : ℕ` and every `T : ℂ` outside the poles `0` and `q^{-k}`,
`Z_rat(1 / (q^n T)) = ε * (q^{n/2} T)^{χ(V_d^n)} * Z_rat(T)` where `ε ∈ {1, -1}` and
`χ(V_d^n) = (n + 1) + (-1)^n * b_n^{prim}(d)` is the exact Euler characteristic! -/
theorem fermatHypersurface_weil_functional_equation_zeta {F : Type*} [Field F] [Fintype F]
    (n d : ℕ) {T : ℂ} (hT : T ≠ 0)
    (hpoles : ∀ k ∈ Finset.range (n + 1), (Fintype.card F : ℂ) ^ k * T ≠ 1) :
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧
      fermatHypersurfaceZetaRat F n d (1 / ((Fintype.card F : ℂ) ^ n * T)) =
        ε * ((((Real.sqrt (Fintype.card F : ℝ) : ℝ) : ℂ) ^ n * T) ^
          ((n + 1 : ℤ) + (-1 : ℤ) ^ n * ((primitiveFermatTuples F n d).card : ℤ))) *
          fermatHypersurfaceZetaRat F n d T := by
  set q : ℂ := (Fintype.card F : ℂ)
  set c : ℂ := ((Real.sqrt (Fintype.card F : ℝ) : ℝ) : ℂ) ^ n
  have hc2 : c ^ 2 = q ^ n := by
    unfold c q
    rw [← pow_mul, mul_comm n 2, pow_mul]
    have hsq : ((Real.sqrt (Fintype.card F : ℝ) : ℝ) : ℂ) ^ 2 = (Fintype.card F : ℂ) := by
      exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card F))
    rw [hsq]
  have hq : q ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hqn : q ^ n ≠ 0 := pow_ne_zero n hq
  have hc_ne : c ≠ 0 := by
    intro h0; rw [h0, zero_pow (by omega : 2 ≠ 0)] at hc2; exact hqn hc2.symm
  have hcT_ne : c * T ≠ 0 := mul_ne_zero hc_ne hT
  obtain ⟨εP, hεP, hfeP⟩ := fermatHypersurface_weil_functional_equation (F := F) n d hT
  -- Transform denominator `∏_{k=0}^n (1 - q^k / (q^n T))`
  have hden :
      ∏ k ∈ Finset.range (n + 1), (1 - q ^ k * (1 / (q ^ n * T))) =
        (-1 : ℂ) ^ (n + 1) * (c * T) ^ (-(n + 1 : ℤ)) *
          ∏ k ∈ Finset.range (n + 1), (1 - q ^ k * T) := by
    have hrew : ∀ k ∈ Finset.range (n + 1),
        1 - q ^ k * (1 / (q ^ n * T)) =
          (-(q ^ (n - k) * T))⁻¹ * (1 - q ^ (n - k) * T) := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hqnk : q ^ (n - k) ≠ 0 := pow_ne_zero (n - k) hq
      have hpow : q ^ k * q ^ (n - k) = q ^ n := by rw [← pow_add, Nat.add_sub_of_le hkn]
      field_simp [hqn, hqnk, hT]
      linear_combination -hpow
    rw [Finset.prod_congr rfl hrew, Finset.prod_mul_distrib]
    have hrev : ∀ (G : ℕ → ℂ),
        ∏ k ∈ Finset.range (n + 1), G (n - k) = ∏ k ∈ Finset.range (n + 1), G k := by
      intro G
      refine Finset.prod_bij (fun k _ => n - k) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro k hk; rw [Finset.mem_range] at hk ⊢; omega
      · intro k₁ hk₁ k₂ hk₂ h; rw [Finset.mem_range] at hk₁ hk₂; omega
      · intro j hj; rw [Finset.mem_range] at hj
        exact ⟨n - j, Finset.mem_range.mpr (by omega), by omega⟩
    rw [hrev (fun k => (-(q ^ k * T))⁻¹), hrev (fun k => 1 - q ^ k * T)]
    congr 1
    rw [Finset.prod_inv_distrib]
    have hneg_prod : ∏ k ∈ Finset.range (n + 1), -(q ^ k * T) =
        (-1 : ℂ) ^ (n + 1) * (∏ k ∈ Finset.range (n + 1), q ^ k) * T ^ (n + 1) := by
      have hrew2 : ∀ k ∈ Finset.range (n + 1), -(q ^ k * T) = (-1 : ℂ) * (q ^ k * T) :=
        fun _ _ => by ring
      rw [Finset.prod_congr rfl hrew2, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.prod_const, Finset.card_range]
      ring
    have hprod_q : ∏ k ∈ Finset.range (n + 1), q ^ k = c ^ (n + 1) := by
      rw [Finset.prod_pow_eq_pow_sum]
      have hsum_k : 2 * ∑ k ∈ Finset.range (n + 1), k = n * (n + 1) := by
        have h := Finset.sum_range_id_mul_two (n + 1)
        simpa [mul_comm] using h
      have hq_sq : q = ((Real.sqrt (Fintype.card F : ℝ) : ℝ) : ℂ) ^ 2 := by
        unfold q
        exact_mod_cast (Real.sq_sqrt (Nat.cast_nonneg (Fintype.card F))).symm
      conv_lhs => rw [hq_sq]
      rw [← pow_mul, hsum_k]
      unfold c
      rw [← pow_mul]
    rw [hneg_prod, hprod_q,
      show -(n + 1 : ℤ) = -((n + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast, mul_pow]
    have hneg1_inv : ((-1 : ℂ) ^ (n + 1))⁻¹ = (-1 : ℂ) ^ (n + 1) := by
      rcases Nat.even_or_odd (n + 1) with hE | hO
      · simp [hE.neg_one_pow]
      · simp [hO.neg_one_pow]
    rw [mul_inv, mul_inv, hneg1_inv]
    ring
  have hden_ne : ∏ k ∈ Finset.range (n + 1), (1 - q ^ k * T) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro k hk
    exact sub_ne_zero.mpr (hpoles k hk).symm
  -- Combine numerator and denominator
  set b := (primitiveFermatTuples F n d).card
  set ε : ℂ := εP * (-1 : ℂ) ^ (n + 1)
  have hε : ε = 1 ∨ ε = -1 := by
    rcases Nat.even_or_odd (n + 1) with hE | hO
    · rcases hεP with rfl | rfl
      · left; simp [ε, hE.neg_one_pow]
      · right; simp [ε, hE.neg_one_pow]
    · rcases hεP with rfl | rfl
      · right; simp [ε, hO.neg_one_pow]
      · left; simp [ε, hO.neg_one_pow]
  have hεP_zpow : εP ^ ((-1 : ℤ) ^ (n + 1)) = εP := by
    rcases Nat.even_or_odd (n + 1) with hE | hO
    · rw [hE.neg_one_pow, zpow_one]
    · rw [hO.neg_one_pow, zpow_neg_one]
      rcases hεP with rfl | rfl <;> norm_num
  have hneg1_div : ((-1 : ℂ) ^ (n + 1))⁻¹ = (-1 : ℂ) ^ (n + 1) := by
    rcases Nat.even_or_odd (n + 1) with hE | hO
    · simp [hE.neg_one_pow]
    · simp [hO.neg_one_pow]
  refine ⟨ε, hε, ?_⟩
  unfold fermatHypersurfaceZetaRat
  change ((fermatHypersurfaceLPoly F n d).eval (1 / (q ^ n * T))) ^ ((-1 : ℤ) ^ (n + 1)) /
      (∏ k ∈ Finset.range (n + 1), (1 - q ^ k * (1 / (q ^ n * T)))) = _
  rw [hfeP, hden]
  rw [mul_zpow, mul_zpow, hεP_zpow, ← zpow_mul]
  have hexp_b : -(b : ℤ) * (-1 : ℤ) ^ (n + 1) = (-1 : ℤ) ^ n * (b : ℤ) := by
    rw [pow_succ]; ring
  rw [hexp_b]
  have hpow_add : (c * T) ^ ((n + 1 : ℤ) + (-1 : ℤ) ^ n * (b : ℤ)) =
      (c * T) ^ (n + 1 : ℤ) * (c * T) ^ ((-1 : ℤ) ^ n * (b : ℤ)) :=
    zpow_add₀ hcT_ne _ _
  have hneg_inv : ((c * T) ^ (-(n + 1 : ℤ)))⁻¹ = (c * T) ^ (n + 1 : ℤ) := by
    rw [zpow_neg, inv_inv]
  rw [hpow_add]
  unfold ε
  have hstep :
      (εP * (c * T) ^ ((-1 : ℤ) ^ n * (b : ℤ)) *
          ((fermatHypersurfaceLPoly F n d).eval T) ^ ((-1 : ℤ) ^ (n + 1))) /
        ((-1 : ℂ) ^ (n + 1) * (c * T) ^ (-(n + 1 : ℤ)) *
          ∏ k ∈ Finset.range (n + 1), (1 - q ^ k * T)) =
      (εP * ((-1 : ℂ) ^ (n + 1))⁻¹) * (((c * T) ^ (-(n + 1 : ℤ)))⁻¹ * (c * T) ^ ((-1 : ℤ) ^ n * (b : ℤ))) *
        (((fermatHypersurfaceLPoly F n d).eval T) ^ ((-1 : ℤ) ^ (n + 1)) /
          ∏ k ∈ Finset.range (n + 1), (1 - q ^ k * T)) := by
    have h1ne : (-1 : ℂ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have h2ne : (c * T) ^ (-(n + 1 : ℤ)) ≠ 0 := zpow_ne_zero _ hcT_ne
    field_simp [h1ne, h2ne, hden_ne]
  rw [hstep, hneg1_div, hneg_inv]

/-- **WEIL CONJECTURE III (RECIPROCAL ROOT NORM FOR `V_d^n / 𝔽_q`)**:
every root `w : ℂ` of `P_n(w) = 0` satisfies `‖w‖ = q ^ (-n / 2)`. -/
theorem fermatHypersurface_weil_root_norm {F : Type*} [Field F] [Fintype F] {n d : ℕ}
    {w : ℂ} (hw : (fermatHypersurfaceLPoly F n d).eval w = 0) :
    ‖w‖ = (Fintype.card F : ℝ) ^ (-((n : ℝ) / 2)) := by
  unfold fermatHypersurfaceLPoly at hw
  rw [Polynomial.eval_prod] at hw
  obtain ⟨χ, hχ, hzero⟩ := Finset.prod_eq_zero_iff.mp hw
  simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] at hzero
  have hmul : fermatHypersurfaceEigenvalue χ * w = 1 := (sub_eq_zero.mp hzero).symm
  have hnorm := congr_arg norm hmul
  rw [norm_mul, norm_one, norm_fermatHypersurfaceEigenvalue_eq_rpow hχ] at hnorm
  rw [eq_inv_of_mul_eq_one_right hnorm, ← Real.rpow_neg (Nat.cast_nonneg _)]

/-- **WEIL CONJECTURE III (THE RIEMANN HYPOTHESIS / DELIGNE PURITY FOR `V_d^n / 𝔽_q`)**:
every zero `s : ℂ` of `P_n(q ^ (-s)) = 0` lies STRICTLY on the critical line
**`s.re = (n : ℝ) / 2`**! -/
theorem fermatHypersurface_weil_riemann_hypothesis {F : Type*} [Field F] [Fintype F] {n d : ℕ}
    {s : ℂ} (hs : (fermatHypersurfaceLPoly F n d).eval ((Fintype.card F : ℂ) ^ (-s)) = 0) :
    s.re = (n : ℝ) / 2 := by
  have hnorm := fermatHypersurface_weil_root_norm hs
  have hq_ge : (2 : ℝ) ≤ (Fintype.card F : ℝ) := by
    exact_mod_cast two_le_card_finiteField (F := F)
  have hq_pos : (0 : ℝ) < (Fintype.card F : ℝ) := by linarith
  have hq_ne1 : (Fintype.card F : ℝ) ≠ 1 := by linarith
  have hlhs : ‖(Fintype.card F : ℂ) ^ (-s)‖ = (Fintype.card F : ℝ) ^ (-s.re) := by
    have h1 := Complex.norm_cpow_eq_rpow_re_of_pos hq_pos (-s)
    simpa [Complex.neg_re] using h1
  rw [hlhs] at hnorm
  have heq : -s.re = -((n : ℝ) / 2) := (Real.rpow_right_inj hq_pos hq_ne1).mp hnorm
  linarith

/-- **UNCONDITIONAL DELIGNE–WEIL POINT-COUNT BOUND FOR `n`-DIMENSIONAL FERMAT HYPERSURFACES**:
`|#V_d^n(𝔽_q) - ∑_{k=0}^n q^k| ≤ b_n^{prim}(d) * q ^ (n / 2)`. -/
theorem fermatHypersurface_deligne_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (n : ℕ) {d : ℕ} (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1) :
    |(fermatHypersurfacePoints F n d : ℝ) -
        ∑ k ∈ Finset.range (n + 1), (Fintype.card F : ℝ) ^ k| ≤
      ((primitiveFermatTuples F n d).card : ℝ) * (Fintype.card F : ℝ) ^ ((n : ℝ) / 2) := by
  have hdiff :
      (((fermatHypersurfacePoints F n d : ℝ) -
          ∑ k ∈ Finset.range (n + 1), (Fintype.card F : ℝ) ^ k : ℝ) : ℂ) =
        (-1 : ℂ) ^ n * ∑ χ ∈ primitiveFermatTuples F n d, fermatHypersurfaceEigenvalue χ := by
    push_cast
    rw [fermatHypersurfacePoints_eq n hd hdvd]
    ring
  calc |(fermatHypersurfacePoints F n d : ℝ) -
          ∑ k ∈ Finset.range (n + 1), (Fintype.card F : ℝ) ^ k|
      = ‖(((fermatHypersurfacePoints F n d : ℝ) -
          ∑ k ∈ Finset.range (n + 1), (Fintype.card F : ℝ) ^ k : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖(-1 : ℂ) ^ n * ∑ χ ∈ primitiveFermatTuples F n d, fermatHypersurfaceEigenvalue χ‖ := by
        rw [hdiff]
    _ = ‖∑ χ ∈ primitiveFermatTuples F n d, fermatHypersurfaceEigenvalue χ‖ := by
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    _ ≤ ∑ χ ∈ primitiveFermatTuples F n d, ‖fermatHypersurfaceEigenvalue χ‖ := norm_sum_le _ _
    _ = ∑ _χ ∈ primitiveFermatTuples F n d, (Fintype.card F : ℝ) ^ ((n : ℝ) / 2) :=
        Finset.sum_congr rfl fun _ hχ => norm_fermatHypersurfaceEigenvalue_eq_rpow hχ
    _ = ((primitiveFermatTuples F n d).card : ℝ) * (Fintype.card F : ℝ) ^ ((n : ℝ) / 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ### Explicit Specialization: Fermat Quartic K3 Surface `X₀⁴ + X₁⁴ + X₂⁴ + X₃⁴ = 0` -/

/-- **FERMAT QUARTIC K3 SURFACE (`n = 2, d = 4`): WEIL RIEMANN HYPOTHESIS (`Re(s) = 1`)**:
every zero `s : ℂ` of `P_2(q^{-s}) = 0` for `X_0^4 + X_1^4 + X_2^4 + X_3^4 = 0` has `s.re = 1`,
every root `w` of `P_2(w) = 0` has `‖w‖ = q⁻¹`, and `deg P_2 = b_2^{prim} = 21` (total `b_2 = 22`,
Euler characteristic `χ = 24`)! -/
theorem fermat_k3_surface_weil_rh {F : Type*} [Field F] [Fintype F]
    (h4 : 4 ∣ Fintype.card F - 1) :
    (fermatHypersurfaceLPoly F 2 4).natDegree = 21 ∧
    (∀ w : ℂ, (fermatHypersurfaceLPoly F 2 4).eval w = 0 →
      ‖w‖ = (Fintype.card F : ℝ)⁻¹) ∧
    (∀ s : ℂ, (fermatHypersurfaceLPoly F 2 4).eval ((Fintype.card F : ℂ) ^ (-s)) = 0 →
      s.re = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [natDegree_fermatHypersurfaceLPoly, card_primitiveFermatTuples_k3 h4]
  · intro w hw
    have h := fermatHypersurface_weil_root_norm hw
    simpa [Real.rpow_neg_one] using h
  · intro s hs
    have h := fermatHypersurface_weil_riemann_hypothesis hs
    norm_num at h
    exact h

/-- **FERMAT QUARTIC K3 SURFACE (`n = 2, d = 4`): UNCONDITIONAL DELIGNE–WEIL POINT BOUND**:
`|#S(𝔽_q) - (q² + q + 1)| ≤ 21 q` for every finite field `𝔽_q` with `4 ∣ (q - 1)`! -/
theorem fermat_k3_surface_point_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (h4 : 4 ∣ Fintype.card F - 1) :
    |(fermatHypersurfacePoints F 2 4 : ℝ) -
        ((Fintype.card F : ℝ) ^ 2 + (Fintype.card F : ℝ) + 1)| ≤
      21 * (Fintype.card F : ℝ) := by
  have h := fermatHypersurface_deligne_bound (F := F) 2 (by omega) h4
  rw [card_primitiveFermatTuples_k3 h4] at h
  have hsum : ∑ k ∈ Finset.range 3, (Fintype.card F : ℝ) ^ k =
      (Fintype.card F : ℝ) ^ 2 + (Fintype.card F : ℝ) + 1 := by
    simp [Finset.sum_range_succ]; ring
  have hrpow : (Fintype.card F : ℝ) ^ (((2 : ℕ) : ℝ) / 2) = (Fintype.card F : ℝ) := by
    norm_num
  rw [hsum, hrpow] at h
  exact_mod_cast h

end FermatHypersurface

/-! ## Section 3: Unconditional Hasse–Weil Bound for CM Elliptic Curves (`y² = x³ - x`, `y² = x³ + 1`) -/

section CMEllipticCurves

/-- Projective point count `#E₁(𝔽_q) = 1 + #{(x, y) ∈ F² | y² = x³ - x}` for the CM elliptic
curve `E₁ : y² = x³ - x` (CM by `ℤ[i]`, `j = 1728`). -/
def cmCurve1Points (F : Type*) [Field F] [Fintype F] [DecidableEq F] : ℕ :=
  1 + (Finset.univ.filter fun p : F × F => p.2 ^ 2 = p.1 ^ 3 - p.1).card

/-- Projective point count `#E₂(𝔽_q) = 1 + #{(x, y) ∈ F² | y² = x³ + 1}` for the CM elliptic
curve `E₂ : y² = x³ + 1` (CM by `ℤ[ω]`, `j = 0`). -/
def cmCurve2Points (F : Type*) [Field F] [Fintype F] [DecidableEq F] : ℕ :=
  1 + (Finset.univ.filter fun p : F × F => p.2 ^ 2 = p.1 ^ 3 + 1).card

/-- Existence of a unique nontrivial quadratic character `η` on `F` when `2 ∣ (q - 1)`,
with `∀ χ, χ ∈ powCharSet F 2 ↔ χ = 1 ∨ χ = η` and `η ^ 2 = 1`. -/
private lemma exists_quadChar {F : Type*} [Field F] [Fintype F]
    (h2 : 2 ∣ Fintype.card F - 1) :
    ∃ η : MulChar F ℂ, η ≠ 1 ∧ η ^ 2 = 1 ∧ ∀ χ : MulChar F ℂ, χ ∈ powCharSet F 2 ↔ χ = 1 ∨ χ = η := by
  classical
  have hcard : (powCharSet F 2).card = 2 := card_powCharSet (by omega) h2
  have h1 : (1 : MulChar F ℂ) ∈ powCharSet F 2 := one_mem_powCharSet F 2
  have herase_card : ((powCharSet F 2).erase 1).card = 1 := by
    rw [Finset.card_erase_of_mem h1, hcard]
  obtain ⟨η, hη_eq⟩ := Finset.card_eq_one.mp herase_card
  have hη_mem : η ∈ (powCharSet F 2).erase 1 := by rw [hη_eq]; exact Finset.mem_singleton_self η
  rw [Finset.mem_erase, mem_powCharSet] at hη_mem
  refine ⟨η, hη_mem.1, hη_mem.2, fun χ => ?_⟩
  constructor
  · intro hχ
    by_cases hχ1 : χ = 1
    · exact Or.inl hχ1
    · have : χ ∈ (powCharSet F 2).erase 1 := Finset.mem_erase.mpr ⟨hχ1, hχ⟩
      rw [hη_eq, Finset.mem_singleton] at this
      exact Or.inr this
  · rintro (rfl | rfl)
    · exact h1
    · exact mem_powCharSet.mpr hη_mem.2

/-- Exact value of `η (-1)` for the quadratic character `η`:
`η (-1) = (-1 : ℂ) ^ ((Fintype.card F - 1) / 2)` whenever `2 ∣ (q - 1)`. -/
private lemma quadChar_neg_one {F : Type*} [Field F] [Fintype F]
    (h2 : 2 ∣ Fintype.card F - 1) {η : MulChar F ℂ} (hη : η ≠ 1) (hη2 : η ^ 2 = 1) :
    η (-1) = (-1 : ℂ) ^ ((Fintype.card F - 1) / 2) := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  set m := Fintype.card F - 1
  have hm_eq : Fintype.card Fˣ = m := Fintype.card_units F
  have hord : orderOf g = m := by
    rw [← hm_eq, orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  -- `η (g : F) = -1`
  have hηg_sq : (η (g : F)) ^ 2 = 1 := by
    rw [← MulChar.pow_apply_coe, hη2, MulChar.one_apply g.isUnit]
  have hηg_ne1 : η (g : F) ≠ 1 := by
    intro h1
    apply hη
    ext x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    have hx : (x : F) = (g : F) ^ k := by
      have := congr_arg (Units.val : Fˣ → F) hk
      simpa using this.symm
    have hη_ginv : η ((g : F)⁻¹) = (η (g : F))⁻¹ := by
      have hmul : η ((g : F)⁻¹) * η (g : F) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ g.ne_zero, map_one]
      exact eq_inv_of_mul_eq_one_left hmul
    have hpow : η ((g : F) ^ k) = (η (g : F)) ^ k := by
      cases k with
      | ofNat n => simp [map_pow]
      | negSucc n =>
        rw [zpow_negSucc, zpow_negSucc, ← inv_pow, map_pow, hη_ginv, inv_pow]
    rw [MulChar.one_apply x.isUnit, hx, hpow, h1, one_zpow]
  have hηg : η (g : F) = -1 := by
    have hfac : (η (g : F) - 1) * (η (g : F) + 1) = 0 := by linear_combination hηg_sq
    rcases mul_eq_zero.mp hfac with h1 | h2
    · exact absurd (sub_eq_zero.mp h1) hηg_ne1
    · linear_combination h2
  -- Show `(g : F) ^ (m / 2) = -1`
  have hdiv2 : m / 2 * 2 = m := Nat.div_mul_cancel h2
  have hgm_sq : ((g : F) ^ (m / 2)) ^ 2 = 1 := by
    rw [← pow_mul, hdiv2]
    have := congr_arg (Units.val : Fˣ → F) (hord ▸ pow_orderOf_eq_one g)
    simpa using this
  have hgm_ne1 : (g : F) ^ (m / 2) ≠ 1 := by
    intro h1
    have hu : g ^ (m / 2) = 1 := Units.ext (by simpa using h1)
    have hdvd : orderOf g ∣ m / 2 := orderOf_dvd_of_pow_eq_one hu
    rw [hord] at hdvd
    have hm_pos : 0 < m := hm_eq ▸ Fintype.card_pos
    have hle := Nat.le_of_dvd (by omega) hdvd
    omega
  have hgm_eq : (g : F) ^ (m / 2) = -1 := by
    have hfac : ((g : F) ^ (m / 2) - 1) * ((g : F) ^ (m / 2) + 1) = 0 := by
      linear_combination hgm_sq
    rcases mul_eq_zero.mp hfac with h1 | h2
    · exact absurd (sub_eq_zero.mp h1) hgm_ne1
    · linear_combination h2
  rw [← hgm_eq, map_pow, hηg]

/-- For every finite field `F` with `2 ∣ (q - 1)` and nontrivial quadratic character `η`,
`#{y : F | y ^ 2 = u} = 1 + η u` for ALL `u : F` (including `u = 0`). -/
private lemma card_sq_eq_one_add_quadChar {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (h2 : 2 ∣ Fintype.card F - 1) {η : MulChar F ℂ} (hη : η ≠ 1)
    (hset : ∀ χ : MulChar F ℂ, χ ∈ powCharSet F 2 ↔ χ = 1 ∨ χ = η) (u : F) :
    ((Finset.univ.filter fun y : F => y ^ 2 = u).card : ℂ) = 1 + η u := by
  classical
  have hfinset : powCharSet F 2 = {1, η} := by
    ext χ; simp [hset]
  rw [card_pow_eq_sum_powCharSet_all (by omega : 1 ≤ 2) h2 u, hfinset,
    Finset.sum_pair hη.symm]
  by_cases hu : u = 0
  · subst hu
    rw [if_pos rfl, (1 : MulChar F ℂ).map_nonunit not_isUnit_zero, zero_add]
  · rw [if_neg hu, zero_add, MulChar.one_apply (isUnit_iff_ne_zero.mpr hu)]

/-- Generic Weierstrass point-counting identity: for any `f : F → F` and quadratic character `η`
(when `2 ∣ q - 1`), `1 + #{(x, y) | y^2 = f x} = q + 1 + ∑ x : F, η (f x)`. -/
private lemma weierstrass_points_eq_sum_quadChar {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (h2 : 2 ∣ Fintype.card F - 1) {η : MulChar F ℂ} (hη : η ≠ 1)
    (hset : ∀ χ : MulChar F ℂ, χ ∈ powCharSet F 2 ↔ χ = 1 ∨ χ = η) (f : F → F) :
    ((1 + (Finset.univ.filter fun p : F × F => p.2 ^ 2 = f p.1).card : ℕ) : ℂ) =
      (Fintype.card F : ℂ) + 1 + ∑ x : F, η (f x) := by
  have hfib : (Finset.univ.filter fun p : F × F => p.2 ^ 2 = f p.1).card =
      ∑ x : F, (Finset.univ.filter fun y : F => y ^ 2 = f x).card := by
    rw [Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter fun p : F × F => p.2 ^ 2 = f p.1)
      (f := Prod.fst) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun x _ => ?_
    refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      rw [← hp.2]; exact hp.1
    · intro p₁ hp₁ p₂ hp₂ h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
      exact Prod.ext (hp₁.2.trans hp₂.2.symm) h
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      exact ⟨(x, y), by simp [hy], rfl⟩
  rw [Nat.cast_add, Nat.cast_one, hfib, Nat.cast_sum]
  simp_rw [card_sq_eq_one_add_quadChar h2 hη hset, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  ring

/-- Existence of a quartic character `χ` of exact order `4` with `χ ^ 2 = η` when `4 ∣ (q - 1)`. -/
private lemma exists_order4Char {F : Type*} [Field F] [Fintype F]
    (h4 : 4 ∣ Fintype.card F - 1) {η : MulChar F ℂ}
    (hset2 : ∀ χ : MulChar F ℂ, χ ∈ powCharSet F 2 ↔ χ = 1 ∨ χ = η) :
    ∃ χ : MulChar F ℂ, χ ^ 2 = η ∧ χ ≠ 1 ∧ χ * η = χ⁻¹ ∧ χ * η ≠ 1 ∧ χ⁻¹ * η ≠ 1 := by
  classical
  have hcard4 : (powCharSet F 4).card = 4 := card_powCharSet (by omega) h4
  have hsub : powCharSet F 2 ⊆ powCharSet F 4 := by
    intro ψ hψ
    rw [mem_powCharSet] at hψ ⊢
    calc ψ ^ 4 = (ψ ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 ^ 2 := by rw [hψ]
      _ = 1 := one_pow 2
  have hdiff_ne : (powCharSet F 4 \ powCharSet F 2).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset hsub, hcard4,
      card_powCharSet (by omega) (dvd_trans (by decide : 2 ∣ 4) h4)]
    omega
  obtain ⟨χ, hχ⟩ := hdiff_ne
  rw [Finset.mem_sdiff, mem_powCharSet, mem_powCharSet] at hχ
  have hχ2_mem : χ ^ 2 ∈ powCharSet F 2 := by
    rw [mem_powCharSet, ← pow_mul]
    exact hχ.1
  have hχ2_eq : χ ^ 2 = η := ((hset2 (χ ^ 2)).mp hχ2_mem).resolve_left hχ.2
  have hχ_ne1 : χ ≠ 1 := fun h1 => hχ.2 (by rw [h1, one_pow])
  have hη2 : η ^ 2 = 1 := mem_powCharSet.mp ((hset2 η).mpr (Or.inr rfl))
  have hχη : χ * η = χ⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    calc χ * (χ * η) = (χ * χ) * η := (mul_assoc χ χ η).symm
      _ = χ ^ 2 * η := by rw [sq]
      _ = η * η := by rw [hχ2_eq]
      _ = η ^ 2 := (sq η).symm
      _ = 1 := hη2
  have hχinv_η : χ⁻¹ * η = χ := by
    calc χ⁻¹ * η = χ⁻¹ * χ ^ 2 := by rw [hχ2_eq]
      _ = χ⁻¹ * (χ * χ) := by rw [sq]
      _ = (χ⁻¹ * χ) * χ := (mul_assoc χ⁻¹ χ χ).symm
      _ = 1 * χ := by rw [inv_mul_cancel]
      _ = χ := one_mul χ
  exact ⟨χ, hχ2_eq, hχ_ne1, hχη, by rw [hχη]; exact inv_ne_one.mpr hχ_ne1,
    by rw [hχinv_η]; exact hχ_ne1⟩

/-- **EXACT JACOBI-SUM POINT COUNT FOR `E₁ : y² = x³ - x` (`q ≡ 1 [MOD 4]`)**:
there exist a quartic character `χ` and quadratic character `η` (`χ ≠ 1, η ≠ 1, χ * η ≠ 1, χ⁻¹ * η ≠ 1`)
such that `#E₁(𝔽_q) = q + 1 + J(χ, η) + J(χ⁻¹, η)`! -/
theorem cmCurve1_eq_sum_jacobiSum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (h4 : 4 ∣ Fintype.card F - 1) :
    ∃ χ η : MulChar F ℂ,
      χ ≠ 1 ∧ η ≠ 1 ∧ χ * η ≠ 1 ∧ χ⁻¹ * η ≠ 1 ∧
        (cmCurve1Points F : ℂ) =
          (Fintype.card F : ℂ) + 1 + jacobiSum χ η + jacobiSum χ⁻¹ η := by
  have h2 : 2 ∣ Fintype.card F - 1 := dvd_trans (by decide : 2 ∣ 4) h4
  obtain ⟨η, hη, hη2, hset2⟩ := exists_quadChar (F := F) h2
  obtain ⟨χ, hχ2, hχ_ne1, hχη, hχη_ne1, hχinv_η_ne1⟩ := exists_order4Char h4 hset2
  refine ⟨χ, η, hχ_ne1, hη, hχη_ne1, hχinv_η_ne1, ?_⟩
  unfold cmCurve1Points
  rw [weierstrass_points_eq_sum_quadChar h2 hη hset2 (fun x => x ^ 3 - x)]
  -- Since `4 ∣ q - 1`, `(q - 1) / 2` is even, so `η (-1) = 1`
  have hη_neg1 : η (-1) = 1 := by
    rw [quadChar_neg_one h2 hη hη2]
    obtain ⟨k, hk⟩ := h4
    have hdiv : (Fintype.card F - 1) / 2 = 2 * k := by omega
    rw [hdiv, pow_mul]
    norm_num
  -- Rewrite `η (x^3 - x) = χ (x^2) * η (x^2 - 1)` and group by `u = x^2`
  have hrew : ∀ x : F, η (x ^ 3 - x) = χ (x ^ 2) * η (x ^ 2 - 1) := by
    intro x
    have hfac : x ^ 3 - x = x * (x ^ 2 - 1) := by ring
    rw [hfac, map_mul]
    congr 1
    rw [← hχ2, sq, MulChar.mul_apply, ← map_mul, ← sq]
  simp_rw [hrew]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun x : F => x ^ 2) (fun _ _ => Finset.mem_univ _)]
  have hfiber : ∀ u : F,
      ∑ x ∈ Finset.univ.filter (fun x : F => x ^ 2 = u), χ (x ^ 2) * η (x ^ 2 - 1) =
        (1 + η u) * (χ u * η (u - 1)) := by
    intro u
    have hcongr : ∑ x ∈ Finset.univ.filter (fun x : F => x ^ 2 = u), χ (x ^ 2) * η (x ^ 2 - 1) =
        ∑ _x ∈ Finset.univ.filter (fun x : F => x ^ 2 = u), (χ u * η (u - 1)) :=
      Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2]
    rw [hcongr, Finset.sum_const, nsmul_eq_mul, card_sq_eq_one_add_quadChar h2 hη hset2 u]
  simp_rw [hfiber]
  have hη_sub : ∀ u : F, η (u - 1) = η (1 - u) := by
    intro u
    have hneg : u - 1 = (-1 : F) * (1 - u) := by ring
    rw [hneg, map_mul, hη_neg1, one_mul]
  have hsplit : ∑ u : F, (1 + η u) * (χ u * η (u - 1)) =
      jacobiSum χ η + jacobiSum χ⁻¹ η := by
    have hterm : ∀ u : F, (1 + η u) * (χ u * η (u - 1)) =
        χ u * η (1 - u) + χ⁻¹ u * η (1 - u) := by
      intro u
      rw [hη_sub u, ← hχη, MulChar.mul_apply]
      ring
    simp_rw [hterm, Finset.sum_add_distrib]
    rfl
  rw [hsplit]
  ring

/-- **EXACT SUPERSINGULAR POINT COUNT FOR `E₁ : y² = x³ - x` (`q ≡ 3 [MOD 4]`)**:
`#E₁(𝔽_q) = q + 1` EXACTLY whenever `Fintype.card F % 4 = 3`! -/
theorem cmCurve1_supersingular {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (h3 : Fintype.card F % 4 = 3) :
    cmCurve1Points F = Fintype.card F + 1 := by
  have h2 : 2 ∣ Fintype.card F - 1 := by omega
  obtain ⟨η, hη, hη2, hset2⟩ := exists_quadChar (F := F) h2
  have hη_neg1 : η (-1) = -1 := by
    rw [quadChar_neg_one h2 hη hη2]
    have hodd : Odd ((Fintype.card F - 1) / 2) := ⟨(Fintype.card F - 3) / 4, by omega⟩
    exact hodd.neg_one_pow
  have hS0 : ∑ x : F, η (x ^ 3 - x) = 0 := by
    have hneg : ∑ x : F, η (x ^ 3 - x) = -∑ x : F, η (x ^ 3 - x) := by
      calc ∑ x : F, η (x ^ 3 - x)
          = ∑ x : F, η ((-x) ^ 3 - (-x)) := by
              refine Finset.sum_bij (fun x _ => -x) (fun _ _ => Finset.mem_univ _)
                (fun _ _ _ _ h => neg_inj.mp h) (fun y _ => ⟨-y, Finset.mem_univ _, neg_neg y⟩)
                (fun x _ => by simp)
        _ = ∑ x : F, η ((-1 : F) * (x ^ 3 - x)) := by
              refine Finset.sum_congr rfl fun x _ => by congr 1; ring
        _ = ∑ x : F, (η (-1) * η (x ^ 3 - x)) := by
              refine Finset.sum_congr rfl fun x _ => map_mul η (-1) (x ^ 3 - x)
        _ = -∑ x : F, η (x ^ 3 - x) := by
              rw [hη_neg1, ← Finset.mul_sum]; ring
    have h2S : (2 : ℂ) * ∑ x : F, η (x ^ 3 - x) = 0 := by linear_combination hneg
    exact (mul_eq_zero.mp h2S).resolve_left (by norm_num)
  have hC : (cmCurve1Points F : ℂ) = (Fintype.card F : ℂ) + 1 := by
    unfold cmCurve1Points
    rw [weierstrass_points_eq_sum_quadChar h2 hη hset2 (fun x => x ^ 3 - x), hS0, add_zero]
  exact_mod_cast hC

/-- **UNCONDITIONAL HASSE–WEIL BOUND FOR `E₁ : y² = x³ - x` (ALL ODD `q`)**:
`|#E₁(𝔽_q) - (q + 1)| ≤ 2 √q` for every finite field `𝔽_q` of odd cardinality! -/
theorem cmCurve1_hasse_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (h2 : 2 ∣ Fintype.card F - 1) :
    |(cmCurve1Points F : ℝ) - ((Fintype.card F : ℝ) + 1)| ≤
      2 * Real.sqrt (Fintype.card F : ℝ) := by
  have hq2 : 2 ≤ Fintype.card F := two_le_card_finiteField (F := F)
  obtain ⟨k, hk⟩ := h2
  have hmod : Fintype.card F % 4 = 1 ∨ Fintype.card F % 4 = 3 := by omega
  rcases hmod with h1 | h3
  · have h4 : 4 ∣ Fintype.card F - 1 := by omega
    obtain ⟨χ, η, hχ, hη, hχη, hχiη, heq⟩ := cmCurve1_eq_sum_jacobiSum (F := F) h4
    have hdiff : (((cmCurve1Points F : ℝ) - ((Fintype.card F : ℝ) + 1) : ℝ) : ℂ) =
        jacobiSum χ η + jacobiSum χ⁻¹ η := by
      push_cast; rw [heq]; ring
    calc |(cmCurve1Points F : ℝ) - ((Fintype.card F : ℝ) + 1)|
        = ‖(((cmCurve1Points F : ℝ) - ((Fintype.card F : ℝ) + 1) : ℝ) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs]
      _ = ‖jacobiSum χ η + jacobiSum χ⁻¹ η‖ := by rw [hdiff]
      _ ≤ ‖jacobiSum χ η‖ + ‖jacobiSum χ⁻¹ η‖ := norm_add_le _ _
      _ = Real.sqrt (Fintype.card F : ℝ) + Real.sqrt (Fintype.card F : ℝ) := by
            rw [norm_jacobiSum_eq_sqrt hχ hη hχη,
              norm_jacobiSum_eq_sqrt (inv_ne_one.mpr hχ) hη hχiη]
      _ = 2 * Real.sqrt (Fintype.card F : ℝ) := by ring
  · rw [cmCurve1_supersingular h3]
    push_cast
    rw [sub_self, abs_zero]
    positivity

/-- Helper: when `Nat.Coprime k (Fintype.card F - 1)`, the `k`-th power map `x ↦ x ^ k` on `F`
is bijective. -/
private lemma pow_bijective_of_coprime {F : Type*} [Field F] [Fintype F]
    {k : ℕ} (hk : 1 ≤ k) (hcop : Nat.Coprime k (Fintype.card F - 1)) :
    Function.Bijective (fun x : F => x ^ k) := by
  classical
  refine (Finite.injective_iff_bijective (f := fun x : F => x ^ k)).mp ?_
  intro x y hxy
  dsimp only at hxy
  by_cases hy : y = 0
  · subst hy
    rw [zero_pow (by omega : k ≠ 0)] at hxy
    exact (pow_eq_zero_iff (by omega : k ≠ 0)).mp hxy
  · have hx : x ≠ 0 := by
      intro h0; subst h0; rw [zero_pow (by omega : k ≠ 0)] at hxy
      exact hy ((pow_eq_zero_iff (by omega : k ≠ 0)).mp hxy.symm)
    let u : Fˣ := Units.mk0 (x * y⁻¹) (mul_ne_zero hx (inv_ne_zero hy))
    have hu_k : u ^ k = 1 := by
      apply Units.ext
      change (x * y⁻¹) ^ k = 1
      rw [mul_pow, inv_pow, hxy, mul_inv_cancel₀ (pow_ne_zero k hy)]
    have hu_m : u ^ (Fintype.card F - 1) = 1 := by
      rw [← Fintype.card_units F]; exact pow_card_eq_one
    have hord1 : orderOf u ∣ k := orderOf_dvd_of_pow_eq_one hu_k
    have hord2 : orderOf u ∣ Fintype.card F - 1 := orderOf_dvd_of_pow_eq_one hu_m
    have hord_dvd1 : orderOf u ∣ 1 := hcop ▸ Nat.dvd_gcd hord1 hord2
    have hu1 : u = 1 := by
      rw [← pow_one u, ← Nat.dvd_one.mp hord_dvd1, pow_orderOf_eq_one]
    have hval : x * y⁻¹ = 1 := congr_arg Units.val hu1
    calc x = (x * y⁻¹) * y := by rw [mul_assoc, inv_mul_cancel₀ hy, mul_one]
      _ = 1 * y := by rw [hval]
      _ = y := one_mul y

/-- Existence of a cubic character `ψ` of exact order `3` with `∀ χ, χ ∈ powCharSet F 3 ↔ χ = 1 ∨ χ = ψ ∨ χ = ψ⁻¹`
whenever `3 ∣ (q - 1)`. -/
private lemma exists_order3Char {F : Type*} [Field F] [Fintype F]
    (h3 : 3 ∣ Fintype.card F - 1) :
    ∃ ψ : MulChar F ℂ, ψ ≠ 1 ∧ ψ ^ 3 = 1 ∧ ψ⁻¹ ≠ ψ ∧
      ∀ χ : MulChar F ℂ, χ ∈ powCharSet F 3 ↔ χ = 1 ∨ χ = ψ ∨ χ = ψ⁻¹ := by
  classical
  have hcard3 : (powCharSet F 3).card = 3 := card_powCharSet (by omega) h3
  have h1 : (1 : MulChar F ℂ) ∈ powCharSet F 3 := one_mem_powCharSet F 3
  have herase_ne : ((powCharSet F 3).erase 1).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem h1, hcard3]
    omega
  obtain ⟨ψ, hψ⟩ := herase_ne
  rw [Finset.mem_erase, mem_powCharSet] at hψ
  have hψinv_ne : ψ⁻¹ ≠ ψ := by
    intro heq
    have hsq : ψ ^ 2 = 1 := by
      calc ψ ^ 2 = ψ * ψ := sq ψ
        _ = ψ⁻¹ * ψ := by rw [heq]
        _ = 1 := inv_mul_cancel ψ
    apply hψ.1
    calc ψ = 1 * ψ := (one_mul ψ).symm
      _ = ψ ^ 2 * ψ := by rw [hsq]
      _ = ψ ^ 3 := (pow_succ ψ 2).symm
      _ = 1 := hψ.2
  have hsub : ({1, ψ, ψ⁻¹} : Finset (MulChar F ℂ)) ⊆ powCharSet F 3 := by
    intro χ hχ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hχ
    rcases hχ with rfl | rfl | rfl
    · exact h1
    · exact mem_powCharSet.mpr hψ.2
    · exact inv_mem_powCharSet (mem_powCharSet.mpr hψ.2)
  have hcard_triple : ({1, ψ, ψ⁻¹} : Finset (MulChar F ℂ)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hψinv_ne.symm]
    simp [hψ.1.symm, (inv_ne_one.mpr hψ.1).symm]
  have hset : powCharSet F 3 = {1, ψ, ψ⁻¹} :=
    (Finset.eq_of_subset_of_card_le hsub (by rw [hcard3, hcard_triple])).symm
  refine ⟨ψ, hψ.1, hψ.2, hψinv_ne, fun χ => ?_⟩
  rw [hset]
  simp

/-- **EXACT JACOBI-SUM POINT COUNT FOR `E₂ : y² = x³ + 1` (`q ≡ 1 [MOD 6]`)**:
there exist a cubic character `ψ` and quadratic character `η` (`ψ ≠ 1, η ≠ 1, ψ * η ≠ 1, ψ⁻¹ * η ≠ 1`)
such that `#E₂(𝔽_q) = q + 1 + J(ψ, η) + J(ψ⁻¹, η)`! -/
theorem cmCurve2_eq_sum_jacobiSum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (h6 : 6 ∣ Fintype.card F - 1) :
    ∃ ψ η : MulChar F ℂ,
      ψ ≠ 1 ∧ η ≠ 1 ∧ ψ * η ≠ 1 ∧ ψ⁻¹ * η ≠ 1 ∧
        (cmCurve2Points F : ℂ) =
          (Fintype.card F : ℂ) + 1 + jacobiSum ψ η + jacobiSum ψ⁻¹ η := by
  classical
  have h2 : 2 ∣ Fintype.card F - 1 := dvd_trans (by decide : 2 ∣ 6) h6
  have h3 : 3 ∣ Fintype.card F - 1 := dvd_trans (by decide : 3 ∣ 6) h6
  obtain ⟨η, hη, hη2, hset2⟩ := exists_quadChar (F := F) h2
  obtain ⟨ψ, hψ, hψ3, hψinv_ne, hset3⟩ := exists_order3Char (F := F) h3
  have hψη_ne1 : ψ * η ≠ 1 := by
    intro h1
    have hpe : ψ = η⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hsq : ψ ^ 2 = 1 := by rw [hpe, inv_pow, hη2, inv_one]
    apply hψ
    calc ψ = 1 * ψ := (one_mul ψ).symm
      _ = ψ ^ 2 * ψ := by rw [hsq]
      _ = ψ ^ 3 := (pow_succ ψ 2).symm
      _ = 1 := hψ3
  have hψinv_η_ne1 : ψ⁻¹ * η ≠ 1 := by
    intro h1
    have hpe : ψ⁻¹ = η⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hsq : ψ ^ 2 = 1 := by
      have : ψ = η := inv_inj.mp hpe
      rw [this, hη2]
    apply hψ
    calc ψ = 1 * ψ := (one_mul ψ).symm
      _ = ψ ^ 2 * ψ := by rw [hsq]
      _ = ψ ^ 3 := (pow_succ ψ 2).symm
      _ = 1 := hψ3
  refine ⟨ψ, η, hψ, hη, hψη_ne1, hψinv_η_ne1, ?_⟩
  -- For any cubic character `ψ`, `ψ (-1) = 1`
  have hψ_neg1 : ψ (-1) = 1 := by
    have hsq : ψ (-1) ^ 2 = 1 := by
      rw [← map_pow]; norm_num
    have hcu : ψ (-1) ^ 3 = 1 := by
      calc ψ (-1) ^ 3 = ψ (-1) ^ 2 * ψ (-1) := pow_succ (ψ (-1)) 2
        _ = (ψ (-1) * ψ (-1)) * ψ (-1) := by rw [sq]
        _ = (ψ * ψ) (-1) * ψ (-1) := by rw [MulChar.mul_apply]
        _ = (ψ * ψ * ψ) (-1) := (MulChar.mul_apply (ψ * ψ) ψ (-1)).symm
        _ = (ψ ^ 3) (-1) := by rw [← sq, ← pow_succ]
        _ = 1 := by
          rw [hψ3, MulChar.one_apply (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr (one_ne_zero (α := F))))]
    calc ψ (-1) = 1 * ψ (-1) := (one_mul _).symm
      _ = ψ (-1) ^ 2 * ψ (-1) := by rw [hsq]
      _ = ψ (-1) ^ 3 := by ring
      _ = 1 := hcu
  -- Exact cube count: `#{x : F | x ^ 3 = u} = 1 + ψ u + ψ⁻¹ u` for ALL `u : F`
  have hfinset3 : powCharSet F 3 = {1, ψ, ψ⁻¹} := by
    ext χ; simp [hset3]
  have hcube : ∀ u : F,
      ((Finset.univ.filter fun x : F => x ^ 3 = u).card : ℂ) = 1 + ψ u + ψ⁻¹ u := by
    intro u
    rw [card_pow_eq_sum_powCharSet_all (by omega : 1 ≤ 3) h3 u, hfinset3]
    rw [Finset.sum_insert (by simp [hψ.symm, (inv_ne_one.mpr hψ).symm]),
      Finset.sum_pair hψinv_ne.symm]
    by_cases hu : u = 0
    · subst hu
      rw [if_pos rfl, (1 : MulChar F ℂ).map_nonunit not_isUnit_zero]
      ring
    · rw [if_neg hu, zero_add, MulChar.one_apply (isUnit_iff_ne_zero.mpr hu)]
      ring
  unfold cmCurve2Points
  rw [weierstrass_points_eq_sum_quadChar h2 hη hset2 (fun x => x ^ 3 + 1)]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun x : F => x ^ 3) (fun _ _ => Finset.mem_univ _)]
  have hfiber : ∀ u : F,
      ∑ x ∈ Finset.univ.filter (fun x : F => x ^ 3 = u), η (x ^ 3 + 1) =
        (1 + ψ u + ψ⁻¹ u) * η (u + 1) := by
    intro u
    have hcongr : ∑ x ∈ Finset.univ.filter (fun x : F => x ^ 3 = u), η (x ^ 3 + 1) =
        ∑ _x ∈ Finset.univ.filter (fun x : F => x ^ 3 = u), η (u + 1) :=
      Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2]
    rw [hcongr, Finset.sum_const, nsmul_eq_mul, hcube u]
  simp_rw [hfiber]
  have hsum_η : ∑ u : F, η (u + 1) = 0 := by
    have hshift : ∑ u : F, η (u + 1) = ∑ v : F, η v :=
      Finset.sum_bij (fun u _ => u + 1) (fun _ _ => Finset.mem_univ _)
        (fun _ _ _ _ h => add_right_cancel h) (fun v _ => ⟨v - 1, Finset.mem_univ _, sub_add_cancel v 1⟩)
        (fun _ _ => rfl)
    rw [hshift]
    exact MulChar.sum_eq_zero_of_ne_one hη
  have hsum_jac : ∀ χ : MulChar F ℂ, χ (-1) = 1 →
      ∑ u : F, χ u * η (u + 1) = jacobiSum χ η := by
    intro χ hχ_neg1
    unfold jacobiSum
    refine Finset.sum_bij (fun u _ => -u) (fun _ _ => Finset.mem_univ _)
      (fun _ _ _ _ h => neg_inj.mp h) (fun t _ => ⟨-t, Finset.mem_univ _, neg_neg t⟩) ?_
    intro u _
    have h1 : (-u : F) = (-1 : F) * u := by ring
    have h2' : 1 - (-u : F) = u + 1 := by ring
    rw [h2', h1, map_mul, hχ_neg1, one_mul]
  have hsplit : ∑ u : F, (1 + ψ u + ψ⁻¹ u) * η (u + 1) =
      jacobiSum ψ η + jacobiSum ψ⁻¹ η := by
    have hterm : ∀ u : F, (1 + ψ u + ψ⁻¹ u) * η (u + 1) =
        η (u + 1) + ψ u * η (u + 1) + ψ⁻¹ u * η (u + 1) := fun _ => by ring
    simp_rw [hterm, Finset.sum_add_distrib]
    rw [hsum_η, zero_add, hsum_jac ψ hψ_neg1,
      hsum_jac ψ⁻¹ (by rw [mulChar_inv_neg_one, hψ_neg1])]
  rw [hsplit]
  ring

/-- **EXACT SUPERSINGULAR POINT COUNT FOR `E₂ : y² = x³ + 1` (`q ≡ 2 [MOD 3]`)**:
`#E₂(𝔽_q) = q + 1` EXACTLY for EVERY finite field `F` with `Fintype.card F % 3 = 2`! -/
theorem cmCurve2_supersingular {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (h2mod3 : Fintype.card F % 3 = 2) :
    cmCurve2Points F = Fintype.card F + 1 := by
  by_cases h2 : 2 ∣ Fintype.card F - 1
  · -- Odd `q`: `x ↦ x ^ 3` is bijective since `gcd(3, q - 1) = 1`, so `∑ η(x^3 + 1) = ∑ η(v) = 0`
    obtain ⟨η, hη, _, hset2⟩ := exists_quadChar (F := F) h2
    have hcop : Nat.Coprime 3 (Fintype.card F - 1) := by
      have hrem : (Fintype.card F - 1) % 3 = 1 := by omega
      rw [Nat.Coprime, Nat.gcd_rec, hrem]
      decide
    have hbij := pow_bijective_of_coprime (F := F) (by omega : 1 ≤ 3) hcop
    have hS0 : ∑ x : F, η (x ^ 3 + 1) = 0 := by
      have h1 : ∑ x : F, η (x ^ 3 + 1) = ∑ v : F, η v :=
        Finset.sum_bij (fun x _ => x ^ 3 + 1) (fun _ _ => Finset.mem_univ _)
          (fun x₁ _ x₂ _ h => hbij.1 (add_right_cancel h))
          (fun v _ => by
            obtain ⟨x, hx⟩ := hbij.2 (v - 1)
            dsimp only at hx
            exact ⟨x, Finset.mem_univ _, by rw [hx, sub_add_cancel]⟩)
          (fun _ _ => rfl)
      rw [h1]
      exact MulChar.sum_eq_zero_of_ne_one hη
    have hC : (cmCurve2Points F : ℂ) = (Fintype.card F : ℂ) + 1 := by
      unfold cmCurve2Points
      rw [weierstrass_points_eq_sum_quadChar h2 hη hset2 (fun x => x ^ 3 + 1), hS0, add_zero]
    exact_mod_cast hC
  · -- Even `q`: `gcd(2, q - 1) = 1`, so `y ↦ y ^ 2` is bijective and every `x` has a unique `y`
    have hodd : Odd (Fintype.card F - 1) := by
      rw [Nat.odd_iff]; omega
    have hcop2 : Nat.Coprime 2 (Fintype.card F - 1) := Nat.coprime_two_left.mpr hodd
    have hbij2 := pow_bijective_of_coprime (F := F) (by omega : 1 ≤ 2) hcop2
    unfold cmCurve2Points
    have hcard : (Finset.univ.filter fun p : F × F => p.2 ^ 2 = p.1 ^ 3 + 1).card =
        Fintype.card F := by
      rw [← Finset.card_univ (α := F)]
      refine Finset.card_bij (fun p _ => p.1) (fun _ _ => Finset.mem_univ _) ?_ ?_
      · intro p₁ hp₁ p₂ hp₂ h
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
        refine Prod.ext h (hbij2.1 ?_)
        dsimp only
        rw [hp₁, hp₂, h]
      · intro x _
        obtain ⟨y, hy⟩ := hbij2.2 (x ^ 3 + 1)
        exact ⟨(x, y), by simp [hy], rfl⟩
    rw [hcard, add_comm]

/-- **UNCONDITIONAL HASSE–WEIL BOUND FOR `E₂ : y² = x³ + 1` (`q ≡ 1 [MOD 6]` OR `q ≡ 2 [MOD 3]`)**:
`|#E₂(𝔽_q) - (q + 1)| ≤ 2 √q`! -/
theorem cmCurve2_hasse_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hq : 6 ∣ Fintype.card F - 1 ∨ Fintype.card F % 3 = 2) :
    |(cmCurve2Points F : ℝ) - ((Fintype.card F : ℝ) + 1)| ≤
      2 * Real.sqrt (Fintype.card F : ℝ) := by
  rcases hq with h6 | h2mod3
  · obtain ⟨ψ, η, hψ, hη, hψη, hψiη, heq⟩ := cmCurve2_eq_sum_jacobiSum (F := F) h6
    have hdiff : (((cmCurve2Points F : ℝ) - ((Fintype.card F : ℝ) + 1) : ℝ) : ℂ) =
        jacobiSum ψ η + jacobiSum ψ⁻¹ η := by
      push_cast; rw [heq]; ring
    calc |(cmCurve2Points F : ℝ) - ((Fintype.card F : ℝ) + 1)|
        = ‖(((cmCurve2Points F : ℝ) - ((Fintype.card F : ℝ) + 1) : ℝ) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs]
      _ = ‖jacobiSum ψ η + jacobiSum ψ⁻¹ η‖ := by rw [hdiff]
      _ ≤ ‖jacobiSum ψ η‖ + ‖jacobiSum ψ⁻¹ η‖ := norm_add_le _ _
      _ = Real.sqrt (Fintype.card F : ℝ) + Real.sqrt (Fintype.card F : ℝ) := by
            rw [norm_jacobiSum_eq_sqrt hψ hη hψη,
              norm_jacobiSum_eq_sqrt (inv_ne_one.mpr hψ) hη hψiη]
      _ = 2 * Real.sqrt (Fintype.card F : ℝ) := by ring
  · rw [cmCurve2_supersingular h2mod3]
    push_cast
    rw [sub_self, abs_zero]
    positivity

end CMEllipticCurves

end RHDirect.Stage8WeilHigherDim

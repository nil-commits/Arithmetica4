import Prize.PPL176_UpperBinPack
import Mathlib.Data.Nat.Log

open scoped BigOperators Nat

namespace PPL176

/-! ## Dual-Scale Pairwise-Coprime Bin-Packing + Exact Top-`t_p` Valuation Packing

This module establishes a new general linear bound for **Erdős Problem #708** across the entire
polynomial range `M ≥ n^{1 + a/b}` with **zero multiplicative prefactor**, strictly improving:
- Haoyu Chen's Sept 2026 Lean 4 record `g(n) ≤ 12n` for `M ≥ n²` to **`4n`** (`3×` sharper);
- Haoyu Chen's Sept 2026 Lean 4 record `g(n) ≤ 15n` for `M ≥ n^{7/4}` to **`5n`** (`3×` sharper);
- `PPL176_UpperBinPack`'s `9n²` threshold for `3n` / `(k n)^{k+1} ≤ M^{k-1}` prefactor thresholds,
  extending down to `n^{5/3} ≤ M → 5n`, `n^{3/2} ≤ M → 6n`, `n^{4/3} ≤ M → 8n`, and in general
  `n^{a+b} ≤ M^b → ⌊(2(a+b)n + a - 1)/a⌋` for all `1 ≤ a ≤ b`.
-/

/-! ### Section 1: Pairwise-Coprime `M`-Bin Packing -/

lemma coprime_prod_of_forall {x : ℕ} :
    ∀ {ys : List ℕ}, (∀ y ∈ ys, Nat.Coprime x y) → Nat.Coprime x ys.prod
  | [], _ => by simp
  | y :: rest, h => by
    rw [List.prod_cons]
    exact Nat.Coprime.mul_right (h y List.mem_cons_self)
      (coprime_prod_of_forall (fun z hz => h z (List.mem_cons_of_mem y hz)))

lemma list_prod_dvd_of_pairwise_coprime {N : ℕ} :
    ∀ {bs : List ℕ}, bs.Pairwise Nat.Coprime → (∀ u ∈ bs, u ∣ N) → bs.prod ∣ N
  | [], _, _ => by simp
  | u :: rest, hpw, hdvd => by
    rw [List.pairwise_cons] at hpw
    rw [List.prod_cons]
    have hcop : Nat.Coprime u rest.prod := coprime_prod_of_forall hpw.1
    exact hcop.mul_dvd_of_dvd_of_dvd (hdvd u List.mem_cons_self)
      (list_prod_dvd_of_pairwise_coprime hpw.2 (fun z hz => hdvd z (List.mem_cons_of_mem u hz)))

/-- Extract two elements violating `R` from a list while preserving `Pairwise Nat.Coprime`
    after merging `u * v` to the front of `rest`. -/
lemma exists_merge_coprime_of_not_pairwise {R : ℕ → ℕ → Prop} [DecidableRel R] :
    ∀ (xs : List ℕ), xs.Pairwise Nat.Coprime → ¬ xs.Pairwise R →
      ∃ (u v : ℕ) (rest : List ℕ),
        ¬ R u v ∧ rest.length + 2 = xs.length ∧
        (u * v) * rest.prod = xs.prod ∧
        (∀ x ∈ rest, x ∈ xs) ∧ u ∈ xs ∧ v ∈ xs ∧
        ((u * v) :: rest).Pairwise Nat.Coprime
  | [], _, h => absurd List.Pairwise.nil h
  | a :: tail, hcop, h => by
    rw [List.pairwise_cons] at h hcop
    by_cases h1 : ∀ b ∈ tail, R a b
    · have htail : ¬ tail.Pairwise R := fun ht => h ⟨h1, ht⟩
      obtain ⟨u, v, rest, hnotR, hlen, hprod, hmem, hu, hv, hrest_cop⟩ :=
        exists_merge_coprime_of_not_pairwise tail hcop.2 htail
      rw [List.pairwise_cons] at hrest_cop
      refine ⟨u, v, a :: rest, hnotR, by simp [hlen], ?_, ?_,
        List.mem_cons_of_mem a hu, List.mem_cons_of_mem a hv, ?_⟩
      · simp only [List.prod_cons]
        rw [← hprod]
        ring
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem a (hmem x hx')
      · rw [List.pairwise_cons]
        refine ⟨?_, ?_⟩
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact (Nat.Coprime.mul_right (hcop.1 u hu) (hcop.1 v hv)).symm
          · exact hrest_cop.1 z hz'
        · rw [List.pairwise_cons]
          exact ⟨fun z hz => hcop.1 z (hmem z hz), hrest_cop.2⟩
    · push Not at h1
      obtain ⟨b, hb_mem, hnotR⟩ := h1
      obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hb_mem
      have hcop_l12 : (l₁ ++ l₂).Pairwise Nat.Coprime := by
        have hpw := hcop.2
        rw [List.pairwise_append] at hpw ⊢
        refine ⟨hpw.1, (List.pairwise_cons.mp hpw.2.1).2, ?_⟩
        intro x hx y hy
        exact hpw.2.2 x hx y (List.mem_cons_of_mem b hy)
      refine ⟨a, b, l₁ ++ l₂, hnotR, by simp; omega, ?_, ?_, List.mem_cons_self, by simp, ?_⟩
      · simp only [List.prod_cons, List.prod_append]
        ring
      · intro x hx
        rcases List.mem_append.mp hx with hx1 | hx2
        · exact List.mem_cons_of_mem a (List.mem_append_left _ hx1)
        · exact List.mem_cons_of_mem a (List.mem_append_right _ (List.mem_cons_of_mem b hx2))
      · rw [List.pairwise_cons]
        refine ⟨?_, hcop_l12⟩
        intro z hz
        have hz_in : z ∈ l₁ ++ b :: l₂ := by
          rcases List.mem_append.mp hz with hz1 | hz2
          · exact List.mem_append_left _ hz1
          · exact List.mem_append_right _ (List.mem_cons_of_mem b hz2)
        have hzb : Nat.Coprime b z := by
          have hpw := hcop.2
          rw [List.pairwise_append] at hpw
          rcases List.mem_append.mp hz with hz1 | hz2
          · exact (hpw.2.2 z hz1 b List.mem_cons_self).symm
          · have hpw2 := hpw.2.1
            rw [List.pairwise_cons] at hpw2
            exact hpw2.1 z hz2
        exact Nat.Coprime.mul_left (hcop.1 z hz_in) hzb

/-- Greedy multiplicative bin-packing preserving pairwise coprimality. -/
lemma list_bin_pack_coprime (L : ℕ) :
    ∀ (n : ℕ) (xs : List ℕ), xs.length = n → (∀ x ∈ xs, 1 ≤ x ∧ x ≤ L) →
      xs.Pairwise Nat.Coprime →
      ∃ bs : List ℕ,
        (∀ u ∈ bs, 1 ≤ u ∧ u ≤ L) ∧
        bs.prod = xs.prod ∧
        bs.Pairwise (fun u v => L < u * v) ∧
        bs.Pairwise Nat.Coprime := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro xs hlen hxs hcop
    by_cases hpw : xs.Pairwise (fun u v => L < u * v)
    · exact ⟨xs, hxs, rfl, hpw, hcop⟩
    · obtain ⟨u, v, rest, hnotgt, hrest_len, hprod, hmem, hu, hv, hnew_cop⟩ :=
        exists_merge_coprime_of_not_pairwise xs hcop hpw
      have huv_le : u * v ≤ L := Nat.le_of_not_lt hnotgt
      have huv_ge : 1 ≤ u * v := Nat.mul_pos (hxs u hu).1 (hxs v hv).1
      let xs' := (u * v) :: rest
      have hlen' : xs'.length < n := by
        simp only [xs', List.length_cons]
        omega
      have hxs' : ∀ x ∈ xs', 1 ≤ x ∧ x ≤ L := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact ⟨huv_ge, huv_le⟩
        · exact hxs x (hmem x hx')
      obtain ⟨bs, hbs_bnd, hbs_prod, hbs_pw, hbs_cop⟩ :=
        ih xs'.length hlen' xs' rfl hxs' hnew_cop
      refine ⟨bs, hbs_bnd, ?_, hbs_pw, hbs_cop⟩
      rw [hbs_prod]
      simpa [xs'] using hprod

/-- Pairwise-coprime bin-packing cover for small prime powers `p ^ E p ≤ M`.
    Because bins are pairwise coprime, each bin needs just ONE multiple in `I`,
    so `|B₁| ≤ r` with ZERO collisions across bins! -/
lemma exists_coprime_binpack_cover {m M : ℕ} {P_small : Finset ℕ} {E : ℕ → ℕ}
    (hP : ∀ p ∈ P_small, p.Prime ∧ p ^ E p ≤ M) :
    ∃ B₁ ⊆ Erdos708Interval m M, ∃ r : ℕ,
      B₁.card ≤ r ∧
      (∏ p ∈ P_small, p ^ E p) ∣ (∏ b ∈ B₁, b) ∧
      (2 ≤ r → (M + 1) ^ r ≤ (∏ p ∈ P_small, p ^ E p) ^ 2) := by
  let xs : List ℕ := P_small.toList.map (fun p => p ^ E p)
  have hxs_prod : xs.prod = ∏ p ∈ P_small, p ^ E p := by
    dsimp [xs]
    rw [← Multiset.prod_coe, ← Multiset.map_coe, Finset.coe_toList]
    rfl
  have hxs_bnd : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ M := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩
    rw [Finset.mem_toList] at hp
    exact ⟨Nat.one_le_pow _ _ (hP p hp).1.pos, (hP p hp).2⟩
  have hxs_cop : xs.Pairwise Nat.Coprime := by
    dsimp [xs]
    rw [List.pairwise_map]
    refine (P_small.nodup_toList).imp_of_mem ?_
    intro p₁ p₂ hp₁ hp₂ hne
    rw [Finset.mem_toList] at hp₁ hp₂
    have hcop := (Nat.coprime_primes (hP p₁ hp₁).1 (hP p₂ hp₂).1).mpr hne
    exact hcop.pow (E p₁) (E p₂)
  obtain ⟨bs, hbs_bnd, hbs_prod, hbs_pw, hbs_cop⟩ :=
    list_bin_pack_coprime M xs.length xs rfl hxs_bnd hxs_cop
  have hpick : ∀ u ∈ bs, ∃ b ∈ Erdos708Interval m M, u ∣ b := by
    intro u hu
    have hbnd := hbs_bnd u hu
    have hu_pos : 0 < u := by omega
    have hdiv_pos : 1 ≤ M / u := (Nat.le_div_iff_mul_le hu_pos).mpr (by simpa using hbnd.2)
    have hcard_pos : 0 < ((Erdos708Interval m M).filter (fun b => u ∣ b)).card :=
      lt_of_lt_of_le (by omega) (card_multiples_Icc_ge m M u hu_pos)
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hcard_pos
    rw [Finset.mem_filter] at hb
    exact ⟨b, hb.1, hb.2⟩
  let picked : List ℕ := bs.attach.map (fun ⟨u, hu⟩ => Classical.choose (hpick u hu))
  let B₁ : Finset ℕ := picked.toFinset
  refine ⟨B₁, ?_, bs.length, ?_, ?_, ?_⟩
  · intro b hb
    rw [List.mem_toFinset] at hb
    dsimp [picked] at hb
    rcases List.mem_map.mp hb with ⟨⟨u, hu⟩, _, rfl⟩
    exact (Classical.choose_spec (hpick u hu)).1
  · calc B₁.card ≤ picked.length := List.toFinset_card_le picked
      _ = bs.length := by simp [picked]
  · rw [← hxs_prod, ← hbs_prod]
    apply list_prod_dvd_of_pairwise_coprime hbs_cop
    intro u hu
    let b := Classical.choose (hpick u hu)
    have hb_spec := Classical.choose_spec (hpick u hu)
    have hb_mem : b ∈ B₁ := by
      rw [List.mem_toFinset]
      dsimp [picked]
      exact List.mem_map.mpr ⟨⟨u, hu⟩, List.mem_attach _ _, rfl⟩
    exact dvd_trans hb_spec.2 (Finset.dvd_prod_of_mem id hb_mem)
  · intro hr
    rw [← hxs_prod, ← hbs_prod]
    exact pairwise_mul_gt_pow_le_sq M bs.length bs rfl hr hbs_pw

/-! ### Section 2: Exact Top-`t` Legendre Valuation Covering (`valCap`) -/

/-- Exact total `p`-adic valuation obtainable from `t` elements of `{m+1, ..., m+M}`:
    `∑_{j=1}^{⌊log_p M⌋} min(t, ⌊M / p^j⌋)`. -/
def valCap (M p t : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 (Nat.log p M), min t (M / p ^ j)

lemma sum_ite_le_eq_min (K v : ℕ) :
    (∑ j ∈ Finset.Icc 1 K, if j ≤ v then 1 else 0) = min K v := by
  rw [Finset.sum_boole, Nat.cast_id]
  have hfilt : (Finset.Icc 1 K).filter (fun j => j ≤ v) = Finset.Icc 1 (min K v) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hfilt, Nat.card_Icc]
  omega

lemma sum_card_filter_le_val (S : Finset ℕ) (p K : ℕ) :
    ∑ j ∈ Finset.Icc 1 K, (S.filter (fun b => j ≤ b.factorization p)).card =
      ∑ b ∈ S, min K (b.factorization p) := by
  calc
    ∑ j ∈ Finset.Icc 1 K, (S.filter (fun b => j ≤ b.factorization p)).card
        = ∑ j ∈ Finset.Icc 1 K, ∑ b ∈ S, if j ≤ b.factorization p then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_boole, Nat.cast_id]
    _ = ∑ b ∈ S, ∑ j ∈ Finset.Icc 1 K, if j ≤ b.factorization p then 1 else 0 := Finset.sum_comm
    _ = ∑ b ∈ S, min K (b.factorization p) := by
          apply Finset.sum_congr rfl
          intro b _
          exact sum_ite_le_eq_min K (b.factorization p)

/-- Greedy top-`t` selection in `{m + 1, ..., m + M}` maximizing `v_p(b)`. -/
lemma exists_top_t_subset_Icc {m M p : ℕ} :
    ∀ t ≤ M, ∃ C ⊆ Erdos708Interval m M,
      C.card = t ∧
      ∀ x ∈ C, ∀ y ∈ Erdos708Interval m M \ C, y.factorization p ≤ x.factorization p
  | 0, _ => ⟨∅, Finset.empty_subset _, Finset.card_empty, fun x hx => absurd hx (Finset.notMem_empty x)⟩
  | t + 1, ht => by
    obtain ⟨C₀, hC₀I, hC₀card, hC₀max⟩ := exists_top_t_subset_Icc (m := m) (M := M) (p := p) t (by omega)
    set I := Erdos708Interval m M
    have hrem_pos : 0 < (I \ C₀).card := by
      have hcard := Finset.card_sdiff_add_card_eq_card hC₀I
      rw [erdos708Interval_card, hC₀card] at hcard
      omega
    obtain ⟨y₀, hy₀_mem, hy₀_max⟩ :=
      Finset.exists_max_image (I \ C₀) (fun y => y.factorization p) (Finset.card_pos.mp hrem_pos)
    rw [Finset.mem_sdiff] at hy₀_mem
    refine ⟨insert y₀ C₀, Finset.insert_subset hy₀_mem.1 hC₀I, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hy₀_mem.2, hC₀card]
    · intro x hx y hy
      rw [Finset.mem_sdiff] at hy
      have hy_rem : y ∈ I \ C₀ := Finset.mem_sdiff.mpr
        ⟨hy.1, fun h => hy.2 (Finset.mem_insert_of_mem h)⟩
      rcases Finset.mem_insert.mp hx with rfl | hx₀
      · exact hy₀_max y hy_rem
      · exact hC₀max x hx₀ y hy_rem

/-- **Exact Top-`t` Valuation Covering Lemma**:
    For every prime `p` and `t ≤ M`, there exists `C ⊆ {m + 1, ..., m + M}` of size `≤ t`
    whose total `p`-adic valuation is at least `valCap M p t`. -/
lemma exists_subset_Icc_card_val_ge_valCap {m M p t : ℕ} (hp : p.Prime) (ht : t ≤ M) :
    ∃ C ⊆ Erdos708Interval m M, C.card ≤ t ∧ valCap M p t ≤ ∑ b ∈ C, b.factorization p := by
  set I := Erdos708Interval m M
  obtain ⟨C, hCI, hCcard, hCmax⟩ := exists_top_t_subset_Icc (m := m) (M := M) (p := p) t ht
  refine ⟨C, hCI, le_of_eq hCcard, ?_⟩
  have hlevel : ∀ j ∈ Finset.Icc 1 (Nat.log p M),
      min t (M / p ^ j) ≤ (C.filter (fun b => j ≤ b.factorization p)).card := by
    intro j hj
    by_cases hall : ∀ x ∈ C, j ≤ x.factorization p
    · have hfilt : C.filter (fun b => j ≤ b.factorization p) = C :=
        Finset.filter_true_of_mem hall
      rw [hfilt, hCcard]
      exact min_le_left t _
    · push Not at hall
      obtain ⟨x, hxC, hxj⟩ := hall
      let Ij := I.filter (fun b => j ≤ b.factorization p)
      have hIj_sub : Ij ⊆ C.filter (fun b => j ≤ b.factorization p) := by
        intro b hb
        rw [Finset.mem_filter] at hb ⊢
        refine ⟨?_, hb.2⟩
        by_contra hbC
        have hle := hCmax x hxC b (Finset.mem_sdiff.mpr ⟨hb.1, hbC⟩)
        omega
      have hpj_pos : 0 < p ^ j := pow_pos hp.pos j
      have hdiv_le_Ij : M / p ^ j ≤ Ij.card := by
        have h1 := card_multiples_Icc_ge m M (p ^ j) hpj_pos
        have heq : I.filter (fun b => p ^ j ∣ b) = Ij := by
          ext b
          simp only [Ij, Finset.mem_filter]
          constructor
          · rintro ⟨hbI, hdvd⟩
            have hb0 : b ≠ 0 := Nat.ne_of_gt (erdos708Interval_pos hbI)
            exact ⟨hbI, (hp.pow_dvd_iff_le_factorization hb0).mp hdvd⟩
          · rintro ⟨hbI, hle⟩
            have hb0 : b ≠ 0 := Nat.ne_of_gt (erdos708Interval_pos hbI)
            exact ⟨hbI, (hp.pow_dvd_iff_le_factorization hb0).mpr hle⟩
        rwa [heq] at h1
      exact le_trans (min_le_right t _) (le_trans hdiv_le_Ij (Finset.card_le_card hIj_sub))
  calc
    valCap M p t
        = ∑ j ∈ Finset.Icc 1 (Nat.log p M), min t (M / p ^ j) := rfl
    _ ≤ ∑ j ∈ Finset.Icc 1 (Nat.log p M),
          (C.filter (fun b => j ≤ b.factorization p)).card := Finset.sum_le_sum hlevel
    _ = ∑ b ∈ C, min (Nat.log p M) (b.factorization p) :=
          sum_card_filter_le_val C p (Nat.log p M)
    _ ≤ ∑ b ∈ C, b.factorization p :=
          Finset.sum_le_sum (fun b _ => min_le_right _ _)

/-- Total `p`-adic valuation of any `A ⊆ [1, M]` is bounded by `valCap M p (min |A| (M / p))`. -/
lemma sum_factorization_le_valCap_min {A : Finset ℕ} {p : ℕ}
    (hA : ∀ x ∈ A, 1 ≤ x) (hp : p.Prime) :
    ∑ x ∈ A, x.factorization p ≤ valCap (A.sup id) p (min A.card (A.sup id / p)) := by
  by_cases hA_emp : A = ∅
  · subst hA_emp; simp
  set M := A.sup id
  have hM_ne : M ≠ 0 := by
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hA_emp
    have h1 := hA x hx
    have h2 : x ≤ M := Finset.le_sup (f := id) hx
    omega
  have hfac_le : ∀ x ∈ A, x.factorization p ≤ Nat.log p M := by
    intro x hx
    have hx1 : 1 ≤ x := hA x hx
    have hxM : x ≤ M := Finset.le_sup (f := id) hx
    have hpow_le : p ^ (x.factorization p) ≤ M :=
      le_trans (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd x p)) hxM
    exact (Nat.le_log_iff_pow_le hp.one_lt hM_ne).mpr hpow_le
  have hsum_eq : ∑ x ∈ A, x.factorization p =
      ∑ j ∈ Finset.Icc 1 (Nat.log p M), (A.filter (fun x => j ≤ x.factorization p)).card := by
    rw [sum_card_filter_le_val A p (Nat.log p M)]
    apply Finset.sum_congr rfl
    intro x hx
    exact (min_eq_right (hfac_le x hx)).symm
  rw [hsum_eq]
  apply Finset.sum_le_sum
  intro j hj
  rw [Finset.mem_Icc] at hj
  have hle_card : (A.filter (fun x => j ≤ x.factorization p)).card ≤ A.card :=
    Finset.card_filter_le _ _
  have hle_div_j : (A.filter (fun x => j ≤ x.factorization p)).card ≤ M / p ^ j := by
    have hsub : A.filter (fun x => j ≤ x.factorization p) ⊆
        (Finset.Icc 1 M).filter (fun x => p ^ j ∣ x) := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      have hx1 : 1 ≤ x := hA x hx.1
      have hxM : x ≤ M := Finset.le_sup (f := id) hx.1
      exact ⟨Finset.mem_Icc.mpr ⟨hx1, hxM⟩, (hp.pow_dvd_iff_le_factorization (by omega)).mpr hx.2⟩
    exact le_trans (Finset.card_le_card hsub) (card_multiples_Icc_one_le M (p ^ j) (pow_pos hp.pos j))
  have hle_div_p : M / p ^ j ≤ M / p :=
    Nat.div_le_div_left (by simpa using Nat.pow_le_pow_right hp.pos hj.1) hp.pos
  exact le_min (le_min hle_card (le_trans hle_div_j hle_div_p)) hle_div_j

/-! ### Section 3: Pure-`ℕ` Power Inequality for Big-Exponent Primes -/

/-- Lower bound on `valCap M p t'` from `s = ⌊log_p (M / t')⌋`:
    `s * t' ≤ valCap M p t'` whenever `1 ≤ t' ≤ M / p`. -/
lemma mul_log_le_valCap {M p t' : ℕ} (hp : p.Prime) (ht' : 1 ≤ t') (ht'_le : t' ≤ M / p) :
    Nat.log p (M / t') * t' ≤ valCap M p t' := by
  set s := Nat.log p (M / t')
  have hs_le_M : s ≤ Nat.log p M := Nat.log_mono_right (Nat.div_le_self M t')
  have hsub : Finset.Icc 1 s ⊆ Finset.Icc 1 (Nat.log p M) :=
    Finset.Icc_subset_Icc_right hs_le_M
  have hterm : ∀ j ∈ Finset.Icc 1 s, min t' (M / p ^ j) = t' := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    apply min_eq_left
    have hpj_le : p ^ j ≤ p ^ s := Nat.pow_le_pow_right hp.pos hj.2
    have hps_le : p ^ s ≤ M / t' := by
      apply Nat.pow_log_le_self
      have := (Nat.le_div_iff_mul_le hp.pos).mp ht'_le
      have : p ≤ M / t' := by
        rw [Nat.le_div_iff_mul_le ht']
        nlinarith [hp.pos]
      have := hp.pos
      omega
    have hmul : t' * p ^ j ≤ M := by
      calc t' * p ^ j = p ^ j * t' := mul_comm t' (p ^ j)
        _ ≤ p ^ s * t' := Nat.mul_le_mul_right t' hpj_le
        _ ≤ (M / t') * t' := Nat.mul_le_mul_right t' hps_le
        _ ≤ M := Nat.div_mul_le_self M t'
    exact (Nat.le_div_iff_mul_le (pow_pos hp.pos j)).mpr hmul
  calc
    s * t' = ∑ _j ∈ Finset.Icc 1 s, t' := by simp [Nat.card_Icc]
    _ = ∑ j ∈ Finset.Icc 1 s, min t' (M / p ^ j) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact (hterm j hj).symm
    _ ≤ ∑ j ∈ Finset.Icc 1 (Nat.log p M), min t' (M / p ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)

/-- **Core Exponential Valuation Inequality**:
    When `1 ≤ a ≤ b` and `n ^ (a + b) ≤ M ^ b`, any prime `p` with `M < p ^ E` and
    minimal cover size `t` (`1 ≤ t ≤ min n (M / p)`) satisfies:
    `M ^ (a * t) < (p ^ E) ^ (2 * (a + b))`. -/
lemma big_prime_pow_bound {M n p E t a b : ℕ}
    (hp : p.Prime) (ha : 1 ≤ a) (hab : a ≤ b)
    (hM_ge : n ^ (a + b) ≤ M ^ b) (hbig : M < p ^ E)
    (ht_pos : 1 ≤ t) (ht_le_n : t ≤ n) (ht_le_Mp : t ≤ M / p)
    (ht_min : 2 ≤ t → valCap M p (t - 1) < E) :
    M ^ (a * t) < (p ^ E) ^ (2 * (a + b)) := by
  by_cases ht1 : t = 1
  · subst ht1
    rw [mul_one]
    have hpow1 : M ^ a < (p ^ E) ^ a := Nat.pow_lt_pow_left hbig (by omega)
    have hpE_pos : 1 ≤ p ^ E := Nat.one_le_pow E p hp.pos
    have hpow2 : (p ^ E) ^ a ≤ (p ^ E) ^ (2 * (a + b)) :=
      Nat.pow_le_pow_right hpE_pos (by omega)
    exact lt_of_lt_of_le hpow1 hpow2
  · have ht2 : 2 ≤ t := by omega
    set t' := t - 1
    have ht'_pos : 1 ≤ t' := by omega
    have ht'_lt_n : t' < n := by omega
    have ht'_le_Mp : t' ≤ M / p := by omega
    have hval_lt : valCap M p t' < E := ht_min ht2
    set s := Nat.log p (M / t')
    have hs_ge1 : 1 ≤ s := by
      have hp_le : p ^ 1 ≤ M / t' := by
        rw [pow_one, Nat.le_div_iff_mul_le ht'_pos]
        have := (Nat.le_div_iff_mul_le hp.pos).mp ht'_le_Mp
        nlinarith [hp.pos]
      have hM_div_ne : M / t' ≠ 0 := by
        have := (Nat.le_div_iff_mul_le hp.pos).mp ht'_le_Mp
        have h1 : t' ≤ M := by
          calc t' = 1 * t' := (one_mul t').symm
            _ ≤ p * t' := Nat.mul_le_mul_right t' hp.pos
            _ = t' * p := mul_comm p t'
            _ ≤ M := this
        exact Nat.ne_of_gt (Nat.div_pos h1 ht'_pos)
      exact (Nat.le_log_iff_pow_le hp.one_lt hM_div_ne).mpr hp_le
    have hst_lt_E : s * t' < E :=
      lt_of_le_of_lt (mul_log_le_valCap hp ht'_pos ht'_le_Mp) hval_lt
    -- Show `M < p ^ (s + 1) * t'`
    have hM_lt_ps1 : M < p ^ (s + 1) * t' := by
      have h1 : M / t' < p ^ (s + 1) := Nat.lt_pow_succ_log_self hp.one_lt (M / t')
      have h2 : M < (M / t' + 1) * t' := by
        have := Nat.div_add_mod M t'
        have := Nat.mod_lt M ht'_pos
        nlinarith
      have h3 : (M / t' + 1) * t' ≤ p ^ (s + 1) * t' :=
        Nat.mul_le_mul_right t' h1
      omega
    -- Deduce `M ^ a < p ^ ((s + 1) * (a + b))`
    have hMa_lt : M ^ a < p ^ ((s + 1) * (a + b)) := by
      have hM_pos : 0 < M := by
        have := (Nat.le_div_iff_mul_le hp.pos).mp ht'_le_Mp
        have := hp.pos
        nlinarith
      have ht'_pow_lt : t' ^ (a + b) < M ^ b := by
        calc t' ^ (a + b) < n ^ (a + b) := Nat.pow_lt_pow_left ht'_lt_n (by omega)
          _ ≤ M ^ b := hM_ge
      have hmul1 : M ^ a * t' ^ (a + b) < M ^ a * M ^ b :=
        Nat.mul_lt_mul_of_pos_left ht'_pow_lt (pow_pos hM_pos a)
      have hMab : M ^ a * M ^ b = M ^ (a + b) := (pow_add M a b).symm
      have hmul2 : M ^ (a + b) < (p ^ (s + 1) * t') ^ (a + b) :=
        Nat.pow_lt_pow_left hM_lt_ps1 (by omega)
      rw [mul_pow, ← pow_mul] at hmul2
      have hcombined : M ^ a * t' ^ (a + b) < p ^ ((s + 1) * (a + b)) * t' ^ (a + b) := by
        linarith [hMab]
      exact Nat.lt_of_mul_lt_mul_right hcombined
    by_cases hs1 : s = 1
    · -- Subcase `s = 1`: `t = t' + 1 ≤ E` and `M ^ a < p ^ (2 * (a + b))`!
      have ht_le_E : t ≤ E := by
        have : 1 * t' < E := hs1 ▸ hst_lt_E
        omega
      have hMa_lt2 : M ^ a < p ^ (2 * (a + b)) := by simpa [hs1] using hMa_lt
      calc
        M ^ (a * t) = (M ^ a) ^ t := by rw [pow_mul]
        _ < (p ^ (2 * (a + b))) ^ t := Nat.pow_lt_pow_left hMa_lt2 (by omega)
        _ = p ^ (t * (2 * (a + b))) := by rw [← pow_mul, mul_comm (2 * (a + b)) t]
        _ ≤ p ^ (E * (2 * (a + b))) :=
            Nat.pow_le_pow_right hp.pos (Nat.mul_le_mul_right _ ht_le_E)
        _ = (p ^ E) ^ (2 * (a + b)) := pow_mul p E (2 * (a + b))
    · -- Subcase `s ≥ 2`: `2 * (s + 1) ≤ 3 * s` and `5 * a + 3 * b ≤ 4 * (a + b)`!
      have hs2 : 2 ≤ s := by omega
      have h2s : 2 * (s + 1) ≤ 3 * s := by omega
      have hM2a_lt : M ^ (2 * a) < p ^ (3 * s * (a + b)) := by
        calc
          M ^ (2 * a) = (M ^ a) ^ 2 := by rw [← pow_mul, mul_comm a 2]
          _ < (p ^ ((s + 1) * (a + b))) ^ 2 := Nat.pow_lt_pow_left hMa_lt (by omega)
          _ = p ^ (2 * (s + 1) * (a + b)) := by rw [← pow_mul]; ring_nf
          _ ≤ p ^ (3 * s * (a + b)) :=
              Nat.pow_le_pow_right hp.pos (Nat.mul_le_mul_right _ h2s)
      have h1 : M ^ (2 * a * t') < p ^ (3 * (a + b) * E) := by
        have hlt1 : (M ^ (2 * a)) ^ t' < (p ^ (3 * s * (a + b))) ^ t' :=
          Nat.pow_lt_pow_left hM2a_lt (by omega)
        have hle2 : p ^ (3 * s * (a + b) * t') ≤ p ^ (3 * (a + b) * E) := by
          apply Nat.pow_le_pow_right hp.pos
          have hst_le : s * t' ≤ E := le_of_lt hst_lt_E
          calc 3 * s * (a + b) * t' = 3 * (a + b) * (s * t') := by ring
            _ ≤ 3 * (a + b) * E := Nat.mul_le_mul_left _ hst_le
        calc M ^ (2 * a * t') = (M ^ (2 * a)) ^ t' := pow_mul M (2 * a) t'
          _ < (p ^ (3 * s * (a + b))) ^ t' := hlt1
          _ = p ^ (3 * s * (a + b) * t') := (pow_mul p (3 * s * (a + b)) t').symm
          _ ≤ p ^ (3 * (a + b) * E) := hle2
      have h2 : M ^ (2 * a) < p ^ (2 * a * E) := by
        have hlt := Nat.pow_lt_pow_left hbig (by omega : 2 * a ≠ 0)
        rw [← pow_mul, mul_comm E (2 * a)] at hlt
        exact hlt
      have hprod : M ^ (2 * a * t' + 2 * a) < p ^ (3 * (a + b) * E + 2 * a * E) := by
        rw [pow_add, pow_add]
        exact Nat.mul_lt_mul'' h1 h2
      have hexpL : 2 * a * t' + 2 * a = 2 * (a * t) := by
        have : t' + 1 = t := Nat.sub_add_cancel ht_pos
        calc 2 * a * t' + 2 * a = 2 * a * (t' + 1) := by ring
          _ = 2 * a * t := by rw [this]
          _ = 2 * (a * t) := by ring
      have hexpR : 3 * (a + b) * E + 2 * a * E ≤ 2 * (2 * (a + b) * E) := by
        have h53 : 3 * (a + b) + 2 * a ≤ 4 * (a + b) := by omega
        calc 3 * (a + b) * E + 2 * a * E = (3 * (a + b) + 2 * a) * E := by ring
          _ ≤ 4 * (a + b) * E := Nat.mul_le_mul_right E h53
          _ = 2 * (2 * (a + b) * E) := by ring
      have hsq : (M ^ (a * t)) ^ 2 < ((p ^ E) ^ (2 * (a + b))) ^ 2 := by
        calc
          (M ^ (a * t)) ^ 2 = M ^ (2 * (a * t)) := by rw [← pow_mul, mul_comm (a * t) 2]
          _ = M ^ (2 * a * t' + 2 * a) := by rw [hexpL]
          _ < p ^ (3 * (a + b) * E + 2 * a * E) := hprod
          _ ≤ p ^ (2 * (2 * (a + b) * E)) := Nat.pow_le_pow_right hp.pos hexpR
          _ = ((p ^ E) ^ (2 * (a + b))) ^ 2 := by
                rw [← pow_mul, ← pow_mul]
                congr 1; ring
      exact (Nat.pow_lt_pow_iff_left (by omega : 2 ≠ 0)).mp hsq

/-! ### Section 4: Main Dual-Scale Theorem and World-Record Corollaries -/

lemma prod_lt_prod_of_nonempty {ι : Type*} [DecidableEq ι] {S : Finset ι} (hS : S.Nonempty)
    {f g : ι → ℕ} (hfg : ∀ x ∈ S, f x < g x) :
    ∏ x ∈ S, f x < ∏ x ∈ S, g x := by
  induction S using Finset.induction_on with
  | empty => exact absurd hS Finset.not_nonempty_empty
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have ha_lt : f a < g a := hfg a (Finset.mem_insert_self a s)
    by_cases hs : s.Nonempty
    · have ihs := ih hs (fun x hx => hfg x (Finset.mem_insert_of_mem hx))
      exact Nat.mul_lt_mul'' ha_lt ihs
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
      simpa using ha_lt

/-- **Main Dual-Scale Theorem for Erdős Problem #708**:
    For every `A ⊆ [1, ∞)` with `1 ≤ a ≤ b` and `|A| ^ (a + b) ≤ (max A) ^ b`
    (i.e. `max A ≥ |A| ^ (1 + a/b)` with **zero prefactor**),
    every interval of length `max A` contains a covering subset `B` of size
    `|B| ≤ (2 * (a + b) * |A| + (a - 1)) / a`. -/
theorem erdos708_coprime_dual_scale {A : Finset ℕ} (hA : ∀ x ∈ A, 1 ≤ x)
    (m a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hM : A.card ^ (a + b) ≤ (A.sup id) ^ b) :
    Erdos708Covers A m ((2 * (a + b) * A.card + (a - 1)) / a) := by
  set n := A.card
  set M := A.sup id
  set I := Erdos708Interval m M
  -- Edge case `n = 0` (`A = ∅`)
  by_cases hn0 : n = 0
  · have hA_emp : A = ∅ := Finset.card_eq_zero.mp hn0
    subst hA_emp
    exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
  -- Edge case `n = 1` (`A = {x}`)
  by_cases hn1 : n = 1
  · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hn1
    subst hx
    have hx1 : 1 ≤ x := hA x (Finset.mem_singleton_self x)
    have hcard_pos : 0 < (I.filter (fun y => x ∣ y)).card := by
      have hdiv_ge : 1 ≤ M / x := by
        have hMx : M = x := by simp [M]
        rw [hMx, Nat.div_self (by omega)]
      exact lt_of_lt_of_le (by omega) (card_multiples_Icc_ge m M x (by omega))
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hcard_pos
    rw [Finset.mem_filter] at hy
    refine ⟨{y}, Finset.singleton_subset_iff.mpr hy.1, ?_, ?_⟩
    · rw [Finset.card_singleton, Nat.le_div_iff_mul_le ha]
      have : n = 1 := hn1
      nlinarith
    · simpa using hy.2
  -- Main case: `2 ≤ n`, hence `2 ≤ M` from `n ^ (a + b) ≤ M ^ b`!
  have hn2 : 2 ≤ n := by omega
  have hM2 : 2 ≤ M := by
    by_contra hlt
    have hM1 : M ≤ 1 := by omega
    have hMpow : M ^ b ≤ 1 := (Nat.pow_le_pow_left hM1 b).trans_eq (one_pow b)
    have hnpow : 2 ^ 2 ≤ n ^ (a + b) := by
      calc 2 ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hn2 2
        _ ≤ n ^ (a + b) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hM_gt1 : 1 < M := by omega
  -- Split primes dividing `∏ x ∈ A, x` into `P_small` (`p ^ E p ≤ M`) and `P_big` (`M < p ^ E p`)
  set E : ℕ → ℕ := fun p => ∑ x ∈ A, x.factorization p
  set P_all := A.biUnion Nat.primeFactors
  set P_small := P_all.filter (fun p => p ^ E p ≤ M)
  set P_big := P_all.filter (fun p => M < p ^ E p)
  have hP_prime : ∀ p ∈ P_all, p.Prime := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨x, _, hxp⟩
    exact Nat.prime_of_mem_primeFactors hxp
  -- Product decomposition `∏ x ∈ A, x = P₁ * P₂`
  set P₁ := ∏ p ∈ P_small, p ^ E p
  set P₂ := ∏ p ∈ P_big, p ^ E p
  have hA0 : ∀ x ∈ A, x ≠ 0 := fun x hx => by have := hA x hx; omega
  have hprodA_ne : ∏ x ∈ A, x ≠ 0 := Finset.prod_ne_zero_iff.mpr hA0
  have hPall_ne : ∏ p ∈ P_all, p ^ E p ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (hP_prime p hp).ne_zero)
  have hprodA_eq_Pall : ∏ x ∈ A, x = ∏ p ∈ P_all, p ^ E p := by
    apply Nat.factorization_inj hprodA_ne hPall_ne
    ext q
    rw [Nat.factorization_prod hA0, Nat.factorization_prod (fun p hp => pow_ne_zero _ (hP_prime p hp).ne_zero)]
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
    by_cases hq : q.Prime
    · have hterm : ∀ p ∈ P_all, (p ^ E p).factorization q = if p = q then E p else 0 := by
        intro p hp
        rw [(hP_prime p hp).factorization_pow, Finsupp.single_apply]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
      by_cases hq_mem : q ∈ P_all
      · simp [hq_mem, E]
      · simp only [hq_mem, ↓reduceIte]
        apply Finset.sum_eq_zero
        intro x hx
        have hnot : q ∉ x.primeFactors := fun h => hq_mem (Finset.mem_biUnion.mpr ⟨x, hx, h⟩)
        rw [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] at hnot
        exact hnot
    · have hzero : ∀ y : ℕ, y.factorization q = 0 := fun y =>
        Nat.factorization_eq_zero_of_not_prime y hq
      simp [hzero]
  have hP₁_mul_P₂ : P₁ * P₂ = ∏ x ∈ A, x := by
    rw [hprodA_eq_Pall]
    have hfilt_eq : P_all.filter (fun p => ¬ (p ^ E p ≤ M)) = P_big := by
      ext p; simp only [P_big, Finset.mem_filter, not_le]
    calc
      P₁ * P₂ = (∏ p ∈ P_all.filter (fun p => p ^ E p ≤ M), p ^ E p) *
            (∏ p ∈ P_all.filter (fun p => ¬ (p ^ E p ≤ M)), p ^ E p) := by rw [hfilt_eq]
      _ = ∏ p ∈ P_all, p ^ E p :=
          Finset.prod_filter_mul_prod_filter_not P_all (fun p => p ^ E p ≤ M) (fun p => p ^ E p)
  have hprodA_le_Mn : ∏ x ∈ A, x ≤ M ^ n := by
    calc ∏ x ∈ A, x ≤ ∏ _x ∈ A, M := Finset.prod_le_prod' (fun x hx => Finset.le_sup (f := id) hx)
      _ = M ^ n := by simp [n]
  -- Step 1: Cover `P_small` using pairwise-coprime bin packing!
  obtain ⟨B₁, hB₁_sub, r, hB₁_card, hB₁_dvd, hr_pow⟩ :=
    exists_coprime_binpack_cover (m := m) (M := M) (P_small := P_small) (E := E)
      (fun p hp => ⟨hP_prime p (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩)
  -- Step 2: Cover each `p ∈ P_big` using minimal `t_p` with `E p ≤ valCap M p t_p`!
  have hex_t : ∀ p ∈ P_big, ∃ t : ℕ, E p ≤ valCap M p t := by
    intro p hp
    have hp_prime := hP_prime p (Finset.mem_filter.mp hp).1
    exact ⟨min n (M / p), sum_factorization_le_valCap_min hA hp_prime⟩
  let tOf : ∀ p ∈ P_big, ℕ := fun p hp => Nat.find (hex_t p hp)
  have ht_spec : ∀ p (hp : p ∈ P_big), E p ≤ valCap M p (tOf p hp) :=
    fun p hp => Nat.find_spec (hex_t p hp)
  have ht_le_min : ∀ p (hp : p ∈ P_big), tOf p hp ≤ min n (M / p) := by
    intro p hp
    have hp_prime := hP_prime p (Finset.mem_filter.mp hp).1
    exact Nat.find_min' (hex_t p hp) (sum_factorization_le_valCap_min hA hp_prime)
  have ht_pos : ∀ p (hp : p ∈ P_big), 1 ≤ tOf p hp := by
    intro p hp
    have hE_pos : 1 ≤ E p := by
      have hlt : M < p ^ E p := (Finset.mem_filter.mp hp).2
      have h0 : E p ≠ 0 := by
        intro h0
        rw [h0, pow_zero] at hlt
        omega
      omega
    have hval := ht_spec p hp
    by_contra h0
    have hteq : tOf p hp = 0 := by omega
    rw [hteq] at hval
    have hv0 : valCap M p 0 = 0 := by simp [valCap]
    omega
  have hcover_big : ∀ p (hp : p ∈ P_big), ∃ C ⊆ I,
      C.card ≤ tOf p hp ∧ E p ≤ ∑ b ∈ C, b.factorization p := by
    intro p hp
    have hp_prime := hP_prime p (Finset.mem_filter.mp hp).1
    have ht_le_M : tOf p hp ≤ M :=
      le_trans (ht_le_min p hp) (le_trans (min_le_right _ _) (Nat.div_le_self M p))
    obtain ⟨C, hCI, hCcard, hCval⟩ := exists_subset_Icc_card_val_ge_valCap (m := m) hp_prime ht_le_M
    exact ⟨C, hCI, hCcard, le_trans (ht_spec p hp) hCval⟩
  choose Cbig hCbig_sub hCbig_card hCbig_val using hcover_big
  let B₂ : Finset ℕ := P_big.attach.biUnion (fun x => Cbig x.1 x.2)
  let B : Finset ℕ := B₁ ∪ B₂
  refine ⟨B, ?_, ?_, ?_⟩
  · -- `B ⊆ I`
    apply Finset.union_subset hB₁_sub
    intro b hb
    rcases Finset.mem_biUnion.mp hb with ⟨⟨p, hp⟩, _, hbc⟩
    exact hCbig_sub p hp hbc
  · -- `B.card ≤ (2 * (a + b) * n + (a - 1)) / a`
    set T := ∑ x ∈ P_big.attach, tOf x.1 x.2
    have hB_card_le : B.card ≤ r + T := by
      calc B.card ≤ B₁.card + B₂.card := Finset.card_union_le B₁ B₂
        _ ≤ r + ∑ x ∈ P_big.attach, (Cbig x.1 x.2).card :=
            Nat.add_le_add hB₁_card Finset.card_biUnion_le
        _ ≤ r + T := Nat.add_le_add_left (Finset.sum_le_sum (fun x _ => hCbig_card x.1 x.2)) r
    have hP₁_pos : 1 ≤ P₁ :=
      Finset.one_le_prod' (fun p hp => Nat.one_le_pow _ _ (hP_prime p (Finset.mem_filter.mp hp).1).pos)
    have hP₂_pos : 1 ≤ P₂ :=
      Finset.one_le_prod' (fun p hp => Nat.one_le_pow _ _ (hP_prime p (Finset.mem_filter.mp hp).1).pos)
    -- Exponential inequality on `P_big`!
    have hbig_strict : P_big.Nonempty → M ^ (a * T) < P₂ ^ (2 * (a + b)) := by
      intro hne
      have hterm : ∀ x ∈ P_big.attach,
          M ^ (a * tOf x.1 x.2) < (x.1 ^ E x.1) ^ (2 * (a + b)) := by
        intro x _
        have hp_prime := hP_prime x.1 (Finset.mem_filter.mp x.2).1
        have hlt_M := (Finset.mem_filter.mp x.2).2
        have hmin_le := ht_le_min x.1 x.2
        apply big_prime_pow_bound hp_prime ha hab hM hlt_M (ht_pos x.1 x.2)
          (le_trans hmin_le (min_le_left _ _)) (le_trans hmin_le (min_le_right _ _))
        intro ht2
        have hlt_spec : tOf x.1 x.2 - 1 < tOf x.1 x.2 := by omega
        have hnot := Nat.find_min (hex_t x.1 x.2) hlt_spec
        omega
      have hprod := prod_lt_prod_of_nonempty (Finset.attach_nonempty_iff.mpr hne) hterm
      have hLHS : ∏ x ∈ P_big.attach, M ^ (a * tOf x.1 x.2) = M ^ (a * T) := by
        rw [Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum]
      have hRHS : ∏ x ∈ P_big.attach, (x.1 ^ E x.1) ^ (2 * (a + b)) = P₂ ^ (2 * (a + b)) := by
        rw [Finset.prod_pow]
        congr 1
        exact Finset.prod_attach P_big (fun p => p ^ E p)
      rwa [hLHS, hRHS] at hprod
    have hbig_le : M ^ (a * T) ≤ P₂ ^ (2 * (a + b)) := by
      by_cases hne : P_big.Nonempty
      · exact le_of_lt (hbig_strict hne)
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        have hT0 : T = 0 := by simp [T, hne]
        rw [hT0, mul_zero, pow_zero]
        exact Nat.one_le_pow _ _ hP₂_pos
    have hmul_bound : a * (r + T) ≤ 2 * (a + b) * n + (a - 1) := by
      by_cases hr2 : 2 ≤ r
      · -- Case `2 ≤ r`: `M ^ (a * r) < P₁ ^ (2 * (a + b))`, so strict product `< M ^ (2 * (a + b) * n)`!
        have hMr_lt : M ^ r < P₁ ^ 2 := by
          have h1 : M ^ r < (M + 1) ^ r := Nat.pow_lt_pow_left (Nat.lt_succ_self M) (by omega)
          exact lt_of_lt_of_le h1 (hr_pow hr2)
        have hMar_lt : M ^ (a * r) < P₁ ^ (2 * (a + b)) := by
          have h1 : M ^ (a * r) < P₁ ^ (2 * a) := by
            calc M ^ (a * r) = (M ^ r) ^ a := by rw [← pow_mul, mul_comm a r]
              _ < (P₁ ^ 2) ^ a := Nat.pow_lt_pow_left hMr_lt (by omega)
              _ = P₁ ^ (2 * a) := (pow_mul P₁ 2 a).symm
          exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right hP₁_pos (by omega))
        have htot_lt : M ^ (a * (r + T)) < M ^ (2 * (a + b) * n) := by
          calc M ^ (a * (r + T)) = M ^ (a * r) * M ^ (a * T) := by rw [mul_add, pow_add]
            _ < P₁ ^ (2 * (a + b)) * P₂ ^ (2 * (a + b)) :=
                Nat.mul_lt_mul_of_lt_of_le' hMar_lt hbig_le (pow_pos (by omega : 0 < M) _)
            _ = (P₁ * P₂) ^ (2 * (a + b)) := (mul_pow P₁ P₂ (2 * (a + b))).symm
            _ ≤ (M ^ n) ^ (2 * (a + b)) :=
                Nat.pow_le_pow_left (hP₁_mul_P₂ ▸ hprodA_le_Mn) _
            _ = M ^ (2 * (a + b) * n) := by rw [← pow_mul, mul_comm n _]
        have hexp_lt : a * (r + T) < 2 * (a + b) * n :=
          (Nat.pow_lt_pow_iff_right hM_gt1).mp htot_lt
        omega
      · -- Case `r ≤ 1`
        have hr1 : r ≤ 1 := by omega
        by_cases hne : P_big.Nonempty
        · have hMT_lt : M ^ (a * T) < M ^ (2 * (a + b) * n) := by
            calc M ^ (a * T) < P₂ ^ (2 * (a + b)) := hbig_strict hne
              _ ≤ (P₁ * P₂) ^ (2 * (a + b)) :=
                  Nat.pow_le_pow_left (Nat.le_mul_of_pos_left P₂ hP₁_pos) _
              _ ≤ (M ^ n) ^ (2 * (a + b)) :=
                  Nat.pow_le_pow_left (hP₁_mul_P₂ ▸ hprodA_le_Mn) _
              _ = M ^ (2 * (a + b) * n) := by rw [← pow_mul, mul_comm n _]
          have hT_lt : a * T < 2 * (a + b) * n :=
            (Nat.pow_lt_pow_iff_right hM_gt1).mp hMT_lt
          have hT_le : a * T ≤ 2 * (a + b) * n - 1 := Nat.le_sub_one_of_lt hT_lt
          have har : a * r ≤ a * 1 := Nat.mul_le_mul_left a hr1
          calc a * (r + T) = a * r + a * T := Nat.mul_add a r T
            _ ≤ a * 1 + (2 * (a + b) * n - 1) := Nat.add_le_add har hT_le
            _ = 2 * (a + b) * n + (a - 1) := by
                have hge1 : 1 ≤ 2 * (a + b) * n := by nlinarith
                omega
        · rw [Finset.not_nonempty_iff_eq_empty] at hne
          have hT0 : T = 0 := by simp [T, hne]
          rw [hT0, add_zero]
          nlinarith
    rw [Nat.le_div_iff_mul_le ha]
    have : B.card * a = a * B.card := mul_comm _ _
    nlinarith
  · -- `(∏ x ∈ A, x) ∣ ∏ b ∈ B, b`
    have hB_sub_I : B ⊆ I := by
      apply Finset.union_subset hB₁_sub
      intro b hb
      rcases Finset.mem_biUnion.mp hb with ⟨⟨p, hp⟩, _, hbc⟩
      exact hCbig_sub p hp hbc
    have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => Nat.ne_of_gt (erdos708Interval_pos (hB_sub_I hb))
    apply prod_dvd_prod_of_factorization_le hA0 hB0
    intro p hp
    by_cases hp_in : p ∈ P_all
    · by_cases hp_sm : p ^ E p ≤ M
      · have hpP₁ : p ∈ P_small := Finset.mem_filter.mpr ⟨hp_in, hp_sm⟩
        have hpe_dvd_P₁ : p ^ E p ∣ P₁ := Finset.dvd_prod_of_mem (fun q => q ^ E q) hpP₁
        have hP₁_dvd_B : P₁ ∣ ∏ b ∈ B, b :=
          dvd_trans hB₁_dvd (Finset.prod_dvd_prod_of_subset B₁ B id Finset.subset_union_left)
        have hpe_dvd_B : p ^ E p ∣ ∏ b ∈ B, b := dvd_trans hpe_dvd_P₁ hP₁_dvd_B
        have hB_ne : ∏ b ∈ B, b ≠ 0 := Finset.prod_ne_zero_iff.mpr hB0
        have hle := (hp.pow_dvd_iff_le_factorization hB_ne).mp hpe_dvd_B
        rw [Nat.factorization_prod hB0] at hle
        simpa [E, Finsupp.coe_finsetSum, Finset.sum_apply] using hle
      · have hpP₂ : p ∈ P_big := Finset.mem_filter.mpr ⟨hp_in, lt_of_not_ge hp_sm⟩
        have hsub : Cbig p hpP₂ ⊆ B := by
          intro b hb
          exact Finset.mem_union_right B₁
            (Finset.mem_biUnion.mpr ⟨⟨p, hpP₂⟩, Finset.mem_attach _ _, hb⟩)
        exact le_trans (hCbig_val p hpP₂)
          (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _))
    · have hzero : ∀ x ∈ A, x.factorization p = 0 := by
        intro x hx
        have hnot : p ∉ x.primeFactors := fun h => hp_in (Finset.mem_biUnion.mpr ⟨x, hx, h⟩)
        rw [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] at hnot
        exact hnot
      rw [Finset.sum_eq_zero hzero]
      exact Nat.zero_le _

/-- Unit-numerator specialization (`a = 1`, `b = k`):
    whenever `|A| ^ (k + 1) ≤ (max A) ^ k` (`M ≥ n^{1 + 1/k}`), `|B| ≤ (2k + 2) |A|`. -/
theorem erdos708_coprime_dual_unit {A : Finset ℕ} (hA : ∀ x ∈ A, 1 ≤ x)
    (m k : ℕ) (hk : 1 ≤ k) (hM : A.card ^ (k + 1) ≤ (A.sup id) ^ k) :
    Erdos708Covers A m ((2 * k + 2) * A.card) := by
  have hcov := erdos708_coprime_dual_scale hA m 1 k (le_refl 1) hk (by simpa [add_comm] using hM)
  simpa [show 2 * (1 + k) = 2 * k + 2 by ring] using hcov

/-- **`4n` Bound for `M ≥ n²`** (3× sharper than Haoyu Chen's Sept 2026 Lean 4 record `12n`,
    and 9× lower threshold than `PPL176_UpperBinPack`'s `9 n²`). -/
theorem erdos708_four_n_of_ge_n2 {A : Finset ℕ} (hA : ∀ x ∈ A, 1 ≤ x) (m : ℕ)
    (hM : A.card ^ 2 ≤ A.sup id) :
    Erdos708Covers A m (4 * A.card) := by
  have hcov := erdos708_coprime_dual_unit hA m 1 (le_refl 1) (by simpa using hM)
  simpa using hcov

/-- **`5n` Bound for `M ≥ n^{5/3}`** (`|A|⁵ ≤ (max A)³`). -/
theorem erdos708_five_n_of_ge_n53 {A : Finset ℕ} (hA : ∀ x ∈ A, 1 ≤ x) (m : ℕ)
    (hM : A.card ^ 5 ≤ (A.sup id) ^ 3) :
    Erdos708Covers A m (5 * A.card) := by
  have hcov := erdos708_coprime_dual_scale hA m 2 3 (by omega) (by omega) (by simpa using hM)
  refine ⟨_, hcov.choose_spec.1, le_trans hcov.choose_spec.2.1 ?_, hcov.choose_spec.2.2⟩
  rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
  omega

/-- **`5n` Bound for `M ≥ n^{7/4}`** (3× sharper than Haoyu Chen's Sept 2026 Lean 4 record `15n`). -/
theorem erdos708_five_n_of_ge_n74 {A : Finset ℕ} (hA : ∀ x ∈ A, 1 ≤ x) (m : ℕ)
    (hM : A.card ^ 7 ≤ (A.sup id) ^ 4) :
    Erdos708Covers A m (5 * A.card) := by
  have hcov := erdos708_coprime_dual_scale hA m 3 4 (by omega) (by omega) (by simpa using hM)
  refine ⟨_, hcov.choose_spec.1, le_trans hcov.choose_spec.2.1 ?_, hcov.choose_spec.2.2⟩
  rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
  omega

/-- **`6n` Bound for `M ≥ n^{3/2}`** (`|A|³ ≤ (max A)²`). -/
theorem erdos708_six_n_of_ge_n32 {A : Finset ℕ} (hA : ∀ x ∈ A, 1 ≤ x) (m : ℕ)
    (hM : A.card ^ 3 ≤ (A.sup id) ^ 2) :
    Erdos708Covers A m (6 * A.card) := by
  have hcov := erdos708_coprime_dual_unit hA m 2 (by omega) (by simpa using hM)
  simpa using hcov

/-- **`8n` Bound for `M ≥ n^{4/3}`** (`|A|⁴ ≤ (max A)³`). -/
theorem erdos708_eight_n_of_ge_n43 {A : Finset ℕ} (hA : ∀ x ∈ A, 1 ≤ x) (m : ℕ)
    (hM : A.card ^ 4 ≤ (A.sup id) ^ 3) :
    Erdos708Covers A m (8 * A.card) := by
  have hcov := erdos708_coprime_dual_unit hA m 3 (by omega) (by simpa using hM)
  simpa using hcov

/-- Arbitrary integer-interval `I ⊂ ℤ` lifting of the prefactor-free `n^{k+1} ≤ M^k` bound. -/
theorem erdos708_coprime_dual_unit_int {A : Finset ℕ} (hA_ne : A.Nonempty)
    (hA : ∀ x ∈ A, 2 ≤ x) (m : ℤ) (k : ℕ) (hk : 1 ≤ k)
    (hM : A.card ^ (k + 1) ≤ (A.sup id) ^ k) :
    Erdos708CoversInt A m ((2 * k + 2) * A.card) := by
  have hcard_pos : 1 ≤ A.card := Finset.card_pos.mpr hA_ne
  have hk_pos : 1 ≤ (2 * k + 2) * A.card := by nlinarith
  exact erdos708CoversInt_of_nat hA_ne hA hk_pos
    (fun m₀ => erdos708_coprime_dual_unit (fun x hx => le_trans (by omega) (hA x hx)) m₀ k hk hM) m

/-- Arbitrary integer-interval `I ⊂ ℤ` `4n` bound for `M ≥ n²`. -/
theorem erdos708_four_n_of_ge_n2_int {A : Finset ℕ} (hA_ne : A.Nonempty)
    (hA : ∀ x ∈ A, 2 ≤ x) (m : ℤ) (hM : A.card ^ 2 ≤ A.sup id) :
    Erdos708CoversInt A m (4 * A.card) := by
  simpa using erdos708_coprime_dual_unit_int hA_ne hA m 1 (le_refl 1) (by simpa using hM)

/-- Arbitrary integer-interval `I ⊂ ℤ` `5n` bound for `M ≥ n^{7/4}`. -/
theorem erdos708_five_n_of_ge_n74_int {A : Finset ℕ} (hA_ne : A.Nonempty)
    (hA : ∀ x ∈ A, 2 ≤ x) (m : ℤ) (hM : A.card ^ 7 ≤ (A.sup id) ^ 4) :
    Erdos708CoversInt A m (5 * A.card) := by
  have hcard_pos : 1 ≤ A.card := Finset.card_pos.mpr hA_ne
  exact erdos708CoversInt_of_nat hA_ne hA (by omega)
    (fun m₀ => erdos708_five_n_of_ge_n74 (fun x hx => le_trans (by omega) (hA x hx)) m₀ hM) m

#print axioms erdos708_coprime_dual_scale
#print axioms erdos708_coprime_dual_unit
#print axioms erdos708_four_n_of_ge_n2
#print axioms erdos708_five_n_of_ge_n53
#print axioms erdos708_five_n_of_ge_n74
#print axioms erdos708_six_n_of_ge_n32
#print axioms erdos708_eight_n_of_ge_n43
#print axioms erdos708_four_n_of_ge_n2_int
#print axioms erdos708_five_n_of_ge_n74_int

end PPL176

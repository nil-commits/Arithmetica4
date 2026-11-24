import RHDirect.ChenDefs
import RHDirect.Stage2DirichletAP
import RHDirect.Stage8BarbanDavenport
import RHDirect.Stage10SiegelWalfiszFull
import RHDirect.Stage10ZeroDensity
import RHDirect.Stage11BombieriVinogradov

/-!
# RHDirect.ChenBilinearBV

**Unconditional Chen Switched Bilinear Bombieri–Vinogradov Theorem** for the triple-prime set
`chenM N` (and its product image `chenMProd N`) from `RHDirect.ChenDefs`, proved directly from
`RHDirect.Stage11BombieriVinogradov.bilinear_multiplicative_large_sieve`,
`RHDirect.Stage11BombieriVinogradov.multiplicative_large_sieve_Ioc_interval`, and
`RHDirect.Stage10SiegelWalfiszFull.siegel_walfisz_pi_real` in pure Mathlib `v4.33.1`.

## Architecture
1. **Unique-Factorization Bijection**: `chenM_prod_injOn` proves `t ↦ t.1 * t.2.1 * t.2.2` is
   injective on `chenM N`, yielding exact cardinality equalities between `chenM N` and `chenMProd N`
   as well as `(chenM N).card ≤ N`.
2. **Exact Squarefree Primitive-Character Orthogonality Identity**: for squarefree `d` coprime to
   `N` and any `m ≤ N`,
   `1_{d ∣ (N - m)} - 1 / φ(d) = φ(d)⁻¹ ∑_{χ ≠ 1} Re(conj(χ N) ψ_χ(m)) - 1_{¬ Coprime m d} φ(gcd(d, m))⁻¹ 1_{(d/gcd(d,m)) ∣ (N - m)}`,
   simultaneously absorbing both the principal character and primitive-conductor transfer errors
   into `O(N^{7/8} (1 + log N))`.
3. **Small-Conductor Bound (`3 ≤ r ≤ (log N)^{B₁}`)**: direct deduction of prime character-sum
   exponential decay from `Stage10SiegelWalfiszFull.siegel_walfisz_pi_real`, summed over `(q₁, q₂)`.
4. **Large-Conductor Bound (`(log N)^{B₁} < r ≤ √N / (log N)^B`)**: pure geometric box cover
   `(1 + Δ)^i` on `(q₂, q₁ * q₂)` splitting `chenM N` into disjoint bilinear rectangles (bounded
   via `Stage11BombieriVinogradov.bilinear_multiplicative_large_sieve`) and a thin boundary strip
   of size `O(Δ N log N)` (bounded via `multiplicative_large_sieve_Ioc_interval`).
5. **Headline Theorems**: `chen_bilinear_bombieri_vinogradov` and
   `chen_bilinear_bombieri_vinogradov_prod`.

Zero `sorry`, zero custom `axiom`s, zero `opaque`, zero `native_decide`.
-/

noncomputable section

open Complex DirichletCharacter Finset Set Filter Topology RHDirect RHDirect.Chen
open scoped BigOperators

namespace RHDirect.Chen

/-! ## Section 1: Unique-Factorization Bijections for `chenM N` and `chenMProd N` -/

/-- The triple-product map `(q₁, q₂, q₃) ↦ q₁ * q₂ * q₃` is injective on `chenM N`,
since `q₁ < N^{1/3} ≤ q₂ ≤ q₃` are all prime. -/
theorem chenM_prod_injOn (N : ℕ) :
    Set.InjOn (fun t : ℕ × ℕ × ℕ => t.1 * t.2.1 * t.2.2) (chenM N : Set (ℕ × ℕ × ℕ)) := by
  rintro ⟨p₁, p₂, p₃⟩ hp ⟨q₁, q₂, q₃⟩ hq hmul
  simp only [Finset.mem_coe, chenM, Finset.mem_filter] at hp hq
  rcases hp.2 with ⟨hp1, hp2, hp3, _, _, _, _, hp1_lt, hp2_ge, hp23, _⟩
  rcases hq.2 with ⟨hq1, hq2, hq3, _, _, _, _, hq1_lt, hq2_ge, hq23, _⟩
  have hp12 : p₁ < p₂ := by exact_mod_cast lt_of_lt_of_le hp1_lt hp2_ge
  have hq12 : q₁ < q₂ := by exact_mod_cast lt_of_lt_of_le hq1_lt hq2_ge
  have hle_of_dvd : ∀ {a b c d : ℕ}, a.Prime → b.Prime → c.Prime → d.Prime →
      b ≤ c → c ≤ d → a ∣ b * c * d → b ≤ a := by
    intro a b c d ha hb hc hd hbc hcd hdvd
    rcases ha.dvd_mul.mp hdvd with h1 | h3
    · rcases ha.dvd_mul.mp h1 with h1' | h2'
      · rw [(Nat.prime_dvd_prime_iff_eq ha hb).mp h1']
      · rw [(Nat.prime_dvd_prime_iff_eq ha hc).mp h2']; exact hbc
    · rw [(Nat.prime_dvd_prime_iff_eq ha hd).mp h3]; exact hbc.trans hcd
  have hp1_dvd : p₁ ∣ q₁ * q₂ * q₃ := ⟨p₂ * p₃, by linarith⟩
  have hq1_dvd : q₁ ∣ p₁ * p₂ * p₃ := ⟨q₂ * q₃, by linarith⟩
  have h1 : p₁ = q₁ := le_antisymm
    (hle_of_dvd hq1 hp1 hp2 hp3 hp12.le hp23 hq1_dvd)
    (hle_of_dvd hp1 hq1 hq2 hq3 hq12.le hq23 hp1_dvd)
  subst h1
  have hmul23 : p₂ * p₃ = q₂ * q₃ := by
    have hEq : p₁ * (p₂ * p₃) = p₁ * (q₂ * q₃) := by linarith
    exact Nat.mul_left_cancel hp1.pos hEq
  have hle2 : ∀ {a b c : ℕ}, a.Prime → b.Prime → c.Prime → b ≤ c → a ∣ b * c → b ≤ a := by
    intro a b c ha hb hc hbc hdvd
    rcases ha.dvd_mul.mp hdvd with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq ha hb).mp h]
    · rw [(Nat.prime_dvd_prime_iff_eq ha hc).mp h]; exact hbc
  have h2 : p₂ = q₂ := le_antisymm
    (hle2 hq2 hp2 hp3 hp23 ⟨q₃, by linarith⟩)
    (hle2 hp2 hq2 hq3 hq23 ⟨p₃, by linarith⟩)
  subst h2
  have h3 : p₃ = q₃ := Nat.mul_left_cancel hp2.pos hmul23
  subst h3
  rfl

/-- Exact cardinality equality `(chenMProd N).card = (chenM N).card`. -/
theorem card_chenMProd_eq (N : ℕ) : (chenMProd N).card = (chenM N).card :=
  Finset.card_image_of_injOn (chenM_prod_injOn N)

/-- Exact filtered cardinality equality for divisibility of `N - m` on `chenMProd N` vs `chenM N`. -/
theorem card_chenMProd_filter_dvd_eq (N d : ℕ) :
    ((chenMProd N).filter (fun m => d ∣ (N - m))).card =
      ((chenM N).filter (fun t => d ∣ (N - t.1 * t.2.1 * t.2.2))).card := by
  unfold chenMProd
  rw [Finset.filter_image]
  exact Finset.card_image_of_injOn
    ((chenM_prod_injOn N).mono (by intro t ht; exact (Finset.mem_filter.mp ht).1))

/-- Every triple in `chenM N` has product strictly less than `N`, so `(chenM N).card ≤ N`. -/
theorem card_chenM_le (N : ℕ) : (chenM N).card ≤ N := by
  rw [← card_chenMProd_eq]
  have hsub : chenMProd N ⊆ Finset.range N := by
    intro m hm
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hm
    simp only [chenM, Finset.mem_filter] at ht
    exact Finset.mem_range.mpr ht.2.2.2.2.2.2.2.2.2.2.2
  exact (Finset.card_le_card hsub).trans (by rw [Finset.card_range])

/-- The pair of the first two primes `(q₁, q₂)` occurring in `chenM N`. -/
def chenMPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range N).product (Finset.range N)).filter fun p =>
    p.1.Prime ∧ p.2.Prime ∧
    ¬ p.1 ∣ N ∧ ¬ p.2 ∣ N ∧
    (N : ℝ) ^ ((1 : ℝ) / 8) ≤ (p.1 : ℝ) ∧
    (p.1 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 3) ∧
    (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (p.2 : ℝ) ∧
    p.1 * p.2 * p.2 < N

/-- The pair-product map `(q₁, q₂) ↦ q₁ * q₂` is injective on `chenMPairs N`,
since `q₁ < N^{1/3} ≤ q₂` are primes. -/
theorem chenMPairs_prod_injOn (N : ℕ) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2) (chenMPairs N : Set (ℕ × ℕ)) := by
  rintro ⟨p₁, p₂⟩ hp ⟨q₁, q₂⟩ hq hmul
  simp only [Finset.mem_coe, chenMPairs, Finset.mem_filter] at hp hq
  rcases hp.2 with ⟨hp1, hp2, _, _, _, hp1_lt, hp2_ge, _⟩
  rcases hq.2 with ⟨hq1, hq2, _, _, _, hq1_lt, hq2_ge, _⟩
  have hp12 : p₁ < p₂ := by exact_mod_cast lt_of_lt_of_le hp1_lt hp2_ge
  have hq12 : q₁ < q₂ := by exact_mod_cast lt_of_lt_of_le hq1_lt hq2_ge
  have hle2 : ∀ {a b c : ℕ}, a.Prime → b.Prime → c.Prime → b ≤ c → a ∣ b * c → b ≤ a := by
    intro a b c ha hb hc hbc hdvd
    rcases ha.dvd_mul.mp hdvd with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq ha hb).mp h]
    · rw [(Nat.prime_dvd_prime_iff_eq ha hc).mp h]; exact hbc
  have h1 : p₁ = q₁ := le_antisymm
    (hle2 hq1 hp1 hp2 hp12.le ⟨q₂, by linarith⟩)
    (hle2 hp1 hq1 hq2 hq12.le ⟨p₂, by linarith⟩)
  subst h1
  have h2 : p₂ = q₂ := Nat.mul_left_cancel hp1.pos hmul
  subst h2
  rfl

/-! ## Section 2: Exact Squarefree Character Orthogonality & Primitive-Conductor Transfer -/

/-- Character sum over Chen's triple-prime set: `∑_{(q₁, q₂, q₃) ∈ chenM N} χ(q₁ q₂ q₃)`. -/
def chenMCharSum {r : ℕ} (χ : DirichletCharacter ℂ r) (N : ℕ) : ℂ :=
  ∑ t ∈ chenM N, χ ((t.1 * t.2.1 * t.2.2 : ℕ) : ZMod r)

/-- For `m ≤ N`, `d ∣ (N - m)` is equivalent to `m ≡ N [MOD d]`. -/
private lemma dvd_sub_iff_modEq {N m d : ℕ} (hmN : m ≤ N) :
    d ∣ (N - m) ↔ m ≡ N [MOD d] := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [Nat.ModEq]
    omega
  · constructor
    · rintro ⟨k, hk⟩
      have hN : N = m + d * k := by omega
      show m % d = N % d
      rw [hN, Nat.add_mul_mod_self_left]
    · intro hmod
      have hmod' : m % d = N % d := hmod
      have hdiv_le : m / d ≤ N / d := Nat.div_le_div_right hmN
      refine ⟨N / d - m / d, ?_⟩
      have h1 := Nat.div_add_mod N d
      have h2 := Nat.div_add_mod m d
      rw [Nat.mul_sub_left_distrib]
      omega

/-- Coprimality consequences of `Squarefree d` for `g = gcd(d, m)` and `d' = d / g`. -/
private lemma squarefree_gcd_div_coprime {d m : ℕ} (hsq : Squarefree d) :
    Nat.Coprime m (d / Nat.gcd d m) ∧ Nat.Coprime (Nat.gcd d m) (d / Nat.gcd d m) := by
  set g := Nat.gcd d m
  set d' := d / g
  have hgd : g * d' = d := Nat.mul_div_cancel' (Nat.gcd_dvd_left d m)
  constructor
  · by_contra hncop
    have hne1 : Nat.gcd m d' ≠ 1 := hncop
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne1
    have hpm : p ∣ m := hpdvd.trans (Nat.gcd_dvd_left m d')
    have hpd' : p ∣ d' := hpdvd.trans (Nat.gcd_dvd_right m d')
    have hpd : p ∣ d := hpd'.trans ⟨g, by linarith⟩
    have hpg : p ∣ g := Nat.dvd_gcd hpd hpm
    have hpp : p * p ∣ d := by
      rw [← hgd]
      exact mul_dvd_mul hpg hpd'
    exact hp.ne_one (Nat.isUnit_iff.mp (hsq p hpp))
  · by_contra hncop
    have hne1 : Nat.gcd g d' ≠ 1 := hncop
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne1
    have hpg : p ∣ g := hpdvd.trans (Nat.gcd_dvd_left g d')
    have hpd' : p ∣ d' := hpdvd.trans (Nat.gcd_dvd_right g d')
    have hpp : p * p ∣ d := by
      rw [← hgd]
      exact mul_dvd_mul hpg hpd'
    exact hp.ne_one (Nat.isUnit_iff.mp (hsq p hpp))

/-- For `d' ∣ d` and `η : DirichletCharacter ℂ d'` with `Nat.Coprime m d'`, the induced character
`χ = changeLevel hd'd η` satisfies `χ.primitiveCharacter m = η m`. -/
private lemma primitiveCharacter_changeLevel_apply_of_coprime {d' d m : ℕ} [NeZero d'] [NeZero d]
    (hd'd : d' ∣ d) (η : DirichletCharacter ℂ d') (hcop : Nat.Coprime m d') :
    (DirichletCharacter.changeLevel hd'd η).primitiveCharacter
        (m : ZMod (DirichletCharacter.changeLevel hd'd η).conductor) =
      η (m : ZMod d') := by
  set χ := DirichletCharacter.changeLevel hd'd η
  have hcond_eq : χ.conductor = η.conductor := DirichletCharacter.conductor_changeLevel η hd'd
  have hcond_dvd_d' : χ.conductor ∣ d' := hcond_eq ▸ η.conductor_dvd_level
  have hchg_eq : DirichletCharacter.changeLevel hcond_dvd_d' χ.primitiveCharacter = η := by
    apply DirichletCharacter.changeLevel_injective hd'd
    rw [← DirichletCharacter.changeLevel_trans χ.primitiveCharacter hcond_dvd_d' hd'd]
    exact χ.changeLevel_primitiveCharacter
  rw [← hchg_eq]
  exact (Stage8BarbanDavenport.changeLevel_apply_nat_of_coprime hcond_dvd_d'
    χ.primitiveCharacter hcop).symm

open Classical in
/-- **Exact Squarefree Primitive-Character Orthogonality Identity**:
for every `d ≥ 1` (`[NeZero d]`) with `Squarefree d` and `Nat.Coprime d N`, and every `m ≤ N`:
`1_{d ∣ (N - m)} - 1 / φ(d) = φ(d)⁻¹ ∑_{χ ≠ 1} Re(conj(χ N) ψ_χ(m)) - 1_{¬ Coprime m d} φ(gcd(d, m))⁻¹ 1_{(d/gcd(d,m)) ∣ (N - m)}`. -/
private lemma indicator_dvd_sub_eq_prim_sum {N m d : ℕ} [NeZero d]
    (hsq : Squarefree d) (hcopN : Nat.Coprime d N) (hmN : m ≤ N) :
    (if d ∣ (N - m) then (1 : ℝ) else 0) - (d.totient : ℝ)⁻¹ =
      (d.totient : ℝ)⁻¹ *
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ d),
          (starRingEnd ℂ (χ (N : ZMod d)) * χ.primitiveCharacter (m : ZMod χ.conductor)).re -
      if ¬ Nat.Coprime m d then
        ((Nat.gcd d m).totient : ℝ)⁻¹ *
          (if (d / Nat.gcd d m) ∣ (N - m) then (1 : ℝ) else 0)
      else 0 := by
  have hd_pos : 0 < d := NeZero.pos d
  have hphi_pos : (0 : ℝ) < (d.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hd_pos)
  by_cases hcopm : Nat.Coprime m d
  · -- Case 1: `Nat.Coprime m d`
    rw [if_neg (not_not.mpr hcopm), sub_zero]
    have horth := Stage2DirichletAP.char_orthogonality_indicator_nat_re hcopN.symm m
    have h1_term : (starRingEnd ℂ ((1 : DirichletCharacter ℂ d) (N : ZMod d)) *
        (1 : DirichletCharacter ℂ d) (m : ZMod d)).re = 1 := by
      rw [Stage2DirichletAP.principal_char_apply_nat N,
        Stage2DirichletAP.principal_char_apply_nat m,
        if_pos hcopN.symm, if_pos hcopm]
      simp
    have hsum_split :
        ∑ χ : DirichletCharacter ℂ d,
            (starRingEnd ℂ (χ (N : ZMod d)) * χ (m : ZMod d)).re =
          1 + ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ d),
            (starRingEnd ℂ (χ (N : ZMod d)) * χ.primitiveCharacter (m : ZMod χ.conductor)).re := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ d)), h1_term]
      congr 1
      refine Finset.sum_congr rfl fun χ _ => ?_
      have hval : χ (m : ZMod d) = χ.primitiveCharacter (m : ZMod χ.conductor) := by
        conv_lhs => rw [← χ.changeLevel_primitiveCharacter]
        exact Stage8BarbanDavenport.changeLevel_apply_nat_of_coprime
          χ.conductor_dvd_level χ.primitiveCharacter hcopm
      rw [hval]
    have hiff : (if d ∣ (N - m) then (1 : ℝ) else 0) = if m ≡ N [MOD d] then 1 else 0 := by
      by_cases h : d ∣ (N - m)
      · rw [if_pos h, if_pos ((dvd_sub_iff_modEq hmN).mp h)]
      · rw [if_neg h, if_neg (fun h' => h ((dvd_sub_iff_modEq hmN).mpr h'))]
    rw [hiff, ← horth, hsum_split]
    ring
  · -- Case 2: `¬ Nat.Coprime m d`
    rw [if_pos hcopm]
    have hndvd : ¬ d ∣ (N - m) := by
      intro hdvd
      have hmod : m % d = N % d := (dvd_sub_iff_modEq hmN).mp hdvd
      have hgcd : Nat.gcd m d = Nat.gcd N d := by
        rw [Nat.gcd_comm m d, Nat.gcd_rec d m, hmod, ← Nat.gcd_rec d N, Nat.gcd_comm]
      exact hcopm (by rw [Nat.coprime_iff_gcd_eq_one, hgcd]; exact hcopN.symm.gcd_eq_one)
    rw [if_neg hndvd]
    set g := Nat.gcd d m
    set d' := d / g
    have hg_dvd : g ∣ d := Nat.gcd_dvd_left d m
    have hgd_eq : g * d' = d := Nat.mul_div_cancel' hg_dvd
    have hd'_dvd : d' ∣ d := ⟨g, by linarith⟩
    have hd'_pos : 0 < d' := by
      by_contra h0
      have hd'0 : d' = 0 := Nat.eq_zero_of_not_pos h0
      rw [hd'0, mul_zero] at hgd_eq
      exact hd_pos.ne' hgd_eq.symm
    have hg_pos : 0 < g := by
      by_contra h0
      have hg0 : g = 0 := Nat.eq_zero_of_not_pos h0
      rw [hg0, zero_mul] at hgd_eq
      exact hd_pos.ne' hgd_eq.symm
    have : NeZero d' := ⟨hd'_pos.ne'⟩
    obtain ⟨hcop_md', hcop_gd'⟩ := squarefree_gcd_div_coprime hsq
    have hcop_Nd' : Nat.Coprime N d' := hcopN.symm.coprime_dvd_right hd'_dvd
    have htot_eq : d.totient = g.totient * d'.totient := by
      rw [← hgd_eq, Nat.totient_mul hcop_gd']
    -- Identify `1 + ∑_{χ ≠ 1} conj(χ N) ψ_χ(m)` with the full character sum mod `d'`
    have h1_prim : (starRingEnd ℂ ((1 : DirichletCharacter ℂ d) (N : ZMod d)) *
        (1 : DirichletCharacter ℂ d).primitiveCharacter
          (m : ZMod (1 : DirichletCharacter ℂ d).conductor)).re = 1 := by
      have hN1 : (1 : DirichletCharacter ℂ d) (N : ZMod d) = 1 := by
        rw [Stage2DirichletAP.principal_char_apply_nat, if_pos hcopN.symm]
      have hm1 : (1 : DirichletCharacter ℂ d).primitiveCharacter
          (m : ZMod (1 : DirichletCharacter ℂ d).conductor) = 1 := by
        have hcond1 : (1 : DirichletCharacter ℂ d).conductor = 1 := DirichletCharacter.conductor_one
        have hu : IsUnit (m : ZMod (1 : DirichletCharacter ℂ d).conductor) :=
          Stage2DirichletAP.isUnit_zmod_of_coprime (by rw [hcond1]; exact Nat.coprime_one_right m)
        have hprim1 : (1 : DirichletCharacter ℂ d).primitiveCharacter = 1 := by
          apply DirichletCharacter.changeLevel_injective (1 : DirichletCharacter ℂ d).conductor_dvd_level
          rw [(1 : DirichletCharacter ℂ d).changeLevel_primitiveCharacter, map_one]
        rw [hprim1, MulChar.one_apply hu]
      rw [hN1, hm1]
      simp
    have hfull_eq_filt :
        ∑ χ : DirichletCharacter ℂ d,
            (starRingEnd ℂ (χ (N : ZMod d)) * χ.primitiveCharacter (m : ZMod χ.conductor)).re =
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.conductor ∣ d'),
            (starRingEnd ℂ (χ (N : ZMod d)) * χ.primitiveCharacter (m : ZMod χ.conductor)).re := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun χ _ => ?_
      by_cases hcd : χ.conductor ∣ d'
      · rw [if_pos hcd]
      · rw [if_neg hcd]
        have hncop_mc : ¬ Nat.Coprime m χ.conductor := by
          intro hcop_mc
          have hcop_gc : Nat.Coprime g χ.conductor := hcop_mc.coprime_dvd_left (Nat.gcd_dvd_right d m)
          have hdvd_gd' : χ.conductor ∣ g * d' := hgd_eq.symm ▸ χ.conductor_dvd_level
          exact hcd (hcop_gc.symm.dvd_of_dvd_mul_left hdvd_gd')
        have hnu : ¬ IsUnit (m : ZMod χ.conductor) :=
          fun hu => hncop_mc ((ZMod.isUnit_iff_coprime m χ.conductor).mp hu)
        rw [MulChar.map_nonunit _ hnu, mul_zero, Complex.zero_re]
    have hbij :
        ∑ η : DirichletCharacter ℂ d',
            (starRingEnd ℂ (η (N : ZMod d')) * η (m : ZMod d')).re =
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.conductor ∣ d'),
            (starRingEnd ℂ (χ (N : ZMod d)) * χ.primitiveCharacter (m : ZMod χ.conductor)).re := by
      refine Finset.sum_bij (fun η _ => DirichletCharacter.changeLevel hd'_dvd η) ?_ ?_ ?_ ?_
      · intro η _
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [DirichletCharacter.conductor_changeLevel η hd'_dvd]
        exact η.conductor_dvd_level
      · intro η₁ _ η₂ _ h
        exact DirichletCharacter.changeLevel_injective hd'_dvd h
      · intro χ hχ
        have hcd : χ.conductor ∣ d' := (Finset.mem_filter.mp hχ).2
        refine ⟨DirichletCharacter.changeLevel hcd χ.primitiveCharacter, Finset.mem_univ _, ?_⟩
        rw [← DirichletCharacter.changeLevel_trans χ.primitiveCharacter hcd hd'_dvd]
        exact χ.changeLevel_primitiveCharacter
      · intro η _
        have hN_eq : DirichletCharacter.changeLevel hd'_dvd η (N : ZMod d) = η (N : ZMod d') :=
          Stage8BarbanDavenport.changeLevel_apply_nat_of_coprime hd'_dvd η hcopN.symm
        have hm_eq := primitiveCharacter_changeLevel_apply_of_coprime hd'_dvd η hcop_md'
        rw [hN_eq, hm_eq]
    have horth' := Stage2DirichletAP.char_orthogonality_indicator_nat_re hcop_Nd' m
    have hphi'_pos : (0 : ℝ) < (d'.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hd'_pos)
    have hgphi_pos : (0 : ℝ) < (g.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hg_pos)
    have hsum_d' :
        ∑ η : DirichletCharacter ℂ d',
            (starRingEnd ℂ (η (N : ZMod d')) * η (m : ZMod d')).re =
          (d'.totient : ℝ) * (if d' ∣ (N - m) then (1 : ℝ) else 0) := by
      have hiff : (if d' ∣ (N - m) then (1 : ℝ) else 0) = if m ≡ N [MOD d'] then 1 else 0 := by
        by_cases h : d' ∣ (N - m)
        · rw [if_pos h, if_pos ((dvd_sub_iff_modEq hmN).mp h)]
        · rw [if_neg h, if_neg (fun h' => h ((dvd_sub_iff_modEq hmN).mpr h'))]
      rw [hiff, ← horth', ← mul_assoc, mul_inv_cancel₀ hphi'_pos.ne', one_mul]
    have hsum_erase :
        1 + ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ d),
              (starRingEnd ℂ (χ (N : ZMod d)) * χ.primitiveCharacter (m : ZMod χ.conductor)).re =
          (d'.totient : ℝ) * (if d' ∣ (N - m) then (1 : ℝ) else 0) := by
      have hadd := Finset.add_sum_erase
        (s := (Finset.univ : Finset (DirichletCharacter ℂ d)))
        (f := fun χ : DirichletCharacter ℂ d =>
          (starRingEnd ℂ (χ (N : ZMod d)) * χ.primitiveCharacter (m : ZMod χ.conductor)).re)
        (Finset.mem_univ (1 : DirichletCharacter ℂ d))
      rw [h1_prim] at hadd
      rw [hadd, hfull_eq_filt, ← hbij, hsum_d']
    have htotR : (d.totient : ℝ) = (g.totient : ℝ) * (d'.totient : ℝ) := by exact_mod_cast htot_eq
    have hmul_cancel :
        (d.totient : ℝ)⁻¹ * ((d'.totient : ℝ) * (if d' ∣ (N - m) then (1 : ℝ) else 0)) =
          (g.totient : ℝ)⁻¹ * (if d' ∣ (N - m) then (1 : ℝ) else 0) := by
      rw [htotR]
      field_simp [hgphi_pos.ne', hphi'_pos.ne']
    have hfinal :
        (d.totient : ℝ)⁻¹ * (1 + ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ d),
          (starRingEnd ℂ (χ (N : ZMod d)) * χ.primitiveCharacter (m : ZMod χ.conductor)).re) =
        (g.totient : ℝ)⁻¹ * (if d' ∣ (N - m) then (1 : ℝ) else 0) := by
      rw [hsum_erase, hmul_cancel]
    linarith

/-- Elementary divisor sum bound `∑_{k=1}^N τ(k) ≤ N * (1 + log N)` for `N ≥ 1`. -/
private lemma sum_divisors_card_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ Finset.Icc 1 N, (k.divisors.card : ℝ) ≤ (N : ℝ) * (1 + Real.log (N : ℝ)) := by
  have hswap :
      ∑ k ∈ Finset.Icc 1 N, (k.divisors.card : ℝ) =
        ∑ a ∈ Finset.Icc 1 N, (((Finset.Icc 1 N).filter (fun k => a ∣ k)).card : ℝ) := by
    have h1 : ∀ k ∈ Finset.Icc 1 N,
        (k.divisors.card : ℝ) = ∑ a ∈ Finset.Icc 1 N, if a ∣ k then (1 : ℝ) else 0 := by
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      congr 1
      congr 1
      ext a
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hak, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hak hk1, (Nat.le_of_dvd hk1 hak).trans hkN⟩, hak⟩
      · rintro ⟨_, hak⟩
        exact ⟨hak, by omega⟩
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hswap]
  have hper : ∀ a ∈ Finset.Icc 1 N,
      (((Finset.Icc 1 N).filter (fun k => a ∣ k)).card : ℝ) ≤ (N : ℝ) / (a : ℝ) := by
    intro a ha
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    have hcard_le : ((Finset.Icc 1 N).filter (fun k => a ∣ k)).card ≤ N / a := by
      have hinj : Set.InjOn (fun k => k / a)
          (((Finset.Icc 1 N).filter (fun k => a ∣ k)) : Set ℕ) := by
        intro k₁ hk₁ k₂ hk₂ h
        dsimp only at h
        have h1 : a * (k₁ / a) = k₁ := Nat.mul_div_cancel' (Finset.mem_filter.mp hk₁).2
        have h2 : a * (k₂ / a) = k₂ := Nat.mul_div_cancel' (Finset.mem_filter.mp hk₂).2
        rw [← h1, ← h2, h]
      have hsub : ((Finset.Icc 1 N).filter (fun k => a ∣ k)).image (fun k => k / a) ⊆
          Finset.Icc 1 (N / a) := by
        intro q hq
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hq
        simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
        have hka : a ≤ k := Nat.le_of_dvd hk.1.1 hk.2
        exact ⟨Nat.div_pos hka ha1, Nat.div_le_div_right hk.1.2⟩
      calc ((Finset.Icc 1 N).filter (fun k => a ∣ k)).card
          = (((Finset.Icc 1 N).filter (fun k => a ∣ k)).image (fun k => k / a)).card :=
            (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.Icc 1 (N / a)).card := Finset.card_le_card hsub
        _ = N / a := by simp [Nat.card_Icc]
    calc (((Finset.Icc 1 N).filter (fun k => a ∣ k)).card : ℝ)
        ≤ ((N / a : ℕ) : ℝ) := by exact_mod_cast hcard_le
      _ ≤ (N : ℝ) / (a : ℝ) := Nat.cast_div_le
  calc ∑ a ∈ Finset.Icc 1 N, (((Finset.Icc 1 N).filter (fun k => a ∣ k)).card : ℝ)
      ≤ ∑ a ∈ Finset.Icc 1 N, (N : ℝ) / (a : ℝ) := Finset.sum_le_sum hper
    _ = (N : ℝ) * ∑ a ∈ Finset.Icc 1 N, (1 : ℝ) / (a : ℝ) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => by ring
    _ ≤ (N : ℝ) * (1 + Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (Stage10ZeroDensity.sum_inv_le_one_add_log hN) (Nat.cast_nonneg _)

/-- Every product of three primes has at most `8` divisors. -/
private lemma divisors_card_mul_mul_le_eight {p q r : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) : (p * q * r).divisors.card ≤ 8 := by
  have hsub : (p * q * r).divisors ⊆
      (p.divisors ×ˢ (q.divisors ×ˢ r.divisors)).image (fun t => t.1 * t.2.1 * t.2.2) := by
    intro d hd
    have hdvd : d ∣ p * q * r := (Nat.mem_divisors.mp hd).1
    obtain ⟨ab, c, hab, hc, rfl⟩ := Nat.dvd_mul.mp hdvd
    obtain ⟨a, b, ha, hb, rfl⟩ := Nat.dvd_mul.mp hab
    exact Finset.mem_image.mpr ⟨(a, b, c),
      Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨ha, hp.ne_zero⟩,
        Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hb, hq.ne_zero⟩,
          Nat.mem_divisors.mpr ⟨hc, hr.ne_zero⟩⟩⟩, rfl⟩
  have hp2 : p.divisors.card = 2 := by rw [hp.divisors, Finset.card_pair hp.ne_one.symm]
  have hq2 : q.divisors.card = 2 := by rw [hq.divisors, Finset.card_pair hq.ne_one.symm]
  have hr2 : r.divisors.card = 2 := by rw [hr.divisors, Finset.card_pair hr.ne_one.symm]
  calc (p * q * r).divisors.card
      ≤ ((p.divisors ×ˢ (q.divisors ×ˢ r.divisors)).image (fun t => t.1 * t.2.1 * t.2.2)).card :=
        Finset.card_le_card hsub
    _ ≤ (p.divisors ×ˢ (q.divisors ×ˢ r.divisors)).card := Finset.card_image_le
    _ = p.divisors.card * (q.divisors.card * r.divisors.card) := by
        rw [Finset.card_product, Finset.card_product]
    _ = 8 := by rw [hp2, hq2, hr2]

/-- Bound on the summed coprimality correction over all squarefree `d ∈ Icc 1 Q` coprime to `N`:
for `N ≥ 256`,
`∑_{d ∈ D} ∑_{t ∈ chenM N} 1_{¬ Coprime (m t) d} φ(gcd(d, m t))⁻¹ 1_{(d/gcd(d, m t)) ∣ (N - m t)} ≤ 16 * N^{7/8} * (1 + log N)`. -/
private lemma sum_coprime_correction_le {N Q : ℕ} (hN : 256 ≤ N) :
    ∑ d ∈ (Finset.Icc 1 Q).filter (fun d => Squarefree d ∧ Nat.Coprime d N),
      ∑ t ∈ chenM N,
        (if ¬ Nat.Coprime (t.1 * t.2.1 * t.2.2) d then
          ((Nat.gcd d (t.1 * t.2.1 * t.2.2)).totient : ℝ)⁻¹ *
            (if (d / Nat.gcd d (t.1 * t.2.1 * t.2.2)) ∣ (N - t.1 * t.2.1 * t.2.2) then (1 : ℝ) else 0)
        else 0) ≤
      16 * (N : ℝ) ^ ((7 : ℝ) / 8) * (1 + Real.log (N : ℝ)) := by
  set D := (Finset.Icc 1 Q).filter (fun d => Squarefree d ∧ Nat.Coprime d N)
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN8_ge2 : (2 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := by
    have h256 : (2 : ℝ) ^ (8 : ℝ) ≤ (N : ℝ) := by
      calc (2 : ℝ) ^ (8 : ℝ) = (256 : ℝ) := by norm_num
        _ ≤ (N : ℝ) := by exact_mod_cast hN
    calc (2 : ℝ) = ((2 : ℝ) ^ (8 : ℝ)) ^ ((1 : ℝ) / 8) := by
          rw [← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := Real.rpow_le_rpow (by positivity) h256 (by norm_num)
  have hN8_pos : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 8) := by linarith
  rw [Finset.sum_comm]
  have hper_t : ∀ t ∈ chenM N,
      ∑ d ∈ D,
          (if ¬ Nat.Coprime (t.1 * t.2.1 * t.2.2) d then
            ((Nat.gcd d (t.1 * t.2.1 * t.2.2)).totient : ℝ)⁻¹ *
              (if (d / Nat.gcd d (t.1 * t.2.1 * t.2.2)) ∣ (N - t.1 * t.2.1 * t.2.2) then (1 : ℝ) else 0)
          else 0) ≤
        (16 / (N : ℝ) ^ ((1 : ℝ) / 8)) * ((N - t.1 * t.2.1 * t.2.2).divisors.card : ℝ) := by
    intro t ht
    simp only [chenM, Finset.mem_filter] at ht
    rcases ht.2 with ⟨hq1, hq2, hq3, _, _, _, hq1_ge, hq1_lt, hq2_ge, hq23, hprod_lt⟩
    set m := t.1 * t.2.1 * t.2.2
    have hq1_le_q2 : t.1 ≤ t.2.1 := by exact_mod_cast (lt_of_lt_of_le hq1_lt hq2_ge).le
    have hphi_ge : ∀ g : ℕ, g ∈ m.divisors.erase 1 →
        (N : ℝ) ^ ((1 : ℝ) / 8) / 2 ≤ (g.totient : ℝ) := by
      intro g hg
      have hg_ne1 : g ≠ 1 := (Finset.mem_erase.mp hg).1
      have hg_dvd : g ∣ m := (Nat.mem_divisors.mp (Finset.mem_erase.mp hg).2).1
      obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg_ne1
      have hpm : p ∣ t.1 * t.2.1 * t.2.2 := hpg.trans hg_dvd
      have hq1_le_p : t.1 ≤ p := by
        rcases hp.dvd_mul.mp hpm with h12 | h3
        · rcases hp.dvd_mul.mp h12 with h1 | h2
          · rw [(Nat.prime_dvd_prime_iff_eq hp hq1).mp h1]
          · rw [(Nat.prime_dvd_prime_iff_eq hp hq2).mp h2]; exact hq1_le_q2
        · rw [(Nat.prime_dvd_prime_iff_eq hp hq3).mp h3]; exact hq1_le_q2.trans hq23
      have hp_ge : (N : ℝ) ^ ((1 : ℝ) / 8) ≤ (p : ℝ) :=
        hq1_ge.trans (by exact_mod_cast hq1_le_p)
      have htot_dvd : p.totient ∣ g.totient := Nat.totient_dvd_of_dvd hpg
      have hg_pos : 0 < g := Nat.pos_of_dvd_of_pos hg_dvd (by positivity [hq1.pos, hq2.pos, hq3.pos])
      have htot_le : p - 1 ≤ g.totient := by
        rw [← Nat.totient_prime hp]
        exact Nat.le_of_dvd (Nat.totient_pos.mpr hg_pos) htot_dvd
      have htotR : (p : ℝ) - 1 ≤ (g.totient : ℝ) := by
        have hp1 : 1 ≤ p := hp.one_lt.le
        have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by simpa using Nat.cast_sub hp1
        rw [← hcast]; exact_mod_cast htot_le
      linarith
    set D_hit := D.filter (fun d => ¬ Nat.Coprime m d ∧ (d / Nat.gcd d m) ∣ (N - m))
    have hsum_eq :
        ∑ d ∈ D,
            (if ¬ Nat.Coprime m d then
              ((Nat.gcd d m).totient : ℝ)⁻¹ *
                (if (d / Nat.gcd d m) ∣ (N - m) then (1 : ℝ) else 0)
            else 0) =
          ∑ d ∈ D_hit, ((Nat.gcd d m).totient : ℝ)⁻¹ := by
      symm
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun d _ => ?_
      by_cases h1 : ¬ Nat.Coprime m d <;> by_cases h2 : (d / Nat.gcd d m) ∣ (N - m) <;>
        simp [h1, h2]
    rw [hsum_eq]
    have hterm_le : ∀ d ∈ D_hit, ((Nat.gcd d m).totient : ℝ)⁻¹ ≤ 2 / (N : ℝ) ^ ((1 : ℝ) / 8) := by
      intro d hd
      have hncop : ¬ Nat.Coprime m d := (Finset.mem_filter.mp hd).2.1
      have hg_mem : Nat.gcd d m ∈ m.divisors.erase 1 := by
        refine Finset.mem_erase.mpr ⟨?_, Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right d m, ?_⟩⟩
        · intro h1; exact hncop (by rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]; exact h1)
        · exact (mul_pos (mul_pos hq1.pos hq2.pos) hq3.pos).ne'
      have hge := hphi_ge (Nat.gcd d m) hg_mem
      calc ((Nat.gcd d m).totient : ℝ)⁻¹
          ≤ ((N : ℝ) ^ ((1 : ℝ) / 8) / 2)⁻¹ := inv_anti₀ (by positivity) hge
        _ = 2 / (N : ℝ) ^ ((1 : ℝ) / 8) := by field_simp [hN8_pos.ne']
    have hcard_hit : D_hit.card ≤ 8 * (N - m).divisors.card := by
      let f : ℕ → ℕ × ℕ := fun d => (Nat.gcd d m, d / Nat.gcd d m)
      have hinj : Set.InjOn f (D_hit : Set ℕ) := by
        intro d₁ _ d₂ _ h
        have h1 : (f d₁).1 * (f d₁).2 = d₁ := Nat.mul_div_cancel' (Nat.gcd_dvd_left d₁ m)
        have h2 : (f d₂).1 * (f d₂).2 = d₂ := Nat.mul_div_cancel' (Nat.gcd_dvd_left d₂ m)
        rw [← h1, ← h2, h]
      have hsub : D_hit.image f ⊆ m.divisors.product (N - m).divisors := by
        intro p hp
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hp
        have hd_mem := Finset.mem_filter.mp hd
        refine Finset.mem_product.mpr ⟨?_, ?_⟩
        · exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right d m,
            (mul_pos (mul_pos hq1.pos hq2.pos) hq3.pos).ne'⟩
        · exact Nat.mem_divisors.mpr ⟨hd_mem.2.2, by omega⟩
      calc D_hit.card = (D_hit.image f).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (m.divisors.product (N - m).divisors).card := Finset.card_le_card hsub
        _ = m.divisors.card * (N - m).divisors.card := Finset.card_product _ _
        _ ≤ 8 * (N - m).divisors.card := Nat.mul_le_mul_right _ (divisors_card_mul_mul_le_eight hq1 hq2 hq3)
    calc ∑ d ∈ D_hit, ((Nat.gcd d m).totient : ℝ)⁻¹
        ≤ ∑ _d ∈ D_hit, (2 / (N : ℝ) ^ ((1 : ℝ) / 8)) := Finset.sum_le_sum hterm_le
      _ = (D_hit.card : ℝ) * (2 / (N : ℝ) ^ ((1 : ℝ) / 8)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (8 * ((N - m).divisors.card : ℝ)) * (2 / (N : ℝ) ^ ((1 : ℝ) / 8)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast hcard_hit
      _ = (16 / (N : ℝ) ^ ((1 : ℝ) / 8)) * ((N - m).divisors.card : ℝ) := by ring
  -- Sum `τ(N - m t)` over `t ∈ chenM N` using injectivity of `t ↦ N - m t`
  have hsum_tau :
      ∑ t ∈ chenM N, ((N - t.1 * t.2.1 * t.2.2).divisors.card : ℝ) ≤
        (N : ℝ) * (1 + Real.log (N : ℝ)) := by
    let g : ℕ × ℕ × ℕ → ℕ := fun t => N - t.1 * t.2.1 * t.2.2
    have hinj : Set.InjOn g (chenM N : Set (ℕ × ℕ × ℕ)) := by
      intro t₁ ht₁ t₂ ht₂ h
      have h1 : t₁.1 * t₁.2.1 * t₁.2.2 < N := (Finset.mem_filter.mp ht₁).2.2.2.2.2.2.2.2.2.2.2
      have h2 : t₂.1 * t₂.2.1 * t₂.2.2 < N := (Finset.mem_filter.mp ht₂).2.2.2.2.2.2.2.2.2.2.2
      have hmul : t₁.1 * t₁.2.1 * t₁.2.2 = t₂.1 * t₂.2.1 * t₂.2.2 := by dsimp only [g] at h; omega
      exact chenM_prod_injOn N ht₁ ht₂ hmul
    have hsub : (chenM N).image g ⊆ Finset.Icc 1 N := by
      intro k hk
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hk
      have hlt : t.1 * t.2.1 * t.2.2 < N := (Finset.mem_filter.mp ht).2.2.2.2.2.2.2.2.2.2.2
      exact Finset.mem_Icc.mpr ⟨by dsimp only [g]; omega, Nat.sub_le N _⟩
    calc ∑ t ∈ chenM N, ((g t).divisors.card : ℝ)
        = ∑ k ∈ (chenM N).image g, (k.divisors.card : ℝ) :=
          (Finset.sum_image (f := fun k : ℕ => (k.divisors.card : ℝ)) hinj).symm
      _ ≤ ∑ k ∈ Finset.Icc 1 N, (k.divisors.card : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _
      _ ≤ (N : ℝ) * (1 + Real.log (N : ℝ)) := sum_divisors_card_le (by omega)
  have hpow : (16 / (N : ℝ) ^ ((1 : ℝ) / 8)) * ((N : ℝ) * (1 + Real.log (N : ℝ))) =
      16 * (N : ℝ) ^ ((7 : ℝ) / 8) * (1 + Real.log (N : ℝ)) := by
    have h1 : (N : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 8) = (N : ℝ) ^ ((7 : ℝ) / 8) := by
      calc (N : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 8)
          = (N : ℝ) ^ (1 : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 8) := by rw [Real.rpow_one]
        _ = (N : ℝ) ^ ((1 : ℝ) - (1 : ℝ) / 8) := (Real.rpow_sub hN_pos _ _).symm
        _ = (N : ℝ) ^ ((7 : ℝ) / 8) := by norm_num
    rw [← h1]; ring
  calc ∑ t ∈ chenM N, ∑ d ∈ D,
          (if ¬ Nat.Coprime (t.1 * t.2.1 * t.2.2) d then
            ((Nat.gcd d (t.1 * t.2.1 * t.2.2)).totient : ℝ)⁻¹ *
              (if (d / Nat.gcd d (t.1 * t.2.1 * t.2.2)) ∣ (N - t.1 * t.2.1 * t.2.2) then (1 : ℝ) else 0)
          else 0)
      ≤ ∑ t ∈ chenM N, (16 / (N : ℝ) ^ ((1 : ℝ) / 8)) * ((N - t.1 * t.2.1 * t.2.2).divisors.card : ℝ) :=
        Finset.sum_le_sum hper_t
    _ = (16 / (N : ℝ) ^ ((1 : ℝ) / 8)) * ∑ t ∈ chenM N, ((N - t.1 * t.2.1 * t.2.2).divisors.card : ℝ) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (16 / (N : ℝ) ^ ((1 : ℝ) / 8)) * ((N : ℝ) * (1 + Real.log (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hsum_tau (by positivity)
    _ = 16 * (N : ℝ) ^ ((7 : ℝ) / 8) * (1 + Real.log (N : ℝ)) := hpow

open Classical in
/-- **Summed Reduction of the Chen Bilinear Discrepancy to Primitive Characters**:
for ALL `N ≥ 256` and `1 ≤ Q ≤ N`,
`∑_{d ∈ D} |#{(chenM N).filter (d ∣ N - m)} - |chenM N|/φ(d)| ≤ 16 N^{7/8} (1 + log N) + 12 log N * ∑_{k ∈ Ico 2 Q} φ(k+1)⁻¹ ∑*_{ψ mod k+1} ‖chenMCharSum ψ N‖`. -/
private lemma sum_chenM_discrepancy_le_prim_sum {N Q : ℕ} (hN : 256 ≤ N) (hQ : 1 ≤ Q)
    (hQN : Q ≤ N) :
    ∑ d ∈ (Finset.Icc 1 Q).filter (fun d => Squarefree d ∧ Nat.Coprime d N),
        |(((chenM N).filter (fun t => d ∣ (N - t.1 * t.2.1 * t.2.2))).card : ℝ) -
          ((chenM N).card : ℝ) / (d.totient : ℝ)| ≤
      16 * (N : ℝ) ^ ((7 : ℝ) / 8) * (1 + Real.log (N : ℝ)) +
      12 * Real.log (N : ℝ) *
        ∑ k ∈ Finset.Ico 2 Q,
          (1 / (Nat.totient (k + 1) : ℝ)) *
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
              ‖chenMCharSum ψ N‖ := by
  set D := (Finset.Icc 1 Q).filter (fun d => Squarefree d ∧ Nat.Coprime d N)
  have hper_d : ∀ d ∈ D,
      |(((chenM N).filter (fun t => d ∣ (N - t.1 * t.2.1 * t.2.2))).card : ℝ) -
          ((chenM N).card : ℝ) / (d.totient : ℝ)| ≤
        (∑ t ∈ chenM N,
          if ¬ Nat.Coprime (t.1 * t.2.1 * t.2.2) d then
            ((Nat.gcd d (t.1 * t.2.1 * t.2.2)).totient : ℝ)⁻¹ *
              (if (d / Nat.gcd d (t.1 * t.2.1 * t.2.2)) ∣ (N - t.1 * t.2.1 * t.2.2) then (1 : ℝ) else 0)
          else 0) +
        (d.totient : ℝ)⁻¹ *
          ∑ r ∈ (Finset.Icc 3 Q).filter (fun r => r ∣ d),
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive),
              ‖chenMCharSum ψ N‖ := by
    intro d hd
    have hd_mem := Finset.mem_filter.mp hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd_mem.1).1
    have hdQ : d ≤ Q := (Finset.mem_Icc.mp hd_mem.1).2
    have hsq : Squarefree d := hd_mem.2.1
    have hcopN : Nat.Coprime d N := hd_mem.2.2
    have : NeZero d := ⟨by omega⟩
    have hphi_pos : (0 : ℝ) < (d.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hd1)
    -- Rewrite LHS as sum over `t ∈ chenM N`
    have hLHS_eq :
        (((chenM N).filter (fun t => d ∣ (N - t.1 * t.2.1 * t.2.2))).card : ℝ) -
            ((chenM N).card : ℝ) / (d.totient : ℝ) =
          ∑ t ∈ chenM N,
            ((if d ∣ (N - t.1 * t.2.1 * t.2.2) then (1 : ℝ) else 0) - (d.totient : ℝ)⁻¹) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
        nsmul_eq_mul, nsmul_eq_mul, mul_one, div_eq_mul_inv]
    have hsum_id :
        ∑ t ∈ chenM N,
            ((if d ∣ (N - t.1 * t.2.1 * t.2.2) then (1 : ℝ) else 0) - (d.totient : ℝ)⁻¹) =
          (d.totient : ℝ)⁻¹ *
            ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ d),
              (starRingEnd ℂ (χ (N : ZMod d)) * chenMCharSum χ.primitiveCharacter N).re -
          ∑ t ∈ chenM N,
            (if ¬ Nat.Coprime (t.1 * t.2.1 * t.2.2) d then
              ((Nat.gcd d (t.1 * t.2.1 * t.2.2)).totient : ℝ)⁻¹ *
                (if (d / Nat.gcd d (t.1 * t.2.1 * t.2.2)) ∣ (N - t.1 * t.2.1 * t.2.2) then (1 : ℝ) else 0)
            else 0) := by
      have hcongr :
          ∑ t ∈ chenM N,
              ((if d ∣ (N - t.1 * t.2.1 * t.2.2) then (1 : ℝ) else 0) - (d.totient : ℝ)⁻¹) =
            ∑ t ∈ chenM N,
              ((d.totient : ℝ)⁻¹ *
                ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ d),
                  (starRingEnd ℂ (χ (N : ZMod d)) *
                    χ.primitiveCharacter ((t.1 * t.2.1 * t.2.2 : ℕ) : ZMod χ.conductor)).re -
                if ¬ Nat.Coprime (t.1 * t.2.1 * t.2.2) d then
                  ((Nat.gcd d (t.1 * t.2.1 * t.2.2)).totient : ℝ)⁻¹ *
                    (if (d / Nat.gcd d (t.1 * t.2.1 * t.2.2)) ∣ (N - t.1 * t.2.1 * t.2.2) then (1 : ℝ) else 0)
                else 0) := by
        refine Finset.sum_congr rfl fun t ht => ?_
        have hlt : t.1 * t.2.1 * t.2.2 < N := (Finset.mem_filter.mp ht).2.2.2.2.2.2.2.2.2.2.2
        exact indicator_dvd_sub_eq_prim_sum hsq hcopN hlt.le
      rw [hcongr, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_comm]
      congr 2
      refine Finset.sum_congr rfl fun χ _ => ?_
      unfold chenMCharSum
      rw [Finset.mul_sum, Complex.re_sum]
    rw [hLHS_eq, hsum_id]
    have hcorr_nn : 0 ≤ ∑ t ∈ chenM N,
        (if ¬ Nat.Coprime (t.1 * t.2.1 * t.2.2) d then
          ((Nat.gcd d (t.1 * t.2.1 * t.2.2)).totient : ℝ)⁻¹ *
            (if (d / Nat.gcd d (t.1 * t.2.1 * t.2.2)) ∣ (N - t.1 * t.2.1 * t.2.2) then (1 : ℝ) else 0)
        else 0) := Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
    -- Bound non-principal character sum by primitive characters of conductors `3 ≤ r ∣ d`
    have hprim_le :
        |∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ d),
            (starRingEnd ℂ (χ (N : ZMod d)) * chenMCharSum χ.primitiveCharacter N).re| ≤
          ∑ r ∈ (Finset.Icc 3 Q).filter (fun r => r ∣ d),
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive),
              ‖chenMCharSum ψ N‖ := by
      have h1 :
          |∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ d),
              (starRingEnd ℂ (χ (N : ZMod d)) * chenMCharSum χ.primitiveCharacter N).re| ≤
            ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ d),
              ‖chenMCharSum χ.primitiveCharacter N‖ := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun χ _ => ?_)
        calc |(starRingEnd ℂ (χ (N : ZMod d)) * chenMCharSum χ.primitiveCharacter N).re|
            ≤ ‖starRingEnd ℂ (χ (N : ZMod d)) * chenMCharSum χ.primitiveCharacter N‖ :=
              Complex.abs_re_le_norm _
          _ = ‖χ (N : ZMod d)‖ * ‖chenMCharSum χ.primitiveCharacter N‖ := by
              rw [norm_mul, Complex.norm_conj]
          _ ≤ 1 * ‖chenMCharSum χ.primitiveCharacter N‖ :=
              mul_le_mul_of_nonneg_right (χ.norm_le_one _) (norm_nonneg _)
          _ = ‖chenMCharSum χ.primitiveCharacter N‖ := one_mul _
      set target : Finset (Σ r : ℕ, DirichletCharacter ℂ r) :=
        ((Finset.Icc 3 Q).filter (fun r => r ∣ d)).sigma fun r =>
          Finset.univ.filter fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive
      let toPrim : DirichletCharacter ℂ d → (Σ r : ℕ, DirichletCharacter ℂ r) :=
        fun χ => ⟨χ.conductor, χ.primitiveCharacter⟩
      let induceFrom : (Σ r : ℕ, DirichletCharacter ℂ r) → DirichletCharacter ℂ d :=
        fun p => if h : p.1 ∣ d then DirichletCharacter.changeLevel h p.2 else 1
      have hind_eq : ∀ χ : DirichletCharacter ℂ d, induceFrom (toPrim χ) = χ := fun χ => by
        dsimp only [induceFrom, toPrim]
        rw [dif_pos χ.conductor_dvd_level, χ.changeLevel_primitiveCharacter]
      have hinj : Set.InjOn toPrim
          ((Finset.univ.erase (1 : DirichletCharacter ℂ d)) : Set (DirichletCharacter ℂ d)) := by
        intro χ₁ _ χ₂ _ h; rw [← hind_eq χ₁, ← hind_eq χ₂, h]
      have hmaps : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ d), toPrim χ ∈ target := by
        intro χ hχ
        have hχne : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
        have hr3 : 3 ≤ χ.conductor := Stage8BarbanDavenport.three_le_conductor_of_ne_one hχne
        have hrd : χ.conductor ∣ d := χ.conductor_dvd_level
        have hrQ : χ.conductor ≤ Q := (Nat.le_of_dvd hd1 hrd).trans hdQ
        simp only [target, toPrim, Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc,
          Finset.mem_univ, true_and]
        exact ⟨⟨⟨hr3, hrQ⟩, hrd⟩, χ.primitiveCharacter_isPrimitive⟩
      refine h1.trans ?_
      have hsig :
          ∑ p ∈ target, ‖chenMCharSum p.2 N‖ =
            ∑ r ∈ (Finset.Icc 3 Q).filter (fun r => r ∣ d),
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive),
                ‖chenMCharSum ψ N‖ := Finset.sum_sigma _ _ _
      rw [← hsig]
      calc ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ d), ‖chenMCharSum (toPrim χ).2 N‖
          = ∑ p ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ d)).image toPrim, ‖chenMCharSum p.2 N‖ :=
            (Finset.sum_image (f := fun p : Σ r : ℕ, DirichletCharacter ℂ r =>
              ‖chenMCharSum p.2 N‖) hinj).symm
        _ ≤ ∑ p ∈ target, ‖chenMCharSum p.2 N‖ :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hmaps)
              fun _ _ _ => norm_nonneg _
    have htri := abs_sub
      ((d.totient : ℝ)⁻¹ * ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ d),
        (starRingEnd ℂ (χ (N : ZMod d)) * chenMCharSum χ.primitiveCharacter N).re)
      (∑ t ∈ chenM N,
        if ¬ Nat.Coprime (t.1 * t.2.1 * t.2.2) d then
          ((Nat.gcd d (t.1 * t.2.1 * t.2.2)).totient : ℝ)⁻¹ *
            (if (d / Nat.gcd d (t.1 * t.2.1 * t.2.2)) ∣ (N - t.1 * t.2.1 * t.2.2) then (1 : ℝ) else 0)
        else 0)
    rw [abs_mul, abs_of_pos (inv_pos.mpr hphi_pos), abs_of_nonneg hcorr_nn] at htri
    have hmul := mul_le_mul_of_nonneg_left hprim_le (inv_nonneg.mpr hphi_pos.le)
    linarith
  have hsum_all := Finset.sum_le_sum hper_d
  rw [Finset.sum_add_distrib] at hsum_all
  have hcorr := sum_coprime_correction_le (Q := Q) hN
  -- Swap `(d, r)` sum and apply `sum_inv_totient_dvd_le`
  have hD_sub : D ⊆ Finset.Icc 1 Q := Finset.filter_subset _ _
  have hlog2Q : Real.log (2 * (Q : ℝ)) ≤ 2 * Real.log (N : ℝ) := by
    have hle : 2 * (Q : ℝ) ≤ (N : ℝ) ^ 2 := by
      have hQR : (Q : ℝ) ≤ (N : ℝ) := by exact_mod_cast hQN
      have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 2 ≤ N)
      nlinarith
    calc Real.log (2 * (Q : ℝ)) ≤ Real.log ((N : ℝ) ^ 2) := Real.log_le_log (by positivity) hle
      _ = 2 * Real.log (N : ℝ) := by rw [Real.log_pow]; push_cast; ring
  have hprim_swap :
      ∑ d ∈ D, (d.totient : ℝ)⁻¹ *
          ∑ r ∈ (Finset.Icc 3 Q).filter (fun r => r ∣ d),
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive),
              ‖chenMCharSum ψ N‖ ≤
        12 * Real.log (N : ℝ) *
          ∑ k ∈ Finset.Ico 2 Q,
            (1 / (Nat.totient (k + 1) : ℝ)) *
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                ‖chenMCharSum ψ N‖ := by
    have hmono :
        ∑ d ∈ D, (d.totient : ℝ)⁻¹ *
            ∑ r ∈ (Finset.Icc 3 Q).filter (fun r => r ∣ d),
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive),
                ‖chenMCharSum ψ N‖ ≤
          ∑ d ∈ Finset.Icc 1 Q, (d.totient : ℝ)⁻¹ *
            ∑ r ∈ (Finset.Icc 3 Q).filter (fun r => r ∣ d),
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive),
                ‖chenMCharSum ψ N‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hD_sub fun _ _ _ =>
        mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
          (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
    have hswap :
        ∑ d ∈ Finset.Icc 1 Q, (d.totient : ℝ)⁻¹ *
            ∑ r ∈ (Finset.Icc 3 Q).filter (fun r => r ∣ d),
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive),
                ‖chenMCharSum ψ N‖ =
          ∑ r ∈ Finset.Icc 3 Q,
            (∑ d ∈ (Finset.Icc 1 Q).filter (fun d => r ∣ d), (d.totient : ℝ)⁻¹) *
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive),
                ‖chenMCharSum ψ N‖ := by
      have h1 : ∀ d ∈ Finset.Icc 1 Q,
          (d.totient : ℝ)⁻¹ *
            ∑ r ∈ (Finset.Icc 3 Q).filter (fun r => r ∣ d),
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive),
                ‖chenMCharSum ψ N‖ =
          ∑ r ∈ Finset.Icc 3 Q,
            if r ∣ d then
              (d.totient : ℝ)⁻¹ *
                ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive),
                  ‖chenMCharSum ψ N‖
            else 0 := fun d _ => by rw [Finset.mul_sum, Finset.sum_filter]
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => by rw [← Finset.sum_filter, ← Finset.sum_mul]
    refine (hmono.trans_eq hswap).trans ?_
    have hle1 :
        ∑ r ∈ Finset.Icc 3 Q,
            (∑ d ∈ (Finset.Icc 1 Q).filter (fun d => r ∣ d), (d.totient : ℝ)⁻¹) *
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive),
                ‖chenMCharSum ψ N‖ ≤
          ∑ r ∈ Finset.Icc 3 Q,
            (12 * Real.log (N : ℝ) * (1 / (r.totient : ℝ))) *
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive),
                ‖chenMCharSum ψ N‖ := by
      refine Finset.sum_le_sum fun r hr => ?_
      have hr1 : 1 ≤ r := by have := (Finset.mem_Icc.mp hr).1; omega
      have hrQ : r ≤ Q := (Finset.mem_Icc.mp hr).2
      have hdiv := Stage8BarbanDavenport.sum_inv_totient_dvd_le hr1 hrQ
      have hlog_le : Real.log (2 * (Q : ℝ) / (r : ℝ)) ≤ 2 * Real.log (N : ℝ) :=
        (Real.log_le_log (by positivity) (div_le_self (by positivity) (by exact_mod_cast hr1))).trans hlog2Q
      have hcoef : ∑ d ∈ (Finset.Icc 1 Q).filter (fun d => r ∣ d), (d.totient : ℝ)⁻¹ ≤
          12 * Real.log (N : ℝ) * (1 / (r.totient : ℝ)) := by
        calc _ ≤ (6 / (r.totient : ℝ)) * Real.log (2 * (Q : ℝ) / (r : ℝ)) := hdiv
          _ ≤ (6 / (r.totient : ℝ)) * (2 * Real.log (N : ℝ)) :=
              mul_le_mul_of_nonneg_left hlog_le (by positivity)
          _ = 12 * Real.log (N : ℝ) * (1 / (r.totient : ℝ)) := by ring
      exact mul_le_mul_of_nonneg_right hcoef (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    refine hle1.trans_eq ?_
    rw [Finset.mul_sum]
    symm
    refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_Ico, Finset.mem_Icc] at hk ⊢; omega
    · intro k₁ _ k₂ _ h; omega
    · intro r hr; simp only [Finset.mem_Icc] at hr
      exact ⟨r - 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro k _; ring
  linarith

/-! ## Section 3: Small-Conductor Bound via `Stage10SiegelWalfiszFull.siegel_walfisz_pi_real` -/

/-- Prime character sum `P(x, ψ) = ∑_{p ≤ x, p prime} ψ(p)`. -/
def primeCharSum {r : ℕ} (ψ : DirichletCharacter ℂ r) (x : ℝ) : ℂ :=
  ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, ψ (p : ZMod r)

/-- Orthogonality of a non-principal Dirichlet character summed over reduced residues `a < r`. -/
private lemma sum_dirichletChar_coprime_eq_zero {r : ℕ} [NeZero r]
    {ψ : DirichletCharacter ℂ r} (hψ : ψ ≠ 1) :
    ∑ a ∈ (Finset.range r).filter (fun a => Nat.Coprime a r), ψ (a : ZMod r) = 0 := by
  have hbij :
      ∑ u : (ZMod r)ˣ, ψ (u : ZMod r) =
        ∑ a ∈ (Finset.range r).filter (fun a => Nat.Coprime a r), ψ (a : ZMod r) := by
    refine Finset.sum_bij (fun u _ => (u : ZMod r).val) ?_ ?_ ?_ ?_
    · intro u _
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
      have hu : IsUnit (((u : ZMod r).val : ℕ) : ZMod r) := by
        rw [ZMod.natCast_zmod_val]; exact u.isUnit
      exact (ZMod.isUnit_iff_coprime _ r).mp hu
    · intro u₁ _ u₂ _ h
      exact Units.ext (by rw [← ZMod.natCast_zmod_val (u₁ : ZMod r),
        ← ZMod.natCast_zmod_val (u₂ : ZMod r), h])
    · intro a ha
      have ha_lt : a < r := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
      have hcop : Nat.Coprime a r := (Finset.mem_filter.mp ha).2
      have hu : IsUnit (a : ZMod r) := Stage2DirichletAP.isUnit_zmod_of_coprime hcop
      refine ⟨hu.unit, Finset.mem_univ _, ?_⟩
      rw [hu.unit_spec, ZMod.val_natCast, Nat.mod_eq_of_lt ha_lt]
    · intro u _
      rw [ZMod.natCast_zmod_val]
  rw [← hbij]
  have hex : ∃ v : (ZMod r)ˣ, ψ (v : ZMod r) ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hψ
    ext x
    rw [MulChar.one_apply x.isUnit]
    exact hall x
  obtain ⟨v, hv⟩ := hex
  set S : ℂ := ∑ u : (ZMod r)ˣ, ψ (u : ZMod r)
  have hmul : ψ (v : ZMod r) * S = S := by
    dsimp only [S]
    rw [Finset.mul_sum]
    have hcongr : ∑ u : (ZMod r)ˣ, ψ (v : ZMod r) * ψ (u : ZMod r) =
        ∑ u : (ZMod r)ˣ, ψ (((v * u : (ZMod r)ˣ) : ZMod r)) :=
      Finset.sum_congr rfl fun u _ => by rw [Units.val_mul, map_mul]
    rw [hcongr]
    exact Fintype.sum_equiv (Equiv.mulLeft v) _ _ fun _ => rfl
  have hzero : (ψ (v : ZMod r) - 1) * S = 0 := by linear_combination hmul
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hv)

/-- **Unconditional Siegel–Walfisz Bound for Prime Character Sums `P(x, ψ)`**:
direct 20-line corollary of `Stage10SiegelWalfiszFull.siegel_walfisz_pi_real`. -/
theorem siegel_walfisz_primeCharSum :
    ∃ c : ℝ, 0 < c ∧
      ∀ A : ℝ, 0 < A →
        ∃ C : ℝ, 0 < C ∧
          ∀ x : ℝ, 4 ≤ x →
            ∀ (r : ℕ) [NeZero r], (r : ℝ) ≤ (Real.log x) ^ A →
              ∀ (ψ : DirichletCharacter ℂ r), ψ ≠ 1 →
                ‖primeCharSum ψ x‖ ≤
                  (r : ℝ) * C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c, hc, hpi_all⟩ := Stage10SiegelWalfiszFull.siegel_walfisz_pi_real
  refine ⟨c, hc, fun A hA => ?_⟩
  obtain ⟨C, hC, hpi⟩ := hpi_all A hA
  refine ⟨C, hC, fun x hx4 r _ hr ψ hψ => ?_⟩
  have hr_pos : 0 < r := NeZero.pos r
  set Rset := (Finset.range r).filter (fun a => Nat.Coprime a r)
  -- Express `primeCharSum ψ x` via `primeCountAP r a x`
  have hgroup :
      primeCharSum ψ x =
        ∑ a ∈ Rset, ψ (a : ZMod r) * (Stage2DirichletAP.primeCountAP r a x : ℂ) := by
    unfold primeCharSum
    have hfilt_cop :
        ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, ψ (p : ZMod r) =
          ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ Nat.Coprime p r),
            ψ (p : ZMod r) := by
      rw [Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hp : p.Prime
      · by_cases hcop : Nat.Coprime p r
        · simp [hp, hcop]
        · have hnu : ¬ IsUnit (p : ZMod r) :=
            fun hu => hcop ((ZMod.isUnit_iff_coprime p r).mp hu)
          simp [hp, hcop, MulChar.map_nonunit ψ hnu]
      · simp [hp]
    rw [hfilt_cop]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun p => p % r) (t := Rset)]
    · refine Finset.sum_congr rfl fun a ha => ?_
      have ha_lt : a < r := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
      have hcop_a : Nat.Coprime a r := (Finset.mem_filter.mp ha).2
      have hfib_eq :
          ((Finset.range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ Nat.Coprime p r)).filter
              (fun p => p % r = a) =
            (Finset.range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD r]) := by
        ext p
        simp only [Finset.mem_filter, Nat.ModEq, Nat.mod_eq_of_lt ha_lt]
        constructor
        · rintro ⟨⟨hp_rng, hp_pr, _⟩, hmod⟩; exact ⟨hp_rng, hp_pr, hmod⟩
        · rintro ⟨hp_rng, hp_pr, hmod⟩
          have hcop_p : Nat.Coprime p r := by
            rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec, hmod]
            exact hcop_a.gcd_eq_one
          exact ⟨⟨hp_rng, hp_pr, hcop_p⟩, hmod⟩
      rw [hfib_eq]
      have hconst : ∀ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD r]),
          ψ (p : ZMod r) = ψ (a : ZMod r) := by
        intro p hp
        have hmod : p ≡ a [MOD r] := (Finset.mem_filter.mp hp).2.2
        rw [(ZMod.natCast_eq_natCast_iff p a r).mpr hmod]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, mul_comm]
      rfl
    · intro p hp
      have hcop_p : Nat.Coprime p r := (Finset.mem_filter.mp hp).2.2
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt p hr_pos), ?_⟩
      rw [Nat.coprime_iff_gcd_eq_one, ← Nat.gcd_rec r p, Nat.gcd_comm]
      exact hcop_p.gcd_eq_one
  set liDiv : ℝ := (∫ t in (2 : ℝ)..x, 1 / Real.log t) / (r.totient : ℝ)
  have hsub_zero :
      primeCharSum ψ x =
        ∑ a ∈ Rset,
          ψ (a : ZMod r) * (((Stage2DirichletAP.primeCountAP r a x : ℝ) - liDiv : ℝ) : ℂ) := by
    rw [hgroup]
    have h0 : ∑ a ∈ Rset, ψ (a : ZMod r) * (liDiv : ℂ) = 0 := by
      rw [← Finset.sum_mul, sum_dirichletChar_coprime_eq_zero hψ, zero_mul]
    calc ∑ a ∈ Rset, ψ (a : ZMod r) * (Stage2DirichletAP.primeCountAP r a x : ℂ)
        = (∑ a ∈ Rset, ψ (a : ZMod r) * (Stage2DirichletAP.primeCountAP r a x : ℂ)) -
            ∑ a ∈ Rset, ψ (a : ZMod r) * (liDiv : ℂ) := by rw [h0, sub_zero]
      _ = ∑ a ∈ Rset,
            ψ (a : ZMod r) * (((Stage2DirichletAP.primeCountAP r a x : ℝ) - liDiv : ℝ) : ℂ) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun a _ => ?_
          push_cast; ring
  rw [hsub_zero]
  have hRcard : (Rset.card : ℝ) ≤ (r : ℝ) := by
    have hnat : Rset.card ≤ r := (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])
    exact_mod_cast hnat
  calc ‖∑ a ∈ Rset, ψ (a : ZMod r) *
          (((Stage2DirichletAP.primeCountAP r a x : ℝ) - liDiv : ℝ) : ℂ)‖
      ≤ ∑ a ∈ Rset, ‖ψ (a : ZMod r) *
          (((Stage2DirichletAP.primeCountAP r a x : ℝ) - liDiv : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ Rset, (C * x * Real.exp (-c * Real.sqrt (Real.log x))) := by
        refine Finset.sum_le_sum fun a ha => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hcop_a : Nat.Coprime a r := (Finset.mem_filter.mp ha).2
        calc ‖ψ (a : ZMod r)‖ * |(Stage2DirichletAP.primeCountAP r a x : ℝ) - liDiv|
            ≤ 1 * (C * x * Real.exp (-c * Real.sqrt (Real.log x))) :=
              mul_le_mul (ψ.norm_le_one _) (hpi x hx4 r hr a hcop_a) (abs_nonneg _) zero_le_one
          _ = C * x * Real.exp (-c * Real.sqrt (Real.log x)) := one_mul _
    _ = (Rset.card : ℝ) * (C * x * Real.exp (-c * Real.sqrt (Real.log x))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (r : ℝ) * C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
        have := mul_le_mul_of_nonneg_right hRcard (by positivity : 0 ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x)))
        linarith

/-- Decomposition of `chenMCharSum ψ N` into an outer sum over `(q₁, q₂) ∈ chenMPairs N` and
an inner prime character-sum difference over `q₃`, up to the `≤ 3` primes `q₃ ∣ N`. -/
private lemma norm_chenMCharSum_le_primeCharSum_diff {r : ℕ} (ψ : DirichletCharacter ℂ r)
    {N : ℕ} (hN : 64 ≤ N) :
    ‖chenMCharSum ψ N‖ ≤
      (N : ℝ) ^ ((2 : ℝ) / 3) * (2 * Real.log (N : ℝ) + 2) +
      ∑ p ∈ chenMPairs N,
        (‖primeCharSum ψ (((N - 1) / (p.1 * p.2) : ℕ) : ℝ)‖ +
         ‖primeCharSum ψ (((p.2 - 1 : ℕ) : ℝ))‖) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  -- Express `chenM N` as a sigma over `p ∈ chenMPairs N` and `q₃`
  have hgroup :
      chenMCharSum ψ N =
        ∑ p ∈ chenMPairs N,
          ψ ((p.1 * p.2 : ℕ) : ZMod r) *
            ∑ q₃ ∈ (Finset.Icc p.2 ((N - 1) / (p.1 * p.2))).filter
                (fun q₃ => q₃.Prime ∧ ¬ q₃ ∣ N),
              ψ (q₃ : ZMod r) := by
    unfold chenMCharSum
    let f : ℕ × ℕ × ℕ → ℕ × ℕ := fun t => (t.1, t.2.1)
    rw [← Finset.sum_fiberwise_of_maps_to (g := f) (t := chenMPairs N)]
    · refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun t _ => t.2.2) ?_ ?_ ?_ ?_
      · intro t ht
        have ht_mem := Finset.mem_filter.mp ht
        have hteq : (t.1, t.2.1) = p := ht_mem.2
        have htp := (Finset.mem_filter.mp ht_mem.1).2
        rcases htp with ⟨hq1, hq2, hq3, _, _, hq3N, _, _, _, hq23, hprod⟩
        have ht1 : t.1 = p.1 := congrArg Prod.fst hteq
        have ht2 : t.2.1 = p.2 := congrArg Prod.snd hteq
        rw [ht1] at hprod hq1
        rw [ht2] at hq23 hprod hq2
        have hp12_pos : 0 < p.1 * p.2 := mul_pos hq1.pos hq2.pos
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq23, ?_⟩, hq3, hq3N⟩
        exact (Nat.le_div_iff_mul_le hp12_pos).mpr (by rw [mul_comm]; omega)
      · intro t₁ ht₁ t₂ ht₂ h
        have h1 : (t₁.1, t₁.2.1) = p := (Finset.mem_filter.mp ht₁).2
        have h2 : (t₂.1, t₂.2.1) = p := (Finset.mem_filter.mp ht₂).2
        have hfst : t₁.1 = t₂.1 := (congrArg Prod.fst h1).trans (congrArg Prod.fst h2).symm
        have hsnd : t₁.2.1 = t₂.2.1 := (congrArg Prod.snd h1).trans (congrArg Prod.snd h2).symm
        exact Prod.ext hfst (Prod.ext hsnd h)
      · intro q₃ hq₃
        have hp_mem := Finset.mem_filter.mp hp
        rcases hp_mem.2 with ⟨hp1, hp2, hp1N, hp2N, hp1_ge, hp1_lt, hp2_ge, hp_prod⟩
        have hq3_mem := Finset.mem_filter.mp hq₃
        have hq3_lo : p.2 ≤ q₃ := (Finset.mem_Icc.mp hq3_mem.1).1
        have hq3_hi : q₃ ≤ (N - 1) / (p.1 * p.2) := (Finset.mem_Icc.mp hq3_mem.1).2
        have hq3_pr : q₃.Prime := hq3_mem.2.1
        have hq3_N : ¬ q₃ ∣ N := hq3_mem.2.2
        have hp12_pos : 0 < p.1 * p.2 := mul_pos hp1.pos hp2.pos
        have hprod_lt : p.1 * p.2 * q₃ < N := by
          have h1 := (Nat.le_div_iff_mul_le hp12_pos).mp hq3_hi
          rw [mul_comm] at h1
          omega
        have hq3_ltN : q₃ < N := by
          have h2 : 2 ≤ p.1 * p.2 := by have := hp1.two_le; have := hp2.two_le; nlinarith
          nlinarith
        refine ⟨(p.1, p.2, q₃), ?_, rfl⟩
        refine Finset.mem_filter.mpr ⟨?_, rfl⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp hp_mem.1).1,
          Finset.mem_product.mpr ⟨(Finset.mem_product.mp hp_mem.1).2, Finset.mem_range.mpr hq3_ltN⟩⟩,
          ⟨hp1, hp2, hq3_pr, hp1N, hp2N, hq3_N, hp1_ge, hp1_lt, hp2_ge, hq3_lo, hprod_lt⟩⟩
      · intro t ht
        have hteq : (t.1, t.2.1) = p := (Finset.mem_filter.mp ht).2
        have ht1 : t.1 = p.1 := congrArg Prod.fst hteq
        have ht2 : t.2.1 = p.2 := congrArg Prod.snd hteq
        rw [ht1, ht2, Nat.cast_mul, map_mul]
    · intro t ht
      have ht_mem := Finset.mem_filter.mp ht
      rcases ht_mem.2 with ⟨hq1, hq2, _, hq1N, hq2N, _, hq1_ge, hq1_lt, hq2_ge, hq23, hprod⟩
      have hprod2 : t.1 * t.2.1 * t.2.1 < N :=
        lt_of_le_of_lt (Nat.mul_le_mul_left (t.1 * t.2.1) hq23) hprod
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨(Finset.mem_product.mp ht_mem.1).1, (Finset.mem_product.mp (Finset.mem_product.mp ht_mem.1).2).1⟩,
        ⟨hq1, hq2, hq1N, hq2N, hq1_ge, hq1_lt, hq2_ge, hprod2⟩⟩
  rw [hgroup]
  -- Bound `(chenMPairs N).card ≤ N^{2/3}`
  have hcard_pairs : ((chenMPairs N).card : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 3) := by
    have hsub : (chenMPairs N).image (fun p => p.1 * p.2) ⊆ Finset.Icc 1 ⌊(N : ℝ) ^ ((2 : ℝ) / 3)⌋₊ := by
      intro m hm
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
      rcases (Finset.mem_filter.mp hp).2 with ⟨hp1, hp2, _, _, _, _, hp2_ge, hprod⟩
      refine Finset.mem_Icc.mpr ⟨mul_pos hp1.pos hp2.pos, Nat.le_floor ?_⟩
      have hprodR : ((p.1 * p.2 : ℕ) : ℝ) * (p.2 : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast hprod.le
      have hN13_pos : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hN_pos _
      have h1 : ((p.1 * p.2 : ℕ) : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (N : ℝ) :=
        (mul_le_mul_of_nonneg_left hp2_ge (Nat.cast_nonneg _)).trans hprodR
      have hdiv : ((p.1 * p.2 : ℕ) : ℝ) ≤ (N : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 3) :=
        (le_div_iff₀ hN13_pos).mpr h1
      have hpow : (N : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 3) = (N : ℝ) ^ ((2 : ℝ) / 3) := by
        calc (N : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 3)
            = (N : ℝ) ^ (1 : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 3) := by rw [Real.rpow_one]
          _ = (N : ℝ) ^ ((1 : ℝ) - (1 : ℝ) / 3) := (Real.rpow_sub hN_pos _ _).symm
          _ = (N : ℝ) ^ ((2 : ℝ) / 3) := by norm_num
      rwa [hpow] at hdiv
    have hnat : (chenMPairs N).card ≤ ⌊(N : ℝ) ^ ((2 : ℝ) / 3)⌋₊ := by
      calc (chenMPairs N).card
          = ((chenMPairs N).image (fun p => p.1 * p.2)).card :=
            (Finset.card_image_of_injOn (chenMPairs_prod_injOn N)).symm
        _ ≤ (Finset.Icc 1 ⌊(N : ℝ) ^ ((2 : ℝ) / 3)⌋₊).card := Finset.card_le_card hsub
        _ = ⌊(N : ℝ) ^ ((2 : ℝ) / 3)⌋₊ := by rw [Nat.card_Icc]; omega
    exact (by exact_mod_cast hnat : ((chenMPairs N).card : ℝ) ≤ (⌊(N : ℝ) ^ ((2 : ℝ) / 3)⌋₊ : ℝ)).trans
      (Nat.floor_le (by positivity))
  -- Bound `N.primeFactors.card ≤ 2 * log N + 2`
  have hpf_card : (N.primeFactors.card : ℝ) ≤ 2 * Real.log (N : ℝ) + 2 := by
    have h2pow : 2 ^ N.primeFactors.card ≤ N := by
      calc 2 ^ N.primeFactors.card
          = ∏ _p ∈ N.primeFactors, (2 : ℕ) := by rw [Finset.prod_const]
        _ ≤ ∏ p ∈ N.primeFactors, p :=
            Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
        _ ≤ N := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd N)
    have hR : (2 : ℝ) ^ N.primeFactors.card ≤ (N : ℝ) := by exact_mod_cast h2pow
    have hlog := Real.log_le_log (by positivity) hR
    rw [Real.log_pow] at hlog
    have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    nlinarith
  -- Per-pair bound: drop `¬ q₃ ∣ N` and rewrite as difference of two `primeCharSum`s
  have hper_p : ∀ p ∈ chenMPairs N,
      ‖ψ ((p.1 * p.2 : ℕ) : ZMod r) *
          ∑ q₃ ∈ (Finset.Icc p.2 ((N - 1) / (p.1 * p.2))).filter (fun q₃ => q₃.Prime ∧ ¬ q₃ ∣ N),
            ψ (q₃ : ZMod r)‖ ≤
        (2 * Real.log (N : ℝ) + 2) +
        (‖primeCharSum ψ (((N - 1) / (p.1 * p.2) : ℕ) : ℝ)‖ +
         ‖primeCharSum ψ (((p.2 - 1 : ℕ) : ℝ))‖) := by
    intro p hp
    rcases (Finset.mem_filter.mp hp).2 with ⟨hp1, hp2, _, _, _, _, _, hp_prod⟩
    have hp12_pos : 0 < p.1 * p.2 := mul_pos hp1.pos hp2.pos
    have hle_U : p.2 ≤ (N - 1) / (p.1 * p.2) :=
      (Nat.le_div_iff_mul_le hp12_pos).mpr (by rw [mul_comm]; omega)
    set U := (N - 1) / (p.1 * p.2)
    set L := p.2 - 1
    have hLU : L ≤ U := by omega
    -- Split `filter (q₃.Prime ∧ ¬ q₃ ∣ N)` as `filter q₃.Prime` minus `filter (q₃.Prime ∧ q₃ ∣ N)`
    have hdiff_N :
        ∑ q₃ ∈ (Finset.Icc p.2 U).filter (fun q₃ => q₃.Prime ∧ ¬ q₃ ∣ N), ψ (q₃ : ZMod r) =
          (∑ q₃ ∈ (Finset.Icc p.2 U).filter Nat.Prime, ψ (q₃ : ZMod r)) -
          (∑ q₃ ∈ (Finset.Icc p.2 U).filter (fun q₃ => q₃.Prime ∧ q₃ ∣ N), ψ (q₃ : ZMod r)) := by
      have hunion : (Finset.Icc p.2 U).filter Nat.Prime =
          (Finset.Icc p.2 U).filter (fun q₃ => q₃.Prime ∧ ¬ q₃ ∣ N) ∪
          (Finset.Icc p.2 U).filter (fun q₃ => q₃.Prime ∧ q₃ ∣ N) := by
        ext q₃; simp only [Finset.mem_filter, Finset.mem_union]; tauto
      have hdisj : Disjoint
          ((Finset.Icc p.2 U).filter (fun q₃ => q₃.Prime ∧ ¬ q₃ ∣ N))
          ((Finset.Icc p.2 U).filter (fun q₃ => q₃.Prime ∧ q₃ ∣ N)) := by
        rw [Finset.disjoint_left]; intro q₃ h1 h2
        exact (Finset.mem_filter.mp h1).2.2 (Finset.mem_filter.mp h2).2.2
      rw [hunion, Finset.sum_union hdisj]
      ring
    -- Express `∑_{q₃ ∈ Icc p.2 U, prime}` as `primeCharSum ψ U - primeCharSum ψ L`
    have hprime_diff :
        ∑ q₃ ∈ (Finset.Icc p.2 U).filter Nat.Prime, ψ (q₃ : ZMod r) =
          primeCharSum ψ (U : ℝ) - primeCharSum ψ (L : ℝ) := by
      unfold primeCharSum
      rw [Nat.floor_natCast, Nat.floor_natCast]
      have hunion : (Finset.range (U + 1)).filter Nat.Prime =
          (Finset.range (L + 1)).filter Nat.Prime ∪ (Finset.Icc p.2 U).filter Nat.Prime := by
        ext q₃
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_range, Finset.mem_Icc]
        have hp2_pos : 1 ≤ p.2 := hp2.one_lt.le
        constructor
        · rintro ⟨hqU, hpr⟩
          by_cases hqL : q₃ < L + 1
          · exact Or.inl ⟨hqL, hpr⟩
          · exact Or.inr ⟨⟨by omega, by omega⟩, hpr⟩
        · rintro (⟨hqL, hpr⟩ | ⟨⟨_, hqU⟩, hpr⟩)
          · exact ⟨by omega, hpr⟩
          · exact ⟨by omega, hpr⟩
      have hdisj : Disjoint ((Finset.range (L + 1)).filter Nat.Prime)
          ((Finset.Icc p.2 U).filter Nat.Prime) := by
        rw [Finset.disjoint_left]
        intro q₃ h1 h2
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at h1 h2
        have hp2_pos : 1 ≤ p.2 := hp2.one_lt.le
        omega
      rw [hunion, Finset.sum_union hdisj]
      ring
    have hbad_le :
        ‖∑ q₃ ∈ (Finset.Icc p.2 U).filter (fun q₃ => q₃.Prime ∧ q₃ ∣ N), ψ (q₃ : ZMod r)‖ ≤
          2 * Real.log (N : ℝ) + 2 := by
      have hsub_pf : (Finset.Icc p.2 U).filter (fun q₃ => q₃.Prime ∧ q₃ ∣ N) ⊆ N.primeFactors := by
        intro q₃ hq₃
        have hm := (Finset.mem_filter.mp hq₃).2
        exact Nat.mem_primeFactors.mpr ⟨hm.1, hm.2, by omega⟩
      calc ‖∑ q₃ ∈ (Finset.Icc p.2 U).filter (fun q₃ => q₃.Prime ∧ q₃ ∣ N), ψ (q₃ : ZMod r)‖
          ≤ ∑ q₃ ∈ (Finset.Icc p.2 U).filter (fun q₃ => q₃.Prime ∧ q₃ ∣ N), ‖ψ (q₃ : ZMod r)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _q₃ ∈ (Finset.Icc p.2 U).filter (fun q₃ => q₃.Prime ∧ q₃ ∣ N), (1 : ℝ) :=
            Finset.sum_le_sum fun q₃ _ => ψ.norm_le_one _
        _ = (((Finset.Icc p.2 U).filter (fun q₃ => q₃.Prime ∧ q₃ ∣ N)).card : ℝ) := by simp
        _ ≤ (N.primeFactors.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub_pf
        _ ≤ 2 * Real.log (N : ℝ) + 2 := hpf_card
    calc ‖ψ ((p.1 * p.2 : ℕ) : ZMod r) *
            ∑ q₃ ∈ (Finset.Icc p.2 U).filter (fun q₃ => q₃.Prime ∧ ¬ q₃ ∣ N), ψ (q₃ : ZMod r)‖
        = ‖ψ ((p.1 * p.2 : ℕ) : ZMod r)‖ *
            ‖∑ q₃ ∈ (Finset.Icc p.2 U).filter (fun q₃ => q₃.Prime ∧ ¬ q₃ ∣ N), ψ (q₃ : ZMod r)‖ :=
          norm_mul _ _
      _ ≤ 1 * ‖∑ q₃ ∈ (Finset.Icc p.2 U).filter (fun q₃ => q₃.Prime ∧ ¬ q₃ ∣ N), ψ (q₃ : ZMod r)‖ :=
          mul_le_mul_of_nonneg_right (ψ.norm_le_one _) (norm_nonneg _)
      _ = ‖(primeCharSum ψ (U : ℝ) - primeCharSum ψ (L : ℝ)) -
            ∑ q₃ ∈ (Finset.Icc p.2 U).filter (fun q₃ => q₃.Prime ∧ q₃ ∣ N), ψ (q₃ : ZMod r)‖ := by
          rw [one_mul, hdiff_N, hprime_diff]
      _ ≤ ‖primeCharSum ψ (U : ℝ) - primeCharSum ψ (L : ℝ)‖ +
            ‖∑ q₃ ∈ (Finset.Icc p.2 U).filter (fun q₃ => q₃.Prime ∧ q₃ ∣ N), ψ (q₃ : ZMod r)‖ :=
          norm_sub_le _ _
      _ ≤ (‖primeCharSum ψ (U : ℝ)‖ + ‖primeCharSum ψ (L : ℝ)‖) + (2 * Real.log (N : ℝ) + 2) := by
          linarith [norm_sub_le (primeCharSum ψ (U : ℝ)) (primeCharSum ψ (L : ℝ))]
      _ = (2 * Real.log (N : ℝ) + 2) + (‖primeCharSum ψ (U : ℝ)‖ + ‖primeCharSum ψ (L : ℝ)‖) := by
          ring
  calc ‖∑ p ∈ chenMPairs N,
          ψ ((p.1 * p.2 : ℕ) : ZMod r) *
            ∑ q₃ ∈ (Finset.Icc p.2 ((N - 1) / (p.1 * p.2))).filter (fun q₃ => q₃.Prime ∧ ¬ q₃ ∣ N),
              ψ (q₃ : ZMod r)‖
      ≤ ∑ p ∈ chenMPairs N,
          ‖ψ ((p.1 * p.2 : ℕ) : ZMod r) *
            ∑ q₃ ∈ (Finset.Icc p.2 ((N - 1) / (p.1 * p.2))).filter (fun q₃ => q₃.Prime ∧ ¬ q₃ ∣ N),
              ψ (q₃ : ZMod r)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ chenMPairs N,
          ((2 * Real.log (N : ℝ) + 2) +
            (‖primeCharSum ψ (((N - 1) / (p.1 * p.2) : ℕ) : ℝ)‖ +
             ‖primeCharSum ψ (((p.2 - 1 : ℕ) : ℝ))‖)) := Finset.sum_le_sum hper_p
    _ = ((chenMPairs N).card : ℝ) * (2 * Real.log (N : ℝ) + 2) +
          ∑ p ∈ chenMPairs N,
            (‖primeCharSum ψ (((N - 1) / (p.1 * p.2) : ℕ) : ℝ)‖ +
             ‖primeCharSum ψ (((p.2 - 1 : ℕ) : ℝ))‖) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ ((2 : ℝ) / 3) * (2 * Real.log (N : ℝ) + 2) +
          ∑ p ∈ chenMPairs N,
            (‖primeCharSum ψ (((N - 1) / (p.1 * p.2) : ℕ) : ℝ)‖ +
             ‖primeCharSum ψ (((p.2 - 1 : ℕ) : ℝ))‖) := by
        gcongr

/-- **Pointwise Small-Conductor Bound on `‖chenMCharSum ψ N‖`**:
for `N ≥ 4096` with `(4 : ℝ) ^ B₁ ≤ Real.log (N : ℝ) / 4`, every `r ≤ (log N)^{B₁}`, and every
non-principal `ψ mod r`,
`‖chenMCharSum ψ N‖ ≤ N^{2/3} (2 log N + 2) + 2 r C_sw N (1 + log N) exp(-(c_sw / 2) √(log N))`. -/
private lemma norm_chenMCharSum_of_siegel_walfisz
    {c_sw C_sw B₁ : ℝ} (hc_sw : 0 < c_sw) (hC_sw : 0 < C_sw) (hB₁ : 0 < B₁)
    (hsw : ∀ x : ℝ, 4 ≤ x → ∀ (r : ℕ) [NeZero r], (r : ℝ) ≤ (Real.log x) ^ (B₁ + 1) →
      ∀ (ψ : DirichletCharacter ℂ r), ψ ≠ 1 →
        ‖primeCharSum ψ x‖ ≤ (r : ℝ) * C_sw * x * Real.exp (-c_sw * Real.sqrt (Real.log x)))
    {N : ℕ} (hN : 4096 ≤ N) (hlog_big : (4 : ℝ) ^ B₁ ≤ Real.log (N : ℝ) / 4)
    {r : ℕ} [NeZero r] (hr : (r : ℝ) ≤ (Real.log (N : ℝ)) ^ B₁)
    {ψ : DirichletCharacter ℂ r} (hψ : ψ ≠ 1) :
    ‖chenMCharSum ψ N‖ ≤
      (N : ℝ) ^ ((2 : ℝ) / 3) * (2 * Real.log (N : ℝ) + 2) +
      2 * (r : ℝ) * C_sw * (N : ℝ) * (1 + Real.log (N : ℝ)) *
        Real.exp (-(c_sw / 2) * Real.sqrt (Real.log (N : ℝ))) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hLN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hN12_ge2 : (2 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 12) := by
    have h4096 : (2 : ℝ) ^ (12 : ℝ) ≤ (N : ℝ) := by
      calc (2 : ℝ) ^ (12 : ℝ) = (4096 : ℝ) := by norm_num
        _ ≤ (N : ℝ) := by exact_mod_cast hN
    calc (2 : ℝ) = ((2 : ℝ) ^ (12 : ℝ)) ^ ((1 : ℝ) / 12) := by
          rw [← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 12) := Real.rpow_le_rpow (by positivity) h4096 (by norm_num)
  have hN14_ge8 : (8 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := by
    have h8 : (8 : ℝ) ^ (4 : ℝ) ≤ (N : ℝ) := by
      calc (8 : ℝ) ^ (4 : ℝ) = (4096 : ℝ) := by norm_num
        _ ≤ (N : ℝ) := by exact_mod_cast hN
    calc (8 : ℝ) = ((8 : ℝ) ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) := by
          rw [← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow (by positivity) h8 (by norm_num)
  have hN13_ge_2N14 : 2 * (N : ℝ) ^ ((1 : ℝ) / 4) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := by
    calc 2 * (N : ℝ) ^ ((1 : ℝ) / 4)
        ≤ (N : ℝ) ^ ((1 : ℝ) / 12) * (N : ℝ) ^ ((1 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_right hN12_ge2 (by positivity)
      _ = (N : ℝ) ^ ((1 : ℝ) / 3) := by rw [← Real.rpow_add hN_pos]; norm_num
  have hSW_at : ∀ x : ℝ, (N : ℝ) ^ ((1 : ℝ) / 4) ≤ x →
      ‖primeCharSum ψ x‖ ≤
        (r : ℝ) * C_sw * x * Real.exp (-(c_sw / 2) * Real.sqrt (Real.log (N : ℝ))) := by
    intro x hx
    have hx4 : 4 ≤ x := by linarith
    have hlog_x_ge : Real.log (N : ℝ) / 4 ≤ Real.log x := by
      have h1 := Real.log_le_log (Real.rpow_pos_of_pos hN_pos _) hx
      rw [Real.log_rpow hN_pos] at h1
      linarith
    have hlog_x_pos : 0 < Real.log x := lt_of_lt_of_le (by positivity) hlog_x_ge
    have hr_x : (r : ℝ) ≤ (Real.log x) ^ (B₁ + 1) := by
      calc (r : ℝ) ≤ (Real.log (N : ℝ)) ^ B₁ := hr
        _ = (4 * (Real.log (N : ℝ) / 4)) ^ B₁ := by congr 1; ring
        _ = (4 : ℝ) ^ B₁ * (Real.log (N : ℝ) / 4) ^ B₁ := Real.mul_rpow (by norm_num) (by positivity)
        _ ≤ Real.log x * (Real.log x) ^ B₁ :=
            mul_le_mul (hlog_big.trans hlog_x_ge)
              (Real.rpow_le_rpow (by positivity) hlog_x_ge hB₁.le)
              (Real.rpow_nonneg (by positivity) B₁) hlog_x_pos.le
        _ = (Real.log x) ^ (B₁ + 1) := by rw [Real.rpow_add hlog_x_pos, Real.rpow_one, mul_comm]
    have hsqrt_ge : Real.sqrt (Real.log (N : ℝ)) / 2 ≤ Real.sqrt (Real.log x) := by
      refine Real.le_sqrt_of_sq_le ?_
      rw [div_pow, Real.sq_sqrt hLN_pos.le]; norm_num; linarith
    have hexp_le : Real.exp (-c_sw * Real.sqrt (Real.log x)) ≤
        Real.exp (-(c_sw / 2) * Real.sqrt (Real.log (N : ℝ))) :=
      Real.exp_le_exp.mpr (by nlinarith)
    exact (hsw x hx4 r hr_x ψ hψ).trans (by gcongr)
  -- Apply `hSW_at` to each pair `p ∈ chenMPairs N`
  have hsum_pairs :
      ∑ p ∈ chenMPairs N,
          (‖primeCharSum ψ (((N - 1) / (p.1 * p.2) : ℕ) : ℝ)‖ +
           ‖primeCharSum ψ (((p.2 - 1 : ℕ) : ℝ))‖) ≤
        2 * (r : ℝ) * C_sw * (N : ℝ) * (1 + Real.log (N : ℝ)) *
          Real.exp (-(c_sw / 2) * Real.sqrt (Real.log (N : ℝ))) := by
    have hper : ∀ p ∈ chenMPairs N,
        ‖primeCharSum ψ (((N - 1) / (p.1 * p.2) : ℕ) : ℝ)‖ +
            ‖primeCharSum ψ (((p.2 - 1 : ℕ) : ℝ))‖ ≤
          (2 * (r : ℝ) * C_sw * (N : ℝ) * Real.exp (-(c_sw / 2) * Real.sqrt (Real.log (N : ℝ)))) *
            ((1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ)) := by
      intro p hp
      rcases (Finset.mem_filter.mp hp).2 with ⟨hp1, hp2, _, _, _, _, hp2_ge, hp_prod⟩
      have hp12_pos : 0 < p.1 * p.2 := mul_pos hp1.pos hp2.pos
      have hU_ge_p2 : p.2 ≤ (N - 1) / (p.1 * p.2) :=
        (Nat.le_div_iff_mul_le hp12_pos).mpr (by rw [mul_comm]; omega)
      have hL_ge : (N : ℝ) ^ ((1 : ℝ) / 4) ≤ ((p.2 - 1 : ℕ) : ℝ) := by
        have hp2_1 : 1 ≤ p.2 := hp2.one_lt.le
        rw [Nat.cast_sub hp2_1, Nat.cast_one]
        linarith
      have hU_ge : (N : ℝ) ^ ((1 : ℝ) / 4) ≤ (((N - 1) / (p.1 * p.2) : ℕ) : ℝ) :=
        hL_ge.trans (by exact_mod_cast (by omega : p.2 - 1 ≤ (N - 1) / (p.1 * p.2)))
      have hU_le : (((N - 1) / (p.1 * p.2) : ℕ) : ℝ) ≤ (N : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) := by
        calc (((N - 1) / (p.1 * p.2) : ℕ) : ℝ)
            ≤ ((N - 1 : ℕ) : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) := Nat.cast_div_le
          _ ≤ (N : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) := by
              refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
              exact_mod_cast Nat.sub_le N 1
      have hL_le : ((p.2 - 1 : ℕ) : ℝ) ≤ (N : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) := by
        have hLU : ((p.2 - 1 : ℕ) : ℝ) ≤ (((N - 1) / (p.1 * p.2) : ℕ) : ℝ) := by
          exact_mod_cast (by omega : p.2 - 1 ≤ (N - 1) / (p.1 * p.2))
        exact hLU.trans hU_le
      have h1 : ‖primeCharSum ψ (((N - 1) / (p.1 * p.2) : ℕ) : ℝ)‖ ≤
          (r : ℝ) * C_sw * ((N : ℝ) / ((p.1 * p.2 : ℕ) : ℝ)) *
            Real.exp (-(c_sw / 2) * Real.sqrt (Real.log (N : ℝ))) :=
        (hSW_at _ hU_ge).trans (by gcongr)
      have h2 : ‖primeCharSum ψ (((p.2 - 1 : ℕ) : ℝ))‖ ≤
          (r : ℝ) * C_sw * ((N : ℝ) / ((p.1 * p.2 : ℕ) : ℝ)) *
            Real.exp (-(c_sw / 2) * Real.sqrt (Real.log (N : ℝ))) :=
        (hSW_at _ hL_ge).trans (by gcongr)
      have hEq : (2 * (r : ℝ) * C_sw * (N : ℝ) * Real.exp (-(c_sw / 2) * Real.sqrt (Real.log (N : ℝ)))) *
          ((1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ)) =
          2 * ((r : ℝ) * C_sw * ((N : ℝ) / ((p.1 * p.2 : ℕ) : ℝ)) *
            Real.exp (-(c_sw / 2) * Real.sqrt (Real.log (N : ℝ)))) := by ring
      linarith
    have hharm : ∑ p ∈ chenMPairs N, (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) ≤ 1 + Real.log (N : ℝ) := by
      have hsub : (chenMPairs N).image (fun p : ℕ × ℕ => p.1 * p.2) ⊆ Finset.Icc 1 N := by
        intro m hm
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
        rcases (Finset.mem_filter.mp hp).2 with ⟨hp1, hp2, _, _, _, _, _, hp_prod⟩
        refine Finset.mem_Icc.mpr ⟨mul_pos hp1.pos hp2.pos, ?_⟩
        have h1 : p.1 * p.2 ≤ p.1 * p.2 * p.2 := Nat.le_mul_of_pos_right _ hp2.pos
        omega
      calc ∑ p ∈ chenMPairs N, (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ)
          = ∑ m ∈ (chenMPairs N).image (fun p : ℕ × ℕ => p.1 * p.2), (1 : ℝ) / (m : ℝ) :=
            (Finset.sum_image (f := fun m : ℕ => (1 : ℝ) / (m : ℝ)) (chenMPairs_prod_injOn N)).symm
        _ ≤ ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / (m : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
        _ ≤ 1 + Real.log (N : ℝ) := Stage10ZeroDensity.sum_inv_le_one_add_log (by omega)
    calc ∑ p ∈ chenMPairs N,
            (‖primeCharSum ψ (((N - 1) / (p.1 * p.2) : ℕ) : ℝ)‖ +
             ‖primeCharSum ψ (((p.2 - 1 : ℕ) : ℝ))‖)
        ≤ ∑ p ∈ chenMPairs N,
            (2 * (r : ℝ) * C_sw * (N : ℝ) * Real.exp (-(c_sw / 2) * Real.sqrt (Real.log (N : ℝ)))) *
              ((1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ)) := Finset.sum_le_sum hper
      _ = (2 * (r : ℝ) * C_sw * (N : ℝ) * Real.exp (-(c_sw / 2) * Real.sqrt (Real.log (N : ℝ)))) *
            ∑ p ∈ chenMPairs N, (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ (2 * (r : ℝ) * C_sw * (N : ℝ) * Real.exp (-(c_sw / 2) * Real.sqrt (Real.log (N : ℝ)))) *
            (1 + Real.log (N : ℝ)) := mul_le_mul_of_nonneg_left hharm (by positivity)
      _ = 2 * (r : ℝ) * C_sw * (N : ℝ) * (1 + Real.log (N : ℝ)) *
            Real.exp (-(c_sw / 2) * Real.sqrt (Real.log (N : ℝ))) := by ring
  exact (norm_chenMCharSum_le_primeCharSum_diff ψ (by omega)).trans (by linarith)

/-! ## Section 4: Large-Conductor Geometric Box & Boundary Bilinear Large Sieve -/

/-- Geometric grid point `g(Δ, i) = ⌊(1 + Δ)^i⌋₊`. -/
private def geoGrid (Δ : ℝ) (i : ℕ) : ℕ :=
  ⌊(1 + Δ) ^ i⌋₊

private lemma geoGrid_zero (Δ : ℝ) : geoGrid Δ 0 = 1 := by
  simp [geoGrid]

private lemma geoGrid_mono {Δ : ℝ} (hΔ : 0 ≤ Δ) : Monotone (geoGrid Δ) := by
  intro i j hij
  exact Nat.floor_mono (pow_le_pow_right₀ (by linarith) hij)

private lemma geoGrid_pos {Δ : ℝ} (hΔ : 0 ≤ Δ) (i : ℕ) : 1 ≤ geoGrid Δ i :=
  geoGrid_zero Δ ▸ geoGrid_mono hΔ (Nat.zero_le i)

/-- Exact disjoint partition of `Ioc (g 0) (g K)` into `⋃_{i < K} Ioc (g i) (g (i + 1))`. -/
private lemma mem_Ioc_geoGrid_exists_unique {Δ : ℝ} (hΔ : 0 ≤ Δ) (K n : ℕ)
    (hn : n ∈ Finset.Ioc (geoGrid Δ 0) (geoGrid Δ K)) :
    ∃! i : ℕ, i < K ∧ n ∈ Finset.Ioc (geoGrid Δ i) (geoGrid Δ (i + 1)) := by
  induction K with
  | zero =>
    simp only [Finset.mem_Ioc] at hn
    omega
  | succ k ih =>
    simp only [Finset.mem_Ioc] at hn
    by_cases hnk : n ≤ geoGrid Δ k
    · obtain ⟨i, ⟨hik, hni⟩, huniq⟩ := ih (Finset.mem_Ioc.mpr ⟨hn.1, hnk⟩)
      refine ⟨i, ⟨Nat.lt_succ_of_lt hik, hni⟩, ?_⟩
      rintro j ⟨hjk, hnj⟩
      have hjk' : j < k := by
        by_contra hge
        have hjk_eq : j = k := by omega
        subst hjk_eq
        simp only [Finset.mem_Ioc] at hnj
        omega
      exact huniq j ⟨hjk', hnj⟩
    · push Not at hnk
      refine ⟨k, ⟨Nat.lt_succ_self k, Finset.mem_Ioc.mpr ⟨hnk, hn.2⟩⟩, ?_⟩
      rintro j ⟨hjk, hnj⟩
      by_contra hne
      have hj_le : j + 1 ≤ k := by omega
      have hle : geoGrid Δ (j + 1) ≤ geoGrid Δ k := geoGrid_mono hΔ hj_le
      simp only [Finset.mem_Ioc] at hnj
      omega

/-- Number of geometric steps `K_idx = ⌊2 log N / Δ⌋₊ + 1` covers up to `N`. -/
private lemma geoGrid_cover_ge {N : ℕ} {Δ : ℝ} (hN : 2 ≤ N) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    N ≤ geoGrid Δ (⌊2 * Real.log (N : ℝ) / Δ⌋₊ + 1) := by
  set K := ⌊2 * Real.log (N : ℝ) / Δ⌋₊ + 1
  have hK_gt : 2 * Real.log (N : ℝ) / Δ < (K : ℝ) := by
    dsimp only [K]; push_cast; exact Nat.lt_floor_add_one _
  have hlog_ge : Δ / 2 ≤ Real.log (1 + Δ) := by
    have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + Δ by linarith)
    have h2 : Δ / 2 ≤ 1 - (1 + Δ)⁻¹ := by
      have hEq : 1 - (1 + Δ)⁻¹ = Δ / (1 + Δ) := by field_simp [(by linarith : 1 + Δ ≠ 0)]; ring
      rw [hEq]
      exact div_le_div_of_nonneg_left hΔ0.le (by linarith) (by linarith)
    linarith
  have hprod_ge : Real.log (N : ℝ) ≤ (K : ℝ) * Real.log (1 + Δ) := by
    have hLN_nn : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
    calc Real.log (N : ℝ) = (2 * Real.log (N : ℝ) / Δ) * (Δ / 2) := by field_simp [hΔ0.ne']
      _ ≤ (K : ℝ) * Real.log (1 + Δ) := mul_le_mul hK_gt.le hlog_ge (by positivity) (by positivity)
  have hpow_ge : (N : ℝ) ≤ (1 + Δ) ^ K := by
    have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    calc (N : ℝ) = Real.exp (Real.log (N : ℝ)) := (Real.exp_log hN_pos).symm
      _ ≤ Real.exp ((K : ℝ) * Real.log (1 + Δ)) := Real.exp_le_exp.mpr hprod_ge
      _ = Real.exp (Real.log ((1 + Δ) ^ K)) := by rw [Real.log_pow]
      _ = (1 + Δ) ^ K := Real.exp_log (by positivity)
  exact Nat.le_floor hpow_ge

/-- Rectangular box subset of `chenM N` for geometric indices `(a, b)`:
`q₂ ∈ Ioc (g a) (g (a + 1))`, `q₁ * q₂ ∈ Ioc (g b) (g (b + 1))`, and
`q₃ ∈ Ioc (g (a + 1)) ((N - 1) / g (b + 1))`. -/
private def chenMRect (N : ℕ) (Δ : ℝ) (a b : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (chenM N).filter fun t =>
    t.2.1 ∈ Finset.Ioc (geoGrid Δ a) (geoGrid Δ (a + 1)) ∧
    t.1 * t.2.1 ∈ Finset.Ioc (geoGrid Δ b) (geoGrid Δ (b + 1)) ∧
    t.2.2 ∈ Finset.Ioc (geoGrid Δ (a + 1)) ((N - 1) / geoGrid Δ (b + 1))

/-- Boundary remainder `chenMBdy N Δ K`: elements of `chenM N` not covered by any rectangle
`chenMRect N Δ a b` with `a, b < K`. -/
private def chenMBdy (N : ℕ) (Δ : ℝ) (K : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (chenM N).filter fun t =>
    ∀ a ∈ Finset.range K, ∀ b ∈ Finset.range K, t ∉ chenMRect N Δ a b

/-- Exact disjoint decomposition of `chenMCharSum ψ N` into geometric rectangles plus boundary. -/
private lemma chenMCharSum_eq_rect_add_bdy {r : ℕ} (ψ : DirichletCharacter ℂ r)
    {N : ℕ} {Δ : ℝ} (hN : 2 ≤ N) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    let K := ⌊2 * Real.log (N : ℝ) / Δ⌋₊ + 1
    chenMCharSum ψ N =
      (∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K,
        (∑ m ∈ Finset.Ioc (geoGrid Δ b) (geoGrid Δ (b + 1)),
          (if ∃ p ∈ chenMPairs N, p.2 ∈ Finset.Ioc (geoGrid Δ a) (geoGrid Δ (a + 1)) ∧ p.1 * p.2 = m
           then (1 : ℂ) else 0) * ψ (m : ZMod r)) *
        (∑ n ∈ Finset.Ioc (geoGrid Δ (a + 1)) ((N - 1) / geoGrid Δ (b + 1)),
          (if n.Prime ∧ ¬ n ∣ N then (1 : ℂ) else 0) * ψ (n : ZMod r))) +
      ∑ t ∈ chenMBdy N Δ K, ψ ((t.1 * t.2.1 * t.2.2 : ℕ) : ZMod r) := by
  intro K
  have hcover : N ≤ geoGrid Δ K := geoGrid_cover_ge hN hΔ0 hΔ1
  set R_all := (Finset.range K ×ˢ Finset.range K).biUnion (fun ab => chenMRect N Δ ab.1 ab.2)
  have hR_sub : R_all ⊆ chenM N := by
    intro t ht
    obtain ⟨ab, _, htab⟩ := Finset.mem_biUnion.mp ht
    exact (Finset.mem_filter.mp htab).1
  have hBdy_eq : chenMBdy N Δ K = chenM N \ R_all := by
    ext t
    simp only [chenMBdy, R_all, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_biUnion,
      Finset.mem_product, not_exists, not_and]
    constructor
    · rintro ⟨ht, hall⟩
      exact ⟨ht, fun ⟨a, b⟩ hab => hall a hab.1 b hab.2⟩
    · rintro ⟨ht, hall⟩
      exact ⟨ht, fun a ha b hb => hall (a, b) ⟨ha, hb⟩⟩
  have hsplit : chenMCharSum ψ N =
      (∑ t ∈ R_all, ψ ((t.1 * t.2.1 * t.2.2 : ℕ) : ZMod r)) +
      (∑ t ∈ chenMBdy N Δ K, ψ ((t.1 * t.2.1 * t.2.2 : ℕ) : ZMod r)) := by
    unfold chenMCharSum
    rw [hBdy_eq, Finset.sum_sdiff_eq_sub hR_sub]
    ring
  rw [hsplit]
  congr 1
  -- Pairwise disjointness of `chenMRect N Δ a b`
  have hdisj : Set.PairwiseDisjoint
      (((Finset.range K ×ˢ Finset.range K : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)))
      (fun ab => chenMRect N Δ ab.1 ab.2) := by
    rintro ⟨a₁, b₁⟩ h1 ⟨a₂, b₂⟩ h2 hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro t ht₁ ht₂
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at h1 h2
    simp only [chenMRect, Finset.mem_filter] at ht₁ ht₂
    have hq2_in : t.2.1 ∈ Finset.Ioc (geoGrid Δ 0) (geoGrid Δ K) := by
      have hmem := (Finset.mem_filter.mp ht₁.1).2
      have hq2_gt1 : 1 < t.2.1 := hmem.2.1.one_lt
      have hq2_ltN : t.2.1 < N := by
        have h1' : t.1 * t.2.1 * t.2.2 < N := hmem.2.2.2.2.2.2.2.2.2.2
        have hle1 : t.2.1 ≤ t.1 * t.2.1 := Nat.le_mul_of_pos_left t.2.1 hmem.1.pos
        have hle2 : t.1 * t.2.1 ≤ t.1 * t.2.1 * t.2.2 := Nat.le_mul_of_pos_right _ hmem.2.2.1.pos
        omega
      exact Finset.mem_Ioc.mpr ⟨by rw [geoGrid_zero]; exact hq2_gt1, hq2_ltN.le.trans hcover⟩
    have hm_in : t.1 * t.2.1 ∈ Finset.Ioc (geoGrid Δ 0) (geoGrid Δ K) := by
      have hmem := (Finset.mem_filter.mp ht₁.1).2
      have hm_gt1 : 1 < t.1 * t.2.1 := by
        have := hmem.1.two_le; have := hmem.2.1.two_le; nlinarith
      have hm_ltN : t.1 * t.2.1 < N := by
        have h1' : t.1 * t.2.1 * t.2.2 < N := hmem.2.2.2.2.2.2.2.2.2.2
        have hle2 : t.1 * t.2.1 ≤ t.1 * t.2.1 * t.2.2 := Nat.le_mul_of_pos_right _ hmem.2.2.1.pos
        omega
      exact Finset.mem_Ioc.mpr ⟨by rw [geoGrid_zero]; exact hm_gt1, hm_ltN.le.trans hcover⟩
    obtain ⟨_, _, huniq_a⟩ := mem_Ioc_geoGrid_exists_unique hΔ0.le K t.2.1 hq2_in
    obtain ⟨_, _, huniq_b⟩ := mem_Ioc_geoGrid_exists_unique hΔ0.le K (t.1 * t.2.1) hm_in
    have ha_eq : a₁ = a₂ :=
      (huniq_a a₁ ⟨h1.1, ht₁.2.1⟩).trans (huniq_a a₂ ⟨h2.1, ht₂.2.1⟩).symm
    have hb_eq : b₁ = b₂ :=
      (huniq_b b₁ ⟨h1.2, ht₁.2.2.1⟩).trans (huniq_b b₂ ⟨h2.2, ht₂.2.2.1⟩).symm
    exact hne (Prod.ext ha_eq hb_eq)
  rw [Finset.sum_biUnion hdisj, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  -- Factor each rectangle `chenMRect N Δ a b` as `(∑_m a_m ψ(m)) * (∑_n b_n ψ(n))`
  set M_set := (Finset.Ioc (geoGrid Δ b) (geoGrid Δ (b + 1))).filter
    (fun m => ∃ p ∈ chenMPairs N, p.2 ∈ Finset.Ioc (geoGrid Δ a) (geoGrid Δ (a + 1)) ∧ p.1 * p.2 = m)
  set N_set := (Finset.Ioc (geoGrid Δ (a + 1)) ((N - 1) / geoGrid Δ (b + 1))).filter
    (fun n => n.Prime ∧ ¬ n ∣ N)
  have hM_sum :
      ∑ m ∈ Finset.Ioc (geoGrid Δ b) (geoGrid Δ (b + 1)),
          (if ∃ p ∈ chenMPairs N, p.2 ∈ Finset.Ioc (geoGrid Δ a) (geoGrid Δ (a + 1)) ∧ p.1 * p.2 = m
           then (1 : ℂ) else 0) * ψ (m : ZMod r) =
        ∑ m ∈ M_set, ψ (m : ZMod r) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => by split_ifs <;> simp
  have hN_sum :
      ∑ n ∈ Finset.Ioc (geoGrid Δ (a + 1)) ((N - 1) / geoGrid Δ (b + 1)),
          (if n.Prime ∧ ¬ n ∣ N then (1 : ℂ) else 0) * ψ (n : ZMod r) =
        ∑ n ∈ N_set, ψ (n : ZMod r) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => by split_ifs <;> simp
  rw [hM_sum, hN_sum, Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_bij (fun t _ => (t.1 * t.2.1, t.2.2)) ?_ ?_ ?_ ?_
  · intro t ht
    have ht_mem := Finset.mem_filter.mp ht
    have hchen := (Finset.mem_filter.mp ht_mem.1).2
    rcases hchen with ⟨hq1, hq2, hq3, hq1N, hq2N, hq3N, hq1_ge, hq1_lt, hq2_ge, hq23, hprod⟩
    have hp_mem : (t.1, t.2.1) ∈ chenMPairs N := by
      have hprod2 : t.1 * t.2.1 * t.2.1 < N :=
        lt_of_le_of_lt (Nat.mul_le_mul_left (t.1 * t.2.1) hq23) hprod
      have ht_rng := Finset.mem_product.mp (Finset.mem_filter.mp ht_mem.1).1
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ht_rng.1, (Finset.mem_product.mp ht_rng.2).1⟩,
        ⟨hq1, hq2, hq1N, hq2N, hq1_ge, hq1_lt, hq2_ge, hprod2⟩⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨ht_mem.2.2.1, ⟨(t.1, t.2.1), hp_mem, ht_mem.2.1, rfl⟩⟩,
       Finset.mem_filter.mpr ⟨ht_mem.2.2.2, ⟨hq3, hq3N⟩⟩⟩
  · intro t₁ ht₁ t₂ ht₂ h
    have hprod_eq : t₁.1 * t₁.2.1 * t₁.2.2 = t₂.1 * t₂.2.1 * t₂.2.2 := by
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      dsimp only at h1 h2
      rw [h1, h2]
    exact chenM_prod_injOn N (Finset.mem_filter.mp ht₁).1 (Finset.mem_filter.mp ht₂).1 hprod_eq
  · intro mn hmn
    have hmn_mem := Finset.mem_product.mp hmn
    have hm_mem := Finset.mem_filter.mp hmn_mem.1
    have hn_mem := Finset.mem_filter.mp hmn_mem.2
    obtain ⟨p, hp_mem, hp2_Ioc, hp_mul⟩ := hm_mem.2
    have hp_f := Finset.mem_filter.mp hp_mem
    rcases hp_f.2 with ⟨hp1, hp2, hp1N, hp2N, hp1_ge, hp1_lt, hp2_ge, _⟩
    have hn_Ioc := Finset.mem_Ioc.mp hn_mem.1
    have hp2_le_n : p.2 ≤ mn.2 :=
      le_trans (Finset.mem_Ioc.mp hp2_Ioc).2 hn_Ioc.1.le
    have hgb1_pos : 0 < geoGrid Δ (b + 1) := geoGrid_pos hΔ0.le (b + 1)
    have hprod_lt : p.1 * p.2 * mn.2 < N := by
      have hm_le : p.1 * p.2 ≤ geoGrid Δ (b + 1) := hp_mul ▸ (Finset.mem_Ioc.mp hm_mem.1).2
      have h1 : mn.2 * geoGrid Δ (b + 1) ≤ N - 1 := (Nat.le_div_iff_mul_le hgb1_pos).mp hn_Ioc.2
      have h2 : p.1 * p.2 * mn.2 ≤ geoGrid Δ (b + 1) * mn.2 := Nat.mul_le_mul_right mn.2 hm_le
      rw [mul_comm] at h1
      omega
    have hn_ltN : mn.2 < N := by
      have hle : mn.2 ≤ p.1 * p.2 * mn.2 := Nat.le_mul_of_pos_left mn.2 (mul_pos hp1.pos hp2.pos)
      omega
    have ht_chen : (p.1, p.2, mn.2) ∈ chenM N := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨(Finset.mem_product.mp hp_f.1).1,
         Finset.mem_product.mpr ⟨(Finset.mem_product.mp hp_f.1).2, Finset.mem_range.mpr hn_ltN⟩⟩,
        ⟨hp1, hp2, hn_mem.2.1, hp1N, hp2N, hn_mem.2.2, hp1_ge, hp1_lt, hp2_ge, hp2_le_n, hprod_lt⟩⟩
    refine ⟨(p.1, p.2, mn.2), ?_, Prod.ext hp_mul rfl⟩
    exact Finset.mem_filter.mpr ⟨ht_chen, hp2_Ioc, hp_mul ▸ hm_mem.1, hn_mem.1⟩
  · intro t _
    rw [Nat.cast_mul, map_mul]

/-- **Boundary Cardinality Bound**:
for `N ≥ 256` and `0 < Δ < 1`,
`((chenMBdy N Δ (⌊2 log N / Δ⌋₊ + 1)).card : ℝ) ≤ 3 * Δ * N * (1 + log N) + N^{5/6} + 1`. -/
private lemma card_chenMBdy_le {N : ℕ} {Δ : ℝ} (hN : 256 ≤ N) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    ((chenMBdy N Δ (⌊2 * Real.log (N : ℝ) / Δ⌋₊ + 1)).card : ℝ) ≤
      3 * Δ * (N : ℝ) * (1 + Real.log (N : ℝ)) + (N : ℝ) ^ ((5 : ℝ) / 6) + 1 := by
  set K := ⌊2 * Real.log (N : ℝ) / Δ⌋₊ + 1
  have hcover : N ≤ geoGrid Δ K := geoGrid_cover_ge (by omega) hΔ0 hΔ1
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  -- Every `t ∈ chenMBdy N Δ K` lies in either `B1` (near diagonal `q₂ ≤ q₃ ≤ (1+Δ) q₂`)
  -- or `B2` (near hyperbola `N / (1 + Δ) ≤ q₁ q₂ q₃ < N`).
  set B1 := (chenM N).filter fun t => (t.2.2 : ℝ) ≤ (1 + Δ) * (t.2.1 : ℝ)
  set B2 := (chenM N).filter fun t => (N : ℝ) / (1 + Δ) ≤ ((t.1 * t.2.1 * t.2.2 : ℕ) : ℝ)
  have hsub_union : chenMBdy N Δ K ⊆ B1 ∪ B2 := by
    intro t ht
    have ht_mem := Finset.mem_filter.mp ht
    have ht_chen := ht_mem.1
    have hnot_rect := ht_mem.2
    have hchen := (Finset.mem_filter.mp ht_chen).2
    rcases hchen with ⟨hq1, hq2, hq3, _, _, _, _, _, _, hq23, hprod⟩
    have hq2_in : t.2.1 ∈ Finset.Ioc (geoGrid Δ 0) (geoGrid Δ K) := by
      have hq2_ltN : t.2.1 < N := by
        have hle1 : t.2.1 ≤ t.1 * t.2.1 := Nat.le_mul_of_pos_left t.2.1 hq1.pos
        have hle2 : t.1 * t.2.1 ≤ t.1 * t.2.1 * t.2.2 := Nat.le_mul_of_pos_right _ hq3.pos
        omega
      exact Finset.mem_Ioc.mpr ⟨by rw [geoGrid_zero]; exact hq2.one_lt, hq2_ltN.le.trans hcover⟩
    have hm_in : t.1 * t.2.1 ∈ Finset.Ioc (geoGrid Δ 0) (geoGrid Δ K) := by
      have hm_gt1 : 1 < t.1 * t.2.1 := by have := hq1.two_le; have := hq2.two_le; nlinarith
      have hm_ltN : t.1 * t.2.1 < N := by
        have hle2 : t.1 * t.2.1 ≤ t.1 * t.2.1 * t.2.2 := Nat.le_mul_of_pos_right _ hq3.pos
        omega
      exact Finset.mem_Ioc.mpr ⟨by rw [geoGrid_zero]; exact hm_gt1, hm_ltN.le.trans hcover⟩
    obtain ⟨a, ⟨haK, hq2_a⟩, _⟩ := mem_Ioc_geoGrid_exists_unique hΔ0.le K t.2.1 hq2_in
    obtain ⟨b, ⟨hbK, hm_b⟩, _⟩ := mem_Ioc_geoGrid_exists_unique hΔ0.le K (t.1 * t.2.1) hm_in
    have hnot_q3 : ¬ t.2.2 ∈ Finset.Ioc (geoGrid Δ (a + 1)) ((N - 1) / geoGrid Δ (b + 1)) := by
      intro hq3_in
      exact hnot_rect a (Finset.mem_range.mpr haK) b (Finset.mem_range.mpr hbK)
        (Finset.mem_filter.mpr ⟨ht_chen, hq2_a, hm_b, hq3_in⟩)
    simp only [Finset.mem_Ioc, not_and, not_le] at hnot_q3
    rw [Finset.mem_union]
    by_cases hlow : t.2.2 ≤ geoGrid Δ (a + 1)
    · left
      refine Finset.mem_filter.mpr ⟨ht_chen, ?_⟩
      have hga_lt : geoGrid Δ a < t.2.1 := (Finset.mem_Ioc.mp hq2_a).1
      have hga_le : ((geoGrid Δ a + 1 : ℕ) : ℝ) ≤ (t.2.1 : ℝ) := by exact_mod_cast hga_lt
      have hpow_lt : (1 + Δ) ^ a < (geoGrid Δ a : ℝ) + 1 := Nat.lt_floor_add_one _
      have hga1_le : (geoGrid Δ (a + 1) : ℝ) ≤ (1 + Δ) ^ (a + 1) := Nat.floor_le (by positivity)
      calc (t.2.2 : ℝ) ≤ (geoGrid Δ (a + 1) : ℝ) := by exact_mod_cast hlow
        _ ≤ (1 + Δ) ^ (a + 1) := hga1_le
        _ = (1 + Δ) * (1 + Δ) ^ a := by rw [pow_succ, mul_comm]
        _ ≤ (1 + Δ) * ((geoGrid Δ a : ℝ) + 1) := mul_le_mul_of_nonneg_left hpow_lt.le (by linarith)
        _ ≤ (1 + Δ) * (t.2.1 : ℝ) := by
            have : (geoGrid Δ a : ℝ) + 1 ≤ (t.2.1 : ℝ) := by exact_mod_cast hga_lt
            exact mul_le_mul_of_nonneg_left this (by linarith)
    · right
      push Not at hlow
      have hhi : (N - 1) / geoGrid Δ (b + 1) < t.2.2 := hnot_q3 hlow
      have hgb1_pos : 0 < geoGrid Δ (b + 1) := geoGrid_pos hΔ0.le (b + 1)
      have hN_le : N ≤ geoGrid Δ (b + 1) * t.2.2 := by
        have h1 : ¬ t.2.2 * geoGrid Δ (b + 1) ≤ N - 1 := by
          intro hle
          have := (Nat.le_div_iff_mul_le hgb1_pos).mpr hle
          omega
        rw [mul_comm] at h1
        omega
      have hgb_lt : geoGrid Δ b < t.1 * t.2.1 := (Finset.mem_Ioc.mp hm_b).1
      have hpow_lt : (1 + Δ) ^ b < (geoGrid Δ b : ℝ) + 1 := Nat.lt_floor_add_one _
      have hgb1_le : (geoGrid Δ (b + 1) : ℝ) ≤ (1 + Δ) * ((t.1 * t.2.1 : ℕ) : ℝ) := by
        calc (geoGrid Δ (b + 1) : ℝ) ≤ (1 + Δ) ^ (b + 1) := Nat.floor_le (by positivity)
          _ = (1 + Δ) * (1 + Δ) ^ b := by rw [pow_succ, mul_comm]
          _ ≤ (1 + Δ) * ((geoGrid Δ b : ℝ) + 1) := mul_le_mul_of_nonneg_left hpow_lt.le (by linarith)
          _ ≤ (1 + Δ) * ((t.1 * t.2.1 : ℕ) : ℝ) := by
              have : (geoGrid Δ b : ℝ) + 1 ≤ ((t.1 * t.2.1 : ℕ) : ℝ) := by exact_mod_cast hgb_lt
              exact mul_le_mul_of_nonneg_left this (by linarith)
      refine Finset.mem_filter.mpr ⟨ht_chen, ?_⟩
      rw [div_le_iff₀ (show 0 < 1 + Δ by linarith)]
      have hNR : (N : ℝ) ≤ (geoGrid Δ (b + 1) : ℝ) * (t.2.2 : ℝ) := by exact_mod_cast hN_le
      calc (N : ℝ) ≤ (geoGrid Δ (b + 1) : ℝ) * (t.2.2 : ℝ) := hNR
        _ ≤ ((1 + Δ) * ((t.1 * t.2.1 : ℕ) : ℝ)) * (t.2.2 : ℝ) :=
            mul_le_mul_of_nonneg_right hgb1_le (Nat.cast_nonneg _)
        _ = ((t.1 * t.2.1 * t.2.2 : ℕ) : ℝ) * (1 + Δ) := by push_cast; ring
  -- Bound `B1.card`
  have hB1 : (B1.card : ℝ) ≤ 2 * Δ * (N : ℝ) * (1 + Real.log (N : ℝ)) + (N : ℝ) ^ ((5 : ℝ) / 6) := by
    -- Fiber `B1` over `q₁ ∈ Icc 1 ⌊N^{1/3}⌋₊` and `q₂ ∈ Icc 1 ⌊√(N / q₁)⌋₊`
    set Q1_max := ⌊(N : ℝ) ^ ((1 : ℝ) / 3)⌋₊
    set box1 : Finset (ℕ × ℕ × ℕ) :=
      (Finset.Icc 1 Q1_max).biUnion fun q₁ =>
        (Finset.Icc 1 ⌊Real.sqrt ((N : ℝ) / (q₁ : ℝ))⌋₊).biUnion fun q₂ =>
          (Finset.Icc q₂ ⌊(1 + Δ) * (q₂ : ℝ)⌋₊).image fun q₃ => (q₁, q₂, q₃)
    have hB1_sub : B1 ⊆ box1 := by
      intro t ht
      have ht_f := Finset.mem_filter.mp ht
      rcases (Finset.mem_filter.mp ht_f.1).2 with ⟨hq1, hq2, _, _, _, _, _, hq1_lt, _, hq23, hprod⟩
      simp only [box1, Finset.mem_biUnion, Finset.mem_image, Finset.mem_Icc]
      refine ⟨t.1, ⟨hq1.one_lt.le, Nat.le_floor hq1_lt.le⟩, t.2.1, ⟨hq2.one_lt.le, ?_⟩,
        t.2.2, ⟨hq23, Nat.le_floor ht_f.2⟩, rfl⟩
      refine Nat.le_floor (Real.le_sqrt_of_sq_le ?_)
      rw [le_div_iff₀ (Nat.cast_pos.mpr hq1.pos)]
      have h1 : t.2.1 * t.2.1 * t.1 ≤ N := by
        have h2 : t.1 * t.2.1 * t.2.1 ≤ t.1 * t.2.1 * t.2.2 := Nat.mul_le_mul_left _ hq23
        nlinarith
      have h1R : ((t.2.1 : ℝ) ^ 2) * (t.1 : ℝ) ≤ (N : ℝ) := by
        rw [sq]; exact_mod_cast h1
      exact h1R
    have hbox1_card : (box1.card : ℝ) ≤
        ∑ q₁ ∈ Finset.Icc 1 Q1_max,
          ∑ q₂ ∈ Finset.Icc 1 ⌊Real.sqrt ((N : ℝ) / (q₁ : ℝ))⌋₊,
            (Δ * (q₂ : ℝ) + 1) := by
      have h1 : box1.card ≤ ∑ q₁ ∈ Finset.Icc 1 Q1_max,
          ∑ q₂ ∈ Finset.Icc 1 ⌊Real.sqrt ((N : ℝ) / (q₁ : ℝ))⌋₊,
            ((Finset.Icc q₂ ⌊(1 + Δ) * (q₂ : ℝ)⌋₊).image fun q₃ => (q₁, q₂, q₃)).card := by
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun q₁ _ => Finset.card_biUnion_le)
      have h1R : (box1.card : ℝ) ≤ ∑ q₁ ∈ Finset.Icc 1 Q1_max,
          ∑ q₂ ∈ Finset.Icc 1 ⌊Real.sqrt ((N : ℝ) / (q₁ : ℝ))⌋₊,
            (((Finset.Icc q₂ ⌊(1 + Δ) * (q₂ : ℝ)⌋₊).image fun q₃ => (q₁, q₂, q₃)).card : ℝ) := by
        exact_mod_cast h1
      refine h1R.trans (Finset.sum_le_sum fun q₁ _ => Finset.sum_le_sum fun q₂ _ => ?_)
      have hc1 : (((Finset.Icc q₂ ⌊(1 + Δ) * (q₂ : ℝ)⌋₊).image fun q₃ => (q₁, q₂, q₃)).card : ℝ) ≤
          ((Finset.Icc q₂ ⌊(1 + Δ) * (q₂ : ℝ)⌋₊).card : ℝ) := by
        exact_mod_cast Finset.card_image_le
      refine hc1.trans ?_
      rw [Nat.card_Icc]
      have hle_fl : q₂ ≤ ⌊(1 + Δ) * (q₂ : ℝ)⌋₊ := Nat.le_floor (by nlinarith [Nat.cast_nonneg (α := ℝ) q₂])
      have hcast : ((⌊(1 + Δ) * (q₂ : ℝ)⌋₊ + 1 - q₂ : ℕ) : ℝ) =
          (⌊(1 + Δ) * (q₂ : ℝ)⌋₊ : ℝ) + 1 - (q₂ : ℝ) := by
        rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
      rw [hcast]
      linarith [Nat.floor_le (show 0 ≤ (1 + Δ) * (q₂ : ℝ) by positivity)]
    have hinner : ∀ q₁ ∈ Finset.Icc 1 Q1_max,
        ∑ q₂ ∈ Finset.Icc 1 ⌊Real.sqrt ((N : ℝ) / (q₁ : ℝ))⌋₊, (Δ * (q₂ : ℝ) + 1) ≤
          Δ * ((N : ℝ) / (q₁ : ℝ)) + Real.sqrt (N : ℝ) := by
      intro q₁ hq₁
      have hq1_pos : (0 : ℝ) < (q₁ : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hq₁).1
      set S := ⌊Real.sqrt ((N : ℝ) / (q₁ : ℝ))⌋₊
      have hSR : (S : ℝ) ≤ Real.sqrt ((N : ℝ) / (q₁ : ℝ)) := Nat.floor_le (Real.sqrt_nonneg _)
      have hS2 : (S : ℝ) ^ 2 ≤ (N : ℝ) / (q₁ : ℝ) := by
        calc (S : ℝ) ^ 2 ≤ (Real.sqrt ((N : ℝ) / (q₁ : ℝ))) ^ 2 :=
              pow_le_pow_left₀ (Nat.cast_nonneg _) hSR 2
          _ = (N : ℝ) / (q₁ : ℝ) := Real.sq_sqrt (by positivity)
      have hS_le_sqN : (S : ℝ) ≤ Real.sqrt (N : ℝ) :=
        hSR.trans (Real.sqrt_le_sqrt (div_le_self hN_pos.le (by exact_mod_cast (Finset.mem_Icc.mp hq₁).1)))
      calc ∑ q₂ ∈ Finset.Icc 1 S, (Δ * (q₂ : ℝ) + 1)
          ≤ ∑ _q₂ ∈ Finset.Icc 1 S, (Δ * (S : ℝ) + 1) := by
            refine Finset.sum_le_sum fun q₂ hq₂ => ?_
            have : (q₂ : ℝ) ≤ (S : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hq₂).2
            nlinarith
        _ = (S : ℝ) * (Δ * (S : ℝ) + 1) := by
            rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        _ = Δ * (S : ℝ) ^ 2 + (S : ℝ) := by ring
        _ ≤ Δ * ((N : ℝ) / (q₁ : ℝ)) + Real.sqrt (N : ℝ) := by nlinarith
    have hQ1_le : Q1_max ≤ N := by
      refine Nat.floor_le_of_le ?_
      calc (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (N : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N)) (by norm_num)
        _ = (N : ℝ) := Real.rpow_one _
    have hsum1 : ∑ q₁ ∈ Finset.Icc 1 Q1_max, Δ * ((N : ℝ) / (q₁ : ℝ)) ≤
        Δ * (N : ℝ) * (1 + Real.log (N : ℝ)) := by
      calc ∑ q₁ ∈ Finset.Icc 1 Q1_max, Δ * ((N : ℝ) / (q₁ : ℝ))
          = (Δ * (N : ℝ)) * ∑ q₁ ∈ Finset.Icc 1 Q1_max, (1 : ℝ) / (q₁ : ℝ) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
        _ ≤ (Δ * (N : ℝ)) * ∑ q₁ ∈ Finset.Icc 1 N, (1 : ℝ) / (q₁ : ℝ) :=
            mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hQ1_le)
                fun _ _ _ => by positivity) (by positivity)
        _ ≤ (Δ * (N : ℝ)) * (1 + Real.log (N : ℝ)) :=
            mul_le_mul_of_nonneg_left (Stage10ZeroDensity.sum_inv_le_one_add_log (by omega)) (by positivity)
        _ = Δ * (N : ℝ) * (1 + Real.log (N : ℝ)) := by ring
    have hsum2 : ∑ _q₁ ∈ Finset.Icc 1 Q1_max, Real.sqrt (N : ℝ) ≤ (N : ℝ) ^ ((5 : ℝ) / 6) := by
      rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, Real.sqrt_eq_rpow]
      calc (Q1_max : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2)
          ≤ (N : ℝ) ^ ((1 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by positivity)
        _ = (N : ℝ) ^ ((5 : ℝ) / 6) := by rw [← Real.rpow_add hN_pos]; norm_num
    have hB1_le_box : (B1.card : ℝ) ≤ (box1.card : ℝ) := by exact_mod_cast Finset.card_le_card hB1_sub
    have hnn : 0 ≤ Δ * (N : ℝ) * (1 + Real.log (N : ℝ)) := by
      have : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N; positivity
    calc (B1.card : ℝ) ≤ (box1.card : ℝ) := hB1_le_box
      _ ≤ ∑ q₁ ∈ Finset.Icc 1 Q1_max, (Δ * ((N : ℝ) / (q₁ : ℝ)) + Real.sqrt (N : ℝ)) :=
          hbox1_card.trans (Finset.sum_le_sum hinner)
      _ = (∑ q₁ ∈ Finset.Icc 1 Q1_max, Δ * ((N : ℝ) / (q₁ : ℝ))) +
          (∑ _q₁ ∈ Finset.Icc 1 Q1_max, Real.sqrt (N : ℝ)) := Finset.sum_add_distrib
      _ ≤ 2 * Δ * (N : ℝ) * (1 + Real.log (N : ℝ)) + (N : ℝ) ^ ((5 : ℝ) / 6) := by linarith
  -- Bound `B2.card` via injectivity of `chenM_prod_injOn` into `Ico ⌊N / (1 + Δ)⌋₊ N`
  have hB2 : (B2.card : ℝ) ≤ Δ * (N : ℝ) + 1 := by
    have hsub : B2.image (fun t => t.1 * t.2.1 * t.2.2) ⊆ Finset.Ico ⌊(N : ℝ) / (1 + Δ)⌋₊ N := by
      intro m hm
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hm
      have ht_f := Finset.mem_filter.mp ht
      have hlt : t.1 * t.2.1 * t.2.2 < N := (Finset.mem_filter.mp ht_f.1).2.2.2.2.2.2.2.2.2.2.2
      have hge : ⌊(N : ℝ) / (1 + Δ)⌋₊ ≤ t.1 * t.2.1 * t.2.2 :=
        Nat.floor_le_of_le ht_f.2
      exact Finset.mem_Ico.mpr ⟨hge, hlt⟩
    have hcard_eq : B2.card = (B2.image (fun t => t.1 * t.2.1 * t.2.2)).card :=
      (Finset.card_image_of_injOn ((chenM_prod_injOn N).mono
        (fun t ht => (Finset.mem_filter.mp ht).1))).symm
    have hnat : B2.card ≤ N - ⌊(N : ℝ) / (1 + Δ)⌋₊ := by
      rw [hcard_eq]
      exact (Finset.card_le_card hsub).trans (by rw [Nat.card_Ico])
    have hfl_le : ⌊(N : ℝ) / (1 + Δ)⌋₊ ≤ N :=
      Nat.floor_le_of_le (div_le_self hN_pos.le (by linarith))
    have h1 : (B2.card : ℝ) ≤ (N : ℝ) - (⌊(N : ℝ) / (1 + Δ)⌋₊ : ℝ) := by
      rw [← Nat.cast_sub hfl_le]; exact_mod_cast hnat
    have h2 : (N : ℝ) / (1 + Δ) - 1 < (⌊(N : ℝ) / (1 + Δ)⌋₊ : ℝ) := by
      linarith [Nat.lt_floor_add_one ((N : ℝ) / (1 + Δ))]
    have h3 : (N : ℝ) - (N : ℝ) / (1 + Δ) ≤ Δ * (N : ℝ) := by
      have hEq : (N : ℝ) - (N : ℝ) / (1 + Δ) = (Δ / (1 + Δ)) * (N : ℝ) := by
        field_simp [(by linarith : 1 + Δ ≠ 0)]; ring
      rw [hEq]
      exact mul_le_mul_of_nonneg_right (div_le_self hΔ0.le (by linarith)) hN_pos.le
    linarith
  have hunion_card : ((chenMBdy N Δ K).card : ℝ) ≤ (B1.card : ℝ) + (B2.card : ℝ) := by
    have hnat : (chenMBdy N Δ K).card ≤ B1.card + B2.card :=
      (Finset.card_le_card hsub_union).trans (Finset.card_union_le B1 B2)
    exact_mod_cast hnat
  have hlogN_nn : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have hΔN_le : Δ * (N : ℝ) ≤ Δ * (N : ℝ) * (1 + Real.log (N : ℝ)) :=
    le_mul_of_one_le_right (by positivity) (by linarith)
  linarith

/-- Elementary `sqrt (a + b) ≤ sqrt a + sqrt b`. -/
private lemma sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
  linarith [show 0 ≤ 2 * Real.sqrt a * Real.sqrt b by positivity]

open Classical in
/-- Sum of primitive character weights `∑_{q ≤ Q} (q / φ(q)) * #{χ mod q : χ.IsPrimitive} ≤ Q²`. -/
private lemma sum_prim_weight_le (Q : ℕ) :
    ∑ k ∈ Finset.range Q,
        (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ((Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive)).card : ℝ) ≤
      (Q : ℝ) ^ 2 := by
  calc ∑ k ∈ Finset.range Q,
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ((Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive)).card : ℝ)
      ≤ ∑ _k ∈ Finset.range Q, (Q : ℝ) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkQ : k + 1 ≤ Q := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
        have hphi_pos : (0 : ℝ) < (Nat.totient (k + 1) : ℝ) :=
          Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.succ_pos k))
        have htot : Fintype.card (DirichletCharacter ℂ (k + 1)) = (k + 1).totient := by
          rw [← Nat.card_eq_fintype_card]
          exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ (k + 1)
        have hcard :
            ((Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive)).card : ℝ) ≤
              (Nat.totient (k + 1) : ℝ) := by
          have hnat : (Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive)).card ≤
              (k + 1).totient :=
            (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, htot])
          exact_mod_cast hnat
        calc (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
              ((Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive)).card : ℝ)
            ≤ (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) * (Nat.totient (k + 1) : ℝ) :=
              mul_le_mul_of_nonneg_left hcard (by positivity)
          _ = ((k + 1 : ℕ) : ℝ) := div_mul_cancel₀ _ hphi_pos.ne'
          _ ≤ (Q : ℝ) := by exact_mod_cast hkQ
    _ = (Q : ℝ) ^ 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, sq]

open Classical in
/-- **Boundary Large-Sieve Bound**:
for `1 ≤ D`, `(D : ℝ) ≤ Real.sqrt N`, `N ≥ 256`, `0 < Δ < 1`, and `(N : ℝ) ^ (-1 / 24) ≤ Δ`,
`(1 / D) * ∑_{k < 2 D} ((k+1)/φ(k+1)) ∑*_{ψ mod k+1} ‖∑_{t ∈ Bdy} ψ(m t)‖ ≤ 20 * N * √Δ * √(1 + log N)`. -/
private lemma sum_chenMBdy_large_sieve_le {D N : ℕ} {Δ : ℝ}
    (hD : 1 ≤ D) (hN : 256 ≤ N) (hD_sqN : (D : ℝ) ≤ Real.sqrt (N : ℝ))
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (hΔ_lo : (N : ℝ) ^ (-(1 : ℝ) / 24) ≤ Δ) :
    let K := ⌊2 * Real.log (N : ℝ) / Δ⌋₊ + 1
    (1 / (D : ℝ)) *
      ∑ k ∈ Finset.range (2 * D),
        (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
            ‖∑ t ∈ chenMBdy N Δ K, ψ ((t.1 * t.2.1 * t.2.2 : ℕ) : ZMod (k + 1))‖ ≤
      20 * (N : ℝ) * Real.sqrt Δ * Real.sqrt (1 + Real.log (N : ℝ)) := by
  intro K
  have hD_pos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  set Bdy := chenMBdy N Δ K
  set BdyProd := Bdy.image (fun t => t.1 * t.2.1 * t.2.2)
  let c : ℕ → ℂ := fun n => if n ∈ BdyProd then 1 else 0
  have hsum_eq : ∀ (r : ℕ) (ψ : DirichletCharacter ℂ r),
      ∑ t ∈ Bdy, ψ ((t.1 * t.2.1 * t.2.2 : ℕ) : ZMod r) =
        ∑ n ∈ Finset.Ioc 0 N, c n * ψ (n : ZMod r) := by
    intro r ψ
    have hinj : Set.InjOn (fun t : ℕ × ℕ × ℕ => t.1 * t.2.1 * t.2.2) (Bdy : Set (ℕ × ℕ × ℕ)) :=
      (chenM_prod_injOn N).mono (fun t ht => (Finset.mem_filter.mp ht).1)
    have hsub : BdyProd ⊆ Finset.Ioc 0 N := by
      intro n hn
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
      rcases (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2 with
        ⟨hq1, hq2, hq3, _, _, _, _, _, _, _, hprod⟩
      exact Finset.mem_Ioc.mpr ⟨mul_pos (mul_pos hq1.pos hq2.pos) hq3.pos, hprod.le⟩
    calc ∑ t ∈ Bdy, ψ ((t.1 * t.2.1 * t.2.2 : ℕ) : ZMod r)
        = ∑ n ∈ BdyProd, ψ (n : ZMod r) := (Finset.sum_image (f := fun n : ℕ => ψ (n : ZMod r)) hinj).symm
      _ = ∑ n ∈ Finset.Ioc 0 N, if n ∈ BdyProd then ψ (n : ZMod r) else 0 := by
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub]
      _ = ∑ n ∈ Finset.Ioc 0 N, c n * ψ (n : ZMod r) := by
          refine Finset.sum_congr rfl fun n _ => by dsimp only [c]; split_ifs <;> simp
  have hL2 : ∑ n ∈ Finset.Ioc 0 N, ‖c n‖ ^ 2 = (Bdy.card : ℝ) := by
    have hinj : Set.InjOn (fun t : ℕ × ℕ × ℕ => t.1 * t.2.1 * t.2.2) (Bdy : Set (ℕ × ℕ × ℕ)) :=
      (chenM_prod_injOn N).mono (fun t ht => (Finset.mem_filter.mp ht).1)
    have hsub : BdyProd ⊆ Finset.Ioc 0 N := by
      intro n hn
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
      rcases (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2 with
        ⟨hq1, hq2, hq3, _, _, _, _, _, _, _, hprod⟩
      exact Finset.mem_Ioc.mpr ⟨mul_pos (mul_pos hq1.pos hq2.pos) hq3.pos, hprod.le⟩
    have h1 : ∑ n ∈ Finset.Ioc 0 N, ‖c n‖ ^ 2 = ∑ n ∈ Finset.Ioc 0 N, if n ∈ BdyProd then (1 : ℝ) else 0 := by
      refine Finset.sum_congr rfl fun n _ => by dsimp only [c]; split_ifs <;> simp
    rw [h1, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub,
      Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_image_of_injOn hinj]
  -- Cauchy–Schwarz + Multiplicative Large Sieve
  let S : Finset (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) :=
    (Finset.range (2 * D)).sigma fun k =>
      Finset.univ.filter fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive
  let w : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ :=
    fun p => ((p.1 + 1 : ℕ) : ℝ) / (Nat.totient (p.1 + 1) : ℝ)
  have hLHS :
      ∑ k ∈ Finset.range (2 * D),
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
              ‖∑ t ∈ Bdy, ψ ((t.1 * t.2.1 * t.2.2 : ℕ) : ZMod (k + 1))‖ =
        ∑ p ∈ S, Real.sqrt (w p) *
          (Real.sqrt (w p) * ‖∑ n ∈ Finset.Ioc 0 N, c n * p.2 (n : ZMod (p.1 + 1))‖) := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [hsum_eq, ← mul_assoc, Real.mul_self_sqrt (by dsimp only [w]; positivity)]
  have hCS :
      ∑ p ∈ S, Real.sqrt (w p) *
          (Real.sqrt (w p) * ‖∑ n ∈ Finset.Ioc 0 N, c n * p.2 (n : ZMod (p.1 + 1))‖) ≤
        Real.sqrt (∑ p ∈ S, w p) *
          Real.sqrt (∑ p ∈ S, w p * ‖∑ n ∈ Finset.Ioc 0 N, c n * p.2 (n : ZMod (p.1 + 1))‖ ^ 2) := by
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq S
      (fun p => Real.sqrt (w p))
      (fun p => Real.sqrt (w p) * ‖∑ n ∈ Finset.Ioc 0 N, c n * p.2 (n : ZMod (p.1 + 1))‖)
    have hW : ∑ p ∈ S, (Real.sqrt (w p)) ^ 2 = ∑ p ∈ S, w p :=
      Finset.sum_congr rfl fun p _ => Real.sq_sqrt (by dsimp only [w]; positivity)
    have hV2 : ∑ p ∈ S, (Real.sqrt (w p) * ‖∑ n ∈ Finset.Ioc 0 N, c n * p.2 (n : ZMod (p.1 + 1))‖) ^ 2 =
        ∑ p ∈ S, w p * ‖∑ n ∈ Finset.Ioc 0 N, c n * p.2 (n : ZMod (p.1 + 1))‖ ^ 2 :=
      Finset.sum_congr rfl fun p _ => by rw [mul_pow, Real.sq_sqrt (by dsimp only [w]; positivity)]
    rw [hW, hV2] at h1
    rw [← Real.sqrt_mul (Finset.sum_nonneg fun p _ => by dsimp only [w]; positivity)]
    exact Real.le_sqrt_of_sq_le h1
  have hW_le : ∑ p ∈ S, w p ≤ (2 * (D : ℝ)) ^ 2 := by
    have hEq : ∑ p ∈ S, w p =
        ∑ k ∈ Finset.range (2 * D),
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ((Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive)).card : ℝ) := by
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun k _ => by dsimp only [w]; rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [hEq]
    simpa [Nat.cast_mul] using sum_prim_weight_le (2 * D)
  have hLS :
      ∑ p ∈ S, w p * ‖∑ n ∈ Finset.Ioc 0 N, c n * p.2 (n : ZMod (p.1 + 1))‖ ^ 2 ≤
        ((N : ℝ) + 3 * ((2 * D : ℕ) : ℝ) ^ 2) * (Bdy.card : ℝ) := by
    have hEq : ∑ p ∈ S, w p * ‖∑ n ∈ Finset.Ioc 0 N, c n * p.2 (n : ZMod (p.1 + 1))‖ ^ 2 =
        ∑ k ∈ Finset.range (2 * D),
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
              ‖∑ n ∈ Finset.Ioc 0 N, c n * ψ (n : ZMod (k + 1))‖ ^ 2 := by
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
    rw [hEq, ← hL2]
    simpa using Stage11BombieriVinogradov.multiplicative_large_sieve_Ioc_interval (2 * D) 0 N c
  have hD2 : (D : ℝ) ^ 2 ≤ (N : ℝ) := by
    calc (D : ℝ) ^ 2 ≤ (Real.sqrt (N : ℝ)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hD_sqN 2
      _ = (N : ℝ) := Real.sq_sqrt hN_pos.le
  have hlen : (N : ℝ) + 3 * ((2 * D : ℕ) : ℝ) ^ 2 ≤ 13 * (N : ℝ) := by
    have hcast : 3 * ((2 * D : ℕ) : ℝ) ^ 2 = 12 * (D : ℝ) ^ 2 := by push_cast; ring
    linarith
  have hBdy_card : (Bdy.card : ℝ) ≤ 5 * Δ * (N : ℝ) * (1 + Real.log (N : ℝ)) := by
    have h1 := card_chenMBdy_le hN hΔ0 hΔ1
    have hlogN_nn : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
    have h56_le : (N : ℝ) ^ ((5 : ℝ) / 6) ≤ Δ * (N : ℝ) := by
      calc (N : ℝ) ^ ((5 : ℝ) / 6)
          ≤ (N : ℝ) ^ ((23 : ℝ) / 24) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N)) (by norm_num)
        _ = (N : ℝ) ^ (-(1 : ℝ) / 24 + (1 : ℝ)) := by norm_num
        _ = (N : ℝ) ^ (-(1 : ℝ) / 24) * (N : ℝ) ^ (1 : ℝ) := Real.rpow_add hN_pos _ _
        _ = (N : ℝ) ^ (-(1 : ℝ) / 24) * (N : ℝ) := by rw [Real.rpow_one]
        _ ≤ Δ * (N : ℝ) := mul_le_mul_of_nonneg_right hΔ_lo hN_pos.le
    have h1_le : (1 : ℝ) ≤ Δ * (N : ℝ) := by
      have : (1 : ℝ) ≤ (N : ℝ) ^ ((5 : ℝ) / 6) :=
        Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ N)) (by norm_num)
      linarith
    nlinarith
  have hprod_le : ((N : ℝ) + 3 * ((2 * D : ℕ) : ℝ) ^ 2) * (Bdy.card : ℝ) ≤
      (10 * (N : ℝ) * Real.sqrt Δ * Real.sqrt (1 + Real.log (N : ℝ))) ^ 2 := by
    have hlogN_nn : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
    have hsq : (10 * (N : ℝ) * Real.sqrt Δ * Real.sqrt (1 + Real.log (N : ℝ))) ^ 2 =
        100 * (N : ℝ) ^ 2 * Δ * (1 + Real.log (N : ℝ)) := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hΔ0.le, Real.sq_sqrt (by linarith)]
      ring
    rw [hsq]
    calc ((N : ℝ) + 3 * ((2 * D : ℕ) : ℝ) ^ 2) * (Bdy.card : ℝ)
        ≤ (13 * (N : ℝ)) * (5 * Δ * (N : ℝ) * (1 + Real.log (N : ℝ))) :=
          mul_le_mul hlen hBdy_card (Nat.cast_nonneg _) (by positivity)
      _ = 65 * (N : ℝ) ^ 2 * Δ * (1 + Real.log (N : ℝ)) := by ring
      _ ≤ 100 * (N : ℝ) ^ 2 * Δ * (1 + Real.log (N : ℝ)) := by nlinarith [show 0 ≤ (N : ℝ) ^ 2 * Δ * (1 + Real.log (N : ℝ)) by positivity]
  have hsqrtW : Real.sqrt (∑ p ∈ S, w p) ≤ 2 * (D : ℝ) :=
    (Real.sqrt_le_sqrt hW_le).trans_eq (Real.sqrt_sq (by positivity))
  have hsqrtV : Real.sqrt (∑ p ∈ S, w p * ‖∑ n ∈ Finset.Ioc 0 N, c n * p.2 (n : ZMod (p.1 + 1))‖ ^ 2) ≤
      10 * (N : ℝ) * Real.sqrt Δ * Real.sqrt (1 + Real.log (N : ℝ)) :=
    (Real.sqrt_le_sqrt (hLS.trans hprod_le)).trans_eq (Real.sqrt_sq (by positivity))
  rw [hLHS]
  calc (1 / (D : ℝ)) * ∑ p ∈ S, Real.sqrt (w p) *
          (Real.sqrt (w p) * ‖∑ n ∈ Finset.Ioc 0 N, c n * p.2 (n : ZMod (p.1 + 1))‖)
      ≤ (1 / (D : ℝ)) * (Real.sqrt (∑ p ∈ S, w p) *
          Real.sqrt (∑ p ∈ S, w p * ‖∑ n ∈ Finset.Ioc 0 N, c n * p.2 (n : ZMod (p.1 + 1))‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hCS (by positivity)
    _ ≤ (1 / (D : ℝ)) * ((2 * (D : ℝ)) * (10 * (N : ℝ) * Real.sqrt Δ * Real.sqrt (1 + Real.log (N : ℝ)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hsqrtW hsqrtV (Real.sqrt_nonneg _) (by positivity)) (by positivity)
    _ = 20 * (N : ℝ) * Real.sqrt Δ * Real.sqrt (1 + Real.log (N : ℝ)) := by
        field_simp [hD_pos.ne']; ring

open Classical in
/-- **Single Geometric Box Bilinear Large-Sieve Bound**:
for `1 ≤ D`, `N ≥ 4096`, `0 < Δ < 1`, `(N : ℝ) ^ (-1 / 24) ≤ Δ`, and any box `(a, b)`:
`(1 / D) * ∑_{k < 2 D} ((k+1)/φ(k+1)) ∑*_{ψ mod k+1} ‖A_{a,b}(ψ) * B_{a,b}(ψ)‖ ≤ 2 Δ N / D + 24 N^{5/6} + 32 D √N`. -/
private lemma sum_chenMRect_box_large_sieve_le {D N a b : ℕ} {Δ : ℝ}
    (hD : 1 ≤ D) (hN : 4096 ≤ N) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hΔ_lo : (N : ℝ) ^ (-(1 : ℝ) / 24) ≤ Δ) :
    (1 / (D : ℝ)) *
      ∑ k ∈ Finset.range (2 * D),
        (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
            ‖(∑ m ∈ Finset.Ioc (geoGrid Δ b) (geoGrid Δ (b + 1)),
                (if ∃ p ∈ chenMPairs N, p.2 ∈ Finset.Ioc (geoGrid Δ a) (geoGrid Δ (a + 1)) ∧ p.1 * p.2 = m
                 then (1 : ℂ) else 0) * ψ (m : ZMod (k + 1))) *
             (∑ n ∈ Finset.Ioc (geoGrid Δ (a + 1)) ((N - 1) / geoGrid Δ (b + 1)),
                (if n.Prime ∧ ¬ n ∣ N then (1 : ℂ) else 0) * ψ (n : ZMod (k + 1)))‖ ≤
      2 * Δ * (N : ℝ) / (D : ℝ) + 24 * (N : ℝ) ^ ((5 : ℝ) / 6) + 32 * (D : ℝ) * Real.sqrt (N : ℝ) := by
  have hD_pos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  set M₁ := geoGrid Δ b
  set M₂ := geoGrid Δ (b + 1)
  set N₁ := geoGrid Δ (a + 1)
  set N₂ := (N - 1) / geoGrid Δ (b + 1)
  let coefA : ℕ → ℂ := fun m =>
    if ∃ p ∈ chenMPairs N, p.2 ∈ Finset.Ioc (geoGrid Δ a) (geoGrid Δ (a + 1)) ∧ p.1 * p.2 = m
    then 1 else 0
  let coefB : ℕ → ℂ := fun n => if n.Prime ∧ ¬ n ∣ N then 1 else 0
  -- If `coefA` vanishes identically on `Ioc M₁ M₂`, the entire LHS is `0`!
  by_cases hA_zero : ∀ m ∈ Finset.Ioc M₁ M₂, coefA m = 0
  · have hzero :
        ∑ k ∈ Finset.range (2 * D),
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
              ‖(∑ m ∈ Finset.Ioc M₁ M₂, coefA m * ψ (m : ZMod (k + 1))) *
               (∑ n ∈ Finset.Ioc N₁ N₂, coefB n * ψ (n : ZMod (k + 1)))‖ = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      have hinner : ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
          ‖(∑ m ∈ Finset.Ioc M₁ M₂, coefA m * ψ (m : ZMod (k + 1))) *
           (∑ n ∈ Finset.Ioc N₁ N₂, coefB n * ψ (n : ZMod (k + 1)))‖ = 0 := by
        refine Finset.sum_eq_zero fun ψ _ => ?_
        have hS0 : ∑ m ∈ Finset.Ioc M₁ M₂, coefA m * ψ (m : ZMod (k + 1)) = 0 :=
          Finset.sum_eq_zero fun m hm => by rw [hA_zero m hm, zero_mul]
        rw [hS0, zero_mul, norm_zero]
      rw [hinner, mul_zero]
    rw [hzero, mul_zero]
    positivity
  · -- Otherwise, there exists `m₀ ∈ Ioc M₁ M₂` with `m₀ = p.1 * p.2` for some `p ∈ chenMPairs N`!
    push Not at hA_zero
    obtain ⟨m₀, hm₀_Ioc, hm₀_ne⟩ := hA_zero
    have hex : ∃ p ∈ chenMPairs N, p.2 ∈ Finset.Ioc (geoGrid Δ a) (geoGrid Δ (a + 1)) ∧ p.1 * p.2 = m₀ := by
      by_contra hno; exact hm₀_ne (if_neg hno)
    obtain ⟨p₀, hp₀, _, hp₀_mul⟩ := hex
    rcases (Finset.mem_filter.mp hp₀).2 with ⟨hp1, hp2, _, _, _, _, hp2_ge, hp_prod⟩
    -- Therefore `N^{1/3} ≤ m₀ ≤ N^{2/3}`, so `N^{1/3} / 4 ≤ M₁ ≤ N^{2/3}`!
    have hm₀_ge : (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (m₀ : ℝ) := by
      have h1 : (p₀.2 : ℝ) ≤ (m₀ : ℝ) := by
        rw [← hp₀_mul]; exact_mod_cast Nat.le_mul_of_pos_left p₀.2 hp1.pos
      exact hp2_ge.trans h1
    have hm₀_lt : (m₀ : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 3) := by
      have hprodR : (m₀ : ℝ) * (p₀.2 : ℝ) ≤ (N : ℝ) := by
        rw [← hp₀_mul]; exact_mod_cast hp_prod.le
      have hN13_pos : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hN_pos _
      have h1 : (m₀ : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (N : ℝ) :=
        (mul_le_mul_of_nonneg_left hp2_ge (Nat.cast_nonneg _)).trans hprodR
      have hdiv := (le_div_iff₀ hN13_pos).mpr h1
      have hpow : (N : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 3) = (N : ℝ) ^ ((2 : ℝ) / 3) := by
        calc (N : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 3)
            = (N : ℝ) ^ (1 : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 3) := by rw [Real.rpow_one]
          _ = (N : ℝ) ^ ((1 : ℝ) - (1 : ℝ) / 3) := (Real.rpow_sub hN_pos _ _).symm
          _ = (N : ℝ) ^ ((2 : ℝ) / 3) := by norm_num
      rwa [hpow] at hdiv
    have hM1_le : (M₁ : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 3) :=
      (by exact_mod_cast (Finset.mem_Ioc.mp hm₀_Ioc).1.le : (M₁ : ℝ) ≤ (m₀ : ℝ)).trans hm₀_lt
    have hM2_ge : (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (M₂ : ℝ) :=
      hm₀_ge.trans (by exact_mod_cast (Finset.mem_Ioc.mp hm₀_Ioc).2)
    have hM1_pos : (0 : ℝ) < (M₁ : ℝ) := Nat.cast_pos.mpr (geoGrid_pos hΔ0.le b)
    have hM2_le : (M₂ : ℝ) ≤ (1 + Δ) * ((M₁ : ℝ) + 1) := by
      have h1 : (M₂ : ℝ) ≤ (1 + Δ) ^ (b + 1) := Nat.floor_le (by positivity)
      have h2 : (1 + Δ) ^ b < (M₁ : ℝ) + 1 := Nat.lt_floor_add_one _
      calc (M₂ : ℝ) ≤ (1 + Δ) ^ (b + 1) := h1
        _ = (1 + Δ) * (1 + Δ) ^ b := by rw [pow_succ, mul_comm]
        _ ≤ (1 + Δ) * ((M₁ : ℝ) + 1) := mul_le_mul_of_nonneg_left h2.le (by linarith)
    have hM1_ge : (N : ℝ) ^ ((1 : ℝ) / 3) / 4 ≤ (M₁ : ℝ) := by
      have hN13_ge4 : (4 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := by
        have h64 : (4 : ℝ) ^ (3 : ℝ) ≤ (N : ℝ) := by
          have : (4096 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
          norm_num; linarith
        calc (4 : ℝ) = ((4 : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) := by
              rw [← Real.rpow_mul (by norm_num)]; norm_num
          _ ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_le_rpow (by positivity) h64 (by norm_num)
      have : (N : ℝ) ^ ((1 : ℝ) / 3) ≤ 2 * ((M₁ : ℝ) + 1) := by nlinarith
      linarith
    -- Interval length bounds `L_m ≤ 2 Δ M₁` and `L_n ≤ N / M₁`
    set L_m : ℝ := ((M₂ - M₁ : ℕ) : ℝ)
    set L_n : ℝ := ((N₂ - N₁ : ℕ) : ℝ)
    have hM12 : M₁ ≤ M₂ := geoGrid_mono hΔ0.le (Nat.le_succ b)
    have hLm_le : L_m ≤ 2 * Δ * (M₁ : ℝ) := by
      have hcast : L_m = (M₂ : ℝ) - (M₁ : ℝ) := Nat.cast_sub hM12
      rw [hcast]
      have hN724 : (8 : ℝ) ≤ (N : ℝ) ^ ((7 : ℝ) / 24) := by
        have h4096 : (8 : ℝ) ^ ((24 : ℝ) / 7) ≤ (N : ℝ) := by
          have h1 : (8 : ℝ) ^ ((24 : ℝ) / 7) ≤ (8 : ℝ) ^ (4 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          have h2 : (8 : ℝ) ^ (4 : ℝ) = 4096 := by norm_num
          have h3 : (4096 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
          linarith
        calc (8 : ℝ) = ((8 : ℝ) ^ ((24 : ℝ) / 7)) ^ ((7 : ℝ) / 24) := by
              rw [← Real.rpow_mul (by norm_num)]; norm_num
          _ ≤ (N : ℝ) ^ ((7 : ℝ) / 24) := Real.rpow_le_rpow (by positivity) h4096 (by norm_num)
      have hΔM1 : 2 ≤ Δ * (M₁ : ℝ) := by
        calc (2 : ℝ) = (8 : ℝ) / 4 := by norm_num
          _ ≤ (N : ℝ) ^ ((7 : ℝ) / 24) / 4 := by linarith
          _ = (N : ℝ) ^ (-(1 : ℝ) / 24) * ((N : ℝ) ^ ((1 : ℝ) / 3) / 4) := by
              rw [← mul_div_assoc, ← Real.rpow_add hN_pos]; norm_num
          _ ≤ Δ * (M₁ : ℝ) := mul_le_mul hΔ_lo hM1_ge (by positivity) hΔ0.le
      nlinarith
    have hLm_le_2M1 : L_m ≤ 2 * (M₁ : ℝ) := by nlinarith
    have hLn_le : L_n ≤ (N : ℝ) / (M₁ : ℝ) := by
      have h1 : N₂ - N₁ ≤ N₂ := Nat.sub_le N₂ N₁
      have h2 : (N₂ : ℝ) ≤ ((N - 1 : ℕ) : ℝ) / (M₂ : ℝ) := Nat.cast_div_le
      have h3 : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N 1
      have hM1_le_M2 : (M₁ : ℝ) ≤ (M₂ : ℝ) := by exact_mod_cast hM12
      calc L_n ≤ (N₂ : ℝ) := by dsimp only [L_n]; exact_mod_cast h1
        _ ≤ ((N - 1 : ℕ) : ℝ) / (M₂ : ℝ) := h2
        _ ≤ (N : ℝ) / (M₁ : ℝ) := div_le_div₀ hN_pos.le h3 hM1_pos hM1_le_M2
    -- Apply `bilinear_multiplicative_large_sieve`
    have hLS := Stage11BombieriVinogradov.bilinear_multiplicative_large_sieve (2 * D) M₁ M₂ N₁ N₂ coefA coefB
    have hA2 : ∑ m ∈ Finset.Ioc M₁ M₂, ‖coefA m‖ ^ 2 ≤ L_m := by
      calc ∑ m ∈ Finset.Ioc M₁ M₂, ‖coefA m‖ ^ 2
          ≤ ∑ _m ∈ Finset.Ioc M₁ M₂, (1 : ℝ) := by
            refine Finset.sum_le_sum fun m _ => ?_
            dsimp only [coefA]; split_ifs <;> norm_num
        _ = L_m := by rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
    have hB2 : ∑ n ∈ Finset.Ioc N₁ N₂, ‖coefB n‖ ^ 2 ≤ L_n := by
      calc ∑ n ∈ Finset.Ioc N₁ N₂, ‖coefB n‖ ^ 2
          ≤ ∑ _n ∈ Finset.Ioc N₁ N₂, (1 : ℝ) := by
            refine Finset.sum_le_sum fun n _ => ?_
            dsimp only [coefB]; split_ifs <;> norm_num
        _ = L_n := by rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
    have hLm_nn : 0 ≤ L_m := Nat.cast_nonneg _
    have hLn_nn : 0 ≤ L_n := Nat.cast_nonneg _
    have h3Q2 : 3 * ((2 * D : ℕ) : ℝ) ^ 2 ≤ (4 * (D : ℝ)) ^ 2 := by
      push_cast; nlinarith
    have hfacM : Real.sqrt (L_m + 3 * ((2 * D : ℕ) : ℝ) ^ 2) ≤ Real.sqrt L_m + 4 * (D : ℝ) := by
      calc Real.sqrt (L_m + 3 * ((2 * D : ℕ) : ℝ) ^ 2)
          ≤ Real.sqrt (L_m + (4 * (D : ℝ)) ^ 2) := Real.sqrt_le_sqrt (by linarith)
        _ ≤ Real.sqrt L_m + Real.sqrt ((4 * (D : ℝ)) ^ 2) :=
            sqrt_add_le_sqrt_add_sqrt hLm_nn (by positivity)
        _ = Real.sqrt L_m + 4 * (D : ℝ) := by rw [Real.sqrt_sq (by positivity)]
    have hfacN : Real.sqrt (L_n + 3 * ((2 * D : ℕ) : ℝ) ^ 2) ≤ Real.sqrt L_n + 4 * (D : ℝ) := by
      calc Real.sqrt (L_n + 3 * ((2 * D : ℕ) : ℝ) ^ 2)
          ≤ Real.sqrt (L_n + (4 * (D : ℝ)) ^ 2) := Real.sqrt_le_sqrt (by linarith)
        _ ≤ Real.sqrt L_n + Real.sqrt ((4 * (D : ℝ)) ^ 2) :=
            sqrt_add_le_sqrt_add_sqrt hLn_nn (by positivity)
        _ = Real.sqrt L_n + 4 * (D : ℝ) := by rw [Real.sqrt_sq (by positivity)]
    have hcomb :
        Real.sqrt (L_m + 3 * ((2 * D : ℕ) : ℝ) ^ 2) *
          Real.sqrt (L_n + 3 * ((2 * D : ℕ) : ℝ) ^ 2) *
          Real.sqrt (∑ m ∈ Finset.Ioc M₁ M₂, ‖coefA m‖ ^ 2) *
          Real.sqrt (∑ n ∈ Finset.Ioc N₁ N₂, ‖coefB n‖ ^ 2) ≤
        L_m * L_n + 4 * (D : ℝ) * (L_n * Real.sqrt L_m) +
          4 * (D : ℝ) * (L_m * Real.sqrt L_n) +
          16 * (D : ℝ) ^ 2 * (Real.sqrt L_m * Real.sqrt L_n) := by
      have h1 :
          Real.sqrt (L_m + 3 * ((2 * D : ℕ) : ℝ) ^ 2) *
            Real.sqrt (L_n + 3 * ((2 * D : ℕ) : ℝ) ^ 2) *
            Real.sqrt (∑ m ∈ Finset.Ioc M₁ M₂, ‖coefA m‖ ^ 2) *
            Real.sqrt (∑ n ∈ Finset.Ioc N₁ N₂, ‖coefB n‖ ^ 2) ≤
          (Real.sqrt L_m + 4 * (D : ℝ)) * (Real.sqrt L_n + 4 * (D : ℝ)) *
            Real.sqrt L_m * Real.sqrt L_n := by
        have ha := Real.sqrt_le_sqrt hA2
        have hb := Real.sqrt_le_sqrt hB2
        gcongr
      refine h1.trans_eq ?_
      have hsqM : Real.sqrt L_m * Real.sqrt L_m = L_m := Real.mul_self_sqrt hLm_nn
      have hsqN : Real.sqrt L_n * Real.sqrt L_n = L_n := Real.mul_self_sqrt hLn_nn
      calc (Real.sqrt L_m + 4 * (D : ℝ)) * (Real.sqrt L_n + 4 * (D : ℝ)) *
              Real.sqrt L_m * Real.sqrt L_n
          = (Real.sqrt L_m * Real.sqrt L_m) * (Real.sqrt L_n * Real.sqrt L_n) +
            4 * (D : ℝ) * ((Real.sqrt L_n * Real.sqrt L_n) * Real.sqrt L_m) +
            4 * (D : ℝ) * ((Real.sqrt L_m * Real.sqrt L_m) * Real.sqrt L_n) +
            16 * (D : ℝ) ^ 2 * (Real.sqrt L_m * Real.sqrt L_n) := by ring
        _ = _ := by rw [hsqM, hsqN]
    -- Bound each of the 4 terms
    have ht1 : L_m * L_n ≤ 2 * Δ * (N : ℝ) := by
      calc L_m * L_n ≤ (2 * Δ * (M₁ : ℝ)) * ((N : ℝ) / (M₁ : ℝ)) :=
            mul_le_mul hLm_le hLn_le hLn_nn (by positivity)
        _ = 2 * Δ * (N : ℝ) := by field_simp [hM1_pos.ne']
    have ht2 : L_n * Real.sqrt L_m ≤ 3 * (N : ℝ) ^ ((5 : ℝ) / 6) := by
      have hsqM : Real.sqrt L_m ≤ 2 * Real.sqrt (M₁ : ℝ) := by
        calc Real.sqrt L_m ≤ Real.sqrt (4 * (M₁ : ℝ)) := Real.sqrt_le_sqrt (by linarith)
          _ = Real.sqrt 4 * Real.sqrt (M₁ : ℝ) := Real.sqrt_mul (by norm_num) _
          _ = 2 * Real.sqrt (M₁ : ℝ) := by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have hsq_M1_ge : (N : ℝ) ^ ((1 : ℝ) / 6) / 2 ≤ Real.sqrt (M₁ : ℝ) := by
        have h1 : Real.sqrt ((N : ℝ) ^ ((1 : ℝ) / 3) / 4) ≤ Real.sqrt (M₁ : ℝ) :=
          Real.sqrt_le_sqrt hM1_ge
        have h2 : Real.sqrt ((N : ℝ) ^ ((1 : ℝ) / 3) / 4) = (N : ℝ) ^ ((1 : ℝ) / 6) / 2 := by
          rw [Real.sqrt_div (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_mul hN_pos.le,
            show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
          norm_num
        rwa [h2] at h1
      have hdiv : (N : ℝ) / Real.sqrt (M₁ : ℝ) ≤ 2 * (N : ℝ) ^ ((5 : ℝ) / 6) := by
        have hN56 : (N : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 6) = (N : ℝ) ^ ((5 : ℝ) / 6) := by
          calc (N : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 6)
              = (N : ℝ) ^ (1 : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 6) := by rw [Real.rpow_one]
            _ = (N : ℝ) ^ ((1 : ℝ) - (1 : ℝ) / 6) := (Real.rpow_sub hN_pos _ _).symm
            _ = (N : ℝ) ^ ((5 : ℝ) / 6) := by norm_num
        calc (N : ℝ) / Real.sqrt (M₁ : ℝ)
            ≤ (N : ℝ) / ((N : ℝ) ^ ((1 : ℝ) / 6) / 2) :=
              div_le_div_of_nonneg_left hN_pos.le (by positivity) hsq_M1_ge
          _ = 2 * ((N : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 6)) := by ring
          _ = 2 * (N : ℝ) ^ ((5 : ℝ) / 6) := by rw [hN56]
      have hcancel : ((N : ℝ) / (M₁ : ℝ)) * Real.sqrt (M₁ : ℝ) = (N : ℝ) / Real.sqrt (M₁ : ℝ) := by
        have hsq_pos : 0 < Real.sqrt (M₁ : ℝ) := Real.sqrt_pos.mpr hM1_pos
        rw [div_mul_eq_mul_div, div_eq_div_iff hM1_pos.ne' hsq_pos.ne']
        linear_combination (N : ℝ) * Real.mul_self_sqrt hM1_pos.le
      -- Tighten `hsqM` using `Real.sqrt 2 ≤ 3 / 2` so `ht2 ≤ 3 * N^{5/6}`!
      have hsq2 : Real.sqrt 2 ≤ 3 / 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
      have hsqM' : Real.sqrt L_m ≤ (3 / 2) * Real.sqrt (M₁ : ℝ) := by
        calc Real.sqrt L_m ≤ Real.sqrt (2 * (M₁ : ℝ)) := Real.sqrt_le_sqrt hLm_le_2M1
          _ = Real.sqrt 2 * Real.sqrt (M₁ : ℝ) := Real.sqrt_mul (by norm_num) _
          _ ≤ (3 / 2) * Real.sqrt (M₁ : ℝ) := mul_le_mul_of_nonneg_right hsq2 (Real.sqrt_nonneg _)
      calc L_n * Real.sqrt L_m
          ≤ ((N : ℝ) / (M₁ : ℝ)) * ((3 / 2) * Real.sqrt (M₁ : ℝ)) :=
            mul_le_mul hLn_le hsqM' (Real.sqrt_nonneg _) (by positivity)
        _ = (3 / 2) * (((N : ℝ) / (M₁ : ℝ)) * Real.sqrt (M₁ : ℝ)) := by ring
        _ = (3 / 2) * ((N : ℝ) / Real.sqrt (M₁ : ℝ)) := by rw [hcancel]
        _ ≤ (3 / 2) * (2 * (N : ℝ) ^ ((5 : ℝ) / 6)) := mul_le_mul_of_nonneg_left hdiv (by norm_num)
        _ = 3 * (N : ℝ) ^ ((5 : ℝ) / 6) := by ring
    have ht3 : L_m * Real.sqrt L_n ≤ 2 * (N : ℝ) ^ ((5 : ℝ) / 6) := by
      have hsqN : Real.sqrt L_n ≤ Real.sqrt (N : ℝ) / Real.sqrt (M₁ : ℝ) := by
        calc Real.sqrt L_n ≤ Real.sqrt ((N : ℝ) / (M₁ : ℝ)) := Real.sqrt_le_sqrt hLn_le
          _ = Real.sqrt (N : ℝ) / Real.sqrt (M₁ : ℝ) := Real.sqrt_div hN_pos.le _
      have hsqM1_le : Real.sqrt (M₁ : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := by
        rw [Real.sqrt_eq_rpow]
        calc (M₁ : ℝ) ^ ((1 : ℝ) / 2) ≤ ((N : ℝ) ^ ((2 : ℝ) / 3)) ^ ((1 : ℝ) / 2) :=
              Real.rpow_le_rpow hM1_pos.le hM1_le (by norm_num)
          _ = (N : ℝ) ^ ((1 : ℝ) / 3) := by rw [← Real.rpow_mul hN_pos.le]; norm_num
      have hcancel : (M₁ : ℝ) * (Real.sqrt (N : ℝ) / Real.sqrt (M₁ : ℝ)) =
          Real.sqrt (M₁ : ℝ) * Real.sqrt (N : ℝ) := by
        have hsq_pos : 0 < Real.sqrt (M₁ : ℝ) := Real.sqrt_pos.mpr hM1_pos
        rw [mul_div_assoc', div_eq_iff hsq_pos.ne']
        linear_combination -Real.sqrt (N : ℝ) * Real.mul_self_sqrt hM1_pos.le
      have hsqN_rpow : Real.sqrt (N : ℝ) = (N : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow (N : ℝ)
      calc L_m * Real.sqrt L_n
          ≤ (2 * (M₁ : ℝ)) * (Real.sqrt (N : ℝ) / Real.sqrt (M₁ : ℝ)) :=
            mul_le_mul hLm_le_2M1 hsqN (Real.sqrt_nonneg _) (by positivity)
        _ = 2 * ((M₁ : ℝ) * (Real.sqrt (N : ℝ) / Real.sqrt (M₁ : ℝ))) := by ring
        _ = 2 * (Real.sqrt (M₁ : ℝ) * Real.sqrt (N : ℝ)) := by rw [hcancel]
        _ ≤ 2 * ((N : ℝ) ^ ((1 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 2)) := by
            rw [hsqN_rpow]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hsqM1_le (by positivity)) (by norm_num)
        _ = 2 * (N : ℝ) ^ ((5 : ℝ) / 6) := by rw [← Real.rpow_add hN_pos]; norm_num
    have ht4 : Real.sqrt L_m * Real.sqrt L_n ≤ 2 * Real.sqrt (N : ℝ) := by
      rw [← Real.sqrt_mul hLm_nn]
      calc Real.sqrt (L_m * L_n) ≤ Real.sqrt (4 * (N : ℝ)) := Real.sqrt_le_sqrt (by nlinarith)
        _ = Real.sqrt 4 * Real.sqrt (N : ℝ) := Real.sqrt_mul (by norm_num) _
        _ = 2 * Real.sqrt (N : ℝ) := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have htotal :
        L_m * L_n + 4 * (D : ℝ) * (L_n * Real.sqrt L_m) +
          4 * (D : ℝ) * (L_m * Real.sqrt L_n) +
          16 * (D : ℝ) ^ 2 * (Real.sqrt L_m * Real.sqrt L_n) ≤
        (D : ℝ) * (2 * Δ * (N : ℝ) / (D : ℝ) + 24 * (N : ℝ) ^ ((5 : ℝ) / 6) +
          32 * (D : ℝ) * Real.sqrt (N : ℝ)) := by
      have hD_cancel : (D : ℝ) * (2 * Δ * (N : ℝ) / (D : ℝ)) = 2 * Δ * (N : ℝ) :=
        mul_div_cancel₀ _ hD_pos.ne'
      have h1 : 4 * (D : ℝ) * (L_n * Real.sqrt L_m) ≤ 12 * (D : ℝ) * (N : ℝ) ^ ((5 : ℝ) / 6) := by
        have := mul_le_mul_of_nonneg_left ht2 (show 0 ≤ 4 * (D : ℝ) by positivity); linarith
      have h2 : 4 * (D : ℝ) * (L_m * Real.sqrt L_n) ≤ 8 * (D : ℝ) * (N : ℝ) ^ ((5 : ℝ) / 6) := by
        have := mul_le_mul_of_nonneg_left ht3 (show 0 ≤ 4 * (D : ℝ) by positivity); linarith
      have h3 : 16 * (D : ℝ) ^ 2 * (Real.sqrt L_m * Real.sqrt L_n) ≤
          32 * (D : ℝ) ^ 2 * Real.sqrt (N : ℝ) := by
        have := mul_le_mul_of_nonneg_left ht4 (show 0 ≤ 16 * (D : ℝ) ^ 2 by positivity); linarith
      have hR : (D : ℝ) * (2 * Δ * (N : ℝ) / (D : ℝ) + 24 * (N : ℝ) ^ ((5 : ℝ) / 6) +
          32 * (D : ℝ) * Real.sqrt (N : ℝ)) =
          (D : ℝ) * (2 * Δ * (N : ℝ) / (D : ℝ)) + 24 * (D : ℝ) * (N : ℝ) ^ ((5 : ℝ) / 6) +
          32 * (D : ℝ) ^ 2 * Real.sqrt (N : ℝ) := by ring
      rw [hR, hD_cancel]
      have hnn56 : 0 ≤ (D : ℝ) * (N : ℝ) ^ ((5 : ℝ) / 6) := by positivity
      linarith
    have hmul := mul_le_mul_of_nonneg_left ((hLS.trans hcomb).trans htotal) (show 0 ≤ 1 / (D : ℝ) by positivity)
    refine hmul.trans_eq ?_
    field_simp [hD_pos.ne']

open Classical in
/-- **Master Unconditional Dyadic Large-Conductor Bound for `chenMCharSum`**:
for ALL `1 ≤ D`, `N ≥ 4096`, `(D : ℝ) ≤ √N`, `0 < Δ < 1`, `(N : ℝ) ^ (-1 / 24) ≤ Δ`:
`∑_{D < r ≤ 2 D} φ(r)⁻¹ ∑*_{ψ mod r} ‖chenMCharSum ψ N‖ ≤
  (⌊2 log N / Δ⌋₊ + 1)² * (2 Δ N / D + 24 N^{5/6} + 32 D √N) + 20 N √Δ √(1 + log N)`. -/
private lemma dyadic_prim_chenMCharSum_bound {D N : ℕ} {Δ : ℝ}
    (hD : 1 ≤ D) (hN : 4096 ≤ N) (hD_sqN : (D : ℝ) ≤ Real.sqrt (N : ℝ))
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (hΔ_lo : (N : ℝ) ^ (-(1 : ℝ) / 24) ≤ Δ) :
    ∑ k ∈ Finset.Ico D (2 * D),
        (1 / (Nat.totient (k + 1) : ℝ)) *
          ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
            ‖chenMCharSum ψ N‖ ≤
      ((⌊2 * Real.log (N : ℝ) / Δ⌋₊ + 1 : ℕ) : ℝ) ^ 2 *
          (2 * Δ * (N : ℝ) / (D : ℝ) + 24 * (N : ℝ) ^ ((5 : ℝ) / 6) +
            32 * (D : ℝ) * Real.sqrt (N : ℝ)) +
        20 * (N : ℝ) * Real.sqrt Δ * Real.sqrt (1 + Real.log (N : ℝ)) := by
  set K := ⌊2 * Real.log (N : ℝ) / Δ⌋₊ + 1
  have hD_pos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD
  -- Step 1: `1 / φ(k+1) ≤ (1 / D) * ((k+1) / φ(k+1))` and extend `Ico D (2D) ⊆ range (2D)`
  have hstep1 :
      ∑ k ∈ Finset.Ico D (2 * D),
          (1 / (Nat.totient (k + 1) : ℝ)) *
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
              ‖chenMCharSum ψ N‖ ≤
        (1 / (D : ℝ)) *
          ∑ k ∈ Finset.range (2 * D),
            (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                ‖chenMCharSum ψ N‖ := by
    have hsub : Finset.Ico D (2 * D) ⊆ Finset.range (2 * D) := by
      intro k hk; exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
    have h1 :
        ∑ k ∈ Finset.Ico D (2 * D),
            (1 / (Nat.totient (k + 1) : ℝ)) *
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                ‖chenMCharSum ψ N‖ ≤
          (1 / (D : ℝ)) *
            ∑ k ∈ Finset.Ico D (2 * D),
              (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
                ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                  ‖chenMCharSum ψ N‖ := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      have hkD : (D : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
        have := (Finset.mem_Ico.mp hk).1; exact_mod_cast (by omega : D ≤ k + 1)
      have hfac : 1 / (Nat.totient (k + 1) : ℝ) ≤
          (1 / (D : ℝ)) * (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) := by
        rw [show (1 / (D : ℝ)) * (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) =
          (((k + 1 : ℕ) : ℝ) / (D : ℝ)) * (1 / (Nat.totient (k + 1) : ℝ)) by ring]
        exact le_mul_of_one_le_left (by positivity) ((one_le_div hD_pos).mpr hkD)
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hfac (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
      mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  -- Step 2: Split `‖chenMCharSum ψ N‖ ≤ ∑_{a, b < K} ‖Rect_{a,b}(ψ)‖ + ‖Bdy(ψ)‖`
  let rectTerm : ℕ → ℕ → (k : ℕ) → DirichletCharacter ℂ (k + 1) → ℝ := fun a b k ψ =>
    ‖(∑ m ∈ Finset.Ioc (geoGrid Δ b) (geoGrid Δ (b + 1)),
        (if ∃ p ∈ chenMPairs N, p.2 ∈ Finset.Ioc (geoGrid Δ a) (geoGrid Δ (a + 1)) ∧ p.1 * p.2 = m
         then (1 : ℂ) else 0) * ψ (m : ZMod (k + 1))) *
     (∑ n ∈ Finset.Ioc (geoGrid Δ (a + 1)) ((N - 1) / geoGrid Δ (b + 1)),
        (if n.Prime ∧ ¬ n ∣ N then (1 : ℂ) else 0) * ψ (n : ZMod (k + 1)))‖
  have hpt : ∀ (k : ℕ) (ψ : DirichletCharacter ℂ (k + 1)),
      ‖chenMCharSum ψ N‖ ≤
        (∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K, rectTerm a b k ψ) +
        ‖∑ t ∈ chenMBdy N Δ K, ψ ((t.1 * t.2.1 * t.2.2 : ℕ) : ZMod (k + 1))‖ := fun k ψ => by
    rw [chenMCharSum_eq_rect_add_bdy ψ (by omega) hΔ0 hΔ1]
    refine (norm_add_le _ _).trans ?_
    gcongr
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
  have hsplit :
      (1 / (D : ℝ)) *
        ∑ k ∈ Finset.range (2 * D),
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
              ‖chenMCharSum ψ N‖ ≤
      (∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K,
        (1 / (D : ℝ)) *
          ∑ k ∈ Finset.range (2 * D),
            (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                rectTerm a b k ψ) +
      (1 / (D : ℝ)) *
        ∑ k ∈ Finset.range (2 * D),
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
              ‖∑ t ∈ chenMBdy N Δ K, ψ ((t.1 * t.2.1 * t.2.2 : ℕ) : ZMod (k + 1))‖ := by
    have h1 :
        (1 / (D : ℝ)) *
          ∑ k ∈ Finset.range (2 * D),
            (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                ‖chenMCharSum ψ N‖ ≤
        (1 / (D : ℝ)) *
          ∑ k ∈ Finset.range (2 * D),
            (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                ((∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K, rectTerm a b k ψ) +
                 ‖∑ t ∈ chenMBdy N Δ K, ψ ((t.1 * t.2.1 * t.2.2 : ℕ) : ZMod (k + 1))‖) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun ψ _ => hpt k ψ) (by positivity))
        (by positivity)
    refine h1.trans_eq ?_
    have hsplit_sum :
        ∑ k ∈ Finset.range (2 * D),
            (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                ((∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K, rectTerm a b k ψ) +
                 ‖∑ t ∈ chenMBdy N Δ K, ψ ((t.1 * t.2.1 * t.2.2 : ℕ) : ZMod (k + 1))‖) =
          (∑ k ∈ Finset.range (2 * D),
            (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K, rectTerm a b k ψ) +
          (∑ k ∈ Finset.range (2 * D),
            (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                ‖∑ t ∈ chenMBdy N Δ K, ψ ((t.1 * t.2.1 * t.2.2 : ℕ) : ZMod (k + 1))‖) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => by rw [← mul_add, ← Finset.sum_add_distrib]
    rw [hsplit_sum, mul_add]
    congr 1
    -- Commute `(k, ψ)` with `(a, b)`
    have hcomm :
        ∑ k ∈ Finset.range (2 * D),
            (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K, rectTerm a b k ψ =
          ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K,
            ∑ k ∈ Finset.range (2 * D),
              (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
                ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                  rectTerm a b k ψ := by
      have h1 : ∀ k ∈ Finset.range (2 * D),
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
              ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K, rectTerm a b k ψ =
          ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K,
            (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                rectTerm a b k ψ := fun k _ => by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => by rw [Finset.sum_comm, Finset.mul_sum]
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    rw [hcomm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
  have hrect_all :
      ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K,
          (1 / (D : ℝ)) *
            ∑ k ∈ Finset.range (2 * D),
              (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
                ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                  rectTerm a b k ψ ≤
        (K : ℝ) ^ 2 *
          (2 * Δ * (N : ℝ) / (D : ℝ) + 24 * (N : ℝ) ^ ((5 : ℝ) / 6) +
            32 * (D : ℝ) * Real.sqrt (N : ℝ)) := by
    calc _ ≤ ∑ _a ∈ Finset.range K, ∑ _b ∈ Finset.range K,
              (2 * Δ * (N : ℝ) / (D : ℝ) + 24 * (N : ℝ) ^ ((5 : ℝ) / 6) +
                32 * (D : ℝ) * Real.sqrt (N : ℝ)) :=
            Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
              sum_chenMRect_box_large_sieve_le hD hN hΔ0 hΔ1 hΔ_lo
      _ = (K : ℝ) ^ 2 *
            (2 * Δ * (N : ℝ) / (D : ℝ) + 24 * (N : ℝ) ^ ((5 : ℝ) / 6) +
              32 * (D : ℝ) * Real.sqrt (N : ℝ)) := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hbdy_all := sum_chenMBdy_large_sieve_le hD (by omega) hD_sqN hΔ0 hΔ1 hΔ_lo
  exact (hstep1.trans hsplit).trans (add_le_add hrect_all hbdy_all)

/-! ## Section 5: Main Headline Theorems (`chen_bilinear_bombieri_vinogradov` & `chenMProd`) -/

/-- Helper: for any `M > 0`, `∃ X ≥ 4, ∀ x ≥ X, (Real.log x) ^ M ≤ x ^ (1 / 24 : ℝ)`. -/
private lemma eventually_log_rpow_le_rpow_24th (M : ℝ) (hM : 0 < M) :
    ∃ X : ℝ, 4 ≤ X ∧ ∀ x : ℝ, X ≤ x → (Real.log x) ^ M ≤ x ^ ((1 : ℝ) / 24) := by
  have hα : (0 : ℝ) < 1 / (24 * M) := by positivity
  have hev := ((isLittleO_log_rpow_atTop hα).tendsto_div_nhds_zero).eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨X₁, hX₁⟩ := hev
  refine ⟨max 4 X₁, le_max_left _ _, fun x hx => ?_⟩
  have hx4 : 4 ≤ x := (le_max_left _ _).trans hx
  have hx1 : X₁ ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hLx_nn : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlt : Real.log x / x ^ (1 / (24 * M)) < 1 := hX₁ x hx1
  have hle1 : Real.log x ≤ x ^ (1 / (24 * M)) :=
    ((div_lt_one (Real.rpow_pos_of_pos hx0 _)).mp hlt).le
  have hpow := Real.rpow_le_rpow hLx_nn hle1 hM.le
  rw [← Real.rpow_mul hx0.le] at hpow
  have hexp : 1 / (24 * M) * M = 1 / 24 := by field_simp [hM.ne']
  rwa [hexp] at hpow

/-- Helper: for any `c > 0` and `P > 0`,
`∃ X ≥ 4, ∀ x ≥ X, (Real.log x) ^ P * Real.exp (-c * Real.sqrt (Real.log x)) ≤ 1`. -/
private lemma eventually_log_rpow_mul_exp_neg_sqrt_le_one {c P : ℝ} (hc : 0 < c) (hP : 0 < P) :
    ∃ X : ℝ, 4 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      (Real.log x) ^ P * Real.exp (-c * Real.sqrt (Real.log x)) ≤ 1 := by
  have hratio : Tendsto (fun u : ℝ => Real.log u / Real.sqrt u) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    exact h.congr fun u => by rw [Real.sqrt_eq_rpow]
  have hcomp : Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.sqrt (Real.log x)) atTop (𝓝 0) :=
    hratio.comp Real.tendsto_log_atTop
  have hev := hcomp.eventually (Iio_mem_nhds (div_pos hc hP))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨X₁, hX₁⟩ := hev
  refine ⟨max 4 X₁, le_max_left _ _, fun x hx => ?_⟩
  have hx4 : 4 ≤ x := (le_max_left _ _).trans hx
  have hx1 : X₁ ≤ x := (le_max_right _ _).trans hx
  have hLx_gt1 : 1 < Real.log x := by
    have : Real.exp 1 < x := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  have hLx_pos : 0 < Real.log x := zero_lt_one.trans hLx_gt1
  have hsq_pos : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hLx_pos
  have hlt : Real.log (Real.log x) / Real.sqrt (Real.log x) < c / P := hX₁ x hx1
  have hmul : P * Real.log (Real.log x) < c * Real.sqrt (Real.log x) := by
    have h1 := (div_lt_iff₀ hsq_pos).mp hlt
    have h2 := mul_lt_mul_of_pos_left h1 hP
    have h3 : P * (c / P * Real.sqrt (Real.log x)) = c * Real.sqrt (Real.log x) := by
      field_simp [hP.ne']
    linarith
  rw [Real.rpow_def_of_pos hLx_pos, ← Real.exp_add]
  exact Real.exp_le_one_iff.mpr (by linarith)

private lemma sum_biUnion_le_local {α β : Type*} [DecidableEq β] (s : Finset α)
    (t : α → Finset β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    ∑ b ∈ s.biUnion t, f b ≤ ∑ a ∈ s, ∑ b ∈ t a, f b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hunion :
        ∑ b ∈ t a ∪ s.biUnion t, f b ≤ ∑ b ∈ t a, f b + ∑ b ∈ s.biUnion t, f b := by
      rw [← Finset.sum_union_inter]
      linarith [Finset.sum_nonneg (s := t a ∩ s.biUnion t) (f := f) fun b _ => hf b]
    linarith

open Classical in
/-- **CHEN'S SWITCHED BILINEAR BOMBIERI–VINOGRADOV THEOREM (UNCONDITIONAL, `ϑ = 1/2`)**:
for EVERY `A : ℝ`, there exist `B > 0` and `C > 0` such that for ALL `N ≥ 4`:
`∑_{d ≤ √N / (log N)^B, Squarefree d, Coprime d N, d odd} |#{(q₁, q₂, q₃) ∈ chenM N : d ∣ (N - q₁ q₂ q₃)} - |chenM N| / φ(d)| ≤ C * N / (log N)^A`. -/
theorem chen_bilinear_bombieri_vinogradov (A : ℝ) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧
      ∀ N : ℕ, 4 ≤ N →
        ∑ d ∈ (Finset.Icc 1 ⌊Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B⌋₊).filter
            (fun d => Squarefree d ∧ Nat.Coprime d N ∧ ∀ p ∈ d.primeFactors, p ≠ 2),
          |(((chenM N).filter (fun t => d ∣ (N - t.1 * t.2.1 * t.2.2))).card : ℝ) -
            ((chenM N).card : ℝ) / (d.totient : ℝ)| ≤
          C * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  set A' : ℝ := max A 1 with hA'_def
  have hA'1 : 1 ≤ A' := le_max_right A 1
  have hA_le_A' : A ≤ A' := le_max_left A 1
  set E : ℝ := 2 * A' + 20 with hE_def
  set B₁ : ℝ := E + A' + 12 with hB1_def
  set B : ℝ := 2 * E + A' + 12 with hB_def
  set M_exp : ℝ := 10 * A' + 150 with hM_def
  have hE_pos : 0 < E := by dsimp only [E]; linarith
  have hB1_pos : 0 < B₁ := by dsimp only [B₁, E]; linarith
  have hB_pos : 0 < B := by dsimp only [B, E]; linarith
  -- Obtain unconditional zero-exception Siegel–Walfisz bound for prime character sums
  obtain ⟨c_sw, hc_sw, hsw_all⟩ := siegel_walfisz_primeCharSum
  obtain ⟨C_sw, hC_sw, hsw⟩ := hsw_all (B₁ + 1) (by linarith)
  -- Obtain asymptotic thresholds
  obtain ⟨X_pow, hX_pow4, hlog_pow⟩ :=
    eventually_log_rpow_le_rpow_24th M_exp (by dsimp only [M_exp]; linarith)
  obtain ⟨X_sw, hX_sw4, hlog_sw⟩ :=
    eventually_log_rpow_mul_exp_neg_sqrt_le_one (show 0 < c_sw / 2 by positivity)
      (by dsimp only [B₁, E]; linarith : 0 < 2 * B₁ + A' + 5)
  set X_log : ℝ := Real.exp (4 * (4 : ℝ) ^ B₁)
  set X₀ : ℝ := max (max 4096 X_log) (max X_pow X_sw) with hX₀_def
  have hX₀_ge4096 : 4096 ≤ X₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hX₀_ge4 : 4 ≤ X₀ := by linarith
  have hlogX₀_gt1 : 1 < Real.log X₀ := by
    have : Real.exp 1 < X₀ := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  -- Large-`N` and small-`N` constants
  set C_large : ℝ := 100 * C_sw + 100000 with hClarge_def
  have hClarge_pos : 0 < C_large := by positivity
  set C_small : ℝ := (2 * X₀ ^ 2 + 1) * (Real.log X₀) ^ A' / 4 with hCsmall_def
  have hCsmall_pos : 0 < C_small := by
    have : 0 < (Real.log X₀) ^ A' := Real.rpow_pos_of_pos (by linarith) A'
    positivity
  set C : ℝ := max C_large C_small with hC_def
  refine ⟨B, C, hB_pos, lt_of_lt_of_le hClarge_pos (le_max_left _ _), fun N hN4 => ?_⟩
  have hNR4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN4
  have hN_pos : (0 : ℝ) < (N : ℝ) := by linarith
  have hLN_gt1 : 1 < Real.log (N : ℝ) := by
    have : Real.exp 1 < (N : ℝ) := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  have hLN_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hLN_gt1
  -- Monotonicity in exponent: `C * N / (log N)^A' ≤ C * N / (log N)^A`
  have hA'_to_A : C * (N : ℝ) / (Real.log (N : ℝ)) ^ A' ≤ C * (N : ℝ) / (Real.log (N : ℝ)) ^ A :=
    div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hLN_pos A)
      (Real.rpow_le_rpow_of_exponent_le hLN_gt1.le hA_le_A')
  refine le_trans ?_ hA'_to_A
  set Q : ℕ := ⌊Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B⌋₊ with hQ_def
  -- Drop the `p ≠ 2` filter cleanly (nonneg summands!)
  have hdrop_odd :
      ∑ d ∈ (Finset.Icc 1 Q).filter
          (fun d => Squarefree d ∧ Nat.Coprime d N ∧ ∀ p ∈ d.primeFactors, p ≠ 2),
        |(((chenM N).filter (fun t => d ∣ (N - t.1 * t.2.1 * t.2.2))).card : ℝ) -
          ((chenM N).card : ℝ) / (d.totient : ℝ)| ≤
      ∑ d ∈ (Finset.Icc 1 Q).filter (fun d => Squarefree d ∧ Nat.Coprime d N),
        |(((chenM N).filter (fun t => d ∣ (N - t.1 * t.2.1 * t.2.2))).card : ℝ) -
          ((chenM N).card : ℝ) / (d.totient : ℝ)| := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => abs_nonneg _
    intro d hd
    have hmem := Finset.mem_filter.mp hd
    exact Finset.mem_filter.mpr ⟨hmem.1, hmem.2.1, hmem.2.2.1⟩
  refine hdrop_odd.trans ?_
  by_cases hQ0 : Q = 0
  · rw [hQ0]
    have : Finset.Icc 1 0 = ∅ := Finset.Icc_eq_empty (by omega)
    rw [this, Finset.filter_empty, Finset.sum_empty]
    positivity
  · have hQ1 : 1 ≤ Q := Nat.pos_of_ne_zero hQ0
    by_cases hN_big : X₀ ≤ (N : ℝ)
    · -- Case 1: Large `N ≥ X₀`
      have hN4096 : 4096 ≤ N := by
        have : (4096 : ℝ) ≤ (N : ℝ) := hX₀_ge4096.trans hN_big
        exact_mod_cast this
      have hlog_big : (4 : ℝ) ^ B₁ ≤ Real.log (N : ℝ) / 4 := by
        have hexp : Real.exp (4 * (4 : ℝ) ^ B₁) ≤ (N : ℝ) :=
          ((le_max_right _ _).trans (le_max_left _ _)).trans hN_big
        have h := Real.log_le_log (Real.exp_pos _) hexp
        rw [Real.log_exp] at h
        linarith
      have hLN_ge2 : 2 ≤ Real.log (N : ℝ) := by
        have h4B1 : (1 : ℝ) ≤ (4 : ℝ) ^ B₁ := Real.one_le_rpow (by norm_num) hB1_pos.le
        linarith
      have hpow_bd : (Real.log (N : ℝ)) ^ M_exp ≤ (N : ℝ) ^ ((1 : ℝ) / 24) :=
        hlog_pow (N : ℝ) (((le_max_left _ _).trans (le_max_right _ _)).trans hN_big)
      have hsw_decay :
          (Real.log (N : ℝ)) ^ (2 * B₁ + A' + 5) *
            Real.exp (-(c_sw / 2) * Real.sqrt (Real.log (N : ℝ))) ≤ 1 :=
        hlog_sw (N : ℝ) (((le_max_right _ _).trans (le_max_right _ _)).trans hN_big)
      have hL_le_N24 : ∀ p : ℝ, 0 ≤ p → p ≤ M_exp → (Real.log (N : ℝ)) ^ p ≤ (N : ℝ) ^ ((1 : ℝ) / 24) :=
        fun p _ hpM => (Real.rpow_le_rpow_of_exponent_le hLN_gt1.le hpM).trans hpow_bd
      have hQR_le : (Q : ℝ) ≤ Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B :=
        Nat.floor_le (by positivity)
      have hQ_le_sqN : (Q : ℝ) ≤ Real.sqrt (N : ℝ) :=
        hQR_le.trans (div_le_self (Real.sqrt_nonneg _) (Real.one_le_rpow hLN_gt1.le hB_pos.le))
      have hQN : Q ≤ N := by
        have h1 : (Q : ℝ) ≤ (N : ℝ) :=
          hQ_le_sqN.trans (Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩)
        exact_mod_cast h1
      -- Start from exact squarefree primitive-character reduction
      have hred := sum_chenM_discrepancy_le_prim_sum (by omega : 256 ≤ N) hQ1 hQN
      -- Bound 1: Coprimality + principal error `16 N^{7/8} (1 + log N) ≤ 32 N / (log N)^A'`
      have hterm_cop :
          16 * (N : ℝ) ^ ((7 : ℝ) / 8) * (1 + Real.log (N : ℝ)) ≤
            32 * (N : ℝ) / (Real.log (N : ℝ)) ^ A' := by
        rw [le_div_iff₀ (Real.rpow_pos_of_pos hLN_pos A')]
        have h1 : (1 + Real.log (N : ℝ)) * (Real.log (N : ℝ)) ^ A' ≤ 2 * (N : ℝ) ^ ((1 : ℝ) / 24) := by
          have hlog_add : 1 + Real.log (N : ℝ) ≤ 2 * Real.log (N : ℝ) := by linarith
          have hpow1 : Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ A' = (Real.log (N : ℝ)) ^ (A' + 1) := by
            calc Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ A'
                = (Real.log (N : ℝ)) ^ A' * (Real.log (N : ℝ)) ^ (1 : ℝ) := by rw [Real.rpow_one, mul_comm]
              _ = (Real.log (N : ℝ)) ^ (A' + 1) := (Real.rpow_add hLN_pos A' 1).symm
          calc (1 + Real.log (N : ℝ)) * (Real.log (N : ℝ)) ^ A'
              ≤ (2 * Real.log (N : ℝ)) * (Real.log (N : ℝ)) ^ A' :=
                mul_le_mul_of_nonneg_right hlog_add (by positivity)
            _ = 2 * (Real.log (N : ℝ)) ^ (A' + 1) := by rw [mul_assoc, hpow1]
            _ ≤ 2 * (N : ℝ) ^ ((1 : ℝ) / 24) :=
                mul_le_mul_of_nonneg_left (hL_le_N24 (A' + 1) (by linarith) (by dsimp only [M_exp]; linarith)) (by norm_num)
        calc 16 * (N : ℝ) ^ ((7 : ℝ) / 8) * (1 + Real.log (N : ℝ)) * (Real.log (N : ℝ)) ^ A'
            = 16 * (N : ℝ) ^ ((7 : ℝ) / 8) * ((1 + Real.log (N : ℝ)) * (Real.log (N : ℝ)) ^ A') := by ring
          _ ≤ 16 * (N : ℝ) ^ ((7 : ℝ) / 8) * (2 * (N : ℝ) ^ ((1 : ℝ) / 24)) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = 32 * (N : ℝ) ^ ((11 : ℝ) / 12) := by
              rw [show 16 * (N : ℝ) ^ ((7 : ℝ) / 8) * (2 * (N : ℝ) ^ ((1 : ℝ) / 24)) =
                32 * ((N : ℝ) ^ ((7 : ℝ) / 8) * (N : ℝ) ^ ((1 : ℝ) / 24)) by ring,
                ← Real.rpow_add hN_pos]; norm_num
          _ ≤ 32 * (N : ℝ) ^ (1 : ℝ) := mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)) (by norm_num)
          _ = 32 * (N : ℝ) := by rw [Real.rpow_one]
      -- Split primitive conductors `k ∈ Ico 2 Q` at `Q₁ = ⌊(log N)^B₁⌋₊`
      set Q₁ : ℕ := ⌊(Real.log (N : ℝ)) ^ B₁⌋₊ with hQ1_def
      have hQ1_ge2 : 2 ≤ Q₁ := by
        have h2B1 : (2 : ℝ) ≤ (Real.log (N : ℝ)) ^ B₁ := by
          calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
            _ ≤ (Real.log (N : ℝ)) ^ (1 : ℝ) := Real.rpow_le_rpow (by norm_num) hLN_ge2 (by norm_num)
            _ ≤ (Real.log (N : ℝ)) ^ B₁ :=
                Real.rpow_le_rpow_of_exponent_le hLN_gt1.le (by dsimp only [B₁, E]; linarith)
        exact Nat.le_floor h2B1
      have hQ1_le_R : (Q₁ : ℝ) ≤ (Real.log (N : ℝ)) ^ B₁ := Nat.floor_le (by positivity)
      have hQ1_ge_half : (Real.log (N : ℝ)) ^ B₁ / 2 ≤ (Q₁ : ℝ) := by
        have hlt := Nat.lt_floor_add_one ((Real.log (N : ℝ)) ^ B₁)
        have h2 : (2 : ℝ) ≤ (Q₁ : ℝ) := by exact_mod_cast hQ1_ge2
        linarith
      have hsplit_prim :
          ∑ k ∈ Finset.Ico 2 Q,
              (1 / (Nat.totient (k + 1) : ℝ)) *
                ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                  ‖chenMCharSum ψ N‖ ≤
            (∑ k ∈ Finset.Ico 2 (min Q₁ Q),
              (1 / (Nat.totient (k + 1) : ℝ)) *
                ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                  ‖chenMCharSum ψ N‖) +
            (∑ k ∈ Finset.Ico Q₁ Q,
              (1 / (Nat.totient (k + 1) : ℝ)) *
                ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                  ‖chenMCharSum ψ N‖) := by
        by_cases hQQ1 : Q ≤ Q₁
        · have hempty : Finset.Ico Q₁ Q = ∅ := Finset.Ico_eq_empty_of_le hQQ1
          rw [Nat.min_eq_right hQQ1, hempty, Finset.sum_empty, add_zero]
        · push Not at hQQ1
          rw [Nat.min_eq_left hQQ1.le]
          have hunion : Finset.Ico 2 Q = Finset.Ico 2 Q₁ ∪ Finset.Ico Q₁ Q := by
            ext k; simp only [Finset.mem_Ico, Finset.mem_union]; omega
          have hdisj : Disjoint (Finset.Ico 2 Q₁) (Finset.Ico Q₁ Q) := by
            rw [Finset.disjoint_left]; intro k h1 h2; simp only [Finset.mem_Ico] at h1 h2; omega
          rw [hunion, Finset.sum_union hdisj]
      -- Bound 2a: Small conductors `k ∈ Ico 2 (min Q₁ Q)` via Siegel–Walfisz
      have hsmall_cond :
          12 * Real.log (N : ℝ) *
            ∑ k ∈ Finset.Ico 2 (min Q₁ Q),
              (1 / (Nat.totient (k + 1) : ℝ)) *
                ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                  ‖chenMCharSum ψ N‖ ≤
            (48 * C_sw + 48) * (N : ℝ) / (Real.log (N : ℝ)) ^ A' := by
        set M_sw : ℝ := (N : ℝ) ^ ((2 : ℝ) / 3) * (2 * Real.log (N : ℝ) + 2) +
          2 * (Real.log (N : ℝ)) ^ B₁ * C_sw * (N : ℝ) * (1 + Real.log (N : ℝ)) *
            Real.exp (-(c_sw / 2) * Real.sqrt (Real.log (N : ℝ)))
        have hper_k : ∀ k ∈ Finset.Ico 2 (min Q₁ Q),
            (1 / (Nat.totient (k + 1) : ℝ)) *
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                ‖chenMCharSum ψ N‖ ≤ M_sw := by
          intro k hk
          have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
          have hkQ1 : k + 1 ≤ Q₁ := by have := (Finset.mem_Ico.mp hk).2; omega
          have hmod_le : ((k + 1 : ℕ) : ℝ) ≤ (Real.log (N : ℝ)) ^ B₁ :=
            (by exact_mod_cast hkQ1 : ((k + 1 : ℕ) : ℝ) ≤ (Q₁ : ℝ)).trans hQ1_le_R
          have hphi_pos : (0 : ℝ) < (Nat.totient (k + 1) : ℝ) :=
            Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.succ_pos k))
          have htot : Fintype.card (DirichletCharacter ℂ (k + 1)) = (k + 1).totient := by
            rw [← Nat.card_eq_fintype_card]
            exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ (k + 1)
          have hcard :
              ((Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive)).card : ℝ) ≤
                (Nat.totient (k + 1) : ℝ) := by
            have hnat : (Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive)).card ≤
                (k + 1).totient :=
              (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, htot])
            exact_mod_cast hnat
          calc (1 / (Nat.totient (k + 1) : ℝ)) *
                ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                  ‖chenMCharSum ψ N‖
              ≤ (1 / (Nat.totient (k + 1) : ℝ)) *
                  ∑ _ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                    M_sw := by
                refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ψ hψ => ?_) (by positivity)
                have hprim : ψ.IsPrimitive := (Finset.mem_filter.mp hψ).2
                have hne1 : ψ ≠ 1 := by
                  intro h1
                  have hc : ψ.conductor = k + 1 := hprim
                  rw [h1, DirichletCharacter.conductor_one] at hc
                  omega
                have hbd := norm_chenMCharSum_of_siegel_walfisz hc_sw hC_sw hB1_pos hsw hN4096
                  hlog_big hmod_le hne1
                refine hbd.trans ?_
                dsimp only [M_sw]; gcongr
            _ = (((Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive)).card : ℝ) /
                  (Nat.totient (k + 1) : ℝ)) * M_sw := by
                rw [Finset.sum_const, nsmul_eq_mul]; ring
            _ ≤ 1 * M_sw := mul_le_mul_of_nonneg_right ((div_le_one hphi_pos).mpr hcard) (by dsimp only [M_sw]; positivity)
            _ = M_sw := one_mul _
        have hsum_k :
            ∑ k ∈ Finset.Ico 2 (min Q₁ Q),
              (1 / (Nat.totient (k + 1) : ℝ)) *
                ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                  ‖chenMCharSum ψ N‖ ≤
              (Real.log (N : ℝ)) ^ B₁ * M_sw := by
          calc _ ≤ ∑ _k ∈ Finset.Ico 2 (min Q₁ Q), M_sw := Finset.sum_le_sum hper_k
            _ = ((Finset.Ico 2 (min Q₁ Q)).card : ℝ) * M_sw := by rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (Q₁ : ℝ) * M_sw := by
                refine mul_le_mul_of_nonneg_right ?_ (by dsimp only [M_sw]; positivity)
                rw [Nat.card_Ico]; exact_mod_cast (by omega : min Q₁ Q - 2 ≤ Q₁)
            _ ≤ (Real.log (N : ℝ)) ^ B₁ * M_sw :=
                mul_le_mul_of_nonneg_right hQ1_le_R (by dsimp only [M_sw]; positivity)
        rw [le_div_iff₀ (Real.rpow_pos_of_pos hLN_pos A')]
        -- Bound both parts of `12 * log N * (log N)^{B₁} * M_sw * (log N)^{A'}`
        have hpart1 :
            12 * Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ B₁ *
              ((N : ℝ) ^ ((2 : ℝ) / 3) * (2 * Real.log (N : ℝ) + 2)) * (Real.log (N : ℝ)) ^ A' ≤
            48 * (N : ℝ) := by
          have h2L : 2 * Real.log (N : ℝ) + 2 ≤ 4 * Real.log (N : ℝ) := by linarith
          have hL_pow : Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ B₁ * Real.log (N : ℝ) *
              (Real.log (N : ℝ)) ^ A' ≤ (N : ℝ) ^ ((1 : ℝ) / 24) := by
            have hEq : Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ B₁ * Real.log (N : ℝ) *
                (Real.log (N : ℝ)) ^ A' = (Real.log (N : ℝ)) ^ (B₁ + A' + 2) := by
              rw [show Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ B₁ * Real.log (N : ℝ) *
                  (Real.log (N : ℝ)) ^ A' =
                (Real.log (N : ℝ)) ^ (1 : ℝ) * (Real.log (N : ℝ)) ^ B₁ *
                (Real.log (N : ℝ)) ^ (1 : ℝ) * (Real.log (N : ℝ)) ^ A' by rw [Real.rpow_one],
                ← Real.rpow_add hLN_pos, ← Real.rpow_add hLN_pos, ← Real.rpow_add hLN_pos]
              congr 1; ring
            rw [hEq]
            exact hL_le_N24 _ (by dsimp only [B₁, E]; linarith) (by dsimp only [B₁, E, M_exp]; linarith)
          calc 12 * Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ B₁ *
                ((N : ℝ) ^ ((2 : ℝ) / 3) * (2 * Real.log (N : ℝ) + 2)) * (Real.log (N : ℝ)) ^ A'
              ≤ 12 * Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ B₁ *
                ((N : ℝ) ^ ((2 : ℝ) / 3) * (4 * Real.log (N : ℝ))) * (Real.log (N : ℝ)) ^ A' := by gcongr
            _ = 48 * (N : ℝ) ^ ((2 : ℝ) / 3) *
                (Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ B₁ * Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ A') := by ring
            _ ≤ 48 * (N : ℝ) ^ ((2 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 24) := by gcongr
            _ = 48 * (N : ℝ) ^ ((17 : ℝ) / 24) := by rw [mul_assoc, ← Real.rpow_add hN_pos]; norm_num
            _ ≤ 48 * (N : ℝ) ^ (1 : ℝ) := mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)) (by norm_num)
            _ = 48 * (N : ℝ) := by rw [Real.rpow_one]
        have hpart2 :
            12 * Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ B₁ *
              (2 * (Real.log (N : ℝ)) ^ B₁ * C_sw * (N : ℝ) * (1 + Real.log (N : ℝ)) *
                Real.exp (-(c_sw / 2) * Real.sqrt (Real.log (N : ℝ)))) * (Real.log (N : ℝ)) ^ A' ≤
            48 * C_sw * (N : ℝ) := by
          have h1L : 1 + Real.log (N : ℝ) ≤ 2 * Real.log (N : ℝ) := by linarith
          have hpow_le : Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ B₁ * (Real.log (N : ℝ)) ^ B₁ *
              Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ A' ≤ (Real.log (N : ℝ)) ^ (2 * B₁ + A' + 5) := by
            have hEq : Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ B₁ * (Real.log (N : ℝ)) ^ B₁ *
                Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ A' =
                (Real.log (N : ℝ)) ^ (2 * B₁ + A' + 2) := by
              rw [show Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ B₁ * (Real.log (N : ℝ)) ^ B₁ *
                  Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ A' =
                (Real.log (N : ℝ)) ^ (1 : ℝ) * (Real.log (N : ℝ)) ^ B₁ *
                (Real.log (N : ℝ)) ^ B₁ * (Real.log (N : ℝ)) ^ (1 : ℝ) * (Real.log (N : ℝ)) ^ A' by rw [Real.rpow_one],
                ← Real.rpow_add hLN_pos, ← Real.rpow_add hLN_pos, ← Real.rpow_add hLN_pos,
                ← Real.rpow_add hLN_pos]
              congr 1; ring
            rw [hEq]
            exact Real.rpow_le_rpow_of_exponent_le hLN_gt1.le (by linarith)
          calc 12 * Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ B₁ *
                (2 * (Real.log (N : ℝ)) ^ B₁ * C_sw * (N : ℝ) * (1 + Real.log (N : ℝ)) *
                  Real.exp (-(c_sw / 2) * Real.sqrt (Real.log (N : ℝ)))) * (Real.log (N : ℝ)) ^ A'
              ≤ 12 * Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ B₁ *
                (2 * (Real.log (N : ℝ)) ^ B₁ * C_sw * (N : ℝ) * (2 * Real.log (N : ℝ)) *
                  Real.exp (-(c_sw / 2) * Real.sqrt (Real.log (N : ℝ)))) * (Real.log (N : ℝ)) ^ A' := by gcongr
            _ = 48 * C_sw * (N : ℝ) *
                ((Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ B₁ * (Real.log (N : ℝ)) ^ B₁ *
                  Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ A') *
                  Real.exp (-(c_sw / 2) * Real.sqrt (Real.log (N : ℝ)))) := by ring
            _ ≤ 48 * C_sw * (N : ℝ) *
                ((Real.log (N : ℝ)) ^ (2 * B₁ + A' + 5) *
                  Real.exp (-(c_sw / 2) * Real.sqrt (Real.log (N : ℝ)))) := by gcongr
            _ ≤ 48 * C_sw * (N : ℝ) * 1 := mul_le_mul_of_nonneg_left hsw_decay (by positivity)
            _ = 48 * C_sw * (N : ℝ) := mul_one _
        have hcomb_sw :
            12 * Real.log (N : ℝ) * ((Real.log (N : ℝ)) ^ B₁ * M_sw) * (Real.log (N : ℝ)) ^ A' ≤
              (48 * C_sw + 48) * (N : ℝ) := by
          dsimp only [M_sw]
          have hEq :
              12 * Real.log (N : ℝ) * ((Real.log (N : ℝ)) ^ B₁ *
                ((N : ℝ) ^ ((2 : ℝ) / 3) * (2 * Real.log (N : ℝ) + 2) +
                  2 * (Real.log (N : ℝ)) ^ B₁ * C_sw * (N : ℝ) * (1 + Real.log (N : ℝ)) *
                    Real.exp (-(c_sw / 2) * Real.sqrt (Real.log (N : ℝ))))) * (Real.log (N : ℝ)) ^ A' =
              12 * Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ B₁ *
                ((N : ℝ) ^ ((2 : ℝ) / 3) * (2 * Real.log (N : ℝ) + 2)) * (Real.log (N : ℝ)) ^ A' +
              12 * Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ B₁ *
                (2 * (Real.log (N : ℝ)) ^ B₁ * C_sw * (N : ℝ) * (1 + Real.log (N : ℝ)) *
                  Real.exp (-(c_sw / 2) * Real.sqrt (Real.log (N : ℝ)))) * (Real.log (N : ℝ)) ^ A' := by
            ring
          rw [hEq]; linarith
        have hmul_k := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsum_k (show 0 ≤ 12 * Real.log (N : ℝ) by positivity))
          (Real.rpow_nonneg hLN_pos.le A')
        exact hmul_k.trans hcomb_sw
      -- Bound 2b: Large conductors `k ∈ Ico Q₁ Q` via Dyadic Geometric Bilinear Large Sieve!
      have hlarge_cond :
          12 * Real.log (N : ℝ) *
            ∑ k ∈ Finset.Ico Q₁ Q,
              (1 / (Nat.totient (k + 1) : ℝ)) *
                ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                  ‖chenMCharSum ψ N‖ ≤
            90000 * (N : ℝ) / (Real.log (N : ℝ)) ^ A' := by
        by_cases hQQ1 : Q ≤ Q₁
        · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, mul_zero]; positivity
        · push Not at hQQ1
          set Δ : ℝ := (Real.log (N : ℝ)) ^ (-E) with hΔ_def
          have hΔ0 : 0 < Δ := Real.rpow_pos_of_pos hLN_pos (-E)
          have hΔ1 : Δ < 1 := by
            rw [hΔ_def, Real.rpow_neg hLN_pos.le]
            exact inv_lt_one_of_one_lt₀ (by
              calc (1 : ℝ) < Real.log (N : ℝ) := hLN_gt1
                _ = (Real.log (N : ℝ)) ^ (1 : ℝ) := (Real.rpow_one _).symm
                _ ≤ (Real.log (N : ℝ)) ^ E :=
                    Real.rpow_le_rpow_of_exponent_le hLN_gt1.le (by dsimp only [E]; linarith))
          have hΔ_lo : (N : ℝ) ^ (-(1 : ℝ) / 24) ≤ Δ := by
            rw [hΔ_def, Real.rpow_neg hLN_pos.le,
              show -(1 : ℝ) / 24 = -((1 : ℝ) / 24) by ring, Real.rpow_neg hN_pos.le]
            exact inv_anti₀ (by positivity)
              (hL_le_N24 E hE_pos.le (by dsimp only [E, M_exp]; linarith))
          -- Cover `Ico Q₁ Q` by `J = Nat.log 2 (Q / Q₁) + 1` dyadic blocks `Ico (Q₁ * 2^j) (2 * (Q₁ * 2^j))`
          set J : ℕ := Nat.log 2 (Q / Q₁) + 1 with hJ_def
          have hcover : Finset.Ico Q₁ Q ⊆
              (Finset.range J).biUnion (fun j => Finset.Ico (Q₁ * 2 ^ j) (2 * (Q₁ * 2 ^ j))) := by
            intro k hk
            simp only [Finset.mem_Ico, Finset.mem_biUnion, Finset.mem_range] at hk ⊢
            refine ⟨Nat.log 2 (k / Q₁), ?_, ?_, ?_⟩
            · have hdiv_le : k / Q₁ ≤ Q / Q₁ := Nat.div_le_div_right hk.2.le
              have hlog_le : Nat.log 2 (k / Q₁) ≤ Nat.log 2 (Q / Q₁) := Nat.log_mono_right hdiv_le
              omega
            · have hk_div : 1 ≤ k / Q₁ := Nat.div_pos hk.1 (by omega)
              have hpow : 2 ^ Nat.log 2 (k / Q₁) ≤ k / Q₁ := Nat.pow_log_le_self 2 (by omega)
              calc Q₁ * 2 ^ Nat.log 2 (k / Q₁) ≤ Q₁ * (k / Q₁) := Nat.mul_le_mul_left Q₁ hpow
                _ ≤ k := Nat.mul_div_le k Q₁
            · have hlt : k / Q₁ < 2 ^ (Nat.log 2 (k / Q₁) + 1) :=
                Nat.lt_pow_succ_log_self (by omega) (k / Q₁)
              have hdiv := Nat.div_add_mod k Q₁
              have hmod : k % Q₁ < Q₁ := Nat.mod_lt k (by omega)
              have hpow : 2 ^ (Nat.log 2 (k / Q₁) + 1) = 2 * 2 ^ Nat.log 2 (k / Q₁) := by
                rw [pow_succ, mul_comm]
              have h1 : k < Q₁ * (k / Q₁ + 1) := by nlinarith
              have h2 : k / Q₁ + 1 ≤ 2 * 2 ^ Nat.log 2 (k / Q₁) := by omega
              calc k < Q₁ * (k / Q₁ + 1) := h1
                _ ≤ Q₁ * (2 * 2 ^ Nat.log 2 (k / Q₁)) := Nat.mul_le_mul_left Q₁ h2
                _ = 2 * (Q₁ * 2 ^ Nat.log 2 (k / Q₁)) := by ring
          have hbiUnion_le :
              ∑ k ∈ Finset.Ico Q₁ Q,
                  (1 / (Nat.totient (k + 1) : ℝ)) *
                    ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                      ‖chenMCharSum ψ N‖ ≤
                ∑ j ∈ Finset.range J,
                  ∑ k ∈ Finset.Ico (Q₁ * 2 ^ j) (2 * (Q₁ * 2 ^ j)),
                    (1 / (Nat.totient (k + 1) : ℝ)) *
                      ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                        ‖chenMCharSum ψ N‖ := by
            calc _ ≤ ∑ k ∈ (Finset.range J).biUnion (fun j => Finset.Ico (Q₁ * 2 ^ j) (2 * (Q₁ * 2 ^ j))),
                      (1 / (Nat.totient (k + 1) : ℝ)) *
                        ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                          ‖chenMCharSum ψ N‖ :=
                    Finset.sum_le_sum_of_subset_of_nonneg hcover fun _ _ _ =>
                      mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
              _ ≤ _ := sum_biUnion_le_local _ _ _ fun _ =>
                    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
          -- Bound `K_idx ≤ 3 * (log N)^{E + 1}`
          set K_idx : ℕ := ⌊2 * Real.log (N : ℝ) / Δ⌋₊ + 1
          have hK_le : (K_idx : ℝ) ≤ 3 * (Real.log (N : ℝ)) ^ (E + 1) := by
            have h1 : (K_idx : ℝ) ≤ 2 * Real.log (N : ℝ) / Δ + 1 := by
              dsimp only [K_idx]; push_cast; linarith [Nat.floor_le (show 0 ≤ 2 * Real.log (N : ℝ) / Δ by positivity)]
            have hdiv : Real.log (N : ℝ) / Δ = (Real.log (N : ℝ)) ^ (E + 1) := by
              rw [hΔ_def, Real.rpow_neg hLN_pos.le, div_inv_eq_mul,
                Real.rpow_add hLN_pos E 1, Real.rpow_one, mul_comm]
            have hge1 : (1 : ℝ) ≤ (Real.log (N : ℝ)) ^ (E + 1) :=
              Real.one_le_rpow hLN_gt1.le (by linarith)
            have h2 : 2 * Real.log (N : ℝ) / Δ = 2 * (Real.log (N : ℝ)) ^ (E + 1) := by
              rw [← hdiv]; ring
            linarith
          -- Bound each dyadic block `j < J` by `2000 * N / (log N)^{A' + 2}`
          have hper_j : ∀ j ∈ Finset.range J,
              ∑ k ∈ Finset.Ico (Q₁ * 2 ^ j) (2 * (Q₁ * 2 ^ j)),
                  (1 / (Nat.totient (k + 1) : ℝ)) *
                    ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                      ‖chenMCharSum ψ N‖ ≤
                2000 * (N : ℝ) / (Real.log (N : ℝ)) ^ (A' + 2) := by
            intro j hj
            set D : ℕ := Q₁ * 2 ^ j
            have hD1 : 1 ≤ D := Nat.mul_pos (by omega) (by positivity)
            have hD_ge_Q1 : Q₁ ≤ D := Nat.le_mul_of_pos_right Q₁ (by positivity)
            have hD_le_Q : D ≤ Q := by
              have hj_le : j ≤ Nat.log 2 (Q / Q₁) := by have := Finset.mem_range.mp hj; omega
              have hpow : 2 ^ j ≤ Q / Q₁ :=
                (Nat.pow_le_pow_right (by omega) hj_le).trans (Nat.pow_log_le_self 2 (by
                  have : 1 ≤ Q / Q₁ := Nat.div_pos hQQ1.le (by omega); omega))
              calc D = Q₁ * 2 ^ j := rfl
                _ ≤ Q₁ * (Q / Q₁) := Nat.mul_le_mul_left Q₁ hpow
                _ ≤ Q := Nat.mul_div_le Q Q₁
            have hD_le_QR : (D : ℝ) ≤ Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B :=
              (by exact_mod_cast hD_le_Q : (D : ℝ) ≤ (Q : ℝ)).trans hQR_le
            have hD_le_sqN : (D : ℝ) ≤ Real.sqrt (N : ℝ) :=
              (by exact_mod_cast hD_le_Q : (D : ℝ) ≤ (Q : ℝ)).trans hQ_le_sqN
            have hdy := dyadic_prim_chenMCharSum_bound hD1 hN4096 hD_le_sqN hΔ0 hΔ1 hΔ_lo
            have hK2 : (K_idx : ℝ) ^ 2 ≤ 9 * (Real.log (N : ℝ)) ^ (2 * E + 2) := by
              calc (K_idx : ℝ) ^ 2 ≤ (3 * (Real.log (N : ℝ)) ^ (E + 1)) ^ 2 :=
                    pow_le_pow_left₀ (Nat.cast_nonneg _) hK_le 2
                _ = 9 * ((Real.log (N : ℝ)) ^ (E + 1) * (Real.log (N : ℝ)) ^ (E + 1)) := by ring
                _ = 9 * (Real.log (N : ℝ)) ^ (2 * E + 2) := by
                    rw [← Real.rpow_add hLN_pos]; congr 2; ring
            -- Term 1: `K_idx² * (2 Δ N / D) ≤ 36 N / (log N)^{A' + 2}`
            have hT1 : (K_idx : ℝ) ^ 2 * (2 * Δ * (N : ℝ) / (D : ℝ)) ≤
                36 * (N : ℝ) / (Real.log (N : ℝ)) ^ (A' + 2) := by
              have hD_lo : (Real.log (N : ℝ)) ^ B₁ / 2 ≤ (D : ℝ) :=
                hQ1_ge_half.trans (by exact_mod_cast hD_ge_Q1)
              have h1 : 2 * Δ * (N : ℝ) / (D : ℝ) ≤
                  4 * (N : ℝ) / (Real.log (N : ℝ)) ^ (B₁ + E) := by
                have h2 : 2 * Δ * (N : ℝ) / (D : ℝ) ≤ 2 * Δ * (N : ℝ) / ((Real.log (N : ℝ)) ^ B₁ / 2) :=
                  div_le_div_of_nonneg_left (by positivity) (by positivity) hD_lo
                refine h2.trans_eq ?_
                rw [hΔ_def, Real.rpow_neg hLN_pos.le, Real.rpow_add hLN_pos B₁ E]
                field_simp [(Real.rpow_pos_of_pos hLN_pos B₁).ne', (Real.rpow_pos_of_pos hLN_pos E).ne']
                ring
              calc (K_idx : ℝ) ^ 2 * (2 * Δ * (N : ℝ) / (D : ℝ))
                  ≤ (9 * (Real.log (N : ℝ)) ^ (2 * E + 2)) *
                    (4 * (N : ℝ) / (Real.log (N : ℝ)) ^ (B₁ + E)) :=
                    mul_le_mul hK2 h1 (by positivity) (by positivity)
                _ = 36 * (N : ℝ) * ((Real.log (N : ℝ)) ^ (2 * E + 2) / (Real.log (N : ℝ)) ^ (B₁ + E)) := by ring
                _ = 36 * (N : ℝ) / (Real.log (N : ℝ)) ^ (B₁ - E - 2) := by
                    rw [← Real.rpow_sub hLN_pos,
                      show (2 * E + 2) - (B₁ + E) = -(B₁ - E - 2) by ring,
                      Real.rpow_neg hLN_pos.le, ← div_eq_mul_inv]
                _ ≤ 36 * (N : ℝ) / (Real.log (N : ℝ)) ^ (A' + 2) :=
                    div_le_div_of_nonneg_left (by positivity) (by positivity)
                      (Real.rpow_le_rpow_of_exponent_le hLN_gt1.le (by dsimp only [B₁, E]; linarith))
            -- Term 2: `K_idx² * (24 N^{5/6}) ≤ 216 N / (log N)^{A' + 2}`
            have hT2 : (K_idx : ℝ) ^ 2 * (24 * (N : ℝ) ^ ((5 : ℝ) / 6)) ≤
                216 * (N : ℝ) / (Real.log (N : ℝ)) ^ (A' + 2) := by
              rw [le_div_iff₀ (Real.rpow_pos_of_pos hLN_pos _)]
              have hL_pow : (Real.log (N : ℝ)) ^ (2 * E + 2) * (Real.log (N : ℝ)) ^ (A' + 2) ≤
                  (N : ℝ) ^ ((1 : ℝ) / 24) := by
                rw [← Real.rpow_add hLN_pos]
                exact hL_le_N24 _ (by dsimp only [E]; linarith) (by dsimp only [E, M_exp]; linarith)
              calc (K_idx : ℝ) ^ 2 * (24 * (N : ℝ) ^ ((5 : ℝ) / 6)) * (Real.log (N : ℝ)) ^ (A' + 2)
                  ≤ (9 * (Real.log (N : ℝ)) ^ (2 * E + 2)) * (24 * (N : ℝ) ^ ((5 : ℝ) / 6)) *
                    (Real.log (N : ℝ)) ^ (A' + 2) := by gcongr
                _ = 216 * (N : ℝ) ^ ((5 : ℝ) / 6) *
                    ((Real.log (N : ℝ)) ^ (2 * E + 2) * (Real.log (N : ℝ)) ^ (A' + 2)) := by ring
                _ ≤ 216 * (N : ℝ) ^ ((5 : ℝ) / 6) * (N : ℝ) ^ ((1 : ℝ) / 24) := by gcongr
                _ = 216 * (N : ℝ) ^ ((7 : ℝ) / 8) := by rw [mul_assoc, ← Real.rpow_add hN_pos]; norm_num
                _ ≤ 216 * (N : ℝ) ^ (1 : ℝ) := mul_le_mul_of_nonneg_left
                    (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)) (by norm_num)
                _ = 216 * (N : ℝ) := by rw [Real.rpow_one]
            -- Term 3: `K_idx² * (32 D √N) ≤ 288 N / (log N)^{A' + 2}`
            have hT3 : (K_idx : ℝ) ^ 2 * (32 * (D : ℝ) * Real.sqrt (N : ℝ)) ≤
                288 * (N : ℝ) / (Real.log (N : ℝ)) ^ (A' + 2) := by
              have hDsq : (D : ℝ) * Real.sqrt (N : ℝ) ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ B := by
                calc (D : ℝ) * Real.sqrt (N : ℝ)
                    ≤ (Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B) * Real.sqrt (N : ℝ) := by gcongr
                  _ = (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) / (Real.log (N : ℝ)) ^ B := by ring
                  _ = (N : ℝ) / (Real.log (N : ℝ)) ^ B := by rw [Real.mul_self_sqrt hN_pos.le]
              calc (K_idx : ℝ) ^ 2 * (32 * (D : ℝ) * Real.sqrt (N : ℝ))
                  ≤ (9 * (Real.log (N : ℝ)) ^ (2 * E + 2)) * (32 * ((N : ℝ) / (Real.log (N : ℝ)) ^ B)) := by
                    have h1 : 32 * (D : ℝ) * Real.sqrt (N : ℝ) = 32 * ((D : ℝ) * Real.sqrt (N : ℝ)) := by ring
                    rw [h1]
                    exact mul_le_mul hK2 (mul_le_mul_of_nonneg_left hDsq (by norm_num)) (by positivity) (by positivity)
                _ = 288 * (N : ℝ) * ((Real.log (N : ℝ)) ^ (2 * E + 2) / (Real.log (N : ℝ)) ^ B) := by ring
                _ = 288 * (N : ℝ) / (Real.log (N : ℝ)) ^ (B - (2 * E + 2)) := by
                    rw [← Real.rpow_sub hLN_pos,
                      show (2 * E + 2) - B = -(B - (2 * E + 2)) by ring,
                      Real.rpow_neg hLN_pos.le, ← div_eq_mul_inv]
                _ ≤ 288 * (N : ℝ) / (Real.log (N : ℝ)) ^ (A' + 2) :=
                    div_le_div_of_nonneg_left (by positivity) (by positivity)
                      (Real.rpow_le_rpow_of_exponent_le hLN_gt1.le (by dsimp only [B, E]; linarith))
            -- Term 4: Boundary term `20 N √Δ √(1 + log N) ≤ 40 N / (log N)^{A' + 2}`
            have hT4 : 20 * (N : ℝ) * Real.sqrt Δ * Real.sqrt (1 + Real.log (N : ℝ)) ≤
                40 * (N : ℝ) / (Real.log (N : ℝ)) ^ (A' + 2) := by
              have hsqΔ : Real.sqrt Δ = (Real.log (N : ℝ)) ^ (-(E / 2)) := by
                rw [hΔ_def, Real.sqrt_eq_rpow, ← Real.rpow_mul hLN_pos.le]; congr 1; ring
              have hsqL : Real.sqrt (1 + Real.log (N : ℝ)) ≤ 2 * Real.log (N : ℝ) := by
                have h1 : 1 + Real.log (N : ℝ) ≤ (2 * Real.log (N : ℝ)) ^ 2 := by nlinarith
                exact (Real.sqrt_le_sqrt h1).trans_eq (Real.sqrt_sq (by linarith))
              calc 20 * (N : ℝ) * Real.sqrt Δ * Real.sqrt (1 + Real.log (N : ℝ))
                  ≤ 20 * (N : ℝ) * (Real.log (N : ℝ)) ^ (-(E / 2)) * (2 * Real.log (N : ℝ)) := by
                    rw [hsqΔ]; gcongr
                _ = 40 * (N : ℝ) * ((Real.log (N : ℝ)) ^ (-(E / 2)) * (Real.log (N : ℝ)) ^ (1 : ℝ)) := by
                    rw [Real.rpow_one]; ring
                _ = 40 * (N : ℝ) / (Real.log (N : ℝ)) ^ (E / 2 - 1) := by
                    rw [← Real.rpow_add hLN_pos,
                      show -(E / 2) + 1 = -(E / 2 - 1) by ring,
                      Real.rpow_neg hLN_pos.le, ← div_eq_mul_inv]
                _ ≤ 40 * (N : ℝ) / (Real.log (N : ℝ)) ^ (A' + 2) :=
                    div_le_div_of_nonneg_left (by positivity) (by positivity)
                      (Real.rpow_le_rpow_of_exponent_le hLN_gt1.le (by dsimp only [E]; linarith))
            have hdist :
                (K_idx : ℝ) ^ 2 *
                    (2 * Δ * (N : ℝ) / (D : ℝ) + 24 * (N : ℝ) ^ ((5 : ℝ) / 6) +
                      32 * (D : ℝ) * Real.sqrt (N : ℝ)) =
                  (K_idx : ℝ) ^ 2 * (2 * Δ * (N : ℝ) / (D : ℝ)) +
                  (K_idx : ℝ) ^ 2 * (24 * (N : ℝ) ^ ((5 : ℝ) / 6)) +
                  (K_idx : ℝ) ^ 2 * (32 * (D : ℝ) * Real.sqrt (N : ℝ)) := by ring
            have hsum_rhs :
                36 * (N : ℝ) / (Real.log (N : ℝ)) ^ (A' + 2) +
                216 * (N : ℝ) / (Real.log (N : ℝ)) ^ (A' + 2) +
                288 * (N : ℝ) / (Real.log (N : ℝ)) ^ (A' + 2) +
                40 * (N : ℝ) / (Real.log (N : ℝ)) ^ (A' + 2) ≤
                2000 * (N : ℝ) / (Real.log (N : ℝ)) ^ (A' + 2) := by
              have hnn : 0 ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ (A' + 2) := by positivity
              have hEq : (36 + 216 + 288 + 40 : ℝ) * ((N : ℝ) / (Real.log (N : ℝ)) ^ (A' + 2)) =
                  36 * (N : ℝ) / (Real.log (N : ℝ)) ^ (A' + 2) +
                  216 * (N : ℝ) / (Real.log (N : ℝ)) ^ (A' + 2) +
                  288 * (N : ℝ) / (Real.log (N : ℝ)) ^ (A' + 2) +
                  40 * (N : ℝ) / (Real.log (N : ℝ)) ^ (A' + 2) := by ring
              have hEq2 : 2000 * (N : ℝ) / (Real.log (N : ℝ)) ^ (A' + 2) =
                  2000 * ((N : ℝ) / (Real.log (N : ℝ)) ^ (A' + 2)) := by ring
              linarith
            linarith
          -- Bound `J ≤ 3 * Real.log N`
          have hJ_le : (J : ℝ) ≤ 3 * Real.log (N : ℝ) := by
            have h2pow : (2 : ℝ) ^ Nat.log 2 (Q / Q₁) ≤ (N : ℝ) := by
              have hnat : 2 ^ Nat.log 2 (Q / Q₁) ≤ N :=
                (Nat.pow_log_le_self 2 (by have := Nat.div_pos hQQ1.le (by omega); omega)).trans
                  ((Nat.div_le_self Q Q₁).trans hQN)
              exact_mod_cast hnat
            have hlog := Real.log_le_log (by positivity) h2pow
            rw [Real.log_pow] at hlog
            have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
            have hJcast : (J : ℝ) = (Nat.log 2 (Q / Q₁) : ℝ) + 1 := by dsimp only [J]; push_cast; ring
            nlinarith
          have hsum_j :
              ∑ k ∈ Finset.Ico Q₁ Q,
                  (1 / (Nat.totient (k + 1) : ℝ)) *
                    ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                      ‖chenMCharSum ψ N‖ ≤
                (3 * Real.log (N : ℝ)) * (2000 * (N : ℝ) / (Real.log (N : ℝ)) ^ (A' + 2)) := by
            calc _ ≤ ∑ _j ∈ Finset.range J, (2000 * (N : ℝ) / (Real.log (N : ℝ)) ^ (A' + 2)) :=
                    hbiUnion_le.trans (Finset.sum_le_sum hper_j)
              _ = (J : ℝ) * (2000 * (N : ℝ) / (Real.log (N : ℝ)) ^ (A' + 2)) := by
                    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              _ ≤ (3 * Real.log (N : ℝ)) * (2000 * (N : ℝ) / (Real.log (N : ℝ)) ^ (A' + 2)) :=
                    mul_le_mul_of_nonneg_right hJ_le (by positivity)
          have hpow_cancel :
              12 * Real.log (N : ℝ) * ((3 * Real.log (N : ℝ)) * (2000 * (N : ℝ) / (Real.log (N : ℝ)) ^ (A' + 2))) =
                72000 * (N : ℝ) / (Real.log (N : ℝ)) ^ A' := by
            have hEq : (Real.log (N : ℝ)) ^ (A' + 2) = (Real.log (N : ℝ)) ^ A' * (Real.log (N : ℝ)) ^ 2 := by
              rw [Real.rpow_add hLN_pos, Real.rpow_two]
            rw [hEq]
            field_simp [(Real.rpow_pos_of_pos hLN_pos A').ne', hLN_pos.ne']
            ring
          calc 12 * Real.log (N : ℝ) *
                ∑ k ∈ Finset.Ico Q₁ Q,
                  (1 / (Nat.totient (k + 1) : ℝ)) *
                    ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                      ‖chenMCharSum ψ N‖
              ≤ 12 * Real.log (N : ℝ) * ((3 * Real.log (N : ℝ)) * (2000 * (N : ℝ) / (Real.log (N : ℝ)) ^ (A' + 2))) :=
                mul_le_mul_of_nonneg_left hsum_j (by positivity)
            _ = 72000 * (N : ℝ) / (Real.log (N : ℝ)) ^ A' := hpow_cancel
            _ ≤ 90000 * (N : ℝ) / (Real.log (N : ℝ)) ^ A' := by
                have h1 : 72000 * (N : ℝ) / (Real.log (N : ℝ)) ^ A' =
                    72000 * ((N : ℝ) / (Real.log (N : ℝ)) ^ A') := by ring
                have h2 : 90000 * (N : ℝ) / (Real.log (N : ℝ)) ^ A' =
                    90000 * ((N : ℝ) / (Real.log (N : ℝ)) ^ A') := by ring
                have hnn : 0 ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ A' := by positivity
                linarith
      -- Combine Bound 1 + Bound 2a + Bound 2b
      have hprim_comb :
          12 * Real.log (N : ℝ) *
            ∑ k ∈ Finset.Ico 2 Q,
              (1 / (Nat.totient (k + 1) : ℝ)) *
                ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                  ‖chenMCharSum ψ N‖ ≤
            (48 * C_sw + 90048) * (N : ℝ) / (Real.log (N : ℝ)) ^ A' := by
        have h1 := mul_le_mul_of_nonneg_left hsplit_prim (show 0 ≤ 12 * Real.log (N : ℝ) by positivity)
        rw [mul_add] at h1
        have hEq : (48 * C_sw + 90048) * (N : ℝ) / (Real.log (N : ℝ)) ^ A' =
            (48 * C_sw + 48) * (N : ℝ) / (Real.log (N : ℝ)) ^ A' +
            90000 * (N : ℝ) / (Real.log (N : ℝ)) ^ A' := by ring
        linarith
      have hClarge_le : C_large ≤ C := le_max_left _ _
      have htot :
          32 * (N : ℝ) / (Real.log (N : ℝ)) ^ A' +
            (48 * C_sw + 90048) * (N : ℝ) / (Real.log (N : ℝ)) ^ A' ≤
          C * (N : ℝ) / (Real.log (N : ℝ)) ^ A' := by
        have hsum_eq :
            32 * (N : ℝ) / (Real.log (N : ℝ)) ^ A' +
              (48 * C_sw + 90048) * (N : ℝ) / (Real.log (N : ℝ)) ^ A' =
            (48 * C_sw + 90080) * ((N : ℝ) / (Real.log (N : ℝ)) ^ A') := by ring
        have hC_eq : C * (N : ℝ) / (Real.log (N : ℝ)) ^ A' =
            C * ((N : ℝ) / (Real.log (N : ℝ)) ^ A') := by ring
        rw [hsum_eq, hC_eq]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        dsimp only [C_large] at hClarge_le
        linarith
      linarith
    · -- Case 2: Small `4 ≤ N < X₀`
      push Not at hN_big
      have hQ_le_N : (Q : ℝ) ≤ (N : ℝ) := by
        calc (Q : ℝ) ≤ Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B := Nat.floor_le (by positivity)
          _ ≤ Real.sqrt (N : ℝ) := div_le_self (Real.sqrt_nonneg _) (Real.one_le_rpow hLN_gt1.le hB_pos.le)
          _ ≤ (N : ℝ) := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
      have hper_triv : ∀ d ∈ (Finset.Icc 1 Q).filter (fun d => Squarefree d ∧ Nat.Coprime d N),
          |(((chenM N).filter (fun t => d ∣ (N - t.1 * t.2.1 * t.2.2))).card : ℝ) -
            ((chenM N).card : ℝ) / (d.totient : ℝ)| ≤ 2 * (N : ℝ) := by
        intro d hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
        have hphi1 : (1 : ℝ) ≤ (d.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd1
        have hcard_le : ((chenM N).card : ℝ) ≤ (N : ℝ) := by exact_mod_cast card_chenM_le N
        have hfilt_le : (((chenM N).filter (fun t => d ∣ (N - t.1 * t.2.1 * t.2.2))).card : ℝ) ≤ (N : ℝ) :=
          (by exact_mod_cast Finset.card_filter_le _ _ : _ ≤ ((chenM N).card : ℝ)).trans hcard_le
        have hdiv_le : ((chenM N).card : ℝ) / (d.totient : ℝ) ≤ (N : ℝ) :=
          (div_le_self (Nat.cast_nonneg _) hphi1).trans hcard_le
        rw [abs_le]
        constructor <;> linarith [Nat.cast_nonneg (α := ℝ) ((chenM N).filter (fun t => d ∣ (N - t.1 * t.2.1 * t.2.2))).card,
          div_nonneg (Nat.cast_nonneg (α := ℝ) (chenM N).card) (by linarith : (0 : ℝ) ≤ (d.totient : ℝ))]
      have hcard_D :
          (((Finset.Icc 1 Q).filter (fun d => Squarefree d ∧ Nat.Coprime d N)).card : ℝ) ≤ (N : ℝ) := by
        have hnat : ((Finset.Icc 1 Q).filter (fun d => Squarefree d ∧ Nat.Coprime d N)).card ≤ Q :=
          (Finset.card_filter_le _ _).trans (by rw [Nat.card_Icc]; omega)
        exact (by exact_mod_cast hnat : _ ≤ (Q : ℝ)).trans hQ_le_N
      have hlog_le : (Real.log (N : ℝ)) ^ A' ≤ (Real.log X₀) ^ A' :=
        Real.rpow_le_rpow hLN_pos.le (Real.log_le_log hN_pos hN_big.le) (by linarith)
      have hsmall_le : 2 * X₀ ^ 2 ≤ C_small * (N : ℝ) / (Real.log (N : ℝ)) ^ A' := by
        rw [le_div_iff₀ (Real.rpow_pos_of_pos hLN_pos A')]
        have h4 : (2 * X₀ ^ 2 + 1) * (Real.log X₀) ^ A' = C_small * 4 := by
          dsimp only [C_small]; ring
        have h1 : 2 * X₀ ^ 2 * (Real.log (N : ℝ)) ^ A' ≤ (2 * X₀ ^ 2 + 1) * (Real.log X₀) ^ A' := by
          have : 2 * X₀ ^ 2 * (Real.log (N : ℝ)) ^ A' ≤ 2 * X₀ ^ 2 * (Real.log X₀) ^ A' :=
            mul_le_mul_of_nonneg_left hlog_le (by positivity)
          have hpos : 0 ≤ (Real.log X₀) ^ A' := by positivity
          linarith
        have h2 : C_small * 4 ≤ C_small * (N : ℝ) := mul_le_mul_of_nonneg_left hNR4 hCsmall_pos.le
        linarith
      calc ∑ d ∈ (Finset.Icc 1 Q).filter (fun d => Squarefree d ∧ Nat.Coprime d N),
              |(((chenM N).filter (fun t => d ∣ (N - t.1 * t.2.1 * t.2.2))).card : ℝ) -
                ((chenM N).card : ℝ) / (d.totient : ℝ)|
          ≤ ∑ _d ∈ (Finset.Icc 1 Q).filter (fun d => Squarefree d ∧ Nat.Coprime d N), (2 * (N : ℝ)) :=
            Finset.sum_le_sum hper_triv
        _ = (((Finset.Icc 1 Q).filter (fun d => Squarefree d ∧ Nat.Coprime d N)).card : ℝ) * (2 * (N : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (N : ℝ) * (2 * (N : ℝ)) := mul_le_mul_of_nonneg_right hcard_D (by positivity)
        _ ≤ 2 * X₀ ^ 2 := by nlinarith
        _ ≤ C_small * (N : ℝ) / (Real.log (N : ℝ)) ^ A' := hsmall_le
        _ ≤ C * (N : ℝ) / (Real.log (N : ℝ)) ^ A' := by gcongr; exact le_max_right _ _

/-- **CHEN'S SWITCHED BILINEAR BOMBIERI–VINOGRADOV THEOREM (`chenMProd N` FORM)**:
equivalent formulation on the product set `chenMProd N = {q₁ q₂ q₃ : (q₁, q₂, q₃) ∈ chenM N}`,
obtained immediately from `chen_bilinear_bombieri_vinogradov` via the unique-factorization
bijections `card_chenMProd_eq` and `card_chenMProd_filter_dvd_eq`. -/
theorem chen_bilinear_bombieri_vinogradov_prod (A : ℝ) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧
      ∀ N : ℕ, 4 ≤ N →
        ∑ d ∈ (Finset.Icc 1 ⌊Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B⌋₊).filter
            (fun d => Squarefree d ∧ Nat.Coprime d N ∧ ∀ p ∈ d.primeFactors, p ≠ 2),
          |(((chenMProd N).filter (fun m => d ∣ (N - m))).card : ℝ) -
            ((chenMProd N).card : ℝ) / (d.totient : ℝ)| ≤
          C * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  obtain ⟨B, C, hB, hC, hmain⟩ := chen_bilinear_bombieri_vinogradov A
  refine ⟨B, C, hB, hC, fun N hN => ?_⟩
  have hcongr :
      ∑ d ∈ (Finset.Icc 1 ⌊Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B⌋₊).filter
          (fun d => Squarefree d ∧ Nat.Coprime d N ∧ ∀ p ∈ d.primeFactors, p ≠ 2),
        |(((chenMProd N).filter (fun m => d ∣ (N - m))).card : ℝ) -
          ((chenMProd N).card : ℝ) / (d.totient : ℝ)| =
      ∑ d ∈ (Finset.Icc 1 ⌊Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B⌋₊).filter
          (fun d => Squarefree d ∧ Nat.Coprime d N ∧ ∀ p ∈ d.primeFactors, p ≠ 2),
        |(((chenM N).filter (fun t => d ∣ (N - t.1 * t.2.1 * t.2.2))).card : ℝ) -
          ((chenM N).card : ℝ) / (d.totient : ℝ)| := by
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [card_chenMProd_filter_dvd_eq, card_chenMProd_eq]
  rw [hcongr]
  exact hmain N hN

end RHDirect.Chen

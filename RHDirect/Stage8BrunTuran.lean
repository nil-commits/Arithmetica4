import RHDirect.Stage8MertensTheorems
import RHDirect.Stage7SieveMethods
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# RHDirect.Stage8BrunTuran

Unconditional (`0`-assumption, `0`-`sorry`, `0`-custom-`axiom`) formalization in pure Mathlib
`v4.33.1` of three classical theorems of analytic number theory:

1. **Brun's Theorem on Twin Primes & General Even-Shift Prime Pairs**:
   - `prime_pair_upper_bound_selberg`: uniform upper bound
     `#{p ≤ x : p prime, p + h prime} ≤ C * (∏_{p ∣ h, p > 2} (p - 1)/(p - 2)) * x / (log x)^2`
     for every even `h ≥ 2` and every `x ≥ 3` (via Montgomery's arithmetic large sieve
     `Stage7SieveMethods.montgomery_arithmetic_large_sieve_Icc` and an elementary squarefree
     `lcm`-fiber lower bound on `montgomeryL`).
   - `twin_prime_upper_bound_selberg`: `π₂(x) ≤ C * x / (log x)^2` for all `x ≥ 3`.
   - `summable_twin_prime_reciprocals`, `summable_brun_constant`, `summable_prime_pair_reciprocals`:
     convergence of `∑_{p, p+2 prime} 1/p` and of Brun's constant `B₂ = ∑_{p, p+2 prime} (1/p + 1/(p+2))`
     via dyadic summation.

2. **Turán's 1934 Second-Moment Theorem & Hardy–Ramanujan 1917 Normal Order of `ω(n)` and `Ω(n)`**:
   - `sum_omega_asymp`, `sum_Omega_asymp`: exact first moments
     `|∑_{n ≤ x} ω(n) - x log log x| ≤ C x` and `|∑_{n ≤ x} Ω(n) - x log log x| ≤ C x`.
   - `turan_second_moment_omega`, `turan_second_moment_Omega`:
     `∑_{n ≤ x} (ω(n) - log log x)^2 ≤ C x log log x` and
     `∑_{n ≤ x} (Ω(n) - log log x)^2 ≤ C x log log x`.
   - `hardy_ramanujan_normal_order_omega_sharp`, `hardy_ramanujan_normal_order_omega`,
     `hardy_ramanujan_normal_order_Omega_sharp`, `hardy_ramanujan_normal_order_Omega`:
     natural density of `{n ≤ N : |f(n) - log log n| > (log log n)^{1/2 + ε}}` (and hence of
     `{n ≤ N : |f(n) - log log n| > ε log log n}`) tends to `0` as `N → ∞` for every `ε > 0`.

3. **Dirichlet's Divisor-Function Average (Dirichlet Hyperbola Method)**:
   - `dirichlet_hyperbola_identity`: exact identity
     `∑_{n ≤ N} d(n) + ⌊√N⌋^2 = 2 ∑_{d ≤ ⌊√N⌋} ⌊N / d⌋`.
   - `dirichlet_divisor_sum_asymp`:
     `|∑_{n ≤ x} d(n) - x (log x + 2 γ - 1)| ≤ C √x` for all `x ≥ 1`.

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open Finset Filter Topology
open scoped BigOperators ArithmeticFunction.omega ArithmeticFunction.Omega ArithmeticFunction.sigma

namespace RHDirect.Stage8BrunTuran

/-! ## Section 1: Unconditional Brun's Theorem on Twin Primes & General Even-Shift Prime Pairs -/

/-- `p` is the lower prime of a twin prime pair `(p, p + 2)`. -/
def IsTwinPrime (p : ℕ) : Prop :=
  p.Prime ∧ (p + 2).Prime

instance (p : ℕ) : Decidable (IsTwinPrime p) :=
  inferInstanceAs (Decidable (p.Prime ∧ (p + 2).Prime))

/-- Prime-pair counting function `π_h(x) = #{1 ≤ p ≤ ⌊x⌋₊ : p prime ∧ (p + h) prime}`. -/
def primePairCounting (h : ℕ) (x : ℝ) : ℕ :=
  ((Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ (p + h).Prime)).card

/-- Twin-prime counting function `π₂(x) = #{1 ≤ p ≤ ⌊x⌋₊ : p prime ∧ (p + 2) prime}`. -/
def twinPrimeCounting (x : ℝ) : ℕ :=
  ((Finset.Icc 1 ⌊x⌋₊).filter IsTwinPrime).card

theorem twinPrimeCounting_eq_primePairCounting (x : ℝ) :
    twinPrimeCounting x = primePairCounting 2 x := rfl

/-- Brun's constant `B₂ = ∑_{p, p+2 prime} (1/p + 1/(p+2))`. -/
def brunConstant : ℝ :=
  ∑' p : ℕ, if p.Prime ∧ (p + 2).Prime then (p : ℝ)⁻¹ + ((p + 2 : ℕ) : ℝ)⁻¹ else 0

/-- Squarefree `lcm` of two squarefree naturals is squarefree. -/
private theorem squarefree_lcm {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (Nat.lcm a b) := by
  have hne : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha.ne_zero hb.ne_zero
  rw [Nat.squarefree_iff_factorization_le_one hne]
  intro p
  rw [Nat.factorization_lcm ha.ne_zero hb.ne_zero, Finsupp.sup_apply]
  exact sup_le ((Nat.squarefree_iff_factorization_le_one ha.ne_zero).mp ha p)
    ((Nat.squarefree_iff_factorization_le_one hb.ne_zero).mp hb p)

/-- Prime factors of `Nat.lcm a b` for `a, b ≠ 0` are the union of their prime factors. -/
private theorem primeFactors_lcm {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Nat.lcm a b).primeFactors = a.primeFactors ∪ b.primeFactors := by
  ext p
  simp only [Nat.mem_primeFactors, Finset.mem_union]
  have hne : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha hb
  constructor
  · rintro ⟨hp, hdvd, -⟩
    have hmul : p ∣ a * b := hdvd.trans (Nat.lcm_dvd_mul a b)
    rcases hp.dvd_mul.mp hmul with hpa | hpb
    · exact Or.inl ⟨hp, hpa, ha⟩
    · exact Or.inr ⟨hp, hpb, hb⟩
  · rintro (⟨hp, hpa, -⟩ | ⟨hp, hpb, -⟩)
    · exact ⟨hp, hpa.trans (Nat.dvd_lcm_left a b), hne⟩
    · exact ⟨hp, hpb.trans (Nat.dvd_lcm_right a b), hne⟩

/-- Elementary inequality for odd primes `p ≥ 3`:
`1/(p - 1) + 1/(p - 1) + 1/(p - 1)² ≤ 2/(p - 2)`. -/
private theorem odd_prime_sieve_fiber_le {p : ℕ} (hp : 3 ≤ p) :
    (1 : ℝ) / ((p : ℝ) - 1) + (1 : ℝ) / ((p : ℝ) - 1) + ((1 : ℝ) / ((p : ℝ) - 1)) ^ 2 ≤
      (2 : ℝ) / ((p : ℝ) - 2) := by
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have h2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  have hden : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 * ((p : ℝ) - 2) := by positivity
  rw [← sub_nonneg]
  have hrew : (2 : ℝ) / ((p : ℝ) - 2) -
      ((1 : ℝ) / ((p : ℝ) - 1) + (1 : ℝ) / ((p : ℝ) - 1) + ((1 : ℝ) / ((p : ℝ) - 1)) ^ 2) =
      (p : ℝ) / (((p : ℝ) - 1) ^ 2 * ((p : ℝ) - 2)) := by
    field_simp [h1.ne', h2.ne']
    ring
  rw [hrew]
  positivity

/-- **Lower Bound on the Prime-Pair Montgomery Sieve Denominator `L(Q)`**:
for any even `h ≥ 2` and `ω(p) = if p ∣ h then 1 else 2`,
`(φ(h) / h) * (log (⌊√Q⌋ + 1))² ≤ montgomeryL ω Q`. -/
theorem montgomeryL_prime_pair_ge {h : ℕ} (hh : 2 ≤ h) (heven : Even h) (Q : ℕ) :
    ((h.totient : ℝ) / (h : ℝ)) * (Real.log ((Nat.sqrt Q : ℝ) + 1)) ^ 2 ≤
      Stage7SieveMethods.montgomeryL (fun p => if p ∣ h then 1 else 2) Q := by
  let w : ℕ → ℕ := fun p => if p ∣ h then 1 else 2
  set R : ℕ := Nat.sqrt Q
  set S₁ : Finset ℕ := (Finset.Icc 1 R).filter (fun n => Squarefree n ∧ Nat.Coprime n h)
  set S₂ : Finset ℕ := (Finset.Icc 1 R).filter Squarefree
  set T : Finset ℕ := (Finset.Icc 1 Q).filter Squarefree
  have hhpos : 0 < h := by omega
  have h2dvd : 2 ∣ h := even_iff_two_dvd.mp heven
  -- Step 1: Lower bound `(∑_{n₁ ∈ S₁} 1/φ(n₁)) * (∑_{n₂ ∈ S₂} 1/φ(n₂))` via `Stage7SieveMethods`
  have hS₁ : ((h.totient : ℝ) / (h : ℝ)) * Real.log ((R : ℝ) + 1) ≤
      ∑ n ∈ S₁, (1 : ℝ) / (n.totient : ℝ) :=
    Stage7SieveMethods.coprime_sum_squarefree_inv_totient_ge hhpos R
  have hS₂ : Real.log ((R : ℝ) + 1) ≤ ∑ n ∈ S₂, (1 : ℝ) / (n.totient : ℝ) :=
    Stage7SieveMethods.log_add_one_le_sum_squarefree_inv_totient R
  have hlog_nn : 0 ≤ Real.log ((R : ℝ) + 1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) R])
  have hprod_ge : ((h.totient : ℝ) / (h : ℝ)) * (Real.log ((R : ℝ) + 1)) ^ 2 ≤
      (∑ n₁ ∈ S₁, (1 : ℝ) / (n₁.totient : ℝ)) * (∑ n₂ ∈ S₂, (1 : ℝ) / (n₂.totient : ℝ)) := by
    have hmul := mul_le_mul hS₁ hS₂ hlog_nn
      (Finset.sum_nonneg fun _ _ => by positivity)
    linarith [show ((h.totient : ℝ) / (h : ℝ)) * Real.log ((R : ℝ) + 1) * Real.log ((R : ℝ) + 1) =
      ((h.totient : ℝ) / (h : ℝ)) * (Real.log ((R : ℝ) + 1)) ^ 2 by ring]
  -- Step 2: Fiberwise grouping by `q = Nat.lcm n₁ n₂ ∈ T`
  have hmaps : ∀ ab ∈ S₁ ×ˢ S₂, Nat.lcm ab.1 ab.2 ∈ T := by
    intro ab hab
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    obtain ⟨haI, hasqf, _⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbI, hbsqf⟩ := Finset.mem_filter.mp hb
    obtain ⟨ha1, haR⟩ := Finset.mem_Icc.mp haI
    obtain ⟨hb1, hbR⟩ := Finset.mem_Icc.mp hbI
    have hlcm_pos : 0 < Nat.lcm ab.1 ab.2 := Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega))
    have hlcm_le : Nat.lcm ab.1 ab.2 ≤ Q := by
      calc Nat.lcm ab.1 ab.2 ≤ ab.1 * ab.2 := Nat.le_of_dvd (Nat.mul_pos ha1 hb1) (Nat.lcm_dvd_mul ab.1 ab.2)
        _ ≤ R * R := Nat.mul_le_mul haR hbR
        _ ≤ Q := Nat.sqrt_le Q
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlcm_pos, hlcm_le⟩, squarefree_lcm hasqf hbsqf⟩
  have hprod_eq : (∑ n₁ ∈ S₁, (1 : ℝ) / (n₁.totient : ℝ)) * (∑ n₂ ∈ S₂, (1 : ℝ) / (n₂.totient : ℝ)) =
      ∑ q ∈ T, ∑ ab ∈ (S₁ ×ˢ S₂).filter (fun ab => Nat.lcm ab.1 ab.2 = q),
        ((1 : ℝ) / (ab.1.totient : ℝ)) * ((1 : ℝ) / (ab.2.totient : ℝ)) := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product',
      ← Finset.sum_fiberwise_of_maps_to hmaps]
  -- Step 3: Bound each `q`-fiber by `sieveWeight ω q`
  have hfiber_le : ∀ q ∈ T,
      ∑ ab ∈ (S₁ ×ˢ S₂).filter (fun ab => Nat.lcm ab.1 ab.2 = q),
        ((1 : ℝ) / (ab.1.totient : ℝ)) * ((1 : ℝ) / (ab.2.totient : ℝ)) ≤
      Stage7SieveMethods.sieveWeight w q := by
    intro q hq
    obtain ⟨_, hqsqf⟩ := Finset.mem_filter.mp hq
    set F : Finset (ℕ × ℕ) := (S₁ ×ˢ S₂).filter (fun ab => Nat.lcm ab.1 ab.2 = q)
    let code : ℕ × ℕ → (q.primeFactors → Fin 3) := fun ab p =>
      if p.1 ∣ ab.1 then (if p.1 ∣ ab.2 then (2 : Fin 3) else (0 : Fin 3)) else (1 : Fin 3)
    let allowed : q.primeFactors → Finset (Fin 3) := fun p =>
      if p.1 ∣ h then {(1 : Fin 3)} else Finset.univ
    let P : Finset (q.primeFactors → Fin 3) := Fintype.piFinset allowed
    let val : (p : q.primeFactors) → Fin 3 → ℝ := fun p c =>
      if c = (2 : Fin 3) then ((1 : ℝ) / ((p.1 : ℝ) - 1)) ^ 2 else (1 : ℝ) / ((p.1 : ℝ) - 1)
    have hcode_maps : ∀ ab ∈ F, code ab ∈ P := by
      intro ab hab
      obtain ⟨habP, _⟩ := Finset.mem_filter.mp hab
      obtain ⟨ha, _⟩ := Finset.mem_product.mp habP
      obtain ⟨_, _, hacop⟩ := Finset.mem_filter.mp ha
      refine Fintype.mem_piFinset.mpr fun p => ?_
      dsimp only [allowed, code]
      split_ifs with hph hpa hpb
      · exfalso
        have hp_pr := Nat.prime_of_mem_primeFactors p.2
        have hg : p.1 ∣ Nat.gcd ab.1 h := Nat.dvd_gcd hpa hph
        rw [hacop.gcd_eq_one] at hg
        exact hp_pr.ne_one (Nat.dvd_one.mp hg)
      · exfalso
        have hp_pr := Nat.prime_of_mem_primeFactors p.2
        have hg : p.1 ∣ Nat.gcd ab.1 h := Nat.dvd_gcd hpa hph
        rw [hacop.gcd_eq_one] at hg
        exact hp_pr.ne_one (Nat.dvd_one.mp hg)
      · exact Finset.mem_singleton_self 1
      · exact Finset.mem_univ _
      · exact Finset.mem_univ _
      · exact Finset.mem_univ _
    have hcode_inj : Set.InjOn code (F : Set (ℕ × ℕ)) := by
      intro ab₁ h₁ ab₂ h₂ heq
      obtain ⟨hP₁, hlcm₁⟩ := Finset.mem_filter.mp h₁
      obtain ⟨hP₂, hlcm₂⟩ := Finset.mem_filter.mp h₂
      obtain ⟨ha₁, hb₁⟩ := Finset.mem_product.mp hP₁
      obtain ⟨ha₂, hb₂⟩ := Finset.mem_product.mp hP₂
      have hasqf₁ : Squarefree ab₁.1 := (Finset.mem_filter.mp ha₁).2.1
      have hbsqf₁ : Squarefree ab₁.2 := (Finset.mem_filter.mp hb₁).2
      have hasqf₂ : Squarefree ab₂.1 := (Finset.mem_filter.mp ha₂).2.1
      have hbsqf₂ : Squarefree ab₂.2 := (Finset.mem_filter.mp hb₂).2
      have hpf_q₁ : q.primeFactors = ab₁.1.primeFactors ∪ ab₁.2.primeFactors := by
        rw [← hlcm₁]; exact primeFactors_lcm hasqf₁.ne_zero hbsqf₁.ne_zero
      have hpf_q₂ : q.primeFactors = ab₂.1.primeFactors ∪ ab₂.2.primeFactors := by
        rw [← hlcm₂]; exact primeFactors_lcm hasqf₂.ne_zero hbsqf₂.ne_zero
      have hpf1_eq : ab₁.1.primeFactors = ab₂.1.primeFactors := by
        ext p
        constructor
        · intro hp1
          have hpq : p ∈ q.primeFactors := by rw [hpf_q₁]; exact Finset.mem_union_left _ hp1
          have hfp := congrFun heq ⟨p, hpq⟩
          have hp_pr : p.Prime := Nat.prime_of_mem_primeFactors hp1
          have hpa₁ : p ∣ ab₁.1 := Nat.dvd_of_mem_primeFactors hp1
          have hpa₂ : p ∣ ab₂.1 := by
            by_contra hnot
            dsimp only [code] at hfp
            rw [if_pos hpa₁, if_neg hnot] at hfp
            split_ifs at hfp <;> cases hfp
          exact Nat.mem_primeFactors.mpr ⟨hp_pr, hpa₂, hasqf₂.ne_zero⟩
        · intro hp2
          have hpq : p ∈ q.primeFactors := by rw [hpf_q₂]; exact Finset.mem_union_left _ hp2
          have hfp := congrFun heq ⟨p, hpq⟩
          have hp_pr : p.Prime := Nat.prime_of_mem_primeFactors hp2
          have hpa₂ : p ∣ ab₂.1 := Nat.dvd_of_mem_primeFactors hp2
          have hpa₁ : p ∣ ab₁.1 := by
            by_contra hnot
            dsimp only [code] at hfp
            rw [if_neg hnot, if_pos hpa₂] at hfp
            split_ifs at hfp <;> cases hfp
          exact Nat.mem_primeFactors.mpr ⟨hp_pr, hpa₁, hasqf₁.ne_zero⟩
      have hpf2_eq : ab₁.2.primeFactors = ab₂.2.primeFactors := by
        ext p
        constructor
        · intro hp1
          have hpq : p ∈ q.primeFactors := by rw [hpf_q₁]; exact Finset.mem_union_right _ hp1
          have hfp := congrFun heq ⟨p, hpq⟩
          have hp_pr : p.Prime := Nat.prime_of_mem_primeFactors hp1
          have hpb₁ : p ∣ ab₁.2 := Nat.dvd_of_mem_primeFactors hp1
          have hpb₂ : p ∣ ab₂.2 := by
            by_contra hnot
            have hpq2 : p ∈ ab₂.1.primeFactors ∪ ab₂.2.primeFactors := hpf_q₂ ▸ hpq
            have hpa₂ : p ∣ ab₂.1 := by
              rcases Finset.mem_union.mp hpq2 with h | h
              · exact Nat.dvd_of_mem_primeFactors h
              · exact absurd (Nat.dvd_of_mem_primeFactors h) hnot
            dsimp only [code] at hfp
            rw [if_pos hpa₂, if_neg hnot] at hfp
            split_ifs at hfp <;> simp_all
          exact Nat.mem_primeFactors.mpr ⟨hp_pr, hpb₂, hbsqf₂.ne_zero⟩
        · intro hp2
          have hpq : p ∈ q.primeFactors := by rw [hpf_q₂]; exact Finset.mem_union_right _ hp2
          have hfp := congrFun heq ⟨p, hpq⟩
          have hp_pr : p.Prime := Nat.prime_of_mem_primeFactors hp2
          have hpb₂ : p ∣ ab₂.2 := Nat.dvd_of_mem_primeFactors hp2
          have hpb₁ : p ∣ ab₁.2 := by
            by_contra hnot
            have hpq1 : p ∈ ab₁.1.primeFactors ∪ ab₁.2.primeFactors := hpf_q₁ ▸ hpq
            have hpa₁ : p ∣ ab₁.1 := by
              rcases Finset.mem_union.mp hpq1 with h | h
              · exact Nat.dvd_of_mem_primeFactors h
              · exact absurd (Nat.dvd_of_mem_primeFactors h) hnot
            dsimp only [code] at hfp
            rw [if_pos hpa₁, if_neg hnot] at hfp
            split_ifs at hfp <;> simp_all
          exact Nat.mem_primeFactors.mpr ⟨hp_pr, hpb₁, hbsqf₁.ne_zero⟩
      have heq1 : ab₁.1 = ab₂.1 := by
        rw [← Nat.prod_primeFactors_of_squarefree hasqf₁,
          ← Nat.prod_primeFactors_of_squarefree hasqf₂, hpf1_eq]
      have heq2 : ab₁.2 = ab₂.2 := by
        rw [← Nat.prod_primeFactors_of_squarefree hbsqf₁,
          ← Nat.prod_primeFactors_of_squarefree hbsqf₂, hpf2_eq]
      exact Prod.ext heq1 heq2
    have hterm : ∀ ab ∈ F,
        ((1 : ℝ) / (ab.1.totient : ℝ)) * ((1 : ℝ) / (ab.2.totient : ℝ)) =
          ∏ p : q.primeFactors, val p (code ab p) := by
      intro ab hab
      obtain ⟨hP, hlcm⟩ := Finset.mem_filter.mp hab
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hP
      have hasqf : Squarefree ab.1 := (Finset.mem_filter.mp ha).2.1
      have hbsqf : Squarefree ab.2 := (Finset.mem_filter.mp hb).2
      have hpf_q : q.primeFactors = ab.1.primeFactors ∪ ab.2.primeFactors := by
        rw [← hlcm]; exact primeFactors_lcm hasqf.ne_zero hbsqf.ne_zero
      have hsub1 : ab.1.primeFactors ⊆ q.primeFactors := by
        rw [hpf_q]; exact Finset.subset_union_left
      have hsub2 : ab.2.primeFactors ⊆ q.primeFactors := by
        rw [hpf_q]; exact Finset.subset_union_right
      have htot1 : (1 : ℝ) / (ab.1.totient : ℝ) =
          ∏ p ∈ q.primeFactors, if p ∣ ab.1 then (1 : ℝ) / ((p : ℝ) - 1) else 1 := by
        rw [← Finset.prod_filter]
        have hfilt : q.primeFactors.filter (fun p => p ∣ ab.1) = ab.1.primeFactors := by
          ext p
          simp only [Finset.mem_filter, Nat.mem_primeFactors]
          constructor
          · rintro ⟨⟨hp, _, _⟩, hpa⟩; exact ⟨hp, hpa, hasqf.ne_zero⟩
          · intro hp1
            exact ⟨Nat.mem_primeFactors.mp (hsub1 (Nat.mem_primeFactors.mpr hp1)), hp1.2.1⟩
        rw [hfilt, Stage7SieveMethods.totient_eq_prod_sub_one_of_squarefree hasqf,
          Nat.cast_prod, one_div, ← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl fun p hp => ?_
        have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
        rw [Nat.cast_sub hp1, Nat.cast_one, one_div]
      have htot2 : (1 : ℝ) / (ab.2.totient : ℝ) =
          ∏ p ∈ q.primeFactors, if p ∣ ab.2 then (1 : ℝ) / ((p : ℝ) - 1) else 1 := by
        rw [← Finset.prod_filter]
        have hfilt : q.primeFactors.filter (fun p => p ∣ ab.2) = ab.2.primeFactors := by
          ext p
          simp only [Finset.mem_filter, Nat.mem_primeFactors]
          constructor
          · rintro ⟨⟨hp, _, _⟩, hpb⟩; exact ⟨hp, hpb, hbsqf.ne_zero⟩
          · intro hp2
            exact ⟨Nat.mem_primeFactors.mp (hsub2 (Nat.mem_primeFactors.mpr hp2)), hp2.2.1⟩
        rw [hfilt, Stage7SieveMethods.totient_eq_prod_sub_one_of_squarefree hbsqf,
          Nat.cast_prod, one_div, ← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl fun p hp => ?_
        have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
        rw [Nat.cast_sub hp1, Nat.cast_one, one_div]
      rw [htot1, htot2, ← Finset.prod_mul_distrib, ← Finset.prod_attach]
      refine Finset.prod_congr rfl fun p _ => ?_
      have hp_or : p.1 ∣ ab.1 ∨ p.1 ∣ ab.2 := by
        have hmem : p.1 ∈ ab.1.primeFactors ∪ ab.2.primeFactors := hpf_q ▸ p.2
        rcases Finset.mem_union.mp hmem with h | h
        · exact Or.inl (Nat.dvd_of_mem_primeFactors h)
        · exact Or.inr (Nat.dvd_of_mem_primeFactors h)
      dsimp only [val, code]
      by_cases h1 : p.1 ∣ ab.1
      · by_cases h2 : p.1 ∣ ab.2
        · simp [h1, h2, sq]
        · simp [h1, h2]
      · have h2 : p.1 ∣ ab.2 := hp_or.resolve_left h1
        simp [h1, h2]
    have hval_nn : ∀ p : q.primeFactors, ∀ c : Fin 3, 0 ≤ val p c := by
      intro p c
      have hp1 : (1 : ℝ) < (p.1 : ℝ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors p.2).one_lt
      dsimp only [val]
      split_ifs <;> positivity
    calc ∑ ab ∈ F, ((1 : ℝ) / (ab.1.totient : ℝ)) * ((1 : ℝ) / (ab.2.totient : ℝ))
        = ∑ ab ∈ F, ∏ p : q.primeFactors, val p (code ab p) :=
          Finset.sum_congr rfl hterm
      _ = ∑ f ∈ F.image code, ∏ p : q.primeFactors, val p (f p) :=
          (Finset.sum_image (f := fun f : q.primeFactors → Fin 3 =>
            ∏ p : q.primeFactors, val p (f p)) hcode_inj).symm
      _ ≤ ∑ f ∈ P, ∏ p : q.primeFactors, val p (f p) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hcode_maps)
            fun _ _ _ => Finset.prod_nonneg fun p _ => hval_nn p _
      _ = ∏ p : q.primeFactors, ∑ c ∈ allowed p, val p c :=
          (Finset.prod_univ_sum (t := allowed) (f := val)).symm
      _ ≤ ∏ p : q.primeFactors, (w p.1 : ℝ) / ((p.1 : ℝ) - (w p.1 : ℝ)) := by
          refine Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun c _ => hval_nn p c) fun p _ => ?_
          have hp_pr : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
          dsimp only [allowed, w]
          by_cases hph : p.1 ∣ h
          · rw [if_pos hph, if_pos hph, Finset.sum_singleton]
            simp [val]
          · rw [if_neg hph, if_neg hph]
            have hp_ne2 : p.1 ≠ 2 := fun h2 => hph (h2 ▸ h2dvd)
            have hp3 : 3 ≤ p.1 := by
              have := hp_pr.two_le; omega
            have hsum3 : ∑ c : Fin 3, val p c =
                (1 : ℝ) / ((p.1 : ℝ) - 1) + (1 : ℝ) / ((p.1 : ℝ) - 1) +
                  ((1 : ℝ) / ((p.1 : ℝ) - 1)) ^ 2 := by
              rw [Fin.sum_univ_three]
              simp [val]
            rw [hsum3, Nat.cast_ofNat]
            exact odd_prime_sieve_fiber_le hp3
      _ = Stage7SieveMethods.sieveWeight w q := by
          unfold Stage7SieveMethods.sieveWeight
          rw [if_pos hqsqf]
          exact Finset.prod_coe_sort q.primeFactors (fun p => (w p : ℝ) / ((p : ℝ) - (w p : ℝ)))
  -- Step 4: Combine everything into `montgomeryL w Q`
  have hsum_le : ∑ q ∈ T, Stage7SieveMethods.sieveWeight w q =
      Stage7SieveMethods.montgomeryL w Q := by
    unfold Stage7SieveMethods.montgomeryL
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    unfold Stage7SieveMethods.sieveWeight
    by_cases hsqf : Squarefree q <;> simp [hsqf]
  calc ((h.totient : ℝ) / (h : ℝ)) * (Real.log ((R : ℝ) + 1)) ^ 2
      ≤ (∑ n₁ ∈ S₁, (1 : ℝ) / (n₁.totient : ℝ)) * (∑ n₂ ∈ S₂, (1 : ℝ) / (n₂.totient : ℝ)) := hprod_ge
    _ = ∑ q ∈ T, ∑ ab ∈ (S₁ ×ˢ S₂).filter (fun ab => Nat.lcm ab.1 ab.2 = q),
          ((1 : ℝ) / (ab.1.totient : ℝ)) * ((1 : ℝ) / (ab.2.totient : ℝ)) := hprod_eq
    _ ≤ ∑ q ∈ T, Stage7SieveMethods.sieveWeight w q := Finset.sum_le_sum hfiber_le
    _ = Stage7SieveMethods.montgomeryL w Q := hsum_le

/-- For every even `h ≥ 2`, `h / φ(h) ≤ 2 * ∏_{p ∣ h, p > 2} (p - 1)/(p - 2)`. -/
theorem div_totient_le_two_mul_odd_singular_factor {h : ℕ} (hh : 2 ≤ h) (heven : Even h) :
    (h : ℝ) / (h.totient : ℝ) ≤
      2 * ∏ p ∈ h.primeFactors.filter (fun p => 2 < p), ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  have hhpos : 0 < h := by omega
  have h2mem : 2 ∈ h.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, even_iff_two_dvd.mp heven, by omega⟩
  have htot_rat : (h.totient : ℚ) = (h : ℚ) * ∏ p ∈ h.primeFactors, (1 - (p : ℚ)⁻¹) :=
    Nat.totient_eq_mul_prod_factors h
  have htot_real : (h.totient : ℝ) =
      (h : ℝ) * ∏ p ∈ h.primeFactors, (((p : ℝ) - 1) / (p : ℝ)) := by
    have hcast := congrArg (fun r : ℚ => (r : ℝ)) htot_rat
    push_cast at hcast
    rw [hcast]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
    field_simp [hp0]
  have htot_pos : (0 : ℝ) < (h.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hhpos)
  have hratio : (h : ℝ) / (h.totient : ℝ) =
      ∏ p ∈ h.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
    rw [div_eq_iff htot_pos.ne', htot_real, mul_left_comm, ← Finset.prod_mul_distrib]
    have hone : ∏ p ∈ h.primeFactors, ((p : ℝ) / ((p : ℝ) - 1) * (((p : ℝ) - 1) / (p : ℝ))) = 1 := by
      refine Finset.prod_eq_one fun p hp => ?_
      have hp1 : (1 : ℝ) < (p : ℝ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
      field_simp [(by linarith : (p : ℝ) - 1 ≠ 0), (by linarith : (p : ℝ) ≠ 0)]
    rw [hone, mul_one]
  rw [hratio, ← Finset.mul_prod_erase h.primeFactors _ h2mem]
  have h2fac : ((2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) - 1) = 2 := by norm_num
  rw [h2fac]
  have herase : h.primeFactors.erase 2 = h.primeFactors.filter (fun p => 2 < p) := by
    ext p
    simp only [Finset.mem_erase, Finset.mem_filter]
    constructor
    · rintro ⟨hne, hp⟩
      have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
      exact ⟨hp, by omega⟩
    · rintro ⟨hp, hgt⟩
      exact ⟨by omega, hp⟩
  rw [herase]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
  · have hp2 : (2 : ℝ) < (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2
    exact div_nonneg (by linarith) (by linarith)
  · have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
      have : 2 < p := (Finset.mem_filter.mp hp).2
      exact_mod_cast (by omega : 3 ≤ p)
    have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have h2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    rw [div_le_div_iff₀ h1 h2]
    nlinarith

/-- Elementary inequality: for every `x ≥ 3`, `√x ≤ 16 * x / (log x)²`. -/
private theorem sqrt_le_sixteen_mul_div_log_sq {x : ℝ} (hx : 3 ≤ x) :
    Real.sqrt x ≤ 16 * x / (Real.log x) ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog_rpow : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 4)
    linarith [show x ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) = 4 * x ^ (1 / 4 : ℝ) by ring]
  have hsq : (Real.log x) ^ 2 ≤ 16 * Real.sqrt x := by
    have h1 : (Real.log x) ^ 2 ≤ (4 * x ^ (1 / 4 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hLx_pos.le hlog_rpow 2
    have h2 : (4 * x ^ (1 / 4 : ℝ)) ^ 2 = 16 * Real.sqrt x := by
      rw [mul_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast (x ^ (1 / 4 : ℝ)) 2,
        ← Real.rpow_mul hx0.le]
      norm_num
    linarith
  rw [le_div_iff₀ (sq_pos_of_pos hLx_pos)]
  calc Real.sqrt x * (Real.log x) ^ 2
      ≤ Real.sqrt x * (16 * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg x)
    _ = 16 * (Real.sqrt x * Real.sqrt x) := by ring
    _ = 16 * x := by rw [Real.mul_self_sqrt hx0.le]

/-- **UNCONDITIONAL GENERAL `2k`-GAP PRIME-PAIR UPPER BOUND (0 ASSUMPTIONS!)**:
there is an absolute constant `C > 0` (independent of `h` and `x`) such that for EVERY even
`h ≥ 2` and EVERY `x ≥ 3`:
`#{p ≤ x : p prime, p + h prime} ≤ C * (∏_{p ∣ h, p > 2} (p - 1)/(p - 2)) * x / (log x)²`. -/
theorem prime_pair_upper_bound_selberg :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℕ, 2 ≤ h → Even h → ∀ x : ℝ, 3 ≤ x →
      (((Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ (p + h).Prime)).card : ℝ) ≤
        C * (∏ p ∈ h.primeFactors.filter (fun p => 2 < p), ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
          x / (Real.log x) ^ 2 := by
  refine ⟨160, by norm_num, fun h hh heven x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  set N : ℕ := ⌊x⌋₊
  have hN3 : 3 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  set Q : ℕ := Nat.sqrt N
  have hQ1 : 1 ≤ Q := Nat.sqrt_pos.mpr (by omega)
  set R : ℕ := Nat.sqrt Q
  have hR1 : 1 ≤ R := Nat.sqrt_pos.mpr hQ1
  -- Show `Real.log x ≤ 4 * Real.log (R + 1)`
  have hx_lt_R4 : x ≤ ((R : ℝ) + 1) ^ 4 := by
    have hNQ : N + 1 ≤ (Q + 1) ^ 2 := by
      have h := Nat.lt_succ_sqrt N
      nlinarith
    have hQR : Q + 1 ≤ (R + 1) ^ 2 := by
      have h := Nat.lt_succ_sqrt Q
      nlinarith
    have hxN : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
    have h1 : (N : ℝ) + 1 ≤ ((Q : ℝ) + 1) ^ 2 := by exact_mod_cast hNQ
    have h2 : (Q : ℝ) + 1 ≤ ((R : ℝ) + 1) ^ 2 := by exact_mod_cast hQR
    have h3 : ((Q : ℝ) + 1) ^ 2 ≤ (((R : ℝ) + 1) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    nlinarith [show (((R : ℝ) + 1) ^ 2) ^ 2 = ((R : ℝ) + 1) ^ 4 by ring]
  have hlogR_pos : 0 < Real.log ((R : ℝ) + 1) := by
    apply Real.log_pos
    have : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1
    linarith
  have hlogx_le : Real.log x ≤ 4 * Real.log ((R : ℝ) + 1) := by
    have h1 : Real.log x ≤ Real.log (((R : ℝ) + 1) ^ 4) := Real.log_le_log hx0 hx_lt_R4
    rw [Real.log_pow] at h1
    simpa using h1
  -- Split primes `P = A ∪ B` at threshold `Q`
  set P : Finset ℕ := (Finset.Icc 1 N).filter (fun p => p.Prime ∧ (p + h).Prime)
  set A : Finset ℕ := P.filter (fun p => Q < p)
  set B : Finset ℕ := P.filter (fun p => p ≤ Q)
  have hsplit : P.card = A.card + B.card := by
    have hdisj : Disjoint A B := Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
    have hunion : A ∪ B = P := by
      ext p; simp only [A, B, Finset.mem_union, Finset.mem_filter]; constructor
      · rintro (h | h) <;> exact h.1
      · intro hp; by_cases hc : Q < p <;> [left; right] <;> exact ⟨hp, by omega⟩
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  -- Bound `B.card ≤ Q ≤ √x ≤ 16 * x / (log x)²`
  have hB_le : (B.card : ℝ) ≤ 16 * x / (Real.log x) ^ 2 := by
    have hB_Q : B.card ≤ Q := by
      have hsub : B ⊆ Finset.Icc 1 Q := by
        intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hpr := (Finset.mem_filter.mp hp'.1).2.1
        exact Finset.mem_Icc.mpr ⟨hpr.pos, hp'.2⟩
      exact (Finset.card_le_card hsub).trans (by rw [Nat.card_Icc]; omega)
    have hQ_sqrt : (Q : ℝ) ≤ Real.sqrt x := by
      rw [Real.le_sqrt (Nat.cast_nonneg Q) hx0.le]
      have hsq : Q * Q ≤ N := Nat.sqrt_le N
      have hNle : (N : ℝ) ≤ x := Nat.floor_le hx0.le
      have hsqR : (Q : ℝ) ^ 2 ≤ (N : ℝ) := by
        rw [sq]; exact_mod_cast hsq
      linarith
    exact ((by exact_mod_cast hB_Q : (B.card : ℝ) ≤ (Q : ℝ)).trans hQ_sqrt).trans
      (sqrt_le_sixteen_mul_div_log_sq hx)
  -- Apply Montgomery's arithmetic large sieve to `A`
  let w : ℕ → ℕ := fun p => if p ∣ h then 1 else 2
  have h2dvd : 2 ∣ h := even_iff_two_dvd.mp heven
  have hA_sub : A ⊆ Finset.Icc (0 + 1) (0 + N) := by
    intro p hp
    have hmem := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
    simpa using hmem
  have hAvoid : ∀ p : ℕ, p.Prime → p ≤ Q →
      w p < p ∧ ∃ SΩ : Finset (ZMod p), SΩ.card = w p ∧ ∀ n ∈ A, (n : ZMod p) ∉ SΩ := by
    intro p hp hpQ
    dsimp only [w]
    by_cases hph : p ∣ h
    · rw [if_pos hph]
      refine ⟨hp.one_lt, {0}, Finset.card_singleton 0, fun n hn hmem => ?_⟩
      have h0 : (n : ZMod p) = 0 := Finset.mem_singleton.mp hmem
      have hdvd : p ∣ n := (ZMod.natCast_eq_zero_iff n p).mp h0
      have hn_pr : n.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2.1
      have hn_gt : Q < n := (Finset.mem_filter.mp hn).2
      have heq : p = n := (Nat.prime_dvd_prime_iff_eq hp hn_pr).mp hdvd
      omega
    · rw [if_neg hph]
      have hp_ne2 : p ≠ 2 := fun h2 => hph (h2 ▸ h2dvd)
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have hneg_ne : -(h : ZMod p) ≠ 0 := by
        intro h0
        have : (h : ZMod p) = 0 := neg_eq_zero.mp h0
        exact hph ((ZMod.natCast_eq_zero_iff h p).mp this)
      refine ⟨by omega, {0, -(h : ZMod p)}, Finset.card_pair hneg_ne.symm, fun n hn hmem => ?_⟩
      have hn_pair := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
      have hn_gt : Q < n := (Finset.mem_filter.mp hn).2
      rcases Finset.mem_insert.mp hmem with h0 | hneg
      · have hdvd : p ∣ n := (ZMod.natCast_eq_zero_iff n p).mp h0
        have heq : p = n := (Nat.prime_dvd_prime_iff_eq hp hn_pair.1).mp hdvd
        omega
      · have heqZ : (n : ZMod p) = -(h : ZMod p) := Finset.mem_singleton.mp hneg
        have hsum0 : ((n + h : ℕ) : ZMod p) = 0 := by
          rw [Nat.cast_add, heqZ, neg_add_cancel]
        have hdvd : p ∣ n + h := (ZMod.natCast_eq_zero_iff (n + h) p).mp hsum0
        have heq : p = n + h := (Nat.prime_dvd_prime_iff_eq hp hn_pair.2).mp hdvd
        omega
  have hMS := Stage7SieveMethods.montgomery_arithmetic_large_sieve_Icc hA_sub w hAvoid
  have hL_ge := montgomeryL_prime_pair_ge hh heven Q
  have htot_pos : (0 : ℝ) < (h.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
  have hh_pos : (0 : ℝ) < (h : ℝ) := by positivity
  have hL_ge_logx : ((h.totient : ℝ) / (h : ℝ)) * ((Real.log x) ^ 2 / 16) ≤
      Stage7SieveMethods.montgomeryL w Q := by
    have hsq : (Real.log x) ^ 2 / 16 ≤ (Real.log ((R : ℝ) + 1)) ^ 2 := by
      have h1 : (Real.log x) ^ 2 ≤ (4 * Real.log ((R : ℝ) + 1)) ^ 2 :=
        pow_le_pow_left₀ hLx_pos.le hlogx_le 2
      linarith
    exact (mul_le_mul_of_nonneg_left hsq (div_nonneg htot_pos.le hh_pos.le)).trans hL_ge
  have hRHS_le : (N : ℝ) + 3 * (Q : ℝ) ^ 2 ≤ 4 * x := by
    have hNle : (N : ℝ) ≤ x := Nat.floor_le hx0.le
    have hQsq : (Q : ℝ) ^ 2 ≤ (N : ℝ) := by
      rw [sq]; exact_mod_cast Nat.sqrt_le N
    linarith
  have hA_le : (A.card : ℝ) ≤ 64 * ((h : ℝ) / (h.totient : ℝ)) * x / (Real.log x) ^ 2 := by
    have hden_pos : 0 < ((h.totient : ℝ) / (h : ℝ)) * ((Real.log x) ^ 2 / 16) := by positivity
    have hmul : (A.card : ℝ) * (((h.totient : ℝ) / (h : ℝ)) * ((Real.log x) ^ 2 / 16)) ≤ 4 * x :=
      ((mul_le_mul_of_nonneg_left hL_ge_logx (Nat.cast_nonneg _)).trans hMS).trans hRHS_le
    rw [le_div_iff₀ (sq_pos_of_pos hLx_pos)]
    have h2 := mul_le_mul_of_nonneg_right hmul (show 0 ≤ 16 * ((h : ℝ) / (h.totient : ℝ)) by positivity)
    have hsimpl : (A.card : ℝ) * (((h.totient : ℝ) / (h : ℝ)) * ((Real.log x) ^ 2 / 16)) *
        (16 * ((h : ℝ) / (h.totient : ℝ))) = (A.card : ℝ) * (Real.log x) ^ 2 := by
      field_simp [htot_pos.ne', hh_pos.ne']
    rw [hsimpl] at h2
    linarith
  -- Combine `A` and `B`, then bound `h / φ(h) ≤ 2 * ∏_{p ∣ h, p > 2} (p - 1)/(p - 2)`
  have hone_le_ratio : (1 : ℝ) ≤ (h : ℝ) / (h.totient : ℝ) := by
    rw [one_le_div htot_pos]
    exact_mod_cast Nat.totient_le h
  have hB_le' : (B.card : ℝ) ≤ 16 * ((h : ℝ) / (h.totient : ℝ)) * x / (Real.log x) ^ 2 := by
    have h1 : 16 * x ≤ 16 * ((h : ℝ) / (h.totient : ℝ)) * x := by nlinarith
    exact hB_le.trans (div_le_div_of_nonneg_right h1 (sq_nonneg _))
  have hP_le : (P.card : ℝ) ≤ 80 * ((h : ℝ) / (h.totient : ℝ)) * x / (Real.log x) ^ 2 := by
    rw [hsplit, Nat.cast_add]
    linarith [show 64 * ((h : ℝ) / (h.totient : ℝ)) * x / (Real.log x) ^ 2 +
        16 * ((h : ℝ) / (h.totient : ℝ)) * x / (Real.log x) ^ 2 =
      80 * ((h : ℝ) / (h.totient : ℝ)) * x / (Real.log x) ^ 2 by ring]
  have hsing := div_totient_le_two_mul_odd_singular_factor hh heven
  calc (P.card : ℝ)
      ≤ 80 * ((h : ℝ) / (h.totient : ℝ)) * x / (Real.log x) ^ 2 := hP_le
    _ ≤ 80 * (2 * ∏ p ∈ h.primeFactors.filter (fun p => 2 < p), ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
          x / (Real.log x) ^ 2 := by
        gcongr
    _ = 160 * (∏ p ∈ h.primeFactors.filter (fun p => 2 < p), ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
          x / (Real.log x) ^ 2 := by ring

/-- **UNCONDITIONAL BRUN'S TWIN-PRIME UPPER BOUND (`π₂(x) ≤ C x / (log x)²`, 0 ASSUMPTIONS!)**. -/
theorem twin_prime_upper_bound_selberg :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
      (twinPrimeCounting x : ℝ) ≤ C * x / (Real.log x) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := prime_pair_upper_bound_selberg
  refine ⟨C, hC, fun x hx => ?_⟩
  have h2 := hbound 2 le_rfl even_two x hx
  have hfilt : (2 : ℕ).primeFactors.filter (fun p => 2 < p) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro p hp
    have hdvd : p ∣ 2 := Nat.dvd_of_mem_primeFactors hp
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  rw [hfilt, Finset.prod_empty, mul_one] at h2
  exact h2

private theorem sum_inv_sub_inv_succ_Ico_two {K : ℕ} (hK : 2 ≤ K) :
    ∑ k ∈ Finset.Ico 2 K, ((k : ℝ)⁻¹ - ((k + 1 : ℕ) : ℝ)⁻¹) = ((2 : ℕ) : ℝ)⁻¹ - (K : ℝ)⁻¹ := by
  induction K, hK using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Ico_succ_top hm, ih]
    ring

/-- Elementary telescoping bound: `∑_{k ∈ Ico 2 K} 1 / (k + 1)² ≤ 1 / 2`. -/
private theorem sum_inv_succ_sq_Ico_two_le (K : ℕ) :
    ∑ k ∈ Finset.Ico 2 K, ((k + 1 : ℕ) : ℝ)⁻¹ ^ 2 ≤ 1 / 2 := by
  have hle : ∀ k ∈ Finset.Ico 2 K,
      ((k + 1 : ℕ) : ℝ)⁻¹ ^ 2 ≤ (k : ℝ)⁻¹ - ((k + 1 : ℕ) : ℝ)⁻¹ := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
    have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
    have hk1pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hdiff : (k : ℝ)⁻¹ - ((k + 1 : ℕ) : ℝ)⁻¹ =
        ((k : ℝ) * ((k + 1 : ℕ) : ℝ))⁻¹ := by
      push_cast
      field_simp [hkpos.ne', (by positivity : (k : ℝ) + 1 ≠ 0)]
      ring
    rw [hdiff, sq, ← mul_inv]
    refine inv_anti₀ (mul_pos hkpos hk1pos) ?_
    have hlt : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact mul_le_mul_of_nonneg_right hlt hk1pos.le
  calc ∑ k ∈ Finset.Ico 2 K, ((k + 1 : ℕ) : ℝ)⁻¹ ^ 2
      ≤ ∑ k ∈ Finset.Ico 2 K, ((k : ℝ)⁻¹ - ((k + 1 : ℕ) : ℝ)⁻¹) :=
        Finset.sum_le_sum hle
    _ ≤ 1 / 2 := by
        by_cases hK : 2 ≤ K
        · rw [sum_inv_sub_inv_succ_Ico_two hK]
          have hKnn : (0 : ℝ) ≤ (K : ℝ)⁻¹ := by positivity
          norm_num
        · have hempty : Finset.Ico 2 K = ∅ := Finset.Ico_eq_empty_of_le (by omega)
          rw [hempty, Finset.sum_empty]
          norm_num

/-- **UNCONDITIONAL GENERALIZED BRUN CONVERGENCE THEOREM (`0` ASSUMPTIONS!)**:
for EVERY even shift `h ≥ 2`, `∑_{p, p+h prime} 1/p < ∞`. -/
theorem summable_prime_pair_reciprocals {h : ℕ} (hh : 2 ≤ h) (heven : Even h) :
    Summable (fun p : ℕ => if p.Prime ∧ (p + h).Prime then (p : ℝ)⁻¹ else 0) := by
  obtain ⟨C₀, hC₀, hbound⟩ := prime_pair_upper_bound_selberg
  set S_h : ℝ := ∏ p ∈ h.primeFactors.filter (fun p => 2 < p), ((p : ℝ) - 1) / ((p : ℝ) - 2)
  have hS_nn : 0 ≤ S_h := Finset.prod_nonneg fun p hp => by
    have hp2 : (2 : ℝ) < (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2
    exact div_nonneg (by linarith) (by linarith)
  set C : ℝ := C₀ * S_h
  have hC_nn : 0 ≤ C := mul_nonneg hC₀.le hS_nn
  let f : ℕ → ℝ := fun p => if p.Prime ∧ (p + h).Prime then (p : ℝ)⁻¹ else 0
  have hf_nn : ∀ p, 0 ≤ f p := fun p => by dsimp only [f]; split_ifs <;> positivity
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine summable_of_sum_range_le hf_nn (c := 4 + C / (Real.log 2) ^ 2) fun N => ?_
  set K : ℕ := N + 2
  have hN_le : N ≤ 2 ^ K := le_trans (by omega : N ≤ K) (Nat.lt_two_pow_self).le
  have hsub_range : Finset.range N ⊆ Finset.range (2 ^ K) := Finset.range_mono hN_le
  -- Dyadic partition of `Finset.range (2 ^ K)` into `range 4` and `Ico (2^k) (2^(k+1))` (`2 ≤ k < K`)
  have hdyadic : ∀ M : ℕ, 2 ≤ M →
      ∑ p ∈ Finset.range (2 ^ M), f p =
        (∑ p ∈ Finset.range 4, f p) +
        ∑ k ∈ Finset.Ico 2 M, ∑ p ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), f p := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      rw [Finset.sum_Ico_succ_top hm, ← add_assoc, ← ih]
      have hle : 2 ^ m ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ m)
      have hsplit : Finset.range (2 ^ (m + 1)) =
          Finset.range (2 ^ m) ∪ Finset.Ico (2 ^ m) (2 ^ (m + 1)) := by
        ext p; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
      have hdisj : Disjoint (Finset.range (2 ^ m)) (Finset.Ico (2 ^ m) (2 ^ (m + 1))) := by
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        simp only [Finset.mem_range, Finset.mem_Ico] at hp1 hp2
        omega
      rw [hsplit, Finset.sum_union hdisj]
  have hsmall : ∑ p ∈ Finset.range 4, f p ≤ 4 := by
    calc ∑ p ∈ Finset.range 4, f p
        ≤ ∑ _p ∈ Finset.range 4, (1 : ℝ) := by
          refine Finset.sum_le_sum fun p _ => ?_
          dsimp only [f]
          split_ifs with hp
          · exact inv_le_one_of_one_le₀ (by exact_mod_cast hp.1.one_lt.le)
          · exact zero_le_one
      _ = 4 := by simp
  have hblock : ∀ k ∈ Finset.Ico 2 K,
      ∑ p ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), f p ≤
        (2 * C / (Real.log 2) ^ 2) * ((k + 1 : ℕ) : ℝ)⁻¹ ^ 2 := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
    have h2k_pos : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
    have h2k1_ge3 : (3 : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by
      have : 8 ≤ 2 ^ (k + 1) := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact_mod_cast (by omega : 3 ≤ 2 ^ (k + 1))
    set B_k : Finset ℕ := (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter (fun p => p.Prime ∧ (p + h).Prime)
    have hsum_Bk : ∑ p ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), f p ≤
        (B_k.card : ℝ) * ((2 ^ k : ℕ) : ℝ)⁻¹ := by
      dsimp only [f]
      rw [← Finset.sum_filter]
      calc ∑ p ∈ B_k, (p : ℝ)⁻¹
          ≤ ∑ _p ∈ B_k, ((2 ^ k : ℕ) : ℝ)⁻¹ := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hge : 2 ^ k ≤ p := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
            exact inv_anti₀ h2k_pos (by exact_mod_cast hge)
        _ = (B_k.card : ℝ) * ((2 ^ k : ℕ) : ℝ)⁻¹ := by simp
    have hBk_sub : B_k ⊆ (Finset.Icc 1 ⌊((2 ^ (k + 1) : ℕ) : ℝ)⌋₊).filter
        (fun p => p.Prime ∧ (p + h).Prime) := by
      intro p hp
      obtain ⟨hpI, hpair⟩ := Finset.mem_filter.mp hp
      obtain ⟨hge, hlt⟩ := Finset.mem_Ico.mp hpI
      rw [Nat.floor_natCast]
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpair.1.pos, hlt.le⟩, hpair⟩
    have hcard_bd : (B_k.card : ℝ) ≤
        C * ((2 ^ (k + 1) : ℕ) : ℝ) / (Real.log ((2 ^ (k + 1) : ℕ) : ℝ)) ^ 2 := by
      have h1 : (B_k.card : ℝ) ≤
          (((Finset.Icc 1 ⌊((2 ^ (k + 1) : ℕ) : ℝ)⌋₊).filter
            (fun p => p.Prime ∧ (p + h).Prime)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hBk_sub
      exact h1.trans (hbound h hh heven ((2 ^ (k + 1) : ℕ) : ℝ) h2k1_ge3)
    have hlog_pow : Real.log ((2 ^ (k + 1) : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    have hpow_cast : ((2 ^ (k + 1) : ℕ) : ℝ) = 2 * ((2 ^ k : ℕ) : ℝ) := by
      rw [pow_succ, Nat.cast_mul, Nat.cast_ofNat, mul_comm]
    calc ∑ p ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), f p
        ≤ (B_k.card : ℝ) * ((2 ^ k : ℕ) : ℝ)⁻¹ := hsum_Bk
      _ ≤ (C * ((2 ^ (k + 1) : ℕ) : ℝ) / (Real.log ((2 ^ (k + 1) : ℕ) : ℝ)) ^ 2) *
            ((2 ^ k : ℕ) : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hcard_bd (by positivity)
      _ = (2 * C / (Real.log 2) ^ 2) * ((k + 1 : ℕ) : ℝ)⁻¹ ^ 2 := by
          rw [hlog_pow, hpow_cast]
          have hk1_ne : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          field_simp [h2k_pos.ne', hlog2_pos.ne', hk1_ne]
  calc ∑ p ∈ Finset.range N, f p
      ≤ ∑ p ∈ Finset.range (2 ^ K), f p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub_range fun p _ _ => hf_nn p
    _ = (∑ p ∈ Finset.range 4, f p) +
          ∑ k ∈ Finset.Ico 2 K, ∑ p ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), f p :=
        hdyadic K (by omega)
    _ ≤ 4 + ∑ k ∈ Finset.Ico 2 K, (2 * C / (Real.log 2) ^ 2) * ((k + 1 : ℕ) : ℝ)⁻¹ ^ 2 :=
        add_le_add hsmall (Finset.sum_le_sum hblock)
    _ = 4 + (2 * C / (Real.log 2) ^ 2) * ∑ k ∈ Finset.Ico 2 K, ((k + 1 : ℕ) : ℝ)⁻¹ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ 4 + (2 * C / (Real.log 2) ^ 2) * (1 / 2) := by
        gcongr
        exact sum_inv_succ_sq_Ico_two_le K
    _ = 4 + C / (Real.log 2) ^ 2 := by ring

/-- **UNCONDITIONAL BRUN'S CONVERGENCE THEOREM (`0` ASSUMPTIONS!)**:
`∑_{p, p+2 prime} 1/p < ∞`. -/
theorem summable_twin_prime_reciprocals :
    Summable (fun p : ℕ => if p.Prime ∧ (p + 2).Prime then (p : ℝ)⁻¹ else 0) :=
  summable_prime_pair_reciprocals le_rfl even_two

/-- **UNCONDITIONAL CONVERGENCE OF BRUN'S CONSTANT `B₂` (`0` ASSUMPTIONS!)**:
`∑_{p, p+2 prime} (1/p + 1/(p + 2)) < ∞`. -/
theorem summable_brun_constant :
    Summable (fun p : ℕ => if p.Prime ∧ (p + 2).Prime then (p : ℝ)⁻¹ + ((p + 2 : ℕ) : ℝ)⁻¹ else 0) := by
  refine Summable.of_nonneg_of_le (fun p => by split_ifs <;> positivity) (fun p => ?_)
    (summable_twin_prime_reciprocals.mul_left 2)
  split_ifs with hp
  · have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.1.pos
    have hinv : ((p + 2 : ℕ) : ℝ)⁻¹ ≤ (p : ℝ)⁻¹ :=
      inv_anti₀ hp_pos (by push_cast; linarith)
    linarith
  · simp

/-! ## Section 2: Turán's 1934 Second-Moment Theorem & Hardy–Ramanujan Normal Order -/

/-- Exact divisibility count on `Icc 1 N`: `#{n ∈ Icc 1 N : d ∣ n} = N / d` for `d ≥ 1`. -/
private theorem card_Icc_dvd (N d : ℕ) (hd : 0 < d) :
    ((Finset.Icc 1 N).filter (fun n => d ∣ n)).card = N / d := by
  have hbij : ((Finset.Icc 1 N).filter (fun n => d ∣ n)).card = (Finset.Icc 1 (N / d)).card := by
    symm
    refine Finset.card_bij (fun k _ => d * k) ?_ ?_ ?_
    · intro k hk
      obtain ⟨hk1, hkd⟩ := Finset.mem_Icc.mp hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hd hk1,
        (Nat.mul_le_mul_left d hkd).trans (Nat.mul_div_le N d)⟩, dvd_mul_right d k⟩
    · intro k₁ _ k₂ _ heq
      exact Nat.eq_of_mul_eq_mul_left hd heq
    · intro n hn
      obtain ⟨hnI, hdn⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hnI
      refine ⟨n / d, Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right hnN⟩, Nat.mul_div_cancel' hdn⟩
      have hpos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn1 hdn) hd
      omega
  rw [hbij, Nat.card_Icc, Nat.add_sub_cancel]

/-- For `1 ≤ n ≤ N`, `ω(n) = ∑_{p ≤ N, p prime} 1_{p ∣ n}`. -/
private theorem cardDistinctFactors_eq_sum_primes {N n : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    (ω n : ℝ) = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, if p ∣ n then (1 : ℝ) else 0 := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  have hcard : ω n = n.primeFactors.card := by
    rw [ArithmeticFunction.cardDistinctFactors_apply, ← Nat.toFinset_factors, List.card_toFinset]
  rw [hcard]
  congr 1
  ext p
  simp only [Nat.mem_primeFactors, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hp, hpn, -⟩
    exact ⟨⟨⟨hp.pos, (Nat.le_of_dvd hn1 hpn).trans hnN⟩, hp⟩, hpn⟩
  · rintro ⟨⟨_, hp⟩, hpn⟩
    exact ⟨hp, hpn, by omega⟩

/-- Exact first-moment double-sum identity: `∑_{n=1}^N ω(n) = ∑_{p ≤ N} ⌊N / p⌋`. -/
theorem sum_omega_eq_sum_div (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (ω n : ℝ) =
      ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, ((N / p : ℕ) : ℝ) := by
  calc ∑ n ∈ Finset.Icc 1 N, (ω n : ℝ)
      = ∑ n ∈ Finset.Icc 1 N,
          ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, if p ∣ n then (1 : ℝ) else 0 :=
        Finset.sum_congr rfl fun n hn =>
          cardDistinctFactors_eq_sum_primes (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
    _ = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
          ∑ n ∈ Finset.Icc 1 N, if p ∣ n then (1 : ℝ) else 0 := Finset.sum_comm
    _ = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, ((N / p : ℕ) : ℝ) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
          card_Icc_dvd N p (Finset.mem_filter.mp hp).2.pos]

/-- Floor-division comparison: for `x ≥ 1` and `d ≥ 1`,
`0 ≤ x / d - ((⌊x⌋₊ / d : ℕ) : ℝ) ≤ 2`. -/
private theorem floor_div_approx {x : ℝ} (hx : 1 ≤ x) {d : ℕ} (hd : 1 ≤ d) :
    0 ≤ x / (d : ℝ) - ((⌊x⌋₊ / d : ℕ) : ℝ) ∧
    x / (d : ℝ) - ((⌊x⌋₊ / d : ℕ) : ℝ) ≤ 2 := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := Nat.one_le_cast.mpr hd
  have hNle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxlt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have hmul_le : ((⌊x⌋₊ / d : ℕ) : ℝ) * (d : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self ⌊x⌋₊ d
  have hlt_mul : (⌊x⌋₊ : ℝ) < (((⌊x⌋₊ / d : ℕ) : ℝ) + 1) * (d : ℝ) := by
    have hnat : ⌊x⌋₊ < (⌊x⌋₊ / d + 1) * d := by
      have := Nat.lt_mul_div_succ ⌊x⌋₊ (by omega : 0 < d)
      linarith
    exact_mod_cast hnat
  constructor
  · rw [sub_nonneg, le_div_iff₀ hd_pos]
    linarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hd_pos]
    nlinarith

/-- Comparison between `∑_{n ≤ x} ω(n)` and `x * ∑_{p ≤ x} 1/p`:
`0 ≤ x * mertensSum2 x - ∑_{n ≤ x} ω(n) ≤ 2 * x` for all `x ≥ 1`. -/
theorem sum_omega_approx_mertensSum2 {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ x * Stage8MertensTheorems.mertensSum2 x - ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ω n : ℝ) ∧
    x * Stage8MertensTheorems.mertensSum2 x - ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ω n : ℝ) ≤ 2 * x := by
  rw [sum_omega_eq_sum_div]
  unfold Stage8MertensTheorems.mertensSum2
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  constructor
  · refine Finset.sum_nonneg fun p hp => ?_
    rw [← div_eq_mul_inv]
    exact (floor_div_approx hx (Finset.mem_filter.mp hp).2.pos).1
  · calc ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (x * (p : ℝ)⁻¹ - ((⌊x⌋₊ / p : ℕ) : ℝ))
        ≤ ∑ _p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (2 : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          rw [← div_eq_mul_inv]
          exact (floor_div_approx hx (Finset.mem_filter.mp hp).2.pos).2
      _ = 2 * (((Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 2 * (⌊x⌋₊ : ℝ) := by
          gcongr
          have hcard : ((Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime).card ≤ ⌊x⌋₊ :=
            (Finset.card_filter_le _ _).trans (by rw [Nat.card_Icc]; omega)
          exact_mod_cast hcard
      _ ≤ 2 * x := by
          gcongr
          exact Nat.floor_le (by linarith)

/-- `1 < Real.log 3`, hence `0 < Real.log (Real.log x)` for every `x ≥ 3`. -/
private theorem one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
  linarith [Real.exp_one_lt_d9]

private theorem log_log_pos_of_ge_three {x : ℝ} (hx : 3 ≤ x) :
    0 < Real.log (Real.log x) := by
  apply Real.log_pos
  exact one_lt_log_three.trans_le (Real.log_le_log (by norm_num) hx)

/-- **EXACT FIRST MOMENT OF `ω(n)` (`0` ASSUMPTIONS!)**:
`∃ C > 0, ∀ x ≥ 3, |∑_{n ≤ x} ω(n) - x * log (log x)| ≤ C * x`. -/
theorem sum_omega_asymp :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ω n : ℝ) - x * Real.log (Real.log x)| ≤ C * x := by
  obtain ⟨C_M, hC_M, hM2⟩ := Stage8MertensTheorems.mertens_second_theorem
  set K : ℝ := 2 + |Stage8MertensTheorems.meisselMertensConst| + C_M / Real.log 3
  have hlog3_pos : 0 < Real.log 3 := zero_lt_one.trans one_lt_log_three
  refine ⟨K, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have happrox := sum_omega_approx_mertensSum2 (by linarith : 1 ≤ x)
  have hM := hM2 x hx
  have hlog_ge : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hM_diff : |Stage8MertensTheorems.mertensSum2 x - Real.log (Real.log x)| ≤
      |Stage8MertensTheorems.meisselMertensConst| + C_M / Real.log 3 := by
    have h1 : Stage8MertensTheorems.mertensSum2 x - Real.log (Real.log x) =
        (Stage8MertensTheorems.mertensSum2 x -
          (Real.log (Real.log x) + Stage8MertensTheorems.meisselMertensConst)) +
        Stage8MertensTheorems.meisselMertensConst := by ring
    rw [h1]
    have htri := abs_add_le
      (Stage8MertensTheorems.mertensSum2 x -
        (Real.log (Real.log x) + Stage8MertensTheorems.meisselMertensConst))
      Stage8MertensTheorems.meisselMertensConst
    have hdiv : C_M / Real.log x ≤ C_M / Real.log 3 :=
      div_le_div_of_nonneg_left hC_M.le hlog3_pos hlog_ge
    unfold Stage8MertensTheorems.mertensSum2 at htri ⊢
    linarith
  have hrew : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ω n : ℝ) - x * Real.log (Real.log x) =
      x * (Stage8MertensTheorems.mertensSum2 x - Real.log (Real.log x)) -
      (x * Stage8MertensTheorems.mertensSum2 x - ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ω n : ℝ)) := by ring
  rw [hrew]
  have htri := abs_sub (x * (Stage8MertensTheorems.mertensSum2 x - Real.log (Real.log x)))
    (x * Stage8MertensTheorems.mertensSum2 x - ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ω n : ℝ))
  have hterm1 : |x * (Stage8MertensTheorems.mertensSum2 x - Real.log (Real.log x))| ≤
      (|Stage8MertensTheorems.meisselMertensConst| + C_M / Real.log 3) * x := by
    rw [abs_mul, abs_of_pos hx0, mul_comm]
    exact mul_le_mul_of_nonneg_right hM_diff hx0.le
  have hterm2 : |x * Stage8MertensTheorems.mertensSum2 x - ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ω n : ℝ)| ≤
      2 * x := by
    rw [abs_of_nonneg happrox.1]
    exact happrox.2
  dsimp only [K]
  linarith

/-- Second-moment upper bound on `∑_{n ≤ x} ω(n)²`:
`∑_{n=1}^{⌊x⌋} ω(n)² ≤ x * S(x)² + x * S(x)` where `S(x) = ∑_{p ≤ x} 1/p`. -/
theorem sum_omega_sq_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ω n : ℝ) ^ 2 ≤
      x * (Stage8MertensTheorems.mertensSum2 x) ^ 2 + x * Stage8MertensTheorems.mertensSum2 x := by
  set N : ℕ := ⌊x⌋₊
  set P : Finset ℕ := (Finset.Icc 1 N).filter Nat.Prime
  have hNle : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hexp : ∑ n ∈ Finset.Icc 1 N, (ω n : ℝ) ^ 2 =
      ∑ p ∈ P, ∑ q ∈ P, ∑ n ∈ Finset.Icc 1 N, if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0 := by
    calc ∑ n ∈ Finset.Icc 1 N, (ω n : ℝ) ^ 2
        = ∑ n ∈ Finset.Icc 1 N, (∑ p ∈ P, if p ∣ n then (1 : ℝ) else 0) ^ 2 :=
          Finset.sum_congr rfl fun n hn => by
            rw [cardDistinctFactors_eq_sum_primes (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2]
      _ = ∑ n ∈ Finset.Icc 1 N, ∑ p ∈ P, ∑ q ∈ P, if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0 := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [sq, Finset.sum_mul]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          by_cases hp : p ∣ n <;> by_cases hq : q ∣ n <;> simp [hp, hq]
      _ = ∑ p ∈ P, ∑ n ∈ Finset.Icc 1 N, ∑ q ∈ P, if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0 :=
          Finset.sum_comm
      _ = ∑ p ∈ P, ∑ q ∈ P, ∑ n ∈ Finset.Icc 1 N, if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0 :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  rw [hexp]
  have hbound_pq : ∀ p ∈ P, ∀ q ∈ P,
      (∑ n ∈ Finset.Icc 1 N, if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0) ≤
        x * (p : ℝ)⁻¹ * (q : ℝ)⁻¹ + if p = q then x * (p : ℝ)⁻¹ else 0 := by
    intro p hp q hq
    have hp_pr : p.Prime := (Finset.mem_filter.mp hp).2
    have hq_pr : q.Prime := (Finset.mem_filter.mp hq).2
    by_cases hpq : p = q
    · subst hpq
      rw [if_pos rfl]
      have hcnt : ∑ n ∈ Finset.Icc 1 N, (if p ∣ n ∧ p ∣ n then (1 : ℝ) else 0) = ((N / p : ℕ) : ℝ) := by
        have h1 : ∀ n ∈ Finset.Icc 1 N,
            (if p ∣ n ∧ p ∣ n then (1 : ℝ) else 0) = if p ∣ n then 1 else 0 := fun n _ => by
          by_cases h : p ∣ n <;> simp [h]
        rw [Finset.sum_congr rfl h1, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
          card_Icc_dvd N p hp_pr.pos]
      rw [hcnt]
      have hle : ((N / p : ℕ) : ℝ) ≤ x * (p : ℝ)⁻¹ := by
        rw [← div_eq_mul_inv]
        linarith [(floor_div_approx hx hp_pr.pos).1]
      have hnn : 0 ≤ x * (p : ℝ)⁻¹ * (p : ℝ)⁻¹ := by positivity
      linarith
    · rw [if_neg hpq, add_zero]
      have hcop : Nat.Coprime p q := (Nat.coprime_primes hp_pr hq_pr).mpr hpq
      have hcnt : ∑ n ∈ Finset.Icc 1 N, (if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0) =
          ((N / (p * q) : ℕ) : ℝ) := by
        have h1 : ∀ n ∈ Finset.Icc 1 N,
            (if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0) = if p * q ∣ n then 1 else 0 := fun n _ => by
          by_cases h : p * q ∣ n
          · have h1 : p ∣ n := (dvd_mul_right p q).trans h
            have h2 : q ∣ n := (dvd_mul_left q p).trans h
            simp [h, h1, h2]
          · have hnot : ¬ (p ∣ n ∧ q ∣ n) := fun ⟨h1, h2⟩ => h (hcop.mul_dvd_of_dvd_of_dvd h1 h2)
            simp [h, hnot]
        rw [Finset.sum_congr rfl h1, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
          card_Icc_dvd N (p * q) (Nat.mul_pos hp_pr.pos hq_pr.pos)]
      rw [hcnt]
      have hle : ((N / (p * q) : ℕ) : ℝ) ≤ x / ((p * q : ℕ) : ℝ) := by
        linarith [(floor_div_approx hx (Nat.mul_pos hp_pr.pos hq_pr.pos)).1]
      calc ((N / (p * q) : ℕ) : ℝ)
          ≤ x / ((p * q : ℕ) : ℝ) := hle
        _ = x * (p : ℝ)⁻¹ * (q : ℝ)⁻¹ := by
            rw [Nat.cast_mul, div_eq_mul_inv, mul_inv, mul_assoc]
  calc ∑ p ∈ P, ∑ q ∈ P, ∑ n ∈ Finset.Icc 1 N, (if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0)
      ≤ ∑ p ∈ P, ∑ q ∈ P, (x * (p : ℝ)⁻¹ * (q : ℝ)⁻¹ + if p = q then x * (p : ℝ)⁻¹ else 0) :=
        Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => hbound_pq p hp q hq
    _ = (∑ p ∈ P, ∑ q ∈ P, x * (p : ℝ)⁻¹ * (q : ℝ)⁻¹) +
          ∑ p ∈ P, ∑ q ∈ P, if p = q then x * (p : ℝ)⁻¹ else 0 := by
        simp_rw [Finset.sum_add_distrib]
    _ = x * (Stage8MertensTheorems.mertensSum2 x) ^ 2 + x * Stage8MertensTheorems.mertensSum2 x := by
        unfold Stage8MertensTheorems.mertensSum2
        congr 1
        · rw [sq, Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => by ring
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [Finset.sum_ite_eq P p (fun _ => x * (p : ℝ)⁻¹), if_pos hp]

/-- **TURÁN'S 1934 SECOND-MOMENT INEQUALITY FOR `ω(n)` (`0` ASSUMPTIONS!)**:
`∃ C > 0, ∀ x ≥ 3, ∑_{n ≤ x} (ω(n) - log log x)² ≤ C * x * log log x`. -/
theorem turan_second_moment_omega :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ω n : ℝ) - Real.log (Real.log x)) ^ 2 ≤
        C * x * Real.log (Real.log x) := by
  obtain ⟨C_M, hC_M, hM2⟩ := Stage8MertensTheorems.mertens_second_theorem
  have hlog3_pos : 0 < Real.log 3 := zero_lt_one.trans one_lt_log_three
  have hLL3_pos : 0 < Real.log (Real.log 3) := log_log_pos_of_ge_three le_rfl
  set K₀ : ℝ := |Stage8MertensTheorems.meisselMertensConst| + C_M / Real.log 3
  have hK₀_nn : 0 ≤ K₀ := by positivity
  set C : ℝ := 5 + (K₀ ^ 2 + K₀) / Real.log (Real.log 3)
  refine ⟨C, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  set N : ℕ := ⌊x⌋₊
  set L : ℝ := Real.log (Real.log x)
  set S : ℝ := Stage8MertensTheorems.mertensSum2 x
  have hL_ge : Real.log (Real.log 3) ≤ L :=
    Real.log_le_log hlog3_pos (Real.log_le_log (by norm_num) hx)
  have hL_pos : 0 < L := hLL3_pos.trans_le hL_ge
  have hNle : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  -- Expand `∑ (ω n - L)²`
  have hexp : ∑ n ∈ Finset.Icc 1 N, ((ω n : ℝ) - L) ^ 2 =
      (∑ n ∈ Finset.Icc 1 N, (ω n : ℝ) ^ 2) - 2 * L * (∑ n ∈ Finset.Icc 1 N, (ω n : ℝ)) +
        (N : ℝ) * L ^ 2 := by
    have h1 : ∀ n ∈ Finset.Icc 1 N,
        ((ω n : ℝ) - L) ^ 2 = (ω n : ℝ) ^ 2 - 2 * L * (ω n : ℝ) + L ^ 2 := fun _ _ => by ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  rw [hexp]
  have hsq_bd : ∑ n ∈ Finset.Icc 1 N, (ω n : ℝ) ^ 2 ≤ x * S ^ 2 + x * S := sum_omega_sq_le hx1
  have hfirst_lb : x * S - 2 * x ≤ ∑ n ∈ Finset.Icc 1 N, (ω n : ℝ) := by
    linarith [(sum_omega_approx_mertensSum2 hx1).2]
  have hM_diff : |S - L| ≤ K₀ := by
    have hM := hM2 x hx
    have hdiv : C_M / Real.log x ≤ C_M / Real.log 3 :=
      div_le_div_of_nonneg_left hC_M.le hlog3_pos (Real.log_le_log (by norm_num) hx)
    have hrew : S - L =
        (S - (L + Stage8MertensTheorems.meisselMertensConst)) +
        Stage8MertensTheorems.meisselMertensConst := by ring
    rw [hrew]
    have htri := abs_add_le (S - (L + Stage8MertensTheorems.meisselMertensConst))
      Stage8MertensTheorems.meisselMertensConst
    dsimp only [S, L, Stage8MertensTheorems.mertensSum2, K₀] at htri ⊢
    linarith
  have hSL_sq : (S - L) ^ 2 ≤ K₀ ^ 2 := by
    rw [← sq_abs (S - L)]
    exact pow_le_pow_left₀ (abs_nonneg _) hM_diff 2
  have hS_le : S ≤ L + K₀ := by linarith [(abs_le.mp hM_diff).2]
  have h2L : -2 * L * (∑ n ∈ Finset.Icc 1 N, (ω n : ℝ)) ≤ -2 * L * (x * S - 2 * x) := by
    nlinarith
  have hNL2 : (N : ℝ) * L ^ 2 ≤ x * L ^ 2 :=
    mul_le_mul_of_nonneg_right hNle (sq_nonneg L)
  have hcomb : (∑ n ∈ Finset.Icc 1 N, (ω n : ℝ) ^ 2) - 2 * L * (∑ n ∈ Finset.Icc 1 N, (ω n : ℝ)) +
      (N : ℝ) * L ^ 2 ≤ 5 * x * L + (K₀ ^ 2 + K₀) * x := by
    have hident : (x * S ^ 2 + x * S) - 2 * L * (x * S - 2 * x) + x * L ^ 2 =
        x * (S - L) ^ 2 + x * S + 4 * x * L := by ring
    nlinarith [mul_le_mul_of_nonneg_left hSL_sq hx0.le, mul_le_mul_of_nonneg_left hS_le hx0.le]
  have hx_le : x ≤ x * L / Real.log (Real.log 3) := by
    rw [le_div_iff₀ hLL3_pos]
    exact mul_le_mul_of_nonneg_left hL_ge hx0.le
  calc (∑ n ∈ Finset.Icc 1 N, (ω n : ℝ) ^ 2) - 2 * L * (∑ n ∈ Finset.Icc 1 N, (ω n : ℝ)) +
        (N : ℝ) * L ^ 2
      ≤ 5 * x * L + (K₀ ^ 2 + K₀) * x := hcomb
    _ ≤ 5 * x * L + (K₀ ^ 2 + K₀) * (x * L / Real.log (Real.log 3)) := by
        gcongr
    _ = C * x * L := by dsimp only [C]; ring

/-- Elementary finite geometric-series bound: for `p ≥ 2`, `∑_{k=2}^M 1 / p^k ≤ 1 / (p * (p - 1))`. -/
private theorem sum_inv_pow_ge_two_le {p : ℕ} (hp : 2 ≤ p) (M : ℕ) :
    ∑ k ∈ Finset.Icc 2 M, ((p : ℝ) ^ k)⁻¹ ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hsub : (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by
    have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    linarith
  have htel : (1 - (p : ℝ)⁻¹) * ∑ k ∈ Finset.Icc 2 M, ((p : ℝ) ^ k)⁻¹ ≤ ((p : ℝ) ^ 2)⁻¹ := by
    by_cases hM : 2 ≤ M
    · have heq : (1 - (p : ℝ)⁻¹) * ∑ k ∈ Finset.Icc 2 M, ((p : ℝ) ^ k)⁻¹ =
          ((p : ℝ) ^ 2)⁻¹ - ((p : ℝ) ^ (M + 1))⁻¹ := by
        induction M, hM using Nat.le_induction with
        | base =>
          simp only [Finset.Icc_self, Finset.sum_singleton]
          field_simp [hp0.ne']
          ring
        | succ m hm ih =>
          have hIcc : Finset.Icc 2 (m + 1) = insert (m + 1) (Finset.Icc 2 m) := by
            ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hIcc, Finset.sum_insert (by simp), mul_add, ih]
          have hpow : (p : ℝ)⁻¹ * ((p : ℝ) ^ (m + 1))⁻¹ = ((p : ℝ) ^ (m + 2))⁻¹ := by
            rw [← mul_inv, mul_comm, ← pow_succ]
          linarith
      rw [heq]
      have : (0 : ℝ) ≤ ((p : ℝ) ^ (M + 1))⁻¹ := by positivity
      linarith
    · have hempty : Finset.Icc 2 M = ∅ := Finset.Icc_eq_empty (by omega)
      rw [hempty, Finset.sum_empty, mul_zero]
      positivity
  have hrhs : ((p : ℝ) ^ 2)⁻¹ / (1 - (p : ℝ)⁻¹) = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    field_simp [hp0.ne', (by linarith : (p : ℝ) - 1 ≠ 0)]
  rw [← hrhs, le_div_iff₀ hsub, mul_comm]
  exact htel

/-- Elementary weighted geometric-series bound: for `p ≥ 2`,
`∑_{k=2}^M (k - 1) / p^k ≤ 1 / (p - 1)²`. -/
private theorem sum_weighted_inv_pow_ge_two_le {p : ℕ} (hp : 2 ≤ p) (M : ℕ) :
    ∑ k ∈ Finset.Icc 2 M, ((k - 1 : ℕ) : ℝ) * ((p : ℝ) ^ k)⁻¹ ≤ 1 / ((p : ℝ) - 1) ^ 2 := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hsub : (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by
    have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    linarith
  -- Multiply by `(1 - 1/p)²` and telescope!
  have htel : (1 - (p : ℝ)⁻¹) ^ 2 *
      ∑ k ∈ Finset.Icc 2 M, ((k - 1 : ℕ) : ℝ) * ((p : ℝ) ^ k)⁻¹ ≤ ((p : ℝ) ^ 2)⁻¹ := by
    by_cases hM : 2 ≤ M
    · have heq : (1 - (p : ℝ)⁻¹) ^ 2 *
          ∑ k ∈ Finset.Icc 2 M, ((k - 1 : ℕ) : ℝ) * ((p : ℝ) ^ k)⁻¹ =
          ((p : ℝ) ^ 2)⁻¹ - ((M : ℝ) * ((p : ℝ) ^ (M + 1))⁻¹ -
            (((M - 1 : ℕ) : ℝ)) * ((p : ℝ) ^ (M + 2))⁻¹) := by
        induction M, hM using Nat.le_induction with
        | base =>
          simp only [Finset.Icc_self, Finset.sum_singleton]
          norm_num
          field_simp [hp0.ne']
          ring
        | succ m hm ih =>
          have hIcc : Finset.Icc 2 (m + 1) = insert (m + 1) (Finset.Icc 2 m) := by
            ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hIcc, Finset.sum_insert (by simp), mul_add, ih]
          have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
          have hms1 : (((m + 1) - 1 : ℕ) : ℝ) = (m : ℝ) := by simp
          rw [hm1, hms1, Nat.cast_add, Nat.cast_one]
          have hp1 : ((p : ℝ) ^ (m + 1))⁻¹ = ((p : ℝ) ^ m)⁻¹ * (p : ℝ)⁻¹ := by
            rw [pow_succ, mul_inv]
          have hp2 : ((p : ℝ) ^ (m + 2))⁻¹ = ((p : ℝ) ^ m)⁻¹ * (p : ℝ)⁻¹ * (p : ℝ)⁻¹ := by
            rw [pow_succ, pow_succ, mul_inv, mul_inv]
          have hp3 : ((p : ℝ) ^ (m + 3))⁻¹ = ((p : ℝ) ^ m)⁻¹ * (p : ℝ)⁻¹ * (p : ℝ)⁻¹ * (p : ℝ)⁻¹ := by
            rw [pow_succ, pow_succ, pow_succ, mul_inv, mul_inv, mul_inv]
          rw [show m + 1 + 1 = m + 2 by omega, show m + 1 + 2 = m + 3 by omega, hp1, hp2, hp3]
          ring
      rw [heq]
      have hrem_nn : 0 ≤ (M : ℝ) * ((p : ℝ) ^ (M + 1))⁻¹ -
          (((M - 1 : ℕ) : ℝ)) * ((p : ℝ) ^ (M + 2))⁻¹ := by
        have hM1 : (((M - 1 : ℕ) : ℝ)) ≤ (M : ℝ) := by exact_mod_cast Nat.sub_le M 1
        have hpow : ((p : ℝ) ^ (M + 2))⁻¹ ≤ ((p : ℝ) ^ (M + 1))⁻¹ :=
          inv_anti₀ (pow_pos hp0 _) (pow_le_pow_right₀ (by linarith) (by omega))
        have h1 : (((M - 1 : ℕ) : ℝ)) * ((p : ℝ) ^ (M + 2))⁻¹ ≤
            (M : ℝ) * ((p : ℝ) ^ (M + 1))⁻¹ :=
          mul_le_mul hM1 hpow (by positivity) (Nat.cast_nonneg M)
        linarith
      linarith
    · have hempty : Finset.Icc 2 M = ∅ := Finset.Icc_eq_empty (by omega)
      rw [hempty, Finset.sum_empty, mul_zero]
      positivity
  have hrhs : ((p : ℝ) ^ 2)⁻¹ / (1 - (p : ℝ)⁻¹) ^ 2 = 1 / ((p : ℝ) - 1) ^ 2 := by
    field_simp [hp0.ne', (by linarith : (p : ℝ) - 1 ≠ 0)]
  rw [← hrhs, le_div_iff₀ (sq_pos_of_pos hsub), mul_comm]
  exact htel

/-- For `1 ≤ n ≤ N`, `Ω(n) - ω(n) = ∑_{p ≤ N, p prime} ∑_{k=2}^N 1_{p^k ∣ n}`. -/
private theorem Omega_sub_omega_eq_sum_prime_pows {N n : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    (Ω n : ℝ) - (ω n : ℝ) =
      ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        ∑ k ∈ Finset.Icc 2 N, if p ^ k ∣ n then (1 : ℝ) else 0 := by
  have hn0 : n ≠ 0 := by omega
  have hOmega : (Ω n : ℝ) = ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) := by
    rw [ArithmeticFunction.cardFactors_eq_sum_factorization, Finsupp.sum, Nat.cast_sum]
    congr 1
  have homega : (ω n : ℝ) = ∑ p ∈ n.primeFactors, (1 : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one,
      ArithmeticFunction.cardDistinctFactors_apply, ← Nat.toFinset_factors, List.card_toFinset]
  rw [hOmega, homega, ← Finset.sum_sub_distrib]
  have hsub : n.primeFactors ⊆ (Finset.Icc 1 N).filter Nat.Prime := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpr.pos, (Nat.le_of_dvd hn1 hdvd).trans hnN⟩, hpr⟩
  have hrew : ∑ p ∈ n.primeFactors, ((n.factorization p : ℝ) - 1) =
      ∑ p ∈ n.primeFactors, ((n.factorization p - 1 : ℕ) : ℝ) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hv1 : 1 ≤ n.factorization p :=
      (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hp)
    rw [Nat.cast_sub hv1, Nat.cast_one]
  rw [hrew]
  calc ∑ p ∈ n.primeFactors, ((n.factorization p - 1 : ℕ) : ℝ)
      = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, ((n.factorization p - 1 : ℕ) : ℝ) := by
        refine Finset.sum_subset hsub fun p hp hnot => ?_
        have hpr : p.Prime := (Finset.mem_filter.mp hp).2
        have hndvd : ¬ p ∣ n := fun h => hnot (Nat.mem_primeFactors.mpr ⟨hpr, h, hn0⟩)
        rw [Nat.factorization_eq_zero_of_not_dvd hndvd]
        simp
    _ = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
          ∑ k ∈ Finset.Icc 2 N, if p ^ k ∣ n then (1 : ℝ) else 0 := by
        refine Finset.sum_congr rfl fun p hp => ?_
        have hpr : p.Prime := (Finset.mem_filter.mp hp).2
        by_cases hpn : p ∣ n
        · have hv_le : n.factorization p ≤ N := by
            have h1 : n.factorization p ≤ p ^ n.factorization p := (Nat.lt_pow_self hpr.one_lt).le
            exact h1.trans ((Nat.le_of_dvd hn1 (Nat.ordProj_dvd n p)).trans hnN)
          have hfilt : (Finset.Icc 2 N).filter (fun k => p ^ k ∣ n) = Finset.Icc 2 (n.factorization p) := by
            ext k
            simp only [Finset.mem_filter, Finset.mem_Icc, hpr.pow_dvd_iff_le_factorization hn0]
            omega
          rw [← Finset.sum_filter, hfilt, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
          congr 1
        · have hv0 : n.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpn
          rw [hv0, Nat.zero_sub, Nat.cast_zero]
          symm
          refine Finset.sum_eq_zero fun k hk => ?_
          have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
          have hndvd : ¬ p ^ k ∣ n := fun h => hpn ((dvd_pow_self p (by omega)).trans h)
          simp [hndvd]

private theorem sum_telescoping_Icc_two {N : ℕ} (hN : 2 ≤ N) :
    ∑ m ∈ Finset.Icc 2 N, (1 : ℝ) / ((m : ℝ) * ((m : ℝ) - 1)) = 1 - (N : ℝ)⁻¹ := by
  induction N, hN using Nat.le_induction with
  | base => simp; norm_num
  | succ m hm ih =>
    have hIcc : Finset.Icc 2 (m + 1) = insert (m + 1) (Finset.Icc 2 m) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp), ih]
    have hmpos : (0 : ℝ) < (m : ℝ) := by positivity
    push_cast
    field_simp [hmpos.ne', (by positivity : (m : ℝ) + 1 ≠ 0)]
    ring

private theorem sum_telescoping_Icc_three {N : ℕ} (hN : 3 ≤ N) :
    ∑ m ∈ Finset.Icc 3 N, (1 : ℝ) / (((m - 1 : ℕ) : ℝ) * (((m - 1 : ℕ) : ℝ) - 1)) =
      1 - ((N - 1 : ℕ) : ℝ)⁻¹ := by
  induction N, hN using Nat.le_induction with
  | base => simp; norm_num
  | succ m hm ih =>
    have hIcc : Finset.Icc 3 (m + 1) = insert (m + 1) (Finset.Icc 3 m) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp), ih]
    have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    have hm2 : (((m + 1) - 1 : ℕ) : ℝ) = (m : ℝ) := by simp
    rw [hm1, hm2]
    have hpos1 : (0 : ℝ) < (m : ℝ) - 1 := by
      have : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have hpos0 : (0 : ℝ) < (m : ℝ) := by positivity
    field_simp [hpos1.ne', hpos0.ne']
    ring

/-- **Uniform `O(N)` Second Moment of `Ω(n) - ω(n)`**:
`∑_{n=1}^N (Ω(n) - ω(n))² ≤ 5 * N` for EVERY `N : ℕ`! -/
theorem sum_Omega_sub_omega_sq_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ((Ω n : ℝ) - (ω n : ℝ)) ^ 2 ≤ 5 * (N : ℝ) := by
  set P : Finset ℕ := (Finset.Icc 1 N).filter Nat.Prime
  set K : Finset ℕ := Finset.Icc 2 N
  set PK : Finset (ℕ × ℕ) := P ×ˢ K
  -- Express `∑ (Ω - ω)²` as a double sum over `(p, k), (q, j) ∈ P ×ˢ K`
  have hexp : ∑ n ∈ Finset.Icc 1 N, ((Ω n : ℝ) - (ω n : ℝ)) ^ 2 =
      ∑ a ∈ PK, ∑ b ∈ PK,
        ∑ n ∈ Finset.Icc 1 N, if a.1 ^ a.2 ∣ n ∧ b.1 ^ b.2 ∣ n then (1 : ℝ) else 0 := by
    have hrew_n : ∀ n ∈ Finset.Icc 1 N,
        ((Ω n : ℝ) - (ω n : ℝ)) = ∑ a ∈ PK, if a.1 ^ a.2 ∣ n then (1 : ℝ) else 0 := fun n hn => by
      rw [Omega_sub_omega_eq_sum_prime_pows (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2]
      exact (Finset.sum_product' P K (fun p k => if p ^ k ∣ n then (1 : ℝ) else 0)).symm
    calc ∑ n ∈ Finset.Icc 1 N, ((Ω n : ℝ) - (ω n : ℝ)) ^ 2
        = ∑ n ∈ Finset.Icc 1 N, (∑ a ∈ PK, if a.1 ^ a.2 ∣ n then (1 : ℝ) else 0) ^ 2 :=
          Finset.sum_congr rfl fun n hn => by rw [hrew_n n hn]
      _ = ∑ n ∈ Finset.Icc 1 N, ∑ a ∈ PK, ∑ b ∈ PK,
            if a.1 ^ a.2 ∣ n ∧ b.1 ^ b.2 ∣ n then (1 : ℝ) else 0 := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [sq, Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          by_cases ha : a.1 ^ a.2 ∣ n <;> by_cases hb : b.1 ^ b.2 ∣ n <;> simp [ha, hb]
      _ = ∑ a ∈ PK, ∑ n ∈ Finset.Icc 1 N, ∑ b ∈ PK,
            if a.1 ^ a.2 ∣ n ∧ b.1 ^ b.2 ∣ n then (1 : ℝ) else 0 := Finset.sum_comm
      _ = ∑ a ∈ PK, ∑ b ∈ PK, ∑ n ∈ Finset.Icc 1 N,
            if a.1 ^ a.2 ∣ n ∧ b.1 ^ b.2 ∣ n then (1 : ℝ) else 0 :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  rw [hexp]
  -- Pointwise bound on each `(a, b)` inner sum
  have hinner : ∀ a ∈ PK, ∀ b ∈ PK,
      (∑ n ∈ Finset.Icc 1 N, if a.1 ^ a.2 ∣ n ∧ b.1 ^ b.2 ∣ n then (1 : ℝ) else 0) ≤
        (N : ℝ) * ((a.1 : ℝ) ^ a.2)⁻¹ * ((b.1 : ℝ) ^ b.2)⁻¹ +
        if a.1 = b.1 then (N : ℝ) * ((a.1 : ℝ) ^ (max a.2 b.2))⁻¹ else 0 := by
    intro a ha b hb
    have ha_pr : a.1.Prime := (Finset.mem_filter.mp (Finset.mem_product.mp ha).1).2
    have hb_pr : b.1.Prime := (Finset.mem_filter.mp (Finset.mem_product.mp hb).1).2
    have hdiv_le : ∀ d : ℕ, 0 < d → ((N / d : ℕ) : ℝ) ≤ (N : ℝ) * (d : ℝ)⁻¹ := fun d hd => by
      rw [← div_eq_mul_inv, le_div_iff₀ (Nat.cast_pos.mpr hd)]
      exact_mod_cast Nat.div_mul_le_self N d
    by_cases heq : a.1 = b.1
    · rw [if_pos heq]
      have hcnt : ∑ n ∈ Finset.Icc 1 N,
          (if a.1 ^ a.2 ∣ n ∧ b.1 ^ b.2 ∣ n then (1 : ℝ) else 0) =
          ((N / (a.1 ^ max a.2 b.2) : ℕ) : ℝ) := by
        have h1 : ∀ n ∈ Finset.Icc 1 N,
            (if a.1 ^ a.2 ∣ n ∧ b.1 ^ b.2 ∣ n then (1 : ℝ) else 0) =
            if a.1 ^ max a.2 b.2 ∣ n then 1 else 0 := fun n _ => by
          rw [← heq]
          have hiff : a.1 ^ a.2 ∣ n ∧ a.1 ^ b.2 ∣ n ↔ a.1 ^ max a.2 b.2 ∣ n := by
            rcases le_total a.2 b.2 with hle | hle
            · rw [max_eq_right hle]
              exact ⟨fun h => h.2, fun h => ⟨(Nat.pow_dvd_pow a.1 hle).trans h, h⟩⟩
            · rw [max_eq_left hle]
              exact ⟨fun h => h.1, fun h => ⟨h, (Nat.pow_dvd_pow a.1 hle).trans h⟩⟩
          by_cases h : a.1 ^ max a.2 b.2 ∣ n <;> simp [hiff, h]
        rw [Finset.sum_congr rfl h1, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
          card_Icc_dvd N (a.1 ^ max a.2 b.2) (pow_pos ha_pr.pos _)]
      rw [hcnt]
      have hle := hdiv_le (a.1 ^ max a.2 b.2) (pow_pos ha_pr.pos _)
      rw [Nat.cast_pow] at hle
      have hnn : 0 ≤ (N : ℝ) * ((a.1 : ℝ) ^ a.2)⁻¹ * ((b.1 : ℝ) ^ b.2)⁻¹ := by positivity
      linarith
    · rw [if_neg heq, add_zero]
      have hcop : Nat.Coprime (a.1 ^ a.2) (b.1 ^ b.2) :=
        ((Nat.coprime_primes ha_pr hb_pr).mpr heq).pow a.2 b.2
      have hcnt : ∑ n ∈ Finset.Icc 1 N,
          (if a.1 ^ a.2 ∣ n ∧ b.1 ^ b.2 ∣ n then (1 : ℝ) else 0) =
          ((N / (a.1 ^ a.2 * b.1 ^ b.2) : ℕ) : ℝ) := by
        have h1 : ∀ n ∈ Finset.Icc 1 N,
            (if a.1 ^ a.2 ∣ n ∧ b.1 ^ b.2 ∣ n then (1 : ℝ) else 0) =
            if a.1 ^ a.2 * b.1 ^ b.2 ∣ n then 1 else 0 := fun n _ => by
          have hiff : a.1 ^ a.2 ∣ n ∧ b.1 ^ b.2 ∣ n ↔ a.1 ^ a.2 * b.1 ^ b.2 ∣ n :=
            ⟨fun ⟨h1, h2⟩ => hcop.mul_dvd_of_dvd_of_dvd h1 h2,
             fun h => ⟨(dvd_mul_right _ _).trans h, (dvd_mul_left _ _).trans h⟩⟩
          by_cases h : a.1 ^ a.2 * b.1 ^ b.2 ∣ n <;> simp [hiff, h]
        rw [Finset.sum_congr rfl h1, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
          card_Icc_dvd N (a.1 ^ a.2 * b.1 ^ b.2) (Nat.mul_pos (pow_pos ha_pr.pos _) (pow_pos hb_pr.pos _))]
      rw [hcnt]
      have hle := hdiv_le (a.1 ^ a.2 * b.1 ^ b.2)
        (Nat.mul_pos (pow_pos ha_pr.pos _) (pow_pos hb_pr.pos _))
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, mul_inv, ← mul_assoc] at hle
      exact hle
  -- Bound the two resulting sums:
  -- Sum 1: `∑_{p ∈ P, k ∈ K} 1 / p^k ≤ 1`
  have hsum1 : ∑ a ∈ PK, ((a.1 : ℝ) ^ a.2)⁻¹ ≤ 1 := by
    rw [show ∑ a ∈ PK, ((a.1 : ℝ) ^ a.2)⁻¹ = ∑ p ∈ P, ∑ k ∈ K, ((p : ℝ) ^ k)⁻¹ from
      Finset.sum_product' P K (fun p k => ((p : ℝ) ^ k)⁻¹)]
    calc ∑ p ∈ P, ∑ k ∈ K, ((p : ℝ) ^ k)⁻¹
        ≤ ∑ p ∈ P, 1 / ((p : ℝ) * ((p : ℝ) - 1)) :=
          Finset.sum_le_sum fun p hp => sum_inv_pow_ge_two_le (Finset.mem_filter.mp hp).2.two_le N
      _ ≤ ∑ m ∈ Finset.Icc 2 N, 1 / ((m : ℝ) * ((m : ℝ) - 1)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun m hm _ => ?_)
          · exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp hp).2.two_le,
              (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2⟩
          · have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
            exact div_nonneg zero_le_one (by nlinarith)
      _ ≤ 1 := by
          by_cases hN2 : 2 ≤ N
          · rw [sum_telescoping_Icc_two hN2]
            have : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
            linarith
          · have hempty : Finset.Icc 2 N = ∅ := Finset.Icc_eq_empty (by omega)
            rw [hempty, Finset.sum_empty]
            exact zero_le_one
  -- Sum 2 (diagonal `a.1 = b.1`): `∑_{p ∈ P} ∑_{k, j ∈ K} 1 / p^(max k j) ≤ 4`
  have hsum2 : ∑ p ∈ P, ∑ k ∈ K, ∑ j ∈ K, ((p : ℝ) ^ max k j)⁻¹ ≤ 4 := by
    have hp_bd : ∀ p ∈ P, ∑ k ∈ K, ∑ j ∈ K, ((p : ℝ) ^ max k j)⁻¹ ≤
        2 / ((p : ℝ) - 1) ^ 2 := by
      intro p hp
      have hp2 : 2 ≤ p := (Finset.mem_filter.mp hp).2.two_le
      have hsym : ∑ k ∈ K, ∑ j ∈ K, ((p : ℝ) ^ max k j)⁻¹ ≤
          2 * ∑ k ∈ K, ((k - 1 : ℕ) : ℝ) * ((p : ℝ) ^ k)⁻¹ := by
        have hpt : ∀ k ∈ K, ∀ j ∈ K,
            ((p : ℝ) ^ max k j)⁻¹ ≤
              (if j ≤ k then ((p : ℝ) ^ k)⁻¹ else 0) + (if k ≤ j then ((p : ℝ) ^ j)⁻¹ else 0) := by
          intro k _ j _
          rcases le_total j k with hle | hle
          · rw [max_eq_left hle, if_pos hle]
            have hnn : 0 ≤ (if k ≤ j then ((p : ℝ) ^ j)⁻¹ else 0) := by split_ifs <;> positivity
            linarith
          · rw [max_eq_right hle, if_pos hle]
            have hnn : 0 ≤ (if j ≤ k then ((p : ℝ) ^ k)⁻¹ else 0) := by split_ifs <;> positivity
            linarith
        have h1 : ∑ k ∈ K, ∑ j ∈ K, ((p : ℝ) ^ max k j)⁻¹ ≤
            (∑ k ∈ K, ∑ j ∈ K, if j ≤ k then ((p : ℝ) ^ k)⁻¹ else 0) +
            (∑ k ∈ K, ∑ j ∈ K, if k ≤ j then ((p : ℝ) ^ j)⁻¹ else 0) := by
          simp_rw [← Finset.sum_add_distrib]
          exact Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun j hj => hpt k hk j hj
        have hswap : ∑ k ∈ K, ∑ j ∈ K, (if k ≤ j then ((p : ℝ) ^ j)⁻¹ else 0) =
            ∑ k ∈ K, ∑ j ∈ K, (if j ≤ k then ((p : ℝ) ^ k)⁻¹ else 0) := by
          rw [Finset.sum_comm]
        have heval : ∑ k ∈ K, ∑ j ∈ K, (if j ≤ k then ((p : ℝ) ^ k)⁻¹ else 0) =
            ∑ k ∈ K, ((k - 1 : ℕ) : ℝ) * ((p : ℝ) ^ k)⁻¹ := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          congr 1
          have hfilt : K.filter (fun j => j ≤ k) = Finset.Icc 2 k := by
            ext j
            simp only [K, Finset.mem_filter, Finset.mem_Icc]
            have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
            omega
          rw [hfilt, Nat.card_Icc]
          have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
          have hnat : k + 1 - 2 = k - 1 := by omega
          rw [hnat]
        linarith
      calc ∑ k ∈ K, ∑ j ∈ K, ((p : ℝ) ^ max k j)⁻¹
          ≤ 2 * ∑ k ∈ K, ((k - 1 : ℕ) : ℝ) * ((p : ℝ) ^ k)⁻¹ := hsym
        _ ≤ 2 * (1 / ((p : ℝ) - 1) ^ 2) :=
            mul_le_mul_of_nonneg_left (sum_weighted_inv_pow_ge_two_le hp2 N) (by norm_num)
        _ = 2 / ((p : ℝ) - 1) ^ 2 := by ring
    calc ∑ p ∈ P, ∑ k ∈ K, ∑ j ∈ K, ((p : ℝ) ^ max k j)⁻¹
        ≤ ∑ p ∈ P, 2 / ((p : ℝ) - 1) ^ 2 := Finset.sum_le_sum hp_bd
      _ ≤ ∑ m ∈ Finset.Icc 2 N, 2 / ((m : ℝ) - 1) ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun _ _ _ => by positivity)
          exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp hp).2.two_le,
            (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2⟩
      _ ≤ 4 := by
          by_cases hN2 : 2 ≤ N
          · have hsplit : Finset.Icc 2 N = insert 2 (Finset.Icc 3 N) := by
              ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            rw [hsplit, Finset.sum_insert (by simp)]
            have h2val : (2 : ℝ) / (((2 : ℕ) : ℝ) - 1) ^ 2 = 2 := by norm_num
            rw [h2val]
            have htail : ∑ m ∈ Finset.Icc 3 N, 2 / ((m : ℝ) - 1) ^ 2 ≤ 2 := by
              have hpt : ∀ m ∈ Finset.Icc 3 N,
                  (2 : ℝ) / ((m : ℝ) - 1) ^ 2 ≤
                    2 * (1 / (((m - 1 : ℕ) : ℝ) * (((m - 1 : ℕ) : ℝ) - 1))) := by
                intro m hm
                have hm3 : 3 ≤ m := (Finset.mem_Icc.mp hm).1
                have hmR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
                have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
                  rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
                rw [hm1]
                have hpos1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
                have hpos2 : (0 : ℝ) < (m : ℝ) - 2 := by linarith
                rw [mul_one_div, div_le_div_iff₀ (sq_pos_of_pos hpos1) (by nlinarith)]
                nlinarith
              calc ∑ m ∈ Finset.Icc 3 N, 2 / ((m : ℝ) - 1) ^ 2
                  ≤ ∑ m ∈ Finset.Icc 3 N,
                      2 * (1 / (((m - 1 : ℕ) : ℝ) * (((m - 1 : ℕ) : ℝ) - 1))) :=
                    Finset.sum_le_sum hpt
                _ = 2 * ∑ m ∈ Finset.Icc 3 N,
                      1 / (((m - 1 : ℕ) : ℝ) * (((m - 1 : ℕ) : ℝ) - 1)) := by
                    rw [Finset.mul_sum]
                _ ≤ 2 * 1 := by
                    gcongr
                    by_cases hN3 : 3 ≤ N
                    · rw [sum_telescoping_Icc_three hN3]
                      have : (0 : ℝ) ≤ ((N - 1 : ℕ) : ℝ)⁻¹ := by positivity
                      linarith
                    · have hempty : Finset.Icc 3 N = ∅ := Finset.Icc_eq_empty (by omega)
                      rw [hempty, Finset.sum_empty]
                      exact zero_le_one
                _ = 2 := by ring
            linarith
          · have hempty : Finset.Icc 2 N = ∅ := Finset.Icc_eq_empty (by omega)
            rw [hempty, Finset.sum_empty]
            norm_num
  -- Combine both sums!
  calc ∑ a ∈ PK, ∑ b ∈ PK, ∑ n ∈ Finset.Icc 1 N,
          (if a.1 ^ a.2 ∣ n ∧ b.1 ^ b.2 ∣ n then (1 : ℝ) else 0)
      ≤ ∑ a ∈ PK, ∑ b ∈ PK,
          ((N : ℝ) * ((a.1 : ℝ) ^ a.2)⁻¹ * ((b.1 : ℝ) ^ b.2)⁻¹ +
            if a.1 = b.1 then (N : ℝ) * ((a.1 : ℝ) ^ (max a.2 b.2))⁻¹ else 0) :=
        Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hinner a ha b hb
    _ = (∑ a ∈ PK, ∑ b ∈ PK, (N : ℝ) * ((a.1 : ℝ) ^ a.2)⁻¹ * ((b.1 : ℝ) ^ b.2)⁻¹) +
        (∑ a ∈ PK, ∑ b ∈ PK, if a.1 = b.1 then (N : ℝ) * ((a.1 : ℝ) ^ (max a.2 b.2))⁻¹ else 0) := by
        simp_rw [Finset.sum_add_distrib]
    _ = (N : ℝ) * (∑ a ∈ PK, ((a.1 : ℝ) ^ a.2)⁻¹) ^ 2 +
        (N : ℝ) * ∑ p ∈ P, ∑ k ∈ K, ∑ j ∈ K, ((p : ℝ) ^ max k j)⁻¹ := by
        congr 1
        · rw [sq, Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => by ring
        · dsimp only [PK]
          rw [Finset.sum_product]
          simp_rw [Finset.sum_product]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_comm]
          have hcollapse : ∀ j ∈ K,
              (∑ q ∈ P, if p = q then (N : ℝ) * ((p : ℝ) ^ max k j)⁻¹ else 0) =
                (N : ℝ) * ((p : ℝ) ^ max k j)⁻¹ := fun j _ => by
            rw [Finset.sum_ite_eq P p (fun _ => (N : ℝ) * ((p : ℝ) ^ max k j)⁻¹), if_pos hp]
          rw [Finset.sum_congr rfl hcollapse, Finset.mul_sum]
    _ ≤ (N : ℝ) * 1 ^ 2 + (N : ℝ) * 4 := by
        have hsq1 : (∑ a ∈ PK, ((a.1 : ℝ) ^ a.2)⁻¹) ^ 2 ≤ 1 ^ 2 :=
          pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) hsum1 2
        gcongr
    _ = 5 * (N : ℝ) := by ring

/-- **TURÁN'S 1934 SECOND-MOMENT INEQUALITY FOR `Ω(n)` (`0` ASSUMPTIONS!)**:
`∃ C > 0, ∀ x ≥ 3, ∑_{n ≤ x} (Ω(n) - log log x)² ≤ C * x * log log x`. -/
theorem turan_second_moment_Omega :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Ω n : ℝ) - Real.log (Real.log x)) ^ 2 ≤
        C * x * Real.log (Real.log x) := by
  obtain ⟨C_ω, hC_ω, hTω⟩ := turan_second_moment_omega
  have hlog3_pos : 0 < Real.log 3 := zero_lt_one.trans one_lt_log_three
  have hLL3_pos : 0 < Real.log (Real.log 3) := log_log_pos_of_ge_three le_rfl
  set C : ℝ := 2 * C_ω + 10 / Real.log (Real.log 3)
  refine ⟨C, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hL_ge : Real.log (Real.log 3) ≤ Real.log (Real.log x) :=
    Real.log_le_log hlog3_pos (Real.log_le_log (by norm_num) hx)
  have hpt : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊,
      ((Ω n : ℝ) - Real.log (Real.log x)) ^ 2 ≤
        2 * ((ω n : ℝ) - Real.log (Real.log x)) ^ 2 + 2 * ((Ω n : ℝ) - (ω n : ℝ)) ^ 2 := by
    intro n _
    nlinarith [sq_nonneg (((ω n : ℝ) - Real.log (Real.log x)) - ((Ω n : ℝ) - (ω n : ℝ)))]
  have h1 := hTω x hx
  have h2 : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Ω n : ℝ) - (ω n : ℝ)) ^ 2 ≤ 5 * x :=
    (sum_Omega_sub_omega_sq_le ⌊x⌋₊).trans
      (mul_le_mul_of_nonneg_left (Nat.floor_le hx0.le) (by norm_num))
  have hx_le : x ≤ x * Real.log (Real.log x) / Real.log (Real.log 3) := by
    rw [le_div_iff₀ hLL3_pos]
    exact mul_le_mul_of_nonneg_left hL_ge hx0.le
  calc ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Ω n : ℝ) - Real.log (Real.log x)) ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          (2 * ((ω n : ℝ) - Real.log (Real.log x)) ^ 2 + 2 * ((Ω n : ℝ) - (ω n : ℝ)) ^ 2) :=
        Finset.sum_le_sum hpt
    _ = 2 * (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ω n : ℝ) - Real.log (Real.log x)) ^ 2) +
          2 * (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Ω n : ℝ) - (ω n : ℝ)) ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (C_ω * x * Real.log (Real.log x)) + 2 * (5 * x) := by gcongr
    _ ≤ 2 * (C_ω * x * Real.log (Real.log x)) +
          10 * (x * Real.log (Real.log x) / Real.log (Real.log 3)) := by nlinarith
    _ = C * x * Real.log (Real.log x) := by dsimp only [C]; ring

/-- **EXACT FIRST MOMENT OF `Ω(n)` (`0` ASSUMPTIONS!)**:
`∃ C > 0, ∀ x ≥ 3, |∑_{n ≤ x} Ω(n) - x * log (log x)| ≤ C * x`. -/
theorem sum_Omega_asymp :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Ω n : ℝ) - x * Real.log (Real.log x)| ≤ C * x := by
  obtain ⟨C_ω, hC_ω, hω⟩ := sum_omega_asymp
  refine ⟨C_ω + 5, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hdiff_nn : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, 0 ≤ (Ω n : ℝ) - (ω n : ℝ) := fun n _ => by
    have hle : ω n ≤ Ω n := by
      rw [ArithmeticFunction.cardDistinctFactors_apply, ArithmeticFunction.cardFactors_apply]
      exact (n.primeFactorsList.dedup_sublist).length_le
    exact sub_nonneg.mpr (by exact_mod_cast hle)
  have hdiff_le_sq : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊,
      (Ω n : ℝ) - (ω n : ℝ) ≤ ((Ω n : ℝ) - (ω n : ℝ)) ^ 2 := fun n _ => by
    have hle : ω n ≤ Ω n := by
      rw [ArithmeticFunction.cardDistinctFactors_apply, ArithmeticFunction.cardFactors_apply]
      exact (n.primeFactorsList.dedup_sublist).length_le
    have hnat : (Ω n - ω n : ℕ) ≤ (Ω n - ω n : ℕ) ^ 2 := by nlinarith
    have hcast : ((Ω n - ω n : ℕ) : ℝ) = (Ω n : ℝ) - (ω n : ℝ) := Nat.cast_sub hle
    rw [← hcast]
    exact_mod_cast hnat
  have hsum_diff : |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Ω n : ℝ) - (ω n : ℝ))| ≤ 5 * x := by
    rw [abs_of_nonneg (Finset.sum_nonneg hdiff_nn)]
    calc ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Ω n : ℝ) - (ω n : ℝ))
        ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Ω n : ℝ) - (ω n : ℝ)) ^ 2 := Finset.sum_le_sum hdiff_le_sq
      _ ≤ 5 * (⌊x⌋₊ : ℝ) := sum_Omega_sub_omega_sq_le ⌊x⌋₊
      _ ≤ 5 * x := mul_le_mul_of_nonneg_left (Nat.floor_le hx0.le) (by norm_num)
  have hrew : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Ω n : ℝ) - x * Real.log (Real.log x) =
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ω n : ℝ) - x * Real.log (Real.log x)) +
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Ω n : ℝ) - (ω n : ℝ)) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [hrew]
  calc |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ω n : ℝ) - x * Real.log (Real.log x)) +
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Ω n : ℝ) - (ω n : ℝ))|
      ≤ |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ω n : ℝ) - x * Real.log (Real.log x)| +
        |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Ω n : ℝ) - (ω n : ℝ))| := abs_add_le _ _
    _ ≤ C_ω * x + 5 * x := add_le_add (hω x hx) hsum_diff
    _ = (C_ω + 5) * x := by ring

/-- Shared Chebyshev / Hardy–Ramanujan engine: any arithmetic function `f : ℕ → ℕ` obeying
Turán's second-moment bound `∑_{n ≤ x} (f n - log log x)² ≤ C x log log x` (`x ≥ 3`) has
sharp normal order `log log n` with fluctuation scale `(log log n)^{1/2 + ε}` for every `ε > 0`. -/
private theorem normal_order_sharp_of_turan (f : ℕ → ℕ)
    (hTuran : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((f n : ℝ) - Real.log (Real.log x)) ^ 2 ≤
        C * x * Real.log (Real.log x)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N : ℕ =>
        (((Finset.Icc 1 N).filter (fun n =>
          |(f n : ℝ) - Real.log (Real.log (n : ℝ))| >
            (Real.log (Real.log (n : ℝ))) ^ ((1 / 2 : ℝ) + ε))).card : ℝ) / (N : ℝ))
        atTop (𝓝 0) := by
  obtain ⟨C, hC, hT⟩ := hTuran
  intro ε hε
  set cε : ℝ := (1 / 2 : ℝ) ^ ((3 / 2 : ℝ) + ε)
  have hcε_pos : 0 < cε := by positivity
  -- Tendsto `log (log N) → ∞`
  have hLL_top : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  -- Upper envelope `1 / √N + (C / cε²) * (log log N)^(-2 ε) → 0`
  have hdom_lim : Tendsto (fun N : ℕ =>
      (Real.sqrt (N : ℝ))⁻¹ +
        (C / cε ^ 2) * (Real.log (Real.log (N : ℝ))) ^ (-(2 * ε))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (Real.sqrt (N : ℝ))⁻¹) atTop (𝓝 0) := by
      have hsq : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
        (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop
          |>.congr fun N => (Real.sqrt_eq_rpow (N : ℝ)).symm
      exact tendsto_inv_atTop_zero.comp hsq
    have h2 : Tendsto (fun N : ℕ => (C / cε ^ 2) * (Real.log (Real.log (N : ℝ))) ^ (-(2 * ε)))
        atTop (𝓝 0) := by
      have hpow : Tendsto (fun N : ℕ => (Real.log (Real.log (N : ℝ))) ^ (-(2 * ε)))
          atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (by positivity : 0 < 2 * ε)).comp hLL_top
      simpa using hpow.const_mul (C / cε ^ 2)
    simpa using h1.add h2
  -- Threshold `M₀` so that `L ≥ 2 * log 2` and `cε * L^(1/2 + ε) ≥ log 2`
  set M₀ : ℝ := max (2 * Real.log 2) (2 * ((2 * Real.log 2) ^ (((1 / 2 : ℝ) + ε)⁻¹)))
  have hev_L : ∀ᶠ N : ℕ in atTop, M₀ ≤ Real.log (Real.log (N : ℝ)) :=
    hLL_top.eventually_ge_atTop M₀
  have hev_N : ∀ᶠ N : ℕ in atTop, 16 ≤ N := eventually_ge_atTop 16
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ hdom_lim
  filter_upwards [hev_N, hev_L] with N hN16 hLM
  have hNR3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 3 ≤ N)
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  set L : ℝ := Real.log (Real.log (N : ℝ))
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL_ge_2log2 : 2 * Real.log 2 ≤ L := (le_max_left _ _).trans hLM
  have hL_pos : 0 < L := by linarith
  have hhalfL_pos : 0 < L / 2 := by linarith
  have hlog2_le_halfpow : Real.log 2 ≤ (1 / 2 : ℝ) * (L / 2) ^ ((1 / 2 : ℝ) + ε) := by
    have h1 : (2 * Real.log 2) ^ (((1 / 2 : ℝ) + ε)⁻¹) ≤ L / 2 := by
      have h := (le_max_right (2 * Real.log 2) _).trans hLM
      linarith
    have hexp_pos : (0 : ℝ) < (1 / 2 : ℝ) + ε := by positivity
    have h2 := Real.rpow_le_rpow (by positivity) h1 hexp_pos.le
    rw [← Real.rpow_mul (by positivity), inv_mul_cancel₀ hexp_pos.ne', Real.rpow_one] at h2
    linarith
  -- Split bad set at `m = Nat.sqrt N`
  set m : ℕ := Nat.sqrt N
  set Bad : Finset ℕ := (Finset.Icc 1 N).filter (fun n =>
    |(f n : ℝ) - Real.log (Real.log (n : ℝ))| >
      (Real.log (Real.log (n : ℝ))) ^ ((1 / 2 : ℝ) + ε))
  set Bad₁ : Finset ℕ := Bad.filter (fun n => n ≤ m)
  set Bad₂ : Finset ℕ := Bad.filter (fun n => m < n)
  have hsplit : Bad.card = Bad₁.card + Bad₂.card := by
    have hdisj : Disjoint Bad₁ Bad₂ := Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
    have hunion : Bad₁ ∪ Bad₂ = Bad := by
      ext n; simp only [Bad₁, Bad₂, Finset.mem_union, Finset.mem_filter]; constructor
      · rintro (h | h) <;> exact h.1
      · intro hn; by_cases h : n ≤ m <;> [left; right] <;> exact ⟨hn, by omega⟩
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  -- Bound `Bad₁.card / N ≤ (√N)⁻¹`
  have hBad₁ : (Bad₁.card : ℝ) / (N : ℝ) ≤ (Real.sqrt (N : ℝ))⁻¹ := by
    have hcard : Bad₁.card ≤ m := by
      have hsub : Bad₁ ⊆ Finset.Icc 1 m := fun n hn => by
        have h1 := Finset.mem_filter.mp hn
        have hI := (Finset.mem_filter.mp h1.1).1
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hI).1, h1.2⟩
      exact (Finset.card_le_card hsub).trans (by rw [Nat.card_Icc]; omega)
    have hm_le : (m : ℝ) ≤ Real.sqrt (N : ℝ) := by
      rw [Real.le_sqrt (Nat.cast_nonneg m) hNpos.le, sq]
      exact_mod_cast Nat.sqrt_le N
    have h1 : (Bad₁.card : ℝ) ≤ Real.sqrt (N : ℝ) := (Nat.cast_le.mpr hcard).trans hm_le
    rw [div_le_iff₀ hNpos]
    calc (Bad₁.card : ℝ)
        ≤ Real.sqrt (N : ℝ) := h1
      _ = (Real.sqrt (N : ℝ))⁻¹ * (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) := by
          have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hNpos).ne'
          field_simp [hs]
      _ = (Real.sqrt (N : ℝ))⁻¹ * (N : ℝ) := by rw [Real.mul_self_sqrt hNpos.le]
  -- Bound `Bad₂.card` via Chebyshev on `hT`
  have hBad₂_pt : ∀ n ∈ Bad₂,
      cε * L ^ ((1 / 2 : ℝ) + ε) ≤ |(f n : ℝ) - L| := by
    intro n hn
    obtain ⟨hnBad, hnm⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnI, hgt⟩ := Finset.mem_filter.mp hnBad
    have hn_le_N : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hnI).2
    have hsqrt_le_n : Real.sqrt (N : ℝ) ≤ (n : ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨Nat.cast_nonneg n, ?_⟩
      have hnat : N < n * n := by
        have h1 : m + 1 ≤ n := hnm
        have h2 : N < (m + 1) * (m + 1) := Nat.lt_succ_sqrt N
        nlinarith
      rw [sq]; exact_mod_cast hnat.le
    have hn_pos : (0 : ℝ) < (n : ℝ) := (Real.sqrt_pos.mpr hNpos).trans_le hsqrt_le_n
    have hlogn_ge : (Real.log (N : ℝ)) / 2 ≤ Real.log (n : ℝ) := by
      have h1 : Real.log (Real.sqrt (N : ℝ)) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (Real.sqrt_pos.mpr hNpos) hsqrt_le_n
      rwa [Real.log_sqrt hNpos.le] at h1
    have hlogn_le : Real.log (n : ℝ) ≤ Real.log (N : ℝ) := Real.log_le_log hn_pos hn_le_N
    have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
    have hlogn_pos : 0 < Real.log (n : ℝ) := by linarith
    have hLLn_ge : L - Real.log 2 ≤ Real.log (Real.log (n : ℝ)) := by
      have h1 : Real.log ((Real.log (N : ℝ)) / 2) ≤ Real.log (Real.log (n : ℝ)) :=
        Real.log_le_log (by positivity) hlogn_ge
      rwa [Real.log_div hlogN_pos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at h1
    have hLLn_le : Real.log (Real.log (n : ℝ)) ≤ L := Real.log_le_log hlogn_pos hlogn_le
    have hLLn_ge_half : L / 2 ≤ Real.log (Real.log (n : ℝ)) := by linarith
    have hpow_ge : (L / 2) ^ ((1 / 2 : ℝ) + ε) ≤
        (Real.log (Real.log (n : ℝ))) ^ ((1 / 2 : ℝ) + ε) :=
      Real.rpow_le_rpow hhalfL_pos.le hLLn_ge_half (by positivity)
    have htri : |(f n : ℝ) - Real.log (Real.log (n : ℝ))| - Real.log 2 ≤ |(f n : ℝ) - L| := by
      have hdiff : |L - Real.log (Real.log (n : ℝ))| ≤ Real.log 2 := by
        rw [abs_of_nonneg (by linarith)]; linarith
      have h1 : |(f n : ℝ) - Real.log (Real.log (n : ℝ))| ≤
          |(f n : ℝ) - L| + |L - Real.log (Real.log (n : ℝ))| := by
        have hrew : (f n : ℝ) - Real.log (Real.log (n : ℝ)) =
            ((f n : ℝ) - L) + (L - Real.log (Real.log (n : ℝ))) := by ring
        rw [hrew]; exact abs_add_le _ _
      linarith
    have hcε_eq : cε * L ^ ((1 / 2 : ℝ) + ε) = (1 / 2 : ℝ) * (L / 2) ^ ((1 / 2 : ℝ) + ε) := by
      dsimp only [cε]
      rw [show L / 2 = (1 / 2 : ℝ) * L by ring,
        Real.mul_rpow (by norm_num) hL_pos.le, ← mul_assoc,
        ← Real.rpow_one_add' (by norm_num : (0 : ℝ) ≤ 1 / 2) (by positivity)]
      congr 2; ring
    rw [hcε_eq]
    linarith
  have hBad₂_sub : Bad₂ ⊆ Finset.Icc 1 N := fun n hn =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
  have hCheb : (Bad₂.card : ℝ) * (cε * L ^ ((1 / 2 : ℝ) + ε)) ^ 2 ≤ C * (N : ℝ) * L := by
    have h1 : (Bad₂.card : ℝ) * (cε * L ^ ((1 / 2 : ℝ) + ε)) ^ 2 ≤
        ∑ n ∈ Bad₂, ((f n : ℝ) - L) ^ 2 := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun n hn => ?_
      rw [← sq_abs ((f n : ℝ) - L)]
      exact pow_le_pow_left₀ (by positivity) (hBad₂_pt n hn) 2
    have h2 : ∑ n ∈ Bad₂, ((f n : ℝ) - L) ^ 2 ≤ ∑ n ∈ Finset.Icc 1 N, ((f n : ℝ) - L) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hBad₂_sub fun _ _ _ => sq_nonneg _
    have h3 := hT (N : ℝ) hNR3
    rw [Nat.floor_natCast] at h3
    exact (h1.trans h2).trans h3
  have hBad₂ : (Bad₂.card : ℝ) / (N : ℝ) ≤ (C / cε ^ 2) * L ^ (-(2 * ε)) := by
    have hpow_sq : (cε * L ^ ((1 / 2 : ℝ) + ε)) ^ 2 = cε ^ 2 * L ^ (1 + 2 * ε) := by
      rw [mul_pow, ← Real.rpow_natCast (L ^ ((1 / 2 : ℝ) + ε)) 2, ← Real.rpow_mul hL_pos.le]
      congr 2; ring
    rw [hpow_sq] at hCheb
    have hden_pos : 0 < (N : ℝ) * (cε ^ 2 * L ^ (1 + 2 * ε)) := by positivity
    rw [div_le_iff₀ hNpos]
    have hL_split : L / L ^ (1 + 2 * ε) = L ^ (-(2 * ε)) := by
      conv_lhs => arg 1; rw [← Real.rpow_one L]
      rw [← Real.rpow_sub hL_pos]
      congr 1; ring
    have hdiv := (le_div_iff₀ (by positivity : 0 < cε ^ 2 * L ^ (1 + 2 * ε))).mpr hCheb
    calc (Bad₂.card : ℝ)
        ≤ C * (N : ℝ) * L / (cε ^ 2 * L ^ (1 + 2 * ε)) := hdiv
      _ = (C / cε ^ 2) * (L / L ^ (1 + 2 * ε)) * (N : ℝ) := by ring
      _ = (C / cε ^ 2) * L ^ (-(2 * ε)) * (N : ℝ) := by rw [hL_split]
  rw [hsplit, Nat.cast_add, add_div]
  exact add_le_add hBad₁ hBad₂

/-- Deduce the classical `ε * log log n` normal-order theorem from the sharp `(log log n)^{1/2 + ε}`
version for any `f : ℕ → ℕ`. -/
private theorem normal_order_of_sharp (f : ℕ → ℕ)
    (hsharp : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N : ℕ =>
        (((Finset.Icc 1 N).filter (fun n =>
          |(f n : ℝ) - Real.log (Real.log (n : ℝ))| >
            (Real.log (Real.log (n : ℝ))) ^ ((1 / 2 : ℝ) + ε))).card : ℝ) / (N : ℝ))
        atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N : ℕ =>
        (((Finset.Icc 1 N).filter (fun n =>
          |(f n : ℝ) - Real.log (Real.log (n : ℝ))| >
            ε * Real.log (Real.log (n : ℝ)))).card : ℝ) / (N : ℝ))
        atTop (𝓝 0) := by
  intro ε hε
  have hquarter := hsharp (1 / 4 : ℝ) (by norm_num)
  have hLL_top : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hsqrt_lim : Tendsto (fun N : ℕ => (Real.sqrt (N : ℝ))⁻¹) atTop (𝓝 0) := by
    have hsq : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop
        |>.congr fun N => (Real.sqrt_eq_rpow (N : ℝ)).symm
    exact tendsto_inv_atTop_zero.comp hsq
  have hdom_lim : Tendsto (fun N : ℕ =>
      (Real.sqrt (N : ℝ))⁻¹ +
        (((Finset.Icc 1 N).filter (fun n =>
          |(f n : ℝ) - Real.log (Real.log (n : ℝ))| >
            (Real.log (Real.log (n : ℝ))) ^ ((1 / 2 : ℝ) + (1 / 4 : ℝ)))).card : ℝ) / (N : ℝ))
      atTop (𝓝 0) := by
    simpa using hsqrt_lim.add hquarter
  set M₁ : ℝ := Real.log 2 + max (ε⁻¹ ^ 4) 1
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ hdom_lim
  filter_upwards [eventually_ge_atTop 16, hLL_top.eventually_ge_atTop M₁] with N hN16 hLM
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  set m : ℕ := Nat.sqrt N
  set Bad : Finset ℕ := (Finset.Icc 1 N).filter (fun n =>
    |(f n : ℝ) - Real.log (Real.log (n : ℝ))| > ε * Real.log (Real.log (n : ℝ)))
  set Bad₁ : Finset ℕ := Bad.filter (fun n => n ≤ m)
  set Bad₂ : Finset ℕ := Bad.filter (fun n => m < n)
  have hsplit : Bad.card = Bad₁.card + Bad₂.card := by
    have hdisj : Disjoint Bad₁ Bad₂ := Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
    have hunion : Bad₁ ∪ Bad₂ = Bad := by
      ext n; simp only [Bad₁, Bad₂, Finset.mem_union, Finset.mem_filter]; constructor
      · rintro (h | h) <;> exact h.1
      · intro hn; by_cases h : n ≤ m <;> [left; right] <;> exact ⟨hn, by omega⟩
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have hBad₁ : (Bad₁.card : ℝ) / (N : ℝ) ≤ (Real.sqrt (N : ℝ))⁻¹ := by
    have hcard : Bad₁.card ≤ m := by
      have hsub : Bad₁ ⊆ Finset.Icc 1 m := fun n hn => by
        have h1 := Finset.mem_filter.mp hn
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp h1.1).1).1, h1.2⟩
      exact (Finset.card_le_card hsub).trans (by rw [Nat.card_Icc]; omega)
    have hm_le : (m : ℝ) ≤ Real.sqrt (N : ℝ) := by
      rw [Real.le_sqrt (Nat.cast_nonneg m) hNpos.le, sq]
      exact_mod_cast Nat.sqrt_le N
    have h1 : (Bad₁.card : ℝ) ≤ Real.sqrt (N : ℝ) := (Nat.cast_le.mpr hcard).trans hm_le
    rw [div_le_iff₀ hNpos]
    calc (Bad₁.card : ℝ) ≤ Real.sqrt (N : ℝ) := h1
      _ = (Real.sqrt (N : ℝ))⁻¹ * (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) := by
          have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hNpos).ne'
          field_simp [hs]
      _ = (Real.sqrt (N : ℝ))⁻¹ * (N : ℝ) := by rw [Real.mul_self_sqrt hNpos.le]
  have hBad₂_sub : Bad₂ ⊆ (Finset.Icc 1 N).filter (fun n =>
      |(f n : ℝ) - Real.log (Real.log (n : ℝ))| >
        (Real.log (Real.log (n : ℝ))) ^ ((1 / 2 : ℝ) + (1 / 4 : ℝ))) := by
    intro n hn
    obtain ⟨hnBad, hnm⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnI, hgt⟩ := Finset.mem_filter.mp hnBad
    refine Finset.mem_filter.mpr ⟨hnI, ?_⟩
    have hsqrt_le_n : Real.sqrt (N : ℝ) ≤ (n : ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨Nat.cast_nonneg n, ?_⟩
      have hnat : N < n * n := by
        have h1 : m + 1 ≤ n := hnm
        have h2 : N < (m + 1) * (m + 1) := Nat.lt_succ_sqrt N
        nlinarith
      rw [sq]; exact_mod_cast hnat.le
    have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have hlogn_ge : (Real.log (N : ℝ)) / 2 ≤ Real.log (n : ℝ) := by
      have h1 := Real.log_le_log (Real.sqrt_pos.mpr hNpos) hsqrt_le_n
      rwa [Real.log_sqrt hNpos.le] at h1
    have hLLn_ge : Real.log (Real.log (N : ℝ)) - Real.log 2 ≤ Real.log (Real.log (n : ℝ)) := by
      have h1 := Real.log_le_log (by positivity : 0 < Real.log (N : ℝ) / 2) hlogn_ge
      rwa [Real.log_div hlogN_pos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at h1
    set t : ℝ := Real.log (Real.log (n : ℝ))
    have ht_ge_eps : ε⁻¹ ^ 4 ≤ t := by
      have h1 : max (ε⁻¹ ^ 4) 1 ≤ t := by dsimp only [M₁] at hLM; linarith
      exact (le_max_left _ _).trans h1
    have ht_pos : 0 < t := by
      have h1 : max (ε⁻¹ ^ 4) 1 ≤ t := by dsimp only [M₁] at hLM; linarith
      linarith [le_max_right (ε⁻¹ ^ 4) (1 : ℝ)]
    have hpow_le : t ^ ((1 / 2 : ℝ) + (1 / 4 : ℝ)) ≤ ε * t := by
      have h1 : ε⁻¹ ≤ t ^ (1 / 4 : ℝ) := by
        have h2 := Real.rpow_le_rpow (by positivity) ht_ge_eps (by norm_num : (0 : ℝ) ≤ 1 / 4)
        rw [← Real.rpow_natCast (ε⁻¹) 4, ← Real.rpow_mul (by positivity)] at h2
        norm_num at h2
        exact h2
      have hmul : 1 ≤ ε * t ^ (1 / 4 : ℝ) := by
        have := mul_le_mul_of_nonneg_left h1 hε.le
        rwa [mul_inv_cancel₀ hε.ne'] at this
      have h2 := mul_le_mul_of_nonneg_right hmul (Real.rpow_nonneg ht_pos.le (3 / 4 : ℝ))
      rw [one_mul, mul_assoc, ← Real.rpow_add ht_pos] at h2
      norm_num at h2 ⊢
      exact h2
    exact lt_of_le_of_lt hpow_le hgt
  rw [hsplit, Nat.cast_add, add_div]
  refine add_le_add hBad₁ ?_
  gcongr

/-- **SHARP HARDY–RAMANUJAN 1917 NORMAL ORDER OF `ω(n)` (`(log log n)^{1/2 + ε}`, 0 ASSUMPTIONS!)**. -/
theorem hardy_ramanujan_normal_order_omega_sharp :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N : ℕ =>
        (((Finset.Icc 1 N).filter (fun n =>
          |(ω n : ℝ) - Real.log (Real.log (n : ℝ))| >
            (Real.log (Real.log (n : ℝ))) ^ ((1 / 2 : ℝ) + ε))).card : ℝ) / (N : ℝ))
        atTop (𝓝 0) :=
  normal_order_sharp_of_turan (fun n => ω n) turan_second_moment_omega

/-- **HARDY–RAMANUJAN 1917 NORMAL ORDER THEOREM FOR `ω(n)` (`0` ASSUMPTIONS!)**:
for every `ε > 0`, the natural density of `n ≤ N` with `|ω(n) - log log n| > ε * log log n`
tends to `0` as `N → ∞`. -/
theorem hardy_ramanujan_normal_order_omega :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N : ℕ =>
        (((Finset.Icc 1 N).filter (fun n =>
          |(ω n : ℝ) - Real.log (Real.log (n : ℝ))| >
            ε * Real.log (Real.log (n : ℝ)))).card : ℝ) / (N : ℝ))
        atTop (𝓝 0) :=
  normal_order_of_sharp (fun n => ω n) hardy_ramanujan_normal_order_omega_sharp

/-- **SHARP HARDY–RAMANUJAN 1917 NORMAL ORDER OF `Ω(n)` (`(log log n)^{1/2 + ε}`, 0 ASSUMPTIONS!)**. -/
theorem hardy_ramanujan_normal_order_Omega_sharp :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N : ℕ =>
        (((Finset.Icc 1 N).filter (fun n =>
          |(Ω n : ℝ) - Real.log (Real.log (n : ℝ))| >
            (Real.log (Real.log (n : ℝ))) ^ ((1 / 2 : ℝ) + ε))).card : ℝ) / (N : ℝ))
        atTop (𝓝 0) :=
  normal_order_sharp_of_turan (fun n => Ω n) turan_second_moment_Omega

/-- **HARDY–RAMANUJAN 1917 NORMAL ORDER THEOREM FOR `Ω(n)` (`0` ASSUMPTIONS!)**:
for every `ε > 0`, the natural density of `n ≤ N` with `|Ω(n) - log log n| > ε * log log n`
tends to `0` as `N → ∞`. -/
theorem hardy_ramanujan_normal_order_Omega :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N : ℕ =>
        (((Finset.Icc 1 N).filter (fun n =>
          |(Ω n : ℝ) - Real.log (Real.log (n : ℝ))| >
            ε * Real.log (Real.log (n : ℝ)))).card : ℝ) / (N : ℝ))
        atTop (𝓝 0) :=
  normal_order_of_sharp (fun n => Ω n) hardy_ramanujan_normal_order_Omega_sharp

/-! ## Section 3: Dirichlet's Divisor-Function Average (Dirichlet Hyperbola Method) -/

/-- **Exact Dirichlet Hyperbola Identity**:
for every `N : ℕ` and `u = Nat.sqrt N`,
`∑_{n=1}^N d(n) + u² = 2 * ∑_{d=1}^u ⌊N / d⌋`. -/
theorem dirichlet_hyperbola_identity (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, σ 0 n + (Nat.sqrt N) ^ 2 =
      2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), N / d := by
  set u : ℕ := Nat.sqrt N
  set S : Finset (ℕ × ℕ) := (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun ab => ab.1 * ab.2 ≤ N)
  set A : Finset (ℕ × ℕ) := S.filter (fun ab => ab.1 ≤ u)
  set B : Finset (ℕ × ℕ) := S.filter (fun ab => ab.2 ≤ u)
  have hS_card : ∑ n ∈ Finset.Icc 1 N, σ 0 n = S.card := by
    have hfib : S.card = ∑ n ∈ Finset.Icc 1 N, (S.filter (fun ab => ab.1 * ab.2 = n)).card := by
      have hmaps : ∀ ab ∈ S, ab.1 * ab.2 ∈ Finset.Icc 1 N := fun ab hab => by
        obtain ⟨hP, hle⟩ := Finset.mem_filter.mp hab
        obtain ⟨ha, hb⟩ := Finset.mem_product.mp hP
        exact Finset.mem_Icc.mpr ⟨Nat.mul_pos (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hb).1, hle⟩
      rw [Finset.card_eq_sum_ones, ← Finset.sum_fiberwise_of_maps_to hmaps]
      exact Finset.sum_congr rfl fun _ _ => (Finset.card_eq_sum_ones _).symm
    rw [hfib]
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    rw [ArithmeticFunction.sigma_zero_apply]
    refine Finset.card_bij (fun d _ => (d, n / d)) ?_ ?_ ?_
    · intro d hd
      obtain ⟨hdn, _⟩ := Nat.mem_divisors.mp hd
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdn hn1
      have hdN : d ≤ N := (Nat.le_of_dvd hn1 hdn).trans hnN
      have hq1 : 1 ≤ n / d := Nat.div_pos (Nat.le_of_dvd hn1 hdn) hd1
      have hqN : n / d ≤ N := (Nat.div_le_self n d).trans hnN
      have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdn
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨hd1, hdN⟩, Finset.mem_Icc.mpr ⟨hq1, hqN⟩⟩, hmul.le.trans hnN⟩, hmul⟩
    · intro d₁ _ d₂ _ h; exact (Prod.mk.inj h).1
    · intro ab hab
      obtain ⟨habS, hmul⟩ := Finset.mem_filter.mp hab
      have ha1 : 1 ≤ ab.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp habS).1).1).1
      refine ⟨ab.1, Nat.mem_divisors.mpr ⟨⟨ab.2, hmul.symm⟩, by omega⟩,
        Prod.ext rfl (Nat.eq_div_of_mul_eq_right (by omega) hmul).symm⟩
  have hunion : A ∪ B = S := by
    ext ab
    simp only [A, B, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hab
      by_cases h1 : ab.1 ≤ u
      · exact Or.inl ⟨hab, h1⟩
      · right
        refine ⟨hab, ?_⟩
        by_contra h2
        have hle : ab.1 * ab.2 ≤ N := (Finset.mem_filter.mp hab).2
        have hgt : N < (u + 1) * (u + 1) := Nat.lt_succ_sqrt N
        nlinarith
  have hu_le_N : u ≤ N := Nat.sqrt_le_self N
  have hinter : A ∩ B = Finset.Icc 1 u ×ˢ Finset.Icc 1 u := by
    ext ab
    simp only [A, B, S, Finset.mem_inter, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨⟨⟨ha1, _⟩, ⟨hb1, _⟩⟩, _⟩, hau⟩, ⟨_, hbu⟩⟩
      exact ⟨⟨ha1, hau⟩, ⟨hb1, hbu⟩⟩
    · rintro ⟨⟨ha1, hau⟩, ⟨hb1, hbu⟩⟩
      have hmul : ab.1 * ab.2 ≤ N := (Nat.mul_le_mul hau hbu).trans (Nat.sqrt_le N)
      exact ⟨⟨⟨⟨⟨ha1, hau.trans hu_le_N⟩, ⟨hb1, hbu.trans hu_le_N⟩⟩, hmul⟩, hau⟩,
        ⟨⟨⟨⟨ha1, hau.trans hu_le_N⟩, ⟨hb1, hbu.trans hu_le_N⟩⟩, hmul⟩, hbu⟩⟩
  have hA_card : A.card = ∑ d ∈ Finset.Icc 1 u, N / d := by
    have hmaps : ∀ ab ∈ A, ab.1 ∈ Finset.Icc 1 u := fun ab hab => by
      obtain ⟨habS, hau⟩ := Finset.mem_filter.mp hab
      have ha1 := (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp habS).1).1).1
      exact Finset.mem_Icc.mpr ⟨ha1, hau⟩
    have hfib : A.card = ∑ d ∈ Finset.Icc 1 u, (A.filter (fun ab => ab.1 = d)).card := by
      rw [Finset.card_eq_sum_ones, ← Finset.sum_fiberwise_of_maps_to hmaps]
      exact Finset.sum_congr rfl fun _ _ => (Finset.card_eq_sum_ones _).symm
    rw [hfib]
    refine Finset.sum_congr rfl fun d hd => ?_
    obtain ⟨hd1, hdu⟩ := Finset.mem_Icc.mp hd
    have hbij : (A.filter (fun ab => ab.1 = d)).card = (Finset.Icc 1 (N / d)).card := by
      refine Finset.card_bij (fun ab _ => ab.2) ?_ ?_ ?_
      · intro ab hab
        obtain ⟨habA, had⟩ := Finset.mem_filter.mp hab
        obtain ⟨habS, _⟩ := Finset.mem_filter.mp habA
        obtain ⟨hP, hmul⟩ := Finset.mem_filter.mp habS
        have hb1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hP).2).1
        rw [had] at hmul
        exact Finset.mem_Icc.mpr ⟨hb1, (Nat.le_div_iff_mul_le hd1).mpr (by linarith)⟩
      · intro ab₁ h₁ ab₂ h₂ heq
        exact Prod.ext ((Finset.mem_filter.mp h₁).2.trans (Finset.mem_filter.mp h₂).2.symm) heq
      · intro k hk
        obtain ⟨hk1, hkd⟩ := Finset.mem_Icc.mp hk
        have hdk : d * k ≤ N := (Nat.mul_le_mul_left d hkd).trans (Nat.mul_div_le N d)
        have hkN : k ≤ N := hkd.trans (Nat.div_le_self N d)
        refine ⟨(d, k), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
            ⟨Finset.mem_Icc.mpr ⟨hd1, hdu.trans hu_le_N⟩, Finset.mem_Icc.mpr ⟨hk1, hkN⟩⟩, hdk⟩,
          hdu⟩, rfl⟩, rfl⟩
    rw [hbij, Nat.card_Icc, Nat.add_sub_cancel]
  have hB_card : B.card = A.card := by
    refine Finset.card_bij (fun ab _ => (ab.2, ab.1)) ?_ ?_ ?_
    · intro ab hab
      obtain ⟨habS, hbu⟩ := Finset.mem_filter.mp hab
      obtain ⟨hP, hmul⟩ := Finset.mem_filter.mp habS
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hP
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hb, ha⟩, by rw [mul_comm]; exact hmul⟩, hbu⟩
    · intro ab₁ _ ab₂ _ h
      exact Prod.ext (Prod.mk.inj h).2 (Prod.mk.inj h).1
    · intro ab hab
      obtain ⟨habS, hau⟩ := Finset.mem_filter.mp hab
      obtain ⟨hP, hmul⟩ := Finset.mem_filter.mp habS
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hP
      exact ⟨(ab.2, ab.1), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hb, ha⟩, by rw [mul_comm]; exact hmul⟩, hau⟩, rfl⟩
  have hAB := Finset.card_union_add_card_inter A B
  rw [hunion, hinter, Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel, ← sq,
    hA_card, hB_card, hA_card, ← two_mul, ← hS_card] at hAB
  exact hAB

/-- Harmonic number approximation via Mathlib's `eulerMascheroniSeq` and `eulerMascheroniSeq'`:
for every `u ≥ 1`, `0 ≤ ∑_{d=1}^u 1/d - (log u + γ) ≤ 1 / u`. -/
private theorem harmonic_sub_log_sub_gamma_bounds {u : ℕ} (hu : 1 ≤ u) :
    0 ≤ (∑ d ∈ Finset.Icc 1 u, (d : ℝ)⁻¹) - (Real.log (u : ℝ) + Real.eulerMascheroniConstant) ∧
    (∑ d ∈ Finset.Icc 1 u, (d : ℝ)⁻¹) - (Real.log (u : ℝ) + Real.eulerMascheroniConstant) ≤
      (u : ℝ)⁻¹ := by
  have hu0 : (0 : ℝ) < (u : ℝ) := Nat.cast_pos.mpr hu
  have hharm : (harmonic u : ℝ) = ∑ d ∈ Finset.Icc 1 u, (d : ℝ)⁻¹ := by
    clear hu hu0
    induction u with
    | zero => simp [harmonic_zero]
    | succ m ih =>
      have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [harmonic_succ, Rat.cast_add, ih, hIcc, Finset.sum_insert (by simp), add_comm]
      congr 1
      push_cast; rfl
  have hlo := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant u
  have hhi := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' u
  unfold Real.eulerMascheroniSeq at hlo
  unfold Real.eulerMascheroniSeq' at hhi
  rw [if_neg (by omega : u ≠ 0)] at hhi
  rw [hharm] at hlo hhi
  constructor
  · linarith
  · have hlog_diff : Real.log ((u : ℝ) + 1) - Real.log (u : ℝ) ≤ (u : ℝ)⁻¹ := by
      rw [← Real.log_div (by positivity) hu0.ne']
      calc Real.log (((u : ℝ) + 1) / (u : ℝ))
          ≤ ((u : ℝ) + 1) / (u : ℝ) - 1 :=
            Real.log_le_sub_one_of_pos (div_pos (by positivity) hu0)
        _ = (u : ℝ)⁻¹ := by field_simp [hu0.ne']; ring
    linarith

/-- **DIRICHLET'S DIVISOR-FUNCTION AVERAGE (`0` ASSUMPTIONS!)**:
`∃ C > 0, ∀ x ≥ 1, |∑_{n ≤ x} d(n) - x * (log x + 2 * γ - 1)| ≤ C * √x`. -/
theorem dirichlet_divisor_sum_asymp :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (σ 0 n : ℝ) -
          x * (Real.log x + 2 * Real.eulerMascheroniConstant - 1)| ≤
        C * Real.sqrt x := by
  refine ⟨15, by norm_num, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hsqx_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have h1_le_sqx : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx
  set N : ℕ := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  set u : ℕ := Nat.sqrt N
  have hu1 : 1 ≤ u := Nat.sqrt_pos.mpr hN1
  have hu_pos : (0 : ℝ) < (u : ℝ) := Nat.cast_pos.mpr hu1
  have hu_le_sqx : (u : ℝ) ≤ Real.sqrt x := by
    rw [Real.le_sqrt (Nat.cast_nonneg u) hx0.le, sq]
    exact (by exact_mod_cast Nat.sqrt_le N : (u : ℝ) * (u : ℝ) ≤ (N : ℝ)).trans (Nat.floor_le hx0.le)
  have hsqx_lt_u1 : Real.sqrt x < (u : ℝ) + 1 := by
    rw [Real.sqrt_lt' (by positivity)]
    have hNlt : N + 1 ≤ (u + 1) ^ 2 := by
      have := Nat.lt_succ_sqrt N; nlinarith
    have hxN : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
    have h1 : (N : ℝ) + 1 ≤ ((u : ℝ) + 1) ^ 2 := by exact_mod_cast hNlt
    linarith
  have hhalf_sqx_lt_u : Real.sqrt x / 2 < (u : ℝ) := by
    have hu1R : (1 : ℝ) ≤ (u : ℝ) := Nat.one_le_cast.mpr hu1
    linarith
  have hx_div_u : x / (u : ℝ) ≤ 2 * Real.sqrt x := by
    rw [div_le_iff₀ hu_pos]
    have hmul := mul_le_mul_of_nonneg_left hhalf_sqx_lt_u.le (by positivity : 0 ≤ 2 * Real.sqrt x)
    have hsq : 2 * Real.sqrt x * (Real.sqrt x / 2) = x := by
      rw [show 2 * Real.sqrt x * (Real.sqrt x / 2) = Real.sqrt x * Real.sqrt x by ring,
        Real.mul_self_sqrt hx0.le]
    linarith
  -- Cast the exact Dirichlet hyperbola identity to `ℝ`
  have hhyp : ∑ n ∈ Finset.Icc 1 N, (σ 0 n : ℝ) =
      2 * (∑ d ∈ Finset.Icc 1 u, ((N / d : ℕ) : ℝ)) - (u : ℝ) ^ 2 := by
    have hnat := dirichlet_hyperbola_identity N
    have hR : (∑ n ∈ Finset.Icc 1 N, (σ 0 n : ℝ)) + (u : ℝ) ^ 2 =
        2 * ∑ d ∈ Finset.Icc 1 u, ((N / d : ℕ) : ℝ) := by
      exact_mod_cast hnat
    linarith
  set H : ℝ := ∑ d ∈ Finset.Icc 1 u, (d : ℝ)⁻¹
  -- Error 1: `|2 * ∑ (N/d) - 2 * x * H| ≤ 4 * √x`
  have herr1 : |2 * (∑ d ∈ Finset.Icc 1 u, ((N / d : ℕ) : ℝ)) - 2 * x * H| ≤ 4 * Real.sqrt x := by
    have hrew : 2 * x * H - 2 * (∑ d ∈ Finset.Icc 1 u, ((N / d : ℕ) : ℝ)) =
        2 * ∑ d ∈ Finset.Icc 1 u, (x / (d : ℝ) - ((N / d : ℕ) : ℝ)) := by
      dsimp only [H]
      rw [mul_assoc, Finset.mul_sum, ← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
    rw [abs_sub_comm, hrew, abs_of_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun d hd =>
      (floor_div_approx hx (Finset.mem_Icc.mp hd).1).1))]
    calc 2 * ∑ d ∈ Finset.Icc 1 u, (x / (d : ℝ) - ((N / d : ℕ) : ℝ))
        ≤ 2 * ∑ _d ∈ Finset.Icc 1 u, (2 : ℝ) := by
          gcongr with d hd
          exact (floor_div_approx hx (Finset.mem_Icc.mp hd).1).2
      _ = 4 * (u : ℝ) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
      _ ≤ 4 * Real.sqrt x := by gcongr
  -- Error 2: `|2 * x * H - 2 * x * (log u + γ)| ≤ 4 * √x`
  have herr2 : |2 * x * H - 2 * x * (Real.log (u : ℝ) + Real.eulerMascheroniConstant)| ≤
      4 * Real.sqrt x := by
    have hhb := harmonic_sub_log_sub_gamma_bounds hu1
    have hrew : 2 * x * H - 2 * x * (Real.log (u : ℝ) + Real.eulerMascheroniConstant) =
        2 * x * (H - (Real.log (u : ℝ) + Real.eulerMascheroniConstant)) := by ring
    rw [hrew, abs_of_nonneg (mul_nonneg (by positivity) hhb.1)]
    calc 2 * x * (H - (Real.log (u : ℝ) + Real.eulerMascheroniConstant))
        ≤ 2 * x * (u : ℝ)⁻¹ := mul_le_mul_of_nonneg_left hhb.2 (by positivity)
      _ = 2 * (x / (u : ℝ)) := by rw [div_eq_mul_inv]; ring
      _ ≤ 2 * (2 * Real.sqrt x) := by gcongr
      _ = 4 * Real.sqrt x := by ring
  -- Error 3: `|2 * x * log u - x * log x| ≤ 4 * √x`
  have herr3 : |2 * x * Real.log (u : ℝ) - x * Real.log x| ≤ 4 * Real.sqrt x := by
    have hlog_eq : Real.log x = 2 * Real.log (Real.sqrt x) := by
      rw [Real.log_sqrt hx0.le]; ring
    have hlog_diff_nn : 0 ≤ Real.log (Real.sqrt x) - Real.log (u : ℝ) :=
      sub_nonneg.mpr (Real.log_le_log hu_pos hu_le_sqx)
    have hlog_diff_le : Real.log (Real.sqrt x) - Real.log (u : ℝ) ≤ (u : ℝ)⁻¹ := by
      rw [← Real.log_div hsqx_pos.ne' hu_pos.ne']
      calc Real.log (Real.sqrt x / (u : ℝ))
          ≤ Real.sqrt x / (u : ℝ) - 1 := Real.log_le_sub_one_of_pos (div_pos hsqx_pos hu_pos)
        _ = (Real.sqrt x - (u : ℝ)) / (u : ℝ) := by field_simp [hu_pos.ne']
        _ ≤ 1 / (u : ℝ) := div_le_div_of_nonneg_right (by linarith) hu_pos.le
        _ = (u : ℝ)⁻¹ := one_div _
    have hrew : x * Real.log x - 2 * x * Real.log (u : ℝ) =
        2 * x * (Real.log (Real.sqrt x) - Real.log (u : ℝ)) := by rw [hlog_eq]; ring
    rw [abs_sub_comm, hrew, abs_of_nonneg (mul_nonneg (by positivity) hlog_diff_nn)]
    calc 2 * x * (Real.log (Real.sqrt x) - Real.log (u : ℝ))
        ≤ 2 * x * (u : ℝ)⁻¹ := mul_le_mul_of_nonneg_left hlog_diff_le (by positivity)
      _ = 2 * (x / (u : ℝ)) := by rw [div_eq_mul_inv]; ring
      _ ≤ 2 * (2 * Real.sqrt x) := by gcongr
      _ = 4 * Real.sqrt x := by ring
  -- Error 4: `|x - u²| ≤ 3 * √x`
  have herr4 : |x - (u : ℝ) ^ 2| ≤ 3 * Real.sqrt x := by
    have hu2_le : (u : ℝ) ^ 2 ≤ x := by
      rw [sq]
      exact (by exact_mod_cast Nat.sqrt_le N : (u : ℝ) * (u : ℝ) ≤ (N : ℝ)).trans (Nat.floor_le hx0.le)
    have hx_lt_u1sq : x < ((u : ℝ) + 1) ^ 2 := by
      have h1 : (Real.sqrt x) ^ 2 < ((u : ℝ) + 1) ^ 2 :=
        pow_lt_pow_left₀ hsqx_lt_u1 hsqx_pos.le (by norm_num)
      rwa [Real.sq_sqrt hx0.le] at h1
    rw [abs_of_nonneg (by linarith)]
    nlinarith
  -- Combine all four errors!
  have htotal : ∑ n ∈ Finset.Icc 1 N, (σ 0 n : ℝ) -
      x * (Real.log x + 2 * Real.eulerMascheroniConstant - 1) =
      (2 * (∑ d ∈ Finset.Icc 1 u, ((N / d : ℕ) : ℝ)) - 2 * x * H) +
      (2 * x * H - 2 * x * (Real.log (u : ℝ) + Real.eulerMascheroniConstant)) +
      (2 * x * Real.log (u : ℝ) - x * Real.log x) +
      (x - (u : ℝ) ^ 2) := by
    rw [hhyp]; ring
  rw [htotal]
  have h1 := abs_add_le
    ((2 * (∑ d ∈ Finset.Icc 1 u, ((N / d : ℕ) : ℝ)) - 2 * x * H) +
      (2 * x * H - 2 * x * (Real.log (u : ℝ) + Real.eulerMascheroniConstant)) +
      (2 * x * Real.log (u : ℝ) - x * Real.log x))
    (x - (u : ℝ) ^ 2)
  have h2 := abs_add_le
    ((2 * (∑ d ∈ Finset.Icc 1 u, ((N / d : ℕ) : ℝ)) - 2 * x * H) +
      (2 * x * H - 2 * x * (Real.log (u : ℝ) + Real.eulerMascheroniConstant)))
    (2 * x * Real.log (u : ℝ) - x * Real.log x)
  have h3 := abs_add_le
    (2 * (∑ d ∈ Finset.Icc 1 u, ((N / d : ℕ) : ℝ)) - 2 * x * H)
    (2 * x * H - 2 * x * (Real.log (u : ℝ) + Real.eulerMascheroniConstant))
  linarith

end RHDirect.Stage8BrunTuran

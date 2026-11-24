import RHDirect.VinogradovMinorArc
import RHDirect.Stage10SiegelWalfiszFull
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Vinogradov — Input (a), Milestone 1: single-arc approximation via θ-Abel summation

Major-arc parameters are LOCKED here to avoid statement drift:
- cutoff `Q = (log N)^B` with `B > 0` a free parameter (Input (b) chooses `A`, then `B`);
- arc width `Q / N`;
- the exponential sum `S` is the **θ-type** prime sum `∑_{p≤N} log p · e(pα)` (NOT Λ/ψ),
  matching `Stage10SiegelWalfiszFull.siegel_walfisz_theta` (uniform `q ≤ (log x)^A`, coprime `a`,
  error `C·x·exp(−c√log x)`).

Milestone 1 target (single arc): for `(a,q)=1`, `q ≤ Q`, `|β| ≤ Q/N`,
`S(a/q + β) = (μ(q)/φ(q)) · v(β) + error`, where `v(β) = ∑_{m≤N} e(mβ)`.
This file lands the reusable discrete Abel-summation identity first (checkpoint 1.0).
No `sorry`, no custom axioms.
-/

open Real Complex Finset MeasureTheory intervalIntegral

namespace RHDirect.Vinogradov

noncomputable section

/-- The singular-integral kernel `v_N(β) = ∑_{m≤N} e(mβ)` (full integer sum). -/
def v (N : ℕ) (β : ℝ) : ℂ :=
  ∑ m ∈ Finset.range (N + 1), e ((m : ℝ) * β)

@[simp] theorem v_zero (β : ℝ) : v 0 β = 1 := by simp [v, e]

/-- Discrete Abel summation (summation by parts): with `A_n = ∑_{k≤n} a_k`,
`∑_{n≤N} a_n f_n = A_N f_N − ∑_{n<N} A_n (f_{n+1} − f_n)`. -/
theorem abel_summation_fin (a : ℕ → ℝ) (f : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (a n : ℂ) * f n =
      (∑ k ∈ Finset.range (N + 1), a k : ℂ) * f N -
        ∑ n ∈ Finset.range N,
          (∑ k ∈ Finset.range (n + 1), a k : ℂ) * (f (n + 1) - f n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h1 : ∑ n ∈ Finset.range (N + 1 + 1), (a n : ℂ) * f n =
        ∑ n ∈ Finset.range (N + 1), (a n : ℂ) * f n + (a (N + 1) : ℂ) * f (N + 1) := by
      rw [Finset.sum_range_succ]
    rw [h1, ih]
    have h2 : ∑ n ∈ Finset.range (N + 1),
        (∑ k ∈ Finset.range (n + 1), a k : ℂ) * (f (n + 1) - f n) =
        ∑ n ∈ Finset.range N,
          (∑ k ∈ Finset.range (n + 1), a k : ℂ) * (f (n + 1) - f n) +
        (∑ k ∈ Finset.range (N + 1), a k : ℂ) * (f (N + 1) - f N) := by
      rw [Finset.sum_range_succ]
    rw [h2]
    have h3 : (∑ k ∈ Finset.range (N + 1 + 1), a k : ℂ) =
        (∑ k ∈ Finset.range (N + 1), a k : ℂ) + a (N + 1) := by
      rw [Finset.sum_range_succ]
    rw [h3]
    ring

/-- The θ-weighted prime sum in residue class `r mod q`, twisted by `e(nβ)`. -/
def thetaAP_twist (q r N : ℕ) (β : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1),
    (↑(if n.Prime ∧ n ≡ r [MOD q] then Real.log (n : ℝ) else 0) : ℂ) * e ((n : ℝ) * β)

/-- Partial sums of the residue-class log-weight are exactly `chebyshevThetaAP`. -/
theorem thetaAP_partial (q r n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (↑(if k.Prime ∧ k ≡ r [MOD q] then Real.log (k : ℝ) else 0) : ℂ)) =
      (Stage2DirichletAP.chebyshevThetaAP q r n : ℂ) := by
  norm_cast
  simp only [Stage2DirichletAP.chebyshevThetaAP, Nat.floor_natCast]

/-- Checkpoint 1.1: Abel-summation form of the twisted residue-class prime sum. -/
theorem thetaAP_twist_abel (q r N : ℕ) (β : ℝ) :
    thetaAP_twist q r N β =
      (Stage2DirichletAP.chebyshevThetaAP q r N : ℂ) * e ((N : ℝ) * β) -
        ∑ n ∈ Finset.range N, (Stage2DirichletAP.chebyshevThetaAP q r n : ℂ) *
          (e (((n + 1) : ℝ) * β) - e ((n : ℝ) * β)) := by
  have h := abel_summation_fin
    (fun n => if n.Prime ∧ n ≡ r [MOD q] then Real.log (n : ℝ) else 0)
    (fun n => e ((n : ℝ) * β)) N
  simp only [thetaAP_twist]
  convert h using 1
  simp [thetaAP_partial]

@[simp] theorem e_natCast (n : ℕ) : e (n : ℝ) = 1 := by
  simpa using e_intCast (n : ℤ)

/-- `e(p·a/q)` depends only on `p mod q`. -/
theorem e_mul_div_mod (p a q : ℕ) (hq : q ≠ 0) :
    e (((p : ℝ) * a) / q) = e ((((p % q : ℕ) : ℝ) * a) / q) := by
  have hnat : (p : ℝ) = (p % q : ℕ) + (q : ℝ) * (p / q : ℕ) := by
    norm_cast
    linarith [Nat.mod_add_div p q]
  have hdiv : (p : ℝ) * a / q = ((p % q : ℕ) : ℝ) * a / q + (((p / q) * a : ℕ) : ℝ) := by
    rw [hnat]
    field_simp [hq]
    push_cast
    ring
  rw [hdiv, e_add, e_natCast, mul_one]

/-- The residue-class fiber of the twisted sum equals `thetaAP_twist`. -/
theorem thetaAP_twist_fiber (q r N : ℕ) (β : ℝ) (hr : r < q) :
    thetaAP_twist q r N β =
      ∑ p ∈ ((Finset.range (N + 1)).filter Nat.Prime).filter (fun p => p % q = r),
        (Real.log (p : ℝ) : ℂ) * e ((p : ℝ) * β) := by
  have hmod : ∀ n, (n ≡ r [MOD q]) ↔ n % q = r := by
    intro n
    change n % q = r % q ↔ n % q = r
    rw [Nat.mod_eq_of_lt hr]
  calc thetaAP_twist q r N β
      = ∑ n ∈ Finset.range (N + 1),
          ite (n.Prime ∧ n % q = r) ((Real.log (n : ℝ) : ℂ) * e ((n : ℝ) * β)) 0 := by
        apply Finset.sum_congr rfl; intro n _
        by_cases hP : n.Prime ∧ n % q = r <;> simp [hP, hmod n]
    _ = ∑ n ∈ (Finset.range (N + 1)).filter (fun n => n.Prime ∧ n % q = r),
          (Real.log (n : ℝ) : ℂ) * e ((n : ℝ) * β) := by
        rw [Finset.sum_filter]
    _ = ∑ p ∈ ((Finset.range (N + 1)).filter Nat.Prime).filter (fun p => p % q = r),
          (Real.log (p : ℝ) : ℂ) * e ((p : ℝ) * β) := by
        congr 1
        ext n
        simp [Finset.mem_filter]
        tauto

/-- Milestone 1.2 (structure): residue-class decomposition of the major-arc sum.
`S(a/q+β) = ∑_{r<q} e(r·a/q) · thetaAP_twist q r N β`. -/
theorem S_major_arc_decomp (N a q : ℕ) (β : ℝ) (hq : q ≠ 0) :
    S N (((a : ℝ) / q) + β) =
      ∑ r ∈ Finset.range q, e ((((r : ℕ) : ℝ) * a) / q) * thetaAP_twist q r N β := by
  simp only [S]
  have he : ∀ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
      (Real.log (p : ℝ) : ℂ) * e ((p : ℝ) * (((a : ℝ) / q) + β)) =
        e ((((p % q : ℕ) : ℝ) * a) / q) * ((Real.log (p : ℝ) : ℂ) * e ((p : ℝ) * β)) := by
    intro p _
    rw [mul_add, e_add]
    have hcast : e ((p : ℝ) * ((a : ℝ) / q)) = e (((p : ℝ) * a) / q) := by
      congr 1
      ring
    rw [hcast, e_mul_div_mod p a q hq]
    ring
  rw [Finset.sum_congr rfl (fun p hp => he p hp)]
  have hmap : ∀ p ∈ (Finset.range (N + 1)).filter Nat.Prime, p % q ∈ Finset.range q := by
    intro p _
    exact Finset.mem_range.mpr (Nat.mod_lt p (Nat.pos_of_ne_zero hq))
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p => p % q) hmap]
  apply Finset.sum_congr rfl; intro r hr
  have hrq : r < q := Finset.mem_range.mp hr
  calc ∑ p ∈ ((Finset.range (N + 1)).filter Nat.Prime).filter (fun p => p % q = r),
        e ((((p % q : ℕ) : ℝ) * a) / q) * ((Real.log (p : ℝ) : ℂ) * e ((p : ℝ) * β))
      = ∑ p ∈ ((Finset.range (N + 1)).filter Nat.Prime).filter (fun p => p % q = r),
          e ((((r : ℕ) : ℝ) * a) / q) * ((Real.log (p : ℝ) : ℂ) * e ((p : ℝ) * β)) := by
        apply Finset.sum_congr rfl; intro p hp
        have hpr : p % q = r := (Finset.mem_filter.mp hp).2
        rw [hpr]
    _ = e ((((r : ℕ) : ℝ) * a) / q) *
        ∑ p ∈ ((Finset.range (N + 1)).filter Nat.Prime).filter (fun p => p % q = r),
          (Real.log (p : ℝ) : ℂ) * e ((p : ℝ) * β) := by
        rw [← Finset.mul_sum]
    _ = e ((((r : ℕ) : ℝ) * a) / q) * thetaAP_twist q r N β := by
        congr 1
        exact (thetaAP_twist_fiber q r N β hrq).symm

/-- Roots-of-unity sum: `∑_{t<m} e(t/m) = ite(m=1)`. -/
theorem sum_e_div (m : ℕ) :
    ∑ t ∈ Finset.range m, e (((t : ℝ) / m)) = if m = 1 then 1 else 0 := by
  by_cases hm : m = 0
  · simp [hm]
  · by_cases hm1 : m = 1
    · simp [hm1]
    · have hm2 : 1 < m := by omega
      simp only [hm1, ite_false]
      have he : ∀ t ∈ Finset.range m, e ((t : ℝ) / m) = e ((1 : ℝ) / m) ^ t := by
        intro t _
        have harg : ((t : ℝ) / m) = ((1 : ℝ) / m) * t := by
          field_simp [hm]
        rw [harg, mul_comm, e_natCast_mul]
      rw [Finset.sum_congr rfl (fun t ht => he t ht)]
      have hgeom := geom_sum_mul (e ((1 : ℝ) / m)) m
      have hpow : e ((1 : ℝ) / m) ^ m = 1 := by
        rw [← e_natCast_mul, mul_comm]
        have harg : ((1 : ℝ) / m) * m = 1 := by field_simp [hm]
        rw [harg]
        simp [e]
      have hne : e ((1 : ℝ) / m) - 1 ≠ 0 := by
        intro h
        have he1 : e ((1 : ℝ) / m) = 1 := by linear_combination h
        rw [e_eq_one_iff] at he1
        obtain ⟨k, hk⟩ := he1
        have h1 : (0 : ℝ) < (1 : ℝ) / m := by positivity
        have h2 : (1 : ℝ) / m < 1 :=
          (div_lt_one (by positivity)).mpr (by exact_mod_cast hm2)
        rw [hk] at h1 h2
        norm_cast at h1 h2
        omega
      rw [hpow, sub_self] at hgeom
      exact mul_eq_zero.mp hgeom |>.resolve_right hne

/-- Convert an antidiagonal sum to a divisors sum: `∑_{x·y=n} f x y = ∑_{d|n} f d (n/d)`. -/
theorem sum_divisorsAntidiagonal_eq_sum_divisors' {n : ℕ} (hn : n ≠ 0) (f : ℕ → ℕ → ℤ) :
    ∑ x ∈ n.divisorsAntidiagonal, f x.1 x.2 = ∑ d ∈ n.divisors, f d (n / d) := by
  apply Finset.sum_bij (fun (x : ℕ × ℕ) _ => x.1)
  · intro x hx
    have hprod : x.1 * x.2 = n := (Nat.mem_divisorsAntidiagonal.mp hx).1
    rw [Nat.mem_divisors]
    exact ⟨⟨x.2, hprod.symm⟩, hn⟩
  · intro x hx y hy hxy
    have hx1 : x.1 ≠ 0 := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx
    have hy1 : y.1 ≠ 0 := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hy
    have hx2 : x.2 = n / x.1 := by
      apply Eq.symm
      apply Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero hx1)
      rw [mul_comm]
      exact (Nat.mem_divisorsAntidiagonal.mp hx).1.symm
    have hy2 : y.2 = n / y.1 := by
      apply Eq.symm
      apply Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero hy1)
      rw [mul_comm]
      exact (Nat.mem_divisorsAntidiagonal.mp hy).1.symm
    ext
    · exact hxy
    · rw [hx2, hy2, hxy]
  · intro d hd
    refine ⟨(d, n / d), ?_, rfl⟩
    rw [Nat.mem_divisorsAntidiagonal]
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
    exact ⟨Nat.mul_div_cancel' hdvd, hn⟩
  · intro x hx
    have hx1 : x.1 ≠ 0 := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx
    have hx2 : x.2 = n / x.1 := by
      apply Eq.symm
      apply Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero hx1)
      rw [mul_comm]
      exact (Nat.mem_divisorsAntidiagonal.mp hx).1.symm
    rw [hx2]

/-- Möbius divisor-sum indicator: `∑_{d|n} μ(d) = ite(n=1)` for `n ≠ 0`. -/
theorem sum_moebius_divisors_eq_ite {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℤ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at h
  have hconv := sum_divisorsAntidiagonal_eq_sum_divisors' hn
    (fun a b => (ArithmeticFunction.moebius a : ℤ) * (ArithmeticFunction.zeta b : ℤ))
  have h2 : ∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius d : ℤ) * (ArithmeticFunction.zeta (n / d) : ℤ) =
      if n = 1 then 1 else 0 :=
    hconv.symm.trans h
  have hz : ∀ d ∈ n.divisors, (ArithmeticFunction.zeta (n / d) : ℤ) = 1 := by
    intro d hd
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hnpos
    have hne : n / d ≠ 0 := by
      have := Nat.div_pos (Nat.le_of_dvd hnpos hdvd) hdpos
      omega
    rw [ArithmeticFunction.zeta_apply_ne hne]
    simp
  have hsum : ∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius d : ℤ) * (ArithmeticFunction.zeta (n / d) : ℤ) =
      ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℤ) := by
    apply Finset.sum_congr rfl; intro d hd
    rw [hz d hd, mul_one]
  rw [hsum] at h2
  exact h2

/-- Multiplication by a coprime residue permutes the roots-of-unity sum:
`∑_{s<m} e(s·a/m) = ∑_{t<m} e(t/m)` when `(a,m)=1`. -/
theorem sum_e_mul_perm (a m : ℕ) (hm : m ≠ 0) (ha : Nat.Coprime a m) :
    ∑ s ∈ Finset.range m, e (((s : ℝ) * a) / m) = ∑ t ∈ Finset.range m, e ((t : ℝ) / m) := by
  classical
  by_cases hm1 : m = 1
  · simp [hm1]
  · haveI : NeZero m := ⟨hm⟩
    let u : (ZMod m)ˣ := ZMod.unitOfCoprime a ha
    have hu : (u : ZMod m) = a := ZMod.coe_unitOfCoprime a ha
    apply Finset.sum_bij (fun (s : ℕ) _ => ZMod.val ((s * a : ℕ) : ZMod m))
    · intro s hs
      exact Finset.mem_range.mpr (ZMod.val_lt _)
    · intro s hs t ht hst
      have hs' : s < m := Finset.mem_range.mp hs
      have ht' : t < m := Finset.mem_range.mp ht
      have hz : ((s * a : ℕ) : ZMod m) = ((t * a : ℕ) : ZMod m) := ZMod.val_injective (n := m) hst
      have hz' : (s : ZMod m) = (t : ZMod m) := by
        have := congrArg (· * (u.inv : ZMod m)) hz
        have hau : (a : ZMod m) * (u.inv : ZMod m) = 1 := by
          rw [← hu]; exact Units.mul_inv u
        rw [Nat.cast_mul, Nat.cast_mul, mul_assoc, mul_assoc, hau, mul_one, mul_one] at this
        exact this
      have hmod : s ≡ t [MOD m] := (ZMod.natCast_eq_natCast_iff s t m).mp hz'
      exact hmod.eq_of_lt_of_lt hs' ht'
    · intro t ht
      refine ⟨ZMod.val ((t : ZMod m) * (u.inv : ZMod m)),
        Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
      have hsa : ((ZMod.val ((t : ZMod m) * (u.inv : ZMod m)) * a : ℕ) : ZMod m) = (t : ZMod m) := by
        have hval : (ZMod.val ((t : ZMod m) * (u.inv : ZMod m)) : ZMod m) =
            (t : ZMod m) * (u.inv : ZMod m) := by simp
        calc ((ZMod.val ((t : ZMod m) * (u.inv : ZMod m)) * a : ℕ) : ZMod m)
            = ((t : ZMod m) * (u.inv : ZMod m)) * (a : ZMod m) := by rw [Nat.cast_mul, hval]
          _ = (t : ZMod m) * ((u.inv : ZMod m) * (a : ZMod m)) := by ring
          _ = (t : ZMod m) * 1 := by
              congr 1
              rw [← hu]
              exact Units.inv_mul u
          _ = (t : ZMod m) := by ring
      have h1 := congrArg ZMod.val hsa
      have h2 : ZMod.val (t : ZMod m) = t := by
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ht)]
      rw [h2] at h1
      exact h1
    · intro s hs
      have hval : ZMod.val ((s * a : ℕ) : ZMod m) = (s * a) % m := ZMod.val_natCast m (s * a)
      have harg : ((s : ℝ) * a) / m = (((s * a) % m : ℕ) : ℝ) / m + ((s * a) / m : ℕ) := by
        have := Nat.mod_add_div (s * a) m
        field_simp [hm]
        norm_cast at this ⊢
        linarith
      rw [harg, e_add, e_natCast, mul_one, ← hval]

/-- Coprime indicator as a Möbius divisor sum (complex-valued). -/
theorem coprime_indicator_moebius (r q : ℕ) (hq : q ≠ 0) :
    (if Nat.Coprime r q then (1 : ℂ) else 0) =
      ∑ d ∈ (Nat.gcd r q).divisors, (ArithmeticFunction.moebius d : ℂ) := by
  have hgcd : Nat.gcd r q ≠ 0 :=
    Nat.ne_of_gt (Nat.gcd_pos_of_pos_right r (Nat.pos_of_ne_zero hq))
  have hz := sum_moebius_divisors_eq_ite hgcd
  have hcast : (∑ d ∈ (Nat.gcd r q).divisors, (ArithmeticFunction.moebius d : ℂ)) =
      (if Nat.gcd r q = 1 then (1 : ℂ) else 0) := by
    have := congrArg (fun k : ℤ => (k : ℂ)) hz
    simpa using this
  rw [hcast]

/-- `divisors (gcd r q) = (divisors q).filter (· ∣ r)`. -/
theorem divisors_gcd_eq_filter (r q : ℕ) (hq : q ≠ 0) :
    (Nat.gcd r q).divisors = q.divisors.filter (fun d => d ∣ r) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter]
  constructor
  · intro h
    have hdvd : d ∣ Nat.gcd r q := h.1
    have hdq : d ∣ q := Nat.dvd_trans hdvd (Nat.gcd_dvd_right r q)
    have hdr : d ∣ r := Nat.dvd_trans hdvd (Nat.gcd_dvd_left r q)
    exact ⟨⟨hdq, hq⟩, hdr⟩
  · intro h
    have hdq : d ∣ q := h.1.1
    have hdr : d ∣ r := h.2
    have hdvd : d ∣ Nat.gcd r q := Nat.dvd_gcd hdr hdq
    have hg0 : Nat.gcd r q ≠ 0 :=
      Nat.ne_of_gt (Nat.gcd_pos_of_pos_right r (Nat.pos_of_ne_zero hq))
    exact ⟨hdvd, hg0⟩

/-- Reindex a sum over multiples of `d` below `q` by `r = d·s`. -/
theorem sum_filter_dvd_reindex (q d : ℕ) (hdvd : d ∣ q) (hdpos : 0 < d) (f : ℕ → ℂ) :
    ∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), f r =
      ∑ s ∈ Finset.range (q / d), f (d * s) := by
  apply Finset.sum_bij (fun r _ => r / d)
  · intro r hr
    have hdr : d ∣ r := (Finset.mem_filter.mp hr).2
    have hrq : r < q := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    exact Finset.mem_range.mpr (by
      rw [Nat.div_lt_iff_lt_mul hdpos, Nat.mul_comm, Nat.mul_div_cancel' hdvd]
      exact hrq)
  · intro r1 hr1 r2 hr2 h
    have h1 : d ∣ r1 := (Finset.mem_filter.mp hr1).2
    have h2 : d ∣ r2 := (Finset.mem_filter.mp hr2).2
    have hr1 : r1 = d * (r1 / d) := (Nat.mul_div_cancel' h1).symm
    have hr2 : r2 = d * (r2 / d) := (Nat.mul_div_cancel' h2).symm
    rw [hr1, hr2, h]
  · intro s hs
    refine ⟨d * s, ?_, Nat.mul_div_cancel_left s hdpos⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr ?_, dvd_mul_right d s⟩
    have hs' : s < q / d := Finset.mem_range.mp hs
    have : d * s < d * (q / d) := Nat.mul_lt_mul_of_pos_left hs' hdpos
    rwa [Nat.mul_div_cancel' hdvd] at this
  · intro r hr
    have hdr : d ∣ r := (Finset.mem_filter.mp hr).2
    rw [Nat.mul_div_cancel' hdr]

/-- Ramanujan identity: `c_q(a) = μ(q)` when `(a,q)=1`. -/
theorem ramanujanSum_eq_moebius_of_coprime (q a : ℕ) (hq : q ≠ 0) (ha : Nat.Coprime a q) :
    ramanujanSum q a = (ArithmeticFunction.moebius q : ℂ) := by
  simp only [ramanujanSum]
  have hexpand : ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
      e (((r : ℝ) * a) / q) =
      ∑ r ∈ Finset.range q, (∑ d ∈ (Nat.gcd r q).divisors,
        (ArithmeticFunction.moebius d : ℂ)) * e (((r : ℝ) * a) / q) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl; intro r hr
    have hite : ite (Nat.Coprime r q) (e (((r : ℝ) * a) / q)) 0 =
        ite (Nat.Coprime r q) (1 : ℂ) 0 * e (((r : ℝ) * a) / q) := by
      split_ifs <;> simp
    rw [hite, coprime_indicator_moebius r q hq]
  rw [hexpand]
  have hswap : ∑ r ∈ Finset.range q, (∑ d ∈ (Nat.gcd r q).divisors,
      (ArithmeticFunction.moebius d : ℂ)) * e (((r : ℝ) * a) / q) =
      ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) *
        ∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), e (((r : ℝ) * a) / q) := by
    have h1 : ∑ r ∈ Finset.range q, (∑ d ∈ (Nat.gcd r q).divisors,
        (ArithmeticFunction.moebius d : ℂ)) * e (((r : ℝ) * a) / q) =
        ∑ r ∈ Finset.range q, ∑ d ∈ q.divisors.filter (fun d => d ∣ r),
          (ArithmeticFunction.moebius d : ℂ) * e (((r : ℝ) * a) / q) := by
      apply Finset.sum_congr rfl; intro r hr
      rw [divisors_gcd_eq_filter r q hq, ← Finset.sum_mul]
    rw [h1]
    have h2 : ∑ r ∈ Finset.range q, ∑ d ∈ q.divisors.filter (fun d => d ∣ r),
        (ArithmeticFunction.moebius d : ℂ) * e (((r : ℝ) * a) / q) =
        ∑ r ∈ Finset.range q, ∑ d ∈ q.divisors,
          ite (d ∣ r) ((ArithmeticFunction.moebius d : ℂ) * e (((r : ℝ) * a) / q)) 0 := by
      apply Finset.sum_congr rfl; intro r hr
      rw [Finset.sum_filter]
    rw [h2, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro d hd
    rw [← Finset.sum_filter, Finset.mul_sum]
  rw [hswap]
  have hinner : ∀ d ∈ q.divisors,
      ∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), e (((r : ℝ) * a) / q) =
        if q / d = 1 then (1 : ℂ) else 0 := by
    intro d hd
    have hdvd : d ∣ q := (Nat.mem_divisors.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hq)
    have hqdnz : q / d ≠ 0 := by
      have : 0 < q / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hdvd) hdpos
      omega
    have hcop : Nat.Coprime a (q / d) :=
      ha.of_dvd_right (Nat.div_dvd_of_dvd hdvd)
    -- reindex r = d*s, then e(d*s*a/q) = e(s*a/(q/d))
    have hreindex : ∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), e (((r : ℝ) * a) / q) =
        ∑ s ∈ Finset.range (q / d), e (((s : ℝ) * a) / ((q / d : ℕ) : ℝ)) := by
      rw [sum_filter_dvd_reindex q d hdvd hdpos]
      apply Finset.sum_congr rfl; intro s hs
      have harg : (((d * s : ℕ) : ℝ) * a) / q = ((s : ℝ) * a) / ((q / d : ℕ) : ℝ) := by
        have hq : (q : ℝ) = (d : ℝ) * ((q / d : ℕ) : ℝ) := by
          rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
        rw [hq]
        field_simp [hdpos.ne', hqdnz]
        push_cast
        ring
      rw [harg]
    rw [hreindex]
    rw [sum_e_mul_perm a (q / d) hqdnz hcop, sum_e_div]
  have hrewrite : ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) *
      ∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), e (((r : ℝ) * a) / q) =
      ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) *
        (if q / d = 1 then (1 : ℂ) else 0) := by
    apply Finset.sum_congr rfl; intro d hd
    rw [hinner d hd]
  rw [hrewrite]
  -- ∑_{d|q} μ(d)·ite(q/d=1) = μ(q) (only d=q contributes)
  have hqdiv : ∀ d ∈ q.divisors, (q / d = 1 ↔ d = q) := by
    intro d hd
    have hdvd : d ∣ q := (Nat.mem_divisors.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hq)
    constructor
    · intro h
      have := (Nat.div_eq_iff_eq_mul_left hdpos hdvd).mp h
      linarith
    · intro h; rw [h]; exact Nat.div_self (Nat.pos_of_ne_zero hq)
  have hcollapse : ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) *
      (if q / d = 1 then (1 : ℂ) else 0) = (ArithmeticFunction.moebius q : ℂ) := by
    have : ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) *
        (if q / d = 1 then (1 : ℂ) else 0) =
        ∑ d ∈ q.divisors, ite (d = q) (ArithmeticFunction.moebius d : ℂ) 0 := by
      apply Finset.sum_congr rfl; intro d hd
      by_cases hdq : d = q
      · subst hdq
        simp [Nat.div_self (Nat.pos_of_ne_zero hq)]
      · have hqdivn : q / d ≠ 1 := by
          intro h; apply hdq; exact (hqdiv d hd).mp h
        simp [hdq, hqdivn]
    rw [this, Finset.sum_ite_eq']
    simp [Nat.mem_divisors_self q hq]
  exact hcollapse

/-- Telescoping: `∑_{n<N} (e((n+1)β) − e(nβ)) = e(Nβ) − 1`. -/
theorem sum_e_telescope (N : ℕ) (β : ℝ) :
    ∑ n ∈ Finset.range N, (e (((n + 1) : ℝ) * β) - e ((n : ℝ) * β)) =
      e ((N : ℝ) * β) - 1 := by
  induction N with
  | zero => simp [e]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have h : ((N + 1 : ℕ) : ℝ) * β = (N : ℝ) * β + β := by push_cast; ring
    rw [h]
    ring

/-- Abel main-term identity: `N·e(Nβ) − ∑_{n<N} n·(e((n+1)β)−e(nβ)) = v_N(β) − 1`. -/
theorem v_abel_main (N : ℕ) (β : ℝ) :
    (N : ℂ) * e ((N : ℝ) * β) -
      ∑ n ∈ Finset.range N, (n : ℂ) * (e (((n + 1) : ℝ) * β) - e ((n : ℝ) * β)) =
      v N β - 1 := by
  have hv : v N β = (N + 1 : ℂ) * e ((N : ℝ) * β) -
      ∑ n ∈ Finset.range N, ((n + 1) : ℂ) * (e (((n + 1) : ℝ) * β) - e ((n : ℝ) * β)) := by
    have := abel_summation_fin (fun _ => (1 : ℝ)) (fun n => e ((n : ℝ) * β)) N
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at this
    simpa [v] using this
  have hsplit : ∑ n ∈ Finset.range N, ((n + 1) : ℂ) *
      (e (((n + 1) : ℝ) * β) - e ((n : ℝ) * β)) =
      ∑ n ∈ Finset.range N, (n : ℂ) * (e (((n + 1) : ℝ) * β) - e ((n : ℝ) * β)) +
      ∑ n ∈ Finset.range N, (e (((n + 1) : ℝ) * β) - e ((n : ℝ) * β)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro n _
    ring
  rw [hv, hsplit, sum_e_telescope]
  ring

/-- SW substitution: `thetaAP_twist q r N β = v_N(β)/φ(q) + (SW error terms)`.
The error is `-1/φ(q) + E(N)·e(Nβ) − ∑_{n<N} E(n)·Δe` with `E(x) = θ(x;q,r) − x/φ(q)`. -/
theorem thetaAP_twist_sw_decomp (q r N : ℕ) (β : ℝ) (hq : q ≠ 0) :
    thetaAP_twist q r N β =
      v N β / (q.totient : ℂ) +
      (-(1 : ℂ) / (q.totient : ℂ) +
        ((Stage2DirichletAP.chebyshevThetaAP q r N : ℂ) - (N : ℂ) / (q.totient : ℂ)) *
          e ((N : ℝ) * β) -
        ∑ n ∈ Finset.range N,
          ((Stage2DirichletAP.chebyshevThetaAP q r n : ℂ) - (n : ℂ) / (q.totient : ℂ)) *
            (e (((n + 1) : ℝ) * β) - e ((n : ℝ) * β))) := by
  rw [thetaAP_twist_abel]
  have hN : (Stage2DirichletAP.chebyshevThetaAP q r N : ℂ) =
      (N : ℂ) / (q.totient : ℂ) +
      ((Stage2DirichletAP.chebyshevThetaAP q r N : ℂ) - (N : ℂ) / (q.totient : ℂ)) := by ring
  rw [hN]
  have hsum : ∑ n ∈ Finset.range N, (Stage2DirichletAP.chebyshevThetaAP q r n : ℂ) *
      (e (((n + 1) : ℝ) * β) - e ((n : ℝ) * β)) =
      ∑ n ∈ Finset.range N, ((n : ℂ) / (q.totient : ℂ)) *
        (e (((n + 1) : ℝ) * β) - e ((n : ℝ) * β)) +
      ∑ n ∈ Finset.range N,
        ((Stage2DirichletAP.chebyshevThetaAP q r n : ℂ) - (n : ℂ) / (q.totient : ℂ)) *
        (e (((n + 1) : ℝ) * β) - e ((n : ℝ) * β)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro n _
    ring
  rw [hsum]
  have hfactor : ∑ n ∈ Finset.range N, ((n : ℂ) / (q.totient : ℂ)) *
      (e (((n + 1) : ℝ) * β) - e ((n : ℝ) * β)) =
      (1 / (q.totient : ℂ)) * ∑ n ∈ Finset.range N, (n : ℂ) *
        (e (((n + 1) : ℝ) * β) - e ((n : ℝ) * β)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n _
    ring
  rw [hfactor]
  have hv := v_abel_main N β
  have hmain : (N : ℂ) / (q.totient : ℂ) * e ((N : ℝ) * β) -
      (1 / (q.totient : ℂ)) * ∑ n ∈ Finset.range N, (n : ℂ) *
        (e (((n + 1) : ℝ) * β) - e ((n : ℝ) * β)) =
      (v N β - 1) / (q.totient : ℂ) := by
    have : (N : ℂ) / (q.totient : ℂ) * e ((N : ℝ) * β) -
        (1 / (q.totient : ℂ)) * ∑ n ∈ Finset.range N, (n : ℂ) *
          (e (((n + 1) : ℝ) * β) - e ((n : ℝ) * β)) =
        (1 / (q.totient : ℂ)) * ((N : ℂ) * e ((N : ℝ) * β) -
          ∑ n ∈ Finset.range N, (n : ℂ) *
            (e (((n + 1) : ℝ) * β) - e ((n : ℝ) * β))) := by ring
    rw [this, hv]
    ring
  linear_combination hmain

/-- Single-arc decomposition: `S(a/q+β) = (c_q(a)/φ(q))·v_N(β) + (coprime SW error) + (non-coprime part)`. -/
theorem S_single_arc_decomp (N a q : ℕ) (β : ℝ) (hq : q ≠ 0) :
    S N (((a : ℝ) / q) + β) =
      (ramanujanSum q a / (q.totient : ℂ)) * v N β +
      (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
        e (((r : ℝ) * a) / q) *
        (-(1 : ℂ) / (q.totient : ℂ) +
          ((Stage2DirichletAP.chebyshevThetaAP q r N : ℂ) - (N : ℂ) / (q.totient : ℂ)) *
            e ((N : ℝ) * β) -
          ∑ n ∈ Finset.range N,
            ((Stage2DirichletAP.chebyshevThetaAP q r n : ℂ) - (n : ℂ) / (q.totient : ℂ)) *
              (e (((n + 1) : ℝ) * β) - e ((n : ℝ) * β)))) +
      ∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime r q),
        e (((r : ℝ) * a) / q) * thetaAP_twist q r N β := by
  rw [S_major_arc_decomp N a q β hq]
  -- partition residues into coprime / non-coprime
  have hpart : ∑ r ∈ Finset.range q, e (((r : ℝ) * a) / q) * thetaAP_twist q r N β =
      ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
        e (((r : ℝ) * a) / q) * thetaAP_twist q r N β +
      ∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime r q),
        e (((r : ℝ) * a) / q) * thetaAP_twist q r N β := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range q) (fun r => Nat.Coprime r q)]
  rw [hpart]
  -- substitute SW decomp on the coprime part
  have hcop : ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
      e (((r : ℝ) * a) / q) * thetaAP_twist q r N β =
      ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
        e (((r : ℝ) * a) / q) *
        (v N β / (q.totient : ℂ) +
          (-(1 : ℂ) / (q.totient : ℂ) +
            ((Stage2DirichletAP.chebyshevThetaAP q r N : ℂ) - (N : ℂ) / (q.totient : ℂ)) *
              e ((N : ℝ) * β) -
            ∑ n ∈ Finset.range N,
              ((Stage2DirichletAP.chebyshevThetaAP q r n : ℂ) - (n : ℂ) / (q.totient : ℂ)) *
                (e (((n + 1) : ℝ) * β) - e ((n : ℝ) * β)))) := by
    apply Finset.sum_congr rfl; intro r hr
    rw [thetaAP_twist_sw_decomp q r N β hq]
  rw [hcop]
  -- split v/φ term from the error, factor v/φ out
  have hsplit : ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
      e (((r : ℝ) * a) / q) *
      (v N β / (q.totient : ℂ) +
        (-(1 : ℂ) / (q.totient : ℂ) +
          ((Stage2DirichletAP.chebyshevThetaAP q r N : ℂ) - (N : ℂ) / (q.totient : ℂ)) *
            e ((N : ℝ) * β) -
          ∑ n ∈ Finset.range N,
            ((Stage2DirichletAP.chebyshevThetaAP q r n : ℂ) - (n : ℂ) / (q.totient : ℂ)) *
              (e (((n + 1) : ℝ) * β) - e ((n : ℝ) * β)))) =
      (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), e (((r : ℝ) * a) / q)) *
        (v N β / (q.totient : ℂ)) +
      ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
        e (((r : ℝ) * a) / q) *
        (-(1 : ℂ) / (q.totient : ℂ) +
          ((Stage2DirichletAP.chebyshevThetaAP q r N : ℂ) - (N : ℂ) / (q.totient : ℂ)) *
            e ((N : ℝ) * β) -
          ∑ n ∈ Finset.range N,
            ((Stage2DirichletAP.chebyshevThetaAP q r n : ℂ) - (n : ℂ) / (q.totient : ℂ)) *
              (e (((n + 1) : ℝ) * β) - e ((n : ℝ) * β))) := by
    simp only [mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [hsplit]
  -- the coprime exponential sum is the Ramanujan sum
  have hram : ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), e (((r : ℝ) * a) / q) =
      ramanujanSum q a := by
    simp only [ramanujanSum]
  rw [hram]
  ring

/-- Single-arc approximation (algebraic form): for `(a,q)=1`,
`S(a/q+β) = (μ(q)/φ(q))·v_N(β) + (coprime SW error) + (non-coprime part)`.
The error terms are explicit; bounding them by `O(N·e^{−c√log N})` uses `siegel_walfisz_theta`. -/
theorem S_single_arc_approx (N a q : ℕ) (β : ℝ) (hq : q ≠ 0) (ha : Nat.Coprime a q) :
    S N (((a : ℝ) / q) + β) =
      ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * v N β +
      (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
        e (((r : ℝ) * a) / q) *
        (-(1 : ℂ) / (q.totient : ℂ) +
          ((Stage2DirichletAP.chebyshevThetaAP q r N : ℂ) - (N : ℂ) / (q.totient : ℂ)) *
            e ((N : ℝ) * β) -
          ∑ n ∈ Finset.range N,
            ((Stage2DirichletAP.chebyshevThetaAP q r n : ℂ) - (n : ℂ) / (q.totient : ℂ)) *
              (e (((n + 1) : ℝ) * β) - e ((n : ℝ) * β)))) +
      ∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime r q),
        e (((r : ℝ) * a) / q) * thetaAP_twist q r N β := by
  rw [S_single_arc_decomp N a q β hq]
  rw [ramanujanSum_eq_moebius_of_coprime q a hq ha]

end

#print axioms RHDirect.Vinogradov.abel_summation_fin
#print axioms RHDirect.Vinogradov.thetaAP_twist_abel
#print axioms RHDirect.Vinogradov.S_major_arc_decomp
#print axioms RHDirect.Vinogradov.sum_e_div
#print axioms RHDirect.Vinogradov.sum_moebius_divisors_eq_ite
#print axioms RHDirect.Vinogradov.sum_e_mul_perm
#print axioms RHDirect.Vinogradov.coprime_indicator_moebius
#print axioms RHDirect.Vinogradov.divisors_gcd_eq_filter
#print axioms RHDirect.Vinogradov.sum_filter_dvd_reindex
#print axioms RHDirect.Vinogradov.ramanujanSum_eq_moebius_of_coprime
#print axioms RHDirect.Vinogradov.v_abel_main
#print axioms RHDirect.Vinogradov.thetaAP_twist_sw_decomp
#print axioms RHDirect.Vinogradov.S_single_arc_decomp
#print axioms RHDirect.Vinogradov.S_single_arc_approx

end RHDirect.Vinogradov

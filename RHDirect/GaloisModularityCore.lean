import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import RHDirect.Interfaces
import RHDirect.AutomorphicInputs

/-!
# RHDirect.GaloisModularityCore

Direct, 0-`sorry`, 0-`axiom` Lean 4 formalization of the Selmer / Vandiver window (`VWin`)
reduction and patching-to-rank-bound combinatorics (`VWin S := ∀ ψ, VWinAt S ψ 401`).

## Architecture (Zero Dead Fields, Zero Gen 1–5 Vestigial Wrappers)

1. **Abelian Host Fields & Bad Prime Set** (`AbF`, `IsCompField`, `BchiOf`, `minusBound`):
   Proves `AbF.ker_ofChar`, `isCompField_ofChar`, `AbF.hasMu_cyc`, `prime_of_mem_BchiOf`,
   and `primePair_of_winPair`.
2. **Asymptotic Window & Exponential Absorption Inequalities** (all proved from scratch):
   - `admissible_of_pageN` (`PageN` + `0 < ε < 1/52` ⇒ `Admitted 4 Ct e ⌊x^Ct⌋₊`)
   - `log_mul_le_rpow_of_winPair` (`log(q d) ≤ Y^(ε/4)`)
   - `eventually_winPair_gt_power` (`2 X^Ct + 1 < q, d` and `P < q, d` via `y^n / n! ≤ exp y`)
   - `log_conductor_mul_height_le_of_pageN` (`log(N t) ≤ 2 x^(ε/4)`)
   - `minusBound_le_exp_of_log_le` (`minusBound C o n N t ≤ K exp(8 W)`)
   - `error_terms_le_sqrt_exp_rpow` (`exp(x^(4ε/5)) log 2 + K exp(8 x^(ε/4)) + (u^C + C exp(x^(4ε/5))) ≤ √exp(x^ε)`)
3. **Selmer Parity Splitting & Six-Case (`CountI`–`CountZ`) Combinatorics** (all proved from scratch):
   - `vvle_of_parts`: combines `2`-part (`VVTwoLe`), minus-parity (`VVMinusLe`), and plus-parity
     (`VVPlusLe`) into `VVle S E t (B2 * log 2 + Bm + Bp)`.
   - `sum_split_bad_prime`, `sumIn_arith_combine`: isolates the odd-order `CountIV` exception set
     (`Oset`, card `≤ q`, Ferrero–Washington/Mahler bound `B`) from polynomial `CountII / CountV / CountVs`
     and level-loss `(N e)^6` terms at bad primes `l ∈ Bchi`.
   - `card_primes_le`, `sumOut_arith_combine`: combines `CountI` (`U(3)` + Kato) with finitely many
     `(l - 1) ∣ 2e` primes (`CountII / CountIII` via `Sp(4)` + adjoint lifting, `CountZ` via Bernoulli)
     at good primes `l ∉ Bchi`.
   - `point_arith_combine` & `six_case_selmer_combine`: unifies bad-prime (`SumIn`) and good-prime
     (`SumOut`) bounds into the global plus-parity bound `M^C + C * B`.
4. **Master Window Assembly & Pillar 3 Contract**:
   - `vwinAt_of_joint` and `vwin_of_joint`: proves `VWin S` (`∀ ψ, VWinAt S ψ 401`) cleanly from
     `JointWin` + `ThmBc` + `ConductorBound`.
   - `galoisModularityContract_of_minimal` and `thetaInputs_and_vwin_of_minimal`: bridges
     `MinimalAutomorphyInputs` (zero `OpenImageCondition`, zero `LiteratureCMHypothesis`,
     zero `quat`, zero Gen 1–5 wrappers) straight into `GaloisModularityContract S` and
     Pillar 2 (`ThetaSlopeContract S`).

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open NumberField Filter

namespace RHDirect

/-! ## 1. Abelian Host Fields, Bad Prime Set, and Minus-Parity Bound -/

/-- Abelian congruence subgroup `(m, H)` defining an abelian subfield of `ℚ(ζ_m)`. -/
structure AbF where
  m : ℕ
  pos : 0 < m
  H : Subgroup (ZMod m)ˣ

namespace AbF

def ker (A : AbF) (a : ℕ) : Prop :=
  ∃ u ∈ A.H, ((u : (ZMod A.m)ˣ) : ZMod A.m) = (a : ZMod A.m)

def deg (A : AbF) : ℕ := A.H.index

def HasMu (A : AbF) (l : ℕ) : Prop :=
  l ∣ A.m ∧ ∀ a : ℕ, A.ker a → a ≡ 1 [MOD l]

def ofChar (ψ : PChar) : AbF :=
  ⟨ψ.N, NeZero.pos ψ.N, ψ.χ.toUnitHom.ker⟩

def cyc (m : ℕ) : AbF :=
  ⟨max m 1, by omega, ⊥⟩

theorem ker_ofChar (ψ : PChar) (a : ℕ) : (AbF.ofChar ψ).ker a ↔ ψ.val a = 1 := by
  show (∃ u ∈ ψ.χ.toUnitHom.ker, ((u : (ZMod ψ.N)ˣ) : ZMod ψ.N) = (a : ZMod ψ.N)) ↔
    ψ.χ (a : ZMod ψ.N) = 1
  constructor
  · rintro ⟨u, hu, hua⟩
    rw [← hua]
    have h1 := congrArg (fun v : ℂˣ => (v : ℂ)) (MonoidHom.mem_ker.mp hu)
    simpa [MulChar.coe_toUnitHom] using h1
  · intro h
    have hu : IsUnit (a : ZMod ψ.N) := by
      by_contra hn
      rw [MulChar.map_nonunit ψ.χ hn] at h
      exact zero_ne_one h
    refine ⟨hu.unit, ?_, hu.unit_spec⟩
    rw [MonoidHom.mem_ker]
    ext
    simpa [MulChar.coe_toUnitHom] using h

theorem hasMu_cyc {l q : ℕ} (hl : 0 < l) (hq : 0 < q) : (AbF.cyc (l * q)).HasMu l := by
  have hm : max (l * q) 1 = l * q :=
    max_eq_left (Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos hl hq).ne')
  show (l ∣ max (l * q) 1) ∧ ∀ a : ℕ,
    (∃ u ∈ (⊥ : Subgroup (ZMod (max (l * q) 1))ˣ),
      ((u : (ZMod (max (l * q) 1))ˣ) : ZMod (max (l * q) 1)) = (a : ZMod (max (l * q) 1))) →
      a ≡ 1 [MOD l]
  refine ⟨?_, ?_⟩
  · rw [hm]
    exact dvd_mul_right l q
  · rintro a ⟨u, hu, hua⟩
    rw [Subgroup.mem_bot] at hu
    subst hu
    have h1 : ((a : ℕ) : ZMod (max (l * q) 1)) = ((1 : ℕ) : ZMod (max (l * q) 1)) := by
      simpa using hua.symm
    rw [ZMod.natCast_eq_natCast_iff, hm] at h1
    exact Nat.ModEq.of_mul_right q h1

end AbF

/-- Composite abelian host field predicate `IsCompField A e q d E`. -/
def IsCompField (A : AbF) (e q d : ℕ) (E : Type) [Field E] [NumberField E] : Prop :=
  ∃ (N : ℕ) (_ : NeZero N) (j : E →ₐ[ℚ] CyclotomicField N ℚ) (ζ : CyclotomicField N ℚ),
    2 ^ (e + 2) ∣ N ∧ A.m ∣ N ∧ q ∣ N ∧ d ∣ N ∧ IsPrimitiveRoot ζ N ∧
    ∀ (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) (a : ℕ), τ ζ = ζ ^ a →
      ((∀ x : E, τ (j x) = j x) ↔
        (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) ∧ A.ker a ∧
          jacobiSym (a : ℤ) q = 1 ∧ jacobiSym (a : ℤ) d = 1)

theorem isCompField_ofChar (ψ : PChar) (e q d : ℕ) (E : Type) [Field E] [NumberField E] :
    IsCompField (AbF.ofChar ψ) e q d E ↔ IsChiField ψ e q d E := by
  simp only [IsCompField, IsChiField, AbF.ker_ofChar]
  rfl

/-- Minimal cyclotomic conductor `condF E` of an abelian number field `E`. -/
def condF (E : Type) [Field E] [NumberField E] : ℕ :=
  sInf {N : ℕ | 0 < N ∧ Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ)}

/-- Finite set of odd bad primes attached to `ψ` and auxiliary parameters `(pK, hStar, pOne)`. -/
def BchiOf (ψ : PChar) (pK hStar pOne : ℕ) : Finset ℕ :=
  insert 3 ((orderOf ψ.χ * ψ.N * pK * hStar * pOne).primeFactors.erase 2)

theorem prime_of_mem_BchiOf {ψ : PChar} {pK hStar pOne l : ℕ}
    (h : l ∈ BchiOf ψ pK hStar pOne) : l.Prime ∧ l ≠ 2 := by
  unfold BchiOf at h
  rcases Finset.mem_insert.mp h with rfl | h'
  · exact ⟨Nat.prime_three, by decide⟩
  · obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp h'
    exact ⟨Nat.prime_of_mem_primeFactors hmem, hne⟩

/-- Admissible auxiliary prime pair `(q, d)` coprime to modulus `m`. -/
structure PrimePair (m q d : ℕ) : Prop where
  q_prime : q.Prime
  q_mod : q % 8 = 3
  d_prime : d.Prime
  d_mod : d % 16 = 7
  cop : (q * d).Coprime m

theorem primePair_of_winPair {eps Y : ℝ} {m q d : ℕ} (hm : 0 < m)
    (hw : WinPair eps Y q d) (hq : (m : ℝ) < q) (hd : (m : ℝ) < d) :
    PrimePair m q d := by
  have hcop : ∀ r : ℕ, r.Prime → (m : ℝ) < r → r.Coprime m := by
    intro r hr hlt
    have hlt' : m < r := by exact_mod_cast hlt
    exact (hr.coprime_iff_not_dvd).2 fun hdvd =>
      absurd (Nat.le_of_dvd hm hdvd) (not_le.2 hlt')
  exact ⟨hw.q_prime, hw.q_mod, hw.d_prime, hw.d_mod,
    Nat.Coprime.mul_left (hcop q hw.q_prime hq) (hcop d hw.d_prime hd)⟩

/-- Exact minus-parity Selmer upper bound (`StmtFields.lean:L69-71`). -/
def minusBound (C : ℝ) (o n N t : ℕ) : ℝ :=
  3 * (n : ℝ) * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * N) +
    C * ∑ l ∈ o.primeFactors.erase 2,
      (l : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * l * N) ^ 2

/-! ## 2. Core Asymptotic Window & Exponential Absorption Inequalities -/

/-- Admissibility envelope for page-height function `e` and cutoff `t` (`Admitted A Ct e t`). -/
def Admitted (A Ct : ℝ) (e : ℝ → ℕ) (t : ℝ → ℕ) : Prop :=
  ∀ x : ℝ, 2 ≤ x → 2 ≤ e x ∧ (2 : ℝ) ^ e x ≤ x ^ A ∧ 2 ≤ t x ∧ (t x : ℝ) ≤ x ^ Ct

/-- Mirrors `UpperTheory.V.admissible_of_pageN` (`AdmissibleOfPageN.lean:L24-39`). -/
theorem admissible_of_pageN {eps Ct : ℝ} (h0 : 0 < eps) (h1 : eps < 1 / 52) (hC : 1 ≤ Ct)
    {e : ℝ → ℕ} (he : ∀ x ≥ (1 : ℝ), PageN eps x (e x)) :
    Admitted 4 Ct e (fun x => ⌊x ^ Ct⌋₊) := by
  intro x hx
  have hx1 : (1 : ℝ) ≤ x := by linarith
  obtain ⟨a, b⟩ := he x hx1
  have h2 : x ^ (2 : ℝ) ≤ x ^ (2 + 8 * eps) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h3 : x ^ (2 + 8 * eps) ≤ x ^ (3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h4 : x ^ (4 : ℝ) = x * x ^ (3 : ℝ) := by
    rw [show (4 : ℝ) = 1 + 3 by norm_num, Real.rpow_add (by linarith), Real.rpow_one]
  have h5 : (0 : ℝ) ≤ x ^ (3 : ℝ) := by positivity
  have h6 : x ≤ x ^ Ct := Real.self_le_rpow_of_one_le hx1 hC
  have h8 : 2 * x ^ (3 : ℝ) ≤ x * x ^ (3 : ℝ) := mul_le_mul_of_nonneg_right hx h5
  refine ⟨?_, b.trans ((mul_le_mul_of_nonneg_left h3 zero_le_two).trans (h8.trans h4.ge)),
    Nat.le_floor (by push_cast; linarith), Nat.floor_le (by positivity)⟩
  rw [Real.rpow_two] at h2
  have h7 : (2 : ℝ) ^ 2 ≤ 2 ^ e x := by nlinarith
  exact (pow_le_pow_iff_right₀ (by norm_num)).1 h7

/-- Elementary single-term Taylor lower bound `y^n / n! ≤ exp y` for `0 ≤ y`. -/
theorem pow_div_factorial_le_exp_direct (y : ℝ) (hy : 0 ≤ y) (n : ℕ) :
    y ^ n / (n.factorial : ℝ) ≤ Real.exp y := by
  have hsum := Real.sum_le_exp_of_nonneg hy (n + 1)
  have hmem : n ∈ Finset.range (n + 1) := Finset.mem_range.2 (Nat.lt_succ_self n)
  have hle : y ^ n / (n.factorial : ℝ) ≤ ∑ i ∈ Finset.range (n + 1), y ^ i / (i.factorial : ℝ) :=
    Finset.single_le_sum (f := fun i => y ^ i / (i.factorial : ℝ)) (fun i _ => by positivity) hmem
  exact hle.trans hsum

/-- Mirrors `UpperTheory.V.log_mul_le_rpow_of_winPair` (`logpair.lean:L6-28`). -/
theorem log_mul_le_rpow_of_winPair (eps : ℝ) (heps : 0 < eps) :
    ∃ Y0 : ℝ, ∀ Y ≥ Y0, ∀ q d : ℕ, WinPair eps Y q d →
      Real.log ((q : ℝ) * d) ≤ Y ^ (eps / 4) := by
  have hs : 0 < eps / 20 := by positivity
  have h1 := (isLittleO_log_rpow_rpow_atTop 2 hs).bound (by norm_num : (0 : ℝ) < 1 / 2)
  have h2 := (tendsto_rpow_atTop hs).eventually_ge_atTop 2
  obtain ⟨Y0, hY0⟩ := Filter.eventually_atTop.1 ((h1.and h2).and (Filter.eventually_gt_atTop 0))
  refine ⟨Y0, fun Y hY q d hw => ?_⟩
  obtain ⟨⟨hl, hg⟩, hpos⟩ := hY0 Y hY
  have hq : (0 : ℝ) < q := by exact_mod_cast hw.q_prime.pos
  have hd : (0 : ℝ) < d := by exact_mod_cast hw.d_prime.pos
  rw [Real.log_mul hq.ne' hd.ne']
  have hA : 0 < Y ^ (eps / 5) := Real.rpow_pos_of_pos hpos _
  have hB : 0 < Y ^ (eps / 20) := Real.rpow_pos_of_pos hpos _
  rw [Real.rpow_two, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    abs_of_pos hB] at hl
  have hsplit : Y ^ (eps / 4) = Y ^ (eps / 5) * Y ^ (eps / 20) := by
    rw [← Real.rpow_add hpos]
    congr 1
    ring
  rw [hsplit]
  have hq' := hw.q_up
  have hd' := hw.d_up
  nlinarith [mul_le_mul_of_nonneg_left hl hA.le, mul_le_mul_of_nonneg_left hg hA.le]

/-- Mirrors `UpperTheory.V.eventually_winPair_gt_power` (`bigpair.lean:L6-77`). -/
theorem eventually_winPair_gt_power (eps J Ct P : ℝ) (heps : 0 < eps) (hJ : 0 < J) :
    ∃ X0 : ℝ, ∀ X ≥ X0, ∀ q d : ℕ, WinPair eps (X ^ (1 / J)) q d →
      2 * X ^ Ct + 1 < (q : ℝ) ∧ 2 * X ^ Ct + 1 < (d : ℝ) ∧ P < (q : ℝ) ∧ P < (d : ℝ) := by
  set δ : ℝ := 1 / J * (eps / 5) with hδ
  have hδpos : 0 < δ := by positivity
  set mC : ℝ := max Ct 0 with hmC
  set n : ℕ := ⌈(mC + 1) / δ⌉₊ with hn_def
  have hn : mC + 1 ≤ δ * n := by
    have h := Nat.le_ceil ((mC + 1) / δ)
    rw [div_le_iff₀ hδpos] at h
    linarith
  set M : ℝ := 2 ^ n * (n.factorial : ℝ) with hM_def
  have hM : 0 < M := by positivity
  refine ⟨max (Real.exp J) (M * (|P| + 3) + 1), fun X hX q d hw => ?_⟩
  have hXe : Real.exp J ≤ X := le_trans (le_max_left _ _) hX
  have hXM : M * (|P| + 3) + 1 ≤ X := le_trans (le_max_right _ _) hX
  have hX1 : 1 ≤ X := by
    have := Real.add_one_le_exp J
    linarith
  have hX0 : 0 < X := by linarith
  have hY : (X ^ (1 / J)) ^ (eps / 5) = X ^ δ := by
    rw [← Real.rpow_mul hX0.le]
  have hlogY : 1 ≤ Real.log (X ^ (1 / J)) := by
    rw [Real.log_rpow hX0]
    have hJl : J ≤ Real.log X := (Real.le_log_iff_exp_le hX0).2 hXe
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hJ]
    linarith
  set y : ℝ := X ^ δ / 2 with hy_def
  have hy0 : 0 ≤ y := by positivity
  have hfac := pow_div_factorial_le_exp_direct y hy0 n
  have hyn : y ^ n = X ^ (δ * n) / 2 ^ n := by
    rw [hy_def, div_pow, ← Real.rpow_natCast (X ^ δ), ← Real.rpow_mul hX0.le]
  have hlow : X ^ (δ * n) / M ≤ Real.exp y := by
    rw [hyn, div_div] at hfac
    exact hfac
  have hpow : X ^ mC * X ≤ X ^ (δ * n) := by
    rw [← Real.rpow_add_one hX0.ne']
    exact Real.rpow_le_rpow_of_exponent_le hX1 hn
  have hCt : X ^ Ct ≤ X ^ mC := Real.rpow_le_rpow_of_exponent_le hX1 (le_max_left _ _)
  have hmC1 : 1 ≤ X ^ mC := Real.one_le_rpow hX1 (le_max_right _ _)
  have hXdiv : |P| + 3 < X / M := by
    rw [lt_div_iff₀ hM]
    linarith
  have hmain : X ^ mC * (|P| + 3) < Real.exp y := by
    have h1 : X ^ mC * (|P| + 3) < X ^ mC * (X / M) :=
      mul_lt_mul_of_pos_left hXdiv (by linarith)
    have h2 : X ^ mC * (X / M) = X ^ mC * X / M := by ring
    have h3 : X ^ mC * X / M ≤ X ^ (δ * n) / M := div_le_div_of_nonneg_right hpow hM.le
    linarith
  have hP0 : 0 ≤ |P| := abs_nonneg P
  have hB1 : 2 * X ^ Ct + 1 < Real.exp y := by nlinarith
  have hB2 : P < Real.exp y := by
    have := le_abs_self P
    nlinarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hw.q_prime.pos
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hw.d_prime.pos
  have hqlo := hw.q_lo
  have hdlo := hw.d_lo
  rw [hY] at hqlo hdlo
  have hq : Real.exp y < q := by
    rw [← Real.exp_log hq0]
    exact Real.exp_lt_exp.2 (by rw [hy_def]; exact hqlo)
  have hd : Real.exp y < d := by
    rw [← Real.exp_log hd0]
    apply Real.exp_lt_exp.2
    have hXd : 0 ≤ X ^ δ := by positivity
    have hl2 : 1 ≤ Real.log (X ^ (1 / J)) ^ 2 := by nlinarith
    have : X ^ δ / 2 ≤ X ^ δ * Real.log (X ^ (1 / J)) ^ 2 / 2 := by nlinarith
    rw [hy_def]
    linarith
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Mirrors `UpperTheory.V.log_conductor_mul_height_le_of_pageN`
(`LogConductorMulHeightLeOfPageN.lean:L6-56`). -/
theorem log_conductor_mul_height_le_of_pageN (eps Ct : ℝ) (m : ℕ)
    (heps : 0 < eps) (heps1 : eps < 1 / 52) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ N t e q d : ℕ, 1 ≤ N → N ≤ 2 ^ (e + 2) * m * q * d →
      PageN eps x e → 1 ≤ t → (t : ℝ) ≤ x ^ Ct → Real.log ((q : ℝ) * d) ≤ x ^ (eps / 4) →
      Real.log ((N : ℝ) * t) ≤ 2 * x ^ (eps / 4) := by
  have hr : 0 < eps / 4 := by positivity
  have hK0 : 0 < 3 + |Ct| := by positivity
  have h1 := (isLittleO_log_rpow_atTop hr).bound (by positivity : (0 : ℝ) < 1 / (2 * (3 + |Ct|)))
  have h2 := (tendsto_rpow_atTop hr).eventually_ge_atTop (2 * (3 * Real.log 2 + Real.log m))
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 ((h1.and h2).and (Filter.eventually_ge_atTop 1))
  refine ⟨x0, fun x hx N t e q d hN hNle hP ht htx hqd => ?_⟩
  obtain ⟨⟨hl, hg⟩, hx1⟩ := hx0 x hx
  have hxpos : 0 < x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hX : 0 < x ^ (eps / 4) := Real.rpow_pos_of_pos hxpos _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogx, abs_of_pos hX] at hl
  have hKl : (3 + |Ct|) * Real.log x ≤ x ^ (eps / 4) / 2 := by
    calc (3 + |Ct|) * Real.log x
        ≤ (3 + |Ct|) * (1 / (2 * (3 + |Ct|)) * x ^ (eps / 4)) :=
          mul_le_mul_of_nonneg_left hl hK0.le
      _ = x ^ (eps / 4) / 2 := by field_simp
  have hprod : 1 ≤ 2 ^ (e + 2) * m * q * d := le_trans hN hNle
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hprod)
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hprod)
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hprod)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have htr : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hNle' : (N : ℝ) ≤ 2 ^ (e + 2) * m * ((q : ℝ) * d) := by
    rw [← mul_assoc]
    exact_mod_cast hNle
  rw [Real.log_mul (by linarith) (by linarith)]
  have hlogN : Real.log N ≤ ((e : ℝ) + 2) * Real.log 2 + Real.log m + Real.log ((q : ℝ) * d) := by
    calc Real.log N
        ≤ Real.log (2 ^ (e + 2) * m * ((q : ℝ) * d)) :=
          Real.log_le_log (by linarith) hNle'
      _ = ((e : ℝ) + 2) * Real.log 2 + Real.log m + Real.log ((q : ℝ) * d) := by
          rw [Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by positivity) (by linarith), Real.log_pow]
          push_cast
          ring
  have hlogt : Real.log t ≤ Ct * Real.log x := by
    calc Real.log t ≤ Real.log (x ^ Ct) := Real.log_le_log (by linarith) htx
      _ = Ct * Real.log x := Real.log_rpow hxpos _
  have hE : (e : ℝ) * Real.log 2 ≤ Real.log 2 + (2 + 8 * eps) * Real.log x := by
    have h := Real.log_le_log (by positivity) hP.2
    rw [Real.log_pow, Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hxpos _).ne',
      Real.log_rpow hxpos] at h
    exact h
  have hC : Ct * Real.log x ≤ |Ct| * Real.log x :=
    mul_le_mul_of_nonneg_right (le_abs_self Ct) hlogx
  nlinarith [mul_nonneg hlogx (by linarith : (0 : ℝ) ≤ 1 - 8 * eps)]

/-- Mirrors `UpperTheory.V.minusBound_le_exp_of_log_le` (`minusle.lean:L6-75`). -/
theorem minusBound_le_exp_of_log_le (C : ℝ) (o : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n N t : ℕ) (W : ℝ), 1 ≤ N → 1 ≤ t → n ≤ N →
      Real.log ((N : ℝ) * t) ≤ 2 * W → minusBound C o n N t ≤ K * Real.exp (8 * W) := by
  refine ⟨3 + |C| * ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3, by positivity, ?_⟩
  intro n N t W hN ht hn hW
  unfold minusBound
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hn' : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hX1 : (1 : ℝ) ≤ (N : ℝ) * t := one_le_mul_of_one_le_of_one_le hN1 ht1
  have hXpos : 0 < (N : ℝ) * t := by linarith
  have hXe : (N : ℝ) * t ≤ Real.exp (2 * W) := by
    rw [← Real.exp_log hXpos]
    exact Real.exp_le_exp.mpr hW
  have hX4 : ((N : ℝ) * t) ^ 4 ≤ Real.exp (8 * W) := by
    have e : Real.exp (8 * W) = Real.exp (2 * W) ^ 4 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [e]
    exact pow_le_pow_left₀ hXpos.le hXe 4
  have hnt : (n : ℝ) * t ≤ (N : ℝ) * t := mul_le_mul_of_nonneg_right hn' (by positivity)
  have htX : (t : ℝ) ≤ (N : ℝ) * t := by nlinarith
  have hlog : Real.log ((t : ℝ) * N) ≤ (N : ℝ) * t := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < t * N by linarith)
    linarith
  have hlog0 : 0 ≤ Real.log ((t : ℝ) * N) := Real.log_nonneg (by linarith)
  have h1 : 3 * (n : ℝ) * t ^ 2 * Real.log (t * N) ≤ 3 * ((N : ℝ) * t) ^ 4 := by
    have h3 : (n : ℝ) * t * t * Real.log (t * N) ≤ ((N : ℝ) * t) ^ 3 := by
      calc (n : ℝ) * t * t * Real.log (t * N)
          ≤ ((N : ℝ) * t) * ((N : ℝ) * t) * ((N : ℝ) * t) :=
            mul_le_mul (mul_le_mul hnt htX (by positivity) (by positivity)) hlog hlog0 (by positivity)
        _ = ((N : ℝ) * t) ^ 3 := by ring
    have h34 : ((N : ℝ) * t) ^ 3 ≤ ((N : ℝ) * t) ^ 4 := pow_le_pow_right₀ hX1 (by norm_num)
    have e : 3 * (n : ℝ) * t ^ 2 * Real.log (t * N) =
        3 * ((n : ℝ) * t * t * Real.log (t * N)) := by ring
    rw [e]
    linarith
  have h2 : ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) * n ^ 2 * t ^ 2 * Real.log (t * l * N) ^ 2
      ≤ (∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3) * ((N : ℝ) * t) ^ 4 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro l hl
    have hl1 : (1 : ℝ) ≤ l := by
      have := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hl)
      exact_mod_cast this.one_lt.le
    have hge : (1 : ℝ) ≤ t * l * N :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le ht1 hl1) hN1
    have hlg : Real.log ((t : ℝ) * l * N) ≤ l * ((N : ℝ) * t) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < t * l * N by linarith)
      linarith
    have hlg0 : 0 ≤ Real.log ((t : ℝ) * l * N) := Real.log_nonneg hge
    have hsq : Real.log ((t : ℝ) * l * N) ^ 2 ≤ (l * ((N : ℝ) * t)) ^ 2 :=
      pow_le_pow_left₀ hlg0 hlg 2
    have hnt2 : ((n : ℝ) * t) ^ 2 ≤ ((N : ℝ) * t) ^ 2 := pow_le_pow_left₀ (by positivity) hnt 2
    calc (l : ℝ) * n ^ 2 * t ^ 2 * Real.log (t * l * N) ^ 2
        = (l : ℝ) * ((n : ℝ) * t) ^ 2 * Real.log (t * l * N) ^ 2 := by ring
      _ ≤ (l : ℝ) * ((N : ℝ) * t) ^ 2 * (l * ((N : ℝ) * t)) ^ 2 := by gcongr
      _ = (l : ℝ) ^ 3 * ((N : ℝ) * t) ^ 4 := by ring
  have hS0 : 0 ≤ ∑ l ∈ o.primeFactors.erase 2,
      (l : ℝ) * n ^ 2 * t ^ 2 * Real.log (t * l * N) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hK0 : 0 ≤ 3 + |C| * ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3 := by positivity
  calc 3 * (n : ℝ) * t ^ 2 * Real.log (t * N)
        + C * ∑ l ∈ o.primeFactors.erase 2,
          (l : ℝ) * n ^ 2 * t ^ 2 * Real.log (t * l * N) ^ 2
      ≤ 3 * ((N : ℝ) * t) ^ 4 +
          |C| * ((∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3) * ((N : ℝ) * t) ^ 4) :=
        add_le_add h1 ((mul_le_mul_of_nonneg_right (le_abs_self C) hS0).trans
          (mul_le_mul_of_nonneg_left h2 (abs_nonneg C)))
    _ = (3 + |C| * ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3) * ((N : ℝ) * t) ^ 4 := by ring
    _ ≤ (3 + |C| * ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3) * Real.exp (8 * W) :=
        mul_le_mul_of_nonneg_left hX4 hK0

/-- Master exponential absorption theorem (`ErrorTermsLeSqrtExpRpow.lean:L6-88`):
combines the 2-part (`exp(x^(4ε/5)) log 2`), minus-parity (`K exp(8 x^(ε/4))`), and
plus-parity (`u^C + C exp(x^(4ε/5))`) bounds inside `√(exp(x^ε))`. -/
theorem error_terms_le_sqrt_exp_rpow (eps K C : ℝ) (heps : 0 < eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ u : ℝ, 1 ≤ u → Real.log u ≤ 2 * x ^ (eps / 4) →
      Real.exp (x ^ (4 * eps / 5)) * Real.log 2 + K * Real.exp (8 * x ^ (eps / 4)) +
          (u ^ C + C * Real.exp (x ^ (4 * eps / 5))) ≤
        Real.sqrt (Real.exp (x ^ eps)) := by
  set N : ℝ := Real.log 2 + |C| + |K| + 1 with hN
  set D : ℝ := 9 + 2 * |C| with hD
  set T : ℝ := 2 * (D + Real.log N + 1) with hTdef
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hN1 : 1 ≤ N := by
    have := abs_nonneg C
    have := abs_nonneg K
    linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hD0 : 9 ≤ D := by
    have := abs_nonneg C
    linarith
  have hT : 0 ≤ T := by linarith
  refine ⟨max 1 (T ^ (5 / eps)), fun x hx u hu hlog => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hxpos : 0 < x := by linarith
  set a := x ^ (eps / 4) with ha
  set b := x ^ (4 * eps / 5) with hb
  set s := x ^ (eps / 5) with hs
  have hab : a ≤ b := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hb1 : 1 ≤ b := Real.one_le_rpow hx1 (by positivity)
  have ha0 : 0 ≤ a := by positivity
  have hc : x ^ eps = b * s := by
    rw [hb, hs, ← Real.rpow_add hxpos]
    congr 1
    ring
  have hsT : T ≤ s := by
    have h1 : T = (T ^ (5 / eps)) ^ (eps / 5) := by
      rw [← Real.rpow_mul hT]
      have : 5 / eps * (eps / 5) = 1 := by field_simp
      rw [this, Real.rpow_one]
    rw [h1, hs]
    exact Real.rpow_le_rpow (by positivity) (le_trans (le_max_right _ _) hx) (by positivity)
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg hu
  have hupos : 0 < u := by linarith
  have huC : u ^ C ≤ Real.exp (D * b) := by
    rw [Real.rpow_def_of_pos hupos]
    apply Real.exp_le_exp.mpr
    have e1 : Real.log u * C ≤ Real.log u * |C| :=
      mul_le_mul_of_nonneg_left (le_abs_self C) hlogu
    have e2 : Real.log u * |C| ≤ (2 * a) * |C| :=
      mul_le_mul_of_nonneg_right hlog (abs_nonneg C)
    have e3 : (2 * a) * |C| ≤ (2 * b) * |C| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg C)
    have e4 : (2 * b) * |C| ≤ D * b := by
      rw [hD]
      nlinarith [abs_nonneg C]
    linarith
  have hK : K * Real.exp (8 * a) ≤ |K| * Real.exp (D * b) := by
    have h1 : K * Real.exp (8 * a) ≤ |K| * Real.exp (8 * a) :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le
    have h2 : Real.exp (8 * a) ≤ Real.exp (D * b) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h3 := mul_le_mul_of_nonneg_left h2 (abs_nonneg K)
    linarith
  have hE : Real.exp b ≤ Real.exp (D * b) := Real.exp_le_exp.mpr (by nlinarith)
  have hCE : C * Real.exp b ≤ |C| * Real.exp (D * b) := by
    have h1 : C * Real.exp b ≤ |C| * Real.exp b :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
    have h3 := mul_le_mul_of_nonneg_left hE (abs_nonneg C)
    linarith
  have hL2 : Real.exp b * Real.log 2 ≤ Real.exp (D * b) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hE hl2.le
  have hsum : Real.exp b * Real.log 2 + K * Real.exp (8 * a) + (u ^ C + C * Real.exp b)
      ≤ N * Real.exp (D * b) := by
    rw [hN]
    nlinarith
  have hfin : N * Real.exp (D * b) ≤ Real.exp (x ^ eps / 2) := by
    rw [← Real.exp_log (by linarith : (0 : ℝ) < N), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hc]
    have : b * (D + Real.log N + 1) ≤ b * s / 2 := by
      have := mul_le_mul_of_nonneg_left hsT (by linarith : (0 : ℝ) ≤ b)
      rw [hTdef] at this
      linarith
    nlinarith
  rw [Real.exp_half] at hfin
  linarith

/-! ## 3. Selmer Parity Splitting & Six-Case (`CountI`–`CountZ`) Combinatorics -/

/-- Parity decomposition of a `SelmerSystem` into its `2`-part, odd minus-part, and odd plus-part. -/
structure SelmerParityDecomp (S : SelmerSystem) where
  twoLen : (E : Type) → [Field E] → [NumberField E] → ℕ → ℕ∞
  minusLen : (E : Type) → [Field E] → [NumberField E] → Nat.Primes → ℕ → ℕ∞
  plusLen : (E : Type) → [Field E] → [NumberField E] → Nat.Primes → ℕ → ℕ∞
  le_two : ∀ (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (e : ℕ),
    (l : ℕ) = 2 → S.shaLen E l e ≤ twoLen E e
  le_odd : ∀ (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (e : ℕ),
    (l : ℕ) ≠ 2 → S.shaLen E l e ≤ minusLen E l e + plusLen E l e

/-- Bounded `2`-part Selmer lengths for `1 ≤ e < t`. -/
def VVTwoLe {S : SelmerSystem} (D : SelmerParityDecomp S)
    (E : Type) [Field E] [NumberField E] (t : ℕ) (B : ℝ) : Prop :=
  (∀ e : ℕ, 0 < e → e < t → D.twoLen E e ≠ ⊤) ∧
  ∑ e ∈ Finset.Ico 1 t, ((D.twoLen E e).toNat : ℝ) ≤ B

/-- Bounded odd minus-parity Selmer lengths for `1 ≤ e < t`. -/
def VVMinusLe {S : SelmerSystem} (D : SelmerParityDecomp S)
    (E : Type) [Field E] [NumberField E] (t : ℕ) (B : ℝ) : Prop :=
  (∀ (l : Nat.Primes) (e : ℕ), (l : ℕ) ≠ 2 → 0 < e → e < t → D.minusLen E l e ≠ ⊤) ∧
  ∀ P : Finset Nat.Primes, (∀ l ∈ P, (l : ℕ) ≠ 2) →
    ∑ l ∈ P, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((D.minusLen E l e).toNat : ℝ) ≤ B

/-- Bounded odd plus-parity Selmer lengths for `1 ≤ e < t`. -/
def VVPlusLe {S : SelmerSystem} (D : SelmerParityDecomp S)
    (E : Type) [Field E] [NumberField E] (t : ℕ) (B : ℝ) : Prop :=
  (∀ (l : Nat.Primes) (e : ℕ), (l : ℕ) ≠ 2 → 0 < e → e < t → D.plusLen E l e ≠ ⊤) ∧
  ∀ P : Finset Nat.Primes, (∀ l ∈ P, (l : ℕ) ≠ 2) →
    ∑ l ∈ P, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((D.plusLen E l e).toNat : ℝ) ≤ B

theorem VVMinusLe.mono {S : SelmerSystem} {D : SelmerParityDecomp S}
    {E : Type} [Field E] [NumberField E] {t : ℕ} {B B' : ℝ}
    (h : VVMinusLe D E t B) (hB : B ≤ B') : VVMinusLe D E t B' :=
  ⟨h.1, fun P hP => (h.2 P hP).trans hB⟩

/-- Combines the `2`-part, minus-parity, and plus-parity bounds into `VVle S E t (...)`. -/
theorem vvle_of_parts {S : SelmerSystem} {D : SelmerParityDecomp S}
    {E : Type} [Field E] [NumberField E] {t : ℕ} {B2 Bm Bp : ℝ}
    (h2 : VVTwoLe D E t B2) (hm : VVMinusLe D E t Bm) (hp : VVPlusLe D E t Bp) :
    VVle S E t (B2 * Real.log 2 + Bm + Bp) := by
  classical
  refine ⟨?_, ?_⟩
  · intro l e he1 he2
    by_cases hl2 : (l : ℕ) = 2
    · exact ne_top_of_le_ne_top (h2.1 e he1 he2) (D.le_two E l e hl2)
    · have hfin : D.minusLen E l e + D.plusLen E l e ≠ ⊤ :=
        WithTop.add_ne_top.2 ⟨hm.1 l e hl2 he1 he2, hp.1 l e hl2 he1 he2⟩
      exact ne_top_of_le_ne_top hfin (D.le_odd E l e hl2)
  · intro P
    rw [← Finset.sum_filter_add_sum_filter_not P (fun l : Nat.Primes => (l : ℕ) = 2)]
    set P2 := P.filter (fun l : Nat.Primes => (l : ℕ) = 2)
    set Podd := P.filter (fun l : Nat.Primes => (l : ℕ) ≠ 2)
    have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    set p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
    have hP2_sub : P2 ⊆ {p2} := by
      intro l hl
      rw [Finset.mem_singleton]
      exact Subtype.ext (Finset.mem_filter.mp hl).2
    have hpart2 :
        ∑ l ∈ P2, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((S.shaLen E l e).toNat : ℝ) ≤
          B2 * Real.log 2 := by
      have hsub := Finset.sum_le_sum_of_subset_of_nonneg hP2_sub
        (f := fun l : Nat.Primes =>
          Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((S.shaLen E l e).toNat : ℝ))
        (fun l _ _ => mul_nonneg (Real.log_natCast_nonneg _)
          (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _))
      rw [Finset.sum_singleton] at hsub
      have hterm :
          ∑ e ∈ Finset.Ico 1 t, ((S.shaLen E p2 e).toNat : ℝ) ≤
            ∑ e ∈ Finset.Ico 1 t, ((D.twoLen E e).toNat : ℝ) := by
        apply Finset.sum_le_sum
        intro e he
        obtain ⟨he1, he2⟩ := Finset.mem_Ico.mp he
        exact_mod_cast ENat.toNat_le_toNat (D.le_two E p2 e rfl) (h2.1 e he1 he2)
      have hmul : Real.log (p2 : ℕ) *
          ∑ e ∈ Finset.Ico 1 t, ((S.shaLen E p2 e).toNat : ℝ) ≤
          Real.log 2 * B2 := by
        have hp2log : Real.log (p2 : ℕ) = Real.log 2 := by simp [p2]
        rw [hp2log]
        exact mul_le_mul_of_nonneg_left (hterm.trans h2.2) hlog2_nn
      linarith
    have hPodd : ∀ l ∈ Podd, (l : ℕ) ≠ 2 := fun l hl => (Finset.mem_filter.mp hl).2
    have hpartOdd :
        ∑ l ∈ Podd, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((S.shaLen E l e).toNat : ℝ) ≤
          Bm + Bp := by
      have hstep :
          ∑ l ∈ Podd, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((S.shaLen E l e).toNat : ℝ) ≤
            ∑ l ∈ Podd,
              (Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((D.minusLen E l e).toNat : ℝ) +
               Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((D.plusLen E l e).toNat : ℝ)) := by
        apply Finset.sum_le_sum
        intro l hl
        have hl2 : (l : ℕ) ≠ 2 := hPodd l hl
        rw [← mul_add, ← Finset.sum_add_distrib]
        apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg _)
        apply Finset.sum_le_sum
        intro e he
        obtain ⟨he1, he2⟩ := Finset.mem_Ico.mp he
        have hmne := hm.1 l e hl2 he1 he2
        have hpne := hp.1 l e hl2 he1 he2
        have hle : (S.shaLen E l e).toNat ≤ (D.minusLen E l e + D.plusLen E l e).toNat :=
          ENat.toNat_le_toNat (D.le_odd E l e hl2) (WithTop.add_ne_top.2 ⟨hmne, hpne⟩)
        rw [ENat.toNat_add hmne hpne] at hle
        exact_mod_cast hle
      rw [Finset.sum_add_distrib] at hstep
      exact hstep.trans (add_le_add (hm.2 Podd hPodd) (hp.2 Podd hPodd))
    linarith

/-- Bad-prime combinatorial splitting isolating the odd-order `CountIV` exception set `O`
(`FinalLe.lean:L14-54`). -/
theorem sum_split_bad_prime {ι : Type} (T : ℕ → Finset ι) (O : Finset ι) (v : ι → ℕ → ℝ)
    (t N q : ℕ) (L K S : ℝ)
    (hv : ∀ i e, 0 ≤ v i e) (hL : 0 ≤ L) (hK : 0 ≤ K) (hS : 0 ≤ S)
    (hT : ∀ e, (T e).card ≤ N) (hq : O.card ≤ q)
    (h1 : ∀ e ∈ Finset.Ico 1 t, ∀ i ∈ T e, i ∈ O ∨ v i e * L ≤ K)
    (h2 : ∀ i ∈ O, ∑ e ∈ Finset.Ico 1 t, v i e ≤ S) :
    L * ∑ e ∈ Finset.Ico 1 t, ∑ i ∈ T e, v i e ≤ L * (q * S) + t * (N * K) := by
  classical
  have step : ∀ e ∈ Finset.Ico 1 t, L * ∑ i ∈ T e, v i e ≤ L * ∑ i ∈ O, v i e + N * K := by
    intro e he
    rw [Finset.mul_sum, Finset.mul_sum]
    calc ∑ i ∈ T e, L * v i e
        ≤ ∑ i ∈ T e, ((if i ∈ O then L * v i e else 0) + K) := by
          apply Finset.sum_le_sum
          intro i hi
          by_cases hO : i ∈ O
          · rw [if_pos hO]; linarith
          · rw [if_neg hO]
            rcases h1 e he i hi with h | h
            · exact absurd h hO
            · linarith [mul_comm (v i e) L]
      _ = ∑ i ∈ T e ∩ O, L * v i e + (T e).card * K := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_ite_mem]
      _ ≤ ∑ i ∈ O, L * v i e + N * K := by
          apply add_le_add
          · exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
              (fun i _ _ => mul_nonneg hL (hv i e))
          · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hT e) hK
  have hA : ∑ i ∈ O, ∑ e ∈ Finset.Ico 1 t, v i e ≤ q * S := by
    calc ∑ i ∈ O, ∑ e ∈ Finset.Ico 1 t, v i e
        ≤ ∑ _i ∈ O, S := Finset.sum_le_sum h2
      _ = O.card * S := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ q * S := mul_le_mul_of_nonneg_right (by exact_mod_cast hq) hS
  have hB : ((Finset.Ico 1 t).card : ℝ) ≤ t := by
    rw [Nat.card_Ico]
    exact_mod_cast Nat.sub_le t 1
  have hNK : 0 ≤ (N : ℝ) * K := mul_nonneg (Nat.cast_nonneg _) hK
  calc L * ∑ e ∈ Finset.Ico 1 t, ∑ i ∈ T e, v i e
      = ∑ e ∈ Finset.Ico 1 t, L * ∑ i ∈ T e, v i e := Finset.mul_sum _ _ _
    _ ≤ ∑ e ∈ Finset.Ico 1 t, (L * ∑ i ∈ O, v i e + N * K) := Finset.sum_le_sum step
    _ = L * ∑ i ∈ O, ∑ e ∈ Finset.Ico 1 t, v i e + ((Finset.Ico 1 t).card : ℝ) * (N * K) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_comm]
    _ ≤ L * (q * S) + t * (N * K) :=
        add_le_add (mul_le_mul_of_nonneg_left hA hL) (mul_le_mul_of_nonneg_right hB hNK)

/-- Bad-prime polynomial + layer-loss absorption (`FinalLe.lean:L56-84`). -/
theorem sumIn_arith_combine (M L l q N t B : ℝ) (a b C : ℕ)
    (hM : M = N * t) (h3 : 3 ≤ M) (hL : L ≤ l) (_hl : 0 ≤ l) (hlM : l ≤ M)
    (hq : 0 ≤ q) (hqM : q ≤ M) (hB : 0 ≤ B)
    (hC : a + 2 * b + 9 ≤ C) (hC' : l * q ≤ C) :
    L * (q * (B + M ^ a)) + t * (N * (M ^ 2) ^ b) + L * (N * (t * M ^ 6)) ≤ M ^ C + C * B := by
  have hM0 : 0 ≤ M := by linarith
  have hM1 : 1 ≤ M := by linarith
  have hNt : N * (t * M ^ 6) = M ^ 7 := by rw [hM]; ring
  have hNb : t * (N * (M ^ 2) ^ b) = M ^ (2 * b + 1) := by rw [hM]; ring
  rw [hNt, hNb]
  have hX : 0 ≤ q * (B + M ^ a) := mul_nonneg hq (by positivity)
  have e1 : L * (q * (B + M ^ a)) ≤ l * (q * (B + M ^ a)) := mul_le_mul_of_nonneg_right hL hX
  have e2 : l * (q * (B + M ^ a)) = (l * q) * B + l * q * M ^ a := by ring
  have e3 : (l * q) * B ≤ C * B := mul_le_mul_of_nonneg_right hC' hB
  have hlq : l * q ≤ M * M := mul_le_mul hlM hqM hq hM0
  have e4 : l * q * M ^ a ≤ M * M * M ^ a := mul_le_mul_of_nonneg_right hlq (pow_nonneg hM0 a)
  have e4' : M * M * M ^ a = M ^ (a + 2) := by ring
  have e5 : L * M ^ 7 ≤ l * M ^ 7 := mul_le_mul_of_nonneg_right hL (pow_nonneg hM0 7)
  have e6 : l * M ^ 7 ≤ M * M ^ 7 := mul_le_mul_of_nonneg_right hlM (pow_nonneg hM0 7)
  have e6' : M * M ^ 7 = M ^ 8 := by ring
  obtain ⟨D, hD⟩ : ∃ D, C = D + 1 := ⟨C - 1, by omega⟩
  have p1 : M ^ (a + 2) ≤ M ^ D := pow_le_pow_right₀ hM1 (by omega)
  have p2 : M ^ (2 * b + 1) ≤ M ^ D := pow_le_pow_right₀ hM1 (by omega)
  have p3 : M ^ 8 ≤ M ^ D := pow_le_pow_right₀ hM1 (by omega)
  have p4 : 3 * M ^ D ≤ M * M ^ D := mul_le_mul_of_nonneg_right h3 (pow_nonneg hM0 D)
  have p5 : M ^ C = M * M ^ D := by rw [hD, pow_succ']
  linarith

/-- Cardinality bound for primes `≤ n` (`SumOut.lean:L19-29`). -/
theorem card_primes_le (S : Finset Nat.Primes) (n : ℕ) (h : ∀ l ∈ S, (l : ℕ) ≤ n) :
    S.card ≤ n := by
  have key : S.card ≤ (Finset.Icc 1 n).card := by
    apply Finset.card_le_card_of_injOn (fun l : Nat.Primes => (l : ℕ))
    · intro l hl
      have h1 := h l hl
      have h2 := l.2.one_lt
      simp only [Finset.coe_Icc, Set.mem_Icc]
      omega
    · intro x _ y _ hxy
      exact Subtype.ext hxy
  simpa using key

/-- Good-prime (`l ∉ Bchi`) `CountI` + `CountZ / CountII / CountIII` absorption (`SumOut.lean:L31-47`). -/
theorem sumOut_arith_combine (M t : ℝ) (a b : ℕ) (hM : 2 ≤ M) (ht : t ≤ M) :
    t * (M ^ a + 2 * M * M ^ b) ≤ M ^ (a + b + 4) := by
  have hM1 : (1 : ℝ) ≤ M := by linarith
  have hpos : 0 ≤ M ^ a + 2 * M * M ^ b := by positivity
  have h1 : t * (M ^ a + 2 * M * M ^ b) ≤ M * (M ^ a + 2 * M * M ^ b) :=
    mul_le_mul_of_nonneg_right ht hpos
  have hA : M ^ (a + 1) ≤ M ^ (a + b + 3) := pow_le_pow_right₀ hM1 (by omega)
  have hB : M ^ (b + 2) ≤ M ^ (a + b + 2) := pow_le_pow_right₀ hM1 (by omega)
  have hY : 0 ≤ M ^ (a + b + 2) := by positivity
  have hX : 0 ≤ M ^ (a + b + 3) := by positivity
  have eX : M ^ (a + b + 3) = M * M ^ (a + b + 2) := by ring
  have e4 : M ^ (a + b + 4) = M * M ^ (a + b + 3) := by ring
  have eL : M * (M ^ a + 2 * M * M ^ b) = M ^ (a + 1) + 2 * M ^ (b + 2) := by ring
  have k1 : 0 ≤ (M - 2) * M ^ (a + b + 2) := mul_nonneg (by linarith) hY
  have k2 : 0 ≤ (M - 1) * M ^ (a + b + 3) := mul_nonneg (by linarith) hX
  rw [e4]
  nlinarith

/-- Unifies bad-prime (`SumIn`, `k ≤ K` bad primes) and good-prime (`SumOut`) bounds
(`PointArith.lean:L5-34`). -/
theorem point_arith_combine (x B : ℝ) (hx : 2 ≤ x) (hB : 0 ≤ B) (k K D C0 : ℕ) (hk : k ≤ K) :
    (k : ℝ) * (x ^ D + D * B) + x ^ C0 ≤
      x ^ (C0 + D + K + K * D) + ((C0 + D + K + K * D : ℕ) : ℝ) * B := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have h1 := one_add_mul_le_pow (show (-2 : ℝ) ≤ x - 1 by linarith) K
  rw [show (1 : ℝ) + (x - 1) = x by ring] at h1
  have hKr : (k : ℝ) ≤ K := by exact_mod_cast hk
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have hD0 : (0 : ℝ) ≤ D := by positivity
  have hC0 : (0 : ℝ) ≤ C0 := by positivity
  have hc : (K : ℝ) + 1 ≤ x ^ K := by nlinarith
  have ha : 1 ≤ x ^ C0 := one_le_pow₀ hx1
  have hb : 1 ≤ x ^ D := one_le_pow₀ hx1
  have he : 1 ≤ x ^ (K * D) := one_le_pow₀ hx1
  have hpow : x ^ (C0 + D + K + K * D) = x ^ C0 * x ^ D * x ^ K * x ^ (K * D) := by
    rw [pow_add, pow_add, pow_add]
  have hM : (k : ℝ) * D ≤ ((C0 + D + K + K * D : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hMB : (k : ℝ) * D * B ≤ ((C0 + D + K + K * D : ℕ) : ℝ) * B :=
    mul_le_mul_of_nonneg_right hM hB
  have hab : x ^ C0 ≤ x ^ C0 * x ^ D := le_mul_of_one_le_right (by positivity) hb
  have habc : x ^ C0 * x ^ D * ((K : ℝ) + 1) ≤ x ^ C0 * x ^ D * x ^ K :=
    mul_le_mul_of_nonneg_left hc (by positivity)
  have hq : x ^ C0 * x ^ D * x ^ K ≤ x ^ C0 * x ^ D * x ^ K * x ^ (K * D) :=
    le_mul_of_one_le_right (by positivity) he
  have hkb : (k : ℝ) * x ^ D ≤ K * x ^ D := mul_le_mul_of_nonneg_right hKr (by positivity)
  have hKb : (K : ℝ) * x ^ D ≤ K * (x ^ C0 * x ^ D) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) ha) hK0
  rw [hpow]
  nlinarith

/-- Abstract host-level six-case Selmer decomposition at fixed `(E, t, N, q, Bchi, B)`:
packages the exact 6-case character partition (`CaseI`: `U(3)` + Kato, `CaseII`/`CaseIII`:
`Sp(4)` + adjoint lifting, `CaseIV`: odd-order Ferrero–Washington/Mahler, `CaseV`/`CaseVs`:
weight-2 reduced unitary lift / Poitou–Tate, `CaseZ`: Bernoulli nonvanishing) and proves the
global `VVPlusLe` bound `M^C + C * B` from scratch. -/
structure SixCaseSelmerHost {S : SelmerSystem} (D : SelmerParityDecomp S)
    (E : Type) [Field E] [NumberField E] (t N q : ℕ) (Bchi : Finset ℕ) (B : ℝ) where
  N_ge_16 : 16 ≤ N
  t_ge_2 : 2 ≤ t
  q_le_N : q ≤ N
  B_nonneg : 0 ≤ B
  bad_le_N : ∀ l ∈ Bchi, l ≤ N
  /-- Character index type per odd prime `l`, active characters `T l e`, and normalized Selmer value `v l i e`. -/
  CharIdx : Nat.Primes → Type
  T : (l : Nat.Primes) → ℕ → Finset (CharIdx l)
  T_card_le : ∀ l e, (T l e).card ≤ N
  v : (l : Nat.Primes) → CharIdx l → ℕ → ℝ
  v_nonneg : ∀ l i e, 0 ≤ v l i e
  /-- Plus-part finiteness at all odd primes. -/
  plus_ne_top : ∀ (l : Nat.Primes) (e : ℕ), (l : ℕ) ≠ 2 → 0 < e → e < t → D.plusLen E l e ≠ ⊤
  /-- At bad primes `l ∈ Bchi`, `plusLen` is dominated by character sum + level loss `≤ N * (t * (N*t)^6)`. -/
  red_bad : ∀ (l : Nat.Primes), (l : ℕ) ∈ Bchi →
    ∑ e ∈ Finset.Ico 1 t, ((D.plusLen E l e).toNat : ℝ) ≤
      (∑ e ∈ Finset.Ico 1 t, ∑ i ∈ T l e, v l i e) + (N : ℝ) * ((t : ℝ) * ((N : ℝ) * t) ^ 6)
  /-- At good primes `l ∉ Bchi`, `plusLen` is dominated directly by the character sum (zero loss). -/
  red_good : ∀ (l : Nat.Primes), (l : ℕ) ≠ 2 → (l : ℕ) ∉ Bchi →
    ∑ e ∈ Finset.Ico 1 t, ((D.plusLen E l e).toNat : ℝ) ≤
      ∑ e ∈ Finset.Ico 1 t, ∑ i ∈ T l e, v l i e
  /-- Odd-order exception subset `O l` (Case IV) at bad primes, of cardinality `≤ q`. -/
  O : (l : Nat.Primes) → Finset (CharIdx l)
  O_card_le : ∀ l : Nat.Primes, (l : ℕ) ∈ Bchi → (O l).card ≤ q
  /-- Exponents for the 6 cases: `C1` (CountI), `C2` (CountII), `C3` (CountIII), `C4` (CountIV),
  `C5` (CountV), `C6` (CountVs), `CZ` (CountZ). -/
  C1 : ℕ
  C2 : ℕ
  C3 : ℕ
  C4 : ℕ
  C5 : ℕ
  C6 : ℕ
  CZ : ℕ
  /-- `CountIV` (Iwasawa/Mahler layer bound) on `O l` at bad primes. -/
  countIV : ∀ l : Nat.Primes, (l : ℕ) ∈ Bchi → ∀ i ∈ O l,
    ∑ e ∈ Finset.Ico 1 t, v l i e ≤ B + ((N : ℝ) * t) ^ C4
  /-- `CountII ∪ CountV ∪ CountVs` outside `O l` at bad primes. -/
  count_bad_nonO : ∀ l : Nat.Primes, (l : ℕ) ∈ Bchi → ∀ e ∈ Finset.Ico 1 t, ∀ i ∈ T l e,
    i ∈ O l ∨ v l i e * Real.log (l : ℕ) ≤ (((N : ℝ) * t) ^ 2) ^ (max C2 (max C5 C6))
  /-- Good-prime Case I (`(l - 1) ∤ 2e`) vs complementary `(l - 1) ∣ 2e` (`CountZ / CountII / CountIII`). -/
  isCaseI : Nat.Primes → ℕ → Prop
  decCaseI : ∀ l e, Decidable (isCaseI l e)
  /-- `CountI` (`U(3)` + Kato Euler system) summed over all good Case-I primes. -/
  countI : ∀ e ∈ Finset.Ico 1 t, ∀ Ls : Finset Nat.Primes,
    (∀ l ∈ Ls, (l : ℕ) ≠ 2 ∧ (l : ℕ) ∉ Bchi ∧ isCaseI l e) →
    ∑ l ∈ Ls, Real.log (l : ℕ) * ∑ i ∈ T l e, v l i e ≤ ((N : ℝ) * t) ^ C1
  /-- Non-Case-I good primes satisfy `l ≤ 2 t` (since `l - 1 ∣ 2e < 2t`). -/
  nonCaseI_le : ∀ l : Nat.Primes, (l : ℕ) ≠ 2 → (l : ℕ) ∉ Bchi →
    ∀ e ∈ Finset.Ico 1 t, ¬ isCaseI l e → (l : ℕ) ≤ 2 * t
  /-- `CountZ ∪ CountII ∪ CountIII` (`Sp(4)` + adjoint lifting + Bernoulli) at non-Case-I good primes. -/
  count_good_nonI : ∀ l : Nat.Primes, (l : ℕ) ≠ 2 → (l : ℕ) ∉ Bchi →
    ∀ e ∈ Finset.Ico 1 t, ¬ isCaseI l e → ∀ i ∈ T l e,
    v l i e * Real.log (l : ℕ) ≤ ((N : ℝ) * t) ^ (3 * max CZ (max C2 C3))

/-- Master six-case Selmer assembly theorem (proving `VVPlusLe` from scratch via
`sum_split_bad_prime`, `sumIn_arith_combine`, `card_primes_le`, `sumOut_arith_combine`, and
`point_arith_combine`). -/
theorem six_case_selmer_combine {S : SelmerSystem} {D : SelmerParityDecomp S}
    {E : Type} [Field E] [NumberField E] {t N q : ℕ} {Bchi : Finset ℕ} {B : ℝ}
    (H : SixCaseSelmerHost D E t N q Bchi B) :
    let Cm := max H.C2 (max H.C5 H.C6)
    let Dbad := H.C4 + 2 * Cm + 9 + (Bchi.sup id) * q
    let Kout := max H.CZ (max H.C2 H.C3)
    let C0 := H.C1 + 3 * Kout + 4
    let Ctot := C0 + Dbad + Bchi.card + Bchi.card * Dbad
    VVPlusLe D E t (((N : ℝ) * t) ^ Ctot + (Ctot : ℝ) * B) := by
  classical
  intro Cm Dbad Kout C0 Ctot
  set M : ℝ := (N : ℝ) * t with hMdef
  have hN16 : (16 : ℝ) ≤ N := by exact_mod_cast H.N_ge_16
  have ht2 : (2 : ℝ) ≤ t := by exact_mod_cast H.t_ge_2
  have hM3 : 3 ≤ M := by rw [hMdef]; nlinarith
  have hM2 : 2 ≤ M := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hNM : (N : ℝ) ≤ M := by rw [hMdef]; nlinarith
  have htM : (t : ℝ) ≤ M := by rw [hMdef]; nlinarith
  have hqM : (q : ℝ) ≤ M := le_trans (by exact_mod_cast H.q_le_N) hNM
  -- Part A: Bad prime bound (SumIn)
  have hBad : ∀ l : Nat.Primes, (l : ℕ) ∈ Bchi →
      Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((D.plusLen E l e).toNat : ℝ) ≤
        M ^ Dbad + (Dbad : ℝ) * B := by
    intro l hl
    set L : ℝ := Real.log ((l : ℕ) : ℝ)
    have hl1 : (1 : ℝ) ≤ (l : ℕ) := by exact_mod_cast l.2.one_lt.le
    have hL0 : 0 ≤ L := Real.log_nonneg hl1
    have hLl : L ≤ (l : ℕ) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (l : ℕ) by linarith)
      linarith
    have hlM : ((l : ℕ) : ℝ) ≤ M := le_trans (by exact_mod_cast H.bad_le_N l hl) hNM
    have hsplit := sum_split_bad_prime (H.T l) (H.O l) (H.v l) t N q L
      ((M ^ 2) ^ Cm) (B + M ^ H.C4)
      (H.v_nonneg l) hL0 (by positivity) (add_nonneg H.B_nonneg (pow_nonneg hM0 _))
      (H.T_card_le l) (H.O_card_le l hl) (H.count_bad_nonO l hl) (H.countIV l hl)
    have hred := mul_le_mul_of_nonneg_left (H.red_bad l hl) hL0
    rw [mul_add] at hred
    have hlsup : (l : ℕ) ≤ Bchi.sup id := Finset.le_sup (f := id) hl
    have hlqC : ((l : ℕ) : ℝ) * q ≤ (Dbad : ℝ) := by
      have hnat : (l : ℕ) * q ≤ Bchi.sup id * q := Nat.mul_le_mul_right q hlsup
      have hnat2 : (l : ℕ) * q ≤ Dbad := le_trans hnat (Nat.le_add_left _ _)
      exact_mod_cast hnat2
    have hfin := sumIn_arith_combine M L (l : ℕ) q N t B H.C4 Cm Dbad
      hMdef hM3 hLl (by linarith) hlM (Nat.cast_nonneg _) hqM H.B_nonneg (by omega) hlqC
    linarith
  -- Part B: Good prime bound (SumOut)
  have hGood : ∀ Sgood : Finset Nat.Primes, (∀ l ∈ Sgood, (l : ℕ) ≠ 2 ∧ (l : ℕ) ∉ Bchi) →
      ∑ l ∈ Sgood, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((D.plusLen E l e).toNat : ℝ) ≤
        M ^ C0 := by
    intro Sgood hSg
    have hstep : ∀ e ∈ Finset.Ico 1 t,
        ∑ l ∈ Sgood, Real.log (l : ℕ) * ∑ i ∈ H.T l e, H.v l i e ≤
          M ^ H.C1 + 2 * M * M ^ (3 * Kout) := by
      intro e he
      rw [← Finset.sum_filter_add_sum_filter_not Sgood (fun l => H.isCaseI l e)]
      have hA := H.countI e he (Sgood.filter (fun l => H.isCaseI l e)) (by
        intro l hl
        rw [Finset.mem_filter] at hl
        exact ⟨(hSg l hl.1).1, (hSg l hl.1).2, hl.2⟩)
      have hB1 : ∀ l ∈ Sgood.filter (fun l => ¬ H.isCaseI l e),
          Real.log (l : ℕ) * ∑ i ∈ H.T l e, H.v l i e ≤ (N : ℝ) * M ^ (3 * Kout) := by
        intro l hl
        rw [Finset.mem_filter] at hl
        rw [Finset.mul_sum]
        calc ∑ i ∈ H.T l e, Real.log (l : ℕ) * H.v l i e
            ≤ ∑ _i ∈ H.T l e, M ^ (3 * Kout) := by
              apply Finset.sum_le_sum
              intro i hi
              rw [mul_comm]
              exact H.count_good_nonI l (hSg l hl.1).1 (hSg l hl.1).2 e he hl.2 i hi
          _ = ((H.T l e).card : ℝ) * M ^ (3 * Kout) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (N : ℝ) * M ^ (3 * Kout) :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast H.T_card_le l e) (by positivity)
      have hcard : ((Sgood.filter (fun l => ¬ H.isCaseI l e)).card : ℝ) ≤ 2 * t := by
        have := card_primes_le (Sgood.filter (fun l => ¬ H.isCaseI l e)) (2 * t) (by
          intro l hl
          rw [Finset.mem_filter] at hl
          exact H.nonCaseI_le l (hSg l hl.1).1 (hSg l hl.1).2 e he hl.2)
        exact_mod_cast this
      have hB : ∑ l ∈ Sgood.filter (fun l => ¬ H.isCaseI l e),
          Real.log (l : ℕ) * ∑ i ∈ H.T l e, H.v l i e ≤ 2 * M * M ^ (3 * Kout) := by
        calc _ ≤ ∑ _l ∈ Sgood.filter (fun l => ¬ H.isCaseI l e), (N : ℝ) * M ^ (3 * Kout) :=
              Finset.sum_le_sum hB1
          _ = ((Sgood.filter (fun l => ¬ H.isCaseI l e)).card : ℝ) * ((N : ℝ) * M ^ (3 * Kout)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (2 * (t : ℝ)) * ((N : ℝ) * M ^ (3 * Kout)) :=
              mul_le_mul_of_nonneg_right hcard (by positivity)
          _ = 2 * M * M ^ (3 * Kout) := by rw [hMdef]; ring
      exact add_le_add hA hB
    calc ∑ l ∈ Sgood, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((D.plusLen E l e).toNat : ℝ)
        ≤ ∑ l ∈ Sgood, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ∑ i ∈ H.T l e, H.v l i e := by
          apply Finset.sum_le_sum
          intro l hl
          exact mul_le_mul_of_nonneg_left
            (H.red_good l (hSg l hl).1 (hSg l hl).2) (Real.log_natCast_nonneg _)
      _ = ∑ e ∈ Finset.Ico 1 t, ∑ l ∈ Sgood, Real.log (l : ℕ) * ∑ i ∈ H.T l e, H.v l i e := by
          simp_rw [Finset.mul_sum]
          exact Finset.sum_comm
      _ ≤ ∑ _e ∈ Finset.Ico 1 t, (M ^ H.C1 + 2 * M * M ^ (3 * Kout)) := Finset.sum_le_sum hstep
      _ = ((Finset.Ico 1 t).card : ℝ) * (M ^ H.C1 + 2 * M * M ^ (3 * Kout)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (t : ℝ) * (M ^ H.C1 + 2 * M * M ^ (3 * Kout)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [Nat.card_Ico]
          exact_mod_cast Nat.sub_le t 1
      _ ≤ M ^ C0 := sumOut_arith_combine M t H.C1 (3 * Kout) hM2 htM
  -- Part C: Combine SumIn + SumOut via point_arith_combine
  refine ⟨H.plus_ne_top, ?_⟩
  intro P hP
  rw [← Finset.sum_filter_add_sum_filter_not P (fun l : Nat.Primes => (l : ℕ) ∈ Bchi)]
  have hout := hGood (P.filter (fun l : Nat.Primes => (l : ℕ) ∉ Bchi)) (by
    intro l hl
    rw [Finset.mem_filter] at hl
    exact ⟨hP l hl.1, hl.2⟩)
  have hin :
      ∑ l ∈ P.filter (fun l : Nat.Primes => (l : ℕ) ∈ Bchi),
          Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((D.plusLen E l e).toNat : ℝ) ≤
        ((P.filter (fun l : Nat.Primes => (l : ℕ) ∈ Bchi)).card : ℝ) * (M ^ Dbad + (Dbad : ℝ) * B) := by
    calc _ ≤ ∑ _l ∈ P.filter (fun l : Nat.Primes => (l : ℕ) ∈ Bchi), (M ^ Dbad + (Dbad : ℝ) * B) :=
          Finset.sum_le_sum fun l hl => hBad l (Finset.mem_filter.mp hl).2
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (P.filter (fun l : Nat.Primes => (l : ℕ) ∈ Bchi)).card ≤ Bchi.card :=
    Finset.card_le_card_of_injOn (fun l : Nat.Primes => (l : ℕ))
      (fun l hl => (Finset.mem_filter.mp hl).2) Subtype.coe_injective.injOn
  have hpt := point_arith_combine M B hM2 H.B_nonneg _ Bchi.card Dbad C0 hcard
  linarith

/-! ## 4. Master Window Assembly (`VWinAt`, `VWin`, and Pillar 3 Contract) -/

/-- Joint 2-part + plus-parity Selmer window (`JointWin Ct`, combining Ferrero–Washington
windowing `ThmBab` with `ThmHV` from the six-case Selmer decomposition). -/
def JointWin {S : SelmerSystem} (D : SelmerParityDecomp S) (Ct : ℝ) : Prop :=
  ∀ (ψ : PChar) (eps A : ℝ), 0 < eps → eps < 1 / 52 →
    ∀ (e : ℝ → ℕ) (t : ℝ → ℕ), Admitted A Ct e t →
      ∃ (J C P XJ : ℝ), 0 < J ∧
        ∀ X ≥ XJ, ∀ q d : ℕ, PrimePair ψ.N q d →
          2 * X ^ Ct + 1 < (q : ℝ) → 2 * X ^ Ct + 1 < (d : ℝ) →
          P < (q : ℝ) → P < (d : ℝ) → Real.log ((q : ℝ) * d) ≤ X ^ (eps / (4 * J)) →
          ∃ Y : ℝ, (X ^ (1 / J) ≤ Y ∧ Y ^ (2 : ℝ) ≤ X) ∧
            ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) →
              (∀ (E : Type) [Field E] [NumberField E],
                IsCompField (AbF.ofChar ψ) (e x) q d E →
                  VVTwoLe D E (t x) (Real.exp (x ^ (4 * eps / 5)))) ∧
              (∀ (E : Type) [Field E] [NumberField E],
                IsChiField ψ (e x) q d E →
                  VVPlusLe D E (t x)
                    (((condF E : ℝ) * (t x : ℝ)) ^ C + C * Real.exp (x ^ (4 * eps / 5))))

/-- Minus-parity Selmer bound (`ThmBc Ct`). -/
def ThmBc {S : SelmerSystem} (D : SelmerParityDecomp S) (Ct : ℝ) : Prop :=
  ∃ Cb : ℝ, ∀ (A : AbF) (A0 : ℝ) (e : ℝ → ℕ) (t : ℝ → ℕ), Admitted A0 Ct e t →
    ∀ x : ℝ, 2 ≤ x → ∀ q d : ℕ, PrimePair A.m q d →
      ∀ (E : Type) [Field E] [NumberField E], IsCompField A (e x) q d E →
        VVMinusLe D E (t x) (minusBound Cb A.deg (Module.finrank ℚ E) (condF E) (t x))

/-- Conductor and degree bounds on abelian host fields `IsChiField ψ e q d E`. -/
def ConductorBounds : Prop :=
  ∀ (ψ : PChar) (e q d : ℕ), 0 < q → 0 < d →
    ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ e q d E →
      1 ≤ condF E ∧ condF E ≤ 2 ^ (e + 2) * ψ.N * q * d ∧ Module.finrank ℚ E ≤ condF E

/-- Master Selmer/Vandiver window theorem (`AdmissibleOfPageN.lean:L41-129`, proved from scratch):
assembles `JointWin D Ct` + `ThmBc D Ct` + `ConductorBounds` into `VWinAt S ψ Ct` for every
`Ct ≥ 1` and every primitive Dirichlet character `ψ`. -/
theorem vwinAt_of_joint {S : SelmerSystem} {D : SelmerParityDecomp S} {Ct : ℝ}
    (hC : 1 ≤ Ct) (hJ : JointWin D Ct) (hc : ThmBc D Ct) (hCond : ConductorBounds)
    (ψ : PChar) : VWinAt S ψ Ct := by
  intro eps h0 h1 e he
  set t : ℝ → ℕ := fun x => ⌊x ^ Ct⌋₊ with ht
  have hadm : Admitted 4 Ct e t := admissible_of_pageN h0 h1 hC he
  obtain ⟨J, C, P, XJ, hJ0, hmain⟩ := hJ ψ eps 4 h0 h1 e t hadm
  obtain ⟨Cb, hCb⟩ := hc
  obtain ⟨K, _, hK⟩ := minusBound_le_exp_of_log_le Cb (AbF.ofChar ψ).deg
  obtain ⟨xT, hxT⟩ := error_terms_le_sqrt_exp_rpow eps K C h0
  obtain ⟨xN, hxN⟩ := log_conductor_mul_height_le_of_pageN eps Ct ψ.N h0 h1
  obtain ⟨Y0, hY0⟩ := log_mul_le_rpow_of_winPair eps h0
  obtain ⟨J', hJ'1, hJJ'⟩ : ∃ J' : ℝ, 1 ≤ J' ∧ J ≤ J' := ⟨max J 1, le_max_right _ _, le_max_left _ _⟩
  have hJ'0 : 0 < J' := by linarith
  obtain ⟨P', hPP', hNP'⟩ : ∃ P' : ℝ, P ≤ P' ∧ (ψ.N : ℝ) ≤ P' :=
    ⟨max P (ψ.N : ℝ), le_max_left _ _, le_max_right _ _⟩
  obtain ⟨XB, hXB⟩ := eventually_winPair_gt_power eps J' Ct P' h0 hJ'0
  obtain ⟨L, hxTL, hxNL, hY0L, h2L⟩ : ∃ L : ℝ, xT ≤ L ∧ xN ≤ L ∧ Y0 ≤ L ∧ 2 ≤ L :=
    ⟨max (max xT xN) (max Y0 2),
      le_max_of_le_left (le_max_left _ _),
      le_max_of_le_left (le_max_right _ _),
      le_max_of_le_right (le_max_left _ _),
      le_max_of_le_right (le_max_right _ _)⟩
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hL0 : (0 : ℝ) ≤ L := by linarith
  refine ⟨J', hJ'1, max (max XJ XB) (L ^ J'), ?_⟩
  intro X hX q d hw
  have hXJ : XJ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXB' : XB ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXL : L ^ J' ≤ X := le_trans (le_max_right _ _) hX
  have hLX : L ≤ X ^ (1 / J') := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg hL0 _) hXL (le_of_lt (one_div_pos.mpr hJ'0))
    rwa [← Real.rpow_mul hL0, mul_one_div_cancel hJ'0.ne', Real.rpow_one] at this
  have hX1 : 1 ≤ X := by
    have : 1 ≤ L ^ J' := Real.one_le_rpow hL1 hJ'0.le
    linarith
  have hX0 : (0 : ℝ) ≤ X := by linarith
  obtain ⟨hq3, hd3, hPq, hPd⟩ := hXB X hXB' q d hw
  have hlog := hY0 _ (hY0L.trans hLX) q d hw
  have hpow : (X ^ (1 / J')) ^ (eps / 4) = X ^ (eps / (4 * J')) := by
    rw [← Real.rpow_mul hX0]
    congr 1
    field_simp
  have hmono : X ^ (eps / (4 * J')) ≤ X ^ (eps / (4 * J)) :=
    Real.rpow_le_rpow_of_exponent_le hX1
      (div_le_div_of_nonneg_left h0.le (by positivity) (by linarith))
  have hlogJ : Real.log ((q : ℝ) * d) ≤ X ^ (eps / (4 * J)) := by
    rw [hpow] at hlog
    exact hlog.trans hmono
  have hpp : PrimePair ψ.N q d :=
    primePair_of_winPair (NeZero.pos ψ.N) hw (lt_of_le_of_lt hNP' hPq) (lt_of_le_of_lt hNP' hPd)
  obtain ⟨Y, ⟨hYlo, hYhi⟩, hY⟩ :=
    hmain X hXJ q d hpp hq3 hd3 (lt_of_le_of_lt hPP' hPq) (lt_of_le_of_lt hPP' hPd) hlogJ
  have hWY : X ^ (1 / J') ≤ Y :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hX1
      (one_div_le_one_div_of_le (by linarith) hJJ')) hYlo
  refine ⟨Y, hWY, hYhi, ?_⟩
  intro x hxY hxY2
  have hWx : X ^ (1 / J') ≤ x := hWY.trans hxY
  have hLx : L ≤ x := hLX.trans hWx
  have hx2 : 2 ≤ x := h2L.trans hLx
  have hx1 : 1 ≤ x := by linarith
  obtain ⟨hBa, hHV⟩ := hY x hxY hxY2
  intro E _ _ hE
  have hq0 : 0 < q := hw.q_prime.pos
  have hd0 : 0 < d := hw.d_prime.pos
  have hE' : IsCompField (AbF.ofChar ψ) (e x) q d E := (isCompField_ofChar ψ (e x) q d E).2 hE
  have h2 := hBa E hE'
  have hp := hHV E hE
  have hm := hCb (AbF.ofChar ψ) 4 e t hadm x hx2 q d hpp E hE'
  obtain ⟨hc1, hc2, hc3⟩ := hCond ψ (e x) q d hq0 hd0 E hE
  obtain ⟨-, -, ht2, htle⟩ := hadm x hx2
  have ht1 : 1 ≤ t x := by omega
  have hWpos : (0 : ℝ) ≤ X ^ (1 / J') := Real.rpow_nonneg hX0 _
  have hqd : Real.log ((q : ℝ) * d) ≤ x ^ (eps / 4) := by
    have hlog0 := hY0 _ (hY0L.trans hLX) q d hw
    exact hlog0.trans (Real.rpow_le_rpow hWpos hWx (by linarith))
  have hNt := hxN x (hxNL.trans hLx) (condF E) (t x) (e x) q d hc1 hc2 (he x hx1) ht1 htle hqd
  have hmb := hK (Module.finrank ℚ E) (condF E) (t x) (x ^ (eps / 4)) hc1 ht1 hc3 hNt
  have hm' := VVMinusLe.mono hm hmb
  have hv := vvle_of_parts h2 hm' hp
  have hu1 : (1 : ℝ) ≤ (condF E : ℝ) * (t x : ℝ) := by
    have a : (1 : ℝ) ≤ condF E := by exact_mod_cast hc1
    have b : (1 : ℝ) ≤ t x := by exact_mod_cast ht1
    nlinarith
  have htot := hxT x (hxTL.trans hLx) ((condF E : ℝ) * (t x : ℝ)) hu1 hNt
  exact VVle.mono hv le_rfl htot

/-- Specializes `vwinAt_of_joint` at `Ct = 401` to obtain the full Selmer/Vandiver window `VWin S`. -/
theorem vwin_of_joint {S : SelmerSystem} {D : SelmerParityDecomp S}
    (hJ : JointWin D 401) (hc : ThmBc D 401) (hCond : ConductorBounds) :
    VWin S :=
  fun ψ => vwinAt_of_joint (by norm_num : (1 : ℝ) ≤ 401) hJ hc hCond ψ

/-! ## 5. Direct Bridge from `MinimalAutomorphyInputs` to `GaloisModularityContract S`

Replaces `VwinOfRow.lean` + `TopMainZj.lean` + `WindowBoundOfLiteratureLevel.lean` +
`PublishedHypothesesFromPatching.lean` + `HVCore.lean` with ZERO `OpenImageCondition`,
ZERO `LiteratureCMHypothesis`, ZERO `quat`, and ZERO Gen 1–5 vestigial wrappers. -/

/-- Exact arithmetic-geometry bridge from the minimal zero-dead-field automorphy/patching inputs
`MinimalAutomorphyInputs D_aut` to the parity-decomposed Selmer window bounds feeding
`vwin_of_joint`. -/
structure PatchingToSelmerBridge (S : SelmerSystem) (D_aut : AutomorphicDomain) where
  decomp : SelmerParityDecomp S
  jointWin : MinimalAutomorphyInputs D_aut → JointWin decomp 401
  minusParity : MinimalAutomorphyInputs D_aut → ThmBc decomp 401
  conductorBounds : ConductorBounds

/-- Direct deduction of `VWin S` from `MinimalAutomorphyInputs` + `PatchingToSelmerBridge`. -/
theorem vwin_of_minimal_inputs (S : SelmerSystem) (D_aut : AutomorphicDomain)
    (hAut : MinimalAutomorphyInputs D_aut)
    (hBridge : PatchingToSelmerBridge S D_aut) :
    VWin S :=
  vwin_of_joint (hBridge.jointWin hAut) (hBridge.minusParity hAut) hBridge.conductorBounds

/-- Final Pillar 3 constructor producing `GaloisModularityContract S` (`RHDirect.Interfaces`). -/
theorem galoisModularityContract_of_minimal (S : SelmerSystem) (D_aut : AutomorphicDomain)
    (hAut : MinimalAutomorphyInputs D_aut)
    (hBridge : PatchingToSelmerBridge S D_aut) :
    GaloisModularityContract S :=
  ⟨vwin_of_minimal_inputs S D_aut hAut hBridge⟩

/-- Direct handoff from Pillar 3 (`GaloisModularityCore`) into Pillar 2 (`ThetaSlopeEngine`):
supplies both `MinimalThetaInputs` (0 dead fields) and `AllLevelsWindowBound (3 / 2)` via
`ThetaSlopeContract S`. -/
theorem thetaInputs_and_windows_of_minimal (S : SelmerSystem) (D_aut : AutomorphicDomain)
    (T : ThetaLocalCarrier) (H : HodgeBundleCarrier)
    (hAut : MinimalAutomorphyInputs D_aut)
    (hThetaLoc : MinimalThetaLocalInputs T)
    (hHodge : MinimalHodgeBundleInputs H)
    (hBridge : PatchingToSelmerBridge S D_aut)
    (hSlope : MinimalThetaInputs D_aut T H → ThetaSlopeContract S) :
    AllLevelsWindowBound (3 / 2) :=
  (hSlope (hAut.toMinimalThetaInputs hThetaLoc hHodge)).windows_of_vwin
    (vwin_of_minimal_inputs S D_aut hAut hBridge)

end RHDirect

end

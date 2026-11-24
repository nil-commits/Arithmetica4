import RHDirect.Interfaces
import RHDirect.ZeroDensityWindow
import RHDirect.CosetWeights
import RHDirect.AnalyticBridge
import RHDirect.Stage2AnalyticWire
import RHDirect.Stage2BehrendSieve
import RHDirect.Stage2DirichletAP
import RHDirect.Stage3BombieriVinogradov
import RHDirect.Stage8BarbanDavenport

/-!
# RHDirect.Stage11SecondMomentFrame

Unconditional (`0` `sorry`, `0` custom `axiom`, `0` warnings, `0` info) direct **Second-Moment
Parseval / Character-Box Averaging Replacement** for the 10,849-line Behrend 3-AP sphere /
Frobenius-orbit layer (Pillar 1 Direct Upgrade, `FROM_SCRATCH_ROADMAP.md` §2.2 / `remark.pdf` fn. 7),
built directly on Mathlib `v4.33.1`, `RHDirect.AnalyticBridge`, `RHDirect.Stage2AnalyticWire`,
`RHDirect.Stage2BehrendSieve`, `RHDirect.Stage3BombieriVinogradov`, and
`RHDirect.Stage8BarbanDavenport`.

## Main Contents
1. **Exact Finite Abelian Plancherel / Parseval Identity & Exceptional-Character Count (`0` Assumptions)**:
   - `dirichlet_plancherel_units` & `dirichlet_parseval_units`: exact Plancherel/Parseval identity
     `∑ χ : DirichletCharacter ℂ q, ‖∑ a : (ZMod q)ˣ, f a * χ (a : ZMod q)‖ ^ 2 = q.totient * ∑ a, ‖f a‖ ^ 2`.
   - `dirichlet_parseval_units_nonprincipal`: exact centered variance Parseval identity on `(ZMod q)ˣ`.
   - `exceptional_char_count_le_parseval` & `good_char_share_of_parseval`: exact second-moment
     exceptional-character bound `≤ (q.totient / V ^ 2) * ∑ a, ‖f a‖ ^ 2`.
   - `dirichlet_parseval_prod_units` & `dirichlet_parseval_prod_synthesis`: exact Parseval identities
     on product unit groups `(ZMod q)ˣ × (ZMod d)ˣ`.
   - `addChar_orthogonality_group`, `addChar_orthogonality_dual`, `addChar_parseval_analysis`,
     `addChar_parseval_synthesis`, and `addChar_parseval_synthesis_erase`: exact finite abelian
     Parseval on any finite abelian group `G`.
2. **Concrete Prime-Residue Thick-Frame Existence Without Behrend 3-AP Spheres**:
   - `exists_dense_good_coset_frame` & `exists_dense_good_coset_frame_prod`: for ANY finite abelian
     group `G` (and concretely `(ZMod q)ˣ × (ZMod d)ˣ`), ANY target character `ψ`, ANY second-moment
     bound `∑_{χ ≠ ψ} ‖E χ‖² ≤ B`, and EVERY `δ ∈ (0, 1)`, at least `(1 - δ) |G|` elements have
     simultaneous normalized error `≤ √(B / (δ |G|))` (constant density `≥ 1 - δ`, zero 3-AP spheres).
   - `cosetFrame_fourier_clear_level_Gm_of_secondMoment` & `dense_frame_coset_slice_lower_bound`:
     direct bridge into `AnalyticBridge`'s `(3o + 1)` weight clearing and `Stage2AnalyticWire`.
   - `secondMoment_replaces_behrend_density`, `secondMoment_replaces_behrend_density_stage2`, and
     `secondMoment_replaces_behrend_density_tendsto`: explicit proof that our Parseval frame
     strictly dominates `Stage2BehrendSieve`'s `exp(-c √(log N))` density for all `N ≥ 2`.
3. **Concrete Twisted Character-Box Zero-Free & Mean-Square Transfer**:
   - `twistedChar`, `twistedChar_injective`, `twistedChar_ne_one_of_ne_one_right`,
     `twistedChar_ne_one_of_ne_one_left`, and `twisted_char_mean_square_le_psiAPVariance`.
   - `cesaroWindowPsiChar` & `bdh_twisted_primes_mean_square_le`: unconditional Barban–Davenport–
     Halberstam mean-square bounds across auxiliary primes `q ≤ Q` (`¬ q ∣ ψ.N`) for all twisted
     characters `ψ χ_q`.
   - `twisted_box_mean_square_transfer` & `twisted_box_zero_free_and_mean_square_transfer`:
     unconditional almost-all-auxiliary-primes simultaneous Chebyshev & Cesàro-1 mean-square transfer
     and zero-free box coupling feeding Pillar 1's `MeanSquareBounds`.
-/

noncomputable section

open Complex DirichletCharacter Finset Filter Topology RHDirect
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace RHDirect
namespace Stage11SecondMomentFrame

/-! ## Section 1: Exact Finite Abelian Parseval Identity & Character-Box Second Moment -/

private lemma norm_sum_sq_eq_re_local {α : Type*} (s : Finset α) (f : α → ℂ) :
    ‖∑ x ∈ s, f x‖ ^ 2 = (∑ x ∈ s, ∑ y ∈ s, f x * starRingEnd ℂ (f y)).re := by
  set z : ℂ := ∑ x ∈ s, f x
  rw [show ‖z‖ ^ 2 = (z * starRingEnd ℂ z).re by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]]
  congr 1
  simp only [z, map_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

/-- **Exact Plancherel Inner-Product Identity on `(ZMod q)ˣ`** (`0` assumptions):
for any `q ≥ 1` and any complex weights `f, g : (ZMod q)ˣ → ℂ`,
`∑_{χ mod q} (∑_a f(a) χ(a)) * conj(∑_b g(b) χ(b)) = φ(q) * ∑_a f(a) * conj(g(a))`. -/
theorem dirichlet_plancherel_units {q : ℕ} [NeZero q] (f g : (ZMod q)ˣ → ℂ) :
    ∑ χ : DirichletCharacter ℂ q,
        (∑ a : (ZMod q)ˣ, f a * χ (a : ZMod q)) *
          starRingEnd ℂ (∑ b : (ZMod q)ˣ, g b * χ (b : ZMod q)) =
      (q.totient : ℂ) * ∑ a : (ZMod q)ˣ, f a * starRingEnd ℂ (g a) := by
  have hexp :
      ∑ χ : DirichletCharacter ℂ q,
          (∑ a : (ZMod q)ˣ, f a * χ (a : ZMod q)) *
            starRingEnd ℂ (∑ b : (ZMod q)ˣ, g b * χ (b : ZMod q)) =
        ∑ χ : DirichletCharacter ℂ q,
          ∑ a : (ZMod q)ˣ, ∑ b : (ZMod q)ˣ,
            f a * starRingEnd ℂ (g b) * (χ (a : ZMod q) * starRingEnd ℂ (χ (b : ZMod q))) := by
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul]
    ring
  rw [hexp, Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  have hinner : ∀ b : (ZMod q)ˣ,
      ∑ χ : DirichletCharacter ℂ q,
          f a * starRingEnd ℂ (g b) * (χ (a : ZMod q) * starRingEnd ℂ (χ (b : ZMod q))) =
        if a = b then (q.totient : ℂ) * (f a * starRingEnd ℂ (g a)) else 0 := by
    intro b
    rw [← Finset.mul_sum, Stage2BehrendSieve.dirichlet_orthogonality_conj (a : ZMod q) (b : ZMod q)]
    by_cases hab : a = b
    · subst hab
      rw [if_pos ⟨a.isUnit, rfl⟩, if_pos rfl]
      ring
    · have hval : (a : ZMod q) ≠ (b : ZMod q) := fun h => hab (Units.ext h)
      rw [if_neg (fun h => hval h.2), if_neg hab, mul_zero]
  rw [Finset.sum_congr rfl fun b _ => hinner b, Finset.sum_ite_eq Finset.univ a,
    if_pos (Finset.mem_univ a)]

/-- **Exact Plancherel / Parseval Identity on `(ZMod q)ˣ`** (`0` assumptions):
for any `q ≥ 1` and any complex weight `f : (ZMod q)ˣ → ℂ`,
`∑ χ : DirichletCharacter ℂ q, ‖∑ a : (ZMod q)ˣ, f a * χ (a : ZMod q)‖ ^ 2 = q.totient * ∑ a : (ZMod q)ˣ, ‖f a‖ ^ 2`. -/
theorem dirichlet_parseval_units {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ a : (ZMod q)ˣ, f a * χ (a : ZMod q)‖ ^ 2 =
      (q.totient : ℝ) * ∑ a : (ZMod q)ˣ, ‖f a‖ ^ 2 := by
  have hre :
      ∑ χ : DirichletCharacter ℂ q, ‖∑ a : (ZMod q)ˣ, f a * χ (a : ZMod q)‖ ^ 2 =
        (∑ χ : DirichletCharacter ℂ q,
          (∑ a : (ZMod q)ˣ, f a * χ (a : ZMod q)) *
            starRingEnd ℂ (∑ b : (ZMod q)ˣ, f b * χ (b : ZMod q))).re := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [hre, dirichlet_plancherel_units f f]
  have hrhs :
      ((q.totient : ℂ) * ∑ a : (ZMod q)ˣ, f a * starRingEnd ℂ (f a)).re =
        (q.totient : ℝ) * ∑ a : (ZMod q)ˣ, ‖f a‖ ^ 2 := by
    rw [show (q.totient : ℂ) = ((q.totient : ℝ) : ℂ) by norm_cast, Complex.re_ofReal_mul,
      Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  exact hrhs

open Classical in
/-- **Exact Centered Non-Principal Parseval Variance Identity on `(ZMod q)ˣ`**:
subtracting the average `μ = (∑ b, f b) / φ(q)` equals the non-principal character second moment. -/
theorem dirichlet_parseval_units_nonprincipal {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℂ) :
    ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        ‖∑ a : (ZMod q)ˣ, f a * χ (a : ZMod q)‖ ^ 2 =
      (q.totient : ℝ) *
        ∑ a : (ZMod q)ˣ, ‖f a - (∑ b : (ZMod q)ˣ, f b) / (q.totient : ℂ)‖ ^ 2 := by
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hphi_ne : (q.totient : ℂ) ≠ 0 := by exact_mod_cast hphi_pos.ne'
  set μ : ℂ := (∑ b : (ZMod q)ˣ, f b) / (q.totient : ℂ)
  have hfull := dirichlet_parseval_units (q := q) (fun a => f a - μ)
  have h1_sum : ∑ a : (ZMod q)ˣ, (f a - μ) * (1 : DirichletCharacter ℂ q) (a : ZMod q) = 0 := by
    have hones : ∀ a : (ZMod q)ˣ, (1 : DirichletCharacter ℂ q) (a : ZMod q) = 1 :=
      fun a => MulChar.one_apply a.isUnit
    simp_rw [hones, mul_one, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      ZMod.card_units_eq_totient, nsmul_eq_mul]
    dsimp only [μ]
    rw [mul_div_cancel₀ _ hphi_ne, sub_self]
  have hnt_sum : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      ∑ a : (ZMod q)ˣ, (f a - μ) * χ (a : ZMod q) = ∑ a : (ZMod q)ˣ, f a * χ (a : ZMod q) := by
    intro χ hχ
    have hχne : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
    have horth : ∑ a : (ZMod q)ˣ, χ (a : ZMod q) = 0 := by
      have htot := MulChar.sum_eq_zero_of_ne_one hχne
      have hsplit : ∑ a : (ZMod q)ˣ, χ (a : ZMod q) = ∑ x : ZMod q, χ x := by
        rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (ZMod q)))
          (p := fun x : ZMod q => IsUnit x)]
        have hnon : ∑ x ∈ Finset.univ.filter (fun x : ZMod q => ¬ IsUnit x), χ x = 0 :=
          Finset.sum_eq_zero fun x hx => MulChar.map_nonunit _ (Finset.mem_filter.mp hx).2
        rw [hnon, add_zero]
        refine Finset.sum_bij (fun a _ => (a : ZMod q))
          (fun a _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.isUnit⟩)
          (fun _ _ _ _ heq => Units.ext heq)
          (fun x hx => ⟨(Finset.mem_filter.mp hx).2.unit, Finset.mem_univ _, (Finset.mem_filter.mp hx).2.unit_spec⟩)
          (fun _ _ => rfl)
      rw [hsplit, htot]
    simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, horth, mul_zero, sub_zero]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : DirichletCharacter ℂ q)),
    h1_sum, norm_zero, zero_pow two_ne_zero, zero_add] at hfull
  rw [← hfull]
  exact Finset.sum_congr rfl fun χ hχ => by rw [hnt_sum χ hχ]

open Classical in
/-- **Second-Moment Exceptional-Character Count (`exceptional_char_count_le_parseval`)** (`0` assumptions):
for ANY `q ≥ 1`, ANY complex weight `f : (ZMod q)ˣ → ℂ`, and ANY threshold `V > 0`, the number of
characters `χ mod q` with `‖∑ a : (ZMod q)ˣ, f a * χ a‖ ≥ V` is at most
`(q.totient / V ^ 2) * ∑ a : (ZMod q)ˣ, ‖f a‖ ^ 2`. -/
theorem exceptional_char_count_le_parseval {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℂ)
    {V : ℝ} (hV : 0 < V) :
    ((Finset.univ.filter (fun χ : DirichletCharacter ℂ q =>
        V ≤ ‖∑ a : (ZMod q)ˣ, f a * χ (a : ZMod q)‖)).card : ℝ) ≤
      ((q.totient : ℝ) / V ^ 2) * ∑ a : (ZMod q)ˣ, ‖f a‖ ^ 2 := by
  set B := Finset.univ.filter (fun χ : DirichletCharacter ℂ q =>
    V ≤ ‖∑ a : (ZMod q)ˣ, f a * χ (a : ZMod q)‖)
  have h1 : (B.card : ℝ) * V ^ 2 ≤
      ∑ χ ∈ B, ‖∑ a : (ZMod q)ˣ, f a * χ (a : ZMod q)‖ ^ 2 := by
    calc (B.card : ℝ) * V ^ 2
        = ∑ _χ ∈ B, V ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ χ ∈ B, ‖∑ a : (ZMod q)ˣ, f a * χ (a : ZMod q)‖ ^ 2 :=
          Finset.sum_le_sum fun χ hχ =>
            pow_le_pow_left₀ hV.le (Finset.mem_filter.mp hχ).2 2
  have h2 : ∑ χ ∈ B, ‖∑ a : (ZMod q)ˣ, f a * χ (a : ZMod q)‖ ^ 2 ≤
      (q.totient : ℝ) * ∑ a : (ZMod q)ˣ, ‖f a‖ ^ 2 := by
    rw [← dirichlet_parseval_units f]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _
  rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hV)]
  exact h1.trans h2

/-- Subset form of `exceptional_char_count_le_parseval`: any `B : Finset (DirichletCharacter ℂ q)`
whose elements satisfy `V ≤ ‖∑ a, f a * χ a‖` obeys `|B| ≤ (φ(q) / V²) ∑ ‖f a‖²`. -/
theorem exceptional_char_subset_card_le_parseval {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℂ)
    (B : Finset (DirichletCharacter ℂ q)) {V : ℝ} (hV : 0 < V)
    (hB : ∀ χ ∈ B, V ≤ ‖∑ a : (ZMod q)ˣ, f a * χ (a : ZMod q)‖) :
    (B.card : ℝ) ≤ ((q.totient : ℝ) / V ^ 2) * ∑ a : (ZMod q)ˣ, ‖f a‖ ^ 2 := by
  classical
  have hsub : B ⊆ Finset.univ.filter (fun χ : DirichletCharacter ℂ q =>
      V ≤ ‖∑ a : (ZMod q)ˣ, f a * χ (a : ZMod q)‖) := fun χ hχ =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ χ, hB χ hχ⟩
  exact (by exact_mod_cast Finset.card_le_card hsub : (B.card : ℝ) ≤ _).trans
    (exceptional_char_count_le_parseval f hV)

/-- **Dense Good-Character Share via Exact Parseval**:
for every `q ≥ 1`, `f : (ZMod q)ˣ → ℂ`, and `δ ∈ (0, 1)`, at least `(1 - δ) * φ(q)` characters
`χ mod q` satisfy `‖∑ a, f a * χ a‖ ≤ √((1 / δ) * ∑ a, ‖f a‖²)`. -/
theorem good_char_share_of_parseval {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℂ)
    {δ : ℝ} (hδ0 : 0 < δ) :
    ∃ G : Finset (DirichletCharacter ℂ q),
      (1 - δ) * (q.totient : ℝ) ≤ (G.card : ℝ) ∧
      ∀ χ ∈ G, ‖∑ a : (ZMod q)ˣ, f a * χ (a : ZMod q)‖ ≤
        Real.sqrt ((1 / δ) * ∑ a : (ZMod q)ˣ, ‖f a‖ ^ 2) := by
  classical
  set E : ℝ := ∑ a : (ZMod q)ˣ, ‖f a‖ ^ 2
  have hE_nn : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcard_univ : ((Finset.univ : Finset (DirichletCharacter ℂ q)).card : ℝ) = (q.totient : ℝ) := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  by_cases hE0 : E = 0
  · refine ⟨Finset.univ, ?_, fun χ _ => ?_⟩
    · rw [hcard_univ]
      nlinarith [Nat.cast_nonneg (α := ℝ) q.totient]
    · have hsum0 : ∑ χ' : DirichletCharacter ℂ q, ‖∑ a : (ZMod q)ˣ, f a * χ' (a : ZMod q)‖ ^ 2 = 0 := by
        rw [dirichlet_parseval_units f]
        change (q.totient : ℝ) * E = 0
        rw [hE0, mul_zero]
      have hterm0 : ‖∑ a : (ZMod q)ˣ, f a * χ (a : ZMod q)‖ ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hsum0 χ (Finset.mem_univ χ)
      rw [sq_eq_zero_iff.mp hterm0]
      exact Real.sqrt_nonneg _
  · have hE_pos : 0 < E := lt_of_le_of_ne hE_nn (Ne.symm hE0)
    set T : ℝ := Real.sqrt ((1 / δ) * E)
    have hT_pos : 0 < T := Real.sqrt_pos.mpr (by positivity)
    have hT_sq : T ^ 2 = (1 / δ) * E := Real.sq_sqrt (by positivity)
    set Bad := Finset.univ.filter (fun χ : DirichletCharacter ℂ q =>
      T < ‖∑ a : (ZMod q)ˣ, f a * χ (a : ZMod q)‖)
    set Good := Finset.univ.filter (fun χ : DirichletCharacter ℂ q =>
      ‖∑ a : (ZMod q)ˣ, f a * χ (a : ZMod q)‖ ≤ T)
    have hBad_le : (Bad.card : ℝ) ≤ δ * (q.totient : ℝ) := by
      have h1 : (Bad.card : ℝ) * T ^ 2 ≤ (q.totient : ℝ) * E := by
        calc (Bad.card : ℝ) * T ^ 2
            = ∑ _χ ∈ Bad, T ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ χ ∈ Bad, ‖∑ a : (ZMod q)ˣ, f a * χ (a : ZMod q)‖ ^ 2 :=
              Finset.sum_le_sum fun χ hχ =>
                pow_le_pow_left₀ hT_pos.le (Finset.mem_filter.mp hχ).2.le 2
          _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖∑ a : (ZMod q)ˣ, f a * χ (a : ZMod q)‖ ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _
          _ = (q.totient : ℝ) * E := dirichlet_parseval_units f
      rw [hT_sq] at h1
      have h2 : (Bad.card : ℝ) * ((1 / δ) * E) ≤ (δ * (q.totient : ℝ)) * ((1 / δ) * E) := by
        calc (Bad.card : ℝ) * ((1 / δ) * E) ≤ (q.totient : ℝ) * E := h1
          _ = (δ * (q.totient : ℝ)) * ((1 / δ) * E) := by field_simp [hδ0.ne']
      exact le_of_mul_le_mul_right h2 (by positivity)
    have hpart : (Good.card : ℝ) + (Bad.card : ℝ) = (q.totient : ℝ) := by
      have hnat : Good.card + Bad.card = (Finset.univ : Finset (DirichletCharacter ℂ q)).card := by
        have hBad_eq : Bad = Finset.univ.filter (fun χ : DirichletCharacter ℂ q =>
            ¬ ‖∑ a : (ZMod q)ˣ, f a * χ (a : ZMod q)‖ ≤ T) := by
          ext χ; simp only [Bad, Finset.mem_filter, not_le]
        rw [hBad_eq]
        exact Finset.card_filter_add_card_filter_not _
      rw [← hcard_univ]
      exact_mod_cast hnat
    exact ⟨Good, by linarith, fun χ hχ => (Finset.mem_filter.mp hχ).2⟩

/-! ### Exact Parseval on Product Unit Groups `(ZMod q)ˣ × (ZMod d)ˣ` -/

/-- Conjugate orthogonality on the product unit group `(ZMod q)ˣ × (ZMod d)ˣ`. -/
theorem dirichlet_orthogonality_prod_units {q d : ℕ} [NeZero q] [NeZero d]
    (u v : (ZMod q)ˣ × (ZMod d)ˣ) :
    ∑ p : DirichletCharacter ℂ q × DirichletCharacter ℂ d,
        (p.1 (u.1 : ZMod q) * p.2 (u.2 : ZMod d)) *
          starRingEnd ℂ (p.1 (v.1 : ZMod q) * p.2 (v.2 : ZMod d)) =
      if u = v then ((q.totient * d.totient : ℕ) : ℂ) else 0 := by
  rw [Fintype.sum_prod_type]
  have hfac :
      ∑ χ₁ : DirichletCharacter ℂ q, ∑ χ₂ : DirichletCharacter ℂ d,
          (χ₁ (u.1 : ZMod q) * χ₂ (u.2 : ZMod d)) *
            starRingEnd ℂ (χ₁ (v.1 : ZMod q) * χ₂ (v.2 : ZMod d)) =
        (∑ χ₁ : DirichletCharacter ℂ q, χ₁ (u.1 : ZMod q) * starRingEnd ℂ (χ₁ (v.1 : ZMod q))) *
        (∑ χ₂ : DirichletCharacter ℂ d, χ₂ (u.2 : ZMod d) * starRingEnd ℂ (χ₂ (v.2 : ZMod d))) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun χ₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ₂ _ => ?_
    rw [map_mul]
    ring
  rw [hfac, Stage2BehrendSieve.dirichlet_orthogonality_conj (u.1 : ZMod q) (v.1 : ZMod q),
    Stage2BehrendSieve.dirichlet_orthogonality_conj (u.2 : ZMod d) (v.2 : ZMod d)]
  by_cases huv : u = v
  · subst huv
    rw [if_pos ⟨u.1.isUnit, rfl⟩, if_pos ⟨u.2.isUnit, rfl⟩, if_pos rfl, Nat.cast_mul]
  · rw [if_neg huv]
    by_cases h1 : u.1 = v.1
    · have h2 : u.2 ≠ v.2 := fun h2 => huv (Prod.ext h1 h2)
      have h2v : (u.2 : ZMod d) ≠ (v.2 : ZMod d) := fun h => h2 (Units.ext h)
      rw [if_pos ⟨u.1.isUnit, congrArg Units.val h1⟩, if_neg (fun h => h2v h.2), mul_zero]
    · have h1v : (u.1 : ZMod q) ≠ (v.1 : ZMod q) := fun h => h1 (Units.ext h)
      rw [if_neg (fun h => h1v h.2), zero_mul]

open Classical in
/-- Dual character orthogonality over `(ZMod q)ˣ`:
`∑_{a ∈ (ZMod q)ˣ} χ₁(a) * conj(χ₂(a)) = if χ₁ = χ₂ then φ(q) else 0`. -/
theorem dirichlet_orthogonality_chars_units {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) :
    ∑ a : (ZMod q)ˣ, χ₁ (a : ZMod q) * starRingEnd ℂ (χ₂ (a : ZMod q)) =
      if χ₁ = χ₂ then (q.totient : ℂ) else 0 := by
  have hconj : ∀ a : (ZMod q)ˣ,
      χ₁ (a : ZMod q) * starRingEnd ℂ (χ₂ (a : ZMod q)) = (χ₁ * χ₂⁻¹) (a : ZMod q) := by
    intro a
    rw [MulChar.mul_apply]
    congr 1
    have h1 : χ₂ (a : ZMod q) * starRingEnd ℂ (χ₂ (a : ZMod q)) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq,
        (Stage2BehrendSieve.dirichlet_norm_eq_one_and_conj χ₂ a.isUnit).1]
      norm_num
    have h2 : χ₂ (a : ZMod q) * χ₂⁻¹ (a : ZMod q) = 1 := by
      rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply a.isUnit]
    have hne : χ₂ (a : ZMod q) ≠ 0 := fun h0 => zero_ne_one (by rw [h0, zero_mul] at h1; exact h1)
    exact mul_left_cancel₀ hne (h1.trans h2.symm)
  rw [Finset.sum_congr rfl fun a _ => hconj a]
  by_cases h : χ₁ = χ₂
  · subst h
    rw [if_pos rfl, mul_inv_cancel]
    have h1 : ∀ a : (ZMod q)ˣ, (1 : DirichletCharacter ℂ q) (a : ZMod q) = 1 :=
      fun a => MulChar.one_apply a.isUnit
    rw [Finset.sum_congr rfl fun a _ => h1 a, Finset.sum_const, Finset.card_univ,
      ZMod.card_units_eq_totient, nsmul_eq_mul, mul_one]
  · rw [if_neg h]
    have hne : χ₁ * χ₂⁻¹ ≠ 1 := fun h1 => h (eq_of_mul_inv_eq_one h1)
    have hsumZ : ∑ x : ZMod q, (χ₁ * χ₂⁻¹) x = 0 := MulChar.sum_eq_zero_of_ne_one hne
    have hEq : ∑ a : (ZMod q)ˣ, (χ₁ * χ₂⁻¹) (a : ZMod q) = ∑ x : ZMod q, (χ₁ * χ₂⁻¹) x := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (ZMod q)))
        (p := fun x : ZMod q => IsUnit x)]
      have hnon : ∑ x ∈ Finset.univ.filter (fun x : ZMod q => ¬ IsUnit x), (χ₁ * χ₂⁻¹) x = 0 :=
        Finset.sum_eq_zero fun x hx => MulChar.map_nonunit _ (Finset.mem_filter.mp hx).2
      rw [hnon, add_zero]
      refine Finset.sum_bij (fun a _ => (a : ZMod q))
        (fun a _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.isUnit⟩)
        (fun _ _ _ _ heq => Units.ext heq)
        (fun x hx => ⟨(Finset.mem_filter.mp hx).2.unit, Finset.mem_univ _, (Finset.mem_filter.mp hx).2.unit_spec⟩)
        (fun _ _ => rfl)
    rw [hEq, hsumZ]

/-- **Exact Parseval Identity on `(ZMod q)ˣ × (ZMod d)ˣ` (Analysis Form)**. -/
theorem dirichlet_parseval_prod_units {q d : ℕ} [NeZero q] [NeZero d]
    (f : (ZMod q)ˣ × (ZMod d)ˣ → ℂ) :
    ∑ p : DirichletCharacter ℂ q × DirichletCharacter ℂ d,
        ‖∑ u : (ZMod q)ˣ × (ZMod d)ˣ, f u * (p.1 (u.1 : ZMod q) * p.2 (u.2 : ZMod d))‖ ^ 2 =
      ((q.totient * d.totient : ℕ) : ℝ) * ∑ u : (ZMod q)ˣ × (ZMod d)ˣ, ‖f u‖ ^ 2 := by
  simp_rw [norm_sum_sq_eq_re_local]
  rw [← Complex.re_sum]
  have hswap :
      ∑ p : DirichletCharacter ℂ q × DirichletCharacter ℂ d,
          ∑ u : (ZMod q)ˣ × (ZMod d)ˣ, ∑ v : (ZMod q)ˣ × (ZMod d)ˣ,
            f u * (p.1 (u.1 : ZMod q) * p.2 (u.2 : ZMod d)) *
              starRingEnd ℂ (f v * (p.1 (v.1 : ZMod q) * p.2 (v.2 : ZMod d))) =
        ((q.totient * d.totient : ℕ) : ℂ) * ∑ u : (ZMod q)ˣ × (ZMod d)ˣ, f u * starRingEnd ℂ (f u) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    have hinner : ∀ v : (ZMod q)ˣ × (ZMod d)ˣ,
        ∑ p : DirichletCharacter ℂ q × DirichletCharacter ℂ d,
            f u * (p.1 (u.1 : ZMod q) * p.2 (u.2 : ZMod d)) *
              starRingEnd ℂ (f v * (p.1 (v.1 : ZMod q) * p.2 (v.2 : ZMod d))) =
          if u = v then ((q.totient * d.totient : ℕ) : ℂ) * (f u * starRingEnd ℂ (f u)) else 0 := by
      intro v
      have hpull :
          ∑ p : DirichletCharacter ℂ q × DirichletCharacter ℂ d,
              f u * (p.1 (u.1 : ZMod q) * p.2 (u.2 : ZMod d)) *
                starRingEnd ℂ (f v * (p.1 (v.1 : ZMod q) * p.2 (v.2 : ZMod d))) =
            f u * starRingEnd ℂ (f v) *
              ∑ p : DirichletCharacter ℂ q × DirichletCharacter ℂ d,
                (p.1 (u.1 : ZMod q) * p.2 (u.2 : ZMod d)) *
                  starRingEnd ℂ (p.1 (v.1 : ZMod q) * p.2 (v.2 : ZMod d)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [map_mul]; ring
      rw [hpull, dirichlet_orthogonality_prod_units u v]
      split_ifs with huv
      · subst huv; ring
      · ring
    rw [Finset.sum_congr rfl fun v _ => hinner v, Finset.sum_ite_eq Finset.univ u,
      if_pos (Finset.mem_univ u)]
  rw [hswap, show ((q.totient * d.totient : ℕ) : ℂ) = (((q.totient * d.totient : ℕ) : ℝ) : ℂ) by norm_cast,
    Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- **Exact Parseval Synthesis Identity on `(ZMod q)ˣ × (ZMod d)ˣ`**:
`∑_{u ∈ (ZMod q)ˣ × (ZMod d)ˣ} ‖∑_{p} E(p) p(u)‖² = φ(q) φ(d) ∑_p ‖E(p)‖²`. -/
theorem dirichlet_parseval_prod_synthesis {q d : ℕ} [NeZero q] [NeZero d]
    (E : DirichletCharacter ℂ q × DirichletCharacter ℂ d → ℂ) :
    ∑ u : (ZMod q)ˣ × (ZMod d)ˣ,
        ‖∑ p : DirichletCharacter ℂ q × DirichletCharacter ℂ d,
          E p * (p.1 (u.1 : ZMod q) * p.2 (u.2 : ZMod d))‖ ^ 2 =
      ((q.totient * d.totient : ℕ) : ℝ) *
        ∑ p : DirichletCharacter ℂ q × DirichletCharacter ℂ d, ‖E p‖ ^ 2 := by
  classical
  simp_rw [norm_sum_sq_eq_re_local]
  rw [← Complex.re_sum]
  have hswap :
      ∑ u : (ZMod q)ˣ × (ZMod d)ˣ,
          ∑ p₁ : DirichletCharacter ℂ q × DirichletCharacter ℂ d,
          ∑ p₂ : DirichletCharacter ℂ q × DirichletCharacter ℂ d,
            E p₁ * (p₁.1 (u.1 : ZMod q) * p₁.2 (u.2 : ZMod d)) *
              starRingEnd ℂ (E p₂ * (p₂.1 (u.1 : ZMod q) * p₂.2 (u.2 : ZMod d))) =
        ((q.totient * d.totient : ℕ) : ℂ) *
          ∑ p : DirichletCharacter ℂ q × DirichletCharacter ℂ d, E p * starRingEnd ℂ (E p) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p₁ _ => ?_
    rw [Finset.sum_comm]
    have hinner : ∀ p₂ : DirichletCharacter ℂ q × DirichletCharacter ℂ d,
        ∑ u : (ZMod q)ˣ × (ZMod d)ˣ,
            E p₁ * (p₁.1 (u.1 : ZMod q) * p₁.2 (u.2 : ZMod d)) *
              starRingEnd ℂ (E p₂ * (p₂.1 (u.1 : ZMod q) * p₂.2 (u.2 : ZMod d))) =
          if p₁ = p₂ then ((q.totient * d.totient : ℕ) : ℂ) * (E p₁ * starRingEnd ℂ (E p₁)) else 0 := by
      intro p₂
      have hpull :
          ∑ u : (ZMod q)ˣ × (ZMod d)ˣ,
              E p₁ * (p₁.1 (u.1 : ZMod q) * p₁.2 (u.2 : ZMod d)) *
                starRingEnd ℂ (E p₂ * (p₂.1 (u.1 : ZMod q) * p₂.2 (u.2 : ZMod d))) =
            E p₁ * starRingEnd ℂ (E p₂) *
              ((∑ a : (ZMod q)ˣ, p₁.1 (a : ZMod q) * starRingEnd ℂ (p₂.1 (a : ZMod q))) *
               (∑ b : (ZMod d)ˣ, p₁.2 (b : ZMod d) * starRingEnd ℂ (p₂.2 (b : ZMod d)))) := by
        rw [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [map_mul, map_mul]; ring
      rw [hpull, dirichlet_orthogonality_chars_units p₁.1 p₂.1,
        dirichlet_orthogonality_chars_units p₁.2 p₂.2]
      by_cases hp : p₁ = p₂
      · subst hp; rw [if_pos rfl, if_pos rfl, if_pos rfl, Nat.cast_mul]; ring
      · rw [if_neg hp]
        by_cases h1 : p₁.1 = p₂.1
        · have h2 : p₁.2 ≠ p₂.2 := fun h2 => hp (Prod.ext h1 h2)
          rw [if_neg h2, mul_zero, mul_zero]
        · rw [if_neg h1, zero_mul, mul_zero]
    rw [Finset.sum_congr rfl fun p₂ _ => hinner p₂, Finset.sum_ite_eq Finset.univ p₁,
      if_pos (Finset.mem_univ p₁)]
  rw [hswap, show ((q.totient * d.totient : ℕ) : ℂ) = (((q.totient * d.totient : ℕ) : ℝ) : ℂ) by norm_cast,
    Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-! ### General Finite Abelian Group `G` (`AddChar G ℂ`) Orthogonality & Parseval -/

/-- Complex conjugation of an additive character equals evaluation at the additive inverse. -/
theorem addChar_conj_eq_neg {G : Type*} [AddCommGroup G] [Fintype G]
    (θ : AddChar G ℂ) (x : G) :
    starRingEnd ℂ (θ x) = θ (-x) := by
  have h1 : θ x * starRingEnd ℂ (θ x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, addChar_norm_eq_one θ x]
    norm_num
  have h2 : θ x * θ (-x) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hne : θ x ≠ 0 := fun h0 => zero_ne_one (by rw [h0, zero_mul] at h1; exact h1)
  exact mul_left_cancel₀ hne (h1.trans h2.symm)

/-- Character orthogonality on any finite abelian group `G`:
`∑_{g : G} θ₁(g) * conj(θ₂(g)) = if θ₁ = θ₂ then |G| else 0`. -/
theorem addChar_orthogonality_group {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (θ₁ θ₂ : AddChar G ℂ) :
    ∑ g : G, θ₁ g * starRingEnd ℂ (θ₂ g) =
      if θ₁ = θ₂ then (Fintype.card G : ℂ) else 0 := by
  have hterm : ∀ g : G, θ₁ g * starRingEnd ℂ (θ₂ g) = (θ₁ - θ₂) g := by
    intro g
    rw [addChar_conj_eq_neg, sub_eq_add_neg, AddChar.add_apply, AddChar.neg_apply,
      AddChar.map_neg_eq_inv]
  rw [Finset.sum_congr rfl fun g _ => hterm g]
  by_cases h : θ₁ = θ₂
  · subst h
    rw [sub_self, if_pos rfl]
    have h0 : ∀ g : G, (0 : AddChar G ℂ) g = 1 := fun g => AddChar.zero_apply g
    rw [Finset.sum_congr rfl fun g _ => h0 g, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  · rw [if_neg h]
    exact AddChar.sum_eq_zero_iff_ne_zero.mpr (sub_ne_zero.mpr h)

/-- Pontryagin separation: every nonzero element `x ≠ 0` of a finite abelian group `G`
is detected by some additive character `θ : AddChar G ℂ` (`θ x ≠ 1`). -/
theorem exists_addChar_ne_one {G : Type*} [AddCommGroup G] [Fintype G]
    {x : G} (hx : x ≠ 0) :
    ∃ θ : AddChar G ℂ, θ x ≠ 1 := by
  classical
  by_contra hall
  push Not at hall
  set A0 : AddSubgroup G := AddSubgroup.zmultiples x
  have htriv : ∀ (θ : AddChar G ℂ) (s : G), s ∈ A0 → θ s = 1 := by
    intro θ s hs
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hs
    rw [AddChar.map_zsmul_eq_zpow, hall θ, one_zpow]
  let π : G →+ G ⧸ A0 := QuotientAddGroup.mk' A0
  have hπ : Function.Surjective π := QuotientAddGroup.mk'_surjective A0
  have hsurj : Function.Surjective (fun χ : AddChar (G ⧸ A0) ℂ => χ.compAddMonoidHom π) := by
    intro θ
    have hker : ∀ y : G, π y = 0 → θ y = 1 := fun y hy =>
      htriv θ y ((QuotientAddGroup.eq_zero_iff y).mp hy)
    have wd : ∀ a b : G, π a = π b → θ a = θ b := by
      intro a b hab
      have h0 : π (a - b) = 0 := by rw [map_sub, hab, sub_self]
      calc θ a = θ (b + (a - b)) := by rw [add_sub_cancel]
        _ = θ b * θ (a - b) := AddChar.map_add_eq_mul θ _ _
        _ = θ b := by rw [hker _ h0, mul_one]
    let s := Function.surjInv hπ
    have hs : ∀ q, π (s q) = q := Function.surjInv_eq hπ
    refine ⟨{ toFun := fun q => θ (s q)
              map_zero_eq_one' := by
                rw [wd (s 0) 0 (by rw [hs, map_zero]), AddChar.map_zero_eq_one]
              map_add_eq_mul' := fun a b => by
                rw [← AddChar.map_add_eq_mul,
                  wd (s (a + b)) (s a + s b) (by rw [hs, map_add, hs, hs])] }, ?_⟩
    ext y
    exact wd _ _ (hs _)
  have hcard_le : Fintype.card (AddChar G ℂ) ≤ Fintype.card (AddChar (G ⧸ A0) ℂ) :=
    Fintype.card_le_of_surjective _ hsurj
  rw [AddChar.card_eq, AddChar.card_eq] at hcard_le
  have hlag : Fintype.card (G ⧸ A0) * Fintype.card A0 = Fintype.card G := by
    have h1 := AddSubgroup.index_mul_card A0
    rw [AddSubgroup.index_eq_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card] at h1
    exact h1
  have hA0_gt1 : 1 < Fintype.card A0 := by
    refine Fintype.one_lt_card_iff.mpr ⟨⟨0, A0.zero_mem⟩, ⟨x, AddSubgroup.mem_zmultiples x⟩, ?_⟩
    intro heq
    exact hx (congrArg Subtype.val heq).symm
  have hq_pos : 0 < Fintype.card (G ⧸ A0) := Fintype.card_pos_iff.mpr ⟨0⟩
  have hlt : Fintype.card (G ⧸ A0) < Fintype.card G := by
    rw [← hlag]
    exact lt_mul_of_one_lt_right hq_pos hA0_gt1
  omega

/-- Dual orthogonality on any finite abelian group `G`:
`∑_{θ : AddChar G ℂ} θ(x) * conj(θ(y)) = if x = y then |G| else 0`. -/
theorem addChar_orthogonality_dual {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (x y : G) :
    ∑ θ : AddChar G ℂ, θ x * starRingEnd ℂ (θ y) =
      if x = y then (Fintype.card G : ℂ) else 0 := by
  have hterm : ∀ θ : AddChar G ℂ, θ x * starRingEnd ℂ (θ y) = θ (x - y) := fun θ => by
    rw [addChar_conj_eq_neg, ← AddChar.map_add_eq_mul, sub_eq_add_neg]
  rw [Finset.sum_congr rfl fun θ _ => hterm θ]
  by_cases h : x = y
  · subst h
    rw [sub_self, if_pos rfl]
    simp only [AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ, AddChar.card_eq,
      nsmul_eq_mul, mul_one]
  · rw [if_neg h]
    let eval : AddChar (AddChar G ℂ) ℂ :=
      { toFun := fun θ => θ (x - y)
        map_zero_eq_one' := AddChar.zero_apply _
        map_add_eq_mul' := fun θ₁ θ₂ => AddChar.add_apply θ₁ θ₂ (x - y) }
    have hne : eval ≠ 0 := by
      obtain ⟨θ₀, hθ₀⟩ := exists_addChar_ne_one (sub_ne_zero.mpr h)
      intro h0
      exact hθ₀ (by simpa [eval] using DFunLike.congr_fun h0 θ₀)
    exact AddChar.sum_eq_zero_iff_ne_zero.mpr hne

/-- **Exact General Finite Abelian Parseval Identity (Analysis Form)**:
for any finite abelian group `G` and any `f : G → ℂ`,
`∑_{θ : AddChar G ℂ} ‖∑_{g : G} f g * θ g‖² = |G| * ∑_{g : G} ‖f g‖²`. -/
theorem addChar_parseval_analysis {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (f : G → ℂ) :
    ∑ θ : AddChar G ℂ, ‖∑ g : G, f g * θ g‖ ^ 2 =
      (Fintype.card G : ℝ) * ∑ g : G, ‖f g‖ ^ 2 := by
  simp_rw [norm_sum_sq_eq_re_local]
  rw [← Complex.re_sum]
  have hswap :
      ∑ θ : AddChar G ℂ, ∑ g₁ : G, ∑ g₂ : G,
          f g₁ * θ g₁ * starRingEnd ℂ (f g₂ * θ g₂) =
        (Fintype.card G : ℂ) * ∑ g : G, f g * starRingEnd ℂ (f g) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g₁ _ => ?_
    rw [Finset.sum_comm]
    have hinner : ∀ g₂ : G,
        ∑ θ : AddChar G ℂ, f g₁ * θ g₁ * starRingEnd ℂ (f g₂ * θ g₂) =
          if g₁ = g₂ then (Fintype.card G : ℂ) * (f g₁ * starRingEnd ℂ (f g₁)) else 0 := by
      intro g₂
      have hpull :
          ∑ θ : AddChar G ℂ, f g₁ * θ g₁ * starRingEnd ℂ (f g₂ * θ g₂) =
            f g₁ * starRingEnd ℂ (f g₂) * ∑ θ : AddChar G ℂ, θ g₁ * starRingEnd ℂ (θ g₂) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun θ _ => ?_
        rw [map_mul]; ring
      rw [hpull, addChar_orthogonality_dual g₁ g₂]
      split_ifs with h12
      · subst h12; ring
      · ring
    rw [Finset.sum_congr rfl fun g₂ _ => hinner g₂, Finset.sum_ite_eq Finset.univ g₁,
      if_pos (Finset.mem_univ g₁)]
  rw [hswap, show (Fintype.card G : ℂ) = ((Fintype.card G : ℝ) : ℂ) by norm_cast,
    Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- **Exact General Finite Abelian Parseval Identity (Synthesis Form)**:
for any finite abelian group `G` and any Fourier coefficients `E : AddChar G ℂ → ℂ`,
`∑_{g : G} ‖∑_{θ : AddChar G ℂ} E θ * θ g‖² = |G| * ∑_{θ : AddChar G ℂ} ‖E θ‖²`. -/
theorem addChar_parseval_synthesis {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (E : AddChar G ℂ → ℂ) :
    ∑ g : G, ‖∑ θ : AddChar G ℂ, E θ * θ g‖ ^ 2 =
      (Fintype.card G : ℝ) * ∑ θ : AddChar G ℂ, ‖E θ‖ ^ 2 := by
  simp_rw [norm_sum_sq_eq_re_local]
  rw [← Complex.re_sum]
  have hswap :
      ∑ g : G, ∑ θ₁ : AddChar G ℂ, ∑ θ₂ : AddChar G ℂ,
          E θ₁ * θ₁ g * starRingEnd ℂ (E θ₂ * θ₂ g) =
        (Fintype.card G : ℂ) * ∑ θ : AddChar G ℂ, E θ * starRingEnd ℂ (E θ) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun θ₁ _ => ?_
    rw [Finset.sum_comm]
    have hinner : ∀ θ₂ : AddChar G ℂ,
        ∑ g : G, E θ₁ * θ₁ g * starRingEnd ℂ (E θ₂ * θ₂ g) =
          if θ₁ = θ₂ then (Fintype.card G : ℂ) * (E θ₁ * starRingEnd ℂ (E θ₁)) else 0 := by
      intro θ₂
      have hpull :
          ∑ g : G, E θ₁ * θ₁ g * starRingEnd ℂ (E θ₂ * θ₂ g) =
            E θ₁ * starRingEnd ℂ (E θ₂) * ∑ g : G, θ₁ g * starRingEnd ℂ (θ₂ g) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [map_mul]; ring
      rw [hpull, addChar_orthogonality_group θ₁ θ₂]
      split_ifs with h12
      · subst h12; ring
      · ring
    rw [Finset.sum_congr rfl fun θ₂ _ => hinner θ₂, Finset.sum_ite_eq Finset.univ θ₁,
      if_pos (Finset.mem_univ θ₁)]
  rw [hswap, show (Fintype.card G : ℂ) = ((Fintype.card G : ℝ) : ℂ) by norm_cast,
    Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun θ _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- **Exact Parseval Synthesis Identity Excluding a Target Character `ψ`**:
for any finite abelian group `G`, any target character `ψ : AddChar G ℂ`, and any `E : AddChar G ℂ → ℂ`,
`∑_{g : G} ‖∑_{θ ≠ ψ} E θ * θ g‖² = |G| * ∑_{θ ≠ ψ} ‖E θ‖²`. -/
theorem addChar_parseval_synthesis_erase {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (ψ : AddChar G ℂ) (E : AddChar G ℂ → ℂ) :
    ∑ g : G, ‖∑ θ ∈ Finset.univ.erase ψ, E θ * θ g‖ ^ 2 =
      (Fintype.card G : ℝ) * ∑ θ ∈ Finset.univ.erase ψ, ‖E θ‖ ^ 2 := by
  classical
  let E' : AddChar G ℂ → ℂ := fun θ => if θ = ψ then 0 else E θ
  have hL : ∀ g : G, ∑ θ : AddChar G ℂ, E' θ * θ g = ∑ θ ∈ Finset.univ.erase ψ, E θ * θ g := by
    intro g
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ ψ)]
    simp only [E', ↓reduceIte, zero_mul, zero_add]
    exact Finset.sum_congr rfl fun θ hθ => by rw [if_neg (Finset.mem_erase.mp hθ).1]
  have hR : ∑ θ : AddChar G ℂ, ‖E' θ‖ ^ 2 = ∑ θ ∈ Finset.univ.erase ψ, ‖E θ‖ ^ 2 := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ ψ)]
    simp only [E', ↓reduceIte, norm_zero, zero_pow two_ne_zero, zero_add]
    exact Finset.sum_congr rfl fun θ hθ => by rw [if_neg (Finset.mem_erase.mp hθ).1]
  have hp := addChar_parseval_synthesis E'
  simpa only [hL, hR] using hp

/-! ## Section 2: Concrete Prime-Residue Thick-Frame Existence Without Behrend 3-AP Spheres -/

/-- **Concrete Prime-Residue Thick-Frame Existence Without Behrend 3-AP Spheres
(`exists_dense_good_coset_frame`)** (`0` assumptions):
Given ANY finite abelian group `G`, ANY target character `ψ : AddChar G ℂ`, ANY Fourier error
spectrum `E : AddChar G ℂ → ℂ` satisfying `∑_{θ ≠ ψ} ‖E θ‖² ≤ B` (`0 ≤ B`), and EVERY `δ ∈ (0, 1)`,
direct Parseval + Markov averaging produces a dense good frame `TT : Finset G` of **constant
density `≥ 1 - δ`** such that EVERY `g ∈ TT` simultaneously obeys:
1. unitary-scaled character-sum error `‖|G|^(-1/2) ∑_{θ ≠ ψ} E θ * θ g‖ ≤ √(B / (δ |G|))`,
2. inverse-Fourier coset error `‖|G|⁻¹ ∑_{θ ≠ ψ} E θ * θ g‖ ≤ √(B / (δ |G|²)) ≤ √(B / (δ |G|))`,
3. unnormalized character-sum error `‖∑_{θ ≠ ψ} E θ * θ g‖ ≤ √(B / δ)`. -/
theorem exists_dense_good_coset_frame {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (ψ : AddChar G ℂ) (E : AddChar G ℂ → ℂ) {B δ : ℝ}
    (hB : 0 ≤ B) (hδ0 : 0 < δ) (_hδ1 : δ < 1)
    (hMS : ∑ θ ∈ Finset.univ.erase ψ, ‖E θ‖ ^ 2 ≤ B) :
    ∃ TT : Finset G,
      (1 - δ) * (Fintype.card G : ℝ) ≤ (TT.card : ℝ) ∧
      (∀ g ∈ TT,
        ((Fintype.card G : ℝ) ^ (-(1 / 2 : ℝ))) *
            ‖∑ θ ∈ Finset.univ.erase ψ, E θ * θ g‖ ≤
          Real.sqrt (B / (δ * (Fintype.card G : ℝ)))) ∧
      (∀ g ∈ TT,
        ‖((Fintype.card G : ℂ)⁻¹) * ∑ θ ∈ Finset.univ.erase ψ, E θ * θ g‖ ≤
          Real.sqrt (B / (δ * (Fintype.card G : ℝ))) ∧
        ‖((Fintype.card G : ℂ)⁻¹) * ∑ θ ∈ Finset.univ.erase ψ, E θ * θ g‖ ≤
          Real.sqrt (B / (δ * (Fintype.card G : ℝ) ^ 2))) ∧
      (∀ g ∈ TT,
        ‖∑ θ ∈ Finset.univ.erase ψ, E θ * θ g‖ ≤ Real.sqrt (B / δ)) := by
  classical
  have hG_pos : (0 : ℝ) < (Fintype.card G : ℝ) :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨0⟩)
  have hG_ge1 : (1 : ℝ) ≤ (Fintype.card G : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨0⟩ : 1 ≤ Fintype.card G)
  have hscale : ∀ g : G,
      ‖∑ θ ∈ Finset.univ.erase ψ, E θ * θ g‖ ≤ Real.sqrt (B / δ) →
      (((Fintype.card G : ℝ) ^ (-(1 / 2 : ℝ))) *
          ‖∑ θ ∈ Finset.univ.erase ψ, E θ * θ g‖ ≤
        Real.sqrt (B / (δ * (Fintype.card G : ℝ)))) ∧
      (‖((Fintype.card G : ℂ)⁻¹) * ∑ θ ∈ Finset.univ.erase ψ, E θ * θ g‖ ≤
        Real.sqrt (B / (δ * (Fintype.card G : ℝ))) ∧
       ‖((Fintype.card G : ℂ)⁻¹) * ∑ θ ∈ Finset.univ.erase ψ, E θ * θ g‖ ≤
        Real.sqrt (B / (δ * (Fintype.card G : ℝ) ^ 2))) := by
    intro g hg
    have hunit :
        ((Fintype.card G : ℝ) ^ (-(1 / 2 : ℝ))) *
            ‖∑ θ ∈ Finset.univ.erase ψ, E θ * θ g‖ ≤
          Real.sqrt (B / (δ * (Fintype.card G : ℝ))) := by
      have hrpow_inv : (Fintype.card G : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (Fintype.card G : ℝ))⁻¹ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hG_pos.le]
      rw [hrpow_inv]
      calc (Real.sqrt (Fintype.card G : ℝ))⁻¹ * ‖∑ θ ∈ Finset.univ.erase ψ, E θ * θ g‖
          ≤ (Real.sqrt (Fintype.card G : ℝ))⁻¹ * Real.sqrt (B / δ) :=
            mul_le_mul_of_nonneg_left hg (inv_nonneg.mpr (Real.sqrt_nonneg _))
        _ = Real.sqrt (B / δ) / Real.sqrt (Fintype.card G : ℝ) := by ring
        _ = Real.sqrt ((B / δ) / (Fintype.card G : ℝ)) := (Real.sqrt_div (div_nonneg hB hδ0.le) _).symm
        _ = Real.sqrt (B / (δ * (Fintype.card G : ℝ))) := by rw [div_div]
    have hinv2 :
        ‖((Fintype.card G : ℂ)⁻¹) * ∑ θ ∈ Finset.univ.erase ψ, E θ * θ g‖ ≤
          Real.sqrt (B / (δ * (Fintype.card G : ℝ) ^ 2)) := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      calc (Fintype.card G : ℝ)⁻¹ * ‖∑ θ ∈ Finset.univ.erase ψ, E θ * θ g‖
          ≤ (Fintype.card G : ℝ)⁻¹ * Real.sqrt (B / δ) :=
            mul_le_mul_of_nonneg_left hg (inv_nonneg.mpr hG_pos.le)
        _ = Real.sqrt (B / δ) / Real.sqrt ((Fintype.card G : ℝ) ^ 2) := by
            rw [Real.sqrt_sq hG_pos.le]; ring
        _ = Real.sqrt ((B / δ) / (Fintype.card G : ℝ) ^ 2) :=
            (Real.sqrt_div (div_nonneg hB hδ0.le) _).symm
        _ = Real.sqrt (B / (δ * (Fintype.card G : ℝ) ^ 2)) := by rw [div_div]
    have hinv1 :
        Real.sqrt (B / (δ * (Fintype.card G : ℝ) ^ 2)) ≤
          Real.sqrt (B / (δ * (Fintype.card G : ℝ))) := by
      refine Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hB (mul_pos hδ0 hG_pos) ?_)
      have hsq : (Fintype.card G : ℝ) ≤ (Fintype.card G : ℝ) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left hsq hδ0.le
    exact ⟨hunit, hinv2.trans hinv1, hinv2⟩
  by_cases hB0 : B = 0
  · subst hB0
    have hsum0 : ∑ g : G, ‖∑ θ ∈ Finset.univ.erase ψ, E θ * θ g‖ ^ 2 = 0 := by
      have h1 : ∑ θ ∈ Finset.univ.erase ψ, ‖E θ‖ ^ 2 = 0 :=
        le_antisymm hMS (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      rw [addChar_parseval_synthesis_erase ψ E, h1, mul_zero]
    have hall0 : ∀ g : G, ‖∑ θ ∈ Finset.univ.erase ψ, E θ * θ g‖ ≤ Real.sqrt (0 / δ) := by
      intro g
      have hg0 : ‖∑ θ ∈ Finset.univ.erase ψ, E θ * θ g‖ ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hsum0 g (Finset.mem_univ g)
      rw [sq_eq_zero_iff.mp hg0]
      exact Real.sqrt_nonneg _
    refine ⟨Finset.univ, ?_, fun g _ => (hscale g (hall0 g)).1,
      fun g _ => (hscale g (hall0 g)).2, fun g _ => hall0 g⟩
    rw [Finset.card_univ]
    nlinarith
  · have hB_pos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    set T : ℝ := Real.sqrt (B / δ)
    have hT_pos : 0 < T := Real.sqrt_pos.mpr (div_pos hB_pos hδ0)
    have hT_sq : T ^ 2 = B / δ := Real.sq_sqrt (div_nonneg hB hδ0.le)
    set Bad : Finset G := Finset.univ.filter (fun g : G =>
      T < ‖∑ θ ∈ Finset.univ.erase ψ, E θ * θ g‖)
    set TT : Finset G := Finset.univ.filter (fun g : G =>
      ‖∑ θ ∈ Finset.univ.erase ψ, E θ * θ g‖ ≤ T)
    have hBad_le : (Bad.card : ℝ) ≤ δ * (Fintype.card G : ℝ) := by
      have h1 : (Bad.card : ℝ) * T ^ 2 ≤ (Fintype.card G : ℝ) * B := by
        calc (Bad.card : ℝ) * T ^ 2
            = ∑ _g ∈ Bad, T ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ g ∈ Bad, ‖∑ θ ∈ Finset.univ.erase ψ, E θ * θ g‖ ^ 2 :=
              Finset.sum_le_sum fun g hg =>
                pow_le_pow_left₀ hT_pos.le (Finset.mem_filter.mp hg).2.le 2
          _ ≤ ∑ g : G, ‖∑ θ ∈ Finset.univ.erase ψ, E θ * θ g‖ ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _
          _ = (Fintype.card G : ℝ) * ∑ θ ∈ Finset.univ.erase ψ, ‖E θ‖ ^ 2 :=
              addChar_parseval_synthesis_erase ψ E
          _ ≤ (Fintype.card G : ℝ) * B := mul_le_mul_of_nonneg_left hMS hG_pos.le
      rw [hT_sq] at h1
      have h2 : (Bad.card : ℝ) * (B / δ) ≤ (δ * (Fintype.card G : ℝ)) * (B / δ) := by
        calc (Bad.card : ℝ) * (B / δ) ≤ (Fintype.card G : ℝ) * B := h1
          _ = (δ * (Fintype.card G : ℝ)) * (B / δ) := by field_simp [hδ0.ne']
      exact le_of_mul_le_mul_right h2 (div_pos hB_pos hδ0)
    have hpart : (TT.card : ℝ) + (Bad.card : ℝ) = (Fintype.card G : ℝ) := by
      have hBad_eq : Bad = Finset.univ.filter (fun g : G =>
          ¬ ‖∑ θ ∈ Finset.univ.erase ψ, E θ * θ g‖ ≤ T) := by
        ext g; simp only [Bad, Finset.mem_filter, not_le]
      have hnat : TT.card + Bad.card = Fintype.card G := by
        rw [hBad_eq, ← Finset.card_univ]
        exact Finset.card_filter_add_card_filter_not _
      exact_mod_cast hnat
    refine ⟨TT, by linarith,
      fun g hg => (hscale g (Finset.mem_filter.mp hg).2).1,
      fun g hg => (hscale g (Finset.mem_filter.mp hg).2).2,
      fun g hg => (Finset.mem_filter.mp hg).2⟩

open Classical in
/-- **Concrete Product-Group Thick-Frame Existence on `(ZMod q)ˣ × (ZMod d)ˣ`** (`0` assumptions):
given ANY target pair `ψ = (ψ₁, ψ₂)` and ANY second-moment bound `∑_{p ≠ ψ} ‖E p‖² ≤ B`,
for EVERY `δ ∈ (0, 1)` at least `(1 - δ) * φ(q) * φ(d)` pairs `(a, b) ∈ (ZMod q)ˣ × (ZMod d)ˣ`
have normalized character-sum error `≤ √(B / (δ * φ(q) * φ(d)))`. -/
theorem exists_dense_good_coset_frame_prod {q d : ℕ} [NeZero q] [NeZero d]
    (ψ : DirichletCharacter ℂ q × DirichletCharacter ℂ d)
    (E : DirichletCharacter ℂ q × DirichletCharacter ℂ d → ℂ)
    {B δ : ℝ} (hB : 0 ≤ B) (hδ0 : 0 < δ) (_hδ1 : δ < 1)
    (hMS : ∑ p ∈ Finset.univ.erase ψ, ‖E p‖ ^ 2 ≤ B) :
    ∃ TT : Finset ((ZMod q)ˣ × (ZMod d)ˣ),
      (1 - δ) * ((q.totient * d.totient : ℕ) : ℝ) ≤ (TT.card : ℝ) ∧
      ∀ u ∈ TT,
        ‖(((q.totient * d.totient : ℕ) : ℂ)⁻¹) *
            ∑ p ∈ Finset.univ.erase ψ, E p * (p.1 (u.1 : ZMod q) * p.2 (u.2 : ZMod d))‖ ≤
          Real.sqrt (B / (δ * ((q.totient * d.totient : ℕ) : ℝ))) ∧
        ‖∑ p ∈ Finset.univ.erase ψ, E p * (p.1 (u.1 : ZMod q) * p.2 (u.2 : ZMod d))‖ ≤
          Real.sqrt (B / δ) := by
  classical
  set N : ℕ := q.totient * d.totient
  have hN_pos_nat : 0 < N :=
    Nat.mul_pos (Nat.totient_pos.mpr (NeZero.pos q)) (Nat.totient_pos.mpr (NeZero.pos d))
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN_pos_nat
  have hN_ge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_pos_nat
  have hcard_prod : ((Finset.univ : Finset ((ZMod q)ˣ × (ZMod d)ˣ)).card : ℝ) = (N : ℝ) := by
    rw [Finset.card_univ, Fintype.card_prod, ZMod.card_units_eq_totient, ZMod.card_units_eq_totient]
  -- Zero out E at ψ and apply `dirichlet_parseval_prod_synthesis`
  let E' : DirichletCharacter ℂ q × DirichletCharacter ℂ d → ℂ := fun p => if p = ψ then 0 else E p
  have hparseval_erase :
      ∑ u : (ZMod q)ˣ × (ZMod d)ˣ,
          ‖∑ p ∈ Finset.univ.erase ψ, E p * (p.1 (u.1 : ZMod q) * p.2 (u.2 : ZMod d))‖ ^ 2 =
        (N : ℝ) * ∑ p ∈ Finset.univ.erase ψ, ‖E p‖ ^ 2 := by
    have hL : ∀ u : (ZMod q)ˣ × (ZMod d)ˣ,
        ∑ p : DirichletCharacter ℂ q × DirichletCharacter ℂ d,
            E' p * (p.1 (u.1 : ZMod q) * p.2 (u.2 : ZMod d)) =
          ∑ p ∈ Finset.univ.erase ψ, E p * (p.1 (u.1 : ZMod q) * p.2 (u.2 : ZMod d)) := by
      intro u
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ ψ)]
      simp only [E', ↓reduceIte, zero_mul, zero_add]
      exact Finset.sum_congr rfl fun p hp => by rw [if_neg (Finset.mem_erase.mp hp).1]
    have hR : ∑ p : DirichletCharacter ℂ q × DirichletCharacter ℂ d, ‖E' p‖ ^ 2 =
        ∑ p ∈ Finset.univ.erase ψ, ‖E p‖ ^ 2 := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ ψ)]
      simp only [E', ↓reduceIte, norm_zero, zero_pow two_ne_zero, zero_add]
      exact Finset.sum_congr rfl fun p hp => by rw [if_neg (Finset.mem_erase.mp hp).1]
    have hp := dirichlet_parseval_prod_synthesis E'
    simpa only [hL, hR] using hp
  have hscale : ∀ u : (ZMod q)ˣ × (ZMod d)ˣ,
      ‖∑ p ∈ Finset.univ.erase ψ, E p * (p.1 (u.1 : ZMod q) * p.2 (u.2 : ZMod d))‖ ≤
        Real.sqrt (B / δ) →
      ‖((N : ℂ)⁻¹) *
          ∑ p ∈ Finset.univ.erase ψ, E p * (p.1 (u.1 : ZMod q) * p.2 (u.2 : ZMod d))‖ ≤
        Real.sqrt (B / (δ * (N : ℝ))) := by
    intro u hu
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (N : ℝ)⁻¹ * ‖∑ p ∈ Finset.univ.erase ψ, E p * (p.1 (u.1 : ZMod q) * p.2 (u.2 : ZMod d))‖
        ≤ (N : ℝ)⁻¹ * Real.sqrt (B / δ) := mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr hN_pos.le)
      _ = Real.sqrt (B / δ) / Real.sqrt ((N : ℝ) ^ 2) := by rw [Real.sqrt_sq hN_pos.le]; ring
      _ = Real.sqrt (B / (δ * (N : ℝ) ^ 2)) := by
          rw [← Real.sqrt_div (div_nonneg hB hδ0.le), div_div]
      _ ≤ Real.sqrt (B / (δ * (N : ℝ))) := by
          refine Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hB (mul_pos hδ0 hN_pos) ?_)
          have hsq : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
          exact mul_le_mul_of_nonneg_left hsq hδ0.le
  by_cases hB0 : B = 0
  · subst hB0
    have hsum0 :
        ∑ u : (ZMod q)ˣ × (ZMod d)ˣ,
          ‖∑ p ∈ Finset.univ.erase ψ, E p * (p.1 (u.1 : ZMod q) * p.2 (u.2 : ZMod d))‖ ^ 2 = 0 := by
      have h1 : ∑ p ∈ Finset.univ.erase ψ, ‖E p‖ ^ 2 = 0 :=
        le_antisymm hMS (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      rw [hparseval_erase, h1, mul_zero]
    have hall0 : ∀ u : (ZMod q)ˣ × (ZMod d)ˣ,
        ‖∑ p ∈ Finset.univ.erase ψ, E p * (p.1 (u.1 : ZMod q) * p.2 (u.2 : ZMod d))‖ ≤
          Real.sqrt (0 / δ) := by
      intro u
      have hu0 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hsum0 u (Finset.mem_univ u)
      rw [sq_eq_zero_iff.mp hu0]
      exact Real.sqrt_nonneg _
    refine ⟨Finset.univ, ?_, fun u _ => ⟨hscale u (hall0 u), hall0 u⟩⟩
    rw [hcard_prod]
    nlinarith
  · have hB_pos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    set T : ℝ := Real.sqrt (B / δ)
    have hT_pos : 0 < T := Real.sqrt_pos.mpr (div_pos hB_pos hδ0)
    have hT_sq : T ^ 2 = B / δ := Real.sq_sqrt (div_nonneg hB hδ0.le)
    set Bad := Finset.univ.filter (fun u : (ZMod q)ˣ × (ZMod d)ˣ =>
      T < ‖∑ p ∈ Finset.univ.erase ψ, E p * (p.1 (u.1 : ZMod q) * p.2 (u.2 : ZMod d))‖)
    set TT := Finset.univ.filter (fun u : (ZMod q)ˣ × (ZMod d)ˣ =>
      ‖∑ p ∈ Finset.univ.erase ψ, E p * (p.1 (u.1 : ZMod q) * p.2 (u.2 : ZMod d))‖ ≤ T)
    have hBad_le : (Bad.card : ℝ) ≤ δ * (N : ℝ) := by
      have h1 : (Bad.card : ℝ) * T ^ 2 ≤ (N : ℝ) * B := by
        calc (Bad.card : ℝ) * T ^ 2
            = ∑ _u ∈ Bad, T ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ u ∈ Bad, ‖∑ p ∈ Finset.univ.erase ψ, E p * (p.1 (u.1 : ZMod q) * p.2 (u.2 : ZMod d))‖ ^ 2 :=
              Finset.sum_le_sum fun u hu =>
                pow_le_pow_left₀ hT_pos.le (Finset.mem_filter.mp hu).2.le 2
          _ ≤ ∑ u : (ZMod q)ˣ × (ZMod d)ˣ,
                ‖∑ p ∈ Finset.univ.erase ψ, E p * (p.1 (u.1 : ZMod q) * p.2 (u.2 : ZMod d))‖ ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _
          _ = (N : ℝ) * ∑ p ∈ Finset.univ.erase ψ, ‖E p‖ ^ 2 := hparseval_erase
          _ ≤ (N : ℝ) * B := mul_le_mul_of_nonneg_left hMS hN_pos.le
      rw [hT_sq] at h1
      have h2 : (Bad.card : ℝ) * (B / δ) ≤ (δ * (N : ℝ)) * (B / δ) := by
        calc (Bad.card : ℝ) * (B / δ) ≤ (N : ℝ) * B := h1
          _ = (δ * (N : ℝ)) * (B / δ) := by field_simp [hδ0.ne']
      exact le_of_mul_le_mul_right h2 (div_pos hB_pos hδ0)
    have hpart : (TT.card : ℝ) + (Bad.card : ℝ) = (N : ℝ) := by
      have hBad_eq : Bad = Finset.univ.filter (fun u : (ZMod q)ˣ × (ZMod d)ˣ =>
          ¬ ‖∑ p ∈ Finset.univ.erase ψ, E p * (p.1 (u.1 : ZMod q) * p.2 (u.2 : ZMod d))‖ ≤ T) := by
        ext u; simp only [Bad, Finset.mem_filter, not_le]
      have hnat : TT.card + Bad.card = (Finset.univ : Finset ((ZMod q)ˣ × (ZMod d)ˣ)).card := by
        rw [hBad_eq]; exact Finset.card_filter_add_card_filter_not _
      rw [← hcard_prod]; exact_mod_cast hnat
    exact ⟨TT, by linarith, fun u hu => ⟨hscale u (Finset.mem_filter.mp hu).2, (Finset.mem_filter.mp hu).2⟩⟩

/-! ### Direct Bridge to `AnalyticBridge`'s `(3o + 1)` Weight Clearing & `Stage2AnalyticWire` -/

/-- Second-moment control of `CosetFrame.offKeptNorm` via Cauchy–Schwarz:
`∑_{θ ∈ A0⊥ \ Kp} ‖G θ‖² ≤ B` implies `φ.offKeptNorm Kp G ≤ √(φ.o * B)`. -/
theorem cosetFrame_offKeptNorm_le_of_secondMoment (φ : CosetFrame)
    (Kp : Finset (AddChar φ.A ℂ)) (G : AddChar φ.A ℂ → ℂ) {B : ℝ}
    (hB : ∑ θ ∈ φ.annihilator \ Kp, ‖G θ‖ ^ 2 ≤ B) :
    φ.offKeptNorm Kp G ≤ Real.sqrt ((φ.o : ℝ) * B) := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (φ.annihilator \ Kp) (fun _ => (1 : ℝ)) (fun θ => ‖G θ‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hcard : ((φ.annihilator \ Kp).card : ℝ) ≤ (φ.o : ℝ) := by
    rw [← φ.card_annihilator]
    exact_mod_cast Finset.card_le_card Finset.sdiff_subset
  have hsq : (φ.offKeptNorm Kp G) ^ 2 ≤ (φ.o : ℝ) * B := by
    unfold CosetFrame.offKeptNorm
    exact hcs.trans (mul_le_mul hcard hB (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _))
  exact Real.le_sqrt_of_sq_le hsq

/-- **Direct `(3o + 1)` Weight-Cleared Second-Moment Transfer (`AnalyticBridge` + `Stage2AnalyticWire`)**:
plugs `L²` off-kept and perturbation bounds directly into `Stage2AnalyticWire.cosetFrame_fourier_clear_level_Gm`
and `AnalyticBridge.level_gm_clear_denom`, clearing the `(3o + 1)⁻¹` denominator with zero Behrend spheres. -/
theorem cosetFrame_fourier_clear_level_Gm_of_secondMoment (φ : CosetFrame) (L : Level)
    (ho : φ.o = L.o) (ι : PChar → AddChar φ.A ℂ)
    (hinj : Set.InjOn ι (L.KEPT : Set PChar)) (h1 : ι PChar.one = 0)
    {TT : Finset φ.A} {δ : ℝ} (hsh : φ.Shares TT δ)
    (hKp : L.KEPT.image ι ⊆ φ.annihilator)
    (G : AddChar φ.A ℂ → ℂ) (Gt : φ.A → AddChar φ.A ℂ → ℂ) (Err : AddChar φ.A ℂ → ℝ)
    (y : ℝ) (hG : ∀ ψ ∈ L.KEPT, (G (ι ψ)).re = (Gchi ψ.χ y).re)
    (hpert : ∀ t ∈ TT, ∀ θ ∈ φ.annihilator, ‖Gt t θ - G θ‖ ≤ Err θ)
    {B B_err : ℝ}
    (hB : ∑ θ ∈ φ.annihilator \ L.KEPT.image ι, ‖G θ‖ ^ 2 ≤ B)
    (hB_err : ∑ θ ∈ φ.annihilator, (Err θ) ^ 2 ≤ B_err) :
    (TT.card : ℝ) *
        ((3 * (L.o : ℝ) + 1) * Gz y + ∑ ψ ∈ L.Nt, (Gchi ψ.χ y).re -
          (3 * (L.o : ℝ) + 1) *
            (Real.sqrt ((φ.o : ℝ) * B) +
             (φ.o : ℝ) * δ * ∑ θ ∈ (L.KEPT.image ι).erase 0, ‖G θ‖ +
             Real.sqrt ((φ.o : ℝ) * B_err))) ≤
      (3 * (L.o : ℝ) + 1) * ∑ t ∈ TT, (∑ θ ∈ φ.annihilator, θ t * Gt t θ).re := by
  have hclear := Stage2AnalyticWire.cosetFrame_fourier_clear_level_Gm
    φ L ho ι hinj h1 hsh hKp G Gt Err y hG hpert
  have hoff : φ.offKeptNorm (L.KEPT.image ι) G ≤ Real.sqrt ((φ.o : ℝ) * B) :=
    cosetFrame_offKeptNorm_le_of_secondMoment φ (L.KEPT.image ι) G hB
  have herr_le : ∑ θ ∈ φ.annihilator, Err θ ≤ Real.sqrt ((φ.o : ℝ) * B_err) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq φ.annihilator (fun _ => (1 : ℝ)) Err
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, φ.card_annihilator] at hcs
    by_cases hneg : ∑ θ ∈ φ.annihilator, Err θ ≤ 0
    · exact hneg.trans (Real.sqrt_nonneg _)
    · exact Real.le_sqrt_of_sq_le (hcs.trans (mul_le_mul_of_nonneg_left hB_err (Nat.cast_nonneg _)))
  have hstep :
      (TT.card : ℝ) *
          (L.Gm y - Real.sqrt ((φ.o : ℝ) * B) -
            (φ.o : ℝ) * δ * ∑ θ ∈ (L.KEPT.image ι).erase 0, ‖G θ‖ -
            Real.sqrt ((φ.o : ℝ) * B_err)) ≤
        ∑ t ∈ TT, (∑ θ ∈ φ.annihilator, θ t * Gt t θ).re :=
    (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)).trans hclear
  have h3pos : (0 : ℝ) < 3 * (L.o : ℝ) + 1 := L.three_o_add_one_pos
  have hmul := mul_le_mul_of_nonneg_left hstep h3pos.le
  have hGm_clear := level_gm_clear_denom L y
  nlinarith

/-- **Coset-Slice Thick-Frame Lower Bound Without Behrend Spheres**:
any dense frame `TT ⊆ φ.A` of density `≥ 1 - η` (as supplied by `exists_dense_good_coset_frame`)
intersects EVERY coset `γ + φ.A0` in at least `(1 - φ.o * η) * |φ.A0|` elements. -/
theorem dense_frame_coset_slice_lower_bound (φ : CosetFrame) (TT : Finset φ.A) {η : ℝ}
    (hTT : (1 - η) * (Fintype.card φ.A : ℝ) ≤ (TT.card : ℝ)) (γ : φ.A) :
    (1 - (φ.o : ℝ) * η) * (Fintype.card φ.A0 : ℝ) ≤
      ((TT.filter (fun t => t - γ ∈ φ.A0)).card : ℝ) := by
  classical
  set C : Finset φ.A := Finset.univ.filter (fun t => t - γ ∈ φ.A0)
  have hC_card : C.card = Fintype.card φ.A0 := by
    have eqv : φ.A0 ≃ {t : φ.A // t - γ ∈ φ.A0} :=
      { toFun := fun s => ⟨γ + s, by simp [s.2]⟩
        invFun := fun t => ⟨t - γ, t.2⟩
        left_inv := fun s => by ext; simp
        right_inv := fun t => by ext; simp }
    rw [← Fintype.card_subtype (fun t : φ.A => t - γ ∈ φ.A0), ← Fintype.card_congr eqv]
  have hmiss_sub : C \ TT ⊆ Finset.univ \ TT := Finset.sdiff_subset_sdiff (Finset.subset_univ C) Subset.rfl
  have hmiss_card : ((C \ TT).card : ℝ) ≤ η * (Fintype.card φ.A : ℝ) := by
    have h1 : (C \ TT).card ≤ (Finset.univ \ TT).card := Finset.card_le_card hmiss_sub
    have h2 : (Finset.univ \ TT).card + TT.card = Fintype.card φ.A := by
      rw [← Finset.card_univ]; exact Finset.card_sdiff_add_card_eq_card (Finset.subset_univ TT)
    have h1R : ((C \ TT).card : ℝ) ≤ ((Finset.univ \ TT).card : ℝ) := by exact_mod_cast h1
    have h2R : ((Finset.univ \ TT).card : ℝ) + (TT.card : ℝ) = (Fintype.card φ.A : ℝ) := by
      exact_mod_cast h2
    linarith
  have hsplit : (TT.filter (fun t => t - γ ∈ φ.A0)).card + (C \ TT).card = C.card := by
    have heq : TT.filter (fun t => t - γ ∈ φ.A0) = C ∩ TT := by
      ext t; simp only [C, Finset.mem_filter, Finset.mem_inter, Finset.mem_univ, true_and, and_comm]
    rw [heq, add_comm]
    exact Finset.card_sdiff_add_card_inter C TT
  have hsplitR :
      ((TT.filter (fun t => t - γ ∈ φ.A0)).card : ℝ) + ((C \ TT).card : ℝ) = (Fintype.card φ.A0 : ℝ) := by
    rw [← hC_card]; exact_mod_cast hsplit
  have hidx : (Fintype.card φ.A : ℝ) = (φ.o : ℝ) * (Fintype.card φ.A0 : ℝ) := by
    exact_mod_cast φ.index_eq.symm
  rw [hidx] at hmiss_card
  linarith

/-! ### Explicit Dominance Over Behrend's `exp(-c √(log N))` Density (`Stage2BehrendSieve`) -/

/-- **Parseval Frame Strictly Dominates Behrend's `exp(-c √(log N))` Density for ALL `N ≥ 2`
(`secondMoment_replaces_behrend_density`)**:
for EVERY Behrend exponent `c > 0` and EVERY `δ > 0` with `δ < 1 - exp(-c √(log 2))`,
our Parseval frame's constant density `1 - δ` strictly exceeds Behrend's `exp(-c √(log N))`
density for **ALL `N ≥ 2`**. -/
theorem secondMoment_replaces_behrend_density {c δ : ℝ} (hc : 0 < c)
    (hδ : δ < 1 - Real.exp (-c * Real.sqrt (Real.log (2 : ℝ))))
    {N : ℕ} (hN : 2 ≤ N) :
    Real.exp (-c * Real.sqrt (Real.log (N : ℝ))) < 1 - δ := by
  have hlog_le : Real.log (2 : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hsqrt_le : Real.sqrt (Real.log (2 : ℝ)) ≤ Real.sqrt (Real.log (N : ℝ)) :=
    Real.sqrt_le_sqrt hlog_le
  have hexp_le : Real.exp (-c * Real.sqrt (Real.log (N : ℝ))) ≤
      Real.exp (-c * Real.sqrt (Real.log (2 : ℝ))) :=
    Real.exp_le_exp.mpr (by nlinarith)
  linarith

/-- **Explicit Numerical Dominance Over `Stage2BehrendSieve.behrend_subexponential_bound` (`c = 6`)**:
for ALL `N ≥ 2` and EVERY `δ ∈ (0, 1/2]`, Behrend's exact density `exp(-6 √(log N))` from
`Stage2BehrendSieve.behrend_subexponential_bound` is strictly `< 1 / 20 < 1 - δ` (over `10×`
smaller than our Parseval frame density `≥ 1/2` already at `N = 2`!). -/
theorem secondMoment_replaces_behrend_density_stage2 {δ : ℝ} (hδ : δ ≤ 1 / 2)
    {N : ℕ} (hN : 2 ≤ N) :
    Real.exp (-6 * Real.sqrt (Real.log (N : ℝ))) < 1 / 20 ∧ (1 / 20 : ℝ) < 1 - δ := by
  have hlog2 : (1 / 2 : ℝ) < Real.log (2 : ℝ) := by linarith [Real.log_two_gt_d9]
  have hlogN : (1 / 2 : ℝ) < Real.log (N : ℝ) :=
    hlog2.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast hN))
  have hsqrt : (1 / 2 : ℝ) < Real.sqrt (Real.log (N : ℝ)) := by
    rw [Real.lt_sqrt (by norm_num)]
    linarith
  have h3 : (3 : ℝ) < 6 * Real.sqrt (Real.log (N : ℝ)) := by linarith
  have hexp3 : (20 : ℝ) < Real.exp 3 := by
    have h27 : (2718 / 1000 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hpow : (2718 / 1000 : ℝ) ^ 3 < (Real.exp 1) ^ 3 := pow_lt_pow_left₀ h27 (by norm_num) (by norm_num)
    rw [← Real.exp_nat_mul] at hpow
    norm_num at hpow ⊢
    linarith
  have hexp_lt : Real.exp (-6 * Real.sqrt (Real.log (N : ℝ))) < 1 / 20 := by
    rw [neg_mul, Real.exp_neg, one_div, inv_lt_inv₀ (Real.exp_pos _) (by norm_num)]
    exact hexp3.trans (Real.exp_lt_exp.mpr h3)
  exact ⟨hexp_lt, by linarith⟩

/-- **Asymptotic Super-Polynomial Dominance Over Behrend**:
for EVERY `c > 0` and EVERY `δ ∈ (0, 1)`, the density gain ratio `(1 - δ) / exp(-c √(log N))`
tends to `+∞` as `N → ∞`. -/
theorem secondMoment_replaces_behrend_density_tendsto {c δ : ℝ} (hc : 0 < c) (hδ1 : δ < 1) :
    Tendsto (fun N : ℕ => (1 - δ) / Real.exp (-c * Real.sqrt (Real.log (N : ℝ)))) atTop atTop := by
  have h1 : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun N : ℕ => Real.sqrt (Real.log (N : ℝ))) atTop atTop :=
    Filter.tendsto_atTop.mpr fun b => by
      filter_upwards [Filter.tendsto_atTop.mp h1 ((max b 0) ^ 2)] with N hN
      exact (le_max_left b 0).trans ((Real.le_sqrt (le_max_right b 0) (by positivity)).mpr hN)
  have h3 : Tendsto (fun N : ℕ => c * Real.sqrt (Real.log (N : ℝ))) atTop atTop :=
    Tendsto.const_mul_atTop hc h2
  have h4 : Tendsto (fun N : ℕ => (1 - δ) * Real.exp (c * Real.sqrt (Real.log (N : ℝ)))) atTop atTop :=
    Tendsto.const_mul_atTop (by linarith) (Real.tendsto_exp_atTop.comp h3)
  refine h4.congr fun N => ?_
  rw [neg_mul, Real.exp_neg, div_inv_eq_mul]

/-! ## Section 3: Concrete Twisted Character-Box Zero-Free & Mean-Square Transfer -/

/-- Canonical twisted Dirichlet character `ψ * χ` modulo `d * q` induced by
`ψ : DirichletCharacter ℂ d` and `χ : DirichletCharacter ℂ q`. -/
def twistedChar {d q : ℕ} (ψ : DirichletCharacter ℂ d) (χ : DirichletCharacter ℂ q) :
    DirichletCharacter ℂ (d * q) :=
  DirichletCharacter.changeLevel (dvd_mul_right d q) ψ *
    DirichletCharacter.changeLevel (dvd_mul_left q d) χ

/-- Pointwise evaluation of `twistedChar ψ χ` on integers coprime to `d * q`. -/
theorem twistedChar_apply_nat_of_coprime {d q : ℕ}
    (ψ : DirichletCharacter ℂ d) (χ : DirichletCharacter ℂ q)
    {n : ℕ} (hcop : Nat.Coprime n (d * q)) :
    twistedChar ψ χ (n : ZMod (d * q)) = ψ (n : ZMod d) * χ (n : ZMod q) := by
  unfold twistedChar
  rw [MulChar.mul_apply,
    Stage8BarbanDavenport.changeLevel_apply_nat_of_coprime (dvd_mul_right d q) ψ hcop,
    Stage8BarbanDavenport.changeLevel_apply_nat_of_coprime (dvd_mul_left q d) χ hcop]

/-- For any fixed `ψ mod d`, twisting `χ ↦ twistedChar ψ χ` is injective on `DirichletCharacter ℂ q`. -/
theorem twistedChar_injective {d q : ℕ} [NeZero d] [NeZero q] (ψ : DirichletCharacter ℂ d) :
    Function.Injective (fun χ : DirichletCharacter ℂ q => twistedChar ψ χ) := by
  have : NeZero (d * q) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne q)⟩
  intro χ₁ χ₂ h
  unfold twistedChar at h
  exact DirichletCharacter.changeLevel_injective (dvd_mul_left q d) (mul_left_cancel h)

/-- If `Nat.Coprime d q` and `twistedChar ψ χ = 1`, then BOTH `ψ = 1` and `χ = 1`. -/
theorem twistedChar_eq_one_iff {d q : ℕ} [NeZero d] [NeZero q] (hcop : Nat.Coprime d q)
    (ψ : DirichletCharacter ℂ d) (χ : DirichletCharacter ℂ q) :
    twistedChar ψ χ = 1 ↔ ψ = 1 ∧ χ = 1 := by
  constructor
  · intro h1
    have hχ : χ = 1 := by
      ext a
      let cr := Nat.chineseRemainder hcop 1 (a : ZMod q).val
      set n : ℕ := cr.val
      have hnd : (n : ZMod d) = 1 := by
        have hmod : n ≡ 1 [MOD d] := cr.property.1
        simpa using (ZMod.natCast_eq_natCast_iff n 1 d).mpr hmod
      have hnq : (n : ZMod q) = (a : ZMod q) := by
        have hmod : n ≡ (a : ZMod q).val [MOD q] := cr.property.2
        have hcast := (ZMod.natCast_eq_natCast_iff n (a : ZMod q).val q).mpr hmod
        rwa [ZMod.natCast_zmod_val] at hcast
      have hcop_d : Nat.Coprime n d := (ZMod.isUnit_iff_coprime n d).mp (hnd ▸ isUnit_one)
      have hcop_q : Nat.Coprime n q := (ZMod.isUnit_iff_coprime n q).mp (hnq ▸ a.isUnit)
      have hcop_dq : Nat.Coprime n (d * q) := hcop_d.mul_right hcop_q
      have heval := congrArg (fun η : DirichletCharacter ℂ (d * q) => η (n : ZMod (d * q))) h1
      rw [twistedChar_apply_nat_of_coprime ψ χ hcop_dq, hnd, hnq, map_one, one_mul,
        MulChar.one_apply ((ZMod.isUnit_iff_coprime n (d * q)).mpr hcop_dq)] at heval
      rw [heval, MulChar.one_apply a.isUnit]
    have hψ : ψ = 1 := by
      ext b
      let cr := Nat.chineseRemainder hcop (b : ZMod d).val 1
      set n : ℕ := cr.val
      have hnd : (n : ZMod d) = (b : ZMod d) := by
        have hmod : n ≡ (b : ZMod d).val [MOD d] := cr.property.1
        have hcast := (ZMod.natCast_eq_natCast_iff n (b : ZMod d).val d).mpr hmod
        rwa [ZMod.natCast_zmod_val] at hcast
      have hnq : (n : ZMod q) = 1 := by
        have hmod : n ≡ 1 [MOD q] := cr.property.2
        simpa using (ZMod.natCast_eq_natCast_iff n 1 q).mpr hmod
      have hcop_d : Nat.Coprime n d := (ZMod.isUnit_iff_coprime n d).mp (hnd ▸ b.isUnit)
      have hcop_q : Nat.Coprime n q := (ZMod.isUnit_iff_coprime n q).mp (hnq ▸ isUnit_one)
      have hcop_dq : Nat.Coprime n (d * q) := hcop_d.mul_right hcop_q
      have heval := congrArg (fun η : DirichletCharacter ℂ (d * q) => η (n : ZMod (d * q))) h1
      rw [twistedChar_apply_nat_of_coprime ψ χ hcop_dq, hnd, hnq, map_one, mul_one,
        MulChar.one_apply ((ZMod.isUnit_iff_coprime n (d * q)).mpr hcop_dq)] at heval
      rw [heval, MulChar.one_apply b.isUnit]
    exact ⟨hψ, hχ⟩
  · rintro ⟨rfl, rfl⟩
    unfold twistedChar
    rw [map_one, map_one, one_mul]

/-- Exact Pythagorean sample-mean optimality: variance around the sample mean `ψ_coprime(x; M) / φ(M)`
is always `≤` variance around `x / φ(M)` (`psiAPVariance M x`). -/
theorem psiAP_variance_coprime_le_psiAPVariance {M : ℕ} [NeZero M] (x : ℝ) :
    ∑ a : (ZMod M)ˣ,
        (Stage2DirichletAP.chebyshevPsiAP M (a : ZMod M).val x -
          Stage2DirichletAP.chebyshevPsiCoprime M x / (M.totient : ℝ)) ^ 2 ≤
      Stage8BarbanDavenport.psiAPVariance M x := by
  rw [Stage8BarbanDavenport.psiAPVariance_eq_units]
  set μ : ℝ := Stage2DirichletAP.chebyshevPsiCoprime M x / (M.totient : ℝ)
  set c : ℝ := x / (M.totient : ℝ)
  have hphi_pos : (0 : ℝ) < (M.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos M))
  have hsum_ap : ∑ a : (ZMod M)ˣ, Stage2DirichletAP.chebyshevPsiAP M (a : ZMod M).val x =
      Stage2DirichletAP.chebyshevPsiCoprime M x := by
    unfold Stage2DirichletAP.chebyshevPsiAP Stage2DirichletAP.chebyshevPsiCoprime
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hcop : Nat.Coprime n M
    · rw [if_pos hcop]
      obtain ⟨a₀, ha₀⟩ := (ZMod.isUnit_iff_coprime n M).mpr hcop
      rw [Finset.sum_eq_single a₀]
      · have hmod : n ≡ (a₀ : ZMod M).val [MOD M] := by
          rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, ha₀]
        rw [if_pos hmod]
      · intro a _ hne
        have hnot : ¬ n ≡ (a : ZMod M).val [MOD M] := fun hmod => by
          rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val] at hmod
          exact hne (Units.ext (hmod.symm.trans ha₀.symm))
        rw [if_neg hnot]
      · intro h; exact absurd (Finset.mem_univ a₀) h
    · rw [if_neg hcop]
      refine Finset.sum_eq_zero fun a _ => ?_
      have hnot : ¬ n ≡ (a : ZMod M).val [MOD M] := fun hmod => by
        rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val] at hmod
        exact hcop ((ZMod.isUnit_iff_coprime n M).mp (hmod ▸ a.isUnit))
      rw [if_neg hnot]
  have hpyth :
      ∑ a : (ZMod M)ˣ, (Stage2DirichletAP.chebyshevPsiAP M (a : ZMod M).val x - c) ^ 2 =
        ∑ a : (ZMod M)ˣ, (Stage2DirichletAP.chebyshevPsiAP M (a : ZMod M).val x - μ) ^ 2 +
        (M.totient : ℝ) * (μ - c) ^ 2 := by
    have hterm : ∀ a : (ZMod M)ˣ,
        (Stage2DirichletAP.chebyshevPsiAP M (a : ZMod M).val x - c) ^ 2 =
          (Stage2DirichletAP.chebyshevPsiAP M (a : ZMod M).val x - μ) ^ 2 +
          2 * (μ - c) * (Stage2DirichletAP.chebyshevPsiAP M (a : ZMod M).val x - μ) +
          (μ - c) ^ 2 := fun _ => by ring
    simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul, hsum_ap]
    have hzero : Stage2DirichletAP.chebyshevPsiCoprime M x - (M.totient : ℝ) * μ = 0 := by
      dsimp only [μ]; rw [mul_div_cancel₀ _ hphi_pos.ne', sub_self]
    rw [hzero, mul_zero, add_zero]
  rw [hpyth]
  have hnn : 0 ≤ (M.totient : ℝ) * (μ - c) ^ 2 := mul_nonneg hphi_pos.le (sq_nonneg _)
  linarith

open Classical in
/-- **Exact Single-Modulus Twisted Character Mean-Square Bound via Parseval + AP Variance**:
for ANY primitive character `ψ : PChar` and ANY `q ≥ 1` coprime to `ψ.N`,
`φ(ψ.N * q)⁻¹ ∑_{χ ≠ 1} ‖ψ(x, ψ χ_q)‖² ≤ psiAPVariance (ψ.N * q) x`. -/
theorem twisted_char_mean_square_le_psiAPVariance (ψ : PChar) {q : ℕ} [NeZero q]
    (hcop : Nat.Coprime ψ.N q) (x : ℝ) :
    ((ψ.N * q).totient : ℝ)⁻¹ *
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ‖Stage2DirichletAP.chebyshevPsiChar (twistedChar ψ.χ χ) x‖ ^ 2 ≤
      Stage8BarbanDavenport.psiAPVariance (ψ.N * q) x := by
  have : NeZero (ψ.N * q) := ⟨Nat.mul_ne_zero (NeZero.ne ψ.N) (NeZero.ne q)⟩
  have hsub :
      (Finset.univ.erase (1 : DirichletCharacter ℂ q)).image (twistedChar ψ.χ) ⊆
        Finset.univ.erase (1 : DirichletCharacter ℂ (ψ.N * q)) := by
    intro η hη
    obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.mp hη
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro h1
    exact (Finset.mem_erase.mp hχ).1 ((twistedChar_eq_one_iff hcop ψ.χ χ).mp h1).2
  have hsum_le :
      ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ‖Stage2DirichletAP.chebyshevPsiChar (twistedChar ψ.χ χ) x‖ ^ 2 ≤
        ∑ η ∈ Finset.univ.erase (1 : DirichletCharacter ℂ (ψ.N * q)),
          ‖Stage2DirichletAP.chebyshevPsiChar η x‖ ^ 2 := by
    rw [← Finset.sum_image (f := fun η => ‖Stage2DirichletAP.chebyshevPsiChar η x‖ ^ 2)
      (g := twistedChar ψ.χ) (fun _ _ _ _ h => twistedChar_injective ψ.χ h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
  calc ((ψ.N * q).totient : ℝ)⁻¹ *
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ‖Stage2DirichletAP.chebyshevPsiChar (twistedChar ψ.χ χ) x‖ ^ 2
      ≤ ((ψ.N * q).totient : ℝ)⁻¹ *
          ∑ η ∈ Finset.univ.erase (1 : DirichletCharacter ℂ (ψ.N * q)),
            ‖Stage2DirichletAP.chebyshevPsiChar η x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = ∑ a : (ZMod (ψ.N * q))ˣ,
          (Stage2DirichletAP.chebyshevPsiAP (ψ.N * q) (a : ZMod (ψ.N * q)).val x -
            Stage2DirichletAP.chebyshevPsiCoprime (ψ.N * q) x / ((ψ.N * q).totient : ℝ)) ^ 2 :=
        (Stage3BombieriVinogradov.psiAP_variance_eq_nonprincipal_chars (q := ψ.N * q) x).symm
    _ ≤ Stage8BarbanDavenport.psiAPVariance (ψ.N * q) x :=
        psiAP_variance_coprime_le_psiAPVariance (M := ψ.N * q) x

/-- Full-character variant when `ψ ≠ PChar.one`: includes `χ = 1` as well since `twistedChar ψ.χ 1 ≠ 1`. -/
theorem twisted_char_mean_square_all_le_psiAPVariance {ψ : PChar} (hψ : ψ ≠ PChar.one)
    {q : ℕ} [NeZero q] (hcop : Nat.Coprime ψ.N q) (x : ℝ) :
    ((ψ.N * q).totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          ‖Stage2DirichletAP.chebyshevPsiChar (twistedChar ψ.χ χ) x‖ ^ 2 ≤
      Stage8BarbanDavenport.psiAPVariance (ψ.N * q) x := by
  classical
  have : NeZero (ψ.N * q) := ⟨Nat.mul_ne_zero (NeZero.ne ψ.N) (NeZero.ne q)⟩
  have hψχ : ψ.χ ≠ 1 := PChar.chi_ne_one_of_ne_one hψ
  have hsub :
      (Finset.univ : Finset (DirichletCharacter ℂ q)).image (twistedChar ψ.χ) ⊆
        Finset.univ.erase (1 : DirichletCharacter ℂ (ψ.N * q)) := by
    intro η hη
    obtain ⟨χ, _, rfl⟩ := Finset.mem_image.mp hη
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro h1
    exact hψχ ((twistedChar_eq_one_iff hcop ψ.χ χ).mp h1).1
  have hsum_le :
      ∑ χ : DirichletCharacter ℂ q,
          ‖Stage2DirichletAP.chebyshevPsiChar (twistedChar ψ.χ χ) x‖ ^ 2 ≤
        ∑ η ∈ Finset.univ.erase (1 : DirichletCharacter ℂ (ψ.N * q)),
          ‖Stage2DirichletAP.chebyshevPsiChar η x‖ ^ 2 := by
    rw [← Finset.sum_image (f := fun η => ‖Stage2DirichletAP.chebyshevPsiChar η x‖ ^ 2)
      (g := twistedChar ψ.χ) (fun _ _ _ _ h => twistedChar_injective ψ.χ h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
  calc ((ψ.N * q).totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          ‖Stage2DirichletAP.chebyshevPsiChar (twistedChar ψ.χ χ) x‖ ^ 2
      ≤ ((ψ.N * q).totient : ℝ)⁻¹ *
          ∑ η ∈ Finset.univ.erase (1 : DirichletCharacter ℂ (ψ.N * q)),
            ‖Stage2DirichletAP.chebyshevPsiChar η x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = ∑ a : (ZMod (ψ.N * q))ˣ,
          (Stage2DirichletAP.chebyshevPsiAP (ψ.N * q) (a : ZMod (ψ.N * q)).val x -
            Stage2DirichletAP.chebyshevPsiCoprime (ψ.N * q) x / ((ψ.N * q).totient : ℝ)) ^ 2 :=
        (Stage3BombieriVinogradov.psiAP_variance_eq_nonprincipal_chars (q := ψ.N * q) x).symm
    _ ≤ Stage8BarbanDavenport.psiAPVariance (ψ.N * q) x :=
        psiAP_variance_coprime_le_psiAPVariance (M := ψ.N * q) x

/-- Dyadic Cesàro-1 mean of `Stage2DirichletAP.chebyshevPsiChar` over `[⌊x / 2⌋₊, ⌊x⌋₊]`. -/
def cesaroWindowPsiChar {M : ℕ} (χ : DirichletCharacter ℂ M) (x : ℝ) : ℂ :=
  ((Finset.Icc ⌊x / 2⌋₊ ⌊x⌋₊).card : ℂ)⁻¹ *
    ∑ k ∈ Finset.Icc ⌊x / 2⌋₊ ⌊x⌋₊, Stage2DirichletAP.chebyshevPsiChar χ (k : ℝ)

/-- Cauchy–Schwarz second-moment bound for `cesaroWindowPsiChar`:
`‖cesaroWindowPsiChar χ x‖² ≤ |I|⁻¹ ∑_{k ∈ [⌊x/2⌋, ⌊x⌋]} ‖ψ(k, χ)‖²`. -/
theorem norm_cesaroWindowPsiChar_sq_le {M : ℕ} (χ : DirichletCharacter ℂ M) {x : ℝ} (hx : 2 ≤ x) :
    ‖cesaroWindowPsiChar χ x‖ ^ 2 ≤
      ((Finset.Icc ⌊x / 2⌋₊ ⌊x⌋₊).card : ℝ)⁻¹ *
        ∑ k ∈ Finset.Icc ⌊x / 2⌋₊ ⌊x⌋₊, ‖Stage2DirichletAP.chebyshevPsiChar χ (k : ℝ)‖ ^ 2 := by
  set I := Finset.Icc ⌊x / 2⌋₊ ⌊x⌋₊
  have hle : ⌊x / 2⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono (by linarith)
  have hcard_pos : (0 : ℝ) < (I.card : ℝ) := by
    have hne : I.Nonempty := ⟨⌊x / 2⌋₊, Finset.mem_Icc.mpr ⟨le_rfl, hle⟩⟩
    exact Nat.cast_pos.mpr hne.card_pos
  unfold cesaroWindowPsiChar
  rw [norm_mul, norm_inv, Complex.norm_natCast, mul_pow, inv_pow]
  have hcs := Stage2BehrendSieve.cauchy_schwarz_complex_card I
    (fun k => Stage2DirichletAP.chebyshevPsiChar χ (k : ℝ))
  calc ((I.card : ℝ) ^ 2)⁻¹ * ‖∑ k ∈ I, Stage2DirichletAP.chebyshevPsiChar χ (k : ℝ)‖ ^ 2
      ≤ ((I.card : ℝ) ^ 2)⁻¹ * ((I.card : ℝ) * ∑ k ∈ I, ‖Stage2DirichletAP.chebyshevPsiChar χ (k : ℝ)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (inv_nonneg.mpr (sq_nonneg _))
    _ = (I.card : ℝ)⁻¹ * ∑ k ∈ I, ‖Stage2DirichletAP.chebyshevPsiChar χ (k : ℝ)‖ ^ 2 := by
        field_simp [hcard_pos.ne']

open Classical in
/-- **Unconditional Barban–Davenport–Halberstam Twisted-Character Mean-Square Bound Across Auxiliary Primes**:
for EVERY `A > 0`, there exists `C > 0` such that for EVERY fixed primitive character `ψ : PChar`,
EVERY `x ≥ 16`, and EVERY `Q : ℕ` with `ψ.N * Q ≤ x / 2`, letting
`P := (Finset.Icc 1 Q).filter (fun q => q.Prime ∧ ¬ q ∣ ψ.N)`, BOTH the Chebyshev mean square
AND the Cesàro-1 mean square over all auxiliary primes `q ∈ P` and twisted characters `ψ χ_q`
(`χ ≠ 1`) are bounded by `C * (x * (ψ.N * Q) * (Real.log x)³ + x² / (Real.log x)^A)`. -/
theorem bdh_twisted_primes_mean_square_le {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ψ : PChar) (x : ℝ), 16 ≤ x → ∀ Q : ℕ, ((ψ.N * Q : ℕ) : ℝ) ≤ x / 2 →
        let P := (Finset.Icc 1 Q).filter (fun q => q.Prime ∧ ¬ q ∣ ψ.N)
        (∑ q ∈ P, ((ψ.N * q).totient : ℝ)⁻¹ *
            ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
              ‖Stage2DirichletAP.chebyshevPsiChar (twistedChar ψ.χ χ) x‖ ^ 2 ≤
          C * (x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A)) ∧
        (∑ q ∈ P, ((ψ.N * q).totient : ℝ)⁻¹ *
            ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
              ‖cesaroWindowPsiChar (twistedChar ψ.χ χ) x‖ ^ 2 ≤
          C * (x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A)) := by
  obtain ⟨C₀, hC₀, hbdh⟩ := Stage8BarbanDavenport.barban_davenport_halberstam_full hA
  set C : ℝ := C₀ * (2 : ℝ) ^ A
  have h2A_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ A := Real.one_le_rpow (by norm_num) hA.le
  have hC_pos : 0 < C := mul_pos hC₀ (by positivity)
  refine ⟨C, hC_pos, fun ψ x hx Q hQ => ?_⟩
  dsimp only
  set P := (Finset.Icc 1 Q).filter (fun q => q.Prime ∧ ¬ q ∣ ψ.N)
  have hx0 : 0 < x := by linarith
  have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hsum_P_le_bdh : ∀ t : ℝ, 4 ≤ t → ((ψ.N * Q : ℕ) : ℝ) ≤ t →
      ∑ q ∈ P, ((ψ.N * q).totient : ℝ)⁻¹ *
          ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            ‖Stage2DirichletAP.chebyshevPsiChar (twistedChar ψ.χ χ) t‖ ^ 2 ≤
        C₀ * (t * ((ψ.N * Q : ℕ) : ℝ) * (Real.log t) ^ 3 + t ^ 2 / (Real.log t) ^ A) := by
    intro t ht hQt
    have hstep1 :
        ∑ q ∈ P, ((ψ.N * q).totient : ℝ)⁻¹ *
            ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
              ‖Stage2DirichletAP.chebyshevPsiChar (twistedChar ψ.χ χ) t‖ ^ 2 ≤
          ∑ q ∈ P, Stage8BarbanDavenport.psiAPVariance (ψ.N * q) t := by
      refine Finset.sum_le_sum fun q hq => ?_
      have hmem := Finset.mem_filter.mp hq
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hmem.1).1
      have : NeZero q := ⟨by omega⟩
      have hcop : Nat.Coprime ψ.N q := ((Nat.Prime.coprime_iff_not_dvd hmem.2.1).mpr hmem.2.2).symm
      exact twisted_char_mean_square_le_psiAPVariance ψ hcop t
    have hinj : Set.InjOn (fun q : ℕ => ψ.N * q) (P : Set ℕ) :=
      fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left (NeZero.pos ψ.N) h
    have hsub : P.image (fun q => ψ.N * q) ⊆ Finset.Icc 1 (ψ.N * Q) := by
      intro M hM
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hM
      have hqI := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
      exact Finset.mem_Icc.mpr ⟨Nat.mul_pos (NeZero.pos ψ.N) (by omega),
        Nat.mul_le_mul_left ψ.N hqI.2⟩
    have hstep2 :
        ∑ q ∈ P, Stage8BarbanDavenport.psiAPVariance (ψ.N * q) t ≤
          ∑ M ∈ Finset.Icc 1 (ψ.N * Q), Stage8BarbanDavenport.psiAPVariance M t := by
      rw [← Finset.sum_image (f := fun M => Stage8BarbanDavenport.psiAPVariance M t) hinj]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun M _ _ =>
        Stage8BarbanDavenport.psiAPVariance_nonneg M t
    exact (hstep1.trans hstep2).trans (hbdh t ht (ψ.N * Q) hQt)
  -- Part 1: Pointwise at `t = x`
  have hpart1 :
      ∑ q ∈ P, ((ψ.N * q).totient : ℝ)⁻¹ *
          ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            ‖Stage2DirichletAP.chebyshevPsiChar (twistedChar ψ.χ χ) x‖ ^ 2 ≤
        C * (x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A) := by
    have h1 := hsum_P_le_bdh x (by linarith) (by linarith)
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    dsimp only [C]
    nlinarith
  -- Part 2: Cesàro-1 window average on `[⌊x / 2⌋₊, ⌊x⌋₊]`
  have hpart2 :
      ∑ q ∈ P, ((ψ.N * q).totient : ℝ)⁻¹ *
          ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            ‖cesaroWindowPsiChar (twistedChar ψ.χ χ) x‖ ^ 2 ≤
        C * (x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A) := by
    set I := Finset.Icc ⌊x / 2⌋₊ ⌊x⌋₊
    have hI_le : ⌊x / 2⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono (by linarith)
    have hI_pos : (0 : ℝ) < (I.card : ℝ) :=
      Nat.cast_pos.mpr (Finset.Nonempty.card_pos ⟨⌊x / 2⌋₊, Finset.mem_Icc.mpr ⟨le_rfl, hI_le⟩⟩)
    have hcs_sum :
        ∑ q ∈ P, ((ψ.N * q).totient : ℝ)⁻¹ *
            ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
              ‖cesaroWindowPsiChar (twistedChar ψ.χ χ) x‖ ^ 2 ≤
          (I.card : ℝ)⁻¹ *
            ∑ k ∈ I, ∑ q ∈ P, ((ψ.N * q).totient : ℝ)⁻¹ *
              ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
                ‖Stage2DirichletAP.chebyshevPsiChar (twistedChar ψ.χ χ) (k : ℝ)‖ ^ 2 := by
      calc ∑ q ∈ P, ((ψ.N * q).totient : ℝ)⁻¹ *
              ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
                ‖cesaroWindowPsiChar (twistedChar ψ.χ χ) x‖ ^ 2
          ≤ ∑ q ∈ P, ((ψ.N * q).totient : ℝ)⁻¹ *
              ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
                ((I.card : ℝ)⁻¹ * ∑ k ∈ I,
                  ‖Stage2DirichletAP.chebyshevPsiChar (twistedChar ψ.χ χ) (k : ℝ)‖ ^ 2) := by
            refine Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum fun χ _ => norm_cesaroWindowPsiChar_sq_le _ (by linarith))
              (inv_nonneg.mpr (Nat.cast_nonneg _))
        _ = (I.card : ℝ)⁻¹ *
              ∑ k ∈ I, ∑ q ∈ P, ((ψ.N * q).totient : ℝ)⁻¹ *
                ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
                  ‖Stage2DirichletAP.chebyshevPsiChar (twistedChar ψ.χ χ) (k : ℝ)‖ ^ 2 := by
            rw [Finset.mul_sum]
            have hR :
                ∑ k ∈ I, (I.card : ℝ)⁻¹ *
                    ∑ q ∈ P, ((ψ.N * q).totient : ℝ)⁻¹ *
                      ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
                        ‖Stage2DirichletAP.chebyshevPsiChar (twistedChar ψ.χ χ) (k : ℝ)‖ ^ 2 =
                  ∑ k ∈ I, ∑ q ∈ P, (I.card : ℝ)⁻¹ * (((ψ.N * q).totient : ℝ)⁻¹ *
                      ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
                        ‖Stage2DirichletAP.chebyshevPsiChar (twistedChar ψ.χ χ) (k : ℝ)‖ ^ 2) :=
              Finset.sum_congr rfl fun _ _ => Finset.mul_sum _ _ _
            rw [hR, Finset.sum_comm]
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
            ring
    have hper_k : ∀ k ∈ I,
        ∑ q ∈ P, ((ψ.N * q).totient : ℝ)⁻¹ *
            ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
              ‖Stage2DirichletAP.chebyshevPsiChar (twistedChar ψ.χ χ) (k : ℝ)‖ ^ 2 ≤
          C * (x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A) := by
      intro k hk
      have hkI := Finset.mem_Icc.mp hk
      have hfl_ge : 8 ≤ ⌊x / 2⌋₊ := Nat.le_floor (by norm_num; linarith)
      have hk4 : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 4 ≤ k)
      have hkx : (k : ℝ) ≤ x :=
        (by exact_mod_cast hkI.2 : (k : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans (Nat.floor_le hx0.le)
      have hQk : ((ψ.N * Q : ℕ) : ℝ) ≤ (k : ℝ) := by
        have hnat : ψ.N * Q ≤ ⌊x / 2⌋₊ := Nat.le_floor hQ
        exact_mod_cast hnat.trans hkI.1
      have hk_gt : x / 4 ≤ (k : ℝ) := by
        have hlt : x / 2 - 1 < (⌊x / 2⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one (x / 2)]
        have hk_ge : (⌊x / 2⌋₊ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkI.1
        linarith
      have hsqrt_le_k : Real.sqrt x ≤ (k : ℝ) := by
        have hsq : (Real.sqrt x) ^ 2 ≤ (x / 4) ^ 2 := by
          rw [Real.sq_sqrt hx0.le]; nlinarith
        exact (le_of_sq_le_sq hsq (by linarith)).trans hk_gt
      have hlogk_ge : Real.log x / 2 ≤ Real.log (k : ℝ) := by
        have h1 := Real.log_le_log (Real.sqrt_pos.mpr hx0) hsqrt_le_k
        rwa [Real.log_sqrt hx0.le] at h1
      have hlogk_le : Real.log (k : ℝ) ≤ Real.log x :=
        Real.log_le_log (by linarith) hkx
      have hlogk_pos : 0 < Real.log (k : ℝ) := by linarith
      have ht1 :
          (k : ℝ) * ((ψ.N * Q : ℕ) : ℝ) * (Real.log (k : ℝ)) ^ 3 ≤
            (2 : ℝ) ^ A * (x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3) := by
        have hbase : (k : ℝ) * ((ψ.N * Q : ℕ) : ℝ) * (Real.log (k : ℝ)) ^ 3 ≤
            x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 := by gcongr
        have hnn : 0 ≤ x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 := by positivity
        nlinarith
      have ht2 :
          (k : ℝ) ^ 2 / (Real.log (k : ℝ)) ^ A ≤
            (2 : ℝ) ^ A * (x ^ 2 / (Real.log x) ^ A) := by
        have hpow : (Real.log x / 2) ^ A = (Real.log x) ^ A / (2 : ℝ) ^ A :=
          Real.div_rpow hLx_pos.le (by norm_num) A
        calc (k : ℝ) ^ 2 / (Real.log (k : ℝ)) ^ A
            ≤ x ^ 2 / (Real.log x / 2) ^ A := by
              refine div_le_div₀ (sq_nonneg x) (pow_le_pow_left₀ (by linarith) hkx 2)
                (Real.rpow_pos_of_pos (by linarith) A)
                (Real.rpow_le_rpow (by linarith) hlogk_ge hA.le)
          _ = (2 : ℝ) ^ A * (x ^ 2 / (Real.log x) ^ A) := by
              rw [hpow]
              field_simp [(Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) A).ne',
                (Real.rpow_pos_of_pos hLx_pos A).ne']
      calc ∑ q ∈ P, ((ψ.N * q).totient : ℝ)⁻¹ *
              ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
                ‖Stage2DirichletAP.chebyshevPsiChar (twistedChar ψ.χ χ) (k : ℝ)‖ ^ 2
          ≤ C₀ * ((k : ℝ) * ((ψ.N * Q : ℕ) : ℝ) * (Real.log (k : ℝ)) ^ 3 +
              (k : ℝ) ^ 2 / (Real.log (k : ℝ)) ^ A) := hsum_P_le_bdh (k : ℝ) hk4 hQk
        _ ≤ C₀ * ((2 : ℝ) ^ A * (x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3) +
              (2 : ℝ) ^ A * (x ^ 2 / (Real.log x) ^ A)) :=
            mul_le_mul_of_nonneg_left (by linarith) hC₀.le
        _ = C * (x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A) := by
            dsimp only [C]; ring
    calc ∑ q ∈ P, ((ψ.N * q).totient : ℝ)⁻¹ *
            ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
              ‖cesaroWindowPsiChar (twistedChar ψ.χ χ) x‖ ^ 2
        ≤ (I.card : ℝ)⁻¹ *
            ∑ k ∈ I, ∑ q ∈ P, ((ψ.N * q).totient : ℝ)⁻¹ *
              ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
                ‖Stage2DirichletAP.chebyshevPsiChar (twistedChar ψ.χ χ) (k : ℝ)‖ ^ 2 := hcs_sum
      _ ≤ (I.card : ℝ)⁻¹ *
            ∑ _k ∈ I, (C * (x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper_k) (inv_nonneg.mpr hI_pos.le)
      _ = C * (x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hI_pos.ne', one_mul]
  exact ⟨hpart1, hpart2⟩

open Classical in
/-- **Concrete Twisted Character-Box Mean-Square Transfer (`twisted_box_mean_square_transfer`)**
(`0` assumptions!):
combining `Stage8BarbanDavenport.barban_davenport_halberstam_full` with Parseval + Markov averaging:
for EVERY `A > 0`, there exists `C > 0` such that for EVERY fixed primitive character `ψ : PChar`,
EVERY `x ≥ 16`, EVERY `Q : ℕ` with `ψ.N * Q ≤ x / 2`, and EVERY `δ ∈ (0, 1)`, letting
`P := (Finset.Icc 1 Q).filter (fun q => q.Prime ∧ ¬ q ∣ ψ.N)` and
`E := C * (x * (ψ.N * Q) * (Real.log x)³ + x² / (Real.log x)^A)`,
at least `(1 - δ) * |P|` auxiliary primes `q ∈ P` SIMULTANEOUSLY satisfy mean-square Chebyshev
AND Cesàro-1 bounds on all twisted characters `ψ χ_q` (`χ ≠ 1`):
`φ(ψ.N * q)⁻¹ ∑_{χ ≠ 1} ‖ψ(x, ψ χ_q)‖² ≤ (2 * E) / (δ * |P|)` AND
`φ(ψ.N * q)⁻¹ ∑_{χ ≠ 1} ‖cesaroWindowPsiChar (ψ χ_q) x‖² ≤ (2 * E) / (δ * |P|)`. -/
theorem twisted_box_mean_square_transfer {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ψ : PChar) (x : ℝ), 16 ≤ x → ∀ Q : ℕ, ((ψ.N * Q : ℕ) : ℝ) ≤ x / 2 →
        ∀ δ : ℝ, 0 < δ → δ < 1 →
          let P := (Finset.Icc 1 Q).filter (fun q => q.Prime ∧ ¬ q ∣ ψ.N)
          let E := C * (x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A)
          ∃ G ⊆ P,
            (1 - δ) * (P.card : ℝ) ≤ (G.card : ℝ) ∧
            ∀ q ∈ G,
              ((ψ.N * q).totient : ℝ)⁻¹ *
                  ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
                    ‖Stage2DirichletAP.chebyshevPsiChar (twistedChar ψ.χ χ) x‖ ^ 2 ≤
                (2 * E) / (δ * (P.card : ℝ)) ∧
              ((ψ.N * q).totient : ℝ)⁻¹ *
                  ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
                    ‖cesaroWindowPsiChar (twistedChar ψ.χ χ) x‖ ^ 2 ≤
                (2 * E) / (δ * (P.card : ℝ)) := by
  obtain ⟨C, hC, hbd⟩ := bdh_twisted_primes_mean_square_le hA
  refine ⟨C, hC, fun ψ x hx Q hQ δ hδ0 _hδ1 => ?_⟩
  dsimp only
  set P := (Finset.Icc 1 Q).filter (fun q => q.Prime ∧ ¬ q ∣ ψ.N)
  set E := C * (x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A)
  by_cases hP : P = ∅
  · refine ⟨∅, Finset.empty_subset P, ?_, fun _ h => absurd h (Finset.notMem_empty _)⟩
    rw [hP, Finset.card_empty, Nat.cast_zero, mul_zero]
  · have hP_pos : (0 : ℝ) < (P.card : ℝ) :=
      Nat.cast_pos.mpr (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hP))
    have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hE_pos : 0 < E := by
      dsimp only [E]
      have h1 : 0 ≤ x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 := by positivity
      have h2 : 0 < x ^ 2 / (Real.log x) ^ A := div_pos (by positivity) (Real.rpow_pos_of_pos hLx_pos A)
      exact mul_pos hC (by linarith)
    set M_psi : ℕ → ℝ := fun q =>
      ((ψ.N * q).totient : ℝ)⁻¹ *
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ‖Stage2DirichletAP.chebyshevPsiChar (twistedChar ψ.χ χ) x‖ ^ 2
    set M_ces : ℕ → ℝ := fun q =>
      ((ψ.N * q).totient : ℝ)⁻¹ *
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ‖cesaroWindowPsiChar (twistedChar ψ.χ χ) x‖ ^ 2
    have hM_psi_nn : ∀ q : ℕ, 0 ≤ M_psi q := fun q =>
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hM_ces_nn : ∀ q : ℕ, 0 ≤ M_ces q := fun q =>
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have ⟨h1, h2⟩ := hbd ψ x hx Q hQ
    have hsum_tot : ∑ q ∈ P, (M_psi q + M_ces q) ≤ 2 * E := by
      rw [Finset.sum_add_distrib]; linarith
    set T : ℝ := (2 * E) / (δ * (P.card : ℝ))
    have hT_pos : 0 < T := div_pos (by linarith) (mul_pos hδ0 hP_pos)
    set Bad := P.filter (fun q => T < M_psi q + M_ces q)
    set Good := P.filter (fun q => M_psi q + M_ces q ≤ T)
    have hBad_le : (Bad.card : ℝ) ≤ δ * (P.card : ℝ) := by
      have hm : (Bad.card : ℝ) * T ≤ 2 * E := by
        calc (Bad.card : ℝ) * T
            = ∑ _q ∈ Bad, T := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ q ∈ Bad, (M_psi q + M_ces q) :=
              Finset.sum_le_sum fun q hq => (Finset.mem_filter.mp hq).2.le
          _ ≤ ∑ q ∈ P, (M_psi q + M_ces q) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun q _ _ =>
                add_nonneg (hM_psi_nn q) (hM_ces_nn q)
          _ ≤ 2 * E := hsum_tot
      have hmul : (Bad.card : ℝ) * T ≤ (δ * (P.card : ℝ)) * T := by
        calc (Bad.card : ℝ) * T ≤ 2 * E := hm
          _ = (δ * (P.card : ℝ)) * T := by
              dsimp only [T]; field_simp [hδ0.ne', hP_pos.ne']
      exact le_of_mul_le_mul_right hmul hT_pos
    have hpart : (Good.card : ℝ) + (Bad.card : ℝ) = (P.card : ℝ) := by
      have hBad_eq : Bad = P.filter (fun q => ¬ M_psi q + M_ces q ≤ T) := by
        ext q; simp only [Bad, Finset.mem_filter, not_le]
      have hnat : Good.card + Bad.card = P.card := by
        rw [hBad_eq]; exact Finset.card_filter_add_card_filter_not _
      exact_mod_cast hnat
    refine ⟨Good, Finset.filter_subset _ _, by linarith, fun q hq => ?_⟩
    have hle := (Finset.mem_filter.mp hq).2
    exact ⟨by linarith [hM_ces_nn q], by linarith [hM_psi_nn q]⟩

open Classical in
/-- **Coupled Zero-Free Box + Twisted Mean-Square Transfer (Feeding Pillar 1 `MeanSquareBounds`)**:
combines `twisted_box_mean_square_transfer` with `ZeroDensityWindow.count_bad_of_zeroDensityBox`
to extract auxiliary primes `q ∈ P` (`q > ψ.N`) that SIMULTANEOUSLY satisfy:
1. both Chebyshev and Cesàro-1 twisted mean-square bounds on all `ψ χ_q` (`χ ≠ 1`), AND
2. `ZeroDensityWindow.ZeroFreeBox (ψ.N * Q)` for EVERY primitive character of conductor `ψ.N * q`. -/
theorem twisted_box_zero_free_and_mean_square_transfer {A C_zd : ℝ} (hA : 0 < A)
    (hZD : ZeroDensityWindow.ZeroDensityBoxBound C_zd) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ψ : PChar) (x : ℝ), 16 ≤ x → ∀ Q : ℕ, 3 ≤ ((ψ.N * Q : ℕ) : ℝ) →
        ((ψ.N * Q : ℕ) : ℝ) ≤ x / 2 →
        ∀ δ : ℝ, 0 < δ → δ < 1 →
          let P := (Finset.Icc 1 Q).filter (fun q => q.Prime ∧ ¬ q ∣ ψ.N ∧ ψ.N < q)
          let E := C * (x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A)
          ∃ G ⊆ P,
            (1 - δ) * (P.card : ℝ) - max C_zd 0 * ((ψ.N * Q : ℕ) : ℝ) ^ (1 / 4 : ℝ) ≤ (G.card : ℝ) ∧
            ∀ q ∈ G,
              (((ψ.N * q).totient : ℝ)⁻¹ *
                  ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
                    ‖Stage2DirichletAP.chebyshevPsiChar (twistedChar ψ.χ χ) x‖ ^ 2 ≤
                (2 * E) / (δ * (P.card : ℝ))) ∧
              (((ψ.N * q).totient : ℝ)⁻¹ *
                  ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
                    ‖cesaroWindowPsiChar (twistedChar ψ.χ χ) x‖ ^ 2 ≤
                (2 * E) / (δ * (P.card : ℝ))) ∧
              (∀ [NeZero (ψ.N * q)] (η : DirichletCharacter ℂ (ψ.N * q)),
                η.IsPrimitive → ZeroDensityWindow.ZeroFreeBox ((ψ.N * Q : ℕ) : ℝ) η) := by
  obtain ⟨C, hC, hbd⟩ := bdh_twisted_primes_mean_square_le hA
  refine ⟨C, hC, fun ψ x hx Q hQ3 hQx δ hδ0 _hδ1 => ?_⟩
  dsimp only
  set P₀ := (Finset.Icc 1 Q).filter (fun q => q.Prime ∧ ¬ q ∣ ψ.N)
  set P := (Finset.Icc 1 Q).filter (fun q => q.Prime ∧ ¬ q ∣ ψ.N ∧ ψ.N < q)
  set E := C * (x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A)
  have hP_sub_P₀ : P ⊆ P₀ := fun q hq => by
    simp only [P, P₀, Finset.mem_filter] at hq ⊢
    exact ⟨hq.1, hq.2.1, hq.2.2.1⟩
  by_cases hP : P = ∅
  · refine ⟨∅, Finset.empty_subset P, ?_, fun _ h => absurd h (Finset.notMem_empty _)⟩
    rw [hP, Finset.card_empty, Nat.cast_zero, mul_zero, zero_sub]
    have hnn : 0 ≤ max C_zd 0 * ((ψ.N * Q : ℕ) : ℝ) ^ (1 / 4 : ℝ) :=
      mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    linarith
  · have hP_pos : (0 : ℝ) < (P.card : ℝ) :=
      Nat.cast_pos.mpr (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hP))
    have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hE_pos : 0 < E := by
      dsimp only [E]
      have h1 : 0 ≤ x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 := by positivity
      have h2 : 0 < x ^ 2 / (Real.log x) ^ A := div_pos (by positivity) (Real.rpow_pos_of_pos hLx_pos A)
      exact mul_pos hC (by linarith)
    set M_psi : ℕ → ℝ := fun q =>
      ((ψ.N * q).totient : ℝ)⁻¹ *
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ‖Stage2DirichletAP.chebyshevPsiChar (twistedChar ψ.χ χ) x‖ ^ 2
    set M_ces : ℕ → ℝ := fun q =>
      ((ψ.N * q).totient : ℝ)⁻¹ *
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ‖cesaroWindowPsiChar (twistedChar ψ.χ χ) x‖ ^ 2
    have hM_psi_nn : ∀ q : ℕ, 0 ≤ M_psi q := fun q =>
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hM_ces_nn : ∀ q : ℕ, 0 ≤ M_ces q := fun q =>
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have ⟨h1, h2⟩ := hbd ψ x hx Q hQx
    have hsum_P : ∑ q ∈ P, (M_psi q + M_ces q) ≤ 2 * E := by
      have hsub_le : ∑ q ∈ P, (M_psi q + M_ces q) ≤ ∑ q ∈ P₀, (M_psi q + M_ces q) :=
        Finset.sum_le_sum_of_subset_of_nonneg hP_sub_P₀ fun q _ _ =>
          add_nonneg (hM_psi_nn q) (hM_ces_nn q)
      rw [Finset.sum_add_distrib] at hsub_le
      have hP₀_eq : ∑ q ∈ P₀, (M_psi q + M_ces q) = ∑ q ∈ P₀, M_psi q + ∑ q ∈ P₀, M_ces q :=
        Finset.sum_add_distrib
      rw [hP₀_eq] at hsub_le
      linarith [Finset.sum_add_distrib (s := P) (f := M_psi) (g := M_ces)]
    set T : ℝ := (2 * E) / (δ * (P.card : ℝ))
    have hT_pos : 0 < T := div_pos (by linarith) (mul_pos hδ0 hP_pos)
    set BadMS := P.filter (fun q => T < M_psi q + M_ces q)
    set BadZF := P.filter (fun q =>
      ∃ (_ : NeZero (ψ.N * q)) (η : DirichletCharacter ℂ (ψ.N * q)),
        η.IsPrimitive ∧ ¬ ZeroDensityWindow.ZeroFreeBox ((ψ.N * Q : ℕ) : ℝ) η)
    have hBadMS_le : (BadMS.card : ℝ) ≤ δ * (P.card : ℝ) := by
      have hm : (BadMS.card : ℝ) * T ≤ 2 * E := by
        calc (BadMS.card : ℝ) * T
            = ∑ _q ∈ BadMS, T := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ q ∈ BadMS, (M_psi q + M_ces q) :=
              Finset.sum_le_sum fun q hq => (Finset.mem_filter.mp hq).2.le
          _ ≤ ∑ q ∈ P, (M_psi q + M_ces q) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun q _ _ =>
                add_nonneg (hM_psi_nn q) (hM_ces_nn q)
          _ ≤ 2 * E := hsum_P
      have hmul : (BadMS.card : ℝ) * T ≤ (δ * (P.card : ℝ)) * T := by
        calc (BadMS.card : ℝ) * T ≤ 2 * E := hm
          _ = (δ * (P.card : ℝ)) * T := by
              dsimp only [T]; field_simp [hδ0.ne', hP_pos.ne']
      exact le_of_mul_le_mul_right hmul hT_pos
    have hBadZF_le : (BadZF.card : ℝ) ≤ max C_zd 0 * ((ψ.N * Q : ℕ) : ℝ) ^ (1 / 4 : ℝ) := by
      refine ZeroDensityWindow.count_bad_of_zeroDensityBox hZD ((ψ.N * Q : ℕ) : ℝ) (ψ.N : ℝ)
        BadZF hQ3 ?_
      intro q hq
      have hmem := Finset.mem_filter.mp hq
      have hqP := Finset.mem_filter.mp hmem.1
      obtain ⟨hne, η, hprim, hnz⟩ := hmem.2
      refine ⟨hqP.2.1, by exact_mod_cast hqP.2.2.2, ψ.N, hne, η, le_rfl, ?_, hprim, hnz⟩
      exact_mod_cast Nat.mul_le_mul_left ψ.N (Finset.mem_Icc.mp hqP.1).2
    set G := P \ (BadMS ∪ BadZF)
    have hG_card : (1 - δ) * (P.card : ℝ) - max C_zd 0 * ((ψ.N * Q : ℕ) : ℝ) ^ (1 / 4 : ℝ) ≤ (G.card : ℝ) := by
      have hunion : (BadMS ∪ BadZF).card ≤ BadMS.card + BadZF.card := Finset.card_union_le _ _
      have hsub_u : BadMS ∪ BadZF ⊆ P :=
        Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      have hadd : G.card + (BadMS ∪ BadZF).card = P.card :=
        Finset.card_sdiff_add_card_eq_card hsub_u
      have haddR : (G.card : ℝ) + ((BadMS ∪ BadZF).card : ℝ) = (P.card : ℝ) := by exact_mod_cast hadd
      have hunionR : ((BadMS ∪ BadZF).card : ℝ) ≤ (BadMS.card : ℝ) + (BadZF.card : ℝ) := by
        exact_mod_cast hunion
      linarith
    refine ⟨G, Finset.sdiff_subset, hG_card, fun q hq => ?_⟩
    have hmem := Finset.mem_sdiff.mp hq
    have hnotMS : q ∉ BadMS := fun h => hmem.2 (Finset.mem_union_left _ h)
    have hnotZF : q ∉ BadZF := fun h => hmem.2 (Finset.mem_union_right _ h)
    have hms_le : M_psi q + M_ces q ≤ T := by
      by_contra hgt
      exact hnotMS (Finset.mem_filter.mpr ⟨hmem.1, lt_of_not_ge hgt⟩)
    refine ⟨by linarith [hM_ces_nn q], by linarith [hM_psi_nn q], fun [hne : NeZero (ψ.N * q)] η hprim => ?_⟩
    by_contra hnz
    exact hnotZF (Finset.mem_filter.mpr ⟨hmem.1, hne, η, hprim, hnz⟩)

end Stage11SecondMomentFrame
end RHDirect

end

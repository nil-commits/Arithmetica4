import Mathlib.RingTheory.FormalGroup.Basic
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.ENat.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr

/-!
# RHDirect.CFT.FormalGroups

Formal Group Laws & Lubin–Tate Formal Modules consolidated from
`GroundTheory.LocalFields.FormalGroups.*`:

1. **Truncation & Fixed Points** (`Truncation`): order bounds for substitution and
   Banach-style unique fixed points in `MvPowerSeries`.
2. **Formal Group Inverses** (`Inverse`): formal inverse power series `inv F` and
   `AddGroup` / `AddCommGroup` structure on `F.Point σ`.
3. **Homomorphisms & Isomorphisms** (`Basics`): `Hom F G`, `AddCommGroup (Hom F G)`,
   `Ring (Hom F F)`, `linearCoeff`, `Iso F G`, and `Iso.ofIsUnit`.
4. **Lubin–Tate Series & Lifting** (`LubinTate`): `IsLubinTateSeries`, `lubinTateLift`,
   existence and uniqueness of commuting multivariate series.
5. **Lubin–Tate Formal Group Law & Formal Module** (`LubinTateGroup`):
   `lubinTateFormalGroup`, `lubinTateEndo`, `existsUnique_formalGroup`,
   `lubinTateHom`, `lubinTateEndRingHom`, `lubinTateFormalModule`, `lubinTateIso`.
6. **Frobenius Twist & Adic Approximation** (`FrobeniusTwist`):
   `exists_limit_of_approx`, `exists_eq_zero_of_approx`, `exists_sub_mul_eq`,
   `exists_units_eq_mul`, `surjective_sub_self`, `surjective_div_self`.
7. **Twisted Lifts** (`TwistedLift`): base change of lifts and `IsTwistedLift`
   existence, uniqueness, and composition.
8. **Isomorphisms Over Unramified Extensions** (`OverUnramified`):
   `Hom.map`, `bijective_twistOp`, `exists_isTwistedLift`, and
   `exists_iso_lubinTateFormalGroup` comparing Lubin–Tate formal groups for two uniformizers.
9. **Adic Convergence on the Maximal Ideal** (`AdicConvergence`):
   `existsUnique_evalAdic`, `evalAdic`, `existsUnique_evalAdic₂`, `evalFormalGroup`,
   `evalMaximalIdeal`, `evalFormalGroupMaximalIdeal`, and `evalFormalGroupMaximalIdeal_sub_add_mem`.
-/

namespace RHDirect.CFT.FormalGroups

/-! ## Section 1: Truncation & Fixed Points -/

section Truncation

open MvPowerSeries

section Subst

variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem le_order_subst_sub_subst {a : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) {f g : MvPowerSeries σ R} {n : ℕ∞}
    (h : n ≤ order (f - g)) : n ≤ order (subst a f - subst a g) := by
  rw [← subst_sub ha]
  refine le_trans ?_ (le_order_subst ha (f - g))
  have h1 : 1 ≤ ⨅ i, (a i).order :=
    le_iInf fun i => one_le_order_iff_constCoeff_eq_zero.2 (ha0 i)
  calc n ≤ 1 * order (f - g) := by simpa using h
    _ ≤ _ := by gcongr

private def Close (n k : ℕ∞) (u v : MvPowerSeries τ S) : Prop :=
  k ≤ order u ∧ k ≤ order v ∧ n + k ≤ order (u - v) + 1

private lemma close_one (n : ℕ∞) : Close n 0 (1 : MvPowerSeries τ S) 1 := by
  refine ⟨by simp, by simp, ?_⟩
  simp

private lemma close_mul {n k l : ℕ∞} {u v u' v' : MvPowerSeries τ S} (h : Close n k u v)
    (h' : Close n l u' v') : Close n (k + l) (u * u') (v * v') := by
  obtain ⟨hu, hv, huv⟩ := h
  obtain ⟨hu', hv', huv'⟩ := h'
  refine ⟨(add_le_add hu hu').trans (le_order_mul), (add_le_add hv hv').trans (le_order_mul), ?_⟩
  have e : u * u' - v * v' = (u - v) * u' + v * (u' - v') := by ring
  rw [e]
  refine le_trans ?_ (add_le_add min_order_le_add le_rfl)
  rw [← min_add_add_right]
  refine le_min ?_ ?_
  · calc n + (k + l) = (n + k) + l := by rw [add_assoc]
      _ ≤ (order (u - v) + 1) + order u' := add_le_add huv hu'
      _ = (order (u - v) + order u') + 1 := by rw [add_right_comm]
      _ ≤ order ((u - v) * u') + 1 := add_le_add le_order_mul le_rfl
  · calc n + (k + l) = k + (n + l) := by rw [add_left_comm]
      _ ≤ order v + (order (u' - v') + 1) := add_le_add hv huv'
      _ = (order v + order (u' - v')) + 1 := by rw [add_assoc]
      _ ≤ order (v * (u' - v')) + 1 := add_le_add le_order_mul le_rfl

private lemma close_pow {n k : ℕ∞} {u v : MvPowerSeries τ S} (h : Close n k u v) (m : ℕ) :
    Close n (m * k) (u ^ m) (v ^ m) := by
  induction m with
  | zero => simpa using close_one (τ := τ) (S := S) n
  | succ m ih =>
    have := close_mul ih h
    rw [pow_succ, pow_succ]
    convert this using 1
    push_cast
    ring

private lemma close_prod {ι : Type*} (s : Finset ι) {n : ℕ∞} {k : ι → ℕ∞}
    {u v : ι → MvPowerSeries τ S} (h : ∀ i ∈ s, Close n (k i) (u i) (v i)) :
    Close n (∑ i ∈ s, k i) (∏ i ∈ s, u i) (∏ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using close_one (τ := τ) (S := S) n
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi]
    exact close_mul (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

private lemma close_monomial {n : ℕ∞} {a b : σ → MvPowerSeries τ S}
    (h : ∀ i, Close n 1 (a i) (b i)) (d : σ →₀ ℕ) :
    Close n (d.degree : ℕ∞) (d.prod fun s e => a s ^ e) (d.prod fun s e => b s ^ e) := by
  have := close_prod d.support (k := fun i => (d i : ℕ∞) * 1) (u := fun i => a i ^ d i)
    (v := fun i => b i ^ d i) (fun i _ => close_pow (h i) (d i))
  simpa [Finsupp.prod, Finsupp.degree_apply] using this

theorem add_le_order_subst_sub_subst {a b : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (hb : HasSubst b) (ha0 : ∀ i, constantCoeff (a i) = 0)
    (hb0 : ∀ i, constantCoeff (b i) = 0) {n : ℕ∞} (hab : ∀ i, n ≤ order (a i - b i))
    {f : MvPowerSeries σ R} {m : ℕ∞} (hf : m ≤ order f) :
    n + m ≤ order (subst a f - subst b f) + 1 := by
  have hclose : ∀ i, Close n 1 (a i) (b i) := fun i =>
    ⟨one_le_order_iff_constCoeff_eq_zero.2 (ha0 i),
      one_le_order_iff_constCoeff_eq_zero.2 (hb0 i), add_le_add (hab i) le_rfl⟩
  have hcoeff : ∀ e : τ →₀ ℕ, (e.degree : ℕ∞) + 1 < n + m →
      coeff e (subst a f - subst b f) = 0 := by
    intro e he
    rw [map_sub, coeff_subst ha, coeff_subst hb,
      ← finsum_sub_distrib (coeff_subst_finite ha f e) (coeff_subst_finite hb f e)]
    refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
    by_cases hd : coeff d f = 0
    · simp [hd]
    rw [← smul_sub, ← map_sub]
    obtain ⟨-, -, hdc⟩ := close_monomial hclose d
    have hmd : m ≤ (d.degree : ℕ∞) := hf.trans (order_le hd)
    have : (e.degree : ℕ∞) + 1 < order ((d.prod fun s e => a s ^ e) -
        (d.prod fun s e => b s ^ e)) + 1 :=
      he.trans_le ((add_le_add le_rfl hmd).trans hdc)
    rw [coeff_of_lt_order ((ENat.add_lt_add_iff_right ENat.one_ne_top).1 this), smul_zero]
  by_contra hlt
  rw [not_le] at hlt
  have hfin : (order (subst a f - subst b f)).toNat = order (subst a f - subst b f) := by
    refine ENat.natCast_toNat fun htop => ?_
    rw [htop] at hlt
    simp at hlt
  obtain ⟨e, he, hdeg⟩ := exists_coeff_ne_zero_and_order hfin
  exact he (hcoeff e (by rw [hdeg]; exact hlt))

end Subst

section FixedPoint

variable {σ R : Type*} [CommRing R]

private theorem le_order_sub_iff (f g : MvPowerSeries σ R) (n : ℕ) :
    (n : ℕ∞) ≤ (f - g).order ↔ ∀ d : σ →₀ ℕ, d.degree < n → coeff d f = coeff d g := by
  constructor
  · intro h d hd
    have h0 : coeff d (f - g) = 0 :=
      coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)
    rwa [map_sub, sub_eq_zero] at h0
  · intro h
    refine nat_le_order fun d hd => ?_
    rw [map_sub, h d hd, sub_self]

theorem existsUnique_fixedPoint (Φ : MvPowerSeries σ R → MvPowerSeries σ R)
    (hΦ : ∀ f g : MvPowerSeries σ R, ∀ n : ℕ, (n : ℕ∞) ≤ order (f - g) →
      ((n + 1 : ℕ) : ℕ∞) ≤ order (Φ f - Φ g)) :
    ∃! f, Φ f = f := by
  simp only [le_order_sub_iff] at hΦ
  have step : ∀ (k : ℕ) (g : MvPowerSeries σ R) (d : σ →₀ ℕ), d.degree < k →
      MvPowerSeries.coeff d (Φ^[k] g) = MvPowerSeries.coeff d (Φ^[k] 0) := by
    intro k g
    induction k with
    | zero => intro d hd; exact absurd hd (Nat.not_lt_zero _)
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hΦ _ _ k ih
  let f : MvPowerSeries σ R := fun d => MvPowerSeries.coeff d (Φ^[d.degree + 1] 0)
  have hf : ∀ d : σ →₀ ℕ,
      MvPowerSeries.coeff d f = MvPowerSeries.coeff d (Φ^[d.degree + 1] 0) := fun _ => rfl
  have approx : ∀ (k : ℕ) (d : σ →₀ ℕ), d.degree < k →
      MvPowerSeries.coeff d f = MvPowerSeries.coeff d (Φ^[k] 0) := by
    intro k d hd
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hd)
    rw [hf, Function.iterate_add_apply Φ (Nat.succ _) m]
    exact (step _ _ d (Nat.lt_succ_self _)).symm
  refine ⟨f, ?_, ?_⟩
  · ext d
    rw [hΦ f _ d.degree (approx _) d (Nat.lt_succ_self _), hf, Function.iterate_succ_apply']
  · intro g hg
    ext d
    rw [hf, ← step _ g d (Nat.lt_succ_self _), Function.iterate_fixed hg]

end FixedPoint

end Truncation

/-! ## Section 2: Formal Group Inverses -/

section Inverse

open MvPowerSeries

variable {R : Type*} [CommRing R] (F : FormalGroup R)

noncomputable def higher : MvPowerSeries (Fin 2) R :=
  F.toPowerSeries - X 0 - X 1

theorem toPowerSeries_eq_X_add_X_add_higher : F.toPowerSeries = X 0 + X 1 + higher F := by
  simp [higher]

theorem two_le_order_higher : (2 : ℕ∞) ≤ order (higher F) := by
  refine nat_le_order fun d hd => ?_
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℕ, d = Finsupp.single 0 a + Finsupp.single 1 b :=
    ⟨d 0, d 1, by ext i; fin_cases i <;> simp⟩
  have hab : a + b < 2 := by simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hd
  have h01 : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro h
    have := congrArg (fun d => d 0) h
    simp at this
  have ha : a < 2 := by omega
  have hb : b < 2 := by omega
  interval_cases a <;> interval_cases b <;> simp_all [higher, coeff_X, F.lin_coeff_X,
    F.lin_coeff_Y, F.zero_constantCoeff, Ne.symm h01]

theorem constantCoeff_higher : constantCoeff (higher F) = 0 :=
  one_le_order_iff_constCoeff_eq_zero.1 (le_trans (by norm_num) (two_le_order_higher F))

theorem subst_eq_add_add_subst_higher {τ : Type*} {a b : MvPowerSeries τ R}
    (hab : HasSubst ![a, b]) :
    subst ![a, b] F.toPowerSeries = a + b + subst ![a, b] (higher F) := by
  conv_lhs => rw [toPowerSeries_eq_X_add_X_add_higher F]
  rw [subst_add hab, subst_add hab, subst_X hab, subst_X hab]
  simp

lemma hasSubst_pair {τ : Type*} {a b : MvPowerSeries τ R} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) : HasSubst ![a, b] :=
  hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simpa

private noncomputable def invStep (g : MvPowerSeries Unit R) : MvPowerSeries Unit R :=
  -X () - subst ![X (), g - C (constantCoeff g)] (higher F)

private lemma constantCoeff_sub_C (g : MvPowerSeries Unit R) :
    constantCoeff (g - C (constantCoeff g)) = 0 := by simp

private lemma invStep_contract (f g : MvPowerSeries Unit R) (n : ℕ)
    (h : (n : ℕ∞) ≤ order (f - g)) :
    ((n + 1 : ℕ) : ℕ∞) ≤ order (invStep F f - invStep F g) := by
  have hX : constantCoeff (X () : MvPowerSeries Unit R) = 0 := by simp
  have key := add_le_order_subst_sub_subst (R := R) (m := 2) (n := (n : ℕ∞))
    (hasSubst_pair hX (constantCoeff_sub_C f)) (hasSubst_pair hX (constantCoeff_sub_C g))
    (fun i => by fin_cases i <;> simp) (fun i => by fin_cases i <;> simp) ?_
    (two_le_order_higher F)
  · have e : invStep F f - invStep F g = -(subst ![X (), f - C (constantCoeff f)] (higher F) -
        subst ![X (), g - C (constantCoeff g)] (higher F)) := by
      simp only [invStep]; ring
    rw [e, order_neg]
    have : ((n + 1 : ℕ) : ℕ∞) + 1 = (n : ℕ∞) + 2 := by push_cast; ring
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 (this ▸ key)
  · intro i
    fin_cases i
    · simp
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · simp [hn]
      · have h0 : constantCoeff (f - g) = 0 := by
          rw [← coeff_zero_eq_constantCoeff_apply]
          exact coeff_of_lt_order (lt_of_lt_of_le (by simpa using hn) h)
        rw [map_sub, sub_eq_zero] at h0
        rw [h0]
        simpa using h

private lemma existsUnique_invStep : ∃! g, invStep F g = g :=
  existsUnique_fixedPoint _ (invStep_contract F)

noncomputable def inv : PowerSeries R :=
  (existsUnique_invStep F).exists.choose

private lemma invStep_inv : invStep F (inv F) = inv F :=
  (existsUnique_invStep F).exists.choose_spec

private lemma constantCoeff_invStep (g : MvPowerSeries Unit R) :
    constantCoeff (invStep F g) = 0 := by
  have hX : constantCoeff (X () : MvPowerSeries Unit R) = 0 := by simp
  rw [invStep, map_sub, map_neg, hX,
    constantCoeff_subst_eq_zero (hasSubst_pair hX (constantCoeff_sub_C g))
      (fun i => by fin_cases i <;> simp) (constantCoeff_higher F)]
  simp

theorem constantCoeff_inv : PowerSeries.constantCoeff (inv F) = 0 := by
  rw [← invStep_inv F]
  exact constantCoeff_invStep F _

theorem hasSubst_inv : PowerSeries.HasSubst (inv F) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_inv F)

private lemma invStep_of_constantCoeff_eq_zero {g : MvPowerSeries Unit R}
    (hg : constantCoeff g = 0) : invStep F g = -X () - subst ![X (), g] (higher F) := by
  simp [invStep, hg]

theorem subst_X_inv :
    subst ![PowerSeries.X, inv F] F.toPowerSeries = (0 : PowerSeries R) := by
  have hX : constantCoeff (X () : MvPowerSeries Unit R) = 0 := by simp
  have hi : constantCoeff (inv F : MvPowerSeries Unit R) = 0 := constantCoeff_inv F
  have := invStep_inv F
  rw [invStep_of_constantCoeff_eq_zero F hi] at this
  change subst ![X (), (inv F : MvPowerSeries Unit R)] F.toPowerSeries = 0
  rw [subst_eq_add_add_subst_higher F (hasSubst_pair hX hi)]
  linear_combination (-1 : MvPowerSeries Unit R) * this

theorem eq_inv_of_subst_eq_zero {g : PowerSeries R} (hg : PowerSeries.constantCoeff g = 0)
    (h : subst ![PowerSeries.X, g] F.toPowerSeries = (0 : PowerSeries R)) : g = inv F := by
  have hX : constantCoeff (X () : MvPowerSeries Unit R) = 0 := by simp
  have hg' : constantCoeff (g : MvPowerSeries Unit R) = 0 := hg
  change subst ![X (), (g : MvPowerSeries Unit R)] F.toPowerSeries = 0 at h
  rw [subst_eq_add_add_subst_higher F (hasSubst_pair hX hg')] at h
  have hfix : invStep F g = g := by
    rw [invStep_of_constantCoeff_eq_zero F hg']
    linear_combination (-1 : MvPowerSeries Unit R) * h
  exact (existsUnique_invStep F).unique hfix (invStep_inv F)

theorem subst_subst_pair {σ : Type*} {g h : PowerSeries R} (hgh : HasSubst ![g, h])
    {x : MvPowerSeries σ R} (hx : PowerSeries.HasSubst x) (G : MvPowerSeries (Fin 2) R) :
    PowerSeries.subst x (subst ![g, h] G : PowerSeries R) =
      subst ![PowerSeries.subst x g, PowerSeries.subst x h] G := by
  have hx' : HasSubst (fun _ : Unit => x) := PowerSeries.hasSubst_iff.mp hx
  rw [PowerSeries.subst_def, subst_comp_subst_apply hgh hx']
  congr 1
  funext s
  fin_cases s <;> rfl

variable {σ : Type*}

noncomputable instance : Neg (F.Point σ) where
  neg x := ⟨PowerSeries.subst x.val (inv F), by
    simpa [PowerSeries.coe_substAlgHom] using (hasSubst_inv F).comp x.prop⟩

theorem neg_point_val (x : F.Point σ) : (-x).val = PowerSeries.subst x.val (inv F) := rfl

private lemma add_neg_point (x : F.Point σ) : x + -x = 0 := by
  apply Subtype.ext
  have hX : constantCoeff (PowerSeries.X : PowerSeries R) = 0 := PowerSeries.constantCoeff_X
  have h := congrArg (PowerSeries.subst x.val) (subst_X_inv F)
  rw [subst_subst_pair (hasSubst_pair hX (constantCoeff_inv F)) x.prop,
    PowerSeries.subst_X x.prop] at h
  rw [FormalGroup.add_apply, neg_point_val, h]
  rw [← PowerSeries.coe_substAlgHom x.prop, map_zero]
  rfl

noncomputable instance instAddGroupPoint : AddGroup (F.Point σ) :=
  { (inferInstance : AddMonoid (F.Point σ)) with
    neg := Neg.neg
    zsmul := zsmulRec
    neg_add_cancel := fun x => by
      have h1 := add_neg_point F x
      have h2 := add_neg_point F (-x)
      have hx : x = -(-x) :=
        calc x = x + 0 := (add_zero x).symm
          _ = x + (-x + -(-x)) := by rw [h2]
          _ = (x + -x) + -(-x) := (add_assoc _ _ _).symm
          _ = -(-x) := by rw [h1, zero_add]
      calc -x + x = -x + -(-x) := congrArg (-x + ·) hx
        _ = 0 := h2 }

noncomputable instance instAddCommGroupPoint [F.IsComm] : AddCommGroup (F.Point σ) :=
  { instAddGroupPoint F with
    add_comm := fun x y => Subtype.ext (F.comm' x.prop y.prop) }

end Inverse

/-! ## Section 3: Homomorphisms, Endomorphism Ring, and Isomorphisms -/

section Basics

open MvPowerSeries

variable {R : Type*} [CommRing R]

theorem hasSubst_powerSeries_subst {τ : Type*} {x : MvPowerSeries τ R}
    (hx : PowerSeries.HasSubst x) {φ : PowerSeries R} (hφ : PowerSeries.HasSubst φ) :
    PowerSeries.HasSubst (PowerSeries.subst x φ) := by
  simpa [PowerSeries.coe_substAlgHom] using hφ.comp hx

theorem subst_powerSeries_subst {τ υ : Type*} {a : MvPowerSeries τ R}
    (ha : PowerSeries.HasSubst a) {b : τ → MvPowerSeries υ R} (hb : HasSubst b)
    (φ : PowerSeries R) :
    subst b (PowerSeries.subst a φ) = PowerSeries.subst (subst b a) φ := by
  have ha' : HasSubst (fun _ : Unit => a) := PowerSeries.hasSubst_iff.mp ha
  rw [PowerSeries.subst_def, PowerSeries.subst_def, subst_comp_subst_apply ha' hb]

theorem subst_X_X (f : MvPowerSeries (Fin 2) R) : subst ![X 0, X 1] f = f := by
  have : (![X 0, X 1] : Fin 2 → MvPowerSeries (Fin 2) R) = X := by
    funext i; fin_cases i <;> rfl
  rw [this, subst_self]
  rfl

theorem constantCoeff_powerSeries_subst {τ : Type*} {a : MvPowerSeries τ R}
    (ha : constantCoeff a = 0) {φ : PowerSeries R} (hφ : PowerSeries.constantCoeff φ = 0) :
    constantCoeff (PowerSeries.subst a φ) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero ha φ hφ

theorem constantCoeff_subst_of_powerSeries {φ ψ : PowerSeries R}
    (hψ : PowerSeries.constantCoeff ψ = 0) (hφ : PowerSeries.constantCoeff φ = 0) :
    PowerSeries.constantCoeff (PowerSeries.subst ψ φ) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hψ φ hφ

theorem constantCoeff_subst_pair_of_powerSeries (G : FormalGroup R) {φ ψ : PowerSeries R}
    (hφ : PowerSeries.constantCoeff φ = 0) (hψ : PowerSeries.constantCoeff ψ = 0) :
    PowerSeries.constantCoeff (subst ![φ, ψ] G.toPowerSeries : PowerSeries R) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_pair hφ hψ)
    (fun i => by fin_cases i; exacts [hφ, hψ]) G.zero_constantCoeff

variable {F G H : FormalGroup R}

theorem point_hasSubst_pair {σ : Type*} (x y : F.Point σ) : HasSubst ![x.val, y.val] :=
  hasSubst_of_constantCoeff_nilpotent fun i => by fin_cases i; exacts [x.prop, y.prop]

noncomputable def substPoint (φ : PowerSeries R) (hφ : PowerSeries.constantCoeff φ = 0)
    {σ : Type*} (x : F.Point σ) : G.Point σ :=
  ⟨PowerSeries.subst x.val φ,
    hasSubst_powerSeries_subst x.prop (PowerSeries.HasSubst.of_constantCoeff_zero' hφ)⟩

theorem substPoint_val (φ : PowerSeries R) (hφ : PowerSeries.constantCoeff φ = 0)
    {σ : Type*} (x : F.Point σ) :
    (substPoint (G := G) φ hφ x).val = PowerSeries.subst x.val φ := rfl

theorem substPoint_congr {φ ψ : PowerSeries R} (e : φ = ψ) (hφ : PowerSeries.constantCoeff φ = 0)
    (hψ : PowerSeries.constantCoeff ψ = 0) {σ : Type*} (x : F.Point σ) :
    (substPoint φ hφ x : G.Point σ) = substPoint ψ hψ x := by
  subst e; rfl

theorem substPoint_X {σ : Type*} (x : F.Point σ) (h) :
    (substPoint PowerSeries.X h x : F.Point σ) = x :=
  Subtype.ext (PowerSeries.subst_X x.prop)

theorem substPoint_zero {σ : Type*} (x : F.Point σ) (h) :
    (substPoint 0 h x : G.Point σ) = 0 := by
  apply Subtype.ext
  rw [substPoint_val, ← PowerSeries.coe_substAlgHom x.prop, map_zero]
  rfl

theorem substPoint_zero_point {σ : Type*} (φ : PowerSeries R) (hφ) :
    (substPoint φ hφ (0 : F.Point σ) : G.Point σ) = 0 :=
  Subtype.ext (PowerSeries.subst_zero_of_constantCoeff_zero hφ)

theorem substPoint_substPoint {φ ψ : PowerSeries R} (hφ : PowerSeries.constantCoeff φ = 0)
    (hψ : PowerSeries.constantCoeff ψ = 0) (h) {σ : Type*} (x : F.Point σ) :
    (substPoint φ hφ (substPoint ψ hψ x : G.Point σ) : H.Point σ) =
      substPoint (PowerSeries.subst ψ φ) h x := by
  apply Subtype.ext
  simp only [substPoint_val]
  exact (PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' hψ) x.prop φ).symm

theorem substPoint_subst_pair {φ ψ : PowerSeries R} (hφ : PowerSeries.constantCoeff φ = 0)
    (hψ : PowerSeries.constantCoeff ψ = 0) (h) {σ : Type*} (x : F.Point σ) :
    (substPoint (subst ![φ, ψ] G.toPowerSeries) h x : G.Point σ) =
      substPoint φ hφ x + substPoint ψ hψ x := by
  apply Subtype.ext
  rw [substPoint_val, FormalGroup.add_apply, substPoint_val, substPoint_val]
  exact subst_subst_pair (hasSubst_pair hφ hψ) x.prop _

theorem substPoint_inv_subst {φ : PowerSeries R} (hφ : PowerSeries.constantCoeff φ = 0) (h)
    {σ : Type*} (x : F.Point σ) :
    (substPoint (PowerSeries.subst φ (inv G)) h x : G.Point σ) = -substPoint φ hφ x := by
  apply Subtype.ext
  rw [substPoint_val, neg_point_val, substPoint_val]
  exact PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hφ)
    x.prop _

variable (F G) in
@[ext]
structure Hom where
  toPowerSeries : PowerSeries R
  constantCoeff_eq_zero : PowerSeries.constantCoeff toPowerSeries = 0
  map_add : PowerSeries.subst F.toPowerSeries toPowerSeries =
    subst ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) toPowerSeries,
      PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) R) toPowerSeries] G.toPowerSeries

namespace Hom

theorem constantCoeff_eq_zero' (f : Hom F G) : constantCoeff f.toPowerSeries = 0 :=
  f.constantCoeff_eq_zero

noncomputable def apply (f : Hom F G) {σ : Type*} (x : F.Point σ) : G.Point σ :=
  substPoint f.toPowerSeries f.constantCoeff_eq_zero x

theorem apply_val (f : Hom F G) {σ : Type*} (x : F.Point σ) :
    (f.apply x).val = PowerSeries.subst x.val f.toPowerSeries := rfl

theorem apply_add (f : Hom F G) {σ : Type*} (x y : F.Point σ) :
    f.apply (x + y) = f.apply x + f.apply y := by
  apply Subtype.ext
  have hxy := point_hasSubst_pair x y
  have hF : PowerSeries.HasSubst F.toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hX : ∀ i : Fin 2, constantCoeff (X i : MvPowerSeries (Fin 2) R) = 0 := fun i => by simp
  have hpair := hasSubst_pair (constantCoeff_powerSeries_subst (hX 0) f.constantCoeff_eq_zero)
    (constantCoeff_powerSeries_subst (hX 1) f.constantCoeff_eq_zero)
  have h := congrArg (subst ![x.val, y.val]) f.map_add
  rw [subst_powerSeries_subst hF hxy, subst_comp_subst_apply hpair hxy] at h
  rw [apply_val, FormalGroup.add_apply, h, FormalGroup.add_apply]
  congr 1
  funext i
  fin_cases i
  · simp [subst_powerSeries_subst (PowerSeries.HasSubst.X (0 : Fin 2)) hxy, subst_X hxy,
      apply_val]
  · simp [subst_powerSeries_subst (PowerSeries.HasSubst.X (1 : Fin 2)) hxy, subst_X hxy,
      apply_val]

theorem apply_zero (f : Hom F G) {σ : Type*} : f.apply (0 : F.Point σ) = 0 :=
  substPoint_zero_point _ _

private noncomputable def genPoint (F : FormalGroup R) (i : Fin 2) : F.Point (Fin 2) :=
  ⟨X i, PowerSeries.HasSubst.X i⟩

noncomputable def ofPoints (φ : PowerSeries R) (hφ : PowerSeries.constantCoeff φ = 0)
    (h : ∀ x y : F.Point (Fin 2),
      (substPoint φ hφ (x + y) : G.Point (Fin 2)) = substPoint φ hφ x + substPoint φ hφ y) :
    Hom F G where
  toPowerSeries := φ
  constantCoeff_eq_zero := hφ
  map_add := by
    have := congrArg Subtype.val (h (genPoint F 0) (genPoint F 1))
    rw [substPoint_val, FormalGroup.add_apply, FormalGroup.add_apply, substPoint_val,
      substPoint_val] at this
    simpa [genPoint, subst_X_X] using this

@[simp]
theorem ofPoints_toPowerSeries (φ : PowerSeries R) (hφ) (h) :
    (ofPoints (F := F) (G := G) φ hφ h).toPowerSeries = φ := rfl

noncomputable def comp (g : Hom G H) (f : Hom F G) : Hom F H :=
  ofPoints (PowerSeries.subst f.toPowerSeries g.toPowerSeries)
    (constantCoeff_subst_of_powerSeries f.constantCoeff_eq_zero g.constantCoeff_eq_zero)
    fun x y => by
      rw [← substPoint_substPoint g.constantCoeff_eq_zero f.constantCoeff_eq_zero,
        ← substPoint_substPoint g.constantCoeff_eq_zero f.constantCoeff_eq_zero,
        ← substPoint_substPoint g.constantCoeff_eq_zero f.constantCoeff_eq_zero]
      exact (congrArg g.apply (f.apply_add x y)).trans (g.apply_add _ _)

theorem toPowerSeries_comp (g : Hom G H) (f : Hom F G) :
    (g.comp f).toPowerSeries = PowerSeries.subst f.toPowerSeries g.toPowerSeries := rfl

theorem apply_comp (g : Hom G H) (f : Hom F G) {σ : Type*} (x : F.Point σ) :
    (g.comp f).apply x = g.apply (f.apply x) :=
  (substPoint_substPoint _ _ _ x).symm

variable (F) in
noncomputable def id : Hom F F :=
  ofPoints PowerSeries.X PowerSeries.constantCoeff_X fun x y => by
    rw [substPoint_X, substPoint_X, substPoint_X]

theorem toPowerSeries_id : (id F).toPowerSeries = PowerSeries.X := rfl

theorem comp_assoc {K : FormalGroup R} (h : Hom H K) (g : Hom G H) (f : Hom F G) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext1
  simp only [toPowerSeries_comp]
  exact PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' g.constantCoeff_eq_zero)
    (PowerSeries.HasSubst.of_constantCoeff_zero' f.constantCoeff_eq_zero) _

theorem id_comp (f : Hom F G) : (id G).comp f = f := by
  ext1
  exact PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' f.constantCoeff_eq_zero)

theorem comp_id (f : Hom F G) : f.comp (id F) = f := by
  ext1
  exact PowerSeries.X_subst _

noncomputable instance : Monoid (Hom F F) where
  mul g f := g.comp f
  one := id F
  mul_assoc h g f := comp_assoc h g f
  one_mul := id_comp
  mul_one := comp_id

theorem mul_def (g f : Hom F F) : g * f = g.comp f := rfl

theorem one_def : (1 : Hom F F) = id F := rfl

noncomputable def toPoint (f : Hom F G) : G.Point Unit :=
  ⟨f.toPowerSeries, PowerSeries.HasSubst.of_constantCoeff_zero' f.constantCoeff_eq_zero⟩

theorem toPoint_injective : Function.Injective (toPoint : Hom F G → G.Point Unit) :=
  fun _ _ h => Hom.ext (congrArg Subtype.val h)

theorem toPoint_comp (g : Hom G H) (f : Hom F G) : (g.comp f).toPoint = g.apply f.toPoint := rfl

noncomputable instance : Zero (Hom F G) where
  zero := ofPoints 0 (map_zero _) fun _ _ => by
    rw [substPoint_zero, substPoint_zero, substPoint_zero, add_zero]

theorem toPowerSeries_zero : (0 : Hom F G).toPowerSeries = 0 := rfl

theorem toPoint_zero : (0 : Hom F G).toPoint = 0 := rfl

theorem zero_apply {σ : Type*} (x : F.Point σ) : (0 : Hom F G).apply x = 0 :=
  substPoint_zero x _

section Comm

variable [G.IsComm]

noncomputable instance : Add (Hom F G) where
  add f g := ofPoints (subst ![f.toPowerSeries, g.toPowerSeries] G.toPowerSeries)
    (constantCoeff_subst_pair_of_powerSeries G f.constantCoeff_eq_zero g.constantCoeff_eq_zero)
    fun x y => by
      rw [substPoint_subst_pair f.constantCoeff_eq_zero g.constantCoeff_eq_zero,
        substPoint_subst_pair f.constantCoeff_eq_zero g.constantCoeff_eq_zero,
        substPoint_subst_pair f.constantCoeff_eq_zero g.constantCoeff_eq_zero]
      exact (congrArg₂ (· + ·) (f.apply_add x y) (g.apply_add x y)).trans
        (add_add_add_comm _ _ _ _)

noncomputable instance : Neg (Hom F G) where
  neg f := ofPoints (PowerSeries.subst f.toPowerSeries (inv G))
    (constantCoeff_subst_of_powerSeries f.constantCoeff_eq_zero (constantCoeff_inv G))
    fun x y => by
      rw [substPoint_inv_subst f.constantCoeff_eq_zero, substPoint_inv_subst
        f.constantCoeff_eq_zero, substPoint_inv_subst f.constantCoeff_eq_zero]
      exact (congrArg Neg.neg (f.apply_add x y)).trans (neg_add _ _)

noncomputable instance : Sub (Hom F G) where
  sub f g := f + -g

noncomputable instance : SMul ℕ (Hom F G) where
  smul := nsmulRec

noncomputable instance : SMul ℤ (Hom F G) where
  smul := zsmulRec

theorem toPowerSeries_add (f g : Hom F G) :
    (f + g).toPowerSeries = subst ![f.toPowerSeries, g.toPowerSeries] G.toPowerSeries := rfl

theorem toPowerSeries_neg (f : Hom F G) :
    (-f).toPowerSeries = PowerSeries.subst f.toPowerSeries (inv G) := rfl

theorem toPoint_add (f g : Hom F G) : (f + g).toPoint = f.toPoint + g.toPoint := rfl

theorem toPoint_neg (f : Hom F G) : (-f).toPoint = -f.toPoint := rfl

theorem toPoint_sub (f g : Hom F G) : (f - g).toPoint = f.toPoint - g.toPoint := by
  rw [sub_eq_add_neg, ← toPoint_neg, ← toPoint_add]
  rfl

theorem toPoint_nsmul (f : Hom F G) (n : ℕ) : (n • f).toPoint = n • f.toPoint := by
  induction n with
  | zero => rw [zero_nsmul]; rfl
  | succ n ih =>
    rw [succ_nsmul, ← ih, ← toPoint_add]
    rfl

theorem toPoint_zsmul (f : Hom F G) (n : ℤ) : (n • f).toPoint = n • f.toPoint := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, natCast_zsmul, ← toPoint_nsmul]
    rfl
  | negSucc n =>
    rw [negSucc_zsmul, ← toPoint_nsmul, ← toPoint_neg]
    rfl

noncomputable instance : AddCommGroup (Hom F G) :=
  toPoint_injective.addCommGroup _ toPoint_zero toPoint_add toPoint_neg toPoint_sub
    toPoint_nsmul toPoint_zsmul

theorem add_apply (f g : Hom F G) {σ : Type*} (x : F.Point σ) :
    (f + g).apply x = f.apply x + g.apply x :=
  substPoint_subst_pair f.constantCoeff_eq_zero g.constantCoeff_eq_zero _ x

theorem neg_apply (f : Hom F G) {σ : Type*} (x : F.Point σ) : (-f).apply x = -f.apply x :=
  substPoint_inv_subst f.constantCoeff_eq_zero _ x

theorem comp_add (g : Hom G H) [H.IsComm] (f₁ f₂ : Hom F G) :
    g.comp (f₁ + f₂) = g.comp f₁ + g.comp f₂ :=
  toPoint_injective (by rw [toPoint_comp, toPoint_add, apply_add, toPoint_add]; rfl)

omit [G.IsComm] in
theorem add_comp [H.IsComm] (g₁ g₂ : Hom G H) (f : Hom F G) :
    (g₁ + g₂).comp f = g₁.comp f + g₂.comp f :=
  toPoint_injective (by rw [toPoint_comp, add_apply, toPoint_add]; rfl)

variable (F) in
theorem toPowerSeries_neg_id [F.IsComm] : (-id F).toPowerSeries = inv F :=
  PowerSeries.X_subst _

end Comm

section Ring

variable [F.IsComm]

noncomputable instance : Ring (Hom F F) :=
  { (inferInstance : AddCommGroup (Hom F F)), (inferInstance : Monoid (Hom F F)) with
    left_distrib := fun f g h => comp_add f g h
    right_distrib := fun f g h => add_comp f g h
    zero_mul := fun f => toPoint_injective (by
      rw [mul_def, toPoint_comp, zero_apply]; rfl)
    mul_zero := fun f => toPoint_injective (by
      rw [mul_def, toPoint_comp]
      exact (apply_zero f).trans rfl) }

theorem one_apply {σ : Type*} (x : F.Point σ) : (1 : Hom F F).apply x = x :=
  substPoint_X x _

theorem intCast_apply (n : ℤ) {σ : Type*} (x : F.Point σ) : (n : Hom F F).apply x = n • x := by
  induction n using Int.induction_on with
  | zero => rw [Int.cast_zero, zero_apply, zero_zsmul]
  | succ n ih => rw [Int.cast_add, Int.cast_one, add_apply, ih, one_apply, add_zsmul, one_zsmul]
  | pred n ih =>
    rw [Int.cast_sub, Int.cast_one, sub_eq_add_neg, add_apply, neg_apply, ih, one_apply,
      sub_zsmul, one_zsmul]

end Ring

end Hom

theorem two_le_order_subst_higher (F : FormalGroup R) {τ : Type*} {a b : MvPowerSeries τ R}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    (2 : ℕ∞) ≤ order (subst ![a, b] (higher F)) := by
  have := le_order_subst_sub_subst (f := higher F) (g := 0) (hasSubst_pair ha hb)
    (fun i => by fin_cases i <;> simp [ha, hb]) (by simpa using two_le_order_higher F)
  rwa [← subst_sub (hasSubst_pair ha hb), sub_zero] at this

theorem coeff_one_subst_pair (F : FormalGroup R) {f g : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.coeff 1 (subst ![f, g] F.toPowerSeries : PowerSeries R) =
      PowerSeries.coeff 1 f + PowerSeries.coeff 1 g := by
  change coeff (Finsupp.single () 1) (subst ![f, g] F.toPowerSeries) =
    coeff (Finsupp.single () 1) f + coeff (Finsupp.single () 1) g
  rw [subst_eq_add_add_subst_higher F (hasSubst_pair hf hg), map_add, map_add,
    coeff_of_lt_order (lt_of_lt_of_le (by simp) (two_le_order_subst_higher F hf hg)), add_zero]

theorem coeff_one_subst {f g : PowerSeries R} (hf : PowerSeries.constantCoeff f = 0)
    (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.coeff 1 (PowerSeries.subst g f) =
      PowerSeries.coeff 1 f * PowerSeries.coeff 1 g := by
  set c := PowerSeries.coeff 1 f with hc
  have hgs : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero' hg
  have hdec : f = PowerSeries.C c * PowerSeries.X + (f - PowerSeries.C c * PowerSeries.X) := by
    ring
  have h2 : (2 : ℕ∞) ≤ (f - PowerSeries.C c * PowerSeries.X).order := by
    refine PowerSeries.nat_le_order _ 2 fun i hi => ?_
    interval_cases i
    · simp [hf]
    · simp [hc]
  have h2' : (2 : ℕ∞) ≤ PowerSeries.order
      (PowerSeries.subst g (f - PowerSeries.C c * PowerSeries.X)) :=
    h2.trans (PowerSeries.le_order_subst_left' hg)
  conv_lhs => rw [hdec]
  rw [PowerSeries.subst_add hgs, PowerSeries.subst_mul hgs, PowerSeries.subst_X hgs, map_add,
    PowerSeries.coeff_of_lt_order 1 (lt_of_lt_of_le (by norm_num) h2'), add_zero]
  change PowerSeries.coeff 1 (PowerSeries.subst g (PowerSeries.C c) * g) = _
  rw [PowerSeries.subst_C]
  exact PowerSeries.coeff_C_mul _ _ _

namespace Hom

theorem coeff_one_comp (g : Hom G H) (f : Hom F G) :
    PowerSeries.coeff 1 (g.comp f).toPowerSeries =
      PowerSeries.coeff 1 g.toPowerSeries * PowerSeries.coeff 1 f.toPowerSeries :=
  coeff_one_subst g.constantCoeff_eq_zero f.constantCoeff_eq_zero

theorem coeff_one_add [G.IsComm] (f g : Hom F G) :
    PowerSeries.coeff 1 (f + g).toPowerSeries =
      PowerSeries.coeff 1 f.toPowerSeries + PowerSeries.coeff 1 g.toPowerSeries :=
  coeff_one_subst_pair G f.constantCoeff_eq_zero g.constantCoeff_eq_zero

theorem coeff_one_id : PowerSeries.coeff 1 (id F).toPowerSeries = 1 := by
  simp [toPowerSeries_id]

end Hom

variable (F) in
noncomputable def linearCoeff [F.IsComm] : Hom F F →+* R where
  toFun f := PowerSeries.coeff 1 f.toPowerSeries
  map_one' := Hom.coeff_one_id
  map_mul' g f := Hom.coeff_one_comp g f
  map_zero' := by simp [Hom.toPowerSeries_zero]
  map_add' f g := Hom.coeff_one_add f g

theorem linearCoeff_apply [F.IsComm] (f : Hom F F) :
    linearCoeff F f = PowerSeries.coeff 1 f.toPowerSeries := rfl

variable (F G) in
structure Iso where
  hom : Hom F G
  inv : Hom G F
  hom_comp_inv : hom.comp inv = Hom.id G
  inv_comp_hom : inv.comp hom = Hom.id F

namespace Iso

variable (F) in
noncomputable def refl : Iso F F := ⟨Hom.id F, Hom.id F, Hom.id_comp _, Hom.id_comp _⟩

def symm (e : Iso F G) : Iso G F := ⟨e.inv, e.hom, e.inv_comp_hom, e.hom_comp_inv⟩

noncomputable def trans (e : Iso F G) (e' : Iso G H) : Iso F H where
  hom := e'.hom.comp e.hom
  inv := e.inv.comp e'.inv
  hom_comp_inv := by
    rw [Hom.comp_assoc, ← Hom.comp_assoc e.hom, e.hom_comp_inv, Hom.id_comp, e'.hom_comp_inv]
  inv_comp_hom := by
    rw [Hom.comp_assoc, ← Hom.comp_assoc e'.inv, e'.inv_comp_hom, Hom.id_comp, e.inv_comp_hom]

theorem isUnit_coeff_one (e : Iso F G) : IsUnit (PowerSeries.coeff 1 e.hom.toPowerSeries) := by
  have h := congrArg (fun f : Hom G G => PowerSeries.coeff 1 f.toPowerSeries) e.hom_comp_inv
  simp only [Hom.coeff_one_comp, Hom.coeff_one_id] at h
  exact IsUnit.of_mul_eq_one _ h

noncomputable def ofIsUnit (f : Hom F G) (hf : IsUnit (PowerSeries.coeff 1 f.toPowerSeries)) :
    Iso F G :=
  have hψ := PowerSeries.constantCoeff_substInvOfIsUnit f.toPowerSeries hf
  have hfψ : PowerSeries.subst (PowerSeries.substInvOfIsUnit f.toPowerSeries hf)
      f.toPowerSeries = PowerSeries.X :=
    PowerSeries.subst_substInvOfIsUnit_right _ f.constantCoeff_eq_zero hf
  have hψf : PowerSeries.subst f.toPowerSeries
      (PowerSeries.substInvOfIsUnit f.toPowerSeries hf) = PowerSeries.X :=
    PowerSeries.subst_substInvOfIsUnit_left _ f.constantCoeff_eq_zero hf
  { hom := f
    inv := Hom.ofPoints (PowerSeries.substInvOfIsUnit f.toPowerSeries hf) hψ fun x y => by
      set u : F.Point (Fin 2) := substPoint _ hψ x + substPoint _ hψ y
      have hu : f.apply u = x + y := by
        rw [Hom.apply_add, Hom.apply, Hom.apply, substPoint_substPoint _ _
          (by rw [hfψ]; exact PowerSeries.constantCoeff_X), substPoint_substPoint _ _
          (by rw [hfψ]; exact PowerSeries.constantCoeff_X), substPoint_congr hfψ _
          PowerSeries.constantCoeff_X, substPoint_congr hfψ _ PowerSeries.constantCoeff_X,
          substPoint_X, substPoint_X]
      rw [← hu, Hom.apply, substPoint_substPoint _ _
          (by rw [hψf]; exact PowerSeries.constantCoeff_X),
        substPoint_congr hψf _ PowerSeries.constantCoeff_X, substPoint_X]
    hom_comp_inv := Hom.ext hfψ
    inv_comp_hom := Hom.ext hψf }

@[simp]
theorem ofIsUnit_hom (f : Hom F G) (hf : IsUnit (PowerSeries.coeff 1 f.toPowerSeries)) :
    (ofIsUnit f hf).hom = f := rfl

end Iso

theorem Hom.exists_iso_iff (f : Hom F G) :
    (∃ e : Iso F G, e.hom = f) ↔ IsUnit (PowerSeries.coeff 1 f.toPowerSeries) :=
  ⟨fun ⟨e, he⟩ => he ▸ e.isUnit_coeff_one, fun hf => ⟨Iso.ofIsUnit f hf, rfl⟩⟩

end Basics

/-! ## Section 4: Lubin–Tate Series & Lifting Lemma -/

section LubinTate

open MvPowerSeries

section Helpers

variable {A : Type*} [CommRing A] {σ : Type*}

noncomputable def substEach (g : PowerSeries A) : σ → MvPowerSeries σ A :=
  fun i => PowerSeries.subst (X i : MvPowerSeries σ A) g

theorem substEach_apply (g : PowerSeries A) (i : σ) :
    (substEach g i : MvPowerSeries σ A) = PowerSeries.subst (X i : MvPowerSeries σ A) g := rfl

theorem constantCoeff_substEach {g : PowerSeries A} (hg : PowerSeries.constantCoeff g = 0)
    (i : σ) : constantCoeff (substEach g i : MvPowerSeries σ A) = 0 :=
  constantCoeff_powerSeries_subst (by simp) hg

theorem hasSubst_substEach [Finite σ] {g : PowerSeries A}
    (hg : PowerSeries.constantCoeff g = 0) : HasSubst (substEach g : σ → MvPowerSeries σ A) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_substEach hg)

theorem le_order_sub {n : ℕ∞} {a b : MvPowerSeries σ A} (ha : n ≤ order a) (hb : n ≤ order b) :
    n ≤ order (a - b) := by
  rw [sub_eq_add_neg]
  exact le_trans (le_min ha (by rwa [order_neg])) min_order_le_add

theorem succ_le_of_add_two_le {n : ℕ} {x : ℕ∞} (h : (n : ℕ∞) + 2 ≤ x + 1) :
    ((n + 1 : ℕ) : ℕ∞) ≤ x := by
  have e : ((n + 1 : ℕ) : ℕ∞) + 1 = (n : ℕ∞) + 2 := by push_cast; ring
  exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 (e ▸ h)

theorem le_order_of_coeff_eq_zero {f : PowerSeries A} {n : ℕ}
    (h : ∀ k < n, PowerSeries.coeff k f = 0) : (n : ℕ∞) ≤ order (f : MvPowerSeries Unit A) := by
  refine nat_le_order fun d hd => ?_
  have hd' : d = Finsupp.single () (d ()) := by ext; simp
  rw [hd'] at hd ⊢
  rw [Finsupp.degree_single] at hd
  exact h _ hd

theorem powerSeries_subst_C_mul_X {τ : Type*} {a : MvPowerSeries τ A} (ha : PowerSeries.HasSubst a)
    (c : A) : PowerSeries.subst a (PowerSeries.C c * PowerSeries.X) = C c * a := by
  rw [PowerSeries.subst_mul ha, PowerSeries.subst_X ha, PowerSeries.subst_C]

theorem two_le_order_sub_C_mul_X {f : PowerSeries A} {c : A}
    (hf0 : PowerSeries.constantCoeff f = 0) (hf1 : PowerSeries.coeff 1 f = c) :
    (2 : ℕ∞) ≤ order ((f - PowerSeries.C c * PowerSeries.X : PowerSeries A) : MvPowerSeries Unit A) :=
  le_order_of_coeff_eq_zero (n := 2) fun k hk => by
    interval_cases k
    · simp [hf0]
    · simp [hf1]

theorem le_order_subst_sub_subst_sub_C_mul {f : PowerSeries A} {c : A}
    (hf0 : PowerSeries.constantCoeff f = 0) (hf1 : PowerSeries.coeff 1 f = c)
    {φ ψ : MvPowerSeries σ A} (hφ : constantCoeff φ = 0) (hψ : constantCoeff ψ = 0) {n : ℕ}
    (h : (n : ℕ∞) ≤ order (φ - ψ)) :
    ((n + 1 : ℕ) : ℕ∞) ≤
      order (PowerSeries.subst φ f - PowerSeries.subst ψ f - C c * (φ - ψ)) := by
  set f₂ : PowerSeries A := f - PowerSeries.C c * PowerSeries.X with hf₂
  have h2 := two_le_order_sub_C_mul_X hf0 hf1
  have hφs : PowerSeries.HasSubst φ := PowerSeries.HasSubst.of_constantCoeff_zero hφ
  have hψs : PowerSeries.HasSubst ψ := PowerSeries.HasSubst.of_constantCoeff_zero hψ
  have hdec : f = PowerSeries.C c * PowerSeries.X + f₂ := by rw [hf₂]; ring
  have e : PowerSeries.subst φ f - PowerSeries.subst ψ f - C c * (φ - ψ) =
      PowerSeries.subst φ f₂ - PowerSeries.subst ψ f₂ := by
    conv_lhs => rw [hdec]
    rw [PowerSeries.subst_add hφs, PowerSeries.subst_add hψs, powerSeries_subst_C_mul_X hφs,
      powerSeries_subst_C_mul_X hψs]
    ring
  rw [e, PowerSeries.subst_def, PowerSeries.subst_def]
  have hφ' : HasSubst (fun _ : Unit => φ) := (PowerSeries.hasSubst_iff).mp hφs
  have hψ' : HasSubst (fun _ : Unit => ψ) := (PowerSeries.hasSubst_iff).mp hψs
  have key := add_le_order_subst_sub_subst hφ' hψ' (fun _ => hφ) (fun _ => hψ) (fun _ => h) h2
  exact succ_le_of_add_two_le key

theorem coeff_rescale_const (c : A) (δ : MvPowerSeries σ A) (e : σ →₀ ℕ) :
    coeff e (rescale (Function.const σ c) δ) = c ^ e.degree * coeff e δ := by
  rw [coeff_rescale]
  congr 1
  simp [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]

theorem le_order_subst_substEach_sub_rescale [Finite σ] {g : PowerSeries A} {c : A}
    (hg0 : PowerSeries.constantCoeff g = 0) (hg1 : PowerSeries.coeff 1 g = c)
    {δ : MvPowerSeries σ A} {n : ℕ} (h : (n : ℕ∞) ≤ order δ) :
    ((n + 1 : ℕ) : ℕ∞) ≤ order (subst (substEach g) δ - rescale (Function.const σ c) δ) := by
  rw [rescale_eq_subst]
  have hb : HasSubst (Function.const σ c • (X : σ → MvPowerSeries σ A)) := HasSubst.smul_X _
  have hab : ∀ i, (2 : ℕ∞) ≤ order (substEach g i - (Function.const σ c • (X : σ → MvPowerSeries σ A)) i) := by
    intro i
    have hXi : PowerSeries.HasSubst (X i : MvPowerSeries σ A) := PowerSeries.HasSubst.X i
    have e : (Function.const σ c • (X : σ → MvPowerSeries σ A)) i =
        PowerSeries.subst (X i : MvPowerSeries σ A) (PowerSeries.C c * PowerSeries.X) := by
      rw [powerSeries_subst_C_mul_X hXi]
      change Function.const σ c i • (X i : MvPowerSeries σ A) = _
      rw [Function.const_apply, smul_eq_C_mul]
    rw [e, substEach_apply, PowerSeries.subst_def, PowerSeries.subst_def]
    exact le_order_subst_sub_subst ((PowerSeries.hasSubst_iff).mp hXi) (fun _ => by simp)
      (two_le_order_sub_C_mul_X hg0 hg1)
  have key := add_le_order_subst_sub_subst (hasSubst_substEach hg0) hb
    (constantCoeff_substEach hg0) (fun i => by simp) hab h
  rw [add_comm] at key
  exact succ_le_of_add_two_le key

theorem subst_X_pow_card_eq_pow {k : Type*} [Field k] [Fintype k] (ψ : MvPowerSeries σ k) :
    subst (fun i => (X i : MvPowerSeries σ k) ^ Fintype.card k) ψ = ψ ^ Fintype.card k := by
  obtain ⟨p, hcp, n, hp, hcard⟩ := FiniteField.card' k
  have := hcp
  have : Fact p.Prime := ⟨hp⟩
  have h := map_iterateFrobenius_expand p hp.ne_zero ψ n
  have hid : iterateFrobenius k p n = RingHom.id k := by
    ext x
    rw [iterateFrobenius_def, ← hcard]
    exact FiniteField.pow_card x
  rw [hid, map_id] at h
  rw [hcard]
  simpa [expand, coe_substAlgHom] using h

end Helpers

section Construction

variable {A : Type*} [CommRing A] {σ : Type*}

noncomputable def dropConst (φ : MvPowerSeries σ A) : MvPowerSeries σ A :=
  φ - C (constantCoeff φ)

theorem constantCoeff_dropConst (φ : MvPowerSeries σ A) : constantCoeff (dropConst φ) = 0 := by
  simp [dropConst]

theorem coeff_dropConst (φ : MvPowerSeries σ A) {e : σ →₀ ℕ} (he : e ≠ 0) :
    coeff e (dropConst φ) = coeff e φ := by
  classical
  rw [dropConst, map_sub, coeff_C, if_neg he, sub_zero]

theorem dropConst_of_constantCoeff_eq_zero {φ : MvPowerSeries σ A} (h : constantCoeff φ = 0) :
    dropConst φ = φ := by
  simp [dropConst, h]

noncomputable def defect (f g : PowerSeries A) (φ : MvPowerSeries σ A) : MvPowerSeries σ A :=
  subst (substEach g) (dropConst φ) - PowerSeries.subst (dropConst φ) f

open Classical in
noncomputable def divBy (c a : A) : A :=
  if h : c ∣ a then h.choose else 0

theorem mul_divBy {c a : A} (h : c ∣ a) : c * divBy c a = a := by
  rw [divBy, dif_pos h]
  exact h.choose_spec.symm

noncomputable def step (π : A) (f g : PowerSeries A) (ℓ φ : MvPowerSeries σ A) :
    MvPowerSeries σ A :=
  fun e => if e.degree ≤ 1 then coeff e ℓ else
    coeff e φ + Ring.inverse (1 - π ^ (e.degree - 1)) * divBy π (coeff e (defect f g φ))

theorem coeff_step (π : A) (f g : PowerSeries A) (ℓ φ : MvPowerSeries σ A) (e : σ →₀ ℕ) :
    coeff e (step π f g ℓ φ) = if e.degree ≤ 1 then coeff e ℓ else
      coeff e φ + Ring.inverse (1 - π ^ (e.degree - 1)) * divBy π (coeff e (defect f g φ)) :=
  rfl

variable [Finite σ] {π : A} {f g : PowerSeries A}
  (hf0 : PowerSeries.constantCoeff f = 0) (hf1 : PowerSeries.coeff 1 f = π)
  (hg0 : PowerSeries.constantCoeff g = 0) (hg1 : PowerSeries.coeff 1 g = π)

include hf0 hf1 hg0 hg1 in
theorem coeff_defect_sub_defect {φ ψ : MvPowerSeries σ A} {n : ℕ}
    (h : (n : ℕ∞) ≤ order (φ - ψ)) {e : σ →₀ ℕ} (he : e.degree ≤ n) :
    coeff e (defect f g φ) - coeff e (defect f g ψ) =
      (π ^ e.degree - π) * coeff e (dropConst φ - dropConst ψ) := by
  have hδ : (n : ℕ∞) ≤ order (dropConst φ - dropConst ψ) := by
    refine nat_le_order fun d hd => ?_
    by_cases hd0 : d = 0
    · simp [hd0, coeff_zero_eq_constantCoeff_apply, constantCoeff_dropConst]
    · rw [map_sub, coeff_dropConst _ hd0, coeff_dropConst _ hd0, ← map_sub]
      exact coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)
  have h1 := le_order_subst_substEach_sub_rescale hg0 hg1 hδ
  have h2 := le_order_subst_sub_subst_sub_C_mul hf0 hf1 (constantCoeff_dropConst φ)
    (constantCoeff_dropConst ψ) hδ
  have h3 := le_order_sub h1 h2
  have hlt : (e.degree : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_of_le he
  have h0 := coeff_of_lt_order (hlt.trans_le h3)
  rw [subst_sub (hasSubst_substEach hg0)] at h0
  simp only [defect, map_sub, coeff_rescale_const, coeff_C_mul] at h0 ⊢
  linear_combination h0

variable (hreg : ∀ x : A, π * x = 0 → x = 0) (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit (1 - π ^ n))
  (hdiv : ∀ (φ : MvPowerSeries σ A) (e : σ →₀ ℕ), π ∣ coeff e (defect f g φ))

include hf0 hf1 hg0 hg1 hreg hunit hdiv in
theorem step_contract (ℓ φ ψ : MvPowerSeries σ A) (n : ℕ) (h : (n : ℕ∞) ≤ order (φ - ψ)) :
    ((n + 1 : ℕ) : ℕ∞) ≤ order (step π f g ℓ φ - step π f g ℓ ψ) := by
  refine nat_le_order fun e he => ?_
  have he' : e.degree ≤ n := Nat.lt_succ_iff.1 he
  rw [map_sub, coeff_step, coeff_step]
  split_ifs with h1
  · exact sub_self _
  · replace h1 := not_le.1 h1
    have he0 : e ≠ 0 := by
      rintro rfl
      simp at h1
    have hkey := coeff_defect_sub_defect hf0 hf1 hg0 hg1 h he'
    rw [map_sub, coeff_dropConst _ he0, coeff_dropConst _ he0] at hkey
    obtain ⟨m, hm⟩ : ∃ m, e.degree = m + 1 := ⟨e.degree - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel]
    rw [hm] at hkey
    have hdiff : divBy π (coeff e (defect f g φ)) - divBy π (coeff e (defect f g ψ)) =
        (π ^ m - 1) * (coeff e φ - coeff e ψ) := by
      rw [← sub_eq_zero]
      apply hreg
      rw [mul_sub, mul_sub, mul_divBy (hdiv φ e), mul_divBy (hdiv ψ e), hkey]
      ring
    have hu := Ring.inverse_mul_cancel _ (hunit m (by omega))
    linear_combination Ring.inverse (1 - π ^ m) * hdiff - (coeff e φ - coeff e ψ) * hu

include hf0 hg0 in
theorem defect_zero : defect f g (0 : MvPowerSeries σ A) = 0 := by
  have h0 : dropConst (0 : MvPowerSeries σ A) = 0 := by simp [dropConst]
  rw [defect, h0, ← coe_substAlgHom (hasSubst_substEach hg0), map_zero,
    PowerSeries.subst_zero_of_constantCoeff_zero hf0, sub_zero]

include hf0 hf1 hg0 hg1 hreg hunit hdiv in
theorem step_eq_self_iff {ℓ : MvPowerSeries σ A} (hℓ : constantCoeff ℓ = 0)
    (φ : MvPowerSeries σ A) :
    step π f g ℓ φ = φ ↔
      (2 : ℕ∞) ≤ order (φ - ℓ) ∧ PowerSeries.subst φ f = subst (substEach g) φ := by
  have hdivBy0 : divBy π 0 = 0 := hreg _ (mul_divBy (dvd_zero π))
  constructor
  · intro hs
    have hlin : ∀ e : σ →₀ ℕ, e.degree ≤ 1 → coeff e φ = coeff e ℓ := by
      intro e he
      have := congrArg (coeff e) hs
      rw [coeff_step, if_pos he] at this
      exact this.symm
    have hφ0 : constantCoeff φ = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, hlin 0 (by simp),
        coeff_zero_eq_constantCoeff_apply, hℓ]
    have hdef : defect f g φ = 0 := by
      ext e
      rw [map_zero]
      by_cases he : e.degree ≤ 1
      · have h1 : ((1 : ℕ) : ℕ∞) ≤ order (φ - 0) := by
          rw [sub_zero, Nat.cast_one]
          exact one_le_order_iff_constCoeff_eq_zero.2 hφ0
        have := coeff_defect_sub_defect hf0 hf1 hg0 hg1 h1 he
        rw [defect_zero hf0 hg0, map_zero, sub_zero] at this
        rw [this]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 he with h | h
        · rw [Finsupp.degree_eq_zero_iff] at h
          subst h
          simp [coeff_zero_eq_constantCoeff_apply, constantCoeff_dropConst]
        · rw [h, pow_one, sub_self, zero_mul]
      · have := congrArg (coeff e) hs
        rw [coeff_step, if_neg he, add_eq_left] at this
        have hu := Ring.inverse_mul_cancel _ (hunit (e.degree - 1) (by omega))
        have hq : divBy π (coeff e (defect f g φ)) = 0 := by
          linear_combination (1 - π ^ (e.degree - 1)) * this -
            divBy π (coeff e (defect f g φ)) * hu
        rw [← mul_divBy (hdiv φ e), hq, mul_zero]
    have h2 : ((2 : ℕ) : ℕ∞) ≤ order (φ - ℓ) :=
      nat_le_order fun e he => by rw [map_sub, hlin e (by omega), sub_self]
    refine ⟨by exact_mod_cast h2, ?_⟩
    · rw [defect, dropConst_of_constantCoeff_eq_zero hφ0, sub_eq_zero] at hdef
      exact hdef.symm
  · rintro ⟨h2, heq⟩
    have hlin : ∀ e : σ →₀ ℕ, e.degree ≤ 1 → coeff e φ = coeff e ℓ := by
      intro e he
      have he2 : (e.degree : ℕ∞) < 2 := by
        have : e.degree < 2 := by omega
        exact_mod_cast this
      have := coeff_of_lt_order (lt_of_lt_of_le he2 h2)
      rwa [map_sub, sub_eq_zero] at this
    have hφ0 : constantCoeff φ = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, hlin 0 (by simp),
        coeff_zero_eq_constantCoeff_apply, hℓ]
    have hdef : defect f g φ = 0 := by
      rw [defect, dropConst_of_constantCoeff_eq_zero hφ0, heq, sub_self]
    ext e
    rw [coeff_step]
    split_ifs with he
    · exact (hlin e he).symm
    · rw [hdef, map_zero, hdivBy0, mul_zero, add_zero]

include hf0 hf1 hg0 hg1 hreg hunit hdiv in
theorem existsUnique_of_dvd_defect {ℓ : MvPowerSeries σ A} (hℓ : constantCoeff ℓ = 0) :
    ∃! φ : MvPowerSeries σ A,
      (2 : ℕ∞) ≤ order (φ - ℓ) ∧ PowerSeries.subst φ f = subst (substEach g) φ := by
  obtain ⟨φ, hφ, huniq⟩ := existsUnique_fixedPoint (step π f g ℓ)
    (step_contract hf0 hf1 hg0 hg1 hreg hunit hdiv ℓ)
  exact ⟨φ, (step_eq_self_iff hf0 hf1 hg0 hg1 hreg hunit hdiv hℓ φ).1 hφ,
    fun ψ hψ => huniq ψ ((step_eq_self_iff hf0 hf1 hg0 hg1 hreg hunit hdiv hℓ ψ).2 hψ)⟩

end Construction

section LocalRing

variable {A : Type*} [CommRing A] [IsLocalRing A]

structure IsLubinTateSeries (π : A) (f : PowerSeries A) : Prop where
  constantCoeff_eq_zero : PowerSeries.constantCoeff f = 0
  coeff_one : PowerSeries.coeff 1 f = π
  dvd_coeff_sub : ∀ n : ℕ,
    π ∣ PowerSeries.coeff n (f - PowerSeries.X ^ Nat.card (IsLocalRing.ResidueField A))

end LocalRing

section DVR

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {π : A}

theorem residue_eq_zero_iff_dvd (hπ : Irreducible π) (a : A) :
    IsLocalRing.residue A a = 0 ↔ π ∣ a := by
  rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton]

theorem isUnit_one_sub_pow (hπ : Irreducible π) {n : ℕ} (hn : 1 ≤ n) : IsUnit (1 - π ^ n) :=
  IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
    (mem_nonunits_iff.2 fun hu => hπ.not_isUnit ((isUnit_pow_iff (by omega)).1 hu))

theorem map_residue_of_isLubinTateSeries [Fintype (IsLocalRing.ResidueField A)]
    (hπ : Irreducible π) {f : PowerSeries A} (hf : IsLubinTateSeries π f) :
    PowerSeries.map (IsLocalRing.residue A) f =
      PowerSeries.X ^ Fintype.card (IsLocalRing.ResidueField A) := by
  ext n
  have := (residue_eq_zero_iff_dvd hπ _).2 (hf.dvd_coeff_sub n)
  rw [map_sub, map_sub, sub_eq_zero, Nat.card_eq_fintype_card] at this
  rw [PowerSeries.coeff_map, this, ← PowerSeries.coeff_map, map_pow, PowerSeries.map_X]

theorem dvd_coeff_defect [Finite (IsLocalRing.ResidueField A)] (hπ : Irreducible π)
    {σ : Type*} [Finite σ] {f g : PowerSeries A} (hf : IsLubinTateSeries π f)
    (hg : IsLubinTateSeries π g) (φ : MvPowerSeries σ A) (e : σ →₀ ℕ) :
    π ∣ coeff e (defect f g φ) := by
  classical
  let := Fintype.ofFinite (IsLocalRing.ResidueField A)
  rw [← residue_eq_zero_iff_dvd hπ, ← coeff_map]
  have hs : PowerSeries.HasSubst (dropConst φ) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_dropConst φ)
  have hE := hasSubst_substEach (σ := σ) hg.constantCoeff_eq_zero
  have hmapE : (fun i => map (IsLocalRing.residue A) (substEach g i : MvPowerSeries σ A)) =
      fun i => X i ^ Fintype.card (IsLocalRing.ResidueField A) := by
    funext i
    rw [substEach_apply, PowerSeries.map_subst (PowerSeries.HasSubst.X i),
      map_residue_of_isLubinTateSeries hπ hg, map_X,
      PowerSeries.subst_pow (PowerSeries.HasSubst.X i), PowerSeries.subst_X (PowerSeries.HasSubst.X i)]
  have hs' : PowerSeries.HasSubst (map (IsLocalRing.residue A) (dropConst φ)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
        constantCoeff_dropConst, map_zero])
  rw [defect, map_sub, map_subst hE, PowerSeries.map_subst hs,
    map_residue_of_isLubinTateSeries hπ hf, PowerSeries.subst_pow hs', PowerSeries.subst_X hs', hmapE,
    subst_X_pow_card_eq_pow, sub_self, map_zero]

end DVR

section LinearForm

variable {A : Type*} [CommRing A]

noncomputable def sum₂ {σ : Type*} [Fintype σ] (a : σ → A) : MvPowerSeries σ A :=
  ∑ i, C (a i) * X i

theorem constantCoeff_linearForm {σ : Type*} [Fintype σ] (a : σ → A) :
    constantCoeff (sum₂ a) = 0 := by
  simp [sum₂]

theorem coeff_eq_of_two_le_order_sub {σ : Type*} {φ ψ : MvPowerSeries σ A}
    (h : (2 : ℕ∞) ≤ order (φ - ψ)) {e : σ →₀ ℕ} (he : e.degree ≤ 1) : coeff e φ = coeff e ψ := by
  have he2 : (e.degree : ℕ∞) < 2 := by
    have : e.degree < 2 := by omega
    exact_mod_cast this
  have := coeff_of_lt_order (lt_of_lt_of_le he2 h)
  rwa [map_sub, sub_eq_zero] at this

end LinearForm

section DVRLift

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {π : A}
  [Finite (IsLocalRing.ResidueField A)] (hπ : Irreducible π) {f g : PowerSeries A}
include hπ

theorem existsUnique_subst_eq {σ : Type*} [Finite σ] (hf : IsLubinTateSeries π f)
    (hg : IsLubinTateSeries π g) {ℓ : MvPowerSeries σ A} (hℓ : constantCoeff ℓ = 0) :
    ∃! φ : MvPowerSeries σ A,
      (2 : ℕ∞) ≤ order (φ - ℓ) ∧ PowerSeries.subst φ f = subst (substEach g) φ :=
  existsUnique_of_dvd_defect hf.constantCoeff_eq_zero hf.coeff_one hg.constantCoeff_eq_zero
    hg.coeff_one (fun _ hx => (mul_eq_zero.1 hx).resolve_left hπ.ne_zero)
    (fun _ hn => isUnit_one_sub_pow hπ hn) (dvd_coeff_defect hπ hf hg) hℓ

theorem existsUnique_subst_eq_linearForm {σ : Type*} [Fintype σ] (hf : IsLubinTateSeries π f)
    (hg : IsLubinTateSeries π g) (a : σ → A) :
    ∃! φ : MvPowerSeries σ A,
      (2 : ℕ∞) ≤ order (φ - sum₂ a) ∧ PowerSeries.subst φ f = subst (substEach g) φ :=
  existsUnique_subst_eq hπ hf hg (constantCoeff_linearForm a)

noncomputable def lubinTateLift {σ : Type*} [Fintype σ] (hf : IsLubinTateSeries π f)
    (hg : IsLubinTateSeries π g) (a : σ → A) : MvPowerSeries σ A :=
  (existsUnique_subst_eq_linearForm hπ hf hg a).exists.choose

variable {σ : Type*} [Fintype σ] (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g)
  (a : σ → A)

theorem two_le_order_lubinTateLift_sub :
    (2 : ℕ∞) ≤ order (lubinTateLift hπ hf hg a - sum₂ a) :=
  (existsUnique_subst_eq_linearForm hπ hf hg a).exists.choose_spec.1

theorem subst_lubinTateLift :
    PowerSeries.subst (lubinTateLift hπ hf hg a) f =
      subst (substEach g) (lubinTateLift hπ hf hg a) :=
  (existsUnique_subst_eq_linearForm hπ hf hg a).exists.choose_spec.2

theorem eq_lubinTateLift {φ : MvPowerSeries σ A} (h2 : (2 : ℕ∞) ≤ order (φ - sum₂ a))
    (h : PowerSeries.subst φ f = subst (substEach g) φ) : φ = lubinTateLift hπ hf hg a :=
  (existsUnique_subst_eq_linearForm hπ hf hg a).unique ⟨h2, h⟩
    (existsUnique_subst_eq_linearForm hπ hf hg a).exists.choose_spec

theorem constantCoeff_lubinTateLift : constantCoeff (lubinTateLift hπ hf hg a) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply,
    coeff_eq_of_two_le_order_sub (two_le_order_lubinTateLift_sub hπ hf hg a) (by simp),
    coeff_zero_eq_constantCoeff_apply, constantCoeff_linearForm]

end DVRLift

end LubinTate

/-! ## Section 5: Lubin–Tate Formal Group Law & Formal Module -/

section LubinTateGroup

open MvPowerSeries

section Composition

variable {A : Type*} [CommRing A] {σ τ : Type*}

private theorem coeff_eq_of_two_le_order {φ ψ : MvPowerSeries σ A}
    (h : (2 : ℕ∞) ≤ order (φ - ψ)) {e : σ →₀ ℕ} (he : e.degree ≤ 1) : coeff e φ = coeff e ψ := by
  have he2 : (e.degree : ℕ∞) < 2 := by
    have : e.degree < 2 := by omega
    exact_mod_cast this
  have := coeff_of_lt_order (lt_of_lt_of_le he2 h)
  rwa [map_sub, sub_eq_zero] at this

def IsLubinTateLift (f g : PowerSeries A) (ℓ φ : MvPowerSeries σ A) : Prop :=
  constantCoeff φ = 0 ∧ (2 : ℕ∞) ≤ order (φ - ℓ) ∧
    PowerSeries.subst φ f = subst (substEach g) φ

theorem isLubinTateLift_X [Finite σ] {g : PowerSeries A} (hg0 : PowerSeries.constantCoeff g = 0)
    (i : σ) : IsLubinTateLift g g (X i) (X i : MvPowerSeries σ A) :=
  ⟨by simp, by simp, by rw [subst_X (hasSubst_substEach hg0)]; rfl⟩

theorem two_le_order_subst_sub_subst_of [Finite τ] {Φ ℓ : MvPowerSeries τ A}
    (hΦ : (2 : ℕ∞) ≤ order (Φ - ℓ)) (hℓ : constantCoeff ℓ = 0) {u v : τ → MvPowerSeries σ A}
    (hu0 : ∀ j, constantCoeff (u j) = 0) (hv0 : ∀ j, constantCoeff (v j) = 0)
    (huv : ∀ j, (2 : ℕ∞) ≤ order (u j - v j)) :
    (2 : ℕ∞) ≤ order (subst u Φ - subst v ℓ) := by
  have hus : HasSubst u := hasSubst_of_constantCoeff_zero hu0
  have hvs : HasSubst v := hasSubst_of_constantCoeff_zero hv0
  have h1 := le_order_subst_sub_subst hus hu0 hΦ
  have h2 := add_le_order_subst_sub_subst hus hvs hu0 hv0 huv (f := ℓ) (m := 1)
    (one_le_order_iff_constCoeff_eq_zero.2 hℓ)
  have h2' : (2 : ℕ∞) ≤ order (subst u ℓ - subst v ℓ) :=
    (ENat.add_le_add_iff_right ENat.one_ne_top).1 h2
  have e : subst u Φ - subst v ℓ = (subst u Φ - subst u ℓ) + (subst u ℓ - subst v ℓ) := by ring
  rw [e]
  exact le_trans (le_min h1 h2') min_order_le_add

theorem IsLubinTateLift.comp [Finite σ] [Finite τ] {f g h : PowerSeries A}
    (hg0 : PowerSeries.constantCoeff g = 0) (hh0 : PowerSeries.constantCoeff h = 0)
    {ℓ Φ : MvPowerSeries τ A} (hΦ : IsLubinTateLift f g ℓ Φ) {v u : τ → MvPowerSeries σ A}
    (hu : ∀ j, IsLubinTateLift g h (v j) (u j)) :
    IsLubinTateLift f h (subst v ℓ) (subst u Φ) := by
  obtain ⟨hΦ0, hΦ2, hΦe⟩ := hΦ
  have hu0 : ∀ j, constantCoeff (u j) = 0 := fun j => (hu j).1
  have hus : HasSubst u := hasSubst_of_constantCoeff_zero hu0
  have hℓ0 : constantCoeff ℓ = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_eq_of_two_le_order hΦ2 (by simp),
      coeff_zero_eq_constantCoeff_apply, hΦ0]
  have hv0 : ∀ j, constantCoeff (v j) = 0 := fun j => by
    rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_eq_of_two_le_order (hu j).2.1 (by simp),
      coeff_zero_eq_constantCoeff_apply, hu0 j]
  refine ⟨constantCoeff_subst_eq_zero hus hu0 hΦ0,
    two_le_order_subst_sub_subst_of hΦ2 hℓ0 hu0 hv0 (fun j => (hu j).2.1), ?_⟩
  have hΦs : PowerSeries.HasSubst Φ := PowerSeries.HasSubst.of_constantCoeff_zero hΦ0
  rw [← subst_powerSeries_subst hΦs hus, hΦe, subst_comp_subst_apply (hasSubst_substEach hg0) hus,
    subst_comp_subst_apply hus (hasSubst_substEach hh0)]
  congr 1
  funext j
  rw [substEach_apply, subst_powerSeries_subst (PowerSeries.HasSubst.X j) hus, subst_X hus]
  exact (hu j).2.2

theorem subst_substEach_unit (g : PowerSeries A) (φ : MvPowerSeries Unit A) :
    subst (substEach g) φ = PowerSeries.subst g φ := by
  have : (substEach g : Unit → MvPowerSeries Unit A) = fun _ => g := by
    funext u
    exact PowerSeries.X_subst g
  rw [this, PowerSeries.subst_def]

end Composition

section FormalModule

variable {A : Type*} [CommRing A]

structure FormalModule (F : FormalGroup A) [F.IsComm] where
  smul : A →+* Hom F F
  linearCoeff_smul : ∀ a, linearCoeff F (smul a) = a

end FormalModule

section LinearFormHelpers

variable {A : Type*} [CommRing A]

theorem subst_linearForm {σ τ : Type*} [Fintype τ] {v : τ → MvPowerSeries σ A} (hv : HasSubst v)
    (a : τ → A) : subst v (sum₂ a) = ∑ j, C (a j) * v j := by
  rw [sum₂, ← coe_substAlgHom hv, map_sum]
  simp only [map_mul, coe_substAlgHom, subst_C, subst_X hv]

theorem linearForm_unit (a : A) :
    sum₂ (fun _ : Unit => a) = PowerSeries.C a * PowerSeries.X := by
  simp only [sum₂, Finset.univ_unique, Finset.sum_singleton]
  rfl

theorem linearForm_fin_two (a b : A) :
    sum₂ (![a, b] : Fin 2 → A) = C a * X 0 + C b * X 1 := by
  simp [sum₂, Fin.sum_univ_two]

theorem subst_linearForm_one_one {σ : Type*} {u v : MvPowerSeries σ A}
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0) :
    subst ![u, v] (sum₂ (![1, 1] : Fin 2 → A)) = u + v := by
  rw [subst_linearForm (hasSubst_pair hu hv)]
  simp [Fin.sum_univ_two]

theorem single_zero_ne_single_one :
    (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
  intro h
  have := congrArg (fun d => d 0) h
  simp at this

theorem substEach_fin_two (g : PowerSeries A) :
    (substEach g : Fin 2 → MvPowerSeries (Fin 2) A) =
      ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) A) g,
        PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) A) g] := by
  funext i
  fin_cases i <;> rfl

end LinearFormHelpers

section LubinTateLaw

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Finite (IsLocalRing.ResidueField A)] {π : A} {f g h : PowerSeries A}

variable (hπ : Irreducible π)
include hπ

theorem isLubinTateLift_lubinTateLift {σ : Type*} [Fintype σ] (hf : IsLubinTateSeries π f)
    (hg : IsLubinTateSeries π g) (a : σ → A) :
    IsLubinTateLift f g (sum₂ a) (lubinTateLift hπ hf hg a) :=
  ⟨constantCoeff_lubinTateLift hπ hf hg a, two_le_order_lubinTateLift_sub hπ hf hg a,
    subst_lubinTateLift hπ hf hg a⟩

theorem eq_lubinTateLift_of {σ : Type*} [Fintype σ] (hf : IsLubinTateSeries π f)
    (hg : IsLubinTateSeries π g) {a : σ → A} {ℓ φ : MvPowerSeries σ A}
    (h : IsLubinTateLift f g ℓ φ) (hℓ : ℓ = sum₂ a) : φ = lubinTateLift hπ hf hg a := by
  subst hℓ
  exact eq_lubinTateLift hπ hf hg a h.2.1 h.2.2

theorem lubinTateLift_assoc (hf : IsLubinTateSeries π f) :
    subst ![subst ![(X 0 : MvPowerSeries (Fin 3) A), X 1]
        (lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A)), X 2]
        (lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A)) =
      subst ![(X 0 : MvPowerSeries (Fin 3) A), subst ![(X 1 : MvPowerSeries (Fin 3) A), X 2]
        (lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A))]
        (lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A)) := by
  set F := lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A)
  have hf0 := hf.constantCoeff_eq_zero
  have hF := isLubinTateLift_lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A)
  set Y : Fin 3 → MvPowerSeries (Fin 3) A := X with hYdef
  have hY : ∀ i : Fin 3, IsLubinTateLift f f (Y i) (Y i) := isLubinTateLift_X hf0
  have h01 := hF.comp hf0 hf0 (v := ![Y 0, Y 1]) (u := ![Y 0, Y 1])
    (fun k => by fin_cases k <;> simpa using hY _)
  have h12 := hF.comp hf0 hf0 (v := ![Y 1, Y 2]) (u := ![Y 1, Y 2])
    (fun k => by fin_cases k <;> simpa using hY _)
  have hP := hF.comp hf0 hf0 (v := ![subst ![Y 0, Y 1] (sum₂ (![1, 1] : Fin 2 → A)), Y 2])
    (u := ![subst ![Y 0, Y 1] F, Y 2]) (fun j => by
      fin_cases j
      · simpa using h01
      · simpa using hY 2)
  have hQ := hF.comp hf0 hf0 (v := ![Y 0, subst ![Y 1, Y 2] (sum₂ (![1, 1] : Fin 2 → A))])
    (u := ![Y 0, subst ![Y 1, Y 2] F]) (fun j => by
      fin_cases j
      · simpa using hY 0
      · simpa using h12)
  have e01 : subst ![Y 0, Y 1] (sum₂ (![1, 1] : Fin 2 → A)) = Y 0 + Y 1 :=
    subst_linearForm_one_one (by simp [Y]) (by simp [Y])
  have e12 : subst ![Y 1, Y 2] (sum₂ (![1, 1] : Fin 2 → A)) = Y 1 + Y 2 :=
    subst_linearForm_one_one (by simp [Y]) (by simp [Y])
  have hP' := eq_lubinTateLift_of hπ hf hf hP (a := ![1, 1, 1]) (by
    rw [e01, subst_linearForm_one_one (by simp [Y]) (by simp [Y])]
    simp [sum₂, Fin.sum_univ_three, Y])
  have hQ' := eq_lubinTateLift_of hπ hf hf hQ (a := ![1, 1, 1]) (by
    rw [e12, subst_linearForm_one_one (by simp [Y]) (by simp [Y])]
    simp [sum₂, Fin.sum_univ_three, Y, add_assoc])
  exact hP'.trans hQ'.symm

theorem lubinTateLift_comm (hf : IsLubinTateSeries π f) :
    lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A) =
      subst ![(X 1 : MvPowerSeries (Fin 2) A), X 0] (lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A)) := by
  have hf0 := hf.constantCoeff_eq_zero
  have hR := (isLubinTateLift_lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A)).comp hf0 hf0
    (v := ![(X 1 : MvPowerSeries (Fin 2) A), X 0]) (u := ![(X 1 : MvPowerSeries (Fin 2) A), X 0])
    (fun j => by fin_cases j <;> exact isLubinTateLift_X hf0 _)
  refine (eq_lubinTateLift_of hπ hf hf hR ?_).symm
  rw [subst_linearForm_one_one (by simp) (by simp)]
  simp [sum₂, Fin.sum_univ_two, add_comm]

noncomputable def lubinTateFormalGroup (hf : IsLubinTateSeries π f) : FormalGroup A where
  toPowerSeries := lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A)
  zero_constantCoeff := constantCoeff_lubinTateLift hπ hf hf _
  lin_coeff_X := by
    rw [coeff_eq_of_two_le_order_sub (two_le_order_lubinTateLift_sub hπ hf hf _) (by simp),
      linearForm_fin_two]
    simp [coeff_X, single_zero_ne_single_one]
  lin_coeff_Y := by
    rw [coeff_eq_of_two_le_order_sub (two_le_order_lubinTateLift_sub hπ hf hf _) (by simp),
      linearForm_fin_two]
    simp [coeff_X, single_zero_ne_single_one.symm]
  assoc := lubinTateLift_assoc hπ hf

theorem lubinTateFormalGroup_toPowerSeries (hf : IsLubinTateSeries π f) :
    (lubinTateFormalGroup hπ hf).toPowerSeries = lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A) :=
  rfl

instance (hf : IsLubinTateSeries π f) : (lubinTateFormalGroup hπ hf).IsComm :=
  ⟨lubinTateLift_comm hπ hf⟩

noncomputable def lubinTateEndo (hf : IsLubinTateSeries π f) :
    Hom (lubinTateFormalGroup hπ hf) (lubinTateFormalGroup hπ hf) where
  toPowerSeries := f
  constantCoeff_eq_zero := hf.constantCoeff_eq_zero
  map_add := by
    have := subst_lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A)
    rw [substEach_fin_two] at this
    exact this

theorem eq_lubinTateFormalGroup (hf : IsLubinTateSeries π f) (F : FormalGroup A) (φ : Hom F F)
    (hφ : φ.toPowerSeries = f) : F = lubinTateFormalGroup hπ hf := by
  apply FormalGroup.ext
  refine eq_lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A) ?_ ?_
  · have h2 := two_le_order_higher F
    have e : higher F = F.toPowerSeries - X 0 - X 1 := rfl
    rwa [e, sub_sub, ← one_mul (X 0 : MvPowerSeries (Fin 2) A), ← one_mul (X 1 : MvPowerSeries (Fin 2) A),
      ← map_one (C : A →+* MvPowerSeries (Fin 2) A), ← linearForm_fin_two] at h2
  · have := φ.map_add
    rw [hφ] at this
    rw [substEach_fin_two]
    exact this

theorem existsUnique_formalGroup (hf : IsLubinTateSeries π f) :
    ∃! F : FormalGroup A, ∃ φ : Hom F F, φ.toPowerSeries = f :=
  ⟨lubinTateFormalGroup hπ hf, ⟨lubinTateEndo hπ hf, rfl⟩,
    fun F ⟨φ, hφ⟩ => eq_lubinTateFormalGroup hπ hf F φ hφ⟩

end LubinTateLaw

section LubinTateHom

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Finite (IsLocalRing.ResidueField A)] {π : A} (hπ : Irreducible π) {f g h : PowerSeries A}
include hπ

theorem isLubinTateLift_subst_X (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g)
    (a : A) {σ : Type*} [Finite σ] (j : σ) :
    IsLubinTateLift f g (C a * X j)
      (PowerSeries.subst (X j : MvPowerSeries σ A) (lubinTateLift hπ hf hg fun _ : Unit => a)) := by
  have hg0 := hg.constantCoeff_eq_zero
  have := (isLubinTateLift_lubinTateLift hπ hf hg fun _ : Unit => a).comp hg0 hg0
    (v := fun _ => X j) (u := fun _ => X j) (fun _ => isLubinTateLift_X hg0 j)
  rw [subst_linearForm (hasSubst_of_constantCoeff_zero fun _ => by simp)] at this
  simpa [PowerSeries.subst_def] using this

theorem lubinTateHom_map_add (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g) (a : A) :
    PowerSeries.subst (lubinTateFormalGroup hπ hg).toPowerSeries
        (lubinTateLift hπ hf hg fun _ : Unit => a) =
      subst ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) A)
          (lubinTateLift hπ hf hg fun _ : Unit => a),
        PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) A)
          (lubinTateLift hπ hf hg fun _ : Unit => a)]
        (lubinTateFormalGroup hπ hf).toPowerSeries := by
  have hf0 := hf.constantCoeff_eq_zero
  have hg0 := hg.constantCoeff_eq_zero
  have hL := (isLubinTateLift_lubinTateLift hπ hf hg fun _ : Unit => a).comp hg0 hg0
    (v := fun _ => sum₂ (![1, 1] : Fin 2 → A))
    (u := fun _ => (lubinTateFormalGroup hπ hg).toPowerSeries)
    (fun _ => isLubinTateLift_lubinTateLift hπ hg hg _)
  have hR := (isLubinTateLift_lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A)).comp hf0 hg0
    (v := ![C a * X 0, C a * X 1])
    (u := ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) A)
          (lubinTateLift hπ hf hg fun _ : Unit => a),
        PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) A)
          (lubinTateLift hπ hf hg fun _ : Unit => a)])
    (fun j => by fin_cases j <;> simpa using isLubinTateLift_subst_X hπ hf hg a _)
  rw [PowerSeries.subst_def]
  refine (eq_lubinTateLift_of hπ hf hg hL (a := ![a, a]) ?_).trans
    (eq_lubinTateLift_of hπ hf hg hR ?_).symm
  · rw [subst_linearForm (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_linearForm _),
      linearForm_fin_two, linearForm_fin_two]
    simp only [Finset.univ_unique, Finset.sum_singleton, map_one, one_mul]
    ring
  · rw [subst_linearForm_one_one (by simp) (by simp), linearForm_fin_two]

noncomputable def lubinTateHom (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g) (a : A) :
    Hom (lubinTateFormalGroup hπ hg) (lubinTateFormalGroup hπ hf) where
  toPowerSeries := lubinTateLift hπ hf hg fun _ : Unit => a
  constantCoeff_eq_zero := constantCoeff_lubinTateLift hπ hf hg _
  map_add := lubinTateHom_map_add hπ hf hg a

variable (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g) (hh : IsLubinTateSeries π h)

theorem lubinTateHom_toPowerSeries (a : A) :
    (lubinTateHom hπ hf hg a).toPowerSeries = lubinTateLift hπ hf hg fun _ : Unit => a :=
  rfl

theorem isLubinTateLift_lubinTateHom (a : A) :
    IsLubinTateLift f g (PowerSeries.C a * PowerSeries.X) (lubinTateHom hπ hf hg a).toPowerSeries :=
  linearForm_unit a ▸ isLubinTateLift_lubinTateLift hπ hf hg _

theorem subst_lubinTateHom (a : A) :
    PowerSeries.subst (lubinTateHom hπ hf hg a).toPowerSeries f =
      PowerSeries.subst g (lubinTateHom hπ hf hg a).toPowerSeries := by
  have := subst_lubinTateLift hπ hf hg (fun _ : Unit => a)
  rw [subst_substEach_unit] at this
  exact this

theorem coeff_one_lubinTateHom (a : A) :
    PowerSeries.coeff 1 (lubinTateHom hπ hf hg a).toPowerSeries = a := by
  have := coeff_eq_of_two_le_order_sub (isLubinTateLift_lubinTateHom hπ hf hg a).2.1
    (e := Finsupp.single () 1) (by simp)
  change coeff (Finsupp.single () 1) _ = a
  rw [this]
  change PowerSeries.coeff 1 (PowerSeries.C a * PowerSeries.X) = a
  simp

theorem eq_lubinTateHom_toPowerSeries (a : A) {φ : PowerSeries A}
    (h0 : PowerSeries.constantCoeff φ = 0) (h1 : PowerSeries.coeff 1 φ = a)
    (h : PowerSeries.subst φ f = PowerSeries.subst g φ) :
    φ = (lubinTateHom hπ hf hg a).toPowerSeries := by
  refine eq_lubinTateLift hπ hf hg _ ?_ ?_
  · rw [linearForm_unit]
    exact two_le_order_sub_C_mul_X h0 h1
  · rw [subst_substEach_unit]
    exact h

theorem lubinTateHom_add (a b : A) :
    lubinTateHom hπ hf hg (a + b) = lubinTateHom hπ hf hg a + lubinTateHom hπ hf hg b := by
  have hf0 := hf.constantCoeff_eq_zero
  have hg0 := hg.constantCoeff_eq_zero
  apply Hom.ext
  rw [Hom.toPowerSeries_add, lubinTateFormalGroup_toPowerSeries]
  have hS := (isLubinTateLift_lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A)).comp hf0 hg0
    (v := ![sum₂ fun _ : Unit => a, sum₂ fun _ : Unit => b])
    (u := ![(lubinTateHom hπ hf hg a).toPowerSeries, (lubinTateHom hπ hf hg b).toPowerSeries])
    (fun j => by
      fin_cases j <;> simpa [lubinTateHom_toPowerSeries] using isLubinTateLift_lubinTateLift hπ hf hg _)
  refine (eq_lubinTateLift_of hπ hf hg hS ?_).symm
  rw [subst_linearForm_one_one (constantCoeff_linearForm _) (constantCoeff_linearForm _)]
  simp only [sum₂, Finset.univ_unique, Finset.sum_singleton, map_add]
  ring

theorem lubinTateHom_mul (a b : A) :
    lubinTateHom hπ hf hh (a * b) = (lubinTateHom hπ hf hg a).comp (lubinTateHom hπ hg hh b) := by
  have hg0 := hg.constantCoeff_eq_zero
  have hh0 := hh.constantCoeff_eq_zero
  apply Hom.ext
  rw [Hom.toPowerSeries_comp, PowerSeries.subst_def]
  have hS := (isLubinTateLift_lubinTateLift hπ hf hg fun _ : Unit => a).comp hg0 hh0
    (v := fun _ => sum₂ fun _ : Unit => b)
    (u := fun _ => (lubinTateHom hπ hg hh b).toPowerSeries)
    (fun _ => isLubinTateLift_lubinTateLift hπ hg hh _)
  refine (eq_lubinTateLift_of hπ hf hh hS ?_).symm
  rw [subst_linearForm (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_linearForm _)]
  simp only [sum₂, Finset.univ_unique, Finset.sum_singleton, map_mul]
  ring

theorem lubinTateHom_self_uniformizer :
    (lubinTateHom hπ hf hf π).toPowerSeries = f :=
  (eq_lubinTateHom_toPowerSeries hπ hf hf π hf.constantCoeff_eq_zero hf.coeff_one rfl).symm

theorem lubinTateHom_self_one : lubinTateHom hπ hf hf 1 = Hom.id _ := by
  apply Hom.ext
  rw [Hom.toPowerSeries_id]
  refine (eq_lubinTateHom_toPowerSeries hπ hf hf 1 (by simp) (by simp) ?_).symm
  rw [PowerSeries.X_subst, PowerSeries.subst_X
    (PowerSeries.HasSubst.of_constantCoeff_zero' hf.constantCoeff_eq_zero)]

theorem lubinTateHom_zero : lubinTateHom hπ hf hg 0 = 0 := by
  apply Hom.ext
  rw [Hom.toPowerSeries_zero]
  refine (eq_lubinTateHom_toPowerSeries hπ hf hg 0 (by simp) (by simp) ?_).symm
  rw [PowerSeries.subst_zero_of_constantCoeff_zero hf.constantCoeff_eq_zero,
    ← PowerSeries.coe_substAlgHom
      (PowerSeries.HasSubst.of_constantCoeff_zero' hg.constantCoeff_eq_zero), map_zero]

noncomputable def lubinTateEndRingHom :
    A →+* Hom (lubinTateFormalGroup hπ hf) (lubinTateFormalGroup hπ hf) where
  toFun a := lubinTateHom hπ hf hf a
  map_one' := lubinTateHom_self_one hπ hf
  map_mul' a b := lubinTateHom_mul hπ hf hf hf a b
  map_zero' := lubinTateHom_zero hπ hf hf
  map_add' a b := lubinTateHom_add hπ hf hf a b

theorem lubinTateEndRingHom_apply (a : A) : lubinTateEndRingHom hπ hf a = lubinTateHom hπ hf hf a :=
  rfl

noncomputable def lubinTateFormalModule : FormalModule (lubinTateFormalGroup hπ hf) where
  smul := lubinTateEndRingHom hπ hf
  linearCoeff_smul a := coeff_one_lubinTateHom hπ hf hf a

noncomputable def lubinTateIso (u : Aˣ) :
    Iso (lubinTateFormalGroup hπ hg) (lubinTateFormalGroup hπ hf) :=
  Iso.ofIsUnit (lubinTateHom hπ hf hg u) (by rw [coeff_one_lubinTateHom]; exact u.isUnit)

theorem lubinTateIso_hom (u : Aˣ) : (lubinTateIso hπ hf hg u).hom = lubinTateHom hπ hf hg u :=
  rfl

end LubinTateHom

end LubinTateGroup

/-! ## Section 6: Frobenius Twist & Adic Approximation -/

section FrobeniusTwist

open IsLocalRing

section Approximation

variable {R : Type*} [CommRing R] (I : Ideal R)

theorem smodEq_pow_iff_sub_mem {x y : R} {n : ℕ} :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule R R)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

theorem exists_limit_of_approx [hI : IsPrecomplete I R] (P : ℕ → R → Prop)
    (hstep : ∀ n x, P n x → ∃ y, y - x ∈ I ^ n ∧ P (n + 1) y) {x₀ : R} (h₀ : P 0 x₀) :
    ∃ x, ∀ n, ∃ y, P n y ∧ x - y ∈ I ^ n := by
  choose g hg hP using hstep
  let f : (n : ℕ) → {x : R // P n x} := fun n =>
    Nat.rec (motive := fun n => {x : R // P n x}) ⟨x₀, h₀⟩
      (fun n x => ⟨g n x.1 x.2, hP n x.1 x.2⟩) n
  have hstep' : ∀ n, (f (n + 1)).1 - (f n).1 ∈ I ^ n := fun n => hg n (f n).1 (f n).2
  have hdiff : ∀ m n, m ≤ n → (f n).1 - (f m).1 ∈ I ^ m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have h1 : (f (n + 1)).1 - (f n).1 ∈ I ^ m := Ideal.pow_le_pow_right hmn (hstep' n)
      have h2 := (I ^ m).add_mem h1 ih
      rwa [sub_add_sub_cancel] at h2
  have htop : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R R) = I ^ n := fun n => by
    rw [smul_eq_mul, Ideal.mul_top]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec hI (f := fun n => (f n).1) (by
    intro m n hmn
    refine SModEq.symm ?_
    rw [SModEq.sub_mem, htop]
    exact hdiff m n hmn)
  refine ⟨L, fun n => ⟨(f n).1, (f n).2, ?_⟩⟩
  have h3 := (hL n).symm
  rwa [SModEq.sub_mem, htop] at h3

theorem exists_eq_zero_of_approx [IsAdicComplete I R] (F : R → R)
    (hF : ∀ n x y, x - y ∈ I ^ n → F x - F y ∈ I ^ n)
    (hstep : ∀ n x, F x ∈ I ^ n → ∃ y, y - x ∈ I ^ n ∧ F y ∈ I ^ (n + 1))
    {m : ℕ} {x₀ : R} (h₀ : F x₀ ∈ I ^ m) : ∃ x, F x = 0 ∧ x - x₀ ∈ I ^ m := by
  obtain ⟨x, hx⟩ := exists_limit_of_approx I (fun n y => F y ∈ I ^ (m + n) ∧ y - x₀ ∈ I ^ m)
    (fun n y ⟨h1, h2⟩ => by
      obtain ⟨z, hz1, hz2⟩ := hstep (m + n) y h1
      refine ⟨z, Ideal.pow_le_pow_right (by omega) hz1, hz2, ?_⟩
      have e : z - x₀ = (z - y) + (y - x₀) := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.pow_le_pow_right (by omega) hz1) h2)
    ⟨by simpa using h₀, by simp⟩
  refine ⟨x, ?_, ?_⟩
  · refine IsHausdorff.haus (I := I) inferInstance _ fun n => ?_
    rw [smodEq_pow_iff_sub_mem, sub_zero]
    obtain ⟨y, ⟨hy1, _⟩, hy⟩ := hx n
    have e : F x = (F x - F y) + F y := by ring
    rw [e]
    exact Ideal.add_mem _ (hF n x y hy) (Ideal.pow_le_pow_right (by omega) hy1)
  · obtain ⟨y, ⟨_, hy2⟩, hy⟩ := hx m
    have e : x - x₀ = (x - y) + (y - x₀) := by ring
    rw [e]
    exact Ideal.add_mem _ hy hy2

end Approximation

section HidaSetting

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]

theorem isLocalHom_of_map_maximalIdeal
    (hunr : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    IsLocalHom (algebraMap A B) := by
  refine ⟨fun a ha => ?_⟩
  by_contra h
  have hm : a ∈ maximalIdeal A := (mem_maximalIdeal a).2 h
  have := Ideal.mem_map_of_mem (algebraMap A B) hm
  rw [hunr] at this
  exact (mem_maximalIdeal _).1 this ha

theorem irreducible_algebraMap (hunr : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
    {π : A} (hπ : Irreducible π) : Irreducible (algebraMap A B π) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at hπ ⊢
  rw [← hunr, hπ, Ideal.map_span, Set.image_singleton]

theorem mem_maximalIdeal_pow_iff {ϖ : B} (hϖ : Irreducible ϖ) {x : B} {n : ℕ} :
    x ∈ maximalIdeal B ^ n ↔ ϖ ^ n ∣ x := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

end HidaSetting

section Solve

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  [Finite (ResidueField A)] [IsAlgClosed (ResidueField B)]
  (σ : B →ₐ[A] B)
  (hσ : ∀ x : B, residue B (σ x) = residue B x ^ Nat.card (ResidueField A))

theorem one_lt_card_residueField : 1 < Nat.card (ResidueField A) :=
  Finite.one_lt_card

include hσ in
theorem exists_residue_sub_mul_add_eq_zero (v w : B) :
    ∃ z : B, residue B (σ z - v * z + w) = 0 := by
  open Polynomial in
  set q := Nat.card (ResidueField A)
  have hq : 1 < q := one_lt_card_residueField
  set a := residue B v
  set b := residue B w
  have hlow : (C b - C a * X : (ResidueField B)[X]).degree < (X ^ q : (ResidueField B)[X]).degree := by
    rw [degree_X_pow]
    refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt degree_C_le (by exact_mod_cast (by omega : 0 < q))
    · exact lt_of_le_of_lt (degree_C_mul_X_le a) (by exact_mod_cast hq)
  have hdeg : (X ^ q + (C b - C a * X) : (ResidueField B)[X]).degree = q := by
    rw [degree_add_eq_left_of_degree_lt hlow, degree_X_pow]
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (X ^ q + (C b - C a * X) : (ResidueField B)[X])
    (by rw [hdeg]; exact_mod_cast (by omega : q ≠ 0))
  obtain ⟨z', rfl⟩ := residue_surjective z
  refine ⟨z', ?_⟩
  simp only [IsRoot, eval_add, eval_sub, eval_pow, eval_X, eval_C, eval_mul] at hz
  rw [map_add, map_sub, map_mul, hσ]
  linear_combination hz

variable {π : A} (hπB : Irreducible (algebraMap A B π))
include hσ hπB

theorem exists_sub_mul_eq_of_mem [IsAdicComplete (maximalIdeal B) B] (v c : B) {m : ℕ} {x₀ : B}
    (h₀ : σ x₀ - v * x₀ - c ∈ maximalIdeal B ^ m) :
    ∃ x, σ x - v * x = c ∧ x - x₀ ∈ maximalIdeal B ^ m := by
  set ϖ := algebraMap A B π
  have hσϖ : ∀ (n : ℕ) (t : B), σ (ϖ ^ n * t) = ϖ ^ n * σ t := by
    intro n t
    rw [map_mul, map_pow, AlgHom.commutes]
  obtain ⟨x, hx, hxm⟩ := exists_eq_zero_of_approx (maximalIdeal B) (fun x => σ x - v * x - c)
    (fun n x y hxy => by
      rw [mem_maximalIdeal_pow_iff hπB] at hxy ⊢
      obtain ⟨t, ht⟩ := hxy
      refine ⟨σ t - v * t, ?_⟩
      have : x = y + ϖ ^ n * t := by rw [← ht]; ring
      simp only [this, map_add, hσϖ]
      ring)
    (fun n x hx => by
      rw [mem_maximalIdeal_pow_iff hπB] at hx
      obtain ⟨w, hw⟩ := hx
      obtain ⟨z, hz⟩ := exists_residue_sub_mul_add_eq_zero σ hσ v w
      rw [residue_eq_zero_iff, hπB.maximalIdeal_eq, Ideal.mem_span_singleton] at hz
      obtain ⟨t, ht⟩ := hz
      refine ⟨x + ϖ ^ n * z, ?_, ?_⟩
      · rw [mem_maximalIdeal_pow_iff hπB]
        exact ⟨z, by ring⟩
      · rw [mem_maximalIdeal_pow_iff hπB]
        refine ⟨t, ?_⟩
        simp only [map_add, hσϖ]
        have e : σ x - v * x - c = ϖ ^ n * w := hw
        linear_combination e + ϖ ^ n * ht)
    h₀
  exact ⟨x, sub_eq_zero.1 (by simpa using hx), hxm⟩

theorem exists_sub_mul_eq [IsAdicComplete (maximalIdeal B) B] (v c : B) :
    ∃ x, σ x - v * x = c := by
  obtain ⟨x, hx, -⟩ := exists_sub_mul_eq_of_mem σ hσ hπB v c (m := 0) (x₀ := 0) (by simp)
  exact ⟨x, hx⟩

theorem exists_units_eq_mul [IsAdicComplete (maximalIdeal B) B] (v : Bˣ) :
    ∃ η : Bˣ, σ η = v * η := by
  set q := Nat.card (ResidueField A)
  have hq : 1 < q := one_lt_card_residueField
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (residue B v) (n := q - 1) (by omega)
  have hv0 : residue B v ≠ 0 := (residue_ne_zero_iff_isUnit _).2 v.isUnit
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hz
    exact hv0 hz.symm
  obtain ⟨z', rfl⟩ := residue_surjective z
  have h₀ : σ z' - v * z' - 0 ∈ maximalIdeal B ^ 1 := by
    rw [pow_one, ← residue_eq_zero_iff, sub_zero, map_sub, map_mul, hσ]
    have e : residue B z' ^ q = residue B z' ^ (q - 1) * residue B z' := by
      rw [← pow_succ]; congr 1; omega
    rw [e, hz, sub_self]
  obtain ⟨x, hx, hxm⟩ := exists_sub_mul_eq_of_mem σ hσ hπB v 0 h₀
  have hxu : IsUnit x := by
    rw [← residue_ne_zero_iff_isUnit]
    rw [pow_one, ← residue_eq_zero_iff, map_sub, sub_eq_zero] at hxm
    rwa [hxm]
  refine ⟨hxu.unit, ?_⟩
  simpa [sub_eq_zero] using hx

end Solve

section Kernel

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  [Finite (ResidueField A)] [IsAlgClosed (ResidueField B)] [IsAdicComplete (maximalIdeal B) B]
  (hunr : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
  (σ : B →ₐ[A] B)
  (hσ : ∀ x : B, residue B (σ x) = residue B x ^ Nat.card (ResidueField A))

include hunr hσ

theorem surjective_sub_self : Function.Surjective fun x : B => σ x - x := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  intro c
  obtain ⟨x, hx⟩ := exists_sub_mul_eq σ hσ (irreducible_algebraMap hunr hπ) 1 c
  exact ⟨x, by simpa using hx⟩

theorem surjective_div_self :
    Function.Surjective fun u : Bˣ => Units.map (σ : B →* B) u / u := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  intro v
  obtain ⟨η, hη⟩ := exists_units_eq_mul σ hσ (irreducible_algebraMap hunr hπ) v
  refine ⟨η, ?_⟩
  rw [div_eq_iff_eq_mul]
  ext
  simpa using hη

end Kernel

end FrobeniusTwist

/-! ## Section 7: Twisted Lifts -/

section TwistedLift

open MvPowerSeries

section BaseChange

variable {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) {ι : Type*}

theorem map_substEach (g : PowerSeries A) (i : ι) :
    map φ (substEach g i : MvPowerSeries ι A) = substEach (PowerSeries.map φ g) i := by
  rw [substEach_apply, substEach_apply, PowerSeries.map_subst (PowerSeries.HasSubst.X i), map_X]

theorem IsLubinTateLift.map [Finite ι] {f g : PowerSeries A}
    (hg0 : PowerSeries.constantCoeff g = 0) {ℓ Φ : MvPowerSeries ι A}
    (h : IsLubinTateLift f g ℓ Φ) :
    IsLubinTateLift (PowerSeries.map φ f) (PowerSeries.map φ g) (MvPowerSeries.map φ ℓ)
      (MvPowerSeries.map φ Φ) := by
  obtain ⟨h0, h2, he⟩ := h
  refine ⟨by rw [constantCoeff_map, h0, map_zero], ?_, ?_⟩
  · rw [← map_sub]
    exact h2.trans (le_order_map φ)
  · have := congrArg (MvPowerSeries.map φ) he
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero h0),
      MvPowerSeries.map_subst (hasSubst_substEach hg0)] at this
    rw [this]
    congr 1
    funext i
    exact map_substEach φ g i

end BaseChange

section Twisted

variable {B : Type*} [CommRing B] (σ : B →+* B) {ι : Type*}

noncomputable def twistedDefect (g f : PowerSeries B) (φ : MvPowerSeries ι B) :
    MvPowerSeries ι B :=
  PowerSeries.subst (dropConst φ) g - subst (substEach f) (map σ (dropConst φ))

def twistOp (u π : B) (d : ℕ) (b : B) : B :=
  u * b - π ^ (d - 1) * σ b

noncomputable def twistStep (u π : B) (g f : PowerSeries B) (ℓ φ : MvPowerSeries ι B) :
    MvPowerSeries ι B :=
  fun e => if e.degree ≤ 1 then coeff e ℓ else
    Function.invFun (twistOp σ u π e.degree)
      (twistOp σ u π e.degree (coeff e φ) - divBy π (coeff e (twistedDefect σ g f φ)))

theorem coeff_twistStep (u π : B) (g f : PowerSeries B) (ℓ φ : MvPowerSeries ι B) (e : ι →₀ ℕ) :
    coeff e (twistStep σ u π g f ℓ φ) = if e.degree ≤ 1 then coeff e ℓ else
      Function.invFun (twistOp σ u π e.degree)
        (twistOp σ u π e.degree (coeff e φ) - divBy π (coeff e (twistedDefect σ g f φ))) :=
  rfl

def IsTwistedLift (g f : PowerSeries B) (ℓ φ : MvPowerSeries ι B) : Prop :=
  constantCoeff φ = 0 ∧ (2 : ℕ∞) ≤ order (φ - ℓ) ∧
    PowerSeries.subst φ g = subst (substEach f) (map σ φ)

variable [Finite ι] {u π : B} {f g : PowerSeries B}
  (hf0 : PowerSeries.constantCoeff f = 0) (hf1 : PowerSeries.coeff 1 f = π)
  (hg0 : PowerSeries.constantCoeff g = 0) (hg1 : PowerSeries.coeff 1 g = u * π)

include hf0 hf1 hg0 hg1 in
theorem coeff_twistedDefect_sub_twistedDefect {φ ψ : MvPowerSeries ι B} {n : ℕ}
    (h : (n : ℕ∞) ≤ order (φ - ψ)) {e : ι →₀ ℕ} (he : e.degree ≤ n) :
    coeff e (twistedDefect σ g f φ) - coeff e (twistedDefect σ g f ψ) =
      u * π * coeff e (dropConst φ - dropConst ψ) -
        π ^ e.degree * σ (coeff e (dropConst φ - dropConst ψ)) := by
  have hδ : (n : ℕ∞) ≤ order (dropConst φ - dropConst ψ) := by
    refine nat_le_order fun d hd => ?_
    by_cases hd0 : d = 0
    · simp [hd0, coeff_zero_eq_constantCoeff_apply, constantCoeff_dropConst]
    · rw [map_sub, coeff_dropConst _ hd0, coeff_dropConst _ hd0, ← map_sub]
      exact coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)
  have hδσ : (n : ℕ∞) ≤ order (map σ (dropConst φ - dropConst ψ)) := hδ.trans (le_order_map σ)
  have h1 := le_order_subst_substEach_sub_rescale hf0 hf1 hδσ
  have h2 := le_order_subst_sub_subst_sub_C_mul hg0 hg1 (constantCoeff_dropConst φ)
    (constantCoeff_dropConst ψ) hδ
  have h3 := le_order_sub h2 h1
  have hlt : (e.degree : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_of_le he
  have h0 := coeff_of_lt_order (hlt.trans_le h3)
  rw [map_sub (MvPowerSeries.map σ), subst_sub (hasSubst_substEach hf0)] at h0
  simp only [twistedDefect, map_sub, coeff_rescale_const, coeff_C_mul, coeff_map] at h0 ⊢
  linear_combination h0

variable (hreg : ∀ x : B, π * x = 0 → x = 0)
  (hT : ∀ d : ℕ, 2 ≤ d → Function.Bijective (twistOp σ u π d))
  (hdiv : ∀ (φ : MvPowerSeries ι B) (e : ι →₀ ℕ), π ∣ coeff e (twistedDefect σ g f φ))

include hf0 hf1 hg0 hg1 hreg hdiv in
theorem twistStep_contract (ℓ φ ψ : MvPowerSeries ι B) (n : ℕ)
    (h : (n : ℕ∞) ≤ order (φ - ψ)) :
    ((n + 1 : ℕ) : ℕ∞) ≤ order (twistStep σ u π g f ℓ φ - twistStep σ u π g f ℓ ψ) := by
  refine nat_le_order fun e he => ?_
  have he' : e.degree ≤ n := Nat.lt_succ_iff.1 he
  rw [map_sub, coeff_twistStep, coeff_twistStep]
  split_ifs with h1
  · exact sub_self _
  · replace h1 := not_le.1 h1
    have he0 : e ≠ 0 := by
      rintro rfl
      simp at h1
    have hkey := coeff_twistedDefect_sub_twistedDefect σ hf0 hf1 hg0 hg1 h he'
    rw [map_sub, coeff_dropConst _ he0, coeff_dropConst _ he0, map_sub] at hkey
    have hd : π * π ^ (e.degree - 1) = π ^ e.degree := by
      rw [← pow_succ']
      congr 1
      omega
    have harg : twistOp σ u π e.degree (coeff e φ) - divBy π (coeff e (twistedDefect σ g f φ)) =
        twistOp σ u π e.degree (coeff e ψ) - divBy π (coeff e (twistedDefect σ g f ψ)) := by
      rw [← sub_eq_zero]
      apply hreg
      have e1 := mul_divBy (hdiv φ e)
      have e2 := mul_divBy (hdiv ψ e)
      simp only [twistOp]
      linear_combination (-1 : B) * hkey - (σ (coeff e φ) - σ (coeff e ψ)) * hd - e1 + e2
    rw [harg, sub_self]

include hf0 hg0 in
theorem twistedDefect_zero : twistedDefect σ g f (0 : MvPowerSeries ι B) = 0 := by
  have h0 : dropConst (0 : MvPowerSeries ι B) = 0 := by simp [dropConst]
  rw [twistedDefect, h0, map_zero, ← coe_substAlgHom (hasSubst_substEach hf0), map_zero,
    PowerSeries.subst_zero_of_constantCoeff_zero hg0, sub_zero]

omit [Finite ι] in
theorem eq_coeff_of_two_le_order_sub {φ ψ : MvPowerSeries ι B}
    (h : (2 : ℕ∞) ≤ order (φ - ψ)) {e : ι →₀ ℕ} (he : e.degree ≤ 1) : coeff e φ = coeff e ψ := by
  have he2 : (e.degree : ℕ∞) < 2 := by
    have : e.degree < 2 := by omega
    exact_mod_cast this
  have := coeff_of_lt_order (lt_of_lt_of_le he2 h)
  rwa [map_sub, sub_eq_zero] at this

omit [Finite ι] in
theorem constantCoeff_eq_zero_of_two_le_order_sub {φ ψ : MvPowerSeries ι B}
    (h : (2 : ℕ∞) ≤ order (φ - ψ)) (hφ : constantCoeff φ = 0) : constantCoeff ψ = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← eq_coeff_of_two_le_order_sub h (by simp),
    coeff_zero_eq_constantCoeff_apply, hφ]

include hf0 hf1 hg0 hg1 hreg hT hdiv in
theorem twistStep_eq_self_iff {ℓ : MvPowerSeries ι B} (hℓ : constantCoeff ℓ = 0)
    (hℓ1 : ∀ e : ι →₀ ℕ, e.degree = 1 → u * π * coeff e ℓ = π * σ (coeff e ℓ))
    (φ : MvPowerSeries ι B) :
    twistStep σ u π g f ℓ φ = φ ↔
      (2 : ℕ∞) ≤ order (φ - ℓ) ∧ PowerSeries.subst φ g = subst (substEach f) (map σ φ) := by
  have hdivBy0 : divBy π 0 = 0 := hreg _ (mul_divBy (dvd_zero π))
  have hd0 : dropConst (0 : MvPowerSeries ι B) = 0 := by simp [dropConst]
  constructor
  · intro hs
    have hlin : ∀ e : ι →₀ ℕ, e.degree ≤ 1 → coeff e φ = coeff e ℓ := by
      intro e he
      have := congrArg (coeff e) hs
      rw [coeff_twistStep, if_pos he] at this
      exact this.symm
    have hφ0 : constantCoeff φ = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, hlin 0 (by simp),
        coeff_zero_eq_constantCoeff_apply, hℓ]
    have hdef : twistedDefect σ g f φ = 0 := by
      ext e
      rw [map_zero]
      by_cases he : e.degree ≤ 1
      · have h1 : ((1 : ℕ) : ℕ∞) ≤ order (φ - 0) := by
          rw [sub_zero, Nat.cast_one]
          exact one_le_order_iff_constCoeff_eq_zero.2 hφ0
        have := coeff_twistedDefect_sub_twistedDefect σ hf0 hf1 hg0 hg1 h1 he
        rw [twistedDefect_zero σ hf0 hg0, map_zero, sub_zero] at this
        rw [this]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 he with h | h
        · rw [Finsupp.degree_eq_zero_iff] at h
          subst h
          simp [coeff_zero_eq_constantCoeff_apply, constantCoeff_dropConst]
        · have he0 : e ≠ 0 := by
            rintro rfl
            simp at h
          rw [hd0, sub_zero, coeff_dropConst _ he0, h, pow_one, hlin e (by omega), hℓ1 e h,
            sub_self]
      · have := congrArg (coeff e) hs
        rw [coeff_twistStep, if_neg he] at this
        have hT' := hT e.degree (by omega)
        have h2 := congrArg (twistOp σ u π e.degree) this
        rw [Function.invFun_eq (hT'.2 _)] at h2
        have hq : divBy π (coeff e (twistedDefect σ g f φ)) = 0 := by
          linear_combination -h2
        rw [← mul_divBy (hdiv φ e), hq, mul_zero]
    have h2 : ((2 : ℕ) : ℕ∞) ≤ order (φ - ℓ) :=
      nat_le_order fun e he => by rw [map_sub, hlin e (by omega), sub_self]
    refine ⟨by exact_mod_cast h2, ?_⟩
    rw [twistedDefect, dropConst_of_constantCoeff_eq_zero hφ0, sub_eq_zero] at hdef
    exact hdef
  · rintro ⟨h2, heq⟩
    have hlin : ∀ e : ι →₀ ℕ, e.degree ≤ 1 → coeff e φ = coeff e ℓ :=
      fun e he => eq_coeff_of_two_le_order_sub h2 he
    have hφ0 : constantCoeff φ = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, hlin 0 (by simp),
        coeff_zero_eq_constantCoeff_apply, hℓ]
    have hdef : twistedDefect σ g f φ = 0 := by
      rw [twistedDefect, dropConst_of_constantCoeff_eq_zero hφ0, heq, sub_self]
    ext e
    rw [coeff_twistStep]
    split_ifs with he
    · exact (hlin e he).symm
    · rw [hdef, map_zero, hdivBy0, sub_zero]
      exact Function.leftInverse_invFun (hT e.degree (by omega)).1 _

include hf0 hf1 hg0 hg1 hreg hT hdiv in
theorem existsUnique_twisted {ℓ : MvPowerSeries ι B} (hℓ : constantCoeff ℓ = 0)
    (hℓ1 : ∀ e : ι →₀ ℕ, e.degree = 1 → u * π * coeff e ℓ = π * σ (coeff e ℓ)) :
    ∃! φ : MvPowerSeries ι B,
      (2 : ℕ∞) ≤ order (φ - ℓ) ∧ PowerSeries.subst φ g = subst (substEach f) (map σ φ) := by
  obtain ⟨φ, hφ, huniq⟩ := existsUnique_fixedPoint (twistStep σ u π g f ℓ)
    (twistStep_contract σ hf0 hf1 hg0 hg1 hreg hdiv ℓ)
  exact ⟨φ, (twistStep_eq_self_iff σ hf0 hf1 hg0 hg1 hreg hT hdiv hℓ hℓ1 φ).1 hφ,
    fun ψ hψ => huniq ψ ((twistStep_eq_self_iff σ hf0 hf1 hg0 hg1 hreg hT hdiv hℓ hℓ1 ψ).2 hψ)⟩

include hf0 hf1 hg0 hg1 in
theorem IsTwistedLift.linear {ℓ φ : MvPowerSeries ι B} (h : IsTwistedLift σ g f ℓ φ)
    (e : ι →₀ ℕ) (he : e.degree = 1) : u * π * coeff e ℓ = π * σ (coeff e ℓ) := by
  obtain ⟨h0, h2, heq⟩ := h
  have hdef : twistedDefect σ g f φ = 0 := by
    rw [twistedDefect, dropConst_of_constantCoeff_eq_zero h0, heq, sub_self]
  have h1 : ((1 : ℕ) : ℕ∞) ≤ order (φ - 0) := by
    rw [sub_zero, Nat.cast_one]
    exact one_le_order_iff_constCoeff_eq_zero.2 h0
  have := coeff_twistedDefect_sub_twistedDefect σ hf0 hf1 hg0 hg1 h1 he.le
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at he
  have hd0 : dropConst (0 : MvPowerSeries ι B) = 0 := by simp [dropConst]
  rw [hdef, twistedDefect_zero σ hf0 hg0, map_zero, sub_zero, hd0, sub_zero, coeff_dropConst _ he0,
    he, pow_one, eq_coeff_of_two_le_order_sub h2 he.le] at this
  linear_combination -this

include hf0 hf1 hg0 hg1 hreg hT hdiv in
theorem IsTwistedLift.unique {ℓ φ ψ : MvPowerSeries ι B} (hφ : IsTwistedLift σ g f ℓ φ)
    (hψ : IsTwistedLift σ g f ℓ ψ) : φ = ψ :=
  (existsUnique_twisted σ hf0 hf1 hg0 hg1 hreg hT hdiv
    (constantCoeff_eq_zero_of_two_le_order_sub hφ.2.1 hφ.1)
    (hφ.linear σ hf0 hf1 hg0 hg1)).unique ⟨hφ.2.1, hφ.2.2⟩ ⟨hψ.2.1, hψ.2.2⟩

end Twisted

section CompositionTwisted

variable {B : Type*} [CommRing B] (σ : B →+* B) {ι τ : Type*} [Finite ι] [Finite τ]
  {f g h : PowerSeries B}

theorem IsTwistedLift.comp_lift (hf0 : PowerSeries.constantCoeff f = 0)
    (hh0 : PowerSeries.constantCoeff h = 0) {ℓ Φ : MvPowerSeries τ B}
    (hΦ : IsTwistedLift σ g f ℓ Φ) {v u : τ → MvPowerSeries ι B}
    (hu : ∀ j, IsLubinTateLift f h (v j) (u j)) (hσu : ∀ j, map σ (u j) = u j) :
    IsTwistedLift σ g h (subst v ℓ) (subst u Φ) := by
  obtain ⟨hΦ0, hΦ2, hΦe⟩ := hΦ
  have hu0 : ∀ j, constantCoeff (u j) = 0 := fun j => (hu j).1
  have hus : HasSubst u := hasSubst_of_constantCoeff_zero hu0
  have hℓ0 : constantCoeff ℓ = 0 := constantCoeff_eq_zero_of_two_le_order_sub hΦ2 hΦ0
  have hv0 : ∀ j, constantCoeff (v j) = 0 := fun j =>
    constantCoeff_eq_zero_of_two_le_order_sub (hu j).2.1 (hu0 j)
  refine ⟨constantCoeff_subst_eq_zero hus hu0 hΦ0,
    two_le_order_subst_sub_subst_of hΦ2 hℓ0 hu0 hv0 (fun j => (hu j).2.1), ?_⟩
  have hΦs : PowerSeries.HasSubst Φ := PowerSeries.HasSubst.of_constantCoeff_zero hΦ0
  have hmu : (fun i => map σ (u i)) = u := funext hσu
  rw [← subst_powerSeries_subst hΦs hus, hΦe, subst_comp_subst_apply (hasSubst_substEach hf0) hus,
    map_subst hus, hmu, subst_comp_subst_apply hus (hasSubst_substEach hh0)]
  congr 1
  funext j
  rw [substEach_apply, subst_powerSeries_subst (PowerSeries.HasSubst.X j) hus, subst_X hus]
  exact (hu j).2.2

theorem IsLubinTateLift.comp_twisted (hf0 : PowerSeries.constantCoeff f = 0)
    (hh0 : PowerSeries.constantCoeff h = 0) {ℓ Ψ : MvPowerSeries τ B}
    (hΨ : IsLubinTateLift g h ℓ Ψ) (hσΨ : MvPowerSeries.map σ Ψ = Ψ) {w v : τ → MvPowerSeries ι B}
    (hv : ∀ j, IsTwistedLift σ h f (w j) (v j)) :
    IsTwistedLift σ g f (subst w ℓ) (subst v Ψ) := by
  obtain ⟨hΨ0, hΨ2, hΨe⟩ := hΨ
  have hv0 : ∀ j, constantCoeff (v j) = 0 := fun j => (hv j).1
  have hvs : HasSubst v := hasSubst_of_constantCoeff_zero hv0
  have hℓ0 : constantCoeff ℓ = 0 := constantCoeff_eq_zero_of_two_le_order_sub hΨ2 hΨ0
  have hw0 : ∀ j, constantCoeff (w j) = 0 := fun j =>
    constantCoeff_eq_zero_of_two_le_order_sub (hv j).2.1 (hv0 j)
  refine ⟨constantCoeff_subst_eq_zero hvs hv0 hΨ0,
    two_le_order_subst_sub_subst_of hΨ2 hℓ0 hv0 hw0 (fun j => (hv j).2.1), ?_⟩
  have hΨs : PowerSeries.HasSubst Ψ := PowerSeries.HasSubst.of_constantCoeff_zero hΨ0
  have hσvs : HasSubst (fun j => MvPowerSeries.map σ (v j)) :=
    hasSubst_of_constantCoeff_zero fun j => by rw [constantCoeff_map, hv0 j, map_zero]
  rw [← subst_powerSeries_subst hΨs hvs, hΨe, subst_comp_subst_apply (hasSubst_substEach hh0) hvs,
    map_subst hvs, hσΨ, subst_comp_subst_apply hσvs (hasSubst_substEach hf0)]
  congr 1
  funext j
  rw [substEach_apply, subst_powerSeries_subst (PowerSeries.HasSubst.X j) hvs, subst_X hvs]
  exact (hv j).2.2

theorem IsTwistedLift.map (hf0 : PowerSeries.constantCoeff f = 0)
    (hσf : PowerSeries.map σ f = f) (hσg : PowerSeries.map σ g = g) {ℓ φ : MvPowerSeries ι B}
    (hφ : IsTwistedLift σ g f ℓ φ) : IsTwistedLift σ g f (map σ ℓ) (map σ φ) := by
  obtain ⟨h0, h2, he⟩ := hφ
  refine ⟨by rw [constantCoeff_map, h0, map_zero], ?_, ?_⟩
  · rw [← map_sub]
    exact h2.trans (le_order_map σ)
  · have := congrArg (MvPowerSeries.map σ) he
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero h0), hσg,
      map_subst (hasSubst_substEach hf0)] at this
    rw [this]
    congr 1
    funext i
    rw [map_substEach σ f i, hσf]

end CompositionTwisted

end TwistedLift

/-! ## Section 8: Isomorphisms Over Completed Unramified Extensions -/

section OverUnramified

open MvPowerSeries IsLocalRing

theorem powerSeries_constantCoeff_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : PowerSeries R) :
    PowerSeries.constantCoeff (PowerSeries.map φ f) = φ (PowerSeries.constantCoeff f) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem pair_eq_substEach {R : Type*} [CommRing R] (k : PowerSeries R) :
    (![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) k,
      PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) R) k] : Fin 2 → MvPowerSeries (Fin 2) R) =
      substEach k := by
  funext i
  fin_cases i <;> rfl

namespace Hom

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {F G : FormalGroup R}

noncomputable def map (h : Hom F G) : Hom (F.map φ) (G.map φ) where
  toPowerSeries := PowerSeries.map φ h.toPowerSeries
  constantCoeff_eq_zero := by
    rw [powerSeries_constantCoeff_map, h.constantCoeff_eq_zero, map_zero]
  map_add := by
    have := congrArg (MvPowerSeries.map φ) h.map_add
    rw [pair_eq_substEach, PowerSeries.map_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff),
      MvPowerSeries.map_subst (hasSubst_substEach h.constantCoeff_eq_zero)] at this
    rw [pair_eq_substEach, FormalGroup.map_toPowerSeries, FormalGroup.map_toPowerSeries, this]
    congr 1
    funext i
    exact map_substEach φ _ i

theorem map_toPowerSeries (h : Hom F G) :
    (h.map φ).toPowerSeries = PowerSeries.map φ h.toPowerSeries :=
  rfl

end Hom

section Fixed

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (σ : B →ₐ[A] B)

theorem map_sigma_map_algebraMap {ι : Type*} (Φ : MvPowerSeries ι A) :
    MvPowerSeries.map (σ : B →+* B) (MvPowerSeries.map (algebraMap A B) Φ) =
      MvPowerSeries.map (algebraMap A B) Φ := by
  ext n
  simp [coeff_map]

theorem powerSeries_map_sigma_map_algebraMap (f : PowerSeries A) :
    PowerSeries.map (σ : B →+* B) (PowerSeries.map (algebraMap A B) f) =
      PowerSeries.map (algebraMap A B) f :=
  map_sigma_map_algebraMap σ f

theorem map_C_mul_X {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a : R) :
    MvPowerSeries.map φ (PowerSeries.C a * PowerSeries.X : PowerSeries R) =
      PowerSeries.C (φ a) * PowerSeries.X := by
  change PowerSeries.map φ (PowerSeries.C a * PowerSeries.X) = _
  simp

theorem coeff_one_C_mul_X {R : Type*} [CommRing R] (a : R) :
    PowerSeries.coeff 1 (PowerSeries.C a * PowerSeries.X) = a := by
  simp

theorem constantCoeff_C_mul_X {R : Type*} [CommRing R] (a : R) :
    constantCoeff (PowerSeries.C a * PowerSeries.X : MvPowerSeries Unit R) = 0 := by
  change PowerSeries.constantCoeff (PowerSeries.C a * PowerSeries.X) = 0
  simp

theorem C_unit_eq {R : Type*} [CommRing R] (a : R) :
    (MvPowerSeries.C a : MvPowerSeries Unit R) = PowerSeries.C a :=
  rfl

end Fixed

section Hypotheses

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Finite (ResidueField A)]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  (σ : B →ₐ[A] B)

omit [IsDomain A] [IsDiscreteValuationRing A] [Finite (ResidueField A)] in
theorem bijective_twistOp [IsAdicComplete (maximalIdeal B) B] {π : A}
    (hπB : Irreducible (algebraMap A B π)) {v : B} (hv : IsUnit v) {d : ℕ} (hd : 2 ≤ d) :
    Function.Bijective (twistOp (σ : B →+* B) v (algebraMap A B π) d) := by
  set ϖ := algebraMap A B π
  have hσc : ∀ x, (σ : B →+* B) x = σ x := fun _ => rfl
  have hσϖ : ∀ (n : ℕ) (t : B), σ (ϖ ^ n * t) = ϖ ^ n * σ t := by
    intro n t
    rw [map_mul, map_pow, AlgHom.commutes]
  have hadd : ∀ x y, twistOp (σ : B →+* B) v ϖ d x - twistOp (σ : B →+* B) v ϖ d y =
      twistOp (σ : B →+* B) v ϖ d (x - y) := by
    intro x y
    simp only [twistOp, map_sub]
    ring
  have hpow : ϖ ^ (d - 1) = ϖ ^ (d - 2) * ϖ := by
    rw [← pow_succ]
    congr 1
    omega
  constructor
  · intro x y hxy
    rw [← sub_eq_zero]
    by_contra hz0
    have hz : v * (x - y) = ϖ ^ (d - 1) * σ (x - y) := by
      have := hadd x y
      rw [hxy, sub_self] at this
      simp only [twistOp, hσc] at this
      linear_combination -this
    obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz0 hπB
    rw [hw, map_mul, map_pow, AlgHom.commutes] at hz
    have h1 : v * w = ϖ ^ (d - 1) * σ w :=
      mul_right_cancel₀ (pow_ne_zero n hπB.ne_zero) (by linear_combination hz)
    have hunit : IsUnit (ϖ ^ (d - 1) * σ w) := h1 ▸ hv.mul w.isUnit
    have hdvd : ϖ ∣ ϖ ^ (d - 1) * σ w := by
      rw [hpow, mul_assoc]
      exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
    exact hπB.not_isUnit (isUnit_of_dvd_unit hdvd hunit)
  · intro c
    obtain ⟨x, hx, -⟩ := exists_eq_zero_of_approx (maximalIdeal B)
      (fun x => twistOp (σ : B →+* B) v ϖ d x - c)
      (fun n x y hxy => by
        rw [mem_maximalIdeal_pow_iff hπB] at hxy ⊢
        obtain ⟨t, ht⟩ := hxy
        refine ⟨v * t - ϖ ^ (d - 1) * σ t, ?_⟩
        have : x = y + ϖ ^ n * t := by rw [← ht]; ring
        simp only [twistOp, hσc, this, map_add, hσϖ]
        ring)
      (fun n x hx => by
        rw [mem_maximalIdeal_pow_iff hπB] at hx
        obtain ⟨w, hw⟩ := hx
        obtain ⟨v', hv'⟩ := hv.exists_right_inv
        refine ⟨x - ϖ ^ n * (v' * w), ?_, ?_⟩
        · rw [mem_maximalIdeal_pow_iff hπB]
          exact ⟨-(v' * w), by ring⟩
        · rw [mem_maximalIdeal_pow_iff hπB]
          refine ⟨ϖ ^ (d - 2) * σ (v' * w), ?_⟩
          simp only [twistOp, hσc, map_sub, hσϖ] at hw ⊢
          linear_combination hw - ϖ ^ n * w * hv' + ϖ ^ n * σ (v' * w) * hpow)
      (m := 0) (x₀ := 0) (by simp)
    exact ⟨x, sub_eq_zero.1 hx⟩

omit [Finite (ResidueField A)] in
theorem map_residue_map_eq_X_pow {π : A} (hmem : algebraMap A B π ∈ maximalIdeal B)
    {f : PowerSeries A} (hf : IsLubinTateSeries π f) :
    PowerSeries.map (residue B) (PowerSeries.map (algebraMap A B) f) =
      PowerSeries.X ^ Nat.card (ResidueField A) := by
  ext n
  obtain ⟨c, hc⟩ := hf.dvd_coeff_sub n
  rw [map_sub] at hc
  have h1 : PowerSeries.coeff n f =
      PowerSeries.coeff n (PowerSeries.X ^ Nat.card (ResidueField A) : PowerSeries A) + π * c := by
    rw [← hc]
    ring
  have h0 : residue B (algebraMap A B π) = 0 := (residue_eq_zero_iff _).2 hmem
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, h1, map_add, map_add, map_mul, map_mul, h0,
    zero_mul, add_zero, PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow]
  split_ifs <;> simp

variable (hunr : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
  (hσ : ∀ x : B, residue B (σ x) = residue B x ^ Nat.card (ResidueField A))
include hunr hσ

theorem dvd_coeff_twistedDefect {π : A} (hπB : Irreducible (algebraMap A B π)) {u : A}
    {f g : PowerSeries A} (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries (u * π) g)
    {ι : Type*} [Finite ι] (φ : MvPowerSeries ι B) (e : ι →₀ ℕ) :
    algebraMap A B π ∣ coeff e (twistedDefect (σ : B →+* B) (PowerSeries.map (algebraMap A B) g)
      (PowerSeries.map (algebraMap A B) f) φ) := by
  classical
  have := isLocalHom_of_map_maximalIdeal hunr
  let := Fintype.ofFinite (ResidueField A)
  obtain ⟨p, hcp, n, hp, hcard⟩ := FiniteField.card' (ResidueField A)
  have := hcp
  have : Fact p.Prime := ⟨hp⟩
  have : CharP (ResidueField B) p :=
    CharP.of_ringHom_of_ne_zero (ResidueField.map (algebraMap A B)) p hp.ne_zero
  have hq : Nat.card (ResidueField A) = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hq0 : p ^ (n : ℕ) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hmemf : algebraMap A B π ∈ maximalIdeal B :=
    (mem_maximalIdeal _).2 hπB.not_isUnit
  have hmemg : algebraMap A B (u * π) ∈ maximalIdeal B := by
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ hmemf
  have hf0 : PowerSeries.constantCoeff (PowerSeries.map (algebraMap A B) f) = 0 := by
    rw [powerSeries_constantCoeff_map, hf.constantCoeff_eq_zero, map_zero]
  have hcomp : (residue B).comp (σ : B →+* B) =
      (iterateFrobenius (ResidueField B) p n).comp (residue B) := by
    ext x
    simp only [RingHom.comp_apply, iterateFrobenius_def]
    rw [← hq]
    exact hσ x
  rw [← residue_eq_zero_iff_dvd hπB, ← coeff_map]
  set ψ := MvPowerSeries.map (residue B) (dropConst φ)
  have hs : PowerSeries.HasSubst (dropConst φ) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_dropConst φ)
  have hs' : PowerSeries.HasSubst ψ := PowerSeries.HasSubst.of_constantCoeff_zero (by
    rw [constantCoeff_map, constantCoeff_dropConst, map_zero])
  have hE := hasSubst_substEach (σ := ι) hf0
  have hmapE : (fun i => MvPowerSeries.map (residue B)
      (substEach (PowerSeries.map (algebraMap A B) f) i : MvPowerSeries ι B)) =
      fun i => X i ^ (p ^ (n : ℕ)) := by
    funext i
    rw [map_substEach, substEach_apply, map_residue_map_eq_X_pow hmemf hf,
      PowerSeries.subst_pow (PowerSeries.HasSubst.X i),
      PowerSeries.subst_X (PowerSeries.HasSubst.X i), hq]
  have hfrob : MvPowerSeries.map (residue B) (MvPowerSeries.map (σ : B →+* B) (dropConst φ)) =
      MvPowerSeries.map (iterateFrobenius (ResidueField B) p n) ψ := by
    ext d
    simp only [coeff_map, ψ]
    exact RingHom.congr_fun hcomp _
  have h3 : subst (fun i => (X i : MvPowerSeries ι (ResidueField B)) ^ (p ^ (n : ℕ)))
      (MvPowerSeries.map (iterateFrobenius (ResidueField B) p n) ψ) =
      MvPowerSeries.map (iterateFrobenius (ResidueField B) p n)
        (subst (fun i => (X i : MvPowerSeries ι (ResidueField B)) ^ (p ^ (n : ℕ))) ψ) := by
    rw [map_subst (HasSubst.X_pow hq0)]
    simp only [map_pow, map_X]
  have h4 := map_iterateFrobenius_expand p hp.ne_zero ψ n
  simp only [expand, coe_substAlgHom] at h4
  rw [twistedDefect, map_sub, map_subst hE, PowerSeries.map_subst hs,
    map_residue_map_eq_X_pow hmemg hg, PowerSeries.subst_pow hs', PowerSeries.subst_X hs', hmapE,
    hfrob, h3, h4, hq, sub_self, map_zero]

end Hypotheses

section Main

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Finite (ResidueField A)]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  [IsAlgClosed (ResidueField B)] [IsAdicComplete (maximalIdeal B) B]
  (hunr : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
  (σ : B →ₐ[A] B)
  (hσ : ∀ x : B, residue B (σ x) = residue B x ^ Nat.card (ResidueField A))
  {π : A} (hπ : Irreducible π) (u : Aˣ) {f g : PowerSeries A}
  (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries (u * π) g)

include hunr hσ hπ hf hg

omit [IsAlgClosed (ResidueField B)] in
theorem isTwistedLift_unique {ι : Type*} [Finite ι] {ℓ φ ψ : MvPowerSeries ι B}
    (hφ : IsTwistedLift (σ : B →+* B) (PowerSeries.map (algebraMap A B) g)
      (PowerSeries.map (algebraMap A B) f) ℓ φ)
    (hψ : IsTwistedLift (σ : B →+* B) (PowerSeries.map (algebraMap A B) g)
      (PowerSeries.map (algebraMap A B) f) ℓ ψ) : φ = ψ := by
  have hπB := irreducible_algebraMap hunr hπ
  refine hφ.unique (σ : B →+* B) (u := algebraMap A B u) (π := algebraMap A B π)
    (by rw [powerSeries_constantCoeff_map, hf.constantCoeff_eq_zero, map_zero])
    (by rw [PowerSeries.coeff_map, hf.coeff_one])
    (by rw [powerSeries_constantCoeff_map, hg.constantCoeff_eq_zero, map_zero])
    (by rw [PowerSeries.coeff_map, hg.coeff_one, map_mul])
    (fun x hx => (mul_eq_zero.1 hx).resolve_left hπB.ne_zero)
    (fun d hd => bijective_twistOp σ hπB (u.isUnit.map (algebraMap A B)) hd)
    (fun φ e => dvd_coeff_twistedDefect σ hunr hσ hπB hf hg φ e) hψ

omit [IsAlgClosed (ResidueField B)] in
theorem exists_isTwistedLift {ε : B} (hε : σ ε = algebraMap A B u * ε) :
    ∃ θ : PowerSeries B, IsTwistedLift (σ : B →+* B) (PowerSeries.map (algebraMap A B) g)
      (PowerSeries.map (algebraMap A B) f) (PowerSeries.C ε * PowerSeries.X) θ := by
  have hπB := irreducible_algebraMap hunr hπ
  have hℓ0 : constantCoeff (PowerSeries.C ε * PowerSeries.X : MvPowerSeries Unit B) = 0 := by
    change PowerSeries.constantCoeff (PowerSeries.C ε * PowerSeries.X) = 0
    simp
  obtain ⟨θ, ⟨h2, he⟩, -⟩ := existsUnique_twisted (σ : B →+* B) (ι := Unit)
    (u := algebraMap A B u) (π := algebraMap A B π)
    (by rw [powerSeries_constantCoeff_map, hf.constantCoeff_eq_zero, map_zero])
    (by rw [PowerSeries.coeff_map, hf.coeff_one])
    (by rw [powerSeries_constantCoeff_map, hg.constantCoeff_eq_zero, map_zero])
    (by rw [PowerSeries.coeff_map, hg.coeff_one, map_mul])
    (fun x hx => (mul_eq_zero.1 hx).resolve_left hπB.ne_zero)
    (fun d hd => bijective_twistOp σ hπB (u.isUnit.map (algebraMap A B)) hd)
    (fun φ e => dvd_coeff_twistedDefect σ hunr hσ hπB hf hg φ e) hℓ0 (fun e he => by
      have hd' : e = Finsupp.single () (e ()) := by ext; simp
      rw [hd', Finsupp.degree_single] at he
      rw [hd', he]
      change algebraMap A B u * algebraMap A B π * PowerSeries.coeff 1
          (PowerSeries.C ε * PowerSeries.X) =
        algebraMap A B π * σ (PowerSeries.coeff 1 (PowerSeries.C ε * PowerSeries.X))
      rw [coeff_one_C_mul_X, hε]
      ring)
  have h2' : (2 : ℕ∞) ≤ order ((PowerSeries.C ε * PowerSeries.X : MvPowerSeries Unit B) - θ) := by
    rw [← neg_sub, order_neg]
    exact h2
  exact ⟨θ, constantCoeff_eq_zero_of_two_le_order_sub h2' hℓ0, h2, he⟩

theorem exists_iso_lubinTateFormalGroup :
    ∃ θ : Iso ((lubinTateFormalGroup hπ hf).map (algebraMap A B))
        ((lubinTateFormalGroup ((irreducible_units_mul u).2 hπ) hg).map (algebraMap A B)),
      IsUnit (PowerSeries.coeff 1 θ.hom.toPowerSeries) ∧
      σ (PowerSeries.coeff 1 θ.hom.toPowerSeries) =
        algebraMap A B u * PowerSeries.coeff 1 θ.hom.toPowerSeries ∧
      PowerSeries.map (σ : B →+* B) θ.hom.toPowerSeries =
        PowerSeries.subst (PowerSeries.map (algebraMap A B) (lubinTateHom hπ hf hf u).toPowerSeries)
          θ.hom.toPowerSeries ∧
      (∀ a : A, θ.hom.comp ((lubinTateHom hπ hf hf a).map (algebraMap A B)) =
        ((lubinTateHom ((irreducible_units_mul u).2 hπ) hg hg a).map (algebraMap A B)).comp
          θ.hom) ∧
      PowerSeries.subst θ.hom.toPowerSeries (PowerSeries.map (algebraMap A B) g) =
        PowerSeries.subst (PowerSeries.map (algebraMap A B) f)
          (PowerSeries.map (σ : B →+* B) θ.hom.toPowerSeries) := by
  have hπ' : Irreducible (u * π) := (irreducible_units_mul u).2 hπ
  have hπB := irreducible_algebraMap hunr hπ
  have hσc : ∀ x, (σ : B →+* B) x = σ x := fun _ => rfl
  have hf0B : PowerSeries.constantCoeff (PowerSeries.map (algebraMap A B) f) = 0 := by
    rw [powerSeries_constantCoeff_map, hf.constantCoeff_eq_zero, map_zero]
  have hg0B : PowerSeries.constantCoeff (PowerSeries.map (algebraMap A B) g) = 0 := by
    rw [powerSeries_constantCoeff_map, hg.constantCoeff_eq_zero, map_zero]
  obtain ⟨η, hη⟩ := exists_units_eq_mul σ hσ hπB (Units.map (algebraMap A B : A →* B) u)
  set ε : B := (η : B)
  have hε : σ ε = algebraMap A B u * ε := by simpa using hη
  obtain ⟨θ, hθ⟩ := exists_isTwistedLift hunr σ hσ hπ u hf hg hε
  have hθ0 : PowerSeries.constantCoeff θ = 0 := hθ.1
  have hθ1 : PowerSeries.coeff 1 θ = ε := by
    have := eq_coeff_of_two_le_order_sub hθ.2.1 (e := Finsupp.single () 1) (by simp)
    change PowerSeries.coeff 1 θ = PowerSeries.coeff 1 (PowerSeries.C ε * PowerSeries.X) at this
    rw [this, coeff_one_C_mul_X]
  have hL : MvPowerSeries.map (algebraMap A B) (sum₂ (![1, 1] : Fin 2 → A)) =
      X 0 + X 1 := by
    rw [linearForm_fin_two]
    simp
  have hFf : IsLubinTateLift (PowerSeries.map (algebraMap A B) f)
      (PowerSeries.map (algebraMap A B) f) (X 0 + X 1)
      (MvPowerSeries.map (algebraMap A B) (lubinTateFormalGroup hπ hf).toPowerSeries) := by
    rw [← hL]
    exact (isLubinTateLift_lubinTateLift hπ hf hf _).map (algebraMap A B) hf.constantCoeff_eq_zero
  have hFg : IsLubinTateLift (PowerSeries.map (algebraMap A B) g)
      (PowerSeries.map (algebraMap A B) g) (X 0 + X 1)
      (MvPowerSeries.map (algebraMap A B) (lubinTateFormalGroup hπ' hg).toPowerSeries) := by
    rw [← hL]
    exact (isLubinTateLift_lubinTateLift hπ' hg hg _).map (algebraMap A B) hg.constantCoeff_eq_zero
  have hHom : ∀ {h h' : PowerSeries A} (hh : IsLubinTateSeries π h) (hh' : IsLubinTateSeries π h')
      (hπ₀ : Irreducible π) (a : A), IsLubinTateLift (PowerSeries.map (algebraMap A B) h)
        (PowerSeries.map (algebraMap A B) h') (PowerSeries.C (algebraMap A B a) * PowerSeries.X)
        (PowerSeries.map (algebraMap A B) (lubinTateHom hπ₀ hh hh' a).toPowerSeries) := by
    intro h h' hh hh' hπ₀ a
    rw [← map_C_mul_X]
    exact (isLubinTateLift_lubinTateHom hπ₀ hh hh' a).map (algebraMap A B) hh'.constantCoeff_eq_zero
  have hHom' : ∀ a : A, IsLubinTateLift (PowerSeries.map (algebraMap A B) g)
        (PowerSeries.map (algebraMap A B) g) (PowerSeries.C (algebraMap A B a) * PowerSeries.X)
        (PowerSeries.map (algebraMap A B) (lubinTateHom hπ' hg hg a).toPowerSeries) := by
    intro a
    rw [← map_C_mul_X]
    exact (isLubinTateLift_lubinTateHom hπ' hg hg a).map (algebraMap A B) hg.constantCoeff_eq_zero
  have uniq := fun {ι : Type} [Finite ι] {ℓ φ ψ : MvPowerSeries ι B} hφ hψ =>
    isTwistedLift_unique hunr σ hσ hπ u hf hg (ℓ := ℓ) (φ := φ) (ψ := ψ) hφ hψ
  have hX : ∀ j : Fin 2, IsTwistedLift (σ : B →+* B) (PowerSeries.map (algebraMap A B) g)
      (PowerSeries.map (algebraMap A B) f) (C ε * X j)
      (PowerSeries.subst (X j : MvPowerSeries (Fin 2) B) θ) := by
    intro j
    have := hθ.comp_lift (σ : B →+* B) hf0B hf0B (v := fun _ : Unit => (X j : MvPowerSeries (Fin 2) B))
      (u := fun _ => X j) (fun _ => isLubinTateLift_X hf0B j) (fun _ => map_X _ _)
    rwa [← PowerSeries.subst_def, ← PowerSeries.subst_def,
      powerSeries_subst_C_mul_X (PowerSeries.HasSubst.X j)] at this
  have hD := hθ.comp_lift (σ : B →+* B) hf0B hf0B
    (v := fun _ : Unit => (X 0 + X 1 : MvPowerSeries (Fin 2) B))
    (u := fun _ => MvPowerSeries.map (algebraMap A B) (lubinTateFormalGroup hπ hf).toPowerSeries)
    (fun _ => hFf) (fun _ => map_sigma_map_algebraMap σ _)
  rw [← PowerSeries.subst_def, ← PowerSeries.subst_def,
    powerSeries_subst_C_mul_X (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))] at hD
  have hE := IsLubinTateLift.comp_twisted (σ : B →+* B) hf0B hg0B hFg
    (map_sigma_map_algebraMap σ _)
    (w := ![C ε * X 0, C ε * X 1])
    (v := ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) B) θ,
      PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) B) θ])
    (fun j => by fin_cases j <;> simpa using hX _)
  have hs2 : HasSubst (![C ε * X 0, C ε * X 1] : Fin 2 → MvPowerSeries (Fin 2) B) :=
    hasSubst_pair (by simp) (by simp)
  rw [subst_add hs2, subst_X hs2, subst_X hs2] at hE
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    at hE
  rw [← mul_add] at hE
  have hDE := uniq hD hE
  let θh : Hom ((lubinTateFormalGroup hπ hf).map (algebraMap A B))
      ((lubinTateFormalGroup hπ' hg).map (algebraMap A B)) :=
    { toPowerSeries := θ
      constantCoeff_eq_zero := hθ0
      map_add := by
        rw [FormalGroup.map_toPowerSeries, FormalGroup.map_toPowerSeries, hDE] }
  let θi := Iso.ofIsUnit θh (by
    change IsUnit (PowerSeries.coeff 1 θ)
    rw [hθ1]
    exact η.isUnit)
  refine ⟨θi, ?_, ?_, ?_, ?_, ?_⟩
  · change IsUnit (PowerSeries.coeff 1 θ)
    rw [hθ1]
    exact η.isUnit
  · change σ (PowerSeries.coeff 1 θ) = _ * PowerSeries.coeff 1 θ
    rw [hθ1, hε]
  · change PowerSeries.map (σ : B →+* B) θ = PowerSeries.subst _ θ
    have h1 := hθ.map (σ : B →+* B) hf0B (powerSeries_map_sigma_map_algebraMap σ f)
      (powerSeries_map_sigma_map_algebraMap σ g)
    have h2 := hθ.comp_lift (σ : B →+* B) hf0B hf0B
      (v := fun _ : Unit => PowerSeries.C (algebraMap A B u) * PowerSeries.X)
      (u := fun _ => PowerSeries.map (algebraMap A B) (lubinTateHom hπ hf hf u).toPowerSeries)
      (fun _ => hHom hf hf hπ u) (fun _ => map_sigma_map_algebraMap σ _)
    rw [← PowerSeries.subst_def, ← PowerSeries.subst_def,
      powerSeries_subst_C_mul_X (PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_C_mul_X _))] at h2
    rw [map_C_mul_X, hσc, hε] at h1
    rw [C_unit_eq, ← mul_assoc, ← map_mul, mul_comm ε] at h2
    exact uniq h1 h2
  · intro a
    apply Hom.ext
    rw [Hom.toPowerSeries_comp, Hom.toPowerSeries_comp, Hom.map_toPowerSeries,
      Hom.map_toPowerSeries]
    change PowerSeries.subst _ θ = PowerSeries.subst θ _
    have h1 := hθ.comp_lift (σ : B →+* B) hf0B hf0B
      (v := fun _ : Unit => PowerSeries.C (algebraMap A B a) * PowerSeries.X)
      (u := fun _ => PowerSeries.map (algebraMap A B) (lubinTateHom hπ hf hf a).toPowerSeries)
      (fun _ => hHom hf hf hπ a) (fun _ => map_sigma_map_algebraMap σ _)
    have h2 := IsLubinTateLift.comp_twisted (σ : B →+* B) hf0B hg0B (hHom' a)
      (map_sigma_map_algebraMap σ _)
      (w := fun _ : Unit => PowerSeries.C ε * PowerSeries.X) (v := fun _ => θ) (fun _ => hθ)
    rw [← PowerSeries.subst_def, ← PowerSeries.subst_def,
      powerSeries_subst_C_mul_X (PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_C_mul_X _))] at h1
    rw [← PowerSeries.subst_def, ← PowerSeries.subst_def,
      powerSeries_subst_C_mul_X (PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_C_mul_X _))] at h2
    rw [C_unit_eq] at h1 h2
    have e : PowerSeries.C ε * (PowerSeries.C (algebraMap A B a) * PowerSeries.X) =
        PowerSeries.C (algebraMap A B a) * (PowerSeries.C ε * PowerSeries.X) := by ring
    rw [e] at h1
    exact uniq h1 h2
  · change PowerSeries.subst θ _ = PowerSeries.subst _ (PowerSeries.map (σ : B →+* B) θ)
    rw [hθ.2.2, subst_substEach_unit]
    rfl

end Main

end OverUnramified

/-! ## Section 9: Adic Convergence & Evaluation on the Maximal Ideal -/

section AdicConvergence

variable {R : Type*} [CommRing R]

noncomputable def partialSum (f : PowerSeries R) (x : R) (n : ℕ) : R :=
  ∑ k ∈ Finset.range n, PowerSeries.coeff k f * x ^ k

theorem partialSum_zero (f : PowerSeries R) (x : R) : partialSum f x 0 = 0 := by
  simp [partialSum]

theorem partialSum_succ (f : PowerSeries R) (x : R) (n : ℕ) :
    partialSum f x (n + 1) = partialSum f x n + PowerSeries.coeff n f * x ^ n := by
  simp [partialSum, Finset.sum_range_succ]

theorem partialSum_succ_sub_mem (I : Ideal R) (f : PowerSeries R) {x : R} (hx : x ∈ I) (n : ℕ) :
    partialSum f x (n + 1) - partialSum f x n ∈ I ^ n := by
  rw [partialSum_succ, add_sub_cancel_left]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hx n)

theorem existsUnique_evalAdic (I : Ideal R) [IsAdicComplete I R] (f : PowerSeries R)
    {x : R} (hx : x ∈ I) :
    ∃! L : R, ∀ n : ℕ, L - partialSum f x n ∈ I ^ n := by
  obtain ⟨L, hL⟩ := exists_limit_of_approx I (fun n y => y = partialSum f x n)
    (fun n y hy => ⟨partialSum f x (n + 1), hy ▸ partialSum_succ_sub_mem I f hx n, rfl⟩)
    (x₀ := partialSum f x 0) rfl
  refine ⟨L, fun n => ?_, fun L' hL' => ?_⟩
  · obtain ⟨y, rfl, hLy⟩ := hL n
    exact hLy
  · rw [← sub_eq_zero]
    refine IsHausdorff.haus (I := I) inferInstance _ fun n => ?_
    rw [smodEq_pow_iff_sub_mem, sub_zero]
    obtain ⟨y, rfl, hLy⟩ := hL n
    have e : L' - L = (L' - partialSum f x n) - (L - partialSum f x n) := by ring
    rw [e]
    exact Ideal.sub_mem _ (hL' n) hLy

noncomputable def evalAdic (I : Ideal R) [IsAdicComplete I R] (f : PowerSeries R)
    {x : R} (hx : x ∈ I) : R :=
  (existsUnique_evalAdic I f hx).exists.choose

theorem evalAdic_sub_partialSum_mem (I : Ideal R) [IsAdicComplete I R] (f : PowerSeries R)
    {x : R} (hx : x ∈ I) (n : ℕ) :
    evalAdic I f hx - partialSum f x n ∈ I ^ n :=
  (existsUnique_evalAdic I f hx).exists.choose_spec n

theorem eq_evalAdic (I : Ideal R) [IsAdicComplete I R] (f : PowerSeries R)
    {x : R} (hx : x ∈ I) {L : R} (hL : ∀ n : ℕ, L - partialSum f x n ∈ I ^ n) :
    L = evalAdic I f hx :=
  (existsUnique_evalAdic I f hx).unique hL (evalAdic_sub_partialSum_mem I f hx)

theorem evalAdic_mem_of_constantCoeff_eq_zero (I : Ideal R) [IsAdicComplete I R]
    {f : PowerSeries R} (hf : PowerSeries.constantCoeff f = 0) {x : R} (hx : x ∈ I) :
    evalAdic I f hx ∈ I := by
  have h1 := evalAdic_sub_partialSum_mem I f hx 1
  simp only [partialSum, Finset.range_one, Finset.sum_singleton, pow_zero, mul_one,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hf, sub_zero, pow_one] at h1
  exact h1

theorem evalAdic_zero (I : Ideal R) [IsAdicComplete I R] {x : R} (hx : x ∈ I) :
    evalAdic I 0 hx = 0 :=
  (eq_evalAdic I 0 hx fun n => by simp [partialSum]).symm

theorem evalAdic_C (I : Ideal R) [IsAdicComplete I R] (c : R) {x : R} (hx : x ∈ I) :
    evalAdic I (PowerSeries.C c) hx = c := by
  symm
  refine eq_evalAdic I (PowerSeries.C c) hx fun n => ?_
  cases n with
  | zero => simp [partialSum]
  | succ n =>
    have hp : partialSum (PowerSeries.C c) x (n + 1) = c := by
      rw [partialSum, Finset.sum_eq_single 0]
      · simp
      · intro k _ hk
        simp [PowerSeries.coeff_C, hk]
      · simp
    rw [hp, sub_self]
    exact Ideal.zero_mem _

theorem evalAdic_X (I : Ideal R) [IsAdicComplete I R] {x : R} (hx : x ∈ I) :
    evalAdic I PowerSeries.X hx = x := by
  symm
  refine eq_evalAdic I PowerSeries.X hx fun n => ?_
  rcases n with _ | _ | n
  · simp [partialSum]
  · simp [partialSum, hx]
  · have hp : partialSum PowerSeries.X x (n + 2) = x := by
      rw [partialSum, Finset.sum_eq_single 1]
      · simp
      · intro k _ hk
        simp [PowerSeries.coeff_X, hk]
      · intro h
        exact absurd (Finset.mem_range.mpr (by omega)) h
    rw [hp, sub_self]
    exact Ideal.zero_mem _

theorem evalAdic_add (I : Ideal R) [IsAdicComplete I R] (f g : PowerSeries R)
    {x : R} (hx : x ∈ I) :
    evalAdic I (f + g) hx = evalAdic I f hx + evalAdic I g hx := by
  symm
  refine eq_evalAdic I (f + g) hx fun n => ?_
  have hp : partialSum (f + g) x n = partialSum f x n + partialSum g x n := by
    simp [partialSum, add_mul, Finset.sum_add_distrib]
  rw [hp]
  have e : evalAdic I f hx + evalAdic I g hx - (partialSum f x n + partialSum g x n) =
      (evalAdic I f hx - partialSum f x n) + (evalAdic I g hx - partialSum g x n) := by ring
  rw [e]
  exact Ideal.add_mem _ (evalAdic_sub_partialSum_mem I f hx n)
    (evalAdic_sub_partialSum_mem I g hx n)

noncomputable def homogSum₂ (F : MvPowerSeries (Fin 2) R) (x y : R) (k : ℕ) : R :=
  ∑ p ∈ Finset.antidiagonal k,
    MvPowerSeries.coeff (Finsupp.single 0 p.1 + Finsupp.single 1 p.2) F * x ^ p.1 * y ^ p.2

noncomputable def partialSum₂ (F : MvPowerSeries (Fin 2) R) (x y : R) (n : ℕ) : R :=
  ∑ k ∈ Finset.range n, homogSum₂ F x y k

theorem homogSum₂_mem (I : Ideal R) (F : MvPowerSeries (Fin 2) R) {x y : R}
    (hx : x ∈ I) (hy : y ∈ I) (k : ℕ) :
    homogSum₂ F x y k ∈ I ^ k := by
  refine Ideal.sum_mem _ fun p hp => ?_
  have hadd : p.1 + p.2 = k := Finset.mem_antidiagonal.mp hp
  rw [mul_assoc]
  refine Ideal.mul_mem_left _ _ ?_
  rw [← hadd, pow_add]
  exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hx p.1) (Ideal.pow_mem_pow hy p.2)

theorem partialSum₂_succ_sub_mem (I : Ideal R) (F : MvPowerSeries (Fin 2) R) {x y : R}
    (hx : x ∈ I) (hy : y ∈ I) (n : ℕ) :
    partialSum₂ F x y (n + 1) - partialSum₂ F x y n ∈ I ^ n := by
  rw [partialSum₂, partialSum₂, Finset.sum_range_succ, add_sub_cancel_left]
  exact homogSum₂_mem I F hx hy n

theorem existsUnique_evalAdic₂ (I : Ideal R) [IsAdicComplete I R] (F : MvPowerSeries (Fin 2) R)
    {x y : R} (hx : x ∈ I) (hy : y ∈ I) :
    ∃! L : R, ∀ n : ℕ, L - partialSum₂ F x y n ∈ I ^ n := by
  obtain ⟨L, hL⟩ := exists_limit_of_approx I (fun n z => z = partialSum₂ F x y n)
    (fun n z hz => ⟨partialSum₂ F x y (n + 1), hz ▸ partialSum₂_succ_sub_mem I F hx hy n, rfl⟩)
    (x₀ := partialSum₂ F x y 0) rfl
  refine ⟨L, fun n => ?_, fun L' hL' => ?_⟩
  · obtain ⟨z, rfl, hLz⟩ := hL n
    exact hLz
  · rw [← sub_eq_zero]
    refine IsHausdorff.haus (I := I) inferInstance _ fun n => ?_
    rw [smodEq_pow_iff_sub_mem, sub_zero]
    obtain ⟨z, rfl, hLz⟩ := hL n
    have e : L' - L = (L' - partialSum₂ F x y n) - (L - partialSum₂ F x y n) := by ring
    rw [e]
    exact Ideal.sub_mem _ (hL' n) hLz

noncomputable def evalAdic₂ (I : Ideal R) [IsAdicComplete I R] (F : MvPowerSeries (Fin 2) R)
    {x y : R} (hx : x ∈ I) (hy : y ∈ I) : R :=
  (existsUnique_evalAdic₂ I F hx hy).exists.choose

theorem evalAdic₂_sub_partialSum₂_mem (I : Ideal R) [IsAdicComplete I R]
    (F : MvPowerSeries (Fin 2) R) {x y : R} (hx : x ∈ I) (hy : y ∈ I) (n : ℕ) :
    evalAdic₂ I F hx hy - partialSum₂ F x y n ∈ I ^ n :=
  (existsUnique_evalAdic₂ I F hx hy).exists.choose_spec n

theorem eq_evalAdic₂ (I : Ideal R) [IsAdicComplete I R] (F : MvPowerSeries (Fin 2) R)
    {x y : R} (hx : x ∈ I) (hy : y ∈ I) {L : R}
    (hL : ∀ n : ℕ, L - partialSum₂ F x y n ∈ I ^ n) :
    L = evalAdic₂ I F hx hy :=
  (existsUnique_evalAdic₂ I F hx hy).unique hL (evalAdic₂_sub_partialSum₂_mem I F hx hy)

noncomputable def evalFormalGroup (I : Ideal R) [IsAdicComplete I R] (F : FormalGroup R)
    {x y : R} (hx : x ∈ I) (hy : y ∈ I) : R :=
  evalAdic₂ I F.toPowerSeries hx hy

theorem evalFormalGroup_mem (I : Ideal R) [IsAdicComplete I R] (F : FormalGroup R)
    {x y : R} (hx : x ∈ I) (hy : y ∈ I) :
    evalFormalGroup I F hx hy ∈ I := by
  have h1 := evalAdic₂_sub_partialSum₂_mem I F.toPowerSeries hx hy 1
  have hp1 : partialSum₂ F.toPowerSeries x y 1 = 0 := by
    simp [partialSum₂, homogSum₂, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      F.zero_constantCoeff]
  rw [hp1, sub_zero, pow_one] at h1
  exact h1

theorem evalFormalGroup_sub_add_mem (I : Ideal R) [IsAdicComplete I R] (F : FormalGroup R)
    {x y : R} (hx : x ∈ I) (hy : y ∈ I) :
    evalFormalGroup I F hx hy - (x + y) ∈ I ^ 2 := by
  have h2 := evalAdic₂_sub_partialSum₂_mem I F.toPowerSeries hx hy 2
  have hp2 : partialSum₂ F.toPowerSeries x y 2 = x + y := by
    have h0 : homogSum₂ F.toPowerSeries x y 0 = 0 := by
      simp [homogSum₂, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, F.zero_constantCoeff]
    have h1 : homogSum₂ F.toPowerSeries x y 1 = y + x := by
      simp [homogSum₂, Finset.Nat.antidiagonal_succ, F.lin_coeff_X, F.lin_coeff_Y]
    rw [partialSum₂, Finset.sum_range_succ, Finset.sum_range_one, h0, h1, zero_add, add_comm]
  rw [hp2] at h2
  exact h2

section MaximalIdeal

variable [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

noncomputable def evalMaximalIdeal (f : PowerSeries R) {x : R}
    (hx : x ∈ IsLocalRing.maximalIdeal R) : R :=
  evalAdic (IsLocalRing.maximalIdeal R) f hx

theorem evalMaximalIdeal_mem {f : PowerSeries R} (hf : PowerSeries.constantCoeff f = 0)
    {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R) :
    evalMaximalIdeal f hx ∈ IsLocalRing.maximalIdeal R :=
  evalAdic_mem_of_constantCoeff_eq_zero (IsLocalRing.maximalIdeal R) hf hx

noncomputable def evalFormalGroupMaximalIdeal (F : FormalGroup R) {x y : R}
    (hx : x ∈ IsLocalRing.maximalIdeal R) (hy : y ∈ IsLocalRing.maximalIdeal R) : R :=
  evalFormalGroup (IsLocalRing.maximalIdeal R) F hx hy

theorem evalFormalGroupMaximalIdeal_mem (F : FormalGroup R) {x y : R}
    (hx : x ∈ IsLocalRing.maximalIdeal R) (hy : y ∈ IsLocalRing.maximalIdeal R) :
    evalFormalGroupMaximalIdeal F hx hy ∈ IsLocalRing.maximalIdeal R :=
  evalFormalGroup_mem (IsLocalRing.maximalIdeal R) F hx hy

theorem evalFormalGroupMaximalIdeal_sub_add_mem (F : FormalGroup R) {x y : R}
    (hx : x ∈ IsLocalRing.maximalIdeal R) (hy : y ∈ IsLocalRing.maximalIdeal R) :
    evalFormalGroupMaximalIdeal F hx hy - (x + y) ∈ IsLocalRing.maximalIdeal R ^ 2 :=
  evalFormalGroup_sub_add_mem (IsLocalRing.maximalIdeal R) F hx hy

end MaximalIdeal

end AdicConvergence

end RHDirect.CFT.FormalGroups

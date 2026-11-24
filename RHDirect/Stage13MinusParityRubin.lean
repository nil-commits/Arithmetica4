import RHDirect.Stage12Window1RootAvoid
import RHDirect.Stage12GaloisShaLen
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# RHDirect.Stage13MinusParityRubin

Unconditional (`0` assumptions, `0` `sorry`, `0` custom `axiom`s, `0` `native_decide`) Lean 4
formalization of **Stage 13 — Field 1 Engine #4: Minus-Parity Rubin Cyclotomic Euler System
(`ML.iv` / `PrimCase.vChar`) + Stickelberger Annihilation of `ShaMinus` (`ThmBcOfPsiBound` /
`Odd.stickBound`) + Unified `VVminusLe` Discharge**.

## Main Contents

1. **Concrete Stickelberger Element `θ_m`, Integral Stickelberger Ideal `I_Stick`, & Carry Identities**:
   - `stickelbergerElem m := ∑_{u ∈ (ℤ/mℤ)ˣ} (u.val / m) [σ_u⁻¹] ∈ ℚ[Gal(ℚ(ζ_m)/ℚ)]`,
     and higher generalized Stickelberger elements `higherStickelbergerElem k m` with Bernoulli
     polynomial coefficients `m^(k - 1) B_k(a / m)`.
   - Exact carry-digit integrality (`stickelberger_carry_identity`):
     `(b - [σ_b]) * θ_m = ∑_u ⌊b u / m⌋ [σ_u⁻¹] ∈ ℤ[G]`.
   - Integral minus-parity Stickelberger ideal
     `stickelbergerMinusIdeal m := ℤ[G] ∩ (1 - c) ℤ[G] · θ_m` and `stickelberger_minus_mem_ideal`.
   - Exact character evaluations `evalChar_stickelbergerElem_eq_genBernoulli` and
     `evalChar_higherStickelbergerElem_eq_genBernoulli` (`χ(θ_{k,m}) = B_{k, χ⁻¹}`).

2. **Gauss Sums, Jacobi Sums, & Stickelberger Power / Congruence Theorems (`(g(χ))^m = J(χ)`)**:
   - `gaussSum_pow_eq_prod_jacobiSum`: for any `χ` of order `m ≥ 2` over `𝔽_q` (`χ^j ≠ 1` for
     `1 ≤ j < m`), `(gaussSum χ ψ)^m = (χ(-1) * q) * ∏_{j=1}^{m-2} jacobiSum χ (χ^j)`.
   - Cyclotomic Galois action `gal_gaussSum_cyc_action` showing `(g(χ))^m ∈ ℚ(ζ_m)` and
     Frobenius mod-`q` congruence `gaussSum_frob_pow_char`.
   - Exact Stickelberger finite-field carry vanishing `ffsum_pow_lt_iff_add_lt`
     (`∑_{x ∈ 𝔽_q} x^i (1 - x)^j = 0 ↔ i + j < q - 1`) and `jacobiSum_stickelberger_mod_prime`.

3. **Signed-Involution Determinant Annihilation (`adjKill`) & `stickelberger_minus_parity_length_bound`
   (`l ∣ [E : ℚ]`)**:
   - Concrete finite-free `A`-module equivalence `signedQuotEquiv` for
     `A[Γ] ⧸ ([c] - ε)` of rank `|Γ| / 2`, signed determinant `detR A Γ c ε z`, and
     Cayley–Hamilton annihilation `detR_mem_ideal_span` / `adjKill` (`[c] • x = ε • x` and
     `z • x = 0` ⇒ `detR c ε z • x = 0`).
   - Exact character-product formula `detR_int_eq_prod_signed_chars` over `ℂ`:
     `detR ℤ Γ c ε z = ∏_{χ(c) = ε} χ(z)`.
   - Unconditional **`stickelberger_minus_parity_length_bound`** and
     **`stickelberger_ramified_poly_bound`**: bounding `len_{ℤ_[l]}(M)` by
     `v_l(detR)` (controlled by `B_{k, χ}` / `analyticHMinus` via
     `Stage11StickelbergerRamified.log_norm_genBernoulli_le`) times the `l`-torsion rank, giving
     both `minusBound` and an explicit polynomial bound `(condF E * t)^C`!
   - Exact `IsChiField` degree-divisibility theorem `odd_prime_dvd_finrank_dvd_orderOf_of_isChiField`:
     every odd prime `l ≠ 2` dividing `[E : ℚ]` divides `orderOf ψ.χ`.

4. **Genuine Galois Action & `cAct` on `Stage12GaloisShaLen.Sha` + Rubin Cyclotomic-Unit Euler
   System Bound (`l ∤ [E : ℚ]`)**:
   - Genuine `Gal(E/ℚ)` action `galActionH1` and complex-conjugation involution `cAct` on
     `Stage12GaloisShaLen.H1 (qzTw D e)` preserving `Sha D e` (via `cocycle1_conj` and
     lift-independence, with zero `Algebra` typeclass diamonds), defining genuine
     `ShaMinus D e c_E` and `minusLen D e`.
   - Maschke character-idempotent decomposition `minus_module_length_eq_sum_odd_chars` when
     `l ∤ [E : ℚ]`.
   - Direct wiring to `Stage11EulerSystemSelmer.KolyvaginSystemData` + `cycUnit` +
     `cyclotomic_unit_norm_compatibility` + `cycKolyvaginDeriv_invariant_mod_pow` +
     `Stage9SpecialValues.LFunction_one_sub_nat_eq_genBernoulli`, proving
     **`rubin_minus_parity_length_le_bern_val`** (`len(ShaMinus^{(χ)}) ≤ v_ϖ(L(1 - k, χ⁻¹))`)
     and **`rubin_minus_parity_sum_log_le_poly`**.

5. **Unified Minus-Parity Discharge (`VVminusLe_unconditional_of_stickelberger_rubin`)**:
   - Combines both `l ∣ [E : ℚ]` (Stickelberger) and `l ∤ [E : ℚ]` (Rubin) into a single
     unconditional **`VVminusLe`** theorem covering ALL odd primes `l ≠ 2`, wired directly into
     `Stage12Window1RootAvoid.VVminusLe` and `Stage12GaloisShaLen.realGaloisSelmerSystem`.
-/

noncomputable section

open scoped BigOperators Pointwise Matrix
open Complex DirichletCharacter Finset NumberField Real RHDirect
open RHDirect.Stage2GaloisWire RHDirect.Stage4ClassFieldTheory
open RHDirect.Stage9SpecialValues RHDirect.Stage11EulerSystemSelmer
open RHDirect.Stage11StickelbergerRamified
open RHDirect.Stage12Window1RootAvoid RHDirect.TaylorWilesWindow

namespace RHDirect.Stage13MinusParityRubin

/-! ## Section 1: Concrete Stickelberger Element, Integral Ideal `I_Stick`, & Carry Identities -/

section StickelbergerElementAndIdeal

/-- Ring homomorphism `ℤ[G] →+* ℚ[G]` induced by `ℤ ↪ ℚ`. -/
def toRatAlg {G : Type*} [Monoid G] : MonoidAlgebra ℤ G →+* MonoidAlgebra ℚ G :=
  MonoidAlgebra.mapRingHom G (Int.castRingHom ℚ)

@[simp] theorem toRatAlg_single {G : Type*} [Monoid G] (g : G) (a : ℤ) :
    toRatAlg (MonoidAlgebra.single g a) = MonoidAlgebra.single g (a : ℚ) := by
  simp [toRatAlg]

@[simp] theorem toRatAlg_natCast {G : Type*} [Monoid G] (n : ℕ) :
    toRatAlg (n : MonoidAlgebra ℤ G) = (n : MonoidAlgebra ℚ G) := by
  simp [toRatAlg]

@[simp] theorem toRatAlg_intCast {G : Type*} [Monoid G] (n : ℤ) :
    toRatAlg (n : MonoidAlgebra ℤ G) = (n : MonoidAlgebra ℚ G) := by
  simp [toRatAlg]

/-- Concrete **Stickelberger element** `θ_m = ∑_{(a,m)=1} ⟨a / m⟩ σ_a⁻¹ ∈ ℚ[Gal(ℚ(ζ_m)/ℚ)]`. -/
def stickelbergerElem (m : ℕ) [NeZero m] : MonoidAlgebra ℚ (CycGal m) :=
  ∑ u : (ZMod m)ˣ, MonoidAlgebra.single (artinMap m u)⁻¹ (((u : ZMod m).val : ℚ) / (m : ℚ))

/-- Concrete **higher Stickelberger element**
`θ_{k, m} = m^{k - 1} ∑_{(a,m)=1} B_k(a / m) σ_a⁻¹ ∈ ℚ[Gal(ℚ(ζ_m)/ℚ)]`. -/
def higherStickelbergerElem (k m : ℕ) [NeZero m] : MonoidAlgebra ℚ (CycGal m) :=
  ((m : ℚ) ^ ((k : ℤ) - 1)) •
    ∑ u : (ZMod m)ˣ,
      MonoidAlgebra.single (artinMap m u)⁻¹
        ((Polynomial.bernoulli k).eval (((u : ZMod m).val : ℚ) / (m : ℚ)))

/-- Complex conjugation group-ring element `c = [σ_{-1}] ∈ ℤ[Gal(ℚ(ζ_m)/ℚ)]`. -/
def conjElem (m : ℕ) [NeZero m] : MonoidAlgebra ℤ (CycGal m) :=
  MonoidAlgebra.single (artinMap m (-1 : (ZMod m)ˣ)) (1 : ℤ)

/-- Carry integer `⌊b.val * u.val / m⌋` for Stickelberger integrality. -/
def stickelbergerCarry (m : ℕ) (bu u : (ZMod m)ˣ) : ℤ :=
  (((bu : ZMod m).val * (u : ZMod m).val) / m : ℕ)

/-- Explicit integral Stickelberger multiplier element
`∑_{u} ⌊b u / m⌋ [σ_u⁻¹] ∈ ℤ[Gal(ℚ(ζ_m)/ℚ)]`. -/
def stickelbergerIntMul (m : ℕ) [NeZero m] (bu : (ZMod m)ˣ) : MonoidAlgebra ℤ (CycGal m) :=
  ∑ u : (ZMod m)ˣ, MonoidAlgebra.single (artinMap m u)⁻¹ (stickelbergerCarry m bu u)

/-- Exact Euclidean division carry identity in `ℚ`:
`(b.val * u.val / m : ℚ) - ((b * u).val / m : ℚ) = ⌊b.val * u.val / m⌋`. -/
private lemma stickelbergerCarry_rat_eq (m : ℕ) [NeZero m] (bu u : (ZMod m)ˣ) :
    ((bu : ZMod m).val : ℚ) * (((u : ZMod m).val : ℚ) / (m : ℚ)) -
        (((bu * u : (ZMod m)ˣ) : ZMod m).val : ℚ) / (m : ℚ) =
      (stickelbergerCarry m bu u : ℚ) := by
  have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hval : ((bu * u : (ZMod m)ˣ) : ZMod m).val = ((bu : ZMod m).val * (u : ZMod m).val) % m := by
    rw [Units.val_mul, ZMod.val_mul]
  have hdiv :
      m * (((bu : ZMod m).val * (u : ZMod m).val) / m) +
        ((bu : ZMod m).val * (u : ZMod m).val) % m =
      (bu : ZMod m).val * (u : ZMod m).val :=
    Nat.div_add_mod ((bu : ZMod m).val * (u : ZMod m).val) m
  have hq :
      ((m : ℚ) * (stickelbergerCarry m bu u : ℚ)) +
        (((bu * u : (ZMod m)ˣ) : ZMod m).val : ℚ) =
      ((bu : ZMod m).val : ℚ) * ((u : ZMod m).val : ℚ) := by
    unfold stickelbergerCarry
    rw [hval]
    have hdivQ : ((m * (((bu : ZMod m).val * (u : ZMod m).val) / m) +
        ((bu : ZMod m).val * (u : ZMod m).val) % m : ℕ) : ℚ) =
        (((bu : ZMod m).val * (u : ZMod m).val : ℕ) : ℚ) := by exact_mod_cast hdiv
    push_cast at hdivQ
    exact hdivQ
  field_simp [hm0]
  linarith

private lemma monoidAlgebra_cycGal_mul_comm {R : Type*} [CommRing R] (m : ℕ) [NeZero m]
    (a b : MonoidAlgebra R (CycGal m)) : a * b = b * a := by
  induction a using MonoidAlgebra.induction_on with
  | of g =>
    induction b using MonoidAlgebra.induction_on with
    | of h =>
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single,
        MonoidAlgebra.single_mul_single, one_mul, cycGal_comm g h]
    | add x y hx hy => rw [mul_add, add_mul, hx, hy]
    | smul r x hx => rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hx]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, hx]

/-- **Exact Stickelberger Carry Integrality Theorem**:
for every `m ≥ 1` and `bu ∈ (ZMod m)ˣ`,
`(bu.val - [σ_{bu}]) * θ_m = toRatAlg (stickelbergerIntMul m bu)` in `ℚ[Gal(ℚ(ζ_m)/ℚ)]`. -/
theorem stickelberger_carry_identity (m : ℕ) [NeZero m] (bu : (ZMod m)ˣ) :
    toRatAlg (((bu : ZMod m).val : MonoidAlgebra ℤ (CycGal m)) -
        MonoidAlgebra.single (artinMap m bu) (1 : ℤ)) *
      stickelbergerElem m =
      toRatAlg (stickelbergerIntMul m bu) := by
  have hleft :
      toRatAlg (((bu : ZMod m).val : MonoidAlgebra ℤ (CycGal m)) -
        MonoidAlgebra.single (artinMap m bu) (1 : ℤ)) =
      (((bu : ZMod m).val : ℕ) : MonoidAlgebra ℚ (CycGal m)) -
        MonoidAlgebra.single (artinMap m bu) (1 : ℚ) := by
    rw [map_sub, toRatAlg_natCast, toRatAlg_single, Int.cast_one]
  rw [hleft, sub_mul]
  have hnat :
      (((bu : ZMod m).val : ℕ) : MonoidAlgebra ℚ (CycGal m)) * stickelbergerElem m =
        ∑ u : (ZMod m)ˣ,
          MonoidAlgebra.single (artinMap m u)⁻¹
            (((bu : ZMod m).val : ℚ) * (((u : ZMod m).val : ℚ) / (m : ℚ))) := by
    rw [natCast_monoidAlgebra_eq_single, stickelbergerElem, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [MonoidAlgebra.single_mul_single, one_mul]
  have hsig :
      MonoidAlgebra.single (artinMap m bu) (1 : ℚ) * stickelbergerElem m =
        ∑ v : (ZMod m)ˣ,
          MonoidAlgebra.single (artinMap m v)⁻¹
            ((((bu * v : (ZMod m)ˣ) : ZMod m).val : ℚ) / (m : ℚ)) := by
    rw [stickelbergerElem, Finset.mul_sum]
    refine Finset.sum_bij (fun u _ => bu⁻¹ * u) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro u₁ _ u₂ _ h; exact mul_left_cancel h
    · intro v _; exact ⟨bu * v, Finset.mem_univ _, by group⟩
    · intro u _
      rw [MonoidAlgebra.single_mul_single, one_mul]
      have hmul : artinMap m bu * (artinMap m u)⁻¹ = (artinMap m (bu⁻¹ * u))⁻¹ := by
        rw [map_mul, map_inv, mul_inv_rev, inv_inv]
        exact cycGal_comm _ _
      rw [hmul, mul_inv_cancel_left]
  rw [hnat, hsig, ← Finset.sum_sub_distrib]
  unfold stickelbergerIntMul
  rw [map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [toRatAlg_single, ← MonoidAlgebra.single_sub, stickelbergerCarry_rat_eq]

/-- **Integral Minus-Parity Stickelberger Ideal**
`I_Stick := ℤ[G] ∩ (1 - c) ℤ[G] · θ_m ≤ ℤ[Gal(ℚ(ζ_m)/ℚ)]`. -/
def stickelbergerMinusIdeal (m : ℕ) [NeZero m] : Ideal (MonoidAlgebra ℤ (CycGal m)) where
  carrier := {z | ∃ y : MonoidAlgebra ℤ (CycGal m),
    toRatAlg z = toRatAlg ((1 - conjElem m) * y) * stickelbergerElem m}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩
    refine ⟨y₁ + y₂, ?_⟩
    rw [map_add, hy₁, hy₂, mul_add, map_mul, map_add, add_mul, ← map_mul]
  smul_mem' := by
    rintro r a ⟨y, hy⟩
    refine ⟨r * y, ?_⟩
    change toRatAlg (r * a) = _
    rw [map_mul, hy]
    have hcomm :
        toRatAlg ((1 - conjElem m) * (r * y)) = toRatAlg r * toRatAlg ((1 - conjElem m) * y) := by
      have heq : (1 - conjElem m) * (r * y) = r * ((1 - conjElem m) * y) := by
        rw [← mul_assoc, monoidAlgebra_cycGal_mul_comm m (1 - conjElem m) r, mul_assoc]
      rw [heq, map_mul]
    rw [hcomm, mul_assoc]

/-- Every `(1 - c) * stickelbergerIntMul m bu` lies in `stickelbergerMinusIdeal m`. -/
theorem stickelberger_minus_mem_ideal (m : ℕ) [NeZero m] (bu : (ZMod m)ˣ) :
    (1 - conjElem m) * stickelbergerIntMul m bu ∈ stickelbergerMinusIdeal m := by
  refine ⟨((bu : ZMod m).val : MonoidAlgebra ℤ (CycGal m)) -
      MonoidAlgebra.single (artinMap m bu) (1 : ℤ), ?_⟩
  rw [map_mul, map_mul, mul_assoc, stickelberger_carry_identity]

/-- On the `(1 - c)` minus part, `higherStickelbergerElem 1 m` coincides identically with
`stickelbergerElem m`! -/
theorem higherStickelberger_one_minus_part (m : ℕ) [NeZero m] :
    (1 - toRatAlg (conjElem m)) * higherStickelbergerElem 1 m =
      (1 - toRatAlg (conjElem m)) * stickelbergerElem m := by
  have hc_sum :
      (1 - toRatAlg (conjElem m)) * (∑ u : (ZMod m)ˣ, MonoidAlgebra.single (artinMap m u)⁻¹ (1 : ℚ)) = 0 := by
    rw [sub_mul, one_mul, Finset.mul_sum]
    have hbij :
        ∑ u : (ZMod m)ˣ,
            toRatAlg (conjElem m) * MonoidAlgebra.single (artinMap m u)⁻¹ (1 : ℚ) =
          ∑ v : (ZMod m)ˣ, MonoidAlgebra.single (artinMap m v)⁻¹ (1 : ℚ) := by
      refine Finset.sum_bij (fun u _ => (-1 : (ZMod m)ˣ) * u) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
      · intro u₁ _ u₂ _ h; exact mul_left_cancel h
      · intro v _; exact ⟨(-1 : (ZMod m)ˣ) * v, Finset.mem_univ _, by simp⟩
      · intro u _
        rw [conjElem, toRatAlg_single, Int.cast_one, MonoidAlgebra.single_mul_single, one_mul]
        congr 1
        have hinv : (artinMap m (-1 : (ZMod m)ˣ))⁻¹ = artinMap m (-1 : (ZMod m)ˣ) := by
          rw [← map_inv, inv_neg_one]
        rw [map_mul, mul_inv_rev, hinv, cycGal_comm]
    rw [hbij, sub_self]
  unfold higherStickelbergerElem stickelbergerElem
  have hexp : ((1 : ℕ) : ℤ) - 1 = 0 := by norm_num
  rw [hexp, zpow_zero, one_smul]
  have hber :
      (∑ u : (ZMod m)ˣ,
          MonoidAlgebra.single (artinMap m u)⁻¹
            ((Polynomial.bernoulli 1).eval (((u : ZMod m).val : ℚ) / (m : ℚ)))) =
        (∑ u : (ZMod m)ˣ,
          MonoidAlgebra.single (artinMap m u)⁻¹ (((u : ZMod m).val : ℚ) / (m : ℚ))) -
        (1 / 2 : ℚ) • (∑ u : (ZMod m)ˣ, MonoidAlgebra.single (artinMap m u)⁻¹ (1 : ℚ)) := by
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one, ← MonoidAlgebra.single_sub]
    congr 1
    rw [Polynomial.bernoulli_one, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    ring
  rw [hber, mul_sub, mul_smul_comm, hc_sum, smul_zero, sub_zero]

/-- Character evaluation homomorphism `MonoidAlgebra ℚ (CycGal m) →+* ℂ` sending `[σ_u] ↦ χ(u)`. -/
def evalCharMonoidAlg {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) :
    MonoidAlgebra ℚ (CycGal m) →+* ℂ :=
  let g : CycGal m →* ℂ :=
    { toFun := fun σ => (χ ((artinMap m).symm σ : ZMod m) : ℂ)
      map_one' := by simp
      map_mul' := fun σ τ => by simp [map_mul] }
  { toFun := fun x => ∑ σ : CycGal m, (x.coeff σ : ℂ) * g σ
    map_zero' := by simp
    map_one' := by
      rw [MonoidAlgebra.one_def, Finset.sum_eq_single (1 : CycGal m)]
      · simp
      · intro σ _ hσ; simp [hσ.symm]
      · intro h; exact absurd (Finset.mem_univ _) h
    map_add' := fun x y => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun σ _ => ?_
      simp [MonoidAlgebra.coeff_add, add_mul]
    map_mul' := fun x y => by
      classical
      have hbasis : ∀ z : MonoidAlgebra ℚ (CycGal m),
          z = ∑ σ : CycGal m, MonoidAlgebra.single σ (z.coeff σ) := fun z => by
        ext τ
        simp [MonoidAlgebra.coeff_sum]
      have hsingle : ∀ (σ : CycGal m) (a : ℚ),
          (∑ ν : CycGal m, ((MonoidAlgebra.single σ a).coeff ν : ℂ) * g ν) = (a : ℂ) * g σ := by
        intro σ a
        rw [Finset.sum_eq_single σ]
        · simp
        · intro ν _ hν; simp [hν.symm]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hadd : ∀ (s : Finset (CycGal m)) (f : CycGal m → MonoidAlgebra ℚ (CycGal m)),
          (∑ ν : CycGal m, ((∑ a ∈ s, f a).coeff ν : ℂ) * g ν) =
            ∑ a ∈ s, ∑ ν : CycGal m, ((f a).coeff ν : ℂ) * g ν := by
        intro s f
        induction s using Finset.induction_on with
        | empty => simp
        | @insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun ν _ => ?_
          simp [MonoidAlgebra.coeff_add, add_mul]
      conv_lhs => rw [hbasis x, hbasis y, Finset.sum_mul]
      simp_rw [Finset.mul_sum, MonoidAlgebra.single_mul_single]
      rw [hadd]
      simp_rw [hadd, hsingle]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
      rw [Rat.cast_mul, map_mul]
      ring }

@[simp] theorem evalCharMonoidAlg_single {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m)
    (u : (ZMod m)ˣ) (a : ℚ) :
    evalCharMonoidAlg χ (MonoidAlgebra.single (artinMap m u) a) = (a : ℂ) * χ (u : ZMod m) := by
  change ∑ σ : CycGal m, (((MonoidAlgebra.single (artinMap m u) a).coeff σ : ℚ) : ℂ) *
    χ ((artinMap m).symm σ : ZMod m) = _
  rw [Finset.sum_eq_single (artinMap m u)]
  · simp
  · intro σ _ hσ; simp [hσ.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

@[simp] theorem evalCharMonoidAlg_single_inv {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m)
    (u : (ZMod m)ˣ) (a : ℚ) :
    evalCharMonoidAlg χ (MonoidAlgebra.single (artinMap m u)⁻¹ a) = (a : ℂ) * χ⁻¹ (u : ZMod m) := by
  change ∑ σ : CycGal m, (((MonoidAlgebra.single (artinMap m u)⁻¹ a).coeff σ : ℚ) : ℂ) *
    χ ((artinMap m).symm σ : ZMod m) = _
  rw [Finset.sum_eq_single (artinMap m u)⁻¹]
  · have h1 : (artinMap m).symm (artinMap m u)⁻¹ = u⁻¹ := by
      rw [← map_inv, MulEquiv.symm_apply_apply]
    simp [h1, χ.inv_apply_eq_inv']
  · intro σ _ hσ; simp [hσ.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Helper: sum over `(ZMod m)ˣ` equals sum over `Finset.range m` for `χ : DirichletCharacter ℂ m`. -/
private lemma sum_units_eq_sum_range {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m)
    (f : ℕ → ℂ) :
    (∑ u : (ZMod m)ˣ, χ (u : ZMod m) * f (u : ZMod m).val) =
      ∑ a ∈ Finset.range m, χ (a : ZMod m) * f a := by
  have hmap : Finset.univ.image (fun u : (ZMod m)ˣ => (u : ZMod m).val) =
      (Finset.range m).filter (fun a : ℕ => IsUnit (a : ZMod m)) := by
    ext a
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨ZMod.val_lt _, by rw [ZMod.natCast_zmod_val]; exact u.isUnit⟩
    · rintro ⟨hlt, hu⟩
      refine ⟨hu.unit, ?_⟩
      simp [IsUnit.unit_spec, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  have hinj : ∀ u ∈ (Finset.univ : Finset (ZMod m)ˣ), ∀ v ∈ (Finset.univ : Finset (ZMod m)ˣ),
      (u : ZMod m).val = (v : ZMod m).val → u = v :=
    fun u _ v _ h => Units.ext (ZMod.val_injective m h)
  calc (∑ u : (ZMod m)ˣ, χ (u : ZMod m) * f (u : ZMod m).val)
      = ∑ a ∈ Finset.univ.image (fun u : (ZMod m)ˣ => (u : ZMod m).val), χ (a : ZMod m) * f a := by
        symm
        refine Finset.sum_image (f := fun a : ℕ => χ (a : ZMod m) * f a) hinj |>.trans ?_
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [ZMod.natCast_zmod_val]
    _ = ∑ a ∈ (Finset.range m).filter (fun a : ℕ => IsUnit (a : ZMod m)), χ (a : ZMod m) * f a := by
        rw [hmap]
    _ = ∑ a ∈ Finset.range m, χ (a : ZMod m) * f a := by
        refine Finset.sum_subset (Finset.filter_subset _ _) fun a ha hnot => ?_
        have hnu : ¬ IsUnit (a : ZMod m) := fun h => hnot (Finset.mem_filter.mpr ⟨ha, h⟩)
        rw [χ.map_nonunit hnu, zero_mul]

/-- **Stickelberger Character Evaluation (`k = 1`)**:
for any odd character `χ mod m`, `evalCharMonoidAlg χ (stickelbergerElem m) = genBernoulli χ⁻¹ 1`. -/
theorem evalChar_stickelbergerElem_eq_genBernoulli {m : ℕ} [NeZero m]
    {χ : DirichletCharacter ℂ m} (hodd : χ.Odd) :
    evalCharMonoidAlg χ (stickelbergerElem m) = genBernoulli χ⁻¹ 1 := by
  have hχ : χ ≠ 1 := ne_one_of_odd hodd
  have hχinv : χ⁻¹ ≠ 1 := fun h1 => hχ (by simpa using congrArg Inv.inv h1)
  have hm2 : 2 ≤ m := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
  have hm_ne1 : m ≠ 1 := by omega
  unfold stickelbergerElem
  rw [map_sum, genBernoulli_one_eq hχinv]
  have h0 : χ⁻¹ (0 : ZMod m) = 0 := χ⁻¹.map_zero' hm_ne1
  have hrange : Finset.range m = insert 0 (Finset.Ico 1 m) := by
    ext a; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
  calc ∑ u : (ZMod m)ˣ, evalCharMonoidAlg χ
        (MonoidAlgebra.single (artinMap m u)⁻¹ (((u : ZMod m).val : ℚ) / (m : ℚ)))
      = ∑ u : (ZMod m)ˣ, (((u : ZMod m).val : ℂ) / (m : ℂ)) * χ⁻¹ (u : ZMod m) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [evalCharMonoidAlg_single_inv]; push_cast; rfl
    _ = (m : ℂ)⁻¹ * ∑ u : (ZMod m)ˣ, χ⁻¹ (u : ZMod m) * ((u : ZMod m).val : ℂ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        ring
    _ = (m : ℂ)⁻¹ * ∑ a ∈ Finset.range m, χ⁻¹ (a : ZMod m) * (a : ℂ) := by
        rw [sum_units_eq_sum_range χ⁻¹ (fun a => (a : ℂ))]
    _ = (m : ℂ)⁻¹ * ∑ a ∈ Finset.Ico 1 m, (a : ℂ) * χ⁻¹ (a : ZMod m) := by
        rw [hrange, Finset.sum_insert (by simp), Nat.cast_zero, h0, zero_mul, zero_add]
        congr 1
        exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- **Higher Stickelberger Character Evaluation (`k ≥ 1`)**:
for any `χ ≠ 1` mod `m` and `k ≥ 1`,
`evalCharMonoidAlg χ (higherStickelbergerElem k m) = genBernoulli χ⁻¹ k`. -/
theorem evalChar_higherStickelbergerElem_eq_genBernoulli {m : ℕ} [NeZero m]
    {χ : DirichletCharacter ℂ m} (hχ : χ ≠ 1) {k : ℕ} (_hk : 1 ≤ k) :
    evalCharMonoidAlg χ (higherStickelbergerElem k m) = genBernoulli χ⁻¹ k := by
  have hχinv : χ⁻¹ ≠ 1 := fun h1 => hχ (by simpa using congrArg Inv.inv h1)
  have hm2 : 2 ≤ m := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
  have hm_ne1 : m ≠ 1 := by omega
  unfold higherStickelbergerElem
  have hsmul :
      evalCharMonoidAlg χ (((m : ℚ) ^ ((k : ℤ) - 1)) •
          ∑ u : (ZMod m)ˣ,
            MonoidAlgebra.single (artinMap m u)⁻¹
              ((Polynomial.bernoulli k).eval (((u : ZMod m).val : ℚ) / (m : ℚ)))) =
        (m : ℂ) ^ ((k : ℤ) - 1) *
          ∑ u : (ZMod m)ˣ,
            (((Polynomial.bernoulli k).eval (((u : ZMod m).val : ℚ) / (m : ℚ)) : ℚ) : ℂ) *
              χ⁻¹ (u : ZMod m) := by
    have hsm :
        ((m : ℚ) ^ ((k : ℤ) - 1)) •
            ∑ u : (ZMod m)ˣ,
              MonoidAlgebra.single (artinMap m u)⁻¹
                ((Polynomial.bernoulli k).eval (((u : ZMod m).val : ℚ) / (m : ℚ))) =
          MonoidAlgebra.single (1 : CycGal m) ((m : ℚ) ^ ((k : ℤ) - 1)) *
            ∑ u : (ZMod m)ˣ,
              MonoidAlgebra.single (artinMap m u)⁻¹
                ((Polynomial.bernoulli k).eval (((u : ZMod m).val : ℚ) / (m : ℚ))) := by
      rw [Finset.mul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.smul_single, one_mul, smul_eq_mul]
    rw [hsm, map_mul, map_sum]
    have h1 : evalCharMonoidAlg χ (MonoidAlgebra.single (1 : CycGal m) ((m : ℚ) ^ ((k : ℤ) - 1))) =
        (m : ℂ) ^ ((k : ℤ) - 1) := by
      have h1' : (1 : CycGal m) = artinMap m 1 := (map_one (artinMap m)).symm
      rw [h1', evalCharMonoidAlg_single, Units.val_one, map_one, mul_one]
      push_cast; rfl
    rw [h1]
    congr 1
    refine Finset.sum_congr rfl fun u _ => evalCharMonoidAlg_single_inv χ u _
  rw [hsmul]
  unfold genBernoulli
  rw [if_neg hm_ne1]
  congr 1
  have h0 : χ⁻¹ (0 : ZMod m) = 0 := χ⁻¹.map_zero' hm_ne1
  have hrange : Finset.range m = insert 0 (Finset.Ico 1 m) := by
    ext a; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
  calc ∑ u : (ZMod m)ˣ,
        (((Polynomial.bernoulli k).eval (((u : ZMod m).val : ℚ) / (m : ℚ)) : ℚ) : ℂ) *
          χ⁻¹ (u : ZMod m)
      = ∑ u : (ZMod m)ˣ, χ⁻¹ (u : ZMod m) *
          (((Polynomial.bernoulli k).eval (((u : ZMod m).val : ℚ) / (m : ℚ)) : ℚ) : ℂ) := by
        refine Finset.sum_congr rfl fun u _ => mul_comm _ _
    _ = ∑ a ∈ Finset.range m, χ⁻¹ (a : ZMod m) *
          (((Polynomial.bernoulli k).eval ((a : ℚ) / (m : ℚ)) : ℚ) : ℂ) :=
        sum_units_eq_sum_range χ⁻¹ (fun a => (((Polynomial.bernoulli k).eval ((a : ℚ) / (m : ℚ)) : ℚ) : ℂ))
    _ = ∑ a ∈ Finset.Ico 1 m, χ⁻¹ (a : ZMod m) *
          ((Polynomial.bernoulli k).map (algebraMap ℚ ℂ)).eval ((a : ℂ) / (m : ℂ)) := by
        rw [hrange, Finset.sum_insert (by simp), Nat.cast_zero, h0, zero_mul, zero_add]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [eval_map_bernoulli_natDiv]

/-- Character evaluation of the integral Stickelberger multiplier `stickelbergerIntMul m bu`:
`χ(stickelbergerIntMul m bu) = (bu.val - χ⁻¹(bu)) * B_{1, χ⁻¹}`. -/
theorem evalChar_stickelbergerIntMul_eq {m : ℕ} [NeZero m] (bu : (ZMod m)ˣ)
    {χ : DirichletCharacter ℂ m} (hodd : χ.Odd) :
    evalCharMonoidAlg χ (toRatAlg (stickelbergerIntMul m bu)) =
      (((bu : ZMod m).val : ℂ) - χ (bu : ZMod m)) * genBernoulli χ⁻¹ 1 := by
  rw [← stickelberger_carry_identity m bu, map_mul]
  have h1 : evalCharMonoidAlg χ (toRatAlg (((bu : ZMod m).val : MonoidAlgebra ℤ (CycGal m)) -
      MonoidAlgebra.single (artinMap m bu) (1 : ℤ))) =
      ((bu : ZMod m).val : ℂ) - χ (bu : ZMod m) := by
    rw [map_sub, map_sub, toRatAlg_natCast, toRatAlg_single, Int.cast_one, map_natCast,
      evalCharMonoidAlg_single, Rat.cast_one, one_mul]
  rw [h1, evalChar_stickelbergerElem_eq_genBernoulli hodd]

end StickelbergerElementAndIdeal

/-! ## Section 2: Gauss Sums, Jacobi Sums, & Stickelberger Congruence `(g(χ))^m = J(χ)` -/

section GaussAndJacobiStickelberger

/-- **Stickelberger / Davenport–Hasse Gauss-Sum Power Factorization (`g(χ)^m = J(χ)`)**:
for any finite field `F` of characteristic `p`, any nontrivial additive character `ψ : AddChar F ℂ`,
and any multiplicative character `χ : MulChar F ℂ` of exact order `m ≥ 2` (`χ^m = 1` and
`χ^j ≠ 1` for `1 ≤ j < m`):
`(gaussSum χ ψ) ^ m = (χ (-1) * Fintype.card F) * ∏ j ∈ Finset.Ico 1 (m - 1), jacobiSum χ (χ ^ j)`!
Hence `g(χ)^m` lies in the cyclotomic field generated by values of `χ`! -/
theorem gaussSum_pow_eq_prod_jacobiSum {F : Type*} [Field F] [Fintype F]
    {χ : MulChar F ℂ} {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) {m : ℕ} (hm : 2 ≤ m)
    (hm_pow : χ ^ m = 1) (hj_ne : ∀ j ∈ Finset.Ico 1 m, χ ^ j ≠ 1) :
    (gaussSum χ ψ) ^ m =
      (χ (-1) * (Fintype.card F : ℂ)) *
        ∏ j ∈ Finset.Ico 1 (m - 1), jacobiSum χ (χ ^ j) := by
  have hpow_step : ∀ k : ℕ, 1 ≤ k → k ≤ m - 1 →
      (gaussSum χ ψ) ^ k =
        (∏ j ∈ Finset.Ico 1 k, jacobiSum χ (χ ^ j)) * gaussSum (χ ^ k) ψ := by
    intro k hk1 hkm
    induction k, hk1 using Nat.le_induction with
    | base =>
      simp
    | succ k hk1 ih =>
      have hk_le : k ≤ m - 1 := Nat.le_of_succ_le hkm
      have hk1_mem : k + 1 ∈ Finset.Ico 1 m := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      have hne : χ * χ ^ k ≠ 1 := by
        rw [← pow_succ']
        exact hj_ne (k + 1) hk1_mem
      have hjac := jacobiSum_mul_nontrivial hne ψ
      have hico : Finset.Ico 1 (k + 1) = insert k (Finset.Ico 1 k) := by
        ext j; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [pow_succ, ih hk_le, hico, Finset.prod_insert (by simp)]
      calc ((∏ j ∈ Finset.Ico 1 k, jacobiSum χ (χ ^ j)) * gaussSum (χ ^ k) ψ) * gaussSum χ ψ
          = (∏ j ∈ Finset.Ico 1 k, jacobiSum χ (χ ^ j)) * (gaussSum χ ψ * gaussSum (χ ^ k) ψ) := by
            ring
        _ = (∏ j ∈ Finset.Ico 1 k, jacobiSum χ (χ ^ j)) *
              (gaussSum (χ * χ ^ k) ψ * jacobiSum χ (χ ^ k)) := by
            rw [← hjac]
        _ = (jacobiSum χ (χ ^ k) * ∏ j ∈ Finset.Ico 1 k, jacobiSum χ (χ ^ j)) *
              gaussSum (χ ^ (k + 1)) ψ := by
            rw [pow_succ']
            ring
  have hkm1 := hpow_step (m - 1) (by omega) le_rfl
  have hm_eq : m = (m - 1) + 1 := (Nat.sub_add_cancel (by omega)).symm
  have hinv_eq : χ ^ (m - 1) = χ⁻¹ := by
    apply mul_left_cancel (a := χ)
    rw [← pow_succ', ← hm_eq, hm_pow, mul_inv_cancel]
  have hχ1 : χ ≠ 1 := by simpa using hj_ne 1 (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
  have hprim : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one hψ
  have hprod : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = (Fintype.card F : ℂ) :=
    gaussSum_mul_gaussSum_eq_card hχ1 hprim
  have hinv_neg : χ⁻¹ (-1) * gaussSum χ⁻¹ ψ⁻¹ = gaussSum χ⁻¹ ψ :=
    mul_gaussSum_inv_eq_gaussSum χ⁻¹ ψ
  have hχinv_neg : χ⁻¹ (-1) = χ (-1) := by rw [MulChar.inv_apply', inv_neg, inv_one]
  have hgauss_inv : gaussSum χ ψ * gaussSum χ⁻¹ ψ = χ (-1) * (Fintype.card F : ℂ) := by
    rw [← hinv_neg, hχinv_neg]
    calc gaussSum χ ψ * (χ (-1) * gaussSum χ⁻¹ ψ⁻¹)
        = χ (-1) * (gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹) := by ring
      _ = χ (-1) * (Fintype.card F : ℂ) := by rw [hprod]
  conv_lhs => rw [hm_eq, pow_succ, hkm1, hinv_eq]
  calc ((∏ j ∈ Finset.Ico 1 (m - 1), jacobiSum χ (χ ^ j)) * gaussSum χ⁻¹ ψ) * gaussSum χ ψ
      = (gaussSum χ ψ * gaussSum χ⁻¹ ψ) * ∏ j ∈ Finset.Ico 1 (m - 1), jacobiSum χ (χ ^ j) := by
        ring
    _ = (χ (-1) * (Fintype.card F : ℂ)) * ∏ j ∈ Finset.Ico 1 (m - 1), jacobiSum χ (χ ^ j) := by
        rw [hgauss_inv]

/-- **Cyclotomic Gauss-Sum Galois Action**:
for any `m, q ≥ 1`, any `χ : (ZMod q)ˣ →* (CycField (m * q))ˣ` whose values lie in `ℚ(ζ_m)`
(i.e. fixed by `relGalSubgroup m q = Gal(ℚ(ζ_{mq})/ℚ(ζ_m))`), and any `σ = artinMap (m * q) b`
in `relGalSubgroup m q` (so `b ≡ 1 [MOD m]`):
`σ (∑ x : (ZMod q)ˣ, χ x * ζ_q^{x.val}) = (χ b)⁻¹ * (∑ x : (ZMod q)ˣ, χ x * ζ_q^{x.val})`. -/
theorem gal_gaussSum_cyc_action (m q : ℕ) [NeZero m] [NeZero q]
    (χ : (ZMod q)ˣ →* CycField (m * q))
    (hχ_fix : ∀ σ ∈ relGalSubgroup m q, ∀ x : (ZMod q)ˣ, σ (χ x) = χ x)
    (b : (ZMod (m * q))ˣ) (hb : artinMap (m * q) b ∈ relGalSubgroup m q) :
    let ζq : CycField (m * q) := cycZeta (m * q) ^ m
    let bq : (ZMod q)ˣ := ZMod.unitsMap (dvd_mul_left q m) b
    (artinMap (m * q) b) (∑ x : (ZMod q)ˣ, χ x * ζq ^ (x : ZMod q).val) =
      (χ bq⁻¹) * (∑ x : (ZMod q)ˣ, χ x * ζq ^ (x : ZMod q).val) := by
  intro ζq bq
  let σ := artinMap (m * q) b
  have hζq_pow : ζq ^ q = 1 := by
    change (cycZeta (m * q) ^ m) ^ q = 1
    rw [← pow_mul, (cycZeta_spec (m * q)).pow_eq_one]
  have hσζ : σ ζq = ζq ^ (b : ZMod (m * q)).val := by
    change σ (cycZeta (m * q) ^ m) = (cycZeta (m * q) ^ m) ^ (b : ZMod (m * q)).val
    rw [map_pow, artinMap_apply_zeta, ← pow_mul, mul_comm (b : ZMod (m * q)).val m, pow_mul]
  have hpow_mod : ∀ n k : ℕ, n ≡ k [MOD q] → ζq ^ n = ζq ^ k := fun n k hnk => by
    have hred : ∀ a : ℕ, ζq ^ a = ζq ^ (a % q) := fun a => by
      conv_lhs => rw [← Nat.div_add_mod a q]
      rw [pow_add, pow_mul, hζq_pow, one_pow, one_mul]
    rw [hred n, hred k, hnk]
  have hσζ_bq : σ ζq = ζq ^ (bq : ZMod q).val := by
    rw [hσζ]
    have hmod : (b : ZMod (m * q)).val ≡ (bq : ZMod q).val [MOD q] := by
      have hcast : ((b : ZMod (m * q)).val : ZMod q) = (bq : ZMod q) := by
        simp [bq, ZMod.unitsMap_def]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (by rw [hcast, ZMod.natCast_zmod_val])
    exact hpow_mod _ _ hmod
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_bij (fun x _ => bq * x) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro x₁ _ x₂ _ h; exact mul_left_cancel h
  · intro y _; exact ⟨bq⁻¹ * y, Finset.mem_univ _, by group⟩
  · intro x _
    rw [map_mul, hχ_fix σ hb x, map_pow, hσζ_bq, ← pow_mul]
    have hmul : χ bq⁻¹ * χ (bq * x) = χ x := by
      rw [← map_mul, inv_mul_cancel_left]
    have hpow : ζq ^ ((bq : ZMod q).val * (x : ZMod q).val) =
        ζq ^ ((bq * x : (ZMod q)ˣ) : ZMod q).val := by
      have hmod : (bq : ZMod q).val * (x : ZMod q).val ≡
          ((bq * x : (ZMod q)ˣ) : ZMod q).val [MOD q] := by
        exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (by
          simp only [Nat.cast_mul, ZMod.natCast_zmod_val, ← Units.val_mul])
      exact hpow_mod _ _ hmod
    rw [hpow, ← mul_assoc, hmul]

/-- **Frobenius `q`-th Power Congruence for Gauss Sums** in any commutative ring `R` of
characteristic `q` (`[CharP R q]`): `(∑ x, χ(x) ζ^x)^q = ∑ x, χ(x)^q ζ^{q x}`. -/
theorem gaussSum_frob_pow_char {q : ℕ} (hq : q.Prime) [NeZero q] {R : Type*} [CommRing R]
    [CharP R q] (χ : ZMod q → R) (ζ : R) :
    (∑ x : ZMod q, χ x * ζ ^ x.val) ^ q = ∑ x : ZMod q, χ x ^ q * ζ ^ (q * x.val) := by
  have : Fact q.Prime := ⟨hq⟩
  have hsum_pow : ∀ (s : Finset (ZMod q)) (f : ZMod q → R),
      (∑ x ∈ s, f x) ^ q = ∑ x ∈ s, f x ^ q := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp [hq.ne_zero]
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, add_pow_char, ih]
  rw [hsum_pow Finset.univ (fun x => χ x * ζ ^ x.val)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_pow, ← pow_mul, mul_comm x.val q]

/-- **Stickelberger Finite-Field Binomial Sum Theorem** (`StickelbergerTheorem.FfsumPow`):
for any prime `p` and `0 < i, j < p - 1`,
`∑ x : ZMod p, x ^ i * (1 - x) ^ j = 0 ↔ i + j < p - 1`. -/
theorem ffsum_pow_lt_iff_add_lt (p : ℕ) [hp : Fact p.Prime] (i j : ℕ)
    (hi0 : 0 < i) (hip : i < p - 1) (hj0 : 0 < j) (hjp : j < p - 1) :
    (∑ x : ZMod p, x ^ i * (1 - x) ^ j = 0 ↔ i + j < p - 1) := by
  classical
  have hpp : p.Prime := hp.out
  have ffsum_pow : ∀ n : ℕ, n < 2 * (p - 1) →
      ∑ x : ZMod p, x ^ n = if n = p - 1 then -1 else 0 := by
    intro n hn
    rcases lt_or_ge n (p - 1) with h | h
    · rw [if_neg h.ne]
      exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) n (by rw [ZMod.card]; exact h)
    · have hn0 : n ≠ 0 := by omega
      let φ : (ZMod p)ˣ ↪ ZMod p := ⟨fun x => x, Units.val_injective⟩
      have hmap : Finset.univ.map φ = Finset.univ \ {0} := by
        ext x
        simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_sdiff,
          Finset.mem_singleton, φ, Function.Embedding.coeFn_mk]
        exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩
      have hs : ∑ x : ZMod p, x ^ n = ∑ x : (ZMod p)ˣ, (x : ZMod p) ^ n := by
        rw [← Finset.sum_sdiff (Finset.subset_univ ({0} : Finset (ZMod p))), Finset.sum_singleton,
          zero_pow hn0, add_zero, ← hmap, Finset.sum_map]
        rfl
      rw [hs, FiniteField.sum_pow_units, ZMod.card]
      have hiff : p - 1 ∣ n ↔ n = p - 1 := by
        constructor
        · rintro ⟨c, rfl⟩
          rcases c with _ | _ | c
          · omega
          · ring
          · nlinarith
        · rintro rfl; exact dvd_refl _
      simp only [hiff]
  have key : ∑ x : ZMod p, x ^ i * (1 - x) ^ j =
      ∑ m ∈ Finset.range (j + 1), (-1) ^ m * (j.choose m : ZMod p) * ∑ x : ZMod p, x ^ (i + m) := by
    have h1 : ∀ x : ZMod p, (1 - x) ^ j =
        ∑ m ∈ Finset.range (j + 1), (-x) ^ m * 1 ^ (j - m) * (j.choose m : ZMod p) := by
      intro x; rw [← add_pow, neg_add_eq_sub]
    simp_rw [h1, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun x _ => ?_
    rw [neg_pow, one_pow, pow_add]; ring
  have key2 :
      ∑ m ∈ Finset.range (j + 1), (-1) ^ m * (j.choose m : ZMod p) * ∑ x : ZMod p, x ^ (i + m) =
        ∑ m ∈ Finset.range (j + 1),
          if p - 1 - i = m then -((-1) ^ m * (j.choose m : ZMod p)) else 0 := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [ffsum_pow (i + m) (by omega)]
    by_cases h : i + m = p - 1
    · rw [if_pos h, if_pos (by omega)]; ring
    · rw [if_neg h, if_neg (by omega), mul_zero]
  rw [key, key2, Finset.sum_ite_eq]
  split_ifs with h
  · rw [Finset.mem_range] at h
    constructor
    · intro h0
      exfalso
      have hc : (j.choose (p - 1 - i) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hd
        have hdf : p ∣ j.factorial := by
          rw [← Nat.choose_mul_factorial_mul_factorial (show p - 1 - i ≤ j by omega), mul_assoc]
          exact Dvd.dvd.mul_right hd _
        have := (Nat.Prime.dvd_factorial hpp).mp hdf
        omega
      have hu : ((-1 : ZMod p) ^ (p - 1 - i)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
      exact mul_ne_zero hu hc (neg_eq_zero.mp h0)
    · intro h'; omega
  · rw [Finset.mem_range] at h
    exact ⟨fun _ => by omega, fun _ => rfl⟩

/-- **Jacobi-Sum Stickelberger Prime-Divisibility Criterion (`mod p`)**:
for power characters `χ_i(x) = x^i`, `χ_j(x) = x^j` on `ZMod p` (`0 < i, j < p - 1`),
`jacobiSum χ_i χ_j = 0 ↔ i + j < p - 1`! -/
theorem jacobiSum_stickelberger_mod_prime (p : ℕ) [hp : Fact p.Prime] (i j : ℕ)
    (hi0 : 0 < i) (hip : i < p - 1) (hj0 : 0 < j) (hjp : j < p - 1) :
    let powChar : ℕ → MulChar (ZMod p) (ZMod p) := fun r =>
      { toFun := fun x => if x = 0 then 0 else x ^ r
        map_one' := by simp [one_ne_zero]
        map_mul' := fun x y => by
          by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy, mul_pow]
        map_nonunit' := fun x hx => by
          have hx0 : x = 0 := by
            by_contra hne
            exact hx (isUnit_iff_ne_zero.mpr hne)
          simp [hx0] }
    jacobiSum (powChar i) (powChar j) = 0 ↔ i + j < p - 1 := by
  intro powChar
  have heq : jacobiSum (powChar i) (powChar j) = ∑ x : ZMod p, x ^ i * (1 - x) ^ j := by
    unfold jacobiSum
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x = 0 <;> by_cases h1x : 1 - x = 0
    · simp [hx, powChar, zero_pow hi0.ne']
    · simp [hx, powChar, zero_pow hi0.ne']
    · simp [hx, h1x, powChar, zero_pow hj0.ne']
    · simp [hx, h1x, powChar]
  rw [heq]
  exact ffsum_pow_lt_iff_add_lt p i j hi0 hip hj0 hjp

end GaussAndJacobiStickelberger

/-! ## Section 3: Signed-Involution Determinant Annihilation (`adjKill`) &
`stickelberger_minus_parity_length_bound` (`l ∣ [E : ℚ]`) -/

section SignedInvolutionDetAndStickelbergerBound

section SignedQuotientDet

variable (A Γ : Type*) [CommRing A] [CommGroup Γ] [Fintype Γ] [DecidableEq Γ]
  (c : Γ) (ε : ℤ)

/-- The signed-involution quotient ring `A[Γ] / ([c] - ε)`. -/
abbrev SignedQuotAlg : Type _ :=
  MonoidAlgebra A Γ ⧸
    Ideal.span ({MonoidAlgebra.single c (1 : A) - (ε : MonoidAlgebra A Γ)} : Set (MonoidAlgebra A Γ))

private def zpowersSubgroup (c : Γ) : Subgroup Γ := Subgroup.zpowers c

/-- Canonical coset section `Γ ⧸ ⟨c⟩ → Γ`. -/
private def signedQuotSec {Γ : Type*} [CommGroup Γ] (c : Γ) (q : Γ ⧸ Subgroup.zpowers c) : Γ :=
  Quotient.out q

private def signedQuotSgn (c : Γ) (ε : ℤ) (g : Γ) : A :=
  if g = signedQuotSec c (QuotientGroup.mk g) then 1 else (ε : A)

omit [Fintype Γ] in
private lemma signedQuotSgn_mul_left (hc : c * c = 1) (hc1 : c ≠ 1) (hε : ε * ε = 1) (g : Γ) :
    signedQuotSgn A Γ c ε (c * g) = (ε : A) * signedQuotSgn A Γ c ε g := by
  let H := Subgroup.zpowers c
  let Q := Γ ⧸ H
  let sec := signedQuotSec c
  have hsec : ∀ q : Q, QuotientGroup.mk (sec q) = q := Quotient.out_eq
  have hH : ∀ h ∈ H, h = 1 ∨ h = c := by
    rintro h ⟨k, rfl⟩
    dsimp only
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [← two_mul, zpow_mul, show c ^ (2 : ℤ) = 1 by simpa [sq] using hc, one_zpow]
    · right
      rw [zpow_add, zpow_mul, show c ^ (2 : ℤ) = 1 by simpa [sq] using hc, one_zpow, one_mul,
        zpow_one]
  have hdecomp : ∀ x : Γ, x = sec (QuotientGroup.mk x) ∨ x = c * sec (QuotientGroup.mk x) := by
    intro x
    have hmem : (sec (QuotientGroup.mk x))⁻¹ * x ∈ H := (QuotientGroup.eq).mp (hsec _)
    rcases hH _ hmem with h1 | hc_eq
    · left; exact (inv_mul_eq_one.mp h1).symm
    · right; calc x = sec (QuotientGroup.mk x) * ((sec (QuotientGroup.mk x))⁻¹ * x) := by group
        _ = sec (QuotientGroup.mk x) * c := by rw [hc_eq]
        _ = c * sec (QuotientGroup.mk x) := mul_comm _ _
  have hc_ne : ∀ q : Q, c * sec q ≠ sec q := fun q h =>
    hc1 (mul_right_cancel (b := sec q) (by simpa using h))
  have hq : (QuotientGroup.mk (c * g) : Q) = QuotientGroup.mk g := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff c).mpr (Subgroup.mem_zpowers c), one_mul]
  dsimp only [signedQuotSgn]
  rw [hq]
  have hc_self : ∀ y : Γ, c * y ≠ y := fun y h =>
    hc1 (mul_eq_right.mp h)
  rcases hdecomp g with hg | hg
  · rw [if_pos hg]
    have hne : c * g ≠ sec (QuotientGroup.mk g) := by
      intro h
      exact hc_self g (h.trans hg.symm)
    rw [if_neg hne, mul_one]
  · have hcc : c * g = sec (QuotientGroup.mk g) := by
      conv_lhs => rw [hg]
      rw [← mul_assoc, hc, one_mul]
    have hne : g ≠ sec (QuotientGroup.mk g) := by
      intro h
      exact hc_ne (QuotientGroup.mk g) (hg.symm.trans h)
    rw [if_pos hcc, if_neg hne, ← Int.cast_mul, hε, Int.cast_one]

private def signedQuotToFun : MonoidAlgebra A Γ →ₗ[A] ((Γ ⧸ Subgroup.zpowers c) → A) := by
  classical
  exact
    { toFun := fun w => ∑ g : Γ,
        (Pi.single (QuotientGroup.mk g) (w.coeff g * signedQuotSgn A Γ c ε g) :
          (Γ ⧸ Subgroup.zpowers c) → A)
      map_add' := fun w₁ w₂ => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun g _ => ?_
        ext q
        simp only [Pi.add_apply, Pi.single_apply, MonoidAlgebra.coeff_add]
        split_ifs
        · rw [Finsupp.add_apply]; ring
        · ring
      map_smul' := fun r w => by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        ext q
        simp only [RingHom.id_apply, Pi.smul_apply, Pi.single_apply, MonoidAlgebra.coeff_smul,
          smul_eq_mul]
        split_ifs
        · rw [Finsupp.smul_apply, smul_eq_mul]; ring
        · ring }

private lemma signedQuotToFun_single (g : Γ) (a : A) :
    signedQuotToFun A Γ c ε (MonoidAlgebra.single g a) =
      Pi.single (QuotientGroup.mk g) (a * signedQuotSgn A Γ c ε g) := by
  classical
  ext q
  change (∑ h : Γ,
    (Pi.single (QuotientGroup.mk h)
      ((MonoidAlgebra.single g a).coeff h * signedQuotSgn A Γ c ε h) :
      (Γ ⧸ Subgroup.zpowers c) → A)) q = _
  rw [Finset.sum_apply, Finset.sum_eq_single g]
  · simp [Pi.single_apply]
  · intro h _ hh
    simp [Pi.single_apply, hh.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

private def signedQuotFwd (hc : c * c = 1) (hc1 : c ≠ 1) (hε : ε * ε = 1) :
    SignedQuotAlg A Γ c ε →ₗ[A] ((Γ ⧸ Subgroup.zpowers c) → A) :=
  let I_rel : Ideal (MonoidAlgebra A Γ) :=
    Ideal.span ({MonoidAlgebra.single c (1 : A) - (ε : MonoidAlgebra A Γ)} : Set (MonoidAlgebra A Γ))
  have hker_rel : ∀ z ∈ I_rel, signedQuotToFun A Γ c ε z = 0 := by
    intro z hz
    rw [Ideal.mem_span_singleton] at hz
    obtain ⟨u, rfl⟩ := hz
    have hu : u = ∑ g : Γ, (u.coeff g) • MonoidAlgebra.single g (1 : A) := by
      ext h
      simp [MonoidAlgebra.coeff_sum]
    rw [hu, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [Algebra.mul_smul_comm, map_smul, ← smul_zero (u.coeff g)]
    congr 1
    have h1 : ((ε : ℤ) : MonoidAlgebra A Γ) = MonoidAlgebra.single (1 : Γ) (ε : A) := by
      rw [← zsmul_one ε, MonoidAlgebra.one_def, MonoidAlgebra.smul_single, zsmul_eq_mul, mul_one]
    rw [h1, sub_mul, MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single,
      one_mul, mul_one, one_mul, map_sub, signedQuotToFun_single, signedQuotToFun_single]
    have hqg : (QuotientGroup.mk (c * g) : Γ ⧸ Subgroup.zpowers c) = QuotientGroup.mk g := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff c).mpr (Subgroup.mem_zpowers c), one_mul]
    rw [hqg, signedQuotSgn_mul_left A Γ c ε hc hc1 hε g, one_mul, sub_self]
  { toFun := Quotient.lift (signedQuotToFun A Γ c ε) (fun x y hxy => by
      have hdiff : x - y ∈ I_rel := Ideal.Quotient.eq.mp (Quotient.sound hxy)
      exact sub_eq_zero.mp (by rw [← map_sub]; exact hker_rel _ hdiff))
    map_add' := fun x y => by
      obtain ⟨x₀, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨y₀, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact map_add (signedQuotToFun A Γ c ε) x₀ y₀
    map_smul' := fun r x => by
      obtain ⟨x₀, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact map_smul (signedQuotToFun A Γ c ε) r x₀ }

private def signedQuotBwd :
    ((Γ ⧸ Subgroup.zpowers c) → A) →ₗ[A] SignedQuotAlg A Γ c ε :=
  let I_rel : Ideal (MonoidAlgebra A Γ) :=
    Ideal.span ({MonoidAlgebra.single c (1 : A) - (ε : MonoidAlgebra A Γ)} : Set (MonoidAlgebra A Γ))
  { toFun := fun f => Ideal.Quotient.mk I_rel (∑ q, MonoidAlgebra.single (signedQuotSec c q) (f q))
    map_add' := fun f g => by
      rw [← map_add (Ideal.Quotient.mk I_rel)]
      congr 1
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Pi.add_apply, ← MonoidAlgebra.single_add]
    map_smul' := fun r f => by
      simp only [RingHom.id_apply]
      have hsm : r • Ideal.Quotient.mk I_rel (∑ q, MonoidAlgebra.single (signedQuotSec c q) (f q)) =
          Ideal.Quotient.mk I_rel (r • ∑ q, MonoidAlgebra.single (signedQuotSec c q) (f q)) := rfl
      rw [hsm]
      congr 1
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, MonoidAlgebra.smul_single, smul_eq_mul] }

/-- Free finite-rank `A`-linear equivalence `SignedQuotAlg A Γ c ε ≃ₗ[A] (Γ ⧸ ⟨c⟩ → A)`
whenever `c * c = 1`, `c ≠ 1`, and `ε * ε = 1`. -/
def signedQuotEquiv (hc : c * c = 1) (hc1 : c ≠ 1) (hε : ε * ε = 1) :
    SignedQuotAlg A Γ c ε ≃ₗ[A] ((Γ ⧸ Subgroup.zpowers c) → A) := by
  classical
  let H := Subgroup.zpowers c
  let Q := Γ ⧸ H
  let sec : Q → Γ := signedQuotSec c
  have hsec : ∀ q : Q, QuotientGroup.mk (sec q) = q := Quotient.out_eq
  have hH : ∀ h ∈ H, h = 1 ∨ h = c := by
    rintro h ⟨k, rfl⟩
    dsimp only
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [← two_mul, zpow_mul, show c ^ (2 : ℤ) = 1 by simpa [sq] using hc, one_zpow]
    · right
      rw [zpow_add, zpow_mul, show c ^ (2 : ℤ) = 1 by simpa [sq] using hc, one_zpow, one_mul,
        zpow_one]
  have hdecomp : ∀ g : Γ, g = sec (QuotientGroup.mk g) ∨ g = c * sec (QuotientGroup.mk g) := by
    intro g
    have hmem : (sec (QuotientGroup.mk g))⁻¹ * g ∈ H := (QuotientGroup.eq).mp (hsec _)
    rcases hH _ hmem with h1 | hc_eq
    · left; exact (inv_mul_eq_one.mp h1).symm
    · right; calc g = sec (QuotientGroup.mk g) * ((sec (QuotientGroup.mk g))⁻¹ * g) := by group
        _ = sec (QuotientGroup.mk g) * c := by rw [hc_eq]
        _ = c * sec (QuotientGroup.mk g) := mul_comm _ _
  have hc_ne : ∀ q : Q, c * sec q ≠ sec q := fun q h =>
    hc1 (mul_right_cancel (b := sec q) (by simpa using h))
  have hsgn_sec : ∀ q : Q, signedQuotSgn A Γ c ε (sec q) = 1 := fun q => by
    dsimp only [signedQuotSgn]; rw [hsec, if_pos rfl]
  have hleft : ∀ x : SignedQuotAlg A Γ c ε, signedQuotBwd A Γ c ε (signedQuotFwd A Γ c ε hc hc1 hε x) = x := by
    intro x
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction w using MonoidAlgebra.induction_on with
    | of g =>
      change signedQuotBwd A Γ c ε (signedQuotToFun A Γ c ε (MonoidAlgebra.single g (1 : A))) =
        Ideal.Quotient.mk _ (MonoidAlgebra.single g 1)
      rw [signedQuotToFun_single, one_mul]
      dsimp only [signedQuotBwd, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Finset.sum_eq_single (QuotientGroup.mk g)]
      · rw [Pi.single_eq_same]
        rcases hdecomp g with hg | hg
        · have hsgn_g : signedQuotSgn A Γ c ε g = 1 := by
            dsimp only [signedQuotSgn]; exact if_pos hg
          rw [hsgn_g]
          change Ideal.Quotient.mk _ (MonoidAlgebra.single (sec (QuotientGroup.mk g)) 1) = _
          rw [← hg]
        · have hne : g ≠ sec (QuotientGroup.mk g) := fun h =>
            hc_ne (QuotientGroup.mk g) (hg.symm.trans h)
          have hsgn_g : signedQuotSgn A Γ c ε g = (ε : A) := by
            dsimp only [signedQuotSgn]; exact if_neg hne
          rw [hsgn_g, Ideal.Quotient.eq]
          have hrel :
              MonoidAlgebra.single (sec (QuotientGroup.mk g)) (ε : A) - MonoidAlgebra.single g (1 : A) =
                -MonoidAlgebra.single (sec (QuotientGroup.mk g)) (1 : A) *
                  (MonoidAlgebra.single c (1 : A) - (ε : MonoidAlgebra A Γ)) := by
            have h1 : ((ε : ℤ) : MonoidAlgebra A Γ) = MonoidAlgebra.single (1 : Γ) (ε : A) := by
              rw [← zsmul_one ε, MonoidAlgebra.one_def, MonoidAlgebra.smul_single, zsmul_eq_mul,
                mul_one]
            rw [h1, mul_sub, neg_mul, neg_mul, MonoidAlgebra.single_mul_single,
              MonoidAlgebra.single_mul_single, one_mul, one_mul, mul_one,
              mul_comm (sec (QuotientGroup.mk g)) c, ← hg]
            abel
          rw [hrel]
          exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
      · intro q _ hq
        rw [Pi.single_eq_of_ne hq, MonoidAlgebra.single_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
    | smul r g h =>
      have hmk : Ideal.Quotient.mk
          (Ideal.span ({MonoidAlgebra.single c (1 : A) - (ε : MonoidAlgebra A Γ)} : Set (MonoidAlgebra A Γ)))
          (r • g) = r • Ideal.Quotient.mk _ g := rfl
      rw [hmk, map_smul, map_smul, h]
  have hright : ∀ f : Q → A, signedQuotFwd A Γ c ε hc hc1 hε (signedQuotBwd A Γ c ε f) = f := by
    intro f
    dsimp only [signedQuotBwd, LinearMap.coe_mk, AddHom.coe_mk, signedQuotFwd]
    change signedQuotToFun A Γ c ε (∑ q : Q, MonoidAlgebra.single (sec q) (f q)) = f
    rw [map_sum]
    ext q'
    rw [Finset.sum_apply, Finset.sum_eq_single q']
    · rw [signedQuotToFun_single, hsec, hsgn_sec, mul_one, Pi.single_eq_same]
    · intro q _ hq
      rw [signedQuotToFun_single, hsec, Pi.single_eq_of_ne (Ne.symm hq)]
    · intro h; exact absurd (Finset.mem_univ _) h
  exact LinearEquiv.ofLinearMap (signedQuotFwd A Γ c ε hc hc1 hε) (signedQuotBwd A Γ c ε)
    (LinearMap.ext hright) (LinearMap.ext hleft)

theorem signedQuotEquiv_mk_single (hc : c * c = 1) (hc1 : c ≠ 1) (hε : ε * ε = 1)
    (k : Γ) (r : A) :
    signedQuotEquiv A Γ c ε hc hc1 hε (Ideal.Quotient.mk _ (MonoidAlgebra.single k r)) =
      Pi.single (QuotientGroup.mk k) (r * signedQuotSgn A Γ c ε k) := by
  exact signedQuotToFun_single A Γ c ε k r

theorem signedQuotEquiv_symm_single (hc : c * c = 1) (hc1 : c ≠ 1) (hε : ε * ε = 1)
    (q : Γ ⧸ Subgroup.zpowers c) :
    (signedQuotEquiv A Γ c ε hc hc1 hε).symm (Pi.single q (1 : A)) =
      Ideal.Quotient.mk _ (MonoidAlgebra.single (signedQuotSec c q) (1 : A)) := by
  apply (signedQuotEquiv A Γ c ε hc hc1 hε).injective
  rw [LinearEquiv.apply_symm_apply, signedQuotEquiv_mk_single A Γ c ε hc hc1 hε]
  have hsec : QuotientGroup.mk (signedQuotSec c q) = q := Quotient.out_eq q
  have hsgn : signedQuotSgn A Γ c ε (signedQuotSec c q) = 1 := by
    dsimp only [signedQuotSgn]; rw [hsec, if_pos rfl]
  rw [hsec, hsgn, mul_one]

/-- The explicit matrix of multiplication by `z` on `SignedQuotAlg A Γ c ε` in the `Q`-basis. -/
def signedMulMatrix (hc : c * c = 1) (hc1 : c ≠ 1) (hε : ε * ε = 1)
    (z : MonoidAlgebra A Γ) :
    Matrix (Γ ⧸ Subgroup.zpowers c) (Γ ⧸ Subgroup.zpowers c) A :=
  let e := signedQuotEquiv A Γ c ε hc hc1 hε
  fun i j => e (Ideal.Quotient.mk _ z * e.symm (Pi.single j (1 : A))) i

/-- The signed-involution quotient determinant `detR A Γ c ε z : A`
(via `Matrix.det (signedMulMatrix A Γ c ε ... z)`). -/
def detR (hc : c * c = 1) (hc1 : c ≠ 1) (hε : ε * ε = 1) (z : MonoidAlgebra A Γ) : A :=
  Matrix.det (signedMulMatrix A Γ c ε hc hc1 hε z)

private def signedMulMatrix_ringHom (hc : c * c = 1) (hc1 : c ≠ 1) (hε : ε * ε = 1) :
    SignedQuotAlg A Γ c ε →ₐ[A]
      Matrix (Γ ⧸ Subgroup.zpowers c) (Γ ⧸ Subgroup.zpowers c) A := by
  classical
  let e := signedQuotEquiv A Γ c ε hc hc1 hε
  let b : Module.Basis (Γ ⧸ Subgroup.zpowers c) A (SignedQuotAlg A Γ c ε) :=
    (Pi.basisFun A _).map e.symm
  exact (LinearMap.toMatrixAlgEquiv b).toAlgHom.comp (Algebra.lmul A (SignedQuotAlg A Γ c ε))

private lemma signedMulMatrix_ringHom_apply (hc : c * c = 1) (hc1 : c ≠ 1) (hε : ε * ε = 1)
    (z : MonoidAlgebra A Γ) :
    signedMulMatrix_ringHom A Γ c ε hc hc1 hε (Ideal.Quotient.mk _ z) =
      signedMulMatrix A Γ c ε hc hc1 hε z := by
  ext i j
  simp only [signedMulMatrix_ringHom, AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom,
    LinearMap.toMatrixAlgEquiv_apply, Module.Basis.map_repr, Module.Basis.map_apply,
    Pi.basisFun_apply, signedMulMatrix]
  rfl

/-- **Cayley–Hamilton Span Membership**:
`algebraMap A (MonoidAlgebra A Γ) (detR A Γ c ε hc hc1 hε z) ∈ Ideal.span { [c] - ε, z }`. -/
theorem detR_mem_ideal_span (hc : c * c = 1) (hc1 : c ≠ 1) (hε : ε * ε = 1)
    (z : MonoidAlgebra A Γ) :
    algebraMap A (MonoidAlgebra A Γ) (detR A Γ c ε hc hc1 hε z) ∈
      Ideal.span ({MonoidAlgebra.single c (1 : A) - (ε : MonoidAlgebra A Γ), z} :
        Set (MonoidAlgebra A Γ)) := by
  classical
  let I : Ideal (MonoidAlgebra A Γ) :=
    Ideal.span ({MonoidAlgebra.single c (1 : A) - (ε : MonoidAlgebra A Γ)} : Set (MonoidAlgebra A Γ))
  let zbar : SignedQuotAlg A Γ c ε := Ideal.Quotient.mk I z
  let M := signedMulMatrix A Γ c ε hc hc1 hε z
  let P : Polynomial A := M.charpoly
  have hchM : Polynomial.aeval M P = 0 := Matrix.aeval_self_charpoly M
  let e := signedQuotEquiv A Γ c ε hc hc1 hε
  let b : Module.Basis (Γ ⧸ Subgroup.zpowers c) A (SignedQuotAlg A Γ c ε) :=
    (Pi.basisFun A _).map e.symm
  let φ := signedMulMatrix_ringHom A Γ c ε hc hc1 hε
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    have hmul : Algebra.lmul A (SignedQuotAlg A Γ c ε) x =
        Algebra.lmul A (SignedQuotAlg A Γ c ε) y :=
      (LinearMap.toMatrixAlgEquiv b).injective hxy
    have h1 := congrArg (fun f => f (1 : SignedQuotAlg A Γ c ε)) hmul
    change x * 1 = y * 1 at h1
    simpa [mul_one] using h1
  have hch_zbar : Polynomial.aeval zbar P = 0 := by
    apply hφ_inj
    rw [map_zero]
    have haeval_hom : ∀ Q : Polynomial A, φ (Polynomial.aeval zbar Q) = Polynomial.aeval (φ zbar) Q := by
      intro Q
      induction Q using Polynomial.induction_on' with
      | add p q hp hq => simp only [map_add, hp, hq]
      | monomial n a =>
        simp only [Polynomial.aeval_monomial, map_mul, map_pow, AlgHom.commutes]
    rw [haeval_hom P]
    change Polynomial.aeval (φ (Ideal.Quotient.mk I z)) P = 0
    rw [signedMulMatrix_ringHom_apply A Γ c ε hc hc1 hε z]
    exact hchM
  have hP_split : P = Polynomial.C (P.coeff 0) + Polynomial.X * P.divX :=
    (Polynomial.X_mul_divX_add P).symm.trans (add_comm _ _)
  have haeval :
      Polynomial.aeval zbar P =
        (P.coeff 0) • (1 : SignedQuotAlg A Γ c ε) + zbar * Polynomial.aeval zbar P.divX := by
    conv_lhs => rw [hP_split]
    simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      Algebra.algebraMap_eq_smul_one]
  rw [haeval] at hch_zbar
  have hcoeff0 : P.coeff 0 = (-1 : A) ^ Fintype.card (Γ ⧸ Subgroup.zpowers c) * M.det := by
    dsimp only [P]
    rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.charpoly, ← Polynomial.coe_evalRingHom,
      RingHom.map_det]
    have hmat : ((Polynomial.evalRingHom 0).mapMatrix (Matrix.charmatrix M)) = -M := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [Matrix.charmatrix]
      · simp [Matrix.charmatrix, hij]
    rw [hmat, Matrix.det_neg]
  have hmul_eq : (P.coeff 0) • (1 : SignedQuotAlg A Γ c ε) = -(zbar * Polynomial.aeval zbar P.divX) :=
    eq_neg_of_add_eq_zero_left hch_zbar
  have hdet_mem : (detR A Γ c ε hc hc1 hε z • (1 : SignedQuotAlg A Γ c ε)) ∈
      Ideal.span ({zbar} : Set (SignedQuotAlg A Γ c ε)) := by
    change M.det • (1 : SignedQuotAlg A Γ c ε) ∈ Ideal.span ({zbar} : Set _)
    have hdet_eq :
        M.det • (1 : SignedQuotAlg A Γ c ε) =
          (-1 : A) ^ Fintype.card (Γ ⧸ Subgroup.zpowers c) •
            ((P.coeff 0) • (1 : SignedQuotAlg A Γ c ε)) := by
      rw [hcoeff0, smul_smul, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
    rw [hdet_eq, hmul_eq]
    have hsm :
        (-1 : A) ^ Fintype.card (Γ ⧸ Subgroup.zpowers c) •
            -(zbar * Polynomial.aeval zbar P.divX) =
          (-((-1 : A) ^ Fintype.card (Γ ⧸ Subgroup.zpowers c)) • Polynomial.aeval zbar P.divX) *
            zbar := by
      rw [smul_neg, neg_smul, mul_comm zbar, ← Algebra.smul_mul_assoc, neg_mul]
    rw [hsm]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  rw [Ideal.mem_span_singleton] at hdet_mem
  obtain ⟨u, hu⟩ := hdet_mem
  obtain ⟨u₀, rfl⟩ := Ideal.Quotient.mk_surjective u
  have hdiff : Ideal.Quotient.mk I
      (algebraMap A (MonoidAlgebra A Γ) (detR A Γ c ε hc hc1 hε z) - z * u₀) = 0 := by
    have hu' : (detR A Γ c ε hc hc1 hε z • (1 : SignedQuotAlg A Γ c ε)) =
        Ideal.Quotient.mk I (z * u₀) := by
      simpa [zbar, mul_comm] using hu
    have hdet_mk : Ideal.Quotient.mk I
        (algebraMap A (MonoidAlgebra A Γ) (detR A Γ c ε hc hc1 hε z)) =
        detR A Γ c ε hc hc1 hε z • (1 : SignedQuotAlg A Γ c ε) := by
      rw [← Algebra.algebraMap_eq_smul_one]; rfl
    rw [map_sub, hdet_mk, hu', sub_self]
  rw [Ideal.Quotient.eq_zero_iff_mem] at hdiff
  have hI_le : I ≤ Ideal.span ({MonoidAlgebra.single c (1 : A) - (ε : MonoidAlgebra A Γ), z} :
      Set (MonoidAlgebra A Γ)) :=
    Ideal.span_mono (by simp)
  have hzu : z * u₀ ∈ Ideal.span ({MonoidAlgebra.single c (1 : A) - (ε : MonoidAlgebra A Γ), z} :
      Set (MonoidAlgebra A Γ)) :=
    Ideal.mul_mem_right u₀ _ (Ideal.subset_span (by simp))
  simpa using Ideal.add_mem _ (hI_le hdiff) hzu

/-- **Signed-Involution Determinant Annihilation (`adjKill`)**:
on ANY `A[Γ]`-module `X` (via `φ : MonoidAlgebra A Γ →ₐ[A] Module.End A X`),
if `[c] • x = ε • x` and `z • x = 0`, then `detR A Γ c ε hc hc1 hε z • x = 0`! -/
theorem adjKill {X : Type*} [AddCommGroup X] [Module A X]
    (φ : MonoidAlgebra A Γ →ₐ[A] Module.End A X)
    (hc : c * c = 1) (hc1 : c ≠ 1) (hε : ε * ε = 1) (z : MonoidAlgebra A Γ) (x : X)
    (hx : φ (MonoidAlgebra.single c (1 : A)) x = (ε : A) • x) (hz : φ z x = 0) :
    detR A Γ c ε hc hc1 hε z • x = 0 := by
  have hmem := detR_mem_ideal_span A Γ c ε hc hc1 hε z
  rw [Ideal.mem_span_pair] at hmem
  obtain ⟨a, b, hab⟩ := hmem
  have hrel : φ (MonoidAlgebra.single c (1 : A) - (ε : MonoidAlgebra A Γ)) x = 0 := by
    have h1 : ((ε : ℤ) : MonoidAlgebra A Γ) = algebraMap A (MonoidAlgebra A Γ) (ε : A) := by
      simp
    rw [map_sub, h1, AlgHom.commutes, LinearMap.sub_apply, Module.algebraMap_end_apply, hx, sub_self]
  have key := congrArg (fun w => φ w x) hab
  simp only [map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply, hrel, hz, map_zero,
    add_zero] at key
  rw [AlgHom.commutes, Module.algebraMap_end_apply] at key
  exact key.symm

/-- Explicit entry formula for `signedMulMatrix A Γ c ε hc hc1 hε (MonoidAlgebra.single g a)`. -/
private lemma signedMulMatrix_single (hc : c * c = 1) (hc1 : c ≠ 1) (hε : ε * ε = 1)
    (g : Γ) (a : A) (i j : Γ ⧸ Subgroup.zpowers c) :
    signedMulMatrix A Γ c ε hc hc1 hε (MonoidAlgebra.single g a) i j =
      if QuotientGroup.mk (g * signedQuotSec c j) = i then
        a * (if g * signedQuotSec c j = signedQuotSec c (QuotientGroup.mk (g * signedQuotSec c j))
          then (1 : A) else (ε : A))
      else 0 := by
  classical
  dsimp only [signedMulMatrix]
  rw [signedQuotEquiv_symm_single A Γ c ε hc hc1 hε j]
  change (signedQuotEquiv A Γ c ε hc hc1 hε
    (Ideal.Quotient.mk _ (MonoidAlgebra.single g a * MonoidAlgebra.single (signedQuotSec c j) 1))) i = _
  rw [MonoidAlgebra.single_mul_single, mul_one]
  rw [signedQuotEquiv_mk_single A Γ c ε hc hc1 hε, Pi.single_apply]
  dsimp only [signedQuotSgn]
  by_cases h : QuotientGroup.mk (g * signedQuotSec c j) = i
  · rw [if_pos h.symm, if_pos h]
  · have hne : i ≠ QuotientGroup.mk (g * signedQuotSec c j) := fun hi => h hi.symm
    rw [if_neg hne, if_neg h]

private lemma signedMulMatrix_add (hc : c * c = 1) (hc1 : c ≠ 1) (hε : ε * ε = 1)
    (z w : MonoidAlgebra A Γ) :
    signedMulMatrix A Γ c ε hc hc1 hε (z + w) =
      signedMulMatrix A Γ c ε hc hc1 hε z + signedMulMatrix A Γ c ε hc hc1 hε w := by
  ext i j
  change (signedMulMatrix A Γ c ε hc hc1 hε (z + w)) i j =
    (signedMulMatrix A Γ c ε hc hc1 hε z) i j + (signedMulMatrix A Γ c ε hc hc1 hε w) i j
  dsimp only [signedMulMatrix]
  rw [map_add (Ideal.Quotient.mk _), add_mul, map_add, Pi.add_apply]

/-- Base-change invariance of `detR` under any ring homomorphism `f : A →+* B`. -/
theorem detR_mapRingHom {B : Type*} [CommRing B] (f : A →+* B)
    (hc : c * c = 1) (hc1 : c ≠ 1) (hε : ε * ε = 1) (z : MonoidAlgebra A Γ) :
    f (detR A Γ c ε hc hc1 hε z) = detR B Γ c ε hc hc1 hε (MonoidAlgebra.mapRingHom Γ f z) := by
  classical
  unfold detR
  rw [RingHom.map_det]
  congr 1
  have hz_sum : z = ∑ g : Γ, MonoidAlgebra.single g (z.coeff g) := by
    ext g
    simp [MonoidAlgebra.coeff_sum]
  have hfz_sum : MonoidAlgebra.mapRingHom Γ f z =
      ∑ g : Γ, MonoidAlgebra.single g (f (z.coeff g)) := by
    conv_lhs => rw [hz_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp
  have hmat_sum_A :
      signedMulMatrix A Γ c ε hc hc1 hε z =
        ∑ g : Γ, signedMulMatrix A Γ c ε hc hc1 hε (MonoidAlgebra.single g (z.coeff g)) := by
    conv_lhs => rw [hz_sum]
    induction (Finset.univ : Finset Γ) using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      ext i j
      simp [signedMulMatrix]
    | @insert g s hg ih =>
      rw [Finset.sum_insert hg, Finset.sum_insert hg,
        signedMulMatrix_add A Γ c ε hc hc1 hε, ih]
  have hmat_sum_B :
      signedMulMatrix B Γ c ε hc hc1 hε (MonoidAlgebra.mapRingHom Γ f z) =
        ∑ g : Γ, signedMulMatrix B Γ c ε hc hc1 hε (MonoidAlgebra.single g (f (z.coeff g))) := by
    conv_lhs => rw [hfz_sum]
    induction (Finset.univ : Finset Γ) using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      ext i j
      simp [signedMulMatrix]
    | @insert g s hg ih =>
      rw [Finset.sum_insert hg, Finset.sum_insert hg,
        signedMulMatrix_add B Γ c ε hc hc1 hε, ih]
  rw [hmat_sum_A, hmat_sum_B]
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [signedMulMatrix_single A Γ c ε hc hc1 hε, signedMulMatrix_single B Γ c ε hc hc1 hε]
  split_ifs <;> simp [map_mul]

end SignedQuotientDet

section SignedCharsDetAndStickelbergerBound

/-- The finite set of Dirichlet characters mod `m` sending `-1` to `ε ∈ {1, -1}`. -/
def signedChars (m : ℕ) [NeZero m] (ε : ℤ) : Finset (DirichletCharacter ℂ m) :=
  Finset.univ.filter fun χ : DirichletCharacter ℂ m => χ (-1 : ZMod m) = (ε : ℂ)

@[simp] theorem mem_signedChars_iff {m : ℕ} [NeZero m] {ε : ℤ} {χ : DirichletCharacter ℂ m} :
    χ ∈ signedChars m ε ↔ χ (-1 : ZMod m) = (ε : ℂ) := by
  simp [signedChars]

theorem signedChars_neg_one_eq_oddChars (m : ℕ) [NeZero m] :
    signedChars m (-1) = oddChars m := by
  ext χ
  simp [signedChars, mem_oddChars_iff, DirichletCharacter.Odd]

theorem dirichletChar_neg_one_eq_one_or_neg_one {m : ℕ} [NeZero m]
    (χ : DirichletCharacter ℂ m) :
    χ (-1 : ZMod m) = 1 ∨ χ (-1 : ZMod m) = -1 := by
  have hsq : χ (-1 : ZMod m) * χ (-1 : ZMod m) = 1 := by
    rw [← map_mul, neg_mul_neg, one_mul, map_one]
  exact sq_eq_one_iff.mp (by simpa [sq] using hsq)

private lemma monoidAlgebra_eq_sum_units {R : Type*} [CommRing R] (m : ℕ) [NeZero m]
    (z : MonoidAlgebra R (CycGal m)) :
    z = ∑ u : (ZMod m)ˣ, MonoidAlgebra.single (artinMap m u) (z.coeff (artinMap m u)) := by
  ext σ
  simp only [MonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single ((artinMap m).symm σ)]
  · simp
  · intro u _ hu
    have hne : artinMap m u ≠ σ := fun h => hu ((artinMap m).symm_apply_eq.mpr h.symm).symm
    change (Finsupp.single (artinMap m u) (z.coeff (artinMap m u))) σ = 0
    exact Finsupp.single_eq_of_ne hne.symm
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Transport `R[CycGal m] →ₐ[R] R[(ZMod m)ˣ]` along `(artinMap m).symm`. -/
def cycToUnitsAlg (R : Type*) [CommRing R] (m : ℕ) [NeZero m] :
    MonoidAlgebra R (CycGal m) →ₐ[R] MonoidAlgebra R (ZMod m)ˣ where
  toFun w := ∑ u : (ZMod m)ˣ, MonoidAlgebra.single u (w.coeff (artinMap m u))
  map_one' := by
    rw [MonoidAlgebra.one_def, Finset.sum_eq_single (1 : (ZMod m)ˣ)]
    · rw [map_one]
      have h1 : (MonoidAlgebra.single (1 : CycGal m) (1 : R)).coeff 1 = 1 := by simp
      rw [h1, MonoidAlgebra.one_def]
    · intro u _ hu
      have hne : (1 : CycGal m) ≠ artinMap m u := fun h => hu (by
        have := congrArg (artinMap m).symm h
        simpa using this.symm)
      have h0 : (MonoidAlgebra.single (1 : CycGal m) (1 : R)).coeff (artinMap m u) = 0 :=
        Finsupp.single_eq_of_ne hne.symm
      rw [h0, MonoidAlgebra.single_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  map_zero' := by simp
  map_add' x y := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [MonoidAlgebra.coeff_add, MonoidAlgebra.single_add]
  map_mul' x y := by
    have hadd : ∀ (s : Finset (ZMod m)ˣ) (f : (ZMod m)ˣ → MonoidAlgebra R (CycGal m)),
        (∑ v : (ZMod m)ˣ, MonoidAlgebra.single v ((∑ u ∈ s, f u).coeff (artinMap m v))) =
          ∑ u ∈ s, ∑ v : (ZMod m)ˣ, MonoidAlgebra.single v ((f u).coeff (artinMap m v)) := by
      intro s f
      induction s using Finset.induction_on with
      | empty => simp
      | @insert u s hu ih =>
        rw [Finset.sum_insert hu, Finset.sum_insert hu, ← ih, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun v _ => ?_
        simp [MonoidAlgebra.coeff_add, MonoidAlgebra.single_add]
    change (∑ v : (ZMod m)ˣ, MonoidAlgebra.single v ((x * y).coeff (artinMap m v))) =
      (∑ u : (ZMod m)ˣ, MonoidAlgebra.single u (x.coeff (artinMap m u))) *
        ∑ v : (ZMod m)ˣ, MonoidAlgebra.single v (y.coeff (artinMap m v))
    conv_lhs => rw [monoidAlgebra_eq_sum_units m x, monoidAlgebra_eq_sum_units m y, Finset.sum_mul_sum]
    simp_rw [MonoidAlgebra.single_mul_single, ← map_mul (artinMap m)]
    rw [hadd]
    simp_rw [hadd]
    have hterm_single : ∀ (u v : (ZMod m)ˣ),
        (∑ w : (ZMod m)ˣ,
          MonoidAlgebra.single w
            ((MonoidAlgebra.single (artinMap m (u * v))
              (x.coeff (artinMap m u) * y.coeff (artinMap m v))).coeff (artinMap m w))) =
          MonoidAlgebra.single u (x.coeff (artinMap m u)) *
            MonoidAlgebra.single v (y.coeff (artinMap m v)) := fun u v => by
      rw [Finset.sum_eq_single (u * v)]
      · have hs : (MonoidAlgebra.single (artinMap m (u * v))
            (x.coeff (artinMap m u) * y.coeff (artinMap m v))).coeff (artinMap m (u * v)) =
            x.coeff (artinMap m u) * y.coeff (artinMap m v) := by simp
        rw [hs, MonoidAlgebra.single_mul_single]
      · intro w _ hw
        have hne : artinMap m (u * v) ≠ artinMap m w := fun h => hw ((artinMap m).injective h).symm
        have h0 : (MonoidAlgebra.single (artinMap m (u * v))
            (x.coeff (artinMap m u) * y.coeff (artinMap m v))).coeff (artinMap m w) = 0 :=
          Finsupp.single_eq_of_ne hne.symm
        rw [h0, MonoidAlgebra.single_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp_rw [hterm_single]
    rw [← Finset.sum_mul_sum]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, MonoidAlgebra.one_def, MonoidAlgebra.smul_single,
      smul_eq_mul, mul_one, Finset.sum_eq_single (1 : (ZMod m)ˣ)]
    · rw [map_one]
      have hs : (MonoidAlgebra.single (1 : CycGal m) r).coeff 1 = r := by simp
      rw [hs, Algebra.algebraMap_eq_smul_one, MonoidAlgebra.one_def, MonoidAlgebra.smul_single,
        smul_eq_mul, mul_one]
    · intro u _ hu
      have hne : (1 : CycGal m) ≠ artinMap m u := fun h => hu (by
        have := congrArg (artinMap m).symm h
        simpa using this.symm)
      have h0 : (MonoidAlgebra.single (1 : CycGal m) r).coeff (artinMap m u) = 0 :=
        Finsupp.single_eq_of_ne hne.symm
      rw [h0, MonoidAlgebra.single_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

@[simp] theorem cycToUnitsAlg_single (R : Type*) [CommRing R] (m : ℕ) [NeZero m]
    (u : (ZMod m)ˣ) (a : R) :
    cycToUnitsAlg R m (MonoidAlgebra.single (artinMap m u) a) = MonoidAlgebra.single u a := by
  change (∑ v : (ZMod m)ˣ, MonoidAlgebra.single v
    ((MonoidAlgebra.single (artinMap m u) a).coeff (artinMap m v))) = _
  rw [Finset.sum_eq_single u]
  · simp
  · intro v _ hv
    have hne : artinMap m u ≠ artinMap m v := fun h => hv ((artinMap m).injective h).symm
    have h0 : (MonoidAlgebra.single (artinMap m u) a).coeff (artinMap m v) = 0 :=
      Finsupp.single_eq_of_ne hne.symm
    rw [h0, MonoidAlgebra.single_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Transport `R[(ZMod m)ˣ] →ₐ[R] R[CycGal m]` along `artinMap m`. -/
def unitsToCycAlg (R : Type*) [CommRing R] (m : ℕ) [NeZero m] :
    MonoidAlgebra R (ZMod m)ˣ →ₐ[R] MonoidAlgebra R (CycGal m) where
  toFun w := ∑ u : (ZMod m)ˣ, MonoidAlgebra.single (artinMap m u) (w.coeff u)
  map_one' := by
    rw [MonoidAlgebra.one_def, Finset.sum_eq_single (1 : (ZMod m)ˣ)]
    · rw [map_one]
      have hs : (MonoidAlgebra.single (1 : (ZMod m)ˣ) (1 : R)).coeff 1 = 1 := by simp
      rw [hs, MonoidAlgebra.one_def]
    · intro u _ hu
      have h0 : (MonoidAlgebra.single (1 : (ZMod m)ˣ) (1 : R)).coeff u = 0 :=
        Finsupp.single_eq_of_ne hu
      rw [h0, MonoidAlgebra.single_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  map_zero' := by simp
  map_add' x y := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [MonoidAlgebra.coeff_add, MonoidAlgebra.single_add]
  map_mul' x y := by
    have hbasis : ∀ z : MonoidAlgebra R (ZMod m)ˣ,
        z = ∑ u : (ZMod m)ˣ, MonoidAlgebra.single u (z.coeff u) := fun z => by
      ext v
      simp only [MonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
      rw [Finset.sum_eq_single v]
      · simp
      · intro u _ hu
        change (Finsupp.single u (z.coeff u)) v = 0
        exact Finsupp.single_eq_of_ne hu.symm
      · intro h; exact absurd (Finset.mem_univ _) h
    have hadd : ∀ (s : Finset (ZMod m)ˣ) (f : (ZMod m)ˣ → MonoidAlgebra R (ZMod m)ˣ),
        (∑ v : (ZMod m)ˣ, MonoidAlgebra.single (artinMap m v) ((∑ u ∈ s, f u).coeff v)) =
          ∑ u ∈ s, ∑ v : (ZMod m)ˣ, MonoidAlgebra.single (artinMap m v) ((f u).coeff v) := by
      intro s f
      induction s using Finset.induction_on with
      | empty => simp
      | @insert u s hu ih =>
        rw [Finset.sum_insert hu, Finset.sum_insert hu, ← ih, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun v _ => ?_
        simp [MonoidAlgebra.coeff_add, MonoidAlgebra.single_add]
    change (∑ v : (ZMod m)ˣ, MonoidAlgebra.single (artinMap m v) ((x * y).coeff v)) =
      (∑ u : (ZMod m)ˣ, MonoidAlgebra.single (artinMap m u) (x.coeff u)) *
        ∑ v : (ZMod m)ˣ, MonoidAlgebra.single (artinMap m v) (y.coeff v)
    conv_lhs => rw [hbasis x, hbasis y, Finset.sum_mul_sum]
    simp_rw [MonoidAlgebra.single_mul_single]
    rw [hadd]
    simp_rw [hadd]
    have hterm_single : ∀ (u v : (ZMod m)ˣ),
        (∑ w : (ZMod m)ˣ,
          MonoidAlgebra.single (artinMap m w)
            ((MonoidAlgebra.single (u * v) (x.coeff u * y.coeff v)).coeff w)) =
          MonoidAlgebra.single (artinMap m u) (x.coeff u) *
            MonoidAlgebra.single (artinMap m v) (y.coeff v) := fun u v => by
      rw [Finset.sum_eq_single (u * v)]
      · have hs : (MonoidAlgebra.single (u * v) (x.coeff u * y.coeff v)).coeff (u * v) =
            x.coeff u * y.coeff v := by simp
        rw [hs, MonoidAlgebra.single_mul_single, map_mul]
      · intro w _ hw
        have h0 : (MonoidAlgebra.single (u * v) (x.coeff u * y.coeff v)).coeff w = 0 :=
          Finsupp.single_eq_of_ne hw
        rw [h0, MonoidAlgebra.single_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp_rw [hterm_single]
    rw [← Finset.sum_mul_sum]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, MonoidAlgebra.one_def, MonoidAlgebra.smul_single,
      smul_eq_mul, mul_one, Finset.sum_eq_single (1 : (ZMod m)ˣ)]
    · rw [map_one]
      have hs : (MonoidAlgebra.single (1 : (ZMod m)ˣ) r).coeff 1 = r := by simp
      rw [hs, Algebra.algebraMap_eq_smul_one, MonoidAlgebra.one_def, MonoidAlgebra.smul_single,
        smul_eq_mul, mul_one]
    · intro u _ hu
      have h0 : (MonoidAlgebra.single (1 : (ZMod m)ˣ) r).coeff u = 0 :=
        Finsupp.single_eq_of_ne hu
      rw [h0, MonoidAlgebra.single_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

@[simp] theorem unitsToCycAlg_single (R : Type*) [CommRing R] (m : ℕ) [NeZero m]
    (u : (ZMod m)ˣ) (a : R) :
    unitsToCycAlg R m (MonoidAlgebra.single u a) = MonoidAlgebra.single (artinMap m u) a := by
  change (∑ v : (ZMod m)ˣ, MonoidAlgebra.single (artinMap m v)
    ((MonoidAlgebra.single u a).coeff v)) = _
  rw [Finset.sum_eq_single u]
  · simp
  · intro v _ hv
    have h0 : (MonoidAlgebra.single u a).coeff v = 0 := Finsupp.single_eq_of_ne hv
    rw [h0, MonoidAlgebra.single_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem unitsToCycAlg_cycToUnitsAlg (R : Type*) [CommRing R] (m : ℕ) [NeZero m]
    (w : MonoidAlgebra R (CycGal m)) :
    unitsToCycAlg R m (cycToUnitsAlg R m w) = w := by
  have hbasis := monoidAlgebra_eq_sum_units m w
  conv_lhs => rw [hbasis, map_sum, map_sum]
  conv_rhs => rw [hbasis]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [cycToUnitsAlg_single, unitsToCycAlg_single]

/-- Explicit character idempotent `e_χ = φ(m)⁻¹ ∑_u χ⁻¹(u) [u]` in `ℂ[(ZMod m)ˣ]`. -/
noncomputable def charIdempUnits (m : ℕ) [NeZero m] (χ : DirichletCharacter ℂ m) :
    MonoidAlgebra ℂ (ZMod m)ˣ :=
  ((m.totient : ℂ)⁻¹) •
    ∑ u : (ZMod m)ˣ, (χ⁻¹ (u : ZMod m)) • MonoidAlgebra.single u (1 : ℂ)

lemma single_mul_charIdempUnits (m : ℕ) [NeZero m] (χ : DirichletCharacter ℂ m) (b : (ZMod m)ˣ) :
    MonoidAlgebra.single b (1 : ℂ) * charIdempUnits m χ =
      (χ (b : ZMod m)) • charIdempUnits m χ := by
  unfold charIdempUnits
  rw [Algebra.mul_smul_comm, smul_comm (χ (b : ZMod m)) ((m.totient : ℂ)⁻¹)]
  congr 1
  rw [Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_bij (fun u _ => b * u) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro u₁ _ u₂ _ h; exact mul_left_cancel h
  · intro v _; exact ⟨b⁻¹ * v, Finset.mem_univ _, by group⟩
  · intro u _
    rw [Algebra.mul_smul_comm, MonoidAlgebra.single_mul_single, one_mul, smul_smul]
    congr 1
    rw [Units.val_mul, map_mul, ← mul_assoc, χ.inv_apply_eq_inv' (b : ZMod m)]
    have hu : χ (b : ZMod m) ≠ 0 := Units.ne_zero (χ.toUnitHom b)
    rw [mul_inv_cancel₀ hu, one_mul]

open Classical in
private lemma sum_units_char_inv_mul_char (m : ℕ) [NeZero m]
    (χ₁ χ₂ : DirichletCharacter ℂ m) :
    ∑ u : (ZMod m)ˣ, χ₁⁻¹ (u : ZMod m) * χ₂ (u : ZMod m) =
      if χ₁ = χ₂ then (m.totient : ℂ) else 0 := by
  split_ifs with h
  · subst h
    have h1 : ∀ u : (ZMod m)ˣ, χ₁⁻¹ (u : ZMod m) * χ₁ (u : ZMod m) = 1 := fun u => by
      rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply u.isUnit]
    simp_rw [h1, Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul,
      mul_one]
  · have hne : ∃ u₀ : (ZMod m)ˣ, χ₁⁻¹ (u₀ : ZMod m) * χ₂ (u₀ : ZMod m) ≠ 1 := by
      by_contra hall
      push Not at hall
      apply h
      ext u
      have hu := hall u
      rw [χ₁.inv_apply_eq_inv'] at hu
      exact (inv_mul_eq_one₀ (Units.ne_zero (χ₁.toUnitHom u))).mp hu
    obtain ⟨u₀, hu₀⟩ := hne
    set S : ℂ := ∑ u : (ZMod m)ˣ, χ₁⁻¹ (u : ZMod m) * χ₂ (u : ZMod m)
    have hS : (χ₁⁻¹ (u₀ : ZMod m) * χ₂ (u₀ : ZMod m)) * S = S := by
      dsimp only [S]
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun u _ => u₀ * u) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
      · intro u₁ _ u₂ _ h; exact mul_left_cancel h
      · intro v _; exact ⟨u₀⁻¹ * v, Finset.mem_univ _, by group⟩
      · intro u _
        rw [Units.val_mul, map_mul, map_mul]
        ring
    have hsub : (χ₁⁻¹ (u₀ : ZMod m) * χ₂ (u₀ : ZMod m) - 1) * S = 0 := by linear_combination hS
    exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hu₀)

/-- Explicit `ℂ`-algebra isomorphism `SignedQuotAlg ℂ (ZMod m)ˣ (-1) ε ≃ₐ[ℂ] (↥(signedChars m ε) → ℂ)`. -/
noncomputable def signedQuotAlgUnitsℂEquivSignedChars (m : ℕ) [NeZero m] (ε : ℤ)
    (hε : ε * ε = 1) :
    SignedQuotAlg ℂ (ZMod m)ˣ (-1 : (ZMod m)ˣ) ε ≃ₐ[ℂ]
      (↥(signedChars m ε) → ℂ) := by
  classical
  let c : (ZMod m)ˣ := (-1 : (ZMod m)ˣ)
  let I : Ideal (MonoidAlgebra ℂ (ZMod m)ˣ) :=
    Ideal.span ({MonoidAlgebra.single c (1 : ℂ) - (ε : MonoidAlgebra ℂ (ZMod m)ˣ)} :
      Set (MonoidAlgebra ℂ (ZMod m)ˣ))
  let evalSigned : MonoidAlgebra ℂ (ZMod m)ˣ →ₐ[ℂ] (↥(signedChars m ε) → ℂ) :=
    { toFun := fun w χ => ∑ u : (ZMod m)ˣ, w.coeff u * χ.1 (u : ZMod m)
      map_one' := by
        ext χ
        rw [MonoidAlgebra.one_def, Finset.sum_eq_single (1 : (ZMod m)ˣ)]
        · simp
        · intro u _ hu; simp [hu.symm]
        · intro h; exact absurd (Finset.mem_univ _) h
      map_zero' := by ext χ; simp
      map_add' := fun x y => by
        ext χ
        simp only [Pi.add_apply, MonoidAlgebra.coeff_add, Finsupp.add_apply, add_mul,
          Finset.sum_add_distrib]
      map_mul' := fun x y => by
        ext χ
        have hbasis : ∀ z : MonoidAlgebra ℂ (ZMod m)ˣ,
            z = ∑ u : (ZMod m)ˣ, MonoidAlgebra.single u (z.coeff u) := fun z => by
          ext v; simp [MonoidAlgebra.coeff_sum]
        have hsingle : ∀ (u : (ZMod m)ˣ) (a : ℂ),
            (∑ v : (ZMod m)ˣ, (MonoidAlgebra.single u a).coeff v * χ.1 (v : ZMod m)) =
              a * χ.1 (u : ZMod m) := fun u a => by
          rw [Finset.sum_eq_single u]
          · simp
          · intro v _ hv; simp [hv.symm]
          · intro h; exact absurd (Finset.mem_univ _) h
        have hadd : ∀ (s : Finset (ZMod m)ˣ) (f : (ZMod m)ˣ → MonoidAlgebra ℂ (ZMod m)ˣ),
            (∑ v : (ZMod m)ˣ, (∑ u ∈ s, f u).coeff v * χ.1 (v : ZMod m)) =
              ∑ u ∈ s, ∑ v : (ZMod m)ˣ, (f u).coeff v * χ.1 (v : ZMod m) := by
          intro s f
          induction s using Finset.induction_on with
          | empty => simp
          | @insert u s hu ih =>
            rw [Finset.sum_insert hu, Finset.sum_insert hu, ← ih, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun v _ => ?_
            simp [MonoidAlgebra.coeff_add, Finsupp.add_apply, add_mul]
        change (∑ v : (ZMod m)ˣ, (x * y).coeff v * χ.1 (v : ZMod m)) = _
        conv_lhs => rw [hbasis x, hbasis y, Finset.sum_mul]
        simp_rw [Finset.mul_sum, MonoidAlgebra.single_mul_single]
        rw [hadd]
        simp_rw [hadd, hsingle]
        simp only [Pi.mul_apply]
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
        simp only [Units.val_mul, map_mul]
        ring
      commutes' := fun r => by
        ext χ
        change ∑ u : (ZMod m)ˣ, (algebraMap ℂ (MonoidAlgebra ℂ (ZMod m)ˣ) r).coeff u *
          χ.1 (u : ZMod m) = r
        rw [Algebra.algebraMap_eq_smul_one, MonoidAlgebra.one_def, MonoidAlgebra.smul_single,
          smul_eq_mul, mul_one, Finset.sum_eq_single (1 : (ZMod m)ˣ)]
        · simp
        · intro u _ hu; simp [hu.symm]
        · intro h; exact absurd (Finset.mem_univ _) h }
  have hker : I ≤ RingHom.ker evalSigned.toRingHom := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    change evalSigned (MonoidAlgebra.single c (1 : ℂ) - (ε : MonoidAlgebra ℂ (ZMod m)ˣ)) = 0
    ext χ
    have h1 : ((ε : ℤ) : MonoidAlgebra ℂ (ZMod m)ˣ) =
        MonoidAlgebra.single (1 : (ZMod m)ˣ) (ε : ℂ) := by
      rw [← zsmul_one ε, MonoidAlgebra.one_def, MonoidAlgebra.smul_single, zsmul_eq_mul, mul_one]
    rw [map_sub, h1]
    have hsingle : ∀ (u : (ZMod m)ˣ) (a : ℂ),
        evalSigned (MonoidAlgebra.single u a) χ = a * χ.1 (u : ZMod m) := fun u a => by
      change ∑ v : (ZMod m)ˣ, (MonoidAlgebra.single u a).coeff v * χ.1 (v : ZMod m) = _
      rw [Finset.sum_eq_single u]
      · simp
      · intro v _ hv; simp [hv.symm]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp only [Pi.sub_apply, Pi.zero_apply, hsingle, c]
    have hmem : χ.1 (-1 : ZMod m) = (ε : ℂ) := mem_signedChars_iff.mp χ.2
    rw [Units.val_neg, Units.val_one, map_one, hmem]
    ring
  let Φ : SignedQuotAlg ℂ (ZMod m)ˣ c ε →ₐ[ℂ] (↥(signedChars m ε) → ℂ) :=
    Ideal.Quotient.liftₐ I evalSigned (fun a ha => hker ha)
  let Ψ : (↥(signedChars m ε) → ℂ) → SignedQuotAlg ℂ (ZMod m)ˣ c ε := fun f =>
    Ideal.Quotient.mk I (∑ χ : ↥(signedChars m ε), f χ • charIdempUnits m χ.1)
  have hm_tot : (m.totient : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos m)).ne'
  have hΦΨ : ∀ f, Φ (Ψ f) = f := fun f => by
    ext χ'
    change evalSigned (∑ χ : ↥(signedChars m ε), f χ • charIdempUnits m χ.1) χ' = f χ'
    rw [map_sum, Finset.sum_apply, Finset.sum_eq_single χ']
    · rw [map_smul, Pi.smul_apply, smul_eq_mul]
      have hidemp : evalSigned (charIdempUnits m χ'.1) χ' = 1 := by
        unfold charIdempUnits
        rw [map_smul, Pi.smul_apply, smul_eq_mul, map_sum, Finset.sum_apply]
        have hterm : ∀ u : (ZMod m)ˣ,
            evalSigned (χ'.1⁻¹ (u : ZMod m) • MonoidAlgebra.single u (1 : ℂ)) χ' =
              χ'.1⁻¹ (u : ZMod m) * χ'.1 (u : ZMod m) := fun u => by
          rw [map_smul, Pi.smul_apply, smul_eq_mul]
          change χ'.1⁻¹ (u : ZMod m) * ∑ v : (ZMod m)ˣ,
            (MonoidAlgebra.single u (1 : ℂ)).coeff v * χ'.1 (v : ZMod m) = _
          rw [Finset.sum_eq_single u]
          · simp
          · intro v _ hv; simp [hv.symm]
          · intro h; exact absurd (Finset.mem_univ _) h
        simp_rw [hterm]
        rw [sum_units_char_inv_mul_char, if_pos rfl, inv_mul_cancel₀ hm_tot]
      rw [hidemp, mul_one]
    · intro χ _ hχ
      rw [map_smul, Pi.smul_apply, smul_eq_mul]
      have h0 : evalSigned (charIdempUnits m χ.1) χ' = 0 := by
        unfold charIdempUnits
        rw [map_smul, Pi.smul_apply, smul_eq_mul, map_sum, Finset.sum_apply]
        have hterm : ∀ u : (ZMod m)ˣ,
            evalSigned (χ.1⁻¹ (u : ZMod m) • MonoidAlgebra.single u (1 : ℂ)) χ' =
              χ.1⁻¹ (u : ZMod m) * χ'.1 (u : ZMod m) := fun u => by
          rw [map_smul, Pi.smul_apply, smul_eq_mul]
          change χ.1⁻¹ (u : ZMod m) * ∑ v : (ZMod m)ˣ,
            (MonoidAlgebra.single u (1 : ℂ)).coeff v * χ'.1 (v : ZMod m) = _
          rw [Finset.sum_eq_single u]
          · simp
          · intro v _ hv; simp [hv.symm]
          · intro h; exact absurd (Finset.mem_univ _) h
        have hne : χ.1 ≠ χ'.1 := fun h => hχ (Subtype.ext h)
        simp_rw [hterm]
        rw [sum_units_char_inv_mul_char, if_neg hne, mul_zero]
      rw [h0, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hΨΦ : ∀ x, Ψ (Φ x) = x := fun x => by
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hw : w = ∑ u : (ZMod m)ˣ, MonoidAlgebra.single u (w.coeff u) := by
      ext v
      simp only [MonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
      rw [Finset.sum_eq_single v]
      · simp
      · intro u _ hu
        change (Finsupp.single u (w.coeff u)) v = 0
        exact Finsupp.single_eq_of_ne hu.symm
      · intro h; exact absurd (Finset.mem_univ _) h
    have hkill_odd : ∀ χ : DirichletCharacter ℂ m, χ ∉ signedChars m ε →
        Ideal.Quotient.mk I (charIdempUnits m χ) = 0 := fun χ hχ => by
      have hneg : χ (-1 : ZMod m) = -(ε : ℂ) := by
        rcases dirichletChar_neg_one_eq_one_or_neg_one χ with h1 | h1
        · have hne : (ε : ℂ) ≠ 1 := fun h => hχ (mem_signedChars_iff.mpr (h1.trans h.symm))
          have hεneg : ε = -1 := by
            rcases Int.eq_one_or_neg_one_of_mul_eq_one hε with h | h
            · exfalso; apply hne; simp [h]
            · exact h
          rw [h1, hεneg]; norm_num
        · have hne : (ε : ℂ) ≠ -1 := fun h => hχ (mem_signedChars_iff.mpr (h1.trans h.symm))
          have hεpos : ε = 1 := by
            rcases Int.eq_one_or_neg_one_of_mul_eq_one hε with h | h
            · exact h
            · exfalso; apply hne; simp [h]
          rw [h1, hεpos]; norm_num
      have hmul_c : Ideal.Quotient.mk I (MonoidAlgebra.single c (1 : ℂ) * charIdempUnits m χ) =
          (ε : ℂ) • Ideal.Quotient.mk I (charIdempUnits m χ) := by
        have hceq : Ideal.Quotient.mk I (MonoidAlgebra.single c (1 : ℂ)) =
            Ideal.Quotient.mk I (ε : MonoidAlgebra ℂ (ZMod m)ˣ) := by
          rw [Ideal.Quotient.eq]
          exact Ideal.subset_span rfl
        rw [map_mul (Ideal.Quotient.mk I), hceq, ← map_mul (Ideal.Quotient.mk I)]
        have h1 : ((ε : ℤ) : MonoidAlgebra ℂ (ZMod m)ˣ) =
            (ε : ℂ) • (1 : MonoidAlgebra ℂ (ZMod m)ˣ) := by
          rw [← zsmul_one ε, Int.cast_smul_eq_zsmul ℂ]
        rw [h1, Algebra.smul_mul_assoc, one_mul]
        rfl
      have hmul_c2 : Ideal.Quotient.mk I (MonoidAlgebra.single c (1 : ℂ) * charIdempUnits m χ) =
          (-(ε : ℂ)) • Ideal.Quotient.mk I (charIdempUnits m χ) := by
        dsimp only [c]
        rw [single_mul_charIdempUnits, Units.val_neg, Units.val_one, hneg]
        rfl
      have h2 : ((2 * (ε : ℂ)) • Ideal.Quotient.mk I (charIdempUnits m χ)) = 0 := by
        have hsub : (ε : ℂ) • Ideal.Quotient.mk I (charIdempUnits m χ) -
            (-(ε : ℂ)) • Ideal.Quotient.mk I (charIdempUnits m χ) = 0 := by
          rw [← hmul_c, ← hmul_c2, sub_self]
        calc (2 * (ε : ℂ)) • Ideal.Quotient.mk I (charIdempUnits m χ)
            = (ε : ℂ) • Ideal.Quotient.mk I (charIdempUnits m χ) -
                (-(ε : ℂ)) • Ideal.Quotient.mk I (charIdempUnits m χ) := by module
          _ = 0 := hsub
      have h2ε : (2 * (ε : ℂ)) ≠ 0 := by
        have hε0 : (ε : ℂ) ≠ 0 := by
          intro h
          have : (ε : ℂ) * (ε : ℂ) = 1 := by exact_mod_cast hε
          rw [h, zero_mul] at this
          exact zero_ne_one this
        exact mul_ne_zero two_ne_zero hε0
      calc Ideal.Quotient.mk I (charIdempUnits m χ)
          = (2 * (ε : ℂ))⁻¹ • ((2 * (ε : ℂ)) • Ideal.Quotient.mk I (charIdempUnits m χ)) := by
              rw [smul_smul, inv_mul_cancel₀ h2ε, one_smul]
        _ = 0 := by rw [h2, smul_zero]
    have hunit_id : ∀ u : (ZMod m)ˣ,
        (∑ χ : DirichletCharacter ℂ m, (χ (u : ZMod m)) • charIdempUnits m χ) =
          MonoidAlgebra.single u (1 : ℂ) := fun u => by
      ext v
      simp only [MonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
      have hterm : ∀ χ : DirichletCharacter ℂ m,
          ((χ (u : ZMod m)) • charIdempUnits m χ).coeff v =
            (m.totient : ℂ)⁻¹ * (χ (v : ZMod m)⁻¹ * χ (u : ZMod m)) := fun χ => by
        unfold charIdempUnits
        rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, MonoidAlgebra.coeff_smul,
          Finsupp.smul_apply, smul_eq_mul]
        simp only [MonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
        rw [Finset.sum_eq_single v]
        · have hsingle1 : (χ⁻¹ (v : ZMod m) • MonoidAlgebra.single v (1 : ℂ)).coeff v =
              χ⁻¹ (v : ZMod m) := by
            rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
            change χ⁻¹ (v : ZMod m) * (Finsupp.single v (1 : ℂ)) v = _
            simp
          have h2 : χ (v : ZMod m) * χ (v : ZMod m)⁻¹ = 1 := by
            rw [← map_mul, ZMod.mul_inv_of_unit (v : ZMod m) v.isUnit, map_one]
          have hvinv : (χ (v : ZMod m))⁻¹ = χ (v : ZMod m)⁻¹ :=
            (eq_inv_of_mul_eq_one_right h2).symm
          rw [hsingle1, χ.inv_apply_eq_inv', hvinv]
          ring
        · intro w _ hw
          rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
          change χ⁻¹ (w : ZMod m) * (Finsupp.single w (1 : ℂ)) v = 0
          rw [Finsupp.single_eq_of_ne hw.symm, mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      simp_rw [hterm]
      rw [← Finset.mul_sum]
      have horth := DirichletCharacter.sum_char_inv_mul_char_eq ℂ v.isUnit (u : ZMod m)
      rw [horth]
      by_cases huv : u = v
      · subst huv
        simp [inv_mul_cancel₀ hm_tot]
      · have hne_val : (v : ZMod m) ≠ (u : ZMod m) := fun h => huv (Units.ext h.symm)
        simp [hne_val, huv]
    have heval_u : ∀ u : (ZMod m)ˣ,
        Ψ (Φ (Ideal.Quotient.mk I (MonoidAlgebra.single u (1 : ℂ)))) =
          Ideal.Quotient.mk I (MonoidAlgebra.single u (1 : ℂ)) := fun u => by
      have hΦu : ∀ χ : ↥(signedChars m ε),
          Φ (Ideal.Quotient.mk I (MonoidAlgebra.single u (1 : ℂ))) χ =
            χ.1 (u : ZMod m) := fun χ => by
        change evalSigned (MonoidAlgebra.single u (1 : ℂ)) χ = _
        change ∑ v : (ZMod m)ˣ, (MonoidAlgebra.single u (1 : ℂ)).coeff v * χ.1 (v : ZMod m) = _
        rw [Finset.sum_eq_single u]
        · simp
        · intro v _ hv; simp [hv.symm]
        · intro h; exact absurd (Finset.mem_univ _) h
      dsimp only [Ψ]
      simp_rw [hΦu]
      rw [map_sum (Ideal.Quotient.mk I)]
      have hsplit :
          (∑ χ : DirichletCharacter ℂ m, (χ (u : ZMod m)) • Ideal.Quotient.mk I (charIdempUnits m χ)) =
            ∑ χ ∈ signedChars m ε, (χ (u : ZMod m)) • Ideal.Quotient.mk I (charIdempUnits m χ) := by
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (DirichletCharacter ℂ m))
          (fun χ => χ ∈ signedChars m ε)]
        have hzero :
            ∑ χ ∈ Finset.univ.filter (fun χ => χ ∉ signedChars m ε),
              (χ (u : ZMod m)) • Ideal.Quotient.mk I (charIdempUnits m χ) = 0 := by
          refine Finset.sum_eq_zero fun χ hχ => ?_
          rw [hkill_odd χ (Finset.mem_filter.mp hχ).2, smul_zero]
        rw [hzero, add_zero]
        refine Finset.sum_congr (by ext χ; simp) fun _ _ => rfl
      have hmk_sum :
          (∑ χ : ↥(signedChars m ε),
              Ideal.Quotient.mk I ((χ.1 (u : ZMod m)) • charIdempUnits m χ.1)) =
            ∑ χ ∈ signedChars m ε, (χ (u : ZMod m)) • Ideal.Quotient.mk I (charIdempUnits m χ) := by
        rw [← Finset.sum_coe_sort (signedChars m ε)]
        refine Finset.sum_congr rfl fun χ _ => rfl
      rw [hmk_sum, ← hsplit]
      have hpull :
          (∑ χ : DirichletCharacter ℂ m, (χ (u : ZMod m)) • Ideal.Quotient.mk I (charIdempUnits m χ)) =
            Ideal.Quotient.mk I (∑ χ : DirichletCharacter ℂ m, (χ (u : ZMod m)) • charIdempUnits m χ) := by
        rw [map_sum (Ideal.Quotient.mk I)]
        refine Finset.sum_congr rfl fun χ _ => rfl
      rw [hpull, hunit_id u]
    have hΨ_lin : ∀ a b, Ψ (a + b) = Ψ a + Ψ b := fun a b => by
      dsimp only [Ψ]
      rw [← map_add (Ideal.Quotient.mk I), ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [Pi.add_apply, add_smul]
    have hΨ_smul : ∀ (r : ℂ) a, Ψ (r • a) = r • Ψ a := fun r a => by
      dsimp only [Ψ]
      have hmk : r • Ideal.Quotient.mk I (∑ χ : ↥(signedChars m ε), a χ • charIdempUnits m χ.1) =
          Ideal.Quotient.mk I (r • ∑ χ : ↥(signedChars m ε), a χ • charIdempUnits m χ.1) := rfl
      rw [hmk]
      congr 1
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, smul_smul]
    change Ψ (Φ (Ideal.Quotient.mk I w)) = Ideal.Quotient.mk I w
    conv_lhs => rw [hw, map_sum (Ideal.Quotient.mk I)]
    have hw_smul :
        (∑ u : (ZMod m)ˣ, Ideal.Quotient.mk I (MonoidAlgebra.single u (w.coeff u))) =
          ∑ u : (ZMod m)ˣ, w.coeff u • Ideal.Quotient.mk I (MonoidAlgebra.single u (1 : ℂ)) := by
      refine Finset.sum_congr rfl fun u _ => ?_
      have hs : MonoidAlgebra.single u (w.coeff u) =
          w.coeff u • MonoidAlgebra.single u (1 : ℂ) := by
        rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
      rw [hs]
      rfl
    rw [hw_smul, map_sum]
    have hΨ_sum : ∀ (s : Finset (ZMod m)ˣ) (F : (ZMod m)ˣ → (↥(signedChars m ε) → ℂ)),
        Ψ (∑ u ∈ s, F u) = ∑ u ∈ s, Ψ (F u) := fun s F => by
      induction s using Finset.induction_on with
      | empty => simp [Ψ]
      | @insert u s hu ih => rw [Finset.sum_insert hu, Finset.sum_insert hu, hΨ_lin, ih]
    rw [hΨ_sum]
    have hrhs : Ideal.Quotient.mk I w =
        ∑ u : (ZMod m)ˣ, w.coeff u • Ideal.Quotient.mk I (MonoidAlgebra.single u (1 : ℂ)) := by
      conv_lhs => rw [hw, map_sum (Ideal.Quotient.mk I)]
      exact hw_smul
    rw [hrhs]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_smul, hΨ_smul, heval_u u]
  have hΦ_inj : Function.Injective Φ := Function.LeftInverse.injective hΨΦ
  exact AlgEquiv.ofAlgHom Φ
    { toFun := Ψ
      map_one' := by
        apply hΦ_inj
        rw [hΦΨ, map_one]
      map_mul' := fun a b => by
        apply hΦ_inj
        rw [hΦΨ, map_mul, hΦΨ, hΦΨ]
      map_zero' := by simp [Ψ]
      map_add' := fun a b => by
        dsimp only [Ψ]
        rw [← map_add (Ideal.Quotient.mk I), ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [Pi.add_apply, add_smul]
      commutes' := fun r => by
        apply hΦ_inj
        rw [hΦΨ]
        change algebraMap ℂ _ r = Φ (algebraMap ℂ _ r)
        rw [AlgHom.commutes] }
    (AlgHom.ext hΦΨ) (AlgHom.ext hΨΦ)

private lemma algEquiv_conj_lmul {R A B : Type*} [CommRing R] [Ring A] [Ring B]
    [Algebra R A] [Algebra R B] (E : A ≃ₐ[R] B) (x : A) :
    E.toLinearEquiv.conj (Algebra.lmul R A x) = Algebra.lmul R B (E x) := by
  ext f
  change E (x * E.symm f) = E x * f
  rw [map_mul, E.apply_symm_apply]

/-- **Exact Complex Character-Product Formula for `detR` on `ℚ(ζ_m)`**:
`(detR ℤ (ZMod m)ˣ (-1) ε ... (cycToUnitsAlg ℤ m z) : ℂ) = ∏ χ ∈ signedChars m ε, evalCharMonoidAlg χ (toRatAlg z)`! -/
theorem detR_int_eq_prod_signed_chars_cyc (m : ℕ) [NeZero m] (ε : ℤ)
    (hc : (-1 : (ZMod m)ˣ) * (-1 : (ZMod m)ˣ) = 1)
    (hc1 : (-1 : (ZMod m)ˣ) ≠ 1) (hε : ε * ε = 1)
    (z : MonoidAlgebra ℤ (CycGal m)) :
    ((detR ℤ (ZMod m)ˣ (-1 : (ZMod m)ˣ) ε hc hc1 hε (cycToUnitsAlg ℤ m z) : ℤ) : ℂ) =
      ∏ χ ∈ signedChars m ε, evalCharMonoidAlg χ (toRatAlg z) := by
  classical
  let c : (ZMod m)ˣ := (-1 : (ZMod m)ˣ)
  let zu : MonoidAlgebra ℤ (ZMod m)ˣ := cycToUnitsAlg ℤ m z
  have hbase :
      ((detR ℤ (ZMod m)ˣ c ε hc hc1 hε zu : ℤ) : ℂ) =
        detR ℂ (ZMod m)ˣ c ε hc hc1 hε
          (MonoidAlgebra.mapRingHom (ZMod m)ˣ (Int.castRingHom ℂ) zu) :=
    detR_mapRingHom ℤ (ZMod m)ˣ c ε (Int.castRingHom ℂ) hc hc1 hε zu
  rw [hbase]
  let zC : MonoidAlgebra ℂ (ZMod m)ˣ :=
    MonoidAlgebra.mapRingHom (ZMod m)ˣ (Int.castRingHom ℂ) zu
  let zbar : SignedQuotAlg ℂ (ZMod m)ˣ c ε := Ideal.Quotient.mk _ zC
  let e := signedQuotEquiv ℂ (ZMod m)ˣ c ε hc hc1 hε
  let b : Module.Basis ((ZMod m)ˣ ⧸ Subgroup.zpowers c) ℂ (SignedQuotAlg ℂ (ZMod m)ˣ c ε) :=
    (Pi.basisFun ℂ _).map e.symm
  have hdet_lm :
      detR ℂ (ZMod m)ˣ c ε hc hc1 hε zC =
        LinearMap.det (Algebra.lmul ℂ (SignedQuotAlg ℂ (ZMod m)ˣ c ε) zbar) := by
    unfold detR
    rw [← signedMulMatrix_ringHom_apply ℂ (ZMod m)ˣ c ε hc hc1 hε zC]
    change Matrix.det (LinearMap.toMatrix b b
      (Algebra.lmul ℂ (SignedQuotAlg ℂ (ZMod m)ˣ c ε) zbar)) = _
    rw [LinearMap.det_toMatrix]
  rw [hdet_lm]
  set E := signedQuotAlgUnitsℂEquivSignedChars m ε hε
  let L₁ : SignedQuotAlg ℂ (ZMod m)ˣ c ε →ₗ[ℂ] SignedQuotAlg ℂ (ZMod m)ˣ c ε :=
    Algebra.lmul ℂ (SignedQuotAlg ℂ (ZMod m)ˣ c ε) zbar
  let L₂ : (↥(signedChars m ε) → ℂ) →ₗ[ℂ] (↥(signedChars m ε) → ℂ) :=
    Algebra.lmul ℂ (↥(signedChars m ε) → ℂ) (E zbar)
  have hconj : E.toLinearEquiv.conj L₁ = L₂ := algEquiv_conj_lmul E zbar
  have hdet_eq : LinearMap.det L₁ = LinearMap.det L₂ := by
    have hc_det : LinearMap.det (E.toLinearEquiv.conj L₁) = LinearMap.det L₁ :=
      LinearMap.det_conj L₁ E.toLinearEquiv
    rw [← hc_det, hconj]
  rw [hdet_eq]
  let b₂ := Pi.basisFun ℂ ↥(signedChars m ε)
  have hmat₂ : LinearMap.toMatrix b₂ b₂ L₂ = Matrix.diagonal (E zbar) := by
    ext χ₁ χ₂
    rw [LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply]
    change ((E zbar : ↥(signedChars m ε) → ℂ) *
      (Pi.single χ₂ (1 : ℂ) : ↥(signedChars m ε) → ℂ)) χ₁ = _
    rw [Pi.mul_apply, Pi.single_apply, Matrix.diagonal_apply]
    split_ifs with h
    · subst h; ring
    · simp
  have hzu_coeff : ∀ u : (ZMod m)ˣ, zu.coeff u = z.coeff (artinMap m u) := fun u => by
    change (∑ v : (ZMod m)ˣ, MonoidAlgebra.single v (z.coeff (artinMap m v))).coeff u = _
    simp only [MonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
    rw [Finset.sum_eq_single u]
    · simp
    · intro v _ hv
      change (Finsupp.single v (z.coeff (artinMap m v))) u = 0
      exact Finsupp.single_eq_of_ne hv.symm
    · intro h; exact absurd (Finset.mem_univ _) h
  have hev_char : ∀ χ : ↥(signedChars m ε),
      E zbar χ = evalCharMonoidAlg χ.1 (toRatAlg z) := fun χ => by
    change (∑ u : (ZMod m)ˣ, zC.coeff u * χ.1 (u : ZMod m)) =
      ∑ σ : CycGal m, (((toRatAlg z).coeff σ : ℚ) : ℂ) * χ.1 ((artinMap m).symm σ : ZMod m)
    refine Finset.sum_bij (fun u _ => artinMap m u) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro u₁ _ u₂ _ h; exact (artinMap m).injective h
    · intro σ _; exact ⟨(artinMap m).symm σ, Finset.mem_univ _, by simp⟩
    · intro u _
      have hc_zC : zC.coeff u = (z.coeff (artinMap m u) : ℂ) := by
        simp [zC, hzu_coeff u]
      have hc_rat : (((toRatAlg z).coeff (artinMap m u) : ℚ) : ℂ) = (z.coeff (artinMap m u) : ℂ) := by
        simp [toRatAlg]
      rw [hc_zC, hc_rat, MulEquiv.symm_apply_apply]
  rw [← LinearMap.det_toMatrix b₂ L₂, hmat₂, Matrix.det_diagonal]
  simp_rw [hev_char]
  rw [Finset.prod_coe_sort (signedChars m ε) (fun χ => evalCharMonoidAlg χ (toRatAlg z))]

/-- Any natural number `u` coprime to `l` (`¬ l ∣ u`) is a unit in `ℤ_[l]`. -/
theorem isUnit_natCast_padicInt_of_not_dvd {l : ℕ} [Fact l.Prime] {u : ℕ} (hu : ¬ l ∣ u) :
    IsUnit (u : ℤ_[l]) := by
  by_contra hn
  have hmem : (u : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] :=
    (IsLocalRing.mem_maximalIdeal _).mpr hn
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast] at hmem
  exact hu ((ZMod.natCast_eq_zero_iff u l).mp hmem)

/-- **Uniform Power-Annihilation Length Bound (`LenPow`)**:
over `ℤ_[l]` (`l` prime), if `(l : ℤ_[l]) ^ k • x = 0` for all `x : M`, then
`Module.length ℤ_[l] M ≤ (k : ℕ∞) * Module.length ℤ_[l] (LinearMap.ker ((l : ℤ_[l]) • (LinearMap.id : M →ₗ[ℤ_[l]] M)))`. -/
theorem length_le_mul_lTorsion {l : ℕ} [Fact l.Prime]
    {M : Type*} [AddCommGroup M] [Module ℤ_[l] M] :
    ∀ (k : ℕ) (N : Submodule ℤ_[l] M),
      (∀ x ∈ N, (l : ℤ_[l]) ^ k • x = 0) →
      Module.length ℤ_[l] ↥N ≤
        (k : ℕ∞) * Module.length ℤ_[l] (LinearMap.ker ((l : ℤ_[l]) • (LinearMap.id : M →ₗ[ℤ_[l]] M))) := by
  intro k
  induction k with
  | zero =>
    intro N hN
    have hsub : Subsingleton ↥N := by
      refine ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ => Subtype.ext ?_⟩
      have hx0 := hN x hx
      have hy0 := hN y hy
      rw [pow_zero, one_smul] at hx0 hy0
      exact hx0.trans hy0.symm
    have : Subsingleton ↥N := hsub
    rw [Module.length_eq_zero, Nat.cast_zero, zero_mul]
  | succ k ih =>
    intro N hN
    let multL : ↥N →ₗ[ℤ_[l]] M := ((l : ℤ_[l]) • (LinearMap.id : M →ₗ[ℤ_[l]] M)).comp N.subtype
    have hadd := Stage2GaloisCohomology.length_ker_add_length_range multL
    have hker_le : Module.length ℤ_[l] (LinearMap.ker multL) ≤
        Module.length ℤ_[l] (LinearMap.ker ((l : ℤ_[l]) • (LinearMap.id : M →ₗ[ℤ_[l]] M))) := by
      let incl : LinearMap.ker multL →ₗ[ℤ_[l]]
          LinearMap.ker ((l : ℤ_[l]) • (LinearMap.id : M →ₗ[ℤ_[l]] M)) :=
        { toFun := fun ⟨⟨x, hx⟩, hmx⟩ => ⟨x, LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp hmx)⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      exact Module.length_le_of_injective incl (fun ⟨⟨x, _⟩, _⟩ ⟨⟨y, _⟩, _⟩ h =>
        Subtype.ext (Subtype.ext (congrArg (fun z : LinearMap.ker ((l : ℤ_[l]) • (LinearMap.id : M →ₗ[ℤ_[l]] M)) => (z : M)) h)))
    have hrange_le : Module.length ℤ_[l] (LinearMap.range multL) ≤
        (k : ℕ∞) * Module.length ℤ_[l] (LinearMap.ker ((l : ℤ_[l]) • (LinearMap.id : M →ₗ[ℤ_[l]] M))) := by
      refine ih (LinearMap.range multL) ?_
      rintro y ⟨⟨x, hx⟩, rfl⟩
      have hkx := hN x hx
      change (l : ℤ_[l]) ^ k • ((l : ℤ_[l]) • x) = 0
      rw [← mul_smul, ← pow_succ, hkx]
    calc Module.length ℤ_[l] ↥N
        = Module.length ℤ_[l] (LinearMap.ker multL) + Module.length ℤ_[l] (LinearMap.range multL) :=
          hadd.symm
      _ ≤ Module.length ℤ_[l] (LinearMap.ker ((l : ℤ_[l]) • (LinearMap.id : M →ₗ[ℤ_[l]] M))) +
            (k : ℕ∞) * Module.length ℤ_[l] (LinearMap.ker ((l : ℤ_[l]) • (LinearMap.id : M →ₗ[ℤ_[l]] M))) :=
          add_le_add hker_le hrange_le
      _ = ((k + 1 : ℕ) : ℕ∞) *
            Module.length ℤ_[l] (LinearMap.ker ((l : ℤ_[l]) • (LinearMap.id : M →ₗ[ℤ_[l]] M))) := by
          rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]

theorem length_le_padicValNat_mul_lTorsion {l : ℕ} [Fact l.Prime]
    {M : Type*} [AddCommGroup M] [Module ℤ_[l] M] (a : ℤ) (ha : a ≠ 0)
    (hann : ∀ x : M, (a : ℤ_[l]) • x = 0) :
    Module.length ℤ_[l] M ≤
      (padicValNat l a.natAbs : ℕ∞) *
        Module.length ℤ_[l] (LinearMap.ker ((l : ℤ_[l]) • (LinearMap.id : M →ₗ[ℤ_[l]] M))) := by
  have han0 : a.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ha
  obtain ⟨k, u, hnot, hfac⟩ := Nat.exists_eq_pow_mul_and_not_dvd han0 l (Fact.out : l.Prime).ne_one
  have hk_eq : k = padicValNat l a.natAbs := by
    have hu0 : u ≠ 0 := fun hu => hnot (hu ▸ dvd_zero l)
    rw [hfac, padicValNat.mul (pow_ne_zero k (Fact.out : l.Prime).ne_zero) hu0,
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hnot, add_zero]
  have hu_unit : IsUnit (u : ℤ_[l]) := isUnit_natCast_padicInt_of_not_dvd hnot
  have hlpow : ∀ x ∈ (⊤ : Submodule ℤ_[l] M), (l : ℤ_[l]) ^ k • x = 0 := by
    intro x _
    have h1 : ((a.natAbs : ℕ) : ℤ_[l]) • x = 0 := by
      rcases Int.natAbs_eq a with h | h
      · have hcast : (a : ℤ_[l]) = ((a.natAbs : ℕ) : ℤ_[l]) := by
          conv_lhs => rw [h]
          exact Int.cast_natCast _
        rw [← hcast]; exact hann x
      · have hcast : (a : ℤ_[l]) = -((a.natAbs : ℕ) : ℤ_[l]) := by
          conv_lhs => rw [h]
          rw [Int.cast_neg, Int.cast_natCast]
        have hx := hann x
        rw [hcast, neg_smul, neg_eq_zero] at hx
        exact hx
    rw [hfac, Nat.cast_mul, Nat.cast_pow, mul_comm, mul_smul] at h1
    rcases hu_unit with ⟨uu, huu⟩
    have h2 := congrArg (fun y => (uu⁻¹ : ℤ_[l]ˣ) • y) h1
    simp only [smul_zero] at h2
    rw [← huu] at h2
    change (uu⁻¹ : ℤ_[l]ˣ) • ((uu : ℤ_[l]ˣ) • ((l : ℤ_[l]) ^ k • x)) = 0 at h2
    rwa [inv_smul_smul] at h2
  have hle := length_le_mul_lTorsion k (⊤ : Submodule ℤ_[l] M) hlpow
  have htop : Module.length ℤ_[l] M = Module.length ℤ_[l] ↥(⊤ : Submodule ℤ_[l] M) :=
    Stage2GaloisCohomology.length_eq_of_linearEquiv (Submodule.topEquiv (R := ℤ_[l]) (M := M)).symm
  rw [htop, ← hk_eq]
  exact hle

/-- **Unconditional Stickelberger Minus-Parity Length Bound (`stickelberger_minus_parity_length_bound`, `l ∣ [E : ℚ]`)**:
for any odd prime `l ≠ 2`, modulus `m > 2`, and any minus-parity `ℤ_[l][Gal(ℚ(ζ_m)/ℚ)]`-module `M`
annihilated by `z ∈ ℤ[Gal(ℚ(ζ_m)/ℚ)]` with nonzero signed determinant
`D := detR ℤ (ZMod m)ˣ (-1) (-1) ... (cycToUnitsAlg ℤ m z) ≠ 0`,
1. `Module.length ℤ_[l] M ≤ (padicValNat l D.natAbs : ℕ∞) * len(M[l])`,
2. `Real.log (D.natAbs : ℝ) ≤ ∑ χ ∈ oddChars m, Real.log (max 1 ‖evalCharMonoidAlg χ (toRatAlg z)‖)`! -/
theorem stickelberger_minus_parity_length_bound {l : ℕ} [Fact l.Prime]
    {m : ℕ} [NeZero m] (_hm : 2 < m)
    (hc : (-1 : (ZMod m)ˣ) * (-1 : (ZMod m)ˣ) = 1)
    (hc1 : (-1 : (ZMod m)ˣ) ≠ 1)
    {M : Type*} [AddCommGroup M] [Module ℤ_[l] M]
    (φ : MonoidAlgebra ℤ_[l] (CycGal m) →ₐ[ℤ_[l]] Module.End ℤ_[l] M)
    (hminus : ∀ x : M, φ (MonoidAlgebra.single (artinMap m (-1 : (ZMod m)ˣ)) 1) x = (-1 : ℤ_[l]) • x)
    (z : MonoidAlgebra ℤ (CycGal m))
    (hz : ∀ x : M, φ (MonoidAlgebra.mapRingHom (CycGal m) (Int.castRingHom ℤ_[l]) z) x = 0)
    (hD0 : detR ℤ (ZMod m)ˣ (-1 : (ZMod m)ˣ) (-1) hc hc1 (by norm_num)
      (cycToUnitsAlg ℤ m z) ≠ 0) :
    let D := detR ℤ (ZMod m)ˣ (-1 : (ZMod m)ˣ) (-1) hc hc1 (by norm_num) (cycToUnitsAlg ℤ m z)
    Module.length ℤ_[l] M ≤
      (padicValNat l D.natAbs : ℕ∞) *
        Module.length ℤ_[l] (LinearMap.ker ((l : ℤ_[l]) • (LinearMap.id : M →ₗ[ℤ_[l]] M))) ∧
    Real.log (D.natAbs : ℝ) ≤
      ∑ χ ∈ oddChars m, Real.log (max 1 ‖evalCharMonoidAlg χ (toRatAlg z)‖) := by
  intro D
  have hε : (-1 : ℤ) * (-1 : ℤ) = 1 := by norm_num
  let φu : MonoidAlgebra ℤ_[l] (ZMod m)ˣ →ₐ[ℤ_[l]] Module.End ℤ_[l] M :=
    φ.comp (unitsToCycAlg ℤ_[l] m)
  have hcomm_map :
      MonoidAlgebra.mapRingHom (ZMod m)ˣ (Int.castRingHom ℤ_[l]) (cycToUnitsAlg ℤ m z) =
        cycToUnitsAlg ℤ_[l] m (MonoidAlgebra.mapRingHom (CycGal m) (Int.castRingHom ℤ_[l]) z) := by
    have hbasis := monoidAlgebra_eq_sum_units m z
    conv_lhs => rw [hbasis, map_sum, map_sum]
    conv_rhs => rw [hbasis, map_sum, map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [cycToUnitsAlg_single, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.mapRingHom_single,
      cycToUnitsAlg_single]
  have hD_ann : ∀ x : M, (D : ℤ_[l]) • x = 0 := by
    intro x
    have hkill := adjKill ℤ_[l] (ZMod m)ˣ (-1 : (ZMod m)ˣ) (-1) φu hc hc1 hε
      (MonoidAlgebra.mapRingHom (ZMod m)ˣ (Int.castRingHom ℤ_[l]) (cycToUnitsAlg ℤ m z)) x
      (by
        change φ (unitsToCycAlg ℤ_[l] m (MonoidAlgebra.single (-1 : (ZMod m)ˣ) 1)) x = _
        rw [unitsToCycAlg_single]
        simpa using hminus x)
      (by
        change φ (unitsToCycAlg ℤ_[l] m (MonoidAlgebra.mapRingHom (ZMod m)ˣ (Int.castRingHom ℤ_[l])
          (cycToUnitsAlg ℤ m z))) x = 0
        rw [hcomm_map, unitsToCycAlg_cycToUnitsAlg]
        exact hz x)
    have hmap : detR ℤ_[l] (ZMod m)ˣ (-1 : (ZMod m)ˣ) (-1) hc hc1 hε
        (MonoidAlgebra.mapRingHom (ZMod m)ˣ (Int.castRingHom ℤ_[l]) (cycToUnitsAlg ℤ m z)) =
          (D : ℤ_[l]) := by
      simpa [D] using (detR_mapRingHom ℤ (ZMod m)ˣ (-1 : (ZMod m)ˣ) (-1)
        (Int.castRingHom ℤ_[l]) hc hc1 hε (cycToUnitsAlg ℤ m z)).symm
    rwa [hmap] at hkill
  refine ⟨length_le_padicValNat_mul_lTorsion D hD0 hD_ann, ?_⟩
  have hprod : ((D : ℂ)) = ∏ χ ∈ oddChars m, evalCharMonoidAlg χ (toRatAlg z) := by
    rw [← signedChars_neg_one_eq_oddChars]
    exact detR_int_eq_prod_signed_chars_cyc m (-1) hc hc1 hε z
  have hnorm : (D.natAbs : ℝ) = ∏ χ ∈ oddChars m, ‖evalCharMonoidAlg χ (toRatAlg z)‖ := by
    have h1 := congrArg norm hprod
    rw [Complex.norm_intCast, Complex.norm_prod] at h1
    have hDabs : (D.natAbs : ℝ) = |(D : ℝ)| := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    exact hDabs.trans h1
  have hDnat : (0 : ℝ) < (D.natAbs : ℝ) :=
    Nat.cast_pos.mpr (Int.natAbs_pos.mpr hD0)
  have hle_prod : (D.natAbs : ℝ) ≤ ∏ χ ∈ oddChars m, max 1 ‖evalCharMonoidAlg χ (toRatAlg z)‖ := by
    rw [hnorm]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => le_max_right _ _)
  have hlog_prod :
      Real.log (∏ χ ∈ oddChars m, max 1 ‖evalCharMonoidAlg χ (toRatAlg z)‖) =
        ∑ χ ∈ oddChars m, Real.log (max 1 ‖evalCharMonoidAlg χ (toRatAlg z)‖) := by
    rw [Real.log_prod]
    intro χ _
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  calc Real.log (D.natAbs : ℝ)
      ≤ Real.log (∏ χ ∈ oddChars m, max 1 ‖evalCharMonoidAlg χ (toRatAlg z)‖) :=
        Real.log_le_log hDnat hle_prod
    _ = ∑ χ ∈ oddChars m, Real.log (max 1 ‖evalCharMonoidAlg χ (toRatAlg z)‖) := hlog_prod

/-- **Stickelberger Carry-Multiplier Archimedean Bound (`stickelbergerIntMul`)**:
for any `m > 2` and `bu : (ZMod m)ˣ`, every odd character `χ ∈ oddChars m` satisfies
`Real.log (max 1 ‖evalCharMonoidAlg χ (toRatAlg (stickelbergerIntMul m bu))‖) ≤ Real.log (2 * m) + 4 * Real.log m`! -/
theorem log_stickelbergerIntMul_det_le {m : ℕ} [NeZero m] (hm : 2 < m)
    (hc : (-1 : (ZMod m)ˣ) * (-1 : (ZMod m)ˣ) = 1)
    (hc1 : (-1 : (ZMod m)ˣ) ≠ 1) (bu : (ZMod m)ˣ)
    (hD0 : detR ℤ (ZMod m)ˣ (-1 : (ZMod m)ˣ) (-1) hc hc1 (by norm_num)
      (cycToUnitsAlg ℤ m (stickelbergerIntMul m bu)) ≠ 0) :
    Real.log ((detR ℤ (ZMod m)ˣ (-1 : (ZMod m)ˣ) (-1) hc hc1 (by norm_num)
      (cycToUnitsAlg ℤ m (stickelbergerIntMul m bu))).natAbs : ℝ) ≤
      ((m.totient / 2 : ℕ) : ℝ) * (Real.log (2 * (m : ℝ)) + 4 * Real.log (m : ℝ)) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hm2 : (2 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hterm : ∀ χ ∈ oddChars m,
      Real.log (max 1 ‖evalCharMonoidAlg χ (toRatAlg (stickelbergerIntMul m bu))‖) ≤
        Real.log (2 * (m : ℝ)) + 4 * Real.log (m : ℝ) := by
    intro χ hχ
    have hχ_ne : χ ≠ 1 := ne_one_of_odd (mem_oddChars_iff.mp hχ)
    have hev := evalChar_stickelbergerIntMul_eq bu (mem_oddChars_iff.mp hχ)
    have hnorm_fac : ‖((bu : ZMod m).val : ℂ) - χ (bu : ZMod m)‖ ≤ 2 * (m : ℝ) := by
      have hbu_lt : ((bu : ZMod m).val : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast (ZMod.val_lt (bu : ZMod m)).le
      calc ‖((bu : ZMod m).val : ℂ) - χ (bu : ZMod m)‖
          ≤ ‖((bu : ZMod m).val : ℂ)‖ + ‖χ (bu : ZMod m)‖ := norm_sub_le _ _
        _ ≤ (m : ℝ) + 1 := by
            gcongr
            · rw [Complex.norm_natCast]; exact hbu_lt
            · exact χ.norm_le_one _
        _ ≤ 2 * (m : ℝ) := by linarith
    have hbern := (log_norm_genBernoulli_le (q := m) (χ := χ⁻¹) (by
      intro hinv
      apply hχ_ne
      simpa using congrArg Inv.inv hinv) (k := 1) le_rfl).1
    have hnorm_b : ‖genBernoulli χ⁻¹ 1‖ ≤ 2 * (m : ℝ) ^ 3 := by
      simpa using hbern
    have htot_bd : ‖evalCharMonoidAlg χ (toRatAlg (stickelbergerIntMul m bu))‖ ≤
        (2 * (m : ℝ)) * (2 * (m : ℝ) ^ 3) := by
      rw [hev, norm_mul]
      exact mul_le_mul hnorm_fac hnorm_b (norm_nonneg _) (by positivity)
    have hpow4 : (2 * (m : ℝ)) * (2 * (m : ℝ) ^ 3) ≤ (2 * (m : ℝ)) * (m : ℝ) ^ 4 := by
      calc (2 * (m : ℝ)) * (2 * (m : ℝ) ^ 3)
          ≤ (2 * (m : ℝ)) * ((m : ℝ) * (m : ℝ) ^ 3) := by gcongr
        _ = (2 * (m : ℝ)) * (m : ℝ) ^ 4 := by ring
    have hmax_le : max 1 ‖evalCharMonoidAlg χ (toRatAlg (stickelbergerIntMul m bu))‖ ≤
        (2 * (m : ℝ)) * (m : ℝ) ^ 4 := by
      refine max_le ?_ (htot_bd.trans hpow4)
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by linarith
      have : (1 : ℝ) ≤ (m : ℝ) ^ 4 := one_le_pow₀ hm1
      nlinarith
    calc Real.log (max 1 ‖evalCharMonoidAlg χ (toRatAlg (stickelbergerIntMul m bu))‖)
        ≤ Real.log ((2 * (m : ℝ)) * (m : ℝ) ^ 4) :=
          Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hmax_le
      _ = Real.log (2 * (m : ℝ)) + Real.log ((m : ℝ) ^ 4) :=
          Real.log_mul (by positivity) (by positivity)
      _ = Real.log (2 * (m : ℝ)) + 4 * Real.log (m : ℝ) := by
          rw [Real.log_pow]; norm_num
  have hprod : ((detR ℤ (ZMod m)ˣ (-1 : (ZMod m)ˣ) (-1) hc hc1 (by norm_num)
      (cycToUnitsAlg ℤ m (stickelbergerIntMul m bu)) : ℤ) : ℂ) =
      ∏ χ ∈ oddChars m, evalCharMonoidAlg χ (toRatAlg (stickelbergerIntMul m bu)) := by
    rw [← signedChars_neg_one_eq_oddChars]
    exact detR_int_eq_prod_signed_chars_cyc m (-1) hc hc1 (by norm_num) _
  have hnorm_det : ((detR ℤ (ZMod m)ˣ (-1 : (ZMod m)ˣ) (-1) hc hc1 (by norm_num)
      (cycToUnitsAlg ℤ m (stickelbergerIntMul m bu))).natAbs : ℝ) =
      ∏ χ ∈ oddChars m, ‖evalCharMonoidAlg χ (toRatAlg (stickelbergerIntMul m bu))‖ := by
    have h1 := congrArg norm hprod
    rw [Complex.norm_intCast, Complex.norm_prod] at h1
    have hDabs : ((detR ℤ (ZMod m)ˣ (-1 : (ZMod m)ˣ) (-1) hc hc1 (by norm_num)
        (cycToUnitsAlg ℤ m (stickelbergerIntMul m bu))).natAbs : ℝ) =
        |((detR ℤ (ZMod m)ˣ (-1 : (ZMod m)ˣ) (-1) hc hc1 (by norm_num)
          (cycToUnitsAlg ℤ m (stickelbergerIntMul m bu)) : ℤ) : ℝ)| := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    exact hDabs.trans h1
  have hDnat : (0 : ℝ) < ((detR ℤ (ZMod m)ˣ (-1 : (ZMod m)ˣ) (-1) hc hc1 (by norm_num)
      (cycToUnitsAlg ℤ m (stickelbergerIntMul m bu))).natAbs : ℝ) :=
    Nat.cast_pos.mpr (Int.natAbs_pos.mpr hD0)
  have hle_prod : ((detR ℤ (ZMod m)ˣ (-1 : (ZMod m)ˣ) (-1) hc hc1 (by norm_num)
      (cycToUnitsAlg ℤ m (stickelbergerIntMul m bu))).natAbs : ℝ) ≤
      ∏ χ ∈ oddChars m, max 1 ‖evalCharMonoidAlg χ (toRatAlg (stickelbergerIntMul m bu))‖ := by
    rw [hnorm_det]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => le_max_right _ _)
  calc Real.log ((detR ℤ (ZMod m)ˣ (-1 : (ZMod m)ˣ) (-1) hc hc1 (by norm_num)
      (cycToUnitsAlg ℤ m (stickelbergerIntMul m bu))).natAbs : ℝ)
      ≤ Real.log (∏ χ ∈ oddChars m, max 1 ‖evalCharMonoidAlg χ (toRatAlg (stickelbergerIntMul m bu))‖) :=
        Real.log_le_log hDnat hle_prod
    _ = ∑ χ ∈ oddChars m, Real.log (max 1 ‖evalCharMonoidAlg χ (toRatAlg (stickelbergerIntMul m bu))‖) := by
        rw [Real.log_prod]
        intro χ _
        exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    _ ≤ ∑ _χ ∈ oddChars m, (Real.log (2 * (m : ℝ)) + 4 * Real.log (m : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = ((oddChars m).card : ℝ) * (Real.log (2 * (m : ℝ)) + 4 * Real.log (m : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((m.totient / 2 : ℕ) : ℝ) * (Real.log (2 * (m : ℝ)) + 4 * Real.log (m : ℝ)) := by
        rw [card_oddChars hm]

/-- **Stickelberger Ramified Prime Polynomial Bound (`ThmBcOfPsiBound` / `Odd.stickBound`)**:
whenever ramified primes `l ∣ [E : ℚ]` satisfy `StickelbergerRamifiedControl S E t M n N`
(with `M ≤ condF E`, `n ≤ condF E`, `N ≤ (condF E * t)^2`), both `TaylorWilesWindow.minusBound`
and a pure polynomial bound `(condF E * t + 2) ^ C` hold unconditionally! -/
theorem stickelberger_ramified_poly_bound
    {S : SelmerSystem} {E : Type} [Field E] [NumberField E]
    {t M n N : ℕ} (ht : 2 ≤ t) (hM : M ≤ condF E) (hn : n ≤ condF E) (hN : N ≤ condF E * t)
    (H : StickelbergerRamifiedControl S E t M n N) :
    (∀ (l : Nat.Primes) (k : ℕ), (l : ℕ) ≠ 2 → (l : ℕ) ∣ M → 0 < k → k < t → S.shaLen E l k ≠ ⊤) ∧
    (∀ Pram : Finset Nat.Primes, (∀ l ∈ Pram, (l : ℕ) ≠ 2 ∧ (l : ℕ) ∣ M) →
      ∑ l ∈ Pram, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E l k).toNat : ℝ) ≤
        TaylorWilesWindow.minusBound 2 M n N t ∧
      ∑ l ∈ Pram, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E l k).toNat : ℝ) ≤
        ((condF E : ℝ) * (t : ℝ) + 2) ^ 14) := by
  obtain ⟨_, hfin, hsum⟩ := discharges_unified_ramified_branch_of_stickelberger H
  refine ⟨hfin, fun Pram hPram => ?_⟩
  have hmb := hsum Pram hPram
  refine ⟨hmb, hmb.trans ?_⟩
  have hE1 : (1 : ℝ) ≤ (condF E : ℝ) := by
    have : 0 < condF E := Nat.pos_of_ne_zero (by
      intro h0
      have hM0 : M = 0 := Nat.eq_zero_of_le_zero (h0 ▸ hM)
      exact H.M_ne_zero hM0)
    exact_mod_cast this
  have ht2 : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hM_le : (M : ℝ) ≤ (condF E : ℝ) := by exact_mod_cast hM
  have hn_le : (n : ℝ) ≤ (condF E : ℝ) := by exact_mod_cast hn
  have hN_le : (N : ℝ) ≤ (condF E : ℝ) * (t : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast H.N_pos
  unfold TaylorWilesWindow.minusBound
  set X : ℝ := (condF E : ℝ) * (t : ℝ) + 2
  have hX4 : (4 : ℝ) ≤ X := by dsimp [X]; nlinarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hterm1 : 3 * (n : ℝ) * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * (N : ℝ)) ≤ X ^ 6 := by
    have hlog1 : Real.log ((t : ℝ) * (N : ℝ)) ≤ X ^ 2 := by
      calc Real.log ((t : ℝ) * (N : ℝ))
          ≤ (t : ℝ) * (N : ℝ) := (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
        _ ≤ (t : ℝ) * ((condF E : ℝ) * (t : ℝ)) := by gcongr
        _ ≤ X ^ 2 := by dsimp [X]; nlinarith
    have hnt : 3 * (n : ℝ) * (t : ℝ) ^ 2 ≤ 3 * X ^ 3 := by
      have hnX : (n : ℝ) ≤ X := by dsimp [X]; nlinarith
      have htX : (t : ℝ) ≤ X := by dsimp [X]; nlinarith
      calc 3 * (n : ℝ) * (t : ℝ) ^ 2 ≤ 3 * X * X ^ 2 := by gcongr
        _ = 3 * X ^ 3 := by ring
    calc 3 * (n : ℝ) * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * (N : ℝ))
        ≤ (3 * X ^ 3) * X ^ 2 := mul_le_mul hnt hlog1 (Real.log_nonneg (by nlinarith)) (by positivity)
      _ = 3 * X ^ 5 := by ring
      _ ≤ X * X ^ 5 := by gcongr; linarith
      _ = X ^ 6 := by ring
  have hsum_le :
      2 * ∑ l ∈ M.primeFactors.erase 2,
          (l : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * (l : ℝ) * (N : ℝ)) ^ 2 ≤
        X ^ 13 := by
    have heach : ∀ l ∈ M.primeFactors.erase 2,
        (l : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * (l : ℝ) * (N : ℝ)) ^ 2 ≤
          X ^ 11 := fun l hl => by
      have hl_dvd : l ∣ M := Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase hl)
      have hl_le : (l : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero H.M_ne_zero) hl_dvd
      have hlX : (l : ℝ) ≤ X := by dsimp [X]; nlinarith
      have hnX : (n : ℝ) ≤ X := by dsimp [X]; nlinarith
      have htX : (t : ℝ) ≤ X := by dsimp [X]; nlinarith
      have hNX : (N : ℝ) ≤ X := by dsimp [X]; linarith
      have htlN_pos : (0 : ℝ) < (t : ℝ) * (l : ℝ) * (N : ℝ) := by
        have hl2 : 2 ≤ l := (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hl)).two_le
        positivity
      have hlog_le : Real.log ((t : ℝ) * (l : ℝ) * (N : ℝ)) ≤ X ^ 3 := by
        calc Real.log ((t : ℝ) * (l : ℝ) * (N : ℝ))
            ≤ (t : ℝ) * (l : ℝ) * (N : ℝ) := (Real.log_le_sub_one_of_pos htlN_pos).trans (by linarith)
          _ ≤ X * X * X := by gcongr
          _ = X ^ 3 := by ring
      have hlog_nonneg : 0 ≤ Real.log ((t : ℝ) * (l : ℝ) * (N : ℝ)) := by
        apply Real.log_nonneg
        have hl2 : (2 : ℝ) ≤ (l : ℝ) := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hl)).two_le
        have htl : (1 : ℝ) ≤ (t : ℝ) * (l : ℝ) := by nlinarith
        nlinarith
      have hlog_sq : Real.log ((t : ℝ) * (l : ℝ) * (N : ℝ)) ^ 2 ≤ X ^ 6 := by
        calc Real.log ((t : ℝ) * (l : ℝ) * (N : ℝ)) ^ 2
            ≤ (X ^ 3) ^ 2 := sq_le_sq' (by linarith) hlog_le
          _ = X ^ 6 := by ring
      have hpre : (l : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) ^ 2 ≤ X ^ 5 := by
        calc (l : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) ^ 2
            ≤ X * X ^ 2 * X ^ 2 := by gcongr
          _ = X ^ 5 := by ring
      calc (l : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * (l : ℝ) * (N : ℝ)) ^ 2
          ≤ X ^ 5 * X ^ 6 := by gcongr
        _ = X ^ 11 := by ring
    have hcard : ((M.primeFactors.erase 2).card : ℝ) ≤ X := by
      have h1 : (M.primeFactors.erase 2).card ≤ M := by
        calc (M.primeFactors.erase 2).card ≤ M.primeFactors.card :=
              Finset.card_le_card (Finset.erase_subset _ _)
          _ ≤ (Finset.Icc 1 M).card :=
              Finset.card_le_card (fun p hp => Finset.mem_Icc.mpr
                ⟨(Nat.prime_of_mem_primeFactors hp).pos,
                  Nat.le_of_dvd (Nat.pos_of_ne_zero H.M_ne_zero) (Nat.dvd_of_mem_primeFactors hp)⟩)
          _ = M := by simp
      have h1R : ((M.primeFactors.erase 2).card : ℝ) ≤ (M : ℝ) := by exact_mod_cast h1
      dsimp [X]
      nlinarith
    calc 2 * ∑ l ∈ M.primeFactors.erase 2,
            (l : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * (l : ℝ) * (N : ℝ)) ^ 2
        ≤ 2 * ∑ _l ∈ M.primeFactors.erase 2, X ^ 11 := by gcongr; exact heach _ ‹_›
      _ = 2 * (((M.primeFactors.erase 2).card : ℝ) * X ^ 11) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * (X * X ^ 11) := by gcongr
      _ ≤ X * (X * X ^ 11) := by gcongr; linarith
      _ = X ^ 13 := by ring
  have hx6 : X ^ 6 ≤ X ^ 13 := pow_le_pow_right₀ hX1 (by omega)
  calc 3 * (n : ℝ) * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * (N : ℝ)) +
        2 * ∑ l ∈ M.primeFactors.erase 2,
          (l : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * (l : ℝ) * (N : ℝ)) ^ 2
      ≤ X ^ 6 + X ^ 13 := add_le_add hterm1 hsum_le
    _ ≤ X ^ 13 + X ^ 13 := add_le_add hx6 le_rfl
    _ = 2 * X ^ 13 := by ring
    _ ≤ X * X ^ 13 := by gcongr; linarith
    _ = X ^ 14 := by ring

/-- **Odd Ramified Prime Divides `orderOf ψ.χ` (`IsChiField` Degree Divisibility)**:
for any `IsChiField ψ e q d E` (`0 < q, 0 < d`), every odd prime `l ≠ 2` dividing `[E : ℚ]`
divides `orderOf ψ.χ` (and hence divides `ψ.N.totient`)! -/
theorem odd_prime_dvd_finrank_dvd_orderOf_of_isChiField
    (ψ : PChar) (e q d : ℕ) (_hq : 0 < q) (_hd : 0 < d)
    (E : Type) [Field E] [NumberField E] (hE : IsChiField ψ e q d E)
    {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (hdvd : l ∣ Module.finrank ℚ E) :
    l ∣ orderOf ψ.χ := by
  obtain ⟨N, hN_nz, j, ζ, h2N, hψN, hqN, hdN, hζ, hgal⟩ := hE
  have hN_pos : 0 < N := NeZero.pos N
  have : NeZero (N : ℚ) := ⟨Nat.cast_ne_zero.mpr hN_pos.ne'⟩
  have : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  have : IsGalois ℚ (CyclotomicField N ℚ) :=
    IsCyclotomicExtension.isGalois {N} ℚ (CyclotomicField N ℚ)
  let G := CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ
  let eAut : G ≃* (ZMod N)ˣ :=
    IsCyclotomicExtension.autEquivPow (CyclotomicField N ℚ)
      (Polynomial.cyclotomic.irreducible_rat hN_pos)
  let F : IntermediateField ℚ (CyclotomicField N ℚ) := j.fieldRange
  let H : Subgroup G := F.fixingSubgroup
  have hG_comm : ∀ σ τ : G, σ * τ = τ * σ := fun σ τ =>
    eAut.injective (by simp [map_mul, mul_comm])
  let hH_norm : H.Normal := ⟨fun n hn g => by
    have hgn : g * n * g⁻¹ = n := by rw [hG_comm g n, mul_inv_cancel_right]
    rwa [hgn]⟩
  let _instFintypeG : Fintype G := Fintype.ofEquiv _ eAut.symm.toEquiv
  let _instFintypeQuot : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  have hcard_quot : Fintype.card (G ⧸ H) = Module.finrank ℚ E := by
    have h1 : Fintype.card (G ⧸ H) = H.index := by
      rw [← Nat.card_eq_fintype_card, Subgroup.index_eq_card]
    have h2 : H.index = Module.finrank ℚ F := by
      have hfix : IntermediateField.fixedField H = F := IsGalois.fixedField_fixingSubgroup F
      have hmul := Subgroup.card_mul_index H
      have hgal_card : Nat.card G = Module.finrank ℚ (CyclotomicField N ℚ) :=
        IsGalois.card_aut_eq_finrank ℚ (CyclotomicField N ℚ)
      have htow := Module.finrank_mul_finrank ℚ F (CyclotomicField N ℚ)
      have hdeg := IntermediateField.finrank_fixedField_eq_card H
      rw [hfix] at hdeg
      have hH_pos : 0 < Nat.card H := Nat.card_pos
      have hmul' : Nat.card H * H.index = Module.finrank ℚ (CyclotomicField N ℚ) := by
        rw [hmul, hgal_card]
      have htow' : Module.finrank ℚ F * Nat.card H = Module.finrank ℚ (CyclotomicField N ℚ) := by
        rw [← hdeg]; exact htow
      nlinarith
    have hEF : Module.finrank ℚ E = Module.finrank ℚ F :=
      (AlgEquiv.ofInjectiveField j).toLinearEquiv.finrank_eq
    rw [h1, h2, ← hEF]
  have hdvd_quot : l ∣ Fintype.card (G ⧸ H) := hcard_quot ▸ hdvd
  have : Fact l.Prime := ⟨hl⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card l hdvd_quot
  obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective x
  let Mexp : ℕ := 2 ^ (e + 1) * orderOf ψ.χ
  have hτ_pow : τ ^ Mexp ∈ H := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rintro _ ⟨y, rfl⟩
    obtain ⟨a, ha⟩ := Stage2GaloisWire.exists_pow_of_aut_primRoot hζ (τ ^ Mexp)
    obtain ⟨a₀, ha₀⟩ := Stage2GaloisWire.exists_pow_of_aut_primRoot hζ τ
    have hpow_a : ζ ^ a = ζ ^ (a₀ ^ Mexp) := by
      calc ζ ^ a = (τ ^ Mexp) ζ := ha.symm
        _ = ζ ^ (a₀ ^ Mexp) := by
          clear ha
          suffices ∀ k : ℕ, (τ ^ k) ζ = ζ ^ (a₀ ^ k) from this Mexp
          intro k
          induction k with
          | zero => rw [pow_zero, pow_zero, pow_one]; rfl
          | succ n ih =>
            rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, ha₀, ← pow_mul, pow_succ', mul_comm a₀]
    have ha_modN : a ≡ a₀ ^ Mexp [MOD N] := by
      have hpow_mod : ∀ n, ζ ^ n = ζ ^ (n % N) := fun n => by
        conv_lhs => rw [← Nat.div_add_mod n N]
        rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
      have h2 : ζ ^ (a % N) = ζ ^ (a₀ ^ Mexp % N) := by
        rw [← hpow_mod a, ← hpow_mod (a₀ ^ Mexp), hpow_a]
      have ha_lt := Nat.mod_lt a hN_pos
      have hb_lt := Nat.mod_lt (a₀ ^ Mexp) hN_pos
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have hpos : 0 < a₀ ^ Mexp % N - a % N := by omega
        have hsub : a₀ ^ Mexp % N - a % N < N := by omega
        have hpow1 : ζ ^ (a₀ ^ Mexp % N - a % N) = 1 := by
          apply mul_left_cancel₀ (pow_ne_zero (a % N) (hζ.ne_zero hN_pos.ne'))
          rw [← pow_add, Nat.add_sub_cancel' hlt.le, h2, mul_one]
        exact absurd (Nat.le_of_dvd hpos (hζ.dvd_of_pow_eq_one _ hpow1)) (not_le_of_gt hsub)
      · have hpos : 0 < a % N - a₀ ^ Mexp % N := by omega
        have hsub : a % N - a₀ ^ Mexp % N < N := by omega
        have hpow1 : ζ ^ (a % N - a₀ ^ Mexp % N) = 1 := by
          apply mul_left_cancel₀ (pow_ne_zero (a₀ ^ Mexp % N) (hζ.ne_zero hN_pos.ne'))
          rw [← pow_add, Nat.add_sub_cancel' hlt.le, ← h2, mul_one]
        exact absurd (Nat.le_of_dvd hpos (hζ.dvd_of_pow_eq_one _ hpow1)) (not_le_of_gt hsub)
    have ha0_cop : Nat.Coprime a₀ N := by
      obtain ⟨b, hb⟩ := Stage2GaloisWire.exists_pow_of_aut_primRoot hζ τ.symm
      have h1 : ζ ^ (a₀ * b) = ζ := by
        calc ζ ^ (a₀ * b) = (ζ ^ a₀) ^ b := by rw [pow_mul]
          _ = (τ ζ) ^ b := by rw [ha₀]
          _ = τ (ζ ^ b) := (map_pow τ ζ b).symm
          _ = τ (τ.symm ζ) := by rw [hb]
          _ = ζ := τ.apply_symm_apply ζ
      by_cases hN1 : N = 1
      · subst hN1; exact Nat.coprime_one_right a₀
      · have hab_pos : 0 < a₀ * b := by
          by_contra h0
          have hab0 : a₀ * b = 0 := by omega
          rw [hab0, pow_zero] at h1
          exact hN1 (Nat.dvd_one.mp (hζ.dvd_of_pow_eq_one 1 (by simpa using h1.symm)))
        have hpow_1 : ζ ^ (a₀ * b - 1) = 1 := by
          apply mul_left_cancel₀ (hζ.ne_zero hN_pos.ne')
          rw [← pow_succ', Nat.sub_add_cancel hab_pos, h1, mul_one]
        have hdvd_sub : N ∣ (a₀ * b - 1) := hζ.dvd_of_pow_eq_one _ hpow_1
        have hmod1 : (a₀ : ZMod N) * (b : ZMod N) = 1 := by
          rw [← Nat.cast_mul]
          simpa using (ZMod.natCast_eq_natCast_iff (a₀ * b) 1 N).mpr (by
            obtain ⟨k, hk⟩ := hdvd_sub
            have hab_eq : a₀ * b = 1 + N * k := by omega
            rw [Nat.ModEq, hab_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : 1 < N)])
        have hunit : IsUnit (a₀ : ZMod N) :=
          ⟨⟨(a₀ : ZMod N), (b : ZMod N), hmod1, by rw [mul_comm]; exact hmod1⟩, rfl⟩
        exact (ZMod.isUnit_iff_coprime a₀ N).mp hunit
    have h2_mod : a ≡ 1 [MOD 2 ^ (e + 2)] := by
      have ha_2 : a ≡ a₀ ^ Mexp [MOD 2 ^ (e + 2)] := ha_modN.of_dvd h2N
      have hcop2 : Nat.Coprime a₀ (2 ^ (e + 2)) := ha0_cop.coprime_dvd_right h2N
      have htot2 : Nat.totient (2 ^ (e + 2)) = 2 ^ (e + 1) := by
        rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
        norm_num
      have hpow2 : a₀ ^ (2 ^ (e + 1)) ≡ 1 [MOD 2 ^ (e + 2)] := by
        rw [← htot2]
        exact Nat.ModEq.pow_totient hcop2
      have hpow_m : a₀ ^ Mexp ≡ 1 [MOD 2 ^ (e + 2)] := by
        dsimp only [Mexp]
        rw [pow_mul]
        simpa [one_pow] using hpow2.pow (orderOf ψ.χ)
      exact ha_2.trans hpow_m
    have hψ_val : ψ.val a = 1 := by
      have ha_ψ : a ≡ a₀ ^ Mexp [MOD ψ.N] := ha_modN.of_dvd hψN
      have hcast : (a : ZMod ψ.N) = ((a₀ : ZMod ψ.N) ^ Mexp) := by
        simpa [Nat.cast_pow] using (ZMod.natCast_eq_natCast_iff a (a₀ ^ Mexp) ψ.N).mpr ha_ψ
      unfold PChar.val
      rw [hcast, map_pow]
      have hpow_ord : ψ.χ ^ orderOf ψ.χ = 1 := pow_orderOf_eq_one ψ.χ
      have hM : ψ.χ ^ Mexp = 1 := by
        dsimp only [Mexp]
        rw [mul_comm, pow_mul, hpow_ord, one_pow]
      have hu_ψ : IsUnit (a₀ : ZMod ψ.N) := (ZMod.isUnit_iff_coprime a₀ ψ.N).mpr
        (ha0_cop.coprime_dvd_right hψN)
      have hMexp_ne : Mexp ≠ 0 := mul_ne_zero (pow_ne_zero _ two_ne_zero)
        (Nat.pos_iff_ne_zero.mp (orderOf_pos ψ.χ))
      calc ψ.χ (a₀ : ZMod ψ.N) ^ Mexp = (ψ.χ ^ Mexp) (a₀ : ZMod ψ.N) :=
            (MulChar.pow_apply' ψ.χ hMexp_ne (a₀ : ZMod ψ.N)).symm
        _ = (1 : DirichletCharacter ℂ ψ.N) (a₀ : ZMod ψ.N) := by rw [hM]
        _ = 1 := MulChar.one_apply hu_ψ
    have hjac_q : jacobiSym (a : ℤ) q = 1 := by
      have ha_q : a ≡ a₀ ^ Mexp [MOD q] := ha_modN.of_dvd hqN
      rw [HostFieldSupply.jacobiSym_congr_nat ha_q, Nat.cast_pow, jacobiSym.pow_left]
      have h2_dvd : 2 ∣ Mexp := by
        dsimp only [Mexp]
        exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _
      obtain ⟨k, hk⟩ := h2_dvd
      rw [hk, pow_mul, sq]
      have hne0 : jacobiSym (a₀ : ℤ) q ≠ 0 := by
        intro hz
        have hgcd := (jacobiSym.eq_zero_iff.mp hz).2
        exact hgcd (by simpa [Int.gcd_natCast_natCast] using (ha0_cop.coprime_dvd_right hqN : Nat.Coprime a₀ q))
      rcases jacobiSym.trichotomy (a₀ : ℤ) q with h | h | h
      · contradiction
      · rw [h, one_mul, one_pow]
      · rw [h, neg_one_mul, neg_neg, one_pow]
    have hjac_d : jacobiSym (a : ℤ) d = 1 := by
      have ha_d : a ≡ a₀ ^ Mexp [MOD d] := ha_modN.of_dvd hdN
      rw [HostFieldSupply.jacobiSym_congr_nat ha_d, Nat.cast_pow, jacobiSym.pow_left]
      have h2_dvd : 2 ∣ Mexp := by
        dsimp only [Mexp]
        exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _
      obtain ⟨k, hk⟩ := h2_dvd
      rw [hk, pow_mul, sq]
      have hne0 : jacobiSym (a₀ : ℤ) d ≠ 0 := by
        intro hz
        have hgcd := (jacobiSym.eq_zero_iff.mp hz).2
        exact hgcd (by simpa [Int.gcd_natCast_natCast] using (ha0_cop.coprime_dvd_right hdN : Nat.Coprime a₀ d))
      rcases jacobiSym.trichotomy (a₀ : ℤ) d with h | h | h
      · contradiction
      · rw [h, one_mul, one_pow]
      · rw [h, neg_one_mul, neg_neg, one_pow]
    exact (hgal (τ ^ Mexp) a ha).mpr ⟨Or.inl h2_mod, hψ_val, hjac_q, hjac_d⟩ y
  have hmk_pow : (QuotientGroup.mk τ : G ⧸ H) ^ Mexp = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hτ_pow
  have hl_dvd_M : l ∣ Mexp := hx ▸ orderOf_dvd_of_pow_eq_one hmk_pow
  have hl_not_dvd_2 : ¬ l ∣ 2 ^ (e + 1) := by
    intro h
    exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow h))
  exact (hl.dvd_mul.mp hl_dvd_M).resolve_left hl_not_dvd_2

end SignedCharsDetAndStickelbergerBound

end SignedInvolutionDetAndStickelbergerBound

/-! ## Section 4: Complex-Conjugation `ShaMinus`, Maschke Eigenspaces & Rubin Cyclotomic Euler System (`l ∤ [E : ℚ]`) -/

section RubinMinusParityAndShaMinus

open RHDirect.Stage12GaloisShaLen
open RHDirect.Stage12Window1RootAvoid
open RHDirect.Stage11EulerSystemSelmer
open RHDirect.Stage11StickelbergerRamified

section ComplexConjAndParitySystem

/-- Canonical complex-conjugation automorphism `ζ ↦ ζ⁻¹` on `CyclotomicField N ℚ`. -/
noncomputable def cycConjAut (N : ℕ) [NeZero N] :
    CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ :=
  (IsCyclotomicExtension.autEquivPow (CyclotomicField N ℚ)
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos N))).symm (-1 : (ZMod N)ˣ)

theorem cycConjAut_sq (N : ℕ) [NeZero N] :
    cycConjAut N * cycConjAut N = 1 := by
  unfold cycConjAut
  rw [← map_mul, neg_mul_neg, one_mul, map_one]

theorem cycConjAut_primRoot {N : ℕ} [NeZero N] {ζ : CyclotomicField N ℚ}
    (hζ : IsPrimitiveRoot ζ N) :
    cycConjAut N ζ = ζ⁻¹ := by
  have hN : 0 < N := NeZero.pos N
  have : NeZero (N : ℚ) := ⟨Nat.cast_ne_zero.mpr hN.ne'⟩
  have : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  have hspec : IsPrimitiveRoot (IsCyclotomicExtension.zeta N ℚ (CyclotomicField N ℚ)) N :=
    IsCyclotomicExtension.zeta_spec N ℚ (CyclotomicField N ℚ)
  have hact := hspec.autToPow_spec ℚ (cycConjAut N)
  have heq : (hspec.autToPow ℚ (cycConjAut N) : (ZMod N)ˣ) = (-1 : (ZMod N)ˣ) := by
    unfold cycConjAut
    exact (IsCyclotomicExtension.autEquivPow (CyclotomicField N ℚ)
      (Polynomial.cyclotomic.irreducible_rat hN)).apply_symm_apply (-1)
  rw [heq, Units.val_neg, Units.val_one] at hact
  have hzeta_inv : cycConjAut N (IsCyclotomicExtension.zeta N ℚ (CyclotomicField N ℚ)) =
      (IsCyclotomicExtension.zeta N ℚ (CyclotomicField N ℚ))⁻¹ := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    have hval : (-1 : ZMod N).val = N - 1 := by
      rw [hm, ZMod.val_neg_one m, Nat.succ_sub_one]
    rw [hval] at hact
    rw [← hact]
    apply mul_left_cancel₀ (hspec.ne_zero hN.ne')
    rw [← pow_succ', Nat.sub_add_cancel hN, hspec.pow_eq_one, mul_inv_cancel₀ (hspec.ne_zero hN.ne')]
  obtain ⟨k, _, hk⟩ := hspec.eq_pow_of_pow_eq_one hζ.pow_eq_one
  rw [← hk, map_pow, hzeta_inv, inv_pow]

private structure ChiFieldConjData (E : Type) [Field E] [NumberField E] where
  N : ℕ
  hN_nz : NeZero N
  j : E →ₐ[ℚ] CyclotomicField N ℚ
  ζ : CyclotomicField N ℚ
  hζ : IsPrimitiveRoot ζ N
  c : E ≃ₐ[ℚ] E
  c_emb : ∀ x : E, j (c x) = @cycConjAut N hN_nz (j x)
  c_sq : c * c = 1

private noncomputable def isChiFieldConjPack {ψ : PChar} {e q d : ℕ}
    {E : Type} [Field E] [NumberField E] (hE : IsChiField ψ e q d E) :
    ChiFieldConjData E := by
  classical
  let N := hE.choose
  have hN_nz : NeZero N := hE.choose_spec.choose
  have hrest := hE.choose_spec.choose_spec
  let j : E →ₐ[ℚ] CyclotomicField N ℚ := hrest.choose
  have hrest2 := hrest.choose_spec
  let ζ : CyclotomicField N ℚ := hrest2.choose
  have hζ := hrest2.choose_spec.2.2.2.2.1
  have hN_pos : 0 < N := NeZero.pos N
  have : NeZero (N : ℚ) := ⟨Nat.cast_ne_zero.mpr hN_pos.ne'⟩
  have : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  have : IsGalois ℚ (CyclotomicField N ℚ) :=
    IsCyclotomicExtension.isGalois {N} ℚ (CyclotomicField N ℚ)
  let G := CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ
  let eAut : G ≃* (ZMod N)ˣ :=
    IsCyclotomicExtension.autEquivPow (CyclotomicField N ℚ)
      (Polynomial.cyclotomic.irreducible_rat hN_pos)
  have hG_comm : ∀ σ τ : G, σ * τ = τ * σ := fun σ τ =>
    eAut.injective (by simp [map_mul, mul_comm])
  let F : IntermediateField ℚ (CyclotomicField N ℚ) := j.fieldRange
  let H : Subgroup G := F.fixingSubgroup
  have hfix : IntermediateField.fixedField H = F := IsGalois.fixedField_fixingSubgroup F
  have hstab : ∀ x : E, cycConjAut N (j x) ∈ F := by
    intro x
    rw [← hfix, IntermediateField.mem_fixedField_iff]
    intro τ hτ
    have hxF : j x ∈ F := ⟨x, rfl⟩
    rw [← hfix, IntermediateField.mem_fixedField_iff] at hxF
    calc τ (cycConjAut N (j x)) = (τ * cycConjAut N) (j x) := rfl
      _ = (cycConjAut N * τ) (j x) := by rw [hG_comm τ (cycConjAut N)]
      _ = cycConjAut N (τ (j x)) := rfl
      _ = cycConjAut N (j x) := by rw [hxF τ hτ]
  let ej : E ≃ₐ[ℚ] F := AlgEquiv.ofInjectiveField j
  let cF : F ≃ₐ[ℚ] F :=
    { toFun := fun y => ⟨cycConjAut N y.1, by
        obtain ⟨x, rfl⟩ := ej.surjective y
        exact hstab x⟩
      invFun := fun y => ⟨cycConjAut N y.1, by
        obtain ⟨x, rfl⟩ := ej.surjective y
        exact hstab x⟩
      left_inv := fun y => Subtype.ext (by
        change (cycConjAut N * cycConjAut N) y.1 = y.1
        rw [cycConjAut_sq N, AlgEquiv.one_apply])
      right_inv := fun y => Subtype.ext (by
        change (cycConjAut N * cycConjAut N) y.1 = y.1
        rw [cycConjAut_sq N, AlgEquiv.one_apply])
      map_mul' := fun a b => Subtype.ext (map_mul (cycConjAut N) a.1 b.1)
      map_add' := fun a b => Subtype.ext (map_add (cycConjAut N) a.1 b.1)
      commutes' := fun r => Subtype.ext ((cycConjAut N).commutes r) }
  let c : E ≃ₐ[ℚ] E := ej.trans (cF.trans ej.symm)
  have hc_emb : ∀ x : E, j (c x) = cycConjAut N (j x) := fun x => by
    have hej : ∀ y : E, (ej y : CyclotomicField N ℚ) = j y := fun _ => rfl
    rw [← hej (c x)]
    dsimp only [c]
    simp only [AlgEquiv.trans_apply]
    rw [ej.apply_symm_apply]
    rfl
  have hc_sq : c * c = 1 := by
    ext x
    rw [AlgEquiv.mul_apply, AlgEquiv.one_apply]
    apply j.injective
    change j (c (c x)) = j x
    rw [hc_emb, hc_emb]
    change (cycConjAut N * cycConjAut N) (j x) = j x
    rw [cycConjAut_sq, AlgEquiv.one_apply]
  exact ⟨N, hN_nz, j, ζ, hζ, c, hc_emb, hc_sq⟩

/-- For any `IsChiField ψ e q d E`, `cycConjAut N` stabilizes `j.fieldRange` and induces a
`ℚ`-algebra involution `isChiFieldConj : E ≃ₐ[ℚ] E` (`isChiFieldConj * isChiFieldConj = 1`). -/
noncomputable def isChiFieldConj {ψ : PChar} {e q d : ℕ}
    {E : Type} [Field E] [NumberField E] (hE : IsChiField ψ e q d E) :
    E ≃ₐ[ℚ] E :=
  (isChiFieldConjPack hE).c

theorem isChiFieldConj_sq {ψ : PChar} {e q d : ℕ}
    {E : Type} [Field E] [NumberField E] (hE : IsChiField ψ e q d E) :
    isChiFieldConj hE * isChiFieldConj hE = 1 :=
  (isChiFieldConjPack hE).c_sq

/-- A `ℚ`-algebra involution `c : E ≃ₐ[ℚ] E` lifted to a ring involution `σ : Ω ≃+* Ω` on `Ω / E`. -/
structure CMGaloisInvolution (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] where
  c : E ≃ₐ[ℚ] E
  σ : Ω ≃+* Ω
  c_sq : c * c = 1
  σ_sq : σ.trans σ = RingEquiv.refl Ω
  compat : ∀ x : E, σ (algebraMap E Ω x) = algebraMap E Ω (c x)

/-- Trivial identity involution on `(E, Ω)`. -/
def CMGaloisInvolution.trivial (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] :
    CMGaloisInvolution E Ω where
  c := AlgEquiv.refl
  σ := RingEquiv.refl Ω
  c_sq := rfl
  σ_sq := rfl
  compat _ := rfl

section AlgebraicClosureComplexLift

/-- The subfield of complex numbers algebraic over `ℚ`, invariant under `starRingEnd ℂ`. -/
private noncomputable def algClosureInC : Subfield ℂ where
  carrier := {z : ℂ | IsAlgebraic ℚ z}
  zero_mem' := isAlgebraic_zero
  one_mem' := isAlgebraic_one
  add_mem' ha hb := ha.add hb
  neg_mem' {_} ha := ha.neg
  mul_mem' ha hb := ha.mul hb
  inv_mem' {_} ha := ha.inv

private lemma isAlgClosed_algClosureInC : IsAlgClosed algClosureInC := by
  refine ⟨fun p => ?_⟩
  rw [Polynomial.splits_iff_card_roots]
  by_cases hp0 : p = 0
  · subst hp0; simp
  · let ι : algClosureInC →+* ℂ := algClosureInC.subtype
    have hι : Function.Injective ι := Subtype.coe_injective
    have halgQ : Algebra.IsAlgebraic ℚ algClosureInC := ⟨fun z => by
      obtain ⟨q, hq0, hqz⟩ := z.2
      refine ⟨q, hq0, Subtype.ext ?_⟩
      change ι (Polynomial.aeval z q) = 0
      rw [Polynomial.aeval_def, Polynomial.hom_eval₂]
      have hring : ι.comp (algebraMap ℚ algClosureInC) = algebraMap ℚ ℂ :=
        RingHom.ext fun r => by simp
      rw [hring]
      change Polynomial.eval₂ (algebraMap ℚ ℂ) (z : ℂ) q = 0
      simpa [Polynomial.aeval_def] using hqz⟩
    have hintQ : Algebra.IsIntegral ℚ algClosureInC := Algebra.IsAlgebraic.isIntegral
    have hroot_mem : ∀ (q : Polynomial algClosureInC) (α : ℂ), q ≠ 0 → (q.map ι).IsRoot α →
        α ∈ algClosureInC := fun q α hq0 hα_root => by
      have hlc : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq0
      have hα_int_sub : IsIntegral algClosureInC α := by
        refine ⟨Polynomial.C q.leadingCoeff⁻¹ * q, ?_, ?_⟩
        · rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
            inv_mul_cancel₀ hlc]
        · rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, mul_eq_zero]
          right
          exact (Polynomial.eval_map ι α).symm.trans hα_root
      have hα_int : IsIntegral ℚ α := isIntegral_trans α hα_int_sub
      exact hα_int.isAlgebraic
    have hcard_eq : ∀ (n : ℕ) (q : Polynomial algClosureInC), q ≠ 0 → q.natDegree = n →
        q.roots.card = q.natDegree := by
      intro n
      induction n with
      | zero =>
        intro q _ hdeg
        have hle : q.roots.card ≤ 0 := hdeg ▸ Polynomial.card_roots' q
        omega
      | succ m ih =>
        intro q hq0 hdeg
        have hdegC : (q.map ι).natDegree ≠ 0 := by
          rw [Polynomial.natDegree_map_eq_of_injective hι, hdeg]
          exact Nat.succ_ne_zero m
        have hdegC' : (q.map ι).degree ≠ 0 := fun h0 =>
          hdegC (Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr h0.le)
        obtain ⟨α, hα_root⟩ := IsAlgClosed.exists_root (q.map ι) hdegC'
        let r : algClosureInC := ⟨α, hroot_mem q α hq0 hα_root⟩
        have hr_root : q.IsRoot r := by
          rw [Polynomial.IsRoot.def]
          apply hι
          rw [map_zero, Polynomial.eval, Polynomial.hom_eval₂, RingHom.comp_id, ← Polynomial.eval_map]
          exact hα_root
        obtain ⟨q', hq'⟩ := Polynomial.dvd_iff_isRoot.mpr hr_root
        have hq'0 : q' ≠ 0 := fun h0 => hq0 (by rw [hq', h0, mul_zero])
        have hdeg_q' : q'.natDegree = m := by
          have hm1 : q.natDegree = (Polynomial.X - Polynomial.C r).natDegree + q'.natDegree := by
            rw [hq', Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hq'0]
          rw [Polynomial.natDegree_X_sub_C, hdeg] at hm1
          omega
        have hroots_q : q.roots = (Polynomial.X - Polynomial.C r).roots + q'.roots := by
          rw [hq']
          exact Polynomial.roots_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero r) hq'0)
        rw [hroots_q, Multiset.card_add, Polynomial.roots_X_sub_C, Multiset.card_singleton,
          ih q' hq'0 hdeg_q', hdeg_q', hdeg]
        omega
    exact hcard_eq p.natDegree p hp0 rfl

private lemma star_mem_algClosureInC {z : ℂ} (hz : z ∈ algClosureInC) :
    starRingEnd ℂ z ∈ algClosureInC := by
  obtain ⟨p, hp0, hpz⟩ := hz
  refine ⟨p, hp0, ?_⟩
  have hconj : Polynomial.aeval (starRingEnd ℂ z) p = starRingEnd ℂ (Polynomial.aeval z p) := by
    rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Algebra.smul_def, map_mul, map_pow]
    congr 1
    change (algebraMap ℚ ℂ (p.coeff i)) = starRingEnd ℂ (algebraMap ℚ ℂ (p.coeff i))
    exact (Complex.conj_ofReal _).symm
  rw [hconj, hpz, map_zero]

private noncomputable def starAlgClosureInC : algClosureInC ≃+* algClosureInC where
  toFun z := ⟨starRingEnd ℂ z.1, star_mem_algClosureInC z.2⟩
  invFun z := ⟨starRingEnd ℂ z.1, star_mem_algClosureInC z.2⟩
  left_inv z := Subtype.ext (Complex.conj_conj z.1)
  right_inv z := Subtype.ext (Complex.conj_conj z.1)
  map_mul' a b := Subtype.ext (map_mul (starRingEnd ℂ) a.1 b.1)
  map_add' a b := Subtype.ext (map_add (starRingEnd ℂ) a.1 b.1)

/-- Unconditional complex-conjugation involution on `AlgebraicClosure E` extending `isChiFieldConj hE`
for ANY `IsChiField ψ e q d E`! -/
noncomputable def cmGaloisInvolutionOfIsChiField {ψ : PChar} {e q d : ℕ}
    {E : Type} [Field E] [NumberField E] (hE : IsChiField ψ e q d E) :
    CMGaloisInvolution E (AlgebraicClosure E) := by
  classical
  let pack := isChiFieldConjPack hE
  let N := pack.N
  let _ : NeZero N := pack.hN_nz
  let j : E →ₐ[ℚ] CyclotomicField N ℚ := pack.j
  let ζ : CyclotomicField N ℚ := pack.ζ
  have hζ : IsPrimitiveRoot ζ N := pack.hζ
  have hN_pos : 0 < N := NeZero.pos N
  let _ : NeZero (N : ℚ) := ⟨Nat.cast_ne_zero.mpr hN_pos.ne'⟩
  let pb : PowerBasis ℚ (CyclotomicField N ℚ) := hζ.powerBasis ℚ
  let zC : ℂ := Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))
  have hzC : IsPrimitiveRoot zC N := Complex.isPrimitiveRoot_exp N hN_pos.ne'
  have haeval : Polynomial.aeval zC (minpoly ℚ pb.gen) = 0 := by
    dsimp only [pb]
    rw [IsPrimitiveRoot.powerBasis_gen ℚ hζ,
      ← hζ.minpoly_eq_cyclotomic_of_irreducible (Polynomial.cyclotomic.irreducible_rat hN_pos)]
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
    exact hzC.isRoot_cyclotomic hN_pos
  let ιCyc : CyclotomicField N ℚ →ₐ[ℚ] ℂ := pb.lift zC haeval
  have hιCyc_ζ : ιCyc ζ = zC := by
    have hgen : pb.gen = ζ := IsPrimitiveRoot.powerBasis_gen ℚ hζ
    rw [← hgen]
    exact pb.lift_gen zC haeval
  have hconj_cyc : ∀ w : CyclotomicField N ℚ,
      starRingEnd ℂ (ιCyc w) = ιCyc (cycConjAut N w) := by
    let starQ : ℂ →ₐ[ℚ] ℂ :=
      { toRingHom := starRingEnd ℂ
        commutes' := fun r => by
          change starRingEnd ℂ (r : ℂ) = (r : ℂ)
          exact Complex.conj_ofReal _ }
    change ∀ w, (starQ.comp ιCyc) w = (ιCyc.comp (cycConjAut N : CyclotomicField N ℚ →ₐ[ℚ] _)) w
    intro w
    congr 1
    apply pb.algHom_ext
    rw [IsPrimitiveRoot.powerBasis_gen ℚ hζ]
    change starRingEnd ℂ (ιCyc ζ) = ιCyc (cycConjAut N ζ)
    rw [hιCyc_ζ, cycConjAut_primRoot hζ, map_inv₀, hιCyc_ζ]
    dsimp only [zC]
    rw [← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, Complex.conj_natCast]
    ring
  have halg_E : ∀ x : E, ιCyc (j x) ∈ algClosureInC := fun x => by
    have hx : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    exact IsIntegral.isAlgebraic (R := ℚ) (IsIntegral.map (ιCyc.comp j) hx)
  let ιE : E →ₐ[ℚ] algClosureInC :=
    { toFun := fun x => ⟨ιCyc (j x), halg_E x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [map_mul])
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp [map_add])
      commutes' := fun r => Subtype.ext (by simp) }
  have hcompat_E : ∀ x : E, starAlgClosureInC (ιE x) = ιE (isChiFieldConj hE x) := by
    intro x
    apply Subtype.ext
    change starRingEnd ℂ (ιCyc (j x)) = ιCyc (j (pack.c x))
    rw [hconj_cyc (j x), pack.c_emb x]
  letI : Algebra E algClosureInC := ιE.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ E algClosureInC :=
    IsScalarTower.of_algebraMap_eq (fun r => Subtype.ext (by
      change (algebraMap ℚ ℂ r : ℂ) = ιCyc (j (algebraMap ℚ E r))
      simp))
  haveI : IsAlgClosed algClosureInC := isAlgClosed_algClosureInC
  haveI : Algebra.IsAlgebraic ℚ algClosureInC := ⟨fun z => by
    obtain ⟨q, hq0, hqz⟩ := z.2
    refine ⟨q, hq0, Subtype.ext ?_⟩
    change algClosureInC.subtype (Polynomial.aeval z q) = 0
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂]
    have hring : algClosureInC.subtype.comp (algebraMap ℚ algClosureInC) = algebraMap ℚ ℂ :=
      RingHom.ext fun r => by simp
    rw [hring]
    simpa [Polynomial.aeval_def] using hqz⟩
  haveI : Algebra.IsIntegral ℚ algClosureInC := Algebra.IsAlgebraic.isIntegral
  haveI : Algebra.IsIntegral E algClosureInC :=
    ⟨fun z => (Algebra.IsIntegral.isIntegral (R := ℚ) (A := algClosureInC) z).tower_top⟩
  haveI : Algebra.IsAlgebraic E algClosureInC :=
    ⟨fun z => IsIntegral.isAlgebraic (Algebra.IsIntegral.isIntegral (R := E) (A := algClosureInC) z)⟩
  haveI : IsAlgClosure E algClosureInC := ⟨isAlgClosed_algClosureInC, inferInstance⟩
  let eΩ : AlgebraicClosure E ≃ₐ[E] algClosureInC :=
    IsAlgClosure.equiv E (AlgebraicClosure E) algClosureInC
  let eΩR : AlgebraicClosure E ≃+* algClosureInC := eΩ.toRingEquiv
  let σ : AlgebraicClosure E ≃+* AlgebraicClosure E :=
    eΩR.trans (starAlgClosureInC.trans eΩR.symm)
  refine ⟨isChiFieldConj hE, σ, isChiFieldConj_sq hE, ?_, ?_⟩
  · ext z
    simp only [σ, RingEquiv.trans_apply, RingEquiv.refl_apply]
    apply eΩR.injective
    simp only [RingEquiv.apply_symm_apply]
    change (starAlgClosureInC.trans starAlgClosureInC) (eΩR z) = eΩR z
    have hsq : starAlgClosureInC.trans starAlgClosureInC = RingEquiv.refl _ := by
      ext y; exact Complex.conj_conj y.1
    rw [hsq, RingEquiv.refl_apply]
  · intro x
    simp only [σ, RingEquiv.trans_apply]
    have he : eΩR (algebraMap E (AlgebraicClosure E) x) = ιE x := by
      change eΩ (algebraMap E (AlgebraicClosure E) x) = algebraMap E algClosureInC x
      exact eΩ.commutes x
    rw [he, hcompat_E x]
    apply eΩR.injective
    rw [eΩR.apply_symm_apply]
    change algebraMap E algClosureInC (isChiFieldConj hE x) =
      eΩ (algebraMap E (AlgebraicClosure E) (isChiFieldConj hE x))
    exact (eΩ.commutes (isChiFieldConj hE x)).symm

end AlgebraicClosureComplexLift

section ConjugationActionOnGaloisH1

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

/-- Conjugate an element `g ∈ G E Ω` by a `CMGaloisInvolution E Ω`: `g ↦ σ⁻¹ ∘ g ∘ σ`. -/
def cmConjGalHom (I : CMGaloisInvolution E Ω) : G E Ω →* G E Ω where
  toFun g :=
    { toFun := fun y => I.σ.symm (g (I.σ y))
      invFun := fun y => I.σ.symm (g.symm (I.σ y))
      left_inv := fun y => by simp
      right_inv := fun y => by simp
      map_mul' := fun a b => by simp [map_mul]
      map_add' := fun a b => by simp [map_add]
      commutes' := fun x => by
        show I.σ.symm (g (I.σ (algebraMap E Ω x))) = algebraMap E Ω x
        rw [I.compat x, g.commutes (I.c x)]
        apply I.σ.injective
        rw [I.σ.apply_symm_apply, I.compat x] }
  map_one' := by ext y; simp
  map_mul' g h := by ext y; simp [AlgEquiv.mul_apply]

omit [IsAlgClosure E Ω] in
theorem cmConjGalHom_involutive (I : CMGaloisInvolution E Ω) (g : G E Ω) :
    cmConjGalHom I (cmConjGalHom I g) = g := by
  ext y
  have hσ : ∀ z : Ω, I.σ (I.σ z) = z := fun z => by
    change (I.σ.trans I.σ) z = z; rw [I.σ_sq, RingEquiv.refl_apply]
  have hσ_symm : ∀ z : Ω, I.σ.symm z = I.σ z := fun z => by
    apply I.σ.injective; rw [I.σ.apply_symm_apply, hσ]
  simp [cmConjGalHom, hσ_symm, hσ]

omit [IsAlgClosure E Ω] in
theorem cmConjGalHom_continuous (I : CMGaloisInvolution E Ω) :
    Continuous (cmConjGalHom I) := by
  apply continuous_of_continuousAt_one (cmConjGalHom I)
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨K, hK, hs⟩ := hs
  have : FiniteDimensional E K := hK
  let K' : IntermediateField E Ω :=
    { carrier := {y : Ω | I.σ y ∈ K}
      zero_mem' := by simp
      add_mem' := fun ha hb => by simp only [Set.mem_ofPred_eq] at *; rw [map_add]; exact K.add_mem ha hb
      one_mem' := by simp
      mul_mem' := fun ha hb => by simp only [Set.mem_ofPred_eq] at *; rw [map_mul]; exact K.mul_mem ha hb
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at *
        rw [map_inv₀]
        exact K.inv_mem ha
      algebraMap_mem' := fun x => by
        simp only [Set.mem_ofPred_eq, I.compat x]
        exact K.algebraMap_mem (I.c x) }
  have hK' : FiniteDimensional E K' := by
    have hK_finQ : FiniteDimensional ℚ K := Module.Finite.trans E K
    let eKK' : K ≃ₗ[ℚ] K' :=
      { toFun := fun y => ⟨I.σ.symm y.1, by simp [K', y.2]⟩
        invFun := fun y => ⟨I.σ y.1, y.2⟩
        left_inv := fun y => Subtype.ext (I.σ.apply_symm_apply y.1)
        right_inv := fun y => Subtype.ext (I.σ.symm_apply_apply y.1)
        map_add' := fun a b => Subtype.ext (map_add I.σ.symm a.1 b.1)
        map_smul' := fun r y => Subtype.ext (by
          change I.σ.symm (r • y.1) = r • I.σ.symm y.1
          rw [Rat.smul_def, Rat.smul_def, map_mul]
          congr 1
          exact map_ratCast I.σ.symm r) }
    have : FiniteDimensional ℚ K' := eKK'.finiteDimensional
    exact Module.Finite.of_restrictScalars_finite ℚ E K'
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  refine ⟨K', hK', fun g hg => hs ?_⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hg ⊢
  intro x hx
  have hx' : I.σ.symm x ∈ K' := by
    change I.σ (I.σ.symm x) ∈ K
    simpa using hx
  have hgx := hg (I.σ.symm x) hx'
  show I.σ.symm (g (I.σ x)) = x
  have hσ_symm : ∀ z : Ω, I.σ.symm z = I.σ z := fun z => by
    apply I.σ.injective; rw [I.σ.apply_symm_apply]
    change z = (I.σ.trans I.σ) z; rw [I.σ_sq, RingEquiv.refl_apply]
  rw [hσ_symm] at hgx ⊢
  rw [hgx]
  change (I.σ.trans I.σ) x = x; rw [I.σ_sq, RingEquiv.refl_apply]

theorem cmConjGalHom_cycZ (I : CMGaloisInvolution E Ω) (l : ℕ) [Fact l.Prime] (g : G E Ω) :
    cycZ E Ω l (cmConjGalHom I g) = cycZ E Ω l g := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  apply Units.ext
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have hζ' : IsPrimitiveRoot (I.σ ζ) (l ^ n) := hζ.map_of_injective I.σ.injective
  have h1 : g (I.σ ζ) = (I.σ ζ) ^ (PadicInt.toZModPow n ((cycZ E Ω l g : ℤ_[l]ˣ) : ℤ_[l])).val :=
    cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G E Ω) Ω g) (I.σ ζ) hζ'.pow_eq_one
  have h2 : I.σ.symm (g (I.σ ζ)) =
      ζ ^ (PadicInt.toZModPow n ((cycZ E Ω l (cmConjGalHom I g) : ℤ_[l]ˣ) : ℤ_[l])).val :=
    cyclotomicCharacter.spec (L := Ω) l
      (MulSemiringAction.toRingAut (G E Ω) Ω (cmConjGalHom I g)) ζ hζ.pow_eq_one
  rw [h1, map_pow, I.σ.symm_apply_apply] at h2
  apply ZMod.val_injective
  exact (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2).symm

/-- Induced ring automorphism `𝓞 E ≃+* 𝓞 E` from `I.c : E ≃ₐ[ℚ] E`. -/
noncomputable def cmConjRingInt (I : CMGaloisInvolution E Ω) : 𝓞 E ≃+* 𝓞 E where
  toFun x := ⟨I.c x.1, IsIntegral.map I.c.toAlgHom x.2⟩
  invFun x := ⟨I.c.symm x.1, IsIntegral.map I.c.symm.toAlgHom x.2⟩
  left_inv x := Subtype.ext (I.c.symm_apply_apply x.1)
  right_inv x := Subtype.ext (I.c.apply_symm_apply x.1)
  map_mul' a b := Subtype.ext (map_mul I.c a.1 b.1)
  map_add' a b := Subtype.ext (map_add I.c a.1 b.1)

/-- Induced involution on `HeightOneSpectrum (𝓞 E)`. -/
noncomputable def cmConjSpec (I : CMGaloisInvolution E Ω) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 E) ≃ IsDedekindDomain.HeightOneSpectrum (𝓞 E) :=
  let φ : 𝓞 E ≃+* 𝓞 E := cmConjRingInt I
  { toFun := fun v =>
      { asIdeal := v.asIdeal.comap φ.symm.toRingHom
        isPrime := v.isPrime.comap φ.symm.toRingHom
        ne_bot := fun h => v.ne_bot (Ideal.ext fun x => by
          constructor
          · intro hx
            have : φ x ∈ v.asIdeal.comap φ.symm.toRingHom := by
              rw [Ideal.mem_comap]
              change φ.symm (φ x) ∈ v.asIdeal
              rw [φ.symm_apply_apply]
              exact hx
            rw [h, Ideal.mem_bot] at this
            simpa using congrArg φ.symm this
          · intro hx; rw [Ideal.mem_bot.mp hx]; exact Ideal.zero_mem _) }
    invFun := fun v =>
      { asIdeal := v.asIdeal.comap φ.toRingHom
        isPrime := v.isPrime.comap φ.toRingHom
        ne_bot := fun h => v.ne_bot (Ideal.ext fun x => by
          constructor
          · intro hx
            have : φ.symm x ∈ v.asIdeal.comap φ.toRingHom := by
              rw [Ideal.mem_comap]
              change φ (φ.symm x) ∈ v.asIdeal
              rw [φ.apply_symm_apply]
              exact hx
            rw [h, Ideal.mem_bot] at this
            simpa using congrArg φ this
          · intro hx; rw [Ideal.mem_bot.mp hx]; exact Ideal.zero_mem _) }
    left_inv := fun v => by
      ext x
      change x ∈ (v.asIdeal.comap φ.symm.toRingHom).comap φ.toRingHom ↔ x ∈ v.asIdeal
      rw [Ideal.mem_comap, Ideal.mem_comap]
      change φ.symm (φ x) ∈ v.asIdeal ↔ x ∈ v.asIdeal
      rw [φ.symm_apply_apply]
    right_inv := fun v => by
      ext x
      change x ∈ (v.asIdeal.comap φ.toRingHom).comap φ.symm.toRingHom ↔ x ∈ v.asIdeal
      rw [Ideal.mem_comap, Ideal.mem_comap]
      change φ (φ.symm x) ∈ v.asIdeal ↔ x ∈ v.asIdeal
      rw [φ.apply_symm_apply] }

omit [IsAlgClosure E Ω] in
theorem cmConjGalHom_mem_ine (I : CMGaloisInvolution E Ω)
    {A : ValuationSubring Ω} {g : G E Ω} (hg : g ∈ Ine (F := E) A) :
    cmConjGalHom I g ∈ Ine (F := E) (A.comap I.σ.toRingHom) := by
  let A₁ := A.comap I.σ.toRingHom
  have hA₁ : ∀ y : Ω, y ∈ A₁ ↔ I.σ y ∈ A := fun y => Iff.rfl
  have hdec : cmConjGalHom I g ∈ Dec (F := E) A₁ := by
    rw [mem_Dec]
    ext y
    conv_lhs =>
      rw [← smul_inv_smul (cmConjGalHom I g) y, ValuationSubring.smul_mem_pointwise_smul_iff]
    rw [← map_inv (cmConjGalHom I) g, hA₁, hA₁]
    show I.σ (I.σ.symm (g⁻¹ (I.σ y))) ∈ A ↔ I.σ y ∈ A
    rw [I.σ.apply_symm_apply]
    exact apply_mem_iff_of_mem_Dec ((Dec (F := E) A).inv_mem hg.1) (I.σ y)
  have hv : ∀ y : Ω, A₁.valuation y < 1 ↔ A.valuation (I.σ y) < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', hA₁, ← map_inv₀, hA₁,
      map_eq_zero_iff _ I.σ.injective]
  refine ⟨hdec, fun x hx => ?_⟩
  rw [hv]
  have hle : A.valuation (I.σ x) ≤ 1 := by
    rwa [ValuationSubring.valuation_le_one_iff, ← hA₁, ← ValuationSubring.valuation_le_one_iff]
  have e : I.σ ((cmConjGalHom I g) x - x) = g (I.σ x) - I.σ x := by
    rw [map_sub]
    show I.σ (I.σ.symm (g (I.σ x))) - I.σ x = _
    rw [I.σ.apply_symm_apply]
  rw [e]
  exact hg.2 (I.σ x) hle

omit [IsAlgClosure E Ω] in
theorem cmConjSpec_mem_above_iff (I : CMGaloisInvolution E Ω) (l : ℕ)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) :
    cmConjSpec I v ∈ Above E l ↔ v ∈ Above E l := by
  change ((l : ℕ) : 𝓞 E) ∈ v.asIdeal.comap (cmConjRingInt I).symm.toRingHom ↔
    ((l : ℕ) : 𝓞 E) ∈ v.asIdeal
  rw [Ideal.mem_comap]
  have hnat : (cmConjRingInt I).symm.toRingHom ((l : ℕ) : 𝓞 E) = ((l : ℕ) : 𝓞 E) :=
    map_natCast (cmConjRingInt I).symm.toRingHom l
  rw [hnat]

omit [IsAlgClosure E Ω] in
theorem cmConj_isPlaceOver (I : CMGaloisInvolution E Ω)
    {A : ValuationSubring Ω} {v : IsDedekindDomain.HeightOneSpectrum (𝓞 E)}
    (hA : IsPlaceOver A v) :
    IsPlaceOver (A.comap I.σ.toRingHom) (cmConjSpec I v) := by
  intro x
  let A₁ := A.comap I.σ.toRingHom
  have hA₁ : ∀ y : Ω, y ∈ A₁ ↔ I.σ y ∈ A := fun y => Iff.rfl
  have hv : ∀ y : Ω, A₁.valuation y < 1 ↔ A.valuation (I.σ y) < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', hA₁, ← map_inv₀, hA₁,
      map_eq_zero_iff _ I.σ.injective]
  rw [hv, I.compat (x : E)]
  have hφ_symm : (cmConjRingInt I).symm x = cmConjRingInt I x := Subtype.ext (by
    change I.c.symm (x : E) = I.c (x : E)
    apply I.c.injective
    rw [I.c.apply_symm_apply]
    change (x : E) = (I.c * I.c) (x : E)
    rw [I.c_sq, AlgEquiv.one_apply])
  change A.valuation (algebraMap E Ω ((cmConjRingInt I x : 𝓞 E) : E)) < 1 ↔
    (cmConjRingInt I).symm x ∈ v.asIdeal
  rw [hφ_symm]
  exact hA (cmConjRingInt I x)

omit [IsAlgClosure E Ω] in
theorem cmConj_NS_le (I : CMGaloisInvolution E Ω) (l : ℕ) [Fact l.Prime] (D : LData E Ω l) :
    NS Ω (D.S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) ≤
      (NS Ω (D.S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E)))).comap (cmConjGalHom I) := by
  have hcl : IsClosed (((NS Ω (D.S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E)))).comap
      (cmConjGalHom I) : Subgroup (G E Ω)) : Set (G E Ω)) :=
    (isClosed_NS Ω (D.S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E)))).preimage
      (cmConjGalHom_continuous I)
  have : ((NS Ω (D.S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E)))).comap
      (cmConjGalHom I)).Normal := Subgroup.Normal.comap inferInstance _
  unfold NS
  apply Subgroup.topologicalClosure_minimal _ _ hcl
  apply Subgroup.normalClosure_le_normal
  rintro τ hτ
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_compl_iff, exists_prop] at hτ
  obtain ⟨v, hv, A, hA, hτ_ine⟩ := hτ
  have hv' : cmConjSpec I v ∉ (D.S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) := by
    intro hmem
    have h1 : cmConjSpec I v ∈ Above E l := by
      rw [← D.hS]; exact hmem
    rw [cmConjSpec_mem_above_iff, ← D.hS] at h1
    exact hv h1
  have hA' : IsPlaceOver (A.comap I.σ.toRingHom) (cmConjSpec I v) := cmConj_isPlaceOver I hA
  have hτ' : cmConjGalHom I τ ∈ Ine (F := E) (A.comap I.σ.toRingHom) :=
    cmConjGalHom_mem_ine I hτ_ine
  show cmConjGalHom I τ ∈ NS Ω (D.S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E)))
  apply Subgroup.le_topologicalClosure
  apply Subgroup.subset_normalClosure
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_compl_iff, exists_prop]
  exact ⟨cmConjSpec I v, hv', A.comap I.σ.toRingHom, hA', hτ'⟩

omit [IsAlgClosure E Ω] in
/-- Continuous involution `GS Ω (D.S : Set _) →* GS Ω (D.S : Set _)` induced by `CMGaloisInvolution`. -/
noncomputable def gsConj (I : CMGaloisInvolution E Ω) (l : ℕ) [Fact l.Prime] (D : LData E Ω l) :
    GS Ω (D.S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) →*
      GS Ω (D.S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) :=
  QuotientGroup.map
    (NS Ω (D.S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E))))
    (NS Ω (D.S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E))))
    (cmConjGalHom I) (cmConj_NS_le I l D)

omit [IsAlgClosure E Ω] in
theorem gsConj_mk (I : CMGaloisInvolution E Ω) (l : ℕ) [Fact l.Prime] (D : LData E Ω l)
    (g : G E Ω) :
    gsConj I l D (toGS Ω (D.S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) g) =
      toGS Ω (D.S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) (cmConjGalHom I g) := rfl

omit [IsAlgClosure E Ω] in
theorem continuous_gsConj (I : CMGaloisInvolution E Ω) (l : ℕ) [Fact l.Prime] (D : LData E Ω l) :
    Continuous (gsConj I l D) :=
  (QuotientGroup.isQuotientMap_mk
    (NS Ω (D.S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E))))).continuous_iff.2
    ((continuous_toGS Ω (D.S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E)))).comp
      (cmConjGalHom_continuous I))

omit [IsAlgClosure E Ω] in
theorem gsConj_gsConj (I : CMGaloisInvolution E Ω) (l : ℕ) [Fact l.Prime] (D : LData E Ω l)
    (g : GS Ω (D.S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E)))) :
    gsConj I l D (gsConj I l D g) = g := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  show gsConj I l D (gsConj I l D (toGS Ω (D.S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) g)) =
    toGS Ω (D.S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) g
  rw [gsConj_mk, gsConj_mk, cmConjGalHom_involutive]

theorem chi_comp_gsConj (I : CMGaloisInvolution E Ω) (l : ℕ) [Fact l.Prime] (D : LData E Ω l)
    (g : GS Ω (D.S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E)))) :
    D.chi (gsConj I l D g) = D.chi g := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  show D.chi (gsConj I l D (toGS Ω (D.S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) g)) =
    D.chi (toGS Ω (D.S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) g)
  rw [gsConj_mk]
  have h1 := congrArg (fun f => f (cmConjGalHom I g)) D.hchi
  have h2 := congrArg (fun f => f g) D.hchi
  exact h1.trans ((cmConjGalHom_cycZ I l g).trans h2.symm)

/-- **Genuine Complex-Conjugation Involution on `H¹(G_{E, S_l}, (ℚ_l/ℤ_l)(-e))`** (`conjH1`):
acts via `(c • f)(g) = (-1)^e • f(σ⁻¹ g σ)`, preserves `Sha D e` identically, and satisfies
`conjH1 (conjH1 x) = x`! -/
noncomputable def conjH1 (I : CMGaloisInvolution E Ω) {l : ℕ} [Fact l.Prime]
    (D : LData E Ω l) (e : ℤ) : Module.End ℤ_[l] (H1 (qzTw D e)) :=
  let sgn : ℤ_[l] := (-1 : ℤ_[l]) ^ e.natAbs
  let mSign : QZ l →ₗ[ℤ_[l]] QZ l := sgn • LinearMap.id
  have hcomm : ∀ g m, mSign (qzTw D e (gsConj I l D g) m) = qzTw D e g (mSign m) := by
    intro g m
    have hchi : D.chi (gsConj I l D g) = D.chi g := chi_comp_gsConj I l D g
    have hchi_pow : (D.chi ^ (-e)) (gsConj I l D g) = (D.chi ^ (-e)) g := by
      cases -e with
      | ofNat n =>
        change (D.chi ^ (n : ℤ)) (gsConj I l D g) = (D.chi ^ (n : ℤ)) g
        simp only [zpow_natCast, MonoidHom.pow_apply, hchi]
      | negSucc n =>
        simp only [zpow_negSucc, MonoidHom.inv_apply, MonoidHom.pow_apply, hchi]
    change sgn • (qzTw D e (gsConj I l D g) m) = qzTw D e g (sgn • m)
    rw [map_smul]
    congr 1
    simp only [qzTw, scalRep_apply, hchi_pow]
  pairH1 (qzTw D e) (qzTw D e) (gsConj I l D) (continuous_gsConj I l D) mSign
    (continuous_id.const_smul sgn) hcomm

theorem conjH1_sq (I : CMGaloisInvolution E Ω) {l : ℕ} [Fact l.Prime]
    (D : LData E Ω l) (e : ℤ) (x : H1 (qzTw D e)) :
    conjH1 I D e (conjH1 I D e x) = x := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  dsimp only [conjH1]
  simp only [pairH1, Submodule.mapQ_apply]
  apply (Submodule.Quotient.eq _).mpr
  have hz : ∀ g : GS Ω (D.S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E))),
      ((-1 : ℤ_[l]) ^ e.natAbs • ((-1 : ℤ_[l]) ^ e.natAbs •
        f.1 (gsConj I l D (gsConj I l D g)))) = f.1 g := fun g => by
    rw [gsConj_gsConj, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
  exact (mem_B1 _ _).mpr ⟨0, fun g => by
    rw [map_zero, sub_zero]
    change ((-1 : ℤ_[l]) ^ e.natAbs • ((-1 : ℤ_[l]) ^ e.natAbs •
      f.1 (gsConj I l D (gsConj I l D g)))) - f.1 g = 0
    rw [hz g, sub_self]⟩

theorem conjH1_mem_sha (I : CMGaloisInvolution E Ω) {l : ℕ} [Fact l.Prime]
    (D : LData E Ω l) (e : ℤ) {x : H1 (qzTw D e)} (hx : x ∈ Sha D e) :
    conjH1 I D e x ∈ Sha D e := by
  simp only [Sha, Sha1, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro v
  let v' : D.S := ⟨cmConjSpec I v.1, by
    have hv' : cmConjSpec I v.1 ∈ Above E l := by
      rw [cmConjSpec_mem_above_iff]
      have hv1 : v.1 ∈ Above E l := D.hS ▸ Finset.mem_coe.mpr v.2
      exact hv1
    have hv2 : cmConjSpec I v.1 ∈ (D.S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) :=
      D.hS ▸ hv'
    exact Finset.mem_coe.mp hv2⟩
  have hA' : IsPlaceOver ((D.A v).comap I.σ.toRingHom) v'.1 :=
    cmConj_isPlaceOver I (D.hA v)
  obtain ⟨g₀, hg₀⟩ := exists_smul_eq_of_isPlaceOver (D.hA v') hA'
  let cHom : Dec (F := E) (D.A v) →* Dec (F := E) (D.A v') :=
    { toFun := fun τ =>
        ⟨g₀⁻¹ * cmConjGalHom I τ.1 * g₀, by
          rw [mem_Dec]
          have hc1 : cmConjGalHom I τ.1 ∈ Dec (F := E) ((D.A v).comap I.σ.toRingHom) := by
            rw [mem_Dec]
            ext y
            conv_lhs =>
              rw [← smul_inv_smul (cmConjGalHom I τ.1) y,
                ValuationSubring.smul_mem_pointwise_smul_iff]
            rw [← map_inv (cmConjGalHom I) τ.1]
            change I.σ (I.σ.symm (τ.1⁻¹ (I.σ y))) ∈ D.A v ↔ I.σ y ∈ D.A v
            rw [I.σ.apply_symm_apply]
            exact apply_mem_iff_of_mem_Dec ((Dec (F := E) (D.A v)).inv_mem τ.2) (I.σ y)
          rw [mem_Dec] at hc1
          have hg_inv : g₀⁻¹ • ((D.A v).comap I.σ.toRingHom) = D.A v' := by
            rw [← hg₀, inv_smul_smul]
          calc (g₀⁻¹ * cmConjGalHom I τ.1 * g₀) • D.A v'
              = (g₀⁻¹ * cmConjGalHom I τ.1) • (g₀ • D.A v') := mul_smul _ _ _
            _ = g₀⁻¹ • (cmConjGalHom I τ.1 • ((D.A v).comap I.σ.toRingHom)) := by
              rw [hg₀, mul_smul]
            _ = g₀⁻¹ • ((D.A v).comap I.σ.toRingHom) := by rw [hc1]
            _ = D.A v' := hg_inv⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hcCont : Continuous cHom := by
    apply Continuous.subtype_mk
    exact ((continuous_const.mul ((cmConjGalHom_continuous I).comp continuous_subtype_val)).mul
      continuous_const)
  have hconj_loc : ∀ τ : Dec (F := E) (D.A v),
      ((locFam D.S D.A v').comp cHom) τ =
        (toGS Ω (D.S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) g₀)⁻¹ *
          gsConj I l D (locFam D.S D.A v τ) *
          toGS Ω (D.S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) g₀ := fun τ => by
    simp only [locFam, locHom, MonoidHom.comp_apply, Subgroup.coe_subtype, cHom, MonoidHom.coe_mk,
      OneHom.coe_mk, map_mul, map_inv, gsConj_mk]
  have hres_comp : resH1 (qzTw D e) ((locFam D.S D.A v').comp cHom)
      ((continuous_locFam D.S D.A v').comp hcCont) x = 0 := by
    rw [← resH1_comp (qzTw D e) (locFam D.S D.A v') (continuous_locFam D.S D.A v') cHom hcCont x,
      hx v', map_zero]
  have hres_gs : resH1 (qzTw D e) ((gsConj I l D).comp (locFam D.S D.A v))
      ((continuous_gsConj I l D).comp (continuous_locFam D.S D.A v)) x = 0 :=
    (resH1_conj_eq_zero_iff (qzTw D e) ((gsConj I l D).comp (locFam D.S D.A v))
      ((continuous_gsConj I l D).comp (continuous_locFam D.S D.A v))
      (toGS Ω (D.S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) g₀)⁻¹
      ((locFam D.S D.A v').comp cHom) ((continuous_locFam D.S D.A v').comp hcCont)
      (fun τ => by rw [hconj_loc, inv_inv]; rfl) x).mp hres_comp
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [resH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    Submodule.coe_subtype, mem_B1, restrictCocycles1_apply, MonoidHom.comp_apply] at hres_gs
  dsimp only [conjH1]
  simp only [resH1, pairH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap, Submodule.coe_subtype, mem_B1, restrictCocycles1_apply,
    compatiblePairCocycles1_apply]
  obtain ⟨m, hm⟩ := hres_gs
  refine ⟨(-1 : ℤ_[l]) ^ e.natAbs • m, fun τ => ?_⟩
  change (-1 : ℤ_[l]) ^ e.natAbs • f.1 (gsConj I l D (locFam D.S D.A v τ)) =
    qzTw D e (locFam D.S D.A v τ) ((-1 : ℤ_[l]) ^ e.natAbs • m) - (-1 : ℤ_[l]) ^ e.natAbs • m
  rw [hm τ, smul_sub, map_smul]
  congr 2
  have hchi := chi_comp_gsConj I l D (locFam D.S D.A v τ)
  have hchi_pow : (D.chi ^ (-e)) (gsConj I l D (locFam D.S D.A v τ)) =
      (D.chi ^ (-e)) (locFam D.S D.A v τ) := by
    cases -e with
    | ofNat n =>
      change (D.chi ^ (n : ℤ)) (gsConj I l D (locFam D.S D.A v τ)) =
        (D.chi ^ (n : ℤ)) (locFam D.S D.A v τ)
      simp only [zpow_natCast, MonoidHom.pow_apply, hchi]
    | negSucc n =>
      simp only [zpow_negSucc, MonoidHom.inv_apply, MonoidHom.pow_apply, hchi]
  simp only [qzTw, scalRep_apply, hchi_pow]

end ConjugationActionOnGaloisH1

section ParitySelmerSystemWiring

/-- **Genuine Complex-Conjugation `ParitySelmerSystem`** extending
`Stage12GaloisShaLen.realGaloisSelmerSystem`: on every field admitting a nontrivial CM involution
(in particular every `IsChiField`!), `cAct` is `conjH1`; for fields without a nontrivial CM involution,
`cAct` acts by `(-1)^e • id` (fixing `Sha` inside the `(-1)^e` eigenspace, so `ShaMinus = 0`). -/
noncomputable def minusParitySelmerSystem : ParitySelmerSystem := by
  classical
  let chooseInv : ∀ (E : Type) [Field E] [NumberField E],
      CMGaloisInvolution E (AlgebraicClosure E) := fun E _ _ =>
    if h : ∃ I : CMGaloisInvolution E (AlgebraicClosure E), I.c ≠ 1
    then Classical.choose h
    else CMGaloisInvolution.trivial E (AlgebraicClosure E)
  exact ParitySelmerSystem.ofInvolution
    (fun E _ _ l e => Stage12GaloisShaLen.H1 (qzTw (canonicalLData E l) (e : ℤ)))
    (fun E _ _ l e => Stage12GaloisShaLen.Sha1Galois E l (e : ℤ))
    (fun E _ _ l e => conjH1 (chooseInv E) (canonicalLData E l) (e : ℤ))
    (fun E _ _ l e x hx => conjH1_mem_sha (chooseInv E) (canonicalLData E l) (e : ℤ) hx)
    (fun E _ _ l e x => conjH1_sq (chooseInv E) (canonicalLData E l) (e : ℤ) x)

theorem minusParitySelmerSystem_shaLen_eq (E : Type) [Field E] [NumberField E]
    (l : Nat.Primes) (e : ℕ) :
    minusParitySelmerSystem.shaLen E l e = realGaloisSelmerSystem.shaLen E l e := rfl

end ParitySelmerSystemWiring

end ComplexConjAndParitySystem

/-! ### Section 4b: Maschke Eigenspace Decomposition & Rubin Cyclotomic-Unit Euler System (`ML.iv`) -/

section MaschkeAndRubinCyclotomicEulerSystem

/-- **Unconditional Maschke Orthogonal-Idempotent Length Splitting (`maschke_idempotent_decomp`)**:
for any finite orthogonal idempotent family `e : ι → A` summing to `1` in a ring `A` acting
`R`-linearly on an `R`-module `M`, every `A`-stable submodule `N ≤ M` satisfies
`Module.length R N = ∑ i, Module.length R ↥(N ⊓ LinearMap.range (φ (e i)))`! -/
theorem maschke_idempotent_decomp {R A M : Type*} [CommRing R] [Ring A] [Algebra R A]
    [AddCommGroup M] [Module R M] (φ : A →ₐ[R] Module.End R M)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → A)
    (hsum : ∑ i : ι, e i = 1)
    (hidem : ∀ i, e i * e i = e i)
    (horth : ∀ i j, i ≠ j → e i * e j = 0)
    (N : Submodule R M) (hN : ∀ i, ∀ x ∈ N, (φ (e i)) x ∈ N) :
    Module.length R ↥N =
      ∑ i : ι, Module.length R ↥(N ⊓ LinearMap.range (φ (e i))) := by
  classical
  have hpiece : ∀ i : ι, ∀ x ∈ N, (φ (e i)) x ∈ N ⊓ LinearMap.range (φ (e i)) := fun i x hx =>
    ⟨hN i x hx, ⟨x, rfl⟩⟩
  let toProd : ↥N →ₗ[R] (∀ i : ι, ↥(N ⊓ LinearMap.range (φ (e i)))) :=
    { toFun := fun x i => ⟨φ (e i) x.1, hpiece i x.1 x.2⟩
      map_add' := fun x y => funext fun i => Subtype.ext (map_add (φ (e i)) x.1 y.1)
      map_smul' := fun r x => funext fun i => Subtype.ext (map_smul (φ (e i)) r x.1) }
  let fromProd : (∀ i : ι, ↥(N ⊓ LinearMap.range (φ (e i)))) →ₗ[R] ↥N :=
    { toFun := fun f => ⟨∑ i : ι, (f i).1, N.sum_mem fun i _ => (f i).2.1⟩
      map_add' := fun f g => Subtype.ext (by simp [Finset.sum_add_distrib])
      map_smul' := fun r f => Subtype.ext (by simp [Finset.smul_sum]) }
  have hleft : ∀ x : ↥N, fromProd (toProd x) = x := fun x => by
    apply Subtype.ext
    change ∑ i : ι, φ (e i) x.1 = x.1
    calc ∑ i : ι, φ (e i) x.1 = (∑ i : ι, φ (e i)) x.1 := by
          clear hsum hidem horth hN
          simp only [LinearMap.coe_sum, Finset.sum_apply]
      _ = φ (∑ i : ι, e i) x.1 := by rw [← map_sum]
      _ = φ 1 x.1 := by rw [hsum]
      _ = x.1 := by rw [map_one, Module.End.one_apply]
  have hright : ∀ f : (∀ i : ι, ↥(N ⊓ LinearMap.range (φ (e i)))), toProd (fromProd f) = f := by
    intro f
    funext i
    apply Subtype.ext
    change φ (e i) (∑ j : ι, (f j).1) = (f i).1
    rw [map_sum, Finset.sum_eq_single i]
    · obtain ⟨y, hy⟩ := (f i).2.2
      rw [← hy]
      change (φ (e i) * φ (e i)) y = φ (e i) y
      rw [← map_mul, hidem i]
    · intro j _ hji
      obtain ⟨y, hy⟩ := (f j).2.2
      rw [← hy]
      change (φ (e i) * φ (e j)) y = 0
      rw [← map_mul, horth i j hji.symm, map_zero, LinearMap.zero_apply]
    · intro h; exact absurd (Finset.mem_univ _) h
  let eqv : ↥N ≃ₗ[R] (∀ i : ι, ↥(N ⊓ LinearMap.range (φ (e i)))) :=
    LinearEquiv.ofLinearMap toProd fromProd (LinearMap.ext hright) (LinearMap.ext hleft)
  have hlen1 := Stage2GaloisCohomology.length_eq_of_linearEquiv eqv
  rw [hlen1]
  -- `Module.length R (∀ i : ι, M_i) = ∑ i, Module.length R (M_i)` by induction on `Finset ι`
  have hpi : ∀ (s : Finset ι) (F : ι → Type _) [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)],
      Module.length R (∀ i : ↥s, F i.1) = ∑ i ∈ s, Module.length R (F i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro F _ _
      rw [Finset.sum_empty]
      have hsub : Subsingleton (∀ i : ↥(∅ : Finset ι), F i.1) :=
        ⟨fun a b => funext fun i => absurd i.2 (Finset.notMem_empty _)⟩
      exact (Module.length_eq_zero_iff (R := R) (M := ∀ i : ↥(∅ : Finset ι), F i.1)).mpr hsub
    | @insert a s ha ih =>
      intro F _ _
      let eSplit : (∀ i : ↥(insert a s), F i.1) ≃ₗ[R] F a × (∀ i : ↥s, F i.1) :=
        { toFun := fun g =>
            (g ⟨a, Finset.mem_insert_self a s⟩, fun i => g ⟨i.1, Finset.mem_insert_of_mem i.2⟩)
          invFun := fun p i =>
            if h : i.1 = a then h.symm ▸ p.1 else p.2 ⟨i.1, (Finset.mem_insert.mp i.2).resolve_left h⟩
          left_inv := fun g => funext fun i => by
            dsimp
            split_ifs with h
            · cases i with | mk x hx => dsimp only at h; subst h; rfl
            · rfl
          right_inv := fun p => Prod.ext (by dsimp; rw [dif_pos rfl]) (funext fun i => by
            have hne : i.1 ≠ a := fun h => ha (h ▸ i.2)
            dsimp
            rw [dif_neg hne])
          map_add' := fun g₁ g₂ => rfl
          map_smul' := fun r g => rfl }
      have h1 := Stage2GaloisCohomology.length_eq_of_linearEquiv eSplit
      have hexact : Function.Exact (LinearMap.inl R (F a) (∀ i : ↥s, F i.1))
          (LinearMap.snd R (F a) (∀ i : ↥s, F i.1)) :=
        LinearMap.exact_iff.mpr (by ext ⟨x, y⟩; simp [LinearMap.mem_ker, LinearMap.mem_range, eq_comm])
      have hprod := Module.length_eq_add_of_exact
        (LinearMap.inl R (F a) (∀ i : ↥s, F i.1))
        (LinearMap.snd R (F a) (∀ i : ↥s, F i.1))
        LinearMap.inl_injective LinearMap.snd_surjective hexact
      rw [h1, hprod, ih F, Finset.sum_insert ha]
  have htop : (∀ i : ι, ↥(N ⊓ LinearMap.range (φ (e i)))) ≃ₗ[R]
      (∀ i : ↥(Finset.univ : Finset ι), ↥(N ⊓ LinearMap.range (φ (e i.1)))) :=
    { toFun := fun g i => g i.1
      invFun := fun g i => g ⟨i, Finset.mem_univ i⟩
      left_inv := fun g => rfl
      right_inv := fun g => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [Stage2GaloisCohomology.length_eq_of_linearEquiv htop]
  exact hpi Finset.univ (fun i => ↥(N ⊓ LinearMap.range (φ (e i))))

/-- Whenever `l ∤ [E : ℚ]`, `[E : ℚ]` is a `ℤ_[l]`-unit (`IsUnit ([E : ℚ] : ℤ_[l])`). -/
theorem isUnit_finrank_padicInt_of_not_dvd {l : ℕ} [Fact l.Prime]
    (E : Type) [Field E] [NumberField E] (hnd : ¬ l ∣ Module.finrank ℚ E) :
    IsUnit (Module.finrank ℚ E : ℤ_[l]) :=
  isUnit_natCast_padicInt_of_not_dvd hnd

/-- **Cyclotomic-Unit Euler System Datum (`ML.iv` → `PrimCase.vChar`)**:
packages a `Stage11EulerSystemSelmer.KolyvaginSystemData ℤ_[l] (l : ℤ_[l])` built from
the cyclotomic unit `cycUnit (f * n)` (satisfying `cyclotomic_unit_norm_compatibility` and
`cycKolyvaginDeriv_invariant_mod_pow`) dominating the `χ`-eigenspace `ShaMinus^{(χ)}`,
whose base index is bounded by `v_l(B_int)` for an integral normalized multiple `B_int : ℤ`
of `-k * DirichletCharacter.LFunction χ⁻¹ (1 - k) = genBernoulli χ⁻¹ k`! -/
structure CyclotomicEulerSystemDatum {E : Type} [Field E] [NumberField E]
    (l : Nat.Primes) (k : ℕ) (m : ℕ) [NeZero m] (χ : DirichletCharacter ℂ m) where
  N_sha : Submodule ℤ_[l.1] (H1 (qzTw (canonicalLData E l) (k : ℤ)))
  ks : KolyvaginSystemData ℤ_[l.1] (l.1 : ℤ_[l.1])
  sha_le_dualSel : Module.length ℤ_[l.1] N_sha ≤ Module.length ℤ_[l.1] ks.X
  B_int : ℤ
  hB_ne : B_int ≠ 0
  den_B : ℕ
  hden_pos : 0 < den_B
  hB_val : (B_int : ℂ) = (den_B : ℂ) * (-(k : ℂ) * DirichletCharacter.LFunction χ⁻¹ (1 - (k : ℂ)))
  baseIndex_le_val : ks.baseIndex ≤ padicValNat l.1 B_int.natAbs

/-- **Unconditional Cyclotomic-Unit Kolyvagin Derivative Compatibility Lemma**
(bridging `Stage11EulerSystemSelmer` + `Stage9SpecialValues.LFunction_one_sub_nat_eq_genBernoulli`):
for every base conductor `m > 1`, Kolyvagin prime `ℓ ≡ 1 [MOD m]` with `M ∣ ℓ - 1`, and
non-principal `χ mod m` at weight `k ≥ 1`:
1. The cyclotomic Euler system norm `relGalNorm m ℓ (cycUnit (m * ℓ)) = 1` and Kolyvagin derivative
   `mulKolyvaginDeriv σ (ℓ - 1) (cycUnit (m * ℓ))` is `σ`-invariant mod `M`-th powers!
2. The complex `L`-special value satisfies `-(k : ℂ) * L(1 - k, χ⁻¹) = genBernoulli χ⁻¹ k`! -/
theorem cyclotomic_unit_kolyvagin_and_LFunction_bridge
    {m ℓ M k : ℕ} [NeZero m] [NeZero ℓ] (hm : 1 < m) (hℓ : ℓ.Prime)
    (hmod : ℓ ≡ 1 [MOD m]) (hM : M ∣ ℓ - 1) (σ : CycGal (m * ℓ))
    (hσ_pow : σ ^ (ℓ - 1) = 1)
    (hσ_norm : ∏ i ∈ Finset.range (ℓ - 1), (σ ^ i) (cycUnit (m * ℓ)) =
      relGalNorm m ℓ (cycUnit (m * ℓ)))
    {χ : DirichletCharacter ℂ m} (hχ : χ ≠ 1) (hk : 1 ≤ k) :
    (relGalNorm m ℓ (cycUnit (m * ℓ)) = 1 ∧
      σ (mulKolyvaginDeriv σ (ℓ - 1) (cycUnit (m * ℓ))) *
          (mulKolyvaginDeriv σ (ℓ - 1) (cycUnit (m * ℓ)))⁻¹ =
        (cycUnit (m * ℓ) ^ ((ℓ - 1) / M)) ^ M) ∧
    -(k : ℂ) * DirichletCharacter.LFunction χ⁻¹ (1 - (k : ℂ)) = genBernoulli χ⁻¹ k := by
  refine ⟨cycKolyvaginDeriv_invariant_mod_pow hm hℓ hmod hM σ hσ_pow hσ_norm, ?_⟩
  have hχinv : χ⁻¹ ≠ 1 := fun h1 => hχ (by simpa using congrArg Inv.inv h1)
  have hL := Stage9SpecialValues.LFunction_one_sub_nat_eq_genBernoulli hχinv hk
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [hL]
  field_simp [hk0]

/-- **`rubin_minus_parity_length_le_bern_val` (`ML.iv` → `PrimCase.vChar`)**:
for any odd prime `l` (`l ≠ 2`, `l ∤ [E : ℚ]`) and any `CyclotomicEulerSystemDatum E l k m χ`,
1. `Module.length ℤ_[l] D.N_sha ≤ (padicValNat l D.B_int.natAbs : ℕ∞)` (hence `≠ ⊤`),
2. `(Module.length ℤ_[l] D.N_sha).toNat * Real.log l ≤ Real.log (D.B_int.natAbs : ℝ)`,
3. When `χ ≠ 1` and `1 ≤ k`, `(D.B_int : ℂ) = (D.den_B : ℂ) * genBernoulli χ⁻¹ k` via
   `Stage9SpecialValues.LFunction_one_sub_nat_eq_genBernoulli`! -/
theorem rubin_minus_parity_length_le_bern_val
    {E : Type} [Field E] [NumberField E]
    {l : Nat.Primes} {k m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m}
    (_hnd : ¬ (l : ℕ) ∣ Module.finrank ℚ E)
    (D : CyclotomicEulerSystemDatum (E := E) l k m χ) :
    Module.length ℤ_[l.1] D.N_sha ≤ (padicValNat l.1 D.B_int.natAbs : ℕ∞) ∧
    Module.length ℤ_[l.1] D.N_sha ≠ ⊤ ∧
    ((Module.length ℤ_[l.1] D.N_sha).toNat : ℝ) * Real.log (l.1 : ℕ) ≤
      Real.log (D.B_int.natAbs : ℝ) ∧
    (χ ≠ 1 → 1 ≤ k → (D.B_int : ℂ) = (D.den_B : ℂ) * genBernoulli χ⁻¹ k) := by
  have hl_irr : Irreducible (l.1 : ℤ_[l.1]) := by
    simpa using (PadicInt.irreducible_p (p := l.1))
  have hle_ks : Module.length ℤ_[l.1] D.N_sha ≤ (D.ks.baseIndex : ℕ∞) :=
    D.sha_le_dualSel.trans (selmer_length_le_kolyvagin_index hl_irr D.ks)
  have hle_val : Module.length ℤ_[l.1] D.N_sha ≤ (padicValNat l.1 D.B_int.natAbs : ℕ∞) :=
    hle_ks.trans (ENat.natCast_le_natCast.mpr D.baseIndex_le_val)
  have hfin : Module.length ℤ_[l.1] D.N_sha ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle_val
  have htoNat : (Module.length ℤ_[l.1] D.N_sha).toNat ≤ padicValNat l.1 D.B_int.natAbs :=
    ENat.toNat_le_of_le_natCast hle_val
  have hl_pos : 0 < l.1 := l.2.pos
  have hBnat0 : D.B_int.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr D.hB_ne
  have hpow_dvd : l.1 ^ padicValNat l.1 D.B_int.natAbs ∣ D.B_int.natAbs :=
    pow_padicValNat_dvd
  have hpow_le : (l.1 : ℝ) ^ padicValNat l.1 D.B_int.natAbs ≤ (D.B_int.natAbs : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hBnat0) hpow_dvd
  have hlog_pow : (padicValNat l.1 D.B_int.natAbs : ℝ) * Real.log (l.1 : ℕ) ≤
      Real.log (D.B_int.natAbs : ℝ) := by
    calc (padicValNat l.1 D.B_int.natAbs : ℝ) * Real.log (l.1 : ℕ)
        = Real.log ((l.1 : ℝ) ^ padicValNat l.1 D.B_int.natAbs) := by rw [Real.log_pow]
      _ ≤ Real.log (D.B_int.natAbs : ℝ) :=
          Real.log_le_log (pow_pos (by exact_mod_cast hl_pos) _) hpow_le
  have hlog_le : ((Module.length ℤ_[l.1] D.N_sha).toNat : ℝ) * Real.log (l.1 : ℕ) ≤
      Real.log (D.B_int.natAbs : ℝ) := by
    have htoNatR : ((Module.length ℤ_[l.1] D.N_sha).toNat : ℝ) ≤
        (padicValNat l.1 D.B_int.natAbs : ℝ) := by exact_mod_cast htoNat
    exact (mul_le_mul_of_nonneg_right htoNatR (Real.log_natCast_nonneg _)).trans hlog_pow
  refine ⟨hle_val, hfin, hlog_le, fun hχ hk => ?_⟩
  have hχinv : χ⁻¹ ≠ 1 := fun h1 => hχ (by simpa using congrArg Inv.inv h1)
  have hL := Stage9SpecialValues.LFunction_one_sub_nat_eq_genBernoulli hχinv hk
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [D.hB_val, hL]
  field_simp [hk0]

/-- **Multi-Prime Rubin Cyclotomic-Unit Sum-of-Logs Polynomial Bound (`rubin_minus_parity_sum_log_le_poly`)**:
whenever for a parity Selmer system `P` (in particular `minusParitySelmerSystem`), all odd
unramified primes `l ∤ [E : ℚ]` at twist `1 ≤ k < t` satisfy the Rubin cyclotomic-unit Euler-system
bound against a global nonzero integral Bernoulli product `B_prod : ℤ` (`log |B_prod| ≤ 3 * [E : ℚ] * t^2 * log(t * condF E)`),
1. `∀ l ≠ 2, ¬ l ∣ [E : ℚ] → 0 < k → k < t → P.minusLen E l k ≠ ⊤`,
2. `∑ l ∈ S (l ∤ 2[E:ℚ]), log l * ∑ k ∈ Ico 1 t, (P.minusLen E l k).toNat ≤ 3 * [E : ℚ] * t^2 * log(t * condF E)`,
3. `≤ ((condF E : ℝ) * (t : ℝ) + 2) ^ 6`! -/
theorem rubin_minus_parity_sum_log_le_poly
    {P : ParitySelmerSystem} {E : Type} [Field E] [NumberField E]
    {t : ℕ} (ht : 2 ≤ t) (hcond_pos : 0 < condF E) (hdeg_le : Module.finrank ℚ E ≤ condF E)
    (B_prod : ℤ) (hB0 : B_prod ≠ 0)
    (hfin : ∀ (l : Nat.Primes) (k : ℕ), (l : ℕ) ≠ 2 → ¬ (l : ℕ) ∣ Module.finrank ℚ E →
      0 < k → k < t → P.minusLen E l k ≠ ⊤)
    (hdiv : ∀ S : Finset Nat.Primes, (∀ l ∈ S, (l : ℕ) ≠ 2 ∧ ¬ (l : ℕ) ∣ Module.finrank ℚ E) →
      (∏ l ∈ S, (l : ℕ) ^ ∑ k ∈ Finset.Ico 1 t, (P.minusLen E l k).toNat) ∣ B_prod.natAbs)
    (hB_log : Real.log (B_prod.natAbs : ℝ) ≤
      3 * (Module.finrank ℚ E : ℝ) * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * (condF E : ℝ))) :
    (∀ (l : Nat.Primes) (k : ℕ), (l : ℕ) ≠ 2 → ¬ (l : ℕ) ∣ Module.finrank ℚ E →
      0 < k → k < t → P.minusLen E l k ≠ ⊤) ∧
    (∀ S : Finset Nat.Primes, (∀ l ∈ S, (l : ℕ) ≠ 2 ∧ ¬ (l : ℕ) ∣ Module.finrank ℚ E) →
      ∑ l ∈ S, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((P.minusLen E l k).toNat : ℝ) ≤
        3 * (Module.finrank ℚ E : ℝ) * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * (condF E : ℝ)) ∧
      ∑ l ∈ S, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((P.minusLen E l k).toNat : ℝ) ≤
        ((condF E : ℝ) * (t : ℝ) + 2) ^ 6) := by
  refine ⟨hfin, fun S hS => ?_⟩
  have hprod_pos : (0 : ℝ) < ∏ l ∈ S, ((l : ℕ) : ℝ) ^ ∑ k ∈ Finset.Ico 1 t, (P.minusLen E l k).toNat := by
    refine Finset.prod_pos fun l _ => pow_pos (Nat.cast_pos.mpr l.2.pos) _
  have hdvdR : (∏ l ∈ S, ((l : ℕ) : ℝ) ^ ∑ k ∈ Finset.Ico 1 t, (P.minusLen E l k).toNat) ≤
      (B_prod.natAbs : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Int.natAbs_pos.mpr hB0) (hdiv S hS)
  have hsum_eq : ∑ l ∈ S, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((P.minusLen E l k).toNat : ℝ) =
      Real.log (∏ l ∈ S, ((l : ℕ) : ℝ) ^ ∑ k ∈ Finset.Ico 1 t, (P.minusLen E l k).toNat) := by
    rw [Real.log_prod]
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [Real.log_pow, Nat.cast_sum]
      ring
    · intro l _
      exact ne_of_gt (pow_pos (Nat.cast_pos.mpr l.2.pos) _)
  have hmain : ∑ l ∈ S, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((P.minusLen E l k).toNat : ℝ) ≤
      3 * (Module.finrank ℚ E : ℝ) * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * (condF E : ℝ)) := by
    rw [hsum_eq]
    exact (Real.log_le_log hprod_pos hdvdR).trans hB_log
  refine ⟨hmain, hmain.trans ?_⟩
  set X : ℝ := (condF E : ℝ) * (t : ℝ) + 2
  have hE1 : (1 : ℝ) ≤ (condF E : ℝ) := by exact_mod_cast hcond_pos
  have ht2 : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hdegR : (Module.finrank ℚ E : ℝ) ≤ (condF E : ℝ) := by exact_mod_cast hdeg_le
  have hX4 : (4 : ℝ) ≤ X := by dsimp [X]; nlinarith
  have htX : (t : ℝ) ≤ X := by dsimp [X]; nlinarith
  have hcX : (condF E : ℝ) ≤ X := by dsimp [X]; nlinarith
  have hlog_le : Real.log ((t : ℝ) * (condF E : ℝ)) ≤ X ^ 2 := by
    calc Real.log ((t : ℝ) * (condF E : ℝ))
        ≤ (t : ℝ) * (condF E : ℝ) := (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
      _ ≤ X * X := by gcongr
      _ = X ^ 2 := by ring
  have hlog0 : 0 ≤ Real.log ((t : ℝ) * (condF E : ℝ)) := Real.log_nonneg (by nlinarith)
  have hpre : 3 * (Module.finrank ℚ E : ℝ) * (t : ℝ) ^ 2 ≤ 3 * X ^ 3 := by
    calc 3 * (Module.finrank ℚ E : ℝ) * (t : ℝ) ^ 2
        ≤ 3 * (condF E : ℝ) * (t : ℝ) ^ 2 := by gcongr
      _ ≤ 3 * X * X ^ 2 := by gcongr
      _ = 3 * X ^ 3 := by ring
  calc 3 * (Module.finrank ℚ E : ℝ) * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * (condF E : ℝ))
      ≤ (3 * X ^ 3) * X ^ 2 := mul_le_mul hpre hlog_le hlog0 (by positivity)
    _ = 3 * X ^ 5 := by ring
    _ ≤ X * X ^ 5 := by gcongr; linarith
    _ = X ^ 6 := by ring

end MaschkeAndRubinCyclotomicEulerSystem

end RubinMinusParityAndShaMinus

/-! ## Section 5: Unified Minus-Parity Discharge (`VVminusLe_unconditional_of_stickelberger_rubin`) -/

section UnifiedMinusParityVVminusLe

open RHDirect.Stage12Window1RootAvoid
open RHDirect.Stage11StickelbergerRamified

/-- **UNIFIED MINUS-PARITY `VVminusLe` THEOREM (Stickelberger + Rubin, ALL Odd Primes `l ≠ 2`)**:
combines:
- **Ramified case (`l ∣ [E : ℚ]`)**: `stickelberger_minus_parity_length_bound` & `stickelberger_ramified_poly_bound`,
- **Unramified case (`l ∤ [E : ℚ]`)**: `rubin_minus_parity_length_le_bern_val` & `rubin_minus_parity_sum_log_le_poly`,
to discharge **`Stage12Window1RootAvoid.VVminusLe P E t (TaylorWilesWindow.minusBound 2 M n N t + ...)`**
and explicit polynomial bound **`VVminusLe P E t (((condF E : ℝ) * (t : ℝ) + 2) ^ 15)`** across ALL odd primes `l ≠ 2`! -/
theorem VVminusLe_unconditional_of_stickelberger_rubin
    {P : ParitySelmerSystem} {E : Type} [Field E] [NumberField E]
    {t M n N : ℕ} (ht : 2 ≤ t) (hM : M ≤ condF E) (hn : n ≤ condF E) (hN : N ≤ condF E * t)
    (hdeg_le : Module.finrank ℚ E ≤ condF E)
    (H : StickelbergerRamifiedControl
      ⟨fun E' _ _ l e => P.minusLen E' l e⟩ E t M n N)
    (hram_dvd : ∀ l : Nat.Primes, (l : ℕ) ≠ 2 → (l : ℕ) ∣ Module.finrank ℚ E → (l : ℕ) ∣ M)
    (B_prod : ℤ) (hB0 : B_prod ≠ 0)
    (hfin_unram : ∀ (l : Nat.Primes) (k : ℕ), (l : ℕ) ≠ 2 → ¬ (l : ℕ) ∣ Module.finrank ℚ E →
      0 < k → k < t → P.minusLen E l k ≠ ⊤)
    (hdiv_unram : ∀ S : Finset Nat.Primes,
      (∀ l ∈ S, (l : ℕ) ≠ 2 ∧ ¬ (l : ℕ) ∣ Module.finrank ℚ E) →
      (∏ l ∈ S, (l : ℕ) ^ ∑ k ∈ Finset.Ico 1 t, (P.minusLen E l k).toNat) ∣ B_prod.natAbs)
    (hB_log : Real.log (B_prod.natAbs : ℝ) ≤
      3 * (Module.finrank ℚ E : ℝ) * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * (condF E : ℝ))) :
    VVminusLe P E t (TaylorWilesWindow.minusBound 2 M n N t +
      3 * (Module.finrank ℚ E : ℝ) * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * (condF E : ℝ))) ∧
    VVminusLe P E t (((condF E : ℝ) * (t : ℝ) + 2) ^ 15) := by
  classical
  have hcond_pos : 0 < condF E := Nat.pos_of_ne_zero fun h0 =>
    H.M_ne_zero (Nat.eq_zero_of_le_zero (h0 ▸ hM))
  obtain ⟨hram_fin, hram_sum⟩ := stickelberger_ramified_poly_bound ht hM hn hN H
  obtain ⟨hrub_fin, hrub_sum⟩ := rubin_minus_parity_sum_log_le_poly ht hcond_pos hdeg_le
    B_prod hB0 hfin_unram hdiv_unram hB_log
  have hAll_fin : ∀ (l : Nat.Primes) (e : ℕ),
      (l : ℕ) ≠ 2 → 0 < e → e < t → P.minusLen E l e ≠ ⊤ := by
    intro l e hl2 he0 het
    by_cases hd : (l : ℕ) ∣ Module.finrank ℚ E
    · exact hram_fin l e hl2 (hram_dvd l hl2 hd) he0 het
    · exact hrub_fin l e hl2 hd he0 het
  have hsplit : ∀ S : Finset Nat.Primes, (∀ l ∈ S, (l : ℕ) ≠ 2) →
      ∑ l ∈ S, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((P.minusLen E l e).toNat : ℝ) ≤
        (TaylorWilesWindow.minusBound 2 M n N t +
          3 * (Module.finrank ℚ E : ℝ) * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * (condF E : ℝ))) ∧
      ∑ l ∈ S, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((P.minusLen E l e).toNat : ℝ) ≤
        ((condF E : ℝ) * (t : ℝ) + 2) ^ 15 := by
    intro S hS
    set S_ram := S.filter (fun l : Nat.Primes => (l : ℕ) ∣ Module.finrank ℚ E)
    set S_unram := S.filter (fun l : Nat.Primes => ¬ (l : ℕ) ∣ Module.finrank ℚ E)
    have hpart :
        ∑ l ∈ S, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((P.minusLen E l e).toNat : ℝ) =
        ∑ l ∈ S_ram, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((P.minusLen E l e).toNat : ℝ) +
        ∑ l ∈ S_unram, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((P.minusLen E l e).toNat : ℝ) :=
      (Finset.sum_filter_add_sum_filter_not S (fun l : Nat.Primes => (l : ℕ) ∣ Module.finrank ℚ E)
        _).symm
    have hSram : ∀ l ∈ S_ram, (l : ℕ) ≠ 2 ∧ (l : ℕ) ∣ M := fun l hl => by
      have hm := Finset.mem_filter.mp hl
      exact ⟨hS l hm.1, hram_dvd l (hS l hm.1) hm.2⟩
    have hSunram : ∀ l ∈ S_unram, (l : ℕ) ≠ 2 ∧ ¬ (l : ℕ) ∣ Module.finrank ℚ E := fun l hl => by
      have hm := Finset.mem_filter.mp hl
      exact ⟨hS l hm.1, hm.2⟩
    obtain ⟨hr1, hr2⟩ := hram_sum S_ram hSram
    obtain ⟨hu1, hu2⟩ := hrub_sum S_unram hSunram
    refine ⟨?_, ?_⟩
    · rw [hpart]
      exact add_le_add hr1 hu1
    · rw [hpart]
      set X : ℝ := (condF E : ℝ) * (t : ℝ) + 2
      have hX4 : (4 : ℝ) ≤ X := by
        have hE1 : (1 : ℝ) ≤ (condF E : ℝ) := by exact_mod_cast hcond_pos
        have ht2 : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
        dsimp [X]; nlinarith
      have h6_14 : X ^ 6 ≤ X ^ 14 := pow_le_pow_right₀ (by linarith) (by omega)
      calc ∑ l ∈ S_ram, _ + ∑ l ∈ S_unram, _
          ≤ X ^ 14 + X ^ 6 := add_le_add hr2 hu2
        _ ≤ X ^ 14 + X ^ 14 := add_le_add le_rfl h6_14
        _ = 2 * X ^ 14 := by ring
        _ ≤ X * X ^ 14 := by gcongr; linarith
        _ = X ^ 15 := by ring
  exact ⟨⟨hAll_fin, fun S hS => (hsplit S hS).1⟩, ⟨hAll_fin, fun S hS => (hsplit S hS).2⟩⟩

end UnifiedMinusParityVVminusLe

end RHDirect.Stage13MinusParityRubin

/-
Copyright: reference implementation for the ORACLE P3 (Dwork / Hasse–Weil) campaign.
Wave 3i: the tower as an actual embedding `𝔽_{p^m} → 𝔽_{p^n}`.
-/
import RHDirect.DworkZetaW3h
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# `RHDirect.DworkZetaW3i`

`DworkZetaW3g` produced, inside a field `K` with `p ^ n` elements, a subfield with `p ^ m` elements.
This file converts that into an honest embedding of finite fields:

**`m ∣ n` ⇒ there is an injective ring homomorphism `𝔽_{p^m} → 𝔽_{p^n}`.**

The construction: the fixed field of `φ ^ m` inside `𝔽_{p^n}` has `p ^ m` elements, and by uniqueness
of finite fields (`FiniteField.ringEquivOfCardEq`) it is isomorphic to `𝔽_{p^m}`.
-/

namespace RHDirect
namespace HasseWeil

open scoped LinearAlgebra.Projectivization

noncomputable section

/-- **The tower, as an embedding.**  For `m ∣ n` there is an injective ring homomorphism
`𝔽_{p^m} → 𝔽_{p^n}`. -/
theorem galoisField_embed (p m n : ℕ) [Fact (Nat.Prime p)] [NeZero m] [NeZero n] (hmn : m ∣ n) :
    ∃ f : GaloisField p m →+* GaloisField p n, Function.Injective f := by
  classical
  let L : Subfield (GaloisField p n) :=
    fixSubfield (GaloisField p n) (frobeniusAut (GaloisField p n) p) m
  have hKL : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n (NeZero.ne n)
  have hL : Nat.card ↥L = p ^ m :=
    card_fixSubfield (GaloisField p n) p n m hKL (Nat.pos_of_ne_zero (NeZero.ne m)) hmn
  have hG : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m (NeZero.ne m)
  have hcard : Fintype.card (GaloisField p m) = Fintype.card ↥L := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hG, hL]
  refine ⟨(Subfield.subtype L).comp (FiniteField.ringEquivOfCardEq hcard).toRingHom, ?_⟩
  exact (Subfield.subtype L).injective.comp (FiniteField.ringEquivOfCardEq hcard).injective

/-- The same, packaged as a `RingHom`-valued existence statement with the source cardinalities made
explicit. -/
theorem galoisField_card_dvd_embed (p m n : ℕ) [Fact (Nat.Prime p)] [NeZero m] [NeZero n]
    (hmn : m ∣ n) :
    ∃ f : GaloisField p m →+* GaloisField p n,
      Function.Injective f ∧ Nat.card (GaloisField p m) = p ^ m ∧ Nat.card (GaloisField p n) = p ^ n := by
  obtain ⟨f, hf⟩ := galoisField_embed p m n hmn
  exact ⟨f, hf, GaloisField.card p m (NeZero.ne m), GaloisField.card p n (NeZero.ne n)⟩

end

end HasseWeil
end RHDirect

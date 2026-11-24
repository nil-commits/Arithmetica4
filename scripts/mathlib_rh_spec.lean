import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Isolated Mathlib-Only Specification of the Five Target RH / GRH Statements

This module imports **ONLY Mathlib** (`Mathlib.NumberTheory.LSeries.RiemannZeta` and
`Mathlib.NumberTheory.LSeries.DirichletContinuation`) and **ZERO `RHDirect` modules**.
It serves as the trusted independent reference specification for `scripts/mathlib_rh_compare.lean`
(mirroring `comparator` / `con-leche --compare`), preventing any definition shadowing or
unintended weakening of the headline theorem statements.
-/

namespace MathlibRHSpec

/-- Target 1: Mathlib's canonical `RiemannHypothesis` verbatim. -/
def SpecRiemannHypothesis : Prop :=
  _root_.RiemannHypothesis

/-- Target 2: Explicit statement of RH for nontrivial zeros of `riemannZeta`. -/
def SpecRiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, _root_.riemannZeta s = 0 →
    (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2

/-- Target 3: Nonvanishing of all Dirichlet L-functions in `Re(s) > 1/2`. -/
def SpecDirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : _root_.DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → _root_.DirichletCharacter.LFunction χ s ≠ 0

/-- Target 4: All critical-strip zeros of any Dirichlet L-function lie on `Re(s) = 1/2`. -/
def SpecDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : _root_.DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → _root_.DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- Target 5: All critical-strip zeros of any primitive Dirichlet L-function lie on `Re(s) = 1/2`. -/
def SpecPrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : _root_.DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → _root_.DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

end MathlibRHSpec

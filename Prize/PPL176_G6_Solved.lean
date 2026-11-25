import Prize.PPL176_G5
import Prize.PPL176_G6
import Prize.PPL176_G6_FromG5

/-!
# PPL 176 (Erdős Problem #708) — Unconditional Settlement `g(6) = 8` and `g(1)..g(6)`

Combining the unconditional `n = 5` upper bound `erdos708_upper_five : SatisfiesBound 5 6`
(`Prize.PPL176_G5`), the unconditional `g(5) ≤ 6 → g(6) ≤ 8` reduction
`erdos708_upper_six_of_upper_five` (`Prize.PPL176_G6_FromG5`), and the sharp lower bound
`erdos708_lower_six_sharp : ¬ SatisfiesBound 6 7` (`Prize.PPL176_G6`), this module settles
`g(6) = 8` and packages the exact values `g(1)..g(6)`.
-/

namespace PPL176

theorem erdos708_upper_six : SatisfiesBound 6 8 :=
  erdos708_upper_six_of_upper_five erdos708_upper_five

theorem erdos708_exact_six : SatisfiesBound 6 8 ∧ ¬ SatisfiesBound 6 7 :=
  ⟨erdos708_upper_six, erdos708_lower_six_sharp⟩

theorem erdos708_exact_one_through_six :
    (SatisfiesBound 1 1 ∧ ¬ SatisfiesBound 1 0) ∧
    (SatisfiesBound 2 2 ∧ ¬ SatisfiesBound 2 1) ∧
    (SatisfiesBound 3 4 ∧ ¬ SatisfiesBound 3 3) ∧
    (SatisfiesBound 4 5 ∧ ¬ SatisfiesBound 4 4) ∧
    (SatisfiesBound 5 6 ∧ ¬ SatisfiesBound 5 5) ∧
    (SatisfiesBound 6 8 ∧ ¬ SatisfiesBound 6 7) :=
  ⟨erdos708_exact_one, erdos708_exact_two, erdos708_exact_three,
   erdos708_exact_four, erdos708_exact_five, erdos708_exact_six⟩

end PPL176

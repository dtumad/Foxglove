module

public import Foxglove.Interp.Bernoulli.Helper

/-! # Uniform sampling by rejection on coin flips

`split n` samples uniformly from `Fin (n + 1)` using biased coins: from `m` upwards, report `m`
with probability `1/(n + 1 - m)` and otherwise move on to `m + 1`.

* `lawOf_split'`: rejection sampling from `m` upwards is uniform on `{m, …, n - 1}`;
* `lawOf_split`: `split n` is uniform on `Fin (n + 1)`.
-/

@[expose] public section
namespace Foxglove

namespace Interp

open ProbSpace unitInterval Helper
open scoped ENNReal

/-- Rejection sampling from `m` upwards: uniform on `{m, …, n - 1}` (`lawOf_split'`). -/
def split' {n : ℕ} (m : Fin n) : BernoulliM (Fin n) := do
  if h₁ : n = m.1 + 1
    then pure m
    else
      let b ← flip
        ⟨
          (mkRat 1 (n - m.1) : ℝ),
          by
            simp only [Set.mem_Icc, Rat.cast_nonneg, zero_le_one, Rat.mkRat_nonneg, true_and]
            norm_cast
            refine Rat.num_le_denom_iff.mp ?_
            unfold mkRat
            split_ifs with h
            · simp
            · simp only [Rat.num_normalize, isUnit_one, Int.natAbs_of_isUnit, Fin.is_le',
              isUnit_iff_eq_one, IsUnit.dvd, Nat.gcd_sub_left_right_of_dvd, Nat.gcd_one_left,
              Nat.cast_one, ne_eq, one_ne_zero, not_false_eq_true, EuclideanDomain.div_self,
              Rat.den_normalize, Nat.div_one, Nat.cast_sub]
              omega⟩
      if b
        then pure m
        else split' (⟨m.1 + 1, (by omega)⟩ : Fin n)
termination_by n - m.1
decreasing_by have := m.isLt; omega

/-- A uniform sample from `Fin (n + 1)` by rejection sampling on coin flips (`lawOf_split`). -/
def split (n : ℕ) : BernoulliM (Fin (n + 1)) :=
  split' (0 : Fin (n + 1))

/-- **Rejection sampling from `m` upwards is uniform on `{m, …, n-1}`**, as a law. -/
lemma lawOf_split' {n : ℕ} (m i : Fin n) :
    ProbTree.lawOf (split' m) i = if m ≤ i then ((n - m.1 : ℕ) : ℝ≥0∞)⁻¹ else 0 := by
  have hi := i.isLt
  induction m using split'.induct with
  | case1 m h₁ =>
    -- the last outcome: no flip left, report `m`
    have hsplit : split' m = (PFunctor.FreeM.pure m : BernoulliM (Fin n)) := by
      rw [split', dite_eq_left h₁]
      rfl
    rw [hsplit, ProbTree.lawOf_pure]
    by_cases hmi : i = m
    · subst hmi; simp [show n - i.1 = 1 by omega]
    · rw [ite_eq_right hmi, ite_eq_right (by rw [Fin.le_def]; omega)]
  | case2 m h₁ ih =>
    -- flip: report `m` with probability `1/(n - m)`, else recurse from `m + 1`
    have hm'lt : m.1 + 1 < n := by omega
    set P : I := ⟨(↑(mkRat 1 (n - m.1)) : ℝ), mkRat_mem_I (by omega)⟩
    have hP : (unitInterval.toNNReal P : ℝ≥0∞) = ((n - m.1 : ℕ) : ℝ≥0∞)⁻¹ :=
      toNNReal_mkRat (n - m.1) (by omega) _
    have hsplit : split' m = PFunctor.FreeM.liftBind (BernoulliOps.Flip P)
        (fun b ↦ if b then (PFunctor.FreeM.pure m : BernoulliM (Fin n))
                 else split' ⟨m.1 + 1, hm'lt⟩) := by
      rw [split', dite_eq_right h₁]
      rfl
    rw [hsplit, ProbTree.lawOf_liftBind]
    simp only [ite_true, Bool.false_eq_true, ite_false, ProbTree.lawOf_pure, ih,
      ProbTree.flipWeight, hP, Fin.le_def, Fin.ext_iff]
    rcases lt_trichotomy i.1 m.1 with hlt | heq | hgt
    · simp [hlt.ne, hlt.not_ge, show ¬ m.1 + 1 ≤ i.1 by omega]
    · simp [heq]
    · -- having failed with probability `1 - 1/(n - m)`, the rest is uniform on `n - m - 1`
      rw [ite_eq_right hgt.ne', ite_eq_left (by omega), ite_eq_left hgt.le, mul_zero, zero_add,
        show n - (m.1 + 1) = (n - m.1) - 1 by omega]
      exact mix_step (n - m.1) (by omega)

/-- **`split n` is uniform on `Fin (n + 1)`**, as a law. -/
lemma lawOf_split (n : ℕ) (i : Fin (n + 1)) :
    ProbTree.lawOf (split n) i = ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
  simp [split, lawOf_split']

end Interp

end Foxglove

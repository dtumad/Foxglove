module

public import Foxglove.Interp.Bernoulli.Helper
public import Foxglove.Interp.Bernoulli.Split


@[expose] public section
namespace Foxglove

namespace Interp

open ProbSpace

open unitInterval
open Helper

section Example

open MeasureTheory
open scoped ENNReal NNReal Classical

def xorTest : BernoulliM Bool := do
  let b₀ ← flip half
  let b₁ ← flip half
  pure (Bool.xor b₀ b₁)

def flipTest1 (a b : I) : BernoulliM (Bool × Bool) := do
  let o₀ ← flip a
  let o₁ ← flip b
  pure (o₀, o₁)

def flipTest2 (a b : I) : BernoulliM (Bool × Bool) := do
  let o₁ ← flip b
  let o₀ ← flip a
  pure (o₀, o₁)

section Flip

open ProbTree

/-- A single flip reports its own bit, so its distribution is `PSp.bernoulli p`. -/
lemma flip_dist {p : I} : outputPSp (interp_psp (flip p)) = PSp.bernoulli p := by
  rw [outputPSp_interp (flip p) (fixpoint_oneFlip (fun b ↦ b) p)
    (reports_oneFlipTree (fun b ↦ b))]
  refine congrArg Option.some (map_eq_of_singletons
    (reports_oneFlipTree (fun b ↦ b)).measurableSet_preimage rfl (fun a ↦ ?_))
  rw [preimage_head,
    ProbTree.flipMeasure_apply_singleton p a (measurableSet_prefixEqEvent_singleton a),
    bernoulli_μ_singleton]

end Flip

section XorTest

open ProbTree

/-- Both fair-flip weights are `1/2`. -/
lemma flipWeight_half (b : Bool) : ProbTree.flipWeight half b = (2⁻¹ : ℝ≥0∞) := by
  cases b
  · rw [ProbTree.flipWeight, ite_eq_right Bool.false_ne_true, halfNN_coe,
      ennreal_one_sub_inv_two]
  · rw [ProbTree.flipWeight, ite_eq_left rfl, halfNN_coe]

lemma xorTest_distr : outputPSp (interp_psp xorTest) = PSp.bernoulli half := by
  rw [outputPSp_interp xorTest (fixpoint_twoFlips Bool.xor half half)
    (reports_twoFlipTree Bool.xor)]
  refine congrArg Option.some (map_eq_of_singletons
    (reports_twoFlipTree Bool.xor).measurableSet_preimage rfl (fun a ↦ ?_))
  -- the two tapes that `xor` sends to `a` each have mass `1/4`
  have hsum : (2⁻¹ : ℝ≥0∞) * 2⁻¹ + 2⁻¹ * 2⁻¹ = 2⁻¹ := by
    rw [← two_mul, ← mul_assoc, ennreal_two_mul_inv_two, one_mul]
  cases a
  · rw [show (fun ρ : Ω ↦ Bool.xor (ρ 0) (ρ 1)) ⁻¹' {false}
        = prefixEqEvent [true, true] ∪ prefixEqEvent [false, false] by
      ext ρ; cases h0 : ρ 0 <;> cases h1 : ρ 1 <;>
        simp [ProbTree.mem_prefixEqEvent_pair, h0, h1]]
    rw [ProbTree.measure_union_atoms _ mem_prefixes_twoFlipTree mem_prefixes_twoFlipTree
        (by simp),
      twoFlipMeasure_apply, twoFlipMeasure_apply, bernoulli_μ_singleton,
      flipWeight_half, flipWeight_half]
    exact hsum
  · rw [show (fun ρ : Ω ↦ Bool.xor (ρ 0) (ρ 1)) ⁻¹' {true}
        = prefixEqEvent [true, false] ∪ prefixEqEvent [false, true] by
      ext ρ; cases h0 : ρ 0 <;> cases h1 : ρ 1 <;>
        simp [ProbTree.mem_prefixEqEvent_pair, h0, h1]]
    rw [ProbTree.measure_union_atoms _ mem_prefixes_twoFlipTree mem_prefixes_twoFlipTree
        (by simp),
      twoFlipMeasure_apply, twoFlipMeasure_apply, bernoulli_μ_singleton,
      flipWeight_half, flipWeight_half]
    exact hsum

/-- `xorTest` is therefore indistinguishable from a single fair flip. -/
lemma xorTest_eq_flip : outputPSp (interp_psp xorTest) = outputPSp (interp_psp (flip half)) := by
  rw [xorTest_distr, flip_dist]

end XorTest

section FlipCommuteTest

open ProbTree

-- flips commute

lemma preimage_swap (x y : Bool) :
    (fun ρ : Ω ↦ (ρ 1, ρ 0)) ⁻¹' {(x, y)} = prefixEqEvent [y, x] := by
  ext ρ
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.ext_iff,
    ProbTree.mem_prefixEqEvent_pair]
  tauto

lemma flip_comm_distr (a b : I) :
    outputPSp (interp_psp (flipTest1 a b)) = outputPSp (interp_psp (flipTest2 a b)) := by
  rw [outputPSp_interp (flipTest1 a b) (fixpoint_twoFlips (fun x y ↦ (x, y)) a b)
      (reports_twoFlipTree (fun x y ↦ (x, y))),
    outputPSp_interp (flipTest2 a b) (fixpoint_twoFlips (fun x y ↦ (y, x)) b a)
      (reports_twoFlipTree (fun x y ↦ (y, x)))]
  refine congrArg Option.some (map_eq_map_of_singletons
    (reports_twoFlipTree (fun x y ↦ (x, y))).measurableSet_preimage
    (reports_twoFlipTree (fun x y ↦ (y, x))).measurableSet_preimage (fun z ↦ ?_))
  obtain ⟨x, y⟩ := z
  rw [preimage_pair, preimage_swap, twoFlipMeasure_apply, twoFlipMeasure_apply, mul_comm]

end FlipCommuteTest

section SplitExample

open ProbTree

/-- Rejection sampling from `m` upwards is uniform on `{m, …, n-1}`. -/
lemma split'_spec {n : ℕ} : ∀ (k : ℕ) (m : Fin n), n - m.1 ≤ k →
    ∃ (t : ProbTree (Fin n)) (μ : Measure[t.ms] Ω) (g : Ω → Fin n),
      fixpoint (rootTree (split' m)) = ⟨t, μ⟩ ∧ ProbTree.Reports t g ∧
      ∀ i : Fin n, μ (g ⁻¹' {i}) = if m.1 ≤ i.1 then ((n - m.1 : ℕ) : ℝ≥0∞)⁻¹ else 0 := by
  intro k
  induction k with
  | zero =>
    intro m hk
    exact absurd m.isLt (by omega)
  | succ k ih =>
    intro m hk
    by_cases h₁ : n = m.1 + 1
    · -- the last outcome: no flip left, report `m`
      have hsplit : split' m = (PFunctor.FreeM.pure m : BernoulliM (Fin n)) := by
        rw [split', dite_eq_left h₁]
        rfl
      rw [hsplit]
      refine ⟨_, _, fun _ ↦ m, fixpoint_rootTree_pure m, reports_leaf_pure m, fun i ↦ ?_⟩
      have hi := i.isLt
      by_cases hmi : i = m
      · have hval : i.1 = m.1 := by rw [hmi]
        rw [show ((fun _ : Ω ↦ m) ⁻¹' {i}) = (Set.univ : Set Ω) by ext ρ; simp [hmi],
          ite_eq_left (by omega : m.1 ≤ i.1), show n - m.1 = 1 by omega, rootTree_univ]
        simp
      · have hne : i.1 ≠ m.1 := fun h ↦ hmi (Fin.ext h)
        rw [show ((fun _ : Ω ↦ m) ⁻¹' {i}) = (∅ : Set Ω) by ext ρ; simp [Ne.symm hmi],
          ite_eq_right (by omega : ¬ (m.1 ≤ i.1))]
        exact measure_empty
    · -- flip: report `m` with probability `1/(n - m)`, else recurse
      have hm'lt : m.1 + 1 < n := by have := m.isLt; omega
      have hK1 : 1 ≤ n - m.1 := by have := m.isLt; omega
      have hih : n - (m.1 + 1) ≤ k := by omega
      obtain ⟨t', μ', g', hfix', hrep', hmass'⟩ := ih ⟨m.1 + 1, hm'lt⟩ hih
      set P : I := ⟨(↑(mkRat 1 (n - m.1)) : ℝ), mkRat_mem_I hK1⟩ with hPdef
      have hP : (unitInterval.toNNReal P : ℝ≥0∞) = ((n - m.1 : ℕ) : ℝ≥0∞)⁻¹ := by
        rw [hPdef]
        exact toNNReal_mkRat (n - m.1) (by omega) _
      have hsplit : split' m = PFunctor.FreeM.liftBind (BernoulliOps.Flip P)
          (fun b ↦ if b then (PFunctor.FreeM.pure m : BernoulliM (Fin n))
                   else split' ⟨m.1 + 1, hm'lt⟩) := by
        rw [split', dite_eq_right h₁]
        rfl
      rw [hsplit]
      have hpeel := fixpoint_rootTree_liftBind₂ (BernoulliOps.Flip P)
        (fun b ↦ if b then (PFunctor.FreeM.pure m : BernoulliM (Fin n))
                 else split' ⟨m.1 + 1, hm'lt⟩)
        (PFunctor.FreeM.pure m) (split' ⟨m.1 + 1, hm'lt⟩) rfl rfl
      rw [fixpoint_rootTree_pure, hfix'] at hpeel
      have hrep := reports_node (reports_leaf_pure m) hrep'
      refine ⟨_, _, _, hpeel, hrep, fun i ↦ ?_⟩
      have hTpre : consFlip true ⁻¹' ((fun ρ : Ω ↦ if ρ 0 then m else g' (tailFlip ρ)) ⁻¹' {i})
          = (fun _ : Ω ↦ m) ⁻¹' {i} := by ext ρ; simp
      have hFpre : consFlip false ⁻¹' ((fun ρ : Ω ↦ if ρ 0 then m else g' (tailFlip ρ)) ⁻¹' {i})
          = g' ⁻¹' {i} := by ext ρ; simp
      rw [joinMeasure_smul_preimage _ _ _ _ hTpre hFpre (hrep.measurableSet_preimage {i}),
        hmass', ProbTree.flipWeight, ProbTree.flipWeight, ite_eq_left rfl,
        ite_eq_right Bool.false_ne_true, hP]
      have hi := i.isLt
      rcases lt_trichotomy i.1 m.1 with hlt | heq | hgt
      · have h1 : i ≠ m := fun h ↦ by rw [h] at hlt; omega
        rw [show ((fun _ : Ω ↦ m) ⁻¹' {i}) = (∅ : Set Ω) by ext ρ; simp [Ne.symm h1],
          measure_empty, ite_eq_right (by omega : ¬ (m.1 + 1 ≤ i.1)),
          ite_eq_right (by omega : ¬ (m.1 ≤ i.1))]
        simp
      · have h1 : i = m := Fin.ext heq
        rw [show ((fun _ : Ω ↦ m) ⁻¹' {i}) = (Set.univ : Set Ω) by ext ρ; simp [h1],
          rootTree_univ, ite_eq_right (by omega : ¬ (m.1 + 1 ≤ i.1)),
          ite_eq_left (by omega : m.1 ≤ i.1)]
        simp
      · have h1 : i ≠ m := fun h ↦ by rw [h] at hgt; omega
        rw [show ((fun _ : Ω ↦ m) ⁻¹' {i}) = (∅ : Set Ω) by ext ρ; simp [Ne.symm h1],
          measure_empty, ite_eq_left (by omega : m.1 + 1 ≤ i.1),
          ite_eq_left (by omega : m.1 ≤ i.1), mul_zero, zero_add,
          show n - (m.1 + 1) = (n - m.1) - 1 by omega]
        exact mix_step (n - m.1) (by omega)

lemma split_distr {n : ℕ} : outputPSp (interp_psp (split n)) = PSp.uniform n := by
  obtain ⟨t, μ, g, hfix, hrep, hmass⟩ := split'_spec (n + 1) (0 : Fin (n + 1)) (by omega)
  have : IsProbabilityMeasure μ := isProbabilityMeasure_of_fixpoint hfix
  rw [split, outputPSp_interp (split' (0 : Fin (n + 1))) hfix hrep]
  refine congrArg Option.some (map_eq_of_singletons hrep.measurableSet_preimage rfl (fun i ↦ ?_))
  rw [hmass i, PSpace.uniform_apply_singleton]
  simp

end SplitExample

end Example

end Interp

end Foxglove

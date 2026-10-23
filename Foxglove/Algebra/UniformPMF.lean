module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # Uniform laws as `PMF`s

Mathlib (since 2026-10-04) states its uniform distributions as measures
(`Measure.uniformOfFinset`).  Foxglove's laws are `PMF`s, so the two `PMF`-valued uniform laws
it uses are kept here: `PMF.uniformOfFinset`, which Mathlib no longer defines, and
`PMF.uniformOfFintype'`, primed because Mathlib's `PMF.uniformOfFintype` is now a deprecated
alias of the measure. -/

@[expose] public section

open scoped ENNReal
open Finset

namespace PMF

variable {α : Type*}

/-- The uniform law on a nonempty finset. -/
noncomputable def uniformOfFinset (s : Finset α) (hs : s.Nonempty) : PMF α := by
  classical
  refine ofFinset (fun a ↦ if a ∈ s then (#s : ℝ≥0∞)⁻¹ else 0) s ?_ fun x hx ↦ by simp [hx]
  simp [ENNReal.mul_inv_cancel, hs.ne_empty]

open scoped Classical in
@[simp]
theorem uniformOfFinset_apply {s : Finset α} (hs : s.Nonempty) (a : α) :
    uniformOfFinset s hs a = if a ∈ s then (#s : ℝ≥0∞)⁻¹ else 0 :=
  rfl

/-- The uniform law on a finite, nonempty type.  Primed because Mathlib's `PMF.uniformOfFintype`
is now a deprecated alias of the measure `Measure.uniformOfFinset`. -/
noncomputable def uniformOfFintype' (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  uniformOfFinset Finset.univ Finset.univ_nonempty

@[simp]
theorem uniformOfFintype'_apply [Fintype α] [Nonempty α] (a : α) :
    uniformOfFintype' α a = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  simp [uniformOfFintype']

/-! ### Uniform laws under maps and products -/

/-- A bijection carries the uniform law to the uniform law. -/
lemma uniformOfFintype'_map_of_bijective {α β : Type*} [Fintype α] [Nonempty α] [Fintype β]
    [Nonempty β] {e : α → β} (he : Function.Bijective e) :
    (uniformOfFintype' α).map e = uniformOfFintype' β := by
  refine PMF.ext fun b ↦ ?_
  obtain ⟨a, rfl⟩ := he.2 b
  rw [map_apply, tsum_eq_single a (fun a' ha' ↦ ite_eq_right fun h ↦ ha' (he.1 h.symm)),
    ite_eq_left rfl, uniformOfFintype'_apply, uniformOfFintype'_apply,
    Fintype.card_of_bijective he]

/-- Two independent uniform points make a uniform pair. -/
lemma uniformOfFintype'_bind_map_prod {α β : Type*} [Fintype α] [Nonempty α] [Fintype β]
    [Nonempty β] :
    (uniformOfFintype' α).bind (fun a ↦ (uniformOfFintype' β).map (Prod.mk a))
      = uniformOfFintype' (α × β) := by
  refine PMF.ext fun ⟨a, b⟩ ↦ ?_
  -- the inner law puts mass `1 / |β|` on `(a, b)` from the fibre `a` and none from the others
  have hb_eq : (uniformOfFintype' β).map (Prod.mk a) (a, b) = (Fintype.card β : ℝ≥0∞)⁻¹ := by
    rw [map_apply, tsum_eq_single b fun b' hb' ↦ ite_eq_right fun h ↦ hb' (Prod.mk.inj h).2.symm,
      ite_eq_left rfl, uniformOfFintype'_apply]
  have hb_ne : ∀ a', a' ≠ a → (uniformOfFintype' β).map (Prod.mk a') (a, b) = 0 := by
    intro a' ha'
    rw [map_apply]
    exact ENNReal.tsum_eq_zero.mpr fun b' ↦ ite_eq_right fun h ↦ ha' (Prod.mk.inj h).1.symm
  rw [bind_apply, tsum_eq_single a fun a' ha' ↦ by rw [hb_ne a' ha', mul_zero], hb_eq,
    uniformOfFintype'_apply, uniformOfFintype'_apply, Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]

/-- Two independent uniform points, combined by a bijection, make a uniform point. -/
lemma uniformOfFintype'_bind_map_of_bijective {α β γ : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] [Fintype γ] [Nonempty γ] {e : α × β → γ}
    (he : Function.Bijective e) :
    (uniformOfFintype' α).bind (fun a ↦ (uniformOfFintype' β).map fun b ↦ e (a, b))
      = uniformOfFintype' γ := by
  rw [← uniformOfFintype'_map_of_bijective he, ← uniformOfFintype'_bind_map_prod, map_bind]
  exact congrArg (bind (uniformOfFintype' α)) (funext fun a ↦ (map_comp (Prod.mk a) _ e).symm)

/-- On a one-point type, the uniform law is the Dirac law. -/
lemma uniformOfFintype'_eq_pure {α : Type*} [Fintype α] [Nonempty α] [Subsingleton α] (a : α) :
    uniformOfFintype' α = PMF.pure a := by
  refine PMF.ext fun b ↦ ?_
  rw [uniformOfFintype'_apply, pure_apply, ite_eq_left (Subsingleton.elim b a),
    Fintype.card_eq_one_iff.mpr ⟨a, fun b ↦ Subsingleton.elim b a⟩, Nat.cast_one, inv_one]

/-- The chance that a uniform point satisfies a decidable predicate. -/
lemma uniformOfFintype'_map_decide_true {α : Type*} [Fintype α] [Nonempty α] {P : α → Prop}
    [DecidablePred P] :
    (uniformOfFintype' α).map (fun x ↦ decide (P x)) true
      = (#(univ.filter P) : ℝ≥0∞) / Fintype.card α := by
  have hs : (univ.filter fun x ↦ (true : Bool) = decide (P x)) = univ.filter P := by
    ext x
    simp only [mem_filter, mem_univ, _root_.true_and]
    exact ⟨fun h ↦ of_decide_eq_true h.symm, fun h ↦ (decide_eq_true h).symm⟩
  simp only [map_apply, tsum_fintype, uniformOfFintype'_apply, sum_ite, sum_const_zero,
    add_zero, sum_const, nsmul_eq_mul, div_eq_mul_inv, hs]

end PMF

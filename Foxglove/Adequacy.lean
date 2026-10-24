module

public import Foxglove.Rules

/-! # Adequacy: a closed program's specification determines its law

Running a closed program from the unit ambient footprint produces one space at which every
specification proved for it holds (`own_run_entails_of_wp`, `pure_of_wp_of_wp`), and `DIST_INJ`
at that space makes the laws two specifications assign to its result agree
(`law_unique_of_wp`).  Since `WP_SAMP` already gives a program its tape law `lawPMF`, any law a
specification gives it is that one:

* `lawPMF_eq_of_wp`: if `⊢ wp t ⦃X, X ~ ν⦄`, then `ν` is the tape law of `t`;
* `lawPMF_of_wp`: the same for law descriptions `⦃X, ∃ μ, ⌜P μ⌝ ∗ X ~ μ⦄`;
* `wp_hasDistribution_iff_lawPMF`: both directions.
-/

@[expose] public section
namespace Foxglove

open ProbSpace
open Iris OrderedUnitalResourceAlgebra BI UpperSetBI OURAProp
open Interp Interp.ProbTree
open scoped ENNReal

noncomputable section

/-! ## The tape law as a `PMF` -/

/-- **The tape law sums to one**, by induction on the program: a flip splits its mass between
the two continuations by weights summing to one (`flipWeight_add`). -/
theorem tsum_lawOf {α : Type} (t : BernoulliM α) : ∑' a, lawOf t a = 1 := by
  classical
  induction t with
  | pure x => simp only [lawOf_pure, tsum_ite_eq]
  | liftBind op cont ih =>
    simp only [lawOf_liftBind, ENNReal.tsum_add, ENNReal.tsum_mul_left, ih, mul_one,
      flipWeight_add]

/-- `tsum_lawOf`, as the `HasSum` a `PMF` asks for. -/
theorem hasSum_lawOf {α : Type} (t : BernoulliM α) : HasSum (lawOf t) 1 :=
  ENNReal.summable.hasSum_iff.2 (tsum_lawOf t)

/-- **The tape law of a coin program**, as a `PMF`. -/
def lawPMF {α : Type} (t : BernoulliM α) : PMF α := ⟨lawOf t, hasSum_lawOf t⟩

@[simp]
lemma lawPMF_apply {α : Type} (t : BernoulliM α) (a : α) : lawPMF t a = lawOf t a := rfl

/-! ## Reading specifications at the unit ambient -/

section Ambient

variable {α : Type} [Inhabited α] {m : Type → Type} [BernoulliInterpretable m] {t : m α}

/-- **A specification holds at a run.**  Run `t` from the unit ambient: `⊢ wp t Q` produces a
witness below the run's space, so owning that space gives `Q` of the run's result. -/
theorem own_run_entails_of_wp {Q : RV α → FProp} (h : ⊢ wp t Q) :
    own (run t (1 : BoundedFootprintPsp)).1.toSpace ⊢ Q (result (run t 1)) := by
  obtain ⟨b, hb₁, -, -, hb₂⟩ := h 1 valid_one (le_refl (1 : BoundedFootprintSpace Bool)) 1 1
    BoundedFootprintPsp.valid_one (mul_one _).le
  rw [mul_one] at hb₁
  exact (own_mono hb₁).trans hb₂

/-- **A closed program's specification is sound for pure facts**: whatever it entails at the
run's result is true. -/
theorem pure_of_wp {Q : RV α → FProp} {φ : Prop} (h : ⊢ wp t Q) (hφ : ∀ X, Q X ⊢ ⌜φ⌝) : φ :=
  (own_run_entails_of_wp h).trans (hφ _) _ (valid_run t 1 BoundedFootprintPsp.valid_one)
    (le_refl (run t (1 : BoundedFootprintPsp)).1.toSpace)

/-- **Two specifications hold together at a run**, so whatever they jointly entail is true. -/
theorem pure_of_wp_of_wp {Q Q' : RV α → FProp} {φ : Prop} (h : ⊢ wp t Q) (h' : ⊢ wp t Q')
    (hφ : ∀ X, iprop(Q X ∧ Q' X) ⊢ ⌜φ⌝) : φ :=
  (and_intro (own_run_entails_of_wp h) (own_run_entails_of_wp h')).trans (hφ _) _
    (valid_run t 1 BoundedFootprintPsp.valid_one)
    (le_refl (run t (1 : BoundedFootprintPsp)).1.toSpace)

/-- **A closed program has at most one law.** -/
theorem law_unique_of_wp {ν ν' : PMF α} (h : ⊢ wp t ⦃X, X ~ ν⦄) (h' : ⊢ wp t ⦃X, X ~ ν'⦄) :
    ν = ν' :=
  pure_of_wp_of_wp h h' fun _ ↦ DIST_INJ

end Ambient

/-- A law satisfying `P`, together with a second law, entails that the second satisfies `P`:
`DIST_INJ` identifies the two. -/
private lemma exists_law_and_law {α : Type} {E : RV α} {P : PMF α → Prop} {ν : PMF α} :
    iprop((∃ μ : PMF α, ⌜P μ⌝ ∗ E ~ μ) ∧ E ~ ν) ⊢ ⌜P ν⌝ :=
  and_exists_right.1.trans <| exists_elim fun μ ↦
    (and_mono sep_and entails_rfl).trans <| and_assoc.1.trans <|
      pure_elim_left fun (hP : P μ) ↦ DIST_INJ.trans (pure_mono fun (h : μ = ν) ↦ h ▸ hP)

/-! ## The law of a closed program -/

section Law

variable {α : Type} [Countable α] [Inhabited α] {m : Type → Type} [BernoulliInterpretable m]
  {t : m α}

/-- **Adequacy of laws.**  If the logic gives a closed program the law `ν`, that is its tape
law. -/
theorem lawPMF_eq_of_wp {ν : PMF α} (h : ⊢ wp t ⦃X, X ~ ν⦄) :
    lawPMF (BernoulliInterpretable.interp t) = ν :=
  law_unique_of_wp (Proofs.WP_SAMP _ _ fun a ↦ (lawPMF_apply _ a).symm) h

/-- `lawPMF_eq_of_wp`, pointwise. -/
theorem lawOf_of_wp {ν : PMF α} (h : ⊢ wp t ⦃X, X ~ ν⦄) (a : α) :
    lawOf (BernoulliInterpretable.interp t) a = ν a := by
  rw [← lawPMF_apply, lawPMF_eq_of_wp h]

/-- **Adequacy of law descriptions.**  If the logic gives a closed program some law satisfying
`P`, its tape law satisfies `P`. -/
theorem lawPMF_of_wp {P : PMF α → Prop} (h : ⊢ wp t ⦃X, ∃ μ : PMF α, ⌜P μ⌝ ∗ X ~ μ⦄) :
    P (lawPMF (BernoulliInterpretable.interp t)) := by
  -- `wp t` is `wp` of the coin program `t` compiles to
  have h₀ : ⊢ wp (BernoulliInterpretable.interp t) ⦃X, ∃ μ : PMF α, ⌜P μ⌝ ∗ X ~ μ⦄ := h
  exact pure_of_wp_of_wp h₀ (Proofs.WP_SAMP _ _ fun a ↦ (lawPMF_apply _ a).symm)
    fun _ ↦ exists_law_and_law

/-- **A closed program has law `ν` in Foxglove exactly when its tape law is `ν`.** -/
theorem wp_hasDistribution_iff_lawPMF {ν : PMF α} :
    (⊢ wp t ⦃X, X ~ ν⦄) ↔ lawPMF (BernoulliInterpretable.interp t) = ν :=
  ⟨lawPMF_eq_of_wp, fun h ↦ Proofs.WP_SAMP _ ν fun a ↦ h ▸ (lawPMF_apply _ a).symm⟩

/-- `wp_hasDistribution_iff_lawPMF`, pointwise. -/
theorem wp_hasDistribution_iff_lawOf {ν : PMF α} :
    (⊢ wp t ⦃X, X ~ ν⦄) ↔ ∀ a, lawOf (BernoulliInterpretable.interp t) a = ν a :=
  ⟨lawOf_of_wp, Proofs.WP_SAMP _ ν⟩

end Law

end

end Foxglove

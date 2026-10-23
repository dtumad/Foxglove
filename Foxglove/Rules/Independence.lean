module

public import Foxglove.Rules.Derived

/-! # Independence of a program's outputs

A pair-valued program's two components are independent with laws `μ` and `ν` when
`⊢ wp t ⦃X, (Prod.fst ∘ X) ~ μ ∗ (Prod.snd ∘ X) ~ ν⦄`, which by `PROD_SPLIT`/`PROD_UNSPLIT` is the
same as the pair having the product law `μ ⊗ ν` (`wp_sep_iff_law_product`).  Independence is
built compositionally:

* `wp_bind_pair_sep`: a sample, then a sampler whose law does not depend on it, are
  independent;
* `wp_bind_sep_bind`: post-processing each component by its own sampler keeps them
  independent, with the laws bound through the samplers' kernels.
-/

@[expose] public section
namespace Foxglove

open ProbSpace
open Iris BI UpperSetBI OURAProp
open Interp

noncomputable section

/-! ## Product laws -/

section ProductLaws

variable {α β γ δ : Type}

/-- The product law, as a bind: sample the first component, then the second. -/
lemma product_eq_bind (μ : PMF α) (ν : PMF β) : μ ⊗ ν = μ.bind fun a ↦ ν.map (Prod.mk a) := by
  classical
  refine PMF.ext fun ⟨a, b⟩ ↦ ?_
  simp only [product_apply, PMF.bind_apply, PMF.map_apply, Prod.mk.injEq]
  rw [tsum_eq_single a fun a' ha' ↦ by simp [Ne.symm ha'],
    tsum_eq_single b fun b' hb' ↦ by simp [Ne.symm hb']]
  simp

/-- Post-processing each component of a product law by its own kernel gives the product of the
bound laws. -/
lemma product_bind_bind (μ : PMF α) (ν : PMF β) (κ₁ : α → PMF γ) (κ₂ : β → PMF δ) :
    ((μ ⊗ ν).bind fun p ↦ (κ₁ p.1).bind fun c ↦ (κ₂ p.2).map (Prod.mk c))
      = μ.bind κ₁ ⊗ ν.bind κ₂ := by
  simp only [product_eq_bind, PMF.bind_bind, PMF.map_bind, PMF.bind_map, Function.comp_def]
  exact congrArg μ.bind (funext fun a ↦ PMF.bind_comm _ _ _)

end ProductLaws

/-! ## Independence and product laws -/

variable {m : Type → Type} [Monad m] [LawfulBernoulliInterpretable m] {α β γ δ : Type}

/-- **A function of the result has the pushed-forward law** (`DIST_FUN`). -/
theorem wp_law_map [Inhabited α] {t : m α} {ν : PMF α} (h : ⊢ wp t ⦃X, X ~ ν⦄) (k : α → β) :
    ⊢ wp t ⦃X, (k ∘ X) ~ ν.map k⦄ :=
  entails_trans h (WP_CONS fun _ ↦ DIST_FUN)

/-- **A product law is independence** (`PROD_SPLIT`). -/
theorem wp_sep_of_law_product [Inhabited β] [Inhabited γ] {t : m (β × γ)} {μ : PMF β} {ν : PMF γ}
    (h : ⊢ wp t ⦃X, X ~ (μ ⊗ ν)⦄) : ⊢ wp t ⦃X, (Prod.fst ∘ X) ~ μ ∗ (Prod.snd ∘ X) ~ ν⦄ :=
  entails_trans h (WP_CONS fun _ ↦ PROD_SPLIT)

/-- **Independence is a product law** (`PROD_UNSPLIT`). -/
theorem wp_law_product_of_sep [Inhabited β] [Inhabited γ] {t : m (β × γ)} {μ : PMF β} {ν : PMF γ}
    (h : ⊢ wp t ⦃X, (Prod.fst ∘ X) ~ μ ∗ (Prod.snd ∘ X) ~ ν⦄) : ⊢ wp t ⦃X, X ~ (μ ⊗ ν)⦄ :=
  entails_trans h (WP_CONS fun _ ↦ PROD_UNSPLIT)

/-- `wp_sep_of_law_product` and `wp_law_product_of_sep` together. -/
theorem wp_sep_iff_law_product [Inhabited β] [Inhabited γ] {t : m (β × γ)} {μ : PMF β} {ν : PMF γ} :
    (⊢ wp t ⦃X, (Prod.fst ∘ X) ~ μ ∗ (Prod.snd ∘ X) ~ ν⦄) ↔ ⊢ wp t ⦃X, X ~ (μ ⊗ ν)⦄ :=
  ⟨wp_law_product_of_sep, wp_sep_of_law_product⟩

/-! ## Building independence -/

/-- **A sample and an independent sampler.**  If the second sampler's law `ν` does not depend
on the first sample, the two results are independent. -/
theorem wp_bind_pair_sep [Inhabited β] [Inhabited γ] {C : m β} {F : β → m γ} {μ : PMF β} {ν : PMF γ}
    (hC : ⊢ wp C ⦃X, X ~ μ⦄) (hF : ∀ b, ⊢ wp (F b) ⦃Y, Y ~ ν⦄) :
    ⊢ wp (C >>= fun b ↦ F b >>= fun c ↦ pure (b, c))
      ⦃Z, (Prod.fst ∘ Z) ~ μ ∗ (Prod.snd ∘ Z) ~ ν⦄ := by
  refine wp_sep_of_law_product ?_
  rw [product_eq_bind]
  exact wp_bind_law hC fun b ↦ wp_bind_pure (Prod.mk b) (hF b)

/-- **Post-processing independent components independently keeps them independent.**  Each
component is fed to its own sampler; the results are independent, with the components' laws
bound through the samplers' laws. -/
theorem wp_bind_sep_bind [Inhabited α] [Inhabited β] [Inhabited γ] [Inhabited δ]
    {C : m (β × γ)} {F₁ : β → m α} {F₂ : γ → m δ} {μ : PMF β} {ν : PMF γ}
    {κ₁ : β → PMF α} {κ₂ : γ → PMF δ}
    (hC : ⊢ wp C ⦃X, (Prod.fst ∘ X) ~ μ ∗ (Prod.snd ∘ X) ~ ν⦄)
    (hF₁ : ∀ b, ⊢ wp (F₁ b) ⦃Y, Y ~ κ₁ b⦄) (hF₂ : ∀ c, ⊢ wp (F₂ c) ⦃Y, Y ~ κ₂ c⦄) :
    ⊢ wp (C >>= fun p ↦ F₁ p.1 >>= fun a ↦ F₂ p.2 >>= fun d ↦ pure (a, d))
      ⦃Z, (Prod.fst ∘ Z) ~ (μ.bind κ₁) ∗ (Prod.snd ∘ Z) ~ (ν.bind κ₂)⦄ := by
  refine wp_sep_of_law_product ?_
  rw [← product_bind_bind]
  exact wp_bind_law (wp_law_product_of_sep hC) fun p ↦
    wp_bind_law (hF₁ p.1) fun a ↦ wp_bind_pure (Prod.mk a) (hF₂ p.2)

end

end Foxglove

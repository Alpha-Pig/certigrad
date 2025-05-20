import CertiGrad.Tensor
import CertiGrad.Tfacts
import CertiGrad.Tactics
import CertiGrad.SimpAttr

import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Ring

import Lean
open Lean Elab Tactic Meta

namespace certigrad
namespace T
open util_list


@[cdiff_simp] axiom  is_cdifferentiable_binary {shape : S} (k : T shape → T shape → TReal) (θ : T shape) :
  is_cdifferentiable (λ θ₀ => k θ₀ θ) θ → is_cdifferentiable (λ θ₀ => k θ θ₀) θ →
  is_cdifferentiable (λ θ₀ => k θ₀ θ₀) θ

@[cdiff_simp] axiom  is_cdifferentiable_integral : ∀ {ishape tshape : S} (f : T ishape → T tshape → TReal) (θ : T tshape),
  (∀ x, is_cdifferentiable (f x) θ) →
  is_uniformly_integrable_around (λ θ₀ x => f x θ₀) θ →
  is_uniformly_integrable_around (λ θ₀ x => ∇ (λ θ₁ => f x θ₁) θ₀) θ →
  is_cdifferentiable (λ θ₀ => ∫ (λ x => f x θ₀)) θ

@[cdiff_simp] axiom  is_cdifferentiable_const {ishape : S} (θ : T ishape) (x : TReal) : is_cdifferentiable (λ (θ₀ : T ishape) => x) θ

@[cdiff_simp] axiom  is_cdifferentiable_id (θ : TReal) : is_cdifferentiable (λ (θ₀ : TReal) => θ₀) θ

@[cdiff_simp] axiom  is_cdifferentiable_exp {shape : S} (k : T shape → TReal)(θ : T shape) :
  is_cdifferentiable k (exp θ) → is_cdifferentiable (λ θ => k (exp θ)) θ

@[cdiff_simp] axiom is_cdifferentiable_exp_id (θ : T []) :
  is_cdifferentiable (λ θ => exp θ) θ

@[cdiff_simp] axiom  is_cdifferentiable_log {shape : S} (k : T shape → TReal) (θ : T shape) : θ > 0 →
  is_cdifferentiable k (log θ) → is_cdifferentiable (λ θ => k (log θ)) θ

@[cdiff_simp] axiom  is_cdifferentiable_sqrt {shape : S} (k : T shape → TReal) (θ : T shape) :
  is_cdifferentiable k (sqrt θ) → is_cdifferentiable (λ θ => k (sqrt θ)) θ

@[cdiff_simp] axiom  is_cdifferentiable_inv {shape : S} (k : T shape → TReal) (θ : T shape) : θ > 0 →
    is_cdifferentiable k θ⁻¹ → is_cdifferentiable (λ θ => k θ⁻¹) θ

@[cdiff_simp] axiom  is_cdifferentiable_inv_id
(θ: TReal): θ >0 → is_cdifferentiable (λ θ => θ⁻¹) θ

@[cdiff_simp] axiom  is_cdifferentiable_scale {shape : S} (k : T shape → TReal) (α : TReal) (x : T shape) :
  is_cdifferentiable k (α • x) → is_cdifferentiable (λ x => k (α • x)) x

@[cdiff_simp] axiom  is_cdifferentiable_neg {shape : S} (k : T shape → TReal) (θ : T shape) :
  is_cdifferentiable k (- θ) → is_cdifferentiable (λ θ => k (- θ)) θ

@[cdiff_simp] axiom  is_cdifferentiable_add₁ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) :
  is_cdifferentiable k (x₁ + x₂) → is_cdifferentiable (λ x₁ => k (x₁ + x₂)) x₁

@[cdiff_simp] axiom  is_cdifferentiable_add₁_id (x₁ x₂ : TReal):
  is_cdifferentiable (λ x₁ => (x₁ + x₂)) x₁

@[cdiff_simp] axiom  is_cdifferentiable_add₂ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) :
  is_cdifferentiable k (x₁ + x₂) → is_cdifferentiable (λ x₂ => k (x₁ + x₂)) x₂
@[cdiff_simp] axiom  is_cdifferentiable_add₂_id(x₁ x₂ : TReal) :
  is_cdifferentiable (λ x₂ => (x₁ + x₂)) x₂

@[cdiff_simp] axiom  is_cdifferentiable_sub₁ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) :
  is_cdifferentiable k (x₁ - x₂) → is_cdifferentiable (λ x₁ => k (x₁ - x₂)) x₁

@[cdiff_simp] axiom  is_cdifferentiable_sub₂ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) :
  is_cdifferentiable k (x₁ - x₂) → is_cdifferentiable (λ x₂ => k (x₁ - x₂)) x₂

@[cdiff_simp] axiom  is_cdifferentiable_mul₁ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) :
  is_cdifferentiable k (x₁ * x₂) → is_cdifferentiable (λ x₁ => k (x₁ * x₂)) x₁

@[cdiff_simp] axiom  is_cdifferentiable_mul₁_id (x₁ x₂ : TReal) :
  is_cdifferentiable (λ x₁ => (x₁ * x₂)) x₁

@[cdiff_simp] axiom  is_cdifferentiable_mul₂ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) :
  is_cdifferentiable k (x₁ * x₂) → is_cdifferentiable (λ x₂ => k (x₁ * x₂)) x₂
@[cdiff_simp] axiom  is_cdifferentiable_mul₂_id (x₁ x₂ : TReal) :
  is_cdifferentiable (λ x₂ => (x₁ * x₂)) x₂

@[cdiff_simp] axiom  is_cdifferentiable_div₁ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) : square x₂ > 0 →
  is_cdifferentiable k (x₁ / x₂) → is_cdifferentiable (λ x₁ => k (x₁ / x₂)) x₁

@[cdiff_simp] axiom  is_cdifferentiable_div₂ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) : square x₂ > 0 →
  is_cdifferentiable k (x₁ / x₂) → is_cdifferentiable (λ x₂ => k (x₁ / x₂)) x₂

@[cdiff_simp] axiom  is_cdifferentiable_sum (k : TReal → TReal) (shape : S) (x : T shape) :
  is_cdifferentiable k (sum x) → is_cdifferentiable (λ x => k (sum x)) x

@[cdiff_simp] axiom  is_cdifferentiable_prod (k : TReal → TReal) (shape : S) (x : T shape) :
  is_cdifferentiable k (prod x) → is_cdifferentiable (λ x => k (prod x)) x

@[cdiff_simp] axiom  is_cdifferentiable_square {shape : S} (k : T shape → TReal) (x : T shape) :
  is_cdifferentiable k (square x) → is_cdifferentiable (λ x => k (square x)) x

@[cdiff_simp] axiom  is_cdifferentiable_gemm₁ {m p : ℕ} (k : T [m, p] → TReal) (n : ℕ) (M : T [m, n]) (N : T [n, p]) :
  is_cdifferentiable k (gemm M N) → is_cdifferentiable (λ M => k (gemm M N)) M

@[cdiff_simp] axiom  is_cdifferentiable_gemm₂ {m p : ℕ} (k : T [m, p] → TReal) (n : ℕ) (M : T [m, n]) (N : T [n, p]) :
  is_cdifferentiable k (gemm M N) → is_cdifferentiable (λ N => k (gemm M N)) N

@[cdiff_simp] axiom  is_cdifferentiable_add_fs {shape : S} (f₁ f₂ : T shape → TReal) (θ : T shape):
  (is_cdifferentiable f₁ θ ∧ is_cdifferentiable f₂ θ) ↔ is_cdifferentiable (λ θ₀ => f₁ θ₀ + f₂ θ₀) θ

@[cdiff_simp] axiom  is_cdifferentiable_scale_f {shape : S} (α : TReal) (f : T shape → TReal) (θ : T shape):
  is_cdifferentiable f θ ↔ is_cdifferentiable (λ x => α • f x) θ

@[cdiff_simp] axiom  is_cdifferentiable_fscale {shape : S} (f : T shape → TReal) (y : TReal) (θ : T shape):
  is_cdifferentiable f θ ↔ is_cdifferentiable (λ x => f x • y) θ

-- Provable
@[cdiff_simp] axiom  is_cdifferentiable_sumr {X : Type} {shape : S} (θ : T shape) (f : T shape → X → TReal) :
  Π (xs : List X),
    (∀ (x : X), x ∈ xs → is_cdifferentiable (λ θ₀ => f θ₀ x) θ) →
    is_cdifferentiable (λ (θ₀ : T shape) => sumr (List.map (f θ₀) xs)) θ






-- elab "proveDifferentiable" : tactic =>
--   withMainContext do
--     logInfo m!"[proveDifferentiableOnly] Attempting to prove differentiability using cdiff_simp and precond_simp rules (repeat)..."
--     try
--       evalTactic (← `(tactic| repeat (simp (config := {maxSteps := 100, failIfUnchanged := false}) only [cdiff_simp, precondition_simp])))
--       evalTactic (← `(tactic| try assumption))
--       logInfo m!"[proveDifferentiableOnly] Finished."
--     catch e =>
--       logError m!"[proveDifferentiableOnly] Failed: {e.toMessageData}"
--       throw e

elab "proveDifferentiable" : tactic =>
  withMainContext do
    logInfo m!"[proveDifferentiable] Attempting to prove differentiability using cdiff_simp with provePreconditions discharger..."
    try
      evalTactic (← `(tactic|
        -- 主要的 simp 调用，只使用 cdiff_simp 进行重写
        -- 并将 provePreconditions 指定为 discharger
        simp (config := {maxSteps := 200, failIfUnchanged := false, discharger := provePreconditions}) only [cdiff_simp];
        -- 在 simp 完成后，可以再尝试一次 assumption 清理可能剩下的简单目标
        try assumption
      ))
      logInfo m!"[proveDifferentiable] Finished successfully."
    catch e =>
      logError m!"[proveDifferentiable] Failed: {e.toMessageData}"
      throw e




set_option trace.Meta.Tactic.simp true
-- set_option trace.Meta.isDefEq true
-- set_option trace.Meta.debug true

example (shape : S) (θ : T []) : is_cdifferentiable (λ θ => exp θ) θ := by
    proveDifferentiable
    simp [cdiff_simp]




example (shape : S) (θ : T []) : is_cdifferentiable (λ θ => 1 + exp θ) θ := by
  proveDifferentiable


example (shape : S) (θ : T []) : is_cdifferentiable (λ θ => 1/ exp θ) θ := by
  apply is_cdifferentiable_exp
  apply is_cdifferentiable_inv
  apply exp_pos
  apply is_cdifferentiable_mul₂_id

example (shape : S) (θ : T []) : is_cdifferentiable (λ θ => 1 + θ) θ := by
    simp [cdiff_simp]

-- lemma is_cdifferentiable_sigmoid {shape : S} (k : T shape → TReal) (θ : T shape) :
--   is_cdifferentiable k (sigmoid θ) → is_cdifferentiable (λ θ => k (sigmoid θ)) θ := by
--     intro H
--     unfold sigmoid
--     apply is_cdifferentiable_neg

end T
end certigrad

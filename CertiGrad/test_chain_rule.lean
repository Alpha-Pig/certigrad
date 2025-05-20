import Lean
import Lean.Meta.Tactic.Simp
import CertiGrad.SimpAttr
import Certigrad.SimpGrad


open certigrad T
set_option trace.Meta.Tactic.simp true
set_option trace.Meta.Tactic.simp.discharge true
-- 测试 grad_chain_rule 是否能被 simp 自动化证明

example {ishape oshape : S} (f : T ishape → T oshape) (k : T oshape → TReal) (θ : T ishape) :
  ∇ (λ θ₀ => k (f θ₀)) θ = tmulT (D (λ θ₀ => f θ₀) θ) (∇ k (f θ)) := by
  -- 明确指定完整路径
  simp

-- This file contains a fixed version of simplifyGradCore

import CertiGrad.Tgrads

namespace certigrad.T

-- Open required namespaces
open Lean Meta Elab Tactic

def applyGradRulesOnce (eInput : Expr) : TacticM (Option (Expr × Expr)) := do
  try
    -- 这些都是 TacticM 函数，或者可以从 TacticM 调用的 MetaM 函数
    let grad ← checkGrad eInput       -- (MetaM/TacticM)
    let k ← computeK grad             -- (MetaM/TacticM) (k 是从 eInput 中为特定化简提取的部分)
    let sTheorems ← buildSimplifyGradSimpLemmas k -- 这是 TacticM SimpTheorems

    -- 使用动态构建的 sTheorems 来化简原始的 eInput
    -- (对应 Lean 3 conv.apply_lemmas_core s e)
    let simpCtx : Simp.Context := {
      config := { -- 根据需要配置，例如禁用zeta等，以便更精确控制
        zeta := false, beta := false, eta := false, proj := false, arith := false
      },
      simpTheorems := #[sTheorems]
    }
    -- Lean.Meta.Simp.main 是 MetaM，可以在 TacticM 中调用
    let (result, _) ← Lean.Meta.Simp.main eInput simpCtx {}

    if let some proof := result.proof? then -- proof : eInput = result.expr (即 newE)
      -- 检查是否真的发生了有意义的改变，避免 result.expr 和 eInput 指针相同且证明是 refl
      if result.expr == eInput && proof.isAppOfArity ``Eq.refl 1 && proof.appArg! == eInput then
        return none
      else
        return some (result.expr, proof) -- 返回 (新表达式, 旧表达式 = 新表达式 的证明)
    else
      return none -- Simp.main 没有产生证明，意味着没有变化
  catch ex =>
    logInfo m!"[applyGradRulesOnce] Failed for {eInput}: {ex.toMessageData}" -- 可选日志
    return none

-- Helper function to check if an MVarId is active
def isActiveMVarId (mvarId : MVarId) : MetaM Bool := do
  return !(← mvarId.isAssigned) && ((← getMCtx).findDecl? mvarId).isSome

-- Main tactic implementation with fixes
def simplifyGradCore : TacticM Unit := do
  let maxIterations := 10 -- 迭代上限
  let mut iteration := 0
  let mut progressMadeOverall := false

  -- 使用List.range替代[0:maxIterations]，避免Decidable类型错误
  for _ in List.range maxIterations do
    iteration := iteration + 1
    let currentMVarId ← getMainGoal

    unless (← isActiveMVarId currentMVarId) do
      logInfo m!"[simplifyGradCore] Goal already solved or inactive."
      break

    -- 确保在目标的上下文中获取等式两边
    let (_, lhs, rhs) ← currentMVarId.withContext do
      let target ← currentMVarId.getType
      match target.eq? with
      | some (_, l, r) => pure (target, l, r)
      | none => throwError "[simplifyGradCore] Goal is not an equality: {target}"

    -- 尝试应用梯度规则简化左侧
    match ← applyGradRulesOnce lhs with
    | some (newLhs, proofLhsEqNewLhs) =>
      progressMadeOverall := true

      let goalToUpdate ← getMainGoal
      unless (← isActiveMVarId goalToUpdate) do
        break

      -- 检查新的左侧是否与右侧等价
      if ← Meta.isDefEq newLhs rhs then
        -- 如果等价，直接使用证明关闭目标
        goalToUpdate.assign proofLhsEqNewLhs
        replaceMainGoal []
        logInfo m!"[simplifyGradCore] LHS simplified to RHS in iteration {iteration}. Goal closed."
        return
      else
        -- 否则创建新目标继续简化
        let newTarget ← mkEq newLhs rhs
        let newGoalMVar ← mkFreshExprMVar newTarget
        goalToUpdate.assign (← Meta.mkEqTrans proofLhsEqNewLhs newGoalMVar)
        replaceMainGoal [newGoalMVar.mvarId!]
        logInfo m!"[simplifyGradCore] LHS simplified in iteration {iteration}. New LHS: {newLhs}"

    | none =>
      -- 如果无法简化，停止迭代
      logInfo m!"[simplifyGradCore] No change to LHS in iteration {iteration}. Stopping."
      break

  -- 处理最大迭代次数和无进展情况
  if iteration == maxIterations then
    logWarning "[simplifyGradCore] Reached max iterations."

  if !progressMadeOverall then
    let finalGoalMVarId ← getMainGoal
    if (← isActiveMVarId finalGoalMVarId) then
      logInfo "[simplifyGradCore] Tactic made no simplification progress overall."

end certigrad.T

-- Register the tactic so it can be used in proofs
elab "simplifyGradCore" : tactic => certigrad.T.simplifyGradCore

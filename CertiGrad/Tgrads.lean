import CertiGrad.Tensor
import CertiGrad.Tfacts
import CertiGrad.Tactics
import CertiGrad.SimpGrad
import CertiGrad.SimpCdiff

import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Ring

import Lean
open Lean Elab Tactic Meta

namespace certigrad
namespace T

open util_list


section simplify_grad


lemma id_rule {A : Type} (a : A) : id a = a := rfl

-- withMainContext resolves unknown free variable error
-- Now reduceK is indirectly wrapped in tid.withcontex
def reduceK (k : Expr) : TacticM Expr :=  do
  -- Create a SimpTheorems object
  let slss ← Meta.SimpTheorems.addConst {} `certigrad.T.id_rule

  -- Attempt to simplify `k` using the simplification theorems
  let simpResult ← Meta.simp k { simpTheorems := #[slss] }

  -- If simplification results in a different expression, return it; otherwise, return the original `k`
  if simpResult.1.expr != k then
    return simpResult.1.expr
  else
    return k

partial def has_x (x e : Expr) : Option Bool :=
  if e.eqv x then pure true
  else
    let f : Bool → Expr → Option Bool := (λ found (m : Expr) =>
      if found then pure true
      else has_x x m)
    e.foldlM f false

/-
  Illustration of input arguments:
  - x is `new_x
  - k is initially `fun x => x`
  - e is the body `... (new_x op y) ...`
-/

partial def computeOuterInnerFunctionsCore (x : Expr) : Expr → Expr → TacticM Expr :=
  λ k e =>
  -- withMainContext resolves the unknown free variables error in computeOuterInnerFunctionsCore
  --  withMainContext
   do
    -- logInfo m!"computeOuterInnerFunctionsCore, x:={x}, k:={k}, e:={e}"

    -- e.g.,  f = @T.prod
    let f := e.getAppFn
    -- e.g., {shape : S} → T shape → TReal
    let f_type ← inferType f
    -- e.g., [ishape, large_body_expr]
    let args := e.getAppArgs'
    let n := args.size
    -- interesting finding: syntax `match` is actually a function
    -- logInfo m!"f:={f}\nf_type:={f_type}\nargs:={args}\nn:={n}"

    if n <= 0 then
      throwError "Expression has zero arguments"

    if n <= 1 then
      -- the right thing to do is constructing a k with single parameter
      let barg := args.get! (n-1)
      -- logInfo m! "barg={barg}"
      if barg == x then return k
      else
        let barg_type ← inferType barg
        let h := (has_x x barg)
        if h = some true then
          computeOuterInnerFunctionsCore x (mkLambda `x BinderInfo.default barg_type (Expr.app k (mkAppN f $ args.set! (n-1) (mkBVar 0)))) barg
        else
          throwError "Strange things happened, somehow x is not in e anymore"

    else
      let barg₁ := args.get! (n-2)
      let barg₂ := args.get! (n-1)
      -- logInfo m!"barg1:={barg₁}, barg2:={barg₂}"

      let barg₁_type ← inferType barg₁
      -- logInfo m!"barg₁_type:={barg₁_type}"
      let barg₂_type ← inferType barg₂

      -- logInfo m!"barg₁_type:={barg₁_type},  barg₂_type:={barg₂_type}"

      let h1 := (has_x x barg₁)
      let h2 := (has_x x barg₂)
      -- logInfo m! "h1:={h1}, h2:={h2}"

      if barg₁ == x || barg₂ == x then
        return k
      else if h1 = some true then
        computeOuterInnerFunctionsCore x (mkLambda `x BinderInfo.default barg₁_type (Expr.app k (mkAppN f $ args.set! (n-2) (mkBVar 0)))) barg₁
      else if h2 = some true then
        computeOuterInnerFunctionsCore x (mkLambda `x BinderInfo.default barg₂_type (Expr.app k (mkAppN f $ args.set! (n-1) (mkBVar 0)))) barg₂
      else
        -- return k
        throwError "Variable not found"

/-
grad is in the form of: `T.is_cdifferentiable f val`
where f is (fun x => ... (x op y) ...)

the goal is to find `k := (fun v => ... v ...)` such that f = `fun x => k (x op y)`
-/

partial def computeOuterInnerFunctions (grad : Expr) : TacticM Expr := do
  -- let f := grad.getAppFn'
  -- logInfo m!"args := {args}"
  -- let f : Expr := if h : f0.isApp then f0.appArg h else f0
  -- logInfo m!"f := {f}"

  -- now f is `fun x => ... (x op y) ...`
  let args := grad.getAppArgs'
  let f := args[1]!

  /-
    f := fun θ₀ => ((2 * T.pi shape * θ₀.square).sqrt⁻¹ * (-(2⁻¹ * ((x - μ) / σ).square)).exp).prod
    input_domain_type := T shape
    binding_body := ((2 * T.pi shape * T.square #0).sqrt⁻¹ * (-(2⁻¹ * ((x - μ) / σ).square)).exp).prod
  -/
  let input_domain_type := f.bindingDomain!
  let binding_body := f.bindingBody!
  -- logInfo m!"input_domain_type := {input_domain_type}, binding_body := {binding_body}"

  let x ← mkFreshExprMVar input_domain_type (userName:= `new_x)
  let body := binding_body.instantiate1 x
  let bodyType ← inferType body

  -- throwError "computeOuterInnerFunctions debug-1"

  /-
    x := ?new_x
    body := ((2 * T.pi shape * ?new_x.square).sqrt⁻¹ * (-(2⁻¹ * ((x - μ) / σ).square)).exp).prod
    bodyType := TReal
  -/
  -- logInfo m!"x:={x}, body:={body}, bodyType:={bodyType}"

  -- initialK is simply an identity function: λ x => x
  -- `bvar 0` is de Bruin index
  let initialK := mkLambda `x BinderInfo.default bodyType (mkBVar 0)
  -- logInfo m!"initialK:={initialK}"

  -- Note: `<|>` prevents logInfo message of computeOuterInnerFunctionsCore
  -- being printed if any error happens inside
  -- `<|>` is solelyfor handling the case f is identity function
  computeOuterInnerFunctionsCore x initialK body <|> return initialK


def computeK (grad : Expr) : TacticM Expr := do
  let k ← computeOuterInnerFunctions grad
  -- logInfo m!"after outer-inner, k = {k}"

  -- Q: why do we need reduceK? this might be problematic,
  -- since after reducing the structure may not match the oringal function
  -- A: reduceK is really needed because the way we construct k
  -- has a lot of nested function applications
  let kSimp ← reduceK k

  -- Perform head eta-expansion
  -- Meta.headEtaExpand kSimp
  -- logInfo m!"after reduceK, k = {kSimp}"
  return kSimp

-- meta def check_grad (e : expr) : tactic expr :=
-- if is_napp_of e `certigrad.T.grad 3 then head_eta_expand e else tactic.fail "not ∇"

def checkGrad (e : Expr) : TacticM Expr :=do
  if e.isAppOfArity `certigrad.T.grad 3 then
    -- In Lean3 implementation, `head_eta_expand e` is returned
    -- but there seems no similar API (e.g., headEtaExpansion) in Lean4
    return e
  else
    throwError "Variable not found"

def tryAddSimp (s : SimpTheorems) (p : Syntax) : TacticM SimpTheorems := do
  -- Try to convert the `Syntax` (which represents a `pexpr`) to an `Expr`
  let oe ← Lean.Elab.Tactic.tryTactic? (elabTerm p none)

  match oe with
  | none =>
    -- If the expression is invalid, return the original `SimpTheorems`
    return s
  | some e =>
    -- If valid, add the expression to the `SimpTheorems`
    return (← s.addConst e.constName!)


def buildSimplifyGradSimpLemmas (k : Expr) : TacticM SimpTheorems := do
  -- List of expressions to elaborate
  -- let dbg1 : Syntax := `(certigrad.T.grad_sum )

  let exprs : List (TacticM (TSyntax `term)) :=
    [ ``(@certigrad.T.grad_const),
      ``(@certigrad.T.grad_id),
      ``(certigrad.T.grad_exp $$k),
      ``(certigrad.T.grad_log $$k),
      ``(certigrad.T.grad_scale $$k),
      ``(certigrad.T.grad_neg $$k),
      ``(certigrad.T.grad_add₁ $$k),
      ``(certigrad.T.grad_add₂ $$k),
      ``(certigrad.T.grad_sub₁ $$k),
      ``(certigrad.T.grad_sub₂ $$k),
      ``(certigrad.T.grad_mul₁ $$k),
      ``(certigrad.T.grad_mul₂ $$k),
      ``(certigrad.T.grad_div₁ $$k),
      ``(certigrad.T.grad_div₂ $$k),
      ``(@certigrad.T.grad_dot₁),
      ``(@certigrad.T.grad_dot₂),
      ``(certigrad.T.grad_square $$k),
      ``(certigrad.T.grad_sqrt $$k),
      ``(certigrad.T.grad_softplus $$k),
      ``(certigrad.T.grad_sigmoid $$k) ]

  let exprs2 ←  Monad.sequence exprs
  -- Convert the list of syntax to expressions
  let es ← exprs2.mapM fun p => elabTerm p none

  -- Create the initial SimpTheorems
  let mut s := {}

  -- Add each elaborated expression to SimpTheorems
  for e in es do
    s ← s.addConst e.constName!
  s ← tryAddSimp s (← ``(certigrad.T.grad_gemm₁ $$k))
  s ← tryAddSimp s (← ``(certigrad.T.grad_gemm₂ $$k))
  s ← tryAddSimp s (← ``(certigrad.T.grad_sum $$k))


  s ← tryAddSimp s (← ``(@certigrad.T.grad_scale_f))

  -- Return the final set of simplification lemmas
  return s




def simplifyGradCoreHelper (tac : MetaM Unit) : TacticM Unit := do
  let tag ← getMainTag
  guard $ tag = `eq
  let target ← getMainGoal
  let grad ← checkGrad (← target.getType)
  let k ← computeK grad
  let s ← buildSimplifyGradSimpLemmas k

  Simp.withSimpContext { simpTheorems := #[s] } tac





def checkIsCDifferentiable (e : Expr) : TacticM Expr := do

  /- e can be mdata : Lean.MData → Lean.Expr → Lean.Expr-/
  -- logInfo m! "checkIsCDifferentiable e={e}"

  if e.isAppOfArity' ``T.is_cdifferentiable 3 then
    -- return (← headBeta e)
    return e
  else
  if e.isAppOfArity' ``T.is_cdifferentiable 2 then
    -- return (← headBeta e)
    throwError " is_cdifferentiable arity is 2"
  else
    throwError "not is_cdifferentiable fn:= {e.getAppFn} fn'={e.getAppFn'} numArgs:= {e.getAppNumArgs'} isConst={e.isConst} isLam={e.isLambda} isApp={e.isApp} isForAll={e.isForall} isLet={e.isLet} isLetFun={e.isLetFun} isProp={e.isProp} isMVar={e.isMVar} isFVar={e.isFVar} isBinding={e.isBinding} isSort={e.isSort} isLit={e.isLit} isMdata={e.isMData}"



def proveDifferentiableCore (tid : MVarId): TacticM (List MVarId) := do
  let tgt ←  instantiateMVars  (← tid.getType)
  let grad ← checkIsCDifferentiable tgt

  let k ← tid.withContext (computeK grad)

  let candidate_exprs : List (MetaM Expr) := [
    (mkAppM ``certigrad.T.is_cdifferentiable_id #[]),
    (mkAppM ``certigrad.T.is_cdifferentiable_const #[]),
    (mkAppM ``certigrad.T.is_cdifferentiable_exp #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_log #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_sqrt #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_scale #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_neg #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_inv #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_add₁ #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_add₂ #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_sub₁ #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_sub₂ #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_mul₁ #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_mul₂ #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_div₁ #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_div₂ #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_square #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_sum #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_prod #[k]),

    -- the following lemmas will be defined later,
    -- thus cannot use double backtick to check their existence
    (mkAppM `certigrad.T.is_cdifferentiable_sigmoid #[k]),
    (mkAppM `certigrad.T.is_cdifferentiable_softplus #[k]),
    (mkAppM `certigrad.T.is_cdifferentiable_mvn_kl₁ #[k]),
    (mkAppM `certigrad.T.is_cdifferentiable_mvn_kl₂ #[k]),
    (mkAppM `certigrad.T.is_cdifferentiable_bernoulli_neglogpdf₁ #[k]),
    (mkAppM `certigrad.T.is_cdifferentiable_bernoulli_neglogpdf₂ #[k]),
  ]

  myFirstApply tid candidate_exprs



elab "proveDifferentiableOnly" : tactic => do
    setGoals (← Meta.repeat' proveDifferentiableCore (← getGoals))

def myAssumption (varIds : List MVarId) : MetaM (List MVarId) := do
  filterM (fun vid : MVarId => do try
      let _ ← vid.assumption; return false
      catch _ => return true)
      varIds

elab "proveDifferentiable" : tactic => do
    -- setGoals (← Meta.repeat' proveDifferentiableCore (← getGoals))

    let varIds ← Meta.repeat' proveDifferentiableCore (← getGoals)

    -- attempt to run `assumption` on each sub-goal
    let varIds ← myAssumption varIds

    let varIds ← Meta.repeat' provePreconditionsCore varIds

    -- attempt to run `assumption` on each sub-goal
    let varIds ← myAssumption varIds

    -- save the remaining sub-goals (if any left)
    setGoals varIds




end simplify_grad




lemma is_cdifferentiable_sigmoid {shape : S} (k : T shape → TReal) (θ : T shape) :
  is_cdifferentiable k (sigmoid θ) → is_cdifferentiable (λ θ => k (sigmoid θ)) θ := by
    intro H
    unfold sigmoid
    proveDifferentiable

lemma is_cdifferentiable_softplus {shape : S} (k : T shape → TReal) (θ : T shape) :
  is_cdifferentiable k (softplus θ) → is_cdifferentiable (λ θ => k (softplus θ)) θ := by
    intro H
    unfold softplus
    proveDifferentiable

lemma is_cdifferentiable_mvn_kl₁ (k : TReal → TReal) (shape : S) (μ σ : T shape) :
  is_cdifferentiable k (mvn_kl μ σ) → is_cdifferentiable (λ μ => k (mvn_kl μ σ)) μ := by
  intro H
  unfold mvn_kl
  proveDifferentiable

lemma is_cdifferentiable_mvn_kl₂ (k : TReal → TReal) (shape : S) (μ σ : T shape) (H_σ : σ > 0) :
  is_cdifferentiable k (mvn_kl μ σ) → is_cdifferentiable (λ σ => k (mvn_kl μ σ)) σ := by
  intro H
  unfold mvn_kl
  apply is_cdifferentiable_binary (λ θ₁ θ₂ => k (-2⁻¹ * T.sum (1 + T.log (square θ₁) - square μ - square θ₂)))
  case a => proveDifferentiable
  case a => proveDifferentiable


lemma is_cdifferentiable_bernoulli_neglogpdf₁ (k : TReal → TReal) (shape : S) (p z : T shape) (H_p₁ : p > 0) (H_p₂ : p < 1) :
  is_cdifferentiable k (bernoulli_neglogpdf p z) → is_cdifferentiable (λ p => k (bernoulli_neglogpdf p z)) p := by
  intro H
  unfold bernoulli_neglogpdf
  apply is_cdifferentiable_binary (λ θ₁ θ₂ => k (-T.sum (z * T.log (eps shape + θ₁) + (1 - z) * T.log (eps shape + (1 - θ₂)))))
  case a => proveDifferentiable
  case a => proveDifferentiable


lemma is_cdifferentiable_bernoulli_neglogpdf₂ (k : TReal → TReal) (shape : S) (p z : T shape) :
  is_cdifferentiable k (bernoulli_neglogpdf p z) → is_cdifferentiable (λ z => k (bernoulli_neglogpdf p z)) z := by
  intro H
  unfold bernoulli_neglogpdf
  apply is_cdifferentiable_binary (λ θ₁ θ₂ => k (-T.sum (θ₁ * T.log (eps shape + p) + (1 -θ₂) * T.log (eps shape + (1 - p)))))
  case a => proveDifferentiable
  case a => proveDifferentiable

-- Random

-- lemma mvn_grad_logpdf_μ_correct {shape : S} (μ σ x : T shape) (H_σ : σ > 0) :
--   ∇ (λ θ => mvn_logpdf θ σ x) μ = mvn_grad_logpdf_μ μ σ x :=
-- begin
-- dunfold mvn_logpdf,
-- note H := square_pos_of_pos H_σ,
-- simplify_grad,
-- simp [smul.def, const_bit0, const_one, const_neg, const_inv, T.neg_div],
-- rw -mul_assoc, rw T.mul_inv_cancel two_pos,
-- simp, rw T.div_div_eq_div_mul,
-- reflexivity
-- end

-- lemma mvn_grad_logpdf_σ_correct {shape : S} (μ σ x : T shape) (H_σ : σ > 0) :
--   ∇ (λ θ => mvn_logpdf μ θ x) σ = mvn_grad_logpdf_σ μ σ x :=
-- have H_σ₂ : square σ > 0, from square_pos_of_pos H_σ,
-- have H_d₁ : is_cdifferentiable (λ θ₀ => -2⁻¹ * sum (square ((x - μ) / θ₀) + log (2 * pi shape) + log (square σ))) σ, by prove_differentiable,
-- have H_d₂ : is_cdifferentiable (λ θ₀ => -2⁻¹ * sum (square ((x - μ) / σ) + log (2 * pi shape) + log (square θ₀))) σ, by prove_differentiable,

-- have H₁ : (2 * (2⁻¹ / square σ)) = σ⁻¹ * σ⁻¹,
--   begin dunfold square, rw [T.mul_div_mul_alt, T.mul_inv_cancel two_pos, one_div_inv, T.mul_inv_pos H_σ H_σ] end,

-- have H₂ : 2 * ((x + -μ) * ((x + -μ) * 2⁻¹)) = (2 * 2⁻¹) * square (x - μ), by simp [square],

-- begin
-- dunfold mvn_logpdf,
-- rw grad_binary (λ θ₁ θ₂ => -2⁻¹ * sum (square ((x - μ) / θ₁) + log (2 * pi shape) + log (square θ₂))) _ H_d₁ H_d₂, dsimp,
-- simplify_grad,
-- simp [smul.def, const_bit0, const_one, const_neg, const_inv, T.neg_div, T.div_div_eq_div_mul],
-- rw H₁,
-- rw -mul_assoc, rw T.mul_inv_cancel H_σ,
-- simp [T.mul_div_mul_alt, T.div_div_eq_div_mul],
-- rw [H₂, T.mul_inv_cancel two_pos],
-- simp [mvn_grad_logpdf_σ]
-- end

-- With data structures
lemma grad_sumr {X : Type} {shape : S} (θ : T shape) (f : T shape → X → TReal) :
  Π (xs : List X),
    is_cdifferentiable (λ (θ₀ : T shape) => sumr (List.map (f θ₀) xs)) θ →
    ∇ (λ (θ₀ : T shape) =>  sumr (List.map (f θ₀) xs)) θ
    =
    sumr (List.map (λ x => ∇ (λ θ₀ => f θ₀ x) θ) xs)
  | [],      H_diff => by { unfold List.map sumr; rw [grad_const] }
  | (x::xs), H_diff => by
    unfold List.map sumr
    unfold List.map sumr at H_diff
    rw [grad_add_fs _ _ _ (Iff.mpr (is_cdifferentiable_add_fs _ _ _) H_diff).left (Iff.mpr (is_cdifferentiable_add_fs _ _ _) H_diff).right]
    rw [grad_sumr _  _ _ ((Iff.mpr (is_cdifferentiable_add_fs _ _ _) H_diff).right)]

-- Note: this could be proved from a `select`/`replicate` formulation,
-- but it is arguably a more natural way of @[simp] axiom atizing the property anyway.

-- @[simp] axiom  multiple_args_general :
--   ∀ (parents : List Reference) (tgt : Reference) (m : env)
--     (f : Dvec T parents^.p2 → T tgt.2 → TReal) (θ : T tgt.2),
--     is_cdifferentiable (λ θ₀ => f (env.get_ks parents (env.insert tgt θ m)) θ₀) θ →
--     is_cdifferentiable (λ θ₀ => sumr (map (λ (idx : ℕ) => f (dvec.update_at θ₀ (env.get_ks parents (env.insert tgt θ m)) idx) θ)
--                                        (filter (λ idx => tgt = dnth parents idx) (riota $ length parents)))) θ →
-- ∇ (λ (θ₀ : T tgt.2) => f (env.get_ks parents (env.insert tgt θ₀ m)) θ₀) θ
-- =
-- ∇ (λ θ₀ => f (env.get_ks parents (env.insert tgt θ m)) θ₀) θ +
-- sumr (map (λ (idx : ℕ) =>
--             ∇ (λ θ₀ => f (dvec.update_at θ₀ (env.get_ks parents (env.insert tgt θ m)) idx) θ) θ)
--          (filter (λ idx => tgt = dnth parents idx) (riota $ length parents)))


end T
end certigrad

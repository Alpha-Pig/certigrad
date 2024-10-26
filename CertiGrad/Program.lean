/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

A Term language for conveniently constructing stochastic computation graphs.
-/
-- import .tensor .graph .tactics .ops data.hash_map

import CertiGrad.Tensor
import CertiGrad.Graph
import CertiGrad.Ops
import CertiGrad.Tactics


#print "compiling program..."

namespace certigrad
namespace program

-- open list

inductive UnaryOp : Type
| neg : UnaryOp
| exp : UnaryOp
| log : UnaryOp
| sqrt : UnaryOp
| softplus : UnaryOp
| sigmoid : UnaryOp

inductive BinaryOp : Type
| add : BinaryOp
| sub : BinaryOp
| mul : BinaryOp
| div : BinaryOp

inductive Term : Type
| unary : UnaryOp → Term → Term
| binary : BinaryOp → Term → Term → Term
| sum : Term → Term
| scale : TReal→ Term → Term
| gemm : Term → Term → Term
| mvn_kl : Term → Term → Term
| mvn_empirical_kl : Term → Term → Term → Term
| bernoulli_neglogpdf : Term → Term → Term
| id : label → Term

-- instance : has_neg Term := ⟨term.unary UnaryOp.neg⟩
-- instance : has_smul TRealterm := ⟨term.scale⟩
-- instance : has_add Term := ⟨term.binary BinaryOp.add⟩
-- instance : has_sub Term := ⟨term.binary BinaryOp.sub⟩
-- instance : has_mul Term := ⟨term.binary BinaryOp.mul⟩
-- instance : has_div Term := ⟨term.binary BinaryOp.div⟩

-- instance coe_id : has_coe label Term := ⟨term.id⟩

def exp : Term → Term := Term.unary UnaryOp.exp
def log : Term → Term := Term.unary UnaryOp.log
def sqrt : Term → Term := Term.unary UnaryOp.sqrt
def softplus : Term → Term := Term.unary UnaryOp.softplus
def sigmoid : Term → Term := Term.unary UnaryOp.sigmoid

inductive rterm : Type
| mvn : Term → Term → rterm
| mvn_std : S → rterm

inductive statement : Type
| param : label → S → statement
| input : label → S → statement
| cost : label → statement
| assign : label → Term → statement
| sample : label → rterm → statement

-- structure state : Type :=
--   (next_id : ℕ) (shapes : hash_map label (λ x => S))
--   (nodes : List node) (costs : List ID) (targets inputs : List Reference)

-- def empty_state : state := ⟨0, mk_hash_map (λ (x : label)=> x^.to_nat), [], [], [], []⟩

-- operators like `ops.neg` are currently commented out in `Ops.lean`
-- def unary_to_op (shape : S) : UnaryOp → det.op [shape] shape
-- | UnaryOp.neg      => ops.neg shape
-- | UnaryOp.exp      => ops.exp shape
-- | UnaryOp.log      => ops.log shape
-- | UnaryOp.sqrt     => ops.sqrt shape
-- | UnaryOp.softplus => ops.softplus shape
-- | UnaryOp.sigmoid  => ops.sigmoid shape

-- def binary_to_op (shape : S) : BinaryOp → det.op [shape, shape] shape
-- | BinaryOp.add     => ops.add shape
-- | BinaryOp.mul     => ops.mul shape
-- | BinaryOp.sub     => ops.sub shape
-- | BinaryOp.div     => ops.div shape

def get_id (next_id : ℕ) : Option ID → ID
| none => ID.nat next_id
| (some ident) => ident

/-
def process_term : Term → state → Option ID → Reference × state

| (term.unary f t) st ident :=
    match process_term t st none with
    | ((p₁, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) :=
      ((ID.nat $ next_id, shape),
        ⟨next_id+1, shapes,
         concat nodes ⟨(get_id next_id ident, shape), [(p₁, shape)], operator.det (unary_to_op shape f)⟩,
         costs, targets, inputs⟩)
    end

| (term.binary f t₁ t₂) st ident :=
    match process_term t₁ st none with
    | ((p₁, shape'), st') :=
    match process_term t₂ st' none with
    | ((p₂, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) :=
      ((get_id next_id ident, shape),
       ⟨next_id+1, shapes,
        concat nodes ⟨(get_id next_id ident, shape), [(p₁, shape), (p₂, shape)], operator.det (binary_to_op shape f)⟩,
               costs, targets, inputs⟩)
    end
    end

| (term.sum t) st ident :=
    match process_term t st none with
    | ((p₁, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) :=
      ((get_id next_id ident, []),
        ⟨next_id+1, shapes,
         concat nodes ⟨(get_id next_id ident, []), [(p₁, shape)], operator.det (ops.sum shape)⟩,
         costs, targets, inputs⟩)
    end

| (term.scale α t) st ident :=
    match process_term t st none with
    | ((p₁, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) :=
      ((get_id next_id ident, shape),
       ⟨next_id+1, shapes,
       concat nodes ⟨(get_id next_id ident, shape), [(p₁, shape)], operator.det (ops.scale α shape)⟩,
       costs, targets, inputs⟩)
    end

| (term.gemm t₁ t₂) st ident :=
    match process_term t₁ st none with
    | ((p₁, shape₁), st') :=
    match process_term t₂ st' none with
    | ((p₂, shape₂), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) :=
      let m := shape₁.head, n := shape₂.head, p := shape₂.tail.head in
      ((get_id next_id ident, [m, p]),
       ⟨next_id+1, shapes,
        concat nodes ⟨(get_id next_id ident, [m, p]), [(p₁, [m, n]), (p₂, [n, p])], operator.det (ops.gemm _ _ _)⟩,
        costs, targets, inputs⟩)
    end
    end

| (term.mvn_kl t₁ t₂) st ident :=
    match process_term t₁ st none with
    | ((p₁, shape'), st') :=
    match process_term t₂ st' none with
    | ((p₂, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) :=
      ((get_id next_id ident, []), ⟨next_id+1, shapes,
        concat nodes ⟨(get_id next_id ident, []), [(p₁, shape), (p₂, shape)], operator.det (ops.mvn_kl shape)⟩,
        costs, targets, inputs⟩)
    end
    end

| (term.mvn_empirical_kl t₁ t₂ t₃) st ident :=
    match process_term t₁ st none with
    | ((p₁, shape''), st') :=
    match process_term t₂ st' none with
    | ((p₂, shape'), st'') :=
    match process_term t₃ st'' none with
    | ((p₃, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) :=
      ((get_id next_id ident, []), ⟨next_id+1, shapes,
        concat nodes ⟨(get_id next_id ident, []), [(p₁, shape), (p₂, shape), (p₃, shape)], operator.det (det.op.mvn_empirical_kl shape)⟩,
        costs, targets, inputs⟩)
    end
    end
    end

| (term.bernoulli_neglogpdf t₁ t₂) st ident :=
    match process_term t₁ st none with
    | ((p₁, shape'), st') :=
    match process_term t₂ st' none with
    | ((p₂, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) :=
      ((get_id next_id ident, []),
        ⟨next_id+1, shapes,
         concat nodes ⟨(get_id next_id ident, []), [(p₁, shape), (p₂, shape)], operator.det (ops.bernoulli_neglogpdf shape)⟩,
         costs, targets, inputs⟩)
    end
    end

| (term.id s) ⟨next_id, shapes, nodes, costs, targets, inputs⟩ ident :=
   match shapes^.find s with
   | (some shape) := ((ID.str s, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩)
   | none         := (default _, empty_state)
   end

def process_rterm : rterm → state → Option ID → Reference × state
| (rterm.mvn t₁ t₂) st ident :=
    match process_term t₁ st none with
    | ((p₁, shape'), st') :=
    match process_term t₂ st' none with
    | ((p₂, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) :=
      ((get_id next_id ident, shape),
        ⟨next_id+1, shapes,
         concat nodes ⟨(get_id next_id ident, shape), [(p₁, shape), (p₂, shape)], operator.rand (rand.op.mvn shape)⟩,
         costs, targets, inputs⟩)
    end
    end

| (rterm.mvn_std shape) ⟨next_id, shapes, nodes, costs, targets, inputs⟩ ident :=
  ((get_id next_id ident, shape),
   ⟨next_id+1, shapes,
    nodes ++ [⟨(get_id next_id ident, shape), [], operator.rand (rand.op.mvn_std shape)⟩],
    costs, targets, inputs⟩)

def program_to_graph_core : List statement → state → state
| [] st := st

| (statement.assign s t::statements) st :=
  match process_term t st (some (ID.str s)) with
  | ((_, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) :=
     program_to_graph_core statements ⟨next_id, shapes^.insert s shape, nodes, costs, targets, inputs⟩
  end

| (statement.sample s t::statements) st :=
  match process_rterm t st (some (ID.str s)) with
  | ((_, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) :=
    program_to_graph_core statements ⟨next_id, shapes^.insert s shape, nodes, costs, targets, inputs⟩
  end

| (statement.param s shape::statements) ⟨next_id, shapes, nodes, costs, targets, inputs⟩ :=
  program_to_graph_core statements ⟨next_id, shapes^.insert s shape, nodes, costs, concat targets (ID.str s, shape), concat inputs (ID.str s, shape)⟩
| (statement.input s shape::statements) ⟨next_id, shapes, nodes, costs, targets, inputs⟩ :=
  program_to_graph_core statements ⟨next_id, shapes^.insert s shape, nodes, costs, targets, concat inputs (ID.str s, shape)⟩
| (statement.cost s::statements) ⟨next_id, shapes, nodes, costs, targets, inputs⟩ :=
  program_to_graph_core statements ⟨next_id, shapes, nodes, concat costs (ID.str s), targets, inputs⟩
-/
end program

def program := List program.statement

-- def program_to_graph : program → graph
-- | prog =>  match program.program_to_graph_core prog program.empty_state with
--            | ⟨next_id, shapes, nodes, costs, targets, inputs⟩ => ⟨nodes, costs, targets, inputs⟩
--            end

-- def mk_inputs : ∀ (g : graph), Dvec T g.inputs.p2 → env
-- | g, ws => env.insert_all g.inputs ws

end certigrad

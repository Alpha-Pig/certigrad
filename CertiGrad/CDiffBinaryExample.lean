import CertiGrad.Tensor
import CertiGrad.Tfacts
import CertiGrad.Tactics
import CertiGrad.SimpCdiff
import CertiGrad.SimpAttr

namespace certigrad
namespace T
open util_list

-- 这个示例演示如何使用is_cdifferentiable_binary证明二元函数的可微分性
-- 示例将专注于简单的实数类型 (TReal) 而不是一般的张量类型

-- 定义一个简单的二元函数
def binary_mul (x y : TReal) : TReal := x * y

-- 完整证明：手动应用is_cdifferentiable_binary
example {shape : S} (θ : T shape) : is_cdifferentiable (λ θ₀ => binary_mul θ₀ θ₀) θ := by
  -- 应用is_cdifferentiable_binary公理
  apply is_cdifferentiable_binary binary_mul θ
  
  -- 证明当第二个参数固定为θ时，函数是可微的
  -- 即证明 λ θ₀ => binary_mul θ₀ θ 是可微的，这相当于 λ θ₀ => θ₀ * θ
  -- 我们可以使用is_cdifferentiable_mul₁
  have h1 : is_cdifferentiable (λ θ₀ => θ₀ * θ) θ := by
    apply is_cdifferentiable_mul₁ (λ x => x) θ θ
    -- 证明恒等函数是可微的
    apply is_cdifferentiable_id
  
  -- 将h1适配为λ θ₀ => binary_mul θ₀ θ的形式
  have h1' : is_cdifferentiable (λ θ₀ => binary_mul θ₀ θ) θ := by
    -- 因为binary_mul θ₀ θ = θ₀ * θ，所以h1已经证明了我们需要的结果
    exact h1
  
  -- 证明当第一个参数固定为θ时，函数是可微的
  -- 即证明 λ θ₀ => binary_mul θ θ₀ 是可微的，这相当于 λ θ₀ => θ * θ₀
  -- 我们可以使用is_cdifferentiable_mul₂
  have h2 : is_cdifferentiable (λ θ₀ => θ * θ₀) θ := by
    apply is_cdifferentiable_mul₂ (λ x => x) θ θ
    -- 证明恒等函数是可微的
    apply is_cdifferentiable_id
  
  -- 将h2适配为λ θ₀ => binary_mul θ θ₀的形式
  have h2' : is_cdifferentiable (λ θ₀ => binary_mul θ θ₀) θ := by
    -- 因为binary_mul θ θ₀ = θ * θ₀，所以h2已经证明了我们需要的结果
    exact h2
  
  -- 组合h1'和h2'，完成证明
  exact ⟨h1', h2'⟩

-- 使用cdiff_simp自动证明
example {shape : S} (θ : T shape) : is_cdifferentiable (λ θ₀ => binary_mul θ₀ θ₀) θ := by
  -- 展开定义
  unfold binary_mul
  
  -- 使用simp only和cdiff_simp来简化目标
  simp only [cdiff_simp]
  
  -- 或者使用cdiff_simp tactic（如果已定义）
  -- cdiff_simp
  
  -- 如果上述方法不能完全解决问题，可能需要手动步骤
  -- 这里是debug选项，可以查看simp过程
  -- set_option trace.Meta.Tactic.simp true
  -- set_option trace.Meta.Tactic.simp.rewrite true
  
  -- 手动完成剩余证明
  -- 应用二元函数可微分性公理
  apply is_cdifferentiable_binary (λ x y => x * y) θ
  
  -- 证明当第二个参数固定为θ时是可微的
  apply is_cdifferentiable_mul₁ (λ x => x) θ θ
  apply is_cdifferentiable_id
  
  -- 证明当第一个参数固定为θ时是可微的
  apply is_cdifferentiable_mul₂ (λ x => x) θ θ
  apply is_cdifferentiable_id

-- 另一个例子：平方函数可以看作二元函数特化的例子
example {shape : S} (θ : T shape) : is_cdifferentiable (λ θ₀ => square θ₀) θ := by
  -- 将square展开为乘法
  have h : (λ θ₀ => square θ₀) = (λ θ₀ => binary_mul θ₀ θ₀) := by
    funext θ₀
    unfold binary_mul
    unfold square
    rw [mul_self_eq_square]
  
  -- 重写目标
  rw [h]
  
  -- 应用前面的例子
  apply is_cdifferentiable_binary binary_mul θ
  
  -- 证明当第二个参数固定为θ时是可微的
  have h1 : is_cdifferentiable (λ θ₀ => θ₀ * θ) θ := by
    apply is_cdifferentiable_mul₁ (λ x => x) θ θ
    apply is_cdifferentiable_id
  
  -- 将h1适配为所需形式
  have h1' : is_cdifferentiable (λ θ₀ => binary_mul θ₀ θ) θ := by
    unfold binary_mul at *
    exact h1
  
  -- 证明当第一个参数固定为θ时是可微的
  have h2 : is_cdifferentiable (λ θ₀ => θ * θ₀) θ := by
    apply is_cdifferentiable_mul₂ (λ x => x) θ θ
    apply is_cdifferentiable_id
  
  -- 将h2适配为所需形式
  have h2' : is_cdifferentiable (λ θ₀ => binary_mul θ θ₀) θ := by
    unfold binary_mul at *
    exact h2
  
  -- 组合完成证明
  exact ⟨h1', h2'⟩

-- 尝试使用直接的cdiff_simp简化
example {shape : S} (θ : T shape) : is_cdifferentiable (λ θ₀ => square θ₀) θ := by
  -- 在debug时可以打开这些选项观察简化过程
  -- set_option trace.Meta.Tactic.simp true
  -- set_option trace.Meta.Tactic.simp.rewrite true
  
  -- 使用cdiff_simp属性的规则简化
  simp only [cdiff_simp]
  
  -- 直接使用对应的square可微规则
  apply is_cdifferentiable_square (λ x => x) θ
  apply is_cdifferentiable_id

end T
end certigrad
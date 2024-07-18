--Syntax
inductive ty : Type
  | Ty_Bool : ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Prod : ty -> ty -> ty

inductive tm : Type
  | tm_var : String -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : String -> ty -> tm -> tm
  | tm_pair : tm -> tm -> tm
  | tm_proj1 : tm -> tm
  | tm_proj2 : tm -> tm
  | tm_true : tm
  | tm_false : tm

notation "<{" e:99 "}>" => e
notation S:50 " -> " T:50 => ty.Ty_Arrow S T
notation S:50 " × " T:50 => ty.Ty_Prod S T
notation "λ" x " : " t ", " y => tm.tm_abs x t y
notation " Bool " => ty.Ty_Bool
notation " true " => tm.tm_true
notation " false " => tm.tm_false
notation "⟨" t ", " t' "⟩" => tm.tm_pair t t'
notation "π₁ " u => tm.tm_proj1 u
notation "π₂ " u => tm.tm_proj2 u
infixl:99 " ∘ " => tm.tm_app

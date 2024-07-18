--- Rough first sketch to start setting up categories, following Abramsky. Need to change how contexts
--- are implemented to properly define semantics...work in progress

import StlcInLean.src.syntax
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

open CategoryTheory
open CategoryTheory.Closed

variable (C : Type) [Category C] [Limits.HasFiniteProducts C] [CartesianClosed C]

#check C
#check (Limits.terminal C)

variable (B : C)

noncomputable def semantic_translation_ty (t : ty) : C :=
  match t with
  | ty.Ty_Bool => B
  | ty.Ty_Arrow T₁ T₂ => (semantic_translation_ty T₁) ⟹ (semantic_translation_ty T₂)
  | ty.Ty_Prod T₁ T₂ => Limits.prod (semantic_translation_ty T₁) (semantic_translation_ty T₂)

notation "[[" T "]]" => semantic_translation_ty T

-- New definition for contexts: Lists of key value pairs instead of partial maps makes recursive definitions easier
def t_map (A : Type) := List (String × A)

def t_update {A : Type} (m : List (String × A)) (x : String) (v : A) : List (String × A) :=
  [(x, v)] ++ m

notation x " !-> " v " ; " m => t_update m x v

def context := List (String × ty)

def update (Γ : context) (x : String) (T: ty) :=
  x !-> T; Γ

notation x " ↦ " v " ; " m => update m x v

-- noncomputable def semantic_translation_ctx (Γ : context) : C :=
--   match Γ with
--   | [] => Limits.terminal C
--   | hd :: tl =>
--     Limits.prod ([[hd.2]]) (semantic_translation_ctx tl)

import StlcInLean.src.syntax

--Operational Semantics

---- Values
---- true and false are values, applications are not values,
---- abstractions are values - reduction stops at abstraction

inductive value : tm → Prop
  | v_abs : ∀ (x : String) (t : ty) (y : tm), value <{λx : t, y}>
  | v_true : value <{true}>
  | v_false : value <{false}>
  | v_pair : ∀ t1 t2, value t1 → value t2 → value <{⟨t1,t2⟩}>

  ---- Substitution
def subst (x : String) (s : tm) (t : tm) : tm :=
  match t with
    | tm.tm_var y => if (x == y) then s else t
    | <{y ∘ y'}> => tm.tm_app (subst x s y) (subst x s y')
    | <{λy : T, t1}> => if (x == y) then t else <{λy : T, (subst x s t1)}>
    | <{⟨t1, t2⟩}> => tm.tm_pair (subst x s t1) (subst x s t2)
    | <{π₁ u}> => tm.tm_proj1 (subst x s u)
    | <{π₂ u}> => tm.tm_proj2 (subst x s u)
    | <{true}> => <{true}>
    | <{false}> => <{false}>

notation "[" x ":=" s "]" t => subst x s t

---- Small-Step Operational Semantics

inductive step : tm -> tm -> Prop
  | ST_AppAbs : ∀ x t1 T2 v2,
    value v2 →
    step (tm.tm_app (<{λx : T2, t1}>) (v2)) (<{[x := v2] t1}>)
  | ST_App1 : ∀ t1 t1' t2,
    step t1 t1' →
    step (t1 ∘ t2) (t1' ∘ t2)
  | ST_App2 : ∀ t2 t2' v1,
    value v1 →
    step t2 t2' →
    step (v1 ∘ t2) (v1 ∘ t2')
  | ST_Pair1 : ∀ t1 t1' t2,
    step t1 t1' →
    step (⟨t1, t2⟩) (⟨t1', t2⟩)
  | ST_Pair2 : ∀ t2 t2' v1,
    value v1 →
    step t2 t2' →
    step (⟨v1, t2⟩) (⟨v1, t2'⟩)
  | ST_Proj1 : ∀ v1 v2,
    value v1 →
    value v2 →
    step (π₁ ⟨v1, v2⟩) v1
  | ST_Proj2 : ∀ v1 v2,
    value v1 →
    value v2 →
    step (π₂ ⟨v1, v2⟩) v2
  | ST_Fst : ∀ u u',
    step u u' →
    step (π₁ u) (π₁ u')
  | ST_Snd : ∀ u u',
    step u u' →
    step (π₂ u) (π₂ u')
infixl:99 "==>" => step

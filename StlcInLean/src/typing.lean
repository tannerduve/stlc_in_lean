import StlcInLean.src.maps
-- Typing

---- We let a context be a partial map for types
def context := partial_map ty

---- has_type Γ t T (equivalently, Γ |- t ∈ T) means that in the typing context Γ, the term t has type T
inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : ∀ Γ x T,
    Γ x = some T →
    has_type Γ (tm.tm_var x) T
  | T_Abs : ∀ x T1 T2 t1 Γ,
    has_type (x ↦ T2; Γ) t1 T1 →
    has_type Γ (<{λx : T2, t1}>) (T2->T1)
  | T_App : ∀ Γ t1 t2,
    has_type Γ t1 (T2 -> T1) ->
    has_type Γ t2 T2 ->
    has_type Γ (t1 ∘ t2) T1 -- t1 ∘ t2 means apply t1 to t2
  | T_Pair : ∀ Γ t1 t2 T U,
    has_type Γ t1 T →
    has_type Γ t2 U →
    has_type Γ ⟨t1, t2⟩ (T × U)
  | T_Proj1 : ∀ u T U,
    has_type Γ u (T × U) →
    has_type Γ (π₁ u) T
  | T_Proj2 : ∀ Γ u T U,
    has_type Γ u (T × U) →
    has_type Γ (π₂ u) U
  | T_True : ∀ Γ,
    has_type Γ true Bool
  | T_False : ∀ Γ,
    has_type Γ false Bool

notation Γ:99 " ⊢ " t1:99 " ∈ " T2:99 => has_type Γ t1 T2

import StlcInLean.src.semantics
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Use
import Mathlib.Tactic.Cases
import Mathlib.Tactic

axiom functional_extensionality : ∀ {X Y: Type}
                                    {f g : X → Y},
  (∀ (x:X), f x = g x) → f = g
------ Total and Partial Maps


-- We define a total map of type A as a function of type String → A

def total_map (A : Type) := String → A

-- The empty map for a type A given a default value v : A is a
-- total map which takes all inputs to v

def empty_map {A : Type} (v : A) : total_map A :=
  fun _ => v

-- We define the update function on total maps as follows:
-- If we want to "update" the map m with the assignment x ↦ v, we construct a new
-- function which returns v on input x but agrees with m on all other inputs

def t_update {A : Type} (m : String → A) (x : String) (v : A) : String → A :=
  fun x' => if x = x' then v else m x'

-- We denote this updated map as x !-> v ; m
notation x " !-> " v " ; " m => t_update m x v

-- Some useful properties of total maps:
---- A map m updated with the assignment x !-> v equals v when applied to x
theorem t_update_eq : ∀ (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v := by
  intros T m x v
  unfold t_update
  simp

---- A map m updated with the assignment x1 !-> v called on x2 where x2 ≠ x1
---- will return m x2
theorem t_update_neq : ∀ (A : Type) (m : total_map A) x1 x2 v,
  x1 ≠ x2 →
  (x1 !-> v ; m) x2 = m x2 := by
  intros T m x1 x2 v H
  unfold t_update
  simp
  intros
  contradiction

-- Recall that typing contexts are defined as partial maps taking Strings to Types.
-- Partial maps are defined in terms of option types
-- Option types represent values which may or may not exist, given a type A, the type
-- Option A is defined as follows:

-- inductive Option ( A : Type ) : Type :=
-- | some : A -> Option A
-- | none : Option A

-- This allows us to define partial maps - if a partial map f is not defined on x,
-- f x = none, otherwise f x = some y

def partial_map (α : Type) := total_map (Option α)

-- We define empty partial map and update for partial maps analogously:

def empty {α : Type} : partial_map α :=
  empty_map none

def update {A : Type} (m : partial_map A) (x : String) (v : A) : partial_map A :=
  x !-> some v ; m

-- We denote update for partial maps with the nicer ↦ notation: x ↦ v; m is
-- the map m with x assigned to v

notation x " ↦ " v " ; " m => update m x v

-- The corresponding theorems for update on partial maps are proven here

theorem update_eq : ∀ (A : Type) (m : partial_map A) x v,
  (x ↦ v ; m) x = some v := by
  intros T m x v
  unfold update
  rw [t_update_eq]

theorem update_neq : ∀ (T : Type) (m : partial_map T) x1 x2 v,
  x1 ≠ x2 →
  (x1 ↦ v ; m) x2 = m x2 := by
  intros T m x1 x2 v h
  unfold update
  apply t_update_neq
  exact h

#check Eq.symm

lemma neqSymm : x ≠ y → y ≠ x := by
  intro h
  intro h'
  apply h
  exact (Eq.symm h')

-- Some important properties of partial maps to be used in our type soundness proof:

---- We say a map f is included in f' if all the entries in f appear in f'
def includedin {A : Type} (m m' : partial_map A) :=
  ∀ x v, (m x) = some v → (m' x) = some v

---- Map update preserves inclusion: if m is included in m', then updating
---- each with the same assignment will preserve this inclusion.
lemma includedin_update : ∀ (T : Type) (m m' : partial_map T) (x : String) (v : T),
  includedin m m' → includedin (x ↦ v; m) (x ↦ v; m') := by
unfold includedin
intros T m m' x v H
intros x1 x2 HT
by_cases h : x1 = x
· rw [h, update_eq]
  rw [h, update_eq] at HT
  exact HT
· have hneq : x1 ≠ x := by
    { intro h'; contradiction }
  rw [update_neq]
  rw [update_neq] at HT
  apply H
  exact HT
  symm
  apply hneq
  symm at hneq
  apply hneq

---- For two distinct assignments, the order in which we update does not matter;
---- updating is commutative (Note the use of functional extensionality axiom)
theorem update_permute : ∀ (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
  x2 ≠ x1 →
  (x1 ↦ v1 ; x2 ↦ v2 ; m) = (x2 ↦ v2 ; x1 ↦ v1 ; m) := by
  intros A m x1 x2 v1 v2 H
  apply funext
  revert x1 x2
  unfold update
  intros x1 x2 H x
  by_cases h : (x1 = x)
  · by_cases h1 : (x2 = x)
    have h2 : x1 = x2 := by
      { rw [h1]
        exact h }
    symm at h2
    contradiction
    · rw [h]
      simp only [t_update, if_pos, if_neg H, h1]
      simp
  · by_cases h1 : (x2 = x)
    · rw [h1]
      simp only [t_update, if_pos, h]
      simp
    · simp only [t_update, if_neg h, if_neg h1]

---- Updating the same variable with two different assignments keeps only the most recent
---- assignment
theorem update_shadow : ∀ (T : Type) (m : partial_map T) x v1 v2,
  (x ↦ v1; x ↦ v2; m) = (x ↦ v1; m) := by
  intros T m x v1 v2
  apply funext
  intros x1
  by_cases h : (x = x1)
  rw [h, update_eq, update_eq]
  rw [update_neq, update_neq, update_neq]
  <;> apply h

#check funext

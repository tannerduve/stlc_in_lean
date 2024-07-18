import StlcInLean.src.typing

-- We aim to prove our type system is sound, that is, our typing relation only accepts terms which
-- are valid in a computational sense. This means well-typed terms do not get "stuck".

-- This requires two parts, which we call progress and preservation. Progress states that any term is either
-- a value or can be reduced further, and preservation states that types are preserved under reduction.

-- We develop all the necessary theory to prove type soundness below

--- Canonical Forms
---- If a term is of type bool, then it is either true or false,
---- If a term is an arrow type, then it must be of the form λx:T, t
---- If a value is a product type, then it must be a pair

lemma canonical_form_bool : ∀ t : tm,
  empty ⊢ t ∈ Bool →
  value t →
  ((t = <{true}>) ∨ (t = <{false}>)) := by
  intros t HT HVal
  cases HT
  case T_True
  · left
    rfl
  case T_False
  · right
    rfl
  all_goals {contradiction}

lemma canonical_form_fun : ∀ t T1 T2,
  empty ⊢ t ∈ (T1 -> T2) →
  value t →
  ∃ x, ∃ u, t = <{λx:T1, u}> := by
  intros t T1 T2 HT HVal
  cases HT
  case T_Abs x t1 a
  · use x
    use t1
  all_goals {contradiction}

lemma canonical_form_pair : ∀ u T U,
  empty ⊢ u ∈ (T × U) →
  value u →
  ∃ t1 t2, u = <{⟨t1, t2⟩}> := by
  intros u T U H Ht
  cases H
  case T_Pair t1 t2 H tTyp
  · use t1, t2
  all_goals {contradiction}


-- Progress - any well-typed term is either a value or reduces to another term
-- Proof by induction on terms
theorem progress : ∀ t T,
  empty ⊢ t ∈ T →
  (value t) ∨ (∃ t', t ==> t') := by
  intros t
  induction' t with x a1 a2 a_ih1 a_ih2 x T t1 _ a1 a2 a_ih1 a_ih2 a a_ih a a_ih
  <;> intros T HT
  <;> try contradiction
  case tm_true
  · left
    apply value.v_true
  case tm_false
  · left
    apply value.v_false
  case tm_abs
  · left
    apply value.v_abs
  case tm_app
  · right
    cases' HT
    · case tm_app.h.T_App T2 H3 H4
      have HA3 : value a1 ∨ ∃ t', a1==>t' := by
        {apply a_ih1; apply H4}
      have HA4 : value a2 ∨ ∃ t', a2 ==> t' := by
        {apply a_ih2; apply H3}
      rcases HA3 with h | h'
      · rcases HA4 with h1 | h2
        have tAbs : ∃ x, ∃ u, a1 = <{λx:T2, u}> := by
          { apply canonical_form_fun; apply H4; exact h }
        cases' tAbs with x H
        cases' H with u H'
        rw [H']
        use <{[x := a2] u}>
        apply step.ST_AppAbs
        apply h1
        cases' h2 with t' Ht'
        use (a1 ∘ t')
        apply step.ST_App2
        exact h
        exact Ht'
      cases' h' with t Ht
      use (t ∘ a2)
      apply step.ST_App1 a1 t a2 Ht
  case tm_pair
  · cases' HT
    case tm_pair.T_Pair T U t1 t2
    have HA3 : value a1 ∨ ∃ a1', a1 ==> a1' := a_ih1 T t1
    have HA4 : value a2 ∨ ∃ t', a2 ==> t' := a_ih2 U t2
    rcases HA3 with h1 | h2
    · rcases HA4 with h | h'
      · left
        apply value.v_pair a1 a2 h1 h
      · right
        cases' h' with t' ht
        use ⟨a1, t'⟩
        apply step.ST_Pair2 a2 t' a1 h1 ht
    case tm_pair.T_Pair.inr
    · rcases HA4 with _ | _
      right
      cases' h2 with t' h2
      use ⟨t', a2⟩
      apply step.ST_Pair1
      apply h2
      right
      cases' h2 with t' h2
      use ⟨t', a2⟩
      apply step.ST_Pair1 a1 t' a2 h2
  cases' HT
  case tm_proj1.T_Proj1 U a1
  · have h : value a ∨ ∃ t', a==>t' := a_ih (T × U) a1
    rcases h with val | steps1
    right
    have hyp : ∃ t1 t2, a = <{⟨t1,t2⟩}> := canonical_form_pair a T U a1 val
    rcases hyp with ⟨t1, t2, hyp⟩
    rw [hyp]
    rw [hyp] at val
    cases val
    case tm_proj1.T_Proj1.inl.h.intro.intro.v_pair t1Val t2Val
    · use t1
      apply step.ST_Proj1 t1 t2 t1Val t2Val
    case tm_proj1.T_Proj1.inr
    · rcases a1
      <;> try contradiction
      case tm_proj1.T_Proj1.inr.T_Pair t1 t2 t1Typ t2Typ
      · have h : value ⟨t1, t2⟩ ∨ ∃ t', ⟨t1, t2⟩==>t' := by
          { apply a_ih (T × U)
            apply has_type.T_Pair empty t1 t2 T U t1Typ t2Typ
          }
        rcases h with val | steps2
        right
        use t1
        have tval : value t1 ∧ value t2 := by
          { constructor
            cases' val;
            case v_pair valt1 valt2;
            apply valt1;
            cases' val;
            case v_pair valt1 valt2;
            apply valt2;
             }
        apply step.ST_Proj1 t1 t2 tval.left tval.right
        right
        cases' steps2 with w Hw
        use π₁ w
        apply step.ST_Fst ⟨t1, t2⟩ w Hw
      case tm_proj1.T_Proj1.inr.T_App T2 t1 t2 Ht2 H1
      · right
        cases' steps1 with t' Ht'
        use (π₁ t')
        apply step.ST_Fst (t1 ∘ t2) t' Ht'
      case tm_proj1.T_Proj1.inr.T_Proj1 u U' Hu
      · right
        cases' steps1 with t' Ht'
        use (π₁ t')
        apply step.ST_Fst (π₁ u) (t') Ht'
      case tm_proj1.T_Proj1.inr.T_Proj2 u T' HT
      · right
        cases' steps1 with t' Ht'
        use (π₁ t')
        apply step.ST_Fst (π₂ u) (t') Ht'
  · cases' HT
    case tm_proj2.T_Proj2 T' HT
    have Ha : value a ∨ ∃ t', a==>t' := a_ih (T' × T) HT
    rcases Ha with val | steps
    right
    have pair : ∃ t1 t2, a = ⟨t1, t2⟩ := canonical_form_pair a T' T HT val
    cases' pair with t1 Ht1
    cases' Ht1 with t2 Ht2
    rw [Ht2]
    rw [Ht2] at val
    cases' val
    case tm_proj2.T_Proj2.inl.h.intro.intro.v_pair t1Val t2Val
    · use t2
      apply step.ST_Proj2 t1 t2 t1Val t2Val
    case tm_proj2.T_Proj2.inr
    · right
      cases' steps with t' Ht'
      use (π₂ t')
      apply step.ST_Snd a t' Ht'

-- The preservation theorem is the second half of type soundness - it states that types
-- are preserved through reduction.
-- More formally, for any term t and type T, if ∅ ⊢ t ∈ T and t reduces to
-- t' for some term t', then ∅ ⊢ t' ∈ T

-- To prove this we need to prove a couple lemmas which will rely on some
-- properties of partial maps - recall that our typing contexts
-- are defined as partial maps associating strings to types

-- We prove preservation by induction on the premise that t reduces to t'
-- For the β-reduction (ST_AppAbs) case, since this definition uses substitution,
-- we need to show that the substitution preserves typing, a "substitution lemma" -
-- if t has type T, then [x:=s]t has type T

-- To prove the substitution lemma, we induct on t, and in the variable case
-- we find ourselves needing to deduce from the fact that a term s has type T in
-- the empty context, it will have type T in every context, to prove this,
-- we use a "weakening" lemma - stated and proven below:

-- Weakening: if context Γ is included in context Γ', and t has type T in Γ, then
-- t has type T in Γ':


lemma weakening : ∀ Γ Γ' t T,
  includedin Γ Γ' →
  Γ ⊢ t ∈ T →
  Γ' ⊢ t ∈ T := by
  intros Γ Γ' t T H Ht
  revert Γ'
  induction Ht
  case T_Var Γ' x a H
  · intros Γ1 H1
    apply has_type.T_Var
    unfold includedin at H1
    apply H1
    exact H
  case T_Abs x T1 T2 t1 Γ1 _ ih
  · intros Γ' H'
    apply has_type.T_Abs
    apply ih
    apply includedin_update ty Γ1 Γ' x T2 H'
  case T_App T2 T1 Γ1 t1 t2 t1Typ t2Typ ih1 ih2
  · intros Γ' H
    apply has_type.T_App
    apply ih1 Γ' H
    apply ih2 Γ' H
  case T_True Γ'
  · intros Γ1 _
    apply has_type.T_True
  case T_False Γ'
  · intros Γ1 _
    apply has_type.T_False
  case T_Pair Γ' t1 t2 T' U' _ _ ih1 ih2
  · intros Γ2 Hinc
    apply has_type.T_Pair
    apply ih1 Γ2 Hinc
    apply ih2 Γ2 Hinc
  case T_Proj1 Γ1 u T' U' _ ih
  · intros Γ2 Hinc
    apply has_type.T_Proj1 u T' U'
    apply ih Γ2 Hinc
  case T_Proj2 Γ1 u T' U' _ ih
  · intros Γ2 Hinc
    apply has_type.T_Proj2 Γ2 u T' U'
    apply ih Γ2 Hinc

-- Now we prove what we really need: if t has type T in the empty context,
-- t has type T in every context
lemma weakening_empty : ∀ Γ t T,
  empty ⊢ t ∈ T →
  Γ ⊢ t ∈ T := by
  intros Γ t T H
  apply weakening empty Γ t T
  intros x t1 H1
  contradiction
  assumption

-- Another useful lemma: Typing contexts are "injective"
lemma unique_typing : ∀ (Γ : context) (x : String) (T U : ty),
  Γ x = some T → Γ x = some U → T = U := by
  intros Γ x T U hT hU
  rw [hT] at hU
  injection hU

-- Now the substitution lemma, if t has type T in any context, then the result of
-- substituting a variable x for a term v in t (where x and v have the same type), will
-- also have type T
lemma substitution_preserves_typing : ∀ Γ t x v T U,
  (x ↦ U; Γ) ⊢ t ∈ T →
  empty ⊢ v ∈ U →
  Γ ⊢ ([x:=v]t) ∈ T := by
  intros Γ t x v T U H1 H2
  revert Γ
  revert T
  induction t
  <;> try contradiction
  case tm_var x'
  · intros T Γ H1
    by_cases h: x = x'
    rw [← h]
    simp [subst]
    rw [h] at H1
    cases' H1
    case pos.T_Var hyp
    · have x'U : (x' ↦ U ; Γ) x' = some U := by { apply update_eq }
      have TU : T = U := unique_typing (x' ↦ U ; Γ) x' T U hyp x'U
      rw [← TU] at H2
      apply weakening_empty Γ v T H2
    simp [subst, h]
    apply has_type.T_Var
    cases' H1
    case neg.a.T_Var a1
    · have h1 : (x ↦ U ; Γ) x' = Γ x' := by
        { apply update_neq;
          apply h }
      rw [← a1]
      symm
      exact h1
  case tm_app a1 a2 IH1 IH2
  · intros T Γ H1
    cases H1
    case tm_app.T_App T2 a3 a4
    · simp [subst]
      apply has_type.T_App
      specialize IH1 (T2 -> T)
      apply IH1 Γ a4
      apply IH2 T2 Γ a3
  case tm_abs a1 T t IH
  · intros T1 Γ H1
    by_cases h : (x = a1)
    rw [← h]
    rw [← h] at H1
    cases' H1
    case pos.T_Abs T1 a2
    · simp [subst]
      apply has_type.T_Abs
      have h1 : (x ↦ T ; x ↦ U ; Γ) = (x ↦ T; Γ) := by rw [update_shadow]
      rw [← h1]
      assumption
    simp [subst, h]
    cases' H1
    case neg.T_Abs T1 b
    · apply has_type.T_Abs
      apply IH
      rw [update_permute]
      assumption
      symm
      apply h
  case tm_pair a1 a2 ih1 ih2
  · intros T2 Γ2 H
    simp [subst]
    cases H
    case tm_pair.T_Pair T' U' HT' HU'
    · apply has_type.T_Pair
      apply ih1 T' Γ2 HT'
      apply ih2 U' Γ2 HU'
  case tm_proj1 a ih
  · intros T Γ H1
    simp [subst]
    cases H1
    case tm_proj1.T_Proj1 U' HU'
    · have h : Γ ⊢ ([x:=v]a) ∈ (T × U') := ih (T × U') Γ HU'
      apply has_type.T_Proj1 ([x:=v]a) T U' h
  case tm_proj2 a ih
  · intros T Γ H1
    simp [subst]
    cases H1
    case tm_proj2.T_Proj2 U' HU'
    · have h : Γ ⊢ ([x:=v]a) ∈ (U' × T) := ih (U' × T) Γ HU'
      apply has_type.T_Proj2 Γ ([x:=v]a) U' T h
  all_goals {
      intros T Γ H1;
      simp [subst];
      cases' H1
      try apply has_type.T_False
      try apply has_type.T_True
  }

-- Preservation theorem : Types are preserved under reduction. We proceed by induction
-- on the hypothesis that t ==> t'.
theorem preservation : ∀ t t' T,
empty ⊢ t ∈ T →
t ==> t' →
empty ⊢ t' ∈ T := by
intros t t' T H1 H2
revert T
induction H2
case ST_AppAbs x t1 T1 t2 _
· intros T H1
  cases H1
  case ST_AppAbs.T_App T2 h h1
  · cases h1
    case ST_AppAbs.T_App.T_Abs ha
    · apply substitution_preserves_typing empty t1 x t2 T T1 ha h
case ST_App1 t1 t2 t3 _ ih
· intros T H1
  cases H1
  case ST_App1.T_App T2 hyp1 hyp2
  · apply has_type.T_App
    apply ih (T2 -> T) hyp2
    exact hyp1
case ST_App2 t1 t2 v1 _ _ ih
· intros T hyp
  cases' hyp
  case ST_App2.T_App T2 a a1
  · apply has_type.T_App empty v1 t2 a1
    apply ih T2 a
case ST_Pair1 t1 t2 t3 _ ih
· intros T H1
  cases H1
  case ST_Pair1.T_Pair T U typ1 typ2
  · apply has_type.T_Pair
    apply ih T typ1
    apply typ2
case ST_Pair2 t1 t2 t3 _ _ ih
· intros T HT
  cases HT
  case ST_Pair2.T_Pair T U typ1 typ2
  · apply has_type.T_Pair empty t3 t2 T U typ1
    apply ih U typ2
case ST_Proj1 v1 v2 _ _
· intros T HT
  cases HT
  case ST_Proj1.T_Proj1 U HU
  · cases HU
    case ST_Proj1.T_Proj1.T_Pair H1 H2
    · exact H1
case ST_Proj2 v1 v2 _ _
· intros T HT
  cases HT
  case ST_Proj2.T_Proj2 U HU
  · cases HU
    case ST_Proj2.T_Proj2.T_Pair H1 H2
    · exact H2
case ST_Fst u u' _ ih
· intros T HT
  cases HT
  case ST_Fst.T_Proj1 U HU
  · have u'typ : empty ⊢ u' ∈ T × U := ih (T × U) HU
    apply has_type.T_Proj1 u' T U u'typ
case ST_Snd u u' _ ih
· intros T HT
  cases HT
  case ST_Snd.T_Proj2 U HU
  · have u'typ : empty ⊢ u' ∈ U × T := ih (U × T) HU
    apply has_type.T_Proj2 empty u' U T u'typ

-- Now we want to put these together to prove that our type system is sound, that is,
-- well-typed terms don't get "stuck". First need to define a few more things

-- A normal form is a term which can not reduce any further
def normal_form
    (t : tm) : Prop :=
  ¬ ∃ t', step t t'

-- We say a term is stuck if it can not reduce but is not one of our defined values
def stuck (t:tm) : Prop :=
  normal_form t ∧ ¬ value t

-- We define here the transitive closure of a binary relation on terms.
-- We use this to capture multi-step reduction (λ-reduction)

inductive multi (R : tm -> tm -> Prop) : tm -> tm -> Prop :=
  | single x y (H : R x y) : multi R x y
  | trans_closure x y z (H : R x y) :
      multi R y z → multi R x z

-- We denote this with a little ⋆
infixl:99 " ==>⋆ " => multi step

-- Now our final theorem : if t is well-typed, and t reduces to t' in some number of
-- steps, then t' is not stuck.
theorem type_soundness : ∀ (t t' : tm) T,
  empty ⊢ t ∈ T →
  t ==>⋆ t' →
  ¬ (stuck t') := by
  intros t t' T tTyp Hmulti
  induction Hmulti
  case single x y H
  · intro contra
    have yTyp : empty ⊢ y ∈ T := preservation x y T tTyp H
    have Hy : (value y ∨ ∃ t', y ==> t') := progress y T yTyp
    rcases contra with ⟨left, right⟩
    rcases Hy with yVal | yStep
    contradiction
    unfold normal_form at left
    contradiction
  case trans_closure x y z H1 _ ih
  · have h : empty ⊢ y ∈ T := preservation x y T tTyp H1
    apply ih h

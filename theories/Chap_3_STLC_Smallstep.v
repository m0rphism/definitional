From Coq Require Import
  Lists.List.

From Theories Require Import
  Tactics.

Import ListNotations.
Open Scope list_scope.

Notation List := list.

Notation Opt := option.
Notation some := Some.
Notation none := None.

Fixpoint index {X : Type} (n : nat) (xs : List (nat * X)) : Opt X :=
  match xs with
  | []      => none
  | (n', x) :: xs' => if beq_nat n n' then some x else index n xs'
  end.

Inductive Multi {X} (R : X -> X -> Prop) : X -> X -> Prop :=
  | m_refl :
      forall x,
      Multi R x x
  | m_step :
      forall x1 x2 x3,
      Multi R x1 x2 ->
      R x2 x3 ->
      Multi R x1 x3
  .

Lemma index_neq :
  forall {X} x y t (te : List (nat * X)),
  not (x = y) ->
  index x ((y, t) :: te) = index x te.
Proof.
  intros until 0; intros Hneq.
  simpl.
  rewrite (proj2 (Nat.eqb_neq x y) Hneq).
  reflexivity.
Qed.

Lemma index_eq_same :
  forall {X} x (te' te : List (nat * X)) x0 t1 t2 t,
  index x (te' ++ (x0, t1) :: (x0, t2) :: te) = some t ->
  index x (te' ++ (x0, t1) :: te) = some t.
Proof.
  intros until 0; intros Heq.
  induction te'.
  Case "te' = []".
    simpl in *.
    destruct (x =? x0).
      eauto.
      eauto.
  Case "te' = a :: te'".
    destruct a as [x' t'].
    simpl in *.
    destruct (x =? x').
      eauto.
      eauto.
Qed.


(** * Specification *)

(** ** Syntax *)

Inductive Typ :=
  | t_void
  | t_arr (t1 t2 : Typ).

Inductive Exp :=
  | e_var (x : nat)
  | e_app (e1 e2 : Exp)
  | e_abs (x : nat) (e : Exp).

Inductive Val : Exp -> Prop :=
  | v_abs : forall x e, Val (e_abs x e).

Definition TypEnv := List (nat * Typ).

Inductive ExpTyp : TypEnv -> Exp -> Typ -> Prop :=
  | et_var :
      forall x te t1,
      index x te = some t1 ->
      ExpTyp te (e_var x) t1
  | et_app :
      forall te e1 e2 t1 t2,
      ExpTyp te e1 (t_arr t1 t2) ->
      ExpTyp te e2 t1 ->
      ExpTyp te (e_app e1 e2) t2
  | et_abs :
      forall te e t1 t2 x,
      ExpTyp ((x, t1) :: te) e t2 ->
      ExpTyp te (e_abs x e) (t_arr t1 t2)
  .

 (* Technical note: Substitution becomes trickier to define if we consider the
 case where s, the term being substituted for a variable in some other term, may
 itself contain free variables. Since we are only interested here in defining
 the step relation on closed terms (i.e., terms like \x:Bool. x that include
 binders for all of the variables they mention), we can sidestep this extra
 complexity, but it must be dealt with when formalizing richer languages. *)
Fixpoint subst (x : nat) (e' e : Exp) : Exp :=
  match e with
  | e_var y => if beq_nat x y then e' else e_var y
  | e_app e1 e2 => e_app (subst x e' e1) (subst x e' e2)
  | e_abs y e =>  e_abs y (if beq_nat x y then e else subst x e' e)
  end.

Inductive Step : Exp -> Exp -> Prop :=
  | s_beta :
    forall x e1 e2,
    Val e2 ->
    Step (e_app (e_abs x e1) e2) (subst x e2 e1)
  | s_app1 :
    forall e1 e2 e1',
    Step e1 e1' ->
    Step (e_app e1 e2) (e_app e1' e2)
  | s_app2 :
    forall e1 e2 e2',
    Val e1 ->
    Step e2 e2' ->
    Step (e_app e1 e2) (e_app e1 e2')
  .

(** * Theorems *)

Hint Constructors Typ Exp Val ExpTyp Step Multi Opt List.
Hint Unfold index length TypEnv subst.
Hint Resolve ex_intro.

Theorem progress :
  forall e t,
  ExpTyp [] e t ->
  Val e \/ exists e', Step e e'.
Proof.
  intros until 0; intros et.
  dependent induction et.
  Case "et_app".
    right.
    specialize (IHet1 ltac:(reflexivity)).
    specialize (IHet2 ltac:(reflexivity)).
    destruct IHet1.
    Case2 "Val e1".
      inversion H; subst.
      destruct IHet2.
      Case3 "Val e2".
        eexists. eapply s_beta. assumption.
      Case3 "Step e2 e2'".
        destruct H0 as [e2' Hstep2].
        eexists. eapply s_app2; eassumption.
    Case2 "Step e1 e1'".
      destruct H as [e1' Hstep1].
      eexists. eapply s_app1; eassumption.
  Case "et_abs".
    left. eapply v_abs.
Qed.

Inductive FreeIn : nat -> Exp -> Prop :=
  | fi_var :
      forall x,
      FreeIn x (e_var x)
  | fi_app1 :
      forall x e1 e2,
      FreeIn x e1 ->
      FreeIn x (e_app e1 e2)
  | fi_app2 :
      forall x e1 e2,
      FreeIn x e2 ->
      FreeIn x (e_app e1 e2)
  | fi_abs :
      forall x y e,
      not (y = x) ->
      FreeIn x e ->
      FreeIn x (e_abs y e)
  .

Definition Closed (e : Exp) : Prop :=
  forall x, not (FreeIn x e).

Lemma free_in_context :
  forall x e t te,
  FreeIn x e ->
  ExpTyp te e t ->
  exists t', index x te = some t'.
Proof.
  intros x e t te Hfi.
  revert t te.
  induction Hfi; intros t te et.
  Case "fi_var".
    eexists. inversion et; subst. eauto.
  Case "fi_app1".
    inversion et; subst.
    eapply IHHfi.
    eassumption.
  Case "fi_app2".
    inversion et; subst.
    eapply IHHfi.
    eassumption.
  Case "fi_abs".
    inversion et; subst.
    eapply IHHfi in H4.
    erewrite index_neq in H4; eauto.
Qed.

Corollary typable_empty_closed :
  forall e t,
  ExpTyp [] e t ->
  Closed e.
Proof.
  intros until 0; intros et x fi.
  eapply free_in_context with (te := []) in fi.
  - inversion fi. inversion H.
  - exact et.
Qed.

Lemma context_invariance :
  forall te te' e t,
  ExpTyp te e t ->
  (forall x, FreeIn x e -> index x te = index x te') ->
  ExpTyp te' e t.
Proof.
  intros until 0; intros et.
  revert te'.
  induction et; intros te' Hsub.
  Case "et_var".
    econstructor.
    rewrite <- H.
    symmetry.
    eapply Hsub.
    econstructor.
  Case "et_app".
    econstructor.
      eapply IHet1. intros y Hfi. eapply Hsub. econstructor; exact Hfi.
      eapply IHet2. intros y Hfi. eapply Hsub. econstructor; exact Hfi.
  Case "et_abs".
    econstructor.
    eapply IHet.
    intros y Hfi.
    case_eq (y =? x); intros Heq.
    Case2 "y =? x = true".
      unfold index. rewrite Heq. reflexivity.
    Case2 "y =? x = false".
      unfold index. rewrite Heq. fold @index.
      eapply Hsub.
      econstructor.
        eapply Nat.eqb_neq. rewrite Nat.eqb_sym. exact Heq.
        exact Hfi.
Qed.

Lemma update_shadow :
  forall x t1 t2 te te' e t,
  ExpTyp (te' ++ (x, t1) :: (x, t2) :: te) e t ->
  ExpTyp (te' ++ (x, t1) :: te) e t.
Proof.
  intros x t1 t2 te te' e t.
  revert x t1 t2 te te' t.
  induction e; intros until 0; intros et.
  Case "et_var".
    inversion et; subst.
    econstructor.
    eapply index_eq_same.
    eauto.
  Case "et_app".
    inversion et; subst.
    eauto.
  Case "et_abs".
    inversion et; subst.
    econstructor.
    rewrite app_comm_cons.
    eapply IHe.
    eauto.
Qed.

Lemma subst_preserves_exptyp :
  forall te x t1 t2 e1 e2,
  ExpTyp ((x, t2) :: te) e1 t1 ->
  ExpTyp [] e2 t2 ->
  ExpTyp te (subst x e2 e1) t1.
Proof.
  intros te x t1 t2 e1; revert te x t1 t2.
  induction e1; intros until 0; intros et1 et2.
  Case "e_var".
    inversion et1; subst.
    simpl in *.
    rewrite Nat.eqb_sym in H1.
    destruct (x0 =? x).
    Case2 "x0 =? x = true".
      inversion H1; subst.
      eapply context_invariance.
      exact et2.
      eapply typable_empty_closed in et2.
      unfold Closed in et2.
      intros x1 fi.
      apply (et2 x1) in fi.
      inversion fi.
    Case2 "x0 =? x = false".
      eapply et_var. assumption.
  Case "e_app".
    inversion et1; subst.
    simpl.
    eapply et_app.
      eapply IHe1_1. eassumption. eassumption.
      eapply IHe1_2. eassumption. eassumption.
  Case "e_abs".
    inversion et1; subst.
    simpl.
    eapply et_abs.
    case_eq (x0 =? x); intros Heq.
    Case2 "x0 =? x = true".
      rewrite Nat.eqb_eq in Heq. subst.
      eapply update_shadow with (te' := []) in H3.
      simpl in H3.
      exact H3.
    Case2 "x0 =? x = false".
      eapply IHe1.
        eapply context_invariance. eassumption.
          intros x1 fi.
          simpl.
          case_eq (x1 =? x); intros Heq2.
          Case3 "x1 =? x = true".
            rewrite Nat.eqb_eq in Heq2. subst.
            rewrite Nat.eqb_sym.
            rewrite Heq.
            reflexivity.
          Case3 "x1 =? x = false".
            reflexivity.
        eassumption.
Qed.

Theorem preservation :
  forall e e' t,
  ExpTyp [] e t ->
  Step e e' ->
  ExpTyp [] e' t.
Proof.
  intros e e' t et.
  revert e'.
  dependent induction et; intros e' s.
  Case "et_app".
    specialize (IHet1 ltac:(reflexivity)).
    specialize (IHet2 ltac:(reflexivity)).
    inversion s; subst.
    Case2 "s_beta".
      inversion et1; subst.
      eapply subst_preserves_exptyp.
        exact H1.
        exact et2.
    Case2 "s_app1".
      econstructor.
        eapply IHet1. exact H2.
        exact et2.
    Case2 "s_app2".
      econstructor.
        exact et1.
        eapply IHet2. exact H3.
  Case "et_abs".
    inversion s.
Qed.

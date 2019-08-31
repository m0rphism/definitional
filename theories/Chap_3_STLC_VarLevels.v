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

(** * Specification *)

Inductive Typ := t_void | t_arr (t1 t2 : Typ).
Inductive Exp := e_var (x : nat) | e_app (e1 e2 : Exp) | e_abs (e : Exp).
Inductive Val := v_abs (ve : List Val) (e : Exp).

Definition ValEnv := List Val.
Definition TypEnv := List Typ.

Fixpoint index {X : Type} (n : nat) (xs : List X) : Opt X :=
  match xs with
  | []      => none
  | x :: xs' => if beq_nat n (length xs') then some x else index n xs'
  end.

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
      forall te e t1 t2,
      ExpTyp (t1 :: te) e t2 ->
      ExpTyp te (e_abs e) (t_arr t1 t2)
  .

Inductive WfEnv : ValEnv -> TypEnv -> Prop :=
  | wfe_nil :
      WfEnv [] []
  | wfe_cons :
      forall v t ve te,
      ValTyp v t ->
      WfEnv ve te ->
      WfEnv (v :: ve) (t :: te)
with ValTyp : Val -> Typ -> Prop :=
  | vt_abs :
      forall ve te e t1 t2,
      WfEnv ve te ->
      ExpTyp (t1 :: te) e t2 ->
      ValTyp (v_abs ve e) (t_arr t1 t2)
  .

(* Note that this notation allows [MonadFail] style patterns for [p]. *)
Notation "' p <- e1 ; e2" :=
  (match e1 with
   | some (some p) => e2
   | some _ => some none
   | none => none
   end)
  (right associativity, at level 60, p pattern).

Fixpoint eval (n : nat) (ve : ValEnv) (e : Exp) : Opt (Opt Val) :=
  match n with
  | 0 => none
  | S n =>
      match e with
      | e_var x => some (index x ve)
      | e_abs e => some (some (v_abs ve e))
      | e_app e1 e2 =>
          ' v_abs ve1' e1' <- eval n ve e1;
          ' v2 <- eval n ve e2;
          eval n (v2 :: ve1') e1'
      end
  end.

(** * Theorems *)

Hint Constructors Typ Exp Val ExpTyp ValTyp WfEnv Opt List.
Hint Unfold index length ValEnv TypEnv.
Hint Resolve ex_intro.

Lemma wve_length :
  forall ve te,
  WfEnv ve te ->
  length ve = length te.
Proof.
  intros ? ? H. induction H.
  Case "wfe_nil". reflexivity.
  Case "wfe_cons". simpl. rewrite IHWfEnv. reflexivity.
Qed.

Hint Immediate wve_length.

Lemma index_max :
  forall X (xs : List X) (n : nat) (x : X),
  index n xs = some x ->
  n < length xs.
Proof.
  intros ? xs. induction xs.
  Case "nil".
    intros ? ? H. simpl in H. inversion H.
  Case "cons".
    intros ? ? H. simpl. case_eq (n =? length xs); intros E.
    Case2 "hit".
      eapply beq_nat_true in E. rewrite <- E. constructor.
    Case2 "miss".
      simpl in H. rewrite E in H. transitivity (length xs).
      - eapply IHxs. apply H.
      - constructor.
Qed.

Lemma index_extend :
  forall X xs n x' (x : X),
  index n xs = some x ->
  index n (x' :: xs) = some x.
Proof.
  intros ? ? ? ? ? H. simpl. rewrite H.
  assert (n < length xs) as H0. { eapply index_max. exact H. }
  assert (n <> length xs) as H1. { omega. }
  assert ((n =? length xs) = false) as H2. { eapply beq_nat_false_iff. exact H1. }
  rewrite H2. reflexivity.
Qed.

Lemma wve_index :
  forall ve te t n,
  WfEnv ve te ->
  index n te = some t ->
  exists v, index n ve = some v /\ ValTyp v t.
Proof.
  intros ? ? ? ? HWf Hindex. induction HWf.
  Case "wfe_nil".
    simpl in Hindex. inversion Hindex.
  Case "wfe_cons".
    simpl in Hindex. case_eq (n =? length te).
    Case2 "index hits head".
      intros Hhit. rewrite Hhit in Hindex. inversion Hindex; subst t0; clear Hindex.
      assert ((n =? length ve) = true) as Hhit'. { eauto using wve_length. }
      assert (index n (v :: ve) = some v). { simpl. rewrite Hhit'. reflexivity. }
      eauto.
    Case2 "index hits tail".
      intros Hmiss. rewrite Hmiss in Hindex.
      assert ((n =? length ve) = false) as Hmiss'. { eauto using wve_length. }
      specialize (IHHWf Hindex). inversion IHHWf as [v0 [H0 H1]].
      exists v0. constructor. { apply index_extend. exact H0. } { exact H1. }
Qed.

Theorem full_safety :
  forall n e te ve res t,
  eval n ve e = some res ->
  ExpTyp te e t ->
  WfEnv ve te ->
  exists v, res = some v /\ ValTyp v t.
Proof.
  intros n. induction n.
  Case "n = 0". intros until 0. intros Heval. inversion Heval.
  Case "n = S n". intros until 0. intros Heval Htype Hwf. destruct e.
    Case2 "var".
      inversion Heval as [Heval']; clear Heval Heval'.
      inversion Htype; subst te0 x t1; rename H1 into Htype'.
      destruct (wve_index _ _ _ _ Hwf Htype') as [v [I V]].
      rewrite I. eexists. split. reflexivity. exact V.
    Case2 "app".
      inversion Htype; subst t2 e0 e3 te0;
        rename H2 into Htype1; rename H4 into Htype2; rename t into t2.
      simpl in Heval.
      remember (eval n ve e1) as mmv1.
      destruct mmv1 as [mv1|].
      Case3 "mmv1 = some mv1".
        (** Apply [IHn] to [e1] *)
        assert (exists v1, mv1 = some v1 /\ ValTyp v1 (t_arr t1 t2)) as [v1 [E1 HVtype1]].
          { eapply IHn; eauto. }
        subst mv1.
        (** Invert [v1] to closure [v_abs ve0 e] with [ExpTyp] evidence. *)
        inversion HVtype1; subst t0 t3. subst v1.
        remember (eval n ve e2) as mmv2.
        destruct mmv2 as [mv2|].
        Case4 "mmv2 = some mv2".
          (** Apply [IHn] to [e2] *)
          assert (exists v2, mv2 = some v2 /\ ValTyp v2 t1) as [v2 [E2 HVtype2]].
            { eapply IHn; eauto. }
          subst mv2.
          (** Apply [IHn] to closure body [e] *)
          eapply IHn; eauto.
        Case4 "mmv2 = none  [contradiction]".
          inversion Heval.
      Case3 "mmv1 = none  [contradiction]".
        inversion Heval.
    Case2 "abs".
      inversion Htype; subst te0 e0. subst t.
      inversion Heval as [Heval']; clear Heval Heval'.
      eexists. split. eauto. eapply vt_abs; eauto.
Qed.

From Theories Require Import
  Tactics Chap_2_Framework.

(** * Specification *)

(** ** Syntax *)

Inductive Typ :=
  | t_void
  | t_arr (t1 t2 : Typ).

Inductive Exp :=
  | e_var (x : nat)
  | e_app (e1 e2 : Exp)
  | e_abs (e : Exp).

Inductive Val :=
  | v_abs (ve : List Val) (e : Exp).

(** ** Type System *)

Definition TypEnv := List Typ.

Inductive ExpTyp : TypEnv -> Exp -> Typ -> Prop :=
  | et_var :
      forall x te t1,
      indexr x te = some t1 ->
      ExpTyp te (e_var x) t1
  | et_app :
      forall te e1 e2 t1 t2,
      ExpTyp te e1 (t_arr t1 t2) ->
      ExpTyp te e2 t1 ->
      ExpTyp te (e_app e1 e2) t2
  | et_abs :
      forall te e t1 t2,
      ExpTyp (t1 :: te) e t2 ->
      ExpTyp te (e_abs e) (t_arr t1 t2).


(** ** Semantics *)

Definition ValEnv := List Val.

Fixpoint eval (n : nat) (ve : ValEnv) (e : Exp) : CanTimeout (CanErr Val) :=
  match n with
  | 0 => none
  | S n =>
      match e with
      | e_var x => done (indexr x ve)
      | e_abs e => done (noerr (v_abs ve e))
      | e_app e1 e2 =>
          ' v_abs ve1' e1' <- eval n ve e1;
          ' v2 <- eval n ve e2;
          eval n (v2 :: ve1') e1'
      end
  end.

(** ** Type Soundness *)

Inductive ValTyp : Val -> Typ -> Prop :=
  | vt_abs :
      forall ve te e t1 t2,
      Forall2 ValTyp ve te ->
      ExpTyp (t1 :: te) e t2 ->
      ValTyp (v_abs ve e) (t_arr t1 t2)
  .

Definition WfEnv : ValEnv -> TypEnv -> Prop :=
  Forall2 ValTyp.

(** * Theorems *)

Hint Constructors Typ Exp Val ExpTyp ValTyp Opt List.
Hint Unfold indexr length ValEnv TypEnv WfEnv.
Hint Resolve ex_intro.

Theorem type_soundness :
  forall n e te ve res t,
  eval n ve e = done res ->
  ExpTyp te e t ->
  WfEnv ve te ->
  exists v, res = noerr v /\ ValTyp v t.
Proof.
  intros n. induction n.
  Case "n = 0". intros until 0. intros Heval. inversion Heval.
  Case "n = S n". intros until 0. intros Heval Htype Hwf. destruct e.
    Case2 "var".
      inversion Heval as [Heval']; clear Heval Heval'.
      inversion Htype; subst te0 x t1; rename H1 into Htype'.
      destruct (fa2_indexr Hwf Htype') as [v [I V]].
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

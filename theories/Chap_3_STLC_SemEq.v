From Theories Require Import
  Tactics Chap_2_Framework.

(** * Specification *)

(** ** Syntax *)

Inductive Exp :=
  | e_var (x : nat)
  | e_app (e1 e2 : Exp)
  | e_abs (e : Exp).

(** ** Semantics *)

Inductive Val :=
  | v_abs (ve : List Val) (e : Exp).

Definition ValEnv := List Val.

Fixpoint eval (n : nat) (ve : ValEnv) (e : Exp) : CanTimeout (CanErr Val) :=
  match n with
  | 0 => timeout
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

Inductive BigStep : ValEnv -> Exp -> Val -> Prop :=
  | bs_var :
      forall ve x v,
      indexr x ve = some v ->
      BigStep ve (e_var x) v
  | bs_abs :
      forall ve e,
      BigStep ve (e_abs e) (v_abs ve e)
  | bs_app :
      forall ve e1 e2 ve' e' v2 v,
      BigStep ve e1 (v_abs ve' e') ->
      BigStep ve e2 v2 ->
      BigStep (v2 :: ve') e' v ->
      BigStep ve (e_app e1 e2) v
  .

(** * Theorems *)

Hint Constructors Exp Val Opt List.
Hint Unfold indexr length.
Hint Resolve ex_intro.

Lemma eval_inc :
  forall m n ve e v,
  eval n ve e = some (some v) ->
  eval (m + n) ve e = eval n ve e.
Proof.
  intros m n. revert m.
  induction n; intros; try solve by inversion.
  replace (m + S n) with (S (m + n)) by omega.
  destruct e.
  Case "e_var".
    simpl in *. eauto.
  Case "e_app".
    rewrite H.
    simpl in *.
      remember (eval n ve e1) as mmv1 eqn:Heval1; symmetry in Heval1.
      remember (eval n ve e2) as mmv2 eqn:Heval2; symmetry in Heval2.
      destruct mmv1; try solve by inversion.
      destruct o; try solve by inversion.
      destruct v0.
      destruct mmv2; try solve by inversion.
      destruct o; try solve by inversion.
      erewrite IHn; eauto.
      erewrite IHn; eauto.
      rewrite Heval1.
      rewrite Heval2.
      erewrite IHn; eauto.
  Case "e_abs".
    simpl in *. eauto.
Qed.

Theorem sem_eq :
  forall ve e v,
  BigStep ve e v <-> (exists n, eval n ve e = some (some v)).
Proof.
  intros. split.
  Case "->".
    intros bs.
    induction bs.
    Case2 "bs_var".
      exists 1. simpl. rewrite H. reflexivity.
    Case2 "bs_abs".
      exists 1. simpl. reflexivity.
    Case2 "bs_app".
      destruct IHbs1 as [n1 IH1].
      destruct IHbs2 as [n2 IH2].
      destruct IHbs3 as [n3 IH3].
      exists (S (n1 + n2 + n3)).
      simpl.
      replace (eval n1 ve e1) with (eval (n1 + n2 + n3) ve e1) in IH1.
      replace (eval n2 ve e2) with (eval (n1 + n2 + n3) ve e2) in IH2.
      replace (eval n3 (v2 :: ve') e') with (eval (n1 + n2 + n3) (v2 :: ve') e') in IH3.
      rewrite IH1, IH2, IH3.
      reflexivity.
      eapply eval_inc. eauto.
      replace (n1 + n2 + n3) with (n3 + n1 + n2) by omega.
      eapply eval_inc. eauto.
      replace (n1 + n2 + n3) with ((n2 + n3) + n1) by omega.
      eapply eval_inc. eauto.
  Case "<-".
    intros [n Heval].
    revert e v ve Heval.
    induction n; intros e v ve Heval.
    Case2 "0". inversion Heval.
    Case2 "S n".
      (* induction e. *)
      destruct e.
      Case3 "e_var".
        simpl in Heval.
        econstructor. inversion Heval. reflexivity.
      Case3 "e_app".
        simpl in Heval.
        remember (eval n ve e1) as mmv1 eqn:Heval1; symmetry in Heval1.
        remember (eval n ve e2) as mmv2 eqn:Heval2; symmetry in Heval2.
        destruct mmv1; try solve by inversion.
        destruct o; try solve by inversion.
        destruct v0.
        destruct mmv2; try solve by inversion.
        destruct o; try solve by inversion.
        econstructor.
          eapply IHn. exact Heval1.
          eapply IHn. exact Heval2.
          eapply IHn. exact Heval.
      Case3 "e_abs".
        simpl in Heval.
        inversion Heval.
        econstructor.
Qed.

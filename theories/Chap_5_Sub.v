From Theories Require Import
  Tactics Chap_2_Framework.

(** * Specification *)

(** ** Syntax *)

Inductive Typ :=
  | t_top
  | t_arr (t1 t2 : Typ).

Inductive Exp :=
  | e_var (x : nat)
  | e_app (e1 e2 : Exp)
  | e_abs (e : Exp).

(** ** Type System *)

Definition TypEnv := List Typ.

Inductive ExpSubTyp : Typ -> Typ -> Prop :=
  | est_top :
      forall t,
      ExpSubTyp t t_top
  | est_arr :
      forall t11 t12 t21 t22,
      ExpSubTyp t21 t11 ->
      ExpSubTyp t12 t22 ->
      ExpSubTyp (t_arr t11 t12) (t_arr t21 t22).

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
      ExpTyp te (e_abs e) (t_arr t1 t2)
  | et_sub :
      forall te e t1 t2,
      ExpTyp te e t1 ->
      ExpSubTyp t1 t2 ->
      ExpTyp te e t2.

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

(** ** Type Soundness *)

Inductive ValTyp : Val -> Typ -> Prop :=
  | vt_abs :
      forall ve te e t1 t2 t,
      Forall2 ValTyp ve te ->
      ExpTyp (t1 :: te) e t2 ->
      ExpSubTyp (t_arr t1 t2) t ->
      ValTyp (v_abs ve e) t.

Definition WfEnv : ValEnv -> TypEnv -> Prop :=
  Forall2 ValTyp.

(** * Theorems *)

Hint Constructors Typ Exp Val ExpTyp ValTyp Opt List ExpSubTyp.
Hint Unfold indexr length ValEnv TypEnv WfEnv.
Hint Resolve ex_intro.

(* TODO: This is trivial: no ambiguity to resolve *)
Lemma invert_abs :
  forall vf t11 t12,
  ValTyp vf (t_arr t11 t12) ->
  exists ve' te' x y t21 t22,
    vf = v_abs ve' y /\
    length ve' = x /\
    WfEnv ve' te' /\
    ExpTyp (t21 :: te') y t22 /\
    ExpSubTyp t11 t21 /\
    ExpSubTyp t22 t12.
Proof.
  intros. inversion H.
  inversion H2. subst.
  do 6 eexists.
  splits; eauto.
Qed.

Lemma est_refl :
  forall t,
  ExpSubTyp t t.
Proof.
  induction 0; eauto.
Qed.

Inductive ExpSubTypN : Typ -> Typ -> nat -> Prop :=
  | estn_top :
      forall t n,
      ExpSubTypN t t_top (S n)
  | estn_arr :
      forall t11 t12 t21 t22 n1 n2,
      ExpSubTypN t21 t11 n1 ->
      ExpSubTypN t12 t22 n2 ->
      ExpSubTypN (t_arr t11 t12) (t_arr t21 t22) (S (n1 + n2)).

Hint Constructors ExpSubTypN.

Lemma estn_inc_l :
  forall m n t1 t2,
  ExpSubTypN t1 t2 n ->
  ExpSubTypN t1 t2 (m + n).
Proof.
  intros until 0; intros est.
  revert m.
  dependent induction est; intros.
  - replace (m + S n) with (S (m + n)) by omega.
    econstructor.
  - replace (m + S (n1 + n2)) with (S ((m + n1) + n2)) by omega.
    eauto.
Qed.

Lemma estn_trans :
  forall n1 n2 t1 t2 t3,
  ExpSubTypN t1 t2 n1 ->
  ExpSubTypN t2 t3 n2 ->
  ExpSubTypN t1 t3 (n1 + n2).
Proof.
  intros n1 n2.
  remember (S (n1 + n2)) as n eqn:E.
  assert (Hsize : n1 + n2 < n) by omega.
  clear E.
  revert n1 n2 Hsize.
  induction n; intros n1 n2 Hsize; intros until 0; intros est1 est2.
  Case "n1 + n2 < 0".
    omega.
  Case "n1 + n2 < S n".
    inversion est1; subst; inversion est2; subst.
    Case2 "t1 <: top <: top".
      econstructor.
    Case2 "t_arr t11 t12 <: t_arr t21 t22 <: top".
      econstructor.
    Case2 "t_arr t11 t12 <: t_arr t21 t22 <: t_arr t31 t32";
      rename t2 into t31; rename t4 into t32;
      rename H  into est11; rename H0 into est12;
      rename H3 into est21; rename H6 into est22;
      rename n0 into n11; rename n3 into n12;
      rename n1 into n21; rename n4 into n22.
      (* replace (S (n11 + n12) + S (n21 + n22)) with *)
      (*         (S (S ((n21 + n11) + (n12 + n22)))) by omega. *)
      (* eapply (estn_inc_l 1). *)
      (* eapply estn_arr; eapply IHn; solve [eassumption | omega]. *)
      assert (est1' : ExpSubTypN t31 t11 (n21 + n11)). { eapply IHn; eauto; omega. }
      assert (est2' : ExpSubTypN t12 t32 (n12 + n22)). { eapply IHn; eauto; omega. }
      replace (S (n11 + n12) + S (n21 + n22)) with
              (S (S ((n21 + n11) + (n12 + n22)))) by omega.
      eapply (estn_inc_l 1).
      econstructor; eassumption.
Qed.

Lemma est_iff_estn :
  forall t1 t2,
  ExpSubTyp t1 t2 <-> (exists n, ExpSubTypN t1 t2 n).
Proof.
  intros t1 t2. split.
  Case "->". intros est. induction est; splith; unshelve eauto; exact 0.
  Case "<-". intros [n estn]. induction estn; unshelve eauto.
Qed.

Lemma est_trans :
  forall t1 t2 t3,
  ExpSubTyp t1 t2 ->
  ExpSubTyp t2 t3 ->
  ExpSubTyp t1 t3.
Proof.
  intros until 0; intros est1 est2.
  eapply est_iff_estn in est1.
  eapply est_iff_estn in est2.
  eapply est_iff_estn.
  splith.
  eexists.
  eapply estn_trans; eassumption.
Qed.

Lemma vt_widen :
  forall v t1 t2,
  ValTyp v t1 ->
  ExpSubTyp t1 t2 ->
  ValTyp v t2.
Proof.
  intros until 0; intros vt est.
  inversion vt; subst.
  econstructor; eauto.
  eapply est_trans; eauto.
Qed.

Theorem type_soundness :
  forall n e te ve res t,
  eval n ve e = some res ->
  ExpTyp te e t ->
  WfEnv ve te ->
  exists v, res = some v /\ ValTyp v t.
Proof.
  intros n. induction n.
  Case "n = 0". intros until 0. intros Heval. inversion Heval.
  Case "n = S n". intros until 0. intros Heval Htype Hwf.
    dependent induction Htype.
    Case2 "var".
      inversion Heval as [Heval']; clear Heval Heval'.
      rename H into Htype'.
      destruct (fa2_indexr Hwf Htype') as [v [I V]].
      rewrite I. eexists. split. reflexivity. exact V.
    Case2 "app".
      clear IHHtype1 IHHtype2.
      simpl in Heval.
      remember (eval n ve e1) as mmv1.
      destruct mmv1 as [mv1|].
      Case3 "mmv1 = some mv1".
        (** Apply [IHn] to [e1] *)
        assert (exists v1, mv1 = some v1 /\ ValTyp v1 (t_arr t1 t2)) as [v1 [E1 HVtype1]].
          { eapply IHn; eauto. }
        subst mv1.
        (** Invert [v1] to closure [v_abs ve0 e] with [ExpTyp] evidence. *)
        (* inversion HVtype1. subst t. subst v1. *)
        destruct (invert_abs _ _ _ HVtype1) as
          (ve1 & te1 & x1' & e1' & t1' & t2' & Ex1' & Ev1 & Hwf1 & Hty1' & Hvst1 & Hvst2).
        subst v1 x1'.

        remember (eval n ve e2) as mmv2.
        destruct mmv2 as [mv2|].
        Case4 "mmv2 = some mv2".
          (** Apply [IHn] to [e2] *)
          assert (exists v2, mv2 = some v2 /\ ValTyp v2 t1) as [v2 [E2 HVtype2]].
            { eapply IHn; eauto. }
          subst mv2.

          assert (Hwf1' : WfEnv (v2 :: ve1) (t1' :: te1)). {
            econstructor.
            - eapply vt_widen; info_eauto.
            - eassumption.
          }

          (** Apply [IHn] to closure body [e] *)
          eapply IHn; eauto.
        Case4 "mmv2 = none  [contradiction]".
          inversion Heval.
      Case3 "mmv1 = none  [contradiction]".
        inversion Heval.
    Case2 "abs".
      inversion Heval as [Heval']; clear Heval Heval'.
      eexists. split. eauto. eapply vt_abs; eauto.
      eapply est_refl.
    Case2 "et_sub".
      assert (exists v : Val, res = some v /\ ValTyp v t1).
        eapply IHHtype; simpl; eauto.
      splith. esplits; eauto.
      eapply vt_widen; eauto.
Qed.

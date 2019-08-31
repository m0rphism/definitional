From Theories Require Import
  Tactics Chap_2_Framework.

(** * Specification *)

(** ** Syntax *)

Inductive Mul :=
  | aff
  | unr.

Inductive Typ :=
  | t_void
  | t_arr (m : Mul) (t1 t2 : Typ).

Inductive Exp :=
  | e_var (x : nat)
  | e_app (e1 e2 : Exp)
  | e_abs (m : Mul) (e : Exp).

(** ** Type System *)

Inductive Acc :=
  | here
  | gone.

Inductive Bind :=
  | bind (a : Acc) (m : Mul) (t : Typ).

Definition TypEnv := List Bind.

Inductive Split : TypEnv -> TypEnv -> TypEnv -> Prop :=
  | sp_nil :
      Split [] [] []
  | sp_gone :
      forall bs bs1 bs2 t m,
      Split bs bs1 bs2 ->
      Split (bind gone m t :: bs) (bind gone m t :: bs1) (bind gone m t :: bs2)
  | sp_left :
      forall bs bs1 bs2 t,
      Split bs bs1 bs2 ->
      Split (bind here aff t :: bs) (bind here aff t :: bs1) (bind gone aff t :: bs2)
  | sp_right :
      forall bs bs1 bs2 t,
      Split bs bs1 bs2 ->
      Split (bind here aff t :: bs) (bind gone aff t :: bs1) (bind here aff t :: bs2)
  | sp_both :
      forall bs bs1 bs2 t,
      Split bs bs1 bs2 ->
      Split (bind here unr t :: bs) (bind here unr t :: bs1) (bind here unr t :: bs2).

Definition restrict_entry (b : Bind) : Bind :=
  match b with
  | bind here aff t => bind gone aff t
  | b               => b
  end.

Definition restrict (m : Mul) (bs : TypEnv) : TypEnv :=
  match m with
  | unr => map restrict_entry bs
  | aff => bs
  end.

(* FIXME: Sub-kinding is not used yet. *)
Inductive SubKind : Mul -> Mul -> Prop :=
  | sk_refl : forall m, SubKind m m
  | sk_aff  :      SubKind unr aff.

Inductive HasKind : Typ -> Mul -> Prop :=
  | hk_void :            HasKind t_void unr
  | hk_arr  : forall m t1 t2, HasKind (t_arr m t1 t2) m.

Inductive ExpTyp : TypEnv -> Exp -> Typ -> Prop :=
  | et_var :
      forall x te t m,
      indexr x te = some (bind here m t) ->
      ExpTyp te (e_var x) t
  | et_app :
      forall te te1 te2 e1 e2 t1 t2 m,
      Split te te1 te2 ->
      ExpTyp te1 e1 (t_arr m t1 t2) ->
      ExpTyp te2 e2 t1 ->
      ExpTyp te (e_app e1 e2) t2
  | et_abs :
      forall te e t1 t2 m m1,
      HasKind t1 m1 ->
      ExpTyp (bind here m1 t1 :: restrict m te) e t2 ->
      ExpTyp te (e_abs m e) (t_arr m t1 t2).

(** ** Semantics *)

Inductive Val :=
  | v_abs (ve : List Val) (m : Mul) (e : Exp).

Definition ValEnv := List Val.

Fixpoint eval (n : nat) (ve : ValEnv) (e : Exp) : CanTimeout (CanErr Val) :=
  match n with
  | 0 => timeout
  | S n =>
      match e with
      | e_var x => done (indexr x ve)
      | e_abs m e => done (noerr (v_abs ve m e))
      | e_app e1 e2 =>
          ' v_abs env1' m' e1' <- eval n ve e1;
          ' v2 <- eval n ve e2;
          eval n (v2 :: env1') e1'
      end
  end.

(** ** Type Soundness *)

Definition bind_typ (b : Bind) : Typ :=
  match b with
  | bind a m t => t
  end.

Inductive ValTyp : Val -> Typ -> Prop :=
  | vt_abs :
      forall ve te e t1 t2 m m1,
      Forall2 (fun v b => ValTyp v (bind_typ b)) ve te ->
      HasKind t1 m1 ->
      ExpTyp (bind here m1 t1 :: te) e t2 ->
      ValTyp (v_abs ve m e) (t_arr m t1 t2).

Definition WfEnv : ValEnv -> TypEnv -> Prop :=
  Forall2 (fun v b => ValTyp v (bind_typ b)).

(* Inductive ValTyp : Val -> Bind -> Prop := *)
(*   | vt_abs : *)
(*       forall a ve te e t1 t2 m m1, *)
(*       Forall2 ValTyp ve te -> *)
(*       HasKind t1 m1 -> *)
(*       ExpTyp (bind here m1 t1 :: te) e t2 -> *)
(*       ValTyp (v_abs ve m e) (bind a m (t_arr m t1 t2)). *)

(* Definition WfEnv : ValEnv -> TypEnv -> Prop := *)
(*   Forall2 ValTyp. *)

(* Inductive WfEnv : ValEnv -> TypEnv -> Prop := *)
(*   | wfe_nil : *)
(*       WfEnv [] [] *)
(*   | wfe_cons : *)
(*       forall v t ve te m, *)
(*       HasKind t m -> *)
(*       ValTyp v t -> *)
(*       WfEnv ve te -> *)
(*       WfEnv (v :: ve) (bind here m t :: te) *)
(*   | wfe_none : *)
(*       forall v t ve te m, *)
(*       HasKind t m -> *)
(*       ValTyp v t -> *)
(*       WfEnv ve te -> *)
(*       WfEnv (v :: ve) (bind gone m t :: te) *)
(* with ValTyp : Val -> Typ -> Prop := *)
(*   | vt_abs : *)
(*       forall ve te e t1 t2 m m1, *)
(*       WfEnv ve te -> *)
(*       HasKind t1 m1 -> *)
(*       ExpTyp (bind here m1 t1 :: te) e t2 -> *)
(*       ValTyp (v_abs ve m e) (t_arr m t1 t2). *)

(** * Theorems *)

Hint Constructors Typ Exp Val Split ExpTyp ValTyp Opt List Forall2.
Hint Unfold indexr length ValEnv TypEnv map restrict_entry restrict WfEnv.
Hint Resolve ex_intro.

Lemma split_preserves_wf :
  forall ve te te1 te2,
  WfEnv ve te ->
  Split te te1 te2 ->
  WfEnv ve te1 /\ WfEnv ve te2.
Proof.
  intros ? ? ? ? ? HSplit.
  generalize dependent ve.
  induction HSplit; intros ve HWf.
  Case "sp_nil".
    auto.
  Case "sp_gone". {
    inversion HWf; subst.
    destruct (IHHSplit xs H3) as [HWf1 HWf2].
    split; eauto.
    (* split. *)
    (* - econstructor. eauto. auto. exact HWf1. *)
    (* - econstructor. eauto. auto. exact HWf2. *)
  }
  Case "sp_left".
    inversion HWf; subst.
    destruct (IHHSplit xs H3) as [HWf1 HWf2].
    split; eauto.
  Case "sp_right".
    inversion HWf; subst.
    destruct (IHHSplit xs H3) as [HWf1 HWf2].
    split; eauto.
  Case "sp_both".
    inversion HWf; subst.
    destruct (IHHSplit xs H3) as [HWf1 HWf2].
    split; eauto.
Qed.

Lemma split_append_comm :
  forall (i1 i2 l r : TypEnv),
  Split (i1 ++ i2) l r ->
  exists l1 r1 l2 r2,
    Split i1 l1 r1 /\
    Split i2 l2 r2 /\
    l1 ++ l2 = l /\
    r1 ++ r2 = r.
Proof.
  intros i1.
  induction i1; intros.
  - simpl in H. exists []. exists []. exists l. exists r. intuition.
  - simpl in H.
    inversion H; subst.
    (* Exact same proofs except for constructor [eapply sp_*]. *)
    + destruct (IHi1 _ _ _ H4) as
        [l1' [r1' [l2' [r2' [HSplit1 [HSplit2 [HEq1 HEq2]]]]]]].
      eexists. eexists. eexists. eexists.
      repeat split.
      * eapply sp_gone. eapply HSplit1.
      * eapply HSplit2.
      * rewrite <- HEq1. rewrite <- app_comm_cons. reflexivity.
      * rewrite <- HEq2. rewrite <- app_comm_cons. reflexivity.
    + destruct (IHi1 _ _ _ H4) as
        [l1' [r1' [l2' [r2' [HSplit1 [HSplit2 [HEq1 HEq2]]]]]]].
      eexists. eexists. eexists. eexists.
      repeat split.
      * eapply sp_left. eapply HSplit1.
      * eapply HSplit2.
      * rewrite <- HEq1. rewrite <- app_comm_cons. reflexivity.
      * rewrite <- HEq2. rewrite <- app_comm_cons. reflexivity.
    + destruct (IHi1 _ _ _ H4) as
        [l1' [r1' [l2' [r2' [HSplit1 [HSplit2 [HEq1 HEq2]]]]]]].
      eexists. eexists. eexists. eexists.
      repeat split.
      * eapply sp_right. eapply HSplit1.
      * eapply HSplit2.
      * rewrite <- HEq1. rewrite <- app_comm_cons. reflexivity.
      * rewrite <- HEq2. rewrite <- app_comm_cons. reflexivity.
    + destruct (IHi1 _ _ _ H4) as
        [l1' [r1' [l2' [r2' [HSplit1 [HSplit2 [HEq1 HEq2]]]]]]].
      eexists. eexists. eexists. eexists.
      repeat split.
      * eapply sp_both. eapply HSplit1.
      * eapply HSplit2.
      * rewrite <- HEq1. rewrite <- app_comm_cons. reflexivity.
      * rewrite <- HEq2. rewrite <- app_comm_cons. reflexivity.
Qed.

Lemma split_append_comm_back :
  forall (i1 l1 r1 i2 l2 r2 : TypEnv),
  Split i1 l1 r1 ->
  Split i2 l2 r2 ->
  Split (i1 ++ i2) (l1 ++ l2) (r1 ++ r2).
Proof.
  induction i1; intros l1 r1 i2 l2 r2 HSplit1 HSplit2.
  - inversion HSplit1; subst. simpl. exact HSplit2.
  - inversion HSplit1; subst; rename bs1 into l1; rename bs2 into r1.
    + simpl. apply sp_gone. eapply IHi1; assumption.
    + simpl. apply sp_left. eapply IHi1; assumption.
    + simpl. apply sp_right. eapply IHi1; assumption.
    + simpl. apply sp_both. eapply IHi1; assumption.
Qed.

Lemma split_restr' :
  forall (i l r : TypEnv),
  Split (map restrict_entry i) l r ->
  exists l' r',
    Split i l' r' /\
    map restrict_entry l' = l /\
    map restrict_entry r' = r.
Proof.
  induction i; intros.
  Case "i = []".
    simpl in H. inversion H; subst.
    exists []. exists []. intuition.
  Case "i = a :: i".
    destruct a.
    destruct a.
    Case2 "a = here".
      destruct m.
      Case3 "m = aff". (* We arbitrarily choose [sp_left]. *)
        simpl in *. inversion H; subst.
        destruct (IHi _ _ H5) as [l' [r' [HSplit' [HEq1' HEq2']]]].
        subst. exists (bind here aff t :: l'). exists (bind gone aff t :: r').
        repeat split. eapply sp_left. exact HSplit'.
      Case3 "m = unr".
        simpl in *. inversion H; subst.
        destruct (IHi _ _ H4) as [l' [r' [HSplit' [HEq1' HEq2']]]].
        subst. exists (bind here unr t :: l'). exists (bind here unr t :: r').
        repeat split. eapply sp_both. exact HSplit'.
    Case2 "a = gone".
      simpl in *. inversion H; subst.
      destruct (IHi _ _ H5) as [l' [r' [HSplit' [HEq1' HEq2']]]].
      subst. exists (bind gone m t :: l'). exists (bind gone m t :: r').
      repeat split. eapply sp_gone. exact HSplit'.
Qed.

Lemma split_restr :
  forall (i1 i2 l r : TypEnv),
  Split (i1 ++ map restrict_entry i2) l r ->
  exists l1 r1 l2 r2,
    Split (i1 ++ i2) (l1 ++ l2) (r1 ++ r2) /\
    l1 ++ map restrict_entry l2 = l /\
    r1 ++ map restrict_entry r2 = r.
Proof.
  intros i1 i2 l r HSplit.
  destruct (split_append_comm _ _ _ _ HSplit) as
    [l1 [r1 [l2 [r2 [HSplit1 [HSplit2 [Eq_l Eq_r]]]]]]].
  destruct (split_restr' i2 l2 r2 HSplit2) as
    [l2' [r2' [HSplit2' [Eq_l2' Eq_r2']]]].
  subst.
  pose (HSplit' := split_append_comm_back _ _ _ _ _ _ HSplit1 HSplit2');
  clearbody HSplit'.
  repeat eexists. intuition.
Qed.

Lemma restr_append_comm :
  forall (xs1 xs2 : TypEnv) m,
  restrict m (xs1 ++ xs2) = restrict m xs1 ++ restrict m xs2.
Proof.
  intros. destruct m.
  - simpl. reflexivity.
  - simpl. rewrite <- map_append_comm. reflexivity.
Qed.

Lemma restrict_entry_idempotent :
  forall (b : Bind),
  restrict_entry (restrict_entry b) = restrict_entry b.
Proof. destruct b. destruct a; destruct m; reflexivity. Qed.

Lemma map_idempotent :
  forall {X} (f : X -> X),
  (forall x, f (f x) = f x) ->
  (forall xs, map f (map f xs) = map f xs).
Proof.
  intros. induction xs.
  - simpl. reflexivity.
  - simpl. rewrite H. rewrite IHxs. reflexivity.
Qed.

Lemma restr_unr_idempotent :
  forall (bs : TypEnv) m,
  restrict m (restrict unr bs) = restrict unr bs.
Proof.
  intros. destruct m.
  - simpl in *. reflexivity.
  - simpl in *. apply map_idempotent. exact restrict_entry_idempotent.
Qed.

Lemma length_app_comm :
  forall {X} (xs1 xs2 : List X),
  length (xs1 ++ xs2) = length xs1 + length xs2.
Proof.
  intros.
  induction xs1.
  - simpl in *. reflexivity.
  - simpl in *. rewrite <- IHxs1. reflexivity.
Qed.

Lemma restr_preserves_indexr :
  forall (te te' : TypEnv) (i : nat) m t ,
  indexr i (te' ++ restrict unr te) = some (bind here m t) ->
  indexr i (te' ++ te) = some (bind here m t).
Proof.
  induction te'; intros.
  - simpl in *.
    induction te.
    + simpl in *. assumption.
    + simpl in *.
      rewrite map_preserves_length in H.
      destruct (i =? length te).
      * destruct a. destruct a.
          destruct m0.
            simpl in *. inversion H.
            simpl in *. inversion H; subst. reflexivity.
          simpl in *. inversion H.
      * apply IHte. assumption.
  - simpl in *.
    rewrite length_app_comm in H.
    rewrite map_preserves_length in H.
    rewrite <- length_app_comm in H.
    destruct (i =? length (te' ++ te)).
    + exact H.
    + apply IHte'; assumption.
Qed.

(** For the safety proof, we only need the special case where [te' ~= [here m1 t1]],
    but we generalize to get a strong enough induction hypothesis. *)
Lemma restr_preserves_hastype :
  forall m e t te te',
  ExpTyp (te' ++ restrict m te) e t ->
  ExpTyp (te' ++ te) e t.
Proof.
  intros m.
  destruct m.
  Case "m = unr". intros ? ? ? ? HExpTyp. simpl in HExpTyp. exact HExpTyp.
  Case "m = aff".
    dependent induction e; intros t te te' HExpTyp.
    - inversion HExpTyp as [? ? ? m Hindex | |]; subst.
      apply et_var with (m := m).
      apply restr_preserves_indexr.
      exact Hindex.
    - inversion HExpTyp as
        [| te'' te1 te2 f x t0 t2 m HSplit HExpTyp1 HExpTyp2|]; subst.
      destruct (split_restr te' te te1 te2 HSplit) as
        [te1' [te2' [te1'' [te2'' [HSplit'' [EQ1 EQ2]]]]]].
      subst.
      eapply et_app with (m := m) (t1 := t0).
      + exact HSplit''.
      + exact (IHe1 (t_arr m t0 t) _ _ HExpTyp1).
      + exact (IHe2 t0 _ _ HExpTyp2).
    - inversion HExpTyp as
        [| | te'' e' t1 t2 m0 m1 HHasKind' HExpTyp']; subst.
      apply et_abs with (m1 := m1).
      + exact HHasKind'.
      + rewrite restr_append_comm in HExpTyp'.
        destruct m.
        * simpl in *.
          exact (IHe t2 te (bind here m1 t1 :: te') HExpTyp').
        * rewrite restr_unr_idempotent in HExpTyp'.
          rewrite <- restr_append_comm in HExpTyp'.
          exact HExpTyp'.
Qed.

Theorem type_soundness :
  forall n e te ve res t,
  eval n ve e = some res ->
  ExpTyp te e t ->
  WfEnv ve te ->
  exists v, res = some v /\ ValTyp v t.
Proof.
  intros n. induction n.
  Case "n = 0". intros ? ? ? ? ? Heval ? ?. inversion Heval.
  Case "n = S n". intros ? ? ? ? ? H H0 H1. destruct e.
    Case2 "var".
      inversion H as [H'].
      inversion H0.
      destruct (fa2_indexr H1 H4) as [v [I V]].
      rewrite I. eexists. eexists. split. exact V.
    Case2 "app".
      simpl in H.
      inversion H0. subst e0 e3 te0 t.
      destruct (split_preserves_wf _ _ _ _ H1 H4) as [HWf1 HWf2].
      remember (eval n ve e1) as mmv1.
      remember (eval n ve e2) as mmv2.
      destruct mmv1 as [mv1|].
      Case3 "mmv1 = some mv1".
        destruct mmv2 as [mv2|].
        Case4 "mmv2 = some mv2".
          (** Apply [IHn] to [e1] *)
          assert (exists v1, mv1 = some v1 /\ ValTyp v1 (t_arr m t1 t2)) as [v1 [E1 HV1]].
            { eapply IHn; eauto. }
          (** Apply [IHn] to [e2] *)
          assert (exists v2, mv2 = some v2 /\ ValTyp v2 t1) as [v2 [E2 HV2]].
            { eapply IHn; eauto. }
          (** Invert [v1] to closure [v_abs ve0 e] with [ExpTyp] evidence. *)
          inversion HV1.
          (** Apply [IHn] to closure body [e] *)
          subst. eapply IHn; eauto.
        Case4 "mmv2 = none  [contradiction]".
          (** Apply [IHn] to [e1] *)
          assert (exists v1, mv1 = some v1 /\ ValTyp v1 (t_arr m t1 t2)) as [v1 [E1 HV1]].
            { eapply IHn; eauto. }
          subst. inversion HV1. subst.
          (** Contradict. *)
          inversion H.
      Case3 "mmv1 = none  [contradiction]".
        solve by inversion.
    Case2 "abs".
      inversion H. inversion H0.
      eexists. split. eauto. eapply vt_abs; eauto.
      eapply restr_preserves_hastype with (te' := [bind here m1 t1]) (m := m).
      exact H8.
Qed.

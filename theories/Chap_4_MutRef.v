From Theories Require Import
  Tactics Chap_2_Framework.

(** * Specification *)

(** ** Syntax *)

Definition Id  := nat.
Definition Loc := nat.

Inductive Typ :=
  | t_arr (t1 t2 : Typ)
  | t_unit
  | t_ref (t : Typ).

Inductive Exp :=
  | e_var (x : nat)
  | e_app (e1 e2 : Exp)
  | e_abs (e : Exp)
  | e_unit
  | e_ref (e : Exp)
  | e_get (e : Exp)
  | e_set (e1 e2 : Exp).

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
      ExpTyp te (e_abs e) (t_arr t1 t2)
  | et_unit :
      forall te,
      ExpTyp te e_unit t_unit
  | et_ref :
      forall te e t,
      ExpTyp te e t ->
      ExpTyp te (e_ref e) (t_ref t)
  | et_get :
      forall te e t,
      ExpTyp te e (t_ref t) ->
      ExpTyp te (e_get e) t
  | et_set :
      forall te e1 e2 t,
      ExpTyp te e1 (t_ref t) ->
      ExpTyp te e2 t ->
      ExpTyp te (e_set e1 e2) t_unit
  .

(** ** Semantics *)

Inductive Val :=
  | v_abs (ve : List Val) (e : Exp)
  | v_unit
  | v_loc (l : Loc).

Definition ValEnv := List Val.
Definition ValStore := List Val.

Fixpoint eval (n : nat) (ve : ValEnv) (vs : ValStore) (e : Exp) :
  CanTimeout (CanErr (Val * ValStore))
:=
  match n with
  | 0 =>
      timeout
  | S n =>
      match e with
      | e_var x =>
          done (omap (fun v => (v, vs)) (indexr x ve))
      | e_abs e =>
          done (noerr (v_abs ve e, vs))
      | e_app e1 e2 =>
          '(v_abs ve1' e1', vs) <- eval n ve vs e1;
          '(v2, vs) <- eval n ve vs e2;
          eval n (v2 :: ve1') vs e1'
      | e_unit =>
          done (noerr (v_unit, vs))
      | e_ref e =>
          '(v, vs) <- eval n ve vs e;
          done (noerr (v_loc (length vs), v :: vs))
      | e_get e =>
          '(v_loc l, vs) <- eval n ve vs e;
          done (omap (fun v => (v, vs)) (indexr l vs))
      | e_set e1 e2 =>
          '(v_loc l, vs) <- eval n ve vs e1;
          '(v2, vs) <- eval n ve vs e2;
          done (noerr (v_unit, update l v2 vs))
      end
  end.

(** ** Type Soundness *)

Definition TypStore := List Typ.

Inductive ValTyp : TypStore -> Val -> Typ -> Prop :=
  | vt_abs :
      forall ts ve te e t1 t2,
      Forall2 (ValTyp ts) ve te ->
      ExpTyp (t1 :: te) e t2 ->
      ValTyp ts (v_abs ve e) (t_arr t1 t2)
  | vt_unit :
      forall ts,
      ValTyp ts v_unit t_unit
  | vt_loc :
      forall ts l t,
      indexr l ts = some t ->
      ValTyp ts (v_loc l) (t_ref t)
  .

Definition WfEnv (ve : ValEnv) (te : TypEnv) (ts : TypStore) : Prop :=
  Forall2 (ValTyp ts) ve te.

Definition WfStore (vs : ValStore) (ts : TypStore) : Prop :=
  Forall2 (ValTyp ts) vs ts.

Notation SubStore := IsSuffixOf.

(** * Theorems *)

Hint Constructors Typ Exp Val ExpTyp ValTyp Opt List.
Hint Unfold indexr length ValEnv TypEnv ValStore TypStore SubStore omap update WfEnv.
Hint Resolve ex_intro.

(* Scheme wfenv_valtype_ind := Induction for WfEnv   Sort Prop *)
(* with   valtype_wfenv_ind := Induction for ValTyp Sort Prop. *)
(* Combined Scheme wfenv_valtype_mutind from wfenv_valtype_ind, valtype_wfenv_ind. *)
(* Combined Scheme valtype_wfenv_mutind from valtype_wfenv_ind, wfenv_valtype_ind. *)

Lemma valtype_wfenv_substore :
  (forall (ve : ValEnv) (te : TypEnv) (ts1 : TypStore),
   WfEnv ve te ts1 ->
   forall (ts2 : TypStore),
   SubStore ts1 ts2 ->
   WfEnv ve te ts2) /\
  (forall (ts1 : TypStore) (v : Val) (t : Typ),
   ValTyp ts1 v t ->
   forall (ts2 : TypStore),
   SubStore ts1 ts2 ->
   ValTyp ts2 v t).
Proof.
Admitted.
(*   eapply wfenv_valtype_mutind. *)
(*   - intros. econstructor. *)
(*   - intros. econstructor. eapply H. *)
(*     + exact H1. *)
(*     + eapply H0. exact H1. *)
(*   - intros. econstructor. *)
(*     + eapply H. exact H0. *)
(*     + assumption. *)
(*   - intros. econstructor. *)
(*   - intros. econstructor. eapply indexr_suffix. *)
(*     + exact e. *)
(*     + exact H. *)
(* Qed. *)

Lemma valtype_substore :
  forall (v : Val) (t : Typ) (ts1 ts2 : TypStore),
  ValTyp ts1 v t ->
  SubStore ts1 ts2 ->
  ValTyp ts2 v t.
Proof.
  intros; eapply valtype_wfenv_substore; eauto.
Qed.

Lemma wfenv_substore:
  forall (te : TypEnv) (ve : ValEnv) (ts1 ts2 : TypStore),
  WfEnv ve te ts1 ->
  SubStore ts1 ts2 ->
  WfEnv ve te ts2.
Proof.
  intros; eapply valtype_wfenv_substore; eauto.
Qed.

Lemma wfstore_extend_inner:
  forall (ts ts' : TypStore) (vs : ValStore) (t : Typ),
    Forall2 (ValTyp ts') vs ts ->
    Forall2 (ValTyp (t :: ts')) vs ts.
Proof.
  intros until 0; intros Hwfs.
  eapply (fa2_map _ _ Hwfs).
  intros x y vt. eapply valtype_substore.
  * exact vt.
  * exists [t]. reflexivity.
Qed.

Lemma wfstore_extend:
  forall (v : Val) (vs : ValStore) (t : Typ) (ts : TypStore),
  WfStore vs ts ->
  ValTyp ts v t ->
  WfStore (v :: vs) (t :: ts).
Proof.
  intros until 0; intros Hwfs Hvt.
  econstructor.
  - eapply valtype_substore.
    + exact Hvt.
    + exists [t]. reflexivity.
  - eapply wfstore_extend_inner. exact Hwfs.
Qed.

Tactic Notation "destruct_eval" constr(e) "as" "[" ident(mv) ident(Heval) "]" :=
  remember (eval _ _ _ e) as mmv eqn:Heval; symmetry in Heval;
  destruct mmv as [mv|]; [|solve by inversion].

Theorem type_soundness :
  forall n e te ve vs ts res t,
  eval n ve vs e = done res ->
  ExpTyp te e t ->
  WfStore vs ts ->
  WfEnv ve te ts ->
  exists v vs' ts',
    res = some (v, vs') /\
    WfStore vs' ts' /\
    SubStore ts ts' /\
    ValTyp ts' v t.
Proof.
  intros n. induction n.

  Case "n = 0". intros until 0. intros Heval. inversion Heval.

  Case "n = S n". intros until 0. intros Heval Htype Hwfs Hwfe. destruct e.

    Case2 "var".
      simpl in Heval.
      inversion Heval as [Heval']; clear Heval Heval'.
      inversion Htype; subst te0 x t1; rename H1 into Htype'.
      destruct (fa2_indexr Hwfe Htype') as [v [I V]].
      rewrite I. simpl. exists v. exists vs. exists ts. intuition. apply suffix_refl.

    Case2 "app".
      inversion Htype; subst t2 e0 e3 te0;
        rename H2 into Htype1; rename H4 into Htype2; rename t into t2.

      simpl in Heval.

      destruct_eval e1 as [mv1 Heval1].
      destruct (IHn _ _ _ _ _ _ _ Heval1 Htype1 Hwfs Hwfe)
        as [v1 [vs1 [ts1 [E1 [Hwfs1 [Hss1 HV1]]]]]].
      subst mv1.

      (* Find out that [v1 = v_abs ve0 e]. *)
      inversion HV1; rename H3 into Hwfe3; rename H4 into Htype3; subst.

      assert (Hwfe1 : WfEnv ve te ts1). {
        eauto using wfenv_substore.
      }

      destruct_eval e2 as [mv2 Heval2].
      destruct (IHn _ _ _ _ _ _ _ Heval2 Htype2 Hwfs1 Hwfe1)
        as [v2 [vs2 [ts2 [E2 [Hwfs2 [Hss2 HV2]]]]]].
      subst mv2.

      assert (Hwfe3' : WfEnv (v2 :: ve0) (t1 :: te0) ts2). {
        econstructor. assumption.
        eapply wfenv_substore. eassumption. assumption.
      }

      destruct (IHn _ _ _ _ _ _ _ Heval Htype3 Hwfs2 Hwfe3')
        as [v3 [vs3 [ts3 [E3 [Hwfs3 [Hss3 HV3]]]]]].

      (* whats missing for the last IHn to match the goal is [SubStore ts ts3]. *)
      assert (Hss : SubStore ts ts3). {
        eauto using suffix_trans.
        (* exact (substore_trans _ _ _ Hss1 (substore_trans _ _ _ Hss2 Hss3)). *)
      }

      subst res.
      exists v3. exists vs3. exists ts3. intuition.

    Case2 "abs".
      inversion Htype; subst te0 e0. subst t.
      inversion Heval as [Heval']; clear Heval Heval'.
      exists (v_abs ve e). exists vs. exists ts.
      intuition. apply suffix_refl. eapply vt_abs; eauto.

    Case2 "unit".
      inversion Htype; subst te0. subst t.
      inversion Heval as [Heval']; clear Heval Heval'.
      do 3 eexists. intuition eauto. apply suffix_refl.

    Case2 "ref".
      inversion Htype; subst te0 e0. subst t. rename H1 into Htype1.
      simpl in Heval.

      destruct_eval e as [mv1 Heval1].
      destruct (IHn _ _ _ _ _ _ _ Heval1 Htype1 Hwfs Hwfe)
        as [v1 [vs1 [ts1 [E1 [Hwfs1 [Hss1 HV1]]]]]].
      subst mv1.

      inversion Heval; clear Heval; subst res.
      exists (v_loc (length vs1)). exists (v1 :: vs1). exists (t0 :: ts1).
      { intuition.
        - eauto using wfstore_extend.
        - eapply suffix_trans.
          + apply Hss1.
          + exists [t0]. reflexivity.
        - econstructor.
          rewrite (fa2_length Hwfs1).
          simpl.
          rewrite Nat.eqb_refl.
          reflexivity.
      }

    Case2 "get".
      inversion Htype; subst te0 e0. subst t. rename H1 into Htype1.
      simpl in Heval.

      destruct_eval e as [mv1 Heval1].
      destruct (IHn _ _ _ _ _ _ _ Heval1 Htype1 Hwfs Hwfe)
        as [v1 [vs1 [ts1 [E1 [Hwfs1 [Hss1 HV1]]]]]].
      subst mv1.

      inversion HV1; subst.
      destruct (fa2_indexr Hwfs1 H2) as [v [Hindex' HV']].
      rewrite Hindex' in Heval; simpl in Heval.
      inversion Heval; subst res.
      exists v, vs1, ts1. eauto.

    Case2 "set".
      inversion Htype; subst te0 e0 e3; rename H2 into Htype1; rename H4 into Htype2.
      subst t.

      simpl in Heval.

      destruct_eval e1 as [mv1 Heval1].
      destruct (IHn _ _ _ _ _ _ _ Heval1 Htype1 Hwfs Hwfe)
        as [v1 [vs1 [ts1 [E1 [Hwfs1 [Hss1 HV1]]]]]].
      subst mv1.

      inversion HV1; subst ts0 t. subst v1.

      assert (Hwfe1 : WfEnv ve te ts1). {
        eauto using wfenv_substore.
      }

      destruct_eval e2 as [mv2 Heval2].
      destruct (IHn _ _ _ _ _ _ _ Heval2 Htype2 Hwfs1 Hwfe1)
        as [v2 [vs2 [ts2 [E2 [Hwfs2 [Hss2 HV2]]]]]].
      subst mv2.

      inversion Heval; subst res.
      exists v_unit, (update l v2 vs2), ts2.
      { splits.
        - eauto.
        - eapply fa2_update_l; eauto using indexr_suffix.
        - eauto using suffix_trans.
        - eauto.
      }
Qed.

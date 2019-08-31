From Theories Require Import
  Tactics Chap_2_Framework.

Notation Unit := unit.

(** * Specification *)

(** ** Syntax *)

(* TODO: we may not need [t_var_a] without subtyping, as there is no information
     about type bounds to propagate inwards. *)
(*  [t_var_b]: bound type variable ala locally nameless
    [t_var_c]: concrete free type variable from opening [t_var_b] in [et_tabs]
               and [vt_tabs]
    [t_var_a]: abstract free type variable from opening [t_var_b] in [teq_all]
               and replaced by [subst] in [compat] *)
Inductive Typ :=
  | t_arr (t1 t2 : Typ)
  | t_all (t : Typ)
  | t_var_b (x : nat)
  | t_var_c (x : nat)
  | t_var_a (x : nat).

Inductive Exp :=
  | e_var (x : nat)
  | e_abs (e : Exp)
  | e_app (e1 e2 : Exp)
  | e_tabs (e : Exp)
  | e_tapp (e : Exp) (t : Typ).

(** ** Type System *)

Inductive TypBind :=
  | bind_exp (t : Typ)
  | bind_typ.

Definition TypEnv := List TypBind.
Definition AbsEnv := List Unit.

Inductive HasVars : nat -> nat -> nat -> Typ -> Prop :=
  | hv_arr :
      forall b a c t1 t2,
      HasVars b a c t1 ->
      HasVars b a c t2 ->
      HasVars b a c (t_arr t1 t2)
  | hv_all :
      forall b a c t2,
      HasVars (S b) a c t2 ->
      HasVars b a c (t_all t2)
  | hv_var_c :
      forall b a c x,
      c > x ->
      HasVars b a c (t_var_c x)
  | hv_var_a :
      forall b a c x,
      a > x ->
      HasVars b a c (t_var_a x)
  | hv_var_b :
      forall b a c x,
      b > x ->
      HasVars b a c (t_var_b x)
  .

(* Notation "'HasVars°' t [ b 'unbound' , a 'abstract' , c 'concrete' ]" := *)
(*   (HasVars b a c t) *)
(*   (at level 50, t at level 0, b at level 0, a at level 0, c at level 0). *)

Fixpoint open_rec (b' : nat) (t' : Typ) (t : Typ) : Typ :=
  match t with
  | t_arr t1 t2 => t_arr (open_rec b' t' t1) (open_rec b' t' t2)
  | t_all t2    => t_all (open_rec (S b') t' t2)
  | t_var_c c   => t_var_c c
  | t_var_a a   => t_var_a a
  | t_var_b b   => if beq_nat b' b then t' else t_var_b b
  end.

Definition open t' t := open_rec 0 t' t.

(* NOTE: The [HasVars] annotations are derived in the fsub formulation from subtyping.
         They are required in the safety proof and [invert_tabs] to show [stp2] reflexivity. *)
(* TODO: Are they just for convenience and can be derived instead? *)
Inductive ExpTyp : TypEnv -> Exp -> Typ -> Prop :=
  | et_var :
      forall x te t1,
      HasVars 0 0 (length te) t1 ->
      indexr x te = some (bind_exp t1) ->
      ExpTyp te (e_var x) t1
  | et_app :
      forall te c x t1 t2,
      ExpTyp te c (t_arr t1 t2) ->
      ExpTyp te x t1 ->
      ExpTyp te (e_app c x) t2
  | et_abs :
      forall te e t1 t2,
      HasVars 0 0 (length te) (t_arr t1 t2) ->
      ExpTyp (bind_exp t1 :: te) e t2 ->
      ExpTyp te (e_abs e) (t_arr t1 t2)
  | et_tapp :
      forall te c t11 t12 t,
      HasVars 0 0 (length te) t11 ->
      ExpTyp te c (t_all t12) ->
      t = open t11 t12 ->
      ExpTyp te (e_tapp c t11) t
  | et_tabs :
      forall te e t2,
      HasVars 0 0 (length te) (t_all t2) ->
      (* In [v_tabs] we also [open] with a [t_var_c], but in [et_tapp] we [open] with the real type. *)
      (* This is the reason why we need [teq_subst] in the soundness proof's [e_tapp] case! *)
      ExpTyp (bind_typ :: te) e (open (t_var_c (length te)) t2) ->
      ExpTyp te (e_tabs e) (t_all t2)
  .

(** ** Semantics *)

Inductive Val :=
  | v_abs  (ve : List Val) (e : Exp)  (* a closure for a term abstraction *)
  | v_tabs (ve : List Val) (e : Exp)  (* a closure for a type abstraction *)
  | v_typ  (ve : List Val) (t : Typ). (* a closure over a type *)

Definition ValEnv := List Val.

Fixpoint eval (n : nat) (ve : ValEnv) (t : Exp) {struct n} : CanTimeout (CanErr Val) :=
  match n with
  | 0 => timeout
  | S n =>
      match t with
      | e_var x => done (indexr x ve)
      | e_abs e => done (noerr (v_abs ve e))
      | e_tabs e => done (noerr (v_tabs ve e))
      | e_app e1 e2 =>
          ' v2 <- eval n ve e2;
          ' v_abs ve' e1' <- eval n ve e1;
          eval n (v2 :: ve') e1'
      | e_tapp e t =>
          ' v_tabs ve' e' <- eval n ve e;
          eval n (v_typ ve t :: ve') e'
      end
  end.

(** ** Type Soundness *)

(* Note, that the [teq_var_a1] and [teq_var_a2] rules don't apply without
   subtyping: bound variables inside a [tall] are only equal to themselves. They
   also can't be equal to a [t_var_c] directly mapping to [t_var_a], because
   such a [t_var_c] would mean the context outside of the [tall] would refer to
   the [tall]'s bound variable. *)
(* TODO: Try Function definition, we're not at subtyping yet. *)
Inductive TEq : ValEnv -> Typ -> ValEnv -> Typ -> AbsEnv -> Prop :=
  | teq_arr :
      forall ve1 ve2 t1 t2 t1' t2' ae,
      TEq ve1 t1 ve2 t2 ae ->
      TEq ve1 t1' ve2 t2' ae ->
      TEq ve1 (t_arr t1 t1') ve2 (t_arr t2 t2') ae
  | teq_all :
      forall ve1 ve2 t1 t2 x ae,
      x = length ae ->
      HasVars 1 (length ae) (length ve1) t1 ->
      HasVars 1 (length ae) (length ve2) t2 ->
      TEq ve1 (open (t_var_a x) t1) ve2 (open (t_var_a x) t2) (tt :: ae) ->
      TEq ve1 (t_all t1) ve2 (t_all t2) ae
  | teq_var_c1 :
      forall ve1 ve2 ve1' t1' x t2 ae,
      indexr x ve1 = some (v_typ ve1' t1') ->
      HasVars 0 0 (length ve1') t1' ->
      TEq ve1' t1' ve2 t2 ae ->
      TEq ve1 (t_var_c x) ve2 t2 ae
  | teq_var_c2 :
      forall ve1 ve2 ve2' t2' x t1 ae,
      indexr x ve2 = some (v_typ ve2' t2') ->
      HasVars 0 0 (length ve2') t2' ->
      TEq ve1 t1 ve2' t2' ae ->
      TEq ve1 t1 ve2 (t_var_c x) ae
  | teq_var_c12 :
      forall ve1 ve2 v x1 x2 ae,
      indexr x1 ve1 = some v ->
      indexr x2 ve2 = some v ->
      TEq ve1 (t_var_c x1) ve2 (t_var_c x2) ae
  | teq_var_a12 :
      forall ve1 ve2 x ae,
      indexr x ae = some tt ->
      TEq ve1 (t_var_a x) ve2 (t_var_a x) ae
  .

Inductive WfEnv : ValEnv -> TypEnv -> Prop :=
  | wfe_nil :
      WfEnv nil nil
  | wfe_cons :
      forall v t ve te,
      ValTyp (v :: ve) v t ->
      WfEnv ve te ->
      WfEnv (v :: ve) (t :: te)
with ValTyp : ValEnv -> Val -> TypBind -> Prop :=
  | vt_ty :
      forall ve1 ve2 te2 t,
      WfEnv ve2 te2 ->
      ValTyp ve1 (v_typ ve2 t) bind_typ
  | vt_abs :
      forall ve1 ve2 te2 e t1 t2 t,
      WfEnv ve2 te2 ->
      ExpTyp (bind_exp t1 :: te2) e t2 ->
      TEq ve2 (t_arr t1 t2) ve1 t [] ->
      ValTyp ve1 (v_abs ve2 e) (bind_exp t)
  | vt_tabs :
      forall ve1 ve2 te2 e t2 t,
      WfEnv ve2 te2 ->
      ExpTyp (bind_typ :: te2) e (open (t_var_c (length ve2)) t2) ->
      TEq ve2 (t_all t2) ve1 t [] ->
      ValTyp ve1 (v_tabs ve2 e) (bind_exp t)
  .

(** * Theorems *)

Hint Constructors Typ Exp Val ExpTyp ValTyp WfEnv Opt List HasVars TEq.
Hint Unfold indexr length ValEnv TypEnv open open_rec.
Hint Resolve ex_intro.

(** ** Lemmas about [index] *)

Lemma index_max :
  forall X xs n (x : X),
  indexr n xs = some x ->
  n < length xs.
Proof.
  intros X xs. induction xs.
  - Case1 "nil". intros. inversion H.
  - Case1 "cons".
    intros. inversion H.
    case_eq (beq_nat n (length xs)); intros E2.
    + Case2 "hit".
      eapply beq_nat_true in E2. subst n. compute. eauto.
    + Case2 "miss".
      rewrite E2 in H1.
      assert (n < length xs). eapply IHxs. apply H1.
      compute. eauto.
Qed.

Lemma index_has :
  forall X (xs : List X) n,
  length xs > n ->
  exists x, indexr n xs = some x.
Proof.
  intros. remember (length xs) as l.
  generalize dependent n.
  generalize dependent xs.
  induction l; intros; try omega.
  destruct xs; simpl.
  - simpl in Heql. inversion Heql.
  - simpl in Heql. inversion Heql. subst.
    case_eq (beq_nat n (length xs)); intros E.
    + eexists. reflexivity.
    + apply beq_nat_false in E. apply IHl; eauto.
      omega.
Qed.

Lemma index_extend :
  forall X xs n x' (x : X),
  indexr n xs = some x ->
  indexr n (x' :: xs) = some x.
Proof.
  intros.
  assert (n < length xs). eapply index_max. eauto.
  assert (beq_nat n (length xs) = false) as E. eapply beq_nat_false_iff. omega.
  unfold indexr. unfold indexr in H. rewrite H. rewrite E. reflexivity.
Qed.

Lemma index_extendr :
  forall {X} (xs : List X) (x x': X) (n : nat),
  indexr (S n) (xs ++ [x]) = some x' ->
  indexr n xs = some x'.
Proof.
  intros until 0; intros Hindex.
  induction xs.
  - eauto.
  - simpl.
    assert ((if S n =? length (xs ++ [x]) then some a else indexr (S n) (xs ++ [x]))
            = some x') by assumption.
    rewrite app_length in H.
    replace (S n =? length xs + length [x]) with (n =? length xs) in H.
    case_eq (n =? length xs); intros Hlen.
    + rewrite Hlen in H. assumption.
    + rewrite Hlen in H. eauto.
    + simpl. replace (length xs + 1) with (S (length xs)) by omega. reflexivity.
Qed.

Lemma index_hit2 :
  forall X n (x' x : X) xs,
  length xs = n ->
  x' = x ->
  indexr n (x' :: xs) = some x.
Proof.
  intros.
  unfold indexr.
  assert (beq_nat n (length xs) = true). eapply beq_nat_true_iff. eauto.
  rewrite H1. subst. reflexivity.
Qed.

(** ** Lemmas about [HasVars] *)

Lemma has_vars_inc :
  forall b a c t,
  HasVars b a c t ->
  forall b' a' c',
  b' >= b -> a' >= a -> c' >= c ->
  HasVars b' a' c' t.
Proof.
  intros b a c t H.
  induction H; intros; solve [eauto | constructor; repeat eapply_hyp; omega].
Qed.

Lemma has_vars_open :
  forall b a c t' t,
  HasVars (b+1) a c t ->
  HasVars b     a c t' ->
  HasVars b     a c (open_rec b t' t).
Proof.
  intros. generalize dependent b.
  induction t; intros; inversion H;
  try econstructor;
  try eapply IHt1; eauto; try eapply IHt2; eauto; try eapply IHt; eauto.
  eapply has_vars_inc; eauto.
  - Case "t_var_b". simpl.
    case_eq (beq_nat b x); intros E. eauto.
    econstructor. eapply beq_nat_false_iff in E. omega.
Qed.

(** ** Type Size for Size Induction *)

Fixpoint tsize (t : Typ) :=
  match t with
  | t_arr t1 t2 => S (tsize t1 + tsize t2)
  | t_all t2    => S (tsize t2)
  | t_var_b _   => 1
  | t_var_c _   => 1
  | t_var_a _   => 1
  end.

Lemma open_preserves_size :
  forall t x n,
  tsize t = tsize (open_rec n (t_var_a x) t).
Proof.
  intros t. induction t; intros; simpl; eauto.
  - simpl. destruct (beq_nat n x); eauto.
Qed.

Ltac induction_tsize t :=
  let Hsize := fresh in
  assert (Hsize : tsize t < S (tsize t)) by omega;
  remember (S (tsize t)) as n eqn:Heqn; clear Heqn; revert t Hsize;
  induction n;
  intro; (* Reintroduce t *)
  [intro; solve by inversion|]. (* Solve [tsize t < 0]. *)

(** ** [TEq] is an Equivalence Relation  *)

Lemma teq_refl :
  forall ae (ve : ValEnv) (t : Typ),
  HasVars 0 (length ae) (length ve) t ->
  TEq ve t ve t ae.
Proof.
  intros until 0; intros Hcl.
  induction Hcl. 2:{
    econstructor; eauto.
    (* [hv_all] doesn't open bound variables, but [teq_all] does.
         Hence, induction about [Hcl] probably doesn't work, so we use [tsize] instead.
         TODO: Do we really need [teq_all] to open bound variables? *)
Restart.
  intros ae ve t. revert ae ve.
  induction t; intros ae ve Hcl. 2:{
    inversion Hcl; subst.
    econstructor; eauto.
    (* IH doesn't fit because of opening. By going over [tsize] with [open_preserves_size] we're fine. *)
Restart.
  (* TODO: Tactic to avoid this intros/revert bullshit. *)
  intros ae ve t; revert ae ve.
  induction_tsize t.
  intros Hsize ae ve0 Hcl.
  inversion Hcl; subst.
  - (* TODO: proper tactic for size induction? *)
    assert (tsize t1 < n /\ tsize t2 < n) as [Hsize1 Hsize2]. { simpl in Hsize. omega. }
    econstructor.
    + eapply IHn. eauto. eauto.
    + eapply IHn. eauto. eauto.
  - assert (tsize t2 < n) as Hsize2. { simpl in Hsize. omega. }
    econstructor.
    + reflexivity.
    + eassumption.
    + eassumption.
    + eapply IHn.
      * simpl in Hsize. unfold open. rewrite <- open_preserves_size. assumption.
      * eapply has_vars_open.
          simpl. eapply has_vars_inc; eauto.
          simpl. eapply has_vars_inc; eauto.
  - eapply index_has in H; destruct H.
    eapply teq_var_c12.
    + eapply H.
    + eapply H.
  - eapply index_has in H; destruct H.
    edestruct x0.
    eapply teq_var_a12.
    eapply H.
  - solve by inversion.
Qed.

Lemma teq_sym :
  forall (ve1 ve2 : ValEnv) (t1 t2 : Typ),
  TEq ve1 t1 ve2 t2 [] ->
  TEq ve2 t2 ve1 t1 [].
Proof.
  induction 1; econstructor; solve [eauto].
Qed.

Lemma teq_trans :
  forall (ve1 ve2 ve3 : ValEnv) (t1 t2 t3 : Typ),
  TEq ve1 t1 ve2 t2 [] ->
  TEq ve2 t2 ve3 t3 [] ->
  TEq ve1 t1 ve3 t3 [].
Proof.
  intros until 0; intros Hteq1 Hteq2.
  revert t3 ve3 Hteq2.
  induction Hteq1; intros t3 ve3 Hteq2.
  Case "t_arr = _ = _".
    dependent induction Hteq2.
    Case2 "t_arr = t_arr = _".
      eauto.
    Case2 "t_arr = t_var_c = _".
      eauto.
  Case "t_all = _ = _".
    dependent induction Hteq2.
    Case2 "t_all = t_all = _".
      eauto.
    Case2 "t_all = t_var_c = _".
      eauto.
  Case "t_var_c = _ = _".
    eauto.
  Case "_ = t_var_c = _".
    dependent induction Hteq2; subst.
    Case2 "_ = t_var_c = _".
      rewrite H1 in H. inversion H; subst ve2' t2'; clear H.
      eauto.
    Case2 "_ = t_var_c = t_var_c".
      eauto.
    Case2 "_ = t_var_c = t_var_c".
      rewrite H in H1. inversion H1; subst v; clear H1.
      eauto.
  Case "t_var_c = t_var_c = _".
    dependent induction Hteq2.
    Case2 "t_var_c = t_var_c = _".
      rewrite H1 in H0. inversion H0; subst v; clear H0.
      eauto.
    Case2 "_ = t_var_c = t_var_c".
      eauto.
    Case2 "t_var_c = t_var_c = t_var_c".
      rewrite H1 in H0. inversion H0; subst v0; clear H0.
      eapply teq_var_c12; eauto.
  Case "t_var_a = t_var_a = _".
    dependent induction Hteq2.
      eauto.
      eauto.
Qed.

(** ** [TEq] and [ValTyp] are preserved under [ValEnv] Extension *)

Lemma teq_ext_ve :
  forall (v : Val) (ve1 ve2 : ValEnv) (t1 t2 : Typ) ae,
  TEq      ve1  t1      ve2  t2 ae ->
  TEq (v :: ve1) t1      ve2  t2 ae /\
  TEq      ve1  t1 (v :: ve2) t2 ae.
Proof.
  intros until 0; intros Hteq.
  induction Hteq; splith.
  Case "teq_arr".
    eauto.
  Case "teq_all".
    split; eapply teq_all; eauto; eapply has_vars_inc; simpl; eauto.
  Case "teq_var_c1".
    eauto using index_extend.
  Case "teq_var_c2".
    eauto using index_extend.
  Case "teq_var_c12".
    split; eapply teq_var_c12; eauto using index_extend.
  Case "teq_var_a12".
    eauto.
Qed.

Lemma vt_ext_ve :
  forall ve v v1 t,
  ValTyp ve v t ->
  ValTyp (v1 :: ve) v t.
Proof.
  intros. induction H.
  - eapply vt_ty. exact H.
  - econstructor.
    + exact H.
    + exact H0.
    + eapply teq_ext_ve; eauto.
  - econstructor.
    + exact H.
    + exact H0.
    + eapply teq_ext_ve; eauto.
Qed.

(** ** [ValTyp] is preserved along [TEq] *)

Lemma vt_widen :
  forall vf H1 H2 t1 t2,
  ValTyp H1 vf (bind_exp t1) ->
  TEq H1 t1 H2 t2 [] ->
  ValTyp H2 vf (bind_exp t2).
Proof.
  intros until 0; intros Hvt. dependent induction Hvt; intros Hteq; subst.
  - econstructor; eauto.
    eapply teq_trans; eauto.
  - econstructor; eauto.
    eapply teq_trans; eauto.
Qed.

(** ** Well-Formed Environments *)

Lemma wve_length :
  forall ve te,
  WfEnv ve te ->
  length ve = length te.
Proof.
  induction 1; simpl; auto.
Qed.

Hint Immediate wve_length.

Lemma wve_index :
  forall H1 ve1 TF i,
  WfEnv H1 ve1 ->
  indexr i ve1 = some TF ->
  exists v, indexr i H1 = some v /\ ValTyp H1 v TF.
Proof.
  intros until 0; intros Hwf Hindex. induction Hwf.
  - Case "nil". inversion Hindex.
  - Case "cons". inversion Hindex.
    case_eq (beq_nat i (length te)); intros E2.
    + Case2 "hit".
      rewrite E2 in H1. inversion H1; subst; clear H1.
      assert (Hlen : length te = length ve). { symmetry. eapply wve_length. eauto. }
      simpl. rewrite Hlen in E2. rewrite E2.
      eexists. split. reflexivity. assumption.
    + Case2 "miss".
      rewrite E2 in H1.
      assert (exists v0, indexr i ve = some v0 /\ ValTyp ve v0 TF) as [? [? ?]] by eauto.
      eexists. split. eapply index_extend. eauto.
      eapply vt_ext_ve. assumption.
Qed.

(** ** Lemmas about [open] and [subst] *)

(* Locally-nameless encoding with respect to var_a variables. *)
Fixpoint subst (u : Typ) (t : Typ) {struct t} : Typ :=
  match t with
  | t_arr t1 t2 => t_arr (subst u t1) (subst u t2)
  | t_all t2    => t_all (subst u t2)
  | t_var_b i   => t_var_b i
  | t_var_c i   => t_var_c i
  | t_var_a i   => if beq_nat i 0 then u else t_var_a (i-1)
  end.

Fixpoint nosubst (t : Typ) {struct t} : Prop :=
  match t with
  | t_arr t1 t2 => nosubst t1 /\ nosubst t2
  | t_all t2    => nosubst t2
  | t_var_b i   => True
  | t_var_c i   => True
  | t_var_a i   => i <> 0
  end.

Lemma nosubst_intro :
  forall b c t,
  HasVars b 0 c t ->
  nosubst t.
Proof.
  intros. generalize dependent b.
  induction t; intros; inversion H; simpl; eauto.
  omega.
Qed.

Lemma nosubst_open :
  forall b t' t,
  nosubst t' ->
  nosubst t ->
  nosubst (open_rec b t' t).
Proof.
  intros. generalize dependent b. induction t; intros;
  try inversion H0; simpl; eauto.
  case_eq (beq_nat b x); intros E. eauto. eauto.
Qed.

Lemma closed_nosubst2 :
  forall t t' b c,
  HasVars b 0 c t ->
  HasVars b 0 0 t' ->
  t = subst t' t.
Proof.
  intros t t' b c Hcl1 Hcl2.
  revert t' Hcl2.
  dependent induction Hcl1; intros t' Hcl2.
  * simpl.
    erewrite <- IHHcl1_1; eauto.
    erewrite <- IHHcl1_2; eauto.
  * simpl.
    erewrite <- IHHcl1; eauto.
    eapply has_vars_inc; eauto; omega.
  * simpl. reflexivity.
  * simpl. omega.
  * simpl. reflexivity.
Qed.

Lemma closed_nosubst :
  forall t n b,
  HasVars b 0 n t ->
  nosubst t /\ exists t', HasVars b 0 0 t' /\ t = subst t' t.
Proof.
  split.
  - eauto using nosubst_intro.
  - eexists. split.
    + eauto.
    + eapply closed_nosubst2; eauto.
Qed.

Lemma closed_subst :
  forall b a c t' t,
  HasVars b (a+1) c t ->
  HasVars 0  a    c t' ->
  HasVars b  a    c (subst t' t).
Proof.
  intros. generalize dependent b.
  induction t; intros; inversion H;
  try econstructor;
  try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto.
  - Case "t_var_a". simpl.
    case_eq (beq_nat x 0); intros E.
    eapply has_vars_inc; eauto; omega.
    econstructor. eapply beq_nat_false_iff in E. subst. omega.
Qed.

Lemma closed_no_open :
  forall t x b a c,
  HasVars b a c t ->
  t = open_rec b x t.
Proof.
  intros. induction H; intros; eauto;
  try solve [compute; compute in IHHasVars; rewrite <-IHHasVars; auto];
  try solve [compute; compute in IHHasVars1; compute in IHHasVars2;
    rewrite <-IHHasVars1; rewrite <-IHHasVars2; auto].
  Case "t_var_b".
    unfold open_rec. assert (b <> x0). omega.
    apply beq_nat_false_iff in H0.
    rewrite H0. auto.
Qed.

Lemma subst_open_commute_m :
  forall b a c a' t' t,
  HasVars (b+1) (a+1) c t ->
  HasVars 0 a' c t' ->
  subst t' (open_rec b (t_var_a (a+1)) t) = open_rec b (t_var_a a) (subst t' t).
Proof.
  intros. generalize dependent b. generalize dependent a.
  induction t; intros; inversion H; simpl; eauto;
    try rewrite IHt1; try rewrite IHt2; try rewrite IHt; eauto.
  - Case "t_var_b". simpl. case_eq (beq_nat b x); intros E.
    simpl. case_eq (beq_nat (a+1) 0); intros E2.
    eapply beq_nat_true_iff in E2. omega.
    assert (a+1-1 = a). omega. eauto.
    eauto.
  - Case "t_var_a". simpl. case_eq (beq_nat x 0); intros E.
    + eapply closed_no_open. eapply has_vars_inc; eauto; omega.
    + eauto.
Qed.

Lemma subst_open_commute :
  forall b a c t' t,
  HasVars (b+1) (a+1) c t ->
  HasVars 0 0 c t' ->
  subst t' (open_rec b (t_var_a (a+1)) t) = open_rec b (t_var_a a) (subst t' t).
Proof.
  intros. eapply subst_open_commute_m; eauto.
Qed.

Lemma subst_open_zero :
  forall b b' c t' t,
  HasVars b' 0 c t ->
  subst t' (open_rec b (t_var_a 0) t) = open_rec b t' t.
Proof.
  intros b b' c t' t; revert b b' c t'.
  induction t; intros until 0; intros Hcl.
  - inversion Hcl; subst.
    simpl.
    rewrite (IHt1 _ b' c).
    rewrite (IHt2 _ (S b') c).
    reflexivity.
    + eapply has_vars_inc; eauto.
    + eapply has_vars_inc; eauto.
  - inversion Hcl; subst.
    simpl.
    rewrite (IHt _ (S b') c).
    reflexivity.
    + eapply has_vars_inc; eauto.
  - simpl.
    inversion Hcl; subst.
    destruct (b =? x).
    + simpl. reflexivity.
    + simpl. reflexivity.
  - simpl.
    reflexivity.
  - inversion Hcl; subst.
    solve by inversion.
Qed.

(** ** [Compat] Definition & Lemmas for [teq_substitute] *)

(* [Compat ve' t' ve t1 t2] describes when [ve, t2] corresponds to
     [ve, t1] with [t_var_a] substituted by [ve', t'].
   We can either substitute [t_var_a 0] with
     1.  a free variable that's mapped [ve', t'] in [ve];
     2.  [t'], but only if [ve = ve']; or
     3.  anything, if there is no [t_var_a] in [t1].
   Only case 1 and 2 are used for [teq_substitute] in [invert_tabs], so the
     others are either for a complete compatibility proof or for a stronger
     induction hypothesis.
   The cases are instantiated to:
     1. [Compat ve0 t1 (v_typ ve0 t1 :: ve1) (open (t_var_a 0) t3) (open (t_var_c x) t3)]
     2. [Compat ve0 t1 ve0                  (open (t_var_a 0) t2) (open t1 t2)]
   Or more unfolded:
     1. [exists x1 : nat,
          index x1 (v_typ ve0 t1 :: ve1) = some (v_typ ve0 t1) /\
          open_rec 0 (t_var_c x) t3 = subst (t_var_c x1) (open (t_var_a 0) t3)].
     2. [ve0 = ve0 /\ open t1 t2 = subst t1 (open (t_var_a 0) t2)].
 *)
Reserved Notation "ve |- [ ve' , t' ]  t1 = t2" (at level 50, t1 at level 0).
Inductive Compat : ValEnv -> Typ -> ValEnv -> Typ -> Typ -> Prop :=
  | cp_indirect :
      forall x ve ve' t t',
      indexr x ve = some (v_typ ve' t') ->
      ve |- [ve', t'] t = subst (t_var_c x) t
  | cp_direct :
      forall ve t t',
      ve |- [ve, t'] t = subst t' t
  | cp_nosubst : (* TODO: having t'' existentially quantified still seems weird. *)
      forall ve ve' t t' t'',
      nosubst t ->
      HasVars 0 0 0 t'' ->
      ve |- [ve', t'] t = subst t'' t
  where "ve |- [ ve' , t' ]  t1 = t2" := (Compat ve' t' ve t1 t2).

Hint Constructors Compat.

Lemma compat_arr :
  forall ve' t' ve t11 t12 t2,
  ve |- [ve', t'] (t_arr t11 t12) = t2 ->
  HasVars 0 0 (length ve') t' ->
  exists t21 t22,
    t2 = t_arr t21 t22 /\
    ve |- [ve', t'] t11 = t21 /\
    ve |- [ve', t'] t12 = t22.
Proof.
  intros until 0; intros Hcompat Hcl. inversion Hcompat; subst.
  Case "cp_indirect".
    simpl. esplits; eauto.
  Case "cp_direct".
    simpl. esplits; eauto.
  Case "cp_nosubst".
    simpl. destruct H. esplits; eauto.
Qed.

Lemma compat_all :
  forall ve' t' ve t1 t2 a,
  ve |- [ve', t'] (t_all t1) = t2 ->
  HasVars 0 0 (length ve') t' ->
  HasVars 1 (a+1) (length ve) t1 ->
  exists t2',
    t2 = t_all t2' /\
    HasVars 1 a (length ve) t2' /\
    ve |- [ve', t'] (open (t_var_a (a+1)) t1) = open (t_var_a a) t2'.
Proof.
  intros until 0; intros Hcompat Hcl1 Hcl2.
  unfold open.
  inversion Hcompat; subst; simpl in *.
  - esplits.
    + reflexivity.
    + eapply closed_subst.
      * eauto.
      * simpl in Hcompat. eapply index_max in H. apply hv_var_c. omega.
    + erewrite <- subst_open_commute.
      * eauto.
      * eauto.
      * eapply index_max in H. eauto.
  - esplits.
    + reflexivity.
    + eapply closed_subst.
      * eauto.
      * eapply has_vars_inc; eauto; omega.
    + erewrite <- subst_open_commute; eauto.
  - esplits.
    + reflexivity.
    + eapply closed_subst.
      * eauto.
      * eapply has_vars_inc; eauto; simpl; omega.
    + erewrite <- subst_open_commute; eauto.
      * eapply cp_nosubst.
          eapply nosubst_open; eauto; simpl; omega.
          eauto.
      * eapply has_vars_inc; eauto; omega.
Qed.

Lemma compat_var_c :
  forall ve' t' ve1 t1' ve2 t2 x,
  ve1 |- [ve', t'] (t_var_c x) = t1' ->
  HasVars 0 0 (length ve') t' ->
  HasVars 0 0 (length ve2) t2 ->
  indexr x ve1 = some (v_typ ve2 t2) ->
  exists t2', t1' = (t_var_c x) /\ ve2 |- [ve', t'] t2 = t2'.
Proof.
  intros until 0; intros Hcompat Hcl1 Hcl2 Hindex. inversion Hcompat; subst.
  Case "cp_indirect".
    simpl. eexists. intuition. eapply cp_nosubst. eapply closed_nosubst. eauto. eauto.
  Case "cp_direct".
    simpl. eexists. intuition. eapply cp_nosubst. eapply closed_nosubst. eauto. eauto.
  Case "cp_nosubst".
    simpl. eexists. intuition. eapply cp_nosubst. eapply closed_nosubst. eauto. eauto.
Qed.

Lemma compat_var_a :
  forall ve' t' ve t1 ae0 x,
  ve |- [ve', t'] (t_var_a x) = t1 ->
  HasVars 0 0 (length ve') t' ->
  indexr x (ae0 ++ [tt]) = some tt ->
  x = 0 \/ exists t2,
    x > 0 /\ t1 = t_var_a (x-1) /\
    indexr (x-1) ae0 = some tt /\
    ve' |- [ve', t'] t1 = t2.
Proof.
  intros until 0; intros Hcompat Hcl Hindex.
  case_eq (beq_nat x 0); intros E.
  - left. eapply beq_nat_true_iff. assumption.
  - right.
    assert (x <> 0) by (eapply beq_nat_false_iff; eauto).
    assert (x > 0) by omega.
    + eexists. intuition.
      * inversion Hcompat; subst.
        -- simpl. rewrite E. reflexivity.
        -- simpl. rewrite E. reflexivity.
        -- simpl. rewrite E. reflexivity.
      * eapply index_extendr.
        replace (S (x - 1)) with x by omega.
        eassumption.
Qed.

(** ** Equivalence between Type Vars in Context & Substitution *)

Lemma teq_substitute :
  forall ve1 ve2 t1 t2 ae ve' t' t1' t2',
  TEq ve1 t1 ve2 t2 (ae ++ [tt]) ->
  HasVars 0 0 (length ve') t' ->
  ve1 |- [ve', t'] t1 = t1' ->
  ve2 |- [ve', t'] t2 = t2' ->
  TEq ve1 t1' ve2 t2' ae.
Proof.
  intros until 0; intros Hteq.
  revert t1' t2' t' ve'.
  dependent induction Hteq; intros t1'' t2'' t' ve' CX IX1 IX2.
  - Case "teq_arr".
    eapply compat_arr in IX1; [|assumption]. repeat destruct IX1 as [? IX1].
    eapply compat_arr in IX2; [|assumption]. repeat destruct IX2 as [? IX2].
    subst. eapply teq_arr.
    + eauto.
    + eauto.
  - Case "teq_all".
    eapply compat_all in IX1.
    eapply compat_all in IX2.
    + splith. subst. eapply teq_all.
      * eauto.
      * eassumption.
      * eassumption.
      * eapply IHHteq.
          reflexivity.
          eassumption.
          rewrite app_length. simpl. assumption.
          rewrite app_length. simpl. assumption.
    + eassumption.
    + rewrite app_length in *. eassumption.
    + rewrite app_length in *. eassumption.
    + rewrite app_length in *. eassumption.
  - Case "teq_var_c1".
    eapply (compat_var_c ve' t' ve1 t1'' ve1' t1') in IX1; eauto.
    repeat destruct IX1 as [? IX1].
    subst.
    assert (ve1' |- [ve', t'] t1' = t1') as CPX. {
      eapply closed_nosubst in H0; splith.
      rewrite H4 at 2.
      eapply cp_nosubst; eauto.
    }
    info_eauto.
  - Case "teq_var_c2".
    eapply (compat_var_c ve' t' ve2 t2'' ve2' t2') in IX2; eauto.
    repeat destruct IX2 as [? IX2].
    subst.
    assert (ve2' |- [ve', t'] t2' = t2') as CPX. {
      eapply closed_nosubst in H0; splith.
      rewrite H4 at 2.
      eapply cp_nosubst; eauto.
    }
    info_eauto.
  - Case "teq_var_c12".
    assert (t1'' = t_var_c x1). { inversion IX1; reflexivity. }
    assert (t2'' = t_var_c x2). { inversion IX2; reflexivity. }
    subst.
    info_eauto.
  - Case "teq_var_a12".
    pose (IXX1 := compat_var_a ve' t' ve1 t1'' ae _ IX1 CX H); clearbody IXX1.
    pose (IXX2 := compat_var_a ve' t' ve2 t2'' ae _ IX2 CX H); clearbody IXX2.
    destruct IXX1; destruct IXX2.
    + subst x. inversion IX1; inversion IX2; subst; simpl in *.
      * eapply teq_var_c12; eauto.
      * eapply teq_var_c1; eauto.
        eapply teq_refl. eapply has_vars_inc; eauto; omega.
      * omega.
      * eapply teq_var_c2; eauto.
        eapply teq_refl. eapply has_vars_inc; eauto; omega.
      * eapply teq_refl. eapply has_vars_inc; eauto; omega.
      * omega.
      * omega.
      * omega.
      * omega.
    + splith; subst. omega.
    + splith; subst. omega.
    + splith; subst. eapply teq_var_a12. assumption.
Qed.

Lemma teq_subst :
  forall (t1 t2 t2' : Typ) (ve ve' : ValEnv),
  HasVars 0 0 (length ve) t1 ->
  TEq ve' (t_all t2') ve (t_all t2) [ ] ->
  TEq (v_typ ve t1 :: ve') (open (t_var_c (length ve')) t2') ve (open t1 t2) [ ].
Proof.
  intros until 0; intros Hcl1 Hteq.
  inversion Hteq; subst; simpl in *.
  eapply teq_substitute with (ae := nil).
  - eapply teq_ext_ve. eassumption.
  - exact Hcl1.
  - erewrite <- (subst_open_zero 0 _ _ (t_var_c (length ve'))); eauto.
    eapply cp_indirect.
    eapply index_hit2; eauto.
  - erewrite <- (subst_open_zero 0 _ _ t1); eauto using cp_direct.
Qed.

(** ** Value Inversion Lemmas *)

Lemma invert_abs :
  forall ve vf t1 t2,
  ValTyp ve vf (bind_exp (t_arr t1 t2)) ->
  exists ve2 te2 e t1' t2',
    vf = v_abs ve2 e /\
    WfEnv ve2 te2 /\
    ExpTyp (bind_exp t1' :: te2) e t2' /\
    TEq ve t1 ve2 t1' [] /\
    TEq ve t2 ve2 t2' [].
Proof.
  intros. inversion H; subst.
  Case "vt_abs".
    inversion H5; subst.
    exists ve2, te2, e, t0, t3. intuition.
    eauto using teq_sym.
    eauto using teq_sym.
  Case "vt_tabs".
    inversion H5.
Qed.

Lemma invert_tabs :
  forall ve1 v t,
  ValTyp ve1 v (bind_exp (t_all t)) ->
  exists ve2 te2 e t',
    v = v_tabs ve2 e /\
    WfEnv ve2 te2 /\
    ExpTyp (bind_typ :: te2) e (open (t_var_c (length ve2)) t') /\
    TEq ve1 (t_all t) ve2 (t_all t') [].
Proof.
  intros until 0; intros Hvt. inversion Hvt.
  Case "vt_abs".
    match goal with
    | [ H : TEq _ (t_arr _ _) _ (t_all _) _ |- _ ] => inversion H
    end.
  Case "vt_tabs".
    do 4 eexists.
    intuition eauto.
    eauto using teq_sym.
Qed.

(** ** Type Soundness Theorem *)

Tactic Notation "destruct_eval" constr(e) "as" "[" ident(mv) ident(Heval) "]" :=
  remember (eval _ _ e) as mmv eqn:Heval; symmetry in Heval;
  destruct mmv as [mv|]; try solve by inversion.

Theorem type_soundness :
  forall n e te ve mv t,
  eval n ve e = some mv ->
  ExpTyp te e t ->
  WfEnv ve te ->
  exists v, mv = some v /\ ValTyp ve v (bind_exp t).
Proof.
  intros n. induction n; intros until 0; intros Heval Hty Hwf.
  Case "n = 0".
    inversion Heval.
  Case "n = S n".
    destruct e.
    Case2 "e_var".
      (* Evaluating a variable succeeds, if looking it up the [ValEnv] succeeds. *)
      simpl in Heval.
      inversion Heval; subst; clear Heval.
      (* The variable is well-typed, so we were able to look it up in the [TypEnv]. *)
      inversion Hty; subst; rename H0 into Hcl; rename H2 into Hty'.
      (* For wellformed environments, we proved in [wve_index], that if a *)
      (* variable has a type in the [TypEnv], then it also has a value in the [ValEnv] *)
      (* with the corresponding [ValTyp], which is exactly our goal. *)
      exact (wve_index _ _ _ _ Hwf Hty').
    Case2 "e_abs".
      (* Evaluating a lambda abstraction always succeeds by taking the closure *)
      (* in the current [ValEnv]. *)
      simpl in Heval.
      inversion Heval; subst.
      eexists; intuition.
      (* The lambda abstraction is well-typed, so it's body is well-typed, too. *)
      inversion Hty; subst; rename H0 into Hcl; rename H2 into Hty'.
      (* We construct the value typing for the closure from scratch: *)
      eapply vt_abs.
        (* The captured environment is the one we are currently in, so it is *)
        (* well-formed by assumption. *)
        Case3 "WfEnv". exact Hwf.
        (* We reuse the body typing from the lambda abstractions [ExpTyp]. *)
        Case3 "Body Typing". exact Hty'.
        (* As we are in the same environment, that the closure captured, *)
        (* the [TEq] is simply reflexivity of [t_arr t1 t2]. *)
        (* This doesn't have to be the case, when we examine the closure of [e1] *)
        (* in the [e_app e1 e2] case. *)
        Case3 "Type Equiv".
          eapply teq_refl. simpl. rewrite (wve_length _ _ Hwf). assumption.
    Case2 "e_app".
      (* The lambda application is well-typed, so both it's sub-expressions are too. *)
      inversion Hty; subst te0 c x t2;
        rename H2 into Hty1; rename H4 into Hty2; rename t into t2.

      (* Evaluating a lambda application [e_app e1 e2] only succeeds if *)
      (* - [e1] evaluates to a closure [v_abs ve' e1']; *)
      (* - [e2] evaluates to some [v2]; and *)
      (* - the closure's body [e1'] evaluates with it's [ValEnv] extended by [v2]. *)
      simpl in Heval.

      (* Evaluating [e2] can't timeout without contradicting [Heval]. *)
      destruct_eval e2 as [mv2 Heval2].
      (* Now that we know that evaluating [e2] can't timeout, we can apply the *)
      (* induction hypothesis to find out that it also doesn't fail and has it's [ExpTyp] as [ValTyp]. *)
      assert (HR2 : exists v2, mv2 = some v2 /\ ValTyp ve v2 (bind_exp t1)).
        { eapply IHn; eauto. }
      inversion HR2 as [v2 [E2 Hvt2]].
      subst mv2.

      (* Evaluating [e1] also can't timeout without contradicting [Heval]. *)
      destruct_eval e1 as [mv1 Heval1].
      (* Now that we know that evaluating [e1] can't timeout, we can apply the *)
      (* induction hypothesis to find out that it also doesn't fail and has it's [ExpTyp] as [ValTyp]. *)
      assert (HR1 : exists v1, mv1 = some v1 /\ ValTyp ve v1 (bind_exp (t_arr t1 t2))).
        { eapply IHn; eauto. }
      inversion HR1 as [v1 [E1 Hvt1]].
      subst mv1.

      (* The [ExpTyp] of [e1] was [t_arr t1 t2], so the [ValTyp] of [v1] is too, *)
      (* so we can invert the [ValTyp] to find out that [v1] is in fact a closure. *)
      destruct (invert_abs _ _ _ _ Hvt1) as
        (ve1 & te1 & e1' & t1' & t2' & Ev1 & Hwf1 & Hty1' & Hteq1 & Hteq2).
      subst v1.
      (* Note that the body isn't given an [ExpTyp] for [t1] and [t2], but instead *)
      (* an [ExpTyp] for some [t1'] and [t2'] which are equivalent to [t1] and [t2], *)
      (* but relative to the captured environment [ve1] instead of the current environment [ve]. *)

      (* At this point, we provided the first two conditions as definitional equalities, *)
      (* so [Heval] simplified to the third condition, i.e. that the closure's body *)
      (* evaluates successfully in it's [ValEnv] extended with the argument value [v2]. *)

      (* If we apply the induction hypothesis to [Heval] we get a [ValTyp] *)
      (* in the closure's environment *)
      (*   [exists v, mv = some v /\ ValTyp (v2 :: ve1) v (bind_exp t2')] *)
      (* but our goal requires a [ValTyp] in the current environment *)
      (*   [exists v, mv = some v /\ ValTyp ve v (bind_exp t2)] *)
      (* so we still need to relate the two. Luckily, the [invert_abs] gave us *)
      (*   [TEq ve1 t2' ve t2 []] *)
      (* so we can use [teq_ext_ve] to add the unused [v2] *)
      (*   [TEq (v2 :: ve1) t2' ve t2 []] *)
      (* and then use [vt_widen] to transport the [ValTyp] along that equivalence. *)

      (* To apply the induction hypothesis to [Heval], we still need to extend the *)
      (* [WfEnv] of the captured environment with the argument [v2] and its type [t1']. *)
      (* But we only have [ValTyp ve v2 t1] in the current environment, so we have to extend *)
      (*   [TEq ve t1 ve1 t1'] *)
      (* to *)
      (*   [TEq ve t1 (v2 :: ve1) t1'] *)
      (* and then transport the [ValTyp] along that equivalence. *)
      assert (Hwf1' : WfEnv (v2 :: ve1) (bind_exp t1' :: te1)). {
        econstructor.
        - eapply vt_widen.
          + exact Hvt2.
          + eapply teq_ext_ve; exact Hteq1.
        - exact Hwf1.
      }

      (* Apply IH as noted above. *)
      assert (exists v, mv = some v /\ ValTyp (v2 :: ve1) v (bind_exp t2')) as HR.
        { eapply IHn; eauto. }
      inversion HR as [v [E Hvt]].
      subst mv.

      eexists; intuition.
      (* Transport [Hvt] along [TEq (v2 :: ve1) t2' ve t2 []] as noted above. *)
      eapply vt_widen; eauto.
      eapply teq_ext_ve; eauto.
      eapply teq_sym; eauto.
    Case2 "e_tabs".
      (* Note that this case is *exactly* the same as [e_abs], up to *)
      (* the rewrite in [Case3 "Body Typing"]. *)
      (* Evaluating a type abstraction always succeeds by taking the closure *)
      (* in the current [ValEnv]. *)
      simpl in Heval.
      inversion Heval; subst mv; clear Heval.
      eexists; intuition.
      (* The type abstraction is well-typed, so it's body is well-typed, too. *)
      inversion Hty; subst; rename H0 into Hcl; rename H2 into Hty'.
      (* We construct the value typing for the closure from scratch: *)
      eapply vt_tabs.
        (* The captured environment is the one we are currently in, so it is *)
        (* well-formed by assumption. *)
        Case3 "WfEnv". exact Hwf.
        (* We reuse the body typing from the lambda abstractions [ExpTyp]. *)
        Case3 "Body Typing". rewrite (wve_length _ _ Hwf). exact Hty'.
        (* As we are in the same environment, that the closure captured, *)
        (* the [TEq] is simply reflexivity of [t_arr t1 t2]. *)
        (* This doesn't have to be the case, when we examine the closure of [e1] *)
        (* in the [e_app e1 e2] case. *)
        Case3 "Type Equiv".
          eapply teq_refl. simpl. rewrite (wve_length _ _ Hwf). assumption.
    Case2 "e_tapp".
      rename t0 into t1.
      (* If a type application is well-typed, then so is the sub-expression. *)
      inversion Hty; subst c t11 t0 te0;
        rename H1 into Hcl1; rename H3 into Hty';
        rename t12 into t2.
      subst t.

      (* Evaluating a type application [e_tapp e t1] only succeeds if *)
      (* - [e] evaluates to a type closure [v_tabs ve' e']; *)
      (* - the closure's body [e1'] evaluates with it's [ValEnv] extended by [v_typ ve t1]. *)
      simpl in Heval.

      (* Evaluating [e] can't timeout without contradicting [Heval]. *)
      destruct_eval e as [mv1 Heval1].
      (* Now that we know that evaluating [e] can't timeout, we can apply the *)
      (* induction hypothesis to find out that it also doesn't fail and has it's [ExpTyp] as [ValTyp]. *)
      assert (HR1 : exists v1, mv1 = some v1 /\ ValTyp ve v1 (bind_exp (t_all t2))).
        { eapply IHn; eauto. }
      inversion HR1 as [v1 [E1 Hvt1]].
      subst mv1.

      (* The [ExpTyp] of [e] was [t_all t2], so the [ValTyp] of [v1] is too, *)
      (* so we can invert the [ValTyp] to find out that [v1] is in fact a type closure. *)
      destruct (invert_tabs _ _ _ Hvt1) as
        (ve1 & te1 & e1' & t2' & Ev1 & Hwf1 & Hty1' & Hteq).
      subst v1.
      (* Note that the body isn't given an [ExpTyp] for [t2], but instead *)
      (* an [ExpTyp] for some [t2'] which are equivalent to [t2], *)
      (* but relative to the captured environment [ve1] instead of the current environment [ve]. *)

      (* At this point, we provided the first two conditions as definitional equalities, *)
      (* so [Heval] simplified to the third condition, i.e. that the closure's body *)
      (* evaluates successfully in it's [ValEnv] extended with the argument value [v_typ ve t1]. *)

      (* If we apply the induction hypothesis to [Heval] we get a [ValTyp] *)
      (* in the closure's environment *)
      (*   [ValTyp (v_typ ve t1 :: ve1) v (bind_exp (open (t_var_c (length ve1)) t2'))] *)
      (* but our goal requires a [ValTyp] in the current environment *)
      (*   [ValTyp ve                  v (bind_exp (open t1                     t2 ))] *)
      (* so we still need to relate the two. Luckily, the [invert_tabs] gave us *)
      (*   [TEq ve (t_all t2)                  ve1  (t_all t2') []] *)
      (* so we can use [teq_subst] to get *)
      (*   [TEq ve (open t1 t2) (v_typ ve t1 :: ve1) (open (t_var_c (length ve1)) t2') []] *)
      (* and then use [vt_widen] to transport the [ValTyp] along that equivalence. *)

      (* Apply IH as noted above. *)
      assert (exists v, mv = some v /\
                   ValTyp (v_typ ve t1 :: ve1) v
                          (bind_exp (open (t_var_c (length ve1)) t2'))) as HR.
        { eapply IHn; info_eauto. }
      inversion HR as [v [E Hvt]].
      subst mv.

      (* Lemma for [teq_subst] below. *)
      assert (Hcl1' : HasVars 0 0 (length ve) t1).
        { erewrite wve_length; eassumption. }

      eexists; intuition.
      (* Transport [Hvt] along [$horrible_teq] as noted above. *)
      eapply vt_widen; eauto.
      eapply teq_subst; eauto.
      eapply teq_sym; eauto.
Qed.

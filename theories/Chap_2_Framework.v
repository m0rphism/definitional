From Theories Require Import
  Tactics.

(** * Maybe *)

Notation Opt := option.
Notation some := Some.
Notation none := None.

Notation CanTimeout := option (only parsing).
Notation timeout := None (only parsing).
Notation done := Some (only parsing).

Notation CanErr := option (only parsing).
Notation error := None (only parsing).
Notation noerr := Some (only parsing).

Notation Result X := (CanTimeout (CanErr X)) (only parsing).

Definition omap {X Y : Type} (f : X -> Y) (mx : Opt X) : Opt Y :=
  match mx with
  | none => none
  | some x => some (f x)
  end.

(* Note that this notation allows [MonadFail] style patterns for [p]. *)
Notation "' p <- e1 ; e2" :=
  (match e1 with
   | some (some p) => e2
   | some _ => some none
   | none => none
   end)
  (right associativity, at level 60, p pattern).

(** * Lists *)

From Coq Require Export
  Lists.List.

Export ListNotations.
Open Scope list_scope.

Notation List := list.

(** ** List Suffixes  *)

Definition IsSuffixOf {X} (xs1 xs2 : List X) : Prop :=
  exists xs, xs ++ xs1 = xs2.

Lemma suffix_refl :
  forall {X} {xs : List X},
  IsSuffixOf xs xs.
Proof.
  intros.
  unfold IsSuffixOf.
  exists []. reflexivity.
Qed.

Lemma suffix_trans :
  forall {X} {xs1 xs2 xs3 : List X},
  IsSuffixOf xs1 xs2 ->
  IsSuffixOf xs2 xs3 ->
  IsSuffixOf xs1 xs3.
Proof.
  intros until 0. intros [xs1' Hss1] [xs2' Hss2].
  subst.
  rewrite app_assoc.
  exists (xs2' ++ xs1'). reflexivity.
Qed.

(** ** List Indexing  *)

Fixpoint indexr {X : Type} (n : nat) (xs : List X) : Opt X :=
  match xs with
  | []      => none
  | x :: xs' => if beq_nat n (length xs') then some x else indexr n xs'
  end.

Fixpoint indexl {X : Type} (n : nat) (xs : List X) : Opt X :=
  match xs with
  | []      => none
  | x :: xs' => if beq_nat n 0 then some x else indexr n xs'
  end.

Lemma indexr_max :
  forall X (xs : List X) (n : nat) (x : X),
  indexr n xs = some x ->
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

Lemma indexr_extend :
  forall X xs n x' (x : X),
  indexr n xs = some x ->
  indexr n (x' :: xs) = some x.
Proof.
  intros ? ? ? ? ? H. simpl. rewrite H.
  assert (n < length xs) as H0. { eapply indexr_max. exact H. }
  assert (n <> length xs) as H1. { omega. }
  assert ((n =? length xs) = false) as H2. { eapply beq_nat_false_iff. exact H1. }
  rewrite H2. reflexivity.
Qed.

Lemma indexr_suffix:
  forall {X} n (xs1 xs2 : List X) (x : X),
  indexr n xs1 = some x ->
  IsSuffixOf xs1 xs2 ->
  indexr n xs2 = some x.
Proof.
  intros until 0; intros Hindex Hsub.
  destruct Hsub as [xs Hsub].
  subst xs2.
  induction xs.
  - assumption.
  - simpl in *. case_eq (n =? length (xs ++ xs1)); intros.
    + eapply indexr_max in IHxs. eapply beq_nat_true in H. omega.
    + assumption.
Qed.

(** ** List Updating  *)

Fixpoint update {X : Type} (n : nat) (x' : X) (xs : List X) : List X :=
  match xs with
  | [] => []
  | x :: xs => if beq_nat n (length xs)
              then x' :: xs
              else x  :: update n x' xs
  end.

(** ** [Forall2] *)

Inductive Forall2 {X Y : Type} (R : X -> Y -> Prop) : List X -> List Y -> Prop :=
  | Forall2_nil :
      Forall2 R [] []
  | Forall2_cons :
      forall (x : X) (y : Y) (xs : List X) (ys : List Y),
      R x y ->
      Forall2 R xs ys ->
      Forall2 R (x :: xs) (y :: ys).

Lemma fa2_length :
  forall {X Y} {P : X -> Y -> Prop} {xs ys},
  Forall2 P xs ys ->
  length xs = length ys.
Proof.
  intros until 0. intros H. induction H.
  Case "fa2_nil". reflexivity.
  Case "fa2_cons". simpl. rewrite IHForall2. reflexivity.
Qed.

Hint Immediate fa2_length.

Lemma fa2_indexr :
  forall {X Y} {P : X -> Y -> Prop} {xs ys} {y} {n},
  Forall2 P xs ys ->
  indexr n ys = some y ->
  exists x, indexr n xs = some x /\ P x y.
Proof.
  intros until 0. intros HWf Hindex. induction HWf.
  Case "wfe_nil".
    simpl in Hindex. inversion Hindex.
  Case "wfe_cons".
    simpl in Hindex.
    assert (length xs = length ys) as Hlen. { eauto using fa2_length. }
    case_eq (n =? length xs).
    Case2 "index hits head".
      intros Hhit.
      assert (indexr n (x :: xs) = some x). { simpl. rewrite Hhit. reflexivity. }
      rewrite Hlen in Hhit. rewrite Hhit in Hindex.
      inversion Hindex; subst y0; clear Hindex.
      eauto.
    Case2 "index hits tail".
      intros Hmiss.
      rewrite Hlen in Hmiss.
      rewrite Hmiss in Hindex.
      specialize (IHHWf Hindex). inversion IHHWf as [v0 [H0 H1]].
      exists v0. constructor. { apply indexr_extend. exact H0. } { exact H1. }
Qed.

Lemma fa2_update_l:
  forall {X Y} (R : X -> Y -> Prop) (xs : List X) (ys : List Y) (n : nat) (x : X) (y : Y),
  indexr n ys = some y ->
  Forall2 R xs ys ->
  R x y ->
  Forall2 R (update n x xs) ys.
Proof.
  intros until 0; intros Hindex Hwfs Hvt.
  revert Hindex Hvt.
  induction Hwfs; intros Hindex Hvt.
  - simpl. econstructor.
  - simpl in *.
    rewrite (fa2_length Hwfs).
    case_eq (n =? length ys); intros Hlength.
    + rewrite Hlength in *.
      inversion Hindex; subst y0; clear Hindex.
      econstructor.
      * exact Hvt.
      * exact Hwfs.
    + rewrite Hlength in *.
      econstructor.
      * exact H.
      * eapply IHHwfs.
        exact Hindex.
        exact Hvt.
Qed.

Lemma fa2_update_r:
  forall {X Y} (R : X -> Y -> Prop) (xs : List X) (ys : List Y) (n : nat) (x : X) (y : Y),
  indexr n xs = some x ->
  Forall2 R xs ys ->
  R x y ->
  Forall2 R xs (update n y ys).
Proof.
  intros until 0; intros Hindex Hwfs Hvt.
  revert Hindex Hvt.
  induction Hwfs; intros Hindex Hvt.
  - simpl. econstructor.
  - simpl in *.
    rewrite <- (fa2_length Hwfs).
    case_eq (n =? length xs); intros Hlength.
    + rewrite Hlength in *.
      inversion Hindex; subst x0; clear Hindex.
      econstructor.
      * exact Hvt.
      * exact Hwfs.
    + rewrite Hlength in *.
      econstructor.
      * exact H.
      * eapply IHHwfs.
        exact Hindex.
        exact Hvt.
Qed.

(* Lemma wfstore_extend_inner: *)
Lemma fa2_map:
  forall {X Y} (R1 : X -> Y -> Prop) (R2 : X -> Y -> Prop) {xs : List X} {ys : List Y},
    Forall2 R1 xs ys ->
    (forall x y, R1 x y -> R2 x y) ->
    Forall2 R2 xs ys.
Proof.
  induction xs; intros until 0; intros fa f.
  - inversion fa. subst. constructor.
  - inversion fa; subst.
    econstructor.
    + eapply f. eassumption.
    + eapply IHxs.
      exact H3.
      exact f.
Qed.


Fixpoint map {X Y} (f : X -> Y) (xs : List X) : List Y :=
  match xs with
  | [] => []
  | x :: xs => f x :: map f xs
  end.


Lemma map_preserves_length :
  forall {X Y} (f : X -> Y) (xs : List X),
  length (map f xs) = length xs.
Proof.
  intros X Y f xs.
  induction xs.
  Case "xs = nil". simpl. reflexivity.
  Case "xs = cons a xs". simpl. rewrite IHxs. reflexivity.
Qed.

Lemma map_append_comm :
  forall {X Y} (f : X -> Y) (xs1 xs2 : List X),
  map f (xs1 ++ xs2) = map f xs1 ++ map f xs2.
Proof.
  intros. induction xs1.
  - simpl. reflexivity.
  - simpl. rewrite IHxs1. reflexivity.
Qed.


(** * Theorems *)

Hint Constructors Opt List Forall2.
Hint Unfold indexr indexl length IsSuffixOf omap update.

(* Lemma wfenv_substore: *)
(*   forall (te : TypEnv) (ve : ValEnv) (ts1 ts2 : TypStore), *)
(*   WfEnv ve te ts1 -> *)
(*   SubStore ts1 ts2 -> *)
(*   WfEnv ve te ts2. *)
(* Proof. *)
(*   intros; eapply valtype_wfenv_substore; eauto. *)
(* Qed. *)

(* Lemma wfstore_extend_inner: *)
(*   forall (ts ts' : TypStore) (vs : ValStore) (t : Typ), *)
(*     Forall2 (ValTyp ts') vs ts -> *)
(*     Forall2 (ValTyp (t :: ts')) vs ts. *)
(* Proof. *)
(*   induction ts; intros ts' vs t Hwfs. *)
(*   - inversion Hwfs. subst. constructor. *)
(*   - inversion Hwfs; subst. *)
(*     econstructor. *)
(*     + eapply valtype_substore. *)
(*       * eapply H2. *)
(*       * exists [t]. reflexivity. *)
(*     + eapply IHts. *)
(*       exact H3. *)
(* Qed. *)

(* Lemma wfstore_extend: *)
(*   forall (v : Val) (vs : ValStore) (t : Typ) (ts : TypStore), *)
(*   WfStore vs ts -> *)
(*   ValTyp ts v t -> *)
(*   WfStore (v :: vs) (t :: ts). *)
(* Proof. *)
(*   intros until 0; intros Hwfs Hvt. *)
(*   econstructor. *)
(*   - eapply valtype_substore. *)
(*     + exact Hvt. *)
(*     + exists [t]. reflexivity. *)
(*   - eapply wfstore_extend_inner. exact Hwfs. *)
(* Qed. *)

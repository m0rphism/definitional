From Coq Require Export
  Omega
  Program.Equality.

From Theories Require Export
  CpdtTactics.

(** * Case *)

(** Alternatives to the usual case markers [-], [+], and [*].

    [Case_n "m = O"] poses an info assumption [case_n := "m = O" : string],
    which has the sideeffect of preventing another [Case] on the same level,
    before the previous goal is finished.
 *)

Require Import String.
Open Scope string_scope.

Tactic Notation "Case_aux" ident(id) constr(val) :=
  first
    [ set (id := val); move id at top
    | fail 1 "previous" id "not finished."
    ].

Tactic Notation "Case_aux'" ident(id) ident(prev_id) constr(val) :=
  match goal with
  | [ H' : _ |- _ ] => unify id H'; fail 1 "Previous" id "not finished."
  | _ => idtac
  end;
  match goal with
  | [ H' : _ |- _ ] => unify prev_id H'
  | _ => fail 1 "Can't introduce" id "without first introducing" prev_id "."
  end;
  first [ set (id := val) | fail 1 "Failed creating" id "." ];
  first [ move id before prev_id | fail 1 "Failed moving" id "below" prev_id "." ].

Ltac Case1 name := Case_aux case1 name.
Ltac Case2 name := Case_aux' case2 case1 name.
Ltac Case3 name := Case_aux' case3 case2 name.
Ltac Case4 name := Case_aux' case4 case3 name.
Ltac Case5 name := Case_aux' case5 case4 name.
Ltac Case6 name := Case_aux' case6 case5 name.
Ltac Case7 name := Case_aux' case7 case6 name.
Ltac Case8 name := Case_aux' case8 case7 name.
Ltac Case9 name := Case_aux' case9 case8 name.

Ltac Case := Case1.

Example Case_ex : forall m n, m + n = n + m.
Proof.
  induction m.
    Case1 "m = O".
      induction n.
        Case2 "n = O".
          admit.
        Case2 "n = S".
          admit.
    Case1 "m = S".
      induction n.
        Case2 "n = O".
          admit.
        Case2 "n = S".
          admit.
Abort.

(** * Solve by inversion *)
(** From SfLib.v *)

Tactic Notation "solve_by_inversion_step" tactic(t) :=
  match goal with
  | H : _ |- _ => solve [ inversion H; subst; t ]
  end
  || fail "because the goal is not solvable by inversion.".

Tactic Notation "solve" "by" "inversion" "1" :=
  solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
  solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
  solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" :=
  solve by inversion 1.

(** * Decomposing Products *)

(* Split all hypotheses in the context which don't cause additional goals. *)
Ltac splith :=
  repeat
    match goal with
    | H : _ |- _ => progress decompose [ex and prod] H; clear H
    end.

(** Like [repeat split] but more predictable as it doesn't solve easy goals and
    doesn't cause unfolding. *)
Ltac splits :=
  repeat eapply conj.

(** Like [repeat eexists] but more predictable as it doesn't solve easy goals and
    doesn't cause unfolding. *)
Ltac esplits :=
  repeat eapply ex_intro; splits.

(** * Folding & Unfolding Notations *)

(** From `https://stackoverflow.com/questions/48594507/unfold-notation-in-ltac` *)

Definition make_visible {X} (f : X) := f.

Notation "` f" := (make_visible f) (at level 5, format "` f").

Tactic Notation "unfold" "notation" constr(f) :=
  change f with (`f).
Tactic Notation "fold" "notation" constr(f) :=
  unfold make_visible.

Example a : 4 <= 5.
Proof.
  unfold notation le.
  fold notation le.
Abort.

(** * Sorting the Context *)

Ltac sort :=
  try match goal with H : ?T |- _ =>
        match type of T with Prop =>
          generalize H; clear H; try sort; intro
        end
      end.

(** * Built-in Wrappers *)
(* Some built-in tactics need to be wrapped to work in higher-order tactics. *)

Ltac destruct' E := destruct E.
Ltac induction' E := induction E.
Ltac gen_dep' x := generalize dependent x.
Ltac symmetry' := symmetry.

(** * Mapping Tactics *)

Ltac map f xs :=
  match xs with
  | (?xs, ?x) => map f xs; f x
  | ?x => f x
  end.

Ltac map_rev f xs :=
  match xs with
  | (?xs, ?x) => f x; map_rev f xs
  | ?x => f x
  end.

(** * Auxilliary Tactics *)

Ltac eapply_hyp :=
  match goal with
  | [ H : _ |- ?G ] => eapply H
  end.

Ltac on_goal t :=
  match goal with
  | [ |- ?E ] => t E
  end.

Ltac on_hyp t :=
  match goal with
  | [ H : ?E |- _ ] => t E
  end.

Ltac on_branch t E :=
  match E with
  | context [ if ?E then _ else _     ] => t E
  | context [ match ?E with _ => _ end ] => t E
  end.

Ltac on_intros f xs :=
  match xs with
  | (?xs, ?x) => intros x; map f xs; generalize dependent x
  | ?x => intros x; f; generalize dependent x
  end.

(** * Assertion *)

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "assert_neq" ident(x) constr(v) :=
  let H := fresh in
  assert (not (x = v)) as H by congruence;
  clear H.

(** * Auto Specialization *)

Ltac auto_specialize :=
  repeat (match goal with
            | H1 : _, H2 : _ |- _ => specialize H1 with H2
          end).

Ltac auto_specialize'' :=
  repeat (match goal with
            | [ H1 : _, H2 : _ |- _ ] => specialize (H1 H2)
          end).

(** Find some hypothesis to rewrite with, ensuring that [auto] proves all of the
    extra subgoals added by [rewrite]. *)
Ltac rewriteHyp :=
  match goal with
    | [ H : _ |- _ ] => rewrite H by solve [ auto ]
  end.

(** * Destruct Match & [crushed] *)

(* Destruct blocking if/match expressions in the goal. *)
Ltac destruct_match :=
  match goal with
  | [ |- context [ if ?E then _ else _     ] ] => destruct E
  | [ |- context [ match ?E with _ => _ end ] ] => destruct E
  | [ H : context [ if ?E then _ else _     ] |- _ ] => destruct E
  | [ H : context [ match ?E with _ => _ end ] |- _ ] => destruct E
  end.

Ltac destruct_match_rec E :=
  match E with
  | context [ if ?E then _ else _     ] => destruct_match_rec E
  | context [ match ?E with _ => _ end ] => destruct_match_rec E
  | ?E                                  => destruct E
  end.

Ltac destruct_match' :=
  match goal with
  | [ |- ?E ] => destruct_match_rec E
  | [ H : ?E |- _ ] => destruct_match_rec E
  end.

Ltac crushed :=
  crush;
  repeat (destruct_match; crush);
  try solve [congruence | omega].

(** * Inversion *)

Ltac inv_subst H := inversion H; subst; clear H.

(** * Generalization *)

(** [gen (x, y, z)] calls [generalized dependent] on [x], [y], and [z]. *)
Ltac gen_rev xs := map gen_dep' xs.
Ltac gen xs := map_rev gen_dep' xs.

(** * Pose Abstract *)

(** Same as [pose (x := e)], but the added hypothesis has the form
    [x : t] instead of [x := e : t]. *)
Tactic Notation "pose" "abstract" ident(x) ":=" constr(e) :=
  pose (x := e); clearbody x.

(** * Inverting simpl *)

(** "[unsimpl E]" replaces all occurence of [X] by [E], where [X] is the result
    that tactic [simpl] would give when used to evaluate [E]. *)

Tactic Notation "unsimpl" constr(E) :=
  let F := (eval simpl in E) in change F with E.

(** * Dup *)

(** Duplicating the goal for testing purposes and tutorials. *)

Require Coq.Numbers.BinNums Coq.ZArith.BinInt.

Definition ltac_int_to_nat (x:BinInt.Z) : nat :=
  match x with
  | BinInt.Z0 => 0%nat
  | BinInt.Zpos p => BinPos.nat_of_P p
  | BinInt.Zneg p => 0%nat
  end.

Ltac number_to_nat N :=
  match type of N with
  | nat => constr:(N)
  | BinInt.Z => let N' := constr:(ltac_int_to_nat N) in eval compute in N'
  end.

(** [dup N] produces [N] copies of the current goal. It is useful
    for building examples on which to illustrate behaviour of tactics.
    [dup] is short for [dup 2]. *)

Lemma dup_lemma : forall P, P -> P -> P.
Proof using. auto. Qed.

Ltac dup_tactic N :=
  match number_to_nat N with
  | 0 => idtac
  | S 0 => idtac
  | S ?N' => apply dup_lemma; [ | dup_tactic N' ]
  end.

Tactic Notation "dup" constr(N) :=
  dup_tactic N.
Tactic Notation "dup" :=
  dup 2.

(** * eqapply *)

Tactic Notation "eqapply" ident(H) :=
  match goal with
  | H' : ?P ?e1' |- ?P ?e1 =>
    assert_eq H' H;
    let E1 := fresh in
    assert (E1: e1 = e1');[eauto|
    try rewrite E1;
    eapply H]
  | H' : ?P ?e1' ?e2' |- ?P ?e1 ?e2 =>
    assert_eq H' H;
    let E1 := fresh in
    let E2 := fresh in
    assert (E1: e1 = e1');[eauto|
    assert (E2: e2 = e2');[clear E1; eauto|
    try rewrite E1;
    try rewrite E2;
    eapply H]]
  | H' : ?P ?e1' ?e2' ?e3' |- ?P ?e1 ?e2 ?e3 =>
    assert_eq H' H;
    let E1 := fresh in
    let E2 := fresh in
    let E3 := fresh in
    assert (E1: e1 = e1');[eauto|
    assert (E2: e2 = e2');[clear E1; eauto|
    assert (E3: e3 = e3');[clear E1 E2; eauto|
    try rewrite E1;
    try rewrite E2;
    try rewrite E3;
    eapply H]]]
  | H' : ?P ?e1' ?e2' ?e3' ?e4' |- ?P ?e1 ?e2 ?e3 ?e4 =>
    assert_eq H' H;
    let E1 := fresh in
    let E2 := fresh in
    let E3 := fresh in
    let E4 := fresh in
    assert (E1: e1 = e1');[eauto|
    assert (E2: e2 = e2');[clear E1; eauto|
    assert (E3: e3 = e3');[clear E1 E2; eauto|
    assert (E4: e4 = e4');[clear E1 E2 E3; eauto|
    try rewrite E1;
    try rewrite E2;
    try rewrite E3;
    try rewrite E4;
    eapply H]]]]
  | H' : ?P ?e1' ?e2' ?e3' ?e4' ?e5' |- ?P ?e1 ?e2 ?e3 ?e4 ?e5 =>
    assert_eq H' H;
    let E1 := fresh in
    let E2 := fresh in
    let E3 := fresh in
    let E4 := fresh in
    let E5 := fresh in
    assert (E1: e1 = e1');[eauto|
    assert (E2: e2 = e2');[clear E1; eauto|
    assert (E3: e3 = e3');[clear E1 E2; eauto|
    assert (E4: e4 = e4');[clear E1 E2 E3; eauto|
    assert (E5: e5 = e5');[clear E1 E2 E3 E4; eauto|
    try rewrite E1;
    try rewrite E2;
    try rewrite E3;
    try rewrite E4;
    try rewrite E5;
    eapply H]]]]]
  | H' : ?P ?e1' ?e2' ?e3' ?e4' ?e5' ?e6' |- ?P ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 =>
    assert_eq H' H;
    let E1 := fresh in
    let E2 := fresh in
    let E3 := fresh in
    let E4 := fresh in
    let E5 := fresh in
    let E6 := fresh in
    assert (E1: e1 = e1');[eauto|
    assert (E2: e2 = e2');[clear E1; eauto|
    assert (E3: e3 = e3');[clear E1 E2; eauto|
    assert (E4: e4 = e4');[clear E1 E2 E3; eauto|
    assert (E5: e5 = e5');[clear E1 E2 E3 E4; eauto|
    assert (E6: e6 = e6');[clear E1 E2 E3 E4 E5; eauto|
    try rewrite E1;
    try rewrite E2;
    try rewrite E3;
    try rewrite E4;
    try rewrite E5;
    try rewrite E6;
    eapply H]]]]]]
  | H' : ?P ?e1' ?e2' ?e3' ?e4' ?e5' ?e6' ?e7' |- ?P ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 =>
    assert_eq H' H;
    let E1 := fresh in
    let E2 := fresh in
    let E3 := fresh in
    let E4 := fresh in
    let E5 := fresh in
    let E6 := fresh in
    let E7 := fresh in
    assert (E1: e1 = e1');[eauto|
    assert (E2: e2 = e2');[clear E1; eauto|
    assert (E3: e3 = e3');[clear E1 E2; eauto|
    assert (E4: e4 = e4');[clear E1 E2 E3; eauto|
    assert (E5: e5 = e5');[clear E1 E2 E3 E4; eauto|
    assert (E6: e6 = e6');[clear E1 E2 E3 E4 E5; eauto|
    assert (E7: e7 = e7');[clear E1 E2 E3 E4 E5 E6; eauto|
    try rewrite E1;
    try rewrite E2;
    try rewrite E3;
    try rewrite E4;
    try rewrite E5;
    try rewrite E6;
    try rewrite E7;
    eapply H]]]]]]]
  end.

Tactic Notation "eqapply" :=
  match goal with
  | H : ?P |- _ => eqapply H
  end.

(* Ltac eqapply_recx P Q t := *)
(*   match P with *)
(*   | ?P ?e => *)
(*     match Q with *)
(*     | ?Q ?e' => *)
(*       let E := fresh in *)
(*       assert (E : e = e'); [eauto| *)
(*         let t := (try rewrite E; t) in *)
(*         eqapply_recx P Q t *)
(*       ] *)
(*     | ?Q => fail *)
(*     end *)
(*   | ?P => *)
(*     match Q with *)
(*     | ?Q ?e' => fail *)
(*     | ?Q => t *)
(*     end *)
(*   end. *)

(* Tactic Notation "eqapplyx" ident(H) := *)
(*   match goal with *)
(*   | H' : ?P |- ?Q => *)
(*     assert_eq H H'; *)
(*     let t := (eapply H) in *)
(*     eqapply_recx P Q t *)
(*   end. *)

(** * [invert] Tactic *)

(** [invert keep] from SF's [LibTactics.v]. *)

Inductive ltac_Mark : Type :=
  | ltac_mark : ltac_Mark.

Ltac gen_until_mark :=
  match goal with H: ?T |- _ =>
    match T with
    | ltac_Mark => clear H
    | _ => generalize H; clear H; gen_until_mark
    end
  end.

Tactic Notation "invert" hyp(H) :=
  pose ltac_mark; inversion H; gen_until_mark.

Ltac gen_subst_until_mark :=
  match goal with H: ?T |- _ =>
    match T with
    | ltac_Mark => clear H
    | ?x = ?y => first [ subst x | subst y ]; gen_subst_until_mark
    | _ => generalize H; clear H; gen_subst_until_mark
    end
  end.

Tactic Notation "inverts" hyp(H) :=
  pose ltac_mark; inversion H; gen_subst_until_mark.
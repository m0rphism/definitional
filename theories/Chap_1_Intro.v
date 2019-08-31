From Theories Require Import
  Tactics Chap_2_Framework.

(** * Specification *)

(** ** Syntax *)

Axiom String : Type.

Inductive Exp :=
| e_num (n : nat)
| e_str (s : String)
| e_add (e1 e2 : Exp).

(** ** Type System *)

Inductive Typ :=
| t_nat : Typ
| t_str : Typ.

Inductive ExpTyp : Exp -> Typ -> Prop :=
| et_num :
    forall n, ExpTyp (e_num n) t_nat
| et_str :
    forall s, ExpTyp (e_str s) t_str
| et_add :
    forall e1 e2,
    ExpTyp e1 t_nat ->
    ExpTyp e2 t_nat ->
    ExpTyp (e_add e1 e2) t_nat.

(** ** Small-Step Semantics *)

Inductive IsValue : Exp -> Prop :=
| iv_num : forall n, IsValue (e_num n)
| iv_str : forall s, IsValue (e_str s).

Inductive Step : Exp -> Exp -> Prop :=
| s_add1 :
    forall e1 e2 e1',
    Step e1 e1' ->
    Step (e_add e1 e2) (e_add e1' e2)
| s_add2 :
    forall e1 e2 e2',
    IsValue e1 ->
    Step e2 e2' ->
    Step (e_add e1 e2) (e_add e1 e2')
| s_add :
    forall n1 n2,
    Step (e_add (e_num n1) (e_num n2)) (e_num (n1 + n2)).

Inductive Multi {X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
| m_refl : forall x, Multi R x x
| m_step : forall x y z, Multi R x y -> R y z -> Multi R x z.

(** ** Big-Step Semantics *)

Inductive Val : Type :=
| v_num (n : nat)
| v_str (s : String).

Inductive BigStep : Exp -> Val -> Prop :=
| bs_add :
    forall e1 e2 n1 n2,
    BigStep e1 (v_num n1) ->
    BigStep e2 (v_num n2) ->
    BigStep (e_add e1 e2) (v_num (n1 + n2)).

(** ** Definitional Interpreter *)

Fixpoint eval (n : nat) (e : Exp) : CanTimeout (CanErr Val) :=
  match n with
  | 0 => none
  | S n =>
      match e with
      | e_num n => done (noerr (v_num n))
      | e_str s => done (noerr (v_str s))
      | e_add e1 e2 =>
          ' v_num n1 <- eval n e1;
          ' v_num n2 <- eval n e2;
          done (noerr (v_num (n1 + n2)))
      end
  end.

(** ** Type Soundness *)

Inductive ValTyp : Val -> Typ -> Prop :=
  | vt_num :
      forall n, ValTyp (v_num n) t_nat
  | vt_str :
      forall s, ValTyp (v_str s) t_str
  .

(** * Theorems *)

Hint Constructors Typ Exp Val ExpTyp ValTyp Opt List.
Hint Unfold indexr length.
Hint Resolve ex_intro.

Lemma preservation :
  forall e1 e2 t,
  ExpTyp e1 t ->
  Step e1 e2 ->
  ExpTyp e2 t.
Proof.
  intros e1 e2 t et.
  revert e2.
  dependent induction et; intros e2' st.
  Case "et_num".
    inversion st.
  Case "et_str".
    inversion st.
  Case "et_add".
    inversion st; subst.
    Case2 "s_add1". eauto.
    Case2 "s_add2". eauto.
    Case2 "s_add". eauto.
Qed.

Lemma progress :
  forall e1 t,
  ExpTyp e1 t ->
  IsValue e1 \/ exists e2, Step e1 e2.
Proof.
  intros e1 t et. induction et.
  Case "et_num".
    left. eapply iv_num.
  Case "et_str".
    left. eapply iv_str.
  Case "et_add".
    right.
    destruct IHet1 as [iv1 | [e1' s1] ].
    Case2 "iv1".
      destruct IHet2 as [iv2 | [e2' s2] ].
      Case3 "iv2".
        inversion iv1; inversion et1; subst; try solve by inversion.
        inversion iv2; inversion et2; subst; try solve by inversion.
        eexists. eapply s_add.
      Case3 "s2".
        eexists. eapply s_add2; eauto.
    Case2 "s1".
      eexists. eapply s_add1; eauto.
Qed.

Definition Diverges (e : Exp) : Prop :=
  forall e', Multi Step e e' -> exists e'', Step e' e''.

Theorem type_soundness_ss :
  forall e t,
  ExpTyp e t ->
  Diverges e \/ exists v, IsValue v /\ Multi Step e v /\ ExpTyp v t.
Proof.
Admitted.

Theorem type_soundness :
  forall n e res t,
  eval n e = done res ->
  ExpTyp e t ->
  exists v, res = noerr v /\ ValTyp v t.
Proof.
Admitted.

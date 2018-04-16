Require Import Coq.Strings.String.
Require Import Coq.FSets.FMapWeakList.
Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.omega.Omega.
Require Import Coq.FSets.FSetWeakList.
Require Import Coq.Bool.Bool.

Open Scope string_scope.

Definition atom := string.

Print DecidableType.

Module StringMiniDec.
    Definition t := string.
    Definition eq_dec := string_dec.
End StringMiniDec.

Module StringDec := Equalities.Make_UDT(StringMiniDec).
Module Gamma := FMapWeakList.Make(StringDec).

Inductive term :=
| t_var : atom -> term
| t_app : term -> term -> term
| t_abs : atom -> term -> term
| t_pair : term -> term -> term
| t_unit : term.

(** Substitute v for x in e, assuming v is a closed term. *)
Fixpoint subst_closed (e : term) (v : term) (x : atom) :=
  match e with
  | t_var x' => if string_dec x' x then v else e
  | t_app e1 e2 => t_app (subst_closed e1 v x) (subst_closed e2 v x)
  | t_abs x' t => if string_dec x' x then e else t_abs x' (subst_closed t v x)
  | t_pair e1 e2 => t_pair (subst_closed e1 v x) (subst_closed e2 v x)
  | t_unit => e
  end.

Notation "[ v ~> x ] e" := (subst_closed e v x) (at level 68).
Notation "e1 @ e2" := (t_app e1 e2) (at level 99, right associativity).

Definition id :term := t_abs "x" (t_var "x").
Definition w : term := t_abs "x" (t_var "x" @ t_var "x").
Definition ww : term := w @ w.

Eval compute in ([ id ~> "x" ] id).
Eval compute in ([ id ~> "y" ] (t_var "y")).
Eval compute in ([ id ~> "y" ] (t_var "x")).

Inductive value : term -> Prop :=
| v_abs : forall x t, value (t_abs x t)
| v_pair : forall v1 v2, value v1 -> value v2 -> value (t_pair v1 v2)
| v_unit : value t_unit.

Hint Constructors value.

Module AtomSet := FSetWeakList.Make(StringDec).

Fixpoint fvars (e : term) : AtomSet.t :=
  match e with
  | t_var x => AtomSet.singleton x
  | t_app e1 e2 => AtomSet.union (fvars e1) (fvars e2)
  | t_abs x e => AtomSet.remove x (fvars e)
  | t_pair e1 e2 => AtomSet.union (fvars e1) (fvars e2)
  | t_unit => AtomSet.empty
  end.

Inductive closed : term -> Prop :=
| c_abs : forall x t, AtomSet.Subset (fvars t) (AtomSet.singleton x) -> closed (t_abs x t)
| c_app : forall e1 e2, closed e1 -> closed e2 -> closed (e1 @ e2)
| c_pair : forall e1 e2, closed e1 -> closed e2 -> closed (t_pair e1 e2)
| c_unit : closed t_unit.

Hint Constructors closed.

Inductive step : term -> term -> Prop :=
| s_beta : forall x t v, value v -> step (t_app (t_abs x t) v) ([v ~> x] t)
| s_app1 : forall e11 e12 e2, step e11 e12 -> step (e11 @ e2) (e12 @ e2)
| s_app2 : forall x t e21 e22, step e21 e22 -> step ((t_abs x t) @ e21) ((t_abs x t) @ e22)
| s_pair1 : forall e11 e12 e2, step e11 e12 -> step (t_pair e11 e2) (t_pair e12 e2)
| s_pair2 : forall v1 e21 e22, value v1 -> step e21 e22 -> step (t_pair v1 e21) (t_pair v1 e22).

Hint Constructors step.

Lemma omega_steps : step ww ww.
Proof.
  apply s_beta.
  constructor.
Qed.

Inductive ty_name :=
| tn_unit : ty_name
| tn_top : ty_name
| tn_bottom : ty_name
| tn_pair : ty_name -> ty_name -> ty_name
| tn_arrow : ty_name -> ty_name -> ty_name.

Definition type := nat -> term -> Prop.

Class ValidType (t : type) (n : ty_name) : Type :=
  {
    contains_value : forall k v, t k v -> value v;
    closed_under_decreasing_index : forall k v j, j <= k -> t k v -> t j v;
  }.

Ltac trivial_ty_proof t := (unfold t; intros; subst; auto).

Definition ty_unit : type := fun k v => v = t_unit.
Instance ty_unit_valid : ValidType ty_unit tn_unit := {}.
Proof.
  trivial_ty_proof ty_unit.
  trivial_ty_proof ty_unit.
Defined.

Definition ty_top : type := fun k v => value v.
Instance ty_top_valid : ValidType ty_top tn_top := {}.
Proof.
  trivial_ty_proof ty_top.
  trivial_ty_proof ty_top.
Defined.

Definition ty_bottom : type := fun k _ => False.
Instance ty_bottom_valid : ValidType ty_bottom tn_bottom := {}.
Proof.
  trivial_ty_proof ty_bottom; exfalso; auto.
  trivial_ty_proof ty_bottom; exfalso; auto.
Defined.

Definition ty_pair t1 t2 : type :=
  fun k t => exists v1 v2, value v1 /\ value v2 /\ t = t_pair v1 v2 /\ forall j, j < k -> t1 j v1 /\ t2 j v2.
Instance ty_pair_valid
         t1 t2 tn1 tn2
         `{ValidType t1 tn1}
         `{ValidType t2 tn2} : ValidType (ty_pair t1 t2) (tn_pair tn1 tn2) := {}.
Proof.
  - unfold ty_pair; intros.
    destruct H1 as [v1 [v2 [Hv1 [Hv2 [Heq Ht]]]]].
    subst; constructor; auto.
  - unfold ty_pair; intros.
    destruct H2 as [v1 [v2 [Hv1 [Hv2 [Heq Ht]]]]].
    subst.
    exists v1, v2.
    split; auto.
    split; auto.
    split; auto.
    intros p Hp.
    assert (p < k) by omega.
    apply Ht; auto.
Defined.

Definition ty_arrow (t1 : type) (t2 : type) : type :=
  fun k t => exists x e, t = t_abs x e /\ (forall j v, j < k -> t1 j v -> t2 j ([v ~> x] e)).
Instance ty_arrow_valid
         t1 t2 tn1 tn2
         `{ValidType t1 tn1}
         `{ValidType t2 tn2} : ValidType (ty_arrow t1 t2) (tn_arrow tn1 tn2) := {}.
Proof.
  - unfold ty_arrow; intros.
    destruct H1 as [x [e [Heq _]]].
    subst; auto.
  - unfold ty_arrow; intros.
    destruct H2 as [x [e [Heq Ht]]].
    subst.
    exists x, e.
    split; auto.
    intros p v Hp Htv.
    assert (p < k) by omega.
    apply Ht; auto.
Qed.

Fixpoint is_value (e : term) : bool :=
  match e with
  | t_abs _ _ => true
  | t_unit => true
  | t_pair v1 v2 => is_value v1 && is_value v2
  | _ => false
  end.

Lemma is_value_iff_value : forall e, reflect (value e) (is_value e).
Proof.
  induction e.
  - apply ReflectF.
    intros contra.
    inversion contra.
  - apply ReflectF.
    intros contra.
    inversion contra.
  - apply ReflectT.
    constructor.
  - case_eq (is_value e1); case_eq (is_value e2).
    + intros He2 He1. simpl. rewrite He2, He1. apply ReflectT.
      apply reflect_iff in IHe1. apply reflect_iff in IHe2.
      apply IHe1 in He1. apply IHe2 in He2. constructor; auto.
    + intros He2 He1. simpl. rewrite He2, He1. apply ReflectF.
      intros contra. inversion contra; subst; clear contra.
      rewrite He2 in IHe2. inversion IHe2; subst; clear IHe2.
      apply H; auto.
    + intros He2 He1. simpl. rewrite He2, He1. apply ReflectF.
      intros contra. inversion contra; subst; clear contra.
      rewrite He1 in IHe1. inversion IHe1; subst; clear IHe1.
      apply H; auto.
    + intros He2 He1. simpl. rewrite He2, He1. apply ReflectF.
      intros contra. inversion contra; subst; clear contra.
      rewrite He1 in IHe1. inversion IHe1; subst; clear IHe1.
      apply H; auto.
  - simpl. apply ReflectT; auto.
Qed.

Hint Resolve is_value_iff_value.

Inductive multistep : term -> nat -> term -> Prop :=
| multistep_refl : forall e, multistep e 0 e
| multistep_step : forall e e' e'' k, step e e' -> multistep e' k e'' -> multistep e (S k) e''.

Hint Constructors multistep.

Definition irred (e : term) : Prop :=
  forall e', step e e' -> False.

Hint Unfold irred.

Definition is_t_abs (e : term) : bool :=
  match e with
  | t_abs _ _ => true
  | _ => false
  end.

Fixpoint is_normal_form (e : term) : bool :=
  match e with
  | t_var _ => true
  | t_app (t_abs x e) t =>
    (negb (is_value t)) && is_normal_form t
  (* In this branch we already know t1 is not an abstraction *)
  | t_app t1 t2 => is_normal_form t1
  | t_pair t1 t2 => if is_value t1 then is_normal_form t2 else is_normal_form t1
  | t_unit => true
  | t_abs _ _ => true
  end.

Lemma value_implies_normal_form : forall e, value e -> is_normal_form e = true.
Proof.
  intros e Hv.
  induction Hv.
  - reflexivity.
  - assert (value v1 <-> is_value v1 = true) by (apply reflect_iff; auto).
    rewrite H in Hv1.
    simpl. rewrite Hv1.
    auto.
  - reflexivity.
Qed.

Ltac contradict_value_nf :=
  match goal with
  | [ H1 : is_value ?x = true, H2 : is_normal_form ?x = false |- _ ] =>
    assert (Hvx: value x <-> is_value x = true) by (apply reflect_iff; auto);
    rewrite <- Hvx in H1;
    apply value_implies_normal_form in H1;
    rewrite H1 in H2;
    discriminate H2
  end.

Lemma not_nf_implies_step :
  forall e, is_normal_form e = false -> exists e', step e e'.
Proof.
  induction e.
  - simpl. discriminate.
  - case_eq (is_value e2);
      case_eq (is_normal_form e2);
      case_eq (is_normal_form e1);
      intros Hnf1 Hnf2 Hv2;
      simpl;
      rewrite Hnf1, Hnf2, Hv2;
      case_eq e1;
      try discriminate;
      try (intros; subst; simpl in *;
           try match goal with
                 [ H : true = false |- _ ] => discriminate H
               end;
           try match goal with
                 [ H : false = true |- _ ] => discriminate H
               end;
           try contradict_value_nf;
           repeat match goal with
                 [ H : ?x = ?x |- _ ] => clear H
                  end;
           try match goal with
                 [ IH1 : ?P -> exists e1', step ?e1 e1',
                   H1 : ?P
                   |- exists e', step (?e1 @ ?e2) e'
                 ] => apply IH1 in H1; destruct H1 as [e1' Hstep1]; exists (e1' @ e2); constructor; auto
               end;
           try match goal with
                 [ IH2 : ?P -> exists e2', step ?e2 e2',
                   H2 : ?P
                   |- exists e', step (?e1 @ ?e2) e'
                 ] => apply IH2 in H2; destruct H2 as [e2' Hstep2]; exists (e1 @ e2'); constructor; auto
               end

          ).
    + assert (Hv2' : value e2 <-> is_value e2 = true) by (apply reflect_iff; auto).
      rewrite <- Hv2' in Hv2.
      exists ([e2 ~> a] t); constructor; auto.
  - simpl. discriminate.
  - simpl. intro Hnf.
    case_eq (is_value e1); intros Hv1; rewrite Hv1 in Hnf.
    + assert (Hv1' : value e1 <-> is_value e1 = true) by (apply reflect_iff; auto).
      rewrite <- Hv1' in Hv1.
      apply IHe2 in Hnf.
      destruct Hnf as [e2' Hstep2].
      exists (t_pair e1 e2'); constructor; auto.
    + apply IHe1 in Hnf.
      destruct Hnf as [e1' Hstep1].
      exists (t_pair e1' e2); constructor; auto.
  - simpl. discriminate.
Qed.
  
Lemma step_implies_not_nf :
  forall e e', step e e' -> is_normal_form e = false.
Proof.
  intros e e' Hstep.
  induction Hstep.
  - simpl; assert (Hv: value v <-> is_value v = true) by (apply reflect_iff; auto).
    rewrite Hv in H. rewrite H. simpl. reflexivity.
  - case_eq (is_normal_form e2);
      case_eq (is_value e2);
      intros Hv2 Hnf2;
      simpl;
      rewrite IHHstep, Hv2, Hnf2;
      case_eq e11;
      try discriminate;
      try (intros; subst; simpl in *;
           try match goal with
                 [ H : true = false |- _ ] => discriminate H
               end;
           try match goal with
                 [ H : false = true |- _ ] => discriminate H
               end;
           try reflexivity;
           repeat match goal with
                 [ H : ?x = ?x |- _ ] => clear H
                  end).
  - simpl. rewrite IHHstep. Search (_ && _ = false). apply andb_false_r.
  - simpl. rewrite IHHstep.
    case_eq (is_value e11); intros Hv11; auto.
    assert (Hv11' : value e11 <-> is_value e11 = true) by (apply reflect_iff; auto).
    rewrite <- Hv11' in Hv11.
    apply value_implies_normal_form in Hv11.
    rewrite IHHstep in Hv11.
    discriminate Hv11.
  - simpl.
    case_eq (is_value v1); intros Hv1; auto.
    assert (Hv1' : value v1 <-> is_value v1 = true) by (apply reflect_iff; auto).
    rewrite Hv1' in H.
    rewrite H in Hv1.
    discriminate Hv1.
Qed.    

Lemma nf_iff_irred : forall e, reflect (irred e) (is_normal_form e).
Proof.
  intros e.
  case_eq (is_normal_form e); intros Hnf.
  - apply ReflectT.
    intros e' contra.
    apply step_implies_not_nf in contra.
    rewrite Hnf in contra.
    discriminate contra.
  - apply ReflectF.
    unfold irred; intros contra.
    apply not_nf_implies_step in Hnf.
    destruct Hnf as [e' Hstep].
    apply (contra e'); auto.
Qed.

Hint Resolve nf_iff_irred.
    
Fixpoint ty_denote (tn : ty_name) : type :=
  match tn with
  | tn_unit => ty_unit
  | tn_top => ty_top
  | tn_bottom => ty_bottom
  | tn_pair t1 t2 => ty_pair (ty_denote t1) (ty_denote t2)
  | tn_arrow t1 t2 => ty_arrow (ty_denote t1) (ty_denote t2)
  end.

Definition has_type (e : term) (k : nat) tn `{ValidType (ty_denote tn) tn} :=
  forall j e', j < k -> multistep e j e' -> irred e' -> (ty_denote tn) (k - j) e'.

Definition safe e k :=
  forall j e', j < k -> multistep e j e' -> value e' \/ exists t, step e' t.

Theorem safety e k t `{ValidType (ty_denote t) t}:
  has_type e k t -> safe e k.
Proof.
  intros Ht.
  inversion H as [Hvalue Hdec].
  unfold safe.
  intros j e' Hlt Hsteps.
  case_eq (is_normal_form e'); intros Hnfe'.
  - assert (Hirrede' : irred e' <-> is_normal_form e' = true) by (apply reflect_iff; auto).
    rewrite <- Hirrede' in Hnfe'.
    left.
    unfold has_type in Ht.
    eapply Hvalue.
    eapply Ht; eauto.
  - right.
    apply not_nf_implies_step in Hnfe'; auto.
Qed.


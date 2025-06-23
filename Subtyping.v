Require Import Syntax Notations LibTactics Tactics.
Require Import List.
Require Import Coq.Classes.RelationClasses.
Import ListNotations.

(* Qualifier ordering  *)
Inductive q_subtype : q -> q -> Prop :=
  | q_refl : forall q1,
      q1 <> Lost ->
      q_subtype q1 q1
  | q_rd : forall q1,
      q_subtype q1 Rd
  | q_bot_lost: forall q1,
      q_subtype Bot q1
where "q1 ⊑ q2" := (q_subtype q1 q2).
Global Hint Constructors q_subtype: typ.

(* Example q_subtype_refl: forall q, q <> Lost -> q ⊑ q. *)
Example lost_subtype_refl: Lost ⊑ Lost -> False.
Proof.
  intros H.
  inversion H; subst; try congruence.
Qed.

(* Subtyping for qualified types *)
Lemma q_subtype_trans: forall μ1 μ2 μ3, μ1 ⊑ μ2 -> μ2 ⊑ μ3 -> μ1 ⊑ μ3.
Proof.
  intros.
  inversion H; steps;
    inversion H0; eauto with typ lia.
Qed.
Global Hint Resolve q_subtype_trans: typ.

(* Java base type subtyping *)
Inductive base_subtype : class_table -> class_name -> class_name -> Prop :=
  | base_refl : forall (CT : class_table) (C : class_name),
      base_subtype CT C C
  | base_trans : forall (CT : class_table) (C D E : class_name),
      base_subtype CT C D ->
      base_subtype CT D E -> 
      base_subtype CT C E
  | base_extends : forall (CT : class_table) (C D : class_name) (decl : class_def),
      In decl CT ->
      cname (signature decl) = C ->
      super (signature decl) = Some D ->
      base_subtype CT C D.
Global Hint Constructors base_subtype: typ.      

(* Qualified type subtyping *)
Inductive qualified_type_subtype : class_table -> qualified_type -> qualified_type -> Prop :=
  | qtype_sub : forall CT qt1 qt2,
      q_subtype (sqtype qt1) (sqtype qt2) ->
      base_subtype CT (sctype qt1) (sctype qt2) ->
      qualified_type_subtype CT qt1 qt2
  | qtype_trans: forall CT qt1 qt2 qt3,
      qualified_type_subtype CT qt1 qt2 ->
      qualified_type_subtype CT qt2 qt3 ->
      qualified_type_subtype CT qt1 qt3
  | qtype_refl: forall CT qt,
      qualified_type_subtype CT qt qt.    

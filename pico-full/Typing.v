Require Import Syntax Subtyping ViewpointAdaptation Helpers.
Require Import String.
Require Import List.
Import ListNotations.
Require Import Arith.

(* STATIC HELPER FUNCTIONS *)

Inductive CollectFields : class_table -> class_name -> list field_def -> Prop :=
  (* Base case: class not found *)
  | CF_NotFound : forall CT C,
      find_class CT C = None ->
      CollectFields CT C []
      
  (* Base case: Object class (no superclass) *)
  | CF_Object : forall CT C def,
      find_class CT C = Some def ->
      super (signature def) = None ->
      CollectFields CT C []
      
  (* Inductive case: class with superclass *)
  | CF_Inherit : forall CT C def parent parent_fields own_fields,
      find_class CT C = Some def ->
      super (signature def) = Some parent ->
      CollectFields CT parent parent_fields ->
      own_fields = Syntax.fields (body def) ->
      CollectFields CT C (parent_fields ++ own_fields).

(* Field lookup relation *)
Inductive FieldLookup : class_table -> class_name -> var -> field_def -> Prop :=
  | FL_Found : forall CT C fields f fdef,
      CollectFields CT C fields ->
      gget fields f = Some fdef ->
      FieldLookup CT C f fdef.

(* Relational versions of your lookup functions *)
Definition sf_def_rel (CT: class_table) (C: class_name) (f: var) (fdef: field_def) : Prop :=
  FieldLookup CT C f fdef.

Definition sf_assignability_rel (CT: class_table) (C: class_name) (f: var) (a: a) : Prop :=
  exists fdef, FieldLookup CT C f fdef /\ assignability (ftype fdef) = a.

Definition sf_mutability_rel (CT: class_table) (C: class_name) (f: var) (q: q) : Prop :=
  exists fdef, FieldLookup CT C f fdef /\ mutability (ftype fdef) = q.

Definition sf_base_rel (CT: class_table) (C: class_name) (f: var) (base: class_name) : Prop :=
  exists fdef, FieldLookup CT C f fdef /\ f_base_type (ftype fdef) = base.
  
(* Key properties of relational field collection *)
Lemma collect_fields_deterministic_rel : forall CT C fields1 fields2,
  CollectFields CT C fields1 ->
  CollectFields CT C fields2 ->
  fields1 = fields2.
Proof.
  intros CT C fields1 fields2 H1 H2.
  generalize dependent fields2.
  induction H1; intros fields2 H3; inversion H3; subst.
  - (* Both not found *) reflexivity.
  - (* H1: not found, H2: object - contradiction *)
    reflexivity.
  - (* H1: not found, H2: inherit - contradiction *)
    rewrite H in H0. discriminate.
  - (* H1: object, H2: not found - contradiction *)
    reflexivity.
  - (* Both object *)
    reflexivity.
  - (* H1: object, H2: inherit - contradiction *)
    rewrite H in H1. 
    injection H1 as Heq. subst def0.
    rewrite H0 in H2. discriminate.
  - (* H1: inherit, H2: not found - contradiction *)
    rewrite H in H4. discriminate.
  - (* H1: inherit, H2: object - contradiction *)
    rewrite H in H4. injection H4 as Heq. subst def0.
    rewrite H0 in H5. discriminate.
  - (* Both inherit *)
    rewrite H in H4. injection H4 as Heq. subst def0.
    rewrite H0 in H5. injection H5 as Heq. subst parent0.
    apply IHCollectFields in H6. subst parent_fields0.
    reflexivity.
Qed.

Lemma field_lookup_deterministic_rel : forall CT C f fdef1 fdef2,
  FieldLookup CT C f fdef1 ->
  FieldLookup CT C f fdef2 ->
  fdef1 = fdef2.
Proof.
  intros CT C f fdef1 fdef2 H1 H2.
  inversion H1 as [CT1 C1 fields1 f1 fdef1' Hcf1 Hget1]. subst.
  inversion H2 as [CT2 C2 fields2 f2 fdef2' Hcf2 Hget2]. subst.
  apply (collect_fields_deterministic_rel CT C fields1 fields2) in Hcf1; auto.
  subst. rewrite Hget1 in Hget2. injection Hget2. auto.
Qed.

Lemma field_inheritance_preserves_type : forall CT C parent def f fdef,
  find_class CT C = Some def ->
  super (signature def) = Some parent ->
  FieldLookup CT parent f fdef ->
  FieldLookup CT C f fdef.
Proof.
  intros CT C parent def f fdef Hfind Hsuper Hparent_lookup.
  inversion Hparent_lookup as [CT' parent' parent_fields f' fdef' Hparent_cf Hparent_get]. subst.
  apply FL_Found with (parent_fields ++ Syntax.fields (body def)).
  - eapply CF_Inherit; eauto.
  - (* Prove gget (parent_fields ++ Syntax.fields (body def)) f = Some fdef *)
    unfold gget in *.
    rewrite nth_error_app1.
    + apply nth_error_Some. rewrite Hparent_get. discriminate.
    + exact Hparent_get.
Qed.

(* Transitive field inheritance via subtyping *)
Lemma field_inheritance_subtyping : forall CT C D f fdef,
  base_subtype CT C D ->
  FieldLookup CT D f fdef ->
  FieldLookup CT C f fdef.
Proof.
  intros CT C D f fdef Hsub Hlookup.
  induction Hsub.
  - (* Reflexivity: C = D *)
    exact Hlookup.
  - (* Transitivity: C <: E <: D *)
    apply IHHsub1.
    apply IHHsub2.
    exact Hlookup.
  - (* Direct inheritance: C extends D *)
    destruct (find_class CT C) as [def|] eqn:Hfind.
    apply (field_inheritance_preserves_type CT C D def f fdef); auto.
    unfold parent_lookup in H1.
    rewrite Hfind in H1.
    simpl in H1.
    exact H1.
    unfold parent_lookup in H1.
    rewrite Hfind in H1.
    discriminate H1.
Qed.

Lemma field_def_consistent_through_subtyping : forall CT C D f fdef1 fdef2,
  base_subtype CT C D ->
  FieldLookup CT C f fdef1 ->
  FieldLookup CT D f fdef2 ->
  fdef1 = fdef2.
Proof.
  intros CT C D f fdef1 fdef2 Hsub Hlookup1 Hlookup2.
  (* Use field inheritance: since C <: D, field f in D is also in C *)
  assert (Hlookup2_in_C : FieldLookup CT C f fdef2).
  {
    apply (field_inheritance_subtyping CT C D f fdef2); assumption.
  }
  (* Now both lookups are in C, so use determinism *)
  eapply field_lookup_deterministic_rel; eauto.
Qed.

(* Corollary for all field properties *)
Lemma sf_def_subtyping : forall CT C D f fdef,
  base_subtype CT C D ->
  sf_def_rel CT D f fdef ->
  sf_def_rel CT C f fdef.
Proof.
  intros CT C D f fdef Hsub Hlookup.
  unfold sf_def_rel in *.
  apply (field_inheritance_subtyping CT C D f fdef); auto.
Qed.

Lemma sf_def_subtyping_reverse : forall CT C D f fdef,
  base_subtype CT C D ->
  sf_def_rel CT C f fdef ->
  sf_def_rel CT D f fdef \/ ~(exists fdef', sf_def_rel CT D f fdef').
Proof.
  intros CT C D f fdef Hsub Hlookup.
  unfold sf_def_rel in *.
  (* Use classical reasoning on the existence of field in D *)
  destruct (classic (exists fdef', FieldLookup CT D f fdef')) as [Hexists | Hnotexists].
  - (* Field exists in D *)
    destruct Hexists as [fdef' Hlookup_D].
    left.
    (* Use consistency: if field exists in both C and D, they must be the same *)
    assert (Hfdef_eq : fdef = fdef').
    {
      eapply field_def_consistent_through_subtyping; eauto.
    }
    subst fdef'.
    exact Hlookup_D.
  - (* Field doesn't exist in D *)
    right.
    exact Hnotexists.
Qed.

Lemma sf_assignability_subtyping_reverse : forall CT C D f a,
  base_subtype CT C D ->
  sf_assignability_rel CT C f a ->
  sf_assignability_rel CT D f a \/ ~(exists a0, sf_assignability_rel CT D f a0).
Proof.
  intros CT C D f a Hsub Hassign_C.
  unfold sf_assignability_rel in *.
  destruct Hassign_C as [fdef [Hfield_C Hassign]].
  
  (* Use classical reasoning on field existence in D *)
  destruct (classic (exists fdef', FieldLookup CT D f fdef')) as [Hexists | Hnotexists].
  - (* Field exists in D *)
    destruct Hexists as [fdef' Hfield_D].
    left.
    (* Use field consistency to show fdef = fdef' *)
    assert (Hfdef_eq : fdef = fdef').
    {
      eapply field_def_consistent_through_subtyping; eauto.
    }
    subst fdef'.
    exists fdef.
    split; [exact Hfield_D | exact Hassign].
  - (* Field doesn't exist in D *)
    right.
    intro Hcontra.
    destruct Hcontra as [a0 [fdef' [Hfield_D' _]]].
    apply Hnotexists.
    exists fdef'.
    exact Hfield_D'.
Qed.

Lemma sf_assignability_subtyping : forall CT C D f a,
  base_subtype CT C D ->
  sf_assignability_rel CT D f a ->
  sf_assignability_rel CT C f a.
Proof.
  intros CT C D f a Hsub Hlookup.
  unfold sf_assignability_rel in *.
  destruct Hlookup as [fdef [Hfield Hassign]].
  exists fdef. split; auto.
  apply (sf_def_subtyping CT C D f fdef); auto.
Qed.

Lemma sf_mutability_subtyping : forall CT C D f q,
  base_subtype CT C D ->
  sf_mutability_rel CT D f q ->
  sf_mutability_rel CT C f q.
Proof.
  intros CT C D f q Hsub Hlookup.
  unfold sf_mutability_rel in *.
  destruct Hlookup as [fdef [Hfield Hmut]].
  exists fdef. split; auto.
  apply (sf_def_subtyping CT C D f fdef); auto.
Qed.

Lemma sf_base_subtyping : forall CT C D f base,
  base_subtype CT C D ->
  sf_base_rel CT D f base ->
  sf_base_rel CT C f base.
Proof.
  intros CT C D f base Hsub Hlookup.
  unfold sf_base_rel in *.
  destruct Hlookup as [fdef [Hfield Hbase]].
  exists fdef. split; auto.
  apply (sf_def_subtyping CT C D f fdef); auto.
Qed.

Lemma sf_assignability_deterministic_rel : forall CT C f a1 a2,
  sf_assignability_rel CT C f a1 ->
  sf_assignability_rel CT C f a2 ->
  a1 = a2.
Proof.
  intros CT C f a1 a2 H1 H2.
  unfold sf_assignability_rel in H1, H2.
  destruct H1 as [fdef1 [Hlookup1 Hassign1]].
  destruct H2 as [fdef2 [Hlookup2 Hassign2]].
  
  (* Use field lookup determinism *)
  assert (Hfdef_eq: fdef1 = fdef2).
  {
    eapply field_lookup_deterministic_rel; eauto.
  }
  subst fdef2.
  
  (* Now assignability (ftype fdef1) = a1 and assignability (ftype fdef1) = a2 *)
  rewrite -> Hassign1 in Hassign2.
  exact Hassign2.
Qed.

(* Collect fields of a class and its superclasses, with fuel to prevent infinite loops *)
(* Fixpoint collect_fields_fuel (fuel : nat) (CT : class_table) (C : class_name) : list field_def :=
  match fuel with
  | O => []
  | S fuel' =>
    match find_class CT C with
    | None => []
    | Some def =>
      let super_fields :=
        match super (signature def) with
        | Some n => collect_fields_fuel fuel' CT n
        | None => []
        end in
      super_fields ++ fields (body def)
    end
  end.

Definition collect_fields (CT : class_table) (C : class_name) : list field_def :=
collect_fields_fuel (length CT) CT C.

Definition fields := collect_fields.

Lemma collect_fields_fuel_zero : forall CT C,
  collect_fields_fuel 0 CT C = [].
Proof.
  intros CT C.
  simpl.
  reflexivity.
Qed.

Lemma collect_fields_fuel_no_class : forall fuel CT C,
  find_class CT C = None ->
  collect_fields_fuel fuel CT C = [].
Proof.
  intros fuel CT C Hno_class.
  destruct fuel as [|fuel'].
  - simpl. reflexivity.
  - simpl. rewrite Hno_class. reflexivity.
Qed.

Lemma collect_fields_fuel_structure : forall fuel' CT C def,
  find_class CT C = Some def ->
  collect_fields_fuel (S fuel') CT C = 
    (match super (signature def) with
     | Some parent => collect_fields_fuel fuel' CT parent
     | None => []
     end) ++ Syntax.fields (body def).
Proof.
  intros fuel' CT C def Hfind.
  simpl. rewrite Hfind. 
  destruct (super (signature def)) as [parent|].
  + reflexivity.
  + simpl. reflexivity.
Qed.

Lemma collect_fields_fuel_inherits_parent : forall fuel CT C def parent f fdef,
  find_class CT C = Some def ->
  super (signature def) = Some parent ->
  fuel > 0 ->
  nth_error (collect_fields_fuel fuel CT parent) f = Some fdef ->
  nth_error (collect_fields_fuel (S fuel) CT C) f = Some fdef.
Proof.
  intros fuel CT C def parent f fdef Hfind Hsuper Hfuel Hparent_field.
  simpl.
  rewrite Hfind.
  rewrite Hsuper.
  (* First prove the length bound *)
  assert (Hbound : f < length (collect_fields_fuel fuel CT parent)).
  {
    apply nth_error_Some.
    rewrite Hparent_field.
    discriminate.
  }
  rewrite nth_error_app1.
  - exact Hbound.
  - exact Hparent_field.
Qed.

(* Static field def look up; We assume identifiers are globally unique  *)
Definition sf_def (CT: class_table) (C: class_name) (f: var) : option field_def :=
  gget (fields CT C) f.

(* Static field assignablity lookup *)
Definition sf_assignability (CT: class_table) (C: class_name) (f: var) : option a :=
  match sf_def CT C f with
  | Some fd => Some (assignability (ftype fd))
  | None => None
  end.

(* Static field mutability lookup *)
Definition sf_mutability (CT: class_table) (C: class_name) (f: var) : option q_f :=
  match sf_def CT C f with
  | Some fd => Some (mutability (ftype fd))
  | None => None
  end.

(* Static field base type lookup *)
Definition sf_base (CT: class_table) (C: class_name) (f: var) : option class_name :=
  match sf_def CT C f with
  | Some fd => Some (f_base_type (ftype fd))
  | None => None
  end.

Lemma field_lookup_deterministic : forall CT C f fdef fdef',
  sf_def CT C f = Some fdef ->
  sf_def CT C f = Some fdef' ->
  fdef = fdef'.
Proof.
  intros CT C f fdef fdef' H1 H2.
  unfold sf_def in *.
  rewrite H1 in H2.
  injection H2.
  auto.
Qed.

(* Fields collection is deterministic *)
Lemma collect_fields_deterministic : forall CT C fds fds',
  collect_fields CT C = fds ->
  collect_fields CT C = fds' ->
  fds = fds'.
Proof.
  intros CT C fds fds' H1 H2.
  rewrite H1 in H2.
  exact H2.
Qed.  *)

(* Look up the constructor for a class *)
Definition constructor_def_lookup (CT : class_table) (C : class_name) : option constructor_def :=
  match find_class CT C with
  | Some def => Some (constructor (body def))
  | None => None
  end.

(* Look up the constructor signature for a class *)
Definition constructor_sig_lookup (CT : class_table) (C : class_name) : option constructor_sig :=
  match constructor_def_lookup CT C with
  | Some ctor => Some (csignature ctor)
  | None => None
  end.

Lemma constructor_def_lookup_dom : forall CT C ctor,
  constructor_def_lookup CT C = Some ctor ->
  C < dom CT.
Proof.
  intros CT C ctor H.
  unfold constructor_def_lookup in H.
  destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
  apply find_class_dom in Hfind.
  exact Hfind.
Qed.

Lemma constructor_sig_lookup_dom : forall CT C csig,
  constructor_sig_lookup CT C = Some csig ->
  C < dom CT.
Proof.
  intros CT C csig H.
  unfold constructor_sig_lookup in H.
  destruct (constructor_def_lookup CT C) as [ctor|] eqn:Hctor; [|discriminate].
  apply constructor_def_lookup_dom in Hctor.
  exact Hctor.
Qed.

Lemma constructor_sig_lookup_implies_def : forall CT C csig,
  constructor_sig_lookup CT C = Some csig ->
  exists cdef, constructor_def_lookup CT C = Some cdef /\ csignature cdef = csig.
Proof.
  intros CT C csig H.
  unfold constructor_sig_lookup in H.
  destruct (constructor_def_lookup CT C) as [ctor|] eqn:Hctor; [|discriminate].
  exists ctor.
  split.
  - reflexivity.
  - injection H as H. exact H.
Qed.

Lemma constructor_def_lookup_Some : forall CT C,
  C < dom CT ->
  exists ctor, constructor_def_lookup CT C = Some ctor.
Proof.
  intros CT C H.
  apply find_class_Some in H.
  destruct H as [def Hdef].
  unfold constructor_def_lookup.
  rewrite Hdef.
  eexists. reflexivity.
Qed.

Lemma constructor_sig_lookup_Some : forall CT C,
  C < dom CT ->
  exists csig, constructor_sig_lookup CT C = Some csig.
Proof.
  intros CT C H.
  apply constructor_def_lookup_Some in H.
  destruct H as [ctor Hctor].
  unfold constructor_sig_lookup.
  rewrite Hctor.
  eexists. reflexivity.
Qed.  

(* Helper to compare class names *)
Definition eq_class_name (c1 c2 : class_name) : bool :=
  match c1, c2 with
  | n1, n2 => Nat.eqb n1 n2
  end.

(* Helper to compare method names *)
Definition eq_method_name (m1 m2 : method_name) : bool :=
  match m1, m2 with
  | n1, n2 => Nat.eqb n1 n2
  end.

Definition gget_method (methods : list method_def) (m : method_name) : option method_def :=
  find (fun mdef => eq_method_name (mname (msignature mdef)) m) methods.

Definition override (parent_methods own_methods : list method_def) : list method_def :=
  own_methods ++ filter (fun pmdef => 
    negb (existsb (fun omdef => 
      eq_method_name (mname (msignature pmdef)) (mname (msignature omdef))) 
    own_methods)) parent_methods.

Inductive CollectMethods : class_table -> class_name -> list method_def -> Prop :=
  (* Class not found *)
  | CM_NotFound : forall CT C,
      find_class CT C = None ->
      CollectMethods CT C []
  (* Object class: no superclass *)
  | CM_Object : forall CT C def,
      find_class CT C = Some def ->
      super (signature def) = None ->
      C < dom CT ->
      CollectMethods CT C (methods (body def))
  (* Class with superclass *)
  | CM_Inherit : forall CT C def parent parent_methods own_methods merged,
      find_class CT C = Some def ->
      super (signature def) = Some parent ->
      C < dom CT ->
      parent < dom CT ->
      cname (signature def) > parent ->
      CollectMethods CT parent parent_methods ->
      own_methods = methods (body def) ->
      (* overriding resolution: own_methods shadow parent_methods *)
      merged = override parent_methods own_methods ->
      CollectMethods CT C merged.
 
Lemma collect_methods_deterministic : forall CT C methods1 methods2,
  CollectMethods CT C methods1 ->
  CollectMethods CT C methods2 ->
  methods1 = methods2.
Proof.
  intros CT C methods1 methods2 H1 H2.
  generalize dependent methods2.
  induction H1; intros.
  inversion H2; subst.
  - (* Both CM_NotFound *)
    reflexivity.
  - (* CM_NotFound vs CM_Object - contradiction *)
    rewrite H in H0. discriminate.
  - (* CM_NotFound vs CM_Inherit - contradiction *)
    rewrite H in H0. discriminate.
  - (* CM_Object vs CM_NotFound - contradiction *)
    inversion H2; subst.
    -- (* CM_NotFound case *)
      rewrite H in H3.
      discriminate.
    -- (* CM_Object case *)
      rewrite H in H3.
      injection H3 as Heq.
      subst def0.
      reflexivity.
    -- (* CM_Inherit case *)
      rewrite H in H3.
      injection H3 as Heq.
      subst def0.
      rewrite H0 in H4.
      discriminate.
  - inversion H7; subst.
    -- (* CM_NotFound case *)
      rewrite H in H8.
      discriminate.
    -- (* CM_Object case *)
      rewrite H in H8.
      injection H8 as Heq.
      subst def0.
      rewrite H0 in H9.
      discriminate.
    -- (* CM_Inherit case *)
      rewrite H in H8.
      injection H8 as Heq.
      subst def0.
      rewrite H0 in H9.
      injection H9 as Heq.
      subst parent0.
      assert (parent_methods = parent_methods0) by (apply IHCollectMethods; exact H13).
      subst parent_methods0.
      reflexivity.
Qed.

(* Inductive MethodLookup : class_table -> class_name -> method_name -> method_def -> Prop :=
  | ML_Found : forall CT C methods m mdef,
      CollectMethods CT C methods ->
      gget_method methods m = Some mdef ->
      MethodLookup CT C m mdef.

Lemma method_lookup_deterministic : forall CT C m mdef1 mdef2,
  MethodLookup CT C m mdef1 ->
  MethodLookup CT C m mdef2 ->
  mdef1 = mdef2.
Proof.
  intros CT C m mdef1 mdef2 H1 H2.
  inversion H1; subst.
  inversion H2; subst.
  (* Both use CollectMethods CT C methods *)
  assert (methods0 = methods).
  {
    eapply collect_methods_deterministic; eauto.
  }
  subst methods0.
  rewrite H0 in H4.
  injection H4 as Heq.
  exact Heq.
Qed.

Inductive MethodParametersBaseTypeLookup : class_table -> class_name -> method_name -> list class_name -> Prop :=
  | ML_Params_Found : forall CT C methods m mdef mparamslist,
      CollectMethods CT C methods ->
      gget_method methods m = Some mdef ->
      mparamslist = map sctype (mparams (msignature mdef)) ->
      MethodParametersBaseTypeLookup CT C m mparamslist
.

Lemma method_parameters_base_type_lookup_deterministic : forall CT C m mparamslist1 mparamslist2,
  MethodParametersBaseTypeLookup CT C m mparamslist1 ->
  MethodParametersBaseTypeLookup CT C m mparamslist2 ->
  mparamslist1 = mparamslist2.
Proof.
  intros CT C m mparamslist1 mparamslist2 H1 H2.
  inversion H1; subst.
  inversion H2; subst.
  (* Both use CollectMethods CT C methods *)
  assert (methods0 = methods).
  {
    eapply collect_methods_deterministic; eauto.
  }
  subst methods0.
  rewrite H0 in H4.
  injection H4 as Heq.
  subst mdef0.
  reflexivity.
Qed.

Inductive MethodReceiverBaseTypeLookup : class_table -> class_name -> method_name -> class_name -> Prop :=
  | ML_Receiver_Found : forall CT C methods m mdef receivertype,
      CollectMethods CT C methods ->
      gget_method methods m = Some mdef ->
      receivertype = sctype (mreceiver (msignature mdef)) ->
      MethodReceiverBaseTypeLookup CT C m receivertype
.

Inductive MethodReturnBaseTypeLookup : class_table -> class_name -> method_name -> class_name -> Prop :=
  | ML_Return_Found : forall CT C methods m mdef returntype,
      CollectMethods CT C methods ->
      gget_method methods m = Some mdef ->
      returntype = sctype (mret (msignature mdef)) ->
      MethodReturnBaseTypeLookup CT C m returntype
.

Lemma method_receiver_base_type_lookup_deterministic : forall CT C m receivertype1 receivertype2,
  MethodReceiverBaseTypeLookup CT C m receivertype1 ->
  MethodReceiverBaseTypeLookup CT C m receivertype2 ->
  receivertype1 = receivertype2.
Proof.
  intros CT C m receivertype1 receivertype2 H1 H2.
  inversion H1; subst.
  inversion H2; subst.
  assert (methods0 = methods).
  {
    eapply collect_methods_deterministic; eauto.
  }
  subst methods0.
  rewrite H0 in H4.
  injection H4 as Heq.
  subst mdef0.
  reflexivity.
Qed.

Lemma method_return_base_type_lookup_deterministic : forall CT C m returntype1 returntype2,
  MethodReturnBaseTypeLookup CT C m returntype1 ->
  MethodReturnBaseTypeLookup CT C m returntype2 ->
  returntype1 = returntype2.
Proof.
  intros CT C m returntype1 returntype2 H1 H2.
  inversion H1; subst.
  inversion H2; subst.
  assert (methods0 = methods).
  {
    eapply collect_methods_deterministic; eauto.
  }
  subst methods0.
  rewrite H0 in H4.
  injection H4 as Heq.
  subst mdef0.
  reflexivity.
Qed.

Lemma method_params_base_type_length : forall CT C m param_types mdef,
  MethodLookup CT C m mdef ->
  MethodParametersBaseTypeLookup CT C m param_types ->
  length param_types = length (mparams (msignature mdef)).
Proof.
  intros CT C m param_types mdef Hlookup Hbase_lookup.
  inversion Hbase_lookup; subst.
  (* We have MethodLookup CT C m mdef and gget_method methods m = Some mdef0 *)
  (* First establish that mdef = mdef0 *)
  assert (Hlookup_mdef0 : MethodLookup CT C m mdef0).
  {
    econstructor; eauto.
  }
  assert (Heq : mdef = mdef0).
  {
    eapply method_lookup_deterministic; eauto.
  }
  subst mdef0.
  (* Now param_types = map sctype (mparams (msignature mdef)) *)
  rewrite length_map.
  reflexivity.
Qed. *)

(* STATIC WELLFORMEDNESS CONDITION *)
(* Well-formedness of type use *)
Definition wf_stypeuse (CT : class_table) (q1: q) (c: class_name) : Prop :=
  match bound CT c with
  | Some q_c_val => q_subtype (vpa_mutabilty q1 q_c_val) q1 /\ 
                   c < dom CT
  | None => False (* or False, depending on your semantics *)
  end.

(* Well-formedness of field *)
Definition wf_field (CT : class_table) (fdef: field_def) : Prop :=
  is_q_f (mutability (ftype fdef)) /\
  wf_stypeuse CT (mutability (ftype fdef)) (f_base_type (ftype fdef)).

(* Well-formedness of static environment *)
Definition wf_senv (CT : class_table) (sΓ : s_env) : Prop :=
  (* The first variable is the receiver and should always be present *)
  dom sΓ > 0 /\
  Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) sΓ.

Lemma senv_var_domain : forall CT sΓ i T,
  wf_senv CT sΓ ->
  nth_error sΓ i = Some T ->
  sctype T < dom CT.
Proof.
  intros CT sΓ i T Hwf_senv Hnth.
  unfold wf_senv in Hwf_senv.
  destruct Hwf_senv as [_ Hforall_wf].
  assert (Hi_bound : i < dom sΓ).
  {
    apply nth_error_Some. rewrite Hnth. discriminate.
  }
  eapply Forall_nth_error in Hforall_wf; eauto.
  unfold wf_stypeuse in Hforall_wf.
  destruct (bound CT (sctype T)) as [qc|] eqn:Hbound.
  - destruct Hforall_wf as [_ Hdom]. exact Hdom.
  - contradiction Hforall_wf.
Qed.

Inductive FindMethodWithName : class_table -> class_name -> method_name -> method_def -> Prop :=
  (* Case 1: method is defined directly in class *)
  | FOM_Here : forall CT C def own_methods m mdef,
      find_class CT C = Some def ->
      own_methods = methods (body def) ->
      gget_method own_methods m = Some mdef ->
      FindMethodWithName CT C m mdef

  (* Case 2: method not in class, look in superclass *)
  | FOM_Super : forall CT C def parent m mdef own_methods,
      find_class CT C = Some def ->
      own_methods = methods (body def) ->
      gget_method own_methods m = None ->
      super (signature def) = Some parent ->
      FindMethodWithName CT parent m mdef ->
      FindMethodWithName CT C m mdef.

Lemma gget_method_name_consistent : forall methods m mdef,
  gget_method methods m = Some mdef ->
  mname (msignature mdef) = m.
Proof.
  intros methods m mdef H.
  unfold gget_method in H.
  apply find_some in H.
  destruct H as [_ Heq_name].
  unfold eq_method_name in Heq_name.
  apply Nat.eqb_eq in Heq_name.
  exact Heq_name.
Qed.

Lemma find_method_with_name_consistent : forall CT C m mdef,
  FindMethodWithName CT C m mdef ->
  mname (msignature mdef) = m.
Proof.
  intros CT C m mdef H.
  induction H.
  - (* FOM_Here *)
    eapply gget_method_name_consistent; eauto.
  - (* FOM_Super *)
    exact IHFindMethodWithName.
Qed.

(* EXPRESSION TYPING RULES *)
Inductive expr_has_type : class_table -> s_env -> expr -> qualified_type -> Prop :=

  (* Null typing *)
  | ET_Null : forall CT Γ q class_name,
      q = Rd -> (* did not define the bottom type of Java base type *)
      wf_senv CT Γ ->
      class_name < dom CT -> (* Add this constraint *)
      expr_has_type CT Γ ENull (Build_qualified_type q class_name)

  (* Variable typing *)
  | ET_Var : forall CT Γ x T,
      wf_senv CT Γ ->
      static_getType Γ x = Some T ->
      expr_has_type CT Γ (EVar x) T
      
  (* Field access typing *)    
  | ET_Field : forall CT Γ x T fDef f,
      wf_senv CT Γ ->
      static_getType Γ x = Some T ->
      sf_def_rel CT (sctype T) f fDef ->
      expr_has_type CT Γ (EField x f) (vpa_type_to_type T (Build_qualified_type (mutability (ftype fDef)) (f_base_type (ftype fDef))))
.

Inductive stmt_typing : class_table -> s_env -> stmt -> s_env -> Prop :=
  (* Skip statement *)
  | ST_Skip : forall CT sΓ,
      wf_senv CT sΓ ->
      stmt_typing CT sΓ SSkip sΓ

  (* Local variable declaration *)
  | ST_Local : forall CT sΓ T x sΓ',
      wf_senv CT sΓ ->
      wf_stypeuse CT (sqtype T) (sctype T) ->
      static_getType sΓ x = None ->
      sΓ' = (sΓ ++ [T]) ->
      (* The local variable is added to the static environment *)
      stmt_typing CT sΓ (SLocal T x) sΓ'

  (* Variable assignment *)
  | ST_VarAss : forall CT sΓ x e Te Tx,
      wf_senv CT sΓ ->
      expr_has_type CT sΓ e Te ->
      x <> 0 -> (* x is not the receiver variable *)
      static_getType sΓ x = Some Tx -> (* rename the varaibles to be more clear*)
      qualified_type_subtype CT Te Tx ->
      stmt_typing CT sΓ (SVarAss x e) sΓ

  (* Field write *)
  | ST_FldWrite : forall CT sΓ x f y Tx Ty fieldT a,
      wf_senv CT sΓ ->
      static_getType sΓ x = Some Tx ->
      static_getType sΓ y = Some Ty ->
      sf_def_rel CT (sctype Tx) f fieldT ->
      sf_assignability_rel CT (sctype Tx) f a ->
      (* TODO: define a helper method to get the adapated type *)
      qualified_type_subtype CT Ty (vpa_qualified_type (sqtype Tx) (Build_qualified_type (mutability (ftype fieldT)) (f_base_type (ftype fieldT)))) ->
      vpa_assignability (sqtype Tx) a = Assignable ->
      stmt_typing CT sΓ (SFldWrite x f y) sΓ

  (* Object creation *)
  | S_New : forall CT sΓ x Tx (qc:q) C args argtypes n1 consig consreturn,
      wf_senv CT sΓ ->
      static_getType sΓ x = Some Tx ->
      static_getType_list sΓ args = Some argtypes ->
      constructor_sig_lookup CT C = Some consig ->
      x <> 0 ->
      length consig.(sparams) = n1 ->
      consig.(cqualifier) = consreturn ->
      is_q_c qc ->
      vpa_mutabilty qc consreturn = qc ->
      Forall2 (fun arg T => qualified_type_subtype CT arg (vpa_qualified_type qc T)) (firstn n1 argtypes) consig.(sparams) ->
      Forall2 (fun arg T => qualified_type_subtype CT arg (vpa_qualified_type qc T)) (skipn n1 argtypes) consig.(cparams) ->
      qualified_type_subtype CT (Build_qualified_type qc C) Tx ->
      stmt_typing CT sΓ (SNew x qc C args) sΓ

  (* Method call *)
  | ST_Call : forall CT sΓ x m y args argtypes Tx Ty mdef,
                    (* sΓ0 sΓ1 mbody *)
      wf_senv CT sΓ ->
      static_getType sΓ x = Some Tx ->
      static_getType sΓ y = Some Ty ->
      static_getType_list sΓ args = Some argtypes ->
      FindMethodWithName CT (sctype Ty) m mdef ->
      x <> 0 -> (* x is not the receiver variable *)
      qualified_type_subtype CT (vpa_qualified_type (sqtype Ty) (mret (msignature mdef))) Tx -> (* assignment subtype checking*)
      qualified_type_subtype CT Ty (vpa_qualified_type (sqtype Ty) (mreceiver (msignature mdef))) -> (* receiver subtype checking *) 
      Forall2 (fun arg T => qualified_type_subtype CT arg (vpa_qualified_type (sqtype Ty) T)) argtypes (mparams (msignature mdef)) -> (* argument subtype checking *)
      stmt_typing CT sΓ (SCall x m y args) sΓ

  (* Cast statement *)
  (* | S_Cast : forall CT Γ x q C y,
      static_lookup Γ y = Some (ctype (Build_qualified_type (q_f_proj q) C)) ->
      wf_stypeuse CT q C ->
      stmt_eval CT Γ (SCast x q C y) Γ *)

  (* Sequence of statements *)
  | ST_Seq : forall CT sΓ s1 sΓ' s2 sΓ'',
      wf_senv CT sΓ ->
      stmt_typing CT sΓ s1 sΓ' ->
      stmt_typing CT sΓ' s2 sΓ'' ->
      stmt_typing CT sΓ (SSeq s1 s2) sΓ''
.

Lemma stmt_typing_wf_env : forall CT sΓ stmt sΓ',
  stmt_typing CT sΓ stmt sΓ' ->
  wf_senv CT sΓ.
Proof.
  intros CT sΓ stmt sΓ' Htyping.
  induction Htyping; auto.
Qed.

Lemma new_stmt_args_length : forall CT sΓ x qc C args argtypes n1 consig,
  stmt_typing CT sΓ (SNew x qc C args) sΓ ->
  static_getType_list sΓ args = Some argtypes ->
  constructor_sig_lookup CT C = Some consig ->
  length consig.(sparams) = n1 ->
  length consig.(sparams) + length consig.(cparams) = length args.
Proof.
  intros CT sΓ x qc C args argtypes n1 consig Htyping Hstatic Hconsig Hn1.
  inversion Htyping; subst.
  (* Extract the Forall2 hypotheses *)
  apply Forall2_length in H15. (* firstn n1 argtypes ~ sparams *)
  apply Forall2_length in H16. (* skipn n1 argtypes ~ cparams *)
  rewrite Hconsig in H6.
  injection H6 as Hconsig_eq.
  subst consig0.
  (* Similarly for argtypes *)
  rewrite Hstatic in H5.
  injection H5 as Hargtypes_eq.
  subst argtypes0.
  (* Now use the length properties from Forall2 *)
  assert (Hfirstn_skipn : dom (firstn dom (sparams consig) argtypes) + dom (skipn dom (sparams consig) argtypes) = dom argtypes).
  {
    rewrite length_firstn.
    rewrite length_skipn.
    lia.
  }
  rewrite H16 in Hfirstn_skipn.
  rewrite H15 in Hfirstn_skipn.
  (* Connect argtypes length with args length *)
  assert (Hargs_argtypes : dom argtypes = dom args).
  {
    apply (static_getType_list_preserves_length sΓ args argtypes).
    exact Hstatic.  
  }
  rewrite -> Hargs_argtypes in Hfirstn_skipn.
  exact Hfirstn_skipn.
Qed.

Inductive wf_constructor : class_table -> class_name -> constructor_def -> Prop :=
  | WFConstructorObject: forall CT C ctor,
    parent_lookup CT C = None ->
    constructor_def_lookup CT C = Some ctor ->
    let sig := csignature ctor in
    let q_c := cqualifier sig in
    (* constructor mutability qualifier is same as bound *)
    Some q_c = bound CT C -> 
    (* Object constructor has no parameters *)
    sparams sig = [] ->
    cparams sig = [] ->
    (* Object class has no fields *)
    CollectFields CT C [] ->
    (* No assignments needed *)
    assignments (cbody ctor) = [] ->
    wf_constructor CT C ctor

  (* Other case: super class and this class both have fields *)
  | WFConstructorInductive: forall CT C ctor superclass_name super_fields_def this_fields_def super_bound supercons_sig,
    parent_lookup CT C = Some superclass_name ->
    constructor_def_lookup CT C = Some ctor ->
    let sig := csignature ctor in
    let q_c := cqualifier sig in
    (* let ccon := ctor_type sig in *)
    (* constructor mutability qualifier is same as bound; Constructor name is the same as class name *)
    Some q_c = bound CT C -> 
    (* Parameter types are wellformed *)
    Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) (sparams sig) ->
    Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) (cparams sig) ->
    CollectFields CT superclass_name super_fields_def -> (* This class has fields *)
    CollectFields CT C this_fields_def -> (* This class has fields *)
    let body := cbody ctor in
    let list_assignment := assignments body in
    let this_fields := map fname this_fields_def in
    let super_fields := map fname super_fields_def in
    (* Constructor body well-formedness *)
    (* 1. The assignments in this constructor has the same length as fields for this class *)
    length list_assignment = length this_fields_def - length super_fields_def ->
    (* 2. The first component (field def) in list_assignment is in this_fields - super_fields *)
    Forall (fun '(f, _) => In f this_fields /\ ~ In f super_fields) list_assignment ->
    (* 3. Assignment preserve subtyping *)
    let ctypes := cparams sig in 
    Forall (fun '(f1, f2) =>
    exists mf Cf T2,
      sf_mutability_rel CT C f1 mf /\
      sf_base_rel CT C f1 Cf /\
      nth_error ctypes f2 = Some T2 /\
      qualified_type_subtype CT 
        (vpa_qualified_type q_c (Build_qualified_type mf Cf)) 
        (vpa_qualified_type q_c T2)
    ) list_assignment ->
    (* 4 Constructor supercall wellformed *)
    (* 4.1 Bound compatibility *)
    bound CT superclass_name = Some super_bound ->
    let stypes := sparams sig in
    vpa_mutabilty q_c super_bound = q_c /\
    (* 4.2 Argument types are adapted subtype of Parameter type of super constructor *)
    constructor_sig_lookup CT superclass_name = Some supercons_sig -> 
    let super_full_params := sparams supercons_sig ++ cparams supercons_sig in 
    length super_full_params = length stypes ->
    length (sparams sig) + length (cparams sig) = length this_fields_def ->
    Forall2 (fun arg T => qualified_type_subtype CT arg (vpa_qualified_type q_c T)) stypes super_full_params ->
    wf_constructor CT C ctor
  .

Inductive wf_method : class_table -> class_name -> method_def -> Prop :=
  | WFMethod: forall CT C mdef mbodyrettype,
    let msig := msignature mdef in
    let methodbody := mbody mdef in
    let mbodystmt := mbody_stmt methodbody in
    let sΓ := msig.(mreceiver) :: msig.(mparams) in
    (* Basic method body well-formedness *)
    (exists sΓ', 
      stmt_typing CT sΓ mbodystmt sΓ' /\
      let mbodyretvar := mreturn methodbody in
      mbodyretvar < dom sΓ' /\
      nth_error sΓ' mbodyretvar = Some mbodyrettype /\
      qualified_type_subtype CT mbodyrettype (mret msig)) ->
    (* Overriding constraints *)
    (forall D supermdef,
      base_subtype CT C D ->
      FindMethodWithName CT C (mname msig) mdef ->
      FindMethodWithName CT D (mname msig) supermdef ->
      mdef = supermdef \/
      (let supermsig := msignature supermdef in 
       Forall2 (fun T1 T2 => qualified_type_subtype CT (vpa_qualified_type (sqtype (mreceiver msig)) T1) T2) (mparams supermsig) (mparams msig) /\
       qualified_type_subtype CT (vpa_qualified_type (sqtype (mreceiver msig)) (mreceiver supermsig)) (mreceiver msig) /\
       qualified_type_subtype CT (mret msig) (vpa_qualified_type (sqtype (mreceiver msig)) (mret supermsig)))) ->
    wf_method CT C mdef.

(* Well-formedness of class *)
Inductive wf_class : class_table -> class_def -> Prop :=

(* Object class *)
| WFObjectDef: forall CT cdef class_name,
  cdef.(signature).(super) = None ->
  (cdef.(signature).(class_qualifier)) = RDM ->
  cdef.(body).(Syntax.fields) = [] ->
  cdef.(body).(methods) = [] ->
  cdef.(signature).(cname) = class_name ->
  wf_constructor CT class_name cdef.(body).(constructor) ->
  Forall (wf_field CT) (cdef.(body).(Syntax.fields)) -> 
  NoDup (map (fun mdef => mname (msignature mdef)) (cdef.(body).(methods))) ->
  wf_class CT cdef

(* Other object *) 
| WFOtherDef: forall CT cdef superC thisC, 
  is_q_c (class_qualifier (signature cdef)) ->
  cdef.(signature).(super) = Some superC -> (* Not Object class *)
  cdef.(signature).(cname) = thisC ->
  thisC > superC -> (* index of current class must be greater than super class *)
  let sig := cdef.(signature) in
  let bod := cdef.(body) in
  let C := cname sig in
  let qC := class_qualifier sig in
  (wf_constructor CT C (constructor bod) /\
  Forall (wf_method CT C) (methods bod) /\
  NoDup (map (fun mdef => mname (msignature mdef)) (methods bod)) /\
  match bound CT superC with
  | Some q_super => 
      exists fs, CollectFields CT C fs /\
      vpa_mutabilty qC q_super = qC /\ 
      Forall (wf_field CT) fs
  | None => 
      CollectFields CT C []
  end) ->
  wf_class CT cdef
.

(* Enhanced class table well-formedness *)
Definition wf_class_table (CT : class_table) : Prop :=
  Forall (wf_class CT) CT /\
  (* Object class must be at index 0 *)
  (exists obj_def, find_class CT 0 = Some obj_def /\ 
                   super (signature obj_def) = None) /\
  (* All non-Object classes must extend Object *)
  (forall i def, i > 0 -> find_class CT i = Some def -> 
                 super (signature def) <> None) /\
  (* Class name matches index *)
  (forall i def, find_class CT i = Some def <-> 
                 cname (signature def) = i).

Lemma find_class_cname_consistent : forall CT i def,
  wf_class_table CT ->
  find_class CT i = Some def ->
  cname (signature def) = i.
Proof.
  intros CT i def Hwf_ct Hfind.
  unfold wf_class_table in Hwf_ct.
  destruct Hwf_ct as [_ [_ [_ Hcname_consistent]]].
  apply Hcname_consistent; exact Hfind.
Qed.

Lemma find_class_consistent : forall CT i def def',
  wf_class_table CT ->
  find_class CT i = Some def ->
  find_class CT i = Some def' ->
  def = def'.
Proof.
  intros CT i def def' Hwf_ct Hfind Hfind'.
  rewrite Hfind in Hfind'.
  injection Hfind' as Heq.
  exact Heq.
Qed.

Lemma sf_def_rel_wf_field : forall CT C f fdef,
  wf_class_table CT ->
  sf_def_rel CT C f fdef ->
  wf_field CT fdef.
Proof.
  intros CT C f fdef Hwf_ct Hsf_def.
  unfold sf_def_rel in Hsf_def.
  inversion Hsf_def as [CT' C' fields f' fdef' Hcf Hget]. subst.
  generalize dependent fdef.
  induction Hcf; intros fdef Hget.
  - (* CF_NotFound case *)
    intros Hgget.
    inversion Hget as [CT' C' fields f' fdef' Hcf Hget']. subst.
    assert (Hfields_empty : fields = []).
    {
      eapply collect_fields_deterministic_rel; eauto.
      apply CF_NotFound. exact H.
    }
    subst fields.
    unfold gget in Hget'.
    simpl in Hget'.
    exfalso.
    simpl in Hget'.
    destruct f; discriminate Hget'.
  - (* CF_Object case *)
    intros Hgget.
    unfold gget in Hgget.
    simpl in Hgget.
    destruct f; discriminate Hgget.
  - (* CF_Inherit case *)
    intros Hgget.
    unfold gget in Hgget.
    rewrite nth_error_app in Hgget.
    destruct (lt_dec f (length parent_fields)) as [Hlt | Hge].
    + (* Field is from parent class *)
      apply IHHcf; auto.
      apply FL_Found with parent_fields; auto.
      unfold gget.
      destruct (f <? dom parent_fields) eqn:Hcmp.
      -- exact Hgget.
      -- exfalso. 
        apply Nat.ltb_nlt in Hcmp.
    lia.
      --
      unfold gget.
    assert (Hcmp : f <? dom parent_fields = true).
    {
      apply Nat.ltb_lt.
      exact Hlt.
    }
    rewrite Hcmp in Hgget.
    exact Hgget.
    + (* Field is from own class *)
    assert (Hown_field : nth_error own_fields (f - dom parent_fields) = Some fdef).
    {
      assert (Hcmp : f <? dom parent_fields = false).
      {
        apply Nat.ltb_nlt.
        exact Hge.
      }
      rewrite Hcmp in Hgget.
      exact Hgget.
    }
    assert (HWFC : wf_class CT def).
    {
      unfold wf_class_table in Hwf_ct.
      destruct Hwf_ct as [wf _].
      eapply Forall_nth_error; eauto.
    }
    inversion HWFC; subst.
  rewrite H4 in Hown_field.
  simpl in Hown_field.
  destruct (f - dom parent_fields) as [|ntest]; simpl in Hown_field; discriminate Hown_field.
  destruct H6 as [Hwf_ctor [Hwf_methods Hbound_case]].
  destruct (bound CT superC) as [q_super|] eqn:Hbound.
  ++ (* Some q_super case *)
    destruct Hbound_case as [mnameunique [fs [Hcf_fs [Hvpa Hwf_fs]]]].
    assert (Hfields_eq : fs = parent_fields ++ fields (body def)).
    {
      eapply collect_fields_deterministic_rel; eauto.
      apply CF_Inherit with (def := def) (parent := parent); eauto.
      assert (HC_eq : C = C0).
      {
        unfold C0, sig.
        symmetry.
        eapply find_class_cname_consistent; eauto.
      }
      rewrite <- HC_eq.
      exact H.
    }
    subst fs.
    apply Forall_app in Hwf_fs.
    destruct Hwf_fs as [_ Hwf_own].
    eapply Forall_nth_error; eauto.
  ++ (* None case *)
    exfalso.
    destruct Hbound_case as [Hnodup Hcf_empty].
    assert (Hfields_eq : [] = parent_fields ++ fields (body def)).
    {
      eapply collect_fields_deterministic_rel; eauto.
      apply CF_Inherit with (def := def) (parent := parent); eauto.
            assert (HC_eq : C = C0).
      {
        unfold C0, sig.
        symmetry.
        eapply find_class_cname_consistent; eauto.
      }
      rewrite <- HC_eq.
      exact H.
    }
    destruct parent_fields, (fields (body def)); simpl in Hfields_eq; try discriminate.
    simpl in Hown_field.
    destruct (f - 0); simpl in Hown_field; discriminate.
Qed.

Lemma vpa_type_to_type_sctype : forall T fieldType,
  sctype (vpa_type_to_type T fieldType) = sctype fieldType.
Proof.
  intros T fieldType.
  unfold vpa_type_to_type.
  destruct T as [q1 c1].
  destruct fieldType as [q2 c2].
  simpl.
  reflexivity.
Qed.

Lemma expr_has_type_class_in_table : forall CT sΓ e T,
  wf_class_table CT ->
  expr_has_type CT sΓ e T ->
  sctype T < dom CT.
Proof.
  intros CT sΓ e T HWFCT Htype.
  induction Htype.
  - (* ET_Null case *)
    exact H1.
  - (* ET_Var case *)
    (* Use the fact that variables in well-formed environments have bounded types *)
    eapply senv_var_domain; eauto.
  - (* ET_Field case *)
    assert (Hwf_field : wf_field CT fDef).
    {
      eapply sf_def_rel_wf_field; eauto.
    }
    unfold wf_field, wf_stypeuse in Hwf_field.
    destruct (bound CT (f_base_type (ftype fDef))) as [qc|] eqn:Hbound.
    + destruct Hwf_field as [_ [_ Hdom]].
      rewrite vpa_type_to_type_sctype.
      simpl.
      exact Hdom.
    + unfold bound in Hbound. destruct Hwf_field as [_ Hfalse]. contradiction Hfalse.
Qed.

(* Well-formedness of program  Aosen: I put it at the end because the main statement need to be well-typed*)
(* Definition WFProgram (p: program_def) : Prop :=
  Forall (fun decl => WFClass p.(classes) decl) p.(classes) . *)

Lemma find_app : forall A (f : A -> bool) l1 l2 x,
  find f l1 = Some x ->
  find f (l1 ++ l2) = Some x.
Proof.
  intros A f l1 l2 x H.
  induction l1 as [|h t IH].
  - (* l1 = [] *)
    simpl in H.
    discriminate.
  - (* l1 = h :: t *)
    simpl in H |- *.
    destruct (f h) eqn:Heq.
    + (* f h = true *)
      injection H as Heq_x.
      subst x.
      reflexivity.
    + (* f h = false *)
      apply IH.
      exact H.
Qed.

Lemma find_app_none : forall A (f : A -> bool) l1 l2,
  find f l1 = None ->
  find f (l1 ++ l2) = find f l2.
Proof.
  intros A f l1 l2 H.
  induction l1 as [|h t IH].
  - (* l1 = [] *)
    simpl.
    reflexivity.
  - (* l1 = h :: t *)
    simpl in H |- *.
    destruct (f h) eqn:Heq.
    + (* f h = true - contradiction *)
      discriminate H.
    + (* f h = false *)
      apply IH.
      exact H.
Qed.

Lemma find_filter_equiv : forall A (f g : A -> bool) l,
  (forall x, In x l -> f x = true -> g x = true) ->
  find f (filter g l) = find f l.
Proof.
  intros A f g l H.
  induction l as [|h t IH].
  - (* l = [] *)
    simpl.
    reflexivity.
  - (* l = h :: t *)
    simpl.
    destruct (g h) eqn:Hg.
    + (* g h = true *)
      simpl.
      destruct (f h) eqn:Hf.
      * (* f h = true *)
        reflexivity.
      * (* f h = false *)
        apply IH.
        intros x Hin Hfx.
        apply H; auto.
        right; exact Hin.
    + (* g h = false *)
      destruct (f h) eqn:Hf.
      * (* f h = true, but g h = false - contradiction with H *)
        exfalso.
        have Hg_true := H h (or_introl eq_refl) Hf.
        rewrite Hg in Hg_true.
        discriminate.
      * (* f h = false *)
        apply IH.
        intros x Hin Hfx.
        apply H; auto.
        right; exact Hin.
Qed.

Lemma find_some_iff : forall A (f : A -> bool) l,
  (exists x, find f l = Some x) <-> (exists x, In x l /\ f x = true).
Proof.
  intros A f l.
  split.
  - (* -> direction *)
    intro H.
    destruct H as [x Hfind].
    exists x.
    apply find_some in Hfind.
    exact Hfind.
  - (* <- direction *)
    intro H.
    destruct H as [x [Hin Hf]].
    induction l as [|h t IH].
    + (* l = [] *)
      simpl in Hin.
      contradiction.
    + (* l = h :: t *)
      simpl.
      destruct (f h) eqn:Heq.
      * (* f h = true *)
        exists h.
        reflexivity.
      * (* f h = false *)
        apply IH.
        simpl in Hin.
        destruct Hin as [Heq_h | Hin_t].
        -- (* x = h *)
           subst x.
           rewrite Hf in Heq.
           discriminate.
        -- (* x in t *)
           exact Hin_t.
Qed.

Lemma override_own_method_found : forall parent_methods own_methods m mdef,
  gget_method own_methods m = Some mdef ->
  gget_method (override parent_methods own_methods) m = Some mdef.
Proof.
  intros parent_methods own_methods m mdef Hown.
unfold override.
unfold gget_method.
induction own_methods as [|h t IH].
- (* own_methods = [] *)
  simpl in Hown.
  discriminate.
- (* own_methods = h :: t *)
  simpl.
  destruct (eq_method_name (mname (msignature h)) m) eqn:Heq.
  + (* Found in head *)
    unfold gget_method in Hown.
    simpl in Hown.
    rewrite Heq in Hown.
    injection Hown as Heq_mdef.
    subst mdef.
    reflexivity.
  + (* Not in head, check tail *)
  assert (Hfind_t : find (fun mdef0 => eq_method_name (mname (msignature mdef0)) m) t = Some mdef).
  {
    unfold gget_method in Hown.
    simpl in Hown.
    rewrite Heq in Hown.
    exact Hown.
  }
  eapply find_app.
  exact Hfind_t.
Qed.

Lemma override_parent_method_preserved : forall parent_methods own_methods m,
  gget_method own_methods m = None ->
  gget_method (override parent_methods own_methods) m = gget_method parent_methods m.
Proof.
  intros parent_methods own_methods m Hnone.
  unfold override, gget_method.
  induction own_methods as [|h t IH].
  - (* own_methods = [] *)
    simpl.
    induction parent_methods as [|h t IH].
    -- simpl. reflexivity.
    -- simpl. 
    destruct (eq_method_name (mname (msignature h)) m) eqn:Heq.
    --- (* eq_method_name returns true *)
      reflexivity.
    --- (* eq_method_name returns false *)
      exact IH.
  - (* own_methods = h :: t *)
    simpl in Hnone |- *.
    destruct (eq_method_name (mname (msignature h)) m) eqn:Heq.
    + (* Found in h - contradiction *)
      discriminate Hnone.
    + (* Not in h, continue *)
    assert (Hfind_t_none : find (fun mdef => eq_method_name (mname (msignature mdef)) m) t = None).
    {
      unfold gget_method in Hnone.
      exact Hnone.
    }
    rewrite find_app_none.
    -- (* Show find on t returns None *)
      exact Hfind_t_none.
    -- (* Show filters are equivalent *)
      apply find_filter_equiv.
      intro pmdef.
      intro Hin.
      rewrite Bool.negb_orb.
      rewrite Bool.andb_true_iff.
      split.
    --- (* Show ~~eq_method_name(pmdef, h) = true *)
      rewrite Bool.negb_true_iff.
      assert (Hneq : mname (msignature pmdef) <> mname (msignature h)).
      {
        intro Heq_names.
        rewrite Heq_names in H.
        rewrite H in Heq.
        discriminate.
      }
      destruct (eq_method_name (mname (msignature pmdef)) (mname (msignature h))) eqn:Heq_pmdef_h.
      +++ (* eq_method_name returns true - contradiction *)
        exfalso.
        apply Hneq.
        apply Nat.eqb_eq in Heq_pmdef_h.
        exact Heq_pmdef_h.
      +++ (* eq_method_name returns false - this is what we want *)
        reflexivity.
    --- (* Show ~~existsb(...) = true *)
      rewrite Bool.negb_true_iff.
      destruct (existsb (fun omdef => eq_method_name (mname (msignature pmdef)) (mname (msignature omdef))) t) eqn:Hexistsb.
      +++ (* existsb returns true - contradiction *)
        exfalso.
        apply existsb_exists in Hexistsb.
        destruct Hexistsb as [omdef [Hin_t Heq_names]].
        (* pmdef matches m, and omdef has same name as pmdef, so omdef matches m *)
        assert (Homdef_m : eq_method_name (mname (msignature omdef)) m = true).
        {
          apply Nat.eqb_eq in H.
          apply Nat.eqb_eq in Heq_names.
          rewrite <- Heq_names.
          apply Nat.eqb_eq.
          exact H.
        }
        (* This contradicts that find on t returns None *)
        unfold gget_method in Hnone.
        assert (Hcontra : find (fun mdef => eq_method_name (mname (msignature mdef)) m) t <> None).
        {
          assert (Hfind_exists : exists x, find (fun mdef => eq_method_name (mname (msignature mdef)) m) t = Some x).
          {
            apply find_some_iff.
            exists omdef.
            split; [exact Hin_t | exact Homdef_m].
          }
          intro Hcontra.
          destruct Hfind_exists as [x Hfind_x].
          rewrite Hfind_x in Hcontra.
          discriminate.
        }
        rewrite Hfind_t_none in Hcontra.
        apply Hcontra.
        reflexivity.
      +++ (* existsb returns false - this is what we want *)
        reflexivity.
Qed.

Lemma override_preserves_param_count : forall CT C parent_methods own_methods m mdef mdef',
  wf_class_table CT ->
  CollectMethods CT C (override parent_methods own_methods) ->
  gget_method own_methods m = Some mdef ->
  gget_method (override parent_methods own_methods) m = Some mdef' ->
  dom (mparams (msignature mdef)) = dom (mparams (msignature mdef')).
Proof.
  intros CT C parent_methods own_methods m mdef mdef' Hwf_ct Hcollect Hown Hoverride.
  have Hfound := override_own_method_found parent_methods own_methods m mdef Hown.
  rewrite Hfound in Hoverride.
  injection Hoverride as Heq.
  subst mdef'.
  reflexivity.
Qed.

(* Lemma method_lookup_in_local_methods : forall CT C mdef m,
  MethodLookup CT C m mdef ->
  exists def, find_class CT C = Some def /\
    (In mdef (methods (body def)) \/
     exists parent_methods, 
       CollectMethods CT C (override parent_methods (methods (body def))) /\
       In mdef (override parent_methods (methods (body def)))).
Proof.
  intros CT C mdef m Hlookup.
  inversion Hlookup; subst.
  inversion H; subst.
  - (* CM_NotFound *)
    exfalso.
    unfold gget_method in H0.
    discriminate.
  - (* CM_Object *)
    exists def.
    split.
    -- exact H1.
    -- left.
      unfold gget_method in H0.
      eapply find_some in H0.
      destruct H0 as [Hin _].
      exact Hin.
  - (* CM_Inherit *)
    exists def.
    split.
    -- exact H1.
    -- right.
      exists parent_methods.
      split.
      + exact H.
      + unfold gget_method in H0.
        eapply find_some in H0.
        destruct H0 as [Hin _].
        exact Hin.
Qed. *)

Lemma parent_lookup_ordering : forall CT C D,
  wf_class_table CT ->
  C < dom CT ->
  D < dom CT ->
  parent_lookup CT C = Some D ->
  D < C.
Proof.
  intros CT C D Hwf Hcdom Hddom Hparent.
  (* Get class definition for C *)
  assert (Hfind_C : exists def_C, find_class CT C = Some def_C).
  { apply find_class_Some. exact Hcdom. }
  destruct Hfind_C as [def_C Hfind_C].
  
  (* From parent_lookup definition *)
  unfold parent_lookup in Hparent.
  rewrite Hfind_C in Hparent.
  
  (* From well-formed class table, get wf_class for C *)
  assert (Hwf_class_C : wf_class CT def_C).
  {
    unfold wf_class_table in Hwf.
    destruct Hwf as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  
  (* From wf_class, parent relationship implies ordering *)
  inversion Hwf_class_C; subst.
  - (* WFObjectDef - contradiction since C has parent *)
    rewrite H in Hparent. discriminate.
  - (* WFOtherDef *)
    assert (Hcname_eq : cname (signature def_C) = C).
    {
      unfold wf_class_table in Hwf.
      destruct Hwf as [_ [_ [_ Hcname_consistent]]].
      apply Hcname_consistent.
      exact Hfind_C.
    }
    rewrite H0 in Hparent.
    injection Hparent as Heq.
    subst D.
    rewrite Hcname_eq in H2.
    lia. (* Convert C > D to D <= C *)
Qed.

Lemma parent_implies_strict_ordering : forall CT C D cdef_C,
  wf_class_table CT ->
  C < dom CT ->
  find_class CT C = Some cdef_C ->
  super (signature cdef_C) = Some D ->
  D < C.
Proof.
  intros CT C D cdef_C Hwf Hcdom Hfind Hsuper.
  
  (* From well-formed class table, get wf_class for C *)
  assert (Hwf_class_C : wf_class CT cdef_C).
  {
    unfold wf_class_table in Hwf.
    destruct Hwf as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  
  (* From wf_class, parent relationship implies strict ordering *)
  inversion Hwf_class_C; subst.
  - (* WFObjectDef - contradiction since C has parent *)
    rewrite H in Hsuper. discriminate.
  - (* WFOtherDef *)
    assert (Hcname_eq : cname (signature cdef_C) = C).
    {
      unfold wf_class_table in Hwf.
      destruct Hwf as [_ [_ [_ Hcname_consistent]]].
      apply Hcname_consistent.
      exact Hfind.
    }
    rewrite H0 in Hsuper.
    injection Hsuper as Heq.
    subst D.
    rewrite Hcname_eq in H2.
    exact H2.
Qed.

Lemma collect_fields_exists : forall CT c,
  wf_class_table CT ->
  c < dom CT ->
  exists field_defs, CollectFields CT c field_defs.
Proof.
  intros CT c Hwf_classtable.
  induction c using lt_wf_ind.
  intros Hdom.
  assert (Hfind : exists def, find_class CT c = Some def).
  {
    apply find_class_Some. exact Hdom.
  }
  destruct Hfind as [def Hfind].
  destruct (super (signature def)) as [parent|] eqn:Hsuper.
  - (* Case: class has superclass *)
    assert (Hparent_dom : parent < c).
    {
      eapply parent_implies_strict_ordering with (cdef_C:= def); eauto.
    }
    assert (Hparent_in_ct : parent < dom CT).
    {
      lia.
    }
    (* Apply induction hypothesis *)
    destruct (H parent Hparent_dom Hparent_in_ct) as [parent_fields Hparent_collect].
    exists (parent_fields ++ Syntax.fields (body def)).
    apply CF_Inherit with (def := def) (parent := parent) (parent_fields := parent_fields) (own_fields := Syntax.fields (body def)); auto.
  - (* Case: Object class (no superclass) *)
    exists ([] : list field_def).
    apply CF_Object with def; auto.
Qed.

Lemma find_overriding_method_deterministic : forall CT C mname mdef1 mdef2,
  wf_class_table CT ->
  C < dom CT ->
  FindMethodWithName CT C mname mdef1 ->
  FindMethodWithName CT C mname mdef2 ->
  mdef1 = mdef2.
Proof.
  intros CT C mname mdef1 mdef2 Hwf_ct Hbound Hfind1 Hfind2.
  (* Strong induction on C *)
  induction C using lt_wf_ind.
  intros.
  
  inversion Hfind1; subst.
  inversion Hfind2; subst.
  
  (* Establish same class definition *)
  assert (Heq_def : def = def0).
  { 
    rewrite H0 in H1.
    injection H1 as Heq.
    exact Heq.
  }
  subst def0.
  
  (* Case analysis on both calls *)
  - (* Both find locally *)
    rewrite H2 in H4.
    injection H4 as Heq.
    exact Heq.
    
  - (* First local, second parent - contradiction *)
    exfalso.
    assert (Heq_def : def = def0).
    {
      rewrite H0 in H1.
      injection H1 as Heq.
      exact Heq.
    }
    subst def0.
    rewrite H2 in H4.
    discriminate H4.
    
  - (* First parent, second local - contradiction *)
    (* exfalso. *)
    {
      inversion Hfind2; subst.
      - (* Case: Hfind2 finds method locally - contradiction *)
        assert (Heq_def : def = def0).
        {
          rewrite H0 in H1.
          injection H1 as Heq.
          exact Heq.
        }
        subst def0.
        rewrite H2 in H6.
        discriminate H6.
      - (* Case: Hfind2 also goes to parent *)
        assert (Heq_def : def = def0).
        {
          rewrite H0 in H1.
          injection H1 as Heq.
          exact Heq.
        }
        subst def0.
        assert (Heq_parent : parent = parent0).
        {
          rewrite H3 in H7.
          injection H7 as Heq.
          exact Heq.
        }
        subst parent0.
        
        (* Apply induction hypothesis *)
        apply (H parent).
        + (* parent < C *)
          eapply parent_implies_strict_ordering; eauto.
        + 
          assert (parent < C). 
          {eapply parent_implies_strict_ordering; eauto.
          }
          lia.
        + exact H4.
        + exact H8. 
    }
Qed.

(* Lemma method_exists_in_subtype : forall CT C D m mdef,
  wf_class_table CT ->
  base_subtype CT C D ->
  FindMethodWithName CT D m mdef ->
  exists mdef', FindMethodWithName CT C m mdef'.
Proof.
  intros CT C D m mdef hwf Hsubtype Hlookup_D.
  generalize dependent mdef.
  induction Hsubtype; intros mdef Hlookup_D.
  - (* Base case: C = D *)
    exists mdef.
    exact Hlookup_D.
  - (* Inductive case: C <: E <: D *)
    (* First get some method from D using IHHsubtype2 *)
    destruct (IHHsubtype2 hwf mdef Hlookup_D) as [mdef_D Hlookup_mdef_D].
    (* Then get some method from C using IHHsubtype1 *)
    destruct (IHHsubtype1 hwf mdef_D Hlookup_mdef_D) as [mdef_C Hlookup_mdef_C].
    exists mdef_C.
    exact Hlookup_mdef_C.
  - (* Get class definition for C *)
    assert (Hexists_class_C : exists class_def_C, find_class CT C = Some class_def_C).
    {
      apply find_class_Some.
      exact H.
    }
    destruct Hexists_class_C as [class_def_C Hfind_C].

    (* Check if method is defined locally in C *)
    destruct (gget_method (methods (body class_def_C)) m) as [local_mdef|] eqn:Hlocal.
    -- (* Method found locally in C *)
      exists local_mdef.
      inversion Hlookup_D; subst.
      (* rename methods into dmethods. *)
      apply ML_Found with (override dmethods (methods (body class_def_C))).
      + (* Prove CollectMethods for object class case *)
        assert (Hsuper_eq : super (signature class_def_C) = Some D).
        {
          unfold parent_lookup in H1.
          rewrite Hfind_C in H1.
          exact H1.
        }
        eapply CM_Inherit; eauto.
        * (* C > D - from well-formed class table ordering *)
          {
          assert (Hwf_class_C : wf_class CT class_def_C).
          {
            unfold wf_class_table in hwf.
            destruct hwf as [Hforall_wf _].
            eapply Forall_nth_error; eauto.
          }
          inversion Hwf_class_C; subst.
          - (* WFObjectDef case - contradiction since C has a parent *)
            rewrite H4 in Hsuper_eq.
            discriminate.
          - (* WFOtherDef case *)
            assert (Hcname_eq : cname (signature class_def_C) = C).
            {
              unfold wf_class_table in hwf.
              destruct hwf as [_ [_ [_ Hcname_consistent]]].
              apply Hcname_consistent.
              exact Hfind_C.
            }
            rewrite Hcname_eq.
            rewrite H5 in Hsuper_eq.
            injection Hsuper_eq as Heq.
            subst superC.
            rewrite Hcname_eq in H7.
            exact H7.
        }
      + 
      apply override_own_method_found.
      exact Hlocal.
    -- (* Method not found locally, inherit from parent *)
      inversion Hlookup_D; subst.
      exists mdef.
      rename methods into dmethods.
      apply ML_Found with (override dmethods (methods (body class_def_C))).
      + assert (Hsuper_eq : super (signature class_def_C) = Some D).
        {
          unfold parent_lookup in H1.
          rewrite Hfind_C in H1.
          exact H1.
        }
        eapply CM_Inherit; eauto.
        *
        {
          assert (Hwf_class_C : wf_class CT class_def_C).
          {
            unfold wf_class_table in hwf.
            destruct hwf as [Hforall_wf _].
            eapply Forall_nth_error; eauto.
          }
          inversion Hwf_class_C; subst.
          - (* WFObjectDef case - contradiction since C has a parent *)
            rewrite H4 in Hsuper_eq.
            discriminate.
          - (* WFOtherDef case *)
            assert (Hcname_eq : cname (signature class_def_C) = C).
            {
              unfold wf_class_table in hwf.
              destruct hwf as [_ [_ [_ Hcname_consistent]]].
              apply Hcname_consistent.
              exact Hfind_C.
            }
            rewrite Hcname_eq.
            rewrite H5 in Hsuper_eq.
            injection Hsuper_eq as Heq.
            subst superC.
            rewrite Hcname_eq in H7.
            exact H7.
        }
      + erewrite override_parent_method_preserved; eauto.
Qed. *)

(* Lemma method_exists_in_strict_subtype : forall CT C D m mdef,
  wf_class_table CT ->
  base_subtype_strict CT C D ->
  MethodLookup CT D m mdef ->
  exists mdef', MethodLookup CT C m mdef'.
Proof.
  intros CT C D m mdef hwf Hsubtype Hlookup_D.
  generalize dependent mdef.
  induction Hsubtype; intros mdef Hlookup_D.
  - (* Inductive case: C <: E <: D *)
    (* First get some method from D using IHHsubtype2 *)
    destruct (IHHsubtype2 hwf mdef Hlookup_D) as [mdef_D Hlookup_mdef_D].
    (* Then get some method from C using IHHsubtype1 *)
    destruct (IHHsubtype1 hwf mdef_D Hlookup_mdef_D) as [mdef_C Hlookup_mdef_C].
    exists mdef_C.
    exact Hlookup_mdef_C.
  - (* Get class definition for C *)
    assert (Hexists_class_C : exists class_def_C, find_class CT C = Some class_def_C).
    {
      apply find_class_Some.
      exact H.
    }
    destruct Hexists_class_C as [class_def_C Hfind_C].

    (* Check if method is defined locally in C *)
    destruct (gget_method (methods (body class_def_C)) m) as [local_mdef|] eqn:Hlocal.
    -- (* Method found locally in C *)
      exists local_mdef.
      inversion Hlookup_D; subst.
      rename methods into dmethods.
      apply ML_Found with (override dmethods (methods (body class_def_C))).
      + (* Prove CollectMethods for object class case *)
        assert (Hsuper_eq : super (signature class_def_C) = Some D).
        {
          unfold parent_lookup in H1.
          rewrite Hfind_C in H1.
          exact H1.
        }
        eapply CM_Inherit; eauto.
        * (* C > D - from well-formed class table ordering *)
          {
          assert (Hwf_class_C : wf_class CT class_def_C).
          {
            unfold wf_class_table in hwf.
            destruct hwf as [Hforall_wf _].
            eapply Forall_nth_error; eauto.
          }
          inversion Hwf_class_C; subst.
          - (* WFObjectDef case - contradiction since C has a parent *)
            rewrite H4 in Hsuper_eq.
            discriminate.
          - (* WFOtherDef case *)
            assert (Hcname_eq : cname (signature class_def_C) = C).
            {
              unfold wf_class_table in hwf.
              destruct hwf as [_ [_ [_ Hcname_consistent]]].
              apply Hcname_consistent.
              exact Hfind_C.
            }
            rewrite Hcname_eq.
            rewrite H5 in Hsuper_eq.
            injection Hsuper_eq as Heq.
            subst superC.
            rewrite Hcname_eq in H7.
            exact H7.
        }
      + 
      apply override_own_method_found.
      exact Hlocal.
    -- (* Method not found locally, inherit from parent *)
      inversion Hlookup_D; subst.
      exists mdef.
      rename methods into dmethods.
      apply ML_Found with (override dmethods (methods (body class_def_C))).
      + assert (Hsuper_eq : super (signature class_def_C) = Some D).
        {
          unfold parent_lookup in H1.
          rewrite Hfind_C in H1.
          exact H1.
        }
        eapply CM_Inherit; eauto.
        *
        {
          assert (Hwf_class_C : wf_class CT class_def_C).
          {
            unfold wf_class_table in hwf.
            destruct hwf as [Hforall_wf _].
            eapply Forall_nth_error; eauto.
          }
          inversion Hwf_class_C; subst.
          - (* WFObjectDef case - contradiction since C has a parent *)
            rewrite H4 in Hsuper_eq.
            discriminate.
          - (* WFOtherDef case *)
            assert (Hcname_eq : cname (signature class_def_C) = C).
            {
              unfold wf_class_table in hwf.
              destruct hwf as [_ [_ [_ Hcname_consistent]]].
              apply Hcname_consistent.
              exact Hfind_C.
            }
            rewrite Hcname_eq.
            rewrite H5 in Hsuper_eq.
            injection Hsuper_eq as Heq.
            subst superC.
            rewrite Hcname_eq in H7.
            exact H7.
        }
      + erewrite override_parent_method_preserved; eauto.
Qed. *)

Lemma subtype_preserves_dom : forall CT C D,
  wf_class_table CT ->
  base_subtype CT C D ->
  C < dom CT ->
  D < dom CT.
Proof.
  intros CT C D Hwf_ct Hsub Hcdom.
  induction Hsub.
  - (* Reflexivity: C = D *)
    exact Hcdom.
  - (* Transitivity: C <: E <: D *)
    apply IHHsub2.
    exact Hwf_ct.
    apply IHHsub1.
    exact Hwf_ct.
    exact Hcdom.
  - (* Direct inheritance: C extends D *)
    (* C is in domain, so it has a valid class definition *)
    assert (Hfind_C : exists def_C, find_class CT C = Some def_C).
    {
      apply find_class_Some.
      exact Hcdom.
    }
    destruct Hfind_C as [def_C Hfind_C].
    
    (* From parent_lookup, C has parent D *)
    unfold parent_lookup in H1.
    rewrite Hfind_C in H1.
    simpl in H1.
    
    (* From well-formed class table, parent must be in domain *)
    assert (Hwf_class_C : wf_class CT def_C).
    {
      unfold wf_class_table in Hwf_ct.
      destruct Hwf_ct as [Hforall_wf _].
      eapply Forall_nth_error; eauto.
    }
    
    (* From wf_class, if C has parent D, then D < C *)
    inversion Hwf_class_C; subst.
    + (* WFObjectDef - contradiction since C has parent *)
      rewrite H2 in H1.
      discriminate.
    + (* WFOtherDef *)
      assert (Hsuper_eq : super (signature def_C) = Some D).
      {
        exact H1.
      }
      (* From class name consistency *)
      assert (Hthis_eq : cname (signature def_C) = C).
      {
        unfold wf_class_table in Hwf_ct.
        destruct Hwf_ct as [_ [_ [_ Hcname_consistent]]].
        apply Hcname_consistent.
        exact Hfind_C.
      }
      exact H0.
Qed.

Inductive IsOverride : class_table -> class_name -> method_def -> class_name -> method_def -> Prop :=
  | IO_Direct : forall CT C D mdef_C mdef_D cdef_C cdef_D,
      base_subtype_strict CT C D ->
      find_class CT C = Some cdef_C ->
      (* super (signature cdef_C) = Some D -> *)
      find_class CT D = Some cdef_D ->
      In mdef_C (methods (body cdef_C)) ->
      In mdef_D (methods (body cdef_D)) ->
      (mname (msignature mdef_C)) = (mname (msignature mdef_D)) ->
      IsOverride CT C mdef_C D mdef_D
  | IO_Trans : forall CT C D E mdef_C mdef_D mdef_E,
      IsOverride CT C mdef_C D mdef_D ->
      IsOverride CT D mdef_D E mdef_E ->
      IsOverride CT C mdef_C E mdef_E.

Lemma base_subtype_CD : forall CT C D,
  wf_class_table CT ->
  base_subtype CT C D ->
  D <= C.
Proof.
  intros CT C D Hwf Hsub.
  induction Hsub.
  - (* base_refl case *)
    easy.
  - (* base_trans case *)
    apply Nat.le_trans with D; auto.
  - (* base_extends case *)
    apply Nat.lt_le_incl.
eapply parent_lookup_ordering; eauto.
Qed.

Lemma base_subtype_strict_CD : forall CT C D,
  wf_class_table CT ->
  base_subtype_strict CT C D ->
  D < C.
Proof.
  intros CT C D Hwf Hsub.
  induction Hsub.
  - (* base_trans case *)
    eapply Nat.lt_trans; [apply IHHsub2 | apply IHHsub1]; exact Hwf.
  - (* base_extends case *)
    eapply parent_lookup_ordering; eauto.
Qed.

(* Lemma method_lookup_name_consistent : forall CT C m mdef,
  MethodLookup CT C m mdef ->
  mname (msignature mdef) = m.
Proof.
  intros CT C m mdef Hlookup.
  inversion Hlookup; subst.
  inversion H; subst.
  - (* CM_NotFound - contradiction *)
    unfold gget_method in H0.
    discriminate.
  - (* CM_Object *)
    eapply gget_method_name_consistent; eauto.
  - (* CM_Inherit *)
    eapply gget_method_name_consistent; eauto.
Qed. *)

Lemma override_preserves_method_name : forall CT C D mdef_C mdef_D,
  IsOverride CT C mdef_C D mdef_D ->
  mname (msignature mdef_C) = mname (msignature mdef_D).
Proof.
  intros CT C D mdef_C mdef_D H.
  induction H.
  
  -
    exact H4.
    
  -
    rewrite IHIsOverride2 in IHIsOverride1.
    auto.
Qed.

Lemma base_subtype_dom : forall CT C D,
  wf_class_table CT ->
  base_subtype CT C D ->
  C < dom CT /\ D < dom CT.
Proof.
  intros CT C D Hwf Hsub.
  induction Hsub.
  - (* base_refl case *)
    split; exact H.
  - (* base_trans case *)
    destruct IHHsub1 as [HC HD].
    destruct IHHsub2 as [HD HE].
    exact Hwf.
    exact Hwf.
    destruct IHHsub2 as [_ HE].
    exact Hwf.
    split; [exact HC | exact HE].
  - (* base_extends case *)
    split; [exact H | exact H0].
Qed.

Lemma base_subtype_strict_dom : forall CT C D,
  wf_class_table CT ->
  base_subtype_strict CT C D ->
  C < dom CT /\ D < dom CT.
Proof.
  intros CT C D Hwf Hsub.
  induction Hsub.
  - (* base_trans case *)
    destruct IHHsub1 as [HC HD].
    destruct IHHsub2 as [HD HE].
    exact Hwf.
    exact Hwf.
    destruct IHHsub2 as [_ HE].
    exact Hwf.
    split; [exact HC | exact HE].
  - (* base_extends case *)
    split; [exact H | exact H0].
Qed.

(* Lemma method_lookup_dom : forall CT C m mdef,
  MethodLookup CT C m mdef ->
  C < dom CT.
Proof.
  intros CT C m mdef H.
  inversion H; subst.
  inversion H0; subst.
  - (* CM_NotFound - contradiction *)
    unfold gget_method in H1.
    discriminate.
  - (* CM_Object *)
    exact H4.
  - (* CM_Inherit *)
    exact H4.
Qed. *)

Lemma override_implies_subtype : forall CT C D mdef_C mdef_D,
  wf_class_table CT ->
  IsOverride CT C mdef_C D mdef_D ->
  base_subtype_strict CT C D.
Proof.
  intros CT C D mdef_C mdef_D Hwf H.
  induction H.
  - (* IO_Direct case *)
  exact H.
  - (* IO_Trans case *)
    eapply base_trans_strict; eauto.
Qed.

Lemma override_implies_greater : forall CT C D mdef_C mdef_D,
  wf_class_table CT ->
  IsOverride CT C mdef_C D mdef_D ->
  C > D.
Proof.
  intros CT C D mdef_C mdef_D Hwf H.
  apply override_implies_subtype in H; auto.
  eapply base_subtype_strict_CD; eauto.
Qed.

Lemma override_implies_method_in_body : forall CT C D cdef_C mdef_C mdef_D,
  wf_class_table CT ->
  find_class CT C = Some cdef_C ->
  IsOverride CT C mdef_C D mdef_D ->
  In mdef_C (methods (body cdef_C)).
Proof.
  intros CT C D cdef_C mdef_C mdef_D Hwf Hfind H.
  generalize dependent Hfind.
  (* inversion H; subst. *)
  induction H.
  - (* IO_Direct case *)
    intros.
    assert (Heq_def : cdef_C0 = cdef_C).
{ 
  rewrite Hfind in H0. 
  injection H0 as Heq. 
  symmetry.
  exact Heq. 
}
subst cdef_C0.
exact H2.
- (* IO_Trans case *)
  intros Hfind.
  apply IHIsOverride1; auto.
Qed.

(* Lemma method_lookup_local_precedence : forall CT C m mdef local_mdef cdef_C,
  wf_class_table CT ->
  find_class CT C = Some cdef_C ->
  MethodLookup CT C m mdef ->
  gget_method (methods (body cdef_C)) m = Some local_mdef ->
  mdef = local_mdef.
Proof.
intros CT C m mdef local_mdef cdef_C Hwf Hfind_C Hlookup Hlocal.

(* Analyze the MethodLookup structure *)
inversion Hlookup; subst.
inversion H; subst.
- (* CM_NotFound - contradiction *)
  unfold gget_method in H0.
  discriminate.
- (* CM_Object - method found in local methods *)
  assert (Heq_def : def = cdef_C).
  { rewrite Hfind_C in H1. injection H1 as Heq. symmetry. exact Heq. }
  subst def.
  (* Both H0 and Hlocal are gget_method calls on the same method list *)
  rewrite Hlocal in H0.
  injection H0 as Heq.
  symmetry.
  exact Heq.
- (* CM_Inherit - method found in override list *)
  assert (Heq_def : def = cdef_C).
  { rewrite Hfind_C in H1. injection H1 as Heq. symmetry. exact Heq. }
  subst def.
  
  (* The override mechanism prioritizes local methods *)
  unfold gget_method in H0.
  unfold override in H0.
  
  (* Since local method exists, gget_method on override list should find it first *)
  assert (Hoverride_finds_local : gget_method (override parent_methods (methods (body cdef_C))) m = Some local_mdef).
  {
    (* Use the fact that override = local ++ filtered_parent, and local takes precedence *)
    eapply override_own_method_found; eauto.
  }
  
  assert (Heq_results : Some mdef = Some local_mdef).
  { rewrite <- H0. exact Hoverride_finds_local. }

  injection Heq_results as Heq.
  exact Heq.
Qed. *)

(* Lemma collect_methods_lookup_consistent : forall CT D m mdef parent_methods,
  wf_class_table CT ->
  CollectMethods CT D parent_methods ->
  MethodLookup CT D m mdef ->
  gget_method parent_methods m = Some mdef.
Proof.
  intros CT D m mdef parent_methods Hwf Hcollect Hlookup.
  
  (* Induction on CollectMethods *)
  induction Hcollect.
  
  - (* CM_Object case: CollectMethods CT D (methods (body def)) *)
    exfalso.

    (* If find_class CT C = None, then MethodLookup CT C should fail *)
    inversion Hlookup; subst.
    inversion H0; subst.
    -- (* CM_NotFound - this is expected, but contradicts successful lookup *)
      unfold gget_method in H1.
      discriminate.
    -- (* CM_Object - contradiction since find_class CT C = None *)
      rewrite H in H2.
      discriminate.
    -- (* CM_Inherit - contradiction since find_class CT C = None *)
      rewrite H in H2.
      discriminate.
  
  - (* CM_Inherit case: CollectMethods CT D (override parent_methods0 (methods (body def))) *)
    inversion Hlookup; subst.
    inversion H2; subst.
    -- (* CM_NotFound - contradiction since lookup succeeded *)
      unfold gget_method in H3.
      discriminate.
    -- (* CM_Object - method found in local methods *)
      assert (Heq_def : def = def0).
      { rewrite H in H4. injection H4 as Heq. exact Heq. }
      subst def0.
      exact H3.
    -- (* CM_Inherit - contradiction since C has no parent *)
      assert (Heq_def : def = def0).
      { rewrite H in H4. injection H4 as Heq. exact Heq. }
      subst def0.
      (* super (signature def) = None contradicts super (signature def) = Some parent *)
      rewrite H0 in H5.
      discriminate.
  -
   inversion Hlookup; subst.
inversion H6; subst.
-- (* CM_NotFound - contradiction since lookup succeeded *)
  unfold gget_method in H7.
  discriminate.
-- (* CM_Object - contradiction since C has a parent *)
  assert (Heq_def : def = def0).
  { 
    rewrite H in H4.
    injection H4 as Heq.
    exact Heq. 
  }
  subst def0.
  (* super (signature def) = Some parent contradicts super (signature def) = None *)
  rewrite H0 in H5.
  discriminate.
-- (* CM_Inherit - method found in override list *)
  assert (Heq_def : def = def0).
  { rewrite H in H4. injection H4 as Heq. exact Heq. }
  subst def0.
  
  (* Verify that the parent and method lists match *)
  assert (Heq_parent : parent = parent0).
  { rewrite H0 in H5. injection H5 as Heq. exact Heq. }
  subst parent0.
  
  assert (Heq_parent_methods : parent_methods = parent_methods0).
  {
    (* Use determinism of CollectMethods *)
    eapply collect_methods_deterministic; eauto.
  }
  subst parent_methods0.

  exact H7.   
Qed. *)

(* Lemma method_lookup_inherited_same : forall CT C D cdef_C m mdef_c mdef_d,
  wf_class_table CT ->
  find_class CT C = Some cdef_C ->
  parent_lookup CT C = Some D ->
  MethodLookup CT C m mdef_c ->
  MethodLookup CT D m mdef_d ->
  gget_method (methods (body cdef_C)) m = None ->
  mdef_c = mdef_d.
Proof.
intros CT C D cdef_C m mdef_c mdef_d Hwf Hfind_C Hparent HlookupC HlookupD Hlocal.

(* Analyze how MethodLookup CT C works without local method *)
inversion HlookupC; subst.
inversion H; subst.
- (* CM_NotFound - contradiction since lookup succeeded *)
  unfold gget_method in H0.
  discriminate.
- (* CM_Object - contradiction since no local method exists *)
  assert (Heq_def : def = cdef_C).
  { rewrite Hfind_C in H1. injection H1 as Heq. symmetry. exact Heq. }
  subst def.
  rewrite Hlocal in H0.
  discriminate.
- (* CM_Inherit - method comes from parent via override mechanism *)
  assert (Heq_def : def = cdef_C).
  { rewrite Hfind_C in H1. injection H1 as Heq. symmetry. exact Heq. }
  subst def.
  
  (* Since no local method exists, override_parent_method_preserved applies *)
  have Hinherited := override_parent_method_preserved parent_methods (methods (body cdef_C)) m Hlocal.
  
  (* From H0: gget_method (override parent_methods (methods (body cdef_C))) m = Some mdef_c *)
  (* From Hinherited: gget_method (override ...) m = gget_method parent_methods m *)
  (* So: gget_method parent_methods m = Some mdef_c *)
  rewrite Hinherited in H0.
  
  (* Now connect parent_methods with MethodLookup CT D *)
  (* From parent_lookup CT C = Some D, we know D is the parent *)
  assert (Hparent_eq : parent = D).
  {
    unfold parent_lookup in Hparent.
    rewrite Hfind_C in Hparent.
    rewrite H2 in Hparent.
    injection Hparent as Heq.
    exact Heq.
  }
  subst parent.
  
  have Hparent_consistent := collect_methods_lookup_consistent CT D m mdef_d parent_methods Hwf H6 HlookupD.

rewrite Hparent_consistent in H0.
injection H0 as Heq.
symmetry.
exact Heq.
Qed. *)

(* Lemma method_different_implies_local : forall CT C D m mdef_C mdef_D cdef_C,
  wf_class_table CT ->
  C < dom CT ->
  D < dom CT ->
  parent_lookup CT C = Some D ->
  C <> D ->
  find_class CT C = Some cdef_C ->
  mdef_C <> mdef_D ->
  MethodLookup CT C m mdef_C ->
  MethodLookup CT D m mdef_D ->
  In mdef_C (methods (body cdef_C)).
Proof.
  intros CT C D m mdef_C mdef_D cdef_C Hwf Hcdom Hddom Hparent Hneq Hfind_C Hneqmdef HlookupC HlookupD.
  
  (* Case analysis: is method locally defined or inherited? *)
  destruct (gget_method (methods (body cdef_C)) m) as [local_mdef|] eqn:Hlocal.
  - (* Method is locally defined *)
    (* Show that local_mdef = mdef_C *)
    assert (Hlocal_eq : local_mdef = mdef_C).
    {
      symmetry.
      eapply method_lookup_local_precedence; eauto.
    }
    subst local_mdef.
    unfold gget_method in Hlocal.
    apply find_some in Hlocal.
    destruct Hlocal as [Hin_local _].
    exact Hin_local.
    
  - (* Method is not locally defined, so it must be inherited *)
    exfalso.
    (* If method is inherited, then mdef_C should equal mdef_D *)
    apply Hneqmdef.
    eapply method_lookup_inherited_same; eauto.
Qed.

Lemma subtype_method_same : forall CT C D m mdef_C mdef_D,
  wf_class_table CT ->
  C < dom CT ->
  D < dom CT ->
  base_subtype CT C D ->
  C = D ->
  MethodLookup CT C m mdef_C ->
  MethodLookup CT D m mdef_D ->
  mdef_C = mdef_D.
Proof.
  intros CT C D m mdef_C mdef_D Hwf Hcdom Hddom Hsub HeqCD HlookupC HlookupD.
  subst D.
  eapply method_lookup_deterministic; eauto.
Qed. *)

Lemma subtype_method_override_direct : forall CT C D mdef_C mdef_D cdef_C cdef_D,
  wf_class_table CT ->
  C < dom CT ->
  D < dom CT ->
  parent_lookup CT C = Some D ->
  find_class CT C = Some cdef_C ->
  find_class CT D = Some cdef_D ->
  In mdef_C (methods (body cdef_C)) ->
  In mdef_D (methods (body cdef_D)) -> 
  (mname (msignature mdef_C)) = (mname (msignature mdef_D)) ->
  IsOverride CT C mdef_C D mdef_D.
Proof.
  intros.
  eapply IO_Direct; eauto.
  eapply base_extends_strict; eauto.
Qed.

Lemma method_lookup_wf_class: forall CT C mdef cdef,
  wf_class_table CT ->
  C < dom CT ->
  find_class CT C = Some cdef ->
  In mdef (methods (body cdef)) ->
  wf_method CT C mdef.
Proof.
  intros CT C mdef cdef Hwf_ct Hdom HfindC Hlookup.
  (* Get the well-formed class from the class table *)
  assert (Hwf_class : wf_class CT cdef).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  
  (* Extract the methods well-formedness from the class well-formedness *)
  inversion Hwf_class; subst.
  - (* WFObjectDef case *)
    exfalso.
    (* Object class has no methods, contradiction *)
    rewrite H2 in Hlookup.
    simpl in Hlookup.
    exact Hlookup.
  - (* WFOtherDef case *)
    destruct H3 as [_ [Hforall_methods _]].
    (* Apply Forall to get wf_method for our specific mdef *)
    apply In_nth_error in Hlookup.
    destruct Hlookup as [n Hnth].
    assert (HC0_eq : C0 = C).
    {
      unfold C0.
      unfold wf_class_table in Hwf_ct.
      destruct Hwf_ct as [_ [_ [_ Hcname_consistent]]].
      apply Hcname_consistent.
      exact HfindC.
    }
    rewrite HC0_eq in Hforall_methods.
    eapply Forall_nth_error; eauto.
Qed.

(* Lemma wf_method_override_same_param_length : forall CT C mdef cdef parentname supermdef,
  wf_method CT C mdef ->
  find_class CT C = Some cdef ->
  super (signature cdef) = Some parentname ->
  FindOverrideMethod CT C (mname (msignature mdef)) mdef ->
  FindOverrideMethod CT parentname (mname (msignature mdef)) supermdef ->
  dom (mparams (msignature mdef)) = dom (mparams (msignature supermdef)).
Proof.
  intros CT C mdef cdef parentname supermdef Hwf_mdef Hfind_C Hsuper Hfind_C_mdef Hfind_parent_mdef.
  inversion Hwf_mdef; subst.
  specialize (H0 cdef parentname supermdef Hfind_C Hsuper Hfind_C_mdef Hfind_parent_mdef).
  destruct H0 as [Heq | [Hforall2 _]].
  - (* Case: mdef = supermdef *)
    rewrite Heq. reflexivity.
  - (* Case: overriding with parameter constraints *)
    apply Forall2_length in Hforall2.
    symmetry.
    exact Hforall2.
Qed. *)

Lemma method_lookup_in_wellformed_inherited: forall CT C m mdef,
  wf_class_table CT ->
  C < dom CT ->
  FindMethodWithName CT C m mdef ->
  exists D ddef, base_subtype CT C D /\ find_class CT D = Some ddef /\ In mdef (methods (body ddef)) /\ wf_method CT D mdef.
Proof.
  intros CT C m mdef Hwf_ct Hdom Hlookup.
  induction C as [C IH] using lt_wf_ind.
  inversion Hlookup; subst.
  - (* FOM_Here case *)
    exists C, def.
    split; [apply base_refl; exact Hdom | split; [exact H | split]].
    + unfold gget_method in H1.
      apply find_some in H1.
      destruct H1 as [Hin _].
      (* rewrite <- H0. *)
      exact Hin.
    + eapply method_lookup_wf_class; eauto.
      unfold gget_method in H1.
      apply find_some in H1.
      destruct H1 as [Hin _].
      (* rewrite <- H0. *)
      exact Hin.
  - (* FOM_Super case *)
    assert (Hparent_lt : parent < C).
    {
      eapply parent_implies_strict_ordering; eauto.
      (* unfold parent_lookup. *)
      (* rewrite H. *)
      (* exact H3. *)
    }
    apply IH in H3; auto.
    destruct H3 as [D [ddef [Hsub [Hfind_D [Hin_D Hwf_D]]]]].
    exists D, ddef.
    split; [eapply base_trans; eauto | split; [exact Hfind_D | split; [exact Hin_D | exact Hwf_D]]].
    eapply base_extends; eauto.
    unfold parent_lookup.
    lia.
    
    unfold parent_lookup.
    rewrite H.
    exact H2.
    lia.
Qed.

Lemma method_name_unique_implies_equal : forall methods mdef1 mdef2,
  NoDup (map (fun mdef => mname (msignature mdef)) methods) ->
  In mdef1 methods ->
  In mdef2 methods ->
  mname (msignature mdef1) = mname (msignature mdef2) ->
  mdef1 = mdef2.
Proof.
  intros methods mdef1 mdef2 Hnodup Hin1 Hin2 Hname_eq.
  induction methods as [|h t IH].
  - (* methods = [] *)
    contradiction.
  - (* methods = h :: t *)
    simpl in Hnodup.
    inversion Hnodup; subst.
    simpl in Hin1, Hin2.
    destruct Hin1 as [Heq1 | Hin1_t], Hin2 as [Heq2 | Hin2_t].
    + (* Both are h *)
      rewrite <- Heq1, <- Heq2. reflexivity.
    + (* mdef1 = h, mdef2 in t *)
      exfalso.
      subst mdef1.
      apply H1.
      rewrite  Hname_eq.
      apply (in_map (fun mdef => mname (msignature mdef))).
      exact Hin2_t.
    + (* mdef1 in t, mdef2 = h *)
      exfalso.
      subst mdef2.
      apply H1.
      rewrite <- Hname_eq.
      apply (in_map (fun mdef => mname (msignature mdef))).
      exact Hin1_t.
    + (* Both in t *)
      apply IH; auto.
Qed.

Lemma wf_method_override_same_param_length_general: forall CT C mdef D supermdef,
  wf_class_table CT ->
  C < dom CT ->
  D < dom CT ->
  base_subtype CT C D ->
  FindMethodWithName CT C (mname (msignature mdef)) mdef ->
  FindMethodWithName CT D (mname (msignature mdef)) supermdef ->
  dom (mparams (msignature mdef)) = dom (mparams (msignature supermdef)).
Proof.
  intros CT C mdef D supermdef Hwf_ct Hcdom Hddom Hsub Hfind_C Hfind_D.
(* Find where each method is actually defined *)
assert (Hexists_C : exists E edef, base_subtype CT C E /\ find_class CT E = Some edef /\ In mdef (methods (body edef)) /\ wf_method CT E mdef).
{
  eapply method_lookup_in_wellformed_inherited; eauto.
}
destruct Hexists_C as [E [edef [Hsub_CE [Hfind_E [Hin_E Hwf_E]]]]].

assert (Hexists_D : exists F fdef, base_subtype CT D F /\ find_class CT F = Some fdef /\ In supermdef (methods (body fdef)) /\ wf_method CT F supermdef).
{
  eapply method_lookup_in_wellformed_inherited; eauto.
}
destruct Hexists_D as [F [fdef [Hsub_DF [Hfind_F [Hin_F Hwf_F]]]]].

(* Case analysis: are E and F the same class? *)
destruct (Nat.eq_dec E F) as [HeqEF | HneqEF].
- (* E = F: methods are in the same class *)
  subst F.
  assert (Heq_def : edef = fdef).
  {
    rewrite Hfind_E in Hfind_F.
    injection Hfind_F as Heq.
    exact Heq.
  }
  subst fdef.
  (* Both methods are in the same class with same name - they must be the same *)
  assert (Heq_mdef : mdef = supermdef).
  {
    (* Use method name uniqueness within a class *)
    assert (Hname_C : mname (msignature mdef) = mname (msignature supermdef)).
    {
      have Hname1 := find_method_with_name_consistent CT C (mname (msignature mdef)) mdef Hfind_C.
      have Hname2 := find_method_with_name_consistent CT D (mname (msignature mdef)) supermdef Hfind_D.
      symmetry.
      exact Hname2.
    }

    (* Get well-formed class *)
    assert (Hwf_class : wf_class CT edef).
    {
      unfold wf_class_table in Hwf_ct.
      destruct Hwf_ct as [Hforall_wf _].
      eapply Forall_nth_error; eauto.
    }

    (* Extract NoDup property from well-formed class *)
    inversion Hwf_class; subst.
    - (* WFObjectDef case *)
      exfalso.
      rewrite H2 in Hin_E.
      simpl in Hin_E.
      exact Hin_E.
    - (* WFOtherDef case *)
      destruct H3 as [_ [_ [Hnodup _]]].
      (* Use NoDup and same name to prove equality *)
      eapply method_name_unique_implies_equal; eauto.
  }
  rewrite Heq_mdef. reflexivity.
  - (* E ≠ F: methods are in different classes, use override relationship *)
  assert (Hsub_EF : base_subtype CT E F).
  {
    (* If mdef is in E and supermdef is in F with same name, *)
    (* and C finds mdef while D finds supermdef, *)
    (* then E must be a superclass of F in the inheritance chain *)
    
    (* Since C <: E and C <: D, and D <: F, *)
    (* if E ≠ F, then either E <: F or F <: E *)
    (* But since FindMethodWithName from C gets mdef (in E) *)
    (* and FindMethodWithName from D gets supermdef (in F), *)
    (* and C <: D, we must have E <: D <: F *)
    
    (* Use the fact that method lookup follows inheritance chain *)
    admit. (* Need lemma about method lookup inheritance ordering *)
  }
  admit.
Admitted.

Lemma wf_method_override_rettype_base_equal: forall CT C mdef D supermdef,
  wf_class_table CT ->
  C < dom CT ->
  D < dom CT ->
  base_subtype CT C D ->
  FindMethodWithName CT C (mname (msignature mdef)) mdef ->
  FindMethodWithName CT D (mname (msignature mdef)) supermdef ->
  sctype (mret (msignature mdef)) = sctype (mret (msignature supermdef)).
Proof.
Admitted.

Lemma wf_method_override_paramstype_base_equal: forall CT C mdef D supermdef,
  wf_class_table CT ->
  C < dom CT ->
  D < dom CT ->
  base_subtype CT C D ->
  FindMethodWithName CT C (mname (msignature mdef)) mdef ->
  FindMethodWithName CT D (mname (msignature mdef)) supermdef ->
  Forall2 (fun mp smp => (sctype mp) = (sctype smp)) (mparams (msignature mdef)) (mparams (msignature supermdef)).
Proof.
Admitted.

Lemma wf_method_override_receiver_base_subtype: forall CT C mdef D supermdef,
  wf_class_table CT ->
  C < dom CT ->
  D < dom CT ->
  base_subtype CT C D ->
  FindMethodWithName CT C (mname (msignature mdef)) mdef ->
  FindMethodWithName CT D (mname (msignature mdef)) supermdef ->
  base_subtype CT (sctype (mreceiver (msignature mdef))) (sctype (mreceiver (msignature supermdef))).
Proof.
Admitted.

Lemma wf_method_override_reciever_qualifer_subtype: forall CT C mdef D supermdef,
  wf_class_table CT ->
  C < dom CT ->
  D < dom CT ->
  base_subtype CT C D ->
  FindMethodWithName CT C (mname (msignature mdef)) mdef ->
  FindMethodWithName CT D (mname (msignature mdef)) supermdef ->
  q_subtype (vpa_mutabilty (sqtype (mreceiver (msignature mdef))) (sqtype (mreceiver (msignature supermdef)))) (sqtype (mreceiver (msignature mdef))) .
Proof.
Admitted.

Lemma wf_method_override_return_qualifer_subtype: forall CT C mdef D supermdef,
  wf_class_table CT ->
  C < dom CT ->
  D < dom CT ->
  base_subtype CT C D ->
  FindMethodWithName CT C (mname (msignature mdef)) mdef ->
  FindMethodWithName CT D (mname (msignature mdef)) supermdef ->
  q_subtype  (sqtype (mret (msignature mdef))) (vpa_mutabilty (sqtype (mreceiver (msignature mdef))) (sqtype (mret (msignature supermdef)))).
Proof.
Admitted.

Lemma wf_method_override_params_qualifer_subtype: forall CT C mdef D supermdef,
  wf_class_table CT ->
  C < dom CT ->
  D < dom CT ->
  base_subtype CT C D ->
  FindMethodWithName CT C (mname (msignature mdef)) mdef ->
  FindMethodWithName CT D (mname (msignature mdef)) supermdef ->
  Forall2 (fun mp smp => q_subtype (sqtype mp) (vpa_mutabilty (sqtype (mreceiver (msignature mdef))) (sqtype smp))) (mparams (msignature mdef)) (mparams (msignature supermdef)).
Proof.
Admitted.

Lemma override_local_precedence : forall parent_methods own_methods m mdef,
  gget_method own_methods m = Some mdef ->
  gget_method (override parent_methods own_methods) m = Some mdef.
Proof.
  intros parent_methods own_methods m mdef Hown.
  unfold override.
  unfold gget_method in *.
  apply find_app.
  exact Hown.
Qed.

Lemma collect_fields_consistent_through_subtyping : forall CT C D fields1 fields2 f fdef1 fdef2,
  wf_class_table CT ->
  base_subtype CT C D ->
  CollectFields CT C fields1 ->
  CollectFields CT D fields2 ->
  gget fields1 f = Some fdef1 ->
  gget fields2 f = Some fdef2 ->
  fdef1 = fdef2.
Proof.
Admitted.

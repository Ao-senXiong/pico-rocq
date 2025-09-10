Require Import Syntax Subtyping ViewpointAdaptation Helpers.
Require Import String.
Require Import List.
Import ListNotations.

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
    unfold parent in H1.
    rewrite Hfind in H1.
    simpl in H1.
    exact H1.
    unfold parent in H1.
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

(* Method def lookup *)
Fixpoint mdef_lookup (fuel : nat) (CT : class_table) (C : class_name) (m : method_name) : option method_def :=
  match fuel with
  | O => None
  | S fuel' =>
    match find_class CT C with
    | None => None
    | Some def =>
      match find (fun mdef => eq_method_name (mname (msignature mdef)) m)
                 (methods (body def)) with
      | Some mdef => Some mdef
      | None =>
        match super (signature def) with
        | None => None
        | Some superC => mdef_lookup fuel' CT superC m
        end
      end
    end
  end.

(* Method definition lookup  *)
Definition method_def_lookup (CT : class_table) (C : class_name) (m : method_name) : option method_def :=
  mdef_lookup (length CT) CT C m.

(* Method signature lookup *)
Definition method_sig_lookup (CT : class_table) (C : class_name) (m : method_name) : option (method_sig) :=
  match mdef_lookup (length CT) CT C m with
  | Some mdef => Some mdef.(msignature)
  | None => None
  end.

(* Method body lookup *)
Definition method_body_lookup (CT : class_table) (C : class_name) (m : method_name) : option method_body :=
  match mdef_lookup (length CT) CT C m with
  | Some mdef => Some mdef.(mbody)
  | None => None
  end.

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
  | ST_Call : forall CT sΓ x m y args argtypes Tx Ty m_sig,
                    (* sΓ0 sΓ1 mbody *)
      wf_senv CT sΓ ->
      static_getType sΓ x = Some Tx ->
      static_getType sΓ y = Some Ty ->
      static_getType_list sΓ args = Some argtypes ->
      method_sig_lookup CT (sctype Ty) m = Some m_sig ->
      x <> 0 -> (* x is not the receiver variable *)
      qualified_type_subtype CT (vpa_qualified_type (sqtype Ty) (mret m_sig)) Tx -> (* assignment subtype checking*)
      qualified_type_subtype CT Ty (vpa_qualified_type (sqtype Ty) (mreceiver m_sig)) -> (* receiver subtype checking *) 
      Forall2 (fun arg T => qualified_type_subtype CT arg (vpa_qualified_type (sqtype Ty) T)) argtypes (mparams m_sig) -> (* argument subtype checking *)
      stmt_typing CT sΓ (SCall x m y args) sΓ

  (* Cast statement *)
  (* | S_Cast : forall CT Γ x q C y,
      static_lookup Γ y = Some (ctype (Build_qualified_type (q_f_proj q) C)) ->
      wf_stypeuse CT q C ->
      stmt_eval CT Γ (SCast x q C y) Γ *)

  (* Sequence of statements *)
  | ST_Seq : forall CT sΓ s1 sΓ' s2 sΓ'',
      stmt_typing CT sΓ s1 sΓ' ->
      stmt_typing CT sΓ' s2 sΓ'' ->
      stmt_typing CT sΓ (SSeq s1 s2) sΓ''
.

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
  (* Other case: super class and this class both have fields *)
  | WFConstructorInductive: forall CT C ctor superclass_name super_fields_def this_fields_def super_bound supercons_sig,
    parent CT C = Some superclass_name ->
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
    Forall2 (fun arg T => qualified_type_subtype CT arg (vpa_qualified_type q_c T)) stypes super_full_params ->
    wf_constructor CT C ctor
  .

Definition find_overriding_method (CT : class_table) (C: class_name) (m: method_sig) : option method_sig :=
  match mdef_lookup (length CT) CT C (mname m) with
  | Some mdef =>
      let msig := msignature mdef in
      if eq_method_name (mname msig) (mname m)
         (* && forallb2 (fun C1 C2 =>
          eq_class_name C1.(sctype) C2.(sctype)
         ) (mparams msig) (mparams m)
         && eq_class_name (sctype (mret msig)) (sctype (mret m)) *)
      then Some msig
      else None
  | None => None
  end.

(* Well-formedness of method *)
Inductive wf_method : class_table -> class_name -> method_def -> Prop :=
  (* Method is not overriding *)
  | WFPlainMethod: forall CT C mdef mbody sΓ sΓ' mbodyrettype,
  find_overriding_method CT C (msignature mdef) = None -> (* No overriding method *)
  let msig := msignature mdef in
  let methodbody := mbody mdef in
  let mbodystmt := mbody_stmt methodbody in
  sΓ = msig.(mreceiver) :: msig.(mparams) ->
  stmt_typing CT sΓ mbodystmt sΓ' ->
  let mbodyretvar := mreturn methodbody in
  mbodyretvar < dom sΓ' -> (* Return variable is in the static environment after method body *)
  nth_error sΓ' mbodyretvar = Some mbodyrettype ->
  let methodreturntype := mret msig in
  qualified_type_subtype CT mbodyrettype methodreturntype -> 
  wf_method CT C mdef

  (* Method is overrding *)
  | WFOverridingMethod: forall CT C mdef mbody sΓ sΓ' mbodyrettype supermsig,
  find_overriding_method CT C (msignature mdef) = Some supermsig ->
  let thismsig := msignature mdef in
  let this_method_return := mret thismsig in
  forallb2 (fun C1 C2 => eq_class_name C1.(sctype) C2.(sctype)) (mparams thismsig) (mparams supermsig)
  && eq_class_name (sctype (mret thismsig)) (sctype (mret supermsig)) ->
  let methodbody := mbody mdef in
  let mbodystmt := mbody_stmt methodbody in
  sΓ = thismsig.(mreceiver) :: thismsig.(mparams) ->
  stmt_typing CT sΓ mbodystmt sΓ' ->
  let mbodyretvar := mreturn methodbody in
  mbodyretvar < dom sΓ' -> (* Return variable is in the static environment after method body *)
  nth_error sΓ' mbodyretvar = Some mbodyrettype ->
  qualified_type_subtype CT mbodyrettype this_method_return -> 
  let this_method_parameters := mparams thismsig in
  let super_method_parameters := mparams supermsig in
  length this_method_parameters = length super_method_parameters -> (* Same number of parameters *)
  (* Check parameter type contravariant *)
  Forall2 (fun T1 T2 => qualified_type_subtype CT (vpa_qualified_type (sqtype (mreceiver thismsig)) T1) (vpa_qualified_type (sqtype (mreceiver thismsig)) T2)) super_method_parameters this_method_parameters ->
  (* Check reciever type contravariant *)
  qualified_type_subtype CT (vpa_qualified_type (sqtype (mreceiver thismsig)) (mreceiver supermsig)) (mreceiver thismsig) ->
  let super_method_return := mret supermsig in
  (* Check return type covariant *)
  qualified_type_subtype CT (vpa_qualified_type (sqtype (mreceiver thismsig)) this_method_return) (vpa_qualified_type (sqtype (mreceiver thismsig)) super_method_return) ->
  wf_method CT C mdef
.

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
  wf_constructor CT C (constructor bod) /\
  Forall (wf_method CT C) (methods bod) /\
  match bound CT superC with
  | Some q_super => 
      exists fs, CollectFields CT C fs /\
      vpa_mutabilty qC q_super = qC /\ 
      Forall (wf_field CT) fs
  | None => 
      CollectFields CT C []
  end
  ->
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
  (forall i def, find_class CT i = Some def -> 
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
    destruct Hbound_case as [fs [Hcf_fs [Hvpa Hwf_fs]]].
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
Require Import Syntax Subtyping ViewpointAdaptation Helpers.
Require Import String.
Require Import List.
Import ListNotations.

(* STATIC HELPER FUNCTIONS *)

(* Class bound look up in the class table  *)
Definition bound (CT : class_table) (C : class_name) : option q_c :=
  match find_class CT C with
  | Some decl => Some (class_qualifier (signature decl))
  | None => None
  end.

(* Parent class lookup in the class table *)
Definition parent (CT : class_table) (C : class_name) : option class_name :=
  match find_class CT C with
  | Some def => super (signature def)
  | None => None
  end.

(* Collect fields of a class and its superclasses, with fuel to prevent infinite loops *)
Fixpoint collect_fields_fuel (fuel : nat) (CT : class_table) (C : class_name) : list field_def :=
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
  | Some q_c_val => q_subtype (vpa_mutabilty q1 (q_c_proj (q_c_val))) q1
  | None => False (* or False, depending on your semantics *)
  end.

(* Well-formedness of field *)
Definition wf_field (CT : class_table) (f: field_def) : Prop :=
  wf_stypeuse CT (q_f_proj (mutability (ftype f))) (f_base_type (ftype f)).

(* Well-formedness of static environment *)
Definition wf_senv (CT : class_table) (sΓ : s_env) : Prop :=
  (* The first variable is the receiver and should always be present *)
  dom sΓ > 0 /\
  Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) sΓ.

(* EXPRESSION TYPING RULES *)
Inductive expr_has_type : class_table -> s_env -> expr -> qualified_type -> Prop :=

  (* Null typing *)
  | ET_Null : forall CT Γ T Object_name,
      wf_senv CT Γ ->
      expr_has_type CT Γ ENull (Build_qualified_type T Object_name)

  (* Variable typing *)
  | ET_Var : forall CT Γ x T,
      wf_senv CT Γ ->
      static_getType Γ x = Some T ->
      expr_has_type CT Γ (EVar x) T
      
  (* Field access typing *)    
  | ET_Field : forall CT Γ x T fT f,
      wf_senv CT Γ ->
      static_getType Γ x = Some T ->
      sf_def CT (sctype T) f = Some fT ->
      expr_has_type CT Γ (EField x f) (Build_qualified_type (q_f_proj (mutability (ftype fT))) (f_base_type (ftype fT)))
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
      sΓ' = (T :: sΓ) ->
      (* The local variable is added to the static environment *)
      stmt_typing CT sΓ (SLocal T x) sΓ'

  (* Variable assignment *)
  | ST_VarAss : forall CT sΓ x e T T',
      wf_senv CT sΓ ->
      expr_has_type CT sΓ e T ->
      static_getType sΓ x = Some T' ->
      qualified_type_subtype CT T T' ->
      stmt_typing CT sΓ (SVarAss x e) sΓ

  (* Field write *)
  | ST_FldWrite : forall CT sΓ x f y Tx Ty fieldT a,
      wf_senv CT sΓ ->
      static_getType sΓ x = Some Tx ->
      static_getType sΓ y = Some Ty ->
      sf_def CT (sctype Tx) f = Some fieldT ->
      sf_assignability CT (sctype Tx) f = Some a ->
      qualified_type_subtype CT Ty (vpa_qualified_type (sqtype Tx) (Build_qualified_type (q_f_proj (mutability (ftype fieldT))) (f_base_type (ftype fieldT)))) ->
      vpa_assignability (sqtype Tx) a = Assignable ->
      stmt_typing CT sΓ (SFldWrite x f y) sΓ

  (* Object creation *)
  | S_New : forall CT sΓ x Tx q C args argtypes n1 consig,
      wf_senv CT sΓ ->
      static_getType sΓ x = Some Tx ->
      static_getType_list sΓ args = Some argtypes ->
      constructor_sig_lookup CT C = Some consig ->
      length consig.(sparams) = n1 ->
      Forall2 (fun arg T => qualified_type_subtype CT arg (vpa_qualified_type (q_c_proj q) T)) (firstn n1 argtypes) consig.(sparams) ->
      Forall2 (fun arg T => qualified_type_subtype CT arg (vpa_qualified_type (q_c_proj q) T)) (skipn n1 argtypes) consig.(cparams) ->
      stmt_typing CT sΓ (SNew x q C args) sΓ

  (* Method call *)
  | ST_Call : forall CT sΓ x m y args argtypes Tx Ty m_sig,
      wf_senv CT sΓ ->
      static_getType sΓ x = Some Tx ->
      static_getType sΓ y = Some Ty ->
      static_getType_list sΓ args = Some argtypes ->
      method_sig_lookup CT (sctype Ty) m = Some m_sig ->
      qualified_type_subtype CT (vpa_qualified_type (sqtype Ty) (mret m_sig)) Tx -> (* assignment subtype checking*)
      qualified_type_subtype CT Ty (vpa_qualified_type (sqtype Ty) (mreciever m_sig)) -> (* receiver subtype checking *) 
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

Inductive wf_constructor : class_table -> class_name -> constructor_def -> Prop :=

  (* Object case + no fields class *)
  (* | WFObjectConstructor : forall CT C ctor,
    fields CT C = [] -> (* Object root class's constructor assumed to be wellformed, other checks should be done at WFClass *)
    constructor_def_lookup CT C = Some ctor ->
    ctor.(csignature).(sparams) = [] -> (* No parameters for Object + no field class constructor *)
    ctor.(csignature).(cparams) = [] -> (* No parameters for Object + no field class constructor *)
    wf_constructor CT C ctor

  (* Only the this class have fields *)
  | WFSuperObjectConstructor: forall CT C ctor superclass_name this_fields this_params,
    parent CT C = Some superclass_name ->
    constructor_def_lookup CT C = Some ctor ->
    let sig := csignature ctor in
    let q_c := cqualifier sig in
    let ccon := ctor_type sig in
    (* constructor mutability qualifier is same as bound; Constructor name is the same as class name *)
    Some q_c = bound CT C /\ ccon = C -> 
    ctor.(csignature).(sparams) = [] -> (* No parameters for Object + no field class constructor *)
    fields CT superclass_name = [] -> (* Superclass don't have fields *)
    fields CT C = this_fields -> (* This class has fields *)
    ctor.(csignature).(cparams) = this_params  -> 
    (* Parameter types are wellformed *)
    Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) (this_params) ->
    length this_fields = length this_params -> (* The number of fields and parameters are the same *)
    (* Constructor body well-formedness *)
    let ctypes := cparams sig in 
    let body := cbody ctor in
    let list_assignment := assignments body in
    (* 1. The assignments in this constructor has the same length as fields for this class *)
    Forall (fun '(f1, f2) =>
    match sf_mutability CT C f1, sf_base CT C f1, nth_error ctypes f2 with
    | Some mf, Some Cf, Some T2 => qualified_type_subtype CT (vpa_qualified_type (q_c_proj q_c) (Build_qualified_type (q_f_proj mf) Cf)) (vpa_qualified_type (q_c_proj q_c) T2)
    | _, _, _ => False
    end) list_assignment ->
    wf_constructor CT C ctor *)

  (* Other case: super class and this class both have fields *)
  | WFConstructorInductive: forall CT C ctor superclass_name super_fields_def this_fields_def super_bound supercons_sig,
    parent CT C = Some superclass_name ->
    constructor_def_lookup CT C = Some ctor ->
    let sig := csignature ctor in
    let q_c := cqualifier sig in
    let ccon := ctor_type sig in
    (* constructor mutability qualifier is same as bound; Constructor name is the same as class name *)
    Some q_c = bound CT C /\ ccon = C -> 
    (* Parameter types are wellformed *)
    Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) (sparams sig) ->
    Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) (cparams sig) ->
    fields CT superclass_name = super_fields_def -> (* This class has fields *)
    fields CT C = this_fields_def -> (* This class has fields *)
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
    match sf_mutability CT C f1, sf_base CT C f1, nth_error ctypes f2 with
    | Some mf, Some Cf, Some T2 => qualified_type_subtype CT (vpa_qualified_type (q_c_proj q_c) (Build_qualified_type (q_f_proj mf) Cf)) (vpa_qualified_type (q_c_proj q_c) T2)
    | _, _, _ => False
    end) list_assignment ->
    (* 4 Constructor supercall wellformed *)
    (* 4.1 Bound compatibility *)
    bound CT superclass_name = Some super_bound ->
    let stypes := sparams sig in
    vpa_mutabilty (q_c_proj q_c) (q_c_proj super_bound) = (q_c_proj q_c) /\
    (* 4.2 Argument types are adapted subtype of Parameter type of super constructor *)
    constructor_sig_lookup CT superclass_name = Some supercons_sig -> 
    let super_full_params := sparams supercons_sig ++ cparams supercons_sig in 
    length super_full_params = length stypes ->
    Forall2 (fun arg T => qualified_type_subtype CT arg (vpa_qualified_type (q_c_proj q_c) T)) stypes super_full_params ->
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
  let methodbody := mbody mdef in
  let mbodystmt := mbody_expr methodbody in
  stmt_typing CT sΓ mbodystmt sΓ' ->
  let mbodyretvar := mreturn methodbody in
  mbodyretvar < dom sΓ' -> (* Return variable is in the static environment after method body *)
  nth_error sΓ' mbodyretvar = Some mbodyrettype ->
  let msignature := msignature mdef in
  let methodreturntype := mret msignature in
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
  let mbodystmt := mbody_expr methodbody in
  stmt_typing CT sΓ mbodystmt sΓ' ->
  let mbodyretvar := mreturn methodbody in
  mbodyretvar < dom sΓ' -> (* Return variable is in the static environment after method body *)
  nth_error sΓ' mbodyretvar = Some mbodyrettype ->
  qualified_type_subtype CT mbodyrettype this_method_return -> 
  let this_method_parameters := mparams thismsig in
  let super_method_parameters := mparams supermsig in
  length this_method_parameters = length super_method_parameters -> (* Same number of parameters *)
  (* Check parameter type contravariant *)
  Forall2 (fun T1 T2 => qualified_type_subtype CT (vpa_qualified_type (sqtype (mreciever thismsig)) T1) (vpa_qualified_type (sqtype (mreciever thismsig)) T2)) super_method_parameters this_method_parameters ->
  (* Check reciever type contravariant *)
  qualified_type_subtype CT (vpa_qualified_type (sqtype (mreciever thismsig)) (mreciever supermsig)) (mreciever thismsig) ->
  let super_method_return := mret supermsig in
  (* Check return type covariant *)
  qualified_type_subtype CT (vpa_qualified_type (sqtype (mreciever thismsig)) this_method_return) (vpa_qualified_type (sqtype (mreciever thismsig)) super_method_return) ->
  wf_method CT C mdef
.

(* Well-formedness of class *)
Inductive wf_class : class_table -> class_def -> Prop :=

(* Object class *)
| WFObjectDef: forall CT cdef class_name,
  cdef.(signature).(super) = None ->
  q_c_proj(cdef.(signature).(class_qualifier)) = RDM ->
  cdef.(body).(Syntax.fields) = [] ->
  cdef.(body).(methods) = [] ->
  cdef.(signature).(cname) = class_name ->
  wf_constructor CT class_name cdef.(body).(constructor) ->
  wf_class CT cdef

(* Other object : TODO how to prevent C extends D; D extends C can be checked by index *) 
| WFOtherDef: forall CT cdef superC thisC, 
  cdef.(signature).(super) = Some superC -> (* Not Object class *)
  cdef.(signature).(cname) = thisC ->
  thisC <> superC -> (* no self inheritance *)
  let sig := cdef.(signature) in
  let bod := cdef.(body) in
  let C := cname sig in
  let qC := class_qualifier sig in
  wf_constructor CT C (constructor bod) /\
  Forall (wf_method CT C) (methods bod) /\
  match bound CT superC, fields CT C with
    | Some q_super, fs =>
        vpa_mutabilty (q_c_proj qC) (q_c_proj q_super) = q_c_proj qC /\ Forall (wf_field CT) fs
    | None, [] => True
    | None, _ => False
  end
  ->
  wf_class CT cdef
.

(* Well-formedness of program  Aosen: I put it at the end because the main statement need to be well-typed*)
(* Definition WFProgram (p: program_def) : Prop :=
  Forall (fun decl => WFClass p.(classes) decl) p.(classes) . *)
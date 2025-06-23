Require Import String.
Require Import Coq.Sets.Ensembles.
From RecordUpdate Require Import RecordSet.
From RecordUpdate Require Import RecordUpdate.

(* ------------------SYNTAX------------------*)
Definition var : Type := nat.
Variant method_name : Type := Method_name(n: nat).
Variant class_name : Type := Class_name(n: nat).
(* Mutability qualifer *)
Inductive q : Type :=
  (* q_c *)
  | Mut
  | Imm
  | RDM
  (* q_f *)
  | Rd
  (* q_h *)
  | Lost
  | Bot.

Definition q_c := { x : q | x = Mut \/ x = Imm \/ x = RDM }.
Definition q_f := { x : q | x = Rd \/ x = Mut \/ x = Imm \/ x = RDM }.
Definition q_h := { x : q | x = Lost \/ x = Bot }.

(* canonical projection *)
Definition q_c_proj (x : q_c) : q := proj1_sig x.
Definition q_f_proj (x : q_f) : q := proj1_sig x.
Definition q_h_proj (x : q_h) : q := proj1_sig x.

(* Assignability qualifier *)
Inductive a : Type :=
  | Assignable
  | Final
  | RDA.

(* Definition r_a := { x : a | x = Assignable \/ x = Final}. *)

(* Canonical projection for assignability *)
(* Definition r_a_proj (x : r_a) : a := proj1_sig x. *)

(* Qualified type  *)
Record qualified_type := {
  sqtype: q; (* Type qualifier *)
  sctype: class_name; (* Class name *)
}.

Definition s_env := list qualified_type.

Inductive expr : Type :=
  | ENull : expr
  | EVar : var -> expr
  | EField : var -> var -> expr. (* x.f TODO should we change that to e.f? *)

Inductive stmt: Type :=
  | SSkip: stmt (* skip *)
  | SLocal: qualified_type -> var -> stmt (* T x*)
  | SVarAss: var -> expr -> stmt (* x = e *)
  | SFldWrite: var -> var -> var -> stmt (* x.f = y *)
  | SNew: var -> q_c -> class_name -> list var -> stmt (* x = new q_c C(y1, ..., yn) *)
  | SCall: var -> method_name -> var -> list var -> stmt (* x = y.m(z1, ..., zn) *)
  (* | SCast: var -> q -> class_name -> var -> stmt x = (q C) y  *)
  (* | SUpcast: var -> q_c -> class_name -> var -> stmt x = (T) y  *)
  | SSeq: stmt -> stmt -> stmt. (* s1; s2 *)

Record field_type := {
  assignability: a;
  mutability: q_f;
  f_base_type : class_name;
}.

(* Field declaration with assignability and mutability *)
Record field_def := {
  ftype : field_type; (* Field type *)
  fname : var; (* Field name *)
}.

Record constructor_body :={
  super_call: list var; (* Super(f1, ..., fn)*)
  assignments: list (var * var); (* this.f1 = f_1; ...; this.fn = f_n *)
}.

Record constructor_sig := {
  cqualifier: q_c; (* Mutable, Immutable, or RDM *)
  ctor_type : class_name; (* Class name *)
  sparams : list qualified_type; (* T x1, ..., T xn Parameters for super call *)
  cparams : list qualified_type; (* T y1, ..., T yn Parameters for field assignment *)
}.

Record constructor_def := {
  csignature : constructor_sig; (* Constructor signature *)
  cbody : constructor_body;
}.

Record method_body := {
  mbody_expr: stmt; (* Method body expression *)
  mreturn: var; (* Return variable *)
}.

Record method_sig := {
  mret : qualified_type; (* Return type *)
  mname : method_name; (* Method name *)
  mreciever: qualified_type; (*T this*)
  mparams : list qualified_type; (* T x1, ..., T xn *)
}.

Record method_def := {
  msignature : method_sig; (* Method signature *)
  mbody : method_body; (* Method body *)
}.

Record class_body := {
  fields : list field_def; (* Class fields *)
  constructor: constructor_def; (* Constructor declaration *)
  methods : list method_def; (* Class methods *)
}.

Record class_sig := {
  class_qualifier : q_c; (* Mutable, Immutable, or RDM *)
  cname : class_name; (* Class name *)
  super : option class_name; (* Superclass name *)
}.

Record class_def := {
  signature : class_sig; (* Class signature *)
  body : class_body; (* Class body *)
}.

Record program_def := {
  classes: list class_def; (* List of class declarations *)
  main_statement: stmt; (* Main statement *)
}.

(* Class table is a list of class declarations *)
Definition class_table := list class_def.

(* ------------------RUNTIME MODEL------------------*)

(* Initialization state *)
(* Inductive init: Type := 
  | initing
  | inited. *)

(* Runtime mutability type *)
Definition q_r := { x : q | x = Mut \/ x = Imm }.
Definition q_r_proj (x : q_r) : q := proj1_sig x.

Definition q_project_q_r (q : q) : option q_r :=
  match q with
  | Mut => Some (exist _ Mut (or_introl eq_refl))
  | Imm => Some (exist _ Imm (or_intror eq_refl))
  | _ => None
  end.

(* Static qualified type *)
(* Runtime type *)
Record runtime_type := mkruntime_type {
  rqtype: q_r; (* Runtime mutability *)
  rctype: class_name; (* Class name *)
}.

(* Convert runtime type to static qualified type *)
Definition runtime_type_to_qualified_type (rt : runtime_type) : qualified_type :=
  {| sqtype := q_r_proj (rqtype rt); sctype := rctype rt |}.

(* Memory address *)
Definition Loc : Type := nat.

(* Runtime value *)
Inductive value : Type :=
  | Null_a : value
  | Iot: Loc -> value.

(* Field mapping *)
Definition fields_mapping := list value. 
Definition var_mapping   := list value.

Record r_env := mkr_env {
  vars: var_mapping; (* Variable mapping *)
  (* Initialization state *)
  (* init_state: init; *)
}.

(* Runtime object *)
Record Obj := mkObj {
  rt_type: runtime_type; (* Runtime type *)
  fields_map: fields_mapping; (* Field mapping *)
}.

Definition heap          := list Obj.
Definition LocSet        := Ensemble Loc.


(* AOSEN: just a test *)
(* Instance settable_r_env : Settable _ :=
  mkSettable (generate_setters mkr_env vars init_state). *)
Record test := mktest {
  abc: nat;
  bcd: nat;
}.

Definition example_env := mktest 42 1.

Definition updated_env := example_env <|abc := 100|>.
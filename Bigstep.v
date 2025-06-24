From Coq Require Import Lia.
Require Import List.
Import ListNotations.
Require Import Syntax Typing Subtyping ViewpointAdaptation Helpers.
Require Import String.
Require Import Coq.Sets.Ensembles.
From RecordUpdate Require Import RecordUpdate.
Require Import Coq.Logic.Classical_Prop.

(* ------------------RUNTIME H ELPER FUNCTION------------------*)
(* The first element should also be a Loc because that is the receiver type*)
Definition get_this_var_mapping (vm : var_mapping) : option Loc :=
  match vm with
  | [] => None
  | ι :: _ => 
    match ι with
    | Null_a => None
    | Iot loc => Some loc
    end
  end.

(* Get the runtime mutability type of a Loc *)
Definition r_muttype (h: heap) (ι: Loc) : option q_r :=
  match getObj h ι with
  | None => None
  | Some o => Some (rqtype (rt_type o))
  end.

(* Get the runtime class name of a Loc *)
Definition r_basetype (h: heap) (ι: Loc) : option class_name :=
  match getObj h ι with
  | None => None
  | Some o => Some (rctype (rt_type o))
  end.

(* Get the runtime type of a Loc *)
Definition r_type (h: heap) (ι: Loc) : option runtime_type :=
  match getObj h ι with
  | None => None
  | Some o => Some (rt_type o)
  end.

(* Get the runtime object at the field f. find the object on the heap 2. get the field mapping 3. return the object *)
(* Definition field_obj (h: heap) (ι: Loc) (f: Loc) : option Obj :=
  match getObj h ι with
  | None => None
  | Some o =>
      match getAVal (fields_map o) f with
      | None => None
      | Some v =>
          match v with
          | Null_a r_a => None
          | Iot r_a loc =>
              match getObj h loc with
              | None => None
              | Some o' => Some o'
              end
          end
      end
  end. *)

(* Determine whether an assignment should be allowed *)
(* Definition can_assign (CT: class_table) (h: heap) (ι: Loc) (f: var) : bool :=
  match getObj h ι with
  | Some o =>
      match getAVal o.(fields_map) f with
      | Some (a, _) =>
          match a with
          | Assignable => true
          | _ => false
          end
      | None => false
      end
  | None => false
  end. *)
Definition can_assign (CT: class_table) (rΓ: r_env) (h: heap) (ι: Loc) (f: var) : bool :=
  match r_muttype h ι, r_basetype h ι with
  | Some q, Some c =>
    match sf_assignability CT c f with
    | Some a =>
        (* match rΓ.(init_state), vpa_assignability (q_r_proj q) a with
        (* | initing, _ => true *)
        | _, Assignable => true
        | _, _ => false
        end *)
        match vpa_assignability (q_r_proj q) a with
        (* | initing, _ => true *)
        | Assignable => true
        |  _ => false
        end
    | None => false
    end
  | _, _ => false
  end.

Definition update_field (h: heap) (ι: Loc) (f: var) (v: value) : heap :=
  match getObj h ι with
  | None => h
  | Some o =>
      let new_fields := update f v o.(fields_map) in
      let new_obj := o <| fields_map := new_fields |>
      in update ι new_obj h
  end.

(* ------------------RUNTIME WELLFORMEDNESS RULES------------------*)
(* Wellformed Runtime Type use  *)
Definition wf_rtypeuse (CT: class_table) (q: q_r) (c: class_name) : Prop :=
  match (bound CT c) with
  | None => False
  | Some q' =>
      match (vpa_mutabilty (q_r_proj q) (q_c_proj q')) with
      | q => True
      (* | _ => False TODO: why redudent? *)
      end
  end.

(* Wellformed Runtime Object: an object is well-formed if itself and its fields' type are well formed *)
Definition wf_obj (CT: class_table) (h: heap) (ι: Loc) : Prop :=
  match getObj h ι with
  | None => False
  | Some o =>
      wf_rtypeuse CT (rt_type o).(rqtype) (rt_type o).(rctype) /\
      Forall (fun v =>
        match v with
        | Null_a => True
        | Iot loc =>
            match getObj h loc with
            | None => False
            | Some o' => wf_rtypeuse CT (rt_type o').(rqtype) (rt_type o').(rctype)
            end
        end) (fields_map o)
  end.

(* Wellformed Runtime environment: a rΓ is well formed if for all variable in its domain, it maps to null_a or a value in the domin of heap *)
Definition wf_renv (CT: class_table) (rΓ: r_env) (h: heap) : Prop :=
  Forall (fun value =>
    match value with
    | Null_a => True
    | Iot loc =>
        match getObj h loc with
        | None => False
        | Some _ => True
        end
    end) rΓ.(vars).

(* Wellformed Runtime Heap: a heap is well-formed if all objects in it are well-formed *)
Definition wf_heap (CT: class_table) (h: heap) : Prop :=
    forall (ι : Loc),
    ι < (List.length h) ->
    wf_obj CT h ι.

(* Wellformed Runtime Typable: the runtime type of the address is subtype of q_this viewpoint adapting the static type *)
Definition wf_r_typable (CT: class_table) (rΓ: r_env) (h: heap) (ι: Loc) (sqt: qualified_type) : Prop :=
  match r_type h ι,  get_this_var_mapping (rΓ.(vars)) with
  | Some rqt, Some ι' =>
    match r_muttype h ι' with
    | Some q =>
      qualified_type_subtype CT (runtime_type_to_qualified_type rqt) (vpa_qualified_type (q_r_proj q) sqt) 
    | _ => False
    end  
  | _, _ => False
  end.

(* Wellformed Runtime Config: if (1) heap is well formed (2) static env is well formed (3) runtime env is well formed (4) the static env and run time env corresponds  *)
Definition wf_r_config (CT: class_table) (sΓ: s_env) (rΓ: r_env) (h: heap)  : Prop :=
  (* class_def in CT are wellformed  *)
  Forall (wf_class CT) CT /\
  (* Heap is well-formed *)
  wf_heap CT h /\
  (* Runtime environment is well-formed *)
  wf_renv CT rΓ h /\
  (* Static environment is well-formed *)
  wf_senv CT sΓ /\
  (* Additional invariant required by the proof *)
  (* (forall x, static_lookup sΓ x = None -> getVal (vars rΓ) x = None) /\ *)
  (* Static and runtime environment correspond *)
  List.length sΓ = List.length rΓ.(vars) /\
  forall i, i < List.length sΓ ->
  forall sqt,
    nth_error sΓ i = Some sqt ->
    match getVal rΓ.(vars) i with
    | Some (Iot loc) => wf_r_typable CT rΓ h loc sqt
    | Some Null_a => True
    | None => False
    end.

Lemma not_in_both_env: forall CT sΓ rΓ h,
    List.length sΓ = List.length rΓ.(vars)->
    forall i, i < List.length sΓ ->
    forall sqt, nth_error sΓ i = Some sqt ->
    match getVal rΓ.(vars) i with
    | Some (Iot loc) => wf_r_typable CT rΓ h loc sqt
    | Some Null_a => True
    | None => False
    end -> (forall x, x >= List.length sΓ -> static_lookup sΓ x = None -> getVal (vars rΓ) x = None).
Proof.
intros.
unfold static_lookup in H1.
destruct (lt_dec x (List.length sΓ)). 
  - (* x < dom sΓ *)
    unfold getVal.
    rewrite nth_error_None.
    rewrite <- H.
    lia.
  - (* x >= dom sΓ *)
    unfold getVal.
    rewrite nth_error_None.
    rewrite <- H.
    lia.
Qed.

Global Hint Resolve not_in_both_env: rch.

(* ------------------EVALUATION RULES------------------*)
(* Reserved Notation "'(' rΓ ',' h ')' '⟦'  s  '⟧'   '-->'  '(' rΓ',' h' ')'" (at level 80). *)

(* PICO expression evaluation *)
Inductive eval_expr : r_env -> heap -> expr -> value -> r_env -> heap -> Prop :=
  (* evalutate null expression  *)
  | EBS_Null : forall rΓ h,
      eval_expr rΓ h ENull Null_a rΓ h

  (* evaluate value expression *)
  | EBS_Val : forall rΓ h x v,
      getVal rΓ.(vars) x = Some v ->
      eval_expr rΓ h (EVar x) v rΓ h

  (* evaluate field access expression *)  
  | EBS_Field : forall rΓ h x f (v:value) v o,
      getObj h x = Some o ->
      getVal o.(fields_map) f = Some v ->
      eval_expr rΓ h (EField x f) v rΓ h
  .
Notation "'(' rΓ ',' h ')' '⟦'  e  '⟧'   '-->'  '(' v ',' rΓ' ',' h' ')'" := (eval_expr rΓ h e v rΓ' h') (at level 80).

(* PICO Statement evaluation *)
Inductive eval_stmt : r_env -> heap -> stmt -> r_env -> heap -> Prop :=
  (* evaluate skip statement *)
  | SBS_Skip : forall rΓ h,
      eval_stmt rΓ h SSkip rΓ h

  (* evaluate local variable declaration statement *)
  | SBS_Local : forall rΓ h T x,
      getVal rΓ.(vars) x = None ->
      eval_stmt rΓ h (SLocal T x)
      (* (rΓ <|vars := update (List.length rΓ.(vars) + 1) Null_a rΓ.(vars)|> <|init_state := rΓ.(init_state)|>) *)
      (rΓ <|vars := update (List.length rΓ.(vars) + 1) Null_a rΓ.(vars)|> )
      h

  (* evaluate variable assignment statement *)
  | SBS_Assign : forall rΓ h x e v1 v2,
      getVal rΓ.(vars) x = Some v1 ->
      eval_expr rΓ h e v2 rΓ h ->
      eval_stmt rΓ h (SVarAss x e)
      (* (rΓ <|vars := update x v2 rΓ.(vars)|> <|init_state := rΓ.(init_state)|>) *)
      (rΓ <|vars := update x v2 rΓ.(vars)|>)
      h

  (* evaluate field write statement *)
  | SBS_FldWrite: forall CT rΓ h x f y v1 lx v2 h',
      getVal rΓ.(vars) x = Some v1 ->
      v1 = Iot lx ->
      getVal rΓ.(vars) y = Some v2 ->
      can_assign CT rΓ h lx f = true ->
      h' = update_field h lx f v2 ->
      eval_stmt rΓ h (SFldWrite x f y) rΓ h'

  (* evaluate object creation statement *)
  | SBS_New: forall rΓ h x q_c c ys vals v l1 qthisr qthis qadapted o rΓ' h',
      getVal rΓ.(vars) 0 = Some v ->
      v = Iot l1 ->
      runtime_lookup_list rΓ ys = Some vals ->
      r_muttype h l1 = Some qthisr ->
      qthis = q_r_proj qthisr ->
      q_project_q_r (vpa_mutabilty qthis (q_c_proj q_c)) = Some qadapted -> 
      o = mkObj (mkruntime_type qadapted c) (vals) ->
      h' = update (List.length h + 1) o h ->
      rΓ' = rΓ <| vars := update x (Iot (List.length h')) rΓ.(vars) |> ->
      eval_stmt rΓ h (SNew x q_c c ys) rΓ' h'

  (* evaluate method call statement *)
  | SBS_Call: forall CT rΓ h x y m zs vals ly cy mbody mstmt mret retval h' rΓ' rΓ'' rΓ''',
    getVal rΓ.(vars) y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    method_body_lookup CT cy m = Some mbody ->
    mstmt = mbody.(mbody_expr) ->
    mret = mbody.(mreturn) ->
    runtime_lookup_list rΓ zs = Some vals ->
    (* rΓ' = mkr_env (Iot ly :: vals) rΓ.(init_state) -> *)
    rΓ' = mkr_env (Iot ly :: vals) ->
    eval_stmt rΓ' h mstmt rΓ'' h' ->
    getVal rΓ''.(vars) mret = Some retval ->
    rΓ''' = rΓ <| vars := update x retval rΓ.(vars) |> ->
    eval_stmt rΓ h (SCall x m y zs) rΓ''' h'

  (* evaluate sequence of statements *)
  | SBS_Seq: forall rΓ h s1 s2 rΓ' h' rΓ'' h'',
      eval_stmt rΓ h s1 rΓ' h' ->
      eval_stmt rΓ' h' s2 rΓ'' h'' ->
      eval_stmt rΓ h (SSeq s1 s2) rΓ'' h''
.

(* evaluate program *)

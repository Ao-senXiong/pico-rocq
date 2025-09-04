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
  match runtime_getObj h ι with
  | None => None
  | Some o => Some (rqtype (rt_type o))
  end.

(* Get the runtime class name of a Loc *)
Definition r_basetype (h: heap) (ι: Loc) : option class_name :=
  match runtime_getObj h ι with
  | None => None
  | Some o => Some (rctype (rt_type o))
  end.

(* Get the runtime type of a Loc *)
Definition r_type (h: heap) (ι: Loc) : option runtime_type :=
  match runtime_getObj h ι with
  | None => None
  | Some o => Some (rt_type o)
  end.

(* Determine whether an assignment should be allowed *)
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
  match runtime_getObj h ι with
  | None => h
  | Some o =>
      let new_fields := update f v o.(fields_map) in
      let new_obj := o <| fields_map := new_fields |>
      in update ι new_obj h
  end.

Lemma update_field_length : forall h ι f v,
  dom (update_field h ι f v) = dom h.
Proof.
  intros.
  unfold update_field.
  destruct (runtime_getObj h ι); [apply update_length | reflexivity].
Qed.

(* ------------------RUNTIME WELLFORMEDNESS RULES------------------*)
(* Wellformed Runtime Type use  *)
Definition wf_rtypeuse (CT: class_table) (q: q_r) (c: class_name) : Prop :=
  match (bound CT c) with
  | None => False
  | Some q' =>
      match (vpa_mutabilty (q_r_proj q) (q_c_proj q')) with
      | q => c < dom CT
      end
  end.

(* Wellformed Runtime Object: an object is well-formed if itself and its fields' type are well formed *)
Definition wf_obj (CT: class_table) (h: heap) (ι: Loc) : Prop :=
  match runtime_getObj h ι with
  | None => False
  | Some o =>
      (* The runtime type of the object is well-formed *)
      wf_rtypeuse CT (rt_type o).(rqtype) (rt_type o).(rctype) /\
      (* All field values are well-formed and have correct types *)
      let field_defs := collect_fields CT (rt_type o).(rctype) in
      List.length (fields_map o) = List.length field_defs /\
      Forall2 (fun v fdef => 
        match v with
        | Null_a => True
        | Iot loc => 
          match runtime_getObj h loc with
          | Some _ => 
            (* Field value exists and has correct type *)
            exists rqt, r_type h loc = Some rqt /\
            qualified_type_subtype CT 
              (runtime_type_to_qualified_type rqt)
              (Build_qualified_type 
                (q_f_proj (mutability (ftype fdef))) 
                (f_base_type (ftype fdef)))
          | None => False
          end
        end) (fields_map o) field_defs
  end.

(* Wellformed Runtime environment: a rΓ is well formed if for all variable in its domain, it maps to null_a or a value in the domin of heap *)
Definition wf_renv (CT: class_table) (rΓ: r_env) (h: heap) : Prop :=
  (* The first variable is the receiver and should always be present as non-null value *)
  dom rΓ.(vars) > 0 /\
  (exists iot, gget rΓ.(vars) 0 = Some (Iot iot)) /\
  Forall (fun value =>
    match value with
    | Null_a => True
    | Iot loc =>
        match runtime_getObj h loc with
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

Lemma vpa_qualified_type_sctype : forall q sqt,
  sctype (vpa_qualified_type q sqt) = sctype sqt.
Proof.
  intros.
  unfold vpa_qualified_type, sctype.
  destruct sqt.
  reflexivity.
Qed.

(* If a heap location is typable by T, its runtime object's base type must be a subtype of T0 *)
Lemma r_obj_subtype_sqt :
  forall CT rΓ h ι sqt o rt,
    wf_stypeuse CT (sqtype sqt) (sctype sqt) ->
    wf_r_typable CT rΓ h ι sqt ->
    wf_heap CT h ->
    runtime_getObj h ι = Some o ->
    rctype (rt_type o) = rt ->
    base_subtype CT rt (sctype sqt).
Proof.
  intros CT rΓ h ι sqt rqt H Hstypuse Hwf Hheap Hbasetype.
  assert (ι < dom h).
  {
    apply runtime_getObj_dom in Hbasetype.  exact Hbasetype.
  }
  unfold wf_r_typable in Hwf.
  remember (r_type h ι) as T eqn:Hr_type.
  destruct T as [rqt'|].
  -
    remember (get_this_var_mapping (vars rΓ)) as mthis eqn:Hgetthis.
    destruct mthis as [ι'|].
    + 
      destruct (r_muttype h ι') as [q|] eqn:Hmuttype.
      * 
        apply qualified_type_subtype_base_subtype with (CT := CT) in Hwf.
          intro Heq.
          unfold r_type in Hr_type.
          rewrite Hbasetype in Hr_type.
          injection Hr_type as Hrqt.
          rewrite <- Heq.
          rewrite <- Hrqt.
          rewrite vpa_qualified_type_sctype in Hwf.
          exact Hwf.
          unfold runtime_type_to_qualified_type, sctype.
          simpl.
          unfold r_type in Hr_type.
          rewrite Hbasetype in Hr_type.
          injection Hr_type as Hrqt.
          unfold wf_heap in Hheap.
          specialize Hheap with ι.
          specialize (Hheap H0).
          unfold wf_obj in Hheap.
          rewrite Hbasetype in Hheap.
          destruct Hheap as [Hrtypeuse Hrdom].
          unfold wf_rtypeuse in Hrtypeuse.
          destruct (bound CT (rctype (rt_type rqt))) as [q_c_val|] eqn:Hbound.
          -- rewrite Hrqt. exact Hrtypeuse.
          -- contradiction.
          -- 
          rewrite vpa_qualified_type_sctype.
          unfold wf_stypeuse in Hstypuse.
          unfold wf_stypeuse in Hstypuse.
          destruct (bound CT (sctype sqt)) as [q_c_val|] eqn:Hbound.
          ++ destruct Hstypuse as [_ Hdom].
            exact Hdom.
          ++ contradiction.
      * 
        exfalso. (* r_muttype should not be None if r_basetype is Some *)
        auto.
    +
      exfalso. (* get_this_var_mapping should not be None if r_basetype is Some *)
      auto.
  - 
    exfalso. (* r_type should not be None if r_basetype is Some *)
    auto.
Qed.


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
  (* Static and runtime environment correspond *)
  List.length sΓ = List.length rΓ.(vars) /\
  forall i, i < List.length sΓ ->
  forall sqt,
    nth_error sΓ i = Some sqt ->
    match runtime_getVal rΓ i with
    | Some (Iot loc) => wf_r_typable CT rΓ h loc sqt
    | Some Null_a => True
    | None => False
    end.

Lemma not_in_both_env: forall CT sΓ rΓ h,
    List.length sΓ = List.length rΓ.(vars)->
    forall i, i < List.length sΓ ->
    forall sqt, nth_error sΓ i = Some sqt ->
    match runtime_getVal rΓ i with
    | Some (Iot loc) => wf_r_typable CT rΓ h loc sqt
    | Some Null_a => True
    | None => False
    end -> (forall x, x >= List.length sΓ -> (static_getType sΓ x = None <-> runtime_getVal rΓ x = None)).
Proof.
intros.
unfold static_getType in H1.
destruct (lt_dec x (List.length sΓ)). 
  - (* x < dom sΓ *)
    unfold runtime_getVal.
    rewrite nth_error_None.
    rewrite <- H.
    lia.
  - (* x >= dom sΓ *)
    unfold runtime_getVal.
    rewrite nth_error_None.
    rewrite <- H.
    split.
    + lia.
    + unfold static_getType.
      apply nth_error_None.
Qed.

Global Hint Resolve not_in_both_env: rch.

(* ------------------EVALUATION RULES------------------*)
(* Reserved Notation "'(' rΓ ',' h ')' '⟦'  s  '⟧'   '-->'  '(' rΓ',' h' ')'" (at level 80). *)

(* Evaluation resulting state *)

Inductive eval_result :=
| OK : eval_result
| MUTATIONEXP: eval_result
| NPE : eval_result.

(* PICO expression evaluation *)
Inductive eval_expr : eval_result -> r_env -> heap -> expr -> value -> eval_result -> r_env -> heap -> Prop :=
  (* evalutate null expression  *)
  | EBS_Null : forall rΓ h,
      eval_expr OK rΓ h ENull Null_a OK rΓ h

  (* evaluate value expression *)
  | EBS_Val : forall rΓ h x v,
      runtime_getVal rΓ x = Some v ->
      eval_expr OK rΓ h (EVar x) v OK rΓ h

  (* evaluate field access expression *)  
  | EBS_Field : forall rΓ h x f v o v1,
      runtime_getVal rΓ x = Some (Iot v) ->
      runtime_getObj h v = Some o ->
      getVal o.(fields_map) f = Some v1 ->
      eval_expr OK rΓ h (EField x f) v1 OK rΓ h

  (* evaluate field access expression yields NPE *)
  | EBS_Field_NPE : forall rΓ h x f v,
      runtime_getVal rΓ x = Some (Null_a) ->
      eval_expr OK rΓ h (EField x f) v NPE rΓ h
  .
Notation "'(' rΓ ',' h ')' '⟦'  e  '⟧'   '-->'  '(' v ',' rΓ' ',' h' ')'" := (eval_expr rΓ h e v rΓ' h') (at level 80).

(* PICO Statement evaluation *)
Inductive eval_stmt : eval_result -> r_env -> heap -> stmt -> eval_result -> r_env -> heap -> Prop :=
  (* evaluate skip statement *)
  | SBS_Skip : forall rΓ h,
      eval_stmt OK rΓ h SSkip OK rΓ h

  (* evaluate local variable declaration statement *)
  | SBS_Local : forall rΓ h T x,
      runtime_getVal rΓ x = None ->
      eval_stmt OK rΓ h (SLocal T x) OK
      (* (rΓ <|vars := update (List.length rΓ.(vars) + 1) Null_a rΓ.(vars)|> <|init_state := rΓ.(init_state)|>) *)
      (rΓ <|vars := rΓ.(vars)++[Null_a] |> )
      h

  (* evaluate variable assignment statement *)
  | SBS_Assign : forall rΓ h x e v1 v2,
      runtime_getVal rΓ x = Some v1 ->
      eval_expr OK rΓ h e v2 OK rΓ h ->
      eval_stmt OK rΓ h (SVarAss x e) OK
      (* (rΓ <|vars := update x v2 rΓ.(vars)|> <|init_state := rΓ.(init_state)|>) *)
      (rΓ <|vars := update x v2 rΓ.(vars)|>)
      h

  | SBS_Assign_NPE : forall rΓ h x e v1 v2 rΓ' h',
    runtime_getVal rΓ x = Some v1 ->
    eval_expr OK rΓ h e v2 NPE rΓ h ->
    eval_stmt OK rΓ h (SVarAss x e) NPE
    (* (rΓ <|vars := update x v2 rΓ.(vars)|> <|init_state := rΓ.(init_state)|>) *)
    (* (rΓ <|vars := update x v2 rΓ.(vars)|>) *)
    rΓ'
    h'

  (* evaluate field write statement *)
  | SBS_FldWrite: forall CT rΓ h x f y lx o vf v2 h',
      runtime_getVal rΓ x = Some (Iot lx) ->
      runtime_getObj h lx = Some o ->
      getVal o.(fields_map) f = Some vf ->
      runtime_getVal rΓ y = Some v2 ->
      can_assign CT rΓ h lx f = true ->
      h' = update_field h lx f v2 ->
      eval_stmt OK rΓ h (SFldWrite x f y) OK rΓ h'

  (* evaluate field write statement NPE *)
  | SBS_FldWrite_NPE: forall rΓ h x f y rΓ' h',
      runtime_getVal rΓ x = Some (Null_a) ->
      eval_stmt OK rΓ h (SFldWrite x f y) NPE rΓ' h'

  (* evaluate object creation statement *)
  | SBS_New: forall rΓ h x (q_c:q_c) c ys vals l1 qthisr qthis qadapted o rΓ' h',
      runtime_getVal rΓ 0 = Some (Iot l1) ->
      runtime_lookup_list rΓ ys = Some vals ->
      r_muttype h l1 = Some qthisr ->
      qthis = q_r_proj qthisr ->
      q_project_q_r (vpa_mutabilty qthis (q_c_proj q_c)) = Some qadapted -> 
      o = mkObj (mkruntime_type qadapted c) (vals) ->
      h' = h++[o] ->
      rΓ' = rΓ <| vars := update x (Iot (dom h)) rΓ.(vars) |> ->
      eval_stmt OK rΓ h (SNew x q_c c ys) OK rΓ' h'

  (* evaluate method call statement *)
  | SBS_Call: forall CT rΓ h x y m zs vals ly cy mbody mstmt mret retval h' rΓ' rΓ'' rΓ''',
    runtime_getVal rΓ y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    method_body_lookup CT cy m = Some mbody ->
    mstmt = mbody.(mbody_stmt) ->
    mret = mbody.(mreturn) ->
    runtime_lookup_list rΓ zs = Some vals ->
    (* rΓ' = mkr_env (Iot ly :: vals) rΓ.(init_state) -> *)
    rΓ' = mkr_env (Iot ly :: vals) ->
    eval_stmt OK rΓ' h mstmt OK rΓ'' h' ->
    runtime_getVal rΓ'' mret = Some retval ->
    rΓ''' = rΓ <| vars := update x retval rΓ.(vars) |> ->
    eval_stmt OK rΓ h (SCall x m y zs) OK rΓ''' h'

  (* evaluate method call statement NPE *)
  | SBS_Call_NPE: forall rΓ h x y m zs rΓ' h',
      runtime_getVal rΓ y = Some (Null_a) ->
      eval_stmt OK rΓ h (SCall x m y zs) NPE rΓ' h'

  | SBS_Call_NPE_Body: forall CT rΓ h x y m zs vals ly cy mbody mstmt mret h' rΓ' rΓ'',
    runtime_getVal rΓ y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    method_body_lookup CT cy m = Some mbody ->
    mstmt = mbody.(mbody_stmt) ->
    mret = mbody.(mreturn) ->
    runtime_lookup_list rΓ zs = Some vals ->
    (* rΓ' = mkr_env (Iot ly :: vals) rΓ.(init_state) -> *)
    rΓ' = mkr_env (Iot ly :: vals) ->
    eval_stmt OK rΓ' h mstmt NPE rΓ'' h' ->
    eval_stmt OK rΓ h (SCall x m y zs) NPE rΓ'' h'

  (* evaluate sequence of statements *)
  | SBS_Seq: forall rΓ h s1 s2 rΓ' h' rΓ'' h'',
      eval_stmt OK rΓ h s1 OK rΓ' h' ->
      eval_stmt OK rΓ' h' s2 OK rΓ'' h'' ->
      eval_stmt OK rΓ h (SSeq s1 s2) OK rΓ'' h''

  | SBS_Seq_NPE_first: forall rΓ h s1 s2 rΓ' h',
      eval_stmt OK rΓ h s1 NPE rΓ' h' ->
      eval_stmt OK rΓ h (SSeq s1 s2) NPE rΓ' h'

  | SBS_Seq_NPE_second: forall rΓ h s1 s2 rΓ' h' rΓ'' h'',
      eval_stmt OK rΓ h s1 OK rΓ' h' ->
      eval_stmt OK rΓ' h' s2 NPE rΓ'' h'' ->
      eval_stmt OK rΓ h (SSeq s1 s2) NPE rΓ'' h''
.

Lemma Forall2_nth_error_prop : forall {A B : Type} (P : A -> B -> Prop) (l1 : list A) (l2 : list B) (n : nat) (a : A) (b : B),
  Forall2 P l1 l2 ->
  nth_error l1 n = Some a ->
  nth_error l2 n = Some b ->
  P a b.
Proof.
  intros A B P l1 l2 n a b Hforall2 Hnth1 Hnth2.
  revert l1 l2 Hforall2 Hnth1 Hnth2.
  induction n; intros l1 l2 Hforall2 Hnth1 Hnth2.
  - (* n = 0 *)
    destruct l1 as [|a1 l1']; [discriminate|].
    destruct l2 as [|b1 l2']; [discriminate|].
    inversion Hforall2; subst.
    simpl in Hnth1, Hnth2.
    injection Hnth1 as Ha_eq.
    injection Hnth2 as Hb_eq.
    subst. exact H2.
  - (* n = S n' *)
    destruct l1 as [|a1 l1']; [discriminate|].
    destruct l2 as [|b1 l2']; [discriminate|].
    inversion Hforall2; subst.
    simpl in Hnth1, Hnth2.
    apply IHn with l1' l2'; assumption.
Qed.

Lemma nth_error_update_neq : forall {A : Type} (l : list A) (i j : nat) (v : A),
  i <> j ->
  nth_error (update i v l) j = nth_error l j.
Proof.
  intros A l i j v Hneq.
  apply update_diff.
  exact Hneq.
Qed.

(* evaluate program *)

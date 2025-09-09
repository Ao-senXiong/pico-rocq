From Coq Require Import Lia.
Require Import List.
Import ListNotations.
Require Import Syntax Typing Subtyping ViewpointAdaptation Helpers.
Require Import String.
Require Import Coq.Sets.Ensembles.
From RecordUpdate Require Import RecordUpdate.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.

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
(* Definition can_assign (CT: class_table) (rΓ: r_env) (h: heap) (ι: Loc) (f: var) : bool :=
  match r_muttype h ι, r_basetype h ι with
  | Some q, Some c =>
    match sf_assignability_rel CT c f with
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

Lemma can_assign_immutable_final_false :
  forall CT rΓ h ι f o,
    r_muttype h ι = Some (exist _ Imm (or_intror eq_refl)) ->
    runtime_getObj h ι = Some o ->
    sf_assignability CT (rctype (rt_type o)) f = Some Final \/
    sf_assignability CT (rctype (rt_type o)) f = Some RDA ->
    can_assign CT rΓ h ι f = false.
Proof.
  intros.
  unfold can_assign.
  rewrite H.
  unfold r_basetype.
  rewrite H0.
  simpl.
  destruct H1 as [HFinal | HRDA].
  - (* Case: Final *)
    rewrite HFinal.
    simpl.
    unfold vpa_assignability.
    simpl.
    reflexivity.
  - (* Case: RDA *)
    rewrite HRDA.
    simpl.
    unfold vpa_assignability.
    simpl.
    reflexivity.
Qed. *)

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
      exists field_defs, CollectFields CT (rt_type o).(rctype) field_defs /\
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
  (exists iot, gget rΓ.(vars) 0 = Some (Iot iot) /\ iot < dom h) /\
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
      \/ ((vpa_qualified_type (q_r_proj q) sqt).(sqtype) = Lost /\ base_subtype CT rqt.(rctype) sqt.(sctype) )
      (* \/ (vpa_qualified_type (q_r_proj q) sqt).(sqtype) = Bot *)
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
(* Lemma r_obj_subtype_sqt :
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
      destruct Hwf as [Hsubtype | [HLost | HBot]].
      * 
        apply qualified_type_subtype_base_subtype with (CT := CT) in Hsubtype.
          intro Heq.
          unfold r_type in Hr_type.
          rewrite Hbasetype in Hr_type.
          injection Hr_type as Hrqt.
          rewrite <- Heq.
          rewrite <- Hrqt.
          rewrite vpa_qualified_type_sctype in Hsubtype.
          exact Hsubtype.
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
Qed. *)


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
Notation "rΓ ',' h '⟦' e '⟧' '-->' v ',' rΓ' ',' h'" := (eval_expr OK rΓ h e v OK rΓ' h') (at level 80).

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
  | SBS_FldWrite: forall rΓ h x f y lx o vf v2 h',
      runtime_getVal rΓ x = Some (Iot lx) ->
      runtime_getObj h lx = Some o ->
      getVal o.(fields_map) f = Some vf ->
      runtime_getVal rΓ y = Some v2 ->
      (* can_assign CT rΓ h lx f = true -> *) (* Runtime need no check *)
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

Lemma vpa_qualified_type_preserves_subtype : forall CT q T1 T2,
  q = Imm \/ q = Mut ->
  qualified_type_subtype CT T1 T2 ->
  qualified_type_subtype CT (vpa_qualified_type q T1) (vpa_qualified_type q T2).
Proof.
  intros CT q T1 T2 Hq Hsub.
  induction Hsub.
  - (* qtype_sub case *)
    unfold vpa_qualified_type.
    destruct qt1 as [q1 c1], qt2 as [q2 c2].
    simpl in *.
    apply qtype_sub; simpl.
    + (* Domain constraint for adapted qt1 *)
      exact H.
    + (* Domain constraint for adapted qt2 *)
      exact H0.
    + (* Mutability subtyping: vpa_mutabilty q q1 ⊑ vpa_mutabilty q q2 *)
      unfold vpa_mutabilty.
destruct q.
* (* q = Rd *)
  destruct q1; destruct q2; simpl; try assumption;
  try apply q_rd; try apply q_bot;
  try (inversion H1; subst; assumption).
  try apply q_refl. discriminate.
* (* q = Mut *)
  destruct q1; destruct q2; simpl; try assumption;
  try apply q_rd; try apply q_bot; try apply q_refl.
  all: try assumption;
     try apply q_refl; try discriminate;
     try apply q_rd;
     try apply q_bot;
     try (exfalso; inversion H1).
* (* q = Imm *)
  destruct q1; destruct q2; simpl; try assumption;
  try apply q_rd; try apply q_bot.
* (* q = Lost *)
  destruct q1; destruct q2; simpl; try assumption;
  try apply q_rd; try apply q_bot.
  all: try assumption;
     try apply q_refl; try discriminate;
     try apply q_rd;
     try apply q_bot;
     try (exfalso; inversion H1).
  destruct Hq as [H_rd_imm | H_rd_mut].
  -- (* Case: Rd = Imm *)
    discriminate H_rd_imm.
  -- (* Case: Rd = Mut *) 
    discriminate H_rd_mut.
* (* q = Bot *)
  destruct q1; destruct q2; simpl.
  all: try assumption;
     try apply q_refl; try discriminate;
     try apply q_rd;
     try apply q_bot;
     try (exfalso; inversion H1).
  destruct Hq as [H_rd_imm | H_rd_mut].
  -- (* Case: Rd = Imm *)
    discriminate H_rd_imm.
  -- (* Case: Rd = Mut *) 
    discriminate H_rd_mut.   
* 
  destruct q1; destruct q2; simpl; try assumption;
  try apply q_rd; try apply q_bot.
  all: try assumption;
     try apply q_refl; try discriminate;
     try apply q_rd;
     try apply q_bot;
     try (exfalso; inversion H1). 
  + (* Base type subtyping preserved *)
      exact H2.
  - (* qtype_trans case *)
    eapply qtype_trans; [exact IHHsub1 | exact IHHsub2].
  - (* qtype_refl case *)
    apply qtype_refl.
    unfold vpa_qualified_type, sctype.
    destruct qt; simpl. exact H.
    unfold vpa_qualified_type.
    destruct qt as [q_qt c_qt].
    simpl.
    unfold vpa_mutabilty.
    destruct Hq as [Hq_imm | Hq_mut].
    + (* q = Imm *)
      subst q.
      {
        destruct q_qt; simpl.
        - (* q_qt = Rd: Rd ≠ Lost *)
          discriminate.
        - (* q_qt = Mut: Mut ≠ Lost *)
          discriminate.
        - (* q_qt = Imm: Imm ≠ Lost *)
          discriminate.
        - (* q_qt = RDM: Imm ≠ Lost *)
          discriminate.
        - (* q_qt = Lost: Lost ≠ Lost contradicts H0 *)
          contradiction H0. reflexivity.
        - (* q_qt = Bot: Bot ≠ Lost *)
          discriminate.
      }
    + (* q = Mut *)  
      subst q.
      (* vpa_mutabilty Mut q_qt *)
      {
        destruct q_qt; simpl.
        - (* q_qt = Rd: Rd ≠ Lost *)
          discriminate.
        - (* q_qt = Mut: Mut ≠ Lost *)
          discriminate.
        - (* q_qt = Imm: Imm ≠ Lost *)
          discriminate.
        - (* q_qt = RDM: Imm ≠ Lost *)
          discriminate.
        - (* q_qt = Lost: Lost ≠ Lost contradicts H0 *)
          contradiction H0. reflexivity.
        - (* q_qt = Bot: Bot ≠ Lost *)
          discriminate.
      }
Qed.

Lemma q_r_proj_imm_or_mut : forall q,
  q_r_proj q = Imm \/ q_r_proj q = Mut.
Proof.
  intros q. destruct q; simpl.
- destruct o as [H1 | H2].
-- right; exact H1.
-- left; exact H2.
Qed.

(* Subtyping Preservation for wf_r_typable *)
Lemma wf_r_typable_subtype : forall CT rΓ h loc T1 T2,
  sctype T1 < dom CT ->
  sctype T2 < dom CT ->
  wf_r_typable CT rΓ h loc T1 ->
  qualified_type_subtype CT T1 T2 ->
  wf_r_typable CT rΓ h loc T2.
Proof.
  intros CT rΓ h loc T1 T2 Hc1dom Hc2dom Hwf Hsub.
  unfold wf_r_typable in *.
  destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
  destruct (get_this_var_mapping (vars rΓ)) as [ι'|] eqn:Hthis; [|contradiction].
  destruct (r_muttype h ι') as [q|] eqn:Hmut; [|contradiction].
  destruct Hwf as [Hwf_sub | Hwf_lost].
  - (* Case: subtyping relation *)
    left.
    eapply qtype_trans; [exact Hwf_sub |].
    apply vpa_qualified_type_preserves_subtype.
    + apply q_r_proj_imm_or_mut.
    + exact Hsub.
  - (* Case: Lost *)
    (* left.
    {
      destruct Hwf_lost as [Hwf_lost_eq Hbasetype].
      eapply qtype_trans.
      - (* First: runtime_type_to_qualified_type rqt <: vpa_qualified_type (q_r_proj q) T1 *)
        apply qtype_sub.
        + (* Domain constraint for runtime type *)
          unfold runtime_type_to_qualified_type. 
          destruct rqt as [rq rc]. simpl.
          (* Need to show rc < dom CT *)
          (* This should follow from well-formedness of the heap/runtime type *)
          admit.
        + (* Domain constraint for adapted T1 *)
          unfold vpa_qualified_type. 
          destruct T1 as [q1 c1]. simpl. exact Hc1dom.
        + (* Qualifier subtyping: q_r_proj (rqtype rqt) ⊑ Lost *)
          unfold runtime_type_to_qualified_type.
          destruct rqt as [rq rc]. simpl.
          admit.
        + (* Base type subtyping: rctype rqt <: sctype T1 *)
          unfold runtime_type_to_qualified_type.
          destruct rqt as [rq rc]. simpl. exact Hbasetype.
      - (* Second: vpa_qualified_type (q_r_proj q) T1 <: vpa_qualified_type (q_r_proj q) T2 *)
        apply vpa_qualified_type_preserves_subtype.
        + apply q_r_proj_imm_or_mut.
        + exact Hsub.
    } *)

    unfold vpa_qualified_type in *.
    destruct T1 as [q1 c1], T2 as [q2 c2].
    simpl in *.
    unfold vpa_mutabilty in Hwf_lost |- *.
    remember (q_r_proj q) as qr.
    destruct q1.
    destruct q2.
    all: try destruct qr eqn:Hqr_cases.
    all: try destruct q2 eqn:Hq2.
    all: try (match goal with
    | |- _ \/ (Rd = Lost /\ _) => 
      left
    | |- _ \/ (_ = Lost /\ _) => 
      right; (* For other cases where the right disjunct might be provable *)
      split; [reflexivity | eapply base_trans; [exact Hbasetype | exact Hc_sub]]
    | _ => 
      right; (* Default case *)
      split; [reflexivity | eapply base_trans; [exact Hbasetype | exact Hc_sub]]
    end).
    (* 19:
     {
      left.
      eapply qtype_trans.
      + (* runtime_type_to_qualified_type rqt <: vpa_qualified_type qr T1 *)
        apply qtype_sub.
        * unfold runtime_type_to_qualified_type.
          destruct rqt as [rq rc]. simpl. admit.
        * unfold vpa_qualified_type. simpl. exfalso.
          destruct Hwf_lost as [Hmut_eq_lost _].
          discriminate Hmut_eq_lost.
        * unfold runtime_type_to_qualified_type. destruct rqt as [rq rc]. simpl.
          destruct Hwf_lost as [Hwf_lost_eq _]. discriminate Hwf_lost_eq.
        * unfold runtime_type_to_qualified_type. destruct rqt as [rq rc]. simpl.
          destruct Hwf_lost as [_ Hbasetype]. eapply base_trans.
        - exact Hbasetype.
        - apply (qualified_type_subtype_base_subtype CT {| sqtype := Mut; sctype := c1 |} {| sqtype := Rd; sctype := c2 |}).
        -- exact Hsub.
        -- exact Hc1dom.
        -- exact Hc2dom.
      + (* vpa_qualified_type qr T1 <: vpa_qualified_type qr {| sqtype := Rd; sctype := c2 |} *)
        apply qtype_refl.
        - exact Hc2dom.
        - discriminate.
    } *)

    all: have hest := Hqr_cases. 
    all: try discriminate Hwf_lost.
    all: try reflexivity.
    all: try pose proof (qualified_type_subtype_base_subtype _ _ _ Hsub Hc1dom Hc2dom) as Hc_sub.
    all: try pose proof (qualified_type_subtype_q_subtype _ _ _ Hsub Hc1dom Hc2dom) as Hq_sub.
    all: try simpl in Hq_sub.
    all: try inversion Hq_sub; subst.
    all: try simpl in Hc_sub.
    all: try inversion Hc_sub; subst.
    all: try pose proof (q_r_proj_imm_or_mut q) as Hqr_cases.
    all: try rewrite <- Heqqr in Hqr_cases.
    all: try destruct Hqr_cases as [Hqr_imm | Hqr_mut].
    all: try discriminate Hqr_imm.
    all: try discriminate Hqr_mut.
    all: try reflexivity.
    all: try exact Hwf_lost.
    all: try destruct Hwf_lost as [Hwf_lost Hbasetype].
    all: try discriminate Hwf_lost.
    all: try (match goal with
    | |- _ \/ (_ = Lost /\ _) => 
      right;
      exfalso;
      apply H;
      reflexivity
    end).

    1:
    {
      eapply qtype_trans.
      - (* runtime_type_to_qualified_type rqt <: {| sqtype := Lost; sctype := c2 |} *)
        apply qtype_sub.
        + (* Domain constraint for runtime type *)
          unfold runtime_type_to_qualified_type.
          destruct rqt as [rq rc]. simpl. admit. (* Need rc < dom CT from heap well-formedness *)
        + (* Domain constraint for Lost type *)
          admit.
        + (* Qualifier subtyping: q_r_proj rq ⊑ Lost *)
          unfold runtime_type_to_qualified_type.
          destruct rqt as [rq rc]. simpl.
          admit.
          (* apply q_rd. Any qualifier is subtype of Rd, but we need Lost here - this might need adjustment *)
        + (* Base type subtyping: rctype rqt <: c2 *)
          unfold runtime_type_to_qualified_type.
          destruct rqt as [rq rc]. simpl.
          admit.
          (* exact Hbasetype. *)
      - (* {| sqtype := Lost; sctype := c2 |} <: {| sqtype := Rd; sctype := c2 |} *)
        exact Hsub.
    }

     (* {
      eapply qtype_trans.
      + (* runtime_type_to_qualified_type rqt <: vpa_qualified_type qr T1 *)
        apply qtype_sub.
        * unfold runtime_type_to_qualified_type.
          destruct rqt as [rq rc]. simpl. admit.
        * unfold vpa_qualified_type. simpl. unfold sctype. admit.
        * unfold runtime_type_to_qualified_type. destruct rqt as [rq rc]. simpl.
          destruct Hwf_lost as [Hwf_lost_eq _]. admit.
        * unfold runtime_type_to_qualified_type. destruct rqt as [rq rc]. simpl.
          eapply base_trans.
        - exact Hbasetype.
        - apply (qualified_type_subtype_base_subtype CT {| sqtype := Mut; sctype := c1 |} {| sqtype := Rd; sctype := c2 |}).
        -- exact Hsub.
        -- exact Hc1dom.
        -- exact Hc2dom.
      + (* vpa_qualified_type qr T1 <: vpa_qualified_type qr {| sqtype := Rd; sctype := c2 |} *)
        apply qtype_refl.
        - exact Hc2dom.
        - discriminate.
    } *)
    
Admitted.

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
(* Critical missing lemmas for type soundness *)

(* 1. Static-Runtime Correspondence Lemmas *)
Lemma runtime_lookup_list_preserves_length : forall rΓ args vals,
  runtime_lookup_list rΓ args = Some vals ->
  List.length vals = List.length args.
Proof.
  intros rΓ args vals H.
  unfold runtime_lookup_list in H.
  generalize dependent vals.
  induction args as [|a args' IH]; intros vals H.
  - simpl in H. injection H as H. subst. reflexivity.
  - simpl in H.
    destruct (runtime_getVal rΓ a) as [v|] eqn:Hval; [|discriminate].
    destruct (mapM (fun x => runtime_getVal rΓ x) args') as [vs|] eqn:Hmap; [|discriminate].
    injection H as H. subst.
    simpl. f_equal. apply IH. reflexivity.
Qed.

Lemma runtime_lookup_list_preserves_typing : forall CT sΓ rΓ h args vals argtypes,
  wf_r_config CT sΓ rΓ h ->
  static_getType_list sΓ args = Some argtypes ->
  runtime_lookup_list rΓ args = Some vals ->
  Forall2 (fun v T => match v with
    | Null_a => True
    | Iot loc => wf_r_typable CT rΓ h loc T
    end) vals argtypes.
Proof.
  intros CT sΓ rΓ h args vals argtypes Hwf Hstatic Hruntime.
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [_ [_ [_ [Hlen Hcorr]]]]].
  generalize dependent vals. generalize dependent argtypes.
  induction args as [|a args' IH]; intros argtypes Hstatic vals Hruntime.
  - (* Base case: empty list *)
    unfold static_getType_list, runtime_lookup_list in *.
    simpl in Hstatic, Hruntime.
    injection Hstatic as Hstatic. injection Hruntime as Hruntime.
    subst. constructor.
  - (* Inductive case: a :: args' *)
    unfold static_getType_list, runtime_lookup_list in *.
    simpl in Hstatic, Hruntime.
    destruct (static_getType sΓ a) as [T|] eqn:HstaticT; [|discriminate].
    destruct (mapM (static_getType sΓ) args') as [Ts|] eqn:HstaticTs; [|discriminate].
    destruct (runtime_getVal rΓ a) as [v|] eqn:HruntimeV; [|discriminate].
    destruct (mapM (runtime_getVal rΓ) args') as [vs|] eqn:HruntimeVs; [|discriminate].
    injection Hstatic as Hstatic. injection Hruntime as Hruntime.
    subst. constructor.
    + (* Show v is well-typed with T *)
      assert (Ha_bound : a < List.length sΓ) by (apply static_getType_dom in HstaticT; exact HstaticT).
      specialize (Hcorr a Ha_bound T HstaticT).
      rewrite HruntimeV in Hcorr.
      destruct v as [|loc]; [trivial | exact Hcorr].
    + (* Apply IH to the tail *)
      apply IH.
      * unfold static_getType_list. reflexivity.
      * unfold runtime_lookup_list. reflexivity.
Qed.

(* 2. Heap Extension Preservation *)
Lemma heap_extension_preserves_objects : forall h obj loc,
  loc < dom h ->
  runtime_getObj (h ++ [obj]) loc = runtime_getObj h loc.
Proof.
  intros h obj loc Hloc.
  unfold runtime_getObj.
  apply nth_error_app1. exact Hloc.
Qed.

Lemma heap_extension_preserves_wf_r_typable : forall CT rΓ h obj loc T,
  wf_r_typable CT rΓ h loc T ->
  wf_r_typable CT rΓ (h ++ [obj]) loc T.
Proof.
  intros CT rΓ h obj loc T Hwf.
  unfold wf_r_typable in *.
  destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
  destruct (get_this_var_mapping (vars rΓ)) as [ι'|] eqn:Hthis; [|contradiction].
  destruct (r_muttype h ι') as [q|] eqn:Hmut; [|contradiction].
  
  assert (Hrtype_ext : r_type (h ++ [obj]) loc = Some rqt).
  {
    unfold r_type in *.
    assert (Hloc_dom : loc < dom h).
    {
      unfold r_type in Hrtype.
      destruct (runtime_getObj h loc) as [o|] eqn:Hobj; [|discriminate].
      apply runtime_getObj_dom in Hobj. exact Hobj.
    }
    rewrite heap_extension_preserves_objects; assumption.
  }
  
  assert (Hmut_ext : r_muttype (h ++ [obj]) ι' = Some q).
  {
    unfold r_muttype in *.
    assert (Hι'_dom : ι' < dom h).
    {
      unfold r_muttype in Hmut.
      destruct (runtime_getObj h ι') as [o|] eqn:Hobj; [|discriminate].
      apply runtime_getObj_dom in Hobj. exact Hobj.
    }
    rewrite heap_extension_preserves_objects; assumption.
  }
  
  rewrite Hrtype_ext.
  rewrite Hmut_ext.
  exact Hwf.
Qed.

(* 3. Subtyping Properties *)
Lemma q_subtype_refl : forall q,
  q <> Lost ->
  q_subtype q q.
Proof.
  intros q Hneq.
  apply q_refl. exact Hneq.
Qed.

(* 4. Forall2 Manipulation Lemmas *)
Lemma Forall2_trans {A B C : Type} (P : A -> B -> Prop) (Q : B -> C -> Prop) (R : A -> C -> Prop) :
  forall l1 l2 l3,
  (forall a b c, P a b -> Q b c -> R a c) ->
  Forall2 P l1 l2 ->
  Forall2 Q l2 l3 ->
  Forall2 R l1 l3.
Proof.
  intros l1 l2 l3 Htrans HP HQ.
  generalize dependent l3. generalize dependent l1.
  induction l2 as [|b l2' IH]; intros l1 HP l3 HQ.
  - inversion HP; subst. inversion HQ; subst. constructor.
  - inversion HP; subst. inversion HQ; subst.
    constructor.
    + apply Htrans with b; assumption.
    + apply IH; assumption.
Qed.

Lemma Forall2_map : forall {A B C} (f : B -> C) (P : A -> C -> Prop) l1 l2,
  Forall2 (fun a b => P a (f b)) l1 l2 ->
  Forall2 P l1 (map f l2).
Proof.
  intros A B C f P l1 l2 H.
  induction H.
  - constructor.
  - simpl. constructor; assumption.
Qed.

(* 5. Field Access and Update Lemmas *)
Lemma field_update_preserves_other_fields : forall (fields : list value) f v f',
  f <> f' ->
  getVal (update f v fields) f' = getVal fields f'.
Proof.
  intros fields f v f' Hneq.
  unfold getVal.
  apply update_diff. exact Hneq.
Qed.

Lemma field_update_preserves_length : forall (fields : list value) f v,
  f < List.length fields ->
  List.length (update f v fields) = List.length fields.
Proof.
  intros fields f v Hbound.
  apply update_length.
Qed.

Lemma Forall2_length : forall {A B} (P : A -> B -> Prop) l1 l2,
  Forall2 P l1 l2 ->
  List.length l1 = List.length l2.
Proof.
  intros A B P l1 l2 H.
  induction H; [reflexivity | simpl; f_equal; assumption].
Qed.

(* Expression Evaluation Preservation *)
(* AOSEN: this is somehow wrong in PICO because x.f could be readonly |> RDM = Lost, which is not compatiable with the value mut/imm *)
Lemma expr_eval_preservation : forall CT sΓ rΓ h e v rΓ' h' T,
  wf_r_config CT sΓ rΓ h ->
  expr_has_type CT sΓ e T ->
  eval_expr OK rΓ h e v OK rΓ' h' ->
  match v with
  | Null_a => True
  | Iot loc => wf_r_typable CT rΓ h loc T
  end.
Proof.
  intros CT sΓ rΓ h e v rΓ' h' T Hwf Htype Heval.
  induction Heval; inversion Htype; subst.
  - (* EBS_Null *) trivial.
  - (* EBS_Val *) 
    unfold wf_r_config in Hwf.
    destruct Hwf as [_ [_ [_ [_ [_ Hcorr]]]]].
    assert (Hx_bound : x < List.length sΓ) by (apply static_getType_dom in H4; exact H4).
    specialize (Hcorr x Hx_bound T H4).
    rewrite H in Hcorr.
    destruct v as [|loc]; [trivial | exact Hcorr].
  - (* EBS_Field *)
  destruct v1 as [|loc]; [trivial|].
  (* Need to show: wf_r_typable CT rΓ h loc (vpa_type_to_type T0 ...) *)
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [Hwf_heap [Hwf_renv [Hwf_senv [_ Hcorr]]]]].
  (* Use heap well-formedness to get field typing *)
  assert (Hobj_wf : wf_obj CT h v).
  {
    apply Hwf_heap.
    apply runtime_getObj_dom in H0.
    exact H0.
  }
  unfold wf_obj in Hobj_wf.
  rewrite H0 in Hobj_wf.
  destruct Hobj_wf as [_ Hfields_wf].
  destruct Hfields_wf as [Hdom_eq Hforall2].
  destruct Hforall2 as [Hcollect [Hdom_eq_test Hforall2]].

  assert (Hfield_lookup : exists fdef, 
    nth_error Hdom_eq f = Some fdef /\
    nth_error (fields_map o) f = Some (Iot loc)).
  {
    (* Use H1 and Hdom_eq to establish this *)
    (* Convert getVal to nth_error using domain equality *)
    assert (Hf_in_dom : f < dom (fields_map o)).
    {
      apply getVal_dom in H1.
      exact H1.
    }
    (* Use domain equality to get f in collect_fields domain *)
    rewrite Hdom_eq_test in Hf_in_dom.
    assert (Hfdef_exists : exists fdef, nth_error Hdom_eq f = Some fdef).
    {
      destruct (nth_error Hdom_eq f) as [fdef|] eqn:Hfdef_lookup.
      - exists fdef. reflexivity.
      - exfalso.
        apply nth_error_None in Hfdef_lookup.
        lia.
    }
    destruct Hfdef_exists as [fdef Hfdef_lookup].
    (* Convert H1 from getVal to nth_error *)
    assert (Hfield_nth : nth_error (fields_map o) f = Some (Iot loc)).
    {
      unfold getVal in H1.
      exact H1.
    }
    exists fdef.
    split; [exact Hfdef_lookup | exact Hfield_nth].
  }
  destruct Hfield_lookup as [fdef [Hfdef_lookup Hfield_nth]].
  (* Apply Forall2 property *)
  eapply Forall2_nth_error_prop in Hforall2; eauto.
  simpl in Hforall2.
  (* Now check if loc exists in heap *)
  destruct (runtime_getObj h loc) as [o_loc|] eqn:Hloc_obj.
  * (* loc exists in heap *)
    destruct Hforall2 as [rqt [Hrtype_loc Hsubtype]].
    (* Now you have the typing for loc *)
    unfold wf_r_typable.
    rewrite Hrtype_loc.
    (* Get this variable mapping *)
    destruct (get_this_var_mapping (vars rΓ)) as [ι'|] eqn:Hthis.
    2:{
      (* Use wf_r_config to show that this variable mapping must exist *)
      destruct Hwf_renv as [Hwf_this [Hwf_this_addr Hwf_renv]].
      (* Hwf_this should guarantee that get_this_var_mapping succeeds *)
      unfold get_this_var_mapping in Hthis.
      (* get_this_var_mapping typically looks at vars[0] *)
      assert (H0_bound : 0 < dom (vars rΓ)) by exact Hwf_this.
      (* unfold dom in H0_bound. *)
      (* Since length > 0, nth_error 0 must succeed *)
      destruct (nth_error (vars rΓ) 0) as [v0|] eqn:Hv0.
      - (* vars[0] exists, so get_this_var_mapping should succeed *)
        simpl in Hthis.
        destruct (vars rΓ) as [|v1 rest] eqn:Hvars.
        simpl in Hv0.
        discriminate.
        simpl in Hv0.
        injection Hv0 as Hv0_eq.
        subst v0.
        (* So v1 = v0, and from Hthis we know v1 = Null_a *)
        destruct v1 as [|loc'].
        + (* v1 = Null_a, consistent with Hthis *)
          (* But this contradicts well-formedness - need stronger condition *)
          (* For now, this might be an allowed case *)
          destruct Hwf_this_addr as [iot Hiot].
          (* gget (Null_a :: rest) 0 should return Null_a, not Iot iot *)
          simpl in Hiot.
          destruct Hiot as [Hiot Hthisdom].
          (* gget is likely nth_error or similar, so gget (Null_a :: rest) 0 = Some Null_a *)
          discriminate Hiot.
        + (* v1 = Iot loc', should make get_this_var_mapping return Some loc' *)
          simpl in Hthis.
          discriminate Hthis.
      - (* vars[0] doesn't exist, contradicts length > 0 *)
        apply nth_error_None in Hv0.
        simpl in H0_bound.
        lia.
    }
    destruct (r_muttype h ι') as [q|] eqn:Hmut.
    2:{
      assert (Hι'_in_heap : ι' < dom h).
      {
        (* ι' comes from get_this_var_mapping, so it must be in heap *)
        (* Use the third component of Hwf_renv *)
        destruct Hwf_renv as [Hwf_this [Hwf_this_addr Hwf_renv]].
        destruct Hwf_this_addr as [iot Hiot].
        destruct Hiot as [Hiot Hthisdom].
        unfold get_this_var_mapping in Hthis.
        assert (Hconnect : ι' = iot).
        {
          unfold get_this_var_mapping in Hthis.
          destruct (vars rΓ) as [|vtest rest] eqn:Hvars.
          - (* Empty list case *)
            discriminate Hthis.
          - (* Non-empty list case *)
            destruct vtest as [|loctest] eqn:Hv.
            + (* Null_a case *)
              discriminate Hthis.
            + (* Iot loc case *)
              injection Hthis as Heq.
              subst ι'.
              simpl in Hiot.
              injection Hiot as Heq2.
              exact Heq2.
        }
        rewrite Hconnect. exact Hthisdom.
      }
      (* Now use heap well-formedness *)
      apply Hwf_heap in Hι'_in_heap.
      unfold wf_obj in Hι'_in_heap.
        destruct Hwf_renv as [Hwf_this [Hwf_this_addr Hwf_renv]].
        destruct Hwf_this_addr as [iot Hiot].
        destruct Hiot as [Hiot Hthisdom].
      assert (Hconnect : ι' = iot).
      {
        unfold get_this_var_mapping in Hthis.
        destruct (vars rΓ) as [|vtest rest] eqn:Hvars.
        - discriminate Hthis.
        - destruct vtest as [|loctest] eqn:Hv.
          + discriminate Hthis.
          + injection Hthis as Heq.
            subst ι'.
            simpl in Hiot.
            injection Hiot as Heq2.
            exact Heq2.
      }
      rewrite Hconnect in Hmut.
      unfold r_muttype in Hmut.
      apply runtime_getObj_Some in Hthisdom.
      destruct Hthisdom as [C [ω Ho']].
      rewrite Ho' in Hmut.
      discriminate Hmut.
    }
  assert (Hfdef_eq : fdef = fDef).
  {
    (* First, get FieldLookup from sf_def_rel *)
    unfold sf_def_rel in H9.
    (* H9: FieldLookup CT (sctype T0) f fDef *)
    
    (* Next, get FieldLookup from CollectFields *)
    assert (Hfield_lookup_o : FieldLookup CT (rctype (rt_type o)) f fdef).
    {
      apply FL_Found with Hdom_eq.
      - exact Hcollect.
      - exact Hfdef_lookup.
    }
    
    (* Now we need to connect (sctype T0) with (rctype (rt_type o)) *)
    (* This should come from the fact that x has type T0 and points to object o *)
    (* Use wf_r_typable for x *)
    assert (Hx_wf : wf_r_typable CT rΓ h v T0).
    {
      assert (Hx_bound : x < dom sΓ) by (apply static_getType_dom in H7; exact H7).
      specialize (Hcorr x Hx_bound T0 H7).
      rewrite H in Hcorr.
      exact Hcorr.
    }
    
    (* Extract base subtyping from wf_r_typable *)
    unfold wf_r_typable in Hx_wf.
    unfold r_type in Hx_wf.
    rewrite H0 in Hx_wf.
    simpl in Hx_wf.
    rewrite Hthis in Hx_wf.
    rewrite Hmut in Hx_wf.
    destruct Hx_wf as [Hx_sub | Hx_lost].
    - (* Subtyping case *)
      inversion Hx_sub; subst.
      simpl in H6.
      (* Now H11: base_subtype CT (rctype (rt_type o)) (sctype (vpa_qualified_type (q_r_proj q) T0)) *)
      (* We need to show fdef = fDef using field lookup determinism *)
      eapply field_lookup_deterministic_rel.
      + exact Hfield_lookup_o.
      + apply (field_inheritance_subtyping CT (rctype (rt_type o)) (sctype T0) f fDef).
        * (* Show base_subtype CT (rctype (rt_type o)) (sctype T0) *)
          (* We have H6: base_subtype CT (rctype (rt_type o)) (sctype (vpa_qualified_type (q_r_proj q) T0)) *)
          (* We need: base_subtype CT (rctype (rt_type o)) (sctype T0) *)
          (* This follows from the fact that vpa_qualified_type preserves sctype *)
          rewrite vpa_qualified_type_sctype in H6.
          exact H6.
        * (* We have the field lookup in the subtype *)
          exact H9.
      +
        admit.
      + admit.
    - (* Lost case - shouldn't happen for concrete objects *)
      admit.
  }
  subst fdef.  
  left.
  (* Apply the subtyping from Hforall2 and VPA *)
  eapply qtype_trans.
  + exact Hsubtype.
  + (* Show VPA preserves subtyping to target type *)
    {
      admit.
    }
* (* loc doesn't exist in heap - contradiction *)
  exfalso.
  exact Hforall2.
Admitted.

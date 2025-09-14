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
      match (vpa_mutabilty (q_r_proj q) q') with
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
                (mutability (ftype fdef)) 
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

(* Determine whether a static qualifier is assiganble/typable under a runtime qualifeir  *)
Definition qualifier_typable (qr: q_r) (q: q) : bool :=
match qr with
| Imm_r =>
  match q with 
  | Imm => true
  | Rd => true
  | Lost => true
  | _ => false
  end
| Mut_r =>
  match q with 
  | Mut => true
  | Rd => true
  | Lost => true
  | _ => false
  end
end.

(* Wellformed Runtime Typable: the runtime type of the address is subtype of q_this viewpoint adapting the static type *)
Definition wf_r_typable (CT: class_table) (rΓ: r_env) (h: heap) (ι: Loc) (sqt: qualified_type) : Prop :=
  match r_type h ι,  get_this_var_mapping (rΓ.(vars)) with
  | Some rqt, Some ι' =>
    match r_muttype h ι' with
    | Some q =>
      base_subtype CT (rctype rqt) (sctype sqt) /\ 
      qualifier_typable (rqtype rqt) (vpa_mutabilty (q_r_proj q) (sqtype sqt)) 
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
  (* CT is well-formed *)
  wf_class_table CT /\
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
Inductive eval_expr : eval_result -> class_table -> r_env -> heap -> expr -> value -> eval_result -> r_env -> heap -> Prop :=
  (* evalutate null expression  *)
  | EBS_Null : forall CT rΓ h,
      eval_expr OK CT rΓ h ENull Null_a OK rΓ h

  (* evaluate value expression *)
  | EBS_Val : forall CT rΓ h x v,
      runtime_getVal rΓ x = Some v ->
      eval_expr OK CT rΓ h (EVar x) v OK rΓ h

  (* evaluate field access expression *)  
  | EBS_Field : forall CT rΓ h x f v o v1,
      runtime_getVal rΓ x = Some (Iot v) ->
      runtime_getObj h v = Some o ->
      getVal o.(fields_map) f = Some v1 ->
      eval_expr OK CT rΓ h (EField x f) v1 OK rΓ h

  (* evaluate field access expression yields NPE *)
  | EBS_Field_NPE : forall CT rΓ h x f v,
      runtime_getVal rΓ x = Some (Null_a) ->
      eval_expr OK CT rΓ h (EField x f) v NPE rΓ h
  .
Notation "rΓ ',' h '⟦' e '⟧' '-->' v ',' rΓ' ',' h'" := (eval_expr OK rΓ h e v OK rΓ' h') (at level 80).

(* PICO Statement evaluation *)
Inductive eval_stmt : eval_result -> class_table -> r_env -> heap -> stmt -> eval_result -> r_env -> heap -> Prop :=
  (* evaluate skip statement *)
  | SBS_Skip : forall CT rΓ h,
      eval_stmt OK CT rΓ h SSkip OK rΓ h

  (* evaluate local variable declaration statement *)
  | SBS_Local : forall CT rΓ h T x,
      runtime_getVal rΓ x = None ->
      eval_stmt OK CT rΓ h (SLocal T x) OK
      (* (rΓ <|vars := update (List.length rΓ.(vars) + 1) Null_a rΓ.(vars)|> <|init_state := rΓ.(init_state)|>) *)
      (rΓ <|vars := rΓ.(vars)++[Null_a] |> )
      h

  (* evaluate variable assignment statement *)
  | SBS_Assign : forall CT rΓ h x e v1 v2,
      runtime_getVal rΓ x = Some v1 ->
      eval_expr OK CT rΓ h e v2 OK rΓ h ->
      eval_stmt OK CT rΓ h (SVarAss x e) OK
      (* (rΓ <|vars := update x v2 rΓ.(vars)|> <|init_state := rΓ.(init_state)|>) *)
      (rΓ <|vars := update x v2 rΓ.(vars)|>)
      h

  | SBS_Assign_NPE : forall CT rΓ h x e v1 v2 rΓ' h',
    runtime_getVal rΓ x = Some v1 ->
    eval_expr OK CT rΓ h e v2 NPE rΓ h ->
    eval_stmt OK CT rΓ h (SVarAss x e) NPE
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
      (* can_assign CT rΓ h lx f = true -> *) (* Runtime need no check *)
      h' = update_field h lx f v2 ->
      eval_stmt OK CT rΓ h (SFldWrite x f y) OK rΓ h'

  (* evaluate field write statement NPE *)
  | SBS_FldWrite_NPE: forall CT rΓ h x f y rΓ' h',
      runtime_getVal rΓ x = Some (Null_a) ->
      eval_stmt OK CT rΓ h (SFldWrite x f y) NPE rΓ' h'

  (* evaluate object creation statement *)
  | SBS_New: forall CT rΓ h x (q_c:q) c ys vals l1 qthisr qthis qadapted o rΓ' h',
      runtime_getVal rΓ 0 = Some (Iot l1) ->
      runtime_lookup_list rΓ ys = Some vals ->
      r_muttype h l1 = Some qthisr ->
      qthis = q_r_proj qthisr ->
      q_project_q_r (vpa_mutabilty qthis q_c) = Some qadapted -> 
      o = mkObj (mkruntime_type qadapted c) (vals) ->
      h' = h++[o] ->
      rΓ' = rΓ <| vars := update x (Iot (dom h)) rΓ.(vars) |> ->
      eval_stmt OK CT rΓ h (SNew x q_c c ys) OK rΓ' h'

  (* evaluate method call statement *)
  | SBS_Call: forall CT rΓ h x y m zs vals ly cy mdef mbody mstmt mret retval h' rΓ' rΓ'' rΓ''',
    runtime_getVal rΓ y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    MethodLookup CT cy m mdef /\ mbody = Syntax.mbody mdef ->
    mstmt = mbody.(mbody_stmt) ->
    mret = mbody.(mreturn) ->
    runtime_lookup_list rΓ zs = Some vals ->
    (* rΓ' = mkr_env (Iot ly :: vals) rΓ.(init_state) -> *)
    rΓ' = mkr_env (Iot ly :: vals) ->
    eval_stmt OK CT rΓ' h mstmt OK rΓ'' h' ->
    runtime_getVal rΓ'' mret = Some retval ->
    rΓ''' = rΓ <| vars := update x retval rΓ.(vars) |> ->
    eval_stmt OK CT rΓ h (SCall x m y zs) OK rΓ''' h'

  (* evaluate method call statement NPE *)
  | SBS_Call_NPE: forall CT rΓ h x y m zs rΓ' h',
      runtime_getVal rΓ y = Some (Null_a) ->
      eval_stmt OK CT rΓ h (SCall x m y zs) NPE rΓ' h'

  | SBS_Call_NPE_Body: forall CT rΓ h x y m zs vals ly cy mdef mbody mstmt mret h' rΓ' rΓ'',
    runtime_getVal rΓ y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    MethodLookup CT cy m mdef /\ mbody = Syntax.mbody mdef ->
    mstmt = mbody.(mbody_stmt) ->
    mret = mbody.(mreturn) ->
    runtime_lookup_list rΓ zs = Some vals ->
    (* rΓ' = mkr_env (Iot ly :: vals) rΓ.(init_state) -> *)
    rΓ' = mkr_env (Iot ly :: vals) ->
    eval_stmt OK CT rΓ' h mstmt NPE rΓ'' h' ->
    eval_stmt OK CT rΓ h (SCall x m y zs) NPE rΓ'' h'

  (* evaluate sequence of statements *)
  | SBS_Seq: forall CT rΓ h s1 s2 rΓ' h' rΓ'' h'',
      eval_stmt OK CT rΓ h s1 OK rΓ' h' ->
      eval_stmt OK CT rΓ' h' s2 OK rΓ'' h'' ->
      eval_stmt OK CT rΓ h (SSeq s1 s2) OK rΓ'' h''

  | SBS_Seq_NPE_first: forall CT rΓ h s1 s2 rΓ' h',
      eval_stmt OK CT rΓ h s1 NPE rΓ' h' ->
      eval_stmt OK CT rΓ h (SSeq s1 s2) NPE rΓ' h'

  | SBS_Seq_NPE_second: forall CT rΓ h s1 s2 rΓ' h' rΓ'' h'',
      eval_stmt OK CT rΓ h s1 OK rΓ' h' ->
      eval_stmt OK CT rΓ' h' s2 NPE rΓ'' h'' ->
      eval_stmt OK CT rΓ h (SSeq s1 s2) NPE rΓ'' h''
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

Lemma q_r_proj_imm_or_mut : forall qr,
  q_r_proj qr = Imm \/ q_r_proj qr = Mut.
Proof.
  intros qr. destruct qr; simpl.
-- right; reflexivity.
-- left; reflexivity.
Qed.

Lemma r_type_dom : forall h loc rqt,
  r_type h loc = Some rqt ->
  loc < dom h.
Proof.
  intros h loc rqt H.
  unfold r_type in H.
  destruct (runtime_getObj h loc) as [o|] eqn:Hobj.
  - (* Some case *)
    unfold runtime_getObj in Hobj.
    apply nth_error_Some.
    rewrite Hobj.
    discriminate.
  - (* None case *)
    simpl in H.
    discriminate H.
Qed.

Lemma qualifier_typable_vpa_subtype : forall CT qr q_proj T1 T2,
  (sctype T1) < (dom CT) ->
  (sctype T2) < (dom CT) ->
  qualified_type_subtype CT T1 T2 ->
  qualifier_typable qr (vpa_mutabilty q_proj (sqtype T1)) ->
  qualifier_typable qr (vpa_mutabilty q_proj (sqtype T2)).
Proof.
  intros CT qr q_proj T1 T2 T1dom T2dom Hsub Hqual1.
  apply qualified_type_subtype_q_subtype in Hsub; [| exact T1dom| exact T2dom].
  unfold qualifier_typable in *.
  destruct qr as [|].
  - (* Goal 1: Mut_r case *)
  unfold vpa_mutabilty in *.
  destruct T1 as [q1 c1], T2 as [q2 c2].
  simpl in *.
  destruct q_proj, q1, q2; simpl in *; auto;
  try (inversion Hsub; subst; simpl in *; auto).

  - (* Goal 2: Imm_r case *)  
    unfold vpa_mutabilty in *.
    destruct T1 as [q1 c1], T2 as [q2 c2].
    simpl in *.
    destruct q_proj, q1, q2; simpl in *; auto;
    try (inversion Hsub; subst; simpl in *; auto).
Qed.

(* Subtyping Preservation for wf_r_typable *)
Lemma wf_r_typable_subtype : forall CT rΓ h loc T1 T2,
  sctype T1 < dom CT ->
  sctype T2 < dom CT ->
  wf_heap CT h ->
  wf_r_typable CT rΓ h loc T1 ->
  qualified_type_subtype CT T1 T2 ->
  wf_r_typable CT rΓ h loc T2.
Proof.
  intros CT rΓ h loc T1 T2 Hc1dom Hc2dom hwfheap Hwf Hsub.
  unfold wf_r_typable in *.
  destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
  destruct (get_this_var_mapping (vars rΓ)) as [ι'|] eqn:Hthis; [|contradiction].
  destruct (r_muttype h ι') as [q|] eqn:Hmut; [|contradiction].
  destruct Hwf as [Hbase1 Hqual1].
  split.
  apply qualified_type_subtype_base_subtype in Hsub.
  apply base_trans with (D:= sctype T1).
  exact Hbase1.
  exact Hsub.
  exact Hc1dom.
  exact Hc2dom.
  eapply qualifier_typable_vpa_subtype; [exact Hc1dom | exact Hc2dom| exact Hsub | exact Hqual1].
Qed.

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

(* evaluation preserves runtime type on heap. *)
Lemma runtime_preserves_r_type_heap : forall CT rΓ h loc C h' vals s rΓ',
  runtime_getObj h loc = Some {| rt_type := C; fields_map := vals |}->
  eval_stmt OK CT rΓ h s OK rΓ' h' ->
  exists vals', runtime_getObj h' loc = Some {| rt_type := C; fields_map := vals' |}.
Proof.
  intros. remember OK as ok. induction H0; subst; try discriminate.
  1-3: exists vals; assumption.
  - (* SBS_FldWrite *)
    destruct (Nat.eq_dec loc lx).
    + subst lx. rewrite H1 in H. inversion H; subst.
      exists (update f v2 vals). unfold runtime_getObj.
      unfold update_field. rewrite H1. simpl.
      rewrite update_hit; auto. apply runtime_getObj_dom in H1; auto.
    + exists vals.
      admit.
  - (* SBS_New *)
    exists vals.
    unfold runtime_getObj.
Admitted.

Lemma Forall2_length : forall {A B} (P : A -> B -> Prop) l1 l2,
  Forall2 P l1 l2 ->
  List.length l1 = List.length l2.
Proof.
  intros A B P l1 l2 H.
  induction H; [reflexivity | simpl; f_equal; assumption].
Qed.

Lemma Forall_nth_error_wf_class : forall CT CT' C def,
  Forall (wf_class CT) CT' ->
  find_class CT' C = Some def ->
  wf_class CT def.
Proof.
  intros CT CT' C def Hforall Hfind.
  generalize dependent C.
  induction CT' as [|cdef CT'' IH]; intros C Hfind.
  - simpl in Hfind.   exfalso.
  destruct C; simpl in Hfind; discriminate.
  - simpl in Hfind.
    destruct C as [|C'].
    + injection Hfind as Heq. subst def.
      inversion Hforall; subst.
      exact H1.
    + inversion Hforall; subst.
    apply IH with (C := C').
    * exact H2.
    * exact Hfind.
Qed.

Lemma find_class_wf_class : forall CT C def,
  wf_class_table CT ->
  find_class CT C = Some def ->
  wf_class CT def.
Proof.
  intros CT C def Hwf_ct Hfind.
  unfold wf_class_table in Hwf_ct.
  (* Use induction on CT to find the class at position C *)
  generalize dependent C.
  induction CT as [|cdef CT' IH]; intros C Hfind.
  - (* Empty CT case *)
  exfalso.
  destruct C; simpl in Hfind; discriminate.

  - (* Non-empty CT case *)
    simpl in Hfind.
    destruct C as [|C'].
    + (* C = 0, so def = cdef *)
      injection Hfind as Heq. subst def.
      inversion Hwf_ct; subst.
      inversion H; subst.
      exact H3.
    + (* C = S C', recurse *)
      inversion Hwf_ct; subst.
      assert (Hfind_CT' : find_class CT' C' = Some def).
      {
        simpl in Hfind.
        exact Hfind.
      }

      apply (Forall_nth_error_wf_class (cdef :: CT') CT' C' def).
      * inversion H; subst.
      exact H4.
      * exact Hfind_CT'.
Qed.

Lemma vpa_assingability_assign_cases: forall q a,
  vpa_assignability q a = Assignable ->
  (a = Assignable) \/
  (q = Mut /\ a = RDA).
Proof.
  intros q a Hvpa.
  unfold vpa_assignability in Hvpa.
  destruct q, a; simpl in Hvpa; try discriminate; auto.
Qed.

Lemma vpa_type_to_type_imm_cases : forall q1 q2,
  vpa_mutabilty q1 q2 = Imm ->
  (q2 = Imm) \/
  (q1 = Imm /\ q2 = RDM).
Proof.
  intros q1 q2 Hvpa.
  unfold vpa_mutabilty in Hvpa.
  destruct q1, q2; simpl in Hvpa; try discriminate; auto.
Qed.

Lemma vpa_type_to_type_mut_cases : forall q1 q2,
  vpa_mutabilty q1 q2 = Mut ->
  (q2 = Mut) \/
  (q1 = Mut /\ q2 = RDM).
Proof.
  intros q1 q2 Hvpa.
  unfold vpa_mutabilty in Hvpa.
  destruct q1, q2; simpl in Hvpa; try discriminate; auto.
Qed.

Lemma vpa_type_to_type_rdm_cases : forall q1 q2,
  vpa_mutabilty q1 q2 = RDM ->
  (q1 = RDM /\ q2 = RDM).
Proof.
  intros q1 q2 Hvpa.
  unfold vpa_mutabilty in Hvpa.
  destruct q1, q2; simpl in Hvpa; try discriminate; auto.
Qed.

Lemma vpa_type_to_type_bot_cases : forall q1 q2,
  vpa_mutabilty q1 q2 = Bot ->
  (q2 = Bot) \/
  (q1 = Bot /\ q2 = RDM).
Proof.
  intros q1 q2 Hvpa.
  unfold vpa_mutabilty in Hvpa.
  destruct q1, q2; simpl in Hvpa; try discriminate; auto.
Qed.

(* Expression Evaluation Preservation *)
Lemma expr_eval_preservation : forall CT sΓ rΓ h e v rΓ' h' T,
  wf_r_config CT sΓ rΓ h ->
  expr_has_type CT sΓ e T ->
  eval_expr OK CT rΓ h e v OK rΓ' h' ->
  match v with
  | Null_a => True
  | Iot loc => wf_r_typable CT rΓ h loc T
  end.
Proof.
  intros CT sΓ rΓ h e v rΓ' h' T Hwf Htype Heval.
  have Hevalcopy := Heval.
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
  destruct Hwf as [Hwfclass [Hwf_heap [Hwf_renv [Hwf_senv [_ Hcorr]]]]].
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
    destruct Hx_wf as [Hx_base Hx_qualifier].
    eapply field_lookup_deterministic_rel.
    - exact Hfield_lookup_o.
    - apply (field_inheritance_subtyping CT (rctype (rt_type o)) (sctype T0) f fDef).
      + exact Hx_base.
      + exact H9.
  }  
  subst fdef.
  split.
  -- (* Base subtyping *)
    rewrite vpa_type_to_type_sctype.
    simpl.
    apply (qualified_type_subtype_base_subtype CT 
      (runtime_type_to_qualified_type rqt)
      {| sqtype := (mutability (ftype fDef)); 
        sctype := f_base_type (ftype fDef) |}).
    + exact Hsubtype.
    + (* Domain constraints follow from well-formedness *)
      unfold runtime_type_to_qualified_type. simpl.
      assert (Hloc_dom : loc < dom h).
      {
        apply runtime_getObj_dom in Hloc_obj. exact Hloc_obj.
      }
      apply Hwf_heap in Hloc_dom.
      unfold wf_obj in Hloc_dom.
      rewrite Hloc_obj in Hloc_dom.
      destruct Hloc_dom as [Hwf_rtype _].
      unfold wf_rtypeuse in Hwf_rtype.
      destruct (bound CT (rctype rqt)) as [qc|] eqn:Hbound.
      ** 
      assert (Hrqt_eq : rqt = rt_type o_loc).
      {
        unfold r_type in Hrtype_loc.
        rewrite Hloc_obj in Hrtype_loc.
        injection Hrtype_loc as Hrqt_eq.
        symmetry. exact Hrqt_eq.
      }
      rewrite Hrqt_eq in Hbound.
      rewrite Hbound in Hwf_rtype.
      rewrite Hrqt_eq.
      exact Hwf_rtype.
      ** 
      assert (Hrqt_eq : rqt = rt_type o_loc).
      {
        unfold r_type in Hrtype_loc.
        rewrite Hloc_obj in Hrtype_loc.
        injection Hrtype_loc as Hrqt_eq.
        symmetry. exact Hrqt_eq.
      }
      rewrite Hrqt_eq in Hbound.
      rewrite Hbound in Hwf_rtype.
      contradiction Hwf_rtype.
    + 
    simpl.
    assert (Hwf_field : wf_field CT fDef).
    {
      eapply sf_def_rel_wf_field; eauto.
    }
    unfold wf_field, wf_stypeuse in Hwf_field.
    destruct (bound CT (f_base_type (ftype fDef))) as [qc|] eqn:Hbound.
    ** destruct Hwf_field as [_ [_ Hdom]]. exact Hdom.
    ** destruct Hwf_field. exfalso. exact H3.
  -- (* Qualifier typability *)
    unfold vpa_type_to_type.
    destruct (rqtype rqt) as [|] eqn: rq.
    all: try destruct (vpa_mutabilty (q_r_proj q)) as [] eqn:qadapted.
    unfold qualifier_typable; reflexivity.
    3:{unfold qualifier_typable; reflexivity.
    }
    3:{unfold qualifier_typable; reflexivity.
    }
    5:{unfold qualifier_typable; reflexivity.
    }
    6:{unfold qualifier_typable; reflexivity.
    }
    6:{unfold qualifier_typable; reflexivity.
    }
    (* exfalso. *)
    destruct T0 as [sqt0 sct0].
    simpl in qadapted.
    unfold vpa_mutabilty in qadapted.
    destruct (q_r_proj q) eqn: qprojr; try discriminate qadapted.
    destruct sqt0 eqn: sqttest.
    all: try destruct (mutability (ftype fDef)) eqn: qf.
    all: try discriminate.
    all: try
    apply qualified_type_subtype_q_subtype in Hsubtype;
    try unfold runtime_type_to_qualified_type in Hsubtype;
    try simpl in Hsubtype;
    try rewrite rq in Hsubtype;
    try simpl in Hsubtype;
    (* Now Hsubtype : Mut ⊑ Imm *)
    try inversion Hsubtype; try subst.
    all: try
    apply qualified_type_subtype_q_subtype in Hsubtype;
    simpl in Hsubtype.
    all: try unfold runtime_type_to_qualified_type; simpl.
    all: try apply qualified_type_subtype_dom2 in H3.
    all: try simpl H3; try exact H3.

    all: try
    unfold wf_heap in Hwf_heap;
    try assert (Hloc_dom : loc < dom h) by (apply runtime_getObj_dom in Hloc_obj; exact Hloc_obj);
    try apply Hwf_heap in Hloc_dom;
    try unfold wf_obj in Hloc_dom;
    try rewrite Hloc_obj in Hloc_dom;
    try destruct Hloc_dom as [Hwf_rtype _];
    try unfold wf_rtypeuse in Hwf_rtype;
    try destruct (bound CT (rctype (rt_type o_loc))) eqn: boundtest;
    assert (Hrqt_eq : rqt = rt_type o_loc) by (unfold r_type in Hrtype_loc; rewrite Hloc_obj in Hrtype_loc; injection Hrtype_loc; auto);
    try rewrite Hrqt_eq;
    try exact Hwf_rtype.

    all: try destruct sqt0 eqn: sqttest;
    try discriminate qadapted.
    all: try destruct T0 eqn: T0test; simpl in qadapted;
    try destruct vpa_mutabilty eqn: vpa_test;
    try discriminate qadapted.
    all: try easy.
    all: try rewrite <- H2; try rewrite Hrqt_eq; try exact Hwf_rtype.
    {
      apply vpa_type_to_type_rdm_cases with (q1:=q_r_proj q)(q2:=vpa_mutabilty sqtype Mut) in vpa_test.
      destruct vpa_test as [H_mut  H_rdm].
      destruct sqtype; discriminate H_rdm.
    }
    {
      apply vpa_type_to_type_rdm_cases with (q1:=q_r_proj q)(q2:=vpa_mutabilty sqtype Rd) in vpa_test.
      destruct vpa_test as [H_mut  H_rdm].
      destruct sqtype; discriminate H_rdm.
    }
    {
      apply vpa_type_to_type_bot_cases with (q1:=q_r_proj q)(q2:=vpa_mutabilty sqtype Mut) in vpa_test.
      destruct vpa_test as [H_mut | [H_q_mut H_rdm]].
      - (* Case: vpa_mutabilty sqtype Imm = Mut *)
        unfold vpa_mutabilty in H_mut.
        destruct sqtype; discriminate H_mut.
      - (* Case: q_r_proj q = Mut /\ vpa_mutabilty sqtype Imm = RDM *)
        unfold vpa_mutabilty in H_rdm.
        destruct sqtype; discriminate H_rdm.
    }
    {
      apply vpa_type_to_type_bot_cases with (q1:=q_r_proj q)(q2:=vpa_mutabilty sqtype Rd) in vpa_test.
      destruct vpa_test as [H_mut | [H_q_mut H_rdm]].
      - (* Case: vpa_mutabilty sqtype Imm = Mut *)
        unfold vpa_mutabilty in H_mut.
        destruct sqtype; discriminate H_mut.
      - (* Case: q_r_proj q = Mut /\ vpa_mutabilty sqtype Imm = RDM *)
        unfold vpa_mutabilty in H_rdm.
        destruct sqtype; discriminate H_rdm.
    }
    {
      apply vpa_type_to_type_mut_cases with (q1:=q_r_proj q)(q2:=vpa_mutabilty sqtype Imm) in vpa_test.
      destruct vpa_test as [H_mut | [H_q_mut H_rdm]].
      - (* Case: vpa_mutabilty sqtype Imm = Mut *)
        unfold vpa_mutabilty in H_mut.
        destruct sqtype; discriminate H_mut.
      - (* Case: q_r_proj q = Mut /\ vpa_mutabilty sqtype Imm = RDM *)
        unfold vpa_mutabilty in H_rdm.
        destruct sqtype; discriminate H_rdm.
    }
    {
      apply vpa_type_to_type_mut_cases with (q1:=q_r_proj q)(q2:=vpa_mutabilty sqtype Rd) in vpa_test.
      destruct vpa_test as [H_mut | [H_q_mut H_rdm]].
      - (* Case: vpa_mutabilty sqtype Imm = Mut *)
        unfold vpa_mutabilty in H_mut.
        destruct sqtype; discriminate H_mut.
      - (* Case: q_r_proj q = Mut /\ vpa_mutabilty sqtype Imm = RDM *)
        unfold vpa_mutabilty in H_rdm.
        destruct sqtype; discriminate H_rdm.
    }
    {
      apply vpa_type_to_type_rdm_cases with (q1:=q_r_proj q)(q2:=vpa_mutabilty sqtype Imm) in vpa_test.
      destruct vpa_test as [H_mut  H_rdm].
      destruct sqtype; discriminate H_rdm.
    }
    {
      apply vpa_type_to_type_rdm_cases with (q1:=q_r_proj q)(q2:=vpa_mutabilty sqtype Rd) in vpa_test.
      destruct vpa_test as [H_mut  H_rdm].
      destruct sqtype; discriminate H_rdm.
    }
    {
      apply vpa_type_to_type_bot_cases with (q1:=q_r_proj q)(q2:=vpa_mutabilty sqtype Imm) in vpa_test.
      destruct vpa_test as [H_mut | [H_q_mut H_rdm]].
      - (* Case: vpa_mutabilty sqtype Imm = Mut *)
        unfold vpa_mutabilty in H_mut.
        destruct sqtype; discriminate H_mut.
      - (* Case: q_r_proj q = Mut /\ vpa_mutabilty sqtype Imm = RDM *)
        unfold vpa_mutabilty in H_rdm.
        destruct sqtype; discriminate H_rdm.
    }
    {
      apply vpa_type_to_type_bot_cases with (q1:=q_r_proj q)(q2:=vpa_mutabilty sqtype Rd) in vpa_test.
      destruct vpa_test as [H_mut | [H_q_mut H_rdm]].
      - (* Case: vpa_mutabilty sqtype Imm = Mut *)
        unfold vpa_mutabilty in H_mut.
        destruct sqtype; discriminate H_mut.
      - (* Case: q_r_proj q = Mut /\ vpa_mutabilty sqtype Imm = RDM *)
        unfold vpa_mutabilty in H_rdm.
        destruct sqtype; discriminate H_rdm.
    }
  *  exfalso.
    exact Hforall2.
  - exfalso. inversion Hevalcopy.
Qed.

Lemma runtime_lookup_list_preserves_wf_values : forall CT rΓ h zs vals0,
  wf_renv CT rΓ h ->
  runtime_lookup_list rΓ zs = Some vals0 ->
  Forall (fun v => match v with 
    | Null_a => True 
    | Iot loc => match runtime_getObj h loc with Some _ => True | None => False end 
    end) vals0.
Proof.
  intros CT rΓ h zs vals0 Hwf_renv Hlookup.
  unfold runtime_lookup_list in Hlookup.
  unfold wf_renv in Hwf_renv.
  destruct Hwf_renv as [_ [_ Hallvals]].
  
  (* Prove by induction on zs and vals0 simultaneously *)
  generalize dependent vals0.
  induction zs as [|z zs' IH]; intros vals0 Hlookup.
  - (* Base case: zs = [] *)
    simpl in Hlookup.
    injection Hlookup as Hlookup.
    subst vals0.
    constructor.
  - (* Inductive case: zs = z :: zs' *)
    simpl in Hlookup.
    destruct (runtime_getVal rΓ z) as [v|] eqn:Hv; [|discriminate].
    destruct (mapM (runtime_getVal rΓ) zs') as [vs|] eqn:Hvs; [|discriminate].
    injection Hlookup as Hlookup.
    subst vals0.
    constructor.
    + (* Show v is well-formed *)
      destruct v as [|loc].
      * (* Case: Null_a *)
        trivial.
      * (* Case: Iot loc *)
        assert (Hloc_bound : z < dom (vars rΓ)).
        {
          apply runtime_getVal_dom in Hv.
          exact Hv.
        }
        assert (Hloc_wf := Forall_nth_error _ _ _ _ Hallvals Hv).
        simpl in Hloc_wf.
        exact Hloc_wf.
    + (* Show vs is well-formed *)
      apply IH.
      reflexivity.
Qed.

Lemma method_frame_vals_wf : forall CT rΓ h ly vals0 zs cy,
  wf_renv CT rΓ h ->
  r_basetype h ly = Some cy ->
  runtime_lookup_list rΓ zs = Some vals0 ->
  Forall (fun value => match value with
    | Null_a => True
    | Iot loc => match runtime_getObj h loc with Some _ => True | None => False end
    end) (Iot ly :: vals0).
Proof.
  intros CT rΓ h ly vals0 zs cy Hwf_renv Hly_base Hlookup.
  constructor.
  - (* First element: Iot ly *)
    simpl.
    unfold r_basetype in Hly_base.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobj; [trivial | discriminate Hly_base].
  - (* Rest of the list: vals0 *)
    eapply runtime_lookup_list_preserves_wf_values; eauto.
Qed.

Lemma wf_class_in_table : forall CT C,
  wf_class_table CT ->
  wf_class CT C ->
  cname (signature C) < dom CT ->
  find_class CT (cname (signature C)) = Some C.
Proof.
  intros CT C Hwf_ct Hwf_class Hdom.
  unfold wf_class_table in Hwf_ct.
  destruct Hwf_ct as [Hforall [_ [_ Hcname_consistent]]].
  
  (* Use the bidirectional consistency directly *)
  apply Hcname_consistent.
  reflexivity.
Qed.
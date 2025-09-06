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
Qed.

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
  wf_r_typable CT rΓ h loc T1 ->
  qualified_type_subtype CT T1 T2 ->
  wf_r_typable CT rΓ h loc T2.
Proof.
  intros CT rΓ h loc T1 T2 Hwf Hsub.
  unfold wf_r_typable in *.
  destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
  destruct (get_this_var_mapping (vars rΓ)) as [ι'|] eqn:Hthis; [|contradiction].
  destruct (r_muttype h ι') as [q|] eqn:Hmut; [|contradiction].
  eapply qtype_trans; eauto.
  apply vpa_qualified_type_preserves_subtype.
  - apply q_r_proj_imm_or_mut.
  - exact Hsub.
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
  assert (Hfield_lookup : exists fdef, 
    nth_error (collect_fields CT (rctype (rt_type o))) f = Some fdef /\
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
    rewrite Hdom_eq in Hf_in_dom.
    (* Now f is in domain of collect_fields, so nth_error succeeds *)
    assert (Hfdef_exists : exists fdef, nth_error (collect_fields CT (rctype (rt_type o))) f = Some fdef).
    {
      destruct (nth_error (collect_fields CT (rctype (rt_type o))) f) as [fdef|] eqn:Hfdef_lookup.
  - (* f is in bounds, nth_error succeeds *)
    exists fdef. reflexivity.
  - (* f is out of bounds, contradiction *)
    exfalso.
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
    (* Combine the results *)
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

(* Lemma new_object_wf_r_typable : forall CT sΓ rΓ h x qc C qthisr qadapted sqt vals l1 vs,
  x <> 0 ->
  static_getType sΓ x = Some sqt ->
  qualified_type_subtype CT {| sqtype := q_c_proj qc; sctype := C |} sqt ->
  vars rΓ = Iot l1 :: vs ->
  r_muttype h l1 = Some qthisr ->
  q_project_q_r (ViewpointAdaptation.vpa_mutabilty (q_r_proj qthisr) (q_c_proj qc)) = Some qadapted ->
  wf_r_typable CT 
    (rΓ <| vars := update x (Iot (dom h)) (vars rΓ) |>)
    (h ++ [{| rt_type := {| rqtype := qadapted; rctype := C |}; fields_map := vals |}])
    (dom h) 
    sqt.
Proof.
  intros CT sΓ rΓ h x qc C qthisr qadapted sqt vals l1 vs Hx_neq_0 Hstatic_type Hsubtype Hvars Hmut_this Hvpa.
  unfold wf_r_typable.
  unfold r_type.
  rewrite runtime_getObj_last.
  simpl.
  unfold get_this_var_mapping.
  rewrite Hvars.
  simpl.
  destruct x as [|x'].
  - (* x = 0 - contradiction *)
    contradiction Hx_neq_0. reflexivity.
  - (* x = S x' *)
    simpl.
    unfold r_muttype.
    rewrite heap_extension_preserves_objects.
    + (* Prove l1 < dom h *)
    unfold r_muttype in Hmut_this.
    destruct (runtime_getObj h l1) as [obj|] eqn:Hobj; [|discriminate].
    apply runtime_getObj_dom in Hobj.
    exact Hobj.
    + 
    {
      unfold r_muttype in Hmut_this.
      destruct (runtime_getObj h l1) as [obj|] eqn:Hobj.
      - (* l1 exists in heap *)
      simpl in Hmut_this.
      injection Hmut_this as Hmut_eq.
      subst qthisr.
      assert (Hrt_eq : runtime_type_to_qualified_type {| rqtype := qadapted; rctype := C |} = 
                {| sqtype := q_r_proj qadapted; sctype := C |}).
      { unfold runtime_type_to_qualified_type. simpl. reflexivity. }
      rewrite Hrt_eq.
      (* Now we need to connect q_r_proj qadapted with q_c_proj qc through VPA *)
      assert (Hvpa_eq : q_r_proj qadapted = vpa_mutabilty (q_r_proj (rqtype (rt_type obj))) (q_c_proj qc)).
      {
        unfold q_project_q_r in Hvpa.
        destruct (vpa_mutabilty (q_r_proj (rqtype (rt_type obj))) (q_c_proj qc)) eqn:Hvpa_result.
        - (* Mut case *)
          injection Hvpa as Hvpa_inj.
          subst qadapted.
          simpl. reflexivity.
        - (* Imm case *)
          injection Hvpa as Hvpa_inj.
          subst qadapted.
          simpl. reflexivity.
        - (* RDM case - should not happen for q_r *)
          discriminate Hvpa.
        - (* Rd case - should not happen for q_r *)
          discriminate Hvpa.
        - (* Lost case - should not happen for q_r *)
          discriminate Hvpa.
        - (* Bot case - should not happen for q_r *)
          discriminate Hvpa.
      }
      eapply qtype_trans.
      + (* First show: qualified_type_subtype CT {| sqtype := q_c_proj qc; sctype := C |} sqt *)
        apply qtype_sub.
  * (* C < dom CT *)
    assert (Hc_dom : C < dom CT).
    {
      (* Extract from the original subtyping hypothesis *)
      inversion Hsubtype; subst.
      - exact H0.
      - admit. (* Handle transitivity case *)
      - admit. (* Handle reflexivity case *)
    }
    exact Hc_dom.
  * (* C < dom CT *)
    assert (Hc_dom : C < dom CT).
    {
      inversion Hsubtype; subst.
      - exact H0.
      - admit.
      - admit.
    }
    exact Hc_dom.
  * (* q_subtype between VPA result and qc *)
    rewrite Hvpa_eq.
    (* VPA result should be subtype of original qc *)
    admit.
  * (* base_subtype reflexivity *)
    apply base_refl.
    assert (Hc_dom : C < dom CT).
    {
      inversion Hsubtype; subst.
      - exact H0.
      - admit.
      - admit.
    }
    exact Hc_dom.
      + (* Then show: qualified_type_subtype CT sqt (vpa_qualified_type (q_r_proj (rqtype (rt_type obj))) sqt) *)
        unfold vpa_qualified_type.
        destruct sqt as [sq sc].
        simpl.
        apply qtype_sub.
        * apply static_getType_dom in Hstatic_type. exact Hstatic_type.
        * apply static_getType_dom in Hstatic_type. exact Hstatic_type.
        * apply q_refl. admit.
        * apply base_refl. apply static_getType_dom in Hstatic_type. exact Hstatic_type.
      simpl.
      (* Now we need to prove the subtyping relationship *)
      apply vpa_qualified_type_preserves_subtype.
      exact Hsubtype.
      - (* l1 doesn't exist - contradiction *)
      discriminate Hmut_this.
    }
Admitted. *)

(* Lemma field_def_preserved_subtype :
  forall CT C1 C2 f fdef,
    base_subtype CT C1 C2 ->
    sf_def CT C2 f = Some fdef ->
    sf_def CT C1 f = Some fdef.
Proof.
  intros CT C1 C2 f fdef Hsubtype Hfield_def.
  unfold sf_def in *.
  (* sf_def CT C f = gget (fields CT C) f *)
  (* fields CT C = collect_fields CT C *)
  
  (* The key insight: if C1 <: C2, then collect_fields CT C1 includes all fields from collect_fields CT C2 *)
  (* This should follow from how inheritance works *)
  
  (* We need a lemma about collect_fields and subtyping *)
  assert (Hfields_include : forall f fdef, 
    gget (collect_fields CT C2) f = Some fdef ->
    gget (collect_fields CT C1) f = Some fdef).
  {
    intros f0 fdef0 Hfield_C2.
    (* The proof depends on how collect_fields works with inheritance *)
    (* If C1 <: C2, then collect_fields CT C1 should include all fields from collect_fields CT C2 *)

    (* We need to use the definition of collect_fields and base_subtype *)
    (* collect_fields traverses the inheritance hierarchy *)
    unfold collect_fields in *.
    unfold collect_fields_fuel in *.

    (* The key insight: base_subtype means C1 is in the inheritance chain of C2 *)
    (* So when collect_fields_fuel traverses C1's hierarchy, it will eventually reach C2 *)
    (* and include all fields from C2 *)

    (* This requires induction on the subtyping derivation *)
    induction Hsubtype.
    - (* base_refl case: C1 = C2 *)
      exact Hfield_C2.
    - (* base_trans case: C1 <: C_mid <: C2 *)
      (* apply IHHsubtype1.
      apply IHHsubtype2.
      exact Hfield_C2. *)
      admit.
- (* base_step case: direct inheritance *)
  assert (HfindC : exists def, find_class CT C = Some def).
  {
    (* Since C < dom CT, find_class must succeed *)
    destruct (find_class CT C) as [def|] eqn:Hfind.
    - exists def. reflexivity.
    - exfalso. 
      unfold find_class in Hfind.
      apply gget_not_dom in Hfind.
      lia.
  }
  destruct HfindC as [def HfindC].
  
  (* Extract the parent relationship *)
  assert (Hsuper : super (signature def) = Some D).
  {
    unfold parent in H1.
    rewrite HfindC in H1.
    simpl in H1.
    exact H1.
  }
    unfold gget in *.

  destruct (dom CT) as [|fuel'] eqn:Hfuel.
  + (* dom CT = 0 - contradiction *)
    assert (C < 0) by (rewrite <- Hfuel; rewrite <- Hfuel in H; exact H).
    lia.
  + simpl.
    rewrite HfindC.
    rewrite Hsuper.
    
    (* The key insight: we need to extract the right part from Hfield_C2 *)
    (* Hfield_C2 shows: nth_error (collect_fields_fuel (S fuel') CT D) f0 = Some fdef0 *)
    (* We need: nth_error (collect_fields_fuel fuel' CT D) f0 = Some fdef0 *)
    
    (* Let's unfold collect_fields_fuel in Hfield_C2 *)
    simpl in Hfield_C2.
    
    (* Now Hfield_C2 should have the structure we can work with *)
    destruct (find_class CT D) as [defD|] eqn:HfindD.
    * (* D found in CT *)
      destruct (super (signature defD)) as [parentD|] eqn:HsuperD.
      -- (* D has a parent *)
        (* Hfield_C2 now has: nth_error (collect_fields_fuel fuel' CT parentD ++ fields (body defD)) f0 = Some fdef0 *)
        (* We can use nth_error_app to extract which part contains the field *)
        destruct (nth_error (collect_fields_fuel fuel' CT parentD) f0) as [fdef_parent|] eqn:Hparent_field.
        ++ (* Field found in parent - use it directly *)
          apply nth_error_app1.
          ** exact Hparent_field.
          ** apply nth_error_Some. rewrite <- Hparent_field. discriminate.
        ++ (* Field not in parent, must be in D's own fields *)
          apply nth_error_app1.
          ** (* We need to show the field is in collect_fields_fuel fuel' CT D *)
             (* Since the field is in D's complete field list, and not in parent, *)
             (* it must be in D's own fields, which are included in collect_fields_fuel fuel' CT D *)
             simpl. rewrite HfindD. rewrite HsuperD.
             apply nth_error_app2.
             --- exact Hparent_field.
             --- (* Extract from Hfield_C2 that the field is in body fields *)
                 assert (Hbody_field : nth_error (Syntax.fields (body defD)) (f0 - length (collect_fields_fuel fuel' CT parentD)) = Some fdef0).
                 {
                   apply nth_error_app2_inv in Hfield_C2.
                   - exact Hfield_C2.
                   - exact Hparent_field.
                 }
                 exact Hbody_field.
          ** apply nth_error_Some. rewrite <- Hfield_C2. discriminate.
      -- (* D has no parent *)
        (* Simpler case - field must be in D's own fields *)
        apply nth_error_app1.
        ** simpl. rewrite HfindD. rewrite HsuperD. simpl. exact Hfield_C2.
        ** apply nth_error_Some. rewrite <- Hfield_C2. discriminate.
    * (* D not found - contradiction *)
      unfold find_class in HfindD.
      apply gget_not_dom in HfindD.
      lia.
  }
  
  apply Hfields_include.
  exact Hfield_def.
Qed.

Lemma runtime_static_assignability_consistency :
  forall CT rΓ h loc Tx C f a qr fields,
    wf_r_typable CT rΓ h loc Tx ->
    runtime_getObj h loc = Some (mkObj (mkruntime_type qr C) fields) ->
    sf_assignability CT (sctype Tx) f = Some a ->
    base_subtype CT C (sctype Tx) ->
    sf_assignability CT C f = Some a.
Proof.
  intros CT rΓ h loc Tx C f a qr fields Hwf_typable Hruntime_obj Hstatic_assign Hsubtype.

  (* The key insight: field assignability is preserved down the subtyping hierarchy *)
  (* If C <: sctype Tx, then field f has the same assignability in both *)
  admit. (* This requires a lemma about field assignability and subtyping *)
Qed. *)
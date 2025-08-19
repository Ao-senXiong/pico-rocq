Require Import Syntax Notations Helpers Typing Subtyping Bigstep.
Require Import List.
Import ListNotations.
Require Import String.
From RecordUpdate Require Import RecordUpdate.
Require Import Coq.Logic.Classical_Prop.
Require Import NZOrder.

(* ------------------------------------------------------------- *)
(* Soundness properties for PICO *)
Theorem preservation_pico :
  forall CT sΓ rΓ h stmt rΓ' h' sΓ',
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ stmt sΓ' -> 
    eval_stmt OK rΓ h stmt OK rΓ' h' -> 
    wf_r_config CT sΓ' rΓ' h'.
Proof.
  intros.
  generalize dependent h. generalize dependent rΓ.
  generalize dependent h'. generalize dependent rΓ'.
  induction H0.
  - (* Case: stmt = Skip *)
    intros.
    inversion H1; subst.
    exact H0.
  - (* Case: stmt = Local *)
    intros.
    inversion H4; subst.
    unfold wf_r_config in *.
    destruct H3 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    repeat split.
    + (* wellformed class *) exact Hclass.
    + (* wellformed heap *) exact Hheap.
    + (* Length of runtime environment greater than 0 *)
    simpl. rewrite length_app. simpl. lia.
    + (* The first element of runtime environment is not null *)
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      destruct Hreceiverval as [iot Hiot].
      exists iot.
      simpl.
      unfold gget in *.
      destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
      * (* Case: vars rΓ = [] *)
        exfalso.
        (* rewrite Hvars in HrEnvLen. *)
        simpl in HrEnvLen.
        lia.
      * (* Case: vars rΓ = v0 :: vs *)
        simpl.
        exact Hiot.
    + (* wellformed runtime environment *)  
    unfold wf_renv in *.
    simpl.
    apply Forall_app.
    split.
    * destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]]. exact Hallvals.
    * constructor.
      -- trivial.
      -- constructor.  
    + (* Length of static environment greater than 0 *)
    destruct Hsenv as [HsenvLength HsenvWellTyped]. rewrite length_app.
    simpl. lia.
    + (* wellformed static environment *)
      unfold wf_senv in *. apply Forall_app. split.
      * destruct Hsenv as [HsenvLength HsenvWellTyped]. exact HsenvWellTyped.
      * destruct H as [_ HTWellTyped]. 
        constructor.
        -- exact H0. (* assuming H is the wellformedness of T *)
        -- constructor. (* empty tail is well-typed *)
    + (* length equality *)
      simpl. rewrite length_app. simpl. rewrite Hlen. rewrite length_app. simpl. lia.
    + (* correspondence between static and runtime environments *)
      intros i Hi sqt Hnth.
      destruct (Nat.eq_dec i (dom sΓ)) as [Heq | Hneq].
      * (* Case: i = dom sΓ (new variable) *)
        subst i.
        unfold runtime_getVal.
        simpl.
        rewrite nth_error_app2.
        -- rewrite Hlen.
           trivial.
        -- rewrite Hlen.
           assert (dom (vars rΓ) - dom (vars rΓ) = 0) by lia.
            rewrite H2.
            simpl.
            trivial.
      * (* Case: i < dom sΓ (existing variable) *)
        assert (Hi_old : i < dom sΓ).
        {
          simpl in Hi. rewrite length_app in Hi. simpl in Hi.
          lia.
        }
        assert (Hnth_old : nth_error sΓ i = Some sqt).
        {
          have Happ := nth_error_app1 sΓ [T] Hi_old.
          rewrite Happ in Hnth.
          exact Hnth.
        }
        specialize (Hcorr i Hi_old sqt Hnth_old).
        unfold runtime_getVal in *.
        simpl.
        rewrite nth_error_app1.
        -- rewrite <- Hlen. exact Hi_old.
        --
           destruct (nth_error (vars rΓ) i) as [v|] eqn:Hgetval.
           ++ (* Case: nth_error (vars rΓ) i = Some v *)
              destruct v as [|loc].
              ** trivial.
              ** admit.
           ++ (* Case: nth_error (vars rΓ) i = None *)
              exfalso.
              apply nth_error_None in Hgetval.
              rewrite <- Hlen in Hgetval.
              lia.
  - (* Case: stmt = VarAss *)
    intros.
    inversion H5; subst.
    unfold wf_r_config in *.
    destruct H4 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    repeat split.
    + (* wellformed class *) exact Hclass.
    + (* wellformed heap *) exact Hheap.
    + (* Length of runtime environment greater than 0 *)
      simpl. destruct Hsenv as [HsenvLength HsenvWellTyped].      
      rewrite update_length.
      rewrite <- Hlen.
      exact HsenvLength.
    + (* The first element of runtime environment is not null *)
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      destruct Hreceiverval as [iot Hiot].
      exists iot.
      simpl.
      unfold gget in *.
      destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
      * (* Case: vars rΓ = [] *)
        exfalso.
        (* rewrite Hvars in HrEnvLen. *)
        simpl in HrEnvLen.
        lia.
      * (* Case: vars rΓ = v0 :: vs *)
        destruct x as [|x'].
           -- (* x = 0 *) contradiction.
           -- (* x = S x' *)
              simpl. (* update (S x') v2 (v0 :: vs) = v0 :: update x' v2 vs *)
              exact Hiot.
    + (* wellformed runtime environment *)
      (* unfold wf_renv in *.
      destruct Hrenv as [Hreceiver [Hreceiverval Hallvals]].
      repeat split.
      * (* receiver at index 0 *)
        exact Hreceiver.
      * (* receiver value wellformed *)
        exact Hreceiverval.
      * (* all values wellformed *)
        apply Forall_forall.
        intros v Hin.
        apply Forall_forall with (x := v) in Hallvals; [exact Hallvals |].
        Show that updating one variable doesn't affect wellformedness of other values *)
        admit.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. exact HsenvLength. 
    + (* wellformed static environment *)
      destruct Hsenv as [HsenvLength HsenvWellTyped]. exact HsenvWellTyped.
    + (* length equality *)
      simpl.
      rewrite update_length.
      exact Hlen.
    + (* correspondence between static and runtime environments *)
      intros i Hi sqt Hnth.
      destruct (Nat.eq_dec i x) as [Heq | Hneq].
      * (* Case: i = x (updated variable) *)
        subst i.
        unfold runtime_getVal.
        simpl.
        rewrite update_same.
        (* Need to show v2 is well-typed with respect to T' *)
        assert (Hsubtype: qualified_type_subtype CT Te Tx) by exact H3.
        assert (Hexpr_type: expr_has_type CT sΓ e Te) by exact H0.
        rewrite <- Hlen; exact Hi.
        destruct v2 as [|loc].
        -- (* Case: v2 = Null_a *)
          trivial.
        -- (* Case: v2 = Iot loc *)
          (* Use subtyping to convert from T to sqt *)
          assert (Hsubtype_preserved : wf_r_typable CT (rΓ <| vars := update x (Iot loc) (vars rΓ) |>) h' loc sqt).
          {
            admit.
            (* Apply subtyping preservation *)
            (* eapply wf_r_typable_subtype.
            - (* Show that extending environment preserves well-typedness *)
              eapply wf_r_typable_extend_env.
              exact Hv2_type.
            - (* Use the subtyping relation H3 *)
              exact H3. *)
          }
          exact Hsubtype_preserved.
      * (* Case: i ≠ x (unchanged variable) *)
        unfold runtime_getVal.
        simpl.
        (* rewrite update_nth_diff; [| exact Hneq].
        (* Use original correspondence for unchanged variables *)
        specialize (Hcorr i Hi sqt Hnth).
        exact Hcorr. *)
    admit.
  - (* Case: stmt = FldWrite *)
    intros.
    inversion H7; subst.
    unfold wf_r_config in *.
    destruct H6 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    repeat split.
    + (* wellformed class *) exact Hclass.
    + (* wellformed heap *) admit.
    + (* Length of runtime environment greater than 0 *)
      simpl. destruct Hsenv as [HsenvLength HsenvWellTyped].      
      rewrite <- Hlen.
      exact HsenvLength.
    +
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      destruct Hreceiverval as [iot Hiot].
      exists iot.
      simpl.
      unfold gget in *.
      destruct (vars rΓ') as [|v0 vs] eqn:Hvars.
      * (* Case: vars rΓ = [] *)
        exfalso.
        (* rewrite Hvars in HrEnvLen. *)
        simpl in HrEnvLen.
        lia.
      * (* Case: vars rΓ = v0 :: vs *)
        destruct x as [|x'].
           (* -- x = 0 contradiction. *)
           -- (* x = S x' *)
              exact Hiot.
           --    (* update (S x') v2 (v0 :: vs) = v0 :: update x' v2 vs *)
              exact Hiot.
    + admit.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. exact HsenvLength.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. exact HsenvWellTyped.
    + exact Hlen.
    + admit.
  - (* Case: stmt = New *)
    intros.
    inversion H10; subst.
    unfold wf_r_config in *.
    destruct H9 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    repeat split.
    + (* wellformed class *) exact Hclass.
    + (* wellformed heap *) admit.
    + (* Length of runtime environment greater than 0 *)
      simpl. destruct Hsenv as [HsenvLength HsenvWellTyped].      
      rewrite update_length. rewrite <- Hlen.
      exact HsenvLength.
    +
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      destruct Hreceiverval as [iot Hiot].
      exists iot.
      simpl.
      unfold gget in *.
      destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
      * (* Case: vars rΓ = [] *)
        exfalso.
        (* rewrite Hvars in HrEnvLen. *)
        simpl in HrEnvLen.
        lia.
      * (* Case: vars rΓ = v0 :: vs *)
        destruct x as [|x'].
           (* -- x = 0 contradiction. *)
           -- (* x = S x' *)
              admit.
           --    (* update (S x') v2 (v0 :: vs) = v0 :: update x' v2 vs *)
              exact Hiot.
    + admit.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. exact HsenvLength.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. exact HsenvWellTyped.
    + rewrite update_length. rewrite <- Hlen. lia.
    + admit.
  - (* Case: stmt = Call *)
    intros.
    inversion H8; subst.
    unfold wf_r_config in *.
    destruct H7 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    repeat split.
    + (* wellformed class *) exact Hclass.
    + admit.
    + (* Length of runtime environment greater than 0 *)
      simpl. destruct Hsenv as [HsenvLength HsenvWellTyped].      
      rewrite update_length. rewrite <- Hlen.
      exact HsenvLength.
    + admit.
    + admit.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. exact HsenvLength.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. exact HsenvWellTyped.
    + rewrite update_length. exact Hlen.
    + admit.
  - (* Case: stmt = Seq *)
    intros. inversion H1; subst.
    specialize (IHstmt_typing1 rΓ'0 h'0 rΓ h H H3) as IH1.
    specialize (IHstmt_typing2 rΓ' h' rΓ'0 h'0 IH1 H6) as IH2.
    exact IH2.
Admitted.

(* ------------------------------------------------------------- *)
(* Immutability properties for PICO *)
Notation "l [ i ]" := (nth_error l i) (at level 50).

Theorem immutability_pico :
  forall CT sΓ rΓ h stmt rΓ' h' sΓ' l C vals vals' f,
    l < dom h ->
    runtime_getObj h l = Some (mkObj (mkruntime_type (exist _ Imm (or_intror eq_refl)) C) vals) ->
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ stmt sΓ' -> 
    eval_stmt OK rΓ h stmt OK rΓ' h' -> 
    runtime_getObj h' l = Some (mkObj (mkruntime_type (exist _ Imm (or_intror eq_refl)) C) vals') ->
    sf_assignability CT C f = Some Final \/ sf_assignability CT C f = Some RDA ->
    nth_error vals f = nth_error vals' f.
Proof.
  intros. induction H3.
  - (* Skip *) inversion H4. intros; subst; rewrite H0 in H4; injection H4; auto.
  - (* Local *) inversion H4; intros; subst; rewrite H0 in H4; injection H4; auto.
  - (* VarAss *) inversion H4; intros; subst; rewrite H0 in H4; injection H4; auto.
  - (* NPE case *) admit.
  - (* FldWrite *) 
    (* Key case: show contradiction with can_assign for immutable Final/RDA fields *)
    admit.
  - (* NPE case *) admit.
  - (* New *) (* h' = h ++ [new_obj], so l < dom h means same object *)
  intros.
  inversion H4; subst.
  (* Since l < dom h, the object at location l is unchanged *)
  unfold runtime_getObj in H14.
  rewrite List.nth_error_app1 in H14; auto.
  unfold runtime_getObj in H0.
  rewrite H0 in H14.
  injection H14; intros; subst.
  reflexivity.
  - (* Call *) (* Similar to other non-mutating cases *) 
  intros.
  (* Apply IH to method body execution *)
  assert (Hwf_method: wf_r_config CT sΓ' rΓ' h).
  {
    unfold wf_r_config in *.
    destruct H1 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    repeat split.
    - exact Hclass.
    - exact Hheap.
    - rewrite H11. simpl. lia.
    - exists ly. rewrite H11. simpl. reflexivity.
    - admit. (* Where to introduce static environment inside the body*)
    - admit.
    - admit.
    - admit.
    - admit. 
  }
  assert (Htyping_method: stmt_typing CT sΓ mstmt sΓ').
  {
    admit.
  }
  (* specialize (IHeval_stmt H H0 Hwf_method Htyping_method H4) as IH.
  exact IH. *)
  admit.
  - (* NPE case*) admit. 
  - (* NPE case*) admit. 
  - (* Seq *) (* Apply IH transitively *) 
  admit.
  - (* NPE case*) admit.  
  - (* NPE case*) admit. 
Admitted.

Theorem readonly_pico :
    forall CT sΓ rΓ h stmt rΓ' h' sΓ' l C vals vals' f qt readonlyx anyf rhs lhs anymethod anyrq,
      stmt = (SFldWrite readonlyx anyf rhs) \/ stmt =  SCall lhs anymethod readonlyx [] -> 
      static_getType sΓ readonlyx = Some qt ->
      (* This is the interesting part, I think I have to supply empty arguments or all arguments as immutable because otherwise I don't if the readonly receiver is aliased with some mutable part *)
      wf_r_config CT sΓ rΓ h ->
      stmt_typing CT sΓ stmt sΓ' -> 
      eval_stmt OK rΓ h stmt OK rΓ' h' -> 
      runtime_getVal rΓ readonlyx = Some (Iot l)  ->
      runtime_getObj h l = Some (mkObj (mkruntime_type anyrq C) vals) ->
      runtime_getObj h' l = Some (mkObj (mkruntime_type anyrq C) vals') ->
      sf_assignability CT C f = Some Final \/ sf_assignability CT C f = Some RDA ->
      nth_error vals f = nth_error vals' f.
      (*This looks like shallow mutability to me, but my language does not allow x.f1.f2 = y.*)
Proof.
Admitted.

(* Inductive reachability : heap -> Loc -> Loc -> Prop :=

(* we can access the current location *)
| rch_heap:
    forall l h,
      l < dom h ->
      reachability h l l

(* we can access a location in the local environment of the object at l0 *)
| rch_step:
    forall l0 l1 f obj v loc h,
      l1 < dom h ->
      getObj h l0 = Some obj ->
      getVal obj.(fields_map) f = Some v -> 
      v = Iot loc ->
      loc = l1 ->
      reachability h l0 l1

(* transitive case *)
| rch_trans:
    forall l0 l1 l2 h,
      reachability h l0 l1 ->
      reachability h l1 l2 ->
      reachability h l0 l2.
Global Hint Constructors reachability: rch. *)

(* Field is in the abstract state if it is qualified by Immut/RDM and Final/RDA *)
(* Reachability by the abstract state *)
(* Inductive reach_by_abstract_state: class_table -> heap -> s_env -> r_env -> Loc -> Loc -> Prop :=
| rch_abs_heap:
    forall ct l h sΓ rΓ,
      l < dom h ->
      reach_by_abstract_state ct h sΓ rΓ l l
| rch_abs_step:
    forall ct l0 l1 c f obj v qf loc h sΓ rΓ,
      l1 < dom h ->
      getObj h l0 = Some obj ->
      getVal obj.(fields_map) f = Some v -> 
      v = Iot loc ->
      loc = l1 ->
      r_basetype h l0 = Some c -> (* Base type of the object at l0 is c *)
      sf_mutability ct c f = Some qf ->
      q_f_proj qf = Imm /\ q_f_proj qf = RDM -> (* Mutability of field is either Imm or RDM *)
      sf_assignability ct c f = Some Final /\ sf_assignability ct c f = Some RDA -> (* Field is Final/RDA *)
      reach_by_abstract_state ct h sΓ rΓ l0 l1
| rch_abstract_state_trans:
    forall ct l0 l1 l2 h sΓ rΓ,
      reach_by_abstract_state ct h sΓ rΓ l0 l1 ->
      reach_by_abstract_state ct h sΓ rΓ l1 l2 ->
      reach_by_abstract_state ct h sΓ rΓ l0 l2.
Global Hint Constructors reach_by_abstract_state: rch_abs. *)

(* Inductive abstract_equality : class_table -> heap -> s_env -> r_env -> Loc -> Loc -> Prop :=
| abs_eq_refl:
    forall ct h sΓ rΓ l,
      l < dom h ->
      abstract_equality ct h sΓ rΓ l l
| abs_eq_fields :
    forall ct h sΓ rΓ l0 l1 obj0 obj1 f v0 v1 loc0 loc1,
      l1 < dom h ->
      getObj h l0 = Some obj0 ->
      getObj h l1 = Some obj1 ->
      getVal obj0.(fields_map) f = Some v0 ->
      getVal obj1.(fields_map) f = Some v1 ->
      v0 = Null_a /\ v1 = Null_a \/
      v0 = Iot loc0 /\ v1 = Iot loc1 /\ abstract_equality ct h sΓ rΓ loc0 loc1
       ->
      abstract_equality ct h sΓ rΓ l0 l1. *)

(* Fixpoint vpa_assignability_by_loc: h -> l0 -> l1     *)
(* Inductive vpa_assign_reachability : heap -> Loc -> Loc -> a -> Prop :=

(* we can access the current location *)
| rch_heap:
    forall l h a,
      l < dom h ->
      reachability h l l a

(* we can access a location in the local environment of the object at l0 *)
| rch_step:
    forall l0 l1 f obj q v loc h a,
      l1 < dom h ->
      getObj h l0 = Some obj ->
      obj.(rt_type) = q ->
      vpa_assignability (q_r_proj q) a = Assignable ->
      getVal obj.(fields_map) f = Some v -> 
      v = Iot loc ->
      loc = l1 ->
      reachability h l0 l1

(* transitive case *)
| rch_trans:
    forall l0 l1 l2 h,
      reachability h l0 l1 ->
      reachability h l1 l2 ->
      reachability h l0 l2. *)

(* Lemma reachable_abs_object_unassignable_by_readonly_reference: *)

(* Lemma reachable_abs_object_unassignable_for_immutable_object:
  forall ct h sΓ rΓ l0 l1:
    reach_by_abstract_state ct h sΓ rΓ l0 l1 -> *)

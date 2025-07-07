Require Import Syntax Notations Helpers Typing Bigstep.
Require Import List.
Import ListNotations.
Require Import String.
From RecordUpdate Require Import RecordUpdate.
Require Import Coq.Logic.Classical_Prop.

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
    + (* wellformed runtime environment *)  
    unfold wf_renv in *.
    admit.
    + (* wellformed static environment *)
      unfold wf_senv in *.
      admit.
      (* constructor; [exact H0|exact H]. *)
    + (* length equality *)
      simpl.
      admit.
      (* rewrite length_app. simpl. lia. *)
    + (* correspondence between static and runtime environments *)
      admit.
    + admit.
    + admit.
    + admit.
        (* intros i Hi sqt Hnth.
        destruct (Nat.eq_dec i (List.length sΓ + 1)).
        * (* i = last index, new variable *)
          subst i.
          unfold runtime_getVal.
          admit.
        * (* i < List.length sΓ, old variables *)
          admit. *)
  - (* Case: stmt = VarAss *)
    admit.
  - (* Case: stmt = FldWrite *)
    admit.
  - (* Case: stmt = New *)
    admit.
  - (* Case: stmt = Call *)
    admit.
  - (* Case: stmt = Seq *)
Admitted.

Theorem progress_pico :
  forall CT sΓ rΓ h stmt sΓ',
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ stmt sΓ' ->
    exists rΓ' h', eval_stmt OK rΓ h stmt OK rΓ' h' \/ eval_stmt OK rΓ h stmt NPE rΓ' h'.
Proof.
  intros. 
  generalize dependent h. generalize dependent rΓ.
  (* do induction, while give names to each introduced item. *)
  induction H0 as [H0 | CT sΓ T x sΓ' H0 H1 H2 H3 
  | CT sΓ x e T T' H0 H1 H2 H3 
  | CT sΓ x f y Tx Ty fieldT H0 H1 H2 H3 H4 H5
  | CT sΓ x Tx q C args argtypes n1 consig H0 H1 H2 H3 H4 H5 H6 
  | CT sΓ x m y args argtypes Tx Ty m_sig  H0 H1 H2 H3 H4 H5 H6 H7  
  | CT sΓ s1 sΓ' s2 sΓ'' H0_ IHstmt_typing1 H0_0 IHstmt_typing2 ]; intros.
  - (* Case: stmt = Skip *)
    exists rΓ, h.
    left.
    apply SBS_Skip.
  - (* Case: stmt = Local *)
    exists (rΓ <| vars := rΓ.(vars)++[Null_a] |>), h.
    left.
    apply SBS_Local.
    unfold wf_r_config in H.
    unfold getVal.
    rewrite nth_error_None.
    replace (dom (vars rΓ)) with dom sΓ. 
    unfold static_getType in H2.
    eapply nth_error_None in H2.
    exact H2.
    destruct H as [ _ [ _ [ _ [ _ [Hdom _]]]]].
    exact Hdom.
  - (* Case: stmt = VarAss *)
    (* Evaluate e first *)
    destruct e.
    + (* Case: e = ENull *)
      exists (rΓ <| vars := update x Null_a rΓ.(vars)|>), h. 
      destruct H as [ _ [ _ [ _ [ _ [_ Hresult]]]]].
      unfold static_getType in H2.
      destruct (runtime_getVal rΓ x) eqn:Hgetval.
      * 
        left. eapply SBS_Assign; [ exact Hgetval | constructor ].
      * 
        exfalso.
        assert (x < dom sΓ) by (apply nth_error_Some; eauto).
        specialize (Hresult x H T' H2).
        rewrite Hgetval in Hresult. exact Hresult.
    + (* Case: e = EVar *)     
      destruct H as [ _ [ _ [ _ [ _ [Henvmatch Hresult]]]]].
      unfold static_getType in H2.
      assert (Hx : x < dom sΓ) by (apply nth_error_Some; eauto).
      specialize (Hresult x Hx T' H2).
      destruct (runtime_getVal rΓ v) eqn:Hgetval.
      * 
        exists (rΓ <| vars := update x v0 rΓ.(vars) |>), h.
        rename v into v1.
        destruct (runtime_getVal rΓ x) eqn:Hgetx.
        --
          left. eapply SBS_Assign; [ exact Hgetx | constructor ].
          exact Hgetval.
        -- 
          exfalso. exact Hresult.
      * 
        exfalso.
        assert (Hv : nth_error sΓ v = Some T) by (inversion H1; auto).
        unfold runtime_getVal in Hgetval.
        assert (v < dom (vars rΓ)) by (rewrite <- Henvmatch; apply nth_error_Some; congruence).
        apply nth_error_None in Hgetval.
        lia.
    + (* Case: e = EField *)
      destruct H as [ _ [ Hheap [ Hrenv [ _ [Henvmatch Hresult]]]]].
      unfold static_getType in H2.
      assert (Hx : x < dom sΓ) by (apply nth_error_Some; eauto).
      pose proof Hresult as Hresult_copy.
      specialize (Hresult_copy x Hx T' H2).
      inversion H1 as [| | ? ? ? ? ? ? Hobj Hfield ]; subst.
      assert (Hv : nth_error sΓ v = Some T0) by (apply Hfield; auto).
      assert (Hv' : v < dom sΓ) by (apply nth_error_Some; auto).
      destruct (runtime_getVal rΓ v) eqn:Hgety.
      *
        destruct v1.
        -- (* Case: v = Null_a *)
          exists rΓ, h.
          right.
          destruct (runtime_getVal rΓ x) eqn:Hgetx.
          ++
            apply SBS_Assign_NPE with v1 Null_a; 
            [ exact Hgetx | apply EBS_Field_NPE; exact Hgety ].
          ++
            exfalso.
            apply runtime_getVal_not_dom in Hgetx.
            lia.
        -- (* Case: v = Iot loc *)
          destruct (runtime_getObj h l) eqn:Hgetval.
          ++ (* can find object by address l *)
            destruct (getVal o.(fields_map) v0) eqn:Hgetfield.
            ** (* Case: field exists *)
              exists (rΓ <| vars := update x v1 rΓ.(vars) |>), h.
              destruct (runtime_getVal rΓ x) eqn:Hgetx.
              ---
                left.
                eapply SBS_Assign.
                +++
                  exact Hgetx.
                +++
                  econstructor.
                  ---- exact Hgety.
                  ---- exact Hgetval.
                  ---- exact Hgetfield.
              ---
                exfalso.    
                auto.
            ** (* Case: field does not exist *)
              exfalso.
              unfold wf_heap in Hheap.
              assert (Hwf_o: wf_obj CT h l).
              {
                apply Hheap.
                apply runtime_getObj_dom in Hgetval.
                exact Hgetval.
              }
              unfold wf_obj in Hwf_o.
              assert (Hwf_o' := Hwf_o).
              rewrite Hgetval in Hwf_o'.
              destruct Hwf_o' as [_ Hdom_eq].
              apply getVal_not_dom in Hgetfield.
              rewrite Hdom_eq in Hgetfield.
              unfold sf_def in H.
              unfold fields in H.
              specialize (Hresult v Hv' T0 Hv).
              rewrite Hgety in Hresult.
              apply r_obj_subtype_sqt with (o := o) (rt := rctype (rt_type o)) in Hresult; [| exact Hgetval | reflexivity ].
              unfold gget in H.
              assert (v0 < dom (collect_fields CT (sctype T0))) by (apply nth_error_Some; congruence).
              specialize (collect_fields_monotone CT (rctype (rt_type o)) (sctype T0) Hresult).
              remember (dom (collect_fields CT (rctype (rt_type o)))) as d1.
              remember (dom (collect_fields CT (sctype T0))) as d2.
              assert (d2 <= d1) by (subst; apply collect_fields_monotone; assumption).
              assert (v0 < d2) by (subst; apply H4).
              assert (v0 >= d1) by (subst; apply Hgetfield).
              lia. (* subtyping polymorphism*)
          ++ (* can not find object by address l *)
            exfalso.
            unfold wf_renv in Hrenv.
            destruct Hrenv as [Hreceiver [Hreceiverval Hrenv]].
            eapply Forall_nth_error in Hrenv as Hfor; [| exact Hgety].
            simpl in Hfor.
            rewrite Hgetval in Hfor.
            exact Hfor.
      *
        exfalso.
        apply runtime_getVal_not_dom in Hgety.
        lia.
  - (* Case: stmt = fldwrite*)
    destruct (runtime_getVal rΓ x) eqn:Hgetx.
    + (* can find x in runtime env*)
      destruct v.
      * (* Case: v = Null_a *)
        exists rΓ, h.
        right.
        apply SBS_FldWrite_NPE.
        exact Hgetx.
      * (* Case: v = Iot loc *)
        destruct H as [ _ [ Hheap [ Hrenv [ _ [Henvmatch Hresult]]]]].
        destruct (runtime_getObj h l) eqn:Hgetval.
        -- (* can find object by address l *)
          destruct (getVal o.(fields_map) f) eqn:Hgetfield.
          ++ (* Case: field exists *)
            destruct (runtime_getVal rΓ y) as [vy |] eqn:Hgety.
            **
              exists rΓ (update_field h l f vy).
              left.
              apply SBS_FldWrite with (CT := CT) (lx := l) (o := o) (vf := v) (v2 := vy); [exact Hgetx | exact Hgetval | exact Hgetfield | exact Hgety | | reflexivity].
              unfold can_assign.
              admit. (* Qualifier subtyping lemma *)
            ** 
              exfalso.
              apply runtime_getVal_not_dom in Hgety.
              apply static_getType_dom in H2.
              lia.
          ++ (* Case: field does not exist *)
            exfalso.
            unfold wf_heap in Hheap.
            assert (Hwf_o: wf_obj CT h l).
            {
              apply Hheap.
              apply runtime_getObj_dom in Hgetval.
              exact Hgetval.
            }
            unfold wf_obj in Hwf_o.
            assert (Hwf_o' := Hwf_o).
            rewrite Hgetval in Hwf_o'.
            destruct Hwf_o' as [_ Hdom_eq].
            apply getVal_not_dom in Hgetfield.
            rewrite Hdom_eq in Hgetfield.
            unfold sf_def in H3.
            unfold fields in H3.
            assert (x < dom sΓ) as Hx.
            {
              unfold static_getType in H1.
              apply nth_error_Some; eauto.
            }
            specialize (Hresult x Hx Tx H1).
            rewrite Hgetx in Hresult.
            apply r_obj_subtype_sqt with (o := o) (rt := rctype
            (rt_type o)) in Hresult; [| exact Hgetval | reflexivity ].
            unfold gget in Hx.
            assert (f < dom (collect_fields CT (sctype Tx))) as Hf.
            {
              unfold gget in H3.
              apply nth_error_Some.
              auto.
            }
            specialize (collect_fields_monotone CT (rctype (rt_type o)) (sctype Tx) Hresult).
            remember (dom (collect_fields CT (rctype (rt_type o)))) as d1.
            remember (dom (collect_fields CT (sctype Tx))) as d2.
            assert (d2 <= d1) by (subst; apply collect_fields_monotone
              ; assumption).
            assert (f < d2) by (subst; apply Hf).
            assert (f >= d1) by (subst; apply Hgetfield).
            lia. (* subtyping polymorphism*)
        -- (* can not find object by address l *)
        exfalso.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [Hreceiver [Hreceiverval Hrenv]].
        eapply Forall_nth_error in Hrenv as Hfor; [| exact Hgetx].
        simpl in Hfor.
        rewrite Hgetval in Hfor.
        exact Hfor.
    + (* can not find x in runtime env*)
      exfalso.
      apply runtime_getVal_not_dom in Hgetx.
      apply static_getType_dom in H1.
      destruct H as [ _ [ _ [ _ [ _ [Henvmatch _]]]]].
      lia.
  - (* Case: stmt = new *)
    destruct (runtime_getVal rΓ x) eqn:Hgetx.
    destruct H as [ _ [ Hheap [ Hrenv [ _ [Henvmatch Hresult]]]]].
    destruct Hrenv as [Hreceiver [Hreceiverval Hrenv]].
    + (* can find x in runtime env*)
      (* TODO(AOSEN): update the heap here  *)
      exists (rΓ <| vars := update x (Iot (dom h + 1)) rΓ.(vars) |>), h.
      left.
      destruct (gget (vars rΓ) 0) as [vrecv |] eqn:Hgetrecv.
      * (* Case: receiver is a variable *)
       destruct vrecv as [|iot].
        -- (* Case: vrecv = Null_a *)
          exfalso.
          specialize (Hreceiverval 0).
          discriminate.
        -- (* Case: vrecv = Iot iot *)
          admit.
      * (* Case: receiver is None *)
        exfalso.
        specialize (Hreceiverval 0).
        discriminate.    
    + (* can not find x in runtime env*)
      exfalso.
      apply runtime_getVal_not_dom in Hgetx.
      apply static_getType_dom in H1.
      destruct H as [ _ [ _ [ _ [ _ [Henvmatch _]]]]].
      lia.
  - (* Case: stmt = call *)
    destruct (runtime_getVal rΓ x) eqn:Hgetx.
    + (* can find x in runtime env*)
      destruct (runtime_getVal rΓ y) eqn:Hgety.
      * (* can find y in runtime env *)
        destruct v0.
        -- (* Case: v0 = Null_a *)
          exists rΓ, h.
          right.
          apply SBS_Call_NPE.
          exact Hgety.
        -- (* Case: v0 = Iot loc *)
          admit.
      * (* can not find y in runtime env *)
        exfalso.
        apply runtime_getVal_not_dom in Hgety.
        apply static_getType_dom in H2.
        destruct H as [ _ [ _ [ _ [ _ [Henvmatch _]]]]].
        lia.
    + (* can not find x in runtime env*)
      exfalso.
      apply runtime_getVal_not_dom in Hgetx.
      apply static_getType_dom in H1.
      destruct H as [ _ [ _ [ _ [ _ [Henvmatch _]]]]].
      lia.
  - (* Case: stmt = seq *)
    intros. specialize (IHstmt_typing1 rΓ h).  apply IHstmt_typing1 in H as Ind1.
    destruct Ind1 as [rΓ' [h' Ind1]].
    destruct Ind1 as [Hok | Hnpe].
    +
      specialize (preservation_pico CT sΓ rΓ h s1 rΓ' h' sΓ' H H0_) as pre1.
      specialize (IHstmt_typing2 rΓ' h'). apply IHstmt_typing2 in pre1 as Ind2; [| exact Hok].
      destruct Ind2 as [rΓ'' [h'' [Hok2 | Hnpe2]]].
      * 
        exists rΓ'' h''. left. econstructor; eauto.
      * 
        exists rΓ'' h''. right. apply SBS_Seq_NPE_second with rΓ' h'; [exact Hok | exact Hnpe2].
    +
      exists rΓ' h'. right. apply SBS_Seq_NPE_first; assumption.
Admitted.
(* Qed. *)

(* ------------------------------------------------------------- *)
(* Immutability properties for PICO *)
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

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
    eval_stmt rΓ h stmt rΓ' h' -> 
    wf_r_config CT sΓ' rΓ' h'.
Proof.
  intros.
  destruct H0.
  - (* Case: stmt = Skip *)
    inversion H1; subst.
    exact H.
  -  
Admitted.

Theorem progress_pico :
  forall CT sΓ rΓ h stmt sΓ',
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ stmt sΓ' ->
    exists rΓ' h', eval_stmt rΓ h stmt rΓ' h'.
Proof.
  intros.
  destruct H0.
  - (* Case: stmt = Skip *)
    exists rΓ, h. apply SBS_Skip.
  - (* Case: stmt = Local *)
    exists (rΓ <| vars := update (List.length rΓ.(vars) + 1) Null_a rΓ.(vars) |>), h.
    apply SBS_Local.
    unfold wf_r_config in H.
    unfold getVal.
    rewrite nth_error_None.
    replace (dom (vars rΓ)) with dom sΓ. 
    unfold  static_getType in H2.
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
        eapply SBS_Assign; [ exact Hgetval | constructor ].
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
          eapply SBS_Assign; [ exact Hgetx | constructor ].
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
      specialize (Hresult x Hx T' H2).
      inversion H1 as [| | ? ? ? ? ? ? Hobj Hfield ]; subst.
      assert (Hv : nth_error sΓ v = Some T0) by (apply Hfield; auto).
      assert (Hv' : v < dom sΓ) by (apply nth_error_Some; auto).
      destruct (runtime_getVal rΓ v) eqn:Hgety.
      *
        destruct v1.
        -- (* Case: v = Null_a *)
          admit. (* Should get stuck because the type system does not prevent NPE*)
        -- (* Case: v = Iot loc *)
          destruct (runtime_getObj h l) eqn:Hgetval.
          ++
            destruct (getVal o.(fields_map) v0) eqn:Hgetfield.
            ** (* Case: field exists *)
              exists (rΓ <| vars := update x v1 rΓ.(vars) |>), h.
              destruct (runtime_getVal rΓ x) eqn:Hgetx.
              ---
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
              destruct Hwf_o' as [_ [_ Hdom_eq]].
              apply getVal_not_dom in Hgetfield.
              rewrite Hdom_eq in Hgetfield.
              unfold sf_def in H.
              unfold fields in H.
              admit. (* subtyping polymorphism*)
          ++ (* well formedness of runtime environment*)
            admit.
      *
        exfalso.
        apply runtime_getVal_not_dom in Hgety.
        lia.
  - (* Case: stmt = fldwrite*)
    destruct (runtime_getVal rΓ x) eqn:Hgetx.
    + (* can find x in runtime env*)
      destruct v.
      * (* Case: v = Null_a *)
        admit. (* Should get stuck because the type system does not prevent NPE*)
      * (* Case: v = Iot loc *)
        admit.
    + (* can not find x in runtime env*)
      admit.
  - (* Case: stmt = new *)
    admit.
  - (* Case: stmt = call *)
    admit.
  - (* Case: stmt = seq *)
    admit.
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

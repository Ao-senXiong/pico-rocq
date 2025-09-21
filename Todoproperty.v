(* Require Import Syntax Notations Helpers Typing Subtyping Bigstep.
Require Import List.
Import ListNotations.
Require Import String.
From RecordUpdate Require Import RecordUpdate.
Require Import Coq.Logic.Classical_Prop.
Require Import NZOrder.

(* TODO: AOSEN do we need this lemma to generalize to + k instead + 1? *)
Lemma collect_fields_fuel_fuel_increase :
  forall fuel CT C decl,
    find_class CT C = Some decl ->
    fuel >= dom CT ->
    collect_fields_fuel fuel CT C = collect_fields_fuel (S fuel) CT C.
Proof.
  intros.
  induction fuel as [|fuel' IH].
  -
    exfalso.
    unfold find_class in H.
    destruct CT as [|hd tl].
    + simpl in H.
      unfold gget in H.
      rewrite nth_error_nil in H. discriminate.
    + simpl in H0. lia.
  - simpl.
    destruct (find_class CT C) as [def|] eqn:Hfind; [| reflexivity].
    + 
    destruct (super (signature def)) as [superC|]; [| reflexivity].
    (* apply IH. *)
    admit.
      (* * f_equal. apply IH. lia.
      * reflexivity.
    + reflexivity. *)
Admitted.

Lemma collect_fields_fuel_step :
  forall fuel CT C decl,
    find_class CT C = Some decl ->
    forall superC,
      super (signature decl) = Some (superC) ->
      collect_fields_fuel (S fuel) CT C =
      collect_fields_fuel fuel CT superC ++ fields (body decl).
Proof.
  intros fuel CT C decl Hfind superC Hsuper.
  simpl.
  rewrite Hfind.
  rewrite Hsuper.
  simpl.
  reflexivity.
Qed.

Lemma collect_fields_monotone :
  forall CT Csub Csup,
    base_subtype CT Csub Csup ->
    dom (collect_fields_fuel dom CT CT Csup) <=
    dom (collect_fields_fuel dom CT CT Csub).
Proof.
  intros CT Csub Csup Hsub.
  induction Hsub.
  - 
    reflexivity.
  -
    exact (Nat.le_trans _ _ _ IHHsub2 IHHsub1).
  -
    destruct (find_class CT C) as [declsub|] eqn:Hfindsub.
    +
      specialize (collect_fields_fuel_step dom CT CT C declsub Hfindsub) as Hstep.
      destruct (super (signature declsub)) as [superC|] eqn:Hsuper.
      *
        admit.
      *
        admit.   
    +
      exfalso. unfold find_class in Hfindsub. unfold gget in Hfindsub.
      apply nth_error_Some in H.
      congruence.
    (* apply Hstep.
    rewrite dom_app.
    apply Nat.le_add_r. *)
Admitted.

(* Typable preserve assignability *)
Lemma r_typable_assignable :
  forall CT rΓ h ι sqt,
    ι < dom h ->
    wf_r_typable CT rΓ h ι sqt ->
    forall q rt f sa ra, 
    r_muttype h ι = Some q ->
    r_basetype h ι = Some rt ->
    sf_assignability CT (sctype sqt) f = Some sa ->
    sf_assignability CT rt f = Some ra ->
    vpa_assignability (sqtype sqt) sa = Assignable ->
    vpa_assignability (q_r_proj q) ra = Assignable.
Proof.
  intros.
  unfold wf_r_typable in H0.
  unfold r_muttype in H1.
  destruct (r_type h ι) as [rqt|] eqn:Hr_type; [|exfalso; unfold r_type in Hr_type; auto].

Admitted.

Lemma subtype_inherits_methods : forall CT C1 C2 m mdef2,
  base_subtype CT C1 C2 ->
  method_def_lookup CT C2 m = Some mdef2 ->
  exists mdef1, method_def_lookup CT C1 m = Some mdef1.
Proof.
  intros CT C1 C2 m mdef2 Hsub Hlookup.
  
  (* This follows from the definition of method_def_lookup *)
  (* which searches up the inheritance hierarchy *)
  unfold method_def_lookup in *.
  unfold mdef_lookup in *.
  
  (* Use induction on the subtype relation and 
     properties of the method lookup algorithm *)
  induction Hsub.
- (* reflexivity case *)
  rewrite Hlookup.
  eexists.
  reflexivity.
- (* transitivity case *)
  specialize (IHHsub2 Hlookup).
  destruct IHHsub2 as [mdef_intermediate Hmdef_intermediate].
  (* specialize (IHHsub1 Hmdef_intermediate). *)
  (* exact IHHsub1. *)
  admit.
- (* direct inheritance case *)
(* unfold method_def_lookup in *.
simpl.
assert (Hfind: find_class CT C = Some (nth C CT default_class_def)).
{ apply find_class_some. exact H. }
rewrite Hfind.
destruct (find (fun mdef => eq_method_name (mname (msignature mdef)) m) (methods (body (nth C CT default_class_def)))) eqn:Hmethods.
- (* Case: C has its own method m *)
  exists m0.
  reflexivity.
- (* Case: C doesn't have method m, inherit from parent *)
  assert (Hsuper: super (signature (nth C CT default_class_def)) = Some D).
  { admit. (* follows from H1 and class table structure *) }
  rewrite Hsuper.
  exists mdef2.
  exact Hlookup. *)
Admitted.

Lemma subtype_lookup_fail : forall CT C1 C2 m,
  base_subtype CT C1 C2 ->
  method_def_lookup CT C1 m = None ->
  method_def_lookup CT C2 m = None.
Proof.
  intros CT C1 C2 m Hsub Hlookup.
  
  (* Proof by contradiction *)
  destruct (method_def_lookup CT C2 m) as [mdef|] eqn:HC2_lookup.
  
  - (* Case: method_def_lookup CT C2 m = Some mdef *)
    (* This contradicts our assumption that C1 lookup fails *)
    exfalso.
    
    (* Since C1 is a subtype of C2, and C2 has method m, 
       then C1 should either have m or inherit it from C2 *)
    assert (Hinherit: exists mdef1, method_def_lookup CT C1 m = Some mdef1).
    {
      (* Use method inheritance property *)
      apply subtype_inherits_methods with (CT := CT) (C1 := C1) (C2 := C2) (m := m) (mdef2 := mdef).
      - exact Hsub.
      - exact HC2_lookup.
    }
    
    (* This contradicts Hlookup *)
    rewrite Hlookup in Hinherit.
    destruct Hinherit as [mdef1 Hcontra].
    discriminate Hcontra.
  - (* Case: method_def_lookup CT C2 m = None *)
    (* This is exactly what we want to prove *)
    reflexivity.
Qed.

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
  | CT sΓ x m y args argtypes Tx Ty m_sig H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13
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
      destruct H4 as [ _ [ _ [ _ [ _ [Hlen Hresult]]]]].
      unfold static_getType in H3.
      destruct (runtime_getVal rΓ x) eqn:Hgetval.
      * 
        left. eapply SBS_Assign; [ exact Hgetval | constructor ].
      * 
        exfalso.
        assert (HxDom : x < dom sΓ) by (apply nth_error_Some; eauto).
        specialize (Hresult x HxDom T' H3).
        rewrite Hgetval in Hresult. exact Hresult.
    + (* Case: e = EVar *)     
      destruct H4 as [ _ [ _ [ _ [ _ [Henvmatch Hresult]]]]].
      unfold static_getType in H3.
      assert (HxDom : x < dom sΓ) by (apply nth_error_Some; eauto).
      specialize (Hresult x HxDom T' H3).
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
      destruct H4 as [ _ [ Hheap [ Hrenv [ Hsenv [Henvmatch Hresult]]]]].
      unfold static_getType in H3.
      assert (HxDom : x < dom sΓ) by (apply nth_error_Some; eauto).
      pose proof Hresult as Hresult_copy.
      specialize (Hresult_copy x HxDom T' H3).
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
              pose proof Hheap as Hheap_copy.
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
              unfold sf_def in H4.
              unfold fields in H4.
              specialize (Hresult v Hv' T0 Hv).
              rewrite Hgety in Hresult.
              apply r_obj_subtype_sqt with (o := o) (rt := rctype (rt_type o)) in Hresult; [| | exact Hheap_copy | exact Hgetval | reflexivity ].
              unfold gget in H4.
              assert (v0 < dom (collect_fields CT (sctype T0))) by (apply nth_error_Some; congruence).
              specialize (collect_fields_monotone CT (rctype (rt_type o)) (sctype T0) Hresult).
              remember (dom (collect_fields CT (rctype (rt_type o)))) as d1.
              remember (dom (collect_fields CT (sctype T0))) as d2.
              assert (d2 <= d1) by (subst; apply collect_fields_monotone; assumption).
              assert (v0 < d2) by (subst; apply H5).
              assert (v0 >= d1) by (subst; apply Hgetfield).
              lia. (* subtyping polymorphism*)
              unfold wf_senv in Hsenv.
              destruct Hsenv as [Hsenv_dom H_static_typeuse].
              apply (Forall_nth_error _ _ _ _ H_static_typeuse Hv).
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
        destruct H7 as [ _ [ Hheap [ Hrenv [ Hsenv [Henvmatch Hresult]]]]].
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
              destruct (r_muttype h l) as [qrecv |] eqn:Hgetrecv.
              ---
                destruct (r_basetype h l) as [C |] eqn:Hgetbasetype;[| unfold r_basetype in Hgetbasetype; rewrite Hgetval in Hgetbasetype; discriminate].
                destruct (sf_assignability CT C f) as [af | ] eqn:Hgetassignability.
                +++ (* Case: field is assignable *)
                destruct (ViewpointAdaptation.vpa_assignability (q_r_proj qrecv) af) as [adaptedaf | |] eqn:Hgetadaptedassignability.
                *** (* Case: field is assignable *)
                  reflexivity.
                *** (* Case: field is final *)
                  exfalso.
                  assert (Hx : x < dom sΓ).
                  {
                    unfold static_getType in H2.
                    apply nth_error_Some; eauto.
                  }
                  specialize (Hresult x Hx Tx H2).
                  rewrite Hgetx in Hresult.
                  assert (Hldom : l < dom h).
                  { apply runtime_getObj_dom in Hgetval. exact Hgetval. }
                  eapply r_typable_assignable with (sqt := Tx) (q := qrecv) (f := f) (sa := H0) (ra := af) in H6; eauto.
                *** (* Case: field is RDA *)
                  exfalso.
                  assert (Hx : x < dom sΓ).
                  {
                    unfold static_getType in H2.
                    apply nth_error_Some; eauto.
                  }
                  specialize (Hresult x Hx Tx H2).
                  rewrite Hgetx in Hresult.
                  assert (Hldom : l < dom h).
                  { apply runtime_getObj_dom in Hgetval. exact Hgetval. }
                  eapply r_typable_assignable with (sqt := Tx) (q := qrecv) (f := f) (sa := H0) (ra := af) in H6; eauto.
                +++ (* Case: Did not find the field *)
                exfalso.
                unfold sf_assignability in Hgetassignability.
                assert (sf_def CT C f = None).
                {
                  destruct (sf_def CT C f); inversion Hgetassignability; reflexivity.
                }
                unfold wf_heap in Hheap.
                assert (Hwf_o: wf_obj CT h l).
                {
                  apply Hheap.
                  apply runtime_getObj_dom in Hgetval.
                  exact Hgetval.
                }
                unfold wf_obj in Hwf_o.
                rewrite Hgetval in Hwf_o.
                destruct Hwf_o as [Hwftypeo Hdomo].
                unfold sf_def in H7.
                unfold gget in H7.
                apply getVal_dom in Hgetfield.
                apply nth_error_None in H7.
                unfold fields in H7.
                assert (rctype (rt_type o) = C).
                {
                  unfold r_basetype in Hgetbasetype.
                  rewrite Hgetval in Hgetbasetype.
                  inversion Hgetbasetype; reflexivity.
                }
                rewrite <- H8 in H7.
                lia.
              ---
                exfalso.
                unfold r_muttype in Hgetrecv.
                rewrite Hgetval in Hgetrecv.
                discriminate. 
            ** 
              exfalso.
              apply runtime_getVal_not_dom in Hgety.
              apply static_getType_dom in H3.
              lia.
          ++ (* Case: field does not exist *)
            exfalso.
            pose proof Hheap as Hheap_copy.
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
            unfold sf_def in H4.
            unfold fields in H4.
            assert (x < dom sΓ) as Hx.
            {
              unfold static_getType in H2.
              apply nth_error_Some; eauto.
            }
            specialize (Hresult x Hx Tx H2).
            rewrite Hgetx in Hresult.
            apply r_obj_subtype_sqt with (o := o) (rt := rctype (rt_type o)) in Hresult; [| |exact Hheap_copy | exact Hgetval | reflexivity ].
            unfold gget in Hx.
            assert (f < dom (collect_fields CT (sctype Tx))) as Hf.
            {
              unfold gget in H4.
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
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenv_dom H_static_typeuse].
            unfold static_getType in H2.
            apply (Forall_nth_error _ _ _ _ H_static_typeuse H2).
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
      apply static_getType_dom in H2.
      destruct H7 as [ _ [ _ [ _ [ _ [Henvmatch _]]]]].
      lia.
  - (* Case: stmt = new *)
    destruct (runtime_getVal rΓ x) eqn:Hgetx.
    destruct H10 as [ _ [ Hheap [ Hrenv [ _ [Henvmatch Hresult]]]]].
    destruct Hrenv as [Hreceiver [Hreceiverval Hrenv]].
    + (* can find x in runtime env*)
      destruct (runtime_lookup_list rΓ args) as [args' |] eqn:Hlookup.
      2:{
        apply mapM_Some_forall in H3.
        apply mapM_None_exists in Hlookup.
        destruct Hlookup as [testx [Hinargs Hnone]].
        assert (Htestx_exists: exists y : qualified_type, static_getType sΓ testx = Some y).
        {
          apply Forall_forall with (x := testx) in H3.
          - exact H3.
          - exact Hinargs.
        }
        destruct Htestx_exists as [testy Hsome].
        apply static_getType_dom in Hsome.
        apply runtime_getVal_not_dom in Hnone.
        lia.
      }
      destruct Hreceiverval as [iot Hgetrecv].
      destruct (r_muttype h iot) as [qrecv |] eqn:Hgetrecvmut.
      2:{
        exfalso.
        unfold r_muttype in Hgetrecvmut.
        destruct (runtime_getObj h iot) eqn:Hobj.
        * discriminate.
        * 
          apply Forall_forall with (x := Iot iot) in Hrenv.
          -- rewrite Hobj in Hrenv. auto.
          -- unfold gget in Hgetrecv. apply nth_error_In with (n := 0). rewrite Hgetrecv. reflexivity.
      }
      destruct (q_project_q_r (ViewpointAdaptation.vpa_mutabilty (q_r_proj qrecv) (q_c_proj q))) as [qadapted |] eqn:Hgetqadapted.
      2:{
        exfalso.
        destruct (q_r_proj qrecv) eqn: hqrecvproj.
        * 
          destruct (q_c_proj q) eqn: hnewqproj.
          -- simpl in Hgetqadapted. discriminate.
          -- simpl in Hgetqadapted. discriminate.
          -- simpl in Hgetqadapted. discriminate.
          -- destruct q as [qval Hqval]. unfold q_c_proj in hnewqproj. simpl in hnewqproj. subst qval. destruct Hqval as [Hmut | [Himm | Hrmd]]; subst; discriminate.
          -- destruct q as [qval Hqval]. unfold q_c_proj in hnewqproj. simpl in hnewqproj. subst qval. destruct Hqval as [Hmut | [Himm | Hrmd]]; subst; discriminate.
          -- destruct q as [qval Hqval]. unfold q_c_proj in hnewqproj. simpl in hnewqproj. subst qval. destruct Hqval as [Hmut | [Himm | Hrmd]]; subst; discriminate.
        *
          destruct (q_c_proj q) eqn: hnewqproj.
          -- simpl in Hgetqadapted. discriminate.
          -- simpl in Hgetqadapted. discriminate.
          -- simpl in Hgetqadapted. discriminate.
          -- destruct q as [qval Hqval]. unfold q_c_proj in hnewqproj. simpl in hnewqproj. subst qval. destruct Hqval as [Hmut | [Himm | Hrmd]]; subst; discriminate.
          -- destruct q as [qval Hqval]. unfold q_c_proj in hnewqproj. simpl in hnewqproj. subst qval. destruct Hqval as [Hmut | [Himm | Hrmd]]; subst; discriminate.
          -- destruct q as [qval Hqval]. unfold q_c_proj in hnewqproj. simpl in hnewqproj. subst qval. destruct Hqval as [Hmut | [Himm | Hrmd]]; subst; discriminate.
        * destruct qrecv as [qval Hqval]. unfold q_r_proj in hqrecvproj. simpl in hqrecvproj. subst qval. destruct Hqval as [Hmut | Himm ]; subst; discriminate.
        * destruct qrecv as [qval Hqval]. unfold q_r_proj in hqrecvproj. simpl in hqrecvproj. subst qval. destruct Hqval as [Hmut | Himm ]; subst; discriminate.
        * destruct qrecv as [qval Hqval]. unfold q_r_proj in hqrecvproj. simpl in hqrecvproj. subst qval. destruct Hqval as [Hmut | Himm ]; subst; discriminate.
        * destruct qrecv as [qval Hqval]. unfold q_r_proj in hqrecvproj. simpl in hqrecvproj. subst qval. destruct Hqval as [Hmut | Himm ]; subst; discriminate.
      }
      exists (rΓ <| vars := update x (Iot (dom h + 1)) rΓ.(vars) |>), (h ++ [mkObj (mkruntime_type qadapted C) args']).      left.
      * (* Case: receiver is a variable *)
        eapply SBS_New.
        ++ exact Hgetrecv.
        ++ exact Hlookup.
        ++ exact Hgetrecvmut.
        ++ reflexivity.
        ++ exact Hgetqadapted.
        ++ reflexivity.
        ++ reflexivity.
        ++ reflexivity.
    + (* can not find x in runtime env*)
      exfalso.
      apply runtime_getVal_not_dom in Hgetx.
      apply static_getType_dom in H2.
      destruct H10 as [ _ [ _ [ _ [ _ [Henvmatch _]]]]].
      lia.
  - (* Case: stmt = call *)
    destruct (runtime_getVal rΓ x) eqn:Hgetx.
    destruct H as [ Hclass [ Hheap [ Hrenv [ Hsenv [Henvmatch Hresult]]]]].
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
          destruct (runtime_lookup_list rΓ args) as [args' |] eqn:Hlookup.
          2:{
            unfold runtime_lookup_list in Hlookup. unfold static_getType_list in H6.
            exfalso.
            apply mapM_Some_forall in H3.
            apply mapM_None_exists in Hlookup.
            destruct Hlookup as [testx [Hinargs Hnone]].
            assert (Htestx_exists: exists y : qualified_type, static_getType sΓ testx = Some y).
            {
              apply Forall_forall with (x := testx) in H3.
              - exact H3.
              - exact Hinargs.
            }
            destruct Htestx_exists as [testy Hsome].
            apply static_getType_dom in Hsome.
            apply runtime_getVal_not_dom in Hnone.
            lia.
          }
          destruct (runtime_getObj h l) eqn:Hobj.
          2:{
            exfalso.
            unfold wf_heap in Hheap.
            apply runtime_getObj_not_dom in Hobj.
            unfold wf_renv in Hrenv.
            destruct Hrenv as [Hreceiver [Hreceiverval Hrenv]].
            eapply Forall_nth_error in Hrenv as Hfor; [| exact Hgety].
            simpl in Hfor. unfold runtime_getObj in Hfor.
            destruct (nth_error h l) eqn:Hnth.
            - (* nth_error h l = Some _ *)
              apply nth_error_None in Hobj. rewrite Hobj in Hnth. discriminate.
            - (* nth_error h l = None *)
              exact Hfor.
          }
          destruct (r_basetype h l) as [C |] eqn:Hgetbasetype.
          2:{
            exfalso.
            unfold r_basetype in Hgetbasetype.
            rewrite Hobj in Hgetbasetype.
            discriminate.
          }
          remember (mkr_env (Iot l :: args')) as rΓ'.
          destruct (method_body_lookup CT C m) as [mbody |] eqn:Hlookupmbody.
          2:{
            exfalso.
            specialize (Hresult y). rewrite -> Henvmatch in Hresult.
            apply runtime_getVal_dom in Hgety as Hgety_dom.
            specialize (Hresult Hgety_dom).
            specialize (Hresult Ty H2).
            rewrite Hgety in Hresult.
            apply r_obj_subtype_sqt with (o := o) (rt := rctype (rt_type o)) in Hresult; [ | | exact Hheap | exact Hobj | reflexivity ].
            unfold method_body_lookup in Hlookupmbody.
            assert (method_def_lookup CT C m = None).
            {
              unfold method_def_lookup.
              destruct (mdef_lookup dom CT CT C m) eqn:Hmdef.
              - (* Case: Some mdef *)
                simpl in Hlookupmbody.
                discriminate Hlookupmbody.
              - (* Case: None *)
                trivial.
            }
            assert (Hcontra: method_def_lookup CT (sctype Ty) m = None).
            {
              apply subtype_lookup_fail with (CT := CT) (C1 := rctype (rt_type o)) (C2 := sctype Ty) (m := m).
              - exact Hresult.
              - unfold r_basetype in Hgetbasetype. rewrite Hobj in Hgetbasetype. injection Hgetbasetype as Heq.
              symmetry in Heq.
              rewrite <- Heq.
              exact H.
            }
            unfold method_sig_lookup in H4.
            unfold method_def_lookup in Hcontra.
            rewrite Hcontra in H4.
            discriminate H4.
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenv_dom H_static_typeuse].
            unfold static_getType in H2.
            apply (Forall_nth_error _ _ _ _ H_static_typeuse H2).
          }
          destruct (method_def_lookup CT C m) as [mdef |] eqn:Hlookupmdef.
          2:{
            exfalso.
            unfold method_body_lookup in Hlookupmbody.
            unfold method_def_lookup in Hlookupmdef.
            rewrite Hlookupmdef in Hlookupmbody.
            discriminate Hlookupmbody.
          }
          destruct (find_class CT C) as [cdef |] eqn:Hcdef. 
          2: {
            exfalso.            
            unfold r_basetype in Hgetbasetype.
            unfold wf_heap in Hheap. 
            pose proof Hobj as Hobj_copy.
            apply runtime_getObj_dom in Hobj.
            specialize (Hheap l Hobj). unfold wf_obj in Hheap.
            rewrite Hobj_copy in Hheap.
            destruct Hheap as [Hwf_type _].
            unfold wf_rtypeuse in Hwf_type.
            rewrite Hobj_copy in Hgetbasetype. injection Hgetbasetype as Heq.
            destruct (bound CT (rctype (rt_type o))) eqn:Hbound.
            2: {
              exact Hwf_type.
            }
            apply find_class_not_dom in Hcdef.
            rewrite Heq in Hwf_type.
            lia.
          }

          assert (HclassC : wf_class CT cdef).
          {
            apply Forall_forall with (x := cdef) in Hclass.
            - exact Hclass.
            - unfold find_class in Hcdef.
              apply gget_In in Hcdef.
              exact Hcdef.
          }

          inversion HclassC as [ | CT' cdef' superC thisC Hsuper Hcname Hneq Hsig Hbody]; subst.
          1:{
            admit. (* This is the object case, should be discharged by more work*)
          }
          remember (mkr_env (Iot l :: args')) as rΓ'.
          destruct H as [Hwf_cons [Hwf_mets Hbound]].
          assert (C = C0).
          {
            admit. (* They are the same because of class lookup*)
          }
          replace C0 with C in Hwf_mets.
          assert (wf_method CT C mdef) as Hwf_m.
          {
            admit.
          }
          remember (Ty :: argtypes) as sΓ'.
          assert (wf_r_config CT sΓ' rΓ' h) as Hwf_rconfig_mbody.
          {
            admit. (* This is something need to be proved, in Dafny, it is more modular *)
          }
          (* specialize (H11 rΓ' h Hwf_rconfig_mbody).
          destruct H11 as [rΓ'' [h' [Heval | Hnpe]]].
          {
            exists rΓ'' h'.
            left.
            eapply SBS_Call.
            ++ exact Hgety.
            ++ exact Hgetbasetype.
            ++ exact Hlookupmbody.
            ++ reflexivity.
            ++ reflexivity.
            ++ exact Hlookup.
            ++ exact HeqrΓ'.
            ++ assert (mbody = H2). 
              {
                admit. (* This is wrong *)
              }
              replace H2 with mbody in Heval.
              exact Heval.
            ++ admit.
            ++ admit.
          }
          {
            exists rΓ'' h'.
            right.
            eapply SBS_Call_NPE_Body.
            ++ exact Hgety.
            ++ exact Hgetbasetype.
            ++ exact Hlookupmbody.
            ++ reflexivity.
            ++ reflexivity.
            ++ exact Hlookup.
            ++ exact HeqrΓ'.
            ++ assert (mbody = H2). 
              {
                admit. (* This is wrong *)
              }
              replace H2 with mbody in Hnpe.
              exact Hnpe.
          } *)
           admit.
      * (* can not find y in runtime env *)
        exfalso.
        apply runtime_getVal_not_dom in Hgety.
        apply static_getType_dom in H2.
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
Qed. *)


  (* 6: 
  {
    inversion Htyping; subst.
    remember (mreceiver m_sig :: mparams m_sig) as sΓmethodinit.
    remember {| vars := Iot ly :: vals |} as rΓmethodinit.
    remember (rΓ <| vars := update x retval (vars rΓ) |>) as rΓ'''.
    apply method_sig_lookup_implies_body_lookup in H16.
    destruct H16 as [mbody0 H16].
    apply method_body_lookup_implies_def_lookup in H16.
    destruct H16 as [mdef H16].
    destruct H16 as [Hmdef_lookup Hbody_eq].
    apply method_body_well_typed in Hmdef_lookup; auto.
    destruct Hmdef_lookup as [sΓmethodend Hmdef_lookup].
    assert (wf_r_config CT sΓmethodend rΓ'' h'). {
      eapply IHHeval with (sΓ := sΓmethodinit) (sΓ' := sΓmethodend); eauto.
      admit.
      admit. (* with some rewrite *)
      (* exact Hmdef_lookup. *)
    }
    admit.
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hwf_classtable _].
    exact Hwf_classtable.
    generalize dependent sΓ'.
    induction H9; try discriminate.
    6:{(* method call case again*)
      intros.
      subst.
      apply IHeval_stmt.
      Print IHeval_stmt.
      (* apply IHeval_stmt with (mbody:=mbody0). *)
      (* apply IHeval_stmt with (mbody1:=mbody0). *)
      all: try reflexivity.
      exact H.
      exact H3.
      exact H5.
      exact H6.
      exact H7.
      exact H8.
      exact H9.
      exact H15.
      exact H16.
      admit.
      admit.
      admit.
      exact Hwf_method_frame.
    }
    {
      unfold wf_r_config in *.
      destruct H8 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
      destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
      repeat split.
      unfold wf_class_table in Hclass.
      exact Hclass.
      exact Hobj.
      exact Hotherclasses.
      apply Hcname_consistent.
      apply Hcname_consistent.
      subst.
      exact Hheap.
      unfold wf_renv in Hrenv.
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      simpl.
      subst rΓ'.
      rewrite update_length.
      exact HrEnvLen.
      unfold wf_renv in Hrenv.
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      destruct Hreceiverval as [iot [Hiot Hiotdom]].
      exists iot.
      simpl.
      unfold gget in *.
      {destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
      - (* Case: vars rΓ = [] *)
        exfalso.
        simpl in HrEnvLen.
        lia.
      - (* Case: vars rΓ = v0 :: vs *)
        destruct x as [|x'].
        + (* Case: x = 0 *)
          contradiction H4.
          reflexivity.
        + (* Case: x = S x' *)
          simpl.
          split.
          * subst rΓ'. exact Hiot.
          * exact Hiotdom.
      }
      {
        unfold wf_renv in Hrenv.
        destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
        simpl.
        subst rΓ'.
        apply Forall_update.
        exact Hallvals.
        destruct retval as [|loc]. easy.
        subst.
        admit.
        apply static_getType_dom in H0.
        rewrite <- Hlen.
        exact H0.
      }
      destruct Hsenv as [HsenvLength HsenvWellTyped].
      exact HsenvLength.
      destruct Hsenv as [HsenvLength HsenvWellTyped].
      exact HsenvWellTyped.
      subst rΓ'.
      rewrite update_length.
      exact Hlen.
      admit.
    }
    {
      unfold wf_r_config in *.
      destruct H8 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
      repeat split.
      unfold wf_class_table in Hclass.
      destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
      exact Hclass.
      destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
      exact Hobj.
      destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
      exact Hotherclasses.
      destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
      apply Hcname_consistent.
      destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
      apply Hcname_consistent.
      exact Hheap. 
      unfold wf_renv in Hrenv.
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      simpl.
      subst rΓ'.
      rewrite update_length.
      exact HrEnvLen.
      unfold wf_renv in Hrenv.
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      destruct Hreceiverval as [iot [Hiot Hiotdom]].
      exists iot.
      simpl.
      unfold gget in *.
      {destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
      - (* Case: vars rΓ = [] *)
        exfalso.
        simpl in HrEnvLen.
        lia.
      - (* Case: vars rΓ = v0 :: vs *)
        destruct x as [|x'].
        + (* Case: x = 0 *)
          contradiction H4.
          reflexivity.
        + (* Case: x = S x' *)
          simpl.
          split.
          * subst rΓ'. exact Hiot.
          * exact Hiotdom.
      }
      {
        unfold wf_renv in Hrenv.
        destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
        simpl.
        subst rΓ'.
        apply Forall_update.
        exact Hallvals.
        destruct retval as [|loc]. easy.
        admit.
        apply static_getType_dom in H0.
        rewrite <- Hlen.
        exact H0.
      }
      destruct Hsenv as [HsenvLength HsenvWellTyped].
      exact HsenvLength.
      destruct Hsenv as [HsenvLength HsenvWellTyped].
      exact HsenvWellTyped.
      subst rΓ'.
      rewrite update_length.
      exact Hlen.
      admit.
    }
    {
      unfold wf_r_config in *.
      destruct H8 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
      repeat split.
      unfold wf_class_table in Hclass.
      destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
      exact Hclass.
      destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
      exact Hobj.
      destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
      exact Hotherclasses.
      destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
      apply Hcname_consistent.
      destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
      apply Hcname_consistent.
      exact Hheap. 
      unfold wf_renv in Hrenv.
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      simpl.
      subst rΓ'.
      rewrite update_length.
      exact HrEnvLen.
      unfold wf_renv in Hrenv.
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      destruct Hreceiverval as [iot [Hiot Hiotdom]].
      exists iot.
      simpl.
      unfold gget in *.
      {destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
      - (* Case: vars rΓ = [] *)
        exfalso.
        simpl in HrEnvLen.
        lia.
      - (* Case: vars rΓ = v0 :: vs *)
        destruct x as [|x'].
        + (* Case: x = 0 *)
          contradiction H4.
          reflexivity.
        + (* Case: x = S x' *)
          simpl.
          split.
          * subst rΓ'. exact Hiot.
          * exact Hiotdom.
      }
      {
        unfold wf_renv in Hrenv.
        destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
        simpl.
        subst rΓ'.
        apply Forall_update.
        exact Hallvals.
        destruct retval as [|loc]. easy.
        admit.
        apply static_getType_dom in H0.
        rewrite <- Hlen.
        exact H0.
      }
      destruct Hsenv as [HsenvLength HsenvWellTyped].
      exact HsenvLength.
      destruct Hsenv as [HsenvLength HsenvWellTyped].
      exact HsenvWellTyped.
      subst rΓ'.
      rewrite update_length.
      exact Hlen.
      admit.
    }
    {
      unfold wf_r_config in *.
      destruct H8 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
      repeat split.
      unfold wf_class_table in Hclass.
      destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
      exact Hclass.
      destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
      exact Hobj.
      destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
      exact Hotherclasses.
      destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
      apply Hcname_consistent.
      destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
      apply Hcname_consistent.
      (* exact Hheap.  *)
      admit.
      unfold wf_renv in Hrenv.
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      simpl.
      subst rΓ'.
      rewrite update_length.
      exact HrEnvLen.
      unfold wf_renv in Hrenv.
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      destruct Hreceiverval as [iot [Hiot Hiotdom]].
      exists iot.
      simpl.
      unfold gget in *.
      {destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
      - (* Case: vars rΓ = [] *)
        exfalso.
        simpl in HrEnvLen.
        lia.
      - (* Case: vars rΓ = v0 :: vs *)
        destruct x as [|x'].
        + (* Case: x = 0 *)
          contradiction H4.
          reflexivity.
        + (* Case: x = S x' *)
          simpl.
          split.
          * subst rΓ'. exact Hiot.
          * subst h'. rewrite update_field_length. exact Hiotdom.
      }
      {
        unfold wf_renv in Hrenv.
        destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
        simpl.
        subst rΓ'.
        apply Forall_update.
        admit.
        admit.
        (* exact Hallvals.
        destruct retval as [|loc]. easy. *)
        apply static_getType_dom in H0.
        rewrite <- Hlen.
        exact H0.
      }
      destruct Hsenv as [HsenvLength HsenvWellTyped].
      exact HsenvLength.
      destruct Hsenv as [HsenvLength HsenvWellTyped].
      exact HsenvWellTyped.
      subst rΓ'.
      rewrite update_length.
      exact Hlen.
      admit.
    }
    { (* Object creation case *)
      unfold wf_r_config in *.
      destruct H8 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
      repeat split.
      unfold wf_class_table in Hclass.
      destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
      exact Hclass.
      destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
      exact Hobj.
      destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
      exact Hotherclasses.
      destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
      apply Hcname_consistent.
      destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
      apply Hcname_consistent.
      admit.
      (* exact Hheap.  *)
      unfold wf_renv in Hrenv.
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      simpl.
      subst rΓ'.
      rewrite update_length.
      exact HrEnvLen.
      unfold wf_renv in Hrenv.
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      destruct Hreceiverval as [iot [Hiot Hiotdom]].
      exists iot.
      simpl.
      unfold gget in *.
      {destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
      - (* Case: vars rΓ = [] *)
        exfalso.
        simpl in HrEnvLen.
        lia.
      - (* Case: vars rΓ = v0 :: vs *)
        destruct x as [|x'].
        + (* Case: x = 0 *)
          contradiction H4.
          reflexivity.
        + (* Case: x = S x' *)
          simpl.
          split.
          * subst rΓ'. exact Hiot.
          * subst h'.
            rewrite length_app.
            simpl.
            lia.
      }
      {
        unfold wf_renv in Hrenv.
        destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
        simpl.
        subst rΓ'.
        apply Forall_update.
        subst.
        (* exact Hallvals. *)
        (* destruct retval as [|loc]. easy. *)
        admit.
        admit.
        apply static_getType_dom in H0.
        rewrite <- Hlen.
        exact H0.
      }
      destruct Hsenv as [HsenvLength HsenvWellTyped].
      exact HsenvLength.
      destruct Hsenv as [HsenvLength HsenvWellTyped].
      exact HsenvWellTyped.
      subst rΓ'.
      rewrite update_length.
      exact Hlen.
      admit.
    }
    { (* sequence case *)
      subst.
      admit.
    }
  } *)


(* Lemma eval_stmt_preserves_heap_domain : forall CT sΓ sΓ' rΓ h stmt rΓ' h',
  wf_r_config CT sΓ rΓ h ->
  stmt_typing CT sΓ stmt sΓ' -> 
  eval_stmt OK CT rΓ h stmt OK rΓ' h' ->
  dom h <= dom h'.
Proof.
  intros CT sΓ sΓ' rΓ h stmt rΓ' h' Hwf Hstmttyping Heval.
  generalize dependent sΓ.
  generalize dependent sΓ'.
  remember OK as ok; induction Heval; try reflexivity; try discriminate.
  3:{
    intros.
    apply method_body_lookup_implies_def_lookup in H1.
    destruct H1 as [mdef H1].
    remember (msignature mdef) as msig.
    destruct H1 as [Hmdef_lookup Hbody_eq].
    have Hmdef_lookupcopy := Hmdef_lookup. 
    apply method_body_well_typed in Hmdef_lookup; auto.
    destruct Hmdef_lookup as [sΓmethodend Hmdef_lookup].
    remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit.
    apply IHHeval with (sΓ:=sΓmethodinit)(sΓ':=sΓmethodend); auto.
    assert (Hwf_method_frame : wf_r_config CT sΓmethodinit 
                                     rΓ' h).
    {
      unfold wf_r_config in *.
      destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
      have Hclasstable := Hclass.
      destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
      repeat split.
      exact Hclass.
      exact Hobj.
      exact Hotherclasses.
      apply Hcname_consistent.
      apply Hcname_consistent.
      exact Hheap.
      rewrite H5.
      simpl.
      lia.
      unfold wf_renv in Hrenv.
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      exists ly.
      split.
      rewrite H5.
      simpl.
      reflexivity.
      unfold runtime_getVal in H.
      destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
      injection H as H1_eq.
      subst v.
      eapply Forall_nth_error in Hallvals; eauto.
      simpl in Hallvals.
      destruct (runtime_getObj h ly) as [obj|] eqn:Hobjly; [|contradiction].
      apply runtime_getObj_dom in Hobjly.
      exact Hobjly.

      (* Inner runtime env is wellformed*)
      rewrite H5.
      simpl.
      constructor.
      simpl.
      unfold runtime_getVal in H.
      destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
      injection H as H1_eq.
      subst v.
      unfold runtime_getVal in Hnth_y.
      unfold wf_renv in Hrenv.
      destruct Hrenv as [_ [_ Hallvals]].
      eapply Forall_nth_error in Hallvals; eauto.
      simpl in Hallvals.
      exact Hallvals.
      eapply runtime_lookup_list_preserves_wf_values; eauto.

      rewrite HeqsΓmethodinit.
      simpl.
      lia.
      
      (* Inner static env's elements are wellformed typeuse *)
      rewrite HeqsΓmethodinit.
      constructor.
      (* Receiver type is well-formed *)
      apply method_sig_wf_from_def with (m_sig := (msignature mdef)) in Hmdef_lookupcopy; auto.
      destruct Hmdef_lookupcopy as [Hreceiver _].
      exact Hreceiver.
      (* Parameter types are well-formed *)
      apply method_sig_wf_from_def with (m_sig := (msignature mdef)) in Hmdef_lookupcopy; auto.
      destruct Hmdef_lookupcopy as [_ Hparams].
      exact Hparams.

      admit.
      admit.
    }
    exact Hwf_method_frame.
    rewrite -> Hbody_eq in Hmdef_lookup.
    rewrite <- H2 in Hmdef_lookup.
    exact Hmdef_lookup. 
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hwf_classtable _].
    exact Hwf_classtable.
  }
  - (* FldWrite: h' = update_field h lx f v2 *)
  intros.
  rewrite H3.
  unfold update_field.
  rewrite H0.
  rewrite update_length.
  reflexivity.
  -
  intros.
  rewrite H5.
  rewrite length_app.
  simpl.
  lia.
  - (* Seq *)
    intros.
    inversion Hstmttyping; subst.
        (* specialize (IHHeval1 eq_refl sΓ'0 sΓ Hwf H3) as IH1.
    specialize (IHHeval2 eq_refl sΓ' sΓ'0 IH1 H5) as IH2. *)
    apply Nat.le_trans with (dom h').
    + (* Apply strong IH to first statement *)
      apply IHHeval1 with (sΓ:=sΓ) (sΓ':=sΓ'0).
      reflexivity.
      exact Hwf.
      exact H3.
    + (* Apply strong IH to second statement *)
      intros.
      apply IHHeval2 with (sΓ:=sΓ'0) (sΓ':=sΓ').
      reflexivity.
      admit. (* somehow need the preservation...*)
      exact H5.
Admitted. *)

(* Theorem readonly_pico :
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
      sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA ->
      nth_error vals f = nth_error vals' f. *)
      (*This looks like shallow mutability to me, but my language does not allow x.f1.f2 = y.*)

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


    (* Method def lookup *)
(* Fixpoint mdef_lookup (fuel : nat) (CT : class_table) (C : class_name) (m : method_name) : option method_def :=
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
  end. *)

(* Method definition lookup  *)
(* Definition method_def_lookup (CT : class_table) (C : class_name) (m : method_name) : option method_def :=
  mdef_lookup (length CT) CT C m. *)

(* Method signature lookup *)
(* Definition method_sig_lookup (CT : class_table) (C : class_name) (m : method_name) : option (method_sig) :=
  match mdef_lookup (length CT) CT C m with
  | Some mdef => Some mdef.(msignature)
  | None => None
  end. *)

(* Method body lookup *)
(* Definition method_body_lookup (CT : class_table) (C : class_name) (m : method_name) : option method_body :=
  match mdef_lookup (length CT) CT C m with
  | Some mdef => Some mdef.(mbody)
  | None => None
  end. *)

(* Lemma method_body_lookup_implies_sig_lookup : forall CT C m mbody,
  method_body_lookup CT C m = Some mbody ->
  exists msig, method_sig_lookup CT C m = Some msig.
Proof.
  intros CT C m mbody H.
  unfold method_body_lookup in H.
  unfold method_sig_lookup.
  destruct (mdef_lookup (length CT) CT C m) as [mdef|] eqn:Hmdef.
  - injection H as H_eq. subst mbody.
    exists (msignature mdef).
    reflexivity.
  - discriminate H.
Qed.

Lemma method_body_lookup_implies_def_lookup : forall CT C m mebody,
  method_body_lookup CT C m = Some mebody ->
  exists mdef, method_def_lookup CT C m = Some mdef /\ (mbody mdef) = mebody.
Proof.
  intros CT C m mebody H.
  unfold method_body_lookup in H.
  unfold method_def_lookup.
  destruct (mdef_lookup (length CT) CT C m) as [mdef|] eqn:Hmdef.
  - injection H as H_eq. subst mebody.
    exists mdef.
    split.
    + reflexivity.
    + reflexivity.
  - discriminate H.
Qed.

Lemma method_sig_lookup_implies_body_lookup : forall CT C m msig,
  method_sig_lookup CT C m = Some msig ->
  exists mbody, method_body_lookup CT C m = Some mbody.
Proof.
  intros CT C m msig H.
  unfold method_sig_lookup in H.
  unfold method_body_lookup.
  destruct (mdef_lookup (length CT) CT C m) as [mdef|] eqn:Hmdef.
  - injection H as H_eq. subst msig.
    exists (mbody mdef).
    reflexivity.
  - discriminate H.
Qed. *)

(* Definition find_overriding_method (CT : class_table) (C: class_name) (m: method_sig) : option method_sig :=
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
  end. *)

  (* Lemma method_frame_wf_r_config : forall CT sΓ rΓ h y ly Ty vals mdef m_sig args argtypes C m,
  wf_r_config CT sΓ rΓ h ->
  C < dom CT ->
  runtime_getVal rΓ y = Some (Iot ly) ->
  static_getType sΓ y = Some Ty ->
  runtime_lookup_list rΓ args = Some vals ->
  static_getType_list sΓ args = Some argtypes ->
  MethodLookup CT C m mdef ->
  m_sig = msignature mdef ->
  qualified_type_subtype CT Ty (vpa_qualified_type (sqtype Ty) (mreceiver m_sig)) ->
  Forall2 (fun arg T => qualified_type_subtype CT arg (vpa_qualified_type (sqtype Ty) T)) 
          argtypes (mparams m_sig) ->
  wf_r_config CT (mreceiver m_sig :: mparams m_sig) 
              {| vars := Iot ly :: vals |} h.
Proof.
  intros.
  unfold wf_r_config.
  repeat split.
  destruct H as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
  unfold wf_class_table in Hclass.
  destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
  exact Hclass.
  destruct H as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
  destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
  exact Hobj.
  destruct H as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
  destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
  exact Hotherclasses.
  destruct H as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
  destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
  apply Hcname_consistent.
  destruct H as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
  destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
  apply Hcname_consistent.

  destruct H as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
  exact Hheap.
  simpl.
  lia.

  {
    exists ly.
    split.
    simpl.
    reflexivity.
    destruct H as [_ [_ [_ [_ [_ Hcorr]]]]].
    specialize (Hcorr y).
    assert (Hy_dom : y < dom sΓ).
    { apply static_getType_dom in H2. exact H2. }
    specialize (Hcorr Hy_dom Ty H2).
    rewrite H1 in Hcorr.
    unfold wf_r_typable in Hcorr.
    destruct (r_type h ly) as [rqt|] eqn:Hrtype; [|contradiction].
    apply r_type_dom in Hrtype.
    exact Hrtype.
  }

  {
    simpl.
    constructor.
    simpl.
    destruct H as [_ [_ [_ [_ [_ Hcorr]]]]].
    specialize (Hcorr y).
    assert (Hy_dom : y < dom sΓ).
    { apply static_getType_dom in H2. exact H2. }
    specialize (Hcorr Hy_dom Ty H2).
    rewrite H1 in Hcorr.
    unfold wf_r_typable in Hcorr.
    destruct (r_type h ly) as [rqt|] eqn:Hrtype; [|contradiction].
    unfold r_type in Hrtype.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobj; [trivial | discriminate].
    assert (H_forall: Forall (fun value => match value with
      | Null_a => True
      | Iot loc => match runtime_getObj h loc with Some _ => True | None => False end
      end) vals).
    {
      eapply runtime_lookup_list_preserves_wf_values; eauto.
      unfold wf_r_config in H.
      destruct H as [_ [_ [Hrenv _]]].
      unfold wf_renv in Hrenv.
      destruct Hrenv as [Hrenvdom [Hreceiver Hforall]].
      (* destruct Hreceiver as [Hreceiverval Hreceivervaldom]. *)
      unfold wf_renv.
      repeat split.
      - (* dom (vars rΓ) > 0 *)
        exact Hrenvdom.
      - (* exists iot, gget (vars rΓ) 0 = Some (Iot iot) /\ iot < dom h *)
        exact Hreceiver.
      - (* Forall well-formed values *)
        exact Hforall.
    }
    exact H_forall.
  }

  {
    simpl. lia.
  }

  {
    constructor.
      destruct H as [Hclass _].
      apply method_sig_wf in H5; auto.
      destruct H5 as [Hreceiver _].
      rewrite H6.
      exact Hreceiver.
      destruct H as [Hclass _].
      apply method_sig_wf in H5; auto.
      destruct H5 as [_ Hparams].
      rewrite H6.
      exact Hparams.
  }

  {
    simpl.
    f_equal.
    apply Forall2_length in H8.
    apply static_getType_list_preserves_length in H4.
    apply runtime_lookup_list_preserves_length in H3.
    rewrite -> H4 in H8.
    rewrite <- H3 in H8.
    symmetry.
    exact H8.
  }
  {
    intros i Hi sqt Hnth.
    destruct i as [|i'].
    - (* Case: i = 0 (receiver) *)
      simpl in Hnth.
      injection Hnth as Heq. subst sqt.
      simpl.
      unfold wf_r_typable.
      destruct H as [Hclasstable [Hheap [_ [Hsenv [_ Hcorr]]]]].
      specialize (Hcorr y).
      assert (Hy_dom : y < dom sΓ).
      { apply static_getType_dom in H2. exact H2. }
      specialize (Hcorr Hy_dom Ty H2).
      rewrite H1 in Hcorr.

      eapply wf_r_typable_subtype; eauto.
      apply senv_var_domain with (sΓ := sΓ) (i := y); auto.
      unfold static_getType in H2.
      exact H2.

      apply method_sig_wf in H5; auto.
      destruct H5 as [Hreceiver _].
      unfold wf_stypeuse in Hreceiver.
      destruct (bound CT (sctype (mreceiver (msignature mdef)))) as [q_bound|] eqn:Hbound; [|contradiction].
      destruct Hreceiver as [_ Hdom].
      rewrite H6.
      exact Hdom.

      unfold wf_r_typable in Hcorr |- *.
      destruct (r_type h ly) as [rqt|] eqn:Hrtype; [|contradiction].
      destruct (get_this_var_mapping (vars {| vars := Iot ly :: vals |})) as [ι'|] eqn:Hthis.
      simpl in Hthis.
      injection Hthis as Hthis_eq.
      subst ι'.
      destruct (r_muttype h ly) as [q|] eqn:Hmut.
      destruct (get_this_var_mapping (vars rΓ)) as [ι'|] eqn:Hthis_orig; [|contradiction].
      destruct (r_muttype h ι') as [q_orig|] eqn:Hmut_orig; [|contradiction].
      (* exact Hcorr. Continue later *)
      admit.

      exfalso.
      unfold r_type in Hrtype.
      unfold r_muttype in Hmut.
      destruct (runtime_getObj h ly) as [obj|] eqn:Hobj; [|discriminate].
      destruct (get_this_var_mapping (vars rΓ)) as [this|] eqn:Hthis; [|discriminate].
      discriminate.

      exfalso.
      simpl in Hthis.
      discriminate.
      admit.

    - (* Case: i = S i' (parameters) *)
      simpl in Hnth.
      assert (Hi'_bound : i' < dom (mparams m_sig)).
      { simpl in Hi. lia. }
      assert (Hparam_nth : nth_error (mparams m_sig) i' = Some sqt).
      { exact Hnth. }
      simpl.
      (* Get the corresponding argument type and value *)
      assert (Hi'_args : i' < dom args).
      {
        apply Forall2_length in H8.
        apply static_getType_list_preserves_length in H4.
        apply runtime_lookup_list_preserves_length in H3.
        rewrite -> H4 in H8.
        rewrite <- H8 in Hi'_bound.
        exact Hi'_bound.
      }
      admit. (* Complex proof involving parameter correspondence *)
  }
Admitted. *)
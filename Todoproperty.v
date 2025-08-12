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
(* Qed. *)

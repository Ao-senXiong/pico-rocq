(* Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation Properties.
Require Import List.
Import ListNotations.
Require Import String.
From RecordUpdate Require Import RecordUpdate.

Theorem preservation_pico_test :
  forall CT sΓ rΓ h stmt rΓ' h' sΓ',
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ stmt sΓ' -> 
    eval_stmt OK rΓ h stmt OK rΓ' h' -> 
    wf_r_config CT sΓ' rΓ' h'.
Proof.
  intros.
  generalize dependent sΓ.
  generalize dependent sΓ'.
  remember OK as ok.
  induction H1; try discriminate.
  6: 
  {
    intros.
    inversion H10. subst sΓ'.
    assert (Hwf_method_frame : wf_r_config CT (mreceiver m_sig :: mparams m_sig) 
                                        {| vars := Iot ly :: vals |} h).
    {
      eapply method_frame_wf_r_config; eauto.
    }
    {
      subst.
      unfold wf_r_config.
      destruct H9 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
      destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      repeat split.
      exact Hclass.
      exact Hobj.
      exact Hotherclasses.
      apply Hcname_consistent.
      apply Hcname_consistent.
      admit.
      (* have H_result := IHeval_stmt eq_refl sΓ (mreceiver m_sig :: mparams m_sig) Hwf_method_frame Hmethod_typing. *)
      rewrite update_length.
      exact HrEnvLen.
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
          easy.
        + (* Case: x = S x' *)
          simpl.
          split.
          * exact Hiot.
          * admit. (* heap length monotone*)
      }
      {
        simpl.
        apply Forall_update.
        (* exact Hallvals. *)
        admit.
        destruct retval as [|loc]. easy.
        subst.
        admit.
        apply static_getType_dom in H16.
        rewrite <- Hlen.
        exact H16.
      }
      destruct Hsenv as [HsenvLength HsenvWellTyped].
      exact HsenvLength.
      destruct Hsenv as [HsenvLength HsenvWellTyped].
      exact HsenvWellTyped.
      rewrite update_length.
      exact Hlen.
      admit.
    }
  }
  - (* Case: stmt = Skip *)
    intros.
    inversion H0; subst.
    exact H.
  - (* Case: stmt = Local *)
    intros.
    inversion H1; subst.
    unfold wf_r_config in *.
    destruct H0 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    repeat split.
    + (* wellformed class *) 
    unfold  wf_class_table in Hclass. destruct Hclass as [Hclass _]. exact Hclass.
    + (* Object wellformedness *)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [Hobject _]]. exact Hobject.
    + (* All other classes have super class*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[Hotherclasses _]]]. exact Hotherclasses.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
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
        -- exact H5. (* assuming H is the wellformedness of T *)
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
            rewrite H0.
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
              ** unfold wf_r_typable in *. simpl.
              assert (get_this_var_mapping (vars rΓ ++ [Null_a]) = get_this_var_mapping (vars rΓ)).
              {
                unfold get_this_var_mapping.
                destruct (vars rΓ) as [|v0 vs]; reflexivity.
              }
              rewrite H0.
              exact Hcorr.
           ++ (* Case: nth_error (vars rΓ) i = None *)
              exfalso.
              apply nth_error_None in Hgetval.
              rewrite <- Hlen in Hgetval.
              lia.
  - (* Case: stmt = VarAss *)
    intros.
    unfold wf_r_config in *.
    destruct H1 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    repeat split.
    + (* wellformed class *) 
    unfold  wf_class_table in Hclass. destruct Hclass as [Hclass _]. exact Hclass.
    + (* Object wellformedness *)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [Hobject _]]. exact Hobject.
    + (* All other classes have super class*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[Hotherclasses _]]]. exact Hotherclasses.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
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
           -- (* x = 0 *) admit.
           -- (* x = S x' *)
              simpl. (* update (S x') v2 (v0 :: vs) = v0 :: update x' v2 vs *)
              exact Hiot.
    + (* wellformed runtime environment *)
    unfold wf_renv in *.
    destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
    simpl.
    apply Forall_update.
    * exact Hallvals.
    * destruct v2 as [|loc].
      -- trivial.
      -- inversion H2; subst.
        assert (Hloc_in_vars : exists i, nth_error (vars rΓ) i = Some (Iot loc)).
        ++ apply runtime_getVal_dom in H.
          destruct Hreceiverval as [iot Hiot].
          exists iot. 
          admit.
        ++ destruct Hloc_in_vars as [i Hi].
          assert (Hloc_wf := Forall_nth_error _ _ _ _ Hallvals Hi).
          simpl in Hloc_wf.
          exact Hloc_wf.
    * apply runtime_getVal_dom in H.
      exact H.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. inversion H2; subst. exact HsenvLength. 
    + (* wellformed static environment *)
      destruct Hsenv as [HsenvLength HsenvWellTyped]. inversion H2; subst. exact HsenvWellTyped.
    + (* length equality *)
      simpl.
      rewrite update_length.
      inversion H2; subst.
      exact Hlen.
    + (* correspondence between static and runtime environments *)
      intros i Hi sqt Hnth.
      destruct (Nat.eq_dec i x) as [Heq | Hneq].
      * (* Case: i = x (updated variable) *)
        subst i.
        unfold runtime_getVal.
        simpl.
        rewrite update_same.
        inversion H2; subst.
        rewrite <- Hlen; exact Hi.
        (* Need to show v2 is well-typed with respect to T' *)
        (* assert (Hsubtype: qualified_type_subtype CT Te Tx) by exact H3.
        assert (Hexpr_type: expr_has_type CT sΓ e Te) by exact H0. *)
        destruct v2 as [|loc].
        -- (* Case: v2 = Null_a *)
          trivial.
        -- (* Case: v2 = Iot loc *)
          (* Use subtyping to convert from T to sqt *)
          assert (Hsubtype_preserved : wf_r_typable CT (rΓ <| vars := update x (Iot loc) (vars rΓ) |>) h loc sqt).
          {
            (* assert (Hsqt_eq : sqt = Tx).
          {
            unfold static_getType in H2.
            rewrite H2 in Hnth.
            injection Hnth as Hsqt_eq.
            symmetry. exact Hsqt_eq.
          }
          subst sqt. *)
          assert (H_loc_Te : wf_r_typable CT rΓ h loc Te).
          {
            (* Apply expression evaluation preservation lemma *)
            apply (expr_eval_preservation CT sΓ rΓ h' e (Iot loc) rΓ h' Te).
            - unfold wf_r_config. repeat split; eauto. 
            + (* wellformed class *) 
            unfold  wf_class_table in Hclass. destruct Hclass as [Hclass _]. exact Hclass.
            + (* Object wellformedness *)
            unfold  wf_class_table in Hclass. destruct Hclass as [_ [Hobject _]]. exact Hobject.
            + (* All other classes have super class*)
            unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[Hotherclasses _]]]. exact Hotherclasses.
            + (* Class identifier match*)
            unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
            + (* Class identifier match*)
            unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
            + unfold wf_renv in Hrenv. destruct Hrenv as [Hrenvdom _]. exact Hrenvdom.
            + unfold wf_renv in Hrenv. destruct Hrenv as [_ [Hreceiver Hrvals]]. exact Hreceiver.
            + unfold wf_renv in Hrenv. destruct Hrenv as [_ [Hreceiver Hrvals]]. exact Hrvals.
            + unfold wf_senv in Hsenv. destruct Hsenv as [Hsenvdom _]. exact Hsenvdom.
            + unfold wf_senv in Hsenv. destruct Hsenv as [Hsenvdom Htypable]. exact Htypable.
            - exact H0.
            - exact H11.
          }
          (* Use subtyping to convert Te to Tx *)
          eapply wf_r_typable_subtype; eauto.
          (* The environment update doesn't affect loc's typing since loc is fresh *)
          unfold wf_r_typable in *.
          (* destruct (r_type h' loc) as [rqt|] eqn:Hrtype; [|contradiction]. *)
          destruct (get_this_var_mapping (vars (rΓ <| vars := update x (Iot loc) (vars rΓ) |>))) as [ι'|] eqn:Hthis.
          - simpl in Hthis.
            (* The this variable (at position 0) is preserved in the update *)
            destruct (get_this_var_mapping (vars rΓ)) as [ι0|] eqn:Hthis_orig.
            + (* Apply subtyping transitivity *)
              assert (Hι'_eq : ι' = ι0).
            {
              unfold get_this_var_mapping in Hthis, Hthis_orig.
              destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
              - discriminate Hthis_orig.
              - destruct x as [|x'].
                + contradiction H1. reflexivity.
                + simpl in Hthis.
                  destruct v0 as [|loc_v0] eqn:Hv0.
            * (* v0 = Null_a *)
              discriminate Hthis_orig.
            * (* v0 = Iot loc_v0 *)
              simpl in Hthis, Hthis_orig.
              injection Hthis_orig as Heq_orig.
              injection Hthis as Heq.
              rewrite <- Heq_orig, <- Heq.
              reflexivity.
            }
            eapply expr_has_type_class_in_table; eauto.
            + eapply expr_has_type_class_in_table; eauto.
          - 
            unfold get_this_var_mapping in Hthis.
            simpl in Hthis.
            destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
            * (* Empty case - contradicts well-formedness *)
              unfold wf_renv in Hrenv.
              destruct Hrenv as [Hdom _].
              rewrite Hvars in Hdom.
              simpl in Hdom.
              lia.
            * (* Non-empty case *)
              destruct x as [|x'].
              + (* x = 0 contradicts H1 *)
                contradiction H1. reflexivity.
              + (* x = S x', so update preserves position 0 *)
                simpl in Hthis.
                unfold wf_renv in Hrenv.
                destruct Hrenv as [_ [Hreceiver _]].
                destruct Hreceiver as [iot [Hiot_gget Hiot_dom]].
                unfold gget in Hiot_gget.
                rewrite Hvars in Hiot_gget.
                simpl in Hiot_gget.
                injection Hiot_gget as Hv0_eq.
                subst v0.
                simpl in Hthis.
                discriminate Hthis.
          - apply senv_var_domain with (sΓ:=sΓ) (i:=x). exact H. exact Hnth.
          - 
          unfold wf_r_typable in H_loc_Te |- *.
          destruct (r_type h' loc) as [rqt|] eqn:Hrtype; [|contradiction].
          destruct (get_this_var_mapping (vars rΓ)) as [ι0|] eqn:Hthis_orig; [|contradiction].
          destruct (r_muttype h' ι0) as [q|] eqn:Hmut; [|contradiction].
          assert (Hthis_preserved : get_this_var_mapping (vars (rΓ <| vars := update x (Iot loc) (vars rΓ) |>)) = Some ι0).
          {
            simpl.
            unfold get_this_var_mapping in Hthis_orig |- *.
            destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
            - discriminate Hthis_orig.
            - destruct x as [|x'].
              + contradiction H1. reflexivity.
              + simpl. exact Hthis_orig.
          }
          rewrite Hthis_preserved.
          rewrite Hmut.
          exact H_loc_Te.
          }
          exact Hsubtype_preserved.
      * (* Case: i ≠ x (unchanged variable) *)
        {
          unfold runtime_getVal.
          simpl.
          rewrite update_diff.
          - symmetry. exact Hneq.
          - assert (Hcorr_orig := Hcorr i Hi sqt Hnth).
            unfold runtime_getVal in Hcorr_orig.
            destruct (nth_error (vars rΓ) i) as [v|] eqn:Hval.
            + destruct v as [|loc].
              * trivial.
              * unfold wf_r_typable in Hcorr_orig |- *.
                destruct (r_type h' loc) as [rqt|] eqn:Hrtype; [|contradiction].
                destruct (get_this_var_mapping (vars rΓ)) as [ι'|] eqn:Hthis; [|contradiction].
                destruct (r_muttype h' ι') as [q|] eqn:Hmut; [|contradiction].
                assert (Hthis_preserved : get_this_var_mapping (update x v2 (vars rΓ)) = Some ι').
                {
                  unfold get_this_var_mapping in *.
                  destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
                  - discriminate Hthis.
                  - destruct x as [|x'].
                    + contradiction H1. reflexivity.
                    + simpl. exact Hthis.
                }
                rewrite Hthis_preserved.
                rewrite Hmut.
                exact Hcorr_orig.
            + contradiction.
        }
  - (* Case: stmt = FldWrite *)
    intros.
    inversion H7; subst.
    unfold wf_r_config in *.
    destruct H6 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    repeat split.
    + (* wellformed class *) 
    unfold  wf_class_table in Hclass. destruct Hclass as [Hclass _]. exact Hclass.
    + (* Object wellformedness *)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [Hobject _]]. exact Hobject.
    + (* All other classes have super class*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[Hotherclasses _]]]. exact Hotherclasses.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
    + (* wellformed heap *) 
    unfold wf_heap in *.
    intros ι Hdom.
    unfold update_field in *.
    destruct (runtime_getObj h lx) as [o_new|] eqn:Hobj.
    * (* Case: object exists at lx *)
      destruct (Nat.eq_dec ι lx) as [Heq | Hneq].
      -- (* Case: ι = lx (the updated object) *)
        subst ι.
        injection H12 as Ho_eq.
        subst o_new.
        unfold wf_obj.
        simpl.
        specialize (Hheap lx).
        rewrite update_length in Hdom.
        specialize (Hheap Hdom).
        unfold wf_obj in Hheap.
        rewrite Hobj in Hheap.
        destruct Hheap as [Hrtypeuse [Hlen_fields Hwf_fields]].
        unfold runtime_getObj.
        rewrite update_same.
        ++ exact Hdom.
        ++ repeat split.
          ** exact Hrtypeuse.
          ** simpl. rewrite update_length. 
          exists Hlen_fields.
          destruct Hwf_fields as [Hcollect [Hlen_eq Hforall2]].
          split.
          --- exact Hcollect.
          --- split.
            +++ exact Hlen_eq.
            +++ (* Need to show Forall2 for updated fields *)
              admit.
        -- unfold wf_obj, runtime_getObj.
        rewrite update_diff.
        ** rewrite update_length in Hdom.
          symmetry. exact Hneq.
        **
        rewrite update_length in Hdom.
        destruct (nth_error h ι) eqn:Htest.
        2:{
          exfalso.
          apply nth_error_None in Htest.
          lia.
        }
        admit.
        * exfalso.
        discriminate H12.
    + destruct Hrenv as [HrEnvLen [Hreceiver Hallvals]]. exact HrEnvLen.
    + destruct Hrenv as [HrEnvLen [Hreceiver Hallvals]]. destruct Hreceiver as [Hreceiverval Hreceivervaldom].
      exists Hreceiverval.
      split.
      * exact (proj1 Hreceivervaldom).
      * rewrite update_field_length.
        exact (proj2 Hreceivervaldom).
    + 
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      eapply Forall_impl; [| exact Hallvals].
      intros v Hv.
      destruct v as [|loc]; [trivial|].
      unfold update_field in Hv |- *.
      destruct (runtime_getObj h lx) as [o'|] eqn:Hobj'; [| exact Hv].
      destruct (Nat.eq_dec loc lx) as [Heq | Hneq].
      * subst loc. rewrite runtime_getObj_update_same; [trivial | ].
        apply runtime_getObj_dom in Hobj'. exact Hobj'. trivial.
      * 
      unfold runtime_getObj.
      rewrite update_diff.
      -- symmetry. exact Hneq.
      -- auto.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. exact HsenvLength.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. exact HsenvWellTyped.
    + exact Hlen.
    + 
    intros i Hi sqt Hnth.
      assert (Hcorr_orig := Hcorr i Hi sqt Hnth).
      destruct (runtime_getVal rΓ' i) as [v|] eqn:Hval; [|exact Hcorr_orig].
      destruct v as [|loc]; [trivial|].
      (* Need to show: wf_r_typable CT rΓ' (update_field h lx f v2) loc sqt *)
      unfold wf_r_typable in Hcorr_orig |- *.
      destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
      destruct (get_this_var_mapping (vars rΓ')) as [ι'|] eqn:Hthis; [|contradiction].
      destruct (r_muttype h ι') as [q|] eqn:Hmut; [|contradiction].
      (* Show that r_type and r_muttype are preserved by update_field *)
      assert (Hrtype_preserved : r_type (update_field h lx f v2) loc = Some rqt).
      {
        unfold r_type.
        unfold update_field.
        have H12_copy := H12.
        remember (runtime_getObj h lx) as obj_result eqn:Hobj_eq.
        destruct obj_result as [o'|].
        - destruct (Nat.eq_dec loc lx) as [Heq | Hneq].
          + subst loc. 
            rewrite runtime_getObj_update_same.
            * simpl. unfold r_type in Hrtype.
              destruct (runtime_getObj h lx) as [o_lx|] eqn:Hobj_lx; [|discriminate Hrtype].
              apply runtime_getObj_dom in Hobj_lx.
              exact Hobj_lx.
            * 
            have Hobj_eq_copy := Hobj_eq.
            symmetry in Hobj_eq.
            apply runtime_getObj_dom in Hobj_eq.
            simpl.
            unfold r_type in Hrtype.
            destruct (runtime_getObj h lx) as [o_lx|] eqn:Hobj_lx; [|discriminate Hrtype].
            injection Hrtype as Hrtype_eq.
            rewrite <- Hrtype_eq.
            injection H12 as Ho'_eq.
            subst o'.
            f_equal.
            injection Hobj_eq_copy as Ho_eq.
            rewrite Ho_eq.
            reflexivity.
          + rewrite runtime_getObj_update_diff.
            * symmetry. exact Hneq.
            * exact Hrtype.
        - exact Hrtype.
      }
      assert (Hmut_preserved : r_muttype (update_field h lx f v2) ι' = Some q).
      {
        unfold r_muttype, update_field.
        destruct (runtime_getObj h lx) as [o'|] eqn:Hobj'; [|exact Hmut].
        destruct (Nat.eq_dec ι' lx) as [Heq | Hneq].
        subst ι'.
        rewrite runtime_getObj_update_same.
        - simpl. unfold r_muttype in Hmut.
        destruct (runtime_getObj h lx) as [otest|] eqn:Hobj; [|discriminate Hmut].
        apply runtime_getObj_dom in Hobj. exact Hobj.
        - simpl.
        unfold r_muttype in Hmut.
        rewrite Hobj' in Hmut.
        exact Hmut.
        -
        {
          rewrite runtime_getObj_update_diff.
          - symmetry. exact Hneq.
          - exact Hmut.
        }
      }
      rewrite Hrtype_preserved.
      rewrite Hmut_preserved.
      exact Hcorr_orig.
  - (* Case: stmt = New *)
    intros.
    inversion H12.
    (* subst. *)
    unfold wf_r_config in *.
    destruct H11 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    repeat split.
    + (* wellformed class *) 
    unfold  wf_class_table in Hclass. destruct Hclass as [Hclass _]. exact Hclass.
    + (* Object wellformedness *)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [Hobject _]]. exact Hobject.
    + (* All other classes have super class*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[Hotherclasses _]]]. exact Hotherclasses.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
    + (* wellformed heap *) 
    unfold wf_heap.
    intros ι Hι.
    subst.
    rewrite length_app in Hι.
    simpl in Hι.
    destruct (Nat.eq_dec ι (dom h)) as [Heq | Hneq].
    * (* ι = dom h (new object) *)
      subst.
      unfold wf_obj.
      rewrite runtime_getObj_last.
      split.
      -- (* wf_rtypeuse for new object *)
        simpl.
        unfold wf_rtypeuse.
        destruct (bound CT C) as [q_c_val|] eqn:Hbound.
        ++ unfold constructor_sig_lookup in H2.
        destruct (find_class CT C) as [def|] eqn:Hfind.
        ** apply find_class_dom in Hfind.
          exact Hfind.
        ** exfalso.
        unfold bound in Hbound.
        rewrite Hfind in Hbound.
        discriminate Hbound.
        ++ 
          unfold constructor_sig_lookup in H2.
          destruct (constructor_def_lookup CT C) as [ctor|] eqn:Hctor.
          ** unfold constructor_def_lookup in Hctor.
            destruct (find_class CT C) as [def|] eqn:Hfind.
            --- unfold bound in Hbound.
              rewrite Hfind in Hbound.
              discriminate Hbound.
            --- discriminate Hctor.
          ** discriminate H2.
      --
      repeat split.
       admit.
    * (* ι < dom h (existing object) *)
      assert (ι < dom h) by lia.
      unfold wf_obj.
      rewrite runtime_getObj_last2; auto.
      {
        specialize (Hheap ι H4).
        unfold wf_obj in Hheap |- *.
        destruct (runtime_getObj h ι) as [o|] eqn:Hobj; [|contradiction].
          destruct Hheap as [Hrtypeuse [Hfields_len Hforall2]].
          repeat split.
          + exact Hrtypeuse.
          + 
          {
          exists Hfields_len.
          destruct Hforall2 as [Hcollect [Hlen_eq Hforall2_prop]].
          split.
          - exact Hcollect.
          - split.
            + exact Hlen_eq.
            + eapply Forall2_impl; [|exact Hforall2_prop].
              intros v fdef Hprop.
              destruct v as [|loc]; [trivial|].
              destruct (runtime_getObj h loc) as [obj_loc|] eqn:Hobj_loc.
              * (* loc exists in original heap *)
                destruct Hprop as [rqt [Hrtype_orig Hsubtype_orig]].
                assert (loc < dom h). {
                  (apply runtime_getObj_dom in Hobj_loc).
                  exact Hobj_loc.
                }
                rewrite runtime_getObj_last2; auto.
                rewrite Hobj_loc.
                exists rqt.
                split.
                -- unfold r_type in Hrtype_orig |- *.
                  rewrite runtime_getObj_last2; auto.
                -- exact Hsubtype_orig.
              * contradiction Hprop.
              }
       }
    + (* Length of runtime environment greater than 0 *)
      simpl. destruct Hsenv as [HsenvLength HsenvWellTyped].
      subst.
      rewrite update_length. rewrite <- Hlen.
      exact HsenvLength.
    +
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      destruct Hreceiverval as [iot Hiot].
      destruct Hiot as [Hiot Hiot_dom].
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
              {
                split.
                - (* Show update preserves position 0 *)
                  simpl. 
                  exfalso. apply H3. reflexivity.
                - (* Show iot is still in extended heap domain *)
                  subst.
                  rewrite length_app. simpl.
                  lia.
              }
           --    (* update (S x') v2 (v0 :: vs) = v0 :: update x' v2 vs *)
            split.   
            subst.
            exact Hiot.
            rewrite H25.
            rewrite length_app.
            simpl.
            lia.
    + 
    destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
    simpl.
    subst.
    apply Forall_update.
    * eapply Forall_impl; [| exact Hallvals].
      intros v Hv.
      destruct v as [|loc]; [trivial|].
      destruct (runtime_getObj h loc) as [obj|] eqn:Hobj; [| contradiction].
      assert (Hloc_dom : loc < dom h) by (apply runtime_getObj_dom in Hobj; exact Hobj).
    rewrite runtime_getObj_last2.
    -- exact Hloc_dom.
    -- rewrite Hobj. trivial.
    * (* Show new object is well-formed *)
      assert (dom h + 1 = S (dom h)) by lia.
      unfold runtime_getObj.
      simpl.
      assert (Hlen_extended: dom (h ++ [{| rt_type := {| rqtype := qadapted; rctype := C |}; fields_map := vals |}]) = dom h + 1).
      -- rewrite length_app. simpl. lia.
      -- rewrite nth_error_app2.
      ** lia.
      ** replace (dom h - dom h) with 0 by lia.
        simpl. reflexivity.
      * assert (Hx_dom : x < dom sΓ) by (apply static_getType_dom in H0; exact H0).
      rewrite <- Hlen; exact Hx_dom.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. exact HsenvLength.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. exact HsenvWellTyped.
    + subst. rewrite update_length. rewrite <- Hlen. lia.
    + 
    {
      intros i Hi sqt Hnth.
      destruct (Nat.eq_dec i x) as [Heq | Hneq].
      - (* Case: i = x (newly assigned variable) *)
        subst i.
        simpl.
        unfold runtime_getVal.
        subst.
        rewrite update_same.
          + assert (x < dom sΓ) by (apply static_getType_dom in H0; exact H0).
          rewrite <- Hlen. exact H4.
        + (* Show wf_r_typable for the new object *)
          {
            unfold wf_r_typable.
            unfold r_type.
            rewrite runtime_getObj_last.
            simpl.
            unfold get_this_var_mapping.
            simpl.
            destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
            - exfalso.
              unfold wf_renv in Hrenv.
              destruct Hrenv as [HrEnvLen _].
              rewrite Hvars in HrEnvLen.
              simpl in HrEnvLen.
              lia.
            - unfold r_muttype.
            destruct x as [|x'].
            + (* Case: x = 0 *)
              contradiction H3. reflexivity.
            + (* Case: x = S x' *)
              unfold runtime_getVal in H17.
              rewrite Hvars in H17.
              simpl in H17.
              injection H17 as H17_eq.
              subst v0.
              simpl.
              unfold r_muttype.
              rewrite heap_extension_preserves_objects.
              * unfold r_muttype in H19.
                destruct (runtime_getObj h l1) as [obj|] eqn:Hobj; [|discriminate].
                apply runtime_getObj_dom in Hobj.
                exact Hobj.
              * unfold r_muttype in H19.
                destruct (runtime_getObj h l1) as [obj|] eqn:Hobj; [|discriminate].
                injection H19 as H19_eq.
                rewrite H19_eq.
                split.
                assert (Hsqt_eq : sqt = Tx).
                {
                  unfold static_getType in H0.
                  rewrite Hnth in H0.
                  injection H0 as H0_eq.
                  exact H0_eq.
                }
                subst sqt.
                unfold runtime_type_to_qualified_type.
                simpl.
                {
                  apply qualified_type_subtype_base_subtype in H10.
                  - exact H10.
                  - (* C < dom CT *)
                    (* This should follow from constructor well-formedness *)
                    apply constructor_sig_lookup_dom in H2.
                    exact H2.
                  - (* sctype Tx < dom CT *)
                    (* This should follow from sΓ well-formedness *)
                    assert (Hwf_Tx : wf_stypeuse CT (sqtype Tx) (sctype Tx)).
                    {
                      unfold wf_senv in Hsenv.
                      destruct Hsenv as [_ Hforall].
                      apply (Forall_nth_error _ _ _ _ Hforall Hnth).
                    }
                    unfold wf_stypeuse in Hwf_Tx.
                    destruct (bound CT (sctype Tx)) as [q_bound|] eqn:Hbound; [|contradiction].
                    destruct Hwf_Tx as [_ Hdom].
                    exact Hdom.  
                }
                {
                  assert (Hsqt_eq : sqt = Tx).
                  {
                    unfold static_getType in H0.
                    rewrite Hnth in H0.
                    injection H0 as H0_eq.
                    exact H0_eq.
                  }
                  subst sqt.

                  (* Extract qualifier subtyping from H10 *)
                  apply qualified_type_subtype_q_subtype in H10.
                  - (* Use the fact that qadapted was constructed to be compatible *)
                    unfold qualifier_typable.
                    (* qadapted comes from q_project_q_r, so it must be Mut_r or Imm_r *)
                    destruct qadapted as [|]; 
                    (* Use H7: vpa_mutabilty qc (cqualifier consig) = qc and other hypotheses *)
                    (* to show the compatibility *)
                    simpl.
                    simpl in H10.
                    unfold q_project_q_r in H21.
                    assert (Hvpa_mut : vpa_mutabilty (q_r_proj qthisr) qc = Mut).
                    {
                      unfold q_project_q_r in H21.
                      destruct (vpa_mutabilty (q_r_proj qthisr) qc) eqn:Hvpa.
                      - (* Case: vpa_mutabilty ... = Mut *)
                        reflexivity.
                      - discriminate H21.
                      - discriminate H21.
                      - discriminate H21.
                      - discriminate H21.
                      - discriminate H21.
                    }
                    rewrite Hvpa_mut in H21.
                    apply vpa_type_to_type_mut_cases in Hvpa_mut.
                    destruct (sqtype Tx) eqn: qx.
                    destruct Hvpa_mut as [H_qc_mut | [H_qthis_mut H_qc_rdm]].
                    assert (vpa_mutabilty (q_r_proj qthisr) Mut = Mut).
                    {
                      unfold vpa_mutabilty.
                      destruct (q_r_proj qthisr). all: try reflexivity.
                    }
                    rewrite H4. easy.
                    assert (vpa_mutabilty (q_r_proj qthisr) Mut = Mut).
                    {
                      unfold vpa_mutabilty.
                      destruct (q_r_proj qthisr). all: try reflexivity.
                    }
                    rewrite H4. easy.
                    exfalso.
                    destruct Hvpa_mut as [H_qc_mut | [H_qthis_mut H_qc_rdm]].
                    {
                      - (* Case: qc = Mut *)
                      subst qc.
                      (* Now we have Mut ⊑ Imm, which is impossible *)
                      inversion H10; discriminate.
                    }
                    subst qc. inversion H10; discriminate. 
                    destruct Hvpa_mut as [H_qc_mut | [H_qthis_mut H_qc_rdm]].
                    subst qc.
                    exfalso.
                    inversion H10; discriminate.
                    rewrite H_qthis_mut.
                    unfold vpa_mutabilty.
                    simpl.
                    reflexivity.
                    assert (vpa_mutabilty (q_r_proj qthisr) Rd = Rd).
                    {
                      unfold vpa_mutabilty.
                      destruct (q_r_proj qthisr); simpl; reflexivity.
                    }
                    rewrite H4. reflexivity.
                    assert (vpa_mutabilty (q_r_proj qthisr) Lost = Lost).
                    {
                      unfold vpa_mutabilty.
                      destruct (q_r_proj qthisr); simpl; reflexivity.
                    }
                    rewrite H4. reflexivity.
                    exfalso.
                    destruct Hvpa_mut as [H_qc_mut | [H_qthis_mut H_qc_rdm]].
                    subst qc.
                    inversion H10; discriminate.
                    subst qc.
                    inversion H10; discriminate.
                    simpl in H10.
                    unfold q_project_q_r in H21.
                    assert (Hvpa_imm : vpa_mutabilty (q_r_proj qthisr) qc = Imm).
                    {
                      unfold q_project_q_r in H21.
                      destruct (vpa_mutabilty (q_r_proj qthisr) qc) eqn:Hvpa.
                      - discriminate H21.
                      - reflexivity.
                      - discriminate H21.
                      - discriminate H21.
                      - discriminate H21.
                      - discriminate H21.
                    }
                    apply vpa_type_to_type_imm_cases in Hvpa_imm.
                    {
                      destruct Hvpa_imm as [H_qc_imm | [H_qthis_imm H_qc_rdm]].
                      - (* Case: qc = Imm *)
                        subst qc.
                        assert (Hsqtype_imm : sqtype Tx =  Imm \/ sqtype Tx = Rd).
                        {
                          inversion H10; subst.
                          left. reflexivity.
                          right. reflexivity.
                        }
                        destruct Hsqtype_imm as [qximm|qxrd].
                        rewrite qximm.
                        unfold vpa_mutabilty.
                        destruct (q_r_proj qthisr); simpl; reflexivity.
                        rewrite qxrd.
                        unfold vpa_mutabilty.
                        destruct (q_r_proj qthisr); simpl; reflexivity.
                      - (* Case: q_r_proj qthisr = Imm /\ qc = RDM *)
                        assert (Hsqtype_rdm : sqtype Tx =  RDM \/ sqtype Tx = Rd).
                        {
                          inversion H10; subst.
                          left. symmetry. exact H11.
                          right. reflexivity.
                          discriminate H4.
                        }
                        destruct Hsqtype_rdm as [qxrdm | qxrd].
                        rewrite qxrdm. rewrite H_qthis_imm.
                        unfold vpa_mutabilty.
                        reflexivity.
                        rewrite qxrd.
                        destruct (q_r_proj qthisr); simpl; reflexivity.
                    }
                  - (* Domain constraints *)
                    apply constructor_sig_lookup_dom in H2. exact H2.
                  - (* Domain constraints *)
                    assert (Hwf_Tx : wf_stypeuse CT (sqtype Tx) (sctype Tx)).
                    {
                      unfold wf_senv in Hsenv.
                      destruct Hsenv as [_ Hforall].
                      apply (Forall_nth_error _ _ _ _ Hforall Hnth).
                    }
                    unfold wf_stypeuse in Hwf_Tx.
                    destruct (bound CT (sctype Tx)) as [q_bound|] eqn:Hbound; [|contradiction].
                    destruct Hwf_Tx as [_ Hdom].
                    exact Hdom.  
                }
          }
      - (* Case: i ≠ x (existing variable) *)
        simpl.
        unfold runtime_getVal.
        subst.
        rewrite update_diff; auto.
        assert (Hcorr_orig := Hcorr i Hi sqt Hnth).
        destruct (runtime_getVal rΓ i) as [v|] eqn:Hval.
      + (* Case: runtime_getVal rΓ i = Some v *)
        destruct v as [|loc].
        * (* Case: v = Null_a *)
        unfold runtime_getVal in Hval.
        rewrite Hval.
        trivial.
        * (* Case: v = Iot loc *)
        unfold runtime_getVal in Hval.
        rewrite Hval.
        unfold wf_r_typable in Hcorr_orig |- *.
        destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
        destruct (get_this_var_mapping (vars rΓ)) as [ι'|] eqn:Hthis; [|contradiction].
        destruct (r_muttype h ι') as [q|] eqn:Hmut; [|contradiction].
        assert (Hthis_preserved : get_this_var_mapping (vars (rΓ <| vars := update x (Iot dom h) (vars rΓ) |>)) = Some ι').
        {
          simpl. 
          unfold get_this_var_mapping in Hthis |- *.
          destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
          - discriminate Hthis.
          - destruct x as [|x'].
            + contradiction H3. reflexivity.
            + simpl. exact Hthis.
            }
            rewrite Hthis_preserved.
            assert (Hloc_bound : loc < dom h).
          {
            unfold r_type in Hrtype.
            destruct (runtime_getObj h loc) as [obj|] eqn:Hobj; [|discriminate].
            apply runtime_getObj_dom in Hobj. exact Hobj.
          }
          assert (Hrtype_ext : r_type (h ++ [{| rt_type := {| rqtype := qadapted; rctype := C |}; fields_map := vals |}]) loc = Some rqt).
          {
            unfold r_type in Hrtype |- *.
            rewrite heap_extension_preserves_objects; auto.
          }
          assert (Hmut_ext : r_muttype (h ++ [{| rt_type := {| rqtype := qadapted; rctype := C |}; fields_map := vals |}]) ι' = Some q).
          {
            unfold r_muttype in Hmut |- *.
            assert (Hι'_bound : ι' < dom h).
            {
              unfold r_muttype in Hmut.
              destruct (runtime_getObj h ι') as [obj|] eqn:Hobj; [|discriminate].
              apply runtime_getObj_dom in Hobj. exact Hobj.
            }
            rewrite heap_extension_preserves_objects; auto.
          }
          rewrite Hrtype_ext.
          rewrite Hmut_ext.
          exact Hcorr_orig.
          + contradiction Hcorr_orig.
          }
  - (* Case: stmt = Seq *)
    intros. inversion H1; subst.
    specialize (IHstmt_typing1 rΓ'0 h'0 rΓ h H H3) as IH1.
    specialize (IHstmt_typing2 rΓ' h' rΓ'0 h'0 IH1 H6) as IH2.
    exact IH2.
Admitted. *)
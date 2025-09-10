Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation.
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
    + (* wellformed class *) 
    unfold  wf_class_table in Hclass. destruct Hclass as [Hclass _]. exact Hclass.
    + (* Object wellformedness *)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [Hobject _]]. exact Hobject.
    + (* All other classes have super class*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[Hotherclasses _]]]. exact Hotherclasses.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. exact Hclassnamematch.
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
              ** unfold wf_r_typable in *. simpl.
              assert (get_this_var_mapping (vars rΓ ++ [Null_a]) = get_this_var_mapping (vars rΓ)).
              {
                unfold get_this_var_mapping.
                destruct (vars rΓ) as [|v0 vs]; reflexivity.
              }
              rewrite H2.
              exact Hcorr.
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
    + (* wellformed class *) 
    unfold  wf_class_table in Hclass. destruct Hclass as [Hclass _]. exact Hclass.
    + (* Object wellformedness *)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [Hobject _]]. exact Hobject.
    + (* All other classes have super class*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[Hotherclasses _]]]. exact Hotherclasses.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. exact Hclassnamematch.
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
    unfold wf_renv in *.
    destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
    simpl.
    apply Forall_update.
    * exact Hallvals.
    * destruct v2 as [|loc].
      -- trivial.
      -- inversion H11; subst.
        assert (Hloc_in_vars : exists i, nth_error (vars rΓ) i = Some (Iot loc)).
        ++ apply runtime_getVal_dom in H4.
          exists x0. 
          unfold runtime_getVal in H4.
          inversion H11; subst.
          unfold runtime_getVal in H7.
          exact H7.
        ++ destruct Hloc_in_vars as [i Hi].
          assert (Hloc_wf := Forall_nth_error _ _ _ _ Hallvals Hi).
          simpl in Hloc_wf.
          exact Hloc_wf.
      ++
      specialize (Hheap v).
      assert (Hv_dom : v < dom h').
      {
        apply runtime_getObj_dom in H6.
        exact H6.
      }
      specialize (Hheap Hv_dom).
      unfold wf_obj in Hheap.
      rewrite H6 in Hheap.
      (* destruct Hheap as [_ [_ Hwf_fields]]. *)
      assert (Hloc_in_fields : nth_error (fields_map o) f = Some (Iot loc)).
      {
        exact H7.
      }
      destruct Hheap as [_ [field_defs [Hcollect [Hlen_eq Hforall2]]]].
      assert (Hfield_exists : exists fdef, nth_error field_defs f = Some fdef).
      {
        assert (Hf_dom : f < List.length (fields_map o)) by (apply nth_error_Some; rewrite Hloc_in_fields; discriminate).
        rewrite Hlen_eq in Hf_dom.
        destruct (nth_error field_defs f) as [fdef|] eqn:Hfdef.
        - exists fdef. reflexivity.
        - exfalso. apply nth_error_None in Hfdef. lia.
      }
      destruct Hfield_exists as [fdef Hfdef].
      (* assert (Hfield_prop := Forall2_nth_error_prop _ _ _ _ _ _ Hwf_fields Hloc_in_fields Hfdef).
      simpl in Hfield_prop. *)
      destruct (runtime_getObj h' loc) as [o'|] eqn:Hloc_obj.
      trivial.
      assert (Hfield_prop := Forall2_nth_error_prop _ _ _ _ _ _ Hforall2 Hloc_in_fields Hfdef).
      simpl in Hfield_prop.
      rewrite Hloc_obj in Hfield_prop.
      exact Hfield_prop.
    * apply runtime_getVal_dom in H8.
      exact H8.
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
            assert (Hsqt_eq : sqt = Tx).
          {
            unfold static_getType in H2.
            rewrite H2 in Hnth.
            injection Hnth as Hsqt_eq.
            symmetry. exact Hsqt_eq.
          }
          subst sqt.
          assert (H_loc_Te : wf_r_typable CT rΓ h' loc Te).
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
            unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. exact Hclassnamematch.
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
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. exact Hclassnamematch.
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
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. exact Hclassnamematch.
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
  - (* Case: stmt = Call *)
    intros.
    inversion H9; subst.
    unfold wf_r_config in *.
    destruct H8 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    repeat split.
    + (* wellformed class *) 
    unfold  wf_class_table in Hclass. destruct Hclass as [Hclass _]. exact Hclass.
    + (* Object wellformedness *)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [Hobject _]]. exact Hobject.
    + (* All other classes have super class*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[Hotherclasses _]]]. exact Hotherclasses.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. exact Hclassnamematch.
    + admit.
    + (* Length of runtime environment greater than 0 *)
      simpl. destruct Hsenv as [HsenvLength HsenvWellTyped].      
      rewrite update_length. rewrite <- Hlen.
      exact HsenvLength.
    + destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      destruct Hreceiverval as [iot Hiot].
      exists iot.
      simpl.
      unfold gget in *.
      destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
      * (* Case: vars rΓ = [] *)
        exfalso.
        simpl in HrEnvLen.
        lia.
      * (* Case: vars rΓ = v0 :: vs *)
        simpl.
        destruct x as [|x'].
      -- (* Case: x = 0 *)
        (* This should be impossible - method calls shouldn't assign to receiver *)
        contradiction H4.
      reflexivity.
      -- (* Case: x = S x' *)
        simpl.
        (* update (S x') retval (v0 :: vs) = v0 :: update x' retval vs *)
        simpl in Hiot.
        destruct Hiot as [Hiot Hiotdom].
        split.
        exact Hiot.
        admit.
    + 
    unfold wf_renv in *.
    destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
    simpl.
    apply Forall_update.
    * (* Show existing values are still well-formed in h' *)
      eapply Forall_impl; [| exact Hallvals].
      intros v Hv.
      destruct v as [|loc]; [trivial|].
      (* For Iot loc, show runtime_getObj h' loc = Some _ *)
      (* This follows from heap preservation during method execution *)
      admit.
    * (* Show retval is well-formed *)
      destruct retval as [|loc]; [trivial|].
      (* retval comes from method execution, so it's well-formed in h' *)
      (* The return value loc comes from rΓ'' which should be well-formed w.r.t. h' *)
      assert (Hwf_method_result: wf_renv CT rΓ'' h').
      {
        (* This should follow from your evaluation preservation theorem *)
        (* You need a lemma that method body execution preserves well-formedness *)
        admit.
      }
      unfold wf_renv in Hwf_method_result.
      destruct Hwf_method_result as [_ [_ Hallvals_method]].
      (* Use the fact that runtime_getVal rΓ'' (mreturn mbody) = Some (Iot loc) *)
      assert (Hreturn_bound: mreturn mbody < dom (vars rΓ'')).
      {
        apply runtime_getVal_dom in H24.
        exact H24.
      }
      assert (Hretval_wf := Forall_nth_error _ _ _ _ Hallvals_method H24).
      simpl in Hretval_wf.
      exact Hretval_wf.
    * (* x < length (vars rΓ) *)
      assert (x < dom sΓ) by (apply static_getType_dom in H0; exact H0).
      rewrite <- Hlen; exact H8.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. exact HsenvLength.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. exact HsenvWellTyped.
    + rewrite update_length. exact Hlen.
    + intros i Hi sqt Hsqt.
    destruct (Nat.eq_dec i x) as [Heq | Hneq].
    * (* Case: i = x *)
      subst i.
      (* rewrite update_same. *)
      (* Use the fact that retval has the correct type from method execution *)
      (* This follows from your method typing and evaluation preservation *)
      admit.
    * (* Case: i ≠ x *)
      simpl.
      unfold runtime_getVal.
      rewrite update_diff; auto.
        destruct (nth_error (vars rΓ) i) as [v|] eqn:Hval.
      -- destruct v as [|loc].
        ++ trivial.
        ++ (* Need to show wf_r_typable with updated environment and new heap *)
        admit.
      -- (* None case *)
        assert (Hcorr_i := Hcorr i Hi sqt Hsqt).
            exfalso.
        assert (i < dom (vars rΓ)) by (rewrite <- Hlen; exact Hi).
        apply nth_error_None in Hval.
        lia.
  - (* Case: stmt = Seq *)
    intros. inversion H1; subst.
    specialize (IHstmt_typing1 rΓ'0 h'0 rΓ h H H3) as IH1.
    specialize (IHstmt_typing2 rΓ' h' rΓ'0 h'0 IH1 H6) as IH2.
    exact IH2.
Admitted.

Definition get_this_type (sΓ : s_env) : option qualified_type :=
  match sΓ with
  | [] => None
  | Tthis :: _ => 
    Some Tthis
  end.

Definition imm_runtime_type (C : class_name) : runtime_type := 
  mkruntime_type Imm_r C.

Lemma imm_not_subtype_mut : ~ q_subtype Imm Mut.
Proof.
  intro H.
  inversion H; subst; discriminate.
Qed.

(* ------------------------------------------------------------- *)
(* Immutability properties for PICO *)
Notation "l [ i ]" := (nth_error l i) (at level 50).

Theorem immutability_pico :
  forall CT sΓ rΓ h stmt rΓ' h' sΓ' l C vals vals' f,
    l < dom h ->
    runtime_getObj h l = Some (mkObj (mkruntime_type Imm_r C) vals) ->
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ stmt sΓ' -> 
    eval_stmt OK rΓ h stmt OK rΓ' h' -> 
    runtime_getObj h' l = Some (mkObj (mkruntime_type Imm_r C) vals') ->
    sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA ->
    nth_error vals f = nth_error vals' f.
Proof.
  intros. remember OK as ok. induction H3; try discriminate.
  - (* Skip *) inversion H4. intros; subst; rewrite H0 in H4; injection H4; auto.
  - (* Local *) inversion H4; intros; subst; rewrite H0 in H4; injection H4; auto.
  - (* VarAss *) inversion H4; intros; subst; rewrite H0 in H4; injection H4; auto.
  - (* FldWrite *) 
  {
    destruct (Nat.eq_dec l lx) as [Heq_l | Hneq_l].
    - (* Case: l = lx (same object being written to) *)
      subst l.
      (* Extract the object type from H0 and H6 *)
      rewrite H0 in H6.
      injection H6 as H6_eq.
      subst o.
      (* Now we have an immutable object, but can_assign returned true *)
      (* This should be impossible for Final/RDA fields on immutable objects *)
      destruct (Nat.eq_dec f f0) as [Heq_f | Hneq_f].
      + (* Case: f = f0 (same field being written) *)
        subst f.
        (* Show contradiction: can_assign should be false for immutable Final/RDA fields *)
        exfalso.
        unfold wf_r_config in H1.
        destruct H1 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
        assert (Hx_bound : x < dom sΓ) by (apply runtime_getVal_dom in H3; rewrite <- Hlen in H3; exact H3).
        inversion H2; subst.
        specialize (Hcorr x Hx_bound Tx H12).
        rewrite H3 in Hcorr.
        assert (Hsubtype: base_subtype CT C (sctype Tx)).
        {
          unfold wf_r_typable in Hcorr.
          destruct (r_type h lx) as [rqt|] eqn:Hrtype; [|contradiction].
          unfold r_type in Hrtype.
          rewrite H0 in Hrtype.
          simpl in Hrtype.
          injection Hrtype as Hrtype_eq.
          destruct (get_this_var_mapping (vars rΓ)) as [ι'|] eqn:Hthis; [|contradiction].
          destruct (r_muttype h ι') as [q|] eqn:Hmut; [|contradiction].
          destruct Hcorr as [Hbase_sub _].
          rewrite <- Hrtype_eq in Hbase_sub.
          simpl in Hbase_sub.
          exact Hbase_sub.
        }
        apply vpa_assingability_assign_cases in H20.
        destruct H5 as [Hffinal | HfRDA].
        apply (sf_assignability_subtyping_reverse CT C (sctype Tx) f0 Final) in Hsubtype.
        destruct Hsubtype as [HqxFinal | Hqxnonexist].
        assert (Heq : a = Final).
        {
          eapply sf_assignability_deterministic_rel; eauto.
        }
        subst a.
        destruct H20 as [HAassignable | HARDA ].
        discriminate HAassignable.
        destruct HARDA as [_ HFinalRDA].
        discriminate HFinalRDA.
        exfalso.
        apply Hqxnonexist.
        exists a.
        exact H17.
        exact Hffinal.
        apply (sf_assignability_subtyping_reverse CT C (sctype Tx) f0 RDA) in Hsubtype.
        2:{exact HfRDA.
        }
        destruct Hsubtype as [HqxRDA | Hqxnonexist].
        assert (Heq : a = RDA).
        {
          eapply sf_assignability_deterministic_rel; eauto.
        }
        subst a.
        destruct H20 as [HAassignable | HARDA ].
        discriminate HAassignable.
        unfold wf_r_typable in Hcorr.
        destruct HARDA as [HsqtypeMut _].
        unfold r_type in Hcorr.
        rewrite H0 in Hcorr.
        simpl in Hcorr.
        destruct (get_this_var_mapping (vars rΓ)) as [ι'|] eqn:Hthis; [|contradiction].
        destruct (r_muttype h ι') as [q|] eqn:Hmut; [|contradiction].
        destruct Hcorr as [_ Hqual].
        unfold qualifier_typable in Hqual.
        rewrite HsqtypeMut in Hqual.
        unfold vpa_mutabilty in Hqual.
        assert (Hq_proj : q_r_proj q = Imm \/ q_r_proj q = Mut) by apply q_r_proj_imm_or_mut.
        destruct Hq_proj as [HqImm | HqMut].
        -- (* Case: q_r_proj q = Imm *)
          rewrite HqImm in Hqual.
          simpl in Hqual.
          unfold is_true in Hqual.
          discriminate Hqual.
        -- (* Case: q_r_proj q = Mut *)  
          rewrite HqMut in Hqual.
          simpl in Hqual.
          unfold is_true in Hqual.
          discriminate Hqual.
        -- 
          apply Hqxnonexist.
          exists a.
          exact H17. 
        + 
        assert (Hvals_eq : vals' = [f0 ↦ v2] (vals)).
        {
          (* Use the definition of update_field and the fact that h' contains the updated object *)
          unfold update_field in H9.
          rewrite H0 in H9.
          rewrite H9 in H4.
          unfold runtime_getObj in H4.
          (* Apply update_same to get the updated object *)
          assert (Hget_same : nth_error (update lx {| rt_type := {| rqtype := Imm_r; rctype := C |}; fields_map := [f0 ↦ v2] (vals) |} h) lx = 
                              Some {| rt_type := {| rqtype := Imm_r; rctype := C |}; fields_map := [f0 ↦ v2] (vals) |}).
          {
            apply update_same.
            exact H.
          }
          rewrite Hget_same in H4.
          injection H4 as H4_eq.
          symmetry. exact H4_eq.
        }
        rewrite Hvals_eq.
        unfold getVal.
        rewrite update_diff.
        symmetry. exact Hneq_f.
        reflexivity.
    -
    assert (Hl_unchanged : runtime_getObj h' l = runtime_getObj h l).
    {
      rewrite H9.
      unfold update_field.
      destruct (runtime_getObj h lx) as [o'|] eqn:Hlx_obj.
      - (* Case: Some o' *)
        injection H6 as H6_eq. subst o'.
        unfold runtime_getObj.
        apply update_diff.
        symmetry. exact Hneq_l.
      - (* Case: None - contradicts H6 *)
        rewrite H6 in Hlx_obj.
        discriminate.
    }
    rewrite H0 in Hl_unchanged.
    rewrite Hl_unchanged in H4.
    injection H4 as H4_eq.
    rewrite <- H4_eq.
    reflexivity.
  }
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
    - (* wellformed class *) 
    unfold  wf_class_table in Hclass. destruct Hclass as [Hclass _]. exact Hclass.
    - (* Object wellformedness *)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [Hobject _]]. exact Hobject.
    - (* All other classes have super class*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[Hotherclasses _]]]. exact Hotherclasses.
    - (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. exact Hclassnamematch.
    - exact Hheap.
    - rewrite H11. simpl. lia.
    - exists ly. rewrite H11. simpl. split. reflexivity. unfold r_basetype in H6.
      destruct (runtime_getObj h ly) as [o|] eqn:Hobj; [apply runtime_getObj_dom in Hobj; exact Hobj | discriminate H6].
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
  - (* Seq *) (* Apply IH transitively *)
  admit.
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
      sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA ->
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

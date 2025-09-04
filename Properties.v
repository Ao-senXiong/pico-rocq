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
  (* 6: { intros. inversion H9; subst. induction H23. 
  8: { eapply IHeval_stmt; eauto. exact H21. } 
  } *)
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
        destruct Hheap as [_ [_ Hwf_fields]].
        assert (Hloc_in_fields : nth_error (fields_map o) f = Some (Iot loc)).
        {
          exact H7.
        }
        assert (Hfield_exists : exists fdef, nth_error (collect_fields CT (rctype (rt_type o))) f = Some fdef).
        {
          apply Forall2_length in Hwf_fields.
          assert (Hf_dom : f < List.length (fields_map o)) by (apply nth_error_Some; rewrite Hloc_in_fields; discriminate).
          rewrite Hwf_fields in Hf_dom.
          destruct (nth_error (collect_fields CT (rctype (rt_type o))) f) as [fdef|] eqn:Hfdef.
          - exists fdef. reflexivity.
          - exfalso. apply nth_error_None in Hfdef. lia.
        }
        destruct Hfield_exists as [fdef Hfdef].

        assert (Hfield_prop := Forall2_nth_error_prop _ _ _ _ _ _ Hwf_fields Hloc_in_fields Hfdef).
        simpl in Hfield_prop.
        destruct (runtime_getObj h' loc) as [o'|] eqn:Hloc_obj; [trivial | contradiction].
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
            admit.
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
    + (* wellformed class *) exact Hclass.
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
          ** simpl. rewrite update_length. exact Hlen_fields.
          **
            simpl.
            admit.
        -- unfold wf_obj, runtime_getObj.
        rewrite update_diff.
        ** rewrite update_length in Hdom.
          symmetry. exact Hneq.
        ** 
        admit.
        * exfalso.
        discriminate H12.
    + destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]]. exact HrEnvLen.
    + destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]]. exact Hreceiverval.
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
    + admit.
  - (* Case: stmt = New *)
    intros.
    inversion H11; subst.
    unfold wf_r_config in *.
    destruct H10 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    repeat split.
    + (* wellformed class *) exact Hclass.
    + (* wellformed heap *) 
    unfold wf_heap.
    intros ι Hι.
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
      -- (* field count matches *)
        simpl.
        admit.
    * (* ι < dom h (existing object) *)
      assert (ι < dom h) by lia.
      unfold wf_obj.
      rewrite runtime_getObj_last2; auto.
      admit. (* apply Hheap; auto. *)
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
    + 
    destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
    simpl.
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
    + rewrite update_length. rewrite <- Hlen. lia.
    + admit.
  - (* Case: stmt = Call *)
    intros.
    inversion H9; subst.
    unfold wf_r_config in *.
    destruct H8 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    repeat split.
    + (* wellformed class *) exact Hclass.
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
        exact Hiot.
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
  intros. remember OK as ok. induction H3; try discriminate.
  - (* Skip *) inversion H4. intros; subst; rewrite H0 in H4; injection H4; auto.
  - (* Local *) inversion H4; intros; subst; rewrite H0 in H4; injection H4; auto.
  - (* VarAss *) inversion H4; intros; subst; rewrite H0 in H4; injection H4; auto.
  - (* FldWrite *) 
    (* Key case: show contradiction with can_assign for immutable Final/RDA fields *)
    admit.
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

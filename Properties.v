Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation.
Require Import List.
Import ListNotations.
Require Import String.
From RecordUpdate Require Import RecordUpdate.

Lemma collect_methods_exists : forall CT C,
  wf_class_table CT ->
  C < dom CT ->
  exists methods, CollectMethods CT C methods.
Proof.
  intros CT C Hwf_ct Hdom.
  induction C as [C IH] using lt_wf_ind.
  assert (Hexists_class : exists class_def, find_class CT C = Some class_def).
  {
    apply find_class_Some.
    exact Hdom.
  }
  destruct Hexists_class as [class_def Hfind_class].
  assert (Hwf_class : wf_class CT class_def).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  inversion Hwf_class; subst.
  - (* WFObjectDef: no parent *)
    exists (methods (body class_def)).
    eapply CM_Object; eauto.
  - (* WFOtherDef: has parent *)
    assert (Hdom_parent : superC < dom CT).
    {
      unfold wf_class_table in Hwf_ct.
      destruct Hwf_ct as [_ [_ [Hotherclasses Hcname_consistent]]].
      assert (Hcname_eq : cname (signature class_def) = C).
      {
        apply Hcname_consistent.
        exact Hfind_class.
      }
      rewrite Hcname_eq in H2.
      (* Use H2: C > superC *)
      lia.
    }
    (* Apply strong induction hypothesis *)
    assert (IH_parent : exists parent_methods, CollectMethods CT superC parent_methods).
    {
      apply IH.
      (* Need to prove superC < C *)
      unfold wf_class_table in Hwf_ct.
      destruct Hwf_ct as [_ [_ [_ Hcname_consistent]]].
      assert (Hcname_eq : cname (signature class_def) = C).
      {
        apply Hcname_consistent.
        exact Hfind_class.
      }
      rewrite Hcname_eq in H2.
      exact H2.
      exact Hdom_parent.
    }
    destruct IH_parent as [parent_methods Hcollect_parent].
    exists (override parent_methods (methods (body class_def))).
    eapply CM_Inherit; eauto.
Qed.

Lemma override_parent_method_found : forall parent_methods own_methods m mdef,
  gget_method own_methods m = None ->
  gget_method parent_methods m = Some mdef ->
  gget_method (override parent_methods own_methods) m = Some mdef.
Proof.
  intros parent_methods own_methods m mdef Hown Hparent.
  unfold override, gget_method.
  rewrite find_app_none; auto.
  
  (* We need to show find returns Some mdef on the filtered list *)
  induction parent_methods as [|h t IH].
  - (* parent_methods = [] *)
    simpl in Hparent.
    discriminate.
  - (* parent_methods = h :: t *)
    simpl in Hparent |- *.
    destruct (eq_method_name (mname (msignature h)) m) eqn:Heq_h.
    + (* h matches m *)
      injection Hparent as Heq_mdef.
      subst h.
      (* Show mdef passes the filter *)
      destruct (negb (existsb (fun omdef => eq_method_name (mname (msignature mdef)) (mname (msignature omdef))) own_methods)) eqn:Hfilter.
      * (* mdef passes filter *)
        simpl.
        rewrite Heq_h.
        reflexivity.
      * (* mdef doesn't pass filter - contradiction *)
        exfalso.
        rewrite Bool.negb_false_iff in Hfilter.
        apply existsb_exists in Hfilter.
        destruct Hfilter as [omdef [Hin_own Heq_names]].
        assert (Homdef_m : eq_method_name (mname (msignature omdef)) m = true).
        {
          apply Nat.eqb_eq in Heq_h.
          apply Nat.eqb_eq in Heq_names.
          rewrite <- Heq_names.
          apply Nat.eqb_eq.
          exact Heq_h.
        }
        unfold gget_method in Hown.
        assert (Hcontra : exists x, find (fun mdef => eq_method_name (mname (msignature mdef)) m) own_methods = Some x).
        {
          apply find_some_iff.
          exists omdef.
          split; [exact Hin_own | exact Homdef_m].
        }
        destruct Hcontra as [x Hx].
        rewrite Hx in Hown.
        discriminate.
    + (* h doesn't match m *)
      destruct (negb (existsb (fun omdef => eq_method_name (mname (msignature h)) (mname (msignature omdef))) own_methods)) eqn:Hfilter_h.
      * (* h passes filter *)
        simpl.
        rewrite Heq_h.
        apply IH.
        exact Hparent.
      * (* h doesn't pass filter *)
        apply IH.
        exact Hparent.
Qed.

Lemma override_parent_method_in : forall parent_methods own_methods m mdef,
  gget_method (override parent_methods own_methods) m = Some mdef ->
  gget_method own_methods m = None ->
  In mdef parent_methods /\ 
  eq_method_name (mname (msignature mdef)) m = true.
Proof.
  intros parent_methods own_methods m mdef Hoverride Hown.
  unfold override, gget_method in Hoverride.
  unfold gget_method in Hown.
  apply find_some in Hoverride.
  destruct Hoverride as [Hin Heq].
  apply in_app_or in Hin.
  destruct Hin as [Hin_own | Hin_filtered].
  - (* mdef is in own_methods - contradiction *)
    exfalso.
    (* If mdef is in own_methods and matches m, then find should return Some *)
    assert (Hfind_some : exists x, find (fun mdef => eq_method_name (mname (msignature mdef)) m) own_methods = Some x).
    {
      apply find_some_iff.
      exists mdef.
      split; [exact Hin_own | exact Heq].
    }
    destruct Hfind_some as [x Hx].
    rewrite Hx in Hown.
    discriminate.
  - (* mdef is in filtered parent_methods *)
    apply filter_In in Hin_filtered.
    destruct Hin_filtered as [Hin_parent _].
    split; [exact Hin_parent | exact Heq].
Qed.

Lemma gget_method_from_in : forall methods m mdef,
  In mdef methods ->
  eq_method_name (mname (msignature mdef)) m = true ->
  exists mdef', gget_method methods m = Some mdef' /\ 
                eq_method_name (mname (msignature mdef')) m = true.
Proof.
  intros methods m mdef Hin Heq.
  unfold gget_method.
  induction methods as [|h t IH].
  - (* methods = [] *)
    contradiction.
  - (* methods = h :: t *)
    simpl.
    destruct (eq_method_name (mname (msignature h)) m) eqn:Heq_h.
    + (* h matches m *)
      exists h.
      split; [reflexivity | exact Heq_h].
    + (* h doesn't match m *)
      simpl in Hin.
      destruct Hin as [Heq_mdef | Hin_t].
      * (* mdef = h - contradiction *)
        subst h.
        rewrite Heq in Heq_h.
        discriminate.
      * (* mdef in t *)
        apply IH.
        exact Hin_t.
Qed.

Lemma method_body_well_typed : forall CT C cdef mdef,
  wf_class_table CT ->
  C < dom CT ->
  find_class CT C = Some cdef ->
  In mdef (methods (body cdef)) ->
  exists sΓ', stmt_typing CT (mreceiver (msignature mdef) :: mparams (msignature mdef)) 
                           (mbody_stmt (mbody mdef)) 
                           sΓ'.
Proof.
  intros CT C cdef mdef Hwf_ct Hdom HfindC Hlookup.
  assert (Hwf_class : wf_class CT cdef).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  assert (Hcname_eq : cname (signature cdef) = C).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [_ [_ Hcname_consistent]].
    destruct Hcname_consistent as [_ Hcname_eq].
    apply Hcname_eq.
    exact HfindC.
  }
  assert (Hwf_mdef : wf_method CT C mdef).
  {
    eapply method_lookup_wf_class; eauto.
  }
  inversion Hwf_mdef; subst.
  destruct H as [sΓ' [Htyping _]].
  exists sΓ'.
  unfold sΓ, msig in Htyping.
  unfold methodbody, mbodystmt in Htyping.
  exact Htyping.
Qed.


(* Lemma method_lookup_in_wellformed_inherited: forall CT C m mdef,
  wf_class_table CT ->
  C < dom CT ->
  FindMethodWithName CT C m mdef ->
  (exists D ddef, base_subtype CT C D /\ find_class CT D = Some ddef /\ In mdef (methods (body ddef)) /\ wf_method CT D mdef).
Proof.
  intros CT C m mdef Hwf_ct Hdom Hlookup.
  induction C as [C IH] using lt_wf_ind.
  inversion Hlookup; subst.
  inversion H; subst.
  - (* CM_NotFound case *)
    exfalso.
    unfold gget_method in H0.
    discriminate.
  - (* CM_Object case *)
    exists C, def.
    split; [apply base_refl; exact H3 | split; [exact H1 | split]].
    + unfold gget_method in H0.
      apply find_some in H0.
      destruct H0 as [Hin _].
      exact Hin.
    + eapply method_lookup_wf_class; eauto.
      unfold gget_method in H0.
      apply find_some in H0.
      destruct H0 as [Hin _].
      exact Hin.
  - (* CM_Inherit case *)
    destruct (gget_method (methods (body def)) m) as [local_mdef|] eqn:Hlocal.
    + (* Method found locally *)
      assert (Hlocal_eq : local_mdef = mdef).
      {
        assert (Hoverride_local : gget_method (override parent_methods (methods (body def))) m = Some local_mdef).
        {
          apply override_own_method_found.
          exact Hlocal.
        }
        rewrite Hoverride_local in H0.
        injection H0 as Heq.
        exact Heq.
      }
      subst local_mdef.
      exists C, def.
      split; [apply base_refl; exact H3 | split; [exact H1 | split]].
      * unfold gget_method in Hlocal.
        apply find_some in Hlocal.
        destruct Hlocal as [Hin _].
        exact Hin.
      * eapply method_lookup_wf_class; eauto.
        unfold gget_method in Hlocal.
        apply find_some in Hlocal.
        destruct Hlocal as [Hin _].
        exact Hin.
    + (* Method inherited from parent *)
      assert (Hparent_mdef : FindMethodWithName CT parent m mdef).
      {
        apply ML_Found with parent_methods; auto.
        erewrite override_parent_method_preserved in H0; eauto.
      }
      assert (Hparent_lt : parent < C).
      {
        assert (Hwf_class : wf_class CT def).
        {
          unfold wf_class_table in Hwf_ct.
          destruct Hwf_ct as [Hforall_wf _].
          eapply Forall_nth_error; eauto.
        }
        inversion Hwf_class; subst.
        - (* WFObjectDef - contradiction *)
          rewrite H7 in H2.
          discriminate.
        - (* WFOtherDef *)
          assert (Hcname_eq : cname (signature def) = C).
          {
            unfold wf_class_table in Hwf_ct.
            destruct Hwf_ct as [_ [_ [_ Hcname_consistent]]].
            apply Hcname_consistent.
            exact H1.
          }
          rewrite H8 in H2.
          injection H2 as Heq.
          subst superC.
          rewrite Hcname_eq in H10.
          exact H10.
      }
      apply IH in Hparent_mdef; auto.
      destruct Hparent_mdef as [D [ddef [Hsub [Hfind_D [Hin_D Hwf_D]]]]].
      exists D, ddef.
      split; [eapply base_trans; eauto | split; [exact Hfind_D | split; [exact Hin_D | exact Hwf_D]]].
      eapply base_extends; eauto.
      unfold parent_lookup.
      rewrite H1.
      exact H2.
Qed. *)

Lemma method_body_well_typed_dispatch : forall CT C m mdef,
  wf_class_table CT ->
  C < dom CT ->
  FindMethodWithName CT C m mdef ->
  exists sΓ', stmt_typing CT (mreceiver (msignature mdef) :: mparams (msignature mdef)) 
                           (mbody_stmt (mbody mdef)) 
                           sΓ'.
Proof.
  intros CT C m mdef Hwf_ct Hdom Hlookup.
  assert (Hexists_class : exists class_def, find_class CT C = Some class_def).
  {
    apply find_class_Some.
    exact Hdom.
  }
  destruct Hexists_class as [class_def Hfind_class].
  assert (Hwf_class : wf_class CT class_def).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  assert (Hcname_eq : cname (signature class_def) = C).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [_ [_ Hcname_consistent]].
    destruct Hcname_consistent as [_ Hcname_eq].
    apply Hcname_eq.
    exact Hfind_class.
  }

  assert (Hwf_inherited : exists D ddef, base_subtype CT C D /\ find_class CT D = Some ddef /\ In mdef (methods (body ddef)) /\ wf_method CT D mdef).
  {
    eapply method_lookup_in_wellformed_inherited; eauto.
  }
  destruct Hwf_inherited as [D [ddef [Hsub [Hfind_D [Hin_D Hwf_D]]]]].

  (* Extract the statement typing from wf_method *)
  inversion Hwf_D; subst.
  destruct H as [sΓ' [Htyping _]].
  exists sΓ'.
  unfold sΓ, msig in Htyping.
  unfold methodbody, mbodystmt in Htyping.
  exact Htyping.
Qed.

Lemma wf_method_sig_types : forall CT C mdef,
  wf_method CT C mdef ->
  wf_stypeuse CT (sqtype (mreceiver (msignature mdef))) (sctype (mreceiver (msignature mdef))) /\
  Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) (mparams (msignature mdef)).
Proof.
  intros CT C mdef Hwf_method.
  inversion Hwf_method; subst.
  destruct H as [sΓ' [Htyping _]].
  assert (Hwf_env : wf_senv CT sΓ).
  {
    eapply stmt_typing_wf_env; eauto.
  }
  unfold sΓ, msig in Hwf_env.
  inversion Hwf_env; subst.
  split.
  - (* Receiver well-formedness *)
    apply Forall_inv in H1.
    exact H1.
  - (* Parameters well-formedness *)
    apply Forall_inv_tail in H1.
    exact H1.
Qed.

Lemma method_sig_wf_reciever : forall CT C cdef mdef,
  wf_class_table CT ->
  C < dom CT ->
  find_class CT C = Some cdef ->
  In mdef (methods (body cdef)) ->
  wf_stypeuse CT (sqtype (mreceiver (msignature mdef))) (sctype (mreceiver (msignature mdef))).
Proof.
  intros CT C cdef mdef Hwf_ct Hdom HfindC Hlookup.
  assert (Hwf_class : wf_class CT cdef).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  assert (Hcname_eq : cname (signature cdef) = C).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [_ [_ Hcname_consistent]].
    destruct Hcname_consistent as [_ Hcname_eq].
    apply Hcname_eq.
    exact HfindC.
  }
  assert (Hwf_mdef : wf_method CT C mdef).
  {
    eapply method_lookup_wf_class; eauto.
  }

  eapply wf_method_sig_types; eauto.
Qed.

Lemma method_sig_wf_parameters : forall CT C cdef mdef,
  wf_class_table CT ->
  C < dom CT ->
  find_class CT C = Some cdef ->
  In mdef (methods (body cdef)) ->
  Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) (mparams (msignature mdef)).
Proof.
  intros CT C cdef mdef Hwf_ct Hdom HfindC Hlookup.
  assert (Hwf_class : wf_class CT cdef).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  assert (Hcname_eq : cname (signature cdef) = C).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [_ [_ Hcname_consistent]].
    destruct Hcname_consistent as [_ Hcname_eq].
    apply Hcname_eq.
    exact HfindC.
  }
  assert (Hwf_mdef : wf_method CT C mdef).
  {
    eapply method_lookup_wf_class; eauto.
  }

  eapply wf_method_sig_types; eauto.
Qed.

Lemma method_sig_wf_receiver_dispatch : forall CT C m mdef,
  wf_class_table CT ->
  C < dom CT ->
  FindMethodWithName CT C m mdef ->
  wf_stypeuse CT (sqtype (mreceiver (msignature mdef))) (sctype (mreceiver (msignature mdef))).
Proof.
  intros CT C m mdef Hwf_ct Hdom Hlookup.
  assert (Hwf_inherited : exists D ddef, base_subtype CT C D /\ find_class CT D = Some ddef /\ In mdef (methods (body ddef)) /\ wf_method CT D mdef).
  {
    eapply method_lookup_in_wellformed_inherited; eauto.
  }
  destruct Hwf_inherited as [D [ddef [Hsub [Hfind_D [Hin_D Hwf_D]]]]].
  eapply wf_method_sig_types; eauto.
Qed.

Lemma method_sig_wf_parameters_dispatch : forall CT C m mdef,
  wf_class_table CT ->
  C < dom CT ->
  FindMethodWithName CT C m mdef ->
  Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) (mparams (msignature mdef)).
Proof.
  intros CT C m mdef Hwf_ct Hdom Hlookup.
  assert (Hwf_inherited : exists D ddef, base_subtype CT C D /\ find_class CT D = Some ddef /\ In mdef (methods (body ddef)) /\ wf_method CT D mdef).
  {
    eapply method_lookup_in_wellformed_inherited; eauto.
  }
  destruct Hwf_inherited as [D [ddef [Hsub [Hfind_D [Hin_D Hwf_D]]]]].
  eapply wf_method_sig_types; eauto.
Qed.

Lemma override_own_method_found : forall parent_methods own_methods m mdefown,
  gget_method own_methods m = Some mdefown ->
  gget_method (override parent_methods own_methods) m = Some mdefown.
Proof.
  intros parent_methods own_methods m mdefown Hown.
  unfold override.
  unfold gget_method.
  apply find_app.
  exact Hown.
Qed.

Lemma In_gget_method_unique : forall method_list mdef m,
  NoDup (map (fun mdef => mname (msignature mdef)) method_list) ->
  In mdef method_list ->
  mname (msignature mdef) = m ->
  gget_method method_list m = Some mdef.
Proof.
  intros method_list mdef m Hnodup Hin Hname.
  unfold gget_method.
  induction method_list as [|hd tl IH].
  - contradiction Hin.
  - simpl in Hin.
    destruct Hin as [Heq | Hin_tl].
    + subst hd.
      simpl.
      unfold eq_method_name.
      rewrite Hname.
      rewrite Nat.eqb_refl.
      reflexivity.
    + simpl.
      unfold eq_method_name.
      destruct (Nat.eqb (mname (msignature hd)) m) eqn:Heqb.
      * (* Contradiction with NoDup *)
        exfalso.
        apply Nat.eqb_eq in Heqb.
        simpl in Hnodup.
        inversion Hnodup; subst.
        apply H1.
        apply in_map_iff.
        exists mdef.
        split; [symmetry; exact Heqb | exact Hin_tl].
      * (* Use IH *)
        apply IH.
        -- simpl in Hnodup.
           inversion Hnodup; auto.
        -- exact Hin_tl.
Qed.

Lemma In_gget_method_unique_class : forall CT C cdef mdef m,
  wf_class_table CT ->
  find_class CT C = Some cdef ->
  In mdef (methods (body cdef)) ->
  mname (msignature mdef) = m ->
  gget_method (methods (body cdef)) m = Some mdef.
Proof.
  intros CT C cdef mdef m Hwf_ct Hfind Hin Hname.
  assert (Hwf_class : wf_class CT cdef).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  apply In_gget_method_unique.
  - (* Extract NoDup from wf_class *)
    inversion Hwf_class; subst.
    + (* WFObjectDef case *)
      rewrite H2.
      simpl.
      constructor.
    + (* WFOtherDef case *)
      destruct H3 as [_ [_ [Hnodup _]]].
      unfold bod in Hnodup.
      exact Hnodup.
  - exact Hin.
  - exact Hname.
Qed.

Lemma constructor_params_field_count : forall CT C ctor csig fields,
  wf_class_table CT ->
  C < dom CT ->
  constructor_def_lookup CT C = Some ctor ->
  csig = csignature ctor ->
  CollectFields CT C fields ->
  List.length (sparams csig) + List.length (cparams csig) = List.length fields.
Proof.
  intros CT C ctor csig fields Hwf_ct Hdom Hctor_lookup Hcsig Hcollect.
  subst csig.
  
  (* Get the class definition *)
  assert (Hclass_exists : exists cdef, find_class CT C = Some cdef).
  {
    apply nth_error_Some_exists.
    exact Hdom.
  }
  destruct Hclass_exists as [cdef Hfind_class].
  
  (* Extract well-formedness of the class *)
  assert (Hwf_class : wf_class CT cdef).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  
  (* Extract constructor well-formedness *)
  assert (Hctor_eq : constructor (body cdef) = ctor).
  {
    unfold constructor_def_lookup in Hctor_lookup.
    rewrite Hfind_class in Hctor_lookup.
    injection Hctor_lookup as Hctor_eq.
    exact Hctor_eq.
  }
  
  (* Use constructor well-formedness from wf_class *)
  inversion Hwf_class; subst.
  - (* Object class case: C = 0 *)
    inversion H4; subst.
    fold sig0.
    rewrite H9.
    rewrite H10.
    inversion Hcollect.
    easy.
    easy.
    unfold parent_lookup in H3.
    assert (HfindC: cdef = def). {
      eapply find_class_consistent; eauto.
    }
    exfalso.
    (* subst def. *)
    unfold parent_lookup in H3.
    rewrite HfindC in H3.
    subst cdef.
    apply find_class_cname_consistent in Hfind_class.
    rewrite Hfind_class in H3.
    rewrite H13 in H3.
    rewrite H14 in H3.
    discriminate H3. exact Hwf_ct.
    unfold parent_lookup in H3.
    exfalso.
    have Hfind_class_copy := Hfind_class.
    apply find_class_cname_consistent in Hfind_class.
    rewrite Hfind_class in H3.
    rewrite Hfind_class_copy in H3.
    rewrite H in H3.
    discriminate.
    exact Hwf_ct.
  - (* Regular class case *)
    destruct H3 as [Hwf_ctor [Hnodup_methods [Hforall_methods Hforall_fields]]].
    inversion Hwf_ctor; subst.
    unfold parent_lookup in H1.
    have Hfind_class_copy := Hfind_class.
    apply find_class_cname_consistent in Hfind_class.
    assert (C0 = C). {
      unfold C0.
      unfold sig.
      exact Hfind_class.
    }
    subst C0.
    rewrite H9 in H1.
    rewrite Hfind_class_copy in H1.
    rewrite H0 in H1.
    discriminate.
    exact Hwf_ct.
    fold bod.
    fold sig1.
    fold stypes.
    
    admit.
Admitted.

Lemma eval_stmt_preserves_heap_domain_simple : forall CT rΓ h stmt rΓ' h',
  eval_stmt OK CT rΓ h stmt OK rΓ' h' ->
  dom h <= dom h'.
Proof.
  intros CT rΓ h stmt rΓ' h' Heval.
  remember OK as ok.
  induction Heval; try reflexivity; try discriminate.
  - (* FldWrite: h' = update_field h lx f v2 *)
    rewrite H3.
    unfold update_field.
    rewrite H0.
    rewrite update_length.
    reflexivity.
  - (* New: h' = h ++ [new_obj] *)
    rewrite H5.
    rewrite length_app.
    simpl.
    lia.
  - (* Call: use IH *)
    apply IHHeval. reflexivity.
  - (* Seq: transitivity *)
    apply Nat.le_trans with (dom h').
    + apply IHHeval1. reflexivity.
    + apply IHHeval2. reflexivity.
Qed.

Lemma runtime_getObj_app_left : forall h h_ext loc obj,
  loc < dom h ->
  runtime_getObj h loc = Some obj ->
  runtime_getObj (h ++ h_ext) loc = Some obj.
Proof.
  intros h h_ext loc obj Hloc_dom Hobj.
  unfold runtime_getObj in *.
  rewrite nth_error_app1.
  - exact Hloc_dom.
  - exact Hobj.
Qed.

(* Not just length, there is no statment can do strong update. *)
Lemma eval_stmt_preserves_r_type : 
  forall CT rΓ h stmt rΓ' h' loc rqt,
    eval_stmt OK CT rΓ h stmt OK rΓ' h' ->
    r_type h loc = Some rqt ->
    loc < dom h ->
    r_type h' loc = Some rqt.
Proof.
  intros CT rΓ h stmt rΓ' h' loc rqt Heval Hrtype Hloc_dom.
  remember OK as ok.
  induction Heval; try discriminate; try (subst; exact Hrtype).
  - (* FldWrite: only fields change, not type *)
    subst h'.
    unfold r_type in Hrtype |- *.
    unfold update_field.
    destruct (runtime_getObj h lx) as [ox|] eqn:Hlx; [|exact Hrtype].
    destruct (Nat.eq_dec loc lx) as [Heq|Hneq].
    + (* loc = lx: type preserved *)
      subst loc.
      rewrite runtime_getObj_update_same.
      * apply runtime_getObj_dom in Hlx. exact Hlx.
      * simpl. unfold r_type in Hrtype.
        rewrite Hlx in Hrtype. exact Hrtype.
    + (* loc ≠ lx: unchanged *)
      rewrite runtime_getObj_update_diff.
      * symmetry. exact Hneq.
      * exact Hrtype.
  - (* New: existing objects unchanged *)
    subst h'.
    unfold r_type in Hrtype |- *.
    destruct (runtime_getObj h loc) as [obj_loc|] eqn:Hobj_loc; [|discriminate].
    injection Hrtype as Hrtype_eq.
    subst rqt.
    erewrite runtime_getObj_app_left; eauto.
  - (* Call: use IH *)
    eapply IHHeval; eauto.
  - (* Seq: transitivity *)
    assert (Hloc_dom' : loc < dom h').
    {
      have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓ h s1 rΓ' h' Heval1.
      lia.
    }
    assert (Hrtype' : r_type h' loc = Some rqt).
    {
      eapply IHHeval1; eauto.
    }
    eapply IHHeval2; eauto.
Qed.

Lemma eval_stmt_preserves_r_muttype : 
  forall CT rΓ h stmt rΓ' h' loc q,
    eval_stmt OK CT rΓ h stmt OK rΓ' h' ->
    r_muttype h loc = Some q ->
    loc < dom h ->
    r_muttype h' loc = Some q.
Proof.
  intros CT rΓ h stmt rΓ' h' loc q Heval Hmut Hloc_dom.
  remember OK as ok.
  induction Heval; try discriminate; try (subst; exact Hmut).
  - (* FldWrite: only fields change, not mutability type *)
    subst h'.
    unfold update_field.
    destruct (runtime_getObj h lx) as [ox|] eqn:Hlx; [|exact Hmut].
    destruct (Nat.eq_dec loc lx) as [Heq|Hneq].
    + (* loc = lx: mutability type preserved *)
      subst loc.
      unfold r_muttype in Hmut |- *.
      unfold update_field.
      injection H0 as H0_eq.
      subst ox.
      rewrite runtime_getObj_update_same.
      * exact Hloc_dom.
      * simpl. rewrite Hlx in Hmut. exact Hmut.
    + (* loc ≠ lx: unchanged *)
      unfold r_muttype in Hmut |- *.
      unfold update_field.
      injection H0 as H0_eq.
      subst ox.
      rewrite runtime_getObj_update_diff.
      * symmetry. exact Hneq.
      * exact Hmut.
  - (* New: existing objects unchanged *)
    subst h'.
    destruct (runtime_getObj h loc) as [obj_loc|] eqn:Hobj_loc.
    2:{
      unfold r_muttype in Hmut.
      rewrite Hobj_loc in Hmut.
        discriminate Hmut.
    }
    unfold r_muttype in Hmut |- *.
    rewrite Hobj_loc in Hmut.
    injection Hmut as Hmut_eq.
    subst q.
    erewrite runtime_getObj_app_left; eauto.
  - (* Call: use IH *)
    eapply IHHeval; eauto.
  - (* Seq: transitivity *)
    assert (Hloc_dom' : loc < dom h').
    {
      have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓ h s1 rΓ' h' Heval1.
      lia.
    }
    assert (Hmut' : r_muttype h' loc = Some q).
    {
      eapply IHHeval1; eauto.
    }
    eapply IHHeval2; eauto.
Qed.

Lemma wf_r_typable_env_independent : forall CT rΓ1 rΓ2 h loc qt,
  get_this_var_mapping (vars rΓ1) = get_this_var_mapping (vars rΓ2) ->
  wf_r_typable CT rΓ1 h loc qt ->
  wf_r_typable CT rΓ2 h loc qt.
Proof.
  intros CT rΓ1 rΓ2 h loc qt Hsame_this Hwf.
  unfold wf_r_typable in *.
  destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
  rewrite <- Hsame_this.
  destruct (get_this_var_mapping (vars rΓ1)) as [ι'|] eqn:Hthis; [|contradiction].
  destruct (r_muttype h ι') as [q|] eqn:Hmut; [|contradiction].
  exact Hwf.
Qed.

Lemma r_basetype_in_dom : forall CT h loc cy,
  wf_heap CT h ->
  r_basetype h loc = Some cy ->
  cy < dom CT.
Proof.
  intros CT h loc cy Hwf_heap Hr_basetype.
  unfold r_basetype in Hr_basetype.
  destruct (runtime_getObj h loc) as [obj|] eqn:Hobj; [|discriminate].
  injection Hr_basetype as Heq.
  subst cy.
  destruct obj as [rt_obj fields_obj].
  destruct rt_obj as [rq_obj rc_obj].
  simpl.
  unfold wf_heap in Hwf_heap.
  assert (Hloc_dom : loc < dom h) by (apply runtime_getObj_dom in Hobj; exact Hobj).
  specialize (Hwf_heap loc Hloc_dom).
  unfold wf_obj in Hwf_heap.
  rewrite Hobj in Hwf_heap.
  destruct Hwf_heap as [Hwf_rtypeuse _].
  unfold wf_rtypeuse in Hwf_rtypeuse.
  simpl in Hwf_rtypeuse.
  destruct (bound CT rc_obj) as [qc|] eqn:Hbound.
  - exact Hwf_rtypeuse.
  - contradiction.
Qed.

(* ------------------------------------------------------------- *)
(* Soundness properties for PICO *)
Theorem preservation_pico :
  forall CT sΓ rΓ h stmt rΓ' h' sΓ',
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ stmt sΓ' -> 
    eval_stmt OK CT rΓ h stmt OK rΓ' h' -> 
    wf_r_config CT sΓ' rΓ' h'.
Proof.
  intros CT sΓ rΓ h stmt rΓ' h' sΓ' Hwf Htyping Heval.
  generalize dependent sΓ.
  generalize dependent sΓ'.
  remember OK as ok.
  induction Heval; intros; try (discriminate; inversion Htyping; subst; exact Hwf).
  6: 
  {
    inversion Htyping; subst.
    destruct H1 as [mdeflookup getmbody].
    remember (msignature mdef) as msig.
    have mdeflookupcopy := mdeflookup.
    apply method_body_well_typed_dispatch in mdeflookup; auto.
    destruct mdeflookup as [sΓmethodend Htyping_method].
    remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit.
    remember {| vars := Iot ly :: vals |} as rΓmethodinit.
    remember (rΓ <| vars := update x retval (vars rΓ) |>) as rΓ'''.
    assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
    { (* Method inner config wellformed.*)
      unfold wf_r_config in Hwf.
      unfold wf_r_config.
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
      rewrite HeqrΓmethodinit.
      simpl.
      lia.
      unfold wf_renv in Hrenv.
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      exists ly.
      split.
      rewrite HeqrΓmethodinit.
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
      rewrite HeqrΓmethodinit.
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
      subst.

      (* Receiver type is well-formed *)
      eapply method_sig_wf_receiver_dispatch; eauto.
      unfold r_basetype in H0.
      destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
      injection H0 as H2_eq.
      subst cy.
      destruct obj as [rt_obj fields_obj].
      destruct rt_obj as [rq_obj rc_obj].
      simpl.
      unfold wf_heap in Hheap.
      assert (Hly_dom : ly < dom h) by (apply runtime_getObj_dom in Hobjy; exact Hobjy).
      specialize (Hheap ly Hly_dom).
      unfold wf_obj in Hheap.
      rewrite Hobjy in Hheap.
      destruct Hheap as [Hwf_rtypeuse _].
      unfold wf_rtypeuse in Hwf_rtypeuse.
      simpl in Hwf_rtypeuse.
      destruct (bound CT rc_obj) as [class_def|] eqn:Hbound.
      exact Hwf_rtypeuse.
      contradiction.

      eapply method_sig_wf_parameters_dispatch; eauto.
      unfold r_basetype in H0.
      destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
      injection H0 as H2_eq.
      subst cy.
      destruct obj as [rt_obj fields_obj].
      destruct rt_obj as [rq_obj rc_obj].
      simpl.
      unfold wf_heap in Hheap.
      assert (Hly_dom : ly < dom h) by (apply runtime_getObj_dom in Hobjy; exact Hobjy).
      specialize (Hheap ly Hly_dom).
      unfold wf_obj in Hheap.
      rewrite Hobjy in Hheap.
      destruct Hheap as [Hwf_rtypeuse _].
      unfold wf_rtypeuse in Hwf_rtypeuse.
      simpl in Hwf_rtypeuse.
      destruct (bound CT rc_obj) as [class_def|] eqn:Hbound.
      exact Hwf_rtypeuse.
      contradiction.

      apply static_getType_list_preserves_length in H15.
      apply runtime_lookup_list_preserves_length in H4.
      rewrite HeqsΓmethodinit.
      rewrite HeqrΓmethodinit.
      simpl.
      f_equal.
      apply Forall2_length in H23.
      rewrite <- Heqmsig.
      assert (Hsubtype : base_subtype CT cy (sctype Ty)).
      {
        assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in H14.
          exact H14.
        }

        (* Apply correspondence to get wf_r_typable *)
        specialize (Hcorr y Hy_dom Ty H14).
        rewrite H in Hcorr.

        (* Extract subtyping from wf_r_typable *)
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in H0.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection H0 as Hcy_eq.
        subst cy.
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].


        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot _]].
        unfold get_this_var_mapping.
        unfold gget in Hget_iot.
        destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].
        injection Hget_iot as Hv0_eq.
        subst v0.

        unfold r_type in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        destruct (r_muttype h iot) as [q|] eqn:Hmut; [|contradiction].
        destruct Hcorr as [Hsubtype _].
        exact Hsubtype.
      }
      rewrite <- H4 in H15.
      rewrite <- H15.
      rewrite H23.
      rewrite Heqmsig.
      eapply wf_method_override_same_param_length_general; eauto.
      eapply r_basetype_in_dom ; eauto.
      apply base_subtype_CD in Hsubtype.
      apply r_basetype_in_dom with (CT:=CT) in H0; auto. 
      lia.
      exact Hclasstable.
      have mdeflookupcopyagain := mdeflookupcopy.
      apply find_method_with_name_consistent in mdeflookupcopy; eauto.
      rewrite mdeflookupcopy.
      exact mdeflookupcopyagain.
      apply find_method_with_name_consistent in mdeflookupcopy; eauto. 
      rewrite mdeflookupcopy.
      exact H16.

      intros i Hi sqt Hnth.
      rewrite HeqsΓmethodinit in Hnth, Hi.
      rewrite HeqrΓmethodinit.
      simpl in *.
      destruct i as [|i'].
      (* Reciever *)
      simpl in Hnth.
      injection Hnth as Hsqt_eq.
      subst sqt.
      simpl.
      (* Need to prove wf_r_typable CT rΓmethodinit h ly (mreceiver (msignature mdef)) *)
      unfold wf_r_typable.
      unfold r_type.
      destruct (runtime_getObj h ly) as [obj|] eqn:Hobj_ly.
      2:{
        unfold r_basetype in H0.
        rewrite Hobj_ly in H0.
        discriminate.
      }
      (* Get the runtime type *)
      simpl.
      destruct (r_muttype h ly) as [qy|] eqn:Hq_ly.
      2:{
        unfold r_muttype in Hq_ly.
        rewrite Hobj_ly in Hq_ly.
        discriminate.
      }
      split.

      admit.
      admit.
      admit.
    }
    assert (wf_r_config CT sΓmethodend rΓ'' h'). 
    {
      eapply IHHeval with (sΓ := sΓmethodinit) (sΓ' := sΓmethodend); eauto.
      rewrite <- getmbody in Htyping_method.
      exact Htyping_method.
    }
    { (* Method call resulting config is wellformed *)
      have H1copy := H1.
      unfold wf_r_config in H1.
      unfold wf_r_config.
      unfold wf_r_config in Hwf.
      destruct Hwf as [_ [Hheapinit [Hrenvinit [Hsenvinit [Hleninit Hcorrinit]]]]].
      unfold wf_renv in Hrenvinit.
      destruct Hrenvinit as [HrEnvLen [Hreceiver Hrenvval]].
      (* destruct Hreceiver as [Hreceiverval Hreceivervaldom]. *)
      destruct H1 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
      destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
      repeat split.
      exact Hclass.
      exact Hobj.
      exact Hotherclasses.
      apply Hcname_consistent.
      apply Hcname_consistent.
      exact Hheap.
      rewrite HeqrΓ'''.
      simpl.
      rewrite update_length.
      simpl.
      lia.
      destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
      exists iot.
      split.
      rewrite HeqrΓ'''.
      simpl.
      unfold gget in *.
      destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
      discriminate Hget_iot.
      injection Hget_iot as Hv0_eq.
      subst v0.
      unfold update.
      destruct x as [|x'].
      easy.
      simpl.
      reflexivity.

      rewrite <- getmbody in Htyping_method.
      have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓmethodinit h (mbody_stmt mbody) rΓ'' h' Heval.
      lia.

      (* Outter runtime env is wellformed*)
      rewrite HeqrΓ'''.
      simpl.
      eapply Forall_update; eauto.
      eapply Forall_impl; [|exact Hrenvval].
      intros v Hv.
      destruct v as [|loc]; [trivial|].
      destruct (runtime_getObj h loc) as [obj|] eqn:Hobjloc; [|contradiction].
      rewrite <- getmbody in Htyping_method.
      have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓmethodinit h (mbody_stmt mbody) rΓ'' h' Heval.
      assert (Hloc_dom : loc < dom h) by (apply runtime_getObj_dom in Hobjloc; exact Hobjloc).
      assert (Hloc_dom' : loc < dom h') by lia.
      destruct (runtime_getObj h' loc) as [obj'|] eqn:Hobj'.
      trivial.
      exfalso. apply runtime_getObj_not_dom in Hobj'. lia.
      unfold runtime_getVal in H6.
      destruct retval as [|loc]; [trivial|].
      unfold wf_renv in Hrenv.
      destruct Hrenv as [_ [_ Hrenv_wf]].
      eapply Forall_nth_error in Hrenv_wf; eauto.
      simpl in Hrenv_wf.
      destruct (runtime_getObj h' loc) as [obj|] eqn:Hobjloc; [trivial|].
      contradiction.
      apply static_getType_dom in H13.
      rewrite Hleninit in H13.
      exact H13.

      rewrite Hleninit.
      exact HrEnvLen.
      unfold wf_senv in Hsenvinit.
      destruct Hsenvinit as [Hsenvpdom Hsenvptypeuse].
      exact Hsenvptypeuse.

      rewrite Hleninit.
      rewrite HeqrΓ'''.
      simpl.
      rewrite update_length.
      easy.

      intros i Hi sqt Hnth.
      destruct (Nat.eq_dec i x) as [Heq | Hneq].
      - (* Case: i = x (updated variable) *)
        subst i.
        rewrite HeqrΓ'''.
        simpl.
        unfold runtime_getVal.
        rewrite update_same.
        + apply static_getType_dom in H13.
          rewrite Hleninit in H13.
          exact H13.
        + (* Show wf_r_typable for retval *)
          assert (Hnth_x : nth_error sΓ' x = Some Tx).
          {
            unfold static_getType in H13.
            exact H13.
          }
          rewrite Hnth_x in Hnth.
          injection Hnth as Hsqt_eq.
          subst sqt.
          (* Use the fact that retval is well-typed from method return *)
          unfold runtime_getVal in H6.
          destruct retval as [|loc]; [trivial|].
          assert (Hret_dom : mreturn mbody < dom (vars rΓ'')).
          {
            apply nth_error_Some.
            rewrite H6.
            discriminate.
          }
          rewrite <- Hlen in Hret_dom.
          specialize (Hcorr (mreturn mbody) Hret_dom (mret (msignature mdef0))).
          assert (Hret_type : exists type_val_ret, nth_error sΓmethodend (mreturn mbody) = type_val_ret).
          {
            admit.
          }
          (* specialize (Hcorr Hret_type).
          unfold runtime_getVal in Hcorr.
          rewrite H6 in Hcorr. *)
          unfold wf_r_typable in *.
          (* retval comes from method execution, so it's well-typed *)
          admit.
      - (* Case: i ≠ x (unchanged variable) *)
        rewrite HeqrΓ'''.
        simpl.
        unfold runtime_getVal.
        rewrite update_diff; [symmetry; exact Hneq|].
        specialize (Hcorrinit i Hi sqt Hnth).
        unfold runtime_getVal in Hcorrinit.
        destruct (nth_error (vars rΓ) i) as [v|] eqn:Hgetval; [|exact Hcorrinit].
        destruct v as [|loc]; [trivial|].
        (* Need to show wf_r_typable is preserved when changing runtime environment and heap *)
        unfold wf_r_typable in Hcorrinit |- *.
        destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
        destruct (get_this_var_mapping (vars rΓ)) as [ι'|] eqn:Hthis; [|contradiction].
        destruct (r_muttype h ι') as [q|] eqn:Hmut; [|contradiction].
        assert (Hrtype_preserved : r_type h' loc = Some rqt).
        {
          eapply eval_stmt_preserves_r_type; eauto.
          unfold r_type in Hrtype.
          destruct (runtime_getObj h loc) as [obj|] eqn:Hobjloc; [|discriminate].
          apply runtime_getObj_dom in Hobjloc.
          exact Hobjloc.
        }
        assert (Hthis_preserved : get_this_var_mapping (update x retval (vars rΓ)) = Some ι').
        {
          unfold get_this_var_mapping in Hthis |- *.
          destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].
          simpl in Hthis |- *.
          unfold update.
          destruct x as [|x'].
          contradiction Hneq.
          easy.
          simpl.
          exact Hthis.
        }
        assert (Hmut_preserved : r_muttype h' ι' = Some q).
        {
          eapply eval_stmt_preserves_r_muttype; eauto.
          unfold r_muttype in Hmut.
          destruct (runtime_getObj h ι') as [obj|] eqn:Hobjl; [|discriminate].
          apply runtime_getObj_dom in Hobjl.
          exact Hobjl.
        }
        rewrite Hrtype_preserved.
        rewrite Hthis_preserved.
        rewrite Hmut_preserved.
        exact Hcorrinit.
    }
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hwf_classtable _].
    exact Hwf_classtable.
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hclass [Hheap _]].
    unfold wf_heap in Hheap.
    unfold r_basetype in H0.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobj; [|discriminate].
    injection H0 as Hcy_eq.
    subst cy.
    assert (Hly_dom : ly < dom h) by (apply runtime_getObj_dom in Hobj; exact Hobj).
    specialize (Hheap ly Hly_dom).
    unfold wf_obj in Hheap.
    rewrite Hobj in Hheap.
    destruct Hheap as [Hwf_rtypeuse _].
    unfold wf_rtypeuse in Hwf_rtypeuse.
    destruct (bound CT (rctype (rt_type obj))) as [class_def|] eqn:Hbound.
    - exact Hwf_rtypeuse.
    - contradiction.
  }
  - (* Case: stmt = Skip *)
    intros.
    inversion Htyping; subst.
    exact Hwf.
  - (* Case: stmt = Local *)
    intros.
    inversion Htyping; subst.
    unfold wf_r_config in *.
    destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
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
      *
        constructor.
        -- exact H3. (* assuming H is the wellformedness of T *)
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
    inversion Htyping; subst.
    unfold wf_r_config in *.
    destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
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
      -- inversion H0; subst.
        (* assert (Hloc_in_vars : exists i, nth_error (vars rΓ) i = Some (Iot loc)). *)
        ++ 
        assert (Hx0_bound : x0 < dom (vars rΓ)).
        {
          apply runtime_getVal_dom in H1.
          exact H1.
        }
        assert (Hloc_wf : match runtime_getObj h loc with Some _ => True | None => False end).
        {
          unfold runtime_getVal in H1.
          assert (Hnth_loc : nth_error (vars rΓ) x0 = Some (Iot loc)) by exact H1.
          eapply Forall_nth_error in Hallvals; eauto.
          simpl in Hallvals.
          exact Hallvals.
        }
        exact Hloc_wf.
        ++ 
        assert (Hv_bound : v < dom h).
        {
          apply runtime_getVal_dom in H1.
          unfold runtime_getVal in H1.
          apply runtime_getObj_dom in H2.
          exact H2.
        }
        specialize (Hheap v Hv_bound).
        unfold wf_obj in Hheap.
        rewrite H2 in Hheap.
        destruct Hheap as [_ [field_defs [Hcollect [Hlen_eq Hforall2]]]].
        assert (Hf_bound : f < List.length (fields_map o)).
        {
          apply nth_error_Some.
          unfold getVal in H6.
          rewrite H6.
          discriminate.
        }
        rewrite Hlen_eq in Hf_bound.
        assert (Hfield_def : exists fdef, nth_error field_defs f = Some fdef).
        {
          apply nth_error_Some_exists.
          exact Hf_bound.
        }
        destruct Hfield_def as [fdef Hfdef].
        unfold getVal in H6.
        eapply Forall2_nth_error in Hforall2; eauto.
        simpl in Hforall2.
        destruct (runtime_getObj h loc) as [obj|] eqn:Hloc_obj.
        --- (* Case: runtime_getObj h loc = Some obj *)
          trivial.
        --- (* Case: runtime_getObj h loc = None *)
          contradiction Hforall2.
    * apply runtime_getVal_dom in H.
      exact H.
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
        (* assert (Hsubtype: qualified_type_subtype CT Te Tx) by exact H3.
        assert (Hexpr_type: expr_has_type CT sΓ e Te) by exact H0. *)
        rewrite <- Hlen; exact Hi.
        destruct v2 as [|loc].
        -- (* Case: v2 = Null_a *)
          trivial.
        -- (* Case: v2 = Iot loc *)
          (* Use subtyping to convert from T to sqt *)
          assert (Hsubtype_preserved : wf_r_typable CT (rΓ <| vars := update x (Iot loc) (vars rΓ) |>) h loc sqt).
          {
            assert (Hsqt_eq : sqt = Tx).
          {
            unfold static_getType in H8.
            rewrite H8 in Hnth.
            injection Hnth as Hsqt_eq.
            symmetry. exact Hsqt_eq.
          }
          subst sqt.
          assert (H_loc_Te : wf_r_typable CT rΓ h loc Te).
          {
            (* Apply expression evaluation preservation lemma *)
            apply (expr_eval_preservation CT sΓ' rΓ h e (Iot loc) rΓ h Te).
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
            - exact H4.
            - exact H0.
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
                + easy.
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
                easy.
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
          - apply senv_var_domain with (sΓ:=sΓ') (i:=x). exact H3. exact Hnth.
          - 
          unfold wf_r_typable in H_loc_Te |- *.
          destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
          destruct (get_this_var_mapping (vars rΓ)) as [ι0|] eqn:Hthis_orig; [|contradiction].
          destruct (r_muttype h ι0) as [q|] eqn:Hmut; [|contradiction].
          assert (Hthis_preserved : get_this_var_mapping (vars (rΓ <| vars := update x (Iot loc) (vars rΓ) |>)) = Some ι0).
          {
            simpl.
            unfold get_this_var_mapping in Hthis_orig |- *.
            destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
            - discriminate Hthis_orig.
            - destruct x as [|x'].
              + easy.
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
                destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
                destruct (get_this_var_mapping (vars rΓ)) as [ι'|] eqn:Hthis; [|contradiction].
                destruct (r_muttype h ι') as [q|] eqn:Hmut; [|contradiction].
                assert (Hthis_preserved : get_this_var_mapping (update x v2 (vars rΓ)) = Some ι').
                {
                  unfold get_this_var_mapping in *.
                  destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
                  - discriminate Hthis.
                  - destruct x as [|x'].
                    + 
                    simpl.
                    destruct v2 as [|loc2].
                    -- (* Case: v2 = Null_a *)
                      exfalso.
                      contradiction H5.
                      reflexivity.
                    -- (* Case: v2 = Iot loc2 *)
                      simpl.
                      destruct v0 as [|loc0].
                      ++ (* Case: v0 = Null_a *)
                        discriminate Hthis.
                      ++ (* Case: v0 = Iot loc0 *)
                        easy.
                    + simpl. exact Hthis.
                }
                rewrite Hthis_preserved.
                rewrite Hmut.
                exact Hcorr_orig.
            + contradiction.
        }
  - (* Case: stmt = FldWrite *)
    intros.
    inversion Htyping; subst.
    unfold wf_r_config in *.
    destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
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
        (* injection H12 as Ho_eq. *)
        (* subst o_new. *)
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
            +++ 
            {
              apply Forall2_update.
              eapply Forall2_impl; [|exact Hforall2].
              intros v fdef Hv_fdef.
              destruct v as [|loc]; [trivial|].
              destruct (runtime_getObj h loc) as [obj_at_loc|] eqn:Hobj_at_loc; [|contradiction Hv_fdef].
              destruct Hv_fdef as [rqt [Hrtype Hsubtype]].
              destruct (Nat.eq_dec loc lx) as [Heq_loc | Hneq_loc].
              (* Case: loc = lx *)
                subst loc.
                unfold update_field.
                simpl.
                rewrite update_same.
                apply runtime_getObj_dom in Hobj_at_loc.
                exact Hobj_at_loc.
                exists rqt.
                split.
              unfold r_type.
                simpl.
                rewrite runtime_getObj_update_same.
                simpl.
                apply runtime_getObj_dom in Hobj_at_loc.
                exact Hobj_at_loc.
                simpl.
                unfold r_type in Hrtype.
                rewrite Hobj_at_loc in Hrtype.
                injection Hrtype as Hrqt_eq.
                rewrite Hobj in Hobj_at_loc.
                injection Hobj_at_loc as Heq_objs.
                subst obj_at_loc.
                rewrite Hrqt_eq.
                reflexivity.
              exact Hsubtype.

              (* Case: loc ≠ lx *)
              rewrite update_diff; [symmetry; exact Hneq_loc |].
              unfold runtime_getObj in Hobj_at_loc.
              rewrite Hobj_at_loc.
              exists rqt.
              split.
              unfold r_type.
                rewrite runtime_getObj_update_diff; [symmetry; exact Hneq_loc|].
                unfold r_type in Hrtype.
                exact Hrtype.
              exact Hsubtype.
              assert (Hf_valid : f < dom (fields_map o_new)).
              {
                injection H0 as Ho_eq. subst o_new.
                apply getVal_dom in H1. exact H1.
              }
              rewrite <- Hlen_eq. exact Hf_valid.

              intros b Hnth_b.
              destruct v2 as [|loc2]; [trivial|].

              assert (Hy_dom : y < dom sΓ').
              {
                apply static_getType_dom in H9. exact H9.
              }
              specialize (Hcorr y Hy_dom Ty H9).
              destruct (runtime_getVal rΓ y) as [loc_y|] eqn:Hy_val; [|contradiction].
              injection H2 as Hloc2_eq.
              subst loc_y.
              unfold update_field.
              destruct (runtime_getObj h lx) as [o_lx|] eqn:Hobj_lx.
              destruct (Nat.eq_dec loc2 lx) as [Heq_loc2_lx | Hneq_loc2_lx].
                (* Case: loc2 = lx *)
                subst loc2.
                unfold runtime_getObj.
                rewrite update_same; [exact Hdom|].
                unfold wf_r_typable in Hcorr.
                destruct (r_type h lx) as [rqt_x|] eqn:Hrtype_x; [|contradiction Hcorr].
                destruct (get_this_var_mapping (vars rΓ)) as [ι'|] eqn:Hthis_var; [|contradiction Hcorr].
                destruct (r_muttype h ι') as [q|] eqn:Hmut; [|contradiction Hcorr].
                destruct Hcorr as [Hbase_sub Hqual_typable].
                exists rqt_x.
                split.
                  unfold r_type.
                  simpl.
                  unfold runtime_getObj.
                  rewrite update_same; [exact Hdom|].
                  simpl.
                  unfold r_type in Hrtype_x.
                  rewrite Hobj_lx in Hrtype_x.
                  injection Hobj as Ho_eq.
                  injection H0 as Ho_eq2.
                  subst o_lx o_new.
                  exact Hrtype_x.
                  admit.
              (* exact H15. *)
              (* Case: loc2 ≠ lx *)
                unfold runtime_getObj.
                rewrite update_diff; [symmetry; exact Hneq_loc2_lx|].
                unfold wf_r_typable in Hcorr.
                destruct (r_type h loc2) as [rqt_loc2|] eqn:Hrtype_loc2; [|contradiction Hcorr].
                destruct (get_this_var_mapping (vars rΓ)) as [ι'|] eqn:Hthis_var; [|contradiction Hcorr].
                destruct (r_muttype h ι') as [q|] eqn:Hmut; [|contradiction Hcorr].
                destruct Hcorr as [Hbase_sub Hqual_typable].
                assert (Hloc2_dom : loc2 < dom h).
                {
                  (* loc2 comes from wf_r_typable, so it must be in heap domain *)
                  unfold r_type in Hrtype_loc2.
                  apply r_type_dom in Hrtype_loc2.
                  exact Hrtype_loc2.
                }
                destruct (nth_error h loc2) as [obj_loc2|] eqn:Hnth_loc2.
                (* Case: loc2 exists in heap *)
                  exists rqt_loc2.
                  split.
                  unfold r_type.
                  unfold runtime_getObj.
                  rewrite update_diff; [symmetry; exact Hneq_loc2_lx|].
                  exact Hrtype_loc2.
                  admit.
                (* Case: loc2 doesn't exist - contradiction *)
                  exfalso.
                  apply nth_error_None in Hnth_loc2.
                  lia.
                  exfalso.
                  discriminate Hobj.
            }
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
        split.
        specialize (Hheap ι Hdom).
        unfold wf_obj in Hheap.
        destruct (runtime_getObj h ι) as [objl|] eqn: Hobjl; [| easy].
        destruct Hheap as [Hwfobjtypeuse _].
        unfold runtime_getObj in Hobjl.
        rewrite Htest in Hobjl.
        inversion Hobjl.
        subst.
        exact Hwfobjtypeuse.

        specialize (Hheap ι Hdom).
        unfold wf_obj in Hheap.
        destruct (runtime_getObj h ι) as [objl|] eqn: Hobjl; [| easy].
        destruct Hheap as [Hwfobjtypeuse Hwfobjfields].
        unfold runtime_getObj in Hobjl.
        rewrite Htest in Hobjl.
        inversion Hobjl.
        subst.
        destruct Hwfobjfields as [field_defs [Hcollect [Hlen_eq Hforall2]]].

        exists field_defs.
        {
          split.
          exact Hcollect.
          split.
          exact Hlen_eq.
          eapply Forall2_impl; [|exact Hforall2].
          intros v fdef Hv_fdef.
          destruct v as [|loc]; [trivial|].
          (* First check if the object exists in the updated heap *)
          unfold update_field.
          destruct (runtime_getObj h lx) as [o_lx|] eqn:Hobj_lx.
            destruct (Nat.eq_dec loc lx) as [Heq | Hneq_loc].
              subst loc.
              rewrite Hobj_lx in Hv_fdef.
            destruct Hv_fdef as [rqt [Hrtype_loc Hsubtype]].
            unfold runtime_getObj.
            rewrite update_same.
            unfold r_type in Hrtype_loc.
            unfold r_type in Hrtype_loc.
            destruct (runtime_getObj h lx) as [oxx|] eqn:Hobj_lxx; [|discriminate Hrtype_loc].
            apply runtime_getObj_dom in Hobj_lxx.
            exact Hobj_lxx.
            exists rqt.
              split.
                unfold r_type.
                rewrite runtime_getObj_update_same.
                apply runtime_getObj_dom in Hobj_lx. exact Hobj_lx.
                 simpl.
                  unfold r_type in Hrtype_loc.
                  rewrite Hobj_lx in Hrtype_loc.
                  injection Hobj as Ho_new_eq.
                  subst o_new.
                  injection Hrtype_loc as Hrqt_eq.
                  subst rqt.
                  reflexivity.
                exact Hsubtype.
            destruct (runtime_getObj h loc) as [obj_loc|] eqn:Hobj_loc; [|contradiction Hv_fdef].
            destruct Hv_fdef as [rqt [Hrtype_loc Hsubtype]].
            unfold runtime_getObj.
            rewrite update_diff.
            symmetry. exact Hneq_loc.
            unfold runtime_getObj in Hobj_loc.
          destruct (nth_error h loc) as [obj|] eqn:Hnth_loc; [|discriminate Hobj_loc].
          injection Hobj_loc as Hobj_eq.
          subst obj.
          exists rqt.
          split.
            unfold r_type.
            rewrite runtime_getObj_update_diff.
            symmetry. exact Hneq_loc.
            exact Hrtype_loc.
            exact Hsubtype.
            exfalso.
            discriminate Hobj.
        }
        * exfalso.
        discriminate H0.
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
      destruct (runtime_getVal rΓ i) as [v|] eqn:Hval; [|exact Hcorr_orig].
      destruct v as [|loc]; [trivial|].
      (* Need to show: wf_r_typable CT rΓ' (update_field h lx f v2) loc sqt *)
      unfold wf_r_typable in Hcorr_orig |- *.
      destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
      destruct (get_this_var_mapping (vars rΓ)) as [ι'|] eqn:Hthis; [|contradiction].
      destruct (r_muttype h ι') as [q|] eqn:Hmut; [|contradiction].
      (* Show that r_type and r_muttype are preserved by update_field *)
      assert (Hrtype_preserved : r_type (update_field h lx f v2) loc = Some rqt).
      {
        unfold r_type.
        unfold update_field.
        (* have H12_copy := H12. *)
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
            (* injection H12 as Ho'_eq. *)
            (* subst o'. *)
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
    inversion Htyping.
    have Hwf_copy := Hwf.
    unfold wf_r_config.
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
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
        destruct (bound CT c) as [q_c_val|] eqn:Hbound.
        ++ unfold constructor_sig_lookup in H14.
        destruct (find_class CT c) as [def|] eqn:Hfind.
        ** apply find_class_dom in Hfind.
          exact Hfind.
        ** exfalso.
        unfold bound in Hbound.
        rewrite Hfind in Hbound.
        discriminate Hbound.
        ++ 
          unfold constructor_sig_lookup in H14.
          destruct (constructor_def_lookup CT c) as [ctor|] eqn:Hctor.
          ** unfold constructor_def_lookup in Hctor.
            destruct (find_class CT c) as [def|] eqn:Hfind.
            --- unfold bound in Hbound.
              rewrite Hfind in Hbound.
              discriminate Hbound.
            --- discriminate Hctor.
          ** discriminate H14.
      --
        {
          assert (Hc_dom : c < dom CT).
   {
     apply constructor_sig_lookup_dom in H14.
     exact H14.
   }
   
   (* Collect fields for class c *)
   assert (Hexists_fields : exists field_defs, CollectFields CT c field_defs).
   {
     eapply collect_fields_exists; eauto.
   }
   destruct Hexists_fields as [field_defs Hcollect_fields].
   
   exists field_defs.
   split.
   + (* CollectFields CT c field_defs *)
     exact Hcollect_fields.
   + split.
     * (* Length equality: dom vals = dom field_defs *)
       (* This follows from constructor well-formedness *)
       (* The constructor should ensure vals has the right length *)
       simpl.
       apply Forall2_length in H23.
       apply Forall2_length in H24.
       apply runtime_lookup_list_preserves_length in H0.
       apply static_getType_list_preserves_length in H13.
       assert (Hargs_total : dom argtypes = dom (sparams consig) + dom (cparams consig)).
      assert (Hargs_total : dom argtypes = dom (sparams consig) + dom (cparams consig)).
      {
        rewrite <- H23, <- H24.
        rewrite <- length_app.
        rewrite firstn_skipn.
        reflexivity.
      }
      exact Hargs_total.
      rewrite H0.
      rewrite <- H13.
      rewrite Hargs_total.
      eapply constructor_sig_lookup_implies_def in H14; eauto.
      destruct H14 as [cdef Hcedflookup].
      destruct Hcedflookup as [Hcedflookup Hcdefcsig].
      eapply constructor_params_field_count; eauto.
     * (* Forall2 property *)
       (* Each value in vals is well-typed according to field_defs *)
       (* This follows from the typing of constructor arguments *)
       apply runtime_lookup_list_preserves_typing with (CT:= CT) ( h := h) (sΓ := sΓ') (args := ys) (argtypes := argtypes) in H0; auto.
       (* Use H23, H24 to show arguments are well-typed *)
       (* Then use constructor well-formedness to connect to field types *)
       admit.
      }
    * (* ι < dom h (existing object) *)
      assert (ι < dom h) by lia.
      unfold wf_obj.
      rewrite runtime_getObj_last2; auto.
      {
        specialize (Hheap ι H2).
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
                  exfalso. easy.
                - (* Show iot is still in extended heap domain *)
                  subst.
                  rewrite length_app. simpl.
                  lia.
              }
           --
            split.   
            subst.
            exact Hiot.
            rewrite H5.
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
      assert (Hlen_extended: dom (h ++ [{| rt_type := {| rqtype := qadapted; rctype := c |}; fields_map := vals |}]) = dom h + 1).
      -- rewrite length_app. simpl. lia.
      -- rewrite nth_error_app2.
      ** lia.
      ** replace (dom h - dom h) with 0 by lia.
        simpl. reflexivity.
      * assert (Hx_dom : x < dom sΓ') by (apply static_getType_dom in H12; exact H12).
      rewrite <- Hlen; exact Hx_dom.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. rewrite <- H22. exact HsenvLength.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. rewrite <- H22. exact HsenvWellTyped.
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
        + assert (x < dom sΓ') by (apply static_getType_dom in H12; exact H12).
        rewrite <- Hlen. exact H2.
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
              easy.
            + (* Case: x = S x' *)
              unfold runtime_getVal in H.
              rewrite Hvars in H.
              simpl in H.
              injection H as H17_eq.
              subst v0.
              simpl.
              unfold r_muttype.
              rewrite heap_extension_preserves_objects.
              unfold r_muttype in H1.
              destruct (runtime_getObj h l1) as [obj|] eqn:Hobj; [|discriminate].
              *
                apply runtime_getObj_dom in Hobj.
                exact Hobj.
              * 
                (* injection H as H19_eq.
                rewrite H19_eq.
                split. *)
                assert (Hsqt_eq : sqt = Tx).
                {
                  unfold static_getType in H12.
                  rewrite Hnth in H12.
                  injection H12 as H0_eq.
                  exact H0_eq.
                }
                subst sqt.
                unfold runtime_type_to_qualified_type.
                simpl.
                {
                  unfold r_muttype in H1.
                  destruct (runtime_getObj h l1) as [obj|] eqn:Hobj; [|discriminate].
                  injection H1 as H1_eq.
                  subst qthisr.
                  split.
                    + apply qualified_type_subtype_base_subtype in H25.
                      * exact H25.
                      * apply constructor_sig_lookup_dom in H14; exact H14.
                      * assert (Hwf_Tx : wf_stypeuse CT (sqtype Tx) (sctype Tx)).
                        {
                          unfold wf_senv in Hsenv.
                          destruct Hsenv as [_ Hforall].
                          apply (Forall_nth_error _ _ _ _ Hforall Hnth).
                        }
                        unfold wf_stypeuse in Hwf_Tx.
                        destruct (bound CT (sctype Tx)) as [q_bound|] eqn:Hbound; [|contradiction].
                        destruct Hwf_Tx as [_ Hdom].
                        exact Hdom.
                    + unfold qualifier_typable.
                      unfold q_project_q_r in H3.
                      destruct (vpa_mutabilty (q_r_proj (rqtype (rt_type obj))) q_c) eqn:Hvpa; try discriminate.
                      injection H3 as H3_eq.
                      subst qadapted.
                      simpl.
                      apply qualified_type_subtype_q_subtype in H25.
                      destruct (sqtype Tx) eqn:Hsqtype_Tx.
                      - (* sqtype Tx = Mut *)
                        unfold vpa_mutabilty.
                        destruct (q_r_proj (rqtype (rt_type obj))); reflexivity.
                      - (* sqtype Tx = Imm *)
                        exfalso.
                        simpl in H25.
                        apply vpa_type_to_type_mut_cases in Hvpa.
                        destruct Hvpa as [Hqc_mut | [Hqthis_mut Hqc_rdm]].
                        * (* Case: q_c = Mut *)
                          subst q_c.
                          easy.
                        * (* Case: q_c = RDM *)
                          subst q_c.
                          easy.
                      - (* sqtype Tx = Rd *)
                        unfold vpa_mutabilty.
                        destruct (q_r_proj (rqtype (rt_type obj))). all: try reflexivity.
                        apply vpa_type_to_type_mut_cases in Hvpa.
                        destruct Hvpa as [Hqc_mut | [Hqthis_mut Hqc_rdm]]; [|trivial].
                        all: try simpl in H25.
                        subst q_c.
                        easy.
                        easy.
                        apply vpa_type_to_type_mut_cases in Hvpa.
                        destruct Hvpa as [Hqc_mut | [Hqthis_mut Hqc_rdm]]; [|trivial].
                        subst q_c.
                        easy.
                        easy.
                        apply vpa_type_to_type_mut_cases in Hvpa.
                        destruct Hvpa as [Hqc_mut | [Hqthis_mut Hqc_rdm]]; [|trivial].
                        subst q_c.
                        easy.
                        easy.
                      - (* sqtype Tx = Lost *)
                        unfold vpa_mutabilty.
                        destruct (q_r_proj (rqtype (rt_type obj))); reflexivity.
                      - destruct (q_r_proj (rqtype (rt_type obj))). all: try reflexivity.
                      - destruct (q_r_proj (rqtype (rt_type obj))).
                        all: unfold vpa_mutabilty.
                        all: try apply vpa_type_to_type_mut_cases in Hvpa.
                        all: try destruct Hvpa as [Hqc_mut | [Hqthis_mut Hqc_rdm]]; [|trivial].
                        all: try subst q_c.
                        all: try easy.
                      - inversion H25; subst. all: try exact H. simpl.
                        apply constructor_sig_lookup_dom in H14.
                        exact H14.
                      - unfold wf_senv in H11.
                        destruct H11 as [Hsenvdom Halltyable].
                        have Hwf_Tx := Forall_nth_error _ _ _ _ Halltyable Hnth.
                        unfold wf_stypeuse in Hwf_Tx.
                        destruct (bound CT (sctype Tx)) as [q_bound|] eqn:Hbound; [|contradiction].
                        destruct Hwf_Tx as [_ Hdom].
                        exact Hdom.
                      - injection H3 as H3_eq. subst qadapted.
                        destruct (q_r_proj (rqtype (rt_type obj))).
                        all: unfold vpa_mutabilty.
                        all: try apply vpa_type_to_type_mut_cases in Hvpa.
                        all: try unfold vpa_mutabilty in Hvpa.
                        all: try destruct q_c.
                        all: try easy.
                        all: try destruct (sqtype Tx) eqn:Hex.
                        all: try easy.
                        all: apply qualified_type_subtype_q_subtype in H25.
                        all: simpl in H25.
                        all: try rewrite Hex in H25. 
                        all: try easy.
                        (* all: try (apply constructor_sig_lookup_dom in H14; exact H14). *)
                        all: try (
                          unfold wf_senv in Hsenv;
                          destruct Hsenv as [_ Hforall];
                          have Hwf_Tx := Forall_nth_error _ _ _ _ Hforall Hnth;
                          unfold wf_stypeuse in Hwf_Tx;
                          destruct (bound CT (sctype Tx)) as [q_bound|] eqn:Hbound; [|contradiction];
                          destruct Hwf_Tx as [_ Hdom];
                          exact Hdom
                        ).
                        all: try (simpl;
                        apply constructor_sig_lookup_dom in H14;
                        exact H14).
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
            + easy.
            + simpl. exact Hthis.
            }
            rewrite Hthis_preserved.
            assert (Hloc_bound : loc < dom h).
          {
            unfold r_type in Hrtype.
            destruct (runtime_getObj h loc) as [obj|] eqn:Hobj; [|discriminate].
            apply runtime_getObj_dom in Hobj. exact Hobj.
          }
          assert (Hrtype_ext : r_type (h ++ [{| rt_type := {| rqtype := qadapted; rctype := c |}; fields_map := vals |}]) loc = Some rqt).
          {
            unfold r_type in Hrtype |- *.
            rewrite heap_extension_preserves_objects; auto.
          }
          assert (Hmut_ext : r_muttype (h ++ [{| rt_type := {| rqtype := qadapted; rctype := c |}; fields_map := vals |}]) ι' = Some q).
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
    intros. inversion Htyping; subst.
    specialize (IHHeval1 eq_refl sΓ'0 sΓ Hwf H4) as IH1.
    specialize (IHHeval2 eq_refl sΓ' sΓ'0 IH1 H6) as IH2.
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
    eval_stmt OK CT rΓ h stmt OK rΓ' h' -> 
    runtime_getObj h' l = Some (mkObj (mkruntime_type Imm_r C) vals') ->
    sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA ->
    nth_error vals f = nth_error vals' f.
Proof.
  intros. remember OK as ok.
  generalize dependent sΓ.
  generalize dependent sΓ'.
  generalize dependent vals. generalize dependent vals'.
  induction H3; try discriminate.
  - (* Skip *) intros; inversion H4; subst; rewrite H0 in H4; injection H4; auto.
  - (* Local *) intros; inversion H4; subst; rewrite H1 in H4; injection H4; auto.
  - (* VarAss *) intros; inversion H4; subst; rewrite H2 in H4; injection H4; auto.
  - (* FldWrite *) 
  {
    intros.
    destruct (Nat.eq_dec l lx) as [Heq_l | Hneq_l].
    - (* Case: l = lx (same object being written to) *)
      subst l.
      (* Extract the object type from H0 and H6 *)
      rewrite H7 in H1.
      injection H1 as H1_eq.
      subst o.
      (* Now we have an immutable object, but can_assign returned true *)
      (* This should be impossible for Final/RDA fields on immutable objects *)
      destruct (Nat.eq_dec f f0) as [Heq_f | Hneq_f].
      + (* Case: f = f0 (same field being written) *)
        subst f.
        (* Show contradiction: can_assign should be false for immutable Final/RDA fields *)
        exfalso.
        unfold wf_r_config in H8.
        destruct H8 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
        assert (Hx_bound : x < dom sΓ) by (apply runtime_getVal_dom in H0; rewrite <- Hlen in H0; exact H0).
        inversion H9; subst.
        specialize (Hcorr x Hx_bound Tx H12).
        rewrite H0 in Hcorr.
        assert (Hsubtype: base_subtype CT C (sctype Tx)).
        {
          unfold wf_r_typable in Hcorr.
          destruct (r_type h lx) as [rqt|] eqn:Hrtype; [|contradiction].
          unfold r_type in Hrtype.
          rewrite H7 in Hrtype.
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
        rewrite H7 in Hcorr.
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
          unfold update_field in H4.
          rewrite H7 in H4.
          rewrite H4 in H6.
          unfold runtime_getObj in H6.
          (* Apply update_same to get the updated object *)
          assert (Hget_same : nth_error (update lx {| rt_type := {| rqtype := Imm_r; rctype := C |}; fields_map := [f0 ↦ v2] (vals) |} h) lx = 
                              Some {| rt_type := {| rqtype := Imm_r; rctype := C |}; fields_map := [f0 ↦ v2] (vals) |}).
          {
            apply update_same.
            exact H.
          }
          rewrite Hget_same in H6.
          injection H6 as H6_eq.
          symmetry. exact H6_eq.
        }
        rewrite Hvals_eq.
        unfold getVal.
        rewrite update_diff.
        symmetry. exact Hneq_f.
        reflexivity.
    -
    assert (Hl_unchanged : runtime_getObj h' l = runtime_getObj h l).
    {
      unfold update_field in H4.
      rewrite H1 in H4.
      rewrite H4.
      unfold runtime_getObj.
      apply update_diff.
      easy.
    }
    rewrite H7 in Hl_unchanged.
    rewrite Hl_unchanged in H6.
    injection H6 as H6_eq.
    rewrite <- H6_eq.
    reflexivity.
  }
  - (* New *) (* h' = h ++ [new_obj], so l < dom h means same object *)
  intros.
  inversion H4; subst.
  (* Since l < dom h, the object at location l is unchanged *)
  unfold runtime_getObj in H9.
  rewrite List.nth_error_app1 in H9; auto.
  unfold runtime_getObj in H10.
  rewrite H10 in H9.
  injection H9; intros; subst.
  reflexivity.
  - (* Call *) (* Similar to other non-mutating cases *) 
  intros.
  revert H7.
  inversion H14. 
  revert H17.
  subst.
  intro H17.
  intro H7.
  destruct H2 as [mdeflookup getmbody].
  remember (msignature mdef) as msig.
  have mdeflookupcopy := mdeflookup.
  apply method_body_well_typed_dispatch in mdeflookup; auto.
  destruct mdeflookup as [sΓmethodend Htyping_method].
  remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit.
  apply IHeval_stmt with (sΓ' := sΓmethodend)(sΓ := sΓmethodinit). 1-5: auto.
  rename rΓ' into rΓmethodinit.
  assert (Hwf_method_frame : wf_r_config CT sΓmethodinit 
                                    rΓmethodinit h).
  {
    unfold wf_r_config in *.
    destruct H13 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    have Hclasstable := Hclass.
    destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
    repeat split.
    exact Hclass.
    exact Hobj.
    exact Hotherclasses.
    apply Hcname_consistent.
    apply Hcname_consistent.
    exact Hheap.
    rewrite H7.
    simpl.
    lia.
    unfold wf_renv in Hrenv.
    destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
    exists ly.
    split.
    rewrite H7.
    simpl.
    reflexivity.
    unfold runtime_getVal in H0.
    destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
    injection H0 as H0_eq.
    subst v.
    eapply Forall_nth_error in Hallvals; eauto.
    simpl in Hallvals.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobjly; [|contradiction].
    apply runtime_getObj_dom in Hobjly.

    exact Hobjly.
    rewrite H7.
    simpl.
    constructor.
    simpl.
    unfold runtime_getVal in H0.
    destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
    injection H0 as H0_eq.
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
    eapply method_sig_wf_receiver_dispatch; eauto.
    unfold r_basetype in H1.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
    injection H1 as H1_eq.
    subst cy.
    destruct obj as [rt_obj fields_obj].
    destruct rt_obj as [rq_obj rc_obj].
    simpl.
    unfold wf_heap in Hheap.
    assert (Hly_dom : ly < dom h) by (apply runtime_getObj_dom in Hobjy; exact Hobjy).
    specialize (Hheap ly Hly_dom).
    unfold wf_obj in Hheap.
    rewrite Hobjy in Hheap.
    destruct Hheap as [Hwf_rtypeuse _].
    unfold wf_rtypeuse in Hwf_rtypeuse.
    simpl in Hwf_rtypeuse.
    destruct (bound CT rc_obj) as [class_def|] eqn:Hbound.
    exact Hwf_rtypeuse.
    contradiction.

    eapply method_sig_wf_parameters_dispatch; eauto.
    unfold r_basetype in H1.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
    injection H1 as H1_eq.
    subst cy.
    destruct obj as [rt_obj fields_obj].
    destruct rt_obj as [rq_obj rc_obj].
    simpl.
    unfold wf_heap in Hheap.
    assert (Hly_dom : ly < dom h) by (apply runtime_getObj_dom in Hobjy; exact Hobjy).
    specialize (Hheap ly Hly_dom).
    unfold wf_obj in Hheap.
    rewrite Hobjy in Hheap.
    destruct Hheap as [Hwf_rtypeuse _].
    unfold wf_rtypeuse in Hwf_rtypeuse.
    simpl in Hwf_rtypeuse.
    destruct (bound CT rc_obj) as [class_def|] eqn:Hbound.
    exact Hwf_rtypeuse.
    contradiction.

    apply static_getType_list_preserves_length in H21.
      apply runtime_lookup_list_preserves_length in H6.
      rewrite HeqsΓmethodinit.
      simpl.
      f_equal.
      apply Forall2_length in H29.
      rewrite <- Heqmsig.

      assert (Hsubtype : base_subtype CT cy (sctype Ty)).
      {
        assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in H20.
          exact H20.
        }

        (* Apply correspondence to get wf_r_typable *)
        specialize (Hcorr y Hy_dom Ty H20).
        rewrite H0 in Hcorr.

        (* Extract subtyping from wf_r_typable *)
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in H1.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection H1 as Hcy_eq.
        subst cy.
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].


        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot _]].
        unfold get_this_var_mapping.
        unfold gget in Hget_iot.
        destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].
        injection Hget_iot as Hv0_eq.
        subst v0.

        unfold r_type in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        destruct (r_muttype h iot) as [q|] eqn:Hmut; [|contradiction].
        destruct Hcorr as [Hsubtype _].
        exact Hsubtype.
      }
    rewrite <- H6 in H21.
    rewrite H7.
    simpl.
    f_equal.
    rewrite <- H21.
    rewrite Heqmsig.
    rewrite H29.
    eapply wf_method_override_same_param_length_general; eauto.
    eapply r_basetype_in_dom ; eauto.
    apply base_subtype_CD in Hsubtype.
    apply r_basetype_in_dom with (CT:=CT) in H1; auto. 
    lia.
    exact Hclasstable.
    have mdeflookupcopyagain := mdeflookupcopy.
    apply find_method_with_name_consistent in mdeflookupcopy; eauto.
    rewrite mdeflookupcopy.
    exact mdeflookupcopyagain.
    apply find_method_with_name_consistent in mdeflookupcopy; eauto. 
    rewrite mdeflookupcopy.
    exact H22.

    admit.
  }
  exact Hwf_method_frame.
  rewrite <- getmbody in Htyping_method.
  exact Htyping_method. 

  unfold wf_r_config in H13.
  destruct H13 as [Hwf_classtable _].
  exact Hwf_classtable.
  unfold r_basetype in H1.
  destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
  injection H1 as H1_eq.
  subst cy.
  destruct obj as [rt_obj fields_obj].
  destruct rt_obj as [rq_obj rc_obj].
  simpl.
  destruct H13 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
  unfold wf_heap in Hheap.
  assert (Hly_dom : ly < dom h) by (apply runtime_getObj_dom in Hobjy; exact Hobjy).
  specialize (Hheap ly Hly_dom).
  unfold wf_obj in Hheap.
  rewrite Hobjy in Hheap.
  destruct Hheap as [Hwf_rtypeuse _].
  unfold wf_rtypeuse in Hwf_rtypeuse.
  simpl in Hwf_rtypeuse.
  destruct (bound CT rc_obj) as [class_def|] eqn:Hbound.
  exact Hwf_rtypeuse.
  contradiction.
  -  (* Seq *) (* Apply IH transitively *)
  intros. inversion H2; subst. 
  specialize (eval_stmt_preserves_heap_domain_simple CT rΓ h s1 rΓ' h' H3_) as Hh'.
  assert (l < dom h') by lia. specialize (runtime_getObj_Some h' l H3) as [C' [values' Hh'some]].
  specialize (runtime_preserves_r_type_heap CT rΓ h l ({| rqtype := Imm_r; rctype := C |})
  h' vals s1 rΓ' H0 H3_) as [vals1 Hrtype]. rewrite Hrtype in Hh'some; inversion Hh'some; subst.
  specialize (IHeval_stmt1 H Heqok H5 values' Hrtype vals H0 sΓ'0 sΓ H1 H10). 
  specialize (preservation_pico CT sΓ rΓ h s1 rΓ' h' sΓ'0 H1 H10 H3_) as Hwf'.
  specialize (IHeval_stmt2 H3 Heqok H5 vals' H4 values' Hrtype sΓ' sΓ'0 Hwf' H12). 
  rewrite IHeval_stmt2 in IHeval_stmt1; auto.
Admitted.


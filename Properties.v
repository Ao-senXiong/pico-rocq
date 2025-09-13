Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation.
Require Import List.
Import ListNotations.
Require Import String.
From RecordUpdate Require Import RecordUpdate.

Lemma method_lookup_wf_class: forall CT C m mdef,
  wf_class_table CT ->
  wf_class CT C ->
  method_def_lookup CT (cname (signature C)) m = Some mdef ->
  wf_method CT (cname (signature C)) mdef.
Proof.
  intros CT C m mdef Hwf_ct Hwf_class Hlookup.
  inversion Hwf_class; subst.
  - (* WFObjectDef case *)
    exfalso.
    unfold method_def_lookup in Hlookup.
    unfold mdef_lookup in Hlookup.
    destruct (dom CT) as [|fuel]; [discriminate|].
    simpl in Hlookup.
    assert (Hfind_class : find_class CT (cname (signature C)) = Some C).
    { 
      apply wf_class_in_table.
      exact Hwf_ct.
      exact Hwf_class.
      assert (Hfind_succeeded : exists def, find_class CT (cname (signature C)) = Some def).
      {
        (* Since the method lookup succeeded, find_class must have succeeded *)
        unfold method_def_lookup in Hlookup.
        unfold mdef_lookup in Hlookup.
        destruct (find_class CT (cname (signature C))) as [def|] eqn:Hfind.
        - exists def. reflexivity.
        - (* If find_class failed, then method lookup would fail *)
          discriminate Hlookup.
      }

      (* If find_class succeeded, then the index is in bounds *)
      destruct Hfind_succeeded as [def Hfind].
      apply find_class_dom in Hfind.
      exact Hfind.
    }
    rewrite Hfind_class in Hlookup.
    simpl in Hlookup.
    rewrite H2 in Hlookup.
    simpl in Hlookup.
    rewrite H in Hlookup.
    discriminate.
  - (* WFOtherDef case *)
    {
      destruct H3 as [_ [Hwf_methods _]].
      unfold method_def_lookup in Hlookup.
      unfold mdef_lookup in Hlookup.
      remember (dom CT) as fuel.
      generalize dependent mdef.
      generalize dependent m.
      generalize dependent C.
      induction fuel as [|fuel' IH]; intros C m mdef Hlookup.

      - (* Base case: fuel = 0 *)
        simpl in Hlookup.
        unfold wf_class_table in Hwf_ct.
        destruct Hwf_ct as [Hforall_wf [Hobject Hclassnamematch]].
        exfalso.
        destruct Hobject as [obj_def [Hfind_obj _]].
        unfold find_class, gget in Hfind_obj.
        rewrite Heqfuel in Hfind_obj.
        simpl in Hfind_obj.
        assert (Hdom_zero : dom CT = 0) by (symmetry; exact Heqfuel).
        rewrite Hdom_zero in Hfind_obj.
        assert (H_contra : 0 < dom CT).
        {
          apply nth_error_Some.
          rewrite Hfind_obj.
          discriminate.
        }
        rewrite Hdom_zero in H_contra.
        lia.

      - (* Inductive case: fuel = S fuel' *)
        simpl in Hlookup.
        destruct (find_class CT (cname (signature C))) as [def|] eqn:Hfind.
        + (* Class found *)
          admit.
              
        + (* Class not found *)
          admit.
    }
Admitted. 

Lemma method_lookup_wf : forall CT C m mdef,
  wf_class_table CT ->
  method_def_lookup CT C m = Some mdef ->
  wf_method CT C mdef.
Proof.
  intros CT C m mdef Hwf_ct Hlookup.
  unfold wf_class_table in Hwf_ct.
  destruct Hwf_ct as [Hforall_wf _].
  unfold method_def_lookup in Hlookup.
  unfold mdef_lookup in Hlookup.
  generalize dependent mdef.
  generalize dependent m.
  induction CT as [|cdef CT' IH]; intros m mdef Hlookup.
  - (* Empty CT case *)
    simpl in Hlookup.
    destruct C; discriminate.
  - (* Non-empty CT case *)
    simpl in Hlookup.
    destruct C as [|C'].
    + (* C = 0, method is in first class *)
      inversion Hforall_wf; subst.
      destruct (find (fun mdef => eq_method_name (mname (msignature mdef)) m) (methods (body cdef))) as [found_mdef|] eqn:Hfind.
      * (* Method found in current class *)
        (* subst mdef. *)
        (* Extract method well-formedness from class well-formedness *)
        inversion H1; subst.
        -- (* WFObjectDef case *)
          admit.
          (* rewrite H7 in Hfind. simpl in Hfind. discriminate. *)
        -- (* WFOtherDef case *)
          destruct H5 as [_ [Hwf_methods _]].
          apply find_some in Hfind.
          destruct Hfind as [Hin Heq_name].
          eapply Forall_forall; eauto.
          admit.
      * (* Method not in current class, check superclass *)
        admit. (* Handle superclass lookup *)
    + (* C = S C', recurse *)
      admit.
Admitted.

Lemma method_body_well_typed : forall CT C m mdef,
  wf_class_table CT ->
  method_def_lookup CT C m = Some mdef ->
  exists sΓ', stmt_typing CT (mreceiver (msignature mdef) :: mparams (msignature mdef)) 
                           (mbody_stmt (mbody mdef)) 
                           sΓ'.
Proof.
  intros CT C m mdef Hwf_ct Hlookup.
  apply method_lookup_wf in Hlookup; auto.
  inversion Hlookup; subst.
  - (* WFPlainMethod case *)
  admit.
  - (* WFOverridingMethod case *)
  admit.
Admitted.

Lemma wf_method_sig_types : forall CT C mdef,
  wf_method CT C mdef ->
  wf_stypeuse CT (sqtype (mreceiver (msignature mdef))) (sctype (mreceiver (msignature mdef))) /\
  Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) (mparams (msignature mdef)).
Proof.
  intros CT C mdef Hwf_method.
  inversion Hwf_method; subst.
  - (* WFPlainMethod case *)
    admit. (* Extract well-formedness from method typing context *)
  - (* WFOverridingMethod case *)
    admit. (* Extract well-formedness from method typing context *)
Admitted.

Lemma method_sig_wf : forall CT C m m_sig,
  wf_class_table CT ->
  method_sig_lookup CT C m = Some m_sig ->
  wf_stypeuse CT (sqtype (mreceiver m_sig)) (sctype (mreceiver m_sig)) /\
  Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) (mparams m_sig).
Proof.
  intros CT C m m_sig Hwf_ct Hlookup.
  unfold method_sig_lookup in Hlookup.
  unfold method_sig_lookup in Hlookup.
  destruct (mdef_lookup (dom CT) CT C m) as [mdef|] eqn:Hmdef; [|discriminate].
  injection Hlookup as Heq. subst m_sig.
  apply method_lookup_wf in Hmdef; auto.
  unfold method_def_lookup in Hmdef.
  apply wf_method_sig_types in Hmdef.
  exact Hmdef.
Qed.

Lemma method_sig_wf_from_def: forall CT C m mdef m_sig,
  wf_class_table CT ->
  method_def_lookup CT C m = Some mdef ->
  m_sig = (msignature mdef) ->
  wf_stypeuse CT (sqtype (mreceiver m_sig)) (sctype (mreceiver m_sig)) /\
  Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) (mparams m_sig).
Proof.
  intros CT C m mdef m_sig Hwf_ct Hlookup.
  intros Heq.
  subst m_sig.
  apply method_lookup_wf in Hlookup; auto.
  apply wf_method_sig_types in Hlookup.
  exact Hlookup.
Qed.

Lemma method_frame_wf_r_config : forall CT sΓ rΓ h y ly Ty vals m_sig args argtypes C m,
  wf_r_config CT sΓ rΓ h ->
  runtime_getVal rΓ y = Some (Iot ly) ->
  static_getType sΓ y = Some Ty ->
  runtime_lookup_list rΓ args = Some vals ->
  static_getType_list sΓ args = Some argtypes ->
  qualified_type_subtype CT Ty (vpa_qualified_type (sqtype Ty) (mreceiver m_sig)) ->
  Forall2 (fun arg T => qualified_type_subtype CT arg (vpa_qualified_type (sqtype Ty) T)) 
          argtypes (mparams m_sig) ->
  method_sig_lookup CT C m = Some m_sig ->
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
    { apply static_getType_dom in H1. exact H1. }
    specialize (Hcorr Hy_dom Ty H1).
    rewrite H0 in Hcorr.
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
    { apply static_getType_dom in H1. exact H1. }
    specialize (Hcorr Hy_dom Ty H1).
    rewrite H0 in Hcorr.
    unfold wf_r_typable in Hcorr.
    destruct (r_type h ly) as [rqt|] eqn:Hrtype; [|contradiction].
    unfold r_type in Hrtype.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobj; [trivial | discriminate].
    assert (H_forall: Forall (fun value => match value with
      | Null_a => True
      | Iot loc => match runtime_getObj h loc with Some _ => True | None => False end
      end) vals).
    {
      have H_typing := runtime_lookup_list_preserves_typing CT sΓ rΓ h args vals argtypes H H3 H2.
      clear H4 H5.
      induction H_typing.
      - constructor.
      - constructor.
        + destruct x as [|loc]; [trivial|].
          unfold wf_r_typable in H4.
          destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
          unfold r_type in Hrtype.
          destruct (runtime_getObj h loc) as [obj|] eqn:Hobj; [trivial | discriminate].
        + admit.
    }
    exact H_forall.
  }
  {
    simpl. lia.
  }
  {
    constructor.
      destruct H as [Hclass _].
      apply method_sig_wf in H6; auto.
      destruct H6 as [Hreceiver _].
      exact Hreceiver.
      destruct H as [Hclass _].
      apply method_sig_wf in H6; auto.
      destruct H6 as [_ Hparams].
      exact Hparams.
  }
  {
    simpl.
    f_equal.
    apply Forall2_length in H5.
    apply static_getType_list_preserves_length in H3.
    apply runtime_lookup_list_preserves_length in H2.
    rewrite -> H3 in H5.
    rewrite <- H2 in H5.
    symmetry.
    exact H5.
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
      { apply static_getType_dom in H1. exact H1. }
      specialize (Hcorr Hy_dom Ty H1).
      rewrite H0 in Hcorr.

      eapply wf_r_typable_subtype; eauto.
      apply senv_var_domain with (sΓ := sΓ) (i := y); auto.
      unfold static_getType in H1.
      exact H1.

      apply method_sig_wf in H6; auto.
      destruct H6 as [Hreceiver _].
      unfold wf_stypeuse in Hreceiver.
      destruct (bound CT (sctype (mreceiver m_sig))) as [q_bound|] eqn:Hbound; [|contradiction].
      destruct Hreceiver as [_ Hdom].
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
      + admit.
      + admit.
      + admit.
      + admit.
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
        apply Forall2_length in H5.
        apply static_getType_list_preserves_length in H3.
        apply runtime_lookup_list_preserves_length in H2.
        rewrite -> H3 in H5.
        rewrite <- H5 in Hi'_bound.
        exact Hi'_bound.
      }
      (* Use the typing correspondence from the original environment *)
      admit. (* Complex proof involving parameter correspondence *)
  }
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
    apply method_body_lookup_implies_def_lookup in H1.
    destruct H1 as [mdef H1].
    remember (msignature mdef) as msig.
    destruct H1 as [Hmdef_lookup Hbody_eq].
    have Hmdef_lookupcopy := Hmdef_lookup. 
    apply method_body_well_typed in Hmdef_lookup; auto.
    destruct Hmdef_lookup as [sΓmethodend Hmdef_lookup].

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
      (* Receiver type is well-formed *)
      apply method_sig_wf_from_def with (m_sig := (msignature mdef)) in Hmdef_lookupcopy; auto.
      destruct Hmdef_lookupcopy as [Hreceiver _].
      exact Hreceiver.
      (* Parameter types are well-formed *)
      apply method_sig_wf_from_def with (m_sig := (msignature mdef)) in Hmdef_lookupcopy; auto.
      destruct Hmdef_lookupcopy as [_ Hparams].
      exact Hparams.

      apply static_getType_list_preserves_length in H15.
      apply runtime_lookup_list_preserves_length in H4.
      rewrite HeqsΓmethodinit.
      rewrite HeqrΓmethodinit.
      simpl.
      f_equal.
      apply Forall2_length in H23.
      rewrite <- Heqmsig.
      (* rewrite <- H23. prove method lookup number of parameters consistent*)
      admit.

      admit.
    }
    assert (wf_r_config CT sΓmethodend rΓ'' h'). 
    {
      eapply IHHeval with (sΓ := sΓmethodinit) (sΓ' := sΓmethodend); eauto.
      rewrite Hbody_eq in Hmdef_lookup.
      exact Hmdef_lookup.
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

      rewrite Hbody_eq in Hmdef_lookup.
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
      rewrite Hbody_eq in Hmdef_lookup.
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

      admit.
    }
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hwf_classtable _].
    exact Hwf_classtable.
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
    (* subst. *)
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
      repeat split.
       admit.
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
    specialize (IHHeval1 eq_refl sΓ'0 sΓ Hwf H3) as IH1.
    specialize (IHHeval2 eq_refl sΓ' sΓ'0 IH1 H5) as IH2.
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
  (* generalize dependent vals. generalize dependent vals'.
  generalize dependent sΓ. generalize dependent sΓ'. *)
  induction H3; try discriminate.
  (* 7:{ inversion H2; subst.
    (* replace the assertions with eval_stmt_preserves_heap_domain. *)
    assert (dom h <= dom h') by admit.
    assert (l < dom h') by lia. specialize (runtime_getObj_Some h' l H6) as [C' [values' Hh']].
    assert (C' = {| rqtype := Imm_r; rctype := C |}).
    {  }
    specialize (IHeval_stmt1 H Heqok sΓ sΓ'0 H1 H9 vals H0 vals'). exact IHeval_stmt. } *)
  - (* Skip *) inversion H4. intros; subst; rewrite H0 in H4; injection H4; auto.
  - (* Local *) inversion H4; intros; subst; rewrite H0 in H4; injection H4; auto.
  - (* VarAss *) inversion H4; intros; subst; rewrite H0 in H4; injection H4; auto.
  - (* FldWrite *) 
  {
    intros.
    destruct (Nat.eq_dec l lx) as [Heq_l | Hneq_l].
    - (* Case: l = lx (same object being written to) *)
      subst l.
      (* Extract the object type from H0 and H6 *)
      rewrite H0 in H2.
      injection H2 as H2_eq.
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
        assert (Hx_bound : x < dom sΓ) by (apply runtime_getVal_dom in H1; rewrite <- Hlen in H1; exact H1).
        inversion H9; subst.
        specialize (Hcorr x Hx_bound Tx H12).
        rewrite H1 in Hcorr.
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
          unfold update_field in H7.
          rewrite H0 in H7.
          rewrite H7 in H4.
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
      unfold update_field in H7.
      rewrite H2 in H7.
      rewrite H7.
      unfold runtime_getObj.
      apply update_diff.
      easy.
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
  apply method_body_lookup_implies_def_lookup in H3.
  destruct H3 as [mdef H3].
  remember (msignature mdef) as msig.
  destruct H3 as [Hmdef_lookup Hbody_eq].
  have Hmdef_lookupcopy := Hmdef_lookup. 
  apply method_body_well_typed in Hmdef_lookup; auto.
  destruct Hmdef_lookup as [sΓmethodend Hmdef_lookup].
  remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit.
  apply IHeval_stmt with (sΓ' := sΓmethodend)(sΓ := sΓmethodinit).
  exact H.
  exact H0.
  easy.
  exact H4.
  exact H5.
  assert (Hwf_method_frame : wf_r_config CT sΓmethodinit 
                                    rΓ' h).
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
    rewrite H9.
    simpl.
    lia.
    unfold wf_renv in Hrenv.
    destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
    exists ly.
    split.
    rewrite H9.
    simpl.
    reflexivity.
    unfold runtime_getVal in H1.
    destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
    injection H1 as H1_eq.
    subst v.
    eapply Forall_nth_error in Hallvals; eauto.
    simpl in Hallvals.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobjly; [|contradiction].
    apply runtime_getObj_dom in Hobjly.

    exact Hobjly.
    rewrite H9.
    simpl.
    constructor.
    simpl.
    unfold runtime_getVal in H1.
    destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
    injection H1 as H1_eq.
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
  rewrite <- H6 in Hmdef_lookup.
  exact Hmdef_lookup. 
  unfold wf_r_config in H13.
  destruct H13 as [Hwf_classtable _].
  exact Hwf_classtable.
  -  (* Seq *) (* Apply IH transitively *)
  admit.
Admitted.


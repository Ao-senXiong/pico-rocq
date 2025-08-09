Require Export Syntax.
Require Export List.
Import ListNotations.
Require Export Notations LibTactics Tactics.
Require Export ssreflect ssrbool Coq.Sets.Finite_sets_facts.
From RecordUpdate Require Import RecordUpdate.

(* ------------------------------------------------------------------------ *)
(** ** Helper functions *)
Definition gget {X: Type} (l : list X)  : Loc -> option X := nth_error l.
Definition runtime_getObj (l : heap)    : Loc -> option Obj := nth_error l.
Definition getVal (l : list value)  : Loc -> option value := nth_error l.
(* Definition getAVal (l : list (r_a * value) )  : Loc -> option (r_a * value) := nth_error l. *)
Definition runtime_getVal (rΓ : r_env): Loc -> option value := nth_error (rΓ.(vars)).
Definition static_getType (sΓ: s_env): Loc -> option qualified_type := nth_error sΓ.

Fixpoint mapM {A B : Type} (f : A -> option B) (l : list A) : option (list B) :=
  match l with
  | [] => Some []
  | x :: xs =>
      match f x, mapM f xs with
      | Some y, Some ys => Some (y :: ys)
      | _, _ => None
      end
  end.

Definition static_getType_list (sΓ: s_env): list Loc -> option (list qualified_type) :=
  fun l => mapM (fun x => static_getType sΓ x) l.

Definition runtime_lookup_list (rΓ: r_env): list Loc -> option (list value) :=
  fun l => mapM (fun x => runtime_getVal rΓ x) l.

Lemma mapM_Some_forall :
  forall {A B} (f : A -> option B) xs ys,
    mapM f xs = Some ys ->
    Forall (fun x => exists y, f x = Some y) xs.
Proof.
  intros A B f xs.
  induction xs as [|x xs IH]; intros ys Hmap.
  - simpl in Hmap. inversion Hmap; subst. constructor.
  - simpl in Hmap.
    destruct (f x) eqn:Hfx; try discriminate.
    destruct (mapM f xs) eqn:Hxsm; try discriminate.
    inversion Hmap; subst.
    constructor.
    + eauto.  (* from Hfx *)
    + eapply IH; eauto.
Qed.

Lemma mapM_None_exists :
  forall {A B} (f : A -> option B) xs,
    mapM f xs = None ->
    exists x, List.In x xs /\ f x = None.
Proof.
  intros A B f xs.
  (* Generalize the hypothesis before induction *)
  revert f.
  induction xs as [|x xs IH]; intros f Hmap; simpl in Hmap.
  - discriminate.
  - destruct (f x) eqn:Hfx.
    + destruct (mapM f xs) eqn:Hmxs.
      * discriminate.
      * (* failure in tail *)
        destruct (IH f Hmxs) as [x' [Hin Hnone]].
        exists x'. split; [right; exact Hin | exact Hnone].
    + (* failure at head *)
      exists x. split; [left; reflexivity | exact Hfx].
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Local hints *)
Local Hint Unfold runtime_getObj runtime_getVal static_getType: updates.
(* ------------------------------------------------------------------------ *)
(** * Updates **)

Fixpoint forallb2 {A B} (f : A -> B -> bool) (l1 : list A) (l2 : list B) : bool :=
  match l1, l2 with
  | [], [] => true
  | x1 :: xs1, x2 :: xs2 => f x1 x2 && forallb2 f xs1 xs2
  | _, _ => false
  end.

Fixpoint update {X : Type} (position : nat) (value : X) (l : list X) : list X :=
  match l, position with
  | [], _ => []
  | _::t, 0 => value :: t
  | h::l', S n => h :: update n value l'
  end.
Notation "[ x ↦  v ] l" := (update x v l) (at level 0).

Fixpoint update_r_env_value (rΓ : r_env) (l : Loc) (v : value) : r_env :=
  match rΓ with
  {| vars := vars; |} => 
      {| vars := update l v vars;|}
  end.

(** ** Updates lemmas *)
Lemma update_same :
  forall X p v (l: list X),
    p < (length l) ->
    (nth_error [p ↦ v]l p) = Some v.
Proof.
  intros X p v; generalize dependent p.
  induction p; steps; eauto with lia.
Qed.
Global Hint Resolve update_same: updates.

Lemma runtime_getObj_update_same:
  forall h l O, l < dom h -> runtime_getObj ([l ↦ O]h) l = Some O.
Proof.
  eauto using update_same.
Qed.

(* Lemma runtime_getVal_update_same:
  forall ρ l v, l < dom ρ -> update_r_env_value ([l ↦ v]ρ) l = Some v.
Proof.
  eauto using update_same.
Qed. *)

Lemma static_getType_update_same:
  forall sΓ l T, l < dom sΓ -> static_getType ([l ↦ T]sΓ) l = Some T.
Proof.
  eauto using update_same.
Qed.

Lemma update_diff :
  forall X p p' v (l: list X),
    p <> p' ->
    (nth_error [p ↦ v]l p') = (nth_error l p').
Proof.
  induction p; intros; destruct l ; destruct p' => //.
  simpl; eauto.
Qed.
Global Hint Resolve update_diff: updates.

Lemma runtime_getObj_update_diff:
  forall h l l' O,
    l <> l' ->
    runtime_getObj ([l ↦ O]h) l' = runtime_getObj h l'.
Proof.
  eauto using update_diff.
Qed.

(* Lemma runtime_getVal_update_diff:
  forall ρ l l' v,
    l <> l' ->
    runtime_getVal ([l ↦ v]ρ) l' = runtime_getVal ρ l'.
Proof.
  eauto using update_diff.
Qed. *)

Lemma static_getType_update_diff:
  forall sΓ l l' T,
    l <> l' ->
    static_getType ([l ↦ T]sΓ) l' = static_getType sΓ l'.
Proof.
  eauto using update_diff.
Qed.

Lemma update_length :
  forall X p v (l: list X),
    length ([p ↦ v]l) = length l.
Proof.
  intros X.
  induction p; steps.
Qed.
Global Hint Resolve update_length: updates.

Lemma gget_dom :
  forall {X : Type} (l : list X) (C : Loc) x,
    gget l C = Some x -> C < length l.
Proof.
  unfold gget.
  intros. eapply nth_error_Some; eauto.
Qed.
Global Hint Resolve gget_dom: updates.

Lemma gget_not_dom :
  forall {X : Type} (l : list X) (C : Loc),
    gget l C = None -> C >= length l.
Proof.
  unfold gget.
  intros. eapply nth_error_None; eauto.
Qed.
Global Hint Resolve gget_not_dom: updates.

Lemma runtime_getObj_dom:
  forall l O h, runtime_getObj h l = Some O -> l < dom h.
Proof.
  unfold runtime_getObj.
  intros; eapply nth_error_Some; eauto.
Qed.
Global Hint Resolve runtime_getObj_dom: updates.

Lemma runtime_getObj_not_dom:
  forall l h, runtime_getObj h l = None -> l >= dom h.
Proof.
  unfold runtime_getObj.
  intros; eapply nth_error_None; eauto.
Qed.
Global Hint Resolve runtime_getObj_dom: updates.

Lemma getVal_dom:
  forall l v ρ, getVal ρ l = Some v -> l < dom ρ.
Proof.
  unfold getVal.
  intros; eapply nth_error_Some; eauto.
Qed.
Global Hint Resolve getVal_dom: updates.

Lemma getVal_not_dom:
  forall l ρ, getVal ρ l = None -> l >= dom ρ.
Proof.
  unfold getVal.
  intros; eapply nth_error_None; eauto.
Qed.
Global Hint Resolve getVal_not_dom: updates.

Lemma runtime_getVal_dom:
  forall l v ρ, runtime_getVal ρ l = Some v -> l < dom ρ.(vars).
Proof.
  unfold runtime_getVal.
  intros; eapply nth_error_Some; eauto.
Qed.
Global Hint Resolve runtime_getVal_dom: updates.

Lemma runtime_getVal_not_dom:
  forall l ρ, runtime_getVal ρ l = None -> l >= dom ρ.(vars).
Proof.
  unfold runtime_getVal.
  intros; eapply nth_error_None; eauto.
Qed.
Global Hint Resolve runtime_getVal_not_dom: updates.

Lemma static_getType_dom:
  forall l O sΓ, static_getType sΓ l = Some O -> l < dom sΓ.
Proof.
  unfold static_getType.
  intros; eapply nth_error_Some; eauto.
Qed.
Global Hint Resolve static_getType_dom: updates.

Lemma static_getType_not_dom:
  forall l sΓ, static_getType sΓ l = None -> l >= dom sΓ.
Proof.
  unfold static_getType.
  intros; eapply nth_error_None; eauto.
Qed.
Global Hint Resolve static_getType_not_dom: updates.

(* ------------------------------------------------------------------------ *)
(** ** Domains lemmas *)

Lemma runtime_getObj_Some : forall σ l,
    l < dom σ ->
    exists C ω, runtime_getObj σ l = Some (mkObj C ω).
Proof.
  intros.
  destruct (runtime_getObj σ l) as [[C ω]|] eqn:?.
  exists C, ω; auto.
  exfalso. eapply nth_error_None in Heqo. lia.
Qed.

(* Lemma getVal_Some : forall ρ f,
    f < dom ρ ->
    exists v, getVal ρ f = Some v.
Proof.
  intros.
  destruct (getVal ρ f) as [|] eqn:?; eauto.
  exfalso. eapply nth_error_None in Heqo. lia.
Qed. *)

Lemma static_getType_Some : forall sΓ l,
    l < dom sΓ ->
    exists T, static_getType sΓ l = Some T.
Proof.
  intros.
  destruct (static_getType sΓ l) as [|] eqn:?; eauto.
  exfalso. eapply nth_error_None in Heqo. lia.
Qed.


(* ------------------------------------------------------------------------ *)
(** ** Assignments *)

(* This function tries to add the new field of index x to an existing object, and does nothing if
the object already exists with not the right number of fields *)
Definition assign_new l x v h : option heap :=
  match (runtime_getObj h l) with
  | Some (mkObj C ω) => if (x =? length ω) then
                    Some [ l ↦ (mkObj C (ω++[v])) ]h
                  else
                    Some [ l ↦ (mkObj C [x ↦ v]ω) ]h
  | None => None (* Error : adding a field to non-existing object *)
end.

Lemma assign_new_dom:
  forall h l x v h',
    assign_new l x v h = Some h' ->
    dom h = dom h'.
Proof.
  unfold assign_new; steps; try rewrite update_length; done.
Qed.

(* Update heap with update in local env : update an already-existing field of an existing object *)
Definition assign l x v h : heap :=
  match (runtime_getObj h l) with
  | Some (mkObj C ω) => [ l ↦ (mkObj C [x ↦ v]ω)] h
  | None => h (* ? *)
  end.

(* ------------------------------------------------------------------------ *)
(** ** Class info *)

(* Definition fieldType C f :=
  match ct C with
  | class _ flds _  =>
      match nth_error flds f with
      | Some (field (T, μ) _) => Some (T, μ)
      | _ => None
      end
  end.

Definition methodInfo C m :=
  match ct C with
  | class _ _ methods =>
      match methods m with
      | None => None
      | Some (method μ Ts retT e) => Some (μ, Ts, retT, e)
      end
  end. *)


(* ------------------------------------------------------------------------ *)
(** ** Additions of new objects *)

Lemma runtime_getObj_last :
  forall σ C ρ,
    runtime_getObj (σ++[mkObj C ρ]) (dom σ) = Some (mkObj C ρ).
Proof.
  induction σ; steps.
Qed.
Global Hint Resolve runtime_getObj_last: core.

Lemma runtime_getObj_last2 :
  forall σ C ρ l,
    l < (dom σ) ->
    runtime_getObj (σ++[ mkObj C ρ ]) l = runtime_getObj σ l.
Proof.
  induction σ; simpl; intros; try lia.
  destruct l;
    steps;
    eauto with lia.
Qed.

Lemma static_getType_last :
  forall Σ T,
    static_getType (Σ++[T]) (dom Σ) = Some T.
Proof.
  induction Σ; steps.
Qed.
Global Hint Resolve static_getType_last: core.

Lemma static_getType_last2 :
  forall Σ T l,
    l < (dom Σ) ->
    static_getType (Σ++[T]) l = static_getType Σ l.
Proof.
  induction Σ; simpl; intros; try lia.
  destruct l;
    steps;
    eauto with lia.
Qed.

(* Lemma runtime_getObj_last_empty :
  forall σ C C' ω l f v,
    runtime_getObj (σ++[(C,[])]) l = Some (C', ω) ->
    getVal ω f = Some v ->
    runtime_getObj σ l = Some (C', ω) /\ l < dom σ.
Proof.
  intros.
  assert (l < dom (σ ++ [(C,[])])).
  {
    unfold getObj in *.
    eapply nth_error_Some.
    rewrite H; steps.
  }
  rewrite app_length in H1 ;
    simpl in H1;
    fold (dom σ) in H1;
    rewrite_anywhere PeanoNat.Nat.add_1_r.
  apply Nat.lt_eq_cases in H1 as [H1 | H1].
  + rewrite getObj_last2 in H; eauto with lia. 
  + inversion H1; subst.
    rewrite getObj_last in H.
    invert_constructor_equalities; steps;
      destruct f; steps.
Qed. *)

(* Lemma getVal_add:
  forall ω l l' f,
    getVal (ω ++ [l]) f = Some l' ->
    (f = length ω /\ l = l') \/ (f < length ω /\ getVal ω f = Some l').
Proof.
  unfold getVal.
  steps.
  assert (f < length ω \/ f = length ω) as [Hf | Hf] ;
    [
      apply Nat.lt_eq_cases, Nat.lt_succ_r;
      pose proof (nth_error_Some (ω ++ [l]) f) as Hf;
      rewrite app_length PeanoNat.Nat.add_1_r in Hf;
      apply Hf
    | rewrite_anywhere nth_error_app1
    | rewrite_anywhere nth_error_app2 ] ;
    steps;
    rewrite_anywhere PeanoNat.Nat.sub_diag; steps.
Qed. *)

(* Lemma getVal_last :
  forall ω v,
    getVal (ω++[v]) (dom ω) = Some v.
Proof.
  induction ω; steps.
Qed.
Global Hint Resolve getVal_last: core.

Lemma getVal_last2 :
  forall ω x v,
    x < (dom ω) ->
    getVal (ω++[v]) x = getVal ω x.
Proof.
  induction ω; simpl; intros; try lia.
  destruct x; steps;
    eauto with lia.
Qed. *)

Lemma Forall_nth_error {A} (P : A -> Prop) (l : list A) (n : nat) (x : A) :
  Forall P l ->
  nth_error l n = Some x ->
  P x.
Proof.
  revert l. induction n as [|n IH]; intros l HForall Hnth.
  - destruct l as [|y l']; simpl in *; [discriminate|].
    inversion Hnth; subst. inversion HForall; subst. assumption.
  - destruct l as [|y l']; simpl in *; [discriminate|].
    inversion HForall; subst.
    apply IH with (l := l'); assumption.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Tactics *)

(* Ltac ct_lookup C :=
  destruct (ct C) as [?Args ?Flds ?Mtds] eqn:?H__ct.

Ltac updates :=
  repeat
    match goal with
    (* appends *)
    |  |- context [ dom (_ ++ _) ] => rewrite app_length; simpl
    | H: context [ dom (_ ++ _) ] |- _ => rewrite app_length in H; simpl in H
    |  |- context [ dom ([_ ↦ _] _) ] => rewrite update_length
    | H: context [ dom ([_ ↦ _] _) ] |- _ => rewrite update_length in H

    (* assign_new *)
    | H: assign_new ?C ?v ?σ = Some ?σ' |- _ =>
        let H1 := fresh "H__dom" in
        add_hypothesis H1 (assign_new_dom σ C v σ' H)

    (* update_same *)
    | H: context [ getObj ([?l ↦ ?O]?σ) ?l = Some ?O'] |- _ =>
        let H1 := fresh "H__dom" in
        add_hypothesis H1 (getObj_dom _ _ _ H);
        rewrite update_length in H1;
        rewrite (getObj_update_same σ l O H1) in H;
        inverts H

    | |- context [ getObj ([?l ↦ ?O]?σ) ?l ] => rewrite (getObj_update_same σ l O)
    | |- context [ getType ([?l ↦ ?O]?σ) ?l ] => rewrite (getType_update_same σ l O)
    | |- context [ getVal ([?l ↦ ?O]?σ) ?l ] => rewrite (getVal_update_same σ l O)

    | H: context [ getVal ([?l ↦ ?O]?σ) ?l = Some ?O'] |- _ =>
        let H1 := fresh "H__dom" in
        add_hypothesis H1 (getVal_dom _ _ _ H);
        rewrite update_length in H1;
        rewrite (getVal_update_same σ l O H1) in H;
        inverts H


    (* update_diff *)
    | H1: ?l <> ?l',
        H2: context [ getObj ([?l ↦ ?O]?σ) ?l' ] |- _ => rewrite (getObj_update_diff σ l l' O H1) in H2
    | H1: ?l <> ?l' |-
        context [ getObj ([?l ↦ ?O]?σ) ?l' ] => rewrite (getObj_update_diff σ l l' O H1)

    | H1: ?l <> ?l',
        H2: context [ getVal ([?l ↦ ?O]?σ) ?l' ] |- _ => rewrite (getVal_update_diff σ l l' O H1) in H2
    | H1: ?l <> ?l' |-
        context [ getVal ([?l ↦ ?O]?σ) ?l' ] => rewrite (getVal_update_diff σ l l' O H1)

    | H1: ?l <> ?l',
        H2: context [ getType ([?l ↦ ?O]?σ) ?l' ] |- _ => rewrite (getType_update_diff σ l l' O H1) in H2
    | H1: ?l <> ?l' |-
        context [ getType ([?l ↦ ?O]?σ) ?l' ] => rewrite (getType_update_diff σ l l' O H1)

    (* get last *)
    | |- context [getObj (?σ ++ _) (dom ?σ) ] => rewrite getObj_last

    end.
Global Hint Extern 1 => updates: updates. *)


(* ------------------------------------------------------------------------ *)
(** ** Maps *)

(* Lemma dom_map:
  forall Σ (f: Tpe -> Tpe),
    dom (map (fun T => f T) Σ) = dom Σ.
Proof.
  intros.
  rewrite map_length. auto.
Qed.


Lemma getType_map:
  forall Σ f l T,
    getType Σ l = Some T ->
    getType (map (fun T => f T) Σ) l = Some (f T).
Proof.
  unfold getType. intros.
  rewrite nth_error_map H. steps.
Qed. *)

(* ------------------------------------------------------------------------ *)
(** ** List Loc *)

(* Ltac inSingleton :=
  match goal with
  | H: ?a ∈ Singleton Loc ?b |- _ => induction H
  | H: {?x} ?y |- _ => induction H
  end. *)


(* ------------------------------------------------------------------------ *)
(** ** Store Subset *)

(** A set of locations is contained in a store: [L ⪽ σ] *)
(* Definition storeSubset σ L :=
  forall l, l ∈ L -> l < dom σ. *)

(** The codomain of an environment is the set of locations it contains *)
(* Definition codom ρ : LocSet :=
  fun l => (List.In l ρ).

Notation "L ⪽ σ" := (storeSubset σ L) (at level 80).
Notation " a ∪ { b } " := (Union Loc a (Singleton Loc b)) (at level 80).
Notation "{ l } ⪽ σ" := (storeSubset σ (Singleton Loc l)) (at level 80).

Local Hint Unfold storeSubset: ss.
Global Hint Resolve Union_intror Union_introl In_singleton: core.

Lemma ss_trans :
  forall a s s',
    dom s <= dom s' ->
    a ⪽ s ->
    a ⪽ s'.
Proof.
  unfold storeSubset; steps.
  eapply H0 in H1 ; lia.
Qed.
Lemma ss_union :
  forall a b s,
    a ⪽ s ->
    b ⪽ s ->
    (a∪b) ⪽ s.
Proof.
  unfold storeSubset; intros.
  induction H1; eauto.
Qed.

Lemma ss_union_l :
  forall a b s,
    (a∪b) ⪽ s -> a ⪽ s.
Proof.
  eauto with ss.
Qed.

Lemma ss_union_r :
  forall a b s,
    (a∪b) ⪽ s -> b ⪽ s.
Proof.
  eauto with ss.
Qed.

Lemma ss_add :
  forall v a s,
    codom (v :: a) ⪽ s <-> v < dom s /\ codom a ⪽ s.
Proof.
  unfold codom, List.In, In, storeSubset in *; split.
  + steps; eapply_any; steps; right => //.
  + steps; move: H0 => [Hl|Hl]; steps.
Qed.

Lemma ss_singleton :
  forall a σ,
    a < dom σ -> {a} ⪽ σ.
Proof.
  unfold storeSubset; steps;
    induction H0 ; steps.
Qed.

Lemma ss_singleton_inv :
  forall a σ,
    {a} ⪽ σ -> a < dom σ.
Proof.
  unfold storeSubset; steps.
Qed.

Lemma ss_codom_empty : forall s, codom [] ⪽ s.
Proof.
  unfold storeSubset; steps.
Qed.
Global Hint Resolve ss_codom_empty: core.

Lemma codom_empty_union: forall a, (codom [] ∪ a) = a.
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included;
    repeat steps || destruct H;
    eauto with ss.
Qed.

Lemma codom_cons:
  forall a ρ, codom (a::ρ) = ({a} ∪ (codom ρ)).
Proof.
  intros; apply Extensionality_Ensembles.
  unfold Same_set; steps; intros l; steps; try inversion H; steps;
    try inSingleton;
    eauto using Union_introl, Union_intror.
Qed.

Lemma ss_update:
  forall L l o σ,
    L ⪽ [l ↦ o] (σ) -> L ⪽ σ.
Proof.
  unfold storeSubset; steps; updates; eauto.
Qed.

Lemma ss_update_inv:
  forall L l o σ,
     L ⪽ σ -> L ⪽ [l ↦ o] (σ).
Proof.
  unfold storeSubset; steps; updates; eauto.
Qed.

Lemma getVal_codom : forall x l ρ,
    getVal ρ x = Some l -> l ∈ codom ρ.
Proof.
  intros.
  eapply nth_error_In in H. auto.
Qed.
Global Hint Resolve getVal_codom: ss.

Ltac ss_trans :=
  repeat match goal with
         | H: dom ?s <= dom ?s' |- ?a ⪽ ?s => apply (ss_trans a s s' H)
         | H: dom ?s <= dom ?s', H': ?a ⪽ ?s |- ?a ⪽ ?s' => apply (ss_trans a s s' H)
         end.

Ltac ss_union :=
  try match goal with
  | |- (?a ∪ ?b) ⪽ ?s => apply ss_union
  | H1: (?a ∪ ?b) ⪽ ?s |- ?a ⪽ ?s => apply (ss_union_l a b s H1)
  | H1: (?a ∪ ?b) ⪽ ?s |- ?b ⪽ ?s => apply (ss_union_r a b s H1)
  end.

Ltac ss :=
  ss_trans;
  repeat match goal with
         | H: { ?a } ⪽ ?σ |- _ => apply ss_singleton_inv in H
         | |- { ?a } ⪽ ?σ => apply ss_singleton
         | |- ?L ⪽ [?l ↦ ?o] ?σ => apply ss_update_inv
         | H: ?a ∪ {?l} ⪽ ?σ |- ?l < dom ?σ => apply ss_singleton_inv, ss_union_r with a, H
         | H: {?l} ∪ ?b ⪽ ?σ |- ?l < dom ?σ => apply ss_singleton_inv, ss_union_l with b, H
         end || ss_union.
Global Hint Extern 1 => ss : core. *)


(* ------------------------------------------------------------------------ *)
(** ** Finite sets results **)

(* Lemma storeSubset_finite: forall σ L,
    L ⪽ σ ->
    Finite Loc L.
Proof.
  induction σ; steps.
  - assert (L = Empty_set Loc); subst; eauto using Empty_is_finite.
    apply Extensionality_Ensembles.
    unfold Same_set, Included; steps; try specialize (H x); steps; try lia.
    inversion H0.
  - assert ((Subtract Loc L (dom σ)) ⪽ σ).
    + intros l; steps.
      inverts H0.
      specialize (H l H1). simpl in H.
      assert (l < dom σ \/ l = dom σ) as [ ] by lia; steps.
      exfalso. apply H2.
      steps.
    + apply IHσ in H0.
      apply Finite_downward_closed with (A:= Union Loc ( (Subtract Loc L dom σ)) ({dom σ})).
      apply Union_preserves_Finite; eauto using Singleton_is_finite.
      intros l; steps.
      destruct_eq (l = dom σ); eauto.
      * apply Union_intror; steps.
      * apply Union_introl; steps.
        unfold Subtract, Setminus, In.
        split; steps. apply Heq. inSingleton. steps.
Qed.

Lemma finite_sets_ind: forall {T: Type} (P: (Ensemble T) -> Prop),
    (P (Empty_set T)) ->
    (forall (F: Ensemble T) (a:T), Finite T F -> P F -> P (Add T F a)) ->
    (forall (F: Ensemble T), Finite T F -> P F).
Proof.
  intros.
  apply Generalized_induction_on_finite_sets; eauto.
  intros.
  induction H2; eauto.
  eapply H0; eauto.
  apply IHFinite.
  intros.
  apply H3.
  unfold Strict_Included, Included, In, Add in *; steps.
  - apply Union_introl; eauto.
    apply H6; eauto.
  - apply H7, Extensionality_Ensembles.
    unfold Same_set, Included; steps.
Qed. *)


(* ------------------------------------------------------------------------ *)
(** ** FieldType *)

(* Lemma fieldType_exists: forall C Args Flds Mtds f,
    ct C = class Args Flds Mtds ->
    f < dom Flds ->
    exists D μ, fieldType C f = Some (D, μ).
Proof.
  intros.
  destruct (fieldType C f) as [[D μ] |] eqn:?; eauto.
  unfold fieldType in *.
  steps.
  apply nth_error_None in matched0. lia.
Qed.

Lemma fieldType_some : forall C Args Flds Mtds f T,
    ct C = class Args Flds Mtds ->
    fieldType C f = Some T ->
    f < dom Flds.
Proof.
  intros.
  unfold fieldType in *. steps.
  eapply nth_error_Some; eauto.
Qed.
Global Hint Resolve fieldType_some: typ. *)


(* ------------------------------------------------------------------------ *)
(** ** List lemmas *)

(* Lemma app_inv_tail_length:
  forall (A: Type) (l l' l1 l2: list A),
    l++l1 = l'++l2 ->
    length l = length l' ->
    l1 = l2.
Proof.
  induction l; steps.
  - symmetry in H0.
    apply length_zero_iff_nil in H0.
    steps.
  - destruct l'; steps; eauto.
Qed. *)

(* Static helpers *)

(* Find a class declaration in the class table *)
Definition find_class (CT : class_table) (C : class_name) : option class_def :=
    gget CT C.

Lemma find_class_dom : forall CT C x,
  find_class CT C = Some x -> C < dom CT.
Proof.
  intros. unfold find_class in H. apply gget_dom in H. exact H.
Qed.

Lemma find_class_not_dom: forall CT C,
  find_class CT C = None -> C >= dom CT.
Proof.
  intros CT C H.
  unfold find_class in H.
  apply gget_not_dom in H.
  exact H.
Qed.

(* Class bound look up in the class table  *)
Definition bound (CT : class_table) (C : class_name) : option q_c :=
  match find_class CT C with
  | Some decl => Some (class_qualifier (signature decl))
  | None => None
  end.

(* Parent class lookup in the class table *)
Definition parent (CT : class_table) (C : class_name) : option class_name :=
  match find_class CT C with
  | Some def => super (signature def)
  | None => None
  end.
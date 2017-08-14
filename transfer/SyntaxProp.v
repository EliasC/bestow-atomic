Require Import List.

Require Export Syntax.
Require Import Shared.

(*
================
freeX properties
================
*)

Lemma freeLocs_ctx :
  forall e l ctx,
    is_econtext ctx ->
    In l (freeLocs e) ->
    In l (freeLocs (ctx e)).
Proof with eauto using in_or_app.
  introv Hctx H.
  inv Hctx; simpls...
Qed.

Lemma freeIds_ctx :
  forall e id ctx,
    is_econtext ctx ->
    In id (freeIds e) ->
    In id (freeIds (ctx e)).
Proof with eauto using in_or_app.
  introv Hctx H.
  inv Hctx; simpls...
Qed.

Lemma freeTIds_ctx :
  forall e l ctx,
    is_econtext ctx ->
    In l (freeTIds e) ->
    In l (freeTIds (ctx e)).
Proof with eauto using in_or_app.
  introv Hctx H.
  inv Hctx; simpls...
Qed.

Lemma subst_not_in :
  forall e x v,
    ~ In x (freeVars e) ->
    subst x v e = e.
Proof with eauto using remove_not_in_neq.
  introv HnIn.
  expr_cases(induction e) Case; simpls...
  + cases_if... contradict HnIn...
  + apply not_in_app in HnIn as [HnIn1 HnIn2]. crush.
  + apply not_in_app in HnIn as [HnIn1 HnIn2]. cases_if.
    - crush.
    - rewrite IHe1... rewrite IHe2...
  + rewrite IHe...
  + cases_if...
    rewrite IHe...
Qed.

Lemma freeLocs_subst :
  forall e v x,
    freeLocs e = nil ->
    freeLocs v = nil ->
    freeLocs (subst x v e) = nil.
Proof with eauto.
  introv eFree vFree.
  induction e; simpls...
  + cases_if...
  + apply app_eq_nil in eFree as (eFree1 & eFree2).
    rewrite IHe1...
  + apply app_eq_nil in eFree as (eFree1 & eFree2).
    rewrite IHe1...
    cases_if...
  + cases_if...
Qed.

Lemma freeLocs_subst_in :
  forall l x v e,
    In l (freeLocs (subst x v e)) ->
    In l (freeLocs v) \/ In l (freeLocs e).
Proof with eauto using in_or_app.
  introv HIn.
  expr_cases(induction e) Case; simpls...
  + cases_if...
  + apply in_app_or in HIn.
    inv HIn; crush.
  + apply in_app_or in HIn.
    inv HIn; crush.
    cases_if; crush.
  + cases_if...
Qed.

Lemma freeIds_subst_in :
  forall l x v e,
    In l (freeIds (subst x v e)) ->
    In l (freeIds v) \/ In l (freeIds e).
Proof with eauto using in_or_app.
  introv HIn.
  induction e; simpls...
  + cases_if...
  + apply in_app_or in HIn.
    inv HIn; crush.
  + apply in_app_or in HIn.
    inv HIn; crush.
    cases_if; crush.
  + cases_if...
Qed.

Lemma freeTIds_subst_in :
  forall l x v e,
    In l (freeTIds (subst x v e)) ->
    In l (freeTIds v) \/ In l (freeTIds e).
Proof with eauto using in_or_app.
  introv HIn.
  induction e; simpls...
  + cases_if...
  + apply in_app_or in HIn.
    inv HIn; crush.
  + apply in_app_or in HIn.
    inv HIn; crush.
    cases_if; crush.
  + cases_if...
Qed.

(*
===============
Heap properties
===============
*)

Lemma heapLookup_nil :
  forall l,
    heapLookup nil l = None.
Proof with auto.
  intros. destruct l...
Qed.

Lemma heapLookup_not_none :
  forall H id,
    heapLookup H id <> None <->
    exists a, heapLookup H id = Some a.
Proof with eauto.
  intros.
  destruct (heapLookup H id) as [[]|]; crush...
Qed.

Lemma heapLookup_lt :
  forall H id,
    id < length H <->
    exists a, heapLookup H id = Some a.
Proof with auto with arith.
  intros H. induction H; intros.
  + rewrite heapLookup_nil; crush.
  + split.
    - destruct id; simpl.
      * repeat eexists...
      * introv Hlt. apply Lt.lt_S_n in Hlt. apply IHlist...
    - destruct id; simpl...
      intros Hex. apply IHlist in Hex...
Qed.

Corollary heapLookup_lt' :
  forall H id a,
    heapLookup H id = Some a ->
    id < length H.
Proof with eauto.
  introv Hlookup. eapply heapLookup_lt...
Qed.

Hint Resolve heapLookup_lt'.

Corollary LH_lt :
  forall id H L,
    LH H id = Some L ->
    id < length H.
Proof with eauto.
  introv HLH.
  unfolds LH.
  remember (heapLookup H id) as lkp.
  destruct lkp...
Qed.

Hint Resolve LH_lt.

Lemma heapLookup_ge :
  forall H id,
    id >= length H <->
    heapLookup H id = None.
Proof with auto using heapLookup_nil with arith.
  split.
  + gen id.
    induction H; destruct id; crush.
  + gen id.
    induction H; introv Hlookup; destruct id; crush.
    apply IHlist in Hlookup...
Qed.

Lemma heapLookup_snoc :
  forall H id obj,
    id < length H ->
    heapLookup H id = heapLookup (snoc H obj) id.
Proof with auto with arith.
  intros H. induction H; introv Hlt.
  + inv Hlt.
  + simpl. destruct id; crush.
Qed.

Lemma heapLookup_in :
  forall H id a,
    heapLookup H id = Some a ->
    List.In a H.
Proof with auto.
  intros H.
  induction H; introv Hlookup.
  + destruct id; inv Hlookup.
  + destruct id as [| id']; simpls.
    - inv Hlookup...
    - right. apply IHlist with id'...
Qed.

Lemma heapExtend_lookup_len :
  forall H a,
    heapLookup (heapExtend H a) (length H) = Some a.
Proof with auto.
  intros H. induction H; crush.
Qed.

Lemma heapExtend_lookup_nlen :
  forall H a id,
    id <> length H ->
    heapLookup (heapExtend H a) id = heapLookup H id.
Proof with auto using heapLookup_nil.
  intros H. unfold heapExtend.
  induction H; introv Hneq; simpls; destruct id; crush...
Qed.

Lemma heapUpdate_nil :
  forall l a,
    heapUpdate nil l a = nil.
Proof.
  auto.
Qed.

Lemma heapUpdate_length :
  forall H id obj,
    length (heapUpdate H id obj) = length H.
Proof with auto.
  intros. gen id.
  induction H; destruct id; crush.
Qed.

Lemma lookup_heapUpdate_eq :
  forall H id obj,
    id < length H ->
    heapLookup (heapUpdate H id obj) id = Some obj.
Proof with auto.
  introv Hlt. unfolds. gen id.
  induction H as [|obj' H']; intros.
  + inv Hlt.
  + destruct id; crush.
Qed.

Lemma lookup_heapUpdate_neq :
  forall H id1 id2 a,
    id1 <> id2 ->
    heapLookup (heapUpdate H id2 a) id1 = heapLookup H id1.
Proof with auto using heapUpdate_nil.
  unfold heapLookup. intros H id1. gen H.
  induction id1 as [|id1']; introv Hneq.
  + destruct H as [|a' H']...
    destruct id2... contradict Hneq...
  + destruct H as [|a' H'];
    destruct id2; crush.
Qed.

Lemma heapUpdate_in :
  forall a a' H id,
    In a (heapUpdate H id a') ->
    In a H \/ a = a'.
Proof with auto using in_cons, in_eq.
  introv HIn. gen id. induction H; intros.
  + inv HIn.
  + simpls. destruct id.
    - inv HIn...
    - inv HIn as [|HIn']...
      apply IHlist in HIn'.
      inv HIn'...
Qed.

(*
================
Tactics
================
*)

Ltac inv_ctx :=
  match goal with
    | H1 : is_econtext ?ctx, H2 : ?ctx _ = _ |- _ =>
        inv H1; inv H2; eauto
  end.

Ltac heap_rewrite :=
  match goal with
    (* Looking up the updated actor in the heap *)
    | _ : _ |- context[heapLookup (heapUpdate _ ?id _) ?id] =>
      rewrite lookup_heapUpdate_eq;
      try rewrite_and_invert; eauto
    | H : context[heapLookup (heapUpdate _ ?id _) ?id] |- _ =>
      rewrite lookup_heapUpdate_eq in H;
      try rewrite_and_invert; eauto

    (* Not looking up the updated actor in the heap *)
    | _ : ?id1 <> ?id2 |- context[heapLookup (heapUpdate _ ?id1 _) ?id2] =>
      rewrite lookup_heapUpdate_neq;
      try rewrite_and_invert; eauto
    | _ : ?id1 <> ?id2 |- context[heapLookup (heapUpdate _ ?id2 _) ?id1] =>
      rewrite lookup_heapUpdate_neq;
      try rewrite_and_invert; eauto
    | _ : ?id1 <> ?id2,
      H : context[heapLookup (heapUpdate _ ?id1 _) ?id2] |- _ =>
      rewrite lookup_heapUpdate_neq in H;
      try rewrite_and_invert; eauto
    | _ : ?id1 <> ?id2,
      H : context[heapLookup (heapUpdate _ ?id2 _) ?id1] |- _ =>
      rewrite lookup_heapUpdate_neq in H;
      try rewrite_and_invert; eauto

    (* Using the known results of a heap lookup *)
    | H1 : heapLookup ?H ?id = _,
      H2 : context[heapLookup ?H ?id] |- _ =>
      rewrite H1 in H2
    | H1 : heapLookup ?H ?id = _ |- context[heapLookup ?H ?id] =>
      rewrite H1

    (* Looking up the newly added actor *)
    | H1 : context[heapLookup (heapExtend ?H _) (length ?H)] |- _ =>
      rewrite heapExtend_lookup_len in H1; eauto
    | _ : _ |- context[heapLookup (heapExtend ?H _) (length ?H)] =>
      rewrite heapExtend_lookup_len; eauto

    (* Not looking up the newly added actor *)
    | _  : ?id <> length ?H,
      H1 : context[heapLookup (heapExtend ?H _) ?id] |- _ =>
      rewrite heapExtend_lookup_nlen in H1; eauto;
      try solve[assert (id < length H); eauto; omega]
    | _  : ?id <> length ?H,
      _ : _ |- context[heapLookup (heapExtend ?H _) ?id] =>
      rewrite heapExtend_lookup_nlen; eauto;
      try solve[assert (id < length H); eauto; omega]
    | _  : ?id < length ?H,
      H1 : context[heapLookup (heapExtend ?H _) ?id] |- _ =>
      rewrite heapExtend_lookup_nlen in H1; eauto; try omega
    | _  : ?id < length ?H,
      _ : _ |- context[heapLookup (heapExtend ?H _) ?id] =>
      rewrite heapExtend_lookup_nlen; eauto; try omega

    (* Length rewrites *)
    | H : context[length (heapUpdate _ _ _)] |- _ =>
      rewrite heapUpdate_length in H; try omega
    | _ : _ |- context[length (heapUpdate _ _ _)] =>
      rewrite heapUpdate_length; try omega
    | H : context[length (heapExtend _ _)] |- _ =>
      unfolds heapExtend; rewrite snoc_length in H;
      try rewrite snoc_length; try omega
    | _ : _ |- context[length (heapExtend _ _)] =>
      unfolds heapExtend; rewrite snoc_length; try omega

    (* Absurd lookup *)
    | _ : context[heapLookup ?H (length ?H)] |- _ =>
      assert (length H < length H); eauto; omega

    | _ =>
      fail 1 "Found no heap relations to rewrite"
  end.

Tactic Notation "heap_case_core" :=
  unfolds LH;
  repeat heap_rewrite;
  repeat inv_eq.

Tactic Notation "heap_case" ident(id1) ident(id2) :=
  destruct (id_eq_dec id1 id2); subst;
  heap_case_core.

Tactic Notation "heap_case'" ident(id1) constr(len) :=
  destruct (id_eq_dec id1 len); subst;
  heap_case_core.

Ltac hauto :=
  match goal with
    (* heapUpdate in conclusion *)
    | _ : _ |- context[heapLookup (heapUpdate _ ?id1 _) ?id2] =>
      heap_case id1 id2
    | _ : _ |- context[LH (heapUpdate _ ?id1 _) ?id2] =>
      heap_case id1 id2

    (* heapUpdate in premise *)
    | _ : context[heapLookup (heapUpdate _ ?id1 _) ?id2] |- _ =>
      heap_case id1 id2
    | _ : context[LH (heapUpdate _ ?id1 _) ?id2] |- _ =>
      heap_case id1 id2

    (* heapExtend in conclusion *)
    | _ : _ |- context[heapLookup (heapExtend ?H _) ?id] =>
      heap_case' id (length H)
    | _ : _ |- context[LH (heapExtend ?H _) ?id] =>
      heap_case' id (length H)

    (* heapExtend in premise *)
    | H1 : context[heapLookup (heapExtend ?H _) ?id] |- _ =>
      heap_case' id (length H)
    | H1 : context[LH (heapExtend ?H _) ?id] |- _ =>
      heap_case' id (length H)

    (* try to rewrite *)
    | _ => repeat heap_rewrite
  end; eauto.

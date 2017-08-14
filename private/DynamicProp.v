Require Export Dynamic.
Require Import SyntaxProp.
Require Import MapProp.

Lemma step_preserves_this :
  forall id M M' H H' n n' e e' l L C Q,
    (exists e, heapLookup H id = Some (l, L, C, Q, e)) ->
    id / (M, H, n); e ==> (M', H', n'); e' ->
    exists L' C' Q' e'', heapLookup H' id = Some (l, L', C', Q', e'').
Proof with hauto.
  introv Hex Hstep.
  gen e'.
  inv Hex as [e' Hlookup].
  expr_cases (induction e) Case; intros;
    inv Hstep; try solve[inv_ctx]...
Qed.

Lemma monotonic_heap :
  forall id M M' H H' n n' e e',
    id / (M, H, n); e ==> (M', H', n'); e' ->
    length H <= length H'.
Proof with hauto.
  introv Hstep.
  gen Hstep. gen e'.
  expr_cases(induction e) Case; intros;
    inv Hstep; try solve[inv_ctx]...
Qed.

Lemma monotonic_local_heap :
  forall id id' M M' H H' n n' e e' L L' l,
    id / (M, H, n); e ==> (M', H', n'); e' ->
    LH H id' = Some L ->
    LH H' id' = Some L' ->
    In l L ->
    In l L'.
Proof with (hauto; eauto using in_cons).
  introv Hstep HLH1 HLH2 HIn.
  gen e'.
  expr_cases (induction e) Case;
    intros; inv Hstep; simpls;
    try inv_ctx;
    try rewrite_and_invert...
  + Case "ENew".
    destruct (heapLookup H id')...
    destruct_actor a...
Qed.

Lemma new_locs_in_local_heap :
  forall id M M' H H' n n' L L' e e',
    id / (M, H, n); e ==> (M', H', n'); e' ->
    LH H id = Some L ->
    LH H' id = Some L' ->
    (forall l, In l (freeLocs e) -> In l L) ->
    (forall l, In l (freeLocs e') -> In l L').
Proof with eauto using in_or_app.
  introv Hstep HLH1 HLH2 HIn HIn'.
  assert (forall l, In l L -> In l L') as Hmono.
    intros; eapply monotonic_local_heap...
  gen e'.
  expr_cases (induction e) Case;
    intros; inv Hstep; simpls;
    try inv_ctx;
    try contradiction;
    simpls;
    try solve [
          first [apply in_app_or in HIn'|
                 apply freeLocs_subst_in in HIn'];
          inv HIn'; eauto using in_or_app]...
  + Case "ENew".
    inv HIn'; try contradiction.
    hauto.
    constructors...
Qed.

Lemma new_ids_in_heap :
  forall id M M' H H' n n' e e',
    id / (M, H, n); e ==> (M', H', n'); e' ->
    (forall id, In id (freeIds e) -> id < length H) ->
    (forall id', In id' (freeIds e') -> id' < length H').
Proof with (hauto; eauto using in_or_app, monotonic_heap).
  introv Hstep Hid HIn.
  assert (length H <= length H') as Hmono...
  gen e'.
  expr_cases (induction e) Case;
    intros; inv Hstep; simpls;
    try inv_ctx;
    try rewrite_and_invert; simpls;
    try (first [apply in_app_or in HIn
               |apply freeIds_subst_in in HIn];
         inv HIn);
    try contradiction;
    try (assert (id' < length H) by eauto using in_or_app; omega)...
Qed.

Lemma bid_actors_in_heap :
  forall id id' M M' H H' n n' e e' l,
    id / (M, H, n); e ==> (M', H', n'); e' ->
    id < length H ->
    (forall l id'', In (l, id'') (freeBIds e) -> id'' < length H) ->
    In (l, id') (freeBIds e') ->
    id' < length H.
Proof with eauto using in_or_app, monotonic_heap.
  introv Hstep Hlt HBId HIn.
  gen e'.
  expr_cases (induction e) Case;
    intros; inv Hstep; simpls;
    try inv_ctx; simpls;
    try contradiction;
    try solve[
          first[apply in_app_or in HIn
               |apply freeBIds_subst_in in HIn];
          inv HIn; eauto using in_or_app]...
  + Case "EBes". inv HIn... inv H. omega.
Qed.

Lemma bid_loc_in_local_heap :
  forall id id' M M' H H' n n' e e' l L L' L'',
    id / (M, H, n); e ==> (M', H', n'); e' ->
    (forall l', In l' (freeLocs e) -> In l' L'') ->
    (forall l' id'',
        In (l', id'') (freeBIds e) ->
        id'' < length H /\
        LH H id'' = Some L -> In l' L) ->
    In (l, id') (freeBIds e') ->
    LH H id' = Some L ->
    LH H' id' = Some L' ->
    LH H id = Some L'' ->
    In l L'.
Proof with eauto using in_or_app.
  introv Hstep Hloc HBId HIn HLH HLH' HLH''.
  gen e'. gen L''.
  expr_cases (induction e) Case;
    intros; inv Hstep; simpls;
    try inv_ctx; simpls;
    try contradiction;
    try rewrite_and_invert;
    try solve[apply in_app_or in HIn;
              inv HIn;
              try solve[eapply IHe1 with (L'' := L'');
                        eauto using in_or_app
                       |eapply IHe2 with (L'' := L'');
                        eauto using in_or_app];
              try eapply monotonic_local_heap;
              try eapply HBId;
              eauto using in_or_app]...
  + Case "EApp".
    eapply freeBIds_subst_in in HIn. inv HIn; eapply HBId...
  + Case "EBes".
    inv HIn; try contradiction.
    inv H...
    repeat rewrite_and_invert...
Qed.

Lemma step_footprint :
  forall id id' M M' H H' n n' e e' e'' l L C Q,
    id / (M, H, n); e ==> (M', H', n'); e' ->
    heapLookup H' id' = Some (l, L, C, Q, e'') ->
    (exists L C Q, heapLookup H id' = Some (l, L, C, Q, e'')) \/
    e'' = EUnit /\ In l L.
Proof with hauto.
  introv Hstep Hlookup.
  gen e'.
  expr_cases (induction e) Case;
    intros; inv Hstep; simpls;
    try inv_ctx...
  + Case "ENew".
    right. splits... constructors...
Qed.

Lemma step_local_heap_neq :
  forall id id' M M' H H' n n' e e' L,
    id / (M, H, n); e ==> (M', H', n'); e' ->
    LH H' id' = Some L ->
    id <> id' ->
    id' < length H ->
    LH H id' = Some L.
Proof with hauto.
  introv Hstep HLH Hneq Hlt.
  gen e'. gen H.
  expr_cases (induction e) Case;
    intros; inv Hstep; simpls;
    try inv_ctx;
    hauto;
    try contradiction;
    try omega...
Qed.

Lemma step_id_lt :
  forall id id' M M' H H' n n' e e' L,
    id / (M, H, n); e ==> (M', H', n'); e' ->
    LH H' id' = Some L ->
    id' < length H \/ id' = length H /\ L = n :: nil.
Proof with hauto.
  introv Hstep HLH.
  gen e'. gen L.
  expr_cases (induction e) Case;
    intros; inv Hstep; simpls;
    try inv_ctx...
Qed.

Lemma step_single_allocation :
  forall id id' M M' H H' n n' e e',
    id / (M, H, n); e ==> (M', H', n'); e' ->
    length H < length H' ->
    id' < length H ->
    LH H' id' = LH H id'.
Proof with (hauto; try omega).
  introv Hstep Hlt Hlt'.
  gen e'. gen H.
  expr_cases (induction e) Case;
    intros; inv Hstep; simpls;
    try inv_ctx...
Qed.

Lemma step_allocates_n :
  forall id id' M M' H H' n n' e e' L,
    id / (M, H, n); e ==> (M', H', n'); e' ->
    LH H id' = Some L ->
    LH H' id' = Some L \/ LH H' id' = Some (n :: L).
Proof with hauto.
  introv Hstep HLH.
  gen e'. gen H.
  expr_cases (induction e) Case;
    intros; inv Hstep;
    try inv_ctx...
Qed.

Lemma monotonic_fresh :
  forall id M M' H H' n n' e e',
    id / (M, H, n); e ==> (M', H', n'); e' ->
    n <= n'.
Proof with eauto.
  introv Hstep.
  gen e'.
  expr_cases (induction e) Case;
    intros; inv Hstep; simpls;
    try inv_ctx...
Qed.

Lemma step_conversation_neq :
  forall id id' M M' H H' n n' e e' C,
    id / (M, H, n); e ==> (M', H', n'); e' ->
    conv H' id' = Some C ->
    id <> id' ->
    id' < length H ->
    conv H id' = Some C.
Proof with hauto.
  introv Hstep Hconv Hneq Hlt.
  gen e'. gen H.
  expr_cases (induction e) Case;
    intros; inv Hstep; simpls;
    try inv_ctx;
    hauto;
    try contradiction;
    try omega...
Qed.

Lemma step_conv_lt :
  forall id id' M M' H H' n n' e e' C,
    id / (M, H, n); e ==> (M', H', n'); e' ->
    conv H' id' = Some C ->
    id' < length H \/ id' = length H /\ forall id, C id = None.
Proof with hauto.
  introv Hstep HLH.
  gen e'. gen C.
  expr_cases (induction e) Case;
    intros; inv Hstep; simpls;
    try inv_ctx; hauto;
    try solve [left; eapply heapLookup_lt; destruct (heapLookup H id'); hauto
              |left; eapply heapLookup_lt; destruct (heapLookup H' id'); hauto]...
Qed.

Lemma step_conversation_effect :
  forall id M M' H H' n n' e e' C C',
    id / (M, H, n); e ==> (M', H', n'); e' ->
    conv H id = Some C ->
    conv H' id = Some C' ->
    (forall id qid,
        C' id = Some qid ->
        C id = Some qid \/ qid = n /\ M' qid = Some (nil, id)).
Proof with eauto.
  introv Hstep Hconv Hconv'.
  gen e'. gen H.
  expr_cases (induction e) Case;
    intros; inv Hstep; simpls;
    try inv_ctx;
    try rewrite_and_invert;
    try solve[hauto
             |rewrite_and_invert].
  + Case "ENew".
    hauto. inv H0.
    rewrite_and_invert.
  + Case "EAtStart".
    hauto.
    - unfold extend in H0.
      cases_if... inv_eq...
    - unfold extend in H0.
      cases_if... inv_eq...
  + Case "EAtStart".
    hauto.
    - unfold extend in H0.
      cases_if... inv_eq...
    - unfold extend in H0.
      cases_if... inv_eq...
  + Case "EAtEnd".
    hauto.
    - unfold drop in H0.
      cases_if...
    - unfold drop in H0.
      cases_if...
  + Case "EAtEnd".
    hauto.
    - unfold drop in H0.
      cases_if...
    - unfold drop in H0.
      cases_if...
Qed.

Require Export WellFormedness.
Require Import SyntaxProp.
Require Import StaticProp.
Require Import DynamicProp.
Require Import MapProp.

Lemma wf_actor_ctx :
  forall M H id l L C Q e ctx,
    is_econtext ctx ->
    wf_actor M H id (l, L, C, Q, ctx e) ->
    wf_actor M H id (l, L, C, Q, e).
Proof with eauto using hasType_ctx, freeLocs_ctx, freeIds_ctx, freeBIds_ctx.
  introv Hctx wfActor.
  inverts wfActor as (t & hasType).
  constructors...
Qed.

Lemma wf_msg_heapExtend :
  forall M H L id msg a,
    wf_msg M H L id msg ->
    wf_msg M (heapExtend H a) L id msg.
Proof with (hauto; eauto using wf_msg).
  introv wfMsg.
  inverts wfMsg as Hex Hloc HId HBId...
  constructors...
  + Case "Ids well-formed". crush.
  + Case "BIds well-formed".
    introv HIn.
    eapply HBId in HIn as [Hlt HBloc].
    splits...
    intros...
Qed.

Lemma wf_actor_heapExtend :
  forall M H id a a',
    wf_actor M H id a ->
    wf_actor M (heapExtend H a') id a.
Proof with (hauto; eauto using wf_msg_heapExtend).
  introv wfA.
  inverts wfA as Hthis wfQueue [t hasType] Hloc HId HBId.
  constructors...
  + Case "Ids well-formed". crush.
  + introv HIn.
    eapply HBId in HIn as [Hlt HBloc].
    split...
    intros...
Qed.

Lemma wf_actors_heapExtend :
  forall M H l L Q e id a,
    (forall id a, heapLookup H id = Some a -> wf_actor M H id a) ->
    wf_actor M H (length H) (l, L, Q, e) ->
    heapLookup (heapExtend H (l, L, Q, e)) id = Some a ->
    wf_actor M (heapExtend H (l, L, Q, e)) id a.
Proof with (hauto; eauto using wf_actor_heapExtend).
  introv wfH wfA Hlookup...
Qed.

Lemma wf_queue_heapUpdate :
  forall M H l L L' C' Q Q' e id id' l0 L0 P0 Q0 e0,
    (forall id a, heapLookup H id = Some a -> wf_actor M H id a) ->
    wf_queue M H L id Q ->
    heapLookup H id' = Some (l0, L0, P0, Q0, e0) ->
    (forall l, In l L0 -> In l L') ->
    wf_queue M (heapUpdate H id' (l, L', C', Q', e)) L id Q.
Proof with (hauto; eauto using wf_msg).
  introv wfActors wfQueue Hlookup Hmono.
  introv HIn.
  apply wfQueue in HIn as wfMsg.
  inverts wfMsg as Hex Hloc HId HBId...
  constructors...
  introv HIn'.
  eapply HBId in HIn' as [Hlt HBloc]...
  splits...
  introv HLH. inv_eq...
Qed.

Lemma wf_queue_snoc :
  forall M H L id Q msg,
    wf_queue M H L id Q ->
    wf_msg M H L id msg ->
    wf_queue M H L id (snoc Q msg).
Proof with eauto.
  introv wfQueue wfMsg.
  induction Q; simpls...
  + unfolds; crush.
  + unfolds wf_queue. introv HIn.
    inv HIn; crush.
Qed.

Lemma wf_heap_heapUpdate :
  forall M H l l' L C Q Q' e e' id,
    wf_heap M H ->
    heapLookup H id = Some (l, L, C, Q, e) ->
    wf_actor M H id (l', L, C, Q', e') ->
    local_heap_disjointness H ->
    conversation_disjointness H ->
    wf_heap M (heapUpdate H id (l', L, C, Q', e')).
Proof with (hauto; eauto using wf_queue_heapUpdate).
  introv wfH Hlookup wfActor Hdisj HCdisj.
  assert (id < length H)...
  constructors.
  + introv Hneq HLH1 HLH2 HIn.
    hauto; eapply Hdisj...
  + introv Hneq Hconv1 Hconv2 HC1 HC2.
    eapply HCdisj; eauto; hauto.
  + introv Hlookup'. inverts wfH as _ _ wfActors...
    - inverts wfActor as Hthis wfQid wfQueue HnAtomic HnDup Htype Hloc HId HBId.
      constructors...
      introv HIn. eapply HBId in HIn as [Hlt' HBloc]...
    - eapply wfActors in Hlookup' as wfActor'.
      inverts wfActor' as Hthis wfQid wfQueue HnAtomic HnDup Htype Hloc HId HBId.
      constructors...
      * introv HIn. eapply HBId in HIn as [Hlt' HBloc]...
Qed.

Lemma conversation_lt :
  forall M H id l L C Q e id' qid,
    wf_queueMap M H ->
    wf_actor M H id (l, L, C, Q, e) ->
    C id' = Some qid ->
    id' < length H.
Proof with eauto.
  introv wfM wfActor HC.
  inverts wfActor as _ wfC _ _ _ _ _ _.
  eapply wfC in HC as [Q' HM].
  eapply wfM in HM as [? [? [?L [HLH ?]]]]...
Qed.

Lemma wf_queueMap_heapUpdate :
  forall M H n id L l C Q e,
    wf_cfg (M, H, n) ->
    conv H id = Some C ->
    LH H id = Some L ->
    wf_queueMap M (heapUpdate H id (l, L, C, Q, e)).
Proof with hauto.
  introv wfCfg Hconv HLH.
  inverts wfCfg as wfH wfM _ _.
  inverts wfH as _ _ wfActors.
  unfolds.
  splits 3.
  + introv HIn. eapply wfM in HIn...
  + introv HIn Hconv' HC...
    - eapply wfM...
    - eapply wfM...
  + eapply wfM in H0 as [_ [_ [L' []]]]...
    - assert (id0 < length H)...
      find_actor id0.
      exists L'.
      splits...
      eapply wf_queue_heapUpdate...
    - assert (id < length H)...
      find_actor id.
      exists L'.
      splits...
      eapply wf_queue_heapUpdate...
Qed.

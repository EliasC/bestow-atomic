Require Export WellFormedness.
Require Import SyntaxProp.
Require Import StaticProp.
Require Import DynamicProp.
Require Import MapProp.

Lemma wf_actor_ctx :
  forall H l L Q e ctx,
    is_econtext ctx ->
    wf_actor H (l, L, Q, ctx e) ->
    wf_actor H (l, L, Q, e).
Proof with eauto using hasType_ctx, freeLocs_ctx, freeIds_ctx, freeBIds_ctx.
  introv Hctx wfActor.
  inverts wfActor as (t & hasType).
  constructors...
Qed.

Lemma wf_msg_heapExtend :
  forall H L msg a,
    wf_msg H L msg ->
    wf_msg (heapExtend H a) L msg.
Proof with hauto.
  introv wfMsg.
  inverts wfMsg as Hex Hloc HId HBId.
  constructors...
  + Case "Ids well-formed". crush.
  + Case "BIds well-formed".
    introv HIn.
    eapply HBId in HIn as [Hlt HBloc].
    splits...
    introv HLH...
Qed.

Hint Unfold wf_queue.

Lemma wf_actor_heapExtend :
  forall H a a',
    wf_actor H a ->
    wf_actor (heapExtend H a') a.
Proof with (hauto; eauto using wf_msg_heapExtend).
  introv wfA.
  destruct a as [[[l L] Q] e].
  inverts wfA as Hthis wfQueue [t hasType] Hloc HId HBId.
  constructors...
  + Case "Ids well-formed". crush.
  + introv HIn.
    eapply HBId in HIn as [Hlt HBloc].
    splits...
    introv HLH...
Qed.

Lemma wf_actors_heapExtend :
  forall H l L Q e id a,
    (forall id a, heapLookup H id = Some a -> wf_actor H a) ->
    wf_actor H (l, L, Q, e) ->
    heapLookup (heapExtend H (l, L, Q, e)) id = Some a ->
    wf_actor (heapExtend H (l, L, Q, e)) a.
Proof with (hauto; eauto using wf_actor_heapExtend).
  introv wfH wfA Hlookup...
Qed.

Hint Unfold wf_queue.

Lemma wf_queue_heapUpdate :
  forall H l L L' Q Q' e id l0 L0 Q0 e0,
    (forall id a, heapLookup H id = Some a -> wf_actor H a) ->
    wf_queue H L Q ->
    heapLookup H id = Some (l0, L0, Q0, e0) ->
    (forall l, In l L0 -> In l L') ->
    wf_queue (heapUpdate H id (l, L', Q', e)) L Q.
Proof with hauto.
  introv wfActors wfQueue Hlookup Hmono.
  introv HIn.
  apply wfQueue in HIn as wfMsg.
  inverts wfMsg as Hex Hloc HId HBId. constructors...
  introv HIn'.
  eapply HBId in HIn' as [Hlt HBloc]...
  splits...
  introv HLH. inv_eq...
Qed.

Lemma wf_queue_snoc :
  forall H L Q msg,
    wf_queue H L Q ->
    wf_msg H L msg ->
    wf_queue H L (snoc Q msg).
Proof with eauto.
  introv wfQueue wfMsg.
  induction Q; simpls...
  + unfolds; crush.
  + unfolds wf_queue. introv HIn.
    inv HIn; crush.
Qed.

Lemma wf_heap_heapUpdate :
  forall H l l' L Q Q' e e' id,
    wf_heap H ->
    heapLookup H id = Some (l, L, Q, e) ->
    wf_actor H (l', L, Q', e') ->
    (forall id1 id2 L1 L2,
         id1 <> id2 ->
         LH H id1 = Some L1 ->
         LH H id2 = Some L2 ->
         (forall l, In l L1 -> ~ In l L2)) ->
    wf_heap (heapUpdate H id (l', L, Q', e')).
Proof with (hauto; eauto using wf_queue_heapUpdate).
  introv wfH Hlookup wfActor Hdisj.
  assert (id < length H)...
  constructors.
  + introv Hneq HLH1 HLH2 HIn.
    repeat hauto; eapply Hdisj...
  + introv Hlookup'. inverts wfH as _ wfActors...
    - inverts wfActor as Hthis wfQueue Htype Hloc HId HBId.
      constructors...
      introv HIn. eapply HBId in HIn as [Hlt' HBloc]...
    - eapply wfActors in Hlookup' as wfActor'.
      inverts wfActor' as Hthis wfQueue Htype Hloc HId HBId.
      constructors...
      introv HIn. eapply HBId in HIn as [Hlt' HBloc]...
Qed.

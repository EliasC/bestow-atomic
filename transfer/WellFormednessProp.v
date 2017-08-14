Require Export WellFormedness.
Require Import SyntaxProp.
Require Import StaticProp.
Require Import DynamicProp.
Require Import MapProp.

Lemma wf_actor_ctx :
  forall O H l L Q e ctx,
    is_econtext ctx ->
    wf_actor O H (l, L, Q, ctx e) ->
    wf_actor O H (l, L, Q, e).
Proof with eauto using
           hasType_ctx, freeLocs_ctx, freeIds_ctx, freeTIds_ctx.
  introv Hctx wfActor.
  inverts wfActor as (t & hasType).
  constructors...
Qed.

Lemma wf_msg_heapExtend :
  forall O H L msg a,
    wf_ownerMap O H ->
    wf_msg O H L msg ->
    wf_msg O (heapExtend H a) L msg.
Proof with hauto.
  introv wfO wfMsg.
  inverts wfMsg as Hex Hloc HId HTId.
  constructors...
  crush.
Qed.

Hint Unfold wf_queue.

Lemma wf_actor_heapExtend :
  forall O H a a',
    wf_ownerMap O H ->
    wf_actor O H a ->
    wf_actor O (heapExtend H a') a.
Proof with (eauto using wf_msg_heapExtend; hauto).
  introv wfO wfA.
  destruct a as [[[l L] Q] e].
  inverts wfA as Hthis HOthis wfQueue [t hasType] Hloc HId HTId.
  constructors...
  crush.
Qed.

Lemma wf_actors_heapExtend :
  forall O H l L Q e id a,
    wf_ownerMap O H ->
    (forall id a, heapLookup H id = Some a -> wf_actor O H a) ->
    wf_actor O H (l, L, Q, e) ->
    heapLookup (heapExtend H (l, L, Q, e)) id = Some a ->
    wf_actor O (heapExtend H (l, L, Q, e)) a.
Proof with (hauto; eauto using wf_actor_heapExtend).
  introv wfO wfH wfA Hlookup...
Qed.

Hint Unfold wf_queue.

Lemma wf_queue_heapUpdate :
  forall O H l L L' Q Q' e id l0 L0 Q0 e0,
    (forall id a, heapLookup H id = Some a -> wf_actor O H a) ->
    wf_queue O H L Q ->
    heapLookup H id = Some (l0, L0, Q0, e0) ->
    (forall l, In l L0 -> In l L') ->
    wf_queue O (heapUpdate H id (l, L', Q', e)) L Q.
Proof with hauto.
  introv wfActors wfQueue Hlookup Hmono.
  introv HIn.
  apply wfQueue in HIn as wfMsg.
  inverts wfMsg as Hex Hloc HId HTId.
  constructors...
Qed.

Lemma wf_queue_snoc :
  forall O H L Q msg,
    wf_queue O H L Q ->
    wf_msg O H L msg ->
    wf_queue O H L (snoc Q msg).
Proof with eauto.
  introv wfQueue wfMsg.
  induction Q; simpls...
  + unfolds; crush.
  + unfolds wf_queue. introv HIn.
    inv HIn; crush.
Qed.

Lemma wf_heap_heapUpdate :
  forall O H l l' L Q Q' e e' id,
    wf_heap O H ->
    heapLookup H id = Some (l, L, Q, e) ->
    wf_actor O H (l', L, Q', e') ->
    (forall id1 id2 L1 L2,
         id1 <> id2 ->
         LH H id1 = Some L1 ->
         LH H id2 = Some L2 ->
         (forall l, In l L1 -> ~ In l L2)) ->
    wf_heap O (heapUpdate H id (l', L, Q', e')).
Proof with (eauto using wf_queue_heapUpdate; hauto).
  introv wfH Hlookup wfActor Hdisj.
  assert (id < length H)...
  constructors.
  + introv Hneq HLH1 HLH2 HIn.
    repeat hauto; eapply Hdisj...
  + introv Hlookup'. inverts wfH as _ wfActors...
    - inverts wfActor as Hthis HOthis wfQueue Htype Hloc HId HTId.
      constructors...
    - eapply wfActors in Hlookup' as wfActor'.
      inverts wfActor' as Hthis HOthis wfQueue Htype Hloc HId HTId.
      constructors...
Qed.

Lemma wf_ownerMap_heapUpdate :
  forall O H id l L Q e,
    wf_ownerMap O H ->
    LH H id = Some L ->
    wf_ownerMap O (heapUpdate H id (l, L, Q, e)).
Proof with hauto.
  introv wfO HLH.
  constructors...
  introv HO.
  eapply wfO in HO as []...
  splits...
  introv HLH'. inv_eq.
Qed.

Lemma ownerMap_fresh :
  forall O H l id n,
    wf_ownerMap O H ->
    (forall L id,
        LH H id = Some L -> Forall (fun l : nat => l < n) L) ->
    O l = Some id ->
    l < n.
Proof with eauto.
  introv wfO Hfresh HO.
  inverts wfO as wfO.
  specializes wfO l id ___.
  inv wfO as [Hlt HLH].
  apply heapLookup_lt in Hlt as [[[[l' L] Q] e] Hlookup].
  assert (LH H id = Some L) as HLH'
      by (unfolds; hauto).
  specializes Hfresh L id ___.
  rewrite Forall_forall in Hfresh...
Qed.

Corollary ownerMap_fresh' :
  forall O H l id n,
    wf_ownerMap O H ->
    (forall L id,
        LH H id = Some L -> Forall (fun l : nat => l < n) L) ->
    O l = Some id ->
    l <> n.
Proof with eauto.
  introv wfO Hfresh HO.
  eapply ownerMap_fresh in HO...
  omega.
Qed.

Hint Resolve ownerMap_fresh'.

Require Export Syntax.
Require Export Static.

Inductive wf_msg (M : queueMap) (H : heap) (L : localHeap) (id : id) : msg -> Prop :=
  | WF_Msg :
      forall x e,
        (exists t, extend empty x TPas |- e \in t) ->
        (forall l, In l (freeLocs e) -> In l L) ->
        (forall id', In id' (freeIds e) -> id' < length H) ->
        (forall l id',
           In (l, id') (freeBIds e) ->
           id' < length H /\
           (forall L', LH H id' = Some L' -> In l L')) ->
        wf_msg M H L id (Msg (ELam x TPas e))
  | WF_Atomic :
      forall qid Q,
        M qid = Some (Q, id) ->
        wf_msg M H L id (Atomic qid)
  | WF_AtomicEnd :
      wf_msg M H L id EndAtomic
.

Definition wf_queue (M : queueMap) (H : heap) (L : localHeap) (id : id) (Q : queue) : Prop :=
    (forall msg, In msg Q -> wf_msg M H L id msg)
.

Hint Unfold wf_queue.

Definition isAtomicMsg (msg : msg) : bool :=
  match msg with
    | Atomic _ => true
    | _ => false
  end.

Inductive wf_actor (M : queueMap) (H : heap) (id : id) : actor -> Prop :=
  | WF_Actor :
      forall l L C Q e,
        In l L ->
        (forall id' qid, C id' = Some qid -> exists Q, M qid = Some (Q, id')) ->
        wf_queue M H L id Q ->
        (forall msg, In msg Q -> msg <> EndAtomic) ->
        (NoDup (filter isAtomicMsg Q)) ->
        (exists t, empty |- e \in t) ->
        (forall l', In l' (freeLocs e) -> In l' L) ->
        (forall id', In id' (freeIds e) -> id' < length H) ->
        (forall l' id',
           In (l', id') (freeBIds e) ->
           id' < length H /\
           (forall L, LH H id' = Some L -> In l' L)) ->
        wf_actor M H id (l, L, C, Q, e)
.

Definition wf_queueMap (M : queueMap) (H : heap) : Prop :=
  forall qid Q id,
    M qid = Some (Q, id) ->
    (forall msg qid, In msg Q -> msg <> Atomic qid) /\
    (forall id' id'' C qid', In EndAtomic Q -> conv H id' = Some C -> C id'' = Some qid' -> qid <> qid') /\
    (exists L, LH H id = Some L /\ wf_queue M H L id Q)
.

Hint Unfold wf_queueMap.

Definition local_heap_disjointness (H : heap) :=
  forall id1 id2 L1 L2,
    id1 <> id2 ->
    LH H id1 = Some L1 ->
    LH H id2 = Some L2 ->
    (forall l, In l L1 -> ~ In l L2)
.

Hint Unfold local_heap_disjointness.

Definition conversation_disjointness (H : heap) :=
  forall id1 id2 C1 C2 id id' qid qid',
    id1 <> id2 ->
    conv H id1 = Some C1 ->
    conv H id2 = Some C2 ->
    C1 id = Some qid ->
    C2 id' = Some qid' ->
    qid <> qid'
.

Hint Unfold conversation_disjointness.

Inductive wf_heap (M : queueMap) (H : heap) : Prop :=
  | WF_Heap :
      local_heap_disjointness H ->
      conversation_disjointness H ->
      (forall id a,
          heapLookup H id = Some a ->
          wf_actor M H id a) ->
      wf_heap M H
.

Definition local_heap_freshness (H : heap) (n : nat) :=
  forall L id,
    LH H id = Some L ->
    Forall (fun l => l < n) L
.

Hint Unfold local_heap_freshness.

Definition queueMap_freshness (M : queueMap) (n : nat) :=
  forall qid Q,
    M qid = Some Q ->
    qid < n
.

Hint Unfold queueMap_freshness.

Inductive wf_cfg : configuration -> Prop :=
  | WF_Cfg :
      forall M H n,
        wf_heap M H ->
        wf_queueMap M H ->
        queueMap_freshness M n ->
        local_heap_freshness H n ->
        wf_cfg (M, H, n)
.
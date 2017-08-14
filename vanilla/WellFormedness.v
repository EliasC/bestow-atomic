Require Export Syntax.
Require Export Static.

Inductive wf_msg (H : heap) (L : list loc) : expr -> Prop :=
  | WF_Msg :
      forall x e,
        (exists t, extend empty x TPas |- e \in t) ->
        (forall l, In l (freeLocs e) -> In l L) ->
        (forall id, In id (freeIds e) -> id < length H) ->
        (forall l id,
           In (l, id) (freeBIds e) ->
           id < length H /\
           (forall L', LH H id = Some L' -> In l L')) ->
        wf_msg H L (ELam x TPas e)
.

Definition wf_queue (H : heap) (L : list loc) (Q : list expr) : Prop :=
    (forall msg, In msg Q -> wf_msg H L msg)
.

Inductive wf_actor (H : heap) : (loc * list loc * list expr * expr) -> Prop :=
  | WF_Actor :
      forall l L Q e,
        In l L ->
        wf_queue H L Q ->
        (exists t, empty |- e \in t) ->
        (forall l', In l' (freeLocs e) -> In l' L) ->
        (forall id, In id (freeIds e) -> id < length H) ->
        (forall l' id,
           In (l', id) (freeBIds e) ->
           id < length H /\
           (forall L, LH H id = Some L -> In l' L)) ->
        wf_actor H (l, L, Q, e)
.

Inductive wf_heap (H : heap) : Prop :=
  | WF_Heap :
      (forall id1 id2 L1 L2,
         id1 <> id2 ->
         LH H id1 = Some L1 ->
         LH H id2 = Some L2 ->
         (forall l, In l L1 -> ~ In l L2))
      ->
      (forall id a,
          heapLookup H id = Some a ->
          wf_actor H a) ->
      wf_heap H
.

Inductive wf_cfg : configuration -> Prop :=
  | WF_Cfg :
      forall H n,
        wf_heap H ->
        (forall L id, LH H id = Some L -> Forall (fun l => l < n) L) ->
        wf_cfg (H, n)
.
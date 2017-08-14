Require Import SyntaxProp.
Require Import StaticProp.
Require Import DynamicProp.
Require Import WellFormednessProp.

Lemma actor_progress :
  forall M H n l L C Q e id,
    wf_cfg (M, H, n) ->
    wf_actor M H id (l, L, C, Q, e) ->
    id < length H ->
    (exists M' H' n' e', id / (M, H, n) ; e ==> (M', H', n') ; e') \/ is_val e.
Proof with eauto 6 using is_val, step_actor, is_econtext.
  introv wfCfg wfActor Hlt.
  assert (exists t, empty |- e \in t) as [t hasType].
    inv wfActor...
  remember empty as Gamma.
  hasType_cases(induction hasType) Case; subst...
  + Case "T_Var".
    inv Hlookup.
  + Case "T_AtStart".
    eapply wf_actor_ctx with (ctx := ctx_atstart) in wfActor as wfActor'...
    crush.
    - eapply EvalContext in H0...
    - left. destruct a; inv Hactive.
      * SCase "Actor".
        inv H0; try solve[inv hasType].
        find_actor id. remember (C0 id0) as conv...
        symmetry in Heqconv. destruct conv.
        ++ repeat eexists. eapply EvalAtomicStartActorFail...
        ++ assert (id0 < length H) as Hlt
               by (inv wfActor; simpls; eauto).
           find_actor id0. heap_case id id0.
           -- repeat eexists. eapply EvalAtomicStartActor; hauto.
           -- repeat eexists. eapply EvalAtomicStartActor...
              rewrite lookup_heapUpdate_neq...
      * SCase "Bestowed".
        inv H0; try solve[inv hasType].
        find_actor id. remember (C0 id0) as conv...
        symmetry in Heqconv. destruct conv.
        ++ repeat eexists. eapply EvalAtomicStartBestowedFail...
        ++ assert (id0 < length H) as Hlt.
             inv wfActor. simpls. specializes H13 l0 id0 ___.
             find_actor id0. heap_case id id0.
           -- repeat eexists. eapply EvalAtomicStartBestowed; hauto.
           -- repeat eexists. eapply EvalAtomicStartBestowed...
              rewrite lookup_heapUpdate_neq...
  + Case "T_AtEnd".
    eapply wf_actor_ctx with (ctx := ctx_atend) in wfActor as wfActor'...
    crush.
    - eapply EvalContext in H0...
    - left. destruct a; inv Hactive.
      * SCase "Actor".
        inv H0; try solve[inv hasType].
        find_actor id. remember (C0 id0) as conv...
        symmetry in Heqconv. destruct conv.
        ++ inverts wfCfg as wfH _ _ _.
           inverts wfH as _ _ wfActors.
           eapply wfActors in Hlookup as wfActor''.
           inv wfActor''.
           assert (exists Q, M q = Some (Q, id0)) as [?Q HM]...
           repeat eexists. eapply EvalAtomicEndActor...
        ++ repeat eexists. eapply EvalAtomicEndActorFail...
      * SCase "Bestowed".
        inv H0; try solve[inv hasType].
        find_actor id. remember (C0 id0) as conv...
        symmetry in Heqconv. destruct conv.
        ++ inverts wfCfg as wfH _ _ _.
           inverts wfH as _ _ wfActors.
           eapply wfActors in Hlookup as wfActor''.
           inv wfActor''.
           assert (exists Q, M q = Some (Q, id0)) as [?Q HM]...
           repeat eexists. eapply EvalAtomicEndBestowed...
        ++ repeat eexists. eapply EvalAtomicEndBestowedFail...
  + Case "T_NewPassive".
    left. find_actor id...
  + Case "T_Mutate".
    apply wf_actor_ctx in wfActor...
    crush.
    - left...
    - inv H0; inv hasType...
  + Case "T_Bestow".
    apply wf_actor_ctx in wfActor...
    crush.
    - left...
    - inv H0; inv hasType...
  + Case "T_Apply".
    apply wf_actor_ctx with (ctx := ctx_appl e2) in wfActor as wfActor'...
    crush.
    - apply EvalContext with (ctx := ctx_appl e2) in H0...
    - apply wf_actor_ctx with (ctx := ctx_appr e1) in wfActor as wfActor''...
      crush.
      * apply EvalContext with (ctx := ctx_appr e1) in H1...
      * inv H0; try solve[inv hasType1]...
        constructors...
  + Case "T_Send".
    apply wf_actor_ctx with (ctx := ctx_send x TPas e') in wfActor as wfActor'...
    crush.
    - apply EvalContext with (ctx := ctx_send x TPas e') in H1...
    - left. unfold is_active in Hactive.
      destruct a; inv Hactive.
      * SCase "ActorSend".
        inv H1; try solve[inv hasType1]...
        inv wfActor'. simpls.
        find_actor id.
        remember (C0 id0) as conv.
        symmetry in Heqconv.
        destruct conv.
        ++ SSCase "Atomic".
           inverts wfCfg as wfH _ _ _.
           inverts wfH as _ _ wfActors.
           eapply wfActors in Hlookup as wfActor''.
           inv wfActor''.
           assert (exists Q, M q = Some (Q, id0)) as [?Q HM]...
           repeat eexists. eapply EvalSendActorAtomic; hauto.
        ++ SSCase "Regular".
           assert (id0 < length H) as Hlt'...
           find_actor id0...
           repeat eexists... eapply EvalSendActor; hauto.
      * SCase "BestowedSend".
        inv H1; try solve[inv hasType1]...
        inv wfActor'. simpls.
        find_actor id.
        remember (C0 id0) as conv.
        symmetry in Heqconv.
        destruct conv.
        ++ SSCase "Atomic".
           inverts wfCfg as wfH _ _ _.
           inverts wfH as _ _ wfActors.
           eapply wfActors in Hlookup as wfActor''.
           inv wfActor''.
           assert (exists Q, M q = Some (Q, id0)) as [?Q HM]...
           repeat eexists. eapply EvalSendBestowedAtomic; hauto.
        ++ SSCase "Regular".
           assert (id0 < length H) as Hlt' by
             specializes H14 l0 id0 ___.
           find_actor id0...
           repeat eexists... eapply EvalSendBestowed; hauto.
Qed.

Theorem progress :
  forall M H n id,
    wf_cfg (M, H, n) ->
    id < length H ->
    (exists cfg', step id (M, H, n) cfg') \/ actor_done (M, H, n) id.
Proof with eauto using step, step_preserves_this.
  introv wfCfg Hlt.
  assert (exists a, heapLookup H id = Some a) as [a Hlookup].
    apply heapLookup_lt in Hlt...
  destruct_actor a.
  assert (wf_actor M H id (l, L, C, Q, e)) as wfActor.
    inverts wfCfg as wfH _ _ _. inverts wfH as [_ _ wfActors]...
  assert (wf_queueMap M H) as wfM
    by (inv wfCfg; eauto).
  apply actor_progress with (l := l) (L := L) (C := C) (Q := Q) (e := e) (id := id) in wfCfg as Halt...
  inv Halt as [Hex | Hdone].
  + Case "e steps".
    left.
    inv Hex as [M' [H' [n' [e' Hstep]]]].
    assert (exists L' C' Q' e'', heapLookup H' id = Some (l, L', C', Q', e'')) as Hlookup'...
    destruct Hlookup' as [? [? [? [? ?]]]].
    eapply EvalActorRun in Hstep...
  + Case "is_val e".
    destruct Q.
    - SCase "Q empty".
      right.
      unfolds. rewrite Hlookup.
      constructors...
    - SCase "Q non-empty".
      destruct m.
      * SSCase "Regular message".
        left. eexists. eapply EvalActorMsg...
      * SSCase "Atomic".
        inverts wfActor as _ _ wfQueue.
        assert (wf_msg M H L id (Atomic q)) as wfMsg
            by (specializes wfQueue (Atomic q) ___; constructors; eauto).
        inverts wfMsg as HM. destruct Q0.
        ++ right... unfolds. hauto. constructors...
        ++ destruct m.
           -- left. eexists. eapply EvalActorPrivateMsg...
           -- eapply wfM in HM as [Hneq [Hend [?L wfQueue']]]; hauto.
              specializes Hneq (Atomic q0) q0 ___. constructors...
              contradiction.
           -- left. eexists... eapply EvalActorPrivateEnd...
      * SSCase "EndAtomic (absurd)".
        inverts wfActor as _ _ _ Hneq.
        specializes Hneq EndAtomic ___. constructors...
        contradiction.
Qed.

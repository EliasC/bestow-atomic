Require Import SyntaxProp.
Require Import WellFormednessProp.

Theorem datarace_freedom :
  forall O H n id1 id2 this1 this2 L1 L2 Q1 Q2 l1 l2,
    wf_cfg (O, H, n) ->
    id1 <> id2 ->
    heapLookup H id1 = Some (this1, L1, Q1, EMut (ELoc l1)) ->
    heapLookup H id2 = Some (this2, L2, Q2, EMut (ELoc l2)) ->
    l1 <> l2.
Proof with eauto.
  introv wfCfg Hneq Hlookup1 Hlookup2.
  inverts wfCfg as wfH wfO Hfresh.
  inverts wfH as Hdisj wfActors.
  eapply wfActors in Hlookup1 as wfActor1.
  eapply wfActors in Hlookup2 as wfActor2.
  inverts wfActor1 as _ _ _ _ Hloc1 _ _.
  inverts wfActor2 as _ _ _ _ Hloc2 _ _.
  simpls.
  assert (In l1 L1) as HIn1...
  assert (In l2 L2) as HIn2...
  assert (LH H id1 = Some L1) as HLH1
      by (unfolds; rewrite Hlookup1; eauto).
  assert (LH H id2 = Some L2) as HLH2
      by (unfolds; rewrite Hlookup2; eauto).
  specializes Hdisj id1 id2 L1 L2 Hneq.
Qed.
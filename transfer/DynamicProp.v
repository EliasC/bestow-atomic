Require Export Dynamic.
Require Import SyntaxProp.
Require Import MapProp.

Lemma step_preserves_this :
  forall id O O' H H' n n' e e' l L Q,
    (exists e, heapLookup H id = Some (l, L, Q, e)) ->
    id / (O, H, n); e ==> (O', H', n'); e' ->
    exists L' Q' e'', heapLookup H' id = Some (l, L', Q', e'').
Proof with hauto.
  introv Hex Hstep.
  gen e'.
  inv Hex as [e' Hlookup].
  expr_cases (induction e) Case; intros; inv Hstep;
  try solve[inv_ctx]...
Qed.

Lemma monotonic_heap :
  forall id O O' H H' n n' e e',
    id / (O, H, n); e ==> (O', H', n'); e' ->
    length H <= length H'.
Proof with hauto.
  introv Hstep.
  gen Hstep. gen e'.
  expr_cases(induction e) Case; intros; inv Hstep;
  try rewrite heapUpdate_length;
  try solve[inv_ctx]...
Qed.

Lemma monotonic_local_heap :
  forall id id' O O' H H' n n' e e' L L' l,
    id / (O, H, n); e ==> (O', H', n'); e' ->
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
    destruct (heapLookup H id') as [[[[? ?] ?] ?]|]...
    repeat inv_eq.
Qed.

Lemma new_ids_in_heap :
  forall id O O' H H' n n' e e',
    id / (O, H, n); e ==> (O', H', n'); e' ->
    (forall id, In id (freeIds e) -> id < length H) ->
    (forall id', In id' (freeIds e') -> id' < length H').
Proof with eauto using in_or_app, monotonic_heap.
  introv Hstep Hid HIn.
  assert (length H <= length H') as Hmono...
  gen e'. gen id'. gen id.
  expr_cases (induction e) Case;
    intros; inv Hstep; simpls;
    try inv_ctx;
    try rewrite_and_invert; simpls;
    try (first [apply in_app_or in HIn
               |apply freeIds_subst_in in HIn];
         inv HIn);
    try contradiction;
    try (assert (id' < length H) by eauto using in_or_app; omega);
    hauto...
Qed.

Lemma step_footprint :
  forall id id' O O' H H' n n' e e' e'' l L Q,
    id / (O, H, n); e ==> (O', H', n'); e' ->
    heapLookup H' id' = Some (l, L, Q, e'') ->
    (exists L Q, heapLookup H id' = Some (l, L, Q, e'')) \/
    e'' = EUnit /\ id' = length H /\ In l L.
Proof with hauto.
  introv Hstep Hlookup.
  gen e'. gen id'.
  expr_cases (induction e) Case;
    intros; inv Hstep; simpls;
    try inv_ctx...
  + Case "ENew".
    right. splits...
    constructors...
Qed.

Lemma step_local_heap_neq :
  forall id id' O O' H H' n n' e e' L,
    id / (O, H, n); e ==> (O', H', n'); e' ->
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
  forall id id' O O' H H' n n' e e' L,
    id / (O, H, n); e ==> (O', H', n'); e' ->
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
  forall id id' O O' H H' n n' e e',
    id / (O, H, n); e ==> (O', H', n'); e' ->
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
  forall id id' O O' H H' n n' e e' L,
    id / (O, H, n); e ==> (O', H', n'); e' ->
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
  forall id O O' H H' n n' e e',
    id / (O, H, n); e ==> (O', H', n'); e' ->
    n <= n'.
Proof with eauto.
  introv Hstep.
  gen e'.
  expr_cases (induction e) Case;
    intros; inv Hstep; simpls;
    try inv_ctx...
Qed.

Lemma ownerMap_monotonic :
  forall id O O' H H' n n' e e' l,
    id / (O, H, n); e ==> (O', H', n'); e' ->
    l < n ->
    O l = O' l.
Proof with eauto.
  introv Hstep Hlt.
  gen e'.
  expr_cases (induction e) Case;
    intros; inv Hstep; simpls;
    try inv_ctx;
    try rewrite_and_invert...
  + Case "ENew".
    assert (l <> n) by omega.
    case_extend.
Qed.

Lemma local_heap_fresh :
  forall H n L l id,
    (forall L id, LH H id = Some L -> Forall (fun l => l < n) L) ->
    LH H id = Some L ->
    In l L ->
    l < n.
Proof with eauto.
  introv Hfresh HLH HIn.
  specializes Hfresh L id HLH...
  rewrite Forall_forall in Hfresh...
Qed.

Corollary local_heap_fresh' :
  forall H n L l id,
    (forall L id, LH H id = Some L -> Forall (fun l => l < n) L) ->
    LH H id = Some L ->
    In l L ->
    l <> n.
Proof with eauto.
  introv Hfresh HLH HIn.
  assert (l < n) by eauto using local_heap_fresh.
  omega.
Qed.

Hint Resolve local_heap_fresh'.

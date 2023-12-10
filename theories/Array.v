(* Array-like operations on Coq lists. *)

From Array Require Import
  Invert.
From Coq Require Import
  List.

Export ListNotations.

Theorem not_exists_forall_not : forall {T} (P : T -> Prop),
  (~exists x, P x) <-> forall x, ~P x.
Proof.
  split.
  - intros H x C. apply H. exists x. assumption.
  - intros H [x C]. apply H in C. assumption.
Qed.

Inductive Get : forall {T}, nat -> list T -> T -> Prop :=
  | GetHead : forall {T} hd tl,
      @Get T O (hd :: tl) hd
  | GetTail : forall {T} n hd tl out,
      @Get T n tl out ->
      @Get T (S n) (hd :: tl) out
  .

Fixpoint get {T} n (li : list T) :=
  match li with
  | [] => None
  | hd :: tl =>
      match n with
      | O => Some hd
      | S m => get m tl
      end
  end.

Theorem get_empty : forall {T} n,
  @get T n [] = None.
Proof. destruct n; reflexivity. Qed.

Theorem get_out_of_bounds : forall {T} n (li : list T),
  length li <= n <->
  get n li = None.
Proof.
  split.
  - generalize dependent n. induction li; intros; simpl in *.
    + apply get_empty.
    + destruct n; try solve [invert H]. simpl. apply IHli.
      apply PeanoNat.Nat.succ_le_mono in H. assumption.
  - generalize dependent n. induction li; intros; simpl in *.
    + apply le_0_n.
    + destruct n. { discriminate H. }
      simpl in *. apply le_n_S. apply IHli in H. assumption.
Qed.

Theorem get_pop : forall {T} n (hd : T) li out,
  get (S n) (hd :: li) = Some out <->
  get n li = Some out.
Proof. split; intros; assumption. Qed.

Theorem get_some_not_empty : forall {T} n li (out : T),
  get n li = Some out ->
  exists hd tl, li = hd :: tl.
Proof.
  intros T n li. generalize dependent n. induction li; intros; simpl in *.
  - rewrite get_empty in H. discriminate H.
  - exists a. exists li. reflexivity.
Qed.

Theorem reflect_get : forall {T} n (li : list T) out,
  Get n li out <-> get n li = Some out.
Proof.
  split; intros.
  - induction H; [reflexivity | assumption].
  - generalize dependent n. generalize dependent out. induction li; intros; simpl in *.
    + destruct n; discriminate H.
    + destruct n. { invert H. constructor. } simpl in *. constructor. apply IHli. assumption.
Qed.

Theorem reflect_not_get : forall {T} n (li : list T),
  get n li = None <-> forall out, ~Get n li out.
Proof.
  split.
  - intros H out C. rewrite reflect_get in C. rewrite H in C. discriminate C.
  - intros H.
    assert (A : forall out, get n li <> Some out). { intros. rewrite <- reflect_get. apply H. }
    destruct (get n li).
    + specialize (A t). contradiction A. reflexivity.
    + reflexivity.
Qed.

Inductive Snoc : forall {T}, T -> list T -> list T -> Prop :=
  | SnocNil : forall {T} x,
      @Snoc T x [] [x]
  | SnocCons : forall {T} x hd tl out,
      @Snoc T x tl out ->
      @Snoc T x (hd :: tl) (hd :: out)
  .

Fixpoint snoc {T} (x : T) li :=
  match li with
  | [] => [x]
  | hd :: tl => hd :: snoc x tl
  end.

Theorem reflect_snoc : forall {T} (x : T) li out,
  Snoc x li out <-> snoc x li = out.
Proof.
  split; intros.
  - induction H; simpl in *. { reflexivity. } f_equal. assumption.
  - generalize dependent x. generalize dependent out. induction li; intros; simpl in *.
    + invert H. constructor.
    + invert H. constructor. apply IHli. reflexivity.
Qed.

Theorem snoc_length : forall {T} (x : T) li,
  length (snoc x li) = S (length li).
Proof.
  intros. generalize dependent x. induction li; intros; simpl in *.
  + reflexivity.
  + f_equal. apply IHli.
Qed.

Theorem snoc_not_empty : forall {T} (x : T) li,
  snoc x li <> [].
Proof. intros T x [] C; discriminate C. Qed.

Theorem snoc_pop : forall {T} (x : T) hd tl,
  snoc x (hd :: tl) = hd :: snoc x tl.
Proof. reflexivity. Qed.

Inductive Skip : forall {T}, nat -> list T -> list T -> Prop :=
  | SkipZero : forall {T} li,
      @Skip T O li li
  | SkipSucc : forall {T} n hd tl out,
      @Skip T n tl out ->
      @Skip T (S n) (hd :: tl) out
  .

Fixpoint skip {T} n (li : list T) :=
  match n with
  | O => Some li
  | S m =>
      match li with
      | [] => None
      | hd :: tl => skip m tl
      end
  end.

Theorem skip_pop : forall {T} n (li : list T) hd tl,
  skip n li = Some (hd :: tl) ->
  skip (S n) li = Some tl.
Proof.
  intros. generalize dependent T. induction n; intros; simpl in *.
  - invert H. reflexivity.
  - destruct li; [discriminate H |]. apply IHn in H.
    destruct li; [discriminate H |]. assumption.
Qed.

Theorem skip_pop_both : forall {T} n (hx : T) tx hy ty,
  skip n (hx :: tx) = Some (hy :: ty) ->
  skip n tx = Some ty.
Proof.
  intros T n hx tx. generalize dependent n. generalize dependent hx.
  induction tx; simpl in *; intros.
  - destruct n; invert H. { reflexivity. } destruct n; invert H1.
  - destruct n; simpl in *. { invert H. reflexivity. }
    apply IHtx in H. assumption.
Qed.

Theorem skip_everything : forall {T} (li : list T),
  skip (length li) li = Some [].
Proof. induction li. { reflexivity. } assumption. Qed.

Theorem reflect_skip : forall {T} n (li : list T) out,
  Skip n li out <-> skip n li = Some out.
Proof.
  split; intros.
  - induction H; [reflexivity | assumption].
  - generalize dependent T. induction n; intros; simpl in *.
    + invert H. constructor.
    + destruct li; [discriminate H |]. constructor. apply IHn. assumption.
Qed.

Theorem reflect_not_skip : forall {T} n (li : list T),
  skip n li = None <-> forall out, ~Skip n li out.
Proof.
  split.
  - intros H out C. rewrite reflect_skip in C. rewrite H in C. discriminate C.
  - intros H.
    assert (A : forall out, skip n li <> Some out). { intros. rewrite <- reflect_skip. apply H. }
    destruct (skip n li).
    + specialize (A l). contradiction A. reflexivity.
    + reflexivity.
Qed.

Theorem skip_undo : forall {T} n (li : list T) hd tl,
  skip (S n) li = Some tl ->
  get n li = Some hd ->
  skip n li = Some (hd :: tl).
Proof.
  intros T n li hd tl Hs Hg. generalize dependent n. generalize dependent hd. generalize dependent tl.
  induction li; intros; simpl in *. { discriminate Hs. }
  destruct n; simpl in *. { invert Hs. invert Hg. reflexivity. }
  destruct li; [discriminate Hs |].
  apply (IHli _ _ _ Hs Hg).
Qed.

Theorem skip_get : forall {T} n (li : list T) hd,
  get n li = Some hd <-> exists tl, skip n li = Some (hd :: tl).
Proof.
  split; intros.
  - generalize dependent T. induction n; intros; simpl in *.
    + destruct li; simpl in *. { discriminate H. }
      invert H. exists li. reflexivity.
    + destruct li; simpl in *. { discriminate H. }
      apply IHn in H. assumption.
  - destruct H as [tl H]. generalize dependent T. induction n; intros; simpl in *.
    + invert H. reflexivity.
    + destruct li; [discriminate H |]. apply IHn in H. assumption.
Qed.

Theorem skip_out_of_bounds : forall {T} n (li : list T),
  length li < n <->
  skip n li = None.
Proof.
  split; intros.
  - generalize dependent n. induction li; intros; simpl in *.
    + destruct n; try solve [invert H]. reflexivity.
    + destruct n; try solve [invert H]. simpl. apply IHli.
      apply PeanoNat.Nat.succ_lt_mono in H. assumption.
  - generalize dependent n. induction li; intros; simpl in *.
    + destruct n. { discriminate H. } apply PeanoNat.Nat.lt_0_succ.
    + destruct n. { discriminate H. }
      simpl in *. rewrite <- PeanoNat.Nat.succ_lt_mono.
      apply IHli. assumption.
Qed.

Theorem skip_in_bounds : forall {T} n (li : list T),
  n <= length li <->
  exists output, skip n li = Some output.
Proof.
  split.
  - intros H. generalize dependent T. induction n; intros; simpl in *.
    + exists li. reflexivity.
    + destruct li; [invert H |]; simpl in *.
      apply PeanoNat.Nat.succ_le_mono in H.
      apply IHn in H. destruct H as [out H].
      exists out. assumption.
  - intros [out H]. generalize dependent T. induction n; intros; simpl in *.
    + apply le_0_n.
    + destruct li; [discriminate H |]. apply IHn in H.
      simpl. rewrite <- PeanoNat.Nat.succ_le_mono. assumption.
Qed.

Inductive Take : forall {T}, nat -> list T -> list T -> Prop :=
  | TakeO : forall {T} li,
      @Take T O li []
  | TakeS : forall {T} n hd tl out,
      @Take T n tl out ->
      @Take T (S n) (hd :: tl) (hd :: out)
  .

Fixpoint take {T} n (li : list T) :=
  match n with
  | O => Some []
  | S m =>
      match li with
      | [] => None
      | hd :: tl =>
          match take m tl with
          | None => None
          | Some out => Some (hd :: out)
          end
      end
  end.

Theorem take_len : forall {T} n (li : list T) out,
  take n li = Some out ->
  length out = n.
Proof.
  intros T n. generalize dependent T. induction n; intros; simpl in *.
  - invert H. reflexivity.
  - destruct li; [discriminate H |].
    destruct (take n li) eqn:E; invert H.
    apply IHn in E. simpl. f_equal. assumption.
Qed.

Theorem take_infer_len : forall {T} n (li : list T) out,
  take n li = Some out ->
  n = length out.
Proof.
  intros. generalize dependent T. induction n; intros; simpl in *.
  - invert H. reflexivity.
  - destruct li; invert H. destruct (take n li) eqn:E; invert H1.
    apply IHn in E. simpl. f_equal. assumption.
Qed.

Theorem reflect_take : forall {T} n (li : list T) out,
  Take n li out <-> take n li = Some out.
Proof.
  split; intros; simpl in *.
  - induction H; simpl in *. { reflexivity. }
    rewrite IHTake. reflexivity.
  - generalize dependent T. induction n; intros; simpl in *. { invert H. constructor. }
    destruct li; [discriminate H |].
    destruct (take n li) eqn:E; invert H.
    constructor. apply IHn. assumption.
Qed.

Theorem reflect_not_take : forall {T} n (li : list T),
  take n li = None <-> forall out, ~Take n li out.
Proof.
  split; intros.
  - intro C. apply reflect_take in C. rewrite H in C. discriminate C.
  - generalize dependent T. induction n; intros; simpl in *.
    + specialize (H []). contradiction H. constructor.
    + destruct li; [reflexivity |].
      destruct (take n li) eqn:E; [| reflexivity].
      apply reflect_take in E. apply (TakeS _ t) in E. apply H in E. destruct E.
Qed.

Theorem take_pop : forall {T} n (hd : T) li out,
  take (S n) (hd :: li) = Some (hd :: out) <->
  take n li = Some out.
Proof. split; intros; [invert H; destruct (take n li); invert H1 | simpl; rewrite H]; reflexivity. Qed.

Theorem take_infer_pop : forall {T} n (hd1 : T) hd2 tl out,
  take (S n) (hd1 :: tl) = Some (hd2 :: out) ->
  hd1 = hd2.
Proof. intros; simpl in *. destruct (take n tl); invert H. reflexivity. Qed.

Theorem take_snoc : forall {T} n (li : list T) hd tl,
  (take n li = Some hd /\ get n li = Some tl) <-> take (S n) li = Some (snoc tl hd).
Proof.
  split.
  - intros [Hhd Htl]. simpl in *.
    generalize dependent n. generalize dependent hd. generalize dependent tl.
    induction li; intros; simpl in *. { rewrite get_empty in Htl. discriminate Htl. }
    destruct n; simpl in *. { invert Hhd. invert Htl. reflexivity. }
    destruct (take n li) eqn:E; invert Hhd. rewrite (IHli tl l); try assumption; reflexivity.
  - intros. simpl in *. destruct li; invert H. destruct (take n li) eqn:E; invert H1.
    generalize dependent n. generalize dependent li. generalize dependent tl.
    generalize dependent l. generalize dependent t. induction hd; intros; invert H0; simpl in *.
    + remember (take_infer_len _ _ _ E). subst. split; reflexivity.
    + destruct n. { invert E. symmetry in H0. apply snoc_not_empty in H0. destruct H0. }
      destruct li; invert E. destruct (take n li) eqn:E; invert H0.
      rewrite take_pop. rewrite get_pop. apply (IHhd t l); assumption.
Qed.

Theorem take_in_bounds : forall {T} n (li : list T),
  n <= length li <->
  exists out, take n li = Some out.
Proof.
  split; generalize dependent T; induction n; intros; simpl in *;
  [exists []; reflexivity | | apply le_0_n | destruct H as [out H]];
  (destruct li; [invert H |]; simpl in *).
  - apply le_S_n in H. apply IHn in H. destruct H as [out H]. exists (t :: out). rewrite H. reflexivity.
  - destruct (take n li) eqn:E; invert H. apply le_n_S. apply IHn. exists l. assumption.
Qed.

Theorem take_out_of_bounds : forall {T} n (li : list T),
  length li < n <-> take n li = None.
Proof.
  split; generalize dependent n; induction li;
  (intros; destruct n; simpl in *; [invert H |]);
  [reflexivity | | apply PeanoNat.Nat.lt_0_succ |].
  - apply PeanoNat.Nat.succ_lt_mono in H. rewrite IHli. { reflexivity. } assumption.
  - destruct (take n li) eqn:E. { discriminate H. } apply -> PeanoNat.Nat.succ_lt_mono. apply IHli. assumption.
Qed.

Inductive CheckedSub : nat -> nat -> nat -> Prop :=
  | CheckedSubO : forall n,
      CheckedSub n 0 n
  | CheckedSubS : forall a b out,
      CheckedSub a b out ->
      CheckedSub (S a) (S b) out
  .

Fixpoint checked_sub a b :=
  match b with
  | O => Some a
  | S b' =>
      match a with
      | O => None
      | S a' => checked_sub a' b'
      end
  end.

Theorem checked_sub_O : forall n,
  checked_sub n O = Some n.
Proof. destruct n; reflexivity. Qed. (* Why is this necessary??? *)

Theorem checked_sub_eq : forall n,
  checked_sub n n = Some O.
Proof. induction n. { reflexivity. } apply IHn. Qed.

Theorem S_le : forall n m,
  S n <= m -> n <= m.
Proof. intros. induction H; repeat constructor. assumption. Qed.

Theorem checked_sub_le : forall a b,
  b <= a ->
  exists c, checked_sub a b = Some c.
Proof.
  intros. generalize dependent a. induction b; intros; simpl in *.
  - exists a. apply checked_sub_O.
  - invert H. { exists O. apply checked_sub_eq. }
    apply IHb. apply (S_le _ _ H0).
Qed.

Theorem reflect_checked_sub : forall a b out,
  CheckedSub a b out <-> checked_sub a b = Some out.
Proof.
  split; intros.
  - induction H; [apply checked_sub_O | assumption].
  - generalize dependent a. generalize dependent out. induction b; intros; simpl in *.
    + rewrite checked_sub_O in H. invert H. constructor.
    + destruct a; simpl in *. { discriminate H. } constructor. apply IHb. assumption.
Qed.

Theorem reflect_not_checked_sub : forall a b,
  checked_sub a b = None <-> forall out, ~CheckedSub a b out.
Proof.
  split; intros.
  - intros C. generalize dependent H. induction C; intros; simpl in *.
    + rewrite checked_sub_O in H. discriminate H.
    + apply IHC in H. assumption.
  - generalize dependent a. induction b; intros; simpl in *.
    + specialize (H a). rewrite reflect_checked_sub in H. contradiction H. apply checked_sub_O.
    + destruct a. { reflexivity. } 
      apply IHb. intros out C. apply CheckedSubS in C. apply H in C. assumption.
Qed.

Theorem checked_sub_infer_eq : forall a b,
  checked_sub a b = Some O ->
  a = b.
Proof.
  intros a b. generalize dependent a. induction b; intros; simpl in *.
  - rewrite checked_sub_O in H. invert H. reflexivity.
  - destruct a; simpl in *. { discriminate H. }
    f_equal. apply IHb. assumption.
Qed.

Theorem checked_sub_S : forall a b c,
  checked_sub a (S b) = Some c ->
  checked_sub a b = Some (S c).
Proof.
  intros a b. generalize dependent a. induction b; intros; simpl in *.
  - destruct a; simpl in *. { discriminate H. } rewrite checked_sub_O in H. invert H. reflexivity.
  - destruct a; [discriminate H |]. simpl in *. apply IHb. assumption.
Qed.

Theorem checked_sub_mono : forall a b c,
  checked_sub a b = Some c ->
  c <= a.
Proof.
  intros a b. generalize dependent a. induction b; intros; simpl in *.
  - rewrite checked_sub_O in H. invert H. constructor.
  - apply checked_sub_S in H. apply IHb in H. apply S_le in H. assumption.
Qed.

Theorem checked_sub_undo : forall a b c,
  checked_sub a b = Some c <->
  a = b + c.
Proof.
  split; intros.
  - generalize dependent a. generalize dependent c. induction b; intros; simpl in *.
    + rewrite checked_sub_O in H. invert H. reflexivity.
    + destruct a; [discriminate H |]. simpl in *. f_equal. apply IHb. assumption.
  - generalize dependent a. generalize dependent c. induction b; intros; simpl in *.
    + subst. rewrite checked_sub_O. reflexivity.
    + destruct a; [discriminate H |]. injection H as H. apply IHb. assumption.
Qed.

Theorem checked_sub_flip : forall a b c,
  checked_sub a b = Some c <->
  checked_sub a c = Some b.
Proof. intros. repeat rewrite checked_sub_undo. rewrite PeanoNat.Nat.add_comm. split; intro H; apply H. Qed.

Theorem skip_len_exists : forall {T} n (li : list T) len,
  checked_sub (length li) n = Some len <->
  exists out, (skip n li = Some out /\ length out = len).
Proof.
  split; intros.
  - generalize dependent T. generalize dependent len. induction n; intros; simpl in *.
    + rewrite checked_sub_O in H. invert H. exists li. split; reflexivity.
    + destruct li; [discriminate H |]. simpl in *. apply IHn. assumption.
  - destruct H as [out [Hskip Hlen]].
    generalize dependent T. generalize dependent len. induction n; intros; simpl in *.
    + rewrite checked_sub_O. f_equal. invert Hskip. reflexivity.
    + destruct li; [discriminate Hskip |]. simpl in *. apply (IHn _ _ _ out); assumption.
Qed.

Theorem skip_len : forall {T} n (li : list T) out,
  skip n li = Some out ->
  checked_sub (length li) n = Some (length out).
Proof.
  intros. generalize dependent T. induction n; intros; simpl in *.
  - invert H. rewrite checked_sub_O. reflexivity.
  - destruct li; [discriminate H |]. apply IHn. assumption.
Qed.

Definition Slice : forall {T}, nat -> nat -> list T -> list T -> Prop := fun {T} i j li out =>
  exists len,
  CheckedSub j i len /\
  exists skipped,
  Skip i li skipped /\
  Take len skipped out.

Definition slice : forall {T}, nat -> nat -> list T -> option (list T) := fun {T} i j li =>
  match checked_sub j i with
  | None => None
  | Some len =>
      match skip i li with
      | None => None
      | Some skipped => take len skipped
      end
  end.

Theorem reflect_slice : forall {T} i j (li : list T) out,
  Slice i j li out <-> slice i j li = Some out.
Proof.
  split; intros.
  - induction H.
    + destruct H as [Hij [skipped [Hskip Htake]]]. unfold slice.
      apply reflect_checked_sub in Hij. rewrite Hij. clear Hij.
      apply reflect_skip in Hskip. rewrite Hskip. clear Hskip.
      apply reflect_take in Htake. rewrite Htake. clear Htake.
      reflexivity.
  - unfold slice in H. generalize dependent T. generalize dependent j. induction i; intros; simpl in *.
    + exists j. split. { constructor. }
      exists li. split. { constructor. }
      rewrite checked_sub_O in H. apply reflect_take in H. assumption.
    + destruct (checked_sub j (S i)) eqn:Eij; [| discriminate H]. apply reflect_checked_sub in Eij.
      destruct li; [discriminate H |].
      destruct (skip i li) eqn:Eskip; [| discriminate H]. apply reflect_skip in Eskip.
      apply reflect_take in H. exists n. split. { assumption. }
      exists l. split. { constructor. assumption. } assumption.
Qed.

Theorem slice_O : forall {T} j (li : list T),
  slice 0 j li = take j li.
Proof. intros. unfold slice. rewrite checked_sub_O. reflexivity. Qed.

Theorem slice_ends_O : forall {T} i (li : list T),
  slice i 0 li = match i with O => Some [] | S _ => None end.
Proof. intros T [] li; reflexivity. Qed.

Theorem slice_ends_O_some : forall {T} i (li : list T) (out : list T),
  slice i 0 li = Some out ->
  i = O /\ out = [].
Proof. intros T [] li out; intros. { invert H. split; reflexivity. } discriminate H. Qed.

Theorem slice_ends_O_none : forall {T} i (li : list T),
  slice i 0 li = None -> exists n, i = S n.
Proof. intros T [] li H. { discriminate H. } exists n. reflexivity. Qed.

Theorem slice_pop : forall {T} i j (hd : T) tl,
  slice (S i) (S j) (hd :: tl) = slice i j tl.
Proof. reflexivity. Qed.

Theorem slice_idx_eq : forall {T} i (li : list T),
  i <= length li ->
  slice i i li = Some [].
Proof.
  intros. unfold slice. rewrite checked_sub_eq.
  apply skip_in_bounds in H. destruct H as [out H]. rewrite H. reflexivity.
Qed.

Theorem slice_infer_idx_eq : forall {T} i j (li : list T),
  slice i j li = Some [] ->
  i = j /\ i <= length li.
Proof.
  intros. generalize dependent T. generalize dependent i. induction j; intros; simpl in *.
  - apply slice_ends_O_some in H. destruct H. subst. split. { reflexivity. } apply le_0_n.
  - destruct i. { rewrite slice_O in H. apply take_infer_len in H. discriminate H. }
    destruct li. { unfold slice in H. simpl in *. destruct (checked_sub j i); discriminate H. }
    rewrite slice_pop in H. apply IHj in H. destruct H. split; [f_equal | simpl; apply le_n_S]; assumption.
Qed.

Theorem slice_len : forall {T} i j (li : list T),
  j <= length li ->
  i <= j ->
  exists out, slice i j li = Some out.
Proof.
  intros T i j li Hj Hi. unfold slice.
  remember (checked_sub_le _ _ Hi) as H eqn:E; clear E. destruct H as [c H]. rewrite H.
  remember (PeanoNat.Nat.le_trans _ _ _ Hi Hj) as Hskip eqn:E; clear E.
  apply skip_in_bounds in Hskip. destruct Hskip as [out Hskip]. rewrite Hskip. apply take_in_bounds.
  generalize dependent T. generalize dependent j. generalize dependent c. induction i; intros; simpl in *.
  - invert Hskip. rewrite checked_sub_O in H. invert H. assumption.
  - destruct li; [discriminate Hskip |].
    destruct j; [invert Hi |]. simpl in *. apply le_S_n in Hi. apply le_S_n in Hj.
    apply (IHi c j Hi H T li Hj out Hskip).
Qed.

Theorem slice_infer_len : forall {T} i j (li : list T) out,
  slice i j li = Some out ->
  j = i + length out.
Proof.
  intros. generalize dependent T. generalize dependent j. induction i; intros; simpl in *.
  - rewrite slice_O in H. apply take_infer_len in H. assumption.
  - destruct j; simpl in *. { unfold slice in H. discriminate H. }
    destruct li; simpl in *. { unfold slice in H. simpl in *. destruct (checked_sub j i); discriminate H. }
    f_equal. apply (IHi _ _ _ _ H).
Qed.

Theorem slice_snoc : forall {T} i j (li : list T) hd tl,
  slice i j li = Some hd ->
  get j li = Some tl ->
  slice i (S j) li = Some (snoc tl hd).
Proof.
  intros T i j li. generalize dependent i. generalize dependent j. induction li; intros; simpl in *.
  - apply get_some_not_empty in H0. destruct H0 as [h [t C]]. discriminate C.
  - destruct j; simpl in *. { invert H0. apply slice_ends_O_some in H. destruct H. subst. reflexivity. }
    destruct i; simpl in *.
    + rewrite slice_O in *. destruct hd. { apply take_infer_len in H. discriminate H. }
      remember (take_infer_pop _ _ _ _ _ H) as E eqn:EE. clear EE. subst.
      rewrite snoc_pop. rewrite take_pop in *. rewrite <- slice_O in *. apply IHli; assumption.
    + rewrite slice_pop in *. apply IHli; assumption.
Qed.

Theorem reflect_not_slice : forall {T} i j (li : list T),
  slice i j li = None <-> forall out, ~Slice i j li out.
Proof.
  split; intros.
  - intros [len [Hij [skipped [Hskip Htake]]]]. rename H into C. unfold slice in C.
      rewrite reflect_checked_sub in Hij. rewrite Hij in C. clear Hij.
      rewrite reflect_skip in Hskip. rewrite Hskip in C. clear Hskip.
      rewrite reflect_take in Htake. rewrite Htake in C. clear Htake.
      discriminate C.
  - unfold Slice in *. unfold slice in *.
    destruct (checked_sub j i) eqn:Eij; [| reflexivity]. apply reflect_checked_sub in Eij.
    destruct (skip i li) eqn:Eskip; [| reflexivity]. apply reflect_skip in Eskip.
    apply reflect_not_take. intros out C.
    specialize (H out). rewrite not_exists_forall_not in H. specialize (H n). apply H.
    split. { assumption. }
    exists l. split; assumption.
Qed.

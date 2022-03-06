Require Import
  Coq.FSets.FMapList
  Coq.Structures.OrderedTypeEx.
Require Import Coq.Arith.Arith.
Module Import M := FMapList.Make(Nat_as_OT).

Inductive LinkedList : Type :=
  | node (self: nat) (n: nat).

Definition memory : Type := M.t LinkedList.

Definition new (m : memory) : LinkedList * memory :=
  let elem := node (1 + cardinal m) 0 in 
  (elem, (add (1 + cardinal m) elem m)).

Definition self_addr (l: LinkedList) : nat :=
  match l with node s _ => s end.

Definition next_addr (l: LinkedList) : nat :=
  match l with node _ n => n end.

Theorem stack_valid : forall l m,
  l = fst (new m) ->
  self_addr l > 0.
Proof.
  intros.
  inversion H; subst.
  unfold new, self_addr.
  simpl. destruct (cardinal (elt:=LinkedList) m).
  - auto.
  - apply gt_Sn_O.
Qed.

Definition is_empty (m: memory) (l: LinkedList) : bool :=
  match l with node _ n => 
      match (find n m) with 
      | Some _ => false
      | None => true 
      end
  end.

Definition push (m: memory) (l: LinkedList) (item: nat) :=
  match l with
  | node s n => ((add item (node item n) m), node s item)
  end.

Definition pop (m: memory) (l: LinkedList) :=
  match (is_empty m l) with
  | true => None
  | false => match l with
             | node s n => Some n
             end
  end.

Theorem pop_on_non_empty: forall 
  (m: memory) (l: LinkedList) (item: nat),
  is_empty m l = false -> 
  pop m l <> None.
Proof.
  intros.
  destruct l.
  destruct n.
  - unfold pop. rewrite H. discriminate.
  - unfold pop. rewrite H. discriminate.
Qed.

Theorem non_empty_after_push: forall
  (m: memory) (l: LinkedList) (item: nat),
  let res := (push m l item) in
  is_empty (fst res) (snd res) = false.
Proof.
  intros.
  destruct l.
  destruct n.
  - simpl. 
    assert (H: E.eq item item).
    reflexivity.
    apply add_1 with (elt:=LinkedList) (m:=m) (e:=node item 0) in H.
    apply find_1 in H.
    rewrite H.
    reflexivity.
  - simpl.
    assert (H: E.eq item item).
    reflexivity.
    apply add_1 with (elt:=LinkedList) (m:=m) (e:=node item (S n)) in H.
    apply find_1 in H.
    rewrite H.
    reflexivity.
Qed.


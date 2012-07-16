(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Axiom iff_eq : forall (P Q : Prop),
(P -> Q) -> (Q -> P) -> P = Q.

Inductive option (T:Type) :Type :=
some : T -> option T | none : option T.


Module Tactics.
Ltac rw a := rewrite a.
Ltac wr a  := rewrite <- a.
Ltac rw2 a b := rewrite  a; rewrite  b.
Ltac wr2 a b := rewrite <- a; rewrite <- b.

Definition first A (a:A) := True.
Definition second A (a:A) := True.

(** the following is a tactic that we will use when
trying to enter a whole table of inequalities at once ***)

Ltac when_comparing :=
match goal with 
id1 : first ?X1, id2 : second ?X2 |- bool =>
first[
assert (X1 = X2); [reflexivity | exact true] |
exact false]
| _ => fail
end.

Ltac outleft :=
match goal with 
|- (?X1 = ?X2) =>
(set (lhs := X1))
|_ => fail
end.

Ltac outright :=
match goal with 
|- (?X1 = ?X2) =>
(set (rhs := X2))
|_ => fail
end.

End Tactics.
Export Tactics.

Module Bool.

(**** we refer to Coq's bool type with two constructors true and false;
for simplicity we prove some basic facts directly (although they 
are surely in the Standard Library somewhere) ************************)

Lemma bool_alt : forall p : bool, 
(p=true \/ p = false).
Proof.
intro p. induction p. apply or_introl; trivial.
apply or_intror; trivial. 
Qed. 

Definition bool_and (a b:bool) : bool :=
match a with
true => b |
false => false end.

Lemma bool_and_true : forall a b,
(bool_and a b = true) = (a = true /\
b = true).
Proof.
intros. apply iff_eq; intros. 
apply conj. induction a; induction b;
try discriminate; try assumption. 
induction a; induction b; try discriminate;
try assumption. induction H. 
rewrite H; rewrite H0; reflexivity. 
Qed.


Definition bool_compare (a b:bool) : bool :=
match a, b with 
true, true => true |
false, false => true |
p,q => false
end.

Lemma bool_compare_eq : forall a b,
bool_compare a b = true -> a = b.
Proof.
intros. induction a; induction b; 
try reflexivity; try assumption; try 
(symmetry; assumption). 
Qed. 

Definition bool_plus (a b:bool) : bool :=
match a, b with 
true, true => false |
false, false => false |
true, false => true |
false, true => true
end.



Definition bool_implies (a b:bool) : bool :=
match a, b with
true, false => false |
p,q => true
end.

Definition bool_or (a b :bool) :  bool :=
match a, b with
true, p => true |
false, p => p
end.

End Bool.
Export Bool.



Module Positive.

(**** here we mimic the positive type from the ZArith library;
again we redo just what we need, 
for uniformity of notation and simplicity ****)

Inductive pos : Type :=
one : pos |
xL : pos -> pos |
xR : pos -> pos .

Fixpoint pos_compare (a  b:pos) {struct a} :bool:=
match a, b with
one, one => true |
xL u, xL v => pos_compare u v |
xR u, xR v => pos_compare u v |
u, v => false
end.

Lemma pos_compare_eq : forall a b,
pos_compare a b = true -> a = b.
Proof.
intro a. induction a; intros; induction b;
try reflexivity. 
assert (false=true). assumption. 
discriminate H0. 
assert (false=true). assumption. 
discriminate H0. 
assert (false=true). assumption. 
discriminate H0. 
assert (pos_compare a b = true). 
assumption. rewrite (IHa _ H0). 
reflexivity. 
assert (false=true). assumption. 
discriminate H0. 
assert (false=true). assumption. 
discriminate H0. 
assert (false=true). assumption. 
discriminate H0. 
assert (pos_compare a b = true). 
assumption. rewrite (IHa _ H0). 
reflexivity. 
Qed.

Lemma pos_compare_refl : forall a,
pos_compare a a = true.
Proof.
intro a; induction a. reflexivity. 
assumption. assumption. 
Qed. 

Lemma pos_compare_neq : forall a b,
pos_compare a b = false -> ~a=b.
Proof.
intros. unfold not; intro. rewrite H0 in H. 
rewrite pos_compare_refl in H. 
discriminate H. 
Qed.

(*** arithmetic on positives which are BinInts;
this is again copied from ZArith *******)

Fixpoint pos_succ (a:pos) : pos :=
match a with 
one => xL one |
xL x => xR x |
xR x => xL (pos_succ x)
end.

Fixpoint pos_plus (a b:pos) {struct a} : pos :=
match a with 
one => pos_succ b |
xL x => 
match b with 
one => xR x |
xL y => xL (pos_plus x y) |
xR y => xR (pos_plus x y)
end |
xR x => 
match b with 
one => xL (pos_succ x) |
xL y => xR (pos_plus x y) |
xR y => xL (pos_succ (pos_plus x y))
end
end.

Definition pos_half (a:pos) : pos :=
match a with 
one => one |
xL u => u |
xR u => u
end.

Fixpoint nat_pos (i:nat) : pos :=
match i with 
O => one |
S j => pos_succ (nat_pos j)
end.

End Positive.
Export Positive.

Module Table.

(***** here we implement the notion of a table
as a collection of trees; the pos type, with its
suggestive constructor names, tells us how to navigate
within the trees. This is a simplification of the
IntMap library, and of course the idea was taken from there.
The functions defined in IntMap seem unnecessarily complicated
at first, although there is certainly an optimization reason
for this. By simplifying things we will certainly lose whatever
optimization that was. In this module we give
some basic proofs, which serves among other things to
make sure we have defined the right functions. 
**********************************)

Inductive table (T:Type) : Type := 
stop : T -> table T |
node : T -> table T -> table T -> table T.


Fixpoint put (T:Type) (t:T) (a:pos) (u : table T)
{struct a} : table T :=
match a with
one => 
match u with 
stop x => node t (stop x) (stop x) |
node x v w => node t v w
end |
xL b => 
match u with 
stop x => node x (put t b (stop x)) (stop x) |
node x v w => node x (put t b v) w
end |
xR b => 
match u with 
stop x => node x (stop x) (put t b (stop x)) |
node x v w => node x v (put t b w)
end 
end.

Fixpoint get (T:Type) (a:pos) (u:table T) 
{struct a} : T := 
match a with 
one =>
match u with 
stop x => x |
node x v w => x 
end |
xL b => 
match u with 
stop x => x |
node x v w => (get b v) 
end |
xR b => 
match u with 
stop x => x |
node x v w => (get b w) 
end
end.

Lemma get_put_eq1 : forall T (t:T) a u,
get a (put t a u) = t.
Proof.
intros. 
generalize a. 
induction u. 
intros. induction a0; try reflexivity. 
simpl. assumption. 
simpl. assumption. 
intros. induction a0; try reflexivity. 
simpl. auto. simpl; auto. 
Qed. 

Lemma get_put_eq : forall T (t:T) a b u,
a = b ->
get a (put t b u) = t.
Proof.
intros. rewrite H. apply get_put_eq1.
Qed. 

Lemma get_put_neq : forall T (t:T) a b u,
~a=b ->
get a (put t b u) = get a u.
Proof.
intros T t a. 
induction a.
intros. 
induction u. 
induction b. induction H; reflexivity. 
reflexivity. reflexivity. 
induction b. induction H; reflexivity. 
reflexivity. reflexivity. 
intro b. induction b. 
intros. induction u. 
simpl. induction a; reflexivity. 
simpl. reflexivity. 
intros. induction u. 
simpl. rewrite IHa. induction a; reflexivity. 
unfold not; intros. apply H. rewrite H0; reflexivity. 
simpl. rewrite IHa. reflexivity. 
unfold not; intros. apply H. rewrite H0; reflexivity. 
intros. induction u. 
simpl. induction a; reflexivity. 
simpl. reflexivity. 

intro b. induction b. 
intros. induction u. simpl. 
induction a; reflexivity. 
simpl. reflexivity. 
intros. induction u. simpl. 
induction a; reflexivity. 
simpl. reflexivity. 
intros. induction u. 
simpl. rewrite IHa. induction a; reflexivity. 
unfold not; intros. apply H. rewrite H0; reflexivity. 
simpl. rewrite IHa. reflexivity. 
unfold not; intros. apply H. rewrite H0; reflexivity. 
Qed. 

Lemma get_put_same : forall T (t:T) a b u,
pos_compare a b = true ->
get a (put t b u) = t.
Proof.
intros. apply get_put_eq. 
apply pos_compare_eq. assumption. 
Qed.

Lemma get_put_diff : forall T (t:T) a b u,
pos_compare a b = false ->
get a (put t b u) = get a u.
Proof.
intros. apply get_put_neq. apply pos_compare_neq.
assumption. 
Qed. 

End Table.
Export Table.

Module List.

(****** a short remake of the List library ******)

Inductive list (T:Type) : Type :=
nil : list T |
cons : T -> list T -> list T.

Definition length : forall (T:Type), list T -> nat.
intros T u. induction u. exact 0. 
exact (S IHu). 
Defined. 

Lemma length_nil : forall T, length (nil T) = 0.
Proof.
intros. reflexivity.
Qed.

Lemma length_cons : forall T (t:T) u, length (cons t u)
= S (length u).
Proof.
intros. reflexivity. 
Qed. 


Definition arity : forall (n:nat) (T:Type),  Type.
intros n T. induction n. 
exact T. exact (T -> IHn). 
Defined.



Definition withdraw : forall (T:Type) (n:nat),
(list T -> T) -> (arity n T).
intros T n. induction n. intro. 
exact (X (nil T)). 
intro. change (T -> arity n T). intro t. 
apply IHn. intro u. 
exact (X (cons t u)). 
Defined. 


Definition onlist : forall (T:Type) (u:list T),
arity (length u) T -> T.
intros T u. induction u. change (T -> T). 
intro t; exact t. 
intro. assert (T -> (arity (length u) T)).
exact X. apply IHu. apply X0. exact t. 
Defined. 




Lemma onlist_withdraw : forall (T:Type) 
(u:list T) (f:list T -> T),
(onlist (u:=u) (withdraw (length u) f))
= f u.
Proof.
intros T u. induction u. intro f; reflexivity. 
intro f. transitivity
(onlist (u:=u) ((withdraw (S (length u)) f) t)).
reflexivity. 
exact (IHu (fun u => f (cons t u))). 
Qed. 

Definition same_arity : forall (n:nat) (T:Type),
arity n T -> arity n T -> Prop.
intro n. induction n. 
intros. exact (X = X0). 
intros. exact (forall t:T,
IHn T (X t) (X0 t)). 
Defined. 

Lemma withdraw_onlist : forall (T:Type) (p:nat)
(f : (forall m : nat, arity m T)),
same_arity (withdraw p (fun u:list T => 
(onlist (u:=u) (f (length u))))) (f p).
Proof.
intros T p. induction p. intro f. 
set (g:= fun u : list T => onlist (u:=u)
(f (length u))). 
change ((withdraw 0 g) = f 0). reflexivity. 
intro f. 
set (g:= fun u : list T => onlist (u:=u)
(f (length u))). 
change (forall t:T, 
same_arity ((withdraw (S p) g) t) ((f (S p)) t)). 
intro t. 
exact (IHp (fun m => f (S m) t)). 
Qed. 

Fixpoint check T (p:T -> bool) (l:list T) 
{struct l} : bool :=
match l with 
nil  => false |
cons t u => bool_or (p t) (check p u)
end.

Lemma check_cons : forall T (p:T -> bool) (t:T)(l:list T),
check p (cons t l) = 
bool_or (p t) (check p l).
Proof.
intros. induction l. 
reflexivity. 
reflexivity. 
Qed. 

Fixpoint listed_have T (p:T-> Prop) (l:list T) 
{struct l} : Prop := 
match l with 
nil => True |
cons t u => (p t) /\ (listed_have p u)
end.

Lemma listed_have_nil : forall T p,
listed_have p (nil T).
Proof.
intros.
change True. trivial.  
Qed.

Lemma listed_have_cons : forall T (p:T->Prop) t u,
listed_have p (cons t u) = (p t /\ listed_have p u).
Proof.
intros. induction u. 
reflexivity. reflexivity. 
Qed. 

Definition list_first T (l:list T) : option T :=
match l with
nil => none T |
cons t m => some t
end.

Definition list_tail T (l:list T) : list T :=
match l with 
nil => nil T |
cons t m => m
end. 

Definition empty_list T (l:list T) : bool :=
match l with
nil => true |
cons t m => false
end. 



End List.
Export List.

Module String.

(**** a type of strings with constructors designed to make
writing and reading them as easy as possible, within the
confines of classical Coq syntax. ***********)

Inductive alphabet : Type :=
a_ : alphabet | b_ : alphabet | c_ : alphabet |
d_ : alphabet |e_ : alphabet |f_ : alphabet |
g_ : alphabet |h_ : alphabet |i_ : alphabet |
j_ : alphabet |k_ : alphabet |l_ : alphabet |
m_ : alphabet |n_ : alphabet |o_ : alphabet |
p_ : alphabet |q_ : alphabet |r_ : alphabet |
s_ : alphabet |t_ : alphabet |u_ : alphabet |
v_ : alphabet |w_ : alphabet |x_ : alphabet |
y_ : alphabet |z_ : alphabet.





Definition alphabet_compare (u v: alphabet) : bool.
intros. 
assert (first u). unfold first. trivial. 
assert (second v). unfold second. trivial. 
induction u; induction v; when_comparing. 
Defined.    

Lemma alphabet_compare_refl : forall a,
alphabet_compare a a = true.
Proof.
intro a; induction a; reflexivity.
Qed. 

Lemma alphabet_compare_eq : forall u v,
alphabet_compare u v = true -> u = v.
Proof.
intros. induction u; induction v; try discriminate;
try reflexivity. 
Qed. 

Definition string := list alphabet.
Definition dot :string := nil alphabet.
Definition J : alphabet ->string -> string := 
(cons (T:=alphabet)).


Coercion J : alphabet >-> Funclass. 

Definition string_compare : string -> string -> bool.
intros u. induction u. intro v; induction v. 
exact true. exact false. intro v; induction v. 
exact false. exact (bool_and (alphabet_compare t t0)
(IHu v)). 
Defined. 

Lemma string_compare_refl : forall u, 
string_compare u u = true. 
Proof. 
intro u. induction u. 
reflexivity. 
change (bool_and (alphabet_compare t t)
(string_compare u u) = true). 
rewrite alphabet_compare_refl. assumption. 
Qed. 

Lemma string_compare_eq : forall u v,
string_compare u v = true -> u = v.
Proof.
intros u. induction u.
intro v. induction v. intros. reflexivity. 
intros. discriminate. 
intros. 
induction v. discriminate. 
assert (bool_and (alphabet_compare t t0) (string_compare u v)
=true). assumption. 
rewrite bool_and_true in H0. induction H0. 
rewrite (alphabet_compare_eq H0). 
rewrite (IHu _ H1). reflexivity. 
Qed. 

Definition a' := (a_ dot).
Definition b' := (b_ dot).
Definition c' := (c_ dot).
Definition d' := (d_ dot).
Definition e' := (e_ dot).
Definition f' := (f_ dot).
Definition g' := (g_ dot).
Definition h' := (h_ dot).
Definition i' := (i_ dot).
Definition j' := (j_ dot).
Definition k' := (k_ dot).
Definition l' := (l_ dot).
Definition m' := (m_ dot).
Definition n' := (n_ dot).
Definition o' := (o_ dot).
Definition p' := (p_ dot).
Definition q' := (q_ dot).
Definition r' := (r_ dot).
Definition s' := (s_ dot).
Definition t' := (t_ dot).
Definition u' := (u_ dot).
Definition v' := (v_ dot).
Definition w' := (w_ dot).
Definition x' := (x_ dot).
Definition y' := (y_ dot).
Definition z' := (z_ dot).

(*** we number the alphabet by positives, from 1 to 26! ****)

Definition alphabet_pos a :=
match a with 
a_ => one |
b_ => xL one |
c_ => xR one |
d_ => xL (xL one) |
e_ => xR (xL one)  |
f_ => xL (xR one)  |
g_ => xR (xR one)  |
h_ => xL (xL (xL one))   |
i_ => xR (xL (xL one))  |
j_ => xL (xR (xL one))  |
k_ => xR (xR (xL one))  |
l_ => xL (xL (xR one))  |
m_ => xR (xL (xR one))  |
n_ => xL (xR (xR one))  |
o_ => xR (xR (xR one))  |
p_ => xL (xL (xL (xL one)))  |
q_ => xR (xL (xL (xL one)))   |
r_ => xL (xR (xL (xL one)))  |
s_ => xR (xR (xL (xL one)))  |
t_ => xL (xL (xR (xL one)))  |
u_ => xR (xL (xR (xL one)))  |
v_ => xL (xR (xR (xL one)))  |
w_ => xR (xR (xR (xL one)))  |
x_ => xL (xL (xL (xR one)))  |
y_ => xR (xL (xL (xR one)))  |
z_ => xL (xR (xL (xR one)))  
end.

(**** the following is a sort of silly attempt at a hash function ****)

Definition string_pos : string -> pos.
intro u. induction u. exact one. 
exact (pos_plus 
(alphabet_pos t) IHu).
Defined. 


End String.
Export String.


Module Hash.

(***** we implement hashtables, using the tables and lists above.
Again, while we don't try to prove everything, we do prove some basic
lemmas indicating that we seem to have defined the functions correctly
*****************************************************************)

Record hashtools (T:Type) : Type :={
comp : T -> T -> bool;
addr : T-> pos
}.

Definition tools_ok T (u:hashtools T) :=
forall x y, comp u x y = true -> x = y.

Definition hashtable T := table (list T).


Definition initialize T : hashtable T :=
(stop (nil T)).

Definition add T (r:hashtools T) (t:T) (u:hashtable T) :=
(put (cons t (get (addr r t) u)) (addr r t) u). 

Lemma get_add_same : forall T (r:hashtools T) (t:T)
a  (u:hashtable T),
pos_compare a (addr r t) = true ->
get a (add r t u) = cons t (get a u).
Proof.
intros. unfold add. 
transitivity (get a (put (cons t (get (addr r t) u)) (addr r t)
u)). reflexivity. 
rewrite get_put_same; try assumption. 
assert (a = addr r t). apply pos_compare_eq; assumption.
rewrite H0; reflexivity. 
Qed. 

Lemma get_add_diff : forall T (r:hashtools T) (t:T)
a (u:hashtable T),
pos_compare a (addr r t) = false ->
get a (add r t u) = get a u.
Proof.
intros. unfold add. 
transitivity (get a (put (cons t (get (addr r t) u)) (addr r t)
u)). reflexivity. 
rewrite get_put_diff; try assumption. reflexivity. 
Qed. 

Fixpoint from_list T (r:hashtools T) (l:list T) 
{struct l} : hashtable T :=
match l with 
nil => initialize T |
cons t u => add r t (from_list r u)
end.



Lemma from_list_cons : forall T (r:hashtools T) u t,
from_list r (cons t u) = add r t (from_list r u).
Proof. 
intros. reflexivity. 
Qed.  




Definition search T (r:hashtools T) 
(t:T) (u: hashtable T) : bool :=
check (fun x => (comp r t x)) (get (addr r t) u).

Lemma search_add : forall T (r:hashtools T)
(s t:T)(u:hashtable T),
(tools_ok r) ->
search r s (add r t u) =
bool_or (comp r s t) (search r s u).
Proof.
intros. 
unfold search. 
pose (p:= pos_compare (addr r s) (addr r t)).
induction (bool_alt p). 
rewrite get_add_same. 
rewrite check_cons. reflexivity. 
assumption. 
rewrite get_add_diff. 
assert (comp r s t = false). 
unfold tools_ok in H. 
induction (bool_alt (comp r s t)). 
unfold p in H0. 
rewrite (H _ _ H1) in H0. 
rewrite pos_compare_refl in H0. 
discriminate H0. assumption. 
rewrite H1. reflexivity. assumption. 
Qed.

Definition all_have T (p:T-> Prop) 
(u:hashtable T) := 
(forall a, listed_have p (get a u)).


Lemma all_have_add : forall T (r:hashtools T)
(p:T->Prop) (t:T)(u:hashtable T), 
all_have p (add r t u) =
(p t /\ all_have p u).
Proof.
intros. apply iff_eq; intros. 
apply conj. 
pose (H (addr r t)). 
assert (listed_have p (get (addr r t) (add r t u))).
assumption. rewrite get_add_same in H0. 
rewrite listed_have_cons in H0. 
induction H0; assumption. 
apply pos_compare_refl. 
unfold all_have. intro a. 
induction (bool_alt (pos_compare a (addr r t))).
assert (get a (add r t u) = cons t (get a u)).
rewrite get_add_same; try assumption. reflexivity. 
pose (H a). 
assert (listed_have p (get a (add r t u))).
assumption. 
rewrite H1 in H2. rewrite listed_have_cons in H2. 
induction H2; assumption. 
assert (get a u = get a (add r t u)).
rewrite get_add_diff; try assumption. 
reflexivity. rewrite H1. 
exact (H a). 
unfold all_have. 
intro a. 
induction (bool_alt (pos_compare a (addr r t))).
rewrite get_add_same; try assumption. 
rewrite listed_have_cons. apply conj.
induction H; assumption. 
induction H. apply H1. 
rewrite get_add_diff. induction H. apply H1. 
assumption. 
Qed. 

Lemma listed_have_one_has : 
forall T (l:list T)(r:hashtools T) (p:T->Prop)
(t:T),
tools_ok r ->
check (fun x => comp r t x) l = true ->
listed_have p l ->
p t.
Proof.
intros T l. 
induction l. intros.
assert (false = true).
exact H0. discriminate. 
intros. 
assert (bool_or (comp r t0 t) 
(check (fun x => comp r t0 x) l) = true).
assumption. 
induction (bool_alt (comp r t0 t)).
unfold tools_ok in H. 
pose (H _ _ H3). 
rewrite e. 
rewrite listed_have_cons in H1. 
induction H1; assumption. 
rewrite H3 in H2. 
apply IHl with r. assumption. 
assumption. rewrite listed_have_cons in H1.
induction H1; assumption. 
Qed.


Lemma all_have_one_has : forall T (r:hashtools T)
(p:T->Prop) (t:T) (u:hashtable T),
tools_ok r ->
search r t u = true ->
all_have p u -> p t.
Proof.
intros. 
assert (listed_have p (get (addr r t) u)).
apply H1. 
unfold search in H0. 
apply listed_have_one_has with T (get (addr r t) u) r.
assumption. assumption. assumption. 
Qed. 




End Hash. 
Export Hash.





Module Inequalities.

(***** it is convenient to have an inductive type
representing the answer of an inequality (see the
ZArith library for an example of this) ****)

Inductive ineq : Type :=
i_lt : ineq | i_eq : ineq | i_gt : ineq.

Fixpoint pos_ineq (a b:pos) {struct a}: ineq :=
match a, b with
one, one => i_eq |
one, _ => i_lt |
xL u, one => i_gt |
xL u, xL v => pos_ineq u v |
xL u, xR v => match (pos_ineq u v) with
i_gt => i_gt | i_eq => i_lt | i_lt => i_lt end|
xR u, one => i_gt |
xR u, xL v => match (pos_ineq u v) with
i_gt => i_gt | i_eq => i_gt | i_lt => i_lt end |
xR u, xR v => pos_ineq u v
end.

Definition pos_max (a b:pos) : pos :=
match (pos_ineq a b) with
i_lt => b |
_ => a end.

Definition alphabet_ineq (a b:alphabet) : ineq :=
pos_ineq (alphabet_pos a) (alphabet_pos b).

(*** ?? we would like to make a table 
of values of this ?? ***)

Fixpoint list_alphabet_ineq (x y:list alphabet)
{struct x} : ineq :=
match x,y with
nil, nil => i_eq |
nil, cons a u => i_lt |
cons a u, nil => i_gt |
cons a u, cons b v =>
match (alphabet_ineq a b) with
i_lt => i_lt |
i_eq => list_alphabet_ineq u v |
i_gt => i_gt
end end.

Definition string_ineq (x y:string) : ineq :=
list_alphabet_ineq x y.



End Inequalities. 
Export Inequalities. 

Module Sorting.

(****** we implement a balanced tree sorting procedure,
which theoretically should have logarithmic time behavior.
Andre' Hirschowitz explained the algorithm to me and said
he thought that this particular one was due to Gerard Huet
*********************************************************)

Inductive order (T:Type) : Type :=
ostop : T -> order T|
onode : pos -> order T-> order T-> order T.

Definition depth T (u:order T) : pos :=
match u with
ostop t => one |
onode a r s => a
end.

Definition tilt T (u v:order T) : ineq :=
pos_ineq (depth u) (depth v).


Definition gnode T (u v:order T) : order T:=
onode (pos_succ (pos_max (depth u) (depth v)))
u v.

Fixpoint leftmost T (u:order T) {struct u}: T :=
match u with 
ostop t => t |
onode a r s => leftmost r end.

Fixpoint rightmost T (u:order T) {struct u}: T :=
match u with 
ostop t => t |
onode a r s => rightmost s end.


(*** we try to implement doing a balanced node
construction; normally the difference between the two
depths at a node should never be more than one. 
However we have not proven this in the current version ***)

Definition bnode T (u v:order T) : order T :=
match tilt u v with 
i_eq => gnode u v |
i_lt => match v with
ostop t => gnode u v |
onode a r s => 
match tilt r s with 
i_gt =>
match r with
ostop q => gnode u v |
onode b x y => gnode (gnode u x) (gnode y s)
end |
_ => gnode (gnode u r) s
end  end |
i_gt => match u with
ostop t => gnode u v |
onode a r s =>
match tilt r s with
i_lt => match s with
ostop q => gnode u v |
onode b x y => gnode (gnode r x) (gnode y v)
end |
_ => gnode r (gnode s v)
end end end.


Fixpoint insert T (j:T->T->ineq) (t:T)(u:order T) 
{struct u} : order T :=
match u with
ostop r => match (j t r) with
i_lt => gnode (ostop t) (ostop r) |
i_eq => ostop t |
i_gt => gnode (ostop r) (ostop t) 
end |
onode a v w =>
match (j t (leftmost w)) with
i_lt => bnode (insert j t v) w |
_ => bnode v (insert j t w)
end end.

(** the above insert will cover over the same
element whereas cautious_insert will leave the existing
element in place if there are several which are j-equal ***)

Fixpoint cautious_insert T (j:T->T->ineq) (t:T)(u:order T) 
{struct u} : order T :=
match u with
ostop r => match (j t r) with
i_lt => gnode (ostop t) (ostop r) |
i_eq => ostop r |
i_gt => gnode (ostop r) (ostop t) 
end |
onode a v w =>
match (j t (leftmost w)) with
i_lt => bnode (cautious_insert j t v) w |
_ => bnode v (cautious_insert j t w)
end end.

Fixpoint concatenate T (a b:list T) {struct a}: list T :=
match a with
nil => b |
cons t u => cons t (concatenate u b)
end.

Fixpoint sublist T (l r : T -> bool) (u:order T) 
{struct u} : list T :=
match 
u with 
ostop t => if (l t) then if (r t) then (cons t (nil T))
else (nil T) else (nil T) |
onode a v w => 
match (l (rightmost v)), (r (leftmost w)) with
true, true => concatenate (sublist l r v) (sublist l r w) |
false, true => sublist l r w |
true, false => sublist l r v |
false, false => nil T
end
end. 

Definition left_margin T (j:T->T->ineq) (t:T) : T -> bool 
:= 
fun x => match (j t x) with 
i_gt => false | _ => true end.

Definition right_margin T (j:T->T->ineq) (t:T) : T -> bool 
:= 
fun x => match (j t x) with 
i_lt => false | _ => true end.

Definition occurence_list T (j:T->T->ineq) (t:T)(u:order T)
: list T :=
sublist (left_margin j t) (right_margin j t) u.








End Sorting.
Export Sorting. 






Module Fmachine.

(***** now we combine the above techniques to program a
forward-chaining procedure in first-order logic. This rewrites a program 
which I originally wrote in C but of course I don't claim
any originality for the idea of forward-chaining---and I don't
know whether anyone else has used precisely the same algorithm.
The basic idea is to order the known statements lexicographically;
then when we would like to go forward with a given lemma,
at each hypothesis we restrict to the interval in the 
lexicographic order which corresponds to the leading characters
of the statement of the hypothesis, up to the first free variable.

Again we don't prove any lemmas here; there are two types of
things one would like to prove: first that the statements which
are found are really consequences of the known statements and
lemmas; and second (more difficult), that we have found all of them
within the constraints of the filter. 
*************************************************************)

Inductive term : Type := 
X : nat -> term |
const  : string -> term  |
ev : term  -> term  -> term .

(*
Coercion lab : string >-> term.*)

Fixpoint nat_ineq (i j:nat) {struct i} : ineq :=
match i,j with 
O,O => i_eq |
S m, O => i_gt |
O, S n => i_lt |
S m, S n => nat_ineq m n
end. 

(* term_ineqL puts variables first *)
Fixpoint term_ineqL (x y:term) {struct x} : ineq :=
match x,y with 
X i, const b => i_lt|
X i, X j => nat_ineq i j |
X i, ev u v => i_lt |
const a, X i => i_gt |
ev u v, X i => i_gt |
const a, const b => string_ineq a b |
const a, ev u v => i_lt |
ev u v, const a => i_gt |
ev u v, ev r s => 
match (term_ineqL u r) with
i_lt => i_lt |
i_eq => term_ineqL v s |
i_gt => i_gt
end end.

(* term_ineqR puts variables last *)
Fixpoint term_ineqR (x y:term) {struct x} : ineq :=
match x,y with 
X i, const b => i_gt|
X i, X j => nat_ineq i j |
X i, ev u v => i_gt |
const a, X i => i_lt |
ev u v, X i => i_lt |
const a, const b => string_ineq a b |
const a, ev u v => i_lt |
ev u v, const a => i_gt |
ev u v, ev r s => 
match (term_ineqR u r) with
i_lt => i_lt |
i_eq => term_ineqR v s |
i_gt => i_gt
end end.


Definition unification_list (v:term) (a : order term) :=
sublist (left_margin term_ineqL v)
(right_margin term_ineqR v) a.

Inductive option (T:Type) : Type :=
none : option T |
some : T -> option T.

Definition initial_unifier : option (table (option term)) 
:= some (stop (none term)).

(*** if there is already a different term there it
gives back a global none ***)
Definition add_to_unifier (t:term) (i:nat)
(u:option (table (option term))): 
option (table (option term)) 
:= let p := nat_pos i in
match u with
none => none (table (option term)) |
some v => 
match (get p v) with 
none => some (put (some t) p v) |
some r => match (term_ineqL r t) with
i_eq => some v |
_ => none (table (option term)) 
end end end.


Fixpoint unify (u:option (table (option term)))
(a b:term) {struct a} : option (table (option term)) :=
match a,b with 
X i, c => add_to_unifier c i u |
const s, X j => none (table (option term)) |
const s, ev m n => none (table (option term)) |
const s, const r => if string_compare r s then u else
none (table (option term)) |
ev m n, X j => none (table (option term)) |
ev m n, const s => none (table (option term)) |
ev m n, ev l p => 
match u with none => none (table (option term)) |
_ => 
unify (unify u m l) n p
end end.


Fixpoint modify (u: table (option term))
(a:term) {struct a} : term :=
match a with 
X i => let g := get (nat_pos i) u in
match g with none => X i |
some t => t end |
const s => const s |
ev x y => ev (modify u x) (modify u y)
end.

Definition unify_ok 
(a b:term) : bool :=
match (unify initial_unifier a b) with 
none => false |
_ => true end.

Definition unifying_table (a b:term) : table (option term)
:= let u := unify initial_unifier a b in
match u with none => stop (none term) |
some v => v end. 

Definition unification_value (i:nat) (a b:term) : term 
:= match (get (nat_pos i) (unifying_table a b)) with
none => const (nil alphabet) |
some t => t
end.



Notation impl := (const (cons i_ (cons m_ (nil alphabet)))).

Definition is_impl (t:term) : bool :=
match t with 
X i => false |
const s => string_compare s 
(cons i_ (cons m_ (nil alphabet))) |
ev u v => false
end.

Definition impl_pattern :=
ev (ev impl (X 0)) (X 1).

(*
Definition fits_impl_pattern (a:term) :=
unify_ok impl_pattern a.

Definition impl_first a :=
unification_value 0 impl_pattern a.

Definition impl_second a :=
unification_value 1 impl_pattern a. 
*)

Definition fits_impl_pattern (a:term):bool :=
match a with 
ev (ev (const s) u) v => string_compare s
(cons i_ (cons m_ (nil alphabet))) |
_ => false
end.

Definition impl_first (a:term) : term :=
match a with 
ev (ev b u) v => u |
u => u 
end.

Definition impl_second (a:term) : term :=
match a with 
ev (ev b u) v => v |
u => u
end.

Fixpoint sequent_conclusion (a:term) : term :=
if (fits_impl_pattern a) then
match a with 
ev (ev b u) v => sequent_conclusion v |
u => u end
else a.

Fixpoint sequent_hyp_list (a:term) : list term :=
if (fits_impl_pattern a) then
match a with 
ev (ev b u) v => cons u (sequent_hyp_list v) |
u => nil term 
end
else (nil term).

Fixpoint sequent_numb_hyps (a:term) : nat :=
if (fits_impl_pattern a) then
match a with
ev (ev b u) v => S (sequent_numb_hyps v) |
_ => O end
else O.


(*************************************
now we set up the basic notations which establish
the logical connectives which our program will 
manipulate. 
****************************************)


Notation and' := (const (cons a_ (cons n_ (nil alphabet)))).
Notation equ :=  (const (cons e_ (cons q_ (nil alphabet)))).
Notation tr := (const (cons t_ (cons r_ (nil alphabet)))).
Notation flse := (const (cons f_ (cons l_ (nil alphabet)))).

Notation look := (const (cons l_ (cons k_ (nil alphabet)))).

Notation "A / B" := (ev A B) (at level 40, left associativity). 

Notation "A 'IMP' B" := (impl / A / B) (at level 81,
right associativity). 

Notation "A 'EQU' B" := (equ / A / B) (at level 82,
no associativity). 

Notation "A 'AND' B" := (and' / A / B) (at level 98,
right associativity). 

Notation "'LOOK' A" := (look / A) (at level 45). 


Definition modus_ponens2 :=
(LOOK (X 0)) IMP (X 0) IMP ((X 0) IMP (X 1)) IMP (X 1).

Definition modus_ponens3 :=
((X 0) IMP (X 1)) IMP ((X 1) IMP (X 2)) IMP ((X 0) IMP (X 2)).

Definition refl := 
(LOOK (X 0)) IMP ((X 0) EQU (X 0)).

Fixpoint insert_term_list (l:list term)
(u:order term) {struct l}: order term :=
match l with
nil => u |
cons t m => insert term_ineqL t (insert_term_list m u)
end.

Fixpoint concat_term_order (v:order term) 
(l:list term) {struct v} : list term :=
match v with
ostop t => cons t l |
onode d r s => (concat_term_order r 
(concat_term_order s l))
end. 

Definition term_order_list (v:order term):list term :=
concat_term_order v (nil term).

Definition modus_output (a1 a2 b:term) :=
(modify (unifying_table a1 b) a2).


Fixpoint modus_output_Blist (a1 a2:term)
(b : list term) {struct b}: list term := 
match b with 
nil => nil term |
cons t u => 
if unify_ok a1 t then cons (modus_output a1 a2 t) 
(modus_output_Blist a1 a2 u) else 
(modus_output_Blist a1 a2 u) end.

Definition modus_output_Border (a:term)
(u: order term) : list term :=
if (fits_impl_pattern a) then 
let a1 := impl_first a in 
let a2 := impl_second a in
let b:=  unification_list a1 u in 
modus_output_Blist a1 a2 b 
else nil term.

Fixpoint modus_output_list (l:list term)
(u: order term) {struct l} : list term :=
match l with
nil => nil term |
cons a m => concatenate (modus_output_Border a u)
(modus_output_list m u)
end.

Record mopair : Type := mop {
imp_list : list term;
stat_ord : order term}.

Definition already_said (u:order term)(t:term) : bool :=
match (occurence_list term_ineqL t u) with
nil => false |
_ => true end.

Definition filter_or (f g:term -> bool) (t:term) :=
bool_or (f t) (g t).

(***** the triage function is where we decide which output
statements to display as new findings; for one thing we don't want
to display statements that we already know, and for another we
want to apply a filter f :term -> bool
with the convention that a term is thrown away if the filter
says true ******************************)


Fixpoint triage (l:list term)(f:term -> bool)
(r : mopair) {struct l}: mopair:=
match l with
nil => r |
cons a m => 
let c := triage m f r in
if (fits_impl_pattern a) then
mop (cons a (imp_list c)) (stat_ord c) 
else 
if (f a) then c else
mop (imp_list c) (insert term_ineqL a (stat_ord c))
end.

Fixpoint max_sequent_numb_hyps (l:list term) : nat :=
match l with 
nil => O |
cons a m =>
let i := (sequent_numb_hyps a) in
let j := (max_sequent_numb_hyps m) in
match (pos_ineq (nat_pos i) (nat_pos j)) with
i_lt => j | 
_ => i end end. 

Fixpoint modus_run (i:nat) (b:mopair) (u :order term)
(f : term -> bool)
{struct i} : mopair :=
match i with
O => b |
S j => let c := modus_run j b u f in
triage 
(modus_output_list (imp_list c) u) 
(filter_or f (already_said u)) 
(mop (nil term) (stat_ord c))
end. 

Definition full_modus_run (l:list term)
(u :order term) (f:term -> bool) : list term :=
term_order_list
(stat_ord (modus_run 
(max_sequent_numb_hyps l) (mop l (ostop tr)) u f)).


Fixpoint term_length_pos (t:term) : pos :=
match t with 
X i => one |
const s => one |
ev u v => pos_plus (term_length_pos u) (term_length_pos v)
end. 

(*** the easiest way to filter terms is
just by their length; we don't really want to display or read
terms that are too long anyway, so our proof will quite likely
take a path which stayse within terms of a bounded length.
Thus the term_length_filter. 
For the definition recall that the term is to be thrown away 
if the filter says true ********************************)


Definition term_length_filter (i:nat) (t:term) : bool :=
match (pos_ineq (term_length_pos t) (nat_pos i)) with
i_gt => true |
_ => false
end.




(**** here is a quick attempt at using the proof display
of Coq, as well as Ltac, to do some input and output.
This might be seen as an answer to a question posed by ????
on the coq-club mailing list, ???date??? ****)

Parameter D : forall (i:nat) T (t:T), Prop.
Axiom show_D : forall i T (t:T), (D i t).
 
Ltac display i t :=
assert (D i t); [apply show_D | idtac].


Ltac display_list l :=
assert (dl_helper : (D 3 l)); [apply show_D|idtac];
match goal with 
id1 : (D 3 ?X1) |- _ => 
(compute in id1;
match goal with 
id1 : (D 3 (nil term)) |- _ => clear dl_helper |
id1 : (D 3 (cons ?X2 ?X3)) |- _ => 
display 2 X2; clear dl_helper; 
display_list X3 |
_ => fail
end) |
_ => fail
end.



Definition test_list := (cons modus_ponens3 (cons
modus_ponens2 (cons refl (nil term)))).

Ltac constitute_list :=
match goal with 
id1 : (D 2 ?X1), id2 : (D 4 ?X2) |- _ =>
display 4 (cons X1 X2); 
clear id1; clear id2; constitute_list  |
_ => idtac
end. 

Ltac display_constituted_list :=
match goal with 
id1 : (D 4 ?X1) |- _ =>
display_list X1; clear id1 |
_ => idtac
end.

Ltac redisplay :=
display 4 (nil term); 
constitute_list; display_constituted_list.

(*** D 2 are the basic list elements
D 5 is the list of implications to use
D 6 is the term order
D 7 is the spam term order ***)

Ltac dispatch :=
match goal with 
id1 : (D 2 ?X1), id2 : (D 6 ?X2)
|- _ => display 6 (insert term_ineqL X1 X2); 
clear id1; clear id2; dispatch |
_ => idtac
end. 

Ltac forward L :=
dispatch; 
match goal with
id2 : (D 6 ?X2), id3 : (D 7 ?X3), 
id4 : (D 9 ?X4) |- _ =>
display_list (full_modus_run L X2 
(filter_or (already_said X3) (term_length_filter X4)))
| _ => idtac
end. 

(****** the following lets us send an unwanted statement
to a spam list, which is then consulted by our filter.
This suggests that one might try to develop a rather
extensive filtering system, maybe based on actual spam-filter
technology, to  throw away unwanted statements and thus
try to limit the combinatorial explosion. ************)

Ltac spam h :=
match goal with 
id1 : (D 2 ?X1), id2 : (D 7 ?X2) |- _ =>
assert (fluff : id1 = h); [solve [reflexivity]|
clear fluff;  
display 7 (insert term_ineqL X1 X2);
clear id1; clear id2 ] |
_ => fail end .


Ltac display_mp :=
match goal with
id1 : (D 5 ?X1), id2 : (D 6 ?X2) |- _ =>
display_list (modus_output_list X1 X2)
| _ => idtac
end. 

Ltac finish_order :=
match goal with 
id1 : (D 6 ?X1) |- (order term) =>
exact X1 |
 _ => fail
end.

Ltac what_we_got :=
match goal with
id1 : (D 6 ?X1) |- _ =>
display_list (term_order_list X1)
| _ => fail
end.

Definition displayed (i:nat) T (t:T) (H:D i t) := t. 


Definition initial_term_order :=
ostop tr.

(***** the following are notations we will use for variables ****)

Notation Za := (const (cons a_ (nil alphabet))).
Notation Zb := (const (cons b_ (nil alphabet))).
Notation Zc := (const (cons c_ (nil alphabet))).
Notation Zd := (const (cons d_ (nil alphabet))).
Notation Ze := (const (cons e_ (nil alphabet))).
Notation Zf := (const (cons f_ (nil alphabet))).
Notation Zg := (const (cons g_ (nil alphabet))).
Notation Zh := (const (cons h_ (nil alphabet))).
Notation Zi := (const (cons i_ (nil alphabet))).
Notation Zj := (const (cons j_ (nil alphabet))).
Notation Zk := (const (cons k_ (nil alphabet))).
Notation Zl := (const (cons l_ (nil alphabet))).
Notation Zm := (const (cons m_ (nil alphabet))).
Notation Zn := (const (cons n_ (nil alphabet))).
Notation Zo := (const (cons o_ (nil alphabet))).
Notation Zp := (const (cons p_ (nil alphabet))).
Notation Zq := (const (cons q_ (nil alphabet))).
Notation Zr := (const (cons r_ (nil alphabet))).
Notation Zs := (const (cons s_ (nil alphabet))).
Notation Zt := (const (cons t_ (nil alphabet))).
Notation Zu := (const (cons u_ (nil alphabet))).
Notation Zv := (const (cons v_ (nil alphabet))).
Notation Zw := (const (cons w_ (nil alphabet))).
Notation Zx := (const (cons x_ (nil alphabet))).
Notation Zy := (const (cons y_ (nil alphabet))).
Notation Zz := (const (cons z_ (nil alphabet))).

End Fmachine.
Export Fmachine.

Module Debug.

(**** this module was used to debug the above programs
(there were many bugs and there are probably still some,
since we haven't proven everything yet) ***************)

Definition nofilter (t:term) := false.

Definition deb_full_modus_run (l:list term) (u:order term):=
full_modus_run l u nofilter.


Definition deb_modus_run (i:nat) (l:list term) (u:order term):=
modus_run i (mop l (ostop tr)) u nofilter.

Definition deb_modus_run_step (b:mopair) (u:order term) :=
triage 
(modus_output_list (imp_list b) u) 
nofilter
(mop (nil term) (stat_ord b)). 

Definition deb_modus_output_list (b:mopair) (u:order term) :=
modus_output_list (imp_list b) u.


Definition test_lem :=
Zh / X 0 / X 1 IMP
Zh / X 1 / X 2 IMP
Zh / X 0 / (Zc / X 1 / X 2).

Definition testlist := 
cons test_lem (nil term).

Definition teststart :=
insert_term_list (
cons (Zh / Za / Zb ) (
cons (Zh / Zb / Zd) (
nil term)))
initial_term_order.

(*
Goal order term.
(*** initialize the order of knowledge ***)
display 6 teststart.
(*** initialize the spam order ***)
display 7 initial_term_order.
(*** set the term length filter to ? ***)
display 9 7.
forward testlist. 
forward testlist. 
*) 



End Debug.



Module Fcat.

(***** as a test we make up a little first-order system 
corresponding in some way to elementary category theory,
and at the end use it to find an equality in a simple
commutative diagram ***********************************)

Notation cat := (const (cons c_ (cons a_ (nil alphabet)))).
Notation ob := (const (cons o_ (cons b_ (nil alphabet)))).
Notation comp := (const (cons c_ (cons o_ (nil alphabet)))).
Notation is_id := (const (cons i_ (cons d_ (nil alphabet)))).
Notation is_inv := (const (cons i_ (cons v_ (nil alphabet)))).
Notation hom := (const (cons h_ (cons m_ (nil alphabet)))).

Notation functor := (const (cons f_ (cons u_ (nil alphabet)))).
Notation fob := (const (cons f_ (cons o_ (nil alphabet)))).
Notation fmor := (const (cons f_ (cons r_ (nil alphabet)))).
Notation fcomp := (const (cons f_ (cons c_ (nil alphabet)))).

Notation nat_trans :=
(const (cons n_ (cons a_ (nil alphabet)))).
Notation nt := (const (cons n_ (cons t_ (nil alphabet)))).

Definition symm := 
(X 0 EQU X 1) IMP (X 1 EQU X 0).

Definition trans :=
(X 0 EQU X 1) IMP (X 1 EQU X 2) IMP
(X 0 EQU X 2).

Definition hom_ob1 :=
hom / X 0 / X 1 / X 2 / X 3 IMP
ob / X 0 / X 1.
Definition hom_ob2 :=
hom / X 0 / X 1 / X 2 / X 3 IMP
ob / X 0 / X 2.

Definition plug_hom :=
hom / X 0 / X 1 / X 2 / X 3 IMP
(X 3 EQU X 4) IMP
hom / X 0 / X 1 / X 2 / X 4.

Definition plug_id :=
is_id / X 0 / X 1 / X 2 IMP
(X 2 EQU X 3) IMP
is_id / X 0 / X 1 / X 3.

Definition plug_comp_left :=
hom / X 0 / X 1 / X 2 / X 3 IMP
hom / X 0 / X 2 / X 4 / X 5 IMP
(X 5 EQU X 6) IMP
(comp / X 0 / X 5 / X 3 EQU comp / X 0 / X 6 / X 3).

Definition plug_comp_right :=
hom / X 0 / X 1 / X 2 / X 3 IMP
hom / X 0 / X 2 / X 4 / X 5 IMP
(X 3 EQU X 6) IMP
(comp / X 0 / X 5 / X 3 EQU comp / X 0 / X 5 / X 6).


Definition hom_comp :=
hom / X 0 / X 1 / X 2 / X 3 IMP
hom / X 0 / X 2 / X 4 / X 5 IMP
hom / X 0 / X 1 / X 4 / (comp / X 0 / X 5 / X 3).

Definition assoc := 
hom / X 0 / X 1 / X 2 / X 3 IMP
hom / X 0 / X 2 / X 4 / X 5 IMP
hom / X 0 / X 4 / X 6 / X 7 IMP
((comp / X 0 / (comp / X 0 / X 7 / X 5) / X 3) EQU 
((comp / X 0 / X 7 / (comp / X 0 / X 5 / X 3)))).

Definition id_hom :=
(is_id / X 0 / X 1 / X 2) IMP 
hom / X 0 / X 1 / X 1 / X 2.

Definition left_id :=
is_id / X 0 / X 1 / X 2 IMP
hom / X 0 / X 3 / X 1/ X 4 IMP
(comp / X 0 / X 2 / X 4 EQU X 4).

Definition right_id :=
is_id / X 0 / X 1 / X 2 IMP
hom / X 0 / X 1 / X 3/ X 4 IMP
(comp / X 0 / X 4 / X 2 EQU X 4).


Definition ob_fob :=
functor / X 0 / X 1 / X 2 IMP
ob / X 0 / X 3 IMP
ob / X 1 / (fob / X 2 / X 3).

Definition hom_fmor :=
functor / X 0 / X 1 / X 2 IMP
hom / X 0 / X 3 / X 4 / X 5 IMP
hom / X 1 / (fob / X 2 / X 3) / (fob / X 2 / X 4)/
(fmor / X 2 / X 5).

Definition fmor_id :=
functor / X 0 / X 1 / X 2 IMP
is_id / X 0 / X 3 / X 4 IMP
is_id / X 1 / (fob / X 2 / X 3) / (fmor / X 2 / X 4).

Definition comp_fmor :=
functor / X 0 / X 1 / X 2 IMP
hom / X 0 / X 3 / X 4 / X 5 IMP
hom / X 0 / X 4 / X 6 / X 7 IMP
(comp / X 1 / (fmor / X 2 / X 7) / (fmor / X 2 / X 5) 
EQU
fmor / X 2 / (comp / X 0 / X 7 / X 5)).

Definition fob_fcomp :=
functor / X 0 / X 1 / X 2 IMP
functor / X 1 / X 3 / X 4 IMP
ob / X 0 / X 5 IMP
(fob / (fcomp / X 4 / X 2) / X 5  EQU
fob / X 4 / (fob / X 2 / X 5)).

Definition fmor_fcomp :=
functor / X 0 / X 1 / X 2 IMP
functor / X 1 / X 3 / X 4 IMP
hom / X 0 / X 5 / X 6 / X 7 IMP
(fmor / (fcomp / X 4 / X 2) / X 7  EQU
fmor / X 4 / (fmor / X 2 / X 7)).

Definition equlist :=
cons symm (
cons trans (nil term)).

Definition catA :=
cons symm (
cons trans (
cons hom_ob1 (
cons hom_ob2 (
cons plug_hom (
cons plug_id (
cons plug_comp_left (
cons plug_comp_right (
cons hom_comp (
cons assoc (
cons id_hom (
cons left_id (
cons right_id (
cons ob_fob (
cons hom_fmor (
cons fmor_id (
cons comp_fmor (
cons fob_fcomp (
cons fmor_fcomp (
nil term))))))))))))))))))).



Ltac fwcat := forward catA. 

(****** we now take an  initial term list
containing the axioms for a diagram with two
adjacent squares of arrows, and equalities saying
that the two squares commute; using the firstorder
machine we will look for the statement that
the outside of the diagram commutes *******)

Definition twosquare :=
insert_term_list (
cons (hom / Za / Zx / Zy/ Zf) (
cons (hom / Za / Zy / Zz/ Zg) (
cons (hom / Za / Zx / Zu / Zm) (
cons (hom / Za / Zy / Zv / Zn) (
cons (hom / Za / Zz / Zw / Zp) (
cons (hom / Za / Zu / Zv / Zh) (
cons (hom / Za / Zv / Zw / Zk) (
cons (comp / Za / Zh / Zm EQU comp / Za / Zn / Zf) (
cons (comp / Za / Zk / Zn EQU comp / Za / Zp / Zg) (
nil term))))))))))
initial_term_order.

(*** un comment the following to test this out *****

Goal (order term).
(*** initialize the order of knowledge ***)
display 6 twosquare.
(*** initialize the spam order ***)
display 7 initial_term_order.
(*** set the term length filter to 5 ***)
display 9 15.
fwcat. 
fwcat. 
fwcat. 
fwcat. 
(*** note H12 which says that Zp Zg Zf = Zk Zh Zm. ***)


****************************************************)

End Fcat.



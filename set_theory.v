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


Require Export tactics.

Set Implicit Arguments.
Unset Strict Implicit.







Module Constructions.

Definition neq (x y : E) := x <> y.




Lemma sub_trans : forall a b c : E, sub a b -> sub b c -> sub a c.
unfold sub in |- *. eau. Qed. 

Lemma sub_refl : forall x, sub x x. 
Proof. 
ir. uhg; ir; am. 
Qed. 

Lemma inc_nonempty : forall x y : E, inc x y -> nonemptyT y.
ir. unfold inc in H. nin H. ap nonemptyT_intro. am.
Qed.

Lemma R_inc : forall (x : E) (a : x), inc (R a) x.
ir. unfold inc in |- *. eapply ex_intro with a. tv.
Qed.

Definition B (x y : E) (hyp : inc x y) :=
  chooseT (fun a : y => R a = x) (inc_nonempty hyp).

Lemma B_eq : forall (x y : E) (hyp : inc x y), R (B hyp) = x.
ir. unfold B in |- *.
pose (chooseT_pr (p:=fun a : y => R a = x)).
ap e. am.
Qed.

Lemma B_back : forall (x:E) (y:x) (hyp : inc (R y) x),
B hyp = y.
Proof.
ir. ap R_inj. rw B_eq. tv. 
Qed. 

Definition empty (x : E) := forall y : E, ~ inc y x. 

Lemma nonemptyT_not_empty : forall x : E, nonemptyT x -> ~ empty x.
ir. nin H. unfold not in |- *. unfold empty in |- *. ir. unfold not in H.
apply H with (R X). ap R_inc. Qed. 



Lemma not_empty_nonemptyT : forall x : E, ~ empty x -> nonemptyT x.
ir. ap excluded_middle. unfold not in |- *. ir. unfold not in H. 
ap H. unfold empty in |- *. unfold not in |- *. ir. ap H0. ap nonemptyT_intro. 
exact (B H1). Qed. 



Inductive emptyset : E :=.

Lemma emptyset_empty : forall x : E, ~ inc x emptyset.
unfold not in |- *. ir.
pose (B H).
elim e.
Qed.


Definition strict_sub (a b : E) := A (neq a b) (sub a b).

Lemma strict_sub_trans1 :
 forall a b c : E, strict_sub a b -> sub b c -> strict_sub a c.
unfold strict_sub in |- *. unfold neq in |- *. unfold not in |- *. ir. 
xd. ir. ap H. ap extensionality. 
am. rewrite H2. am. xd. 
apply sub_trans with b; au. Qed. 



Lemma strict_sub_trans2 :
 forall a b c : E, sub a b -> strict_sub b c -> strict_sub a c.
unfold strict_sub in |- *. unfold neq in |- *. unfold not in |- *. ir. 
xd. ir. ap H0. ap extensionality. 
am. rewrite <- H2. am. xd. 
apply sub_trans with b; au. Qed. 





Definition exists_unique (p : EP) :=
  A (ex p) (forall x y : E, p x -> p y -> x = y).

Lemma exT_exists : forall p : EP, (exists x : E, p x) -> ex p.
ir.
nin H.
pose ex_intro.
eau.
Qed.




Lemma p_or_not_p : forall P : Prop, P \/ ~ P.
ir.
eapply excluded_middle.
unfold not in |- *.
ir.
assert P; ap excluded_middle; unfold not in |- *; au.
Qed.


(***** by cases ********)



Definition by_cases_pr (T : Type) (P : Prop) (a : P -> T) 
  (b : ~ P -> T) (x : T) :=
  A (forall p : P, a p = x) (forall q : ~ P, b q = x).

Lemma by_cases_exists :
 forall (T : Type) (P : Prop) (a : P -> T) (b : ~ P -> T),
 exists x : T, by_cases_pr a b x.
ir. assert (P \/ ~ P). ap p_or_not_p. nin H.
eapply ex_intro with (a H). unfold by_cases_pr in |- *. xd.
ir. assert (H = p). ap proof_irrelevance. rewrite H0. tv.
ir. pose (q H). elim f.
eapply ex_intro with (b H). unfold by_cases_pr in |- *. xd.
ir. pose (H p). elim f.
ir. assert (H = q). ap proof_irrelevance. rewrite H0. tv.
Qed.

Lemma by_cases_nonempty :
 forall (T : Type) (P : Prop) (a : P -> T) (b : ~ P -> T), nonemptyT T.
ir.
ir. assert (P \/ ~ P). ap p_or_not_p. nin H.
eapply nonemptyT_intro. exact (a H).
eapply nonemptyT_intro. exact (b H).
Qed.



Definition by_cases (T : Type) (P : Prop) (a : P -> T) 
  (b : ~ P -> T) :=
  chooseT (fun x : T => by_cases_pr a b x) (by_cases_nonempty a b).


Lemma by_cases_property :
 forall (T : Type) (P : Prop) (a : P -> T) (b : ~ P -> T),
 by_cases_pr a b (by_cases a b).
ir.
cp (by_cases_exists a b).
cp (by_cases_nonempty a b).
cp (chooseT_pr H0 H).
unfold by_cases in |- *.
assert (by_cases_nonempty a b = H0).
ap proof_irrelevance.
rewrite H2.
am.
Qed.

Lemma by_cases_unique :
 forall (T : Type) (P : Prop) (a : P -> T) (b : ~ P -> T) (x : T),
 by_cases_pr a b x -> by_cases a b = x.
ir.
cp (by_cases_property a b).
ir. assert (P \/ ~ P). ap p_or_not_p. nin H1.
unfold by_cases_pr in H.  unfold by_cases_pr in H0.  xd.
transitivity (a H1). sy. au. au.
unfold by_cases_pr in H.  unfold by_cases_pr in H0.  xd.
transitivity (b H1). sy. au. au.
Qed.


Lemma by_cases_if :
 forall (T : Type) (P : Prop) (a : P -> T) (b : ~ P -> T) (p : P),
 by_cases a b = a p.
ir. eapply by_cases_unique.
unfold by_cases_pr in |- *. xd.
ir. assert (p = p0). ap proof_irrelevance. rewrite H. tv.
ir. cp (q p). elim H.
Qed.



Lemma by_cases_if_not :
 forall (T : Type) (P : Prop) (a : P -> T) (b : ~ P -> T) (q : ~ P),
 by_cases a b = b q.
ir. eapply by_cases_unique.
unfold by_cases_pr in |- *. xd.
ir.
cp (q p). elim H.
ir. assert (q = q0). ap proof_irrelevance. rewrite H. tv.
Qed.



(***** choose ******)



Definition refined_pr (p:EP) (x:E) :=
(ex p -> p x) &
~(ex p) -> x = emptyset.

Lemma refined_pr_if : forall p x,
ex p -> refined_pr p x = p x.
Proof.
ir. ap iff_eq; ir. uh H0. ee. 
au. uhg; ee. au. ir. nin (H1 H). 
Qed.

Lemma refined_pr_not : forall p x,
~(ex p) -> refined_pr p x = (x = emptyset).
Proof.
ir. ap iff_eq; ir. uh H0; ee; au. uhg; ee; au. 
ir. nin (H H1). 
Qed. 

Lemma exists_refined_pr : forall p,
ex (refined_pr p). 
Proof.
ir. apply by_cases with (ex p); ir. 
cp H; nin H. sh x. rww refined_pr_if. 
sh emptyset. rww refined_pr_not. 
Qed. 


Definition choose' : EP -> E.
ir.
eapply chooseT.
am.
eapply nonemptyT_intro.
exact Prop.
Defined.


Lemma choose'_pr : forall p : EP, ex p -> p (choose' p).
ir.
unfold choose' in |- *.
eapply chooseT_pr.
nin H.
apply ex_intro with x.
am.
Qed.

Definition choose (p:EP) := choose' (refined_pr p).

Lemma choose_pr : forall p, ex p -> p (choose p).
Proof.
ir. uf choose. cp (exists_refined_pr p). 
cp (choose'_pr H0). uh H1; ee. cp (H1 H). am. 
Qed.

Lemma choose_not : forall p, ~(ex p) -> choose p = emptyset.
Proof.
ir. uf choose. cp (exists_refined_pr p). 
cp (choose'_pr H0). uh H1; ee. 
cp (H2 H). am. 
Qed. 


Definition rep (x : E) := choose (fun y : E => inc y x). 

Lemma nonempty_rep : forall x : E, nonempty x -> inc (rep x) x. 
ir. nin H. unfold rep in |- *. ap choose_pr.
apply ex_intro with y. 
am. Qed. 







Lemma exists_proof : forall p : EP, ~ (forall x : E, ~ p x) -> ex p.
ir. unfold not in H. eapply excluded_middle. unfold not in |- *.
ir. ap H. ir. ap H0. eapply ex_intro with x.
am. 
Qed.

Lemma not_exists_pr : forall p : EP, ~ ex p <-> (forall x : E, ~ p x).
ir. unfold iff in |- *. ap conj. ir. unfold not in |- *. unfold not in H.
ir. ap H. apply ex_intro with x. am.
  ir. unfold not in |- *. unfold not in H. ir. nin H0.
apply H with x. am. 
Qed. 


(**** forking depending on a property ***)

Definition Yy : forall (P : Prop) (f : P -> E), E1.
intros P f x. apply by_cases with P. exact f.
ir. exact x. Defined. 

Lemma Yy_if :
 forall (P : Prop) (hyp : P) (f : P -> E) (x z : E), f hyp = z -> Yy f x = z. 
ir. unfold Yy in |- *. set (b := fun p : ~ P => x). 
rewrite <- H. ap by_cases_if. Qed. 

Lemma Yy_if_not :
 forall (P : Prop) (hyp : ~ P) (f : P -> E) (x z : E), x = z -> Yy f x = z. 
ir. unfold Yy in |- *. set (b := fun p : ~ P => x).
transitivity (b hyp). ap by_cases_if_not. tv. 
Qed.

Definition Y : Prop -> E2.
intros P x y.
eapply by_cases with P.
ir. exact x.
ir. exact y.
Defined.

Lemma Y_if : forall (P : Prop) (hyp : P) (x y z : E), x = z -> Y P x y = z.
ir. unfold Y in |- *. set (a := fun p : P => x). set (b := fun p : ~ P => y).
transitivity (a hyp). ap by_cases_if. transitivity x. 
tv.
am. Qed.

Lemma Y_if_not :
 forall (P : Prop) (hyp : ~ P) (x y z : E), y = z -> Y P x z = y.
ir. unfold Y in |- *. set (a := fun p : P => x). set (b := fun p : ~ P => z).
transitivity (b hyp).  ap by_cases_if_not. rewrite H. tv.
Qed.

Lemma Y_if_rw : forall (P:Prop) (hyp :P) (x y:E),
Y P x y = x.
Proof.
ir. ap Y_if. am. tv. 
Qed. 

Lemma Y_if_not_rw : forall (P:Prop) (hyp : ~P) (x y:E),
Y P x y = y.
Proof.
ir. ap Y_if_not; try am; try tv. 
Qed. 

Record Rec (x : E) (f : x -> E) : E := join {head : x; tail : f head}.
Implicit Arguments join [x f].

Definition Z : E -> EP -> E.
intros x p.
pose (T:=Rec (fun a : x => p (R a))).
exact (IM (fun t : T => R (head t))).
Defined.

Lemma Z_inc :
 forall (x : E) (p : EP) (y : E), inc y x -> p y -> inc y (Z x p).
ir. unfold Z in |- *. eapply IM_inc. unfold inc in H. nin H.
assert (p (R x0)). rewrite H. am.
pose (join (f:=fun a : x => p (R a)) x0 H1). apply ex_intro with r. tv.
Qed.

Lemma Z_sub : forall (x : E) (p : EP), sub (Z x p) x.
ir. unfold sub in |- *. ir. pose (IM_exists H).
nin e. rewrite <- H0. ap R_inc.
Qed.

Lemma Z_pr : forall (x : E) (p : EP) (y : E), inc y (Z x p) -> p y.
ir. unfold inc in H. nin H. unfold Z in x0.
pose (R_inc x0). pose (IM_exists i). 
nin e. pose (tail x1).

simpl in p0. rewrite H0 in p0. 
rewrite <- H. am.
Qed.

Lemma Z_all :
 forall (x : E) (p : EP) (y : E), inc y (Z x p) -> A (inc y x) (p y).
ir. xd. assert (sub (Z x p) x). ap Z_sub.
ap H0; am.
set (x_ := Z_pr H); au.
Qed.

Ltac Ztac :=
  match goal with
  | id1:(inc ?X1 (Z _ _)) |- _ => pose (Z_all id1); xd
  |  |- (inc _ (Z _ _)) => ap Z_inc; au
  | _ => idtac
  end.


Definition X (x : E) (f : x -> E) (y : E) :=
  Yy (fun hyp : inc y x => f (B hyp)) emptyset. 

Lemma X_eq :
 forall (x : E) (f : x -> E) (y z : E),
 (exists a : x, A (R a = y) (f a = z)) -> X f y = z. 
ir. nin H. xd. unfold X in |- *. 
assert (inc y x). rewrite <- H. ap R_inc. 
apply Yy_if with H1. assert (B H1 = x0).  
ap R_inj. rewrite B_eq. au. rewrite H2. am.
Qed. 

Lemma X_rewrite : forall (x : E) (f : x -> E) (a : x), X f (R a) = f a. 
ir. 
ap X_eq. apply ex_intro with a. xd.
Qed. 


Definition cut (x : E) (p : x -> Prop) :=
  Z x (fun y : E => forall hyp : inc y x, p (B hyp)). 

Lemma cut_sub : forall (x : E) (p : x -> Prop), sub (cut p) x. 
ir. unfold cut in |- *. ap Z_sub. Qed. 


Definition cut_to (x : E) (p : x -> Prop) (y : cut p) :=
  B (cut_sub (p:=p) (R_inc y)). 

Lemma cut_to_R_eq :
 forall (x : E) (p : x -> Prop) (y : cut p), R (cut_to y) = R y. 
ir. unfold cut_to in |- *. rewrite B_eq. tv. Qed. 



Lemma cut_pr : forall (x : E) (p : x -> Prop) (y : cut p), p (cut_to y).
ir. unfold cut_to in |- *. unfold cut in y. 
set (k := fun y : E => forall hyp : inc y x, p (B hyp)) in *. 
pose (R_inc y). 
Ztac.
Qed. 


Lemma cut_inc :
 forall (x : E) (p : x -> Prop) (y : x), p y -> inc (R y) (cut p). 
ir. unfold cut in |- *. ap Z_inc. ap R_inc. ir. 
assert (B hyp = y). ap R_inj. ap B_eq. rewrite H0. 
am. Qed. 





Definition IM_lift : forall (a : E) (f : a -> E), IM f -> a. 
ir. assert (exists x : a, f x = R X0). ap IM_exists. 
ap R_inc. assert (nonemptyT a). nin H. 
ap nonemptyT_intro; am. exact (chooseT (fun x : a => f x = R X0) H0). 
Defined. 

Lemma IM_lift_pr :
 forall (a : E) (f : a -> E) (x : IM f), f (IM_lift x) = R x. 
ir. assert (exists y : a, f y = R x). ap IM_exists. 
ap R_inc.  uf IM_lift. set
  (K :=
   ex_ind (fun (x0 : a) (_ : (fun u : a => f u = R x) x0) => nonemptyT_intro x0)
     (IM_exists (R_inc x))) in *. 
pose (chooseT_pr K H). am. 
Qed. 


Definition elt x y := inc y x.

Lemma elt_inc : forall x y, elt x y = inc y x.
Proof. ir. tv. Qed.

Hint Rewrite elt_inc : aw. 


End Constructions.

Export Constructions.

Module Little.



Inductive one_point : E :=
    point : one_point.

Definition singleton (x : E) := IM (fun p : one_point => x).

Lemma singleton_inc : forall x : E, inc x (singleton x).
ir. unfold singleton in |- *. ap IM_inc.
apply ex_intro with point. tv. Qed.

Lemma singleton_eq : forall x y : E, inc y (singleton x) -> y = x.
ir. pose (IM_exists H). nin e.
sy. tv. Qed.


Lemma singleton_inj : forall x y : E, singleton x = singleton y -> x = y. 
ir. assert (inc x (singleton y)). rewrite <- H.
ap singleton_inc.
ap singleton_eq. am. Qed.









Inductive two_points : E :=
  | first : two_points
  | second : two_points.

Definition doubleton_map : forall x y : E, two_points -> E.
intros x y t. nin t. exact x. exact y. Defined.

Definition doubleton (x y : E) := IM (doubleton_map x y).

Lemma doubleton_first : forall x y : E, inc x (doubleton x y).
ir. unfold doubleton in |- *. ap IM_inc. apply ex_intro with first.
tv. Qed.


Lemma doubleton_second : forall x y : E, inc y (doubleton x y).
ir. unfold doubleton in |- *. ap IM_inc. apply ex_intro with second.
tv. Qed.



Lemma doubleton_or :
 forall x y z : E, inc z (doubleton x y) -> z = x \/ z = y.
ir. pose (IM_exists H). nin e. nin x0.
compute in H0.
intuition.
compute in H0. intuition. Qed.   


Lemma doubleton_inj :
 forall x y z w : E,
 doubleton x y = doubleton z w -> A (x = z) (y = w) \/ A (x = w) (y = z). 
ir. assert (inc x (doubleton z w)). rewrite <- H. ap doubleton_first. 
pose (doubleton_or H0). assert (inc y (doubleton z w)). 
rewrite <- H. 
ap doubleton_second. pose (doubleton_or H1). nin o.
nin o0. assert (inc w (doubleton x y)). rewrite H. 
ap doubleton_second. pose (doubleton_or H4). nin o. 
ap or_introl. xd. rewrite H5. rewrite H2. am.
ap or_introl. xd. 
ap or_introl. xd. 
nin o0.
ap or_intror. xd. 
assert (inc z (doubleton x y)). rewrite H. ap doubleton_first. 
pose (doubleton_or H4). nin o. ap or_introl. xd. 
ap or_introl. xd. rewrite H5. rewrite H3. 
am. Qed.

Lemma doubleton_singleton : forall x,
doubleton x x = singleton x.
Proof.
ir. ap extensionality; uhg; ir.
cp (doubleton_or H). nin H0. rw H0;
ap singleton_inc. rw H0; ap singleton_inc.
cp (singleton_eq H). rw H0. ap doubleton_first. 
Qed.

End Little.

Export Little. 

Module Basic_Realizations.

Lemma nat_zero_emptyset : R 0 = emptyset.
Proof.
ap extensionality; uhg; ir. 
cp (nat_realization_O H). elim H0. 
nin (B H).  
Qed.

Lemma false_emptyset : emptyset = False :> Type. 
Proof.
ap extensionality; uhg; ir. 
nin (B H). elim (B H). 
Qed.

Lemma R_false_emptyset : R False = emptyset.
Proof.
ap extensionality; uhg; ir. 
assert (R False = False). ap prop_realization. 
rwi H0 H. nin (B H). nin (B H). 
Qed.

Lemma true_proof_emptyset : forall t : True, R t = emptyset.
Proof.
ir. cp (true_proof_realization_empty t). rw H. 
rw nat_zero_emptyset. tv. 
Qed.

Lemma true_singleton_emptyset : singleton emptyset = True.
Proof.
ap extensionality; uhg; ir. cp (singleton_eq H). 
rw H0. assert True. tv. cp (true_proof_emptyset H1). 
uf inc. sh H1. am. 
cp (true_proof_emptyset (B H)). 
rwi B_eq H0. rw H0. ap singleton_inc. 
Qed.

Lemma R_true_singleton_emptyset : R True = singleton emptyset.
Proof.
rw prop_realization. sy; ap true_singleton_emptyset. 
Qed.

Lemma R_one_singleton_emptyset : R 1 = singleton emptyset.
Proof.
ap extensionality; uhg; ir. 
rwi nat_realization_S H. nin H. 
rwi nat_zero_emptyset H. nin (B H). 
rwi nat_zero_emptyset H. rw H. 
ap singleton_inc. 
rw nat_realization_S. ap or_intror. 
cp (singleton_eq H). rw nat_zero_emptyset; am. 
Qed.

Lemma R_two_prop : R 2 = Prop. 
Proof.
ap extensionality; uhg; ir. 
rwi nat_realization_S H. nin H. 
rwi R_one_singleton_emptyset H. 
cp (singleton_eq H). rw H0. 
uf inc. sh False. rww R_false_emptyset. 
rwi R_one_singleton_emptyset H. 
rwi true_singleton_emptyset H. 
uhg; sh True. rw prop_realization; sy; am. 
apply by_cases with (B H). ir. 
assert (B H = True). ap iff_eq; ir. 
tv. am. assert (x = R True). wr H1. 
rww B_eq. rw nat_realization_S. 
ap or_intror. rw R_one_singleton_emptyset. 
wr R_true_singleton_emptyset. am. 
ir. assert (B H = False). ap iff_eq; ir. 
au. elim H1. 
rw nat_realization_S. ap or_introl. 
rw R_one_singleton_emptyset. 
assert (x = R (B H)). rww B_eq. 
rw H2. rw H1. 
rw R_false_emptyset. ap singleton_inc. 
Qed. 

End Basic_Realizations.
Export Basic_Realizations.

Module Complement. 

Definition complement (a b : E) := Z a (fun x : E => ~ inc x b).

Lemma inc_complement :
 forall a b x : E, inc x (complement a b) = (inc x a & ~ inc x b).
ir.
ap iff_eq; ir.
ufi complement H; Ztac.

uf complement; ap Z_inc.
xd.

xd.
Qed. 


Lemma use_complement :
 forall a b x : E, inc x a -> ~ inc x (complement a b) -> inc x b.
ir.
ap excluded_middle.
uf not; ir.
ap H0.
uf complement; ap Z_inc.
am.

am.
Qed. 

End Complement.
Export Complement.

Module Pair.

Export Little.

Definition pair (x y : E) :=
  doubleton (singleton x) (doubleton emptyset (singleton y)).

Definition is_pair (u : E) :=
  ex (fun x : E => ex (fun y : E => u = pair x y)).

Lemma lem1 : forall x y z w : E, pair x y = pair z w -> x = z.
ir. assert (inc (singleton x) (pair z w)). rewrite <- H.
unfold pair in |- *. ap doubleton_first. unfold pair in H0. pose (doubleton_or H0). 
nin o. ap singleton_inj. am. assert (inc emptyset (singleton x)).
rewrite H1. ap doubleton_first. assert (inc (singleton w) (singleton x)). 
rewrite H1. ap doubleton_second. assert (emptyset = x :> Type). ap singleton_eq. am.
assert (singleton w = x). ap singleton_eq. am. assert (inc w emptyset).
rewrite H4. rewrite <- H5. ap singleton_inc. pose (emptyset_empty H6). 
elim f. Qed. 


Lemma lem2 : forall x y z w : E, pair x y = pair z w -> y = w.
ir. assert (inc (doubleton emptyset (singleton y)) (pair z w)). 
rewrite <- H. unfold pair in |- *. ap doubleton_second. unfold pair in H0.
pose (doubleton_or H0). nin o. assert (inc emptyset (singleton z)).
rewrite <- H1. ap doubleton_first. assert (inc (singleton y) (singleton z)).
rewrite <- H1. ap doubleton_second. pose (singleton_eq H2).
pose (singleton_eq H3). assert (inc y emptyset). rewrite e. rewrite <- e0.
ap singleton_inc. pose (emptyset_empty H4). elim f. 
assert (inc (singleton y) (doubleton emptyset (singleton w))). 
rewrite <- H1. ap doubleton_second. pose (doubleton_or H2). 
nin o. assert (inc y emptyset). rewrite <- H3. ap singleton_inc. 
pose (emptyset_empty H4). elim f. ap singleton_inj. am. Qed. 




Definition pr1 (u : E) :=
  choose (fun x : E => ex (fun y : E => u = pair x y)).
Definition pr2 (u : E) :=
  choose (fun y : E => ex (fun x : E => u = pair x y)).

Notation J := pair.
Notation P := pr1.
Notation Q := pr2. 


Definition pair_recovers (u : E) := pair (pr1 u) (pr2 u) = u.

Lemma pair_recov : forall u : E, is_pair u -> pair_recovers u.
ir. unfold is_pair in H. unfold pair_recovers in |- *. 
pose (choose_pr H). assert (ex (fun y : E => ex (fun x : E => u = pair x y))).
nin e. apply ex_intro with x. apply ex_intro with (pr1 u). am. pose (choose_pr H0).
nin e. nin e0. assert (u = pair (pr1 u) x). 
am. assert (u = pair x0 (pr2 u)). am. 
assert (pair (pr1 u) x = pair x0 (pr2 u)). rewrite <- H3.
am. pose (lem1 H5). rewrite e. sy. am. 
Qed. 

Lemma pair_is_pair : forall x y : E, is_pair (pair x y). 
ir. unfold is_pair in |- *. apply ex_intro with x.
apply ex_intro with y. tv. Qed. 


Lemma pr1_pair : forall x y : E, pr1 (pair x y) = x.
ir. set (u := pair x y) in *. assert (is_pair u). 
unfold u in |- *. ap pair_is_pair. pose(pair_recov H). 
unfold pair_recovers in (type of p). unfold u in (type of p). pose (lem1 p). am. Qed. 

 

Lemma pr2_pair : forall x y : E, pr2 (pair x y) = y.
ir. set (u := pair x y) in *. assert (is_pair u). 
unfold u in |- *. ap pair_is_pair. pose (pair_recov H). 
unfold pair_recovers in (type of p). unfold u in (type of p). pose (lem2 p). am. Qed. 

Lemma pair_extensionality : forall a b, 
is_pair a -> is_pair b -> pr1 a = pr1 b -> pr2 a = pr2 b ->
a = b.
Proof.
ir. transitivity (pair (pr1 a) (pr2 a)).
assert (pair_recovers a). app pair_recov. 
uh H3. sy; am. rw H1; rw H2. 
assert (pair_recovers b). app pair_recov. 
uh H3. am.  
Qed. 

Lemma uneq2 : forall (f:E-> E-> E) (a b c d:E),
a=c -> b = d -> f a b = f c d.
Proof.
ir. rw H; rww H0. 
Qed. 


Definition V (x f : E) := choose (fun y : E => inc (pair x y) f).

Lemma V_inc :
 forall x z f : E,
 ex (fun y : E => inc (pair x y) f) -> z = V x f -> inc (pair x z) f. 
ir. pose (choose_pr H). rewrite H0. am. Qed. 

Lemma V_or : forall x f,
(inc (pair x (V x f)) f) \/
((forall z, ~(inc (pair x z) f)) & (V x f = emptyset)).
Proof.
ir. apply by_cases with (ex (fun y=> inc (pair x y) f)).
ir. ap or_introl. app V_inc. 
ir. ap or_intror. ee. ir. uhg; ee. ir. ap H. 
sh z; am. 
uf V. ap choose_not. am. 
Qed. 


End Pair.
Export Pair.

Module Image. 

Definition create (x : E) (f : E1) := IM (fun a : x => f (R a)). 

Lemma incl :
 forall (x : E) (f : E1) (a : E), inc a x -> inc (f a) (create x f).
ir. unfold create in |- *. ap IM_inc. 
apply ex_intro with (B H). pose (B_eq H). rewrite e. 
tv. Qed. 


Lemma show_inc :
 forall (x : E) (f : E1) (z : E),
 ex (fun a : E => A (inc a x) (f a = z)) -> inc z (create x f).
ir. nin H. xd. rewrite <- H0. 
ap incl. am. Qed. 

Lemma ex :
 forall (x : E) (f : E1) (a : E),
 inc a (create x f) -> ex (fun b : E => A (inc b x) (f b = a)).
ir. pose (IM_exists H). nin e. apply ex_intro with (R x0). xd. unfold inc in |- *. apply ex_intro with x0. 
tv. Qed. 

Lemma inc_rw : forall  f x y,
inc y (create x f) =
exists z, (inc z x & f z = y).
Proof.
ir. ap iff_eq; ir. cp (ex H).
nin H0. sh x0; xd. 
ap show_inc. nin H. sh x0; xd. 
Qed. 

Lemma subset : forall a b x y,
sub x y ->
(forall u, inc u x -> a u = b u) ->
sub (Image.create x a) (Image.create y b).
Proof.
ir. uhg; ir. rwi Image.inc_rw H1. nin H1; ee. 
rw Image.inc_rw. sh x1; xd. wr H2; sy; ap H0; am.  
Qed. 

Lemma same : forall (a b:E1) (x y:E),
x = y ->
(forall u, inc u x -> a u = b u) ->
Image.create x a = Image.create y b.
Proof.
ir. 
ap extensionality. ap subset. rw H; uhg; ir; am. am. 
ap subset. rw H; uhg; ir; am. ir. sy; ap H0. rw H; am. 
Qed. 


Lemma refl : forall a x,
(forall y, inc y x -> a y = y) -> 
create x a = x. 
Proof.
ir. ap extensionality; uhg; ir. rwi inc_rw H0. nin H0; ee. 
wr H1. rw H. am. am. rw inc_rw. sh x0. 
xd. 
Qed.


Lemma trans : forall a b x,
create (create x a) b = create x (fun y=> b (a y)).
Proof.
ir. 
ap extensionality; uhg; ir. 
rwi inc_rw H. nin H; ee. 
rw inc_rw. rwi inc_rw H. nin H; ee. 
sh x2. ee; try am. rw H1; am. 
rwi inc_rw H. nin H; ee. rw inc_rw. 
sh (a x1); ee. rw inc_rw. sh x1; ee; try tv. am.  
Qed. 

End Image.

Module Powerset. 

Definition powerset (x : E) := IM (fun p : x -> Prop => cut p).


Lemma powerset_inc : forall x y : E, sub x y -> inc x (powerset y). 
ir. unfold powerset in |- *. ap IM_inc. apply ex_intro with (fun b : y => inc (R b) x). ap extensionality. unfold sub in |- *. ir. 
pose (B H0). pose (B_eq H0). pose (cut_pr c). assert (x0 = R (cut_to c)). transitivity (R c). unfold c in |- *. 
au. sy. ap cut_to_R_eq. rewrite H1. am. 
unfold sub in |- *. ir. pose (B H0). pose (B_eq H0). 
rewrite <- e. unfold cut in |- *. ap Z_inc. ap H. rewrite e. 
am. ir. pose (B_eq hyp). rewrite e0. 
rewrite e. am. Qed. 


Lemma powerset_sub : forall x y : E, inc x (powerset y) -> sub x y.
ir. unfold powerset in H. pose (IM_exists H). nin e. 
rewrite <- H0. ap cut_sub. Qed. 

Lemma powerset_inc_rw : forall x y, inc x (powerset y) = sub x y.
Proof. 
ir. ap iff_eq; ir. ap powerset_sub; am. ap powerset_inc; am. 
Qed. 

End Powerset. 
Export Powerset. 

Module Union. 

Record Integral (x : E) : E :=  {param : x; elt : R param}.

Definition union (x : E) := IM (fun i : Integral x => R (elt (x:=x) i)).




Lemma union_inc : forall x y a : E, inc x y -> inc y a -> inc x (union a).
ir. 
pose (B H0). assert (R a0 = y). unfold a0 in |- *. ap B_eq. 
assert (inc x (R a0)). rewrite H1. am. 
pose (B H2). pose (Build_Integral (x:=a) (param:=a0) r). unfold union in |- *.
ap IM_inc. apply ex_intro with i. change (R r = x) in |- *. 
unfold r in |- *. ap B_eq. Qed. 



Lemma union_exists :
 forall x a : E,
 inc x (union a) -> ex (fun y : E => A (inc x y) (inc y a)).
ir. unfold union in H. pose (IM_exists H). 
nin e. apply ex_intro with (R (param x0)). 
xd. rewrite <- H0. ap R_inc. ap R_inc. Qed. 

Definition union2 (x y : E) := union (doubleton x y). 


Lemma union2_or : forall x y a : E, inc a (union2 x y) -> inc a x \/ inc a y.
ir. unfold union2 in H. pose (union_exists H). 
nin e. xd. pose (doubleton_or H1). 
nin o. rewrite H2 in H0. intuition. 
rewrite H2 in H0; intuition. Qed. 


Lemma union2_first : forall x y a : E, inc a x -> inc a (union2 x y).
ir. unfold union2 in |- *. apply union_inc with x. am.
ap doubleton_first. Qed. 

Lemma union2_second : forall x y a : E, inc a y -> inc a (union2 x y).
ir. unfold union2 in |- *. apply union_inc with y. am.
ap doubleton_second. Qed. 


Definition tack_on (x y : E) := union2 x (singleton y). 

Lemma tack_on_or : forall x y z : E, inc z (tack_on x y) ->
(inc z x \/ z = y). 
Proof. 
ir. ufi tack_on H. cp (union2_or H). nin H0.
ap or_introl; am. ap or_intror. ap singleton_eq; am. 
Qed. 

Lemma tack_on_inc: forall x y z:E,
(inc z (tack_on x y) ) = (inc z x \/ z = y).
Proof.
ir. ap iff_eq. ir; ap tack_on_or. am. ir.
nin H. uf tack_on. ap union2_first. am.
uf tack_on. ap union2_second. rw H. 
ap singleton_inc. 
Qed.

Definition tack x y := tack_on y x.

Lemma tack_or : forall x y z : E, inc z (tack y x) ->
(inc z x \/ z = y).
Proof.
ir. uf tack. app tack_on_or.
Qed.

Lemma tack_inc :  forall x y z:E,
(inc z (tack y x) ) = (inc z x \/ z = y).
Proof.
ir. uf tack. app tack_on_inc.
Qed. 

End Union. 

Export Union. 

Module Intersection. 


Definition intersection (x : E) :=
  Z (rep x) (fun y : E => forall z : E, inc z x -> inc y z). 

Lemma intersection_inc :
 forall x a : E,
 nonempty x -> (forall y : E, inc y x -> inc a y) -> inc a (intersection x). 
ir. unfold intersection in |- *. ap Z_inc. 
pose (nonempty_rep H). ap H0. am. am. 
Qed. 

Lemma intersection_forall :
 forall x a y : E, inc a (intersection x) -> inc y x -> inc a y. 
ir. unfold intersection in H. 
Ztac. Qed.

Lemma intersection_sub : forall x y : E, inc y x -> sub (intersection x) y.
ir.
unfold sub in |- *.
ir.
apply intersection_forall with x; au.
Qed.


Definition intersection2 (x y : E) := intersection (doubleton x y).

Lemma intersection2_inc :
 forall x y a : E, inc a x -> inc a y -> inc a (intersection2 x y).
ir.
unfold intersection2 in |- *.
ap intersection_inc.
apply nonempty_intro with x.
ap doubleton_first.
ir.
cp (doubleton_or H1).
nin H2.
rewrite H2.
am.
rewrite H2.
am.
Qed.

Lemma intersection2_first :
 forall x y a : E, inc a (intersection2 x y) -> inc a x.
ir.
unfold intersection2 in H.
eapply intersection_forall with (doubleton x y).
am.
ap doubleton_first.
Qed.




Lemma intersection2_second :
 forall x y a : E, inc a (intersection2 x y) -> inc a y.
ir.
unfold intersection2 in H.
eapply intersection_forall with (doubleton x y).
am.
ap doubleton_second.
Qed.


Lemma intersection_use_inc :
 forall x y : E, inc y (intersection x) -> forall z : E, inc z x -> inc y z.
ir. apply intersection_forall with x; am.
Qed. 


End Intersection.

Export Intersection. 





Module Transposition.

Definition create (i j a : E) := Y (a = i) j (Y (a = j) i a).



Lemma not_i_not_j : forall i j a : E, a <> i -> a <> j -> create i j a = a.
ir. unfold create in |- *. apply (Y_if_not H). sy. 
apply (Y_if_not H0). tv. 
Qed.

Lemma i_j_j_i : forall i j a : E, create i j a = create j i a.
ir. unfold create in |- *. apply by_cases with (a = i). ir. 
ap (Y_if H). sy. apply by_cases with (a = j). 
ir. ap (Y_if H0). rewrite <- H. am. 
ir. ap (Y_if_not H0). sy. ap (Y_if H). 
tv. ir. ap (Y_if_not H). apply by_cases with (a = j). 
ir. ap (Y_if H0). sy. ap (Y_if H0). 
tv. 
ir. ap (Y_if_not H0). ap (Y_if_not H0). 
ap (Y_if_not H). tv. Qed. 


Lemma i_j_i : forall i j : E, create i j i = j.
ir. unfold create in |- *. assert (i = i); tv. ap (Y_if H). 
tv. 
Qed.

Lemma i_j_j : forall i j : E, create i j j = i.
ir. rewrite i_j_j_i. ap i_j_i. Qed. 




Lemma i_i_a : forall i a : E, create i i a = a.
ir. apply by_cases with (a = i). ir. rewrite H. 
ap i_j_j. ir. unfold create in |- *. ap (Y_if_not H). 
sy. ap (Y_if_not H). tv. 
Qed.



Lemma surj : forall i j a : E, ex (fun b : E => create i j b = a).
ir.
apply by_cases with (a = i).
ir. apply ex_intro with j. rewrite H. ap i_j_j. 
ir. apply by_cases with (a = j). ir. 
apply ex_intro with i. rewrite H0. ap i_j_i. 
ir. 
apply ex_intro with a. ap not_i_not_j. 
am. am. 
Qed.


Lemma involutive : forall i j a : E, create i j (create i j a) = a. 
ir. apply by_cases with (a = i). ir. 
rewrite H. rewrite i_j_i. ap i_j_j. 
apply by_cases with (a = j). ir. rewrite H. rewrite i_j_j. 
ap i_j_i. ir. pose (not_i_not_j H0 H). 
rewrite e. am. Qed. 

Lemma inj : forall i j a b : E, create i j a = create i j b -> a = b.
ir. transitivity (create i j (create i j a)). 
sy; ap involutive. rewrite H. ap involutive. 
Qed. 



End Transposition.



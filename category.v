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

Require Import Arith.
Require Export universe.



Ltac cw := autorewrite with cw; try tv; try am. 


Module Category.
Export Universe. 

Module Notations.





Definition Objects  := R (o_(b_(j_ DOT ))).
Definition Composition := R (c_(m_(p_ DOT ))).
Definition Identity := R (i_(d_ (t_ DOT ))).
Definition Structure := R (s_ (t_ (r_ DOT))). 
(*** the latter is a placeholder for any additional
structure we might want to put on ****)


Definition objects a := V Objects a.
Definition morphisms a := V Underlying a.
Definition composition a := V Composition a.
Definition identity a  := V Identity a. 
Definition structure a := V Structure a.






Definition create (o m:E) (c : E2) (i:E1) (s:E):=
denote Objects o (
denote Underlying m (
denote Composition 
(L m (fun u => L (Z m (fun v => source u = target v)) (c u))) (
denote Identity (L o i) (
denote Structure s (
stop))))). 





Lemma objects_create :forall o m c i s, objects (create o m c i s) = o. 
ir; uf objects; uf create. drw. 
Qed. 


Lemma morphisms_create : forall o m c i s, morphisms 
(create o m c i s) = m. 
ir; uf morphisms; uf create. drw. 
Qed. 

Lemma structure_create : forall o m c i s,
structure (create o m c i s) = s.
Proof.
ir; uf structure; uf create. drw.
Qed. 


Lemma composition_create : forall o m c i s,
composition (create o m c i s) = 
L m (fun u => (L (Z m (fun v => source u = target v)) (c u))).
Proof.
ir. uf create. uf composition. drw.
Qed.



Lemma identity_create : forall o m c i s,
identity (create o m c i s)  = L o i.
Proof.
ir. uf create. uf identity. drw. 
Qed.


Hint Rewrite objects_create morphisms_create composition_create
identity_create : cw.

Definition comp a u v := V v (V u (composition a)).
Definition id a x := V x (identity a).

Definition like a := a = create (objects a)
(morphisms a) (comp a) (id a) (structure a).

Lemma create_extensionality : forall o m c i  s o1 m1 c1 i1 s1,
o = o1 -> m = m1 -> 
(forall u v, inc u m -> inc v m -> source u = target v 
-> c u v = c1 u v) ->
(forall x, inc x o -> i x = i1 x) ->
s = s1 -> 
create o m c i s = create o1 m1 c1 i1 s1.
Proof.
ir. wr H. wr H0. 
assert (lem1: 
L m (fun u => L (Z m (fun v => source u = target v)) (c u)) =
L m (fun u => L (Z m (fun v => source u = target v)) (c1 u))). 
ap Function.create_extensionality. tv. 
ir. ap Function.create_extensionality. tv. 
ir. ap H1. am. Ztac. Ztac. 

assert (lem2: L o i = L o i1).
ap Function.create_extensionality. tv.
au. 
uf create. rw lem1. rw lem2. rw H3. reflexivity. 
Qed. 

Lemma create_like : forall o m c i s,
like (create o m c i s).
Proof.
ir. uf like. ap create_extensionality. 
rw objects_create; tv. rw morphisms_create; tv. 
ir. 
uf comp. 
rw composition_create. 
rw create_V_rewrite. rw create_V_rewrite. 
tv. Ztac. am. ir. 
uf id. rw identity_create. 
rw create_V_rewrite. tv. am. 
rw structure_create. tv. Qed. 

Definition is_ob a x := inc x (objects a).
Definition is_mor a u := inc u (morphisms a).



End Notations.
Export Notations.



Lemma is_ob_create : forall o m c i  s x,
is_ob (create o m c i s) x = (inc x o).
Proof.
ir. 
uf is_ob. cw. 
Qed. 

Lemma is_mor_create : forall o m c i s u,
is_mor (create o m c i s) u = (inc u m).
Proof.
ir. uf is_mor. cw. 
Qed. 

Lemma comp_create : forall o m c i s u v,
inc u m -> inc v m -> source u = target v -> 
comp (create o m c i s) u v = c u v.
Proof.
ir. uf comp. cw. aw. 
Ztac. 
Qed. 

Lemma id_create : forall o m c i s x,
inc x o -> 
id (create o m c i s) x = i x.
Proof.
ir. uf id. cw. aw. 
Qed. 


(**** axioms ****)

Definition are_composable a f g :=
is_mor a f &
is_mor a g &
source f = target g.


Definition is_ob_facts a x :=
is_ob a x &
is_mor a (id a x) &
source (id a x) = x &
target (id a x) = x &
(forall f, is_mor a f-> source f = x -> comp a f (id a x) = f) &
(forall f, is_mor a f-> target f = x -> comp a (id a x) f = f).


Definition is_mor_facts a f:=
is_mor a f & 
is_ob a (source f) & 
is_ob a (target f) &
comp a (id a (target f)) f = f &
comp a f (id a (source f)) = f &
Arrow.like f.

Definition are_composable_facts a f g:=
are_composable a f g &
is_mor a (comp a f g) &
source (comp a f g) = source g &
target (comp a f g) = target f.

Definition axioms a := 
(forall x, is_ob a x = is_ob_facts a x) &
(forall u, is_mor a u = is_mor_facts a u) &
(forall u v, are_composable a u v = are_composable_facts a u v) &
(forall u v w, are_composable a u v -> are_composable a v w ->
   (comp a (comp a u v) w) = (comp a u (comp a v w))) &
like a.

Definition composable a u v :=
axioms a & are_composable a u v.

Definition mor a u := axioms a & is_mor a u.

Definition ob a x := axioms a & is_ob a x.

Definition mor_facts c u := 
mor c u &
ob c (source u) &
ob c (target u) &
comp c (id c (target u)) u = u &
comp c u (id c (source u)) = u &
Arrow.like u.

Lemma mor_facts_rw : forall c u,
mor c u = mor_facts c u. 
Proof.
ir. ap iff_eq; ir. 
cp H; uh H; ee. cp H; uh H; ee. 
rwi H3 H1. uh H1; ee. 
uhg; xd. uhg; xd. uhg; xd. uh H; ee; am. 
Qed. 

Definition ob_facts c x :=
ob c x &
mor c (id c x) &
composable c (id c x) (id c x) &
source (id c x) = x &
target (id c x) = x &
comp c (id c x) (id c x) = (id c x)&
(forall u, mor c u -> source u = x -> comp c u (id c x) = u)&
(forall u, mor c u -> target u = x -> comp c (id c x) u = u).

Lemma ob_facts_rw : forall c x,
ob c x = ob_facts c x. 
Proof. 
ir. ap iff_eq; ir. cp H; uh H; ee. 
cp H; uh H; ee. clear H6. cp H1; uh H1; ee. 
rwi H H6. uh H6; ee. 
uhg; xd. uhg; xd. 
uhg; xd. uhg; xd. 
rw H8; rw H9; tv. 
ir. ap H10. lu. am. 
ir. ap H11; lu. lu. 
Qed. 

Definition composable_facts c u v :=
axioms c &
are_composable c u v &
mor c u &
mor c v &
mor c (comp c u v)&
source u = target v & 
source (comp c u v) = source v &
target (comp c u v) = target u. 

Lemma composable_facts_rw : forall c u v,
composable c u v = composable_facts c u v.
Proof.
ir; ap iff_eq; ir. cp H; uh H; ee. 
cp H; uh H; ee. clear H6. 
uhg; dj; try am. 
uhg; ee. am. lu. uhg; ee; lu. 
rwi H4 H1. uh H1; ee. uhg; ee; try am. 
uh H7; ee; am. 
rwi H4 H7. uh H7. ee. am. 
rwi H4 H7. uh H7. ee. am. 
uhg; uh H; xd. 
Qed. 

Lemma show_composable : forall c u v,
mor c u -> mor c v -> source u = target v ->
composable c u v.
Proof.
ir. cp H; uh H; ee. cp H; uh H; ee. 
uhg; ee. am. uh H0; ee. uhg; ee; try am.  
Qed. 

Lemma show_composable_facts : forall c u v,
mor c u -> mor c v -> source u = target v ->
composable_facts c u v.
Proof.
ir. wr composable_facts_rw; ap show_composable; am. 
Qed. 

Definition associativity_facts c u v w :=
composable_facts c u v &
composable_facts c v w &
composable_facts c u (comp c v w) &
composable_facts c (comp c u v) w &
comp c u (comp c v w) = comp c (comp c u v) w.

Lemma show_associativity_facts : forall c u v w,
composable c u v -> composable c v w -> 
associativity_facts c u v w. 
Proof.
ir. cp H; uh H; ee. 
cp H; uh H; ee. clear H7. 
uhg.
do 4 (wr composable_facts_rw). 
ee; try am. 
rwi composable_facts_rw H0;
rwi composable_facts_rw H1. 
uh H0; uh H1; ee.
ap show_composable. 
am. am. 
rw H20. am. 
ap show_composable. 
rwi composable_facts_rw H1; uh H1; ee; am. 
rwi composable_facts_rw H0; uh H0; ee; am.
rwi composable_facts_rw H1; uh H1; ee.
rw H12. 
uh H0; ee. uh H14; ee. am. 
sy; ap H6. am. uh H0; ee; am. 
Qed. 

Definition morphism_property (o m:E) (c:E2) (i:E1) u:=
inc u m  & inc (source u) o & inc (target u) o &
c u (i (source u)) = u &
c (i (target u)) u = u &
Arrow.like u.

Definition object_property (o m:E) (i:E1) x :=
inc x o & inc (i x) m & source (i x) = x & target (i x) = x. 

Definition composable_property (m:E) (c:E2)  u v:=
inc u m & inc v m & source u = target v & 
inc (c u v) m &
source (c u v) = source v &
target (c u v) = target u.


Definition property (o m:E) (c:E2) (i:E1) :=
(forall x, inc x o = object_property o m i x) &
(forall u, inc u m = morphism_property o m c i u) &
(forall u v, inc u m -> inc v m -> source u = target v ->
   composable_property m c  u v) &
(forall u v w, inc u m -> inc v m -> inc w m -> 
   source u = target v -> source v = target w ->
   c (c u v) w = c u (c v w)).

Lemma are_composable_create_rw : forall o m c i s u v,
are_composable (create o m c i s) u v = 
(inc u m & inc v m & source u = target v).
Proof.
ir. ap iff_eq; ir. uh H.
rwi is_mor_create H. rwi is_mor_create H. xd. 
uhg. do 2 (rw is_mor_create). xd. 
Qed. 

Lemma create_axioms : forall o m (c : E2) (i:E1) (s:E),
property o m c i ->
axioms (create o m c i s).
Proof.
ir. 
set (k:=(create o m c i s)).


assert (lem1 : forall u v, are_composable k u v = 
(inc u m & inc v m & source u = target v)).
ir. ap iff_eq; ir. ufi k H0. 
rwi are_composable_create_rw H0. 
xd.
uf k. rw are_composable_create_rw. 
xd. 
uh H; ee. 


assert (lem2: forall u, is_mor k u = inc u m). 
ir. ap iff_eq; ir. ufi k H3. 
rwi is_mor_create H3. am. 
uf k; rw is_mor_create; am. 

assert (lem3: forall u v, inc u m -> inc v m -> 
source u = target v -> comp k u v = c u v).
ir. uf k. rw comp_create; tv. 


assert (lem5: forall x, inc x o -> id k x = i x).
ir. uf k. rw id_create. tv. am. 

assert (lem6: forall (x:E), is_ob k x = inc x o).
ir; ap iff_eq; ir. ufi k H3. rwi is_ob_create H3. am.
uf k; rw is_ob_create; am. 


(*** the proof of axioms ***)
(*** mor facts ***)
uhg; ee; ir. 
ap iff_eq; ir. cp H3; rwi lem6 H3. 
rwi H H3. uh H3; ee. 
uhg; dj. am. rw lem2. rw lem5. am. am.
rw lem5; am. 
rw lem5; am. rw lem5. rw lem3. 
rwi lem2 H12. rwi H0 H12. uh H12; ee.
wr H13. am. wr lem2. am. 
wr lem5. wr lem2. am. am. rw H7. am. 
am. rw lem3. rw lem5. rwi lem2 H13. 
rwi H0 H13. uh H13; ee. wr H14. 
am. lu. wr lem2. am. wr lem2. am. 
rw H10. sy; am. lu. 

ap iff_eq; ir. rwi lem2 H3. 
rwi H0 H3. uh H3; ee. 
uhg; ee. rw lem2; am. rw lem6; am. rw lem6; am. 
rw lem3. rw lem5. am. am. 
rww lem5. rwi H H5. lu. am. 
rww lem5. rwi H0 H3. uh H3; ee. 
rwi H H10. uh H10; ee. am. 

rww lem3. rw lem5. am. am. 
rw lem5. rwi H H4. uh H4; ee. 
am. am. rw lem5. rwi H H4. 
uh H4; ee. sy; am. am. am.  
lu. 


ap iff_eq; ir. cp H3; uh H3; ee. 
rwi lem2 H3. rwi lem2 H5. 
util (H1 u v). am. am. am. 
uh H7; ee. 
uhg; xd. rw lem2. rww lem3. 
rww lem3. rww lem3. lu. 

(*** associativity ***)
assert (inc u m). 
wr lem2; lu. 
assert (inc v m). 
wr lem2; lu. 
assert (inc w m). 
wr lem2; lu. 
assert (source u = target v). lu.
assert (source v = target w). lu. 
rww lem3. rww lem3. rww lem3. rww lem3. 
rwi lem1 H3; rwi lem1 H4; ee. 
ap H2; try am. 
rww lem3. cp (H1 _ _ H6 H7 H9). 
lu. 
rww lem3. cp (H1 _ _ H5 H6 H8). 
util (H1 v w). am. am. am. 
uh H11; ee. rw H16. am. 

util (H1 u v). am. am. am. 
rw lem3. uh H10; ee. am. am. am. am. 
rww lem3. util (H1 u v). am. am. am. 
uh H10; ee. rw H14. am. 

uf k. 
ap create_like. 
Qed. 



Lemma ob_existence_rw : forall a x,
ob a x = (exists f, (mor a f & source f = x)).
Proof.
ir. ap iff_eq; ir. 
rwi ob_facts_rw H. uh H; ee. sh (id a x); xd. 
nin H. ee. rwi mor_facts_rw H. uh H; ee. wr H0; am. 
Qed. 

Lemma left_id: forall a b x u,
ob a x -> mor a u -> target u = x -> a = b ->
comp a (id b x) u = u.
Proof.
ir. rwi mor_facts_rw H0; uh H0; ee.
wr H2; wr H1; am.  
Qed.

Lemma right_id : forall a b x u, 
ob a x -> mor a u -> source u = x -> a= b ->
comp a u (id b x) = u.
Proof.
ir. rwi mor_facts_rw H0; uh H0; ee.
wr H2; wr H1; am.
Qed. 

Lemma left_id_unique : forall a e x,
axioms a -> mor a e -> 
source e = x ->
(forall f, composable a e f -> comp a e f = f) ->
e = id a x.
Proof.
ir. 
rwi mor_facts_rw H0. wr H1. uh H0; ee.
transitivity (comp a e (id a x)). 
rw right_id; try tv; try lu. wr H1; am.
wr H2. wr H1; tv. ap show_composable. 
am. rwi ob_facts_rw H3; uh H3; ee; am. 
rwi ob_facts_rw H3; uh H3; ee; sy; am.  
Qed. 

Lemma right_id_unique : forall a e x,
axioms a -> mor a e -> 
target e = x ->
(forall f, composable a f e -> comp a f e = f) ->
e = id a x.
Proof.
ir. 
rwi mor_facts_rw H0. wr H1. uh H0; ee.
transitivity (comp a (id a (target e)) e). 
rw left_id; try tv; try lu. 
ap H2. ap show_composable. 
rwi ob_facts_rw H4; uh H4; ee; am. am. 
rwi ob_facts_rw H4; uh H4; ee; am.  
Qed. 

Definition same_data (o m : E) (c : E2) (i: E1)
(o1 m1 : E) (c1 : E2) (i1: E1):=
(forall x, inc x o = inc x o1) &
(forall u, inc u m = inc u m1) &
(forall u v, inc u m -> inc v m -> source u = target v -> c u v = c1 u v) &
(forall x, inc  x o -> i x = i1 x).


Lemma ob_create : forall o m c i s x,
property o m c i-> ob (create o m c i s) x = inc x o. 
Proof.
ir. 
set (k:= create o m c i s). 
assert (lem0 : axioms k). 
uf k; ap create_axioms; am. 
assert (lem1 : forall x, ob k x = is_ob k x).
ir. ap iff_eq; ir. lu. uhg; ee; am. 
rw lem1. uf k; rw is_ob_create; tv. 
Qed. 

Lemma mor_create : forall o m c i s u,
property o m c i-> mor (create o m c i s) u = inc u m. 
Proof.
ir. 
set (k:= create o m c i s). 
assert (lem0 : axioms k). 
uf k; ap create_axioms; am. 
assert (lem1 : forall u, mor k u = is_mor k u).
ir. ap iff_eq; ir. lu. uhg; ee; am. 
rw lem1. uf k; rw is_mor_create; tv. 
Qed. 

Lemma uncomp : forall a b u v u1 v1,
a = b -> u = u1 -> v = v1 -> comp a u v = comp b u1 v1.
Proof.
ir. rw H; rw H0; rw H1; tv. 
Qed. 

Lemma U_morphisms : forall a,
(U a) = morphisms a. 
Proof.
ir. tv. 
Qed. 

Lemma is_mor_mor : forall a u,
axioms a -> is_mor a u -> mor a u.
Proof.
ir. uh H; ee. 
rwi H1 H0. uhg; uh H0; xd. 
uhg; au. 
Qed.

Lemma is_ob_ob : forall a x,
axioms a -> is_ob a x -> ob a x.
Proof.
ir. uh H; ee. 
rwi H H0. uhg; uh H0; xd. 
uhg; au. 
Qed. 

Lemma ob_is_ob : forall a x,
ob a x -> is_ob a x.
Proof.
ir. lu. 
Qed.

Lemma mor_id : forall a x,
ob a x -> mor a (id a x).
Proof.
ir. rwi ob_facts_rw H; uh H; ee. am. 
Qed.

Lemma mor_id_rw : forall a x,
ob a x -> mor a (id a x) = True.
Proof.
ir. ap iff_eq; ir; try tv. app mor_id. 
Qed. 

Lemma source_id : forall a x,
ob a x -> source (id a x) = x.
Proof.
ir. rwi ob_facts_rw H; uh H; ee. am. 
Qed.

Lemma target_id : forall a x,
ob a x -> target (id a x) = x.
Proof.
ir. rwi ob_facts_rw H; uh H; ee. am. 
Qed. 

Lemma ob_source : forall a u,
mor a u -> ob a (source u) = True.
Proof.
ir. rwi mor_facts_rw H; uh H; ee. 
ap iff_eq; ir; try tv; try am. 
Qed.

Lemma ob_target : forall a u,
mor a u -> ob a (target u) = True.
Proof.
ir. rwi mor_facts_rw H; uh H; ee. 
ap iff_eq; ir; try tv; try am.  
Qed. 

Lemma mor_comp : forall a b u v,
mor a u -> mor a v -> 
source u = target v -> a = b -> mor a (comp b u v)= True.
Proof.
ir. wr H2. assert (composable_facts a u v).
ap show_composable_facts; am. 
ap iff_eq; ir; try tv; try am. lu. 
Qed.


Lemma source_comp : forall a u v,
mor a u -> mor a v -> 
source u = target v -> source (comp a u v) = source v.
Proof.
ir. assert (composable_facts a u v).
ap show_composable_facts; am. lu. 
Qed.


Lemma target_comp : forall a u v,
mor a u -> mor a v -> 
source u = target v ->target (comp a u v) = target u.
Proof.
ir. assert (composable_facts a u v).
ap show_composable_facts; am. lu. 
Qed.


Lemma assoc : forall a b u v w,
mor a u -> mor a v -> mor a w ->
source u = target v -> source v = target w ->
a= b ->
comp a (comp b u v) w = comp a u (comp b v w).
Proof.
ir. wr H4. 
assert (associativity_facts a u v w). 
ap show_associativity_facts; ap show_composable;
am.   
uh H5; ee. sy; am. 
Qed. 



Lemma mor_arrow_like : forall a u,
mor a u -> Arrow.like u. 
Proof.
ir. rwi mor_facts_rw H. lu. 
Qed. 
 

Hint Rewrite left_id right_id mor_id_rw source_id target_id
ob_source ob_target mor_comp source_comp target_comp : cw. 

Lemma mor_inc_U : forall a u,
mor a u -> inc u (U a).
Proof.
ir. change (is_mor a u); lu. 
Qed.

Lemma mor_is_mor : forall a u,
mor a u -> is_mor a u.
Proof.
ir. lu.
Qed.





Definition opp' a :=
Notations.create (objects a) (Image.create (morphisms a) flip)
(fun u v => flip (comp a (flip v) (flip u)))
(fun x => flip (id a x)) (structure a).

Lemma is_ob_opp' : forall a x,
is_ob (opp' a) x = is_ob a x.
Proof.
ir. uf opp'. rw is_ob_create. tv. 
Qed.

Lemma structure_opp' : forall a, structure (opp' a) =
structure a. 
Proof.
ir. uf opp'. rww structure_create. 
Qed. 

Lemma inc_image_create_flip : forall a u,
inc u (Image.create (morphisms a) flip) = is_mor (opp' a) u.
Proof.
ir. uf opp'. rw is_mor_create. tv. 
Qed.

Lemma is_mor_opp' : forall a u,
is_mor (opp' a) u = is_mor a (flip u).
Proof.
ir. uf opp'. rw is_mor_create. 
rw Image.inc_rw. app iff_eq; ir. 
nin H. ee. wr H0. rw flip_flip. 
am. 
sh (flip u). ee. am. rww flip_flip. 
Qed.


Lemma comp_opp' : forall a u v,
is_mor (opp' a) u -> is_mor (opp' a) v -> 
source u = target v -> 
comp (opp' a) u v = flip (comp a (flip v) (flip u)).
Proof.
ir. uf opp'. rw comp_create. tv. 
rww inc_image_create_flip. 
rww inc_image_create_flip. am. 
Qed.

Lemma id_opp' : forall a x,
is_ob (opp' a) x -> 
id (opp' a) x = flip (id a x).
Proof.
ir. uf opp'. rw id_create. tv. 
ufi opp' H. rwi is_ob_create H. am. 
Qed. 

Lemma opp'_opp' : forall a, 
axioms a -> opp' (opp' a) = a.
Proof.
ir. assert (like a). 
lu.  uh H0. 
transitivity (create (objects a) (morphisms a) (comp a) (id a)
(structure a)).
assert (Image.create (Image.create (morphisms a) flip) flip 
= morphisms a). 
ap extensionality; uhg; ir. rwi Image.inc_rw H1.
nin H1. ee. rwi Image.inc_rw H1. nin H1. ee. 
wr H2. wr H3. rw flip_flip. am. 
ap Image.show_inc. sh (flip x). ee. 
ap Image.show_inc. sh x. ee. am. tv. 
rww flip_flip. 

uf opp'. ap create_extensionality. 
rww objects_create. rw morphisms_create.
am. 
rw morphisms_create. rw H1. ir. 
rw comp_create. rw flip_flip. rw flip_flip. rww flip_flip.
ap Image.show_inc. sh v; ee; try am. tv. 
ap Image.show_inc. sh u; ee; try tv; try am. 
rw source_flip. rw target_flip. sy; am. 
apply mor_arrow_like with a. app is_mor_mor. 
apply mor_arrow_like with a. app is_mor_mor. 
rw objects_create. ir. 
rw id_create. rww flip_flip. am. rww structure_create.
sy; am. 
Qed. 



Lemma opp'_axioms : forall a, 
axioms a -> axioms (opp' a).
Proof.
ir. 
assert (morli : forall u, is_mor a u -> Arrow.like u). 
ir. uh H; ee. rwi H1 H0. uh H0; ee. am. 
assert (obidli : forall x, is_ob a x -> Arrow.like (id a x)). 
ir. uh H. ee. rwi H H0. uh H0. ee. 
ap morli. am. 
assert (flifli : forall u, flip (flip u) = u). 
ir. rw flip_flip. tv. 

 

uf opp'. ap create_axioms. 
assert (ax : axioms a).
am. 
uh H; ee. 
assert (alike : like a).
am. clear H3. 
uhg; dj;
try (ap iff_eq; ir). 

assert (ob a x). apply is_ob_ob. am. am. 
uhg; ee. am. 
ap Image.show_inc. sh (id a x). ee. 
ap mor_is_mor. ap mor_id. ap is_ob_ob. am. 
am. tv. rw source_flip. rww target_id. 
ap obidli. am. 
rw target_flip. rww source_id. app obidli. 
lu. 

assert (mor a (flip u)). 
rwi Image.inc_rw H4. nin H4; ee. 
ap is_mor_mor. am. wr H5. rw flip_flip.
am. 


uhg; ee. am. wr (flifli u). 
rw source_flip. 
uh H5; ee. rwi H0 H6. lu. 
ap morli. lu. 
wr source_flip. 
ap ob_is_ob. rww ob_source. 
rw like_flip. ap morli. lu. 
rw flip_flip. rw left_id. rww flip_flip. 
wr target_flip. rww ob_target. 
rw like_flip. ap morli. lu. 
am. rww target_flip. 
rw like_flip. ap morli. lu. tv. 
rw flip_flip. rw right_id. rww flip_flip.
wr source_flip. rww ob_source. 
rw like_flip. ap morli. lu. 
am. rww source_flip. 
rw like_flip. ap morli. lu. tv. 
rw like_flip. ap morli. lu. 
lu. 

assert (mor a (flip u)). 
rwi Image.inc_rw H5. nin H5; ee. wr H8. rw flip_flip.
app is_mor_mor. 
assert (mor a (flip v)). 
rwi Image.inc_rw H6. nin H6; ee. wr H9. rw flip_flip.
app is_mor_mor. 
assert (Arrow.like u). 
rw like_flip. ap morli. ap mor_is_mor. am. 
assert (Arrow.like v). 
rw like_flip. ap morli. ap mor_is_mor. am. 

uhg; ee. am. am. am. 
ap Image.show_inc. 
sh (comp a (flip v) (flip u)). ee. 
ap mor_is_mor. rw mor_comp. tv. 
am. am. rw source_flip. rw target_flip. sy; am. 
rw like_flip. ap morli. ap mor_is_mor. tv. 
rw like_flip. ap morli. ap mor_is_mor. am. tv. 
tv. rw source_flip. rw target_comp. rww target_flip.

am. am. rw source_flip. rw target_flip. sy; am. am. am.
ap morli. ap mor_is_mor. rw mor_comp. 
tv. am. am. 
 rw source_flip. rw target_flip. sy; am. 

tv. am. tv. 
rw target_flip. rw source_comp. rww source_flip. 

am. am. rw source_flip. rww target_flip. 
sy; am. am. 

ap morli. ap mor_is_mor. rw mor_comp. 
tv. am. am. 
 rww source_flip. rww target_flip. sy; am. 

tv. 
rw flip_flip. rw flip_flip. 

assert (mor a (flip u)). 
rwi Image.inc_rw H6. nin H6; ee. wr H11. rw flip_flip.
app is_mor_mor. 
assert (mor a (flip v)). 
rwi Image.inc_rw H7. nin H7; ee. wr H12. rw flip_flip.
app is_mor_mor. 
assert (mor a (flip w)). 
rwi Image.inc_rw H8. nin H8; ee. wr H13. rw flip_flip.
app is_mor_mor. 
assert (Arrow.like u). 
rw like_flip. ap morli. ap mor_is_mor. am. 
assert (Arrow.like v). 
rw like_flip. ap morli. ap mor_is_mor. am. 
assert (Arrow.like w). 
rw like_flip. ap morli. ap mor_is_mor. am. 

rw assoc. tv. am. am. am. 
rww source_flip. rww target_flip. sy; am. 
sy; rww source_flip; rww target_flip. tv. 
Qed. 


Definition opp a := Y (axioms a) (opp' a) a.

Lemma axioms_opp : forall a,
axioms (opp a) = axioms a.
Proof.
ir. apply by_cases with (axioms a); ir.
assert (opp a = opp' a). 
uf opp. ap (Y_if  H). tv. 
rw H0. 
ap iff_eq; ir. am. ap opp'_axioms. am. 
assert (opp a = a). 
uf opp. ap (Y_if_not H). tv. rww H0. 
Qed. 

Lemma opp_axioms : forall a, axioms a -> axioms (opp a).
Proof.
ir. rww axioms_opp. 
Qed. 

Lemma opp_opp : forall a, opp (opp a) = a.
Proof.
ir. apply by_cases with (axioms a); ir. 
assert (opp a = opp' a).
uf opp. ap (Y_if  H). tv. 
rw H0. 
assert (axioms (opp' a)). ap opp'_axioms. am. 
assert (opp (opp' a) = opp' (opp' a)).
uf opp. ap (Y_if  H1). reflexivity. 
rw H2. rw opp'_opp'. tv. am. 
assert (opp a = a). 
uf opp. ap (Y_if_not H). tv. rw H0. 
uf opp. ap (Y_if_not H). tv.
Qed. 

Lemma structure_opp : forall a, structure (opp a) = structure a.
Proof.
ir. 
apply by_cases with (axioms a); ir. 
assert (opp a = opp' a).
uf opp. ap (Y_if  H). tv. 
rw H0. rww structure_opp'. 
assert (opp a = a). 
uf opp. ap (Y_if_not H). tv.
rww H0. 
Qed. 

Lemma ob_opp' : forall a x,
axioms a -> 
ob (opp' a) x = ob a x.
Proof.
ir. 
sy. ap iff_eq; ir. 
uhg; ee. ap opp'_axioms. lu. 
rw is_ob_opp'. lu. 
uhg; ee. am. 
wr is_ob_opp'. lu. 
Qed. 

Lemma mor_opp' : forall a u,
axioms a -> 
mor (opp' a) u = mor a (flip u).
Proof.
ir. 
assert (lem : forall b v, axioms b -> 
mor (opp' b) v -> mor b (flip v)).
ir. uhg; ee. am. uh H1; ee. 
rwi is_mor_opp' H2. am. 
ap iff_eq; ir. au. 
assert (u = flip (flip u)). 
rw flip_flip; tv. 
uhg; ee. ap opp'_axioms. am. 
rw is_mor_opp'. app  mor_is_mor. 
Qed. 

Lemma unfold_opp : forall a, axioms a -> 
opp a = opp' a.
Proof.
ir. uf opp. ap (Y_if H). tv. 
Qed.


Lemma ob_opp : forall a x,
ob (opp a) x = ob a x.
Proof.
ir. ap iff_eq; ir. 
assert (axioms a). wr axioms_opp. uh H; ee; am. 
rwi unfold_opp H. rwi ob_opp' H. am. 
am. am. 
assert (axioms a). uh H; ee; am. 
rww unfold_opp. rww ob_opp'. 
Qed. 

Lemma mor_opp : forall a u,
mor (opp a) u = mor a (flip u).
Proof.
ir. ap iff_eq; ir. 
assert (axioms a). wr axioms_opp. uh H; ee; am. 
rwi unfold_opp H. rwi mor_opp' H. am. 
am. am. 
assert (axioms a). uh H; ee; am. 
rww unfold_opp. rww mor_opp'. 
Qed. 

Lemma comp_opp : forall a u v,
mor (opp a) u -> mor (opp a) v -> source u = target v ->
comp (opp a) u v = flip (comp a (flip v) (flip u)).
Proof.
ir. assert (axioms a). 
wr axioms_opp. uh H; ee; am. 
rw unfold_opp. rw comp_opp'. 
tv. ap mor_is_mor. wrr unfold_opp. 
ap mor_is_mor. wrr  unfold_opp. tv. am. 
Qed.


Lemma id_opp : forall a x,
ob (opp a) x -> 
id (opp a) x = flip (id a x).
Proof.
ir. assert (axioms a). 
wr axioms_opp. uh H; ee; am. 
rw unfold_opp. rww id_opp'. ap ob_is_ob. 
wrr unfold_opp. am.  
Qed. 


Lemma composable_opp : forall a u v,
axioms a -> 
composable (opp a) u v = composable a (flip v) (flip u).
Proof.
ir. ap iff_eq; ir. 
rwi composable_facts_rw H0; ap show_composable;  
try (wr mor_opp; lu); try (rw mor_opp; lu). 
rw source_flip. rw target_flip; try (sy; lu). 
apply mor_arrow_like with (opp a); lu. 
apply mor_arrow_like with (opp a); lu. 
rwi composable_facts_rw H0. ap show_composable. 
uh H0; ee. rww mor_opp. rww mor_opp. 
lu. uh H0; ee. 
wr source_flip. wr target_flip. 
sy; am. rw like_flip. apply mor_arrow_like with a; lu. 
rw like_flip; apply mor_arrow_like with a; lu. 
Qed. 



Definition are_inverse a u v :=
mor a u & mor a v &
source u = target v &
source v = target u &
comp a u v = id a (source v) &
comp a v u = id a (source u).



Lemma are_inverse_symm :forall a u v,
are_inverse a u v -> are_inverse a v u.
Proof.
ir. uh H; ee. uhg; ee; try am. 
Qed. 

Definition invertible a u := 
exists v, are_inverse a u v.

Definition inverse a u := choose (are_inverse a u).

Lemma invertible_inverse :
forall a u, invertible a u -> are_inverse a u (inverse a u).
Proof.
ir. exact (choose_pr H). 
Qed.

Lemma inverse_unique : forall a u v w,
are_inverse a u v -> are_inverse a u w -> v = w.
Proof.
ir. uh H; uh H0; ee. 
transitivity (comp a (comp a v u) w).
rw assoc. rw H4.
rw right_id. tv. 
uh H0; ee. cw. am.  rww H3. tv. 
am. am. am. am. am. tv. 
rw H10. cw. cw.  sy; am. 
Qed. 

Lemma inverse_uni : forall v w,
(exists a, exists u, (are_inverse a u v & are_inverse a u w)) ->
v = w. 
Proof.
ir. nin H. nin H. ee. 
exact (inverse_unique H H0). 
Qed. 

Lemma inverse_eq : forall a u v,
are_inverse a u v -> inverse a u = v. 
Proof.
ir. ap inverse_uni. sh a. sh u. ee.
ap invertible_inverse. uhg. sh v; am. am. 
Qed. 

Lemma inverse_invertible : forall a u,
invertible a u -> invertible a (inverse a u).
Proof.
ir. uhg. sh u. ap are_inverse_symm. 
ap invertible_inverse. am. 
Qed.

Lemma inverse_inverse : forall a u,
invertible a u -> inverse a (inverse a u) = u.
Proof.
ir. apply inverse_unique with a (inverse a u). 
ap invertible_inverse. ap inverse_invertible. am. 
ap are_inverse_symm. ap invertible_inverse. am. 
Qed. 

Lemma source_inverse : forall a u,
invertible a u -> source (inverse a u) = target u.
Proof.
ir. cp (invertible_inverse H). uh H0; ee. 
lu. 
Qed.

Lemma target_inverse : forall a u,
invertible a u -> target (inverse a u) = source u.
Proof.
ir. cp (invertible_inverse H). uh H0; ee. 
sy; lu. 
Qed.

Lemma left_inverse : forall a u,
invertible a u -> comp a (inverse a u) u = id a (source u).
Proof.
ir. cp (invertible_inverse H). uh H0; ee. am. 
Qed.

Lemma right_inverse : forall a u,
invertible a u -> comp a u (inverse a u) = id a (target u).
Proof.
ir. cp (invertible_inverse H). uh H0; ee. 
rwi source_inverse H4. am. am.  
Qed. 



Lemma mor_inverse : forall a u,
invertible a u -> 
mor a (inverse a u).
Proof.
ir. cp (invertible_inverse H). uh H0; ee. lu. 
Qed.

Lemma mor_inverse_rw : forall a b u,
invertible a u -> a = b -> 
mor a (inverse b u) = True.
Proof.
ir. app iff_eq; ir. wr H0. app mor_inverse. 
Qed.

Hint Rewrite source_inverse target_inverse left_inverse
right_inverse mor_inverse_rw :cw.

Lemma composable_inverse_left : forall a u,
invertible a u -> composable a (inverse a u) u.
Proof.
ir. cp (invertible_inverse H). uh H0; ee.
ap show_composable; lu. 
Qed.

Lemma composable_inverse_right : forall a u,
invertible a u -> composable a u (inverse a u).
Proof.
ir. cp (invertible_inverse H). uh H0; ee.
ap show_composable; lu.
Qed. 

Lemma composable_inverse : forall a u v,
composable a u v -> invertible a u -> invertible a v ->
composable a (inverse a v) (inverse a u).
Proof.
ir. 
cp (invertible_inverse H0).
cp (invertible_inverse H1). 
cp H. rwi composable_facts_rw H; uh H; ee. 
ap show_composable. lu. lu. 
rw source_inverse; try am. rw target_inverse; try am. 
sy; am. 
Qed. 

Lemma invertible_comp_are_inverse : forall a u v,
composable a u v -> invertible a u -> invertible a v ->
are_inverse a (comp a u v) (comp a (inverse a v) (inverse a u)).
Proof.
ir. 
cp (invertible_inverse H0).
cp (invertible_inverse H1). 
cp H. rwi composable_facts_rw H; uh H; ee. 


uhg; ee; try am. cw. lu. lu.  
cw. 
sy; lu. 
cw.  lu. lu. cw. sy; lu. 
cw. lu. lu. cw. sy; lu. 
cw. 
rw assoc. 
assert (comp a v (comp a (inverse a v) (inverse a u))=
inverse a u).
wr assoc. cw. 
cw. cw. cw. cw. cw. lu. cw. cw.  sy; lu. tv. 
rw H12. cw. lu. lu. cw. lu. lu. 
cw. sy; lu. lu. cw. lu. lu. cw. 
sy; lu. tv. lu. lu. cw. sy; lu. 
rw assoc. 
assert (comp a (inverse a u) (comp a u v) = v).
wrr assoc. cw. cw. sy; lu. cw. cw. 
rw H12. cw. cw. cw. cw. cw. sy; lu. cw. tv. 
Qed. 

Lemma invertible_comp : forall a u v,
composable a u v -> invertible a u -> invertible a v ->
invertible a (comp a u v).
Proof.
ir. uhg; sh (comp a (inverse a v) (inverse a u)). 
ap invertible_comp_are_inverse; am. 
Qed.

Lemma inverse_comp : forall a u v,
composable a u v -> invertible a u -> invertible a v ->
inverse a (comp a u v) = comp a (inverse a v) (inverse a u).
Proof.
ir. ap inverse_eq. ap invertible_comp_are_inverse; am. 
Qed. 


Lemma identity_are_inverse : forall a x,
ob a x -> are_inverse a (id a x) (id a x). 
Proof.
ir. rwi ob_facts_rw H. uh H; ee. 
uhg; ee; try am. cw. cw. cw. cw. 
Qed. 

Lemma inverse_id : forall a x,
ob a x -> inverse a (id a x) = id a x.
Proof.
ir. ap inverse_eq. ap identity_are_inverse; am. 
Qed. 

Hint Rewrite inverse_id : cw.

Ltac alike :=
match goal with 
id1 : (mor _ ?X1) |- (Arrow.like ?X1) =>
exact (mor_arrow_like id1) |
_=>fail 
end. 


End Category.





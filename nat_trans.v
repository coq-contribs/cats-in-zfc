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
Require Export functor.

Ltac nw := autorewrite with nw; try tv; try am. 
Ltac nw' := repeat autorewrite with nw; try tv; try am. 

Ltac nr := autorewrite with nw.
Ltac fr := autorewrite with fw.
Ltac cr := autorewrite with cw. 

Module Nat_Trans.
Export Functor.

(*** we don't use the following first try because
it turns out to be the same as a functor and this
causes problems with rewriting:
Definition create f g t :=
Arrow.create f g (L (objects (source f)) t).
************************************************)

Definition Ntrans := R (n_ (t_ (r_ DOT))).

Definition ntrans_arrow_create f t :=
denote Ntrans (L (objects (source f)) t) stop.

Definition ntrans_arrow_ev n x := 
V x (V Ntrans n).

Lemma ntrans_arrow_ev_create : forall f t x,
inc x (objects (source f)) -> ntrans_arrow_ev 
(ntrans_arrow_create f t) x = t x.
Proof.
ir. uf ntrans_arrow_ev. 
uf ntrans_arrow_create. 
drw. aw. 
Qed.

Definition create f g t :=
Arrow.create f g (ntrans_arrow_create f t).

Definition ntrans n x :=
ntrans_arrow_ev (arrow n) x.


Lemma source_create : forall f g t, source (create f g t) = f.
Proof.
ir.  uf create. rww Arrow.source_create.  
Qed.

Lemma target_create : forall f g t, target (create f g t) = g.
Proof.
ir.  uf create. rww Arrow.target_create. 
Qed.


Lemma ntrans_create : forall f g t x, 
inc x (objects (source f)) -> ntrans (create f g t) x = (t x).
Proof.
ir. uf create. 
uf ntrans. aw. 
rww ntrans_arrow_ev_create. 
Qed.

Definition osource n := source (source n).
Definition otarget n := target (target n).

Lemma osource_create : forall f g t, 
osource (create f g t) = source f.
Proof.
ir. uf osource. 
rw source_create; tv. 
Qed.

Lemma otarget_create : forall f g t, 
otarget (create f g t) = target g.
Proof.
ir. uf otarget. 
rw target_create; tv. 
Qed.



Lemma create_extensionality : forall f g t f1 g1 t1,
f = f1 -> g = g1 -> (forall x, inc x (objects (source f)) ->
t x = t1 x) -> 
create f g t = create f1 g1 t1.
Proof.
ir. wr H; wr H0. uf create. 
ap uneq. 
uf ntrans_arrow_create. 
up. app Function.create_extensionality. 
ir. au. 
Qed. 


Definition like t := 
create (source t) (target t) (ntrans t) = t. 

Lemma create_like : forall f g t,
like (create f g t). 
Proof.
ir. uf like. ap create_extensionality.
rww source_create. rww target_create. 
ir. rww ntrans_create. 
rwi source_create H. am. 
Qed. 


Definition axioms t :=
(like t) &
(Category.axioms (osource t)) &
(Category.axioms (otarget t)) &
(Functor.axioms (source t)) &
(Functor.axioms (target t)) &
(source (target t)) = (osource t) &
(target (source t)) = (otarget t) &
(forall x, ob (osource t) x -> 
     mor (otarget t) (ntrans t x)) &
(forall x, ob (osource t) x -> 
     source (ntrans t x) = fob (source t) x) &
(forall x, ob (osource t) x -> 
     target  (ntrans t x) = fob (target t) x) &
(forall u, mor (osource t) u ->
   comp (otarget t) (ntrans t (target u)) 
      (fmor (source t) u)
  =comp (otarget t) (fmor (target t) u) 
      (ntrans t (source  u))).

Definition property f g t :=
(Functor.axioms f) &
(Functor.axioms g) &
(source f) = (source g) &
(target f) = (target g) &
(forall x, ob (source f) x ->
  mor (target g) (t x)) &
(forall x, ob (source f) x ->
  source  (t x) = fob f x) &
(forall x, ob (source f) x ->
  target (t x) = fob g x) &
(forall u, mor (source f) u ->
  comp (target g) (t (target  u)) (fmor f u) =
  comp (target g) (fmor g u) (t (source  u))).

Lemma create_axioms :
forall f g t, property f g t -> 
axioms (create f g t).
Proof.
ir. uf axioms.
ee; ir;  try (ap create_like); do 3 
(first [rw osource_create| rw otarget_create|
rw source_create| rw target_create| idtac]).
uh H; ee. uh H; ee; am. 
uh H; ee. uh H0; ee; am.  lu. lu. 
uh H; ee; sy; am. uh H; ee; am. 

rw ntrans_create. uh H; ee. 
ap H4. rwi osource_create H0. am. 
change (is_ob (source f) x). 
rwi osource_create H0. lu. 
rwi osource_create H0. 
rw ntrans_create. uh H; ee. au. 
change (is_ob (source f) x); lu. 
rwi osource_create H0. 
rw ntrans_create. 
uh H; ee. au. 
change (is_ob (source f) x); lu. 
rwi osource_create H0. 
rw ntrans_create. rw ntrans_create. 
uh H; ee. au. 
change (is_ob (source f) (source u)). 
assert (ob (source f) (source u)). 
cw. lu. 
change (is_ob (source f) (target u)). 
assert (ob (source f) (target u)). 
cw. lu. 
Qed. 

Lemma axioms_like : forall t, axioms t ->
like t = True.
Proof.
ir. app iff_eq; ir. lu. 
Qed.

Lemma axioms_property : forall t, axioms t ->
property (source t) (target t) (ntrans t).
Proof.
ir. uh H; uhg; xd.
Qed. 

Lemma source_target : forall a,
axioms a -> source (target a) = osource a.
Proof.
ir. lu. 
Qed.

Lemma target_source : forall a,
axioms a -> target (source a) = otarget a.
Proof.
ir. lu. 
Qed. 

Lemma mor_ntrans : forall a c x,
axioms a -> ob (osource a) x -> 
c = otarget a ->
mor c (ntrans a x).
Proof.
ir. uh H; ee. rw H1; au.  
Qed.

Lemma mor_ntrans_rw : forall a c x,
axioms a -> ob (osource a) x -> 
c = otarget a ->
mor c (ntrans a x) = True.
Proof.
ir. app iff_eq; ir; app mor_ntrans.
Qed. 

Lemma source_ntrans : forall a x,
axioms a -> ob (osource a) x ->
source  (ntrans a x) = fob (source a) x.
Proof.
ir.  uh H; xd. 
Qed.

Lemma target_ntrans : forall a x,
axioms a -> ob (osource a) x ->
target (ntrans a x) = fob (target a) x.
Proof.
ir.  uh H; xd. 
Qed.

Hint Rewrite axioms_like
source_ntrans target_ntrans mor_ntrans_rw : nw. 

Lemma carre : forall a u,
axioms a -> mor (osource a) u ->
comp (otarget a) (ntrans a (target  u)) (fmor (source a) u)=
comp (otarget a) (fmor (target a) u) (ntrans a (source  u)).
Proof.
ir. uh H; xd. 
Qed.

Lemma carre_verbose_rw : forall a c1 f u,
axioms a -> mor (osource a) u ->
c1 = otarget a ->  
f = source a -> 
comp c1 (ntrans a (target u)) (fmor f u)=
comp (otarget a) (fmor (target a) u) (ntrans a (source u)).
Proof.
ir. 
rw H1; rw H2. ap carre; am. 
Qed. 


Lemma functor_axioms_source : forall a, axioms a -> 
Functor.axioms (source a) = True.
Proof.
ir. app iff_eq; ir.  uh H; ee. am. 
Qed.

Lemma functor_axioms_target : forall a, axioms a ->
Functor.axioms (target a) = True.
Proof.
ir. app iff_eq; ir. uh H; ee. am. 
Qed.

Lemma category_axioms_osource : forall a, axioms a ->
Category.axioms (osource a) = True.
Proof.
ir. app iff_eq; ir. uh H; ee. am. 
Qed.

Lemma category_axioms_otarget : forall a, axioms a ->
Category.axioms (otarget a) = True.
Proof.
ir. app iff_eq; ir. uh H; ee. am. 
Qed.

Lemma source_source : forall a, source (source a) = osource a.
Proof. ir. tv. Qed.

Lemma target_target : forall a, target (target a) = otarget a.
Proof. ir. tv. Qed.

Hint Rewrite functor_axioms_source functor_axioms_target
category_axioms_osource category_axioms_otarget
source_source target_target : nw. 

Definition vident f :=
create f f (fun x => id (target f) (fob f x)).

Lemma source_vident : forall f, 
source (vident f) = f. Proof. ir. uf vident.
rw source_create. tv.  Qed.

Lemma target_vident : forall f, 
target (vident f) = f. 
Proof. ir. uf vident. rww target_create.  
Qed.

Lemma osource_vident : forall f, 
osource (vident f) = (source f). Proof. ir. 
uf osource. 
rww source_vident.  Qed.

Lemma otarget_vident : forall f, 
otarget (vident f) = (target f). Proof. ir. 
uf otarget. rww target_vident. Qed.

Lemma ntrans_vident : forall f x,
ob (source f) x -> ntrans (vident f) x = id (target f) (fob f x).
Proof. 
ir. uf vident. rw ntrans_create. tv. 
lu. 
Qed. 

Definition vcompose a b := 
create (source b) (target a)
(fun x => comp (otarget a) (ntrans a x) (ntrans b x)).

Lemma source_vcompose : forall a b, source (vcompose a b) 
= (source b).
Proof.
ir. uf vcompose. rw source_create. tv. 
Qed.

Lemma target_vcompose : forall a b, target (vcompose a b)
= (target a).
Proof.
ir. uf vcompose. rww target_create. 
Qed. 

Lemma osource_vcompose : forall a b,  osource (vcompose a b)
= osource b.
Proof. ir. uf osource. 
rww source_vcompose. Qed.

Lemma otarget_vcompose : forall a b,  otarget (vcompose a b)
= otarget a.
Proof. ir. uf otarget. rww target_vcompose. Qed.

Lemma ntrans_vcompose : forall a b x,
ob (osource b) x -> ntrans (vcompose a b) x = 
comp (otarget a) (ntrans a x) (ntrans b x).
Proof.
ir. 
uf vcompose. rw ntrans_create. tv. lu. 
Qed. 


Hint Rewrite osource_create otarget_create 
source_target target_source
source_vident target_vident osource_vident otarget_vident
ntrans_vident
source_vcompose target_vcompose 
osource_vcompose otarget_vcompose
ntrans_vcompose :nw. 

Lemma vcompose_axioms : forall a b, 
axioms a -> axioms b -> source a = target b
-> axioms (vcompose a b) = True.
Proof.
ir. app iff_eq; ir. clear H2.
assert (osource a = osource b).
uf osource; rw H1; nw. 
assert (otarget a = otarget b). 
uf otarget; wr H1; nw. 
uhg; ee. uf vcompose; ap create_like. 
nw. nw. nw. nw. nw. nw. sy; am. ir. 
nw. 
rww mor_comp. nw. rwi osource_vcompose H4. 
rww H2. nw. rwi osource_vcompose H4. am. 
nw. rww H1. rwi osource_vcompose H4. 
rww H2. rwi osource_vcompose H4; am. 
rwi osource_vcompose H4; am. 
ir. rwi osource_vcompose H4. 
cp H4. wri H2 H4. 
nw. cw. nw. nw. nw. nw. rww H1. 
ir. rwi osource_vcompose H4.
cp H4; wri H2 H4. 
nw. cw. nw. nw. nw. nw. rww H1. 
ir. rwi osource_vcompose H4.
cp H4; wri H2 H4. 
nw. rw assoc. 
rw H3. rw carre. 
wr assoc. wr assoc. app uncomp. 
wr H3. wr H1. rww carre. 
fw. nw. nw. sy; am. 
nw. cw. sy; am. nw. cw. 
fw. nw. cw. nw. nw. nw. 
rww H1. cw. cw. tv.  
nw. cw. sy; am. fw. 
nw. nw. nw. cw. 
nw. fw. rww H1. nw. 
nw. cw. nw. fw. nw. 
nw. cw. tv. am. am. 
nw. cw. nw. cw. fw. nw. 
nw. nw. rww H1. cw. cw. 
nw. fw. nw. cw. tv. cw. cw. 
Qed. 

Lemma vident_axioms : forall f,
Functor.axioms f -> axioms (vident f)  = True.
Proof.
ir. app iff_eq; ir. clear H0.
uf vident. ap create_axioms. 
uhg; dj. am. am. tv. tv. 
ap mor_id. ap ob_fob. am. am. rw source_id.
tv. ap ob_fob; am. 
rw target_id; try tv; try (ap ob_fob; am). 
cp H7; rwi mor_facts_rw H7; uh H7; ee.
rw left_id. rw right_id. tv. 
ap ob_fob; am. ap mor_fmor; am. 
rw source_fmor; try am. tv. 
tv. fw. fw. fw. tv. 
Qed. 



Lemma axioms_extensionality : forall a b,
axioms a -> axioms b ->
source a = source b -> 
target a = target b ->
(forall x, ob (osource a) x -> ntrans a x = ntrans b x) ->
a = b.
Proof.
ir. 
assert (like a).
nw. assert (like b). nw. 
uh H4; uh H5.
wr H4; wr H5. 
rw H1. rw H2. 
uf create. (*up. uf ntrans_arrow_create. *)
up. 
app Function.create_extensionality. 
ir. wri H1 H7. ap H3. 
ap is_ob_ob. nw. am. 
Qed. 

Lemma left_vident : forall a,
axioms a -> vcompose (vident (target a)) a = a.
Proof.
ir. ap axioms_extensionality. 
rww vcompose_axioms. nw. 
rww vident_axioms. nw. nw. am. nw. nw. ir. 
rwi osource_vcompose H0. 
nw'. cw. fw. nw. nw. nw. nw. 
Qed. 

Lemma right_vident : forall a,
axioms a -> vcompose a (vident (source a)) = a.
Proof.
ir. ap axioms_extensionality. 
rww vcompose_axioms. nw. 
nw. rww vident_axioms. nw. nw. am. nw. nw. ir. 
rwi osource_vcompose H0. 
rwi osource_vident H0. 
rwi source_source H0. 
nw'. cw. fw. nw. nw. nw. nw. 
Qed. 

Lemma weak_left_vident : forall a f,
axioms a -> f = target a -> vcompose (vident f) a = a.
Proof.
ir. rw H0. ap left_vident. am. 
Qed.

Lemma weak_right_vident : forall a f,
axioms a -> f = source a -> vcompose a (vident f) = a.
Proof.
ir. rw H0. ap right_vident. am. 
Qed. 

Hint Rewrite weak_left_vident weak_right_vident : nw.






Lemma vcompose_assoc : forall a b c,
axioms a -> axioms b -> axioms c ->
source a = target b -> source b = target c ->
vcompose (vcompose a b) c = 
vcompose a (vcompose b c).
Proof.
ir. 
ap axioms_extensionality; try am. 
rww vcompose_axioms. rww vcompose_axioms. 
nw. rww vcompose_axioms. rww vcompose_axioms. 
nw. rww source_vcompose. rww source_vcompose.
rww source_vcompose. rw target_vcompose.
rw target_vcompose. rw target_vcompose. tv. 
ir. 
rwi osource_vcompose H4. 
assert (otarget b = otarget a).
uf otarget. wr H2. nw.
assert (otarget c = otarget a).
uf otarget. wr H3; nw. 
assert (osource b = osource a).
uf osource. rw H2. nw.
assert (osource c = osource a).
uf osource. rw H2; nw. uf osource. 
rw H3. nw. 
rwi H8 H4.
rww ntrans_vcompose. 
rww ntrans_vcompose. rw ntrans_vcompose. 
rw ntrans_vcompose. nw. 
rw assoc.  
rww H5. nw.  nw. rww H7. sy; am. nw. rww H8. 
sy; am. nw. rww H2. rww H7. nw. 
rww H3. rww H7. rww H8. tv. rww H8. 
nw. rww H8. rww H7. rww H8. 
Qed. 






Definition htrans_left f a :=
create (fcompose f (source a))
(fcompose f (target a))
(fun x => (fmor f (ntrans a x))).

Definition htrans_right a f :=
create (fcompose (source a) f)
(fcompose (target a) f)
(fun x=> (ntrans a (fob f x))).

Lemma source_htrans_left : forall f a,
source (htrans_left f a) = 
fcompose f (source a).
Proof. ir. uf htrans_left. 
rww source_create.  Qed. 

Lemma target_htrans_left : forall f a,
target (htrans_left f a) = 
fcompose f (target a).
Proof. ir. uf htrans_left. rww target_create. 
Qed. 


Lemma osource_htrans_left : forall f a,
osource (htrans_left f a) = osource a.
Proof. ir.  uf osource. 
rww source_htrans_left. 
rww source_fcompose. 
Qed. 

Lemma otarget_htrans_left : forall f a,
otarget (htrans_left f a) = target f.
Proof. ir.  uf otarget. rww target_htrans_left.
rww target_fcompose. Qed. 

Lemma source_htrans_right : forall f a,
source (htrans_right a f) = 
fcompose (source a) f.
Proof. ir.  uf htrans_right. rww source_create.
Qed. 

Lemma target_htrans_right : forall f a,
target (htrans_right a f) = 
fcompose (target a) f.
Proof. ir.  uf htrans_right. rww target_create.
Qed. 

Lemma osource_htrans_right : forall f a,
osource (htrans_right a f) = source f.
Proof. ir.  uf osource. rww source_htrans_right.
rww source_fcompose. Qed. 

Lemma otarget_htrans_right : forall f a,
otarget (htrans_right a f) = otarget a.
Proof. ir.  uf otarget. rw target_htrans_right.
rww target_fcompose. 
Qed. 



Hint Rewrite source_htrans_left target_htrans_left 
osource_htrans_left otarget_htrans_left
source_htrans_right target_htrans_right
osource_htrans_right otarget_htrans_right : nw. 


Lemma ntrans_htrans_left : forall f a x,
ob (osource a) x ->
ntrans (htrans_left f a) x =
fmor f (ntrans a x).
Proof.
ir. uf htrans_left. rw ntrans_create. 
tv. rw source_fcompose. lu. 
Qed. 

Lemma ntrans_htrans_right : forall f a x,
ob (source f) x ->
ntrans (htrans_right a f) x =
ntrans a (fob f x).
Proof.
ir. uf htrans_right. rw ntrans_create. 
tv. rw source_fcompose. lu.  
Qed. 

Hint Rewrite ntrans_htrans_left ntrans_htrans_right : hw. 

Lemma htrans_left_axioms : forall f a,
Functor.axioms f -> axioms a ->
source f = otarget a -> 
axioms (htrans_left f a).
Proof.
ir. 


uhg; ee. 
uf htrans_left. ap create_like. 
rw osource_htrans_left. nw. 
rww otarget_htrans_left. fw. 
rww source_htrans_left.  
fw. nw. nw. 
rw target_htrans_left. 
fw. nw. rw osource_htrans_left. 
rw target_htrans_left. rw source_fcompose. 
nw. rw source_htrans_left. rw target_fcompose.
rww otarget_htrans_left. 
ir. rwi osource_htrans_left H2. 
rw otarget_htrans_left. 
rw ntrans_htrans_left. fw. nw. am. 

ir. rwi osource_htrans_left H2. rw
ntrans_htrans_left. rw source_fmor. 
rw source_htrans_left. rw source_ntrans. 
rw fob_fcompose. tv. am. nw. nw. 
nw. am. am. am. nw. am. 

ir. rwi osource_htrans_left H2. 
rww ntrans_htrans_left. rww target_htrans_left.
rww target_fmor. rww target_ntrans. rww fob_fcompose.
nw. nw. nw. 

ir. rwi osource_htrans_left H2. 
rw otarget_htrans_left. 
rw ntrans_htrans_left. rw target_htrans_left.
rw ntrans_htrans_left. rw fmor_fcompose. 
rw source_htrans_left. 
rw fmor_fcompose. 
rw comp_fmor.
rw comp_fmor. 
ap uneq. rw H1. rww carre. 
am. fw. nw. nw. nw. cw. 
nw. fw. nw. nw. cw. am. nw. cw. 
fw. nw. nw. nw. fw. nw. cw. am. nw. 
nw. nw. am. nw. nw. nw. cw. cw. 
Qed.

Lemma htrans_right_axioms : forall f a,
Functor.axioms f -> axioms a ->
osource a = target f -> 
axioms (htrans_right a f).
Proof.
ir. 
uhg; ee. uf htrans_right; ap create_like. 
rw osource_htrans_right. fw. 
rw otarget_htrans_right. nw. 
rw source_htrans_right. fw. 
nw. rw target_htrans_right. fw. 
nw. nw. rw target_htrans_right. 
rw source_fcompose. rw osource_htrans_right. 
tv. rw source_htrans_right. rw target_fcompose. 
rw otarget_htrans_right. nw. 

ir. rwi osource_htrans_right H2. rw otarget_htrans_right.
rw ntrans_htrans_right. nw. fw. am. 

ir. rwi osource_htrans_right H2. 
rw ntrans_htrans_right. rw source_ntrans. 
rw source_htrans_right. rww fob_fcompose. 
nw. am. fw. am. 

ir. rwi osource_htrans_right H2. 
rw ntrans_htrans_right. rw target_ntrans. 
rw target_htrans_right. rww fob_fcompose. 
nw. nw. am. fw. am. 

ir. rwi osource_htrans_right H2. 
rw otarget_htrans_right. 
rw ntrans_htrans_right. 
rw source_htrans_right. rw target_htrans_right. 
rw ntrans_htrans_right. rw fmor_fcompose. 
rw fmor_fcompose. 
wr target_fmor. wr source_fmor. rw carre. tv. 

am. fw. am. am. am. am. nw. am. 
nw. am. nw. am. nw. am. cw. cw.  
Qed.

Definition hcomposable a b :=
axioms a & axioms b & osource a = otarget b.

Definition hcompose a b :=
vcompose (htrans_right a (target b)) (htrans_left (source a) b).

Lemma hcompose_axioms : forall a b,
axioms a -> axioms b -> osource a = otarget b
-> axioms (hcompose a b).
Proof.
ir. 
uf hcompose. 
rw vcompose_axioms. tv. 
ap htrans_right_axioms. nw.  am. 
rw H1. tv. 
ap htrans_left_axioms. nw. am. 
am. 
rw source_htrans_right. 
rw target_htrans_left. tv. 
Qed. 

Lemma source_hcompose : forall a b, 
source (hcompose a b) = fcompose (source a) (source b).
Proof.
ir. uf hcompose. rw source_vcompose. 
rw source_htrans_left. tv. 
Qed. 

Lemma target_hcompose : forall a b, 
target (hcompose a b) = fcompose (target a) (target b).
Proof.
ir. uf hcompose. rw target_vcompose. 
rw target_htrans_right. tv. 
Qed. 

Lemma osource_hcompose : forall a b,
osource (hcompose a b) = osource b.
Proof.
ir. uf osource. rww source_hcompose. 
fw. 
Qed.

Lemma otarget_hcompose : forall a b,
otarget (hcompose a b) = otarget a.
Proof.
ir. uf otarget. rww target_hcompose.
rww target_fcompose. 
Qed.

Lemma ntrans_hcompose : forall a b x,
hcomposable a b -> ob (osource b) x ->
ntrans (hcompose a b) x = 
comp (otarget a) (ntrans a (fob (target b) x))
        (fmor (source a) (ntrans b x)).
Proof.
ir. uf hcompose. 
rw ntrans_vcompose. rw otarget_htrans_right. 
rw ntrans_htrans_right. 
rw ntrans_htrans_left. tv. 
am. uh H; ee. nw. rww osource_htrans_left. 
Qed.

Definition hcompose1 a b := 
vcompose (htrans_left (target a) b) (htrans_right a (source b)).

Lemma hcompose1_axioms : forall a b,
hcomposable a b -> axioms (hcompose1 a b).
Proof.
ir. 
uh H; ee. 
uf hcompose1. 
rw vcompose_axioms. tv. 
ap htrans_left_axioms. nw. am. 
nw.   
ap htrans_right_axioms. nw. am. 
nw. 
rw source_htrans_left. 
rw target_htrans_right. tv. 
Qed. 

Lemma hcomposable_commutativity : forall a b x,
hcomposable a b -> ob (osource b) x -> 
comp (otarget a) (ntrans a (fob (target b) x))
  (fmor (source a) (ntrans b x)) =
comp (otarget a) (fmor (target a) (ntrans b x))
  (ntrans a (fob (source b) x)).
Proof.
ir. 
cp H. uh H; ee. 

assert (lem1 : fob (target b) x = 
target (ntrans b x)).
rw target_ntrans. tv. am. am. 
assert (lem2 : fob (source b) x =
source (ntrans b x)). 
rw source_ntrans. tv. am. am. 

rw lem1. rw carre. rw lem2. tv. 
am. ap mor_ntrans. am. am. am. 
Qed. 


Lemma hcompose_other : forall a b, 
hcomposable a b -> hcompose a b =
hcompose1 a b.
Proof.
ir. cp H; uh H; ee. 
assert (lem1: axioms (hcompose a b)). 
ap hcompose_axioms; am. 
assert (lem2 : axioms (hcompose1 a b)).
ap hcompose1_axioms; am. 

ap axioms_extensionality. 
app hcompose_axioms. 
app hcompose1_axioms. 
rw source_hcompose. 
uf hcompose1. rw source_vcompose. 
rw source_htrans_right. tv. 

rw target_hcompose. 
uf hcompose1. rw target_vcompose. 
rww target_htrans_left. 
 
ir. 
rwi osource_hcompose H3. 
rw ntrans_hcompose. 
uf hcompose1. 
rw ntrans_vcompose. rw otarget_htrans_left. 
rw ntrans_htrans_left. 
rw ntrans_htrans_right. 
assert (target (target a) = otarget a).
tv. rw H4. 
ap hcomposable_commutativity. am. am. am. 
am. rw osource_htrans_right. am. am. am. 
Qed. 



Lemma hcompose_vident_left : forall f a,
axioms a -> Functor.axioms f ->
source f = otarget a ->
hcompose (vident f) a = htrans_left f a.
Proof.
ir. ap axioms_extensionality. 
ap hcompose_axioms. 
rw vident_axioms. tv. 
am. am. nw. app htrans_left_axioms. 
rww source_hcompose. rw source_htrans_left. 
rw source_vident. tv. rw target_hcompose. 
rw target_vident. rw target_htrans_left. tv. 

ir. 
rwi osource_hcompose H2. 
rw ntrans_hcompose. 
rw ntrans_htrans_left. 
rw otarget_vident. rw ntrans_vident. 
rw left_id. rw source_vident. tv. 
ap ob_fob. am. rw H1.
uf otarget. ap ob_fob. 
nw. 
nw. nw. fw. nw. nw. 

rw target_fmor. rw target_ntrans. tv. 
am. am. am. nw. tv. fw. nw. nw. am. 
uhg; ee. rww vident_axioms. am. 
nw. am. 
Qed.

Lemma hcompose_vident_right : forall a f,
axioms a -> Functor.axioms f -> 
target f = osource a ->
hcompose a (vident f) = htrans_right a f.
Proof.
ir. 
ap axioms_extensionality. ap hcompose_axioms.
uhg; ee.
nw. nw. nw. nw. nw. nw. nw. 
ir. nw. 
ir. nw. 
ir. nw. 
ir. rw carre. tv. am. am. rww vident_axioms. 
nw. sy; am. ap htrans_right_axioms. am.
am. sy; am. rw source_hcompose.
rw source_htrans_right. rw source_vident. tv. 
rw target_hcompose. rw target_vident. rw target_htrans_right.
tv. 
ir. rwi osource_hcompose H2. rwi osource_vident H2. 
rww ntrans_hcompose. rww ntrans_vident. 
rww ntrans_htrans_right. 
rww target_vident. rww fmor_id. rw target_source. 
rw right_id. tv. fw. nw. nw. wr H1. fw. nw. 
nw. wr H1; fw. nw. wr H1; fw. tv. am. 
nw. sy; am. fw. uhg; ee. am. 
rww vident_axioms. rw otarget_vident. sy; am. 
rww osource_vident. 
Qed. 

Lemma vident_hcomposable : forall f g,
Functor.axioms f -> Functor.axioms g ->
source f = target g -> hcomposable (vident f) (vident g).
Proof.
ir. uhg; ee. rww vident_axioms. rww vident_axioms.
rw osource_vident. rww otarget_vident. 
Qed. 

Lemma hcompose_vident_vident : forall f g,
Functor.axioms f -> Functor.axioms g ->
source f = target g -> 
hcompose (vident f) (vident g) = vident (fcompose f g).
Proof.
ir. 
rw hcompose_vident_left. 
ap axioms_extensionality. 
ap htrans_left_axioms. am. rww vident_axioms.
rww otarget_vident. 
rww vident_axioms. app fcompose_axioms.
rw source_htrans_left. rw source_vident. 
rw source_vident. tv. 
rw target_htrans_left. rw target_vident. rw target_vident. 
tv. 
ir. rwi osource_htrans_left H2. rwi osource_vident H2. 
rw ntrans_htrans_left. 
rw ntrans_vident. rw ntrans_vident. 
rw target_fcompose. rw fmor_id. 
ap  uneq. rww fob_fcompose. am. am. 
fw. fw. am. nw. 
rww vident_axioms. 
am. nw. 
Qed. 

Lemma htrans_right_vident : forall f g,
Functor.axioms f -> Functor.axioms g -> source f = target g->
htrans_right (vident f) g = vident (fcompose f g).
Proof.
ir. wr hcompose_vident_right. 
rw hcompose_vident_vident. tv. am. 
am. am. rww vident_axioms. am. 
nw. sy; am. 
Qed.

Lemma htrans_left_vident : forall f g,
Functor.axioms f -> Functor.axioms g -> source f = target g->
htrans_left f (vident g) = vident (fcompose f g).
Proof.
ir. wr hcompose_vident_left. 
rw hcompose_vident_vident. tv. am. 
am. am. rww vident_axioms. am. nw.  
Qed. 



Lemma interchange : forall a b c d,
target a = source c -> 
target b = source d -> 
osource b = otarget a -> 
axioms a -> axioms b -> axioms c -> axioms d -> 
vcompose (hcompose d c) (hcompose b a) =
hcompose (vcompose d b) (vcompose c a).
Proof.
ir. 

assert (lema : osource d = otarget c).
uf osource. wr target_source.  wr H0. 
wr H. rw source_target. am. 
am. am. 

assert (lemb : osource d = osource b).
rw lema. wr source_target. rw H0. sy; am. 
am. 

assert (lem1 : hcomposable d c).
uhg; ee; try am. 

assert (lem2 : hcomposable b a).
uhg; ee; try am. 


assert (lem5: otarget d = otarget b).
uf otarget. rw H0. rw target_source. 
tv. am.

assert (lem6 : osource c = osource a).
uf osource. wr H. rw source_target.
tv. am. 

assert (lem7 : otarget d = otarget b). 
uf otarget. rw H0. rw target_source. 
tv. am. 

assert (lem8 : osource b = otarget c).
wr lema. sy; am. 

ap axioms_extensionality. 
rw vcompose_axioms. tv. ap  hcompose_axioms; am. 
ap hcompose_axioms; am. 
rw source_hcompose. rw target_hcompose. 
rw H0. rw H. tv. 
ap hcompose_axioms.
rww vcompose_axioms. sy; am. 
rww vcompose_axioms. sy; am. 
rw osource_vcompose. rww otarget_vcompose. 
rw source_vcompose. rw source_hcompose. 
rw source_hcompose. rw source_vcompose. rw source_vcompose. 
tv. 
rw target_vcompose. rw target_hcompose. 
rw target_hcompose. rw target_vcompose. 
rww target_vcompose. 

ir. rwi osource_vcompose H6. 
rwi osource_hcompose H6. 
cp H6. wri lem6 H7. 
rww ntrans_vcompose. rww ntrans_hcompose.
rww ntrans_hcompose. rw ntrans_hcompose. 
rw ntrans_vcompose. 
rw otarget_hcompose. 
rw otarget_vcompose. rw target_vcompose. 
rw source_vcompose. 
rw ntrans_vcompose. 
rww assoc. rww assoc. 
app uncomp. 
wrr assoc. wr lema. 
assert (osource d = source (source b)). 
nw. rw H8. wr comp_fmor. 
wr assoc. ap uncomp. tv. rw target_source. 
wr H0. 
rw H.

sy. ap hcomposable_commutativity. 
uhg; ee. am. am. am. 

(*** 33 rewriting obligations and other subsidiary goals ***)
am. am. 
nw. nw. fw. nw. nw. fw. nw. nw. nw. fw. 
nw. nw. nw. nw. rw target_fmor. 
rw target_ntrans. tv. am. am. nw. 
nw. fw. nw. nw. 
rw source_fmor. rw source_ntrans.
rw target_fmor. rw target_ntrans. rww H. 
am. am. nw. nw. am. am. nw. nw. 
nw. nw. nw. nw. nw. rww H. 
fw. nw. nw. nw. nw. fw. nw. nw. 
fw. nw. nw. nw. rw source_fmor. rw source_ntrans. 
rw target_ntrans. rw H0. rww H. am. 
fw. nw. nw. am. am. nw.
nw. rw source_ntrans. rw target_fmor. 
rw target_ntrans. tv. am. am. nw. nw. am. 
fw. nw. nw. nw. fw. nw. nw. 
nw. fw. nw. nw. fw. 
nw. nw. rw mor_comp. tv. rw lem8. 
nw. rw H1. nw. 
nw. rww H. am. nw. 
rw source_ntrans. rw target_ntrans. 
wr H0. tv. am. fw. nw. nw. 
am. fw. nw. nw. 
rww source_ntrans. rw target_fmor. ap uneq. 
rw target_comp. rw target_ntrans. tv. 
am. am. nw. wr lem8. 
rw H1. nw. nw. rww H. 
nw. cw. nw. nw. 
nw. rww H. rw lem8. fw. nw. nw. 
nw. rw lemb. rw lem8. fw. nw. 
nw. fw. nw. nw. nw. 
cw. nw. fw. nw. nw. 
fw. nw. nw. nw. 
rw source_ntrans. 
rw target_fmor. rw target_ntrans.
tv. am. am. nw. nw. am. 
fw. nw. nw. rw source_ntrans. 
rw target_fmor. rw target_ntrans. 
tv. am. am. nw. nw. am. 
fw. nw. nw. 
rw source_fmor. rw source_ntrans. 
rw target_comp. rw target_ntrans. 
wr H0. rww H. am. 
fw. nw. nw. nw. fw. nw. nw. 
fw. nw. nw. nw. 
rw source_ntrans. rw target_fmor. 
rw target_ntrans. tv. 
am. am. nw. nw. am. fw. 
nw. nw. am. am. nw. 
nw. am. rw target_vcompose. 
fw. nw. nw. 
uhg; ee. rww vcompose_axioms. 
sy; am. 
rww vcompose_axioms. sy; am. 
rw osource_vcompose. rww otarget_vcompose. 
rw osource_vcompose. am. 
rww osource_hcompose. 
Qed. 



Definition constant_nt a b u :=
create (constant_functor a b (source u))
(constant_functor a b (target u))
(fun x:E => u).

Lemma osource_constant_nt : forall a b u,
osource (constant_nt a b u) = a.
Proof. ir. uf constant_nt. 
rw osource_create.
rww source_constant_functor.
Qed. 

Lemma otarget_constant_nt : forall a b u,
otarget (constant_nt a b u) = b.
Proof. ir. uf constant_nt.
rw otarget_create. rww target_constant_functor. Qed.

Lemma source_constant_nt : forall a b u,
source (constant_nt a b u) = constant_functor a b (source u).
Proof. ir. 
uf constant_nt. rww source_create. 
Qed.

Lemma target_constant_nt : forall a b u,
target (constant_nt a b u) = constant_functor a b (target u).
Proof. ir. 
uf constant_nt. rww target_create.
Qed.

Lemma ntrans_constant_nt : forall a b u x,
ob a x ->  ntrans (constant_nt a b u) x = u.
Proof.
ir. uf constant_nt. rww ntrans_create. 
rw source_constant_functor. lu.  
Qed. 

Lemma constant_nt_axioms : forall a b u,
Category.axioms a -> Category.axioms b ->
mor b u -> axioms (constant_nt a b u).
Proof.
ir. uf constant_nt. ap create_axioms. 
cp H1. rwi mor_facts_rw H2. uh H2; ee. 
uhg; ee. 
app constant_functor_axioms. 
app constant_functor_axioms. 
rww source_constant_functor. 
rww source_constant_functor. 
rww target_constant_functor. 

rww target_constant_functor.
ir. rww target_constant_functor. 
ir. 
rww fob_constant_functor. 
rwi source_constant_functor H8; am. 
ir. 
rwi source_constant_functor H8. 
rww fob_constant_functor. 
ir. 
rwi source_constant_functor H8. 
rww fmor_constant_functor. 
rww fmor_constant_functor. 
rw target_constant_functor. 
rww left_id. 
Qed.


Lemma vcompose_htrans_right_htrans_right : 
forall u v f g, axioms u -> axioms v ->
Functor.axioms f -> f = g -> 
source u = target v -> target f = osource u ->
vcompose (htrans_right u f) (htrans_right v g) =
htrans_right (vcompose u v) f.
Proof.
ir. 
assert (osource u = osource v).
uf osource. rw H3. 
rw source_target. tv. am. 
cp hcompose_vident_right. wr H2. 
util (H6 u f). am. am. am. 
util (H6 v f). am. am. wr H5; am. 
util (H6 (vcompose u v) f). rww vcompose_axioms.
am. rww osource_vcompose. wrr H5. 
wr H7. wr H8. 
assert (vident f = vcompose (vident f) (vident f)).
rw weak_left_vident. reflexivity. 
rww vident_axioms. rww target_vident. 
rwi H10 H9. wr H9. 
apply interchange. 
rww target_vident. rww source_vident. sy; am. 
rww otarget_vident. sy; wrr H5. 
rww vident_axioms. am. rww vident_axioms. am. 
Qed.

Lemma vcompose_htrans_left_htrans_left : 
forall u v f g, axioms u -> axioms v ->
Functor.axioms f -> f = g -> 
source u = target v -> source f = otarget u ->
vcompose (htrans_left f u) (htrans_left g v) =
htrans_left f (vcompose u v).
Proof.
ir. 
assert (otarget u = otarget v).
uf otarget. wr H3. 
rw target_source. tv. am. 
cp hcompose_vident_left. wr H2. 
util (H6 f u). am. am. am. 
util (H6 f v). am. am. wr H5; am. 
util (H6 f (vcompose u v)). rww vcompose_axioms.
am. rww otarget_vcompose. 
wr H7. wr H8. 
assert (vident f = vcompose (vident f) (vident f)).
rw weak_left_vident. reflexivity. 
rww vident_axioms. rww target_vident. 
rwi H10 H9. wr H9. 
apply interchange. 
sy; am. 
rww target_vident. rww source_vident. 
rww osource_vident. sy; wrr H5. sy; am. am.
rww vident_axioms. am. rww vident_axioms. 
Qed.


(**** oppnt stuff ****)

Definition oppnt' u :=
Nat_Trans.create (oppf (target u)) (oppf (source u))
(fun x => flip (ntrans u x)). 

Lemma source_oppnt' : forall u,
source (oppnt' u) = oppf (target u).
Proof.
ir. uf oppnt'. rw source_create. tv. 
Qed.

Lemma target_oppnt' : forall u,
target (oppnt' u) = oppf (source u).
Proof.
ir. uf oppnt'. rw target_create. tv. 
Qed.

Lemma osource_oppnt' : forall u,
axioms u -> 
osource (oppnt' u) = opp (osource u).
Proof.
ir. uf osource. 
rw source_oppnt'. rw source_oppf. rww source_target.
rww functor_axioms_target. 
Qed.

Lemma otarget_oppnt' : forall u, axioms u -> 
otarget (oppnt' u) = opp (otarget u).
Proof.
ir. uf otarget. 
rw target_oppnt'. rw target_oppf. rww target_source.
rww functor_axioms_source.
Qed.

Lemma ntrans_oppnt' : forall u x,
axioms u -> ob (osource u) x -> 
ntrans (oppnt' u) x = flip (ntrans u x).
Proof.
ir. uf oppnt'. 
rw ntrans_create. tv. 
rw source_oppf. 
ap ob_is_ob. rw ob_opp. 
rww source_target. 
rww functor_axioms_target. 
Qed.

Lemma oppnt'_axioms : forall u,
Nat_Trans.axioms u -> Nat_Trans.axioms (oppnt' u).
Proof.
ir. cp H. uh H0; ee. 
uhg; ee. uf oppnt'. ap create_like. 
rw osource_oppnt'. ap opp_axioms. am. am. 
rw otarget_oppnt'. ap opp_axioms. am. am. 
rw source_oppnt'. ap oppf_axioms. am. 
rw target_oppnt'. ap oppf_axioms. am. 
rw target_oppnt'. rw source_oppf. 
rw osource_oppnt'. tv. am. 
am. rw source_oppnt'. rw target_oppf. 
rw otarget_oppnt'. tv. am. 
ir. 
am. rw otarget_oppnt'. (* rw ntrans_oppnt'. 
rw mor_opp. rw flip_flip. ap H7. rwi osource_oppnt' H11. 
rwi ob_opp H11. am. am. am. am. am. 
rwi osource_oppnt' H11. 
rwi ob_opp H11. am. am. am. am. *)

ir. rwi osource_oppnt' H11. rwi ob_opp H11. 
rw ntrans_oppnt'. rw mor_opp. rw flip_flip. 
app mor_ntrans. am. am. am. am. 
(*rw source_flip. rw fob_oppf. 
rw target_ntrans. tv. 
am. am. am. rw source_oppf. rw source_target. 
rw ob_opp. am. am. am. 
assert (mor (otarget u) (ntrans u x)). 
ap mor_ntrans. am. am. tv. 
apply mor_arrow_like with (otarget  u). am. am. 
am. am. am. *)

ir. rwi osource_oppnt' H11. rwi ob_opp H11. 
rw ntrans_oppnt'. rw source_flip. 
rw source_oppnt'. rw fob_oppf. 
rw target_ntrans. tv. 
am. am. am. rw source_oppf. rw source_target. 
rw ob_opp. am. am. am. 
assert (mor (otarget u) (ntrans u x)). 
ap mor_ntrans. am. am. tv. 
apply mor_arrow_like with (otarget  u). am. am. 
am. am. 


ir. cp H11. rwi osource_oppnt' H12. 
rwi ob_opp H12. 
rw ntrans_oppnt'. 
rw target_flip. 
rw target_oppnt'. rw fob_oppf. 
rw source_ntrans. tv. am. 
am. am. 
rw source_oppf. rw ob_opp. am. 
rww functor_axioms_source. 
apply mor_arrow_like with (otarget u). 
ap mor_ntrans. am. am. tv. am. 
am. am. 

ir. 
cp H11. rwi osource_oppnt' H12. 
cp H12. rwi mor_opp H13. 
rw otarget_oppnt'. rw target_oppnt'. 
rw ntrans_oppnt'. rw ntrans_oppnt'. 
rw fmor_oppf. 
rw source_oppnt'. rw fmor_oppf. 
rw comp_opp. 
rw flip_flip. 
rw comp_opp. rw flip_flip. rw flip_flip. 
rw flip_flip. assert (source u0 = target (flip u0)). 
rww target_flip. 
apply mor_arrow_like with (osource (oppnt' u)). 
am. rw H14. ap uneq. 
rw H10. 
rw source_flip. tv. 
apply mor_arrow_like with (osource (oppnt' u)). am. 
am. 
rw mor_opp. rw flip_flip. wr target_source. 
ap mor_fmor. am. 
am. am. rw mor_opp. 
rw flip_flip. ap mor_ntrans. am. 
wr target_flip. rww ob_target. 
apply mor_arrow_like with (osource (oppnt' u)). am. 
tv. 
rw source_flip. 
rw target_flip. 
rw source_ntrans. 
rw target_fmor. 
ap uneq. rw target_flip. tv. 
apply mor_arrow_like with (opp (osource u)); am. 
am. am. am. 
wr target_flip. rww ob_target. 
apply mor_arrow_like with (opp (osource u)); am. 
apply mor_arrow_like with (otarget u). 
ap mor_ntrans. am. wr target_flip. rww ob_target. 
apply mor_arrow_like with (opp (osource u)); am. tv. 
apply mor_arrow_like with (target (source u)). 
ap mor_fmor. am. am. 


rw mor_opp. 
rw flip_flip. ap mor_ntrans. 
am. wr source_flip. rww ob_source. 
apply mor_arrow_like with (osource (oppnt' u)). am. tv. 
rw mor_opp. 
rw flip_flip. uf otarget. ap mor_fmor. 
am. rww source_target. 

rw source_flip. 
rw target_flip. 
rw target_ntrans. rw source_fmor. 
ap uneq. rw source_flip. tv. 
apply mor_arrow_like with (osource (oppnt' u)). am.
am. rw source_target. am. am. am. 
wr source_flip. rww ob_source. 
apply mor_arrow_like with (osource (oppnt' u)). am.
apply mor_arrow_like with (target (target u)). 
app mor_fmor. rw source_target. am. am. 
apply mor_arrow_like with (otarget u). 
app mor_ntrans. wr source_flip. 
rww ob_source. 
apply mor_arrow_like with (osource (oppnt' u)). am.
rww functor_axioms_target. 

rw source_oppf. rww source_target. 
rww functor_axioms_target.
rww functor_axioms_source. rw source_oppf. am. am. 

am. wr target_flip. rww ob_target. 
apply mor_arrow_like with (osource (oppnt' u)). am.
am. 
wr source_flip. rww ob_source. 
apply mor_arrow_like with (osource (oppnt' u)). am.
am. am. 
Qed.

Lemma oppnt'_oppnt' : forall u,
Nat_Trans.axioms u -> 
oppnt' (oppnt' u) = u.
Proof.
ir. ap axioms_extensionality. 
ap oppnt'_axioms. ap oppnt'_axioms. 
am. am. 
rw source_oppnt'. rw target_oppnt'. 
rw oppf_oppf. tv. 
uh H; ee. 
rw target_oppnt'. rw source_oppnt'. 
rw oppf_oppf. tv. 
ir. rw ntrans_oppnt'. rw ntrans_oppnt'. 
rw flip_flip. tv. am. 
rwi osource_oppnt' H0. 
rwi ob_opp H0. 
rwi osource_oppnt' H0. rwi ob_opp H0. 
am. am. 
app oppnt'_axioms. app oppnt'_axioms. 
rwi osource_oppnt' H0. 
rwi ob_opp H0. am. 
app oppnt'_axioms. 
Qed.

Lemma vcompose_oppnt' : forall u v,
Nat_Trans.axioms u -> Nat_Trans.axioms v ->
source u = target v -> 
vcompose (oppnt' v) (oppnt' u) = oppnt' (vcompose u v).
Proof.
ir. 
assert (axioms (oppnt' u)). 
app oppnt'_axioms. 
assert (axioms (oppnt' v)). 
app oppnt'_axioms. 
assert (source (oppnt' v) = target (oppnt' u)).
rw source_oppnt'. rw target_oppnt'. rww H1. 
assert (lem1 : otarget u = otarget v).
uf otarget. wr H1. rww target_source. 
assert (lem2 : osource u = osource v).
uf osource. rw H1. rww source_target. 


ap axioms_extensionality. 
rww vcompose_axioms. 
ap oppnt'_axioms. 
rww vcompose_axioms. 
rw source_vcompose. rw source_oppnt'. 
rw source_oppnt'. rw target_vcompose. tv. 
rw target_vcompose. rw target_oppnt'. 
rw target_oppnt'. rww source_vcompose. 

ir. 
rwi osource_vcompose H5. 
cp H5. 
rwi osource_oppnt' H6. rwi ob_opp H6. 
rw ntrans_vcompose. rw otarget_oppnt'. 
rw ntrans_oppnt'. rw ntrans_oppnt'. 
rw ntrans_oppnt'. rw comp_opp. ap uneq. 
rw flip_flip. rw flip_flip. 
rw ntrans_vcompose. 
rww lem1.  wrr lem2. 
rww mor_opp. rw flip_flip.
ap mor_ntrans. am. wrr lem2. tv. 
rww mor_opp. rw flip_flip.
ap mor_ntrans. am. am. tv. sy; am. 

rw source_flip. rw target_flip. 
rw target_ntrans. rw source_ntrans. rww H1. am. 
am. am. wrr lem2. 
apply mor_arrow_like with (otarget u). 
app mor_ntrans. 
apply mor_arrow_like with (otarget u). 
app mor_ntrans. 
wrr lem2. 

rww vcompose_axioms. 
rw osource_vcompose. wrr lem2. am. am. am. 
wrr lem2. am. am. 
am. 
Qed.

Lemma vident_oppf1 : forall f,
Functor.axioms f -> 
vident (oppf f) = oppnt' (vident f).
Proof.
ir. 

ap axioms_extensionality. 
rw vident_axioms. tv. app oppf_axioms. 
app oppnt'_axioms. rww vident_axioms. 
rw source_vident. rw source_oppnt'. 
rw target_vident. tv. 
rw target_vident. rw target_oppnt'. rw source_vident. 
tv. 

ir. 
cp H0. rwi osource_vident H0. rwi source_oppf H0. 
rwi ob_opp H0. 
rw ntrans_vident. rw ntrans_oppnt'. 
rw ntrans_vident. 
rw target_oppf. rw fob_oppf. rw id_opp. 
tv. rw ob_opp. ap ob_fob. 
am. am.  
am. rw source_oppf. rw ob_opp. am. 
 am. am. am. rww vident_axioms. 
rw osource_vident. am. 
rw source_oppf. rw ob_opp. am. 
am. am. 
Qed.

Definition oppnt u := Y (Nat_Trans.axioms u) (oppnt' u) u.

Lemma unfold_oppnt : forall u,
Nat_Trans.axioms u -> oppnt u = oppnt' u.
Proof.
ir. uf oppnt. ap (Y_if H). tv. 
Qed.

Lemma oppnt_axioms : forall u,
Nat_Trans.axioms u -> Nat_Trans.axioms (oppnt u).
Proof.
ir. rww unfold_oppnt. app oppnt'_axioms. 
Qed.

Lemma oppnt_oppnt : forall u, oppnt (oppnt u) = u.
Proof.
ir. apply by_cases with (Nat_Trans.axioms u); ir. 
rw unfold_oppnt. rw unfold_oppnt. 
rww oppnt'_oppnt'. am. 
app oppnt_axioms. 
assert (oppnt u = u). 
uf oppnt. ap (Y_if_not H). tv. rw H0. am. 
Qed.

Lemma axioms_oppnt : forall u,
Nat_Trans.axioms (oppnt u) = Nat_Trans.axioms u.
Proof.
ir. ap iff_eq; ir. wr oppnt_oppnt. app oppnt_axioms. 
app oppnt_axioms. 
Qed.

Lemma source_oppnt : forall u, axioms u -> 
source (oppnt u) = oppf (target u).
Proof.
ir. rww unfold_oppnt. rww source_oppnt'. 
Qed.

Lemma target_oppnt : forall u, axioms u -> 
target (oppnt u) = oppf (source u).
Proof.
ir. rww unfold_oppnt. rww target_oppnt'. 
Qed.

Lemma osource_oppnt : forall u,
axioms u -> 
osource (oppnt u) = opp (osource u).
Proof.
ir. uf osource. rw source_oppnt.
rw source_oppf. rww source_target. 
rww functor_axioms_target. am. 
Qed.

Lemma otarget_oppnt : forall u, axioms u -> 
otarget (oppnt u) = opp (otarget u).
Proof.
ir. uf otarget. rw target_oppnt.
rw target_oppf. rww target_source. 
rww functor_axioms_source. am. 
Qed.

Lemma ntrans_oppnt : forall u x,
axioms u -> ob (osource u) x -> 
ntrans (oppnt u) x = flip (ntrans u x).
Proof.
ir. rww unfold_oppnt. rww ntrans_oppnt'. 
Qed.





Lemma vcompose_oppnt : forall u v,
Nat_Trans.axioms u -> Nat_Trans.axioms v ->
source u = target v -> 
vcompose (oppnt v) (oppnt u) = oppnt (vcompose u v).
Proof.
ir. rww unfold_oppnt. rww unfold_oppnt. 
rww vcompose_oppnt'. 
rww unfold_oppnt. rww vcompose_axioms. 
Qed.

Lemma vident_oppf : forall f,
Functor.axioms f -> 
vident (oppf f) = oppnt (vident f).
Proof.
ir. sy; rw unfold_oppnt. 
sy; rw vident_oppf1. reflexivity. am. 
rww vident_axioms. 
Qed.

(**** we should also do the following sometime ******
Lemma oppnt_htrans_left : forall f g u,
Functor.axioms f -> Nat_Trans.axioms u ->
source f = otarget u -> 
oppnt (htrans_left f u) =
htrans_left (oppf f) (oppnt u).
Proof.

Qed.

Lemma oppnt_htrans_right : forall f g u,
Functor.axioms f -> Nat_Trans.axioms u ->
target f = osource u -> 
oppnt (htrans_right u f) =
htrans_right (oppnt u) (oppf f).
Proof.

Qed.

Lemma oppnt_hcompose : forall u v,
Nat_Trans.axioms u -> Nat_Trans.axioms v ->
osource u = otarget v -> 
oppnt (hcompose u v) = hcompose (oppnt u) (oppnt v).
Proof.

Qed.

****************************************************)


End Nat_Trans. 








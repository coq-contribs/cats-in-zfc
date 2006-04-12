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
Require Export limits.


Module Colimit.
Export Limit.


Definition cocone_create v e := cone_create v e. 


Definition coedge_nt := edge_nt. 
Definition coedge c x := ntrans (coedge_nt c) x.
Definition cosocle c := source (coedge_nt c).
Definition cocone_source c := source (cosocle c).
Definition cocone_target c := target (cosocle c).

Definition cocone_like c := cocone_create (vertex c) (coedge_nt c) = c. 



Lemma vertex_cocone_create : forall v e, vertex (cocone_create v e) = v.
Proof.
ir.
uf cocone_create. uf cone_create. uf vertex. drw. 
Qed.

Lemma coedge_nt_cocone_create : forall v e, coedge_nt (cocone_create v e) = e.
Proof.
ir. uf cocone_create. uf cone_create. uf coedge_nt. 
uf edge_nt. drw. 
Qed. 

Lemma cocone_like_cocone_create : forall v e,
cocone_like (cocone_create v e). 
Proof. ir. uf cocone_like. 
rw vertex_cocone_create. rww coedge_nt_cocone_create. 
Qed. 

Definition is_cocone c :=
cocone_like c &
Nat_Trans.axioms (coedge_nt c) &
ob (cocone_target c) (vertex c) &
target (coedge_nt c) = 
constant_functor (cocone_source c) (cocone_target c) (vertex c).

Lemma cocone_extensionality : forall c d,
is_cocone c -> is_cocone d -> vertex c = vertex d ->
cosocle c = cosocle d -> 
(forall x, ob (cocone_source c) x -> coedge c x = coedge d x) ->
c = d.
Proof.
ir. 
assert (cocone_source c = cocone_source d).
uf cocone_source. rww H2. 
assert (cocone_target c = cocone_target d).
uf cocone_target; rww H2. 
uh H; uh H0; ee. uh H; uh H0. wr H; wr H0. 
rw H1. ap uneq.  
app Nat_Trans.axioms_extensionality. 
rw H11. rw H8. 
rw H4; rw H5; rw H1. reflexivity. 
Qed.

Definition cocone_create2 f v e :=
cocone_create v (Nat_Trans.create f
(constant_functor (source f) (target f) v) e).

Lemma is_cocone_cocone_create2 : forall f v e,
Functor.axioms f->
ob (target f) v->
(forall x, ob (source f) x -> mor (target f) (e x)) ->
(forall x, ob (source f) x -> target (e x) = v) ->
(forall x, ob (source f) x -> source (e x) = (fob f x)) ->
(forall u, mor (source f) u -> 
comp (target f) (e (target u)) (fmor f u) = e (source u)) ->
is_cocone (cocone_create2 f v e).
Proof.
ir. uf cocone_create2. 
uhg; ee. ap cocone_like_cocone_create. 
rw coedge_nt_cocone_create. 
app Nat_Trans.create_axioms. uhg; ee. 
am. 

app constant_functor_axioms. uh H; ee; am. uh H; ee; am. 
rww source_constant_functor. 
rww target_constant_functor. 
ir. rw target_constant_functor. au. ir.
au. ir. 
rw fob_constant_functor. au. am. am. 
ir. rw target_constant_functor. 

rww fmor_constant_functor.
rww H4. 
rww left_id. ap H1. rww  ob_source. 
rw H2. tv. rww ob_source. 
rw vertex_cocone_create. 
uf cocone_target. uf cosocle. 
rw coedge_nt_cocone_create. 
rw source_create. am. 
rw coedge_nt_cocone_create. rw target_create. 
rw vertex_cocone_create. uf cocone_source; 
uf cocone_target; uf cosocle; rw coedge_nt_cocone_create.
rw source_create. tv. 
Qed.

Lemma coedge_nt_axioms : forall c,
is_cocone c -> Nat_Trans.axioms (coedge_nt c).
Proof.
ir. uh H; ee; am. 
Qed. 


Lemma otarget_coedge_nt : forall c,
is_cocone c -> 
otarget (coedge_nt c) = cocone_target c.
Proof.
ir. tv. uf cocone_target. uf cosocle. 
rww target_source. app coedge_nt_axioms. 
Qed.

Lemma osource_coedge_nt : forall c,
osource (coedge_nt c) = cocone_source c.
Proof.
ir. uf cocone_source. uf cosocle. 
tv. 
Qed. 

Definition cocone_composable u c :=
is_cocone c &
mor (cocone_target c) u & 
source u = vertex c.

Lemma cocone_composable_rw : forall c u,
is_cocone c -> mor (cocone_target c) u -> source u = vertex c ->
cocone_composable u c = True.
Proof.
ir. uf cocone_composable. 
app iff_eq; ir; try tv. xd.  
Qed.

Definition cocone_compose u c :=
cocone_create (target u) (vcompose  
(constant_nt (cocone_source c) (cocone_target c) u) 
(coedge_nt c)).

Lemma vertex_cocone_compose : forall u c ,
vertex (cocone_compose u c) = target u.
Proof.
ir. uf cocone_compose. rw vertex_cocone_create. tv. 
Qed.

Lemma coedge_nt_cocone_compose : forall u c,
coedge_nt (cocone_compose u c) = (vcompose 
(constant_nt (cocone_source c) (cocone_target c) u)
(coedge_nt c)).
Proof. ir. 
uf cocone_compose. rw coedge_nt_cocone_create. tv. 
Qed.

Lemma coedge_cocone_compose : forall c u x,
ob (cocone_source c) x -> 
coedge (cocone_compose u c) x = 
comp (cocone_target c) u (coedge c x).
Proof.
ir.
uf coedge. rw coedge_nt_cocone_compose. 
rw ntrans_vcompose. 
rw otarget_constant_nt. 
rw ntrans_constant_nt. tv. am. 
rw osource_coedge_nt. am. 
Qed. 

Lemma source_coedge_nt : forall c,
source (coedge_nt c) = cosocle c.
Proof. ir. tv. Qed. 

Lemma target_coedge_nt : forall c, is_cocone c ->
target (coedge_nt c) = constant_functor (cocone_source c)
(cocone_target c) (vertex c). 
Proof.
ir. uh H. 
ee; am. 
Qed. 

Lemma cosocle_cocone_compose : forall c u,
cosocle (cocone_compose u c) = cosocle c.
Proof.
ir. uf cosocle. rw coedge_nt_cocone_compose. 
rw source_vcompose. tv. 
Qed.

Lemma cocone_target_cocone_compose : forall c u,
cocone_target (cocone_compose u c) = 
cocone_target c.
Proof.
ir. uf cocone_target. rw cosocle_cocone_compose. tv. 
Qed.

Lemma cocone_source_cocone_compose : forall c u,
cocone_source (cocone_compose u c) = 
cocone_source c.
Proof.
ir. uf cocone_source. rw cosocle_cocone_compose. tv. 
Qed.

Lemma mor_coedge : forall c x,
ob (cocone_source c) x -> is_cocone c ->
mor (cocone_target c) (coedge c x).
Proof.
ir. uf coedge. ap mor_ntrans. 
lu. rww osource_coedge_nt. rww otarget_coedge_nt. 
Qed. 


Lemma ob_vertex : forall c,
is_cocone c -> ob (cocone_target c) (vertex c).
Proof.
ir. uh H; ee. am. 
Qed. 

Lemma target_coedge : forall c x,
ob (cocone_source c) x -> is_cocone c ->
target (coedge c x) = vertex c.
Proof.
ir. uf coedge. rw target_ntrans. 
rw target_coedge_nt. 
rw fob_constant_functor. tv. am. 
ap ob_vertex. am. am. lu. 
rww osource_coedge_nt. 
Qed.


Lemma source_coedge : forall c x,
ob (cocone_source c) x -> is_cocone c ->
source (coedge c x) = fob (cosocle c) x.
Proof.
ir. uf coedge. 
rw source_ntrans. tv. uh H0; ee. am. 
ufi cocone_source H. ufi cosocle H. 
am. 
Qed.

Lemma ntrans_coedge_nt : forall c x,
ntrans (coedge_nt c) x = coedge c x.
Proof.
ir. tv. 
Qed. 

Lemma cocommutativity : forall c u,
mor (cocone_source c) u -> is_cocone c ->
comp (cocone_target c) (coedge c (target u)) 
(fmor (cosocle c) u) =
coedge c (source u).
Proof.
ir. 
assert (K:is_cocone c). am. 
uh H0; ee. uf coedge. 
assert (cocone_target c = otarget (coedge_nt c)). 
rww otarget_coedge_nt. 
assert (cosocle c = source (coedge_nt c)). 
rww source_coedge_nt. 
assert (lem1: forall y, ntrans (coedge_nt c) y = coedge c y). 
ir. tv. 
rw H4; rw H5. 
rw carre. 
rw target_coedge_nt. 
rw fmor_constant_functor. rw left_id. tv. 
wr H4; am. wr H4. change (mor (cocone_target c) (coedge c (source u))).
app mor_coedge. rww ob_source. 
rw ntrans_coedge_nt. rw target_coedge. tv. 
rww ob_source. am. 
 rww otarget_coedge_nt. am. am. am. 
rww osource_coedge_nt. 
Qed. 

Lemma cocone_source_axioms : forall c, is_cocone c ->
Category.axioms (cocone_source c).
Proof.
ir. cp H. uh H; ee. uh H1; ee. 
rwi osource_coedge_nt H4. exact H4. 
Qed.

Lemma cocone_target_axioms : forall c, is_cocone c ->
Category.axioms (cocone_target c).
Proof.
ir. cp H. uh H; ee. uh H1; ee. 
rwi otarget_coedge_nt H5. exact H5. am. 
Qed.

Lemma cosocle_axioms : forall c, is_cocone c ->
Functor.axioms (cosocle c).
Proof.
ir. uh H; ee. uh H0; ee. 
exact H5. 
Qed.




Lemma is_cocone_cocone_compose : forall c u,
cocone_composable u c -> 
is_cocone (cocone_compose u c).
Proof.
ir. 
assert (is_cocone c). lu. 
uhg; ee. uf cocone_like. uf cocone_compose. 
rw vertex_cocone_create. rw coedge_nt_cocone_create. tv. 
rw coedge_nt_cocone_compose. 
rww vcompose_axioms.  
ap constant_nt_axioms. 
app cocone_source_axioms. app cocone_target_axioms. 
uh H; ee; am. app coedge_nt_axioms. 
rww source_constant_nt. 
rw target_coedge_nt. 
uh H; ee. rww H2. am. 
rw cocone_target_cocone_compose. rw vertex_cocone_compose. 
rw ob_target. tv. uh H; ee; am. 
rw coedge_nt_cocone_compose. 
rw target_vcompose. rw target_constant_nt. 
rw cocone_source_cocone_compose. rw cocone_target_cocone_compose. 
rw vertex_cocone_compose. tv. 
Qed.

Lemma cocone_compose_cocone_compose : forall a u v,
cocone_composable u a -> composable (cocone_target a) v u ->
cocone_compose v (cocone_compose u a) =
cocone_compose (comp (cocone_target a) v u) a.
Proof.
ir. 
rwi composable_facts_rw H0. 
apply cocone_extensionality. 
app is_cocone_cocone_compose. uf cocone_composable; ee. 
app is_cocone_cocone_compose. rw cocone_target_cocone_compose. 
lu. 
rw vertex_cocone_compose. uh H0; ee; am. 
app is_cocone_cocone_compose. uhg; ee. lu. 
rww mor_comp. lu. lu. lu. 
rw source_comp. lu. lu. lu. lu. 
rw vertex_cocone_compose. rw vertex_cocone_compose. 
rw target_comp. tv. lu. lu. lu. 
rw cosocle_cocone_compose. rw cosocle_cocone_compose.
rw cosocle_cocone_compose. tv. 
ir. rw coedge_cocone_compose. rw cocone_target_cocone_compose. 
rw coedge_cocone_compose. rw coedge_cocone_compose. 
rw assoc. tv. uh H0; ee; am. uh H0; ee; am. 
ap mor_coedge. rwi cocone_source_cocone_compose H1. 
rwi cocone_source_cocone_compose H1. am. lu. 
uh H; ee. uh H0; ee; am. 
rw target_coedge. uh H; ee; am. 
rwi cocone_source_cocone_compose H1. 
rwi cocone_source_cocone_compose H1. 
am. lu.  tv. 
rwi cocone_source_cocone_compose H1. 
rwi cocone_source_cocone_compose H1. 
am. 
uhg; ee. ap cocone_source_axioms. 
lu. ap ob_is_ob. rwi cocone_source_cocone_compose H1. 
rwi cocone_source_cocone_compose H1. am. 
rwi cocone_source_cocone_compose H1. am. 
Qed. 

Definition is_couni a :=
is_cocone a & 
(forall u v, cocone_composable u a -> cocone_composable v a ->
cocone_compose u a = cocone_compose v a -> u = v).

Definition is_coversal a :=
is_cocone a &
(forall b, is_cocone b -> cosocle b = cosocle a -> 
(exists u, (cocone_composable u a & cocone_compose u a = b))).

Definition is_colimit a :=
is_couni a & is_coversal a.

Lemma is_colimit_is_coversal : forall a,
is_colimit a -> is_coversal a.
Proof. ir. lu. Qed.

Lemma is_colimit_is_couni : forall a,
is_colimit a -> is_couni a.
Proof. ir. lu. Qed. 

Lemma is_colimit_is_cocone : forall a,
is_colimit a -> is_cocone a.
Proof.
ir. lu. 
Qed.

Definition is_colimit_of f a :=
is_colimit a & cosocle a = f. 

Definition has_colimit f :=
exists a, is_colimit_of f a.

Definition has_colimits_over c b :=
(forall f, 
Functor.axioms f -> source f = c -> target f = b ->
has_colimit f).



(************ at this point it is a good idea
to start the comparison with 
limits **********************************************)

Definition oppc c := 
(cocone_create (vertex c)
(oppnt (edge_nt c))).




Lemma oppc_co : forall c, 
oppc c = cone_create (vertex c)
(oppnt (coedge_nt c)).
Proof.
ir. uf oppc. 
uf cocone_create. uf coedge_nt. tv. 
Qed. 

Lemma vertex_oppc : forall c, vertex (oppc c) = vertex c.
Proof.
ir. uf oppc. rw vertex_cocone_create. tv. 
Qed. 

Lemma coedge_nt_oppc : forall c,
coedge_nt (oppc c) = oppnt (edge_nt c).
Proof.
ir. uf oppc. rww coedge_nt_cocone_create.
Qed.

Lemma edge_nt_oppc : forall c,
edge_nt (oppc c) = oppnt (coedge_nt c).
Proof.
ir. uf oppc. rww edge_nt_cone_create.
Qed.

Lemma coedge_oppc : forall c x,
ob (cone_source c) x -> is_cone c -> 
coedge (oppc c) x = flip (edge c x). 
Proof.
ir. uf coedge. rw coedge_nt_oppc. 
rw ntrans_oppnt. tv. 
app edge_nt_axioms. rw osource_edge_nt. am. am.
Qed.

Lemma edge_oppc : forall c x,
ob (cocone_source c) x -> is_cocone c -> 
edge (oppc c) x = flip (coedge c x). 
Proof.
ir. uf edge. rw edge_nt_oppc. 
rw ntrans_oppnt. tv. 
app coedge_nt_axioms. rw osource_coedge_nt. am. 
Qed.

Lemma oppc_oppc_cone : forall c, is_cone c ->
oppc (oppc c) = c.
Proof.
ir. uf oppc. 
rw vertex_cocone_create. 
uf cocone_create. 
rw edge_nt_cone_create. rw oppnt_oppnt.
uh H; ee. uh H; ee. am. 
Qed.

Lemma oppc_oppc_cocone : forall c, is_cocone c ->
oppc (oppc c) = c.
Proof.
ir. rw oppc_co. 
rw vertex_oppc. 
rw coedge_nt_oppc. rw oppnt_oppnt. 
uh H; ee. uh H; ee. am. 
Qed. 


Lemma cosocle_oppc : forall c,
is_cone c -> 
cosocle (oppc c) = oppf (socle c).
Proof.
ir. uf cosocle. 
rw coedge_nt_oppc. 
rw source_oppnt. tv. 
app edge_nt_axioms. 
Qed.

Lemma socle_oppc : forall c, is_cocone c ->
socle (oppc c) = oppf (cosocle c).
Proof.
ir. uf socle. 
rw edge_nt_oppc. 
rw target_oppnt. tv. 
app coedge_nt_axioms. 
Qed. 

Lemma cocone_source_oppc : forall c, is_cone c -> 
cocone_source (oppc c) = opp (cone_source c).
Proof.
ir. uf cocone_source. 
rw cosocle_oppc. rw source_oppf. tv. 
ap socle_axioms. am. am. 
Qed.

Lemma cocone_target_oppc :  forall c, is_cone c ->
cocone_target (oppc c) = opp (cone_target c).
Proof.
ir. uf cocone_target. 
rw cosocle_oppc. rw target_oppf. tv. 
app socle_axioms. am. 
Qed.

Lemma cone_source_oppc : forall c, is_cocone c ->
cone_source (oppc c) = opp (cocone_source c).
Proof.
ir. uf cone_source. 
rw socle_oppc. rw source_oppf. tv. 
app cosocle_axioms. am. 
Qed.

Lemma cone_target_oppc :  forall c, is_cocone c ->
cone_target (oppc c) = opp (cocone_target c).
Proof.
ir. uf cone_target. 
rw socle_oppc. rw target_oppf. tv. 
app cosocle_axioms. am. 
Qed.

Lemma is_cocone_oppc : forall c, is_cone c ->
is_cocone (oppc c).
Proof.
ir. 
cp H; uh H; uhg; ee. 
uh H; uhg. 
rw vertex_oppc. rw coedge_nt_oppc. 
uf oppc. tv. rw coedge_nt_oppc. app oppnt_axioms. 
rw cocone_target_oppc. rw ob_opp. 
rw vertex_oppc. am. 
am. 

rw coedge_nt_oppc. rw target_oppnt. 
rw source_edge_nt. 
rw cocone_source_oppc. 
rw cocone_target_oppc. 
rw vertex_oppc. rw oppf_constant_functor.
reflexivity. app cone_source_axioms. 
app Limit.ob_vertex. am. 
am. am. am. Qed.

Lemma is_cone_oppc : forall c, is_cocone c ->
is_cone (oppc c).
Proof.
ir. 
cp H; uh H; uhg; ee. 
uh H; uhg. 
rw vertex_oppc. rw coedge_nt_oppc. 
uf oppc. tv. rw coedge_nt_oppc. app oppnt_axioms. 
rw cone_target_oppc. rw ob_opp. 
rw vertex_oppc. am. 
am.  

rw edge_nt_oppc. rw source_oppnt. 
rw target_coedge_nt. 
rw cone_source_oppc. 
rw cone_target_oppc. 
rw vertex_oppc. rw oppf_constant_functor.
reflexivity. app cocone_source_axioms. 
app ob_vertex. am. am. am. am. 
Qed.

Lemma cocone_composable_oppc : forall c u,
cone_composable c (flip u) ->
cocone_composable u (oppc c). 
Proof.
ir. 
uhg; ee. ap is_cocone_oppc. 
uh H; ee; am. rw cocone_target_oppc. 
rw mor_opp. uh H; ee; am. 
uh H; ee. am. 

rw vertex_oppc. uh H; ee. 
wr H1. 
rww target_flip. 
apply by_cases with (Arrow.like u).
ir. am. ir. 
rwi flip_not_like H0. 
apply mor_arrow_like with (cone_target c); am. 
am. 
Qed. 

Lemma cone_composable_oppc : forall c u,
cocone_composable (flip u) c->
cone_composable (oppc c) u. 
Proof.
ir. 
uhg; ee. ap is_cone_oppc. 
uh H; ee; am. rw cone_target_oppc. 
rw mor_opp. uh H; ee; am. 
uh H; ee; am. 
rw vertex_oppc. uh H; ee. 
wr H1. 
rww source_flip. 
apply by_cases with (Arrow.like u).
ir. am. ir. 
rwi flip_not_like H0. 
apply mor_arrow_like with (cocone_target c); am. 
am. 
Qed. 


Lemma oppc_cone_compose : forall c u,
cone_composable c u -> 
oppc (cone_compose c u) =  (cocone_compose (flip u) (oppc c)).
Proof.
ir. 
assert (cocone_composable (flip u) (oppc c)).
ap cocone_composable_oppc. rw flip_flip.
am. 
ap cocone_extensionality. 
app is_cocone_oppc. 
rww is_cone_cone_compose. 
app is_cocone_cocone_compose. 
rw vertex_oppc. rw vertex_cone_compose. 
rw vertex_cocone_compose. rw target_flip.
tv. uh H; ee. ap (mor_arrow_like H1). 

rw cosocle_oppc. rw socle_cone_compose. 
rw cosocle_cocone_compose. rw cosocle_oppc. tv. 

uh H; ee; am. rww is_cone_cone_compose.

ir. 
assert (is_cone c). 
uh H; ee; am. 
rwi cocone_source_oppc H1. 
rwi cone_source_cone_compose H1. 
cp H1. rwi ob_opp H1. 


rw coedge_oppc. sy. 
rw coedge_cocone_compose. 
rw edge_cone_compose. 
rw coedge_oppc. 
rw cocone_target_oppc. rw comp_opp. 
rw flip_flip. rw flip_flip. tv. 
wr cocone_target_oppc. 
rw cocone_target_oppc. 
rw mor_opp. rw flip_flip. 
uh H; ee; am. uh H; ee; am. uh H; ee; am. 
rw mor_opp. rw flip_flip. 
ap mor_edge. am. uh H; ee; am. 

rw source_flip. rw target_flip.
rw source_edge. uh H; ee; am. am. 
am. 
apply mor_arrow_like with (cone_target c). app mor_edge. 
uh H; ee; alike. am. am. am. 
am. am. 
rw cocone_source_oppc. am. am. 
rww cone_source_cone_compose. rww is_cone_cone_compose. 
rww is_cone_cone_compose. 
Qed. 

Lemma oppc_cocone_compose : forall c u,
cocone_composable u c -> 
oppc (cocone_compose u c) =  (cone_compose (oppc c) (flip u)).
Proof.
ir. 
assert (cone_composable (oppc c) (flip u)).
ap cone_composable_oppc. rw flip_flip.
am. 
ap cone_extensionality. 
app is_cone_oppc. 
app is_cocone_cocone_compose. 
rww is_cone_cone_compose. 
rw vertex_oppc. rw vertex_cocone_compose. 
rw vertex_cone_compose. rw source_flip.
tv. uh H; ee. ap (mor_arrow_like H1). 

rw socle_oppc. rw cosocle_cocone_compose. 
rw socle_cone_compose. rw socle_oppc. tv. 
uh H; ee; am.
app is_cocone_cocone_compose. 

ir. 
 rwi cone_source_oppc H1. 
rwi cocone_source_cocone_compose H1. 
cp H1. rwi ob_opp H1. 
wri cone_source_oppc H2. 

rw edge_oppc. sy. 
rw edge_cone_compose. 
rw coedge_cocone_compose. 
rw edge_oppc. 
rw cone_target_oppc. rw comp_opp. 
rw flip_flip. rw flip_flip. tv. 
rw mor_opp. 
rw flip_flip. ap mor_coedge. am. uh H; ee; am. 
rw mor_opp. rw flip_flip. uh H; ee; am. 
rw source_flip. rw target_flip.
rw target_coedge. uh H; ee; sy; am. 
am. uh H; ee; am. uh H; ee; alike. 
apply mor_arrow_like with (cocone_target c). ap mor_coedge. 
am. uh H; ee; am. uh H; ee; am. am. uh H; ee; am. 
am. am. am. 
rww cocone_source_cocone_compose. app is_cocone_cocone_compose. 
uh H; ee; am. app is_cocone_cocone_compose. 
Qed. 

Lemma is_couni_oppc : forall c,
is_uni c -> is_couni (oppc c).
Proof.
ir. cp H. uh H0; ee. 
uhg. ee. app is_cocone_oppc. 
ir. 
assert (c = oppc (oppc c)).
rww oppc_oppc_cone. 
assert (cone_composable c (flip u)).
rw H5. 
ap cone_composable_oppc. rw flip_flip. am.
assert (cone_composable c (flip v)).
rw H5. 
ap cone_composable_oppc. rw flip_flip. am.


assert (flip u = flip v).
ap H1. am. am. 

transitivity (oppc (oppc (cone_compose c (flip u)))).
sy. rw oppc_oppc_cone. reflexivity. 
rww is_cone_cone_compose. 
rw oppc_cone_compose. 
rw flip_flip. rw H4. 
transitivity (oppc (oppc (cone_compose c (flip v)))).
sy. rw oppc_cone_compose. rw flip_flip. 
reflexivity. 
am. 
rw oppc_oppc_cone. reflexivity. 
rww is_cone_cone_compose. am. 
transitivity (flip (flip u)). rww flip_flip. 
rw H8. rww flip_flip. 
Qed. 

Lemma is_uni_oppc : forall c,
is_couni c -> is_uni (oppc c).
Proof.
ir. cp H. uh H0; ee. 
uhg. ee. app is_cone_oppc. 
ir. 
assert (c = oppc (oppc c)).
rww oppc_oppc_cocone. 
assert (cocone_composable (flip u) c).
rw H5. 
ap cocone_composable_oppc. rw flip_flip. am.
assert (cocone_composable (flip v) c).
rw H5. 
ap cocone_composable_oppc. rw flip_flip. am.


assert (flip u = flip v).
ap H1. am. am. 

transitivity (oppc (oppc (cocone_compose (flip u) c))).
sy. rw oppc_oppc_cocone. reflexivity. 
app is_cocone_cocone_compose. 
rw oppc_cocone_compose. 
rw flip_flip. rw H4. 
transitivity (oppc (oppc (cocone_compose (flip v) c))).
sy. rw oppc_cocone_compose. rw flip_flip. 
reflexivity. 
am. 
rw oppc_oppc_cocone. reflexivity. 
app is_cocone_cocone_compose. am. 
transitivity (flip (flip u)). rww flip_flip. 
rw H8. rww flip_flip. 
Qed. 

Lemma is_coversal_oppc : forall c,
is_versal c -> is_coversal (oppc c).
Proof.
ir. uh H; uhg; ee. 
app is_cocone_oppc. ir. 
cp H2. rwi cosocle_oppc H3. 
util (H0 (oppc b)). app is_cone_oppc. 
rw socle_oppc. rw H3. 
rw oppf_oppf. tv. am. 
nin H4. ee. 
assert (cocone_composable (flip x) (oppc c)).
app cocone_composable_oppc. rww flip_flip.
sh (flip x). ee; try am.
transitivity (oppc (oppc b)). wr H5.
sy. rw oppc_cone_compose. reflexivity. am. 
rww oppc_oppc_cocone. 
am. 
Qed.

Lemma is_versal_oppc : forall c,
is_coversal c -> is_versal (oppc c).
Proof.
ir. uh H; uhg; ee. 
app is_cone_oppc. ir. 
cp H2. rwi socle_oppc H3. 
util (H0 (oppc b)). app is_cocone_oppc. 
rw cosocle_oppc. rw H3. 
rw oppf_oppf. tv. am. 
nin H4. ee. 
assert (cone_composable (oppc c) (flip x)).
app cone_composable_oppc. rww flip_flip.
sh (flip x). ee; try am.
transitivity (oppc (oppc b)). wr H5.
sy. rw oppc_cocone_compose. reflexivity. am. 
rww oppc_oppc_cone. am. 
Qed.

Lemma is_limit_oppc : forall c,
is_colimit c -> is_limit (oppc c).
Proof.
ir. uh H; uhg; ee. app is_uni_oppc.
app is_versal_oppc.
Qed.


Lemma is_colimit_oppc : forall c,
is_limit c -> is_colimit (oppc c).
Proof.
ir. uh H; uhg; ee. app is_couni_oppc.
app is_coversal_oppc.
Qed.

Lemma is_colimit_of_oppf : forall f a,
is_limit_of f a -> is_colimit_of (oppf f) (oppc a).
Proof.
ir. uhg; ee. ap is_colimit_oppc. 
uh H; ee; am.
rw cosocle_oppc. 
uh H; ee. rww H0. 
uh H; ee. uh H; ee. uh H; ee. am. 
Qed. 

Lemma is_limit_of_oppf : forall f a,
is_colimit_of f a -> is_limit_of (oppf f) (oppc a).
Proof.
ir. uhg; ee. ap is_limit_oppc. 
uh H; ee; am.
rw socle_oppc. 
uh H; ee. rww H0. 
uh H; ee. uh H; ee. uh H; ee. am. 
Qed. 

Lemma has_colimit_oppf : forall f,
has_limit f -> has_colimit (oppf f).
Proof.
ir. uhg. uh H; ee. nin H. sh (oppc x).
app is_colimit_of_oppf. 
Qed.

Lemma has_limit_oppf : forall f,
has_colimit f -> has_limit (oppf f).
Proof.
ir. uhg. uh H; ee. nin H. sh (oppc x).
app is_limit_of_oppf. 
Qed.

Lemma has_colimits_over_opp : forall b c,
Category.axioms b -> Category.axioms c -> 
has_limits_over c b ->
has_colimits_over (opp c) (opp b).
Proof.
ir. uhg. 
ir. assert (f = oppf (oppf f)). 
rww oppf_oppf. rw H5. 
ap has_colimit_oppf. uh H1. 
ap H1. app oppf_axioms. rw source_oppf. rw H3.
rww opp_opp. am. rw target_oppf. rw H4. 
rww opp_opp. am.  
Qed. 

Lemma has_limits_over_opp : forall b c,
Category.axioms b -> Category.axioms c -> 
has_colimits_over c b ->
has_limits_over (opp c) (opp b).
Proof.
ir. uhg. 
ir. assert (f = oppf (oppf f)). 
rww oppf_oppf. rw H5. 
ap has_limit_oppf. uh H1. 
ap H1. app oppf_axioms. rw source_oppf. rw H3.
rww opp_opp. am. rw target_oppf. rw H4. 
rww opp_opp. am.  
Qed. 



(************************ now we get back to the
definition of colimit; we use the above so that
it is involutive with respect to oppc ************)

(**** the definition obtained by copying limits.v would be:
Definition colimit f :=
choose (is_colimit_of f).
************* however this doesn't seem to give 
oppc (colimit) = limit
which would seem practical...********************)

Definition colimit f := oppc (limit (oppf f)).

Lemma has_colimit_functor_axioms : forall f,
has_colimit f -> Functor.axioms f.
Proof.
ir. uh H. nin H. uh H. ee. 
wr H0. ap cosocle_axioms. app is_colimit_is_cocone. 
Qed. 

Lemma has_limit_functor_axioms : forall f,
has_limit f -> Functor.axioms f.
Proof.
ir. uh H. nin H. uh H. ee. 
wr H0. ap socle_axioms. app is_limit_is_cone. 
Qed. 

Lemma if_has_colimit : forall f,
has_colimit f -> is_colimit_of f (colimit f).
Proof.
ir. 
uhg. ee. uf colimit. 
ap is_colimit_oppc. 
ap is_limit_limit. ap has_limit_oppf. am. 
uf colimit. rw cosocle_oppc. 
rw socle_limit. rw oppf_oppf. 
tv. 
app has_limit_oppf. 
app is_limit_is_cone. app is_limit_limit. 
app has_limit_oppf. 
Qed. 

Lemma is_colimit_colimit : forall f,
has_colimit f -> is_colimit (colimit f).
Proof.
ir. cp (if_has_colimit H). lu. 
Qed. 

Lemma cosocle_colimit : forall f,
has_colimit f -> cosocle (colimit f) = f.
Proof.
ir. cp (if_has_colimit H). lu. 
Qed. 

Lemma colimit_oppf : forall f, has_limit f ->
colimit (oppf f) = oppc (limit f).
Proof.
ir. uf colimit. rw oppf_oppf. 
tv. 
Qed. 

Lemma limit_oppf : forall f, has_colimit f ->
limit (oppf f) = oppc (colimit f).
Proof.
ir. uf colimit. rw oppc_oppc_cone. 
tv. ap is_limit_is_cone. 
ap is_limit_limit. app has_limit_oppf. 
Qed. 

(****** we should also continue integrating 
results about cocommutation with oppc into the rest of the
file below (later...) ************************)

Definition colimit_to_cocone b a :=
choose (fun u => (cocone_composable u b & cocone_compose u b = a)).

Lemma colimit_to_cocone_pr : forall a b,
is_cocone a -> is_colimit b -> cosocle a = cosocle b ->
(cocone_composable (colimit_to_cocone b a) b 
& cocone_compose (colimit_to_cocone b a) b = a).
Proof.
ir. uh H0; ee. uh H2; ee. util (H3 a). am. am. 
cp (choose_pr H4). cbv beta in H5. ee. 
am. uh H2; ee. 
util (H3 a). am. am. 
cp (choose_pr H4). cbv beta in H5. ee. 
am. 
Qed.

Lemma mor_colimit_to_cocone : forall a b y,
is_cocone a -> is_colimit b -> cosocle a = cosocle b ->
y = cocone_target b ->
mor y (colimit_to_cocone b a). 
Proof.
ir. cp (colimit_to_cocone_pr H H0 H1). 
ee. uh H3; ee. rw H2; am. 
Qed. 

Lemma target_colimit_to_cocone : forall a b,
is_cocone a -> is_colimit b -> cosocle a = cosocle b ->
target (colimit_to_cocone b a) = vertex a.
Proof.
ir. cp (colimit_to_cocone_pr H H0 H1). 
ee. transitivity (vertex (cocone_compose (colimit_to_cocone b a) b)).
rw vertex_cocone_compose. tv. 
rw H3. tv. 
Qed.

Lemma source_colimit_to_cocone : forall a b,
is_cocone a -> is_colimit b -> cosocle a = cosocle b ->
source (colimit_to_cocone b a) = vertex b.
Proof.
ir. cp (colimit_to_cocone_pr H H0 H1). 
ee. uh H2; ee. am. 
Qed.

Lemma cocone_compose_colimit_to_cocone : forall a b,
is_cocone a -> is_colimit b ->  cosocle a = cosocle b ->
cocone_compose (colimit_to_cocone b a) b = a.
Proof.
ir. cp (colimit_to_cocone_pr H H0 H1). 
ee. am. 
Qed. 

Lemma cocone_composable_colimit_to_cocone : forall a b,
is_cocone a -> is_colimit b -> cosocle a = cosocle b -> 
cocone_composable (colimit_to_cocone b a) b. 
Proof.
ir. 
cp (colimit_to_cocone_pr H H0 H1). 
ee. am.  
Qed. 

Lemma colimit_to_cocone_cocone_compose1 : forall a u, 
is_colimit a -> cocone_composable u a ->
colimit_to_cocone a (cocone_compose u a) = u. 
Proof.
ir. 
assert (lem1 : is_colimit a). am. 
uh H; ee. uh H; ee. ap H2. 
uhg; ee. am. ap mor_colimit_to_cocone.
app is_cocone_cocone_compose. 
am.  rw cosocle_cocone_compose. tv. tv. 
rw source_colimit_to_cocone. tv. app is_cocone_cocone_compose.
am.  rw cosocle_cocone_compose. tv. am. 
rw cocone_compose_colimit_to_cocone. tv. 
app is_cocone_cocone_compose. am. rww cosocle_cocone_compose.
Qed. 

Lemma colimit_to_cocone_cocone_compose : forall a b u,
is_colimit b -> cocone_composable u a -> 
cosocle a = cosocle b ->
colimit_to_cocone b (cocone_compose u a) = 
comp (cocone_target b) u (colimit_to_cocone b a).
Proof.
ir. set (k:= comp (cocone_target b) u (colimit_to_cocone b a)).
assert (cocone_target a = cocone_target b). 
uf cocone_target. rww H1. 
assert (lem1 : is_cocone a). 
lu. 
transitivity (colimit_to_cocone b (cocone_compose k b)).
uf k. wr cocone_compose_cocone_compose. 
rw cocone_compose_colimit_to_cocone. tv. lu. 
am. am. 
app cocone_composable_colimit_to_cocone. 
app show_composable. 
wr H2; uh H0; ee; am.
app mor_colimit_to_cocone.  
rww target_colimit_to_cocone. uh H0; ee; am.   
rww colimit_to_cocone_cocone_compose1. 
uf k. uhg; ee. uh H; ee. uh H; ee; am. 
rww mor_comp. 
wr H2; uh H0; ee; am.
app mor_colimit_to_cocone. 
rww target_colimit_to_cocone. uh H0; ee; am.  
rw source_comp. 
rww source_colimit_to_cocone. 
wr H2; uh H0; ee; am.
app mor_colimit_to_cocone. 
rww target_colimit_to_cocone. uh H0; ee; am.  
Qed.


Definition cocone_transform c u :=
cocone_create (vertex c) (vcompose (coedge_nt c) u).

Lemma vertex_cocone_transform : forall u c,
vertex (cocone_transform c u) = vertex c.
Proof.
ir. uf cocone_transform. rww vertex_cocone_create. 
Qed.

Lemma coedge_nt_cocone_transform : forall u c,
coedge_nt (cocone_transform c u) = vcompose (coedge_nt c) u.
Proof.
ir. uf cocone_transform. rww coedge_nt_cocone_create. 
Qed.



Lemma cosocle_cocone_transform : forall u c,
cosocle (cocone_transform c u) = source u.
Proof.
ir. uf cosocle. 
rww coedge_nt_cocone_transform. rww source_vcompose. 
Qed.

Definition cocone_transformable c u :=
is_cocone c &
Nat_Trans.axioms u &
target u = cosocle c.

Lemma source_cosocle : forall c, source (cosocle c) =
cocone_source c.
Proof.
ir. tv. 
Qed. 

Lemma target_cosocle : forall c, target (cosocle c)
= cocone_target c.
Proof.
ir. tv. 
Qed. 

Lemma coedge_cocone_transform : forall c u x,
cocone_transformable c u -> ob (cocone_source c) x -> 
coedge (cocone_transform c u) x =
comp (cocone_target c) (coedge c x) (ntrans u x).
Proof.
ir. uf coedge. 
rw coedge_nt_cocone_transform. 
rw ntrans_vcompose. 
rw otarget_coedge_nt. tv. uh H; ee; am. 
uh H; ee. wr source_target. rw H2. 
rw source_cosocle. am. am.  
Qed.

Lemma cocone_source_cocone_transform : forall u c,
cocone_transformable c u -> 
cocone_source (cocone_transform c u) = cocone_source c.
Proof.
ir. uf cocone_source. 
rw cosocle_cocone_transform. 
uh H; ee.  rw source_source.
wr source_target. rww H1. am. 
Qed.

Lemma cocone_target_cocone_transform : forall u c,
cocone_transformable c u -> 
cocone_target (cocone_transform c u) = cocone_target c.
Proof.
ir. uf cocone_target. 
rww cosocle_cocone_transform. 
uh H; ee. wr H1. rww target_source. 
Qed.



Lemma is_cocone_cocone_transform : forall u c,
cocone_transformable c u -> is_cocone (cocone_transform c u).
Proof.
ir. 
cp H; uh H; ee. 
uhg; ee. 
uf cocone_transform. app cocone_like_cocone_create. 
rw coedge_nt_cocone_transform. rww vcompose_axioms. 
app coedge_nt_axioms. 
rww source_coedge_nt. sy; am. 
rw vertex_cocone_transform. rww cocone_target_cocone_transform.
uh H; ee. am. 
rw coedge_nt_cocone_transform. 
rw target_vcompose. rw target_coedge_nt. 
rw cocone_source_cocone_transform. 
rw cocone_target_cocone_transform. rww vertex_cocone_transform.
am. am. am.  
Qed.

Definition cocone_pushdown f c :=
cocone_create (fob f (vertex c)) (htrans_left f (coedge_nt c)).

Lemma vertex_cocone_pushdown : forall f c,
vertex (cocone_pushdown f c) = fob f (vertex c).
Proof.
ir. uf cocone_pushdown. rww vertex_cocone_create. 
Qed.

Lemma coedge_nt_cocone_pushdown : forall f c,
coedge_nt (cocone_pushdown f c) = htrans_left f (coedge_nt c).
Proof.
ir. uf cocone_pushdown. rww coedge_nt_cocone_create. 
Qed.

Lemma cosocle_cocone_pushdown : forall f c,
cosocle (cocone_pushdown f c) = fcompose f (cosocle c).
Proof.
ir. uf cosocle. rw coedge_nt_cocone_pushdown. 
rw source_htrans_left. tv.  
Qed.

Lemma cocone_source_cocone_pushdown : forall f c,
cocone_source (cocone_pushdown f c) = cocone_source c.
Proof.
ir. uf cocone_source. rw cosocle_cocone_pushdown.
rw source_fcompose. tv. 
Qed.

Lemma cocone_target_cocone_pushdown : forall f c,
cocone_target (cocone_pushdown f c) = target f.
Proof.
ir. uf cocone_target. rw cosocle_cocone_pushdown.
rww target_fcompose. 
Qed.

Lemma coedge_cocone_pushdown : forall f c x,
ob (cocone_source c) x -> is_cocone c ->
coedge (cocone_pushdown f c) x = fmor f (coedge c x).
Proof.
ir. uf coedge. 
rw coedge_nt_cocone_pushdown. rw ntrans_htrans_left. 
tv. rww osource_coedge_nt. 
Qed. 

Lemma is_cocone_cocone_pushdown : forall f c,
is_cocone c -> Functor.axioms f -> source f = cocone_target c ->
is_cocone (cocone_pushdown f c).
Proof.
ir. uhg; ee. uf cocone_pushdown. 
ap cocone_like_cocone_create. 
rw coedge_nt_cocone_pushdown. app htrans_left_axioms. 
uh H; ee. am. rww otarget_coedge_nt. 

rw cocone_target_cocone_pushdown. 
rw vertex_cocone_pushdown.
app ob_fob. rw H1. uh H; ee; am. 
rw coedge_nt_cocone_pushdown. rw target_htrans_left. 
rw target_coedge_nt. 
rw fcompose_right_constant_functor. 
rw cocone_source_cocone_pushdown. 
rw cocone_target_cocone_pushdown. 
rw vertex_cocone_pushdown. tv. am. am. 
app cocone_source_axioms. 
app ob_vertex. am. 
Qed. 

Lemma cocone_pushdown_cocone_pushdown : forall f g a,
is_cocone a -> Functor.axioms f -> Functor.axioms g ->
source g = cocone_target a -> source f = target g ->
cocone_pushdown f (cocone_pushdown g a) =
cocone_pushdown (fcompose f g) a.
Proof.
ir. 
ap cocone_extensionality. 
ap is_cocone_cocone_pushdown. ap is_cocone_cocone_pushdown. 
am. am. am. am. 
rw cocone_target_cocone_pushdown. am. 
ap is_cocone_cocone_pushdown. am. 
ap fcompose_axioms. am. 
am. am. rw source_fcompose. am. 
rw vertex_cocone_pushdown. 
rw vertex_cocone_pushdown. 
rw vertex_cocone_pushdown. 
rw fob_fcompose. tv. am. 
am. am. rw H2. ap ob_vertex. 
am. 
rww cosocle_cocone_pushdown. rww cosocle_cocone_pushdown. 
sy; rw cosocle_cocone_pushdown. 
rw fcompose_assoc. tv. am. am. 
app cosocle_axioms. am. am. 

ir. rwi cocone_source_cocone_pushdown H4. 
rwi cocone_source_cocone_pushdown H4. 
rw coedge_cocone_pushdown. 
 rw coedge_cocone_pushdown. 
rw coedge_cocone_pushdown. 
rw fmor_fcompose. tv. am. am. am. 
rw H2. ap mor_coedge. am. am. 
am. am. am. am. rw cocone_source_cocone_pushdown. am. 
app is_cocone_cocone_pushdown.
Qed. 

Definition cocone_pullback f c := 
cocone_create (vertex c) (htrans_right (coedge_nt c) f).

Lemma vertex_cocone_pullback : forall f c,
vertex (cocone_pullback f c) = vertex c.
Proof.
ir. uf cocone_pullback. rww vertex_cocone_create.
Qed.

Lemma coedge_nt_cocone_pullback : forall f c,
coedge_nt (cocone_pullback f c) = htrans_right (coedge_nt c) f.
Proof.
ir. uf cocone_pullback. rww coedge_nt_cocone_create. 
Qed.

Lemma cosocle_cocone_pullback : forall f c,
cosocle (cocone_pullback f c) = fcompose (cosocle c) f.
Proof.
ir. uf cosocle. rw coedge_nt_cocone_pullback. 
rw source_htrans_right. tv.  
Qed.

Lemma cocone_source_cocone_pullback : forall f c,
cocone_source (cocone_pullback f c) = source f.
Proof.
ir. uf cocone_source. rw cosocle_cocone_pullback.
rw source_fcompose. tv. 
Qed.

Lemma cocone_target_cocone_pullback : forall f c,
cocone_target (cocone_pullback f c) = cocone_target c.
Proof.
ir. uf cocone_target. rw cosocle_cocone_pullback.
rww target_fcompose. 
Qed.

Lemma coedge_cocone_pullback : forall f c x,
ob (source f) x -> 
coedge (cocone_pullback f c) x = coedge c (fob f x).
Proof.
ir. uf coedge. 
rw coedge_nt_cocone_pullback. rw ntrans_htrans_right. 
tv. am. 
Qed. 



Lemma is_cocone_cocone_pullback : forall f c,
is_cocone c -> Functor.axioms f -> cocone_source c = target f ->
is_cocone (cocone_pullback f c).
Proof.
ir. uhg; ee. uf cocone_pullback. 
ap cocone_like_cocone_create. 
rw coedge_nt_cocone_pullback. app htrans_right_axioms. 
uh H; ee. am. 

rw cocone_target_cocone_pullback. 
rw vertex_cocone_pullback.
app ob_vertex. 
rw coedge_nt_cocone_pullback. rw target_htrans_right. 
rw target_coedge_nt. 
rw fcompose_left_constant_functor. 
rw cocone_source_cocone_pullback. 
rw cocone_target_cocone_pullback. 
rw vertex_cocone_pullback. tv. am. sy; am. 
app cocone_target_axioms. 
app ob_vertex. am. 
Qed. 



Lemma cocone_compose_id : forall c, 
is_cocone c -> 
cocone_compose (id (cocone_target c) (vertex c)) c = c.
Proof.
ir. ap cocone_extensionality. 
app is_cocone_cocone_compose. 
uhg; ee. am. ap mor_id. ap ob_vertex. 
am. rww source_id. app ob_vertex. am. 
rww vertex_cocone_compose. rww target_id. 
app ob_vertex. rww cosocle_cocone_compose. 
ir. rwi cocone_source_cocone_compose H0. 
rww coedge_cocone_compose. rww left_id. app ob_vertex.
app mor_coedge. rww target_coedge. 
Qed. 

Lemma cocone_compose_cocone_transform : forall f c u,
is_cocone c -> cocone_composable u c -> cocone_transformable c f ->
cocone_compose u (cocone_transform c f) =
cocone_transform (cocone_compose u c) f.
Proof.
ir. ap cocone_extensionality. 
app is_cocone_cocone_compose. 
uhg; ee. app is_cocone_cocone_transform. 
rww cocone_target_cocone_transform. lu. 
rww vertex_cocone_transform. lu. 
app is_cocone_cocone_transform. 
uhg; ee. app is_cocone_cocone_compose. 
lu. rw cosocle_cocone_compose. lu. 
rw vertex_cocone_compose; rww vertex_cocone_transform. 
rww vertex_cocone_compose. 
rw cosocle_cocone_compose. rww cosocle_cocone_transform.
rww cosocle_cocone_transform. 
ir. 
rwi cocone_source_cocone_compose H2. 
rwi cocone_source_cocone_transform H2; try am. 
assert (osource f = cocone_source c). 
uf cocone_source. 
wr source_target. ap uneq. 
uh H1; ee. am. uh H1; ee; am.  
assert (otarget f = cocone_target c). 
uf cocone_target. 
uf otarget. ap uneq. uh H1; ee; am. 

rw coedge_cocone_compose. 
rw coedge_cocone_transform. rw coedge_cocone_transform. 
rww cocone_target_cocone_transform. 
rww cocone_target_cocone_compose. 
rww coedge_cocone_compose. rww assoc. 
uh H0; ee; am. 
app  mor_coedge. uh H0; ee. 
ap mor_ntrans. uh H1; ee; am. 
rww H3. sy; am.  
rww target_coedge. uh H0; ee; am. 
rw target_ntrans. rw source_coedge. 
uh H1; ee. rww H6. am. am. 
uh H1; ee; am. rww H3. 

uhg; ee. app is_cocone_cocone_compose. lu. 
rww cosocle_cocone_compose. lu. 
rw cocone_source_cocone_compose. am. am. am. 
rww cocone_source_cocone_transform. 
Qed.

Lemma colimit_to_cocone_id : forall a b,
is_colimit a -> a = b -> 
colimit_to_cocone a b = id (cocone_target b) (vertex b).
Proof.
ir. wr H0. cp H.
uh H1; ee. 
uh H1; ee. ap H3. 
uhg; ee. am. ap mor_colimit_to_cocone. am. 
am. tv. tv. 
rww source_colimit_to_cocone. 
uhg; ee. am. 
ap mor_id. ap ob_vertex. am. 
rw source_id. tv. ap ob_vertex. am. 
rww cocone_compose_colimit_to_cocone. 
rww cocone_compose_id. 
Qed.


Lemma comp_coedge_colimit_to_cocone : forall r s x b, 
is_colimit s -> is_cocone r -> cosocle r = cosocle s ->
b = cocone_target s -> ob (cocone_source s) x ->
comp b (colimit_to_cocone s r) (coedge s x) =
coedge r x.
Proof.
ir. rw H2. 
transitivity (coedge (cocone_compose (colimit_to_cocone s r) s) x).
rww coedge_cocone_compose. 
rw cocone_compose_colimit_to_cocone. tv. 
am. am. am. 
Qed.


Lemma cocone_transform_vident : forall f c,
f = cosocle c -> is_cocone c ->
cocone_transform c (vident f) = c.
Proof.
ir. uf cocone_transform.
rw weak_right_vident. lu. app coedge_nt_axioms. 
rww source_coedge_nt.  
Qed.



Lemma cocone_transform_vcompose : forall u v c,
is_cocone c -> cocone_transformable c v -> 
Nat_Trans.axioms u -> source v = target u ->
cocone_transform c (vcompose v u) =
cocone_transform (cocone_transform c v) u.
Proof.
ir. uh H0; ee. 
uf cocone_transform. rw vertex_cocone_create. ap uneq. 
rw coedge_nt_cocone_create. 
rww vcompose_assoc.  app coedge_nt_axioms. 
rww source_coedge_nt. sy; am. 
Qed.






(**** stuff about colimits and isomorphisms ****)


Lemma comp_colimit_to_cocone_inversely : forall a b c,
is_colimit a -> is_colimit b -> cosocle a = cosocle b ->
cocone_target a = c ->
comp c (colimit_to_cocone a b) (colimit_to_cocone b a) =
id c (vertex b).
Proof.
ir. 
assert (cocone_target b = c).
uf cocone_target. wr H1. am. 
cp H; cp H0.
uh H4; uh H5; ee. 
uh H4; uh H5. ee. 

assert (composable c (colimit_to_cocone a b) (colimit_to_cocone b a)).
ap show_composable. app mor_colimit_to_cocone. 
sy; am. sy; am. app mor_colimit_to_cocone. sy; am.  
rww source_colimit_to_cocone. rww target_colimit_to_cocone. 
sy; am. 

ap H8. 
uhg; ee. am. rw H3. 
rww mor_comp. 
ap mor_colimit_to_cocone. am. am. sy; am. sy; am. 
app mor_colimit_to_cocone. sy; am.  
rw source_colimit_to_cocone. 
rww target_colimit_to_cocone.  am. am. 
sy; am. 
rw source_comp. rww source_colimit_to_cocone. 
app mor_colimit_to_cocone. sy; am. 
sy; am. app mor_colimit_to_cocone. sy; am.  
rw source_colimit_to_cocone. 
rww target_colimit_to_cocone. am.  am. sy; am. 
uhg; ee. am. rw H3. ap mor_id. 
wr H3. ap ob_vertex. am. 
rw source_id. tv. wr H3; app ob_vertex. 
wr H3. wr cocone_compose_cocone_compose. 
rw cocone_compose_colimit_to_cocone. rw cocone_compose_colimit_to_cocone. 
rw cocone_compose_id. tv. am. am. am. sy; am. 
am. am. am. 

uhg; ee. 
am. app mor_colimit_to_cocone. 
rww source_colimit_to_cocone. 
rww H3.  
Qed. 


Lemma are_inverse_colimit_to_cocone : forall a b c,
is_colimit a -> is_colimit b -> cosocle a = cosocle b ->
cocone_target a = c ->
are_inverse c (colimit_to_cocone a b) (colimit_to_cocone b a).
Proof.
ir. 
assert (cocone_target b = c).
uf cocone_target. wr H1. am. 
cp H; cp H0.
uh H4; uh H5; ee. 
uh H4; uh H5. ee. 
uhg; ee; try am.  
app mor_colimit_to_cocone. 
sy; am. sy; am. 
app mor_colimit_to_cocone. sy; am. 
rww source_colimit_to_cocone. rww target_colimit_to_cocone. 
sy; am. 
rww target_colimit_to_cocone. rww source_colimit_to_cocone.
sy; am. 
rw source_colimit_to_cocone. 
app comp_colimit_to_cocone_inversely. 
am. am. am. 
rww comp_colimit_to_cocone_inversely. 
rww source_colimit_to_cocone. sy; am. sy; am. 
Qed.

Lemma invertible_colimit_to_cocone : forall a b c,
is_colimit a -> is_colimit b -> cosocle a = cosocle b ->
cocone_target a = c -> 
invertible c (colimit_to_cocone a b).
Proof.
ir. 
uhg. sh (colimit_to_cocone b a). 
app are_inverse_colimit_to_cocone. 
Qed.

Lemma inverse_colimit_to_cocone : forall a b c,
is_colimit a -> is_colimit b -> cosocle a = cosocle b ->
cocone_target a = c -> 
inverse c (colimit_to_cocone a b) = colimit_to_cocone b a.
Proof.
ir. 
cp (are_inverse_colimit_to_cocone H H0 H1 H2).
app inverse_eq. 
Qed.

Lemma is_colimit_cocone_compose : forall a u,
is_colimit a -> cocone_composable u a ->
invertible (cocone_target a) u -> 
is_colimit (cocone_compose u a).
Proof.
ir. 
assert (lem1: is_cocone (cocone_compose u a)).
app is_cocone_cocone_compose. 

uhg; ee. 

(**** couni proof ****)
uhg; ee. am. ir. 
assert (mor (cocone_target a) u0).
uh H2; ee. rwi cocone_target_cocone_compose H5. am. 

assert (mor (cocone_target a) v). 
uh H3; ee. rwi cocone_target_cocone_compose H6; am. 
assert (target u = source u0). sy. 
uh H2; ee. rwi vertex_cocone_compose H8; am. 
assert (target u = source v). sy. 
uh H3; ee. rwi vertex_cocone_compose H9; am. 
assert (mor (cocone_target a) u). 
uh H0; ee. am. 
rwi cocone_compose_cocone_compose H4. 
rwi cocone_compose_cocone_compose H4. 
uh H; ee. uh H; ee. 
assert (comp (cocone_target a) u0 u = comp (cocone_target a) v u).
ap H11. uhg; ee. am. rww mor_comp. 
wrr H7. rww source_comp. 
uh H0; ee; am. sy; am.  
uhg; ee. am. rww mor_comp. 
sy; am. rw source_comp. uh H0; ee; am.
lu. lu. sy; am.  am. 
transitivity (comp (cocone_target a) 
(comp (cocone_target a) u0 u) (inverse (cocone_target a) u)). 
rw assoc. 
rw right_inverse. rw right_id. tv. 


rww ob_target. am. sy; am. tv. am. 
am. am. ap mor_inverse. 
am. sy; am. rw target_inverse. tv. am.  tv. 
rw H12. rw assoc. 
rw right_inverse. rw right_id. tv. 
rww ob_target. am. sy; am. tv. am. 
am. am. app mor_inverse. sy; am. 
rww target_inverse. tv. am. app show_composable. 
sy; am. am. app show_composable. sy; am. 

(*** coversal proof ***)
assert (lema: source u = vertex a). lu. 
uhg; ee. am. ir. 
assert (lem0 : cosocle b = cosocle a). 
rwi cosocle_cocone_compose H3. am. 
assert (lem2: composable (cocone_target a) 
(colimit_to_cocone a b) (inverse (cocone_target a) u)).
ap show_composable. 
app mor_colimit_to_cocone. app mor_inverse. 
rw target_inverse.
rww source_colimit_to_cocone. sy; am. am.  

assert (is_cocone a). 
uh H; ee. uh H; ee; am. 

sh (comp (cocone_target a) 
(colimit_to_cocone a b) (inverse (cocone_target a) u)).
ee. 
uhg; ee. am. rw cocone_target_cocone_compose. 
rww mor_comp. 

ap mor_colimit_to_cocone. am. am. am. tv. 
app mor_inverse. 
rww target_inverse. rww source_colimit_to_cocone. sy; am. 
rww source_comp. rww source_inverse. 
rww vertex_cocone_compose. 
app mor_colimit_to_cocone. 
app mor_inverse. 
rww source_colimit_to_cocone. 
rww target_inverse. sy; am. 

assert (cocone_target a = cocone_target (cocone_compose u a)).
rww cocone_target_cocone_compose. 

assert (mor (cocone_target a) u). uh H0; ee; am.  


rw cocone_compose_cocone_compose. 
rw assoc. rww left_inverse. 
rw right_id. rw cocone_compose_colimit_to_cocone. tv. 
am. am. am. rww ob_source. 
app mor_colimit_to_cocone. rw source_colimit_to_cocone. 
sy; am. am. am. am. tv. app mor_colimit_to_cocone. 
app mor_inverse. am. 

rww target_inverse. rww source_colimit_to_cocone. 
sy; am. 
rww source_inverse. tv. am.  ap show_composable. 
rww mor_comp. 
app mor_colimit_to_cocone. app mor_inverse. 
rww target_inverse. rww source_colimit_to_cocone. 
sy; am. am. 
rww source_comp. rww source_inverse. 
app mor_colimit_to_cocone. app mor_inverse. 
rww target_inverse. rww source_colimit_to_cocone. 
sy; am. 
Qed. 

Lemma colimit_to_cocone_invertible_is_colimit : forall a b,
is_colimit b -> is_cocone a -> cosocle a = cosocle b ->
invertible (cocone_target b) (colimit_to_cocone b a) -> 
is_colimit a.
Proof.
ir. assert  (a = cocone_compose (colimit_to_cocone b a) b).
rw cocone_compose_colimit_to_cocone. tv. 
am.  am. am. rw H3. 
ap is_colimit_cocone_compose. am. 
uhg; ee. uh H; ee. uh H; ee; am. 
app mor_colimit_to_cocone.
rww source_colimit_to_cocone. lu. 
Qed.

(***** added in september: dotted *****)

Definition codotted a := colimit_to_cocone (colimit (cosocle a)) a.

Lemma target_codotted : forall a, is_cocone a ->
has_colimit (cosocle a) -> target (codotted a) = vertex a.
Proof.
ir.
uf codotted. rww target_colimit_to_cocone. 
app is_colimit_colimit. 
rww cosocle_colimit. 
Qed. 

Lemma source_codotted : forall a, is_cocone a ->
has_colimit (cosocle a) -> source (codotted a) = 
vertex (colimit (cosocle a)).
Proof.
ir.
uf codotted. rww source_colimit_to_cocone. 
app is_colimit_colimit. 
rww cosocle_colimit. 
Qed. 

Lemma mor_codotted : forall a, is_cocone a ->
has_colimit (cosocle a) -> mor (cocone_target a) (codotted a).
Proof.
ir.
uf codotted. app mor_colimit_to_cocone. 
app is_colimit_colimit. 
rww cosocle_colimit. 
uf cocone_target. rww cosocle_colimit. 
Qed. 

Lemma cocone_target_colimit : forall f,
has_colimit f -> cocone_target (colimit f) = target f.
Proof.
ir. uf cocone_target. rww cosocle_colimit. 
Qed.

Lemma cocone_source_colimit : forall f,
has_colimit f -> cocone_source (colimit f) = source f.
Proof.
ir. uf cocone_source. rww cosocle_colimit. 
Qed. 



Lemma cocone_composable_codotted : forall a, is_cocone a ->
has_colimit (cosocle a) -> cocone_composable 
(codotted a) (colimit (cosocle a)). 
Proof.
ir. uf cocone_composable. ee. 
ap is_colimit_is_cocone. app is_colimit_colimit. 
rww cocone_target_colimit. 
rw target_cosocle. 
app mor_codotted. 
rww source_codotted. 
Qed. 

Lemma cocone_compose_codotted : forall a, is_cocone a ->
has_colimit (cosocle a) -> 
cocone_compose (codotted a) (colimit (cosocle a)) = a.
Proof.
ir. uf codotted. 
rww cocone_compose_colimit_to_cocone. 
app is_colimit_colimit. rww cosocle_colimit. 
Qed. 

Lemma codotted_cocone_compose : forall u a,
cocone_composable u a -> has_colimit (cosocle a) -> 
codotted (cocone_compose u a) = 
comp (cocone_target a) u (codotted a).
Proof.
ir. uf codotted. 
rw colimit_to_cocone_cocone_compose. 
rw cosocle_cocone_compose. 
rw cocone_target_colimit. rw target_cosocle. reflexivity. 
am. app is_colimit_colimit. rw cosocle_cocone_compose. am. 
am. rw cosocle_colimit. rw cosocle_cocone_compose. tv. 
rww cosocle_cocone_compose. 
Qed.

Lemma colimit_to_cocone_refl : forall a, is_colimit a ->
colimit_to_cocone a a = id (cocone_target a) (vertex a).
Proof.
ir. transitivity
(comp (cocone_target a) (colimit_to_cocone a a) (colimit_to_cocone a a)).
wr colimit_to_cocone_cocone_compose. 
rw cocone_compose_colimit_to_cocone. tv. lu. am. 
tv. lu. app cocone_composable_colimit_to_cocone. 
lu. tv. 
rww comp_colimit_to_cocone_inversely. 
Qed.

Lemma codotted_colimit : forall f, Functor.axioms f -> 
has_colimit f ->
codotted (colimit f) = id (target f) (vertex (colimit f)).
Proof.
ir. uf codotted. 
rww cosocle_colimit. 
rw colimit_to_cocone_refl. rw cocone_target_colimit. 
tv. am. app is_colimit_colimit. 
Qed.

Lemma codotted_unique : forall f u, Functor.axioms f ->
has_colimit f -> cocone_composable u (colimit f) -> 
codotted (cocone_compose u (colimit f)) = u.
Proof.
ir. rw codotted_cocone_compose. 
rw codotted_colimit. 
rw cocone_target_colimit. rw right_id. tv. 
assert (target f = cocone_target (colimit f)). 
rww cocone_target_colimit. rw H2. 
app ob_vertex. ap is_colimit_is_cocone. app is_colimit_colimit. 
uh H1; ee. rwi cocone_target_colimit H2. am. am. 
uh H1; ee. am. tv. am. am. am. 
am. rww cosocle_colimit. 
Qed.

Lemma invertible_codotted_is_colimit : forall a,
is_cocone a -> has_colimit (cosocle a) ->
invertible (cocone_target a) (codotted a) -> is_colimit a.
Proof.
ir. 
assert (a = cocone_compose (codotted a) (colimit (cosocle a)) ). 
rww cocone_compose_codotted. 
rw H2. app is_colimit_cocone_compose. 
app is_colimit_colimit. 
app cocone_composable_codotted. 
rw cocone_target_colimit. rw target_cosocle. am. am. 
Qed.

Lemma is_colimit_invertible_codotted : forall a,
is_colimit a -> invertible (cocone_target a) (codotted a).
Proof.
ir. uf codotted. 
assert (has_colimit (cosocle a)). 
uhg. sh a. uhg; ee. am. tv. 
ap invertible_colimit_to_cocone. ap is_colimit_colimit. 
am. 
am. 
rww cosocle_colimit. rw cocone_target_colimit. 
rww target_cosocle. am. 
Qed.


(**** stuff about functors commuting with colimits ***)

Section Cocommutation_Def.
Variable f a b: E.

Hypothesis cocone_a : is_cocone a.
Hypothesis colimit_b : is_colimit b.
Hypothesis fsource_cocone_target : source f = cocone_target a.
Hypothesis f_functor : Functor.axioms f. 
Hypothesis compose_ntarg : fcompose f (cosocle a) = cosocle b.


Definition cocommutation := 
colimit_to_cocone b (cocone_pushdown f a).

Lemma target_cocommutation :  
target cocommutation = fob f (vertex a).
Proof.
uf cocommutation. 
rw target_colimit_to_cocone. 
rww vertex_cocone_pushdown. app is_cocone_cocone_pushdown.
am. rww cosocle_cocone_pushdown. 
Qed.

Lemma source_cocommutation : 
source cocommutation  = vertex b.
Proof.
ir. uf cocommutation. 
rw source_colimit_to_cocone. tv. app is_cocone_cocone_pushdown.
am. rww cosocle_cocone_pushdown. 
Qed.

Lemma cocone_target_b : cocone_target b = target f.
Proof.
uf cocone_target. wr compose_ntarg. 
rw target_fcompose. tv. 
Qed. 


Lemma mor_cocommutation : 
mor (target f) cocommutation.
Proof.
uf cocommutation. 
ap mor_colimit_to_cocone. 
app is_cocone_cocone_pushdown. am. 
rww cosocle_cocone_pushdown. 
rww cocone_target_b. 
Qed.

Lemma cocone_composable_cocommutation : 
cocone_composable cocommutation b.
Proof.
uhg; ee. cp colimit_b. 
uh H; ee. lu. 
rw cocone_target_b.  

ap mor_cocommutation. 
rw source_cocommutation. tv. 
Qed. 

Lemma cocone_compose_cocommutation : 
cocone_compose cocommutation b = cocone_pushdown f a.
Proof.
uf cocommutation. 
rw cocone_compose_colimit_to_cocone. tv. 
app is_cocone_cocone_pushdown. am. 
rww cosocle_cocone_pushdown. 
Qed.

Lemma invertible_cocommutation_is_colimit_cocone_pushdown : 
forall c, target f = c -> 
invertible c cocommutation = 
is_colimit (cocone_pushdown f a).
Proof.
ir. wr H. ap iff_eq; ir. 
wr cocone_compose_cocommutation. 
app is_colimit_cocone_compose. 
ap cocone_composable_cocommutation. 
rww cocone_target_b. 

uf cocommutation. 
ap invertible_colimit_to_cocone. 
am. am. rww cosocle_cocone_pushdown. 
sy; am. 
rww cocone_target_b. 
Qed.


End Cocommutation_Def. 

Section cocone_Pushdown_cocone_Compose.
Variables u a f: E.

Hypothesis K : is_cocone a.
Hypothesis K0 : Functor.axioms f.
Hypothesis K1 : source f = cocone_target a.
Hypothesis K2 : mor (source f) u.
Hypothesis K3 : source u = vertex a. 

Lemma cocone_composable_u_a : cocone_composable u a.
Proof.
uhg; ee. am. wr K1; am. am. 
Qed.

Lemma cocone_pushdown_cocone_compose : 
cocone_pushdown f (cocone_compose u a) = 
cocone_compose (fmor f u) (cocone_pushdown f a).
Proof.
ap cocone_extensionality. 
ap is_cocone_cocone_pushdown. app is_cocone_cocone_compose. 
ap cocone_composable_u_a. 
am. rww cocone_target_cocone_compose.
app is_cocone_cocone_compose. uhg; ee. 
app is_cocone_cocone_pushdown. 
rww cocone_target_cocone_pushdown. app mor_fmor. 
rww source_fmor. rww vertex_cocone_pushdown. 
rww K3. 
rww vertex_cocone_pushdown. 
rww vertex_cocone_compose. 
rww vertex_cocone_compose. rww target_fmor. 
rww cosocle_cocone_pushdown. rww cosocle_cocone_compose.
rww cosocle_cocone_compose. rww cosocle_cocone_pushdown. 
ir. 
rwi cocone_source_cocone_pushdown H. rwi cocone_source_cocone_compose H. 
rw coedge_cocone_pushdown. 
rw coedge_cocone_compose. rw coedge_cocone_compose. 
rw cocone_target_cocone_pushdown. 
rw coedge_cocone_pushdown. 
wr K1. wr comp_fmor. tv. 
am. am.  rw K1. app mor_coedge. 
rww target_coedge. am. am. rww cocone_source_cocone_pushdown. 
uhg; ee. 
app cocone_source_axioms. app ob_is_ob. 
rww cocone_source_cocone_compose. app is_cocone_cocone_compose. 
uhg; ee; try am. wrr K1. 
Qed. 

End cocone_Pushdown_cocone_Compose. 

Section cocone_Pushdown_colimit_to_cocone.
Variables a b f : E.

Hypothesis K : Functor.axioms f.
Hypothesis K0 : is_cocone a.
Hypothesis K1 : is_colimit b.
Hypothesis K2 : cosocle a = cosocle b.
Hypothesis K3 : source f = cocone_target b.
Hypothesis K4 : is_colimit (cocone_pushdown f b).

Lemma cocone_compose_cocone_pushdown_fmor_colimit_to_cocone :
cocone_compose  (fmor f (colimit_to_cocone b a)) 
(cocone_pushdown f b)
= cocone_pushdown f a.
Proof.
assert (lem0 : is_cocone b). 
cp K1. uh H; ee. lu. 
assert (lem1 : a = cocone_compose (colimit_to_cocone b a) b).
rww cocone_compose_colimit_to_cocone. 
transitivity 
(cocone_pushdown f (cocone_compose  (colimit_to_cocone b a) b)).
assert (cocone_pushdown f 
(cocone_compose (colimit_to_cocone b a) b)
= cocone_compose  
(fmor f (colimit_to_cocone b a)) (cocone_pushdown f b)).
rw cocone_pushdown_cocone_compose. reflexivity. 
am. am. am. 
app mor_colimit_to_cocone. 
rww source_colimit_to_cocone. 
rw H. reflexivity. 
assert (cocone_compose (colimit_to_cocone b a) b = a). 
rw cocone_compose_colimit_to_cocone. tv. am. am. 
am. rw H. reflexivity. 
Qed.


Lemma fmor_colimit_to_cocone :
fmor f (colimit_to_cocone b a) = 
colimit_to_cocone (cocone_pushdown f b) (cocone_pushdown f a).
Proof.
cp K4. uh H; ee. uh H; ee. 
assert (is_cocone b).
cp K1. uh H2; ee; lu. 
assert (is_coversal b). cp K1; lu. 
ap H1. 
uhg; ee. app is_cocone_cocone_pushdown. 
rww cocone_target_cocone_pushdown. app mor_fmor. rw K3.
app mor_colimit_to_cocone. 
rww source_fmor. rww vertex_cocone_pushdown. 
rww source_colimit_to_cocone. rw K3; app mor_colimit_to_cocone. 
uhg; ee. app  is_cocone_cocone_pushdown. 
rww cocone_target_cocone_pushdown. 

ap mor_colimit_to_cocone. ap is_cocone_cocone_pushdown. 
am. am. rw K3. uf cocone_target. rww K2. am. 
rww cosocle_cocone_pushdown. rw cosocle_cocone_pushdown. 
rww K2. 
rww cocone_target_cocone_pushdown. 
rw source_colimit_to_cocone. tv. app is_cocone_cocone_pushdown. 
rw K3; uf cocone_target; rww K2. am. 
rww cosocle_cocone_pushdown. rw cosocle_cocone_pushdown. 
rww K2. 
rw cocone_compose_cocone_pushdown_fmor_colimit_to_cocone. 
sy; rw cocone_compose_colimit_to_cocone. tv. app is_cocone_cocone_pushdown.
rw K3; uf cocone_target; rww K2. am. 
rw cosocle_cocone_pushdown. rw cosocle_cocone_pushdown. rww K2. 
Qed.

End cocone_Pushdown_colimit_to_cocone.

Section colimit_Preservation_Invariance.
Variables a b f : E. 

Hypothesis K : Functor.axioms f.
Hypothesis K0 : is_colimit a.
Hypothesis K1 : is_colimit b.
Hypothesis K2 : cosocle a = cosocle b.
Hypothesis K3 : source f = cocone_target b.
Hypothesis K4 : is_colimit (cocone_pushdown f b).


Lemma invertible_colimit_to_cocone_a_b:
invertible (source f) (colimit_to_cocone a b).
Proof.
app invertible_colimit_to_cocone. rw K3; uf cocone_target; rw K2. 
tv.  
Qed.

Lemma invertible_fmor_ctl :
invertible (target f) (fmor f (colimit_to_cocone b a)).
Proof.
app invertible_fmor. 
app invertible_colimit_to_cocone. sy; am. sy; am. 
Qed.



Lemma colimit_preservation_invariance : 
is_colimit (cocone_pushdown f a).
Proof.
ir. 
ap (colimit_to_cocone_invertible_is_colimit 
(a:= (cocone_pushdown f a)) (b:=(cocone_pushdown f b))).
am. app is_cocone_cocone_pushdown. cp K0; lu. 
rw K3; uf cocone_target; rww K2. 
rw cosocle_cocone_pushdown. rw cosocle_cocone_pushdown.
rww K2. 
wr fmor_colimit_to_cocone. 
rw cocone_target_cocone_pushdown. ap invertible_fmor_ctl. 
am. cp K0; lu. am. am. 
am. am. 
Qed.

End colimit_Preservation_Invariance.


Lemma cocone_pushdown_are_inverse_invol : forall a f g,
is_cocone a -> are_finverse f g -> 
source f = cocone_target a ->
cocone_pushdown g (cocone_pushdown f a) = a.
Proof.
ir. ap cocone_extensionality.
ap is_cocone_cocone_pushdown. ap is_cocone_cocone_pushdown. 
am. uh H0; ee; am. am. 
uh H0; ee; am. rw cocone_target_cocone_pushdown. 
uh H0; ee; am. am. 
rw vertex_cocone_pushdown. rw vertex_cocone_pushdown. 
wr fob_fcompose. uh H0; ee. rw H6. 
rw fob_fidentity. tv. rw H1. ap ob_vertex. am. 
uh H0; ee; am. uh H0; ee; am. uh H0; ee; am. 
rw H1. ap ob_vertex. am. 
rw cosocle_cocone_pushdown. rw cosocle_cocone_pushdown. 
wr fcompose_assoc. uh H0; ee. 
rw H6. 
rw left_fidentity. tv. 
ap cosocle_axioms. am. am. uh H0; ee; am. 
uh H0; ee; am. ap cosocle_axioms. am. 
uh H0; ee; am. am. 

ir. 
rwi cocone_source_cocone_pushdown H2. 
rwi cocone_source_cocone_pushdown H2. 
uh H0; ee. 
rw coedge_cocone_pushdown. 
rw coedge_cocone_pushdown. 
wr fmor_fcompose. rw H7. 
rw fmor_fidentity. tv. 
rw H1. ap mor_coedge. am. am. am. 
am. am. rw H1. ap mor_coedge. am. am. am. am.
rw cocone_source_cocone_pushdown. am. 
ap is_cocone_cocone_pushdown. am. am. am. 
Qed.

Lemma are_finverse_preserves_colimits : forall a f g,
is_colimit a -> are_finverse f g ->
source f = cocone_target a -> 
is_colimit (cocone_pushdown f a).
Proof.
ir. 
uh H0; ee. 
assert (is_cocone a). 
uh H; ee. uh H; ee. am. 
assert (is_cocone (cocone_pushdown f a)). 
ap is_cocone_cocone_pushdown. am. 
am. am. 

assert (lem1 : forall x, ob (source f) x ->
fob g (fob f x) = x).
ir. wr fob_fcompose. rw H6. 
rw fob_fidentity. tv. am. am. am. am. am. 

assert (lem2 : forall x, ob (target f) x ->
fob f (fob g x) = x).
ir. wr fob_fcompose. rw H5.
rw fob_fidentity. tv. rww H4. am. am. am. rww H4. 


assert (lem3 : forall u, mor (source f) u ->
fmor g (fmor f u) = u).
ir. wr fmor_fcompose. rw H6. rw fmor_fidentity. 
tv. am. am. am. am. am. 


assert (lem4 : forall u, mor (target f) u ->
fmor f (fmor g u) = u).
ir. wr fmor_fcompose. rw H5. rw fmor_fidentity. 
tv. rww H4.  am. am. am. rww H4. 


uhg; ee. 

(**** couni proof *****) 

uhg; ee. am. 
ir. 
uh H9; ee. 
uh H10; ee. 
rwi cocone_target_cocone_pushdown H12. 
rwi cocone_target_cocone_pushdown H14. 

assert (cocone_pushdown g (cocone_pushdown f a) = a). 
rw cocone_pushdown_are_inverse_invol. tv. am. 
uhg; ee; am. am.  



assert (cocone_compose (fmor g u) a =
cocone_compose (fmor g v) a).
wr H16. 
wr cocone_pushdown_cocone_compose. 
sy; wr cocone_pushdown_cocone_compose. 
rw H11. reflexivity. 
am. am. rw cocone_target_cocone_pushdown. am.  


rww H4. 
am. ap is_cocone_cocone_pushdown. am. am. am. am. 
rw cocone_target_cocone_pushdown. am. rw H4. am. 
am. 
uh H; ee. uh H; ee. 
assert (fmor g u = fmor g v). 
ap H19. 
uhg; ee. am. wr H1. rw H3. ap mor_fmor. 
am. rww H4. 
rw source_fmor. 
rw H13. rw vertex_cocone_pushdown. 
rw lem1. tv. rw H1. ap ob_vertex. am. 
am. rww H4. 
uhg; ee. am. wr H1. rw H3. ap mor_fmor. 
am. rw H4. am. 
rw source_fmor. rw H15. 
rw vertex_cocone_pushdown. rw lem1. tv. 
rw H1. ap ob_vertex. am. am. 
rww H4. am. 
wr lem4. wr H20. rw lem4. tv. 
am. am. 

(***** coversal proof ****)

uhg; ee. am. ir. cp H. uh H11. ee. 
uh H12. ee. 
util (H13 (cocone_pushdown g b)). 
ap is_cocone_cocone_pushdown. am. am. 
uf cocone_target. rw H10. 
rw cosocle_cocone_pushdown. rw target_fcompose. am. 
rw cosocle_cocone_pushdown. rw H10. 
rw cosocle_cocone_pushdown. 
wr fcompose_assoc. rw H6. 
rw left_fidentity. tv. app cosocle_axioms. 
exact H1. am. am. 
app cosocle_axioms. am. exact H1. 

nin H14. ee. uh H14; ee. 
sh (fmor f x). ee. 
uhg; ee. 
ap is_cocone_cocone_pushdown. am. am. 
am. 
rw cocone_target_cocone_pushdown. ap mor_fmor. 
am. rw H1. am. 
rw vertex_cocone_pushdown. 
rw source_fmor. rww H17. am. rww H1. 
wr cocone_pushdown_cocone_compose. rw H15. 
rw cocone_pushdown_are_inverse_invol. tv. 
am. uhg; ee; am. uf cocone_target. 
rw H10. rw cosocle_cocone_pushdown. 
rw target_fcompose. am. am. am. 
am. rww H1. am. 
Qed.

Lemma has_colimits_over_finverse_invariance : 
forall a b c, 
Category.axioms a -> Category.axioms b -> Category.axioms c ->
has_colimits_over c a ->
(exists f, (exists g, 
(are_finverse f g & source f = a & target f = b))) ->
has_colimits_over c b.
Proof.
ir. 
nin H3. nin H3. ee. 
uhg; ee. ir. uhg; ee. 
set (k:= fcompose x0 f). 
uh H3; ee. 
assert (Functor.axioms k). 
uf k. ap fcompose_axioms. 
am. am. rw H11. rw H5. sy; am. 
assert (source k = c). 
uf k. rw source_fcompose. am. 
assert (target k = a). 
uf k. rw target_fcompose. wr H10. am. 
assert (fcompose x k = f).
uf k. wr fcompose_assoc. rw H12. 
rw left_fidentity. tv. am. rw H11. rw H5. 
sy; am. am. am. am. am. rw H11. 
rw H5. sy; am. 

uh H2; ee. util (H2 k). am. am. am. 
uh H18. nin H18. uh H18. ee. 
sh (cocone_pushdown x x1). 
uhg; ee. 
apply are_finverse_preserves_colimits with x0. am. 
uhg; ee; am. uf cocone_target. rw H19. 
rw H16. am. 
rw cosocle_cocone_pushdown. rw H19. am. 
Qed.

End Colimit.

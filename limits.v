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
Require Export nat_trans.

Ltac lw := autorewrite with lw; try tv; try am. 
Ltac lr := autorewrite with lw.

Module Limit.
Export Nat_Trans.

Definition Vertex := R (v_ (r_ (x_ DOT))).

Definition Edge := R (e_ (d_ (g_ DOT))).

Definition cone_create v e := 
denote Vertex v (
denote Edge e stop). 


 

Definition vertex c := V Vertex c.
Definition edge_nt c := V Edge c.
Definition edge c x := ntrans (edge_nt c) x.
Definition socle c := target (edge_nt c).
Definition cone_source c := source (socle c).
Definition cone_target c := target (socle c).

Definition cone_like c := cone_create (vertex c) (edge_nt c) = c. 



Lemma vertex_cone_create : forall v e, vertex (cone_create v e) = v.
Proof.
ir.
uf cone_create. uf vertex. drw. 
Qed.

Lemma edge_nt_cone_create : forall v e, edge_nt (cone_create v e) = e.
Proof.
ir. uf cone_create. uf edge_nt. drw. 
Qed. 

Lemma cone_like_cone_create : forall v e,
cone_like (cone_create v e). 
Proof. ir. uf cone_like. 
rw vertex_cone_create. rww edge_nt_cone_create. 
Qed. 

Definition is_cone c :=
cone_like c &
Nat_Trans.axioms (edge_nt c) &
ob (cone_target c) (vertex c) &
source (edge_nt c) = 
constant_functor (cone_source c) (cone_target c) (vertex c).

Lemma cone_extensionality : forall c d,
is_cone c -> is_cone d -> vertex c = vertex d ->
socle c = socle d -> 
(forall x, ob (cone_source c) x -> edge c x = edge d x) ->
c = d.
Proof.
ir. 
assert (cone_source c = cone_source d).
uf cone_source. rww H2. 
assert (cone_target c = cone_target d).
uf cone_target; rww H2. 
uh H; uh H0; ee. uh H; uh H0. wr H; wr H0. 
rw H1. ap uneq.  
app Nat_Trans.axioms_extensionality. 
rw H11. rw H8. 
rw H4; rw H5; rw H1. reflexivity. 
ir. util (H3 x). uf cone_source. uf socle. 
rw Nat_Trans.source_target. am. am. am. 
Qed.

Definition cone_create2 f v e :=
cone_create v (Nat_Trans.create 
(constant_functor (source f) (target f) v) f e).

Lemma is_cone_cone_create2 : forall f v e,
Functor.axioms f->
ob (target f) v->
(forall x, ob (source f) x -> mor (target f) (e x)) ->
(forall x, ob (source f) x -> source (e x) = v) ->
(forall x, ob (source f) x -> target (e x) = (fob f x)) ->
(forall u, mor (source f) u -> 
comp (target f) (fmor f u) (e (source u)) = e (target u)) ->
is_cone (cone_create2 f v e).
Proof.
ir. uf cone_create2. 
uhg; ee. ap cone_like_cone_create. 
rw edge_nt_cone_create. 
app Nat_Trans.create_axioms. uhg; ee. 
app constant_functor_axioms. uh H; ee; am. uh H; ee; am. am. 
rww source_constant_functor. 
rww target_constant_functor. 
ir. rwi source_constant_functor H5. au. 
ir. rwi source_constant_functor H5. 
rw fob_constant_functor. au. am. am. 
ir. rwi source_constant_functor H5. au. 
ir. rwi source_constant_functor H5. 
rww fmor_constant_functor.
rww H4. 
rww right_id. ap H1. rww  ob_target. 
rw H2. tv. rww ob_target. 
rw vertex_cone_create. 
uf cone_target. uf socle. 
rw edge_nt_cone_create. 
rw target_create. am. 
rw edge_nt_cone_create. rw source_create. 
rw vertex_cone_create. uf cone_source; 
uf cone_target; uf socle; rw edge_nt_cone_create.
rw target_create. tv. 
Qed.



Lemma otarget_edge_nt : forall c,
otarget (edge_nt c) = cone_target c.
Proof.
ir. tv. 
Qed.

Lemma osource_edge_nt : forall c,
is_cone c -> 
osource (edge_nt c) = cone_source c.
Proof.
ir. uf cone_source. uf socle. 
rw Nat_Trans.source_target. tv. lu. 
Qed. 

Definition cone_composable c u :=
is_cone c &
mor (cone_target c) u & 
target u = vertex c.

Lemma cone_composable_rw : forall c u,
is_cone c -> mor (cone_target c) u -> target u = vertex c ->
cone_composable c u = True.
Proof.
ir. uf cone_composable. 
app iff_eq; ir; try tv. xd. 
Qed.

Definition cone_compose c u :=
cone_create (source u) (vcompose (edge_nt c) 
(constant_nt (cone_source c) (cone_target c) u)).

Lemma vertex_cone_compose : forall c u ,
vertex (cone_compose c u) = source u.
Proof.
ir. uf cone_compose. rw vertex_cone_create. tv. 
Qed.

Lemma edge_nt_cone_compose : forall c u,
edge_nt (cone_compose c u) = (vcompose (edge_nt c)
(constant_nt (cone_source c) (cone_target c) u)).
Proof. ir. 
uf cone_compose. rw edge_nt_cone_create. tv. 
Qed.

Lemma edge_cone_compose : forall c u x,
ob (cone_source c) x -> cone_composable c u ->
edge (cone_compose c u) x = comp (cone_target c) (edge c x) u.
Proof.
ir.
uf edge. rw edge_nt_cone_compose. 
rw ntrans_vcompose. 
rw otarget_edge_nt. ap uneq. 
rw ntrans_constant_nt. tv. am. 
rw osource_constant_nt. am. 
Qed. 

Lemma socle_cone_compose : forall c u,
socle (cone_compose c u) = socle c.
Proof.
ir. uf socle. rw edge_nt_cone_compose. 
rw target_vcompose. tv. 
Qed.

Lemma cone_target_cone_compose : forall c u,
cone_target (cone_compose c u) = 
cone_target c.
Proof.
ir. uf cone_target. rw socle_cone_compose. tv. 
Qed.

Lemma cone_source_cone_compose : forall c u,
cone_source (cone_compose c u) = 
cone_source c.
Proof.
ir. uf cone_source. rw socle_cone_compose. tv. 
Qed.

Lemma mor_edge : forall c x,
ob (cone_source c) x -> is_cone c ->
mor (cone_target c) (edge c x).
Proof.
ir. uf edge. ap mor_ntrans. 
lu. rww osource_edge_nt. rww otarget_edge_nt. 
Qed. 

Lemma source_edge_nt : forall c,
is_cone c -> source (edge_nt c) =
constant_functor (cone_source c) (cone_target c) (vertex c).
Proof.
ir. uh H; ee. rw H2. tv. 
Qed.

Lemma ob_vertex : forall c,
is_cone c -> ob (cone_target c) (vertex c).
Proof.
ir. uh H; ee. am. 
Qed. 

Lemma source_edge : forall c x,
ob (cone_source c) x -> is_cone c ->
source (edge c x) = vertex c.
Proof.
ir. uf edge. rw source_ntrans. 
rw source_edge_nt. 
rw fob_constant_functor. tv. am. 
ap ob_vertex. am. am. lu. 
rww osource_edge_nt. 
Qed.

Lemma target_edge_nt : forall c,
target (edge_nt c) = socle c. 
Proof.
ir. tv. 
Qed. 

Lemma target_edge : forall c x,
ob (cone_source c) x -> is_cone c ->
target (edge c x) = fob (socle c) x.
Proof.
ir. uf edge. 
rw target_ntrans. tv. uh H0; ee. am. 
ufi cone_source H. ufi socle H. 
rwi source_target H. am. 
uh H0; ee; am. 
Qed.

Lemma commutativity : forall c u,
mor (cone_source c) u -> is_cone c ->
comp (cone_target c) (fmor (socle c) u) (edge c (source u)) =
edge c (target u).
Proof.
ir. 
uh H0; ee. uf edge. 
assert (cone_target c = otarget (edge_nt c)). 
rww otarget_edge_nt. 
assert (socle c = target (edge_nt c)). 
rww target_edge_nt. 
assert (lem1: forall y, ntrans (edge_nt c) y = edge c y). 
ir. tv. 
rw H4; rw H5. 
wr carre. 
rw source_edge_nt. 
rw fmor_constant_functor. rw right_id. tv. 
wr H4; am. wr H4. change (mor (cone_target c) (edge c (target u))).
app mor_edge. rww ob_target. uhg; ee; am. 
rw lem1. rww source_edge. rww ob_target. 
uhg; ee; am. rww otarget_edge_nt. am. 
uhg; ee; am. am. rww osource_edge_nt. uhg; ee; am. 
Qed. 

Lemma cone_source_axioms : forall c, is_cone c ->
Category.axioms (cone_source c).
Proof.
ir. cp H. uh H; ee. uh H1; ee. 
rwi osource_edge_nt H4. exact H4. am. 
Qed.

Lemma cone_target_axioms : forall c, is_cone c ->
Category.axioms (cone_target c).
Proof.
ir. cp H. uh H; ee. uh H1; ee. 
rwi otarget_edge_nt H5. exact H5. 
Qed.

Lemma socle_axioms : forall c, is_cone c ->
Functor.axioms (socle c).
Proof.
ir. uh H; ee. uh H0; ee. 
exact H6. 
Qed.


Hint Rewrite vertex_cone_compose edge_nt_cone_compose 
cone_composable_rw edge_cone_compose 
socle_cone_compose
cone_target_cone_compose
cone_source_cone_compose
: lw.

Lemma is_cone_cone_compose : forall c u,
cone_composable c u -> 
is_cone (cone_compose c u) = True.
Proof.
ir. ap iff_eq; ir; try tv. 
uhg; ee. uf cone_like. uf cone_compose. 
rw vertex_cone_create. rw edge_nt_cone_create. tv. 
rw edge_nt_cone_compose. 
rww vcompose_axioms. lu. 
ap constant_nt_axioms. 
ap cone_source_axioms. lu. 
ap cone_target_axioms. lu. lu. 
rw target_constant_nt. uh H; ee. 
uh H; ee. rw H2; am. 
rw cone_target_cone_compose. rw vertex_cone_compose. 
uh H; ee. rww ob_source. 
rw edge_nt_cone_compose. 
rw source_vcompose. rw source_constant_nt. 
rw cone_source_cone_compose. rw cone_target_cone_compose. 
rw vertex_cone_compose. tv. 
Qed.

Lemma cone_compose_cone_compose : forall a u v,
cone_composable a u -> composable (cone_target a) u v ->
cone_compose (cone_compose a u) v =
cone_compose a (comp (cone_target a) u v).
Proof.
ir. 
rwi composable_facts_rw H0. 
apply cone_extensionality. 
rww is_cone_cone_compose. uf cone_composable; ee. 
rww is_cone_cone_compose. rw cone_target_cone_compose. 
lu. 
rw vertex_cone_compose. sy; lu. 
rww is_cone_cone_compose. uhg; ee. lu. 
rww mor_comp. lu. lu. lu. 
rw target_comp. lu. lu. lu. lu. 
rw vertex_cone_compose. rw vertex_cone_compose. 
rw source_comp. tv. lu. lu. lu. 
rw socle_cone_compose. rw socle_cone_compose.
rw socle_cone_compose. tv. 
ir. rw edge_cone_compose. rw cone_target_cone_compose. 
rw edge_cone_compose. rw edge_cone_compose. 
rw assoc. tv. 
ap mor_edge. rwi cone_source_cone_compose H1. 
rwi cone_source_cone_compose H1. am. lu. 
uh H; ee. am. uh H0; ee; am. 
rw source_edge. sy; lu. 
rwi cone_source_cone_compose H1. 
rwi cone_source_cone_compose H1. 
am. lu. lu. tv. 
rwi cone_source_cone_compose H1. 
rwi cone_source_cone_compose H1. 
am. 
uhg; ee. lu. rww mor_comp. 
uh H0; ee; am. uh H0; ee; am.  lu. rw target_comp. 
lu. uh H0; ee; am. uh H0; ee; am.  lu. 
rwi cone_source_cone_compose H1. 
rwi cone_source_cone_compose H1. 
am. am. rw cone_source_cone_compose. 
rwi cone_source_cone_compose H1. 
rwi cone_source_cone_compose H1. am. 
uhg; ee. rww is_cone_cone_compose. 
rw cone_target_cone_compose. uh H0; ee; am. 
rw vertex_cone_compose. sy; lu. 
Qed. 

Definition is_uni a :=
is_cone a & 
(forall u v, cone_composable a u -> cone_composable a v ->
cone_compose a u = cone_compose a v -> u = v).

Definition is_versal a :=
is_cone a &
(forall b, is_cone b -> socle b = socle a -> 
(exists u, (cone_composable a u & cone_compose a u = b))).

Definition is_limit a :=
is_uni a & is_versal a.

Lemma is_limit_is_versal : forall a,
is_limit a -> is_versal a.
Proof. ir. lu. Qed.

Lemma is_limit_is_uni : forall a,
is_limit a -> is_uni a.
Proof. ir. lu. Qed. 

Lemma is_limit_is_cone : forall a,
is_limit a -> is_cone a.
Proof.
ir. lu. 
Qed.

Definition is_limit_of f a :=
is_limit a & socle a = f. 

Definition has_limit f :=
exists a, is_limit_of f a.

Definition has_limits_over c b :=
(forall f, 
Functor.axioms f -> source f = c -> target f = b ->
has_limit f).


Definition limit f :=
choose (is_limit_of f).

Lemma if_has_limit : forall f,
has_limit f -> is_limit_of f (limit f).
Proof.
ir. uh H. 
exact (choose_pr H). 
Qed. 

Lemma is_limit_limit : forall f,
has_limit f -> is_limit (limit f).
Proof.
ir. cp (if_has_limit H). lu. 
Qed. 

Lemma socle_limit : forall f,
has_limit f -> socle (limit f) = f.
Proof.
ir. cp (if_has_limit H). lu. 
Qed. 

Definition cone_to_limit a b :=
choose (fun u => (cone_composable b u & cone_compose b u = a)).

Lemma cone_to_limit_pr : forall a b,
is_cone a -> is_limit b -> socle a = socle b ->
(cone_composable b (cone_to_limit a b) 
& cone_compose b (cone_to_limit a b) = a).
Proof.
ir. uh H0; ee. uh H2; ee. util (H3 a). am. am. 
cp (choose_pr H4). cbv beta in H5. ee. 
am. uh H2; ee. 
util (H3 a). am. am. 
cp (choose_pr H4). cbv beta in H5. ee. 
am. 
Qed.

Lemma mor_cone_to_limit : forall a b y,
is_cone a -> is_limit b -> socle a = socle b ->
y = cone_target b ->
mor y (cone_to_limit a b). 
Proof.
ir. cp (cone_to_limit_pr H H0 H1). 
ee. uh H3; ee. rw H2; am. 
Qed. 

Lemma source_cone_to_limit : forall a b,
is_cone a -> is_limit b -> socle a = socle b ->
source (cone_to_limit a b) = vertex a.
Proof.
ir. cp (cone_to_limit_pr H H0 H1). 
ee. transitivity (vertex (cone_compose b (cone_to_limit a b))).
rw vertex_cone_compose. tv. 
rw H3. tv. 
Qed.

Lemma target_cone_to_limit : forall a b,
is_cone a -> is_limit b -> socle a = socle b ->
target (cone_to_limit a b) = vertex b.
Proof.
ir. cp (cone_to_limit_pr H H0 H1). 
ee. uh H2; ee. am. 
Qed.

Lemma cone_compose_cone_to_limit : forall a b,
is_cone a -> is_limit b ->  socle a = socle b ->
cone_compose b (cone_to_limit a b) = a.
Proof.
ir. cp (cone_to_limit_pr H H0 H1). 
ee. am. 
Qed. 

Lemma cone_composable_cone_to_limit : forall a b,
is_cone a -> is_limit b -> socle a = socle b -> 
cone_composable b (cone_to_limit a b) = True. 
Proof.
ir. 
cp (cone_to_limit_pr H H0 H1). 
ee. app iff_eq; ir; try am. 
Qed. 

Lemma cone_to_limit_cone_compose1 : forall a u, 
is_limit a -> cone_composable a u ->
cone_to_limit (cone_compose a u) a = u. 
Proof.
ir. 
assert (lem1 : is_limit a). am. 
uh H; ee. uh H; ee. ap H2. 
uhg; ee. am. ap mor_cone_to_limit.
rww is_cone_cone_compose. 
am.  rw socle_cone_compose. tv. tv. 
rw target_cone_to_limit. tv. rww is_cone_cone_compose.
am.  rw socle_cone_compose. tv. am. 
rw cone_compose_cone_to_limit. tv. 
rww is_cone_cone_compose. am. rww socle_cone_compose.
Qed. 

Lemma cone_to_limit_cone_compose : forall a b u,
is_limit b -> cone_composable a u -> 
socle a = socle b ->
cone_to_limit (cone_compose a u) b = 
comp (cone_target b) (cone_to_limit a b) u.
Proof.
ir. set (k:= comp (cone_target b) (cone_to_limit a b) u).
assert (cone_target a = cone_target b). 
uf cone_target. rww H1. 
assert (lem1 : is_cone a). 
lu. 
transitivity (cone_to_limit (cone_compose b k) b).
uf k. wr cone_compose_cone_compose. 
rw cone_compose_cone_to_limit. tv. lu. 
am. am. 
rww cone_composable_cone_to_limit. 
app show_composable. app mor_cone_to_limit. 
wr H2. lu. 
rww source_cone_to_limit. sy; lu.  
rww cone_to_limit_cone_compose1. 
uf k. uhg; ee. uh H; ee. uh H; ee; am. 
rww mor_comp. app mor_cone_to_limit. 
wr H2. lu. rww source_cone_to_limit. sy; lu. 
rw target_comp. 
rww target_cone_to_limit. 
app mor_cone_to_limit. 
wr H2; lu. 
rww source_cone_to_limit. sy; lu. 
Qed.


Definition cone_transform u c :=
cone_create (vertex c) (vcompose u (edge_nt c)).

Lemma vertex_cone_transform : forall u c,
vertex (cone_transform u c) = vertex c.
Proof.
ir. uf cone_transform. rww vertex_cone_create. 
Qed.

Lemma edge_nt_cone_transform : forall u c,
edge_nt (cone_transform u c) = vcompose u (edge_nt c).
Proof.
ir. uf cone_transform. rww edge_nt_cone_create. 
Qed.

Lemma socle_cone_transform : forall u c,
socle (cone_transform u c) = target u.
Proof.
ir. uf socle. 
rww edge_nt_cone_transform. rww target_vcompose. 
Qed.

Definition cone_transformable u c :=
is_cone c &
Nat_Trans.axioms u &
source u = socle c.

Lemma cone_source_cone_transform : forall u c,
cone_transformable u c -> 
cone_source (cone_transform u c) = cone_source c.
Proof.
ir. uf cone_source. 
rw socle_cone_transform. 
uh H; ee. rww source_target. uf osource; rww H1. 
Qed.

Lemma cone_target_cone_transform : forall u c,
cone_transformable u c -> 
cone_target (cone_transform u c) = cone_target c.
Proof.
ir. uf cone_target. 
rww socle_cone_transform. 
uh H; ee. wr H1. rww target_source. 
Qed.




Lemma edge_cone_transform : forall u c x,
ob (osource u) x -> cone_transformable u c -> 
edge (cone_transform u c) x =
comp (cone_target c) (ntrans u x) (edge c x).
Proof.
ir. uf edge. 
rw edge_nt_cone_transform. rw ntrans_vcompose. 
uh H0; ee. wr target_source. rw H2. tv. am. 
uh H0. ee. rw osource_edge_nt. uf cone_source. 
wr H2. am. am. 
Qed.

Lemma is_cone_cone_transform : forall u c,
cone_transformable u c -> is_cone (cone_transform u c).
Proof.
ir. uhg; ee. 
uf cone_transform. app cone_like_cone_create. 
rw edge_nt_cone_transform. rww vcompose_axioms. 
lu. uh H; ee. uh H; ee. am. 
uh H; ee. am. 
rw vertex_cone_transform. rww cone_target_cone_transform.
uh H; ee. uh H; ee. am. 
rw edge_nt_cone_transform. 
rw source_vcompose. rw source_edge_nt. 
rw cone_source_cone_transform. 
rw cone_target_cone_transform. rww vertex_cone_transform.
am. am. lu. 
Qed.

Definition cone_pushdown f c :=
cone_create (fob f (vertex c)) (htrans_left f (edge_nt c)).

Lemma vertex_cone_pushdown : forall f c,
vertex (cone_pushdown f c) = fob f (vertex c).
Proof.
ir. uf cone_pushdown. rww vertex_cone_create. 
Qed.

Lemma edge_nt_cone_pushdown : forall f c,
edge_nt (cone_pushdown f c) = htrans_left f (edge_nt c).
Proof.
ir. uf cone_pushdown. rww edge_nt_cone_create. 
Qed.

Lemma socle_cone_pushdown : forall f c,
socle (cone_pushdown f c) = fcompose f (socle c).
Proof.
ir. uf socle. rw edge_nt_cone_pushdown. 
rw target_htrans_left. tv.  
Qed.

Lemma cone_source_cone_pushdown : forall f c,
cone_source (cone_pushdown f c) = cone_source c.
Proof.
ir. uf cone_source. rw socle_cone_pushdown.
rw source_fcompose. tv. 
Qed.

Lemma cone_target_cone_pushdown : forall f c,
cone_target (cone_pushdown f c) = target f.
Proof.
ir. uf cone_target. rw socle_cone_pushdown.
rww target_fcompose. 
Qed.

Lemma edge_cone_pushdown : forall f c x,
ob (cone_source c) x -> is_cone c ->
edge (cone_pushdown f c) x = fmor f (edge c x).
Proof.
ir. uf edge. 
rw edge_nt_cone_pushdown. rw ntrans_htrans_left. 
tv. rww osource_edge_nt. 
Qed. 

Lemma is_cone_cone_pushdown : forall f c,
is_cone c -> Functor.axioms f -> source f = cone_target c ->
is_cone (cone_pushdown f c).
Proof.
ir. uhg; ee. uf cone_pushdown. 
ap cone_like_cone_create. 
rw edge_nt_cone_pushdown. app htrans_left_axioms. 
uh H; ee. am. rw cone_target_cone_pushdown. 
rw vertex_cone_pushdown.
app ob_fob. rw H1. uh H; ee; am. 
rw edge_nt_cone_pushdown. rw source_htrans_left. 
rw source_edge_nt. 
rw fcompose_right_constant_functor. 
rw cone_source_cone_pushdown. 
rw cone_target_cone_pushdown. 
rw vertex_cone_pushdown. tv. am. am. 
app cone_source_axioms. 
app ob_vertex. am. 
Qed. 

Lemma cone_pushdown_cone_pushdown : forall f g a,
is_cone a -> Functor.axioms f -> Functor.axioms g ->
source g = cone_target a -> source f = target g ->
cone_pushdown f (cone_pushdown g a) =
cone_pushdown (fcompose f g) a.
Proof.
ir. 
ap cone_extensionality. 
ap is_cone_cone_pushdown. ap is_cone_cone_pushdown. 
am. am. am. am. 
rw cone_target_cone_pushdown. am. 
ap is_cone_cone_pushdown. am. 
ap fcompose_axioms. am. 
am. am. rw source_fcompose. am. 
rw vertex_cone_pushdown. 
rw vertex_cone_pushdown. 
rw vertex_cone_pushdown. 
rw fob_fcompose. tv. am. 
am. am. rw H2. ap ob_vertex. 
am. 
rww socle_cone_pushdown. rww socle_cone_pushdown. 
sy; rw socle_cone_pushdown. 
rw fcompose_assoc. tv. am. am. 
app socle_axioms. am. am. 

ir. rwi cone_source_cone_pushdown H4. 
rwi cone_source_cone_pushdown H4. 
rw edge_cone_pushdown. 
 rw edge_cone_pushdown. 
rw edge_cone_pushdown. 
rw fmor_fcompose. tv. am. am. am. 
rw H2. ap mor_edge. am. am. 
am. am. am. am. rw cone_source_cone_pushdown. am. 
app is_cone_cone_pushdown.
Qed. 

Definition cone_pullback f c := 
cone_create (vertex c) (htrans_right (edge_nt c) f).

Lemma vertex_cone_pullback : forall f c,
vertex (cone_pullback f c) = vertex c.
Proof.
ir. uf cone_pullback. rww vertex_cone_create.
Qed.

Lemma edge_nt_cone_pullback : forall f c,
edge_nt (cone_pullback f c) = htrans_right (edge_nt c) f.
Proof.
ir. uf cone_pullback. rww edge_nt_cone_create. 
Qed.

Lemma socle_cone_pullback : forall f c,
socle (cone_pullback f c) = fcompose (socle c) f.
Proof.
ir. uf socle. rw edge_nt_cone_pullback. 
rw target_htrans_right. tv.  
Qed.

Lemma cone_source_cone_pullback : forall f c,
cone_source (cone_pullback f c) = source f.
Proof.
ir. uf cone_source. rw socle_cone_pullback.
rw source_fcompose. tv. 
Qed.

Lemma cone_target_cone_pullback : forall f c,
cone_target (cone_pullback f c) = cone_target c.
Proof.
ir. uf cone_target. rw socle_cone_pullback.
rww target_fcompose. 
Qed.

Lemma edge_cone_pullback : forall f c x,
ob (source f) x -> 
edge (cone_pullback f c) x = edge c (fob f x).
Proof.
ir. uf edge. 
rw edge_nt_cone_pullback. rw ntrans_htrans_right. 
tv. am. 
Qed. 



Lemma is_cone_cone_pullback : forall f c,
is_cone c -> Functor.axioms f -> cone_source c = target f ->
is_cone (cone_pullback f c).
Proof.
ir. uhg; ee. uf cone_pullback. 
ap cone_like_cone_create. 
rw edge_nt_cone_pullback. app htrans_right_axioms. 
uh H; ee. am. rww osource_edge_nt. 

rw cone_target_cone_pullback. 
rw vertex_cone_pullback.
app ob_vertex. 
rw edge_nt_cone_pullback. rw source_htrans_right. 
rw source_edge_nt. 
rw fcompose_left_constant_functor. 
rw cone_source_cone_pullback. 
rw cone_target_cone_pullback. 
rw vertex_cone_pullback. tv. am. sy; am. 
app cone_target_axioms. 
app ob_vertex. am. 
Qed. 



Lemma cone_compose_id : forall c, 
is_cone c -> 
cone_compose c (id (cone_target c) (vertex c)) = c.
Proof.
ir. ap cone_extensionality. 
rww is_cone_cone_compose. 
uhg; ee. am. ap mor_id. ap ob_vertex. 
am. rww target_id. app ob_vertex. am. 
rww vertex_cone_compose. rww source_id. 
app ob_vertex. rww socle_cone_compose. 
ir. rwi cone_source_cone_compose H0. 
rww edge_cone_compose. rww right_id. app ob_vertex.
app mor_edge. rww source_edge. 
uhg; ee. am. app mor_id. app ob_vertex. 
rww target_id. app ob_vertex. 
Qed. 

Lemma cone_compose_cone_transform : forall f c u,
is_cone c -> cone_composable c u -> cone_transformable f c ->
cone_compose (cone_transform f c) u =
cone_transform f (cone_compose c u).
Proof.
ir. ap cone_extensionality. 
rww is_cone_cone_compose. 
uhg; ee. app is_cone_cone_transform. 
rww cone_target_cone_transform. lu. 
rww vertex_cone_transform. lu. 
app is_cone_cone_transform. 
uhg; ee. rww is_cone_cone_compose. 
lu. rw socle_cone_compose. lu. 
rw vertex_cone_compose; rww vertex_cone_transform. 
rww vertex_cone_compose. 
rw socle_cone_compose. rww socle_cone_transform.
rww socle_cone_transform. 
ir. 
rwi cone_source_cone_compose H2. 
rwi cone_source_cone_transform H2; try am. 
assert (osource f = cone_source c). 
uf cone_source. uf osource. ap uneq; lu. 
assert (otarget f = cone_target c). 
uf cone_target. wr target_source.  ap uneq. 
uh H1; ee. am. lu. 

rw edge_cone_compose. 
rw edge_cone_transform. rw edge_cone_transform. 
rww cone_target_cone_transform. 
rww cone_target_cone_compose. 
rww edge_cone_compose. rww assoc. 
app mor_ntrans. lu. uh H1; ee. rww H3. 
sy; am. app  mor_edge. uh H0; ee. am. 
rww source_ntrans. rww target_edge. 
uh H1; ee. rww H6. lu. rww H3. 
rww source_edge. sy; lu. rww H3. 
uhg; ee. rww is_cone_cone_compose. lu. 
rww socle_cone_compose. lu. rww H3. am. 
rww cone_source_cone_transform. 
uhg; ee. app is_cone_cone_transform. 
rww cone_target_cone_transform. uh H0; ee; am. 
rww vertex_cone_transform. lu. 
Qed.

Lemma cone_to_limit_id : forall a b,
is_limit a -> a = b -> 
cone_to_limit a b = id (cone_target b) (vertex b).
Proof.
ir. cp H.
uh H1; ee. 
uh H1; ee. ap H3. 
uhg; ee. am. ap mor_cone_to_limit. am. 
wr H0; lu. rw H0; tv. rw H0; tv. 
rw target_cone_to_limit. rw H0; tv. am. 
wr H0; lu. rw H0; tv. 
uhg; ee. am. 
wr H0; ap mor_id. ap ob_vertex. am. 
rw target_id. rw H0; tv. ap ob_vertex. 
wr H0; am. 
wr H0; rw cone_compose_cone_to_limit. 
rw cone_compose_id. tv. am. am. am. tv. 
Qed.

Lemma comp_edge_cone_to_limit : forall r s x b, 
is_limit s -> is_cone r -> socle r = socle s ->
b = cone_target s -> ob (cone_source s) x ->
comp b (edge s x) (cone_to_limit r s) =
edge r x.
Proof.
ir. 
transitivity (edge (cone_compose s (cone_to_limit r s)) x).
rw edge_cone_compose. rww H2. am. 
rww cone_composable_cone_to_limit. 
rw cone_compose_cone_to_limit. tv. 
am. am. am. 
Qed.

Lemma edge_nt_axioms : forall c,
is_cone c -> Nat_Trans.axioms (edge_nt c).
Proof.
ir. lu. Qed.

Lemma cone_transform_vident : forall f c,
f = socle c -> is_cone c ->
cone_transform (vident f) c = c.
Proof.
ir. uf cone_transform.
rw weak_left_vident. lu. app edge_nt_axioms. rww target_edge_nt.  
Qed.



Lemma cone_transform_vcompose : forall u v c,
is_cone c -> cone_transformable v c -> 
Nat_Trans.axioms u -> source u = target v ->
cone_transform (vcompose u v) c =
cone_transform u (cone_transform v c).
Proof.
ir. uh H0; ee. 
uf cone_transform. rw vertex_cone_create. ap uneq. 
rw edge_nt_cone_create. 
rww vcompose_assoc.  app edge_nt_axioms. 
Qed.






(**** stuff about limits and isomorphisms ****)


Lemma comp_cone_to_limit_inversely : forall a b c,
is_limit a -> is_limit b -> socle a = socle b ->
cone_target a = c ->
comp c (cone_to_limit a b) (cone_to_limit b a) =
id c (vertex b).
Proof.
ir. 
assert (cone_target b = c).
uf cone_target. wr H1. am. 
cp H; cp H0.
uh H4; uh H5; ee. 
uh H4; uh H5. ee. 

assert (composable c (cone_to_limit a b) (cone_to_limit b a)).
ap show_composable. app mor_cone_to_limit. 
sy; am. app mor_cone_to_limit. sy; am. sy; am. 
rww source_cone_to_limit. rww target_cone_to_limit. 
sy; am. 

ap H8. 
uhg; ee. am. rw H3. 
rww mor_comp. 
ap mor_cone_to_limit. am. am. am. sy; am. 
app mor_cone_to_limit. sy; am. sy; am. 
rw source_cone_to_limit. 
rww target_cone_to_limit. sy; am. am. am. 
am. 
rw target_comp. rww target_cone_to_limit. 
app mor_cone_to_limit. sy; am. 
app mor_cone_to_limit. sy; am. sy; am. 
rw source_cone_to_limit. 
rww target_cone_to_limit. sy; am. am. am. 
am. 
uhg; ee. am. rw H3. ap mor_id. 
wr H3. ap ob_vertex. am. 
rw target_id. tv. wr H3; app ob_vertex. 
wr H3. wr cone_compose_cone_compose. 
rw cone_compose_cone_to_limit. rw cone_compose_cone_to_limit. 
rw cone_compose_id. tv. am. am. am. sy; am. 
am. am. am. 

uhg; ee. 
am. app mor_cone_to_limit. 
rww target_cone_to_limit. 
rww H3.  
Qed. 


Lemma are_inverse_cone_to_limit : forall a b c,
is_limit a -> is_limit b -> socle a = socle b ->
cone_target a = c ->
are_inverse c (cone_to_limit a b) (cone_to_limit b a).
Proof.
ir. 
assert (cone_target b = c).
uf cone_target. wr H1. am. 
cp H; cp H0.
uh H4; uh H5; ee. 
uh H4; uh H5. ee. 
uhg; ee; try am.  
app mor_cone_to_limit. 
sy; am. 
app mor_cone_to_limit. sy; am. 
sy; am. 
rww source_cone_to_limit. rww target_cone_to_limit. 
sy; am. 
rww target_cone_to_limit. rww source_cone_to_limit.
sy; am. 
rw source_cone_to_limit. 
app comp_cone_to_limit_inversely. 
am. am. sy; am. 
rww comp_cone_to_limit_inversely. 
rww source_cone_to_limit. sy; am. 
Qed.

Lemma invertible_cone_to_limit : forall a b c,
is_limit a -> is_limit b -> socle a = socle b ->
cone_target a = c -> 
invertible c (cone_to_limit a b).
Proof.
ir. 
uhg. sh (cone_to_limit b a). 
app are_inverse_cone_to_limit. 
Qed.

Lemma inverse_cone_to_limit : forall a b c,
is_limit a -> is_limit b -> socle a = socle b ->
cone_target a = c -> 
inverse c (cone_to_limit a b) = cone_to_limit b a.
Proof.
ir. 
cp (are_inverse_cone_to_limit H H0 H1 H2).
app inverse_eq. 
Qed.

Lemma is_limit_cone_compose : forall a u,
is_limit a -> cone_composable a u ->
invertible (cone_target a) u -> 
is_limit (cone_compose a u).
Proof.
ir. 
assert (lem1: is_cone (cone_compose a u)).
rww is_cone_cone_compose. 

uhg; ee. 

(**** uni proof ****)
uhg; ee. am. ir. 
assert (mor (cone_target a) u0).
uh H2; ee. rwi cone_target_cone_compose H5. am. 

assert (mor (cone_target a) v). 
uh H3; ee. rwi cone_target_cone_compose H6; am. 
assert (source u = target u0). sy. 
uh H2; ee. rwi vertex_cone_compose H8; am. 
assert (source u = target v). sy. 
uh H3; ee. rwi vertex_cone_compose H9; am. 
assert (mor (cone_target a) u). 
uh H0; ee. am. 
rwi cone_compose_cone_compose H4. 
rwi cone_compose_cone_compose H4. 
uh H; ee. uh H; ee. 
assert (comp (cone_target a) u u0 = comp (cone_target a) u v).
ap H11. uhg; ee. am. rww mor_comp. 
rww target_comp. 
lu. 
uhg; ee. am. rww mor_comp. 
rw target_comp. lu. 
lu. lu. lu. am. 
transitivity (comp (cone_target a) (inverse (cone_target a) u)
(comp (cone_target a) u u0)). 
wr assoc. 
rw left_inverse. rw left_id. tv. 


rww ob_source. am. sy; am. tv. am. 
ap mor_inverse. 
am. am. am. rw source_inverse. tv. am. am. tv. 
rw H12. wr assoc. 
rw left_inverse. rw left_id. tv. 
rww ob_source. am. sy; am. tv. am. 
app mor_inverse. am. am. 
rww source_inverse. am. tv. am. app show_composable. 
am. app show_composable. 

(*** versal proof ***)
assert (lema: target u = vertex a). lu. 
uhg; ee. am. ir. 
assert (lem0 : socle b = socle a). 
rwi socle_cone_compose H3. am. 
assert (lem2: composable (cone_target a) (inverse (cone_target a) u)
(cone_to_limit b a)).
ap show_composable. app mor_inverse. 
app mor_cone_to_limit. 
rw source_inverse.
rww target_cone_to_limit. lu. 


sh (comp (cone_target a) (inverse (cone_target a) u)
(cone_to_limit b a)).
ee. 
uhg; ee. am. rw cone_target_cone_compose. 
rww mor_comp. 
app mor_inverse. 
app mor_cone_to_limit. 
rww source_inverse. rww target_cone_to_limit. 
rww target_comp. rww target_inverse. 
assert (cone_target a = cone_target (cone_compose a u)).
rww cone_target_cone_compose. 
rww vertex_cone_compose. 
app mor_inverse. app mor_cone_to_limit. 
rww source_inverse. rww target_cone_to_limit. 

assert (mor (cone_target a) u). uh H0; ee; am.  


rw cone_compose_cone_compose. 
wr assoc. rww right_inverse. 
rw left_id. rw cone_compose_cone_to_limit. tv. 
am. am. am. rww ob_target. 
app mor_cone_to_limit. rw target_cone_to_limit. 
sy; am. am. am. am. tv. am.
app mor_inverse. 
app mor_cone_to_limit. 
rww target_inverse. 
rww source_inverse. rww target_cone_to_limit. 
tv. am. ap show_composable. 
am. rww mor_comp. 
app mor_inverse. app mor_cone_to_limit. 
rww source_inverse. rww target_cone_to_limit. 
rww target_comp. rww target_inverse. 
app mor_inverse. app mor_cone_to_limit. 
rww source_inverse. rww target_cone_to_limit. 
Qed. 

Lemma cone_to_limit_invertible_is_limit : forall a b,
is_limit b -> is_cone a -> socle a = socle b ->
invertible (cone_target b) (cone_to_limit a b) -> is_limit a.
Proof.
ir. assert  (a = cone_compose b (cone_to_limit a b)).
rw cone_compose_cone_to_limit. tv. 
am.  am. am. rw H3. 
ap is_limit_cone_compose. am. 
uhg; ee. uh H; ee. uh H; ee; am. 
app mor_cone_to_limit.
rww target_cone_to_limit. lu. 
Qed.

(***** added in september: dotted *****)

Definition dotted a := cone_to_limit a (limit (socle a)).

Lemma source_dotted : forall a, is_cone a ->
has_limit (socle a) -> source (dotted a) = vertex a.
Proof.
ir.
uf dotted. rww source_cone_to_limit. 
app is_limit_limit. 
rww socle_limit. 
Qed. 

Lemma target_dotted : forall a, is_cone a ->
has_limit (socle a) -> target (dotted a) = vertex (limit (socle a)).
Proof.
ir.
uf dotted. rww target_cone_to_limit. 
app is_limit_limit. 
rww socle_limit. 
Qed. 

Lemma mor_dotted : forall a, is_cone a ->
has_limit (socle a) -> mor (cone_target a) (dotted a).
Proof.
ir.
uf dotted. app mor_cone_to_limit. 
app is_limit_limit. 
rww socle_limit. 
uf cone_target. rww socle_limit. 
Qed. 

Lemma cone_target_limit : forall f,
has_limit f -> cone_target (limit f) = target f.
Proof.
ir. uf cone_target. rww socle_limit. 
Qed.

Lemma cone_source_limit : forall f,
has_limit f -> cone_source (limit f) = source f.
Proof.
ir. uf cone_source. rww socle_limit. 
Qed. 

Lemma target_socle : forall a, target (socle a) = cone_target a.
Proof. ir. reflexivity. Qed.

Lemma source_socle : forall a, source (socle a) = cone_source a.
Proof. ir. reflexivity. Qed.


Lemma cone_composable_dotted : forall a, is_cone a ->
has_limit (socle a) -> cone_composable (limit (socle a)) 
(dotted a).
Proof.
ir. uf cone_composable. ee. 
ap is_limit_is_cone. app is_limit_limit. 
rww cone_target_limit. 
rw target_socle. 
app mor_dotted. 
rww target_dotted. 
Qed. 

Lemma cone_compose_dotted : forall a, is_cone a ->
has_limit (socle a) -> cone_compose (limit (socle a)) (dotted a)
= a.
Proof.
ir. uf dotted. 
rww cone_compose_cone_to_limit. 
app is_limit_limit. rww socle_limit. 
Qed. 

Lemma dotted_cone_compose : forall u a,
cone_composable a u -> has_limit (socle a) -> 
dotted (cone_compose a u) = comp (cone_target a) (dotted a) u.
Proof.
ir. uf dotted. 
rw cone_to_limit_cone_compose. 
rw socle_cone_compose. 
rw cone_target_limit. rw target_socle. reflexivity. 
am. app is_limit_limit. rw socle_cone_compose. am. 
am. rw socle_limit. rw socle_cone_compose. tv. 
rww socle_cone_compose. 
Qed.

Lemma cone_to_limit_refl : forall a, is_limit a ->
cone_to_limit a a = id (cone_target a) (vertex a).
Proof.
ir. transitivity
(comp (cone_target a) (cone_to_limit a a) (cone_to_limit a a)).
wr cone_to_limit_cone_compose. 
rw cone_compose_cone_to_limit. tv. lu. am. 
tv. lu. rww cone_composable_cone_to_limit. 
lu. tv. 
rww comp_cone_to_limit_inversely. 
Qed.

Lemma dotted_limit : forall f, Functor.axioms f -> has_limit f ->
dotted (limit f) = id (target f) (vertex (limit f)).
Proof.
ir. uf dotted. 
rww socle_limit. 
rw cone_to_limit_refl. rw cone_target_limit. 
tv. am. app is_limit_limit. 
Qed.

Lemma dotted_unique : forall f u, Functor.axioms f ->
has_limit f -> cone_composable (limit f) u -> 
dotted (cone_compose (limit f) u) = u.
Proof.
ir. rw dotted_cone_compose. 
rw dotted_limit. 
rw cone_target_limit. rw left_id. tv. 
assert (target f = cone_target (limit f)). 
rww cone_target_limit. rw H2. 
app ob_vertex. ap is_limit_is_cone. app is_limit_limit. 
uh H1; ee. rwi cone_target_limit H2. am. am. 
uh H1; ee. am. tv. am. am. am. 
am. rww socle_limit. 
Qed.

Lemma invertible_dotted_is_limit : forall a,
is_cone a -> has_limit (socle a) ->
invertible (cone_target a) (dotted a) -> is_limit a.
Proof.
ir. 
assert (a = cone_compose (limit (socle a)) (dotted a)). 
rww cone_compose_dotted. 
rw H2. app is_limit_cone_compose. 
app is_limit_limit. 
app cone_composable_dotted. 
rw cone_target_limit. rw target_socle. am. am. 
Qed.

Lemma is_limit_invertible_dotted : forall a,
is_limit a -> invertible (cone_target a) (dotted a).
Proof.
ir. uf dotted. 
assert (has_limit (socle a)). 
uhg. sh a. uhg; ee. am. tv. 
ap invertible_cone_to_limit. am. ap is_limit_limit. 
am. 
rww socle_limit. tv. 
Qed.


(**** stuff about functors commuting with limits ***)

Section Commutation_Def.
Variable f a b: E.

Hypothesis cone_a : is_cone a.
Hypothesis limit_b : is_limit b.
Hypothesis fsource_cone_target : source f = cone_target a.
Hypothesis f_functor : Functor.axioms f. 
Hypothesis compose_ntarg : fcompose f (socle a) = socle b.


Definition commutation := 
cone_to_limit (cone_pushdown f a) b.

Lemma source_commutation :  
source commutation = fob f (vertex a).
Proof.
uf commutation. 
rw source_cone_to_limit. 
rww vertex_cone_pushdown. app is_cone_cone_pushdown.
am. rww socle_cone_pushdown. 
Qed.

Lemma target_commutation : 
target commutation  = vertex b.
Proof.
ir. uf commutation. 
rw target_cone_to_limit. tv. app is_cone_cone_pushdown.
am. rww socle_cone_pushdown. 
Qed.

Lemma cone_target_b : cone_target b = target f.
Proof.
uf cone_target. wr compose_ntarg. 
rw target_fcompose. tv. 
Qed. 


Lemma mor_commutation : 
mor (target f) commutation.
Proof.
uf commutation. 
ap mor_cone_to_limit. 
app is_cone_cone_pushdown. am. 
rww socle_cone_pushdown. 
rww cone_target_b. 
Qed.

Lemma cone_composable_commutation : 
cone_composable b commutation.
Proof.
uhg; ee. cp limit_b. 
uh H; ee. lu. 
rw cone_target_b.  

ap mor_commutation. 
rw target_commutation. tv. 
Qed. 

Lemma cone_compose_commutation : 
cone_compose b commutation = cone_pushdown f a.
Proof.
uf commutation. 
rw cone_compose_cone_to_limit. tv. 
app is_cone_cone_pushdown. am. 
rww socle_cone_pushdown. 
Qed.

Lemma invertible_commutation_is_limit_cone_pushdown : 
forall c, target f = c -> 
invertible c commutation = 
is_limit (cone_pushdown f a).
Proof.
ir. wr H. ap iff_eq; ir. 
wr cone_compose_commutation. 
app is_limit_cone_compose. 
ap cone_composable_commutation. 
rww cone_target_b. 

uf commutation. 
ap invertible_cone_to_limit. 
am. am. rww socle_cone_pushdown. 
rww cone_target_cone_pushdown.  
Qed.


End Commutation_Def. 

Section Cone_Pushdown_Cone_Compose.
Variables u a f: E.

Hypothesis K : is_cone a.
Hypothesis K0 : Functor.axioms f.
Hypothesis K1 : source f = cone_target a.
Hypothesis K2 : mor (source f) u.
Hypothesis K3 : target u = vertex a. 

Lemma cone_composable_a_u : cone_composable a u.
Proof.
uhg; ee. am. wr K1; am. am. 
Qed.

Lemma cone_pushdown_cone_compose : 
cone_pushdown f (cone_compose a u) = 
cone_compose (cone_pushdown f a) (fmor f u).
Proof.
ap cone_extensionality. 
ap is_cone_cone_pushdown. rww is_cone_cone_compose. 
ap cone_composable_a_u. 
am. rww cone_target_cone_compose.
rww is_cone_cone_compose. uhg; ee. 
app is_cone_cone_pushdown. 
rww cone_target_cone_pushdown. app mor_fmor. 
rww target_fmor. rww vertex_cone_pushdown. 
rww K3. 
rww vertex_cone_pushdown. 
rww vertex_cone_compose. 
rww vertex_cone_compose. rww source_fmor. 
rww socle_cone_pushdown. rww socle_cone_compose.
rww socle_cone_compose. rww socle_cone_pushdown. 
ir. 
rwi cone_source_cone_pushdown H. rwi cone_source_cone_compose H. 
rw edge_cone_pushdown. 
rw edge_cone_compose. rw edge_cone_compose. 
rw cone_target_cone_pushdown. 
rw edge_cone_pushdown. 
wr K1. wr comp_fmor. tv. 
am. rw K1. app mor_edge. rww K1. 
wrr K1. rww source_edge. sy; am. 
am. am. rww cone_source_cone_pushdown. 
uhg; ee. app is_cone_cone_pushdown. 
rww cone_target_cone_pushdown. 
app mor_fmor. 
rww vertex_cone_pushdown. rww target_fmor. 
rww K3. am. ap cone_composable_a_u. 
rww cone_source_cone_compose. rww is_cone_cone_compose. 
ap cone_composable_a_u. 
Qed. 

End Cone_Pushdown_Cone_Compose. 

Section Cone_Pushdown_Cone_To_Limit.
Variables a b f : E.

Hypothesis K : Functor.axioms f.
Hypothesis K0 : is_cone a.
Hypothesis K1 : is_limit b.
Hypothesis K2 : socle a = socle b.
Hypothesis K3 : source f = cone_target b.
Hypothesis K4 : is_limit (cone_pushdown f b).

Lemma cone_compose_cone_pushdown_fmor_cone_to_limit :
cone_compose (cone_pushdown f b) (fmor f (cone_to_limit a b)) 
= cone_pushdown f a.
Proof.
assert (lem0 : is_cone b). 
cp K1. uh H; ee. lu. 
assert (lem1 : a = cone_compose b (cone_to_limit a b)).
rww cone_compose_cone_to_limit. 
transitivity (cone_pushdown f (cone_compose b (cone_to_limit a b))).
assert (cone_pushdown f (cone_compose b (cone_to_limit a b))
= cone_compose (cone_pushdown f b) (fmor f (cone_to_limit a b))).
rw cone_pushdown_cone_compose. reflexivity. 
am. am. am. 
app mor_cone_to_limit. 
rww target_cone_to_limit. 
rw H. reflexivity. 
assert (cone_compose b (cone_to_limit a b) = a). 
rw cone_compose_cone_to_limit. tv. am. am. 
am. rw H. reflexivity. 
Qed.


Lemma fmor_cone_to_limit :
fmor f (cone_to_limit a b) = 
cone_to_limit (cone_pushdown f a) (cone_pushdown f b).
Proof.
cp K4. uh H; ee. uh H; ee. 
assert (is_cone b).
cp K1. uh H2; ee; lu. 
assert (is_versal b). cp K1; lu. 
ap H1. 
uhg; ee. app is_cone_cone_pushdown. 
rww cone_target_cone_pushdown. app mor_fmor. rw K3.
app mor_cone_to_limit. 
rww target_fmor. rww vertex_cone_pushdown. 
rww target_cone_to_limit. rw K3; app mor_cone_to_limit. 
uhg; ee. app  is_cone_cone_pushdown. 
rww cone_target_cone_pushdown. 

ap mor_cone_to_limit. ap is_cone_cone_pushdown. 
am. am. rw K3. uf cone_target. rww K2. am. 
rww socle_cone_pushdown. rw socle_cone_pushdown. 
rww K2. 
rww cone_target_cone_pushdown. 
rw target_cone_to_limit. tv. app is_cone_cone_pushdown. 
rw K3; uf cone_target; rww K2. am. 
rww socle_cone_pushdown. rw socle_cone_pushdown. 
rww K2. 
rw cone_compose_cone_pushdown_fmor_cone_to_limit. 
sy; rw cone_compose_cone_to_limit. tv. app is_cone_cone_pushdown.
rw K3; uf cone_target; rww K2. am. 
rw socle_cone_pushdown. rw socle_cone_pushdown. rww K2. 
Qed.

End Cone_Pushdown_Cone_To_Limit.

Section Limit_Preservation_Invariance.
Variables a b f : E. 

Hypothesis K : Functor.axioms f.
Hypothesis K0 : is_limit a.
Hypothesis K1 : is_limit b.
Hypothesis K2 : socle a = socle b.
Hypothesis K3 : source f = cone_target b.
Hypothesis K4 : is_limit (cone_pushdown f b).


Lemma invertible_cone_to_limit_a_b:
invertible (source f) (cone_to_limit a b).
Proof.
app invertible_cone_to_limit. rw K3; uf cone_target; rw K2. 
tv.  
Qed.

Lemma invertible_fmor_ctl :
invertible (target f) (fmor f (cone_to_limit a b)).
Proof.
app invertible_fmor. 
app invertible_cone_to_limit. rw K3; uf cone_target; rww K2. 
Qed.



Lemma limit_preservation_invariance : 
is_limit (cone_pushdown f a).
Proof.
ir. 
ap (cone_to_limit_invertible_is_limit 
(a:= (cone_pushdown f a)) (b:=(cone_pushdown f b))).
am. app is_cone_cone_pushdown. cp K0; lu. 
rw K3; uf cone_target; rww K2. 
rw socle_cone_pushdown. rw socle_cone_pushdown.
rww K2. 
wr fmor_cone_to_limit. 
rw cone_target_cone_pushdown. ap invertible_fmor_ctl. 
am. cp K0; lu. am. am. 
am. am. 
Qed.

End Limit_Preservation_Invariance.


Lemma cone_pushdown_are_inverse_invol : forall a f g,
is_cone a -> are_finverse f g -> 
source f = cone_target a ->
cone_pushdown g (cone_pushdown f a) = a.
Proof.
ir. ap cone_extensionality.
ap is_cone_cone_pushdown. ap is_cone_cone_pushdown. 
am. uh H0; ee; am. am. 
uh H0; ee; am. rw cone_target_cone_pushdown. 
uh H0; ee; am. am. 
rw vertex_cone_pushdown. rw vertex_cone_pushdown. 
wr fob_fcompose. uh H0; ee. rw H6. 
rw fob_fidentity. tv. rw H1. ap ob_vertex. am. 
uh H0; ee; am. uh H0; ee; am. uh H0; ee; am. 
rw H1. ap ob_vertex. am. 
rw socle_cone_pushdown. rw socle_cone_pushdown. 
wr fcompose_assoc. uh H0; ee. 
rw H6. 
rw left_fidentity. tv. 
ap socle_axioms. am. am. uh H0; ee; am. 
uh H0; ee; am. ap socle_axioms. am. 
uh H0; ee; am. am. 

ir. 
rwi cone_source_cone_pushdown H2. 
rwi cone_source_cone_pushdown H2. 
uh H0; ee. 
rw edge_cone_pushdown. 
rw edge_cone_pushdown. 
wr fmor_fcompose. rw H7. 
rw fmor_fidentity. tv. 
rw H1. ap mor_edge. am. am. am. 
am. am. rw H1. ap mor_edge. am. am. am. am.
rw cone_source_cone_pushdown. am. 
ap is_cone_cone_pushdown. am. am. am. 
Qed.

Lemma are_finverse_preserves_limits : forall a f g,
is_limit a -> are_finverse f g ->
source f = cone_target a -> 
is_limit (cone_pushdown f a).
Proof.
ir. 
uh H0; ee. 
assert (is_cone a). 
uh H; ee. uh H; ee. am. 
assert (is_cone (cone_pushdown f a)). 
ap is_cone_cone_pushdown. am. 
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

(**** uni proof *****) 

uhg; ee. am. 
ir. 
uh H9; ee. 
uh H10; ee. 
rwi cone_target_cone_pushdown H12. 
rwi cone_target_cone_pushdown H14. 

assert (cone_pushdown g (cone_pushdown f a) = a). 
rw cone_pushdown_are_inverse_invol. tv. am. 
uhg; ee; am. am.  



assert (cone_compose a (fmor g u) =
cone_compose a (fmor g v)).
wr H16. 
wr cone_pushdown_cone_compose. 
sy; wr cone_pushdown_cone_compose. 
rw H11. reflexivity. 
am. am. rw cone_target_cone_pushdown. am.  


rww H4. 
am. ap is_cone_cone_pushdown. am. am. am. am. 
rw cone_target_cone_pushdown. am. rw H4. am. 
am. 
uh H; ee. uh H; ee. 
assert (fmor g u = fmor g v). 
ap H19. 
uhg; ee. am. wr H1. rw H3. ap mor_fmor. 
am. rww H4. 
rw target_fmor. 
rw H13. rw vertex_cone_pushdown. 
rw lem1. tv. rw H1. ap ob_vertex. am. 
am. rww H4. 
uhg; ee. am. wr H1. rw H3. ap mor_fmor. 
am. rw H4. am. 
rw target_fmor. rw H15. 
rw vertex_cone_pushdown. rw lem1. tv. 
rw H1. ap ob_vertex. am. am. 
rww H4. am. 
wr lem4. wr H20. rw lem4. tv. 
am. am. 

(***** versal proof ****)

uhg; ee. am. ir. cp H. uh H11. ee. 
uh H12. ee. 
util (H13 (cone_pushdown g b)). 
ap is_cone_cone_pushdown. am. am. 
uf cone_target. rw H10. 
rw socle_cone_pushdown. rw target_fcompose. am. 
rw socle_cone_pushdown. rw H10. 
rw socle_cone_pushdown. 
wr fcompose_assoc. rw H6. 
rw left_fidentity. tv. app socle_axioms. 
exact H1. am. am. 
app socle_axioms. am. exact H1. 

nin H14. ee. uh H14; ee. 
sh (fmor f x). ee. 
uhg; ee. 
ap is_cone_cone_pushdown. am. am. 
am. 
rw cone_target_cone_pushdown. ap mor_fmor. 
am. rw H1. am. 
rw vertex_cone_pushdown. 
rw target_fmor. rww H17. am. rww H1. 
wr cone_pushdown_cone_compose. rw H15. 
rw cone_pushdown_are_inverse_invol. tv. 
am. uhg; ee; am. uf cone_target. 
rw H10. rw socle_cone_pushdown. 
rw target_fcompose. am. am. am. 
am. rww H1. am. 
Qed.

Lemma has_limits_over_finverse_invariance : 
forall a b c, 
Category.axioms a -> Category.axioms b -> Category.axioms c ->
has_limits_over c a ->
(exists f, (exists g, 
(are_finverse f g & source f = a & target f = b))) ->
has_limits_over c b.
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
sh (cone_pushdown x x1). 
uhg; ee. 
apply are_finverse_preserves_limits with x0. am. 
uhg; ee; am. uf cone_target. rw H19. 
rw H16. am. 
rw socle_cone_pushdown. rw H19. am. 
Qed.



End Limit.













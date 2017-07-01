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
Require Export colimits.
Require Export little_cat.
Require Export fc_limits. 
Require Export cardinal.


Module Equalizer.
Export Finite_Cat.
Export Limit.
Export Twoarrow_Cat.

Definition equalizer_hypothesis a u v y :=
twoarrow_hypothesis a u v &
mor a y & source u = target y &
comp a u y = comp a v y.


Definition equalizer_cone a u v y :=
cone_create (source y) (twoarrow_nt a 
(id a (source y)) (id a (source y)) u v y (comp a u y)).

Lemma vertex_equalizer_cone : forall a u v y,
vertex (equalizer_cone a u v y) = source y.
Proof.
ir. uf equalizer_cone. 
rw vertex_cone_create. tv. 
Qed.

Lemma edge_nt_equalizer_cone : forall a u v y,
edge_nt (equalizer_cone a u v y) = 
(twoarrow_nt a 
(id a (source y)) (id a (source y)) u v y (comp a u y)).
Proof.
ir. uf equalizer_cone. 
rw edge_nt_cone_create. tv. 
Qed. 

Lemma edge_equalizer_cone_R : forall a u v y (x:obsy twoarrow_data),
edge (equalizer_cone a u v y) (R x) =
match x with 
o1 => y | o2 => (comp a u y)
end.
Proof.
ir. 
uf edge. 
rw edge_nt_equalizer_cone. 
rw ntrans_twoarrow_nt_R. tv. 
Qed. 

Lemma socle_equalizer_cone : forall a u v y,
socle (equalizer_cone a u v y) = twoarrow_functor a u v.
Proof.
ir. uf socle. 
rw edge_nt_equalizer_cone. 
rw target_twoarrow_nt. tv. 
Qed.

Lemma cone_source_equalizer_cone : forall a u v y,
cone_source (equalizer_cone a u v y) = twoarrow_cat.
Proof.
ir. uf cone_source. 
rw socle_equalizer_cone. rww source_twoarrow_functor. 
Qed.

Lemma cone_target_equalizer_cone : forall a u v y,
cone_target (equalizer_cone a u v y) = a.
Proof.
ir. uf cone_target. 
rw socle_equalizer_cone. rww target_twoarrow_functor. 
Qed.

Lemma equalizer_twoarrow_nt_hypothesis : forall a u v y,
equalizer_hypothesis a u v y ->
twoarrow_nt_hypothesis a (id a (source y)) (id a (source y)) u v y
  (comp a u y).
Proof.
ir. uh H; ee. 
uh H; ee. 
assert (ob a (source y)). rww ob_source. 
assert (ob a (target y)). rww ob_target. 

uhg; ee. 

uh H0; ee; am. app mor_id. 
app mor_id. am. am. am. 
rww mor_comp. rww source_id. sy; am. 
rww source_comp. rww target_id. 
rww target_comp. 
tv. tv. am. am. rww assoc. 
rww right_id. app mor_id.  rww target_id. 

rww assoc. rww right_id. app mor_id. 
rww target_id. 
Qed. 

Lemma is_cone_equalizer_cone : forall a u v y,
equalizer_hypothesis a u v y ->
is_cone (equalizer_cone a u v y).
Proof.
ir. uhg; ee. 
uf equalizer_cone. 
ap cone_like_cone_create. 
rw edge_nt_equalizer_cone. 
ap twoarrow_nt_axioms. 
app equalizer_twoarrow_nt_hypothesis. 
rw cone_target_equalizer_cone. 
rw vertex_equalizer_cone. uh H; ee. rww ob_source. 

rw edge_nt_equalizer_cone. 
rw source_twoarrow_nt. 
rw cone_source_equalizer_cone. 
rw cone_target_equalizer_cone. 
rw vertex_equalizer_cone. sy; 
rw constant_functor_twoarrow_functor. tv. 
tv. uh H; ee. rww ob_source. 
Qed.

Definition eqzmap c := edge c (R o1').

Lemma source_eqzmap : forall c,
is_cone c -> cone_source c = twoarrow_cat ->
source (eqzmap c) =  vertex c.
Proof.
ir. uf eqzmap. rww source_edge. 
rw H0. app ob_twoarrow_cat. 
Qed.

Lemma equalizer_hypothesis_eqzmap : 
forall a u v c, twoarrow_hypothesis a u v -> 
is_cone c -> socle c = twoarrow_functor a u v ->
equalizer_hypothesis a u v (eqzmap c).
Proof.
ir. 
assert (a = cone_target c).
uf cone_target. rw H1. rw target_twoarrow_functor. 
tv. 
assert (cone_source c = twoarrow_cat).
uf cone_source. rw H1. 
rww source_twoarrow_functor. 
uhg. ee. am. 
uf eqzmap. 
rw H2. 
ap mor_edge. 
rw H3. ap ob_twoarrow_cat. 
am. 
uf eqzmap. rw target_edge. 
rw H1. 
rw fob_twoarrow_functor_R. tv. am. 
rw H3. ap ob_twoarrow_cat. am. 

set (k:= edge_nt c).
util (twoarrow_nt_ntrans (u:=k)).
uf k. app edge_nt_axioms. 
uf k. rww osource_edge_nt. 
assert (otarget k = a).
uf k. rww otarget_edge_nt. sy; am. 
assert 
(fmor (source k) (catyd_arrow (d:=twoarrow_data) a0') =
id a (vertex c)). 
uf k. 
rw source_edge_nt. 
rw fmor_constant_functor. wr H2. tv. 
rw H3. ap mor_twoarrow_cat. am. 

assert 
(fmor (source k) (catyd_arrow (d:=twoarrow_data) a1') =
id a (vertex c)). 
uf k. 
rw source_edge_nt. 
rw fmor_constant_functor. wr H2. tv. 
rw H3. ap mor_twoarrow_cat. am. 

assert 
(fmor (target k) (catyd_arrow (d:=twoarrow_data) a0') = u).
uf k. 
rw target_edge_nt. 
rw H1. rw fmor_twoarrow_functor_catyd_arrow. 
tv. am. 

assert 
(fmor (target k) (catyd_arrow (d:=twoarrow_data) a1') = v).
uf k. 
rw target_edge_nt. 
rw H1. rw fmor_twoarrow_functor_catyd_arrow. 
tv. am. 

util (twoarrow_nt_hypothesis_ntrans (u:=k)).
uf k. app edge_nt_axioms. uf k. 
rw osource_edge_nt. am. am. 
rwi H6 H10. 
rwi H5 H10. rwi H7 H10. rwi H8 H10. 
rwi H9 H10. 
assert (ntrans k (R o1') = eqzmap c).
uf eqzmap. uf edge.
tv. rwi H11 H10. 
set (m:= ntrans k (R o2')).
assert (m = ntrans k (R o2')). tv. wri H12 H10.
uh H10; ee. wr H27. wr H28. 
reflexivity. 
Qed.

Lemma equalizer_cone_eq : forall a u v c,
twoarrow_hypothesis a u v -> 
is_cone c -> socle c = twoarrow_functor a u v ->
c = equalizer_cone a u v (eqzmap c).
Proof.
ir. 
assert (a = cone_target c).
uf cone_target. rw H1. rw target_twoarrow_functor. 
tv. 
assert (cone_source c = twoarrow_cat).
uf cone_source. rw H1. 
rww source_twoarrow_functor. 

set (k:= edge_nt c).
util (twoarrow_nt_ntrans (u:=k)).
uf k. app edge_nt_axioms. 
uf k. rww osource_edge_nt. 
assert (otarget k = a).
uf k. rww otarget_edge_nt. sy; am. 
assert 
(fmor (source k) (catyd_arrow (d:=twoarrow_data) a0') =
id a (vertex c)). 
uf k. 
rw source_edge_nt. 
rw fmor_constant_functor. wr H2. tv. 
rw H3. ap mor_twoarrow_cat. am. 

assert 
(fmor (source k) (catyd_arrow (d:=twoarrow_data) a1') =
id a (vertex c)). 
uf k. 
rw source_edge_nt. 
rw fmor_constant_functor. wr H2. tv. 
rw H3. ap mor_twoarrow_cat. am. 

assert 
(fmor (target k) (catyd_arrow (d:=twoarrow_data) a0') = u).
uf k. 
rw target_edge_nt. 
rw H1. rw fmor_twoarrow_functor_catyd_arrow. 
tv. am. 

assert 
(fmor (target k) (catyd_arrow (d:=twoarrow_data) a1') = v).
uf k. 
rw target_edge_nt. 
rw H1. rw fmor_twoarrow_functor_catyd_arrow. 
tv. am. 

rwi H5 H4. rwi H6 H4. rwi H7 H4. rwi H8 H4. 
rwi H9 H4. 


transitivity (cone_create (vertex c) k).
uh H0; ee. uh H0; ee. 
sy; am. 
uf equalizer_cone. 
rw source_eqzmap. 
ap uneq. wr H4. ap uneq. 

util (twoarrow_nt_hypothesis_ntrans (u:=k)).
uf k. app edge_nt_axioms. uf k. 
rw osource_edge_nt. am. am. 
rwi H6 H10. 
rwi H5 H10. rwi H7 H10. rwi H8 H10. 
rwi H9 H10. 
assert (ntrans k (R o1') = eqzmap c).
uf eqzmap. uf edge.
tv. rwi H11 H10. 
set (m:= ntrans k (R o2')).
assert (m = ntrans k (R o2')). tv. wri H12 H10.
uh H10; ee. wr H27. 
rw right_id. tv. rw H2. app ob_vertex. 
am. rw H21. rw target_id. tv. 
rw H2; app ob_vertex. tv. am. am. 
Qed.

Lemma eqzmap_equalizer_cone : forall a u v y,
equalizer_hypothesis a u v y ->
eqzmap (equalizer_cone a u v y) = y.
Proof.
ir. uf eqzmap. 
rw edge_equalizer_cone_R. tv. 
Qed.

Lemma eqzmap_cone_compose : forall c z,
is_cone c -> cone_source c = twoarrow_cat ->
cone_composable c z ->
eqzmap (cone_compose c z) = comp (cone_target c) (eqzmap c) z.
Proof.
ir. 
uf eqzmap. 
rw edge_cone_compose. tv. rw H0; ap ob_twoarrow_cat. 
am. 
Qed.

Definition eqzfirst c := 
(fmor (socle c) (catyd_arrow (d:=twoarrow_data) a0')).
Definition eqzsecond c :=
(fmor (socle c) (catyd_arrow (d:=twoarrow_data) a1')).

Lemma equalizer_hypothesis_eqz : forall c,
is_cone c -> cone_source c = twoarrow_cat ->
equalizer_hypothesis (cone_target c) (eqzfirst c) (eqzsecond c)
(eqzmap c).
Proof.
ir. util (equalizer_hypothesis_eqzmap (a:= cone_target c)
(u:= eqzfirst c) (v:= eqzsecond c) (c:=c)).
uf eqzfirst. uf eqzsecond. 
uf cone_target. ap functor_twoarrow_hypothesis. 
app socle_axioms. am. am. 
uf cone_target. 
uf eqzfirst. uf eqzsecond. ap functor_twoarrow_eq.
app socle_axioms. am. 
am. 
Qed.

Lemma equalizer_cone_eq2 : forall c,
is_cone c -> cone_source c = twoarrow_cat ->
c = equalizer_cone (cone_target c) (eqzfirst c) (eqzsecond c)
(eqzmap c).
Proof.
ir. 
util (equalizer_cone_eq (a:= cone_target c)
(u:= eqzfirst c) (v:= eqzsecond c) (c:=c)).
uf eqzfirst. uf eqzsecond. 
uf cone_target. ap functor_twoarrow_hypothesis. 
app socle_axioms. am. am. 
uf cone_target. 
uf eqzfirst. uf eqzsecond. ap functor_twoarrow_eq.
app socle_axioms. am. 
am. 
Qed.


Lemma eqzmap_extensionality : forall a b,
is_cone a -> is_cone b -> cone_source a = twoarrow_cat 
-> socle a = socle b -> eqzmap a = eqzmap b -> a = b.
Proof.
ir. 
assert (cone_source b = twoarrow_cat).
uf cone_source. wr H2. am. 
util (equalizer_cone_eq2 (c:= a)). 
am. am. 
util (equalizer_cone_eq2 (c:= b)). 
am. am. rw H5; rw H6. 
assert (eqzfirst a = eqzfirst b).
uf eqzfirst. rww H2. 
assert (eqzsecond a = eqzsecond b).
uf eqzsecond. rw H2. reflexivity. 
rw H3; rw H7; rw H8. 
assert (cone_target a = cone_target b).
uf cone_target. rww H2. rw H9. 
reflexivity. 
Qed.

Lemma cone_compose_equalizer_cone : forall a u v y z,
equalizer_hypothesis a u v y ->
mor a z -> source y = target z -> 
cone_compose (equalizer_cone a u v y) z = 
equalizer_cone a u v (comp a y z).
Proof.
ir. 

assert (lem1: equalizer_hypothesis a u v (comp a y z)).
uh H; uhg; ee. am. rww mor_comp. 
rww target_comp. wr assoc. 
rw H4. rww assoc. uh H; ee; am. 
uh H; ee. wr H6. am. uh H; ee; am. am. 
am. am. am. tv. 

assert (lem2 : cone_composable (equalizer_cone a u v y) z).
uhg; ee. 
app  is_cone_equalizer_cone. 
rww cone_target_equalizer_cone. 
rww vertex_equalizer_cone. sy; am.


ap eqzmap_extensionality. 
rww is_cone_cone_compose. 
app is_cone_equalizer_cone. 
rw cone_source_cone_compose. rww cone_source_equalizer_cone. 
rw socle_cone_compose. 
rww socle_equalizer_cone. rww socle_equalizer_cone. 
rww eqzmap_cone_compose. 
rww cone_target_equalizer_cone. 
rww eqzmap_equalizer_cone. 
rww eqzmap_equalizer_cone. 
app is_cone_equalizer_cone. 
rww cone_source_equalizer_cone. 
Qed.

Lemma cone_composable_equalizer_cone : forall a u v y z,
equalizer_hypothesis a u v y -> mor a z ->
source y = target z -> 
cone_composable (equalizer_cone a u v y) z.
Proof.
ir. uhg; ee. app is_cone_equalizer_cone. 
rww cone_target_equalizer_cone. 
rww vertex_equalizer_cone. sy; am. 
Qed. 

Lemma is_uni_equalizer_cone : forall a u v y,
equalizer_hypothesis a u v y ->
is_uni (equalizer_cone a u v y) =
(forall z z', mor a z -> mor a z' ->
source y = target z -> source y = target z' ->
comp a y z = comp a y z' -> z = z').
Proof.
ir. ap iff_eq; ir. 
uh H0. ee. ap H6.
app cone_composable_equalizer_cone.
app cone_composable_equalizer_cone.
rw cone_compose_equalizer_cone. 
sy; rw cone_compose_equalizer_cone.
rww H5. am. am. am. am. am. am. 

uhg. ee. app is_cone_equalizer_cone. 
ir. 
cp H1; cp H2. uh H4; uh H5; ee. 
rwi cone_target_equalizer_cone H8. 
rwi cone_target_equalizer_cone H6. 
rwi vertex_equalizer_cone H9. 
rwi vertex_equalizer_cone H7. 

app H0. sy; am. sy; am. 
rwi cone_compose_equalizer_cone H3. 
transitivity 
(eqzmap (equalizer_cone a u v (comp a y u0))).
rw eqzmap_equalizer_cone. tv. 
uh H; ee. uhg; ee; try am. 
rww mor_comp. sy; am. 
rww target_comp. sy; am. 
wr assoc. rw H12. rww assoc. 
uh H; ee; am. uh H; ee. 
sy; wrr H14. sy; am. 
uh H; ee; sy; am. uh H; ee; am. am.  am. 
am. sy; am. tv. 
rw H3. 
rw cone_compose_equalizer_cone. 
rw eqzmap_equalizer_cone. tv. 
uh H; ee. uh H; ee. 
uhg; ee; try am. uhg; ee; am. 
rww mor_comp. sy; am. 
rww target_comp. sy; am. 
wr assoc. rw H12. rww assoc. 
wr H14. am. sy; am. 
am. am. am. am. sy; am. 
tv. am. am. sy; am. 
am. am. sy; am. 
Qed.

Lemma is_versal_equalizer_cone : forall a u v y,
equalizer_hypothesis a u v y ->
is_versal (equalizer_cone a u v y) =
(forall z, equalizer_hypothesis a u v z -> 
(exists w, (mor a w & source y = target w &
comp a y w = z))).
Proof.
ir. ap iff_eq; ir. 
uh H0; ee. 
util (H2 (equalizer_cone a u v z)). 
app is_cone_equalizer_cone. 
rww socle_equalizer_cone; sy; 
rww socle_equalizer_cone. 
nin H3. ee. 
cp H3. uh H5; ee. 
rwi cone_target_equalizer_cone H6. 
rwi vertex_equalizer_cone H7. 
rwi cone_compose_equalizer_cone H4. 
sh x; ee. am. sy; am. 
transitivity (eqzmap (equalizer_cone a u v (comp a y x))).
rw eqzmap_equalizer_cone. tv. 
uh H; uhg; ee; try am. rww mor_comp. sy; am.
rww target_comp. sy; am. 
uh H; ee. 
wrr assoc. rw H10; rww assoc. 
wr H12. am. sy; am. sy; am. 
rw H4. rww eqzmap_equalizer_cone. am. am. 
sy; am. 

uhg; ee. app is_cone_equalizer_cone. ir. 
rwi socle_equalizer_cone H2. 
cp H. 
uh H3. ee. cp (equalizer_cone_eq H3 H1 H2). 
cp (equalizer_hypothesis_eqzmap H3 H1 H2). 

util (H0 (eqzmap b)). am. 
nin H9. ee. sh x; ee. 
app cone_composable_equalizer_cone. 
rww cone_compose_equalizer_cone. rw H11. sy; am. 
Qed.

Definition is_equalizer a u v y :=
equalizer_hypothesis a u v y &
is_limit (equalizer_cone a u v y).

Lemma show_is_equalizer : forall a u v y ,
equalizer_hypothesis a u v y ->
(forall z z', mor a z -> mor a z' ->
source y = target z -> source y = target z' ->
comp a y z = comp a y z' -> z = z') ->
(forall z, equalizer_hypothesis a u v z -> 
(exists w, (mor a w & source y = target w &
comp a y w = z))) ->
is_equalizer a u v y.
Proof.
ir. uhg; ee. am. 
uhg. ee. rww is_uni_equalizer_cone. 
rww is_versal_equalizer_cone. 
Qed.


Definition has_equalizer a u v :=
twoarrow_hypothesis a u v &
has_limit (twoarrow_functor a u v).

Lemma has_equalizer_rw : forall a u v,
has_equalizer a u v = (exists y, is_equalizer a u v y).
Proof.
ir. ap iff_eq; ir. 
uh H; ee. uh H0. 
nin H0. uh H0; ee. sh (eqzmap x).
uhg; ee. 
ap equalizer_hypothesis_eqzmap. am. 
app is_limit_is_cone. am. 

assert (is_cone x). 
app is_limit_is_cone.
util (equalizer_cone_eq (a:=a) (u:=u) (v:=v) (c:=x)). 
am. am. am. 
wr H3. am. 

nin H. uhg; ee. 
uh H; ee. uh H; ee; am. 
uh H; ee. 
uhg. 
sh (equalizer_cone a u v x). 
uhg; ee. am. 
rww socle_equalizer_cone.  
Qed.

Definition has_equalizers a :=
Category.axioms a &
(forall u v, twoarrow_hypothesis a u v -> 
has_equalizer a u v).


Definition equalizer a u v := 
eqzmap (limit (twoarrow_functor a u v)).

Lemma equalizer_hypothesis_equalizer : forall a u v,
has_equalizer a u v ->
equalizer_hypothesis a u v (equalizer a u v).
Proof.
ir. uf equalizer. 
app equalizer_hypothesis_eqzmap. 
uh H; ee; am. 
ap is_limit_is_cone. ap is_limit_limit.
uh H; ee; am. 
rw socle_limit. tv. uh H; ee; am. 
Qed.

Lemma equalizer_hypothesis_comp : forall a u v y z,
equalizer_hypothesis a u v y -> mor a z ->
source y = target z  ->
equalizer_hypothesis a u v (comp a y z).
Proof.
ir. uh H; uhg; ee. am. rww mor_comp. 
rww target_comp. 
wrr assoc. rw H4. rww assoc.
uh H; ee. am. uh H; ee. 
wrr H6. uh H; ee; am. 
Qed.

Lemma is_equalizer_equalizer : forall a u v,
has_equalizer a u v ->
is_equalizer a u v (equalizer a u v).
Proof.
ir. uhg; ee. 
app equalizer_hypothesis_equalizer. 
uf equalizer. 
wr equalizer_cone_eq. 
ap is_limit_limit. uh H; ee; am. 
uh H; ee. am. 
ap is_limit_is_cone. ap is_limit_limit. uh H; ee; am. 
rw socle_limit. tv. uh H; ee; am. 
Qed.

Lemma has_equalizers_has_equalizer : forall a u v,
has_equalizers a -> twoarrow_hypothesis a u v->
has_equalizer a u v.
Proof.
ir. uh H; ee. ap H1. am. 
Qed.

Lemma has_equalizers_has_limits_over : forall a,
Category.axioms a ->
has_equalizers a = has_limits_over twoarrow_cat a.
Proof.
ir. ap iff_eq; ir. 
uhg. ir. uh H0. ee. 
util (H4 (fmor f (catyd_arrow a0')) (fmor f (catyd_arrow a1'))).
wr H3. ap functor_twoarrow_hypothesis. am. 
am. 
uh H5. ee. wri H3 H6. 
rww functor_twoarrow_eq. 

uh H0. uhg; ee. am. 
ir. uhg; ee; try am. 
ap H0. 
app twoarrow_functor_axioms. 
rww source_twoarrow_functor. 
rww target_twoarrow_functor. 
Qed.

Lemma mor_equalizer : forall a u v,
has_equalizer a u v ->
mor a (equalizer a u v).
Proof.
ir. cp (is_equalizer_equalizer H). 
uh H0; ee. 
uh H0; ee. am. 
Qed.

Lemma target_equalizer : forall a u v,
has_equalizer a u v ->
target (equalizer a u v) = source u.
Proof.
ir. cp (is_equalizer_equalizer H). 
uh H0; ee. 
uh H0; ee. sy; am. 
Qed.

Lemma comp_equalizer_eq : forall a u v,
has_equalizer a u v ->
comp a u (equalizer a u v) = comp a v (equalizer a u v).
Proof.
ir. cp (is_equalizer_equalizer H). 
uh H0; ee. 
uh H0; ee. am. 
Qed.

Definition eqz_dotted a u v y :=
dotted (equalizer_cone a u v y).

Lemma equalizer_cone_equalizer : forall a u v,
has_equalizer a u v ->
equalizer_cone a u v (equalizer a u v) =
limit (twoarrow_functor a u v).
Proof.
ir. 
uf equalizer. 
wr equalizer_cone_eq. tv. uh H; ee; am. 
ap is_limit_is_cone. ap is_limit_limit. 
uh H; ee; am. 
rw socle_limit. tv. uh H; ee; am. 
Qed. 

Lemma cone_composable_eqz_dotted : forall a u v y,
has_equalizer a u v -> equalizer_hypothesis a u v y ->
cone_composable (equalizer_cone a u v (equalizer a u v))
(eqz_dotted a u v y).
Proof.
ir. 
uf eqz_dotted. 
rw equalizer_cone_equalizer. 
assert (twoarrow_functor a u v =
socle (equalizer_cone a u v y)). 
rww socle_equalizer_cone. rw H1. 
ap cone_composable_dotted. 
app is_cone_equalizer_cone. 
rw socle_equalizer_cone. uh H; ee; am. 
am. 
Qed. 

Lemma cone_compose_eqz_dotted : forall a u v y,
has_equalizer a u v -> equalizer_hypothesis a u v y ->
cone_compose (equalizer_cone a u v (equalizer a u v))
(eqz_dotted a u v y) = equalizer_cone a u v y.
Proof.
ir. 
uf eqz_dotted. 
rw equalizer_cone_equalizer. 
assert (twoarrow_functor a u v =
socle (equalizer_cone a u v y)). 
rww socle_equalizer_cone. rw H1. 
ap cone_compose_dotted. 
app is_cone_equalizer_cone. 
rw socle_equalizer_cone. uh H; ee; am. am. 
Qed. 

Lemma eqz_dotted_uni : forall a u v y r,
has_equalizer a u v -> equalizer_hypothesis a u v y ->
cone_composable (equalizer_cone a u v (equalizer a u v)) r ->
cone_compose (equalizer_cone a u v (equalizer a u v)) r =
equalizer_cone a u v y -> 
eqz_dotted a u v y = r.
Proof.
ir. uf eqz_dotted. 
wr H2. 
rw equalizer_cone_equalizer. ap dotted_unique. 
ap twoarrow_functor_axioms. uh H0; ee; am. 
uh H; ee; am. 
wr equalizer_cone_equalizer. am. am. am. 
Qed. 

Lemma mor_eqz_dotted : forall a u v y,
has_equalizer a u v -> equalizer_hypothesis a u v y ->
mor a (eqz_dotted a u v y).
Proof.
ir. 
cp (cone_composable_eqz_dotted H H0). 
uh H1; ee. rwi cone_target_equalizer_cone H2. am. 
Qed.

Lemma target_eqz_dotted : forall a u v y,
has_equalizer a u v -> equalizer_hypothesis a u v y ->
target (eqz_dotted a u v y) = source (equalizer a u v).
Proof.
ir. 
cp (cone_composable_eqz_dotted H H0). 
uh H1; ee. rwi vertex_equalizer_cone H3. am. 
Qed.

Lemma comp_equalizer_eqz_dotted : forall a u v y,
has_equalizer a u v -> equalizer_hypothesis a u v y ->
comp a (equalizer a u v) (eqz_dotted a u v y) = y.
Proof.
ir. 
cp (cone_compose_eqz_dotted H H0). 
transitivity (eqzmap (equalizer_cone a u v y)).
wr H1. 
rw eqzmap_cone_compose. 
rw cone_target_equalizer_cone. 
rw eqzmap_equalizer_cone. tv. 
ap equalizer_hypothesis_equalizer. am. 
ap is_cone_equalizer_cone. 
app equalizer_hypothesis_equalizer. 
rww cone_source_equalizer_cone. 
app cone_composable_eqz_dotted. 
rww eqzmap_equalizer_cone.
Qed.



Lemma eqz_dotted_comp : forall a u v z,
has_equalizer a u v -> mor a z ->
source (equalizer a u v) = target z ->
eqz_dotted a u v (comp a (equalizer a u v) z) = z.
Proof.
ir. 
assert (equalizer_hypothesis a u v (equalizer a u v)).
app equalizer_hypothesis_equalizer. 
ap eqz_dotted_uni. am. 
app equalizer_hypothesis_comp. 
uhg; ee. app is_cone_equalizer_cone. 
rww cone_target_equalizer_cone. 
rww vertex_equalizer_cone. sy; am. 
rw cone_compose_equalizer_cone. tv. 
am. am. am. 
Qed.

(*** now we apply the result of fc_limits to 
the case of equalizers ***********************)

Lemma has_equalizers_functor_cat : forall a b,
Category.axioms a -> has_equalizers b -> 
has_equalizers (functor_cat a b).
Proof.
ir. rw has_equalizers_has_limits_over.
cp H0.
uh H1; ee. 
rwi has_equalizers_has_limits_over H0. 
ap has_limits_functor_cat. am. am. 
ap twoarrow_cat_axioms. am. am. 
ap functor_cat_axioms. am. 
uh H0; ee; am. 
Qed.








Lemma has_finite_limits_has_equalizers : forall a,
has_finite_limits a ->  has_equalizers a.
Proof.
ir. rw has_equalizers_has_limits_over. 
uh H; ee. ap H0. 
ap is_finite_twoarrow_cat. uh H; ee; am. 
Qed.

End Equalizer. 


Export Equalizer.


(*** we should be able to more or less recopy Equalizer to
get a module Fiprod for fiber products; then also 
dualize to get coequalizers and cofiber products. The other
main type of limits and colimits we need to do are direct
products and coproducts ... *****************************)

Module Coequalizer. 

(**** we do this module by dualizing the module
Equalizer, rather than by relying on colimits *******)




Definition coequalizer_hypothesis a u v y :=
twoarrow_hypothesis a u v &
mor a y & source y = target u &
comp a y u = comp a y v.

Lemma coeq_hyp_eq_hyp : forall a u v y,
Category.axioms a -> 
coequalizer_hypothesis a u v y = 
equalizer_hypothesis (opp a) (flip u) (flip v) (flip y).
Proof.
ir. ap iff_eq; ir. 
uh H0; uhg; ee. 
uh H0; uhg; ee. 
rww mor_opp. rww flip_flip. 
rww mor_opp. rww flip_flip. 
rw source_flip. rw source_flip. 
am. alike. alike. 
rw target_flip; try alike. 
rww target_flip; try alike. 
rww mor_opp; rww flip_flip. 
rww target_flip; try alike. 
rww source_flip; try alike. sy; am. 
uh H0; ee; alike. 
rw comp_opp. 
rw comp_opp. rw flip_flip. 
rw flip_flip. rw flip_flip. ap uneq. am. 
rww mor_opp; rww flip_flip. 
uh H0; ee; am. 
rww mor_opp; rww flip_flip. 
rww target_flip; try alike. 
rww source_flip; try alike.
uh H0; ee. wr H6. sy; am. 
uh H0; ee; alike. 
rww mor_opp; rww flip_flip. 
uh H0; ee; am. 
rww mor_opp; rww flip_flip. 
rww target_flip; try alike. 
rww source_flip; try alike.
sy; am. uh H0; ee; alike. 



uh H0; ee. uh H0; ee. 
uhg; dj. uhg; dj. rwi mor_opp H0. 
rwi flip_flip H0. am. 
rwi mor_opp H4. 
rwi flip_flip H4. am. 
wr target_flip; try alike. 
rw H6. rw target_flip; try alike. tv. 
wr source_flip; try alike. rw H5. 
rww source_flip; try alike. 
rwi mor_opp H1. 
rwi flip_flip H1. am. 
uh H7; ee. wr target_flip; try alike. 
wr H2. rw H5. 
rww source_flip; try alike. sy; am. 

rwi comp_opp H3. rwi flip_flip H3. 
rwi flip_flip H3. transitivity (flip (flip (comp a y u))).
rww flip_flip. rw H3. 
rw comp_opp. rw flip_flip. rw flip_flip. rw flip_flip. 
tv.  am. am.  
wr H5. am. 
am. am. am. 
Qed. 





Definition is_coequalizer a u v y :=
Category.axioms a & 
is_equalizer (opp a) (flip u) (flip v) (flip y).



Lemma show_is_coequalizer : forall a u v y ,
Category.axioms a -> 
coequalizer_hypothesis a u v y ->
(forall z z', mor a z -> mor a z' ->
source z = target y -> source z' = target y ->
comp a z y = comp a z' y -> z = z') ->
(forall z, coequalizer_hypothesis a u v z -> 
(exists w, (mor a w & source w = target y &
comp a w y = z))) ->
is_coequalizer a u v y.
Proof.
ir. uhg; ee. am. 
ap show_is_equalizer. 
wr coeq_hyp_eq_hyp. am. am. 
ir. set (z1:=flip z). set (z2 := flip z'). 
assert (z1 = z2). ap H1. 
uf z1. rwi mor_opp H3. am. 
rwi mor_opp H4. am.  
uf z1. rw source_flip; try alike. wr H5. 
rww source_flip; try alike. uh H0; ee. 
alike. 
uf z2. rw source_flip; try alike. wr H6. 
rww source_flip; try alike. uh H0; ee. 
alike. 
rwi comp_opp H7. 
rwi flip_flip H7. 
rwi comp_opp H7. rwi flip_flip H7. 
ap flip_eq. am. 
rww mor_opp. rw flip_flip. 
uh H0; ee; am. 
am. 
am. rww mor_opp. rw flip_flip.
uh H0; ee; am. 
am. 
am. 
ap flip_eq. am. 

ir. 
cp H3. set (z1 := flip z).
assert (z= flip z1). 
uf z1; rww flip_flip. rwi H5 H4.
wri coeq_hyp_eq_hyp H4. 
nin (H2 z1 H4). ee. 
sh (flip x). ee. rww mor_opp. 
rww flip_flip. 
rw source_flip. rw target_flip. 
sy; am. alike. uh H0; ee; alike. 
rw comp_opp. 
rw flip_flip. rw flip_flip. ap flip_eq. 
rw flip_flip. am. 
rww mor_opp. rw flip_flip. uh H0; ee; am. 
rww mor_opp. rww flip_flip. 
rw source_flip. rw target_flip. sy; am. 
alike. uh H0; ee; alike. am. 
Qed.


Definition has_coequalizer a u v :=
twoarrow_hypothesis a u v &
has_equalizer (opp a) (flip u) (flip v).


Lemma has_coequalizer_rw : forall a u v,
has_coequalizer a u v = (exists y, is_coequalizer a u v y).
Proof.
ir. ap iff_eq; ir. 
uh H; ee. 
rwi has_equalizer_rw H0. 
nin H0. sh (flip x). 
uhg; ee. uh H; ee. uh H; ee; am. rww flip_flip. 
nin H. uh H; ee. 
uhg; ee. 
uh H0; ee. 
wri coeq_hyp_eq_hyp H0. uh H0. ee; am. am. 
rw has_equalizer_rw. sh (flip x).
am. 
Qed.

Definition has_coequalizers a :=
Category.axioms a &
(forall u v, twoarrow_hypothesis a u v -> 
has_coequalizer a u v).


Definition coequalizer a u v := 
flip (equalizer (opp a) (flip u) (flip v)).

Lemma coequalizer_hypothesis_coequalizer : forall a u v,
has_coequalizer a u v ->
coequalizer_hypothesis a u v (coequalizer a u v).
Proof.
ir. uf coequalizer. 
rw coeq_hyp_eq_hyp. rw flip_flip. 
ap equalizer_hypothesis_equalizer. 
uh H. ee; am. uh H; ee. uh H; ee. uh H; ee; am. 
Qed.

Lemma coequalizer_hypothesis_comp : forall a u v y z,
coequalizer_hypothesis a u v y -> mor a z ->
source z = target y  ->
coequalizer_hypothesis a u v (comp a z y).
Proof.
ir. 
rw coeq_hyp_eq_hyp. 
rwi coeq_hyp_eq_hyp H. 
assert (flip (comp a z y) =
comp (opp a) (flip y) (flip z)). 
rw comp_opp. 
rw flip_flip. rww flip_flip. 
uh H; ee; am. 
rww mor_opp. 
rww flip_flip. 

rw source_flip; try alike. rw target_flip. 
sy; am. alike. uh H; ee. 
rwi mor_opp H2. rwi flip_flip H2; alike. 

rw H2. ap equalizer_hypothesis_comp. am. 
rww mor_opp. rww flip_flip.  

rw source_flip; try alike. rw target_flip. 
sy; am. alike. uh H; ee. 
rwi mor_opp H3. rwi flip_flip H3; alike. 
uh H0; ee; am. uh H0; ee; am. 
Qed.

Lemma is_coequalizer_coequalizer : forall a u v,
has_coequalizer a u v ->
is_coequalizer a u v (coequalizer a u v).
Proof.
ir. assert (Category.axioms a).
uh H; ee. uh H; ee. uh H; ee; am. 
uhg; ee; try am. 
uf coequalizer. rw flip_flip. 
ap is_equalizer_equalizer. uh H; ee. am. 
Qed.

Lemma has_coequalizers_has_coequalizer : forall a u v,
has_coequalizers a -> twoarrow_hypothesis a u v->
has_coequalizer a u v.
Proof.
ir. uh H; ee. ap H1. am. 
Qed.

Lemma twoarrow_hypothesis_opp1 : forall a u v,
Category.axioms a -> 
twoarrow_hypothesis a u v ->
twoarrow_hypothesis (opp a) (flip u) (flip v).
Proof.
ir. uh H0; ee. uhg; ee. 
rww mor_opp. rww flip_flip.  
rww mor_opp. rww flip_flip.  
rw source_flip; try alike. 
rw source_flip; try alike. am. 
rw target_flip; try alike. 
rw target_flip; try alike. am. 
Qed. 

Lemma twoarrow_hypothesis_opp : forall a u v,
Category.axioms a -> 
twoarrow_hypothesis (opp a) u v =
twoarrow_hypothesis a (flip u) (flip v).
Proof.
ir. ap iff_eq; ir. 
uh H0; uhg; ee. rwi mor_opp H0. am. 
wrr mor_opp. 
rw source_flip; try alike. rw source_flip; try alike. 
am. rw target_flip; try alike. rw target_flip; try alike. 
am. 

uh H0; ee. 
wri mor_opp H0. wri mor_opp H1. 
 uhg; ee; try am. 
rwi target_flip H3; try alike. rwi target_flip H3; try alike. 
am. 
rwi source_flip H2; try alike. rwi source_flip H2; try alike. 
am. 
Qed.

Lemma twoarrow_hypothesis_opp_flip : forall a u v,
Category.axioms a -> 
twoarrow_hypothesis (opp a) (flip u) (flip v) =
twoarrow_hypothesis a u v.
Proof.
ir. 
rw twoarrow_hypothesis_opp. 
rw flip_flip. rw flip_flip. tv. am. 
Qed. 


Lemma has_coeq_has_eq : forall a u v,
Category.axioms a -> 
has_coequalizer a u v = has_equalizer (opp a) (flip u) (flip v).
Proof.
ir. ap iff_eq; ir. 
uh H0; ee. am. uhg; ee. uh H0; ee. 
rwi twoarrow_hypothesis_opp_flip H0. 
am. am. am. 
Qed. 

Lemma has_eq_has_coeq : forall a u v,
Category.axioms a -> 
has_equalizer a u v = has_coequalizer (opp a) (flip u) (flip v).
Proof.
ir. 
rw has_coeq_has_eq. rw flip_flip. rw flip_flip. 
rw opp_opp. tv. app opp_axioms. 
Qed. 

Lemma has_coequalizers_opp : forall a,
has_coequalizers (opp a) = has_equalizers a.
Proof.
ir. ap iff_eq; ir. 
uh H; ee. uhg; ee. wrr axioms_opp. 
ir. rw has_eq_has_coeq. 
ap H0. 
rw twoarrow_hypothesis_opp_flip. am. 
wrr axioms_opp. wrr axioms_opp. 

uh H; ee. uhg; ee. 
app opp_axioms. ir. 
rw has_coeq_has_eq. 
rw opp_opp. ap H0. 
wr twoarrow_hypothesis_opp. am. am. app opp_axioms. 
Qed.

Lemma has_equalizers_opp : forall a,
has_equalizers (opp a) = has_coequalizers a.
Proof.
ir. wr has_coequalizers_opp. 
rww opp_opp. 
Qed. 

Lemma has_coequalizers_has_colimits_over_opp : forall a,
Category.axioms a ->
has_coequalizers a = has_colimits_over (opp twoarrow_cat) a.
Proof.
ir. ap iff_eq; ir. assert (a = opp (opp a)). 
rww opp_opp. rw H1. 
ap has_colimits_over_opp. app opp_axioms. 
ap twoarrow_cat_axioms. 
wr  has_equalizers_has_limits_over.  
rw has_equalizers_opp. am. app opp_axioms. 

wr has_equalizers_opp. rw has_equalizers_has_limits_over.
assert (twoarrow_cat = opp (opp twoarrow_cat)).
rww opp_opp. rw H1. 
ap has_limits_over_opp. am. 
ap opp_axioms. ap twoarrow_cat_axioms. am. 
app opp_axioms. 
Qed.

Lemma mor_coequalizer : forall a u v,
has_coequalizer a u v ->
mor a (coequalizer a u v).
Proof.
ir. cp (coequalizer_hypothesis_coequalizer H). 
uh H0; ee. am. 
Qed.

Lemma source_coequalizer : forall a u v,
has_coequalizer a u v ->
source (coequalizer a u v) = target u.
Proof.
ir. cp (coequalizer_hypothesis_coequalizer H). 
uh H0; ee. am. 
Qed.

Lemma comp_coequalizer_eq : forall a u v,
has_coequalizer a u v ->
comp a (coequalizer a u v) u = comp a (coequalizer a u v) v.
Proof.
ir. cp (coequalizer_hypothesis_coequalizer H). 
uh H0; ee. am. 
Qed.

Definition coeqz_dotted a u v y :=
flip (eqz_dotted (opp a) (flip u) (flip v) (flip y)).



Lemma mor_coeqz_dotted : forall a u v y,
has_coequalizer a u v -> coequalizer_hypothesis a u v y ->
mor a (coeqz_dotted a u v y).
Proof.
ir. 
rwi has_coeq_has_eq H. 
rwi coeq_hyp_eq_hyp H0. 
uf coeqz_dotted. 
wr mor_opp. app mor_eqz_dotted. 
 uh H0; ee. 
uh H1; ee; am.  uh H0; ee. 
uh H1; ee; am. 
Qed.

Lemma source_eqz_dotted : forall a u v y,
has_coequalizer a u v -> coequalizer_hypothesis a u v y ->
source (coeqz_dotted a u v y) = target (coequalizer a u v).
Proof.
ir. 
rwi has_coeq_has_eq H. 
rwi coeq_hyp_eq_hyp H0. 
uf coeqz_dotted. 
rw source_flip. 
rw target_eqz_dotted. 
uf coequalizer. rw target_flip. 
tv. 
apply mor_arrow_like with (opp a). app mor_equalizer. 
am. am. 
apply mor_arrow_like with (opp a). 
app mor_eqz_dotted. 
uh H0; ee. 
uh H1; ee; am. uh H0; ee. 
uh H1; ee; am. 
Qed.

Lemma comp_coequalizer_coeqz_dotted : forall a u v y,
has_coequalizer a u v -> coequalizer_hypothesis a u v y ->
comp a (coeqz_dotted a u v y) (coequalizer a u v) = y.
Proof.
ir. 
rwi has_coeq_has_eq H. 
rwi coeq_hyp_eq_hyp H0. 

uf coeqz_dotted. 
uf coequalizer. ap flip_eq. wr comp_opp. 
ap comp_equalizer_eqz_dotted. am. am. 
app mor_equalizer. app mor_eqz_dotted. 
rw target_eqz_dotted. tv. am. am. 
uh H0; ee. uh H1; ee; am. 
uh H0; ee. uh H1; ee; am. 
Qed.



Lemma coeqz_dotted_comp : forall a u v z,
has_coequalizer a u v -> mor a z ->
source z = target (coequalizer a u v)  ->
coeqz_dotted a u v (comp a z (coequalizer a u v)) = z.
Proof.
ir. cp H. rwi has_coeq_has_eq H. 
assert (coequalizer_hypothesis a u v (comp a z (coequalizer a u v))).
app coequalizer_hypothesis_comp. 
app coequalizer_hypothesis_coequalizer. 

rwi coeq_hyp_eq_hyp H3. 
uf coeqz_dotted. 
assert (flip (comp a z (coequalizer a u v)) =
comp (opp a) (equalizer (opp a) (flip u) (flip v)) (flip z)).
rw comp_opp. sy; rw flip_flip. 
uf coequalizer. tv. 
app mor_equalizer. rww mor_opp. rww flip_flip. 
ufi coequalizer H1. 
rwi target_flip H1. wr H1. rww target_flip. 
alike. 
apply mor_arrow_like with (opp a). 
app mor_equalizer. 

rw H4. rw eqz_dotted_comp. rww flip_flip. am. 
rw mor_opp. rww flip_flip. 
ufi coequalizer H1. 
rwi target_flip H1. wr H1. rww target_flip. 
alike. 
apply mor_arrow_like with (opp a). 
app mor_equalizer. 
uh H0; ee; am. uh H0; ee; am. 
Qed.

(*** now we apply the result of fc_limits to 
the case of coequalizers ***********************)



Lemma has_coequalizers_functor_cat : forall a b,
Category.axioms a -> has_coequalizers b -> 
has_coequalizers (functor_cat a b).
Proof.
ir. rw has_coequalizers_has_colimits_over_opp.
cp H0.
uh H1; ee. 
rwi has_coequalizers_has_colimits_over_opp H0. 
ap has_colimits_functor_cat. am. am. 
ap opp_axioms. ap twoarrow_cat_axioms. am. am. 
ap functor_cat_axioms. am. 
uh H0; ee; am. 
Qed.



Lemma has_finite_limits_has_coequalizers : forall a,
has_finite_colimits a ->  has_coequalizers a.
Proof.
ir. rw has_coequalizers_has_colimits_over_opp. 
uh H; ee. ap H0. 
ap is_finite_cat_opp. 
ap is_finite_twoarrow_cat. uh H; ee; am. 
Qed.


End Coequalizer.

Export Coequalizer. 

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Arith.
Require Export colimits.
Require Export little_cat.
Require Export fc_limits. 
Require Export cardinal.


Module Fiprod.
Export Finite_Cat.
Export Limit.
Export Vee_Cat.

Definition fiprod_hypothesis a u v y1 y2 :=
vee_hypothesis a u v &
mor a y1 & mor a y2 
& source u = target y1 &
source v = target y2 &
source y1 = source y2 &
comp a u y1 = comp a v y2.


Definition fiprod_cone a u v y1 y2 :=
cone_create (source y1) (vee_nt a 
(id a (source y1)) (id a (source y2)) u v y1 
(comp a u y1) y2).

Lemma vertex_fiprod_cone : forall a u v y1 y2,
vertex (fiprod_cone a u v y1 y2) = source y1.
Proof.
ir. uf fiprod_cone. 
rw vertex_cone_create. tv. 
Qed.

Lemma edge_nt_fiprod_cone : forall a u v y1 y2,
edge_nt (fiprod_cone a u v y1 y2) = 
(vee_nt a 
(id a (source y1)) (id a (source y2)) u v 
y1 
(comp a u y1) y2).
Proof.
ir. uf fiprod_cone. 
rw edge_nt_cone_create. tv. 
Qed. 

Lemma edge_fiprod_cone_R : forall a u v y1 y2 (x:obsy vee_data),
edge (fiprod_cone a u v y1 y2) (R x) =
match x with 
o1 => y1 | o2 => (comp a u y1) | o3 => y2
end.
Proof.
ir. 
uf edge. 
rw edge_nt_fiprod_cone. 
rw ntrans_vee_nt_R. tv. 
Qed. 

Lemma socle_fiprod_cone : forall a u v y1 y2,
socle (fiprod_cone a u v y1 y2) = vee_functor a u v.
Proof.
ir. uf socle. 
rw edge_nt_fiprod_cone. 
rw target_vee_nt. tv. 
Qed.

Lemma cone_source_fiprod_cone : forall a u v y1 y2,
cone_source (fiprod_cone a u v y1 y2) = vee_cat.
Proof.
ir. uf cone_source. 
rw socle_fiprod_cone. rww source_vee_functor. 
Qed.

Lemma cone_target_fiprod_cone : forall a u v y1 y2,
cone_target (fiprod_cone a u v y1 y2) = a.
Proof.
ir. uf cone_target. 
rw socle_fiprod_cone. rww target_vee_functor. 
Qed.

Lemma fiprod_vee_nt_hypothesis : forall a u v y1 y2,
fiprod_hypothesis a u v y1 y2 ->
vee_nt_hypothesis a (id a (source y1)) 
(id a (source y2)) u v y1
  (comp a u y1) y2.
Proof.
ir. uh H; ee. 
uh H; ee. 
assert (ob a (source y1)). rww ob_source. 
assert (ob a (target y1)). rww ob_target. 
assert (ob a (source y2)). rww ob_source. 
assert (ob a (target y2)). rww ob_target. 

uhg; ee. 

uh H; ee; am. 
app mor_id. 
app mor_id. am. am. am.  
rww mor_comp. am. rww source_id. sy; am. 
rww source_comp. rww target_id. 
rww target_comp. rww source_id. sy; am. 
rww H4. am. 
rww assoc. 
rww right_id. app mor_id.  rww target_id. 

rww assoc. rww right_id. app mor_id. 
rww target_id. 
Qed. 

Lemma is_cone_fiprod_cone : forall a u v y1 y2,
fiprod_hypothesis a u v y1 y2 ->
is_cone (fiprod_cone a u v y1 y2).
Proof.
ir. uhg; ee. 
uf fiprod_cone. 
ap cone_like_cone_create. 
rw edge_nt_fiprod_cone. 
ap vee_nt_axioms. 
app fiprod_vee_nt_hypothesis. 
rw cone_target_fiprod_cone. 
rw vertex_fiprod_cone. uh H; ee. rww ob_source. 

rw edge_nt_fiprod_cone. 
rw source_vee_nt. 
rw cone_source_fiprod_cone. 
rw cone_target_fiprod_cone. 
rw vertex_fiprod_cone. sy; 
rw constant_functor_vee_functor. 
uh H; ee. rww H4. 
tv. 
uh H; ee. rww ob_source. 
Qed.

Definition fimap1 c := edge c (R o1').

Definition fimap2 c := edge c (R o3').

Lemma source_fimap1 : forall c,
is_cone c -> cone_source c = vee_cat ->
source (fimap1 c) =  vertex c.
Proof.
ir. uf fimap1.  rww source_edge. 
rw H0. app ob_vee_cat. 
Qed.

Lemma source_fimap2 : forall c,
is_cone c -> cone_source c = vee_cat ->
source (fimap2 c) =  vertex c.
Proof.
ir. uf fimap2. rww source_edge. 
rw H0. app ob_vee_cat. 
Qed.

Lemma fiprod_hypothesis_fimaps : 
forall a u v c, vee_hypothesis a u v -> 
is_cone c -> socle c = vee_functor a u v ->
fiprod_hypothesis a u v (fimap1 c) (fimap2 c).
Proof.
ir. 
assert (a = cone_target c).
uf cone_target. rw H1. rw target_vee_functor. 
tv. 
assert (cone_source c = vee_cat).
uf cone_source. rw H1. 
rww source_vee_functor. 
uhg. ee. am. 
uf fimap1. 
rw H2. ap mor_edge. 
rw H3. ap ob_vee_cat. 
am. 
uf fimap2. 
rw H2. ap mor_edge. 
rw H3. ap ob_vee_cat. 
am. 
uf fimap1. rw target_edge. 
rw H1. 
rw fob_vee_functor_R. tv. am. 
rw H3. ap ob_vee_cat. am. 
uf fimap2.  rw target_edge. 
rw H1. 
rw fob_vee_functor_R. tv. am. 
rw H3. ap ob_vee_cat. am. 

uf fimap1. uf fimap2. 
rw source_edge. rw source_edge. tv. 
rw H3. ap ob_vee_cat. am. 
rw H3. ap ob_vee_cat. am. 

set (k:= edge_nt c).
util (vee_nt_ntrans (u:=k)).
uf k. app edge_nt_axioms. 
uf k. rww osource_edge_nt. 
assert (otarget k = a).
uf k. rww otarget_edge_nt. sy; am. 
assert 
(fmor (source k) (catyd_arrow (d:=vee_data) a12') =
id a (vertex c)). 
uf k. 
rw source_edge_nt. 
rw fmor_constant_functor. wr H2. tv. 
rw H3. ap mor_vee_cat. am. 



assert 
(fmor (source k) (catyd_arrow (d:=vee_data) a32') =
id a (vertex c)). 
uf k. 
rw source_edge_nt. 
rw fmor_constant_functor. wr H2. tv. 
rw H3. ap mor_vee_cat. am. 

assert 
(fmor (target k) (catyd_arrow (d:=vee_data) a12') = u).
uf k. 
rw target_edge_nt. 
rw H1. rw fmor_vee_functor_catyd_arrow. 
tv. am. 

assert 
(fmor (target k) (catyd_arrow (d:=vee_data) a32') = v).
uf k. 
rw target_edge_nt. 
rw H1. rw fmor_vee_functor_catyd_arrow. 
tv. am. 

util (vee_nt_hypothesis_ntrans (u:=k)).
uf k. app edge_nt_axioms. uf k. 
rw osource_edge_nt. am. am. 
rwi H6 H10. 
rwi H5 H10. rwi H7 H10. rwi H8 H10. 
rwi H9 H10. 

assert (ntrans k (R o1') = (fimap1 c)).
uf fimap1. uf edge.
tv. 

assert (ntrans k (R o3') = (fimap2 c)).
uf fimap2. uf edge.
tv. 

rwi H11 H10. 
set (m:= ntrans k (R o2')).
assert (m = ntrans k (R o2')). tv. rwi H12 H10.
wri H13 H10. uh H10; ee. 
wr H29. wr H30. 
reflexivity. 
Qed.

Lemma fiprod_cone_eq : forall a u v c,
vee_hypothesis a u v -> 
is_cone c -> socle c = vee_functor a u v ->
c = fiprod_cone a u v (fimap1 c) (fimap2 c).
Proof.
ir. 
assert (a = cone_target c).
uf cone_target. rw H1. rw target_vee_functor. 
tv. 
assert (cone_source c = vee_cat).
uf cone_source. rw H1. 
rww source_vee_functor. 

set (k:= edge_nt c).
util (vee_nt_ntrans (u:=k)).
uf k. app edge_nt_axioms. 
uf k. rww osource_edge_nt. 
assert (otarget k = a).
uf k. rww otarget_edge_nt. sy; am. 
assert 
(fmor (source k) (catyd_arrow (d:=vee_data) a12') =
id a (vertex c)). 
uf k. 
rw source_edge_nt. 
rw fmor_constant_functor. wr H2. tv. 
rw H3. ap mor_vee_cat. am. 

assert 
(fmor (source k) (catyd_arrow (d:=vee_data) a32') =
id a (vertex c)). 
uf k. 
rw source_edge_nt. 
rw fmor_constant_functor. wr H2. tv. 
rw H3. ap mor_vee_cat. am. 

assert 
(fmor (target k) (catyd_arrow (d:=vee_data) a12') = u).
uf k. 
rw target_edge_nt. 
rw H1. rw fmor_vee_functor_catyd_arrow. 
tv. am. 

assert 
(fmor (target k) (catyd_arrow (d:=vee_data) a32') = v).
uf k. 
rw target_edge_nt. 
rw H1. rw fmor_vee_functor_catyd_arrow. 
tv. am. 

rwi H5 H4. rwi H6 H4. rwi H7 H4. rwi H8 H4. 
rwi H9 H4. 


transitivity (cone_create (vertex c) k).
uh H0; ee. uh H0; ee. 
sy; am. 
uf fiprod_cone. 
rw source_fimap1. 
rw source_fimap2. 
ap uneq. wr H4. 

assert (lem1 : ntrans k (R o1') = (fimap1 c)).
uf fimap1. uf edge.
tv. 
assert (lem2 : ntrans k (R o3') = (fimap2 c)).
uf fimap2. uf edge.
tv. 
assert (ntrans k (R o2') = comp a u (fimap1 c)).
uf fimap1. 


util (vee_nt_hypothesis_ntrans (u:=k)).
uf k. app edge_nt_axioms. uf k. 
rw osource_edge_nt. am. am. 
rwi H6 H10. 
rwi H5 H10. rwi H7 H10. rwi H8 H10. 
rwi H9 H10. 



rwi lem1 H10. rwi lem2 H10. 
set (m:= ntrans k (R o2')).
assert (m = ntrans k (R o2')). tv. wri H11 H10.
uh H10; ee. uf edge. 
change (m=comp a u (ntrans k (R o1'))). 
rw lem1. wr H27. 
rw right_id. tv. rw H2. app ob_vertex. 
am. rw H21. rw target_id. tv. 
rw H2; app ob_vertex. tv. 

rw lem1. rw lem2. rw H10. reflexivity. am. 
am. am. am.  
Qed.



Lemma fimap1_fiprod_cone : forall a u v y1 y2,
fimap1 (fiprod_cone a u v y1 y2) = y1.
Proof.
ir. 
uf fimap1. 
rw edge_fiprod_cone_R. tv. 
Qed.

Lemma fimap2_fiprod_cone : forall a u v y1 y2,
fimap2 (fiprod_cone a u v y1 y2) = y2.
Proof.
ir. 
uf fimap2. 
rw edge_fiprod_cone_R. tv. 
Qed.

Lemma fimap1_cone_compose : forall c z,
is_cone c -> cone_source c = vee_cat ->
cone_composable c z ->
fimap1 (cone_compose c z) = 
(comp (cone_target c) (fimap1 c) z).
Proof.
ir. 
uf fimap1. 
rw edge_cone_compose. tv. 
rw H0. ap ob_vee_cat. am.  
Qed.

Lemma fimap2_cone_compose : forall c z,
is_cone c -> cone_source c = vee_cat ->
cone_composable c z ->
fimap2 (cone_compose c z) = 
(comp (cone_target c) (fimap2 c) z).
Proof.
ir. 
uf fimap2. 
rw edge_cone_compose. tv. 
rw H0. ap ob_vee_cat. am.  
Qed.

Definition veefirst c := 
(fmor (socle c) (catyd_arrow (d:=vee_data) a12')).
Definition veesecond c :=
(fmor (socle c) (catyd_arrow (d:=vee_data) a32')).

Lemma fiprod_hypothesis_vee_fimaps : forall c,
is_cone c -> cone_source c = vee_cat ->
fiprod_hypothesis (cone_target c) (veefirst c) (veesecond c)
(fimap1 c) (fimap2 c).
Proof.
ir. util (fiprod_hypothesis_fimaps (a:= cone_target c)
(u:= veefirst c) (v:= veesecond c) (c:=c)).
uf veefirst. uf veesecond. 
uf cone_target. ap functor_vee_hypothesis. 
app socle_axioms. am. am. 
uf cone_target. 
uf veefirst. uf veesecond. ap functor_vee_eq.
app socle_axioms. am. 
am. 
Qed.

Lemma fiprod_cone_eq2 : forall c,
is_cone c -> cone_source c = vee_cat ->
c = fiprod_cone (cone_target c) (veefirst c) (veesecond c)
(fimap1 c) (fimap2 c).
Proof.
ir. 
util (fiprod_cone_eq (a:= cone_target c)
(u:= veefirst c) (v:= veesecond c) (c:=c)).
uf veefirst. uf veesecond. 
uf cone_target. ap functor_vee_hypothesis. 
app socle_axioms. am. am. 
uf cone_target. 
uf veefirst. uf veesecond. ap functor_vee_eq.
app socle_axioms. am. 
am. 
Qed.


Lemma fimaps_extensionality : forall a b,
is_cone a -> is_cone b -> cone_source a = vee_cat 
-> socle a = socle b -> fimap1 a = fimap1 b ->
fimap2 a = fimap2 b -> a = b.
Proof.
ir. 
assert (cone_source b = vee_cat).
uf cone_source. wr H2. am. 
util (fiprod_cone_eq2 (c:= a)). 
am. am. 
util (fiprod_cone_eq2 (c:= b)). 
am. am. rw H6; rw H7. 
assert (veefirst a = veefirst b).
uf veefirst. rww H2. 
assert (veesecond a = veesecond b).
uf veesecond. rw H2. reflexivity. 
rw H3; rw H8; rw H9. 
assert (cone_target a = cone_target b).
uf cone_target. rww H2. rw H10. rw H4. 
reflexivity. 
Qed.

Lemma cone_compose_fiprod_cone : forall a u v y1 y2 z,
fiprod_hypothesis a u v y1 y2 ->
mor a z -> source y1 = target z -> 
cone_compose (fiprod_cone a u v y1 y2) z = 
fiprod_cone a u v (comp a y1 z) (comp a y2 z).
Proof.
ir. 

assert (lem1: fiprod_hypothesis a u v 
(comp a y1 z) (comp a y2 z)).
uh H; uhg; ee. am. rww mor_comp. 
rww mor_comp. wrr H6. rww target_comp. 
rww target_comp. wrr H6. 
rww source_comp. rww source_comp. wrr H6. 

wr assoc. 
rw H7. rww assoc. uh H; ee; am. wrr H6. 
uh H; ee; am. am. am. am. am. tv. 

assert (lem2 : cone_composable (fiprod_cone a u v y1 y2) z).
uhg; ee. 
app  is_cone_fiprod_cone. 
rww cone_target_fiprod_cone. 
rww vertex_fiprod_cone. sy; am.


ap fimaps_extensionality. 
rww is_cone_cone_compose. 
app is_cone_fiprod_cone. 
rw cone_source_cone_compose. rww cone_source_fiprod_cone. 
rw socle_cone_compose. 
rww socle_fiprod_cone. rww socle_fiprod_cone. 
rww fimap1_cone_compose. 
rww cone_target_fiprod_cone. 
rww fimap1_fiprod_cone. 
rww fimap1_fiprod_cone. 
app is_cone_fiprod_cone. 
rww cone_source_fiprod_cone. 
rww fimap2_cone_compose. 
rww cone_target_fiprod_cone. 
rww fimap2_fiprod_cone. 
rww fimap2_fiprod_cone. 
app is_cone_fiprod_cone. 
rww cone_source_fiprod_cone. 
Qed.

Lemma cone_composable_fiprod_cone : forall a u v y1 y2 z,
fiprod_hypothesis a u v y1 y2 -> mor a z ->
source y1 = target z -> 
cone_composable (fiprod_cone a u v y1 y2) z.
Proof.
ir. uhg; ee. app is_cone_fiprod_cone. 
rww cone_target_fiprod_cone. 
rww vertex_fiprod_cone. sy; am. 
Qed. 

Lemma is_uni_fiprod_cone : forall a u v y1 y2,
fiprod_hypothesis a u v y1 y2 ->
is_uni (fiprod_cone a u v y1 y2) =
(forall z z', mor a z -> mor a z' ->
source y1 = target z -> source y1 = target z' ->
comp a y1 z = comp a y1 z' -> 
comp a y2 z = comp a y2 z'-> z = z').
Proof.
ir. ap iff_eq; ir. 
uh H0. ee. ap H7.
app cone_composable_fiprod_cone.
app cone_composable_fiprod_cone.
rw cone_compose_fiprod_cone. 
sy; rw cone_compose_fiprod_cone.
sy. rw H5. rw H6. tv. am. am. am. am. am. am. 

uhg. ee. app is_cone_fiprod_cone. 
ir. 
cp H1; cp H2. uh H4; uh H5; ee. 
rwi cone_target_fiprod_cone H8. 
rwi cone_target_fiprod_cone H6. 
rwi vertex_fiprod_cone H9. 
rwi vertex_fiprod_cone H7. 

app H0. sy; am. sy; am. 
rwi cone_compose_fiprod_cone H3. 
tv. 
transitivity 
(fimap1 (fiprod_cone a u v (comp a y1 u0) (comp a y2 u0))).
rw fimap1_fiprod_cone. tv. 
rw H3. 
rw fimap1_cone_compose. 
rw cone_target_fiprod_cone. 
rw fimap1_fiprod_cone. tv. 
am. rww cone_source_fiprod_cone. 
am. am. am. sy; am. 


transitivity 
(fimap2 (cone_compose (fiprod_cone a u v y1 y2) u0)).
rw cone_compose_fiprod_cone.
rw fimap2_fiprod_cone. tv. am. am. sy; am. 
rw H3. 
rw fimap2_cone_compose. 
rw cone_target_fiprod_cone. 
rw fimap2_fiprod_cone. tv. 
am. rww cone_source_fiprod_cone. 
am. 
Qed.

Lemma is_versal_fiprod_cone : forall a u v y1 y2,
fiprod_hypothesis a u v y1 y2 ->
is_versal (fiprod_cone a u v y1 y2) =
(forall z1 z2, fiprod_hypothesis a u v z1 z2 -> 
(exists w, (mor a w & source y1 = target w &
comp a y1 w = z1 & comp a y2 w = z2))).
Proof.
ir. ap iff_eq; ir. 
uh H0; ee. 
util (H2 (fiprod_cone a u v z1 z2)). 
app is_cone_fiprod_cone. 
rww socle_fiprod_cone; sy; 
rww socle_fiprod_cone. 
nin H3. ee. 
cp H3. uh H5; ee. 
rwi cone_target_fiprod_cone H6. 
rwi vertex_fiprod_cone H7. 
rwi cone_compose_fiprod_cone H4. 
sh x; ee. am. sy; am. 
transitivity 
(fimap1 (fiprod_cone a u v (comp a y1 x) (comp a y2 x))).
rw fimap1_fiprod_cone. tv. 
rw H4. rw fimap1_fiprod_cone. tv. 

transitivity 
(fimap2 (fiprod_cone a u v (comp a y1 x) (comp a y2 x))).
rw fimap2_fiprod_cone. tv. 
rw H4. rw fimap2_fiprod_cone. tv. am. am. sy; am. 


assert (lem1: fiprod_hypothesis a u v y1 y2). 
am. 
uh H; uhg; ee; try am. app is_cone_fiprod_cone. 
ir. 
rwi socle_fiprod_cone H8. 
cp (fiprod_cone_eq H H7 H8). 
cp (fiprod_hypothesis_fimaps H H7 H8). 

util (H0 (fimap1 b) (fimap2 b)). am. 
nin H11. ee. sh x; ee. 
app cone_composable_fiprod_cone. 
rww cone_compose_fiprod_cone. rw H13. 
rw H14. sy; am. 
Qed.

Definition is_fiprod a u v y1 y2 :=
fiprod_hypothesis a u v y1 y2 &
is_limit (fiprod_cone a u v y1 y2).

Lemma show_is_fiprod : forall a u v y1 y2 ,
fiprod_hypothesis a u v y1 y2 ->
(forall z z', mor a z -> mor a z' ->
source y1 = target z -> source y1 = target z' ->
comp a y1 z = comp a y1 z' -> comp a y2 z = comp a y2 z' 
-> z = z') ->
(forall z1 z2, fiprod_hypothesis a u v z1 z2 -> 
(exists w, (mor a w & source y1 = target w &
comp a y1 w = z1 & comp a y2 w = z2))) ->
is_fiprod a u v y1 y2.
Proof.
ir. uhg; ee. am. 
uhg. ee. rww is_uni_fiprod_cone. 
rww is_versal_fiprod_cone. 
Qed.


Definition has_fiprod a u v :=
vee_hypothesis a u v &
has_limit (vee_functor a u v).

Lemma has_fiprod_rw : forall a u v,
has_fiprod a u v = (exists y1, exists y2, is_fiprod a u v y1 y2).
Proof.
ir. ap iff_eq; ir. 
uh H; ee. uh H0. 
nin H0. uh H0; ee. sh (fimap1 x).
sh (fimap2 x). uhg; ee. 
ap fiprod_hypothesis_fimaps. am. 
app is_limit_is_cone. am. 

assert (is_cone x). 
app is_limit_is_cone.
util (fiprod_cone_eq (a:=a) (u:=u) (v:=v) (c:=x)). 
am. am. am. 
wr H3. am. 

nin H. nin H. uhg; ee. 
uh H; ee. uh H; ee; am. 
uh H; ee. 
uhg. 
sh (fiprod_cone a u v x x0). 
uhg; ee. am. 
rww socle_fiprod_cone.  
Qed.

Definition has_fiprods a :=
Category.axioms a &
(forall u v, vee_hypothesis a u v -> 
has_fiprod a u v).


Definition fipr1 a u v := 
fimap1 (limit (vee_functor a u v)).

Definition fipr2 a u v := 
fimap2 (limit (vee_functor a u v)).

Lemma fiprod_hypothesis_fiprod : forall a u v,
has_fiprod a u v ->
fiprod_hypothesis a u v (fipr1 a u v) (fipr2 a u v).
Proof.
ir. uf fipr1; uf fipr2. 
app fiprod_hypothesis_fimaps. 
uh H; ee; am. 
ap is_limit_is_cone. ap is_limit_limit.
uh H; ee; am. 
rw socle_limit. tv. uh H; ee; am. 
Qed.

Lemma fiprod_hypothesis_comp : forall a u v y1 y2 z,
fiprod_hypothesis a u v y1 y2 -> mor a z ->
source y1 = target z  ->
fiprod_hypothesis a u v (comp a y1  z) (comp a y2 z).
Proof.
ir. uh H; uhg; ee. am. rww mor_comp. 
rww mor_comp. wrr H6. rww target_comp. 
rww target_comp. wrr H6. 
rww source_comp. rww source_comp. wrr H6. 
wrr assoc. rw H7. rww assoc.
uh H; ee. am. wrr H6. uh H; ee; am. 
Qed.

Lemma is_fiprod_fiprod : forall a u v,
has_fiprod a u v ->
is_fiprod a u v (fipr1 a u v) (fipr2 a u v).
Proof.
ir. uhg; ee. 
app fiprod_hypothesis_fiprod. 
uf fipr1; uf fipr2. 
wr fiprod_cone_eq. 
ap is_limit_limit. uh H; ee; am. 
uh H; ee. am. 
ap is_limit_is_cone. ap is_limit_limit. uh H; ee; am. 
rw socle_limit. tv. uh H; ee; am. 
Qed.

Lemma has_fiprods_has_fiprod : forall a u v,
has_fiprods a -> vee_hypothesis a u v->
has_fiprod a u v.
Proof.
ir. uh H; ee. ap H1. am. 
Qed.

Lemma has_fiprods_has_limits_over : forall a,
Category.axioms a ->
has_fiprods a = has_limits_over vee_cat a.
Proof.
ir. ap iff_eq; ir. 
uhg. ir. uh H0. ee. 
util (H4 (fmor f (catyd_arrow a12')) (fmor f (catyd_arrow a32'))).
wr H3. ap functor_vee_hypothesis. am. 
am. 
uh H5. ee. wri H3 H6. 
rww functor_vee_eq. 

uh H0. uhg; ee. am. 
ir. uhg; ee; try am. 
ap H0. 
app vee_functor_axioms. 
rww source_vee_functor. 
rww target_vee_functor. 
Qed.

Lemma mor_fipr1 : forall a u v,
has_fiprod a u v ->
mor a (fipr1 a u v).
Proof.
ir. cp (is_fiprod_fiprod H). 
uh H0; ee. 
uh H0; ee. am. 
Qed.

Lemma mor_fipr2 : forall a u v,
has_fiprod a u v ->
mor a (fipr2 a u v).
Proof.
ir. cp (is_fiprod_fiprod H). 
uh H0; ee. 
uh H0; ee. am. 
Qed.

Lemma target_fipr1 : forall a u v,
has_fiprod a u v ->
target (fipr1 a u v) = source u.
Proof.
ir. cp (is_fiprod_fiprod H). 
uh H0; ee. 
uh H0; ee. sy; am. 
Qed.

Lemma target_fipr2 : forall a u v,
has_fiprod a u v ->
target (fipr2 a u v) = source v.
Proof.
ir. cp (is_fiprod_fiprod H). 
uh H0; ee. 
uh H0; ee. sy; am. 
Qed.

Lemma source_fipr2 : forall a u v,
has_fiprod a u v ->
source (fipr2 a u v) = source (fipr1 a u v).
Proof.
ir. cp (is_fiprod_fiprod H). 
uh H0; ee. 
uh H0; ee. sy; am. 
Qed. 

Lemma comp_fiprod_eq : forall a u v,
has_fiprod a u v ->
comp a u (fipr1 a u v) = comp a v (fipr2 a u v).
Proof.
ir. cp (is_fiprod_fiprod H). 
uh H0; ee. 
uh H0; ee. am. 
Qed.

Definition fipr_dotted a u v y1 y2 :=
dotted (fiprod_cone a u v y1 y2).

Lemma fiprod_cone_fiprod : forall a u v,
has_fiprod a u v ->
fiprod_cone a u v (fipr1 a u v) (fipr2 a u v) =
limit (vee_functor a u v).
Proof.
ir. 
uf fipr1; uf fipr2. 
wr fiprod_cone_eq. tv. uh H; ee; am. 
ap is_limit_is_cone. ap is_limit_limit. 
uh H; ee; am. 
rw socle_limit. tv. uh H; ee; am. 
Qed. 

Lemma cone_composable_fipr_dotted : forall a u v y1 y2,
has_fiprod a u v -> fiprod_hypothesis a u v y1 y2 ->
cone_composable (fiprod_cone a u v (fipr1 a u v) (fipr2 a u v))
(fipr_dotted a u v y1 y2).
Proof.
ir. 
uf fipr_dotted. 
rw fiprod_cone_fiprod. 
assert (vee_functor a u v =
socle (fiprod_cone a u v y1 y2)). 
rww socle_fiprod_cone. rw H1. 
ap cone_composable_dotted. 
app is_cone_fiprod_cone. 
rw socle_fiprod_cone. uh H; ee; am. 
am. 
Qed. 

Lemma cone_compose_fipr_dotted : forall a u v y1 y2,
has_fiprod a u v -> fiprod_hypothesis a u v y1 y2 ->
cone_compose (fiprod_cone a u v (fipr1 a u v) (fipr2 a u v))
(fipr_dotted a u v y1 y2) = fiprod_cone a u v y1 y2.
Proof.
ir. 
uf fipr_dotted. 
rw fiprod_cone_fiprod. 
assert (vee_functor a u v =
socle (fiprod_cone a u v y1 y2)). 
rww socle_fiprod_cone. rw H1. 
ap cone_compose_dotted. 
app is_cone_fiprod_cone. 
rw socle_fiprod_cone. uh H; ee; am. am. 
Qed. 

Lemma fipr_dotted_uni : forall a u v y1 y2 r,
has_fiprod a u v -> fiprod_hypothesis a u v y1 y2 ->
cone_composable (fiprod_cone a u v (fipr1 a u v) (fipr2 a u v)) r ->
cone_compose (fiprod_cone a u v (fipr1 a u v) (fipr2 a u v)) r =
fiprod_cone a u v y1 y2 -> 
fipr_dotted a u v y1 y2 = r.
Proof.
ir. uf fipr_dotted. 
wr H2. 
rw fiprod_cone_fiprod. ap dotted_unique. 
ap vee_functor_axioms. uh H0; ee; am. 
uh H; ee; am. 
wr fiprod_cone_fiprod. am. am. am. 
Qed. 

Lemma mor_fipr_dotted : forall a u v y1 y2,
has_fiprod a u v -> fiprod_hypothesis a u v y1 y2 ->
mor a (fipr_dotted a u v y1 y2).
Proof.
ir. 
cp (cone_composable_fipr_dotted H H0). 
uh H1; ee. rwi cone_target_fiprod_cone H2. am. 
Qed.

Lemma target_fipr_dotted : forall a u v y1 y2,
has_fiprod a u v -> fiprod_hypothesis a u v y1 y2 ->
target (fipr_dotted a u v y1 y2) = source (fipr1 a u v).
Proof.
ir. 
cp (cone_composable_fipr_dotted H H0). 
uh H1; ee. rwi vertex_fiprod_cone H3. am. 
Qed.

Lemma comp_fipr1_fipr_dotted : forall a u v y1 y2,
has_fiprod a u v -> fiprod_hypothesis a u v y1 y2 ->
comp a (fipr1 a u v) (fipr_dotted a u v y1 y2) = y1.
Proof.
ir. 
cp (cone_compose_fipr_dotted H H0). 
transitivity (fimap1 (fiprod_cone a u v y1 y2)).
wr H1. 
rw fimap1_cone_compose. 
rw cone_target_fiprod_cone. 
rw fimap1_fiprod_cone. tv. 
ap is_cone_fiprod_cone. 

ap fiprod_hypothesis_fiprod. am. 
rww cone_source_fiprod_cone. 
app cone_composable_fipr_dotted. 
rww fimap1_fiprod_cone.
Qed.

Lemma comp_fipr2_fipr_dotted : forall a u v y1 y2,
has_fiprod a u v -> fiprod_hypothesis a u v y1 y2 ->
comp a (fipr2 a u v) (fipr_dotted a u v y1 y2) = y2.
Proof.
ir. 
cp (cone_compose_fipr_dotted H H0). 
transitivity (fimap2 (fiprod_cone a u v y1 y2)).
wr H1. 
rw fimap2_cone_compose. 
rw cone_target_fiprod_cone. 
rw fimap2_fiprod_cone. tv. 
ap is_cone_fiprod_cone. 
app fiprod_hypothesis_fiprod. 
rww cone_source_fiprod_cone. 
app cone_composable_fipr_dotted. 
rww fimap2_fiprod_cone.
Qed.

Lemma fipr_dotted_comp : forall a u v z,
has_fiprod a u v -> mor a z ->
source (fipr1 a u v) = target z ->
fipr_dotted a u v (comp a (fipr1 a u v) z)
(comp a (fipr2 a u v) z) = z.
Proof.
ir. 
assert (fiprod_hypothesis a u v (fipr1 a u v) (fipr2 a u v)).
app fiprod_hypothesis_fiprod. 
ap fipr_dotted_uni. am. 
app fiprod_hypothesis_comp. 
uhg; ee. app is_cone_fiprod_cone. 
rww cone_target_fiprod_cone. 
rww vertex_fiprod_cone. sy; am. 
rw cone_compose_fiprod_cone. tv. 
am. am. am. 
Qed.

(*** now we apply the result of fc_limits to 
the case of fiprods ***********************)

Lemma has_fiprods_functor_cat : forall a b,
Category.axioms a -> has_fiprods b -> 
has_fiprods (functor_cat a b).
Proof.
ir. rw has_fiprods_has_limits_over.
cp H0.
uh H1; ee. 
rwi has_fiprods_has_limits_over H0. 
ap has_limits_functor_cat. am. am. 
ap vee_cat_axioms. am. am. 
ap functor_cat_axioms. am. 
uh H0; ee; am. 
Qed.








Lemma has_finite_limits_has_fiprods : forall a,
has_finite_limits a ->  has_fiprods a.
Proof.
ir. rw has_fiprods_has_limits_over. 
uh H; ee. ap H0. 
ap is_finite_vee_cat. uh H; ee; am. 
Qed.

End Fiprod. 


Export Fiprod.


(*** we should be able to more or less recopy fiprod to
get a module Fiprod for fiber products; then also 
dualize to get cofiprods and cofiber products. The other
main type of limits and colimits we need to do are direct
products and coproducts ... *****************************)

Module Cofiprod. 

(**** we do this module by dualizing the module
fiprod, rather than by relying on colimits *******)

Definition covee_hypothesis a u v :=
mor a u & mor a v & 
source u = source v.



Definition cofiprod_hypothesis a u v y1 y2 :=
covee_hypothesis a u v &
mor a y1 & mor a y2 & source y1 = target u &
source y2 = target v &
comp a y1 u = comp a y2 v.

Lemma cofi_hyp_fi_hyp : forall a u v y1 y2,
Category.axioms a -> 
cofiprod_hypothesis a u v y1 y2 = 
fiprod_hypothesis (opp a) (flip u) (flip v) (flip y1) (flip y2).
Proof.
ir. ap iff_eq; ir. 
uh H0; uhg; ee. 
uh H0; uhg; ee. 
rww mor_opp. rww flip_flip. 
rww mor_opp. rww flip_flip. 
rw target_flip. rw target_flip. 
am. alike. alike. 
rww mor_opp. rww flip_flip.
rw mor_opp; rww flip_flip.
rw target_flip; try alike. 
rw source_flip; try alike. sy; am. uh H0; ee; alike.
rw target_flip; try alike. 
rw source_flip; try alike. sy; am. uh H0; ee; alike.
rw source_flip; try alike. 
rw source_flip; try alike. 
transitivity (target (comp a y1 u)). 
rw target_comp. tv. am. uh H0; ee; am. am. 
rw H5. rww target_comp. uh H0; ee; am. 

rw comp_opp. 
rw comp_opp. rw flip_flip. 
rw flip_flip. rw flip_flip. rw flip_flip. ap uneq. am. 
rww mor_opp; rww flip_flip. 
uh H0; ee; am. 
rww mor_opp; rww flip_flip. 
rww target_flip; try alike. 
rww source_flip; try alike.
uh H0; ee. sy; am. 
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
rwi mor_opp H7. 
rwi flip_flip H7. am. 
wr target_flip; try alike. 
rw H8. rw target_flip; try alike. tv. 
rwi mor_opp H1. rwi flip_flip H1; am. 
rwi mor_opp H2. rwi flip_flip H2; am. 

wr source_flip; try alike. rw H3. 
rww target_flip; try alike. 
rwi mor_opp H0. 
rwi flip_flip H0. alike.  wr target_flip; try alike. 
wr H4. uh H9; ee. 
rww source_flip; try alike. 

rwi comp_opp H6. rwi flip_flip H6. 
rwi flip_flip H6. ap flip_eq. 
rw H6. 
rw comp_opp. rw flip_flip. rw flip_flip. tv. 
am. am. am. am. am. am. 
Qed. 





Definition is_cofiprod a u v y1 y2 :=
Category.axioms a & 
is_fiprod (opp a) (flip u) (flip v) (flip y1) (flip y2).


Lemma show_is_cofiprod : forall a u v y1 y2,
Category.axioms a -> 
cofiprod_hypothesis a u v y1 y2 ->
(forall z z', mor a z -> mor a z' ->
source z = target y1 -> source z' = target y1 ->
comp a z y1 = comp a z' y1  -> comp a z y2 = comp a z' y2
-> z = z') ->
(forall z1 z2, cofiprod_hypothesis a u v z1 z2 -> 
(exists w, (mor a w & source w = target y1 &
comp a w y1 = z1 & comp a w y2 = z2))) ->
is_cofiprod a u v y1 y2.
Proof.
ir. 
assert (lem1 : target y1 = target y2).
uh H0. ee. transitivity (target (comp a y1 u)).
rww target_comp. uh H0; ee; am. 
rw H7. rww target_comp. uh H0; ee; am. 

uhg; ee. am. 
ap show_is_fiprod. 
wr cofi_hyp_fi_hyp. am. am. 
ir. set (z1:=flip z). set (z2 := flip z'). 
assert (z1 = z2). ap H1. 
uf z1. rwi mor_opp H3. am. 
rwi mor_opp H4. am.  
uf z1. rw source_flip; try alike. wr H5. 
rww source_flip; try alike. uh H0; ee. 
alike. 
uf z2. rw source_flip; try alike. wr H6. 
rww source_flip; try alike. uh H0; ee. 
alike. uf z1; uf z2. 
rwi comp_opp H7. 
rwi flip_flip H7. 
rwi comp_opp H7. rwi flip_flip H7. 
rwi comp_opp H8. 
rwi flip_flip H8. 
rwi comp_opp H8. rwi flip_flip H8. 

ap flip_eq. 
am.  
rww mor_opp. rw flip_flip. 
uh H0; ee; am. 
am. 
uh H0; ee. 
rw source_flip. 
wr lem1. 
rwi source_flip H6. am. alike. alike. 
rww mor_opp. rw flip_flip.
uh H0; ee; am. am. 
rw source_flip; try alike. wr lem1. 
rwi source_flip H5. am. uh H0; ee; alike. 
uh H0; ee; alike. 
rw mor_opp; rww flip_flip. uh H0; ee; am. 
am. am. rw mor_opp; rw flip_flip; uh H0; ee; am. 
am. am. 


uf z1; uf z2. 
rwi comp_opp H7. 
rwi flip_flip H7. 
rwi comp_opp H7. rwi flip_flip H7. 
rwi comp_opp H8. 
rwi flip_flip H8. 
rwi comp_opp H8. rwi flip_flip H8. 

ap flip_eq. 
am.  
rww mor_opp. rw flip_flip. 
uh H0; ee; am. 
am. 
uh H0; ee. 
rw source_flip. 
wr lem1. 
rwi source_flip H6. am. alike. alike. 
rww mor_opp. rw flip_flip.
uh H0; ee; am. am. 
rw source_flip; try alike. wr lem1. 
rwi source_flip H5. am. uh H0; ee; alike. 
uh H0; ee; alike. 
rw mor_opp; rww flip_flip. uh H0; ee; am. 
am. am. rw mor_opp; rw flip_flip; uh H0; ee; am. 
am. am. ap flip_eq. am.  

ir. 
cp H3. set (z1' := flip z1).
assert (z1= flip z1'). 
uf z1'; rww flip_flip. rwi H5 H4.
set (z2' := flip z2).
assert (z2= flip z2'). 
uf z2'; rww flip_flip. rwi H6 H4.

wri cofi_hyp_fi_hyp H4. 
nin (H2 z1' z2' H4). ee. 
sh (flip x). ee. rww mor_opp. 
rww flip_flip. 
rw source_flip. rw target_flip. 
sy; am. alike. uh H0; ee; alike. 
rw comp_opp. 
rw flip_flip. rw flip_flip. ap flip_eq. 
rw flip_flip. exact H9.  
rww mor_opp. rw flip_flip. uh H0; ee; am. 
rww mor_opp. rww flip_flip. 
rw source_flip. rw target_flip. sy; am. 
alike. uh H0; ee; alike. 
rw comp_opp. rw flip_flip. rw flip_flip. 
ap flip_eq. rw flip_flip. exact H10. 
rw mor_opp; rw flip_flip. uh H0; ee; am. 
rw mor_opp; rww flip_flip. 
rw source_flip. rw target_flip. 
rww H8. sy; am. alike. uh H0; ee; alike. 
am. 
Qed.


Definition has_cofiprod a u v :=
covee_hypothesis a u v &
has_fiprod (opp a) (flip u) (flip v).


Lemma has_cofiprod_rw : forall a u v,
has_cofiprod a u v = 
(exists y1, exists y2, is_cofiprod a u v y1 y2).
Proof.
ir. ap iff_eq; ir. 
uh H; ee. 
rwi has_fiprod_rw H0. 
nin H0. nin H0. sh (flip x). sh (flip x0).

uhg; ee. uh H; ee. uh H; ee; am. rw flip_flip. 
rw flip_flip. am. 
nin H. nin H. 
assert (cofiprod_hypothesis a u v x x0).
rw cofi_hyp_fi_hyp. 
uh H; ee. uh H0; ee. 
am. uh H; ee. am. 

uhg; ee. uh H0; ee; am. 
uh H; ee. 
rw has_fiprod_rw. sh (flip x).
sh (flip x0). am. 
Qed.

Definition has_cofiprods a :=
Category.axioms a &
(forall u v, covee_hypothesis a u v -> 
has_cofiprod a u v).


Definition cofipr1 a u v := 
flip (fipr1 (opp a) (flip u) (flip v)).

Definition cofipr2 a u v := 
flip (fipr2 (opp a) (flip u) (flip v)).

Lemma cofiprod_hypothesis_cofiprod : forall a u v,
has_cofiprod a u v ->
cofiprod_hypothesis a u v (cofipr1 a u v) (cofipr2 a u v).
Proof.
ir. uf cofipr1; uf cofipr2. 
rw cofi_hyp_fi_hyp. rw flip_flip. 
rw flip_flip. 
ap fiprod_hypothesis_fiprod. 
uh H. ee; am. uh H; ee. uh H; ee. uh H; ee; am. 
Qed.

Lemma cofiprod_hypothesis_comp : forall a u v y1 y2 z,
cofiprod_hypothesis a u v y1 y2 -> mor a z ->
source z = target y1  ->
cofiprod_hypothesis a u v (comp a z y1) (comp a z y2).
Proof.
ir. 
rw cofi_hyp_fi_hyp. 
rwi cofi_hyp_fi_hyp H. 
assert (flip (comp a z y1) =
comp (opp a) (flip y1) (flip z)). 
rw comp_opp. 
rw flip_flip. rww flip_flip. 
uh H; ee; am. 
rww mor_opp. 
rww flip_flip. 

rw source_flip; try alike. rw target_flip. 
sy; am. alike. uh H; ee. 
rwi mor_opp H2. rwi flip_flip H2; alike. 


assert (flip (comp a z y2) =
comp (opp a) (flip y2) (flip z)). 
rw comp_opp. 
rw flip_flip. rww flip_flip. 
uh H; ee; am. 
rww mor_opp. 
rww flip_flip. 

uh H; ee. wr H7.

rw source_flip; try alike. rw target_flip. 
sy; am. alike. 
rwi mor_opp H3. rwi flip_flip H3; alike. 



rw H2; rw H3. ap fiprod_hypothesis_comp. am. 
rww mor_opp. rww flip_flip.  

rw source_flip; try alike. rw target_flip. 
sy; am. alike. uh H; ee. 
rwi mor_opp H4. rwi flip_flip H4; alike. 
uh H0; ee; am. uh H0; ee; am. 
Qed.

Lemma is_cofiprod_cofiprod : forall a u v,
has_cofiprod a u v ->
is_cofiprod a u v (cofipr1 a u v) (cofipr2 a u v).
Proof.
ir. assert (Category.axioms a).
uh H; ee. uh H; ee. uh H; ee; am. 
uhg; ee; try am. 
uf cofipr1; uf cofipr2. rw flip_flip. 
rw flip_flip. 
ap is_fiprod_fiprod. uh H; ee. am. 
Qed.

Lemma has_cofiprods_has_cofiprod : forall a u v,
has_cofiprods a -> covee_hypothesis a u v->
has_cofiprod a u v.
Proof.
ir. uh H; ee. ap H1. am. 
Qed.

Lemma covee_hypothesis_opp1 : forall a u v,
Category.axioms a -> 
covee_hypothesis a u v ->
vee_hypothesis (opp a) (flip u) (flip v).
Proof.
ir. uh H0; ee. uhg; ee. 
rww mor_opp. rww flip_flip.  
rww mor_opp. rww flip_flip.  
rw target_flip; try alike. 
rw target_flip; try alike. am. 
Qed. 

Lemma covee_hypothesis_opp : forall a u v,
Category.axioms a -> 
covee_hypothesis (opp a) u v =
vee_hypothesis a (flip u) (flip v).
Proof.
ir. ap iff_eq; ir. 
uh H0; uhg; ee. rwi mor_opp H0. am. 
wrr mor_opp. 
rw target_flip; try alike. rw target_flip; try alike. 
am. 

uh H0; ee. uhg; ee. 
rw mor_opp; am. rw mor_opp; am. 
rwi target_flip H2; try alike. rwi target_flip H2; try alike. 
am. 
wri mor_opp H1; alike. wri mor_opp H0; alike. 
Qed.

Lemma vee_hypothesis_opp_flip : forall a u v,
Category.axioms a -> 
vee_hypothesis (opp a) (flip u) (flip v) =
covee_hypothesis a u v.
Proof.
ir. 
transitivity (covee_hypothesis (opp (opp a))
u v).  rw covee_hypothesis_opp. tv. 
app opp_axioms. rww opp_opp. 
Qed. 


Lemma has_cofipr_has_fipr : forall a u v,
Category.axioms a -> 
has_cofiprod a u v = has_fiprod (opp a) (flip u) (flip v).
Proof.
ir. ap iff_eq; ir. 
uh H0; ee. am. uhg; ee. uh H0; ee. 
rwi vee_hypothesis_opp_flip H0. 
am. am. am. 
Qed. 

Lemma has_fipr_has_cofipr : forall a u v,
Category.axioms a -> 
has_fiprod a u v = has_cofiprod (opp a) (flip u) (flip v).
Proof.
ir. 
rw has_cofipr_has_fipr. rw flip_flip. rw flip_flip. 
rw opp_opp. tv. app opp_axioms. 
Qed. 

Lemma has_cofiprods_opp : forall a,
has_cofiprods (opp a) = has_fiprods a.
Proof.
ir. ap iff_eq; ir. 
uh H; ee. uhg; ee. wrr axioms_opp. 
ir. rw has_fipr_has_cofipr. 
ap H0. 
rw covee_hypothesis_opp. rw flip_flip. 
rw flip_flip. am. 
wrr axioms_opp. wrr axioms_opp. 

uh H; ee. uhg; ee. 
app opp_axioms. ir. 
rw has_cofipr_has_fipr. 
rw opp_opp. ap H0. 
wr covee_hypothesis_opp. am. am. app opp_axioms. 
Qed.

Lemma has_fiprods_opp : forall a,
has_fiprods (opp a) = has_cofiprods a.
Proof.
ir. wr has_cofiprods_opp. 
rww opp_opp. 
Qed. 

Lemma has_cofiprods_has_colimits_over_opp : forall a,
Category.axioms a ->
has_cofiprods a = has_colimits_over (opp vee_cat) a.
Proof.
ir. ap iff_eq; ir. assert (a = opp (opp a)). 
rww opp_opp. rw H1. 
ap has_colimits_over_opp. app opp_axioms. 
ap vee_cat_axioms. 
wr  has_fiprods_has_limits_over.  
rw has_fiprods_opp. am. app opp_axioms. 

wr has_fiprods_opp. rw has_fiprods_has_limits_over.
assert (vee_cat = opp (opp vee_cat)).
rww opp_opp. rw H1. 
ap has_limits_over_opp. am. 
ap opp_axioms. ap vee_cat_axioms. am. 
app opp_axioms. 
Qed.

Lemma mor_cofipr1 : forall a u v,
has_cofiprod a u v ->
mor a (cofipr1 a u v).
Proof.
ir. cp (cofiprod_hypothesis_cofiprod H). 
uh H0; ee. am. 
Qed.

Lemma mor_cofipr2 : forall a u v,
has_cofiprod a u v ->
mor a (cofipr2 a u v).
Proof.
ir. cp (cofiprod_hypothesis_cofiprod H). 
uh H0; ee. am. 
Qed.

Lemma source_cofipr1 : forall a u v,
has_cofiprod a u v ->
source (cofipr1 a u v) = target u.
Proof.
ir. cp (cofiprod_hypothesis_cofiprod H). 
uh H0; ee. am. 
Qed.

Lemma source_cofipr2 : forall a u v,
has_cofiprod a u v ->
source (cofipr2 a u v) = target v.
Proof.
ir. cp (cofiprod_hypothesis_cofiprod H). 
uh H0; ee. am. 
Qed.

Lemma target_cofipr2 : forall a u v,
has_cofiprod a u v ->
target (cofipr2 a u v) = target (cofipr1 a u v).
Proof.
ir.  cp (cofiprod_hypothesis_cofiprod H). 
uh H0; ee. 

uh H0; ee. 
transitivity (target (comp a (cofipr1 a u v) u)).
rw H5. rw target_comp. tv. 
ap mor_cofipr2. am. am. 
rw source_cofipr2. tv. am. 
rw target_comp. tv. 
app mor_cofipr1. am. 
rww source_cofipr1. 
Qed. 

Lemma comp_cofiprod_eq : forall a u v,
has_cofiprod a u v ->
comp a (cofipr1 a u v) u = comp a (cofipr2 a u v) v.
Proof.
ir. cp (cofiprod_hypothesis_cofiprod H). 
uh H0; ee. am. 
Qed.

Definition cofipr_dotted a u v y1 y2 :=
flip (fipr_dotted (opp a) (flip u) (flip v) (flip y1) (flip y2)).



Lemma mor_cofipr_dotted : forall a u v y1 y2,
has_cofiprod a u v -> cofiprod_hypothesis a u v y1 y2 ->
mor a (cofipr_dotted a u v y1 y2).
Proof.
ir. 
rwi has_cofipr_has_fipr H. 
rwi cofi_hyp_fi_hyp H0. 
uf cofipr_dotted. 
wr mor_opp. app mor_fipr_dotted. 
 uh H0; ee. 
uh H1; ee; am.  uh H0; ee. 
uh H1; ee; am. 
Qed.

Lemma source_fipr_dotted : forall a u v y1 y2,
has_cofiprod a u v -> cofiprod_hypothesis a u v y1 y2 ->
source (cofipr_dotted a u v y1 y2) = target (cofipr1 a u v).
Proof.
ir. 
rwi has_cofipr_has_fipr H. 
rwi cofi_hyp_fi_hyp H0. 
uf cofipr_dotted. 
rw source_flip. 
rw target_fipr_dotted. 
uf cofipr1. rw target_flip. 
tv. 
apply mor_arrow_like with (opp a). app mor_fipr1. 
am. am. 
apply mor_arrow_like with (opp a). 
app mor_fipr_dotted. 
uh H0; ee. 
uh H1; ee; am. uh H0; ee. 
uh H1; ee; am. 
Qed.

Lemma comp_cofipr1_cofipr_dotted : forall a u v y1 y2,
has_cofiprod a u v -> cofiprod_hypothesis a u v y1 y2 ->
comp a (cofipr_dotted a u v y1 y2) (cofipr1 a u v) = y1.
Proof.
ir. 
rwi has_cofipr_has_fipr H. 
rwi cofi_hyp_fi_hyp H0. 

uf cofipr_dotted. 
uf cofipr1. ap flip_eq. wr comp_opp. 
ap comp_fipr1_fipr_dotted. am. am. 
app mor_fipr1. app mor_fipr_dotted. 
rw target_fipr_dotted. tv. am. am. 
uh H0; ee. uh H1; ee; am. 
uh H0; ee. uh H1; ee; am. 
Qed.

Lemma comp_cofipr2_cofipr_dotted : forall a u v y1 y2,
has_cofiprod a u v -> cofiprod_hypothesis a u v y1 y2 ->
comp a (cofipr_dotted a u v y1 y2) (cofipr2 a u v) = y2.
Proof.
ir. 
rwi has_cofipr_has_fipr H. 
rwi cofi_hyp_fi_hyp H0. 

uf cofipr_dotted. 
uf cofipr2. ap flip_eq. wr comp_opp. 
ap comp_fipr2_fipr_dotted. am. am. 
app mor_fipr2. app mor_fipr_dotted. 
rw target_fipr_dotted. tv. 
rw source_fipr2. tv. am. am. 
am. 
uh H0; ee. uh H1; ee; am. 
uh H0; ee. uh H1; ee; am. 
Qed.


Lemma cofipr_dotted_comp : forall a u v z,
has_cofiprod a u v -> mor a z ->
source z = target (cofipr1 a u v)  ->
cofipr_dotted a u v (comp a z (cofipr1 a u v))
(comp a z (cofipr2 a u v)) = z.
Proof.
ir. cp H. rwi has_cofipr_has_fipr H. 
assert (cofiprod_hypothesis a u v 
(comp a z (cofipr1 a u v)) (comp a z (cofipr2 a u v))).
app cofiprod_hypothesis_comp. 
app cofiprod_hypothesis_cofiprod. 

rwi cofi_hyp_fi_hyp H3. 
uf cofipr_dotted. 
assert (flip (comp a z (cofipr1 a u v)) =
comp (opp a) (fipr1 (opp a) (flip u) (flip v)) (flip z)).
rw comp_opp. sy; rw flip_flip. 
uf cofipr1. tv. 
app mor_fipr1. rww mor_opp. rww flip_flip. 
ufi cofipr1 H1. 
rwi target_flip H1. wr H1. rww target_flip. 
alike. 
apply mor_arrow_like with (opp a). 
app mor_fipr1. 

assert (flip (comp a z (cofipr2 a u v)) =
comp (opp a) (fipr2 (opp a) (flip u) (flip v)) (flip z)).
rw comp_opp. sy; rw flip_flip. 
uf cofipr2. tv. 
app mor_fipr2. rww mor_opp. rww flip_flip. 
assert (lem1 : source z = target (cofipr2 a u v)).
rw target_cofipr2. am. am. 
ufi cofipr2 lem1. 
rwi target_flip lem1. wr lem1. rww target_flip. 
alike. 
apply mor_arrow_like with (opp a). 
app mor_fipr2. 

rw H4. rw H5. rw fipr_dotted_comp. rww flip_flip. am. 
rw mor_opp. rww flip_flip. 
ufi cofipr1 H1. 
rwi target_flip H1. wr H1. rww target_flip. 
alike. 
apply mor_arrow_like with (opp a). 
app mor_fipr1. 
uh H0; ee; am. uh H0; ee; am. 
Qed.

(*** now we apply the result of fc_limits to 
the case of cofiprods ***********************)



Lemma has_cofiprods_functor_cat : forall a b,
Category.axioms a -> has_cofiprods b -> 
has_cofiprods (functor_cat a b).
Proof.
ir. rw has_cofiprods_has_colimits_over_opp.
cp H0.
uh H1; ee. 
rwi has_cofiprods_has_colimits_over_opp H0. 
ap has_colimits_functor_cat. am. am. 
ap opp_axioms. ap vee_cat_axioms. am. am. 
ap functor_cat_axioms. am. 
uh H0; ee; am. 
Qed.



Lemma has_finite_limits_has_cofiprods : forall a,
has_finite_colimits a ->  has_cofiprods a.
Proof.
ir. rw has_cofiprods_has_colimits_over_opp. 
uh H; ee. ap H0. 
ap is_finite_cat_opp. 
ap is_finite_vee_cat. uh H; ee; am. 
Qed.


End Cofiprod.

Export Cofiprod. 

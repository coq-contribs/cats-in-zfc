Set Implicit Arguments.
Unset Strict Implicit.

Require Import Arith.
Require Export colimits.
Require Export functor_cat.

Ltac lw := autorewrite with lw; try tv; try am. 
Ltac lr := autorewrite with lw.

Module Functor_Cat_Limit.
Export Functor_Cat.
Export Colimit. 

Module MainResultMod.
Section MainResult.
Variables a b f: E.

Hypothesis Xa : Category.axioms a.
Hypothesis Xb : Category.axioms b.
Hypothesis Ff : Functor.axioms f. 
Hypothesis F2 : target f = functor_cat a b.

Definition pointf x := fcompose (point_functor a b x) f.

Definition c:= source f.

Definition F1 : source f = c.
Proof. tv. Qed. 

Definition Xc : Category.axioms c.
Proof.
uf c. cp Ff; lu. 
Qed. 

Lemma source_pointf : forall x, source (pointf x) = c.
Proof.
ir. uf pointf. rw source_fcompose. tv. 
Qed.

Lemma target_pointf : forall x, target (pointf x) = b.
Proof.
ir. uf pointf. rww target_fcompose. rww target_point_functor.
 Qed.

Lemma pointf_axioms : forall x, ob a x ->
Functor.axioms (pointf x). 
Proof.
ir. uf pointf. 
ap fcompose_axioms. 
app point_functor_axioms. 
am. rww source_point_functor. 
sy; am. 
Qed. 

Definition pointl x := limit (pointf x).

Hypothesis FL : forall x, ob a x -> has_limit (pointf x).

Lemma is_limit_pointl : forall x, ob a x -> is_limit (pointl x).
Proof.
ir. uf pointl. ap is_limit_limit. au. 
Qed.

Lemma is_cone_pointl : forall x, ob a x -> is_cone (pointl x).
Proof.
ir. cp (is_limit_pointl H). lu. 
Qed. 



Lemma socle_pointl : forall x, ob a x -> 
socle (pointl x) = pointf x.
Proof.
ir. uf pointl. rw socle_limit. tv. au. 
Qed.

Lemma cone_target_pointl : forall x, ob a x ->
cone_target (pointl x) = b. 
Proof.
ir. uf cone_target. rw socle_pointl. tv. 
rww target_pointf. am. 
Qed. 

Lemma cone_source_pointl : forall x, ob a x ->
cone_source (pointl x) = c.
Proof.
ir. uf cone_source. rw socle_pointl. 
rww source_pointf. am.  
Qed. 




Definition pointv x := vertex (pointl x).

Lemma vertex_pointl : forall x, 
vertex (pointl x) = pointv x. 
Proof. ir. tv. Qed. 

Lemma ob_pointv : forall x, ob a x -> ob b (pointv x).
Proof.  ir.  
uf pointv. assert (b = cone_target (pointl x)).
uf cone_target. rw socle_pointl. rww target_pointf. am.  
rw H0. ap Limit.ob_vertex. 
cp (is_limit_pointl H). lu. 
Qed.

Definition newcone u := 
cone_transform
(htrans_right (point_trans a b u) f)
(pointl (source u)).

Lemma is_cone_newcone : forall u,
mor a u -> is_cone (newcone u).
Proof.
ir. uf newcone. 
ap is_cone_cone_transform. 
uhg; ee. 
ap is_cone_pointl. rww ob_source.  
ap htrans_right_axioms. am. 
ap point_trans_axioms. am. 
am. rw osource_point_trans. 
sy; am. 
rw socle_pointl. 
rw source_htrans_right. 
rw source_point_trans. 
uf pointf. tv.  
rww ob_source; am. 
Qed.

Lemma socle_newcone : forall u, mor a u ->
socle (newcone u) = pointf (target u).
Proof.
ir. uf newcone. 
rw socle_cone_transform. rw target_htrans_right. 
rw target_point_trans. tv. 
Qed.

Lemma vertex_newcone : forall u, mor a u ->
vertex (newcone u) = pointv (source u).
Proof.
ir. uf newcone. 
rw vertex_cone_transform. tv. 
Qed.

Definition restr u := cone_to_limit (newcone u) (pointl (target u)).

Lemma mor_restr : forall u,  mor a u ->
mor b (restr u).
Proof.
ir. uf restr. ap mor_cone_to_limit. 
ap is_cone_newcone. am. 
ap is_limit_pointl. rww ob_target. 
rw socle_newcone. rw socle_pointl. tv. rww ob_target; am.
am. uf otarget. rww cone_target_pointl. 
rww  ob_target. 
Qed.

Lemma source_restr : forall u, mor a u ->
source (restr u) = pointv (source u).
Proof.
ir. uf restr.  rw source_cone_to_limit. 
rw vertex_newcone. tv. am. 
ap is_cone_newcone. am. 
ap  is_limit_pointl. rww  ob_target. 
rw socle_newcone. rw socle_pointl. tv. 
rww  ob_target. am. 
Qed.

Lemma target_restr : forall u, mor a u ->
target (restr u) = pointv (target u).
Proof.
ir. uf restr. rw target_cone_to_limit. 
tv. ap is_cone_newcone. am. 
ap is_limit_pointl.
rww  ob_target. 
rw socle_newcone. rw socle_pointl. tv. 
rww  ob_target. am. 
Qed.




Lemma restr_id : forall x, ob a x ->
restr (id a x) = id b (pointv x).
Proof.
ir. uf restr. 
rw cone_to_limit_id. 
rw cone_target_pointl. 
rw vertex_pointl. rw target_id. tv. 
am. rw target_id. am. am. 
uf newcone. 
wr vident_point_functor. 
rw htrans_right_vident. 
rw cone_transform_vident. 
ap is_limit_pointl. rw source_id. am. am. 
assert (is_limit (pointl (source (id a x)))).
ap is_limit_pointl. rww source_id. 
rw socle_pointl. 
rw source_id. tv. am. rww source_id. 
app is_cone_pointl. rww source_id. 
ap point_functor_axioms. am. am. am. 
rw source_point_functor. sy; am. am. am. 
uf newcone. rww source_id. rww target_id. 
wr vident_point_functor. 
rw htrans_right_vident. 
rw cone_transform_vident. tv. 
rw socle_pointl. tv. am. 
app is_cone_pointl.  app point_functor_axioms. am. 
rww source_point_functor. sy; am. am. am. 
Qed.



Lemma restr_comp : forall u v, composable a u v ->
restr (comp a u v) = comp b (restr u) (restr v). 
Proof.
ir. 
assert (mu : mor a u).
rwi composable_facts_rw H; lu. 
assert (mv : mor a v).
rwi composable_facts_rw H; lu. 
assert (sutv : source u = target v).
rwi composable_facts_rw H; lu. 
uf restr. 
assert (osu : ob a (source u)).
rww ob_source.
assert (otu : ob a (target u)).
rww ob_target.
assert (osv : ob a (source v)).
rww ob_source.
assert (otv : ob a (target v)).
rww ob_target.



transitivity (comp (cone_target (pointl (target u)))
(cone_to_limit (newcone u) (pointl (target u)))
  (cone_to_limit (newcone v) (pointl (target v)))).
wr cone_to_limit_cone_compose. 
rw target_comp. 
assert (lem1 : (newcone (comp a u v)) = 
(cone_compose (newcone u) 
(cone_to_limit (newcone v) (pointl (target v))))).
uf newcone. 
set (uu := htrans_right (point_trans a b u) f).
set (vv := htrans_right (point_trans a b v) f).
set (uv := htrans_right (point_trans a b (comp a u v)) f).
assert (uuax : Nat_Trans.axioms uu).
uf uu. ap htrans_right_axioms. 
am. app point_trans_axioms. 
rw osource_point_trans. sy; am. 

assert (vvax : Nat_Trans.axioms vv).
uf vv. ap htrans_right_axioms. 
am. app point_trans_axioms. 
rw osource_point_trans. sy; am. 

assert (suu : source uu = pointf (source u)).
uf uu; rw source_htrans_right. 
rw source_point_trans. reflexivity.

assert (tuu : target uu = pointf (target u)).
uf uu; rw target_htrans_right. 
rw target_point_trans. reflexivity. 

assert (svv : source vv = pointf (source v)).
uf vv; rw source_htrans_right. 
rw source_point_trans. reflexivity.

assert (tvv : target vv = pointf (target v)).
uf vv; rw target_htrans_right. 
rw target_point_trans. reflexivity.


rw source_comp. 
rw sutv. 
set (k:= (cone_to_limit (cone_transform vv (pointl (source v))) 
(pointl (target v)))). 
assert (cone_compose (cone_transform uu (pointl (target v))) k
= cone_transform uu (cone_compose (pointl (target v)) k)).
ap cone_compose_cone_transform. 
app is_cone_pointl. 
uhg; ee. app is_cone_pointl.  
rww cone_target_pointl. uf k. 
ap mor_cone_to_limit. 
ap is_cone_cone_transform. uhg; ee. app is_cone_pointl.
am. rww socle_pointl. 
app is_limit_pointl. 
rww socle_cone_transform.
rww socle_pointl. 
rww cone_target_pointl. 

uf k. rww target_cone_to_limit. 
app is_cone_cone_transform. uhg; ee. 
app is_cone_pointl. am. rww socle_pointl. 
app is_limit_pointl. rww socle_cone_transform. 
rww socle_pointl. uhg; ee. app is_cone_pointl.
am. rw socle_pointl. wr sutv. am. am. 

rw H0. 
uf k. 

assert (cone_compose (pointl (target v))
(cone_to_limit (cone_transform vv (pointl (source v)))
(pointl (target v))) =
(cone_transform vv (pointl (source v)))).

rw cone_compose_cone_to_limit. reflexivity. 
app is_cone_cone_transform. uhg; ee. 
app is_cone_pointl. am. rww socle_pointl. 
app is_limit_pointl. rww socle_cone_transform.
rww socle_pointl. 
rw H1. 
assert (uv = vcompose uu vv). 
uf uu; uf vv. 
rw vcompose_htrans_right_htrans_right. 
assert (vcompose (point_trans a b u) (point_trans a b v)
= point_trans a b (comp a u v)). 
app vcompose_point_trans. 
rw H2. reflexivity. 
app  point_trans_axioms. app point_trans_axioms. 
am. reflexivity. 
rww source_point_trans. rw target_point_trans. 
rw sutv. reflexivity. 
rw osource_point_trans. am. 
rw H2. 
rw cone_transform_vcompose. reflexivity. 
app is_cone_pointl. uhg; ee. 
app is_cone_pointl. am. rww socle_pointl. am. 
rw suu. rw tvv. rw sutv. reflexivity. am. am. 
am. 

(**** end of proof of lem1 ! ***)


rw lem1. tv. am. am.
am. ap is_limit_pointl. am. 
uhg; ee. app is_cone_newcone. 
ap mor_cone_to_limit. ap is_cone_newcone. 
am. 
ap is_limit_pointl. am. 
rw socle_newcone. rw socle_pointl. tv. 
am.  am. 
uf cone_target. 
rw socle_newcone. rw socle_pointl. 
rw target_pointf. rw target_pointf. tv. am. am. 
rw target_cone_to_limit. 
rw vertex_newcone. 
rw vertex_pointl. rwi composable_facts_rw H.
uh H; ee. rw H4; tv. am. 
ap is_cone_newcone. am. 
app is_limit_pointl. 
rw socle_newcone. rw socle_pointl. tv. 
am. am. 
rw socle_newcone. rw socle_pointl. tv. 
am.  am. 
rw cone_target_pointl. tv. am.  
Qed.

(*** plv = presheaf_limit_vertex ***)
Definition plv :=
Functor.create a b restr.

Lemma source_plv : source plv = a.
Proof.
ir. uf plv. rww Functor.source_create. 
Qed.

Lemma target_plv : target plv = b.
Proof.
ir. uf plv. rww Functor.target_create. 
Qed.

Lemma fmor_plv : forall u, mor a u ->
fmor plv u = restr u.
Proof.
ir. uf plv. rww Functor.fmor_create. 
Qed.

Lemma fob_plv : forall x, ob a x ->
fob plv x = pointv x.
Proof.
ir.  
uf fob. rww fmor_plv. rw source_plv.
rww restr_id. rww source_id. 
app ob_pointv. rw source_plv. app mor_id. 
Qed.

Lemma plv_axioms : 
Functor.axioms plv.
Proof.
uf plv.
ap Functor.create_axioms. 
sh pointv. 
uhg; ee; try am; ir. 
app ob_pointv. 
rww restr_id. 
app mor_restr. 
rww source_restr. 
rww target_restr. 
rww restr_comp. app show_composable. 
Qed.


Definition ple x := Nat_Trans.create plv (fob f x)
(fun y => edge (pointl y) x).

Lemma source_ple : forall x, source (ple x) = plv.
Proof. ir. uf ple. rww Nat_Trans.source_create. Qed.

Lemma target_ple : forall x, target (ple x) = fob f x.
Proof. ir. uf ple. rww Nat_Trans.target_create. Qed.

Lemma osource_ple : forall x, osource (ple x) = a.
Proof.
ir. uf osource. rw source_ple. rw source_plv. tv. 
Qed.

Lemma otarget_ple : forall x,  ob c x -> otarget (ple x) = b.
Proof.
ir. uf otarget. rw target_ple. 
assert (ob (functor_cat a b) (fob f x)). wr F2. 
app ob_fob. rwi ob_functor_cat H0. uh H0; ee. 
am. am. am.  
Qed.

Lemma ntrans_ple : forall y x, ob c x -> ob a y -> ntrans (ple x) y = 
edge (pointl y) x. 
Proof.
ir. uf ple. 
rww ntrans_create. 
change (is_ob (source plv) y). rw source_plv. lu. 
Qed. 

Lemma fmor_edge_edge_restr : 
forall x u, ob c x -> mor a u -> 
comp b (fmor (fob f x) u) (edge (pointl (source u)) x) =
comp b (edge (pointl (target u)) x) (restr u).
Proof.
ir. uf restr. 
transitivity (edge (cone_compose (pointl (target u))
(cone_to_limit (newcone u) (pointl (target u)))) x).
rw cone_compose_cone_to_limit. 
uf newcone. 
rw edge_cone_transform. 
rw ntrans_htrans_right. 
rw ntrans_point_trans. 
rw cone_target_pointl. tv. rww ob_source. am. 
wr F2. app ob_fob. 
rww F1. 
rw osource_htrans_right. rww F1. 
uhg; ee. app is_cone_pointl. rww ob_source. 
app htrans_right_axioms. app  point_trans_axioms. 
rww osource_point_trans. sy; am. 
rw source_htrans_right. rw source_point_trans. 
rw socle_pointl. tv. rww ob_source. app is_cone_newcone. 
app is_limit_pointl. 

rww ob_target. rw socle_newcone. rww socle_pointl. 
rww ob_target. am. 
rw edge_cone_compose. 
rw cone_target_pointl. tv. rww ob_target. 
rw cone_source_pointl. am. rww ob_target. 
uhg; ee. app is_cone_pointl. rww ob_target. 
rw cone_target_pointl. 
app mor_cone_to_limit. app is_cone_newcone. app is_limit_pointl.
rww ob_target. rww socle_newcone. rww socle_pointl. 
rww ob_target. rww cone_target_pointl. rww ob_target. 
rww ob_target. 
rww target_cone_to_limit. app is_cone_newcone. 
app is_limit_pointl. rww ob_target. 
rww socle_newcone. rww socle_pointl. rww ob_target. 
Qed. 

Lemma nat_trans_axioms_ple : forall x, ob c x -> 
Nat_Trans.axioms (ple x).
Proof.
ir. 
assert (ob (functor_cat a b) (fob f x)). 
wr F2. app ob_fob. cp H0. 
rwi ob_functor_cat H1; try am. uh H1; ee. 

uhg; ee. uf ple. 
ap create_like. 
rww osource_ple. rww otarget_ple. 
rww source_ple. app plv_axioms. 
rw target_ple. 
am. rw target_ple. rw H2. rww osource_ple. 
rw source_ple. rw target_plv. rww otarget_ple. 
ir. 
rwi osource_ple H4. 
rww otarget_ple. rww ntrans_ple. 
assert (b = cone_target (pointl x0)). 
rww cone_target_pointl. 
rw H5. app mor_edge. 
rww cone_source_pointl. app is_cone_pointl. 
ir. rwi osource_ple H4. 
rww source_ple. 
rww ntrans_ple. rww source_edge.
rww vertex_pointl. rww fob_plv. 
rww cone_source_pointl. app is_cone_pointl.
ir. rwi osource_ple H4. 
rww target_ple. rww ntrans_ple. 
rww target_edge. rww socle_pointl. 
uf pointf. rw fob_fcompose. 
rw fob_point_functor. tv. am. am. 
am. am. app point_functor_axioms. am. 
rww source_point_functor. sy; am. am. 
rww cone_source_pointl. app is_cone_pointl. 
ir. rwi osource_ple H4. 
rww otarget_ple. rww target_ple. rw source_ple. 
rw ntrans_ple. rw ntrans_ple. 
rw fmor_plv. sy; ap fmor_edge_edge_restr. am. 
am. am. am. rww ob_source. am. rww ob_target. 
Qed. 


Lemma axioms_fob_f : forall x, ob c x ->
Functor.axioms (fob f x).
Proof.
ir. assert (fhom a b (fob f x)). wr ob_functor_cat.
wr F2. app ob_fob. am. am. lu. 
Qed.

Lemma source_fob_f : forall x, ob c x ->
source (fob f x) = a.
Proof.
ir. assert (fhom a b (fob f x)). wr ob_functor_cat.
wr F2. app ob_fob. am. am. lu. 
Qed.

Lemma target_fob_f : forall x, ob c x ->
target (fob f x) = b.
Proof.
ir. assert (fhom a b (fob f x)). wr ob_functor_cat.
wr F2. app ob_fob. am. am. lu. 
Qed.

Lemma axioms_fmor_f : forall u, mor c u ->
Nat_Trans.axioms (fmor f u).
Proof.
ir. assert (nt2hom a b (fmor f u)). 
wr mor_functor_cat. wr F2; app mor_fmor. 
am. am. lu. 
Qed.

Lemma osource_fmor_f : forall u, mor c u ->
osource (fmor f u) = a.
Proof.
ir. assert (nt2hom a b (fmor f u)). 
wr mor_functor_cat. wr F2; app mor_fmor. 
am. am. lu. 
Qed.

Lemma otarget_fmor_f : forall u, mor c u ->
otarget (fmor f u) = b.
Proof.
ir. assert (nt2hom a b (fmor f u)). 
wr mor_functor_cat. wr F2; app mor_fmor. 
am. am. lu. 
Qed.


Lemma ple_commutation : forall u, mor c u ->
vcompose (fmor f u) (ple (source u)) =
ple (target u).
Proof.
ir. 
assert (ob c (source u)). rww ob_source.
assert (ob c (target u)). rww ob_target. 
ap Nat_Trans.axioms_extensionality.
rww vcompose_axioms. 
app axioms_fmor_f. app nat_trans_axioms_ple. 
rww target_ple.
rww source_fmor. app nat_trans_axioms_ple. 
rw source_vcompose. rw source_ple. rw source_ple. 
tv. 
rw target_vcompose. rw target_ple. rw target_fmor. 
tv. am. am. 
ir. rwi osource_vcompose H2. rwi osource_ple H2. 
rww ntrans_vcompose. 
rww otarget_fmor_f. rww ntrans_ple. 
rww ntrans_ple. 
assert (b = cone_target (pointl x)). 
rww cone_target_pointl. 
assert (ntrans (fmor f u) x = fmor (socle (pointl x)) u).
rw socle_pointl. uf pointf. 
rw fmor_fcompose. rw fmor_point_functor. 
tv. wr F2; app mor_fmor. 
app point_functor_axioms. am. 
rww source_point_functor. sy; am. am. am. 
rw H3. rw H4. 
rw Limit.commutativity. tv. rww cone_source_pointl. 
app is_cone_pointl. rww osource_ple. 
Qed.

(*** plc = presheaf limit cone ***)
Definition plc := cone_create2 f plv ple.

Lemma vertex_plc : vertex plc = plv.
Proof.
ir. uf plc. 
uf cone_create2. rww vertex_cone_create. 
Qed.

Lemma socle_plc : socle plc = f.
Proof.
ir. uf plc; uf cone_create2. 
uf socle. 
rw edge_nt_cone_create. 
rw target_create. tv. 
Qed.

Lemma cone_source_plc : cone_source plc = c.
Proof.
uf cone_source. rw socle_plc. tv. 
Qed.

Lemma cone_target_plc : cone_target plc = (functor_cat a b).
Proof.
ir. uf cone_target. rw socle_plc. am. 
Qed.

Lemma edge_plc : forall x, ob c x -> edge plc x = ple x.
Proof.
ir. uf plc; uf cone_create2. uf edge. 
rw edge_nt_cone_create. rw ntrans_create. 
tv. rw source_constant_functor. 
change (is_ob c x). lu. 
Qed.



Lemma is_cone_plc : is_cone plc.
Proof.
uf plc. ap is_cone_cone_create2. am. 
rw F2. rw ob_functor_cat. uhg; ee. 
app plv_axioms. rww source_plv. rww target_plv. 
am. am. ir. 
rw F2; rw mor_functor_cat. uhg; ee. 
app nat_trans_axioms_ple. 
rww osource_ple. rww otarget_ple. am. am. 
ir. rww source_ple. 
ir. rww target_ple. 
ir. 
rw F2. rw comp_functor_cat. ap ple_commutation. am. 
am. am. wr F2; app mor_fmor. 
rww mor_functor_cat. uhg; ee. 
app nat_trans_axioms_ple. rww ob_source. 
rww osource_ple. rww otarget_ple. rww ob_source. 
rww source_fmor. rww target_ple. 
Qed. 

Section Limit_Pr.
Variable other : E.
Hypothesis oth_cone : is_cone other.
Hypothesis socle_other : socle other = f.

Definition otherv := vertex other.

Lemma cone_source_other : cone_source other = c.
Proof.
uf cone_source. rw socle_other. tv. 
Qed.

Lemma cone_target_other : cone_target other = functor_cat a b.
Proof.
ir. uf cone_target. rww socle_other. 
Qed.



Lemma source_otherv : source otherv = a.
Proof.
uf otherv. 
assert (ob (functor_cat a b) otherv). 
wr cone_target_other. uf otherv. app Limit.ob_vertex. 
rwi ob_functor_cat H. lu. am. am.  
Qed.

Lemma target_otherv : target otherv = b.
Proof.
uf otherv. 
assert (ob (functor_cat a b) otherv). 
wr cone_target_other. uf otherv. app Limit.ob_vertex. 
rwi ob_functor_cat H. lu. am. am. 
Qed.

Lemma axioms_otherv : Functor.axioms otherv.
Proof.
uf otherv. 
assert (ob (functor_cat a b) otherv). 
wr cone_target_other. uf otherv. app Limit.ob_vertex. 
rwi ob_functor_cat H. lu. am. am. 
Qed.

(*** we want to construct a presh morph from otherv to plv 
and show that any other such is equal to it ***)

Definition other_pt y:=
cone_pushdown (point_functor a b y) other.

Lemma is_cone_other_pt : forall y, ob a y ->
is_cone (other_pt y).
Proof.
ir. uf other_pt. 
ap is_cone_cone_pushdown. am. 
app point_functor_axioms. 
rww source_point_functor. 
rww cone_target_other. 
Qed.

Lemma socle_other_pt : forall y, ob a y -> 
socle (other_pt y) = pointf y.
Proof.
ir. uf other_pt. 
rw socle_cone_pushdown. 
rw socle_other. tv. 
Qed.

Lemma cone_source_other_pt : forall y, ob a y ->
cone_source (other_pt y) = c.
Proof.
ir. 
uf cone_source. rww socle_other_pt. 
rww source_pointf. 
Qed.

Lemma cone_target_other_pt : forall y, ob a y ->
cone_target (other_pt y) = b.
Proof.
ir. 
uf cone_target. rww socle_other_pt. 
rww target_pointf. 
Qed.

Lemma vertex_other_pt : forall y, ob a y ->
vertex (other_pt y) = fob otherv y.
Proof.
ir. uf other_pt. 
rw vertex_cone_pushdown. 
rw fob_point_functor. tv. am. 
am. wr cone_target_other. 
app  Limit.ob_vertex. am. 
Qed. 


Lemma edge_other_pt : forall x y,
ob a y -> ob c x ->
edge (other_pt y) x = ntrans (edge other x) y.
Proof.
ir. uf other_pt. 
rw edge_cone_pushdown. 
rw fmor_point_functor. tv. 
wr cone_target_other. ap mor_edge. 
rww cone_source_other. am. 
rww cone_source_other. am. 
Qed.



Definition our_mval y := cone_to_limit (other_pt y) (pointl y).

Lemma source_our_mval : forall y, ob a y -> 
source (our_mval y) = fob otherv y.
Proof.
ir. uf our_mval. 
rw source_cone_to_limit. rw vertex_other_pt. 
tv. am. app is_cone_other_pt. 
ap is_limit_pointl. 
am. rw socle_other_pt. 
rw socle_pointl. tv. am. 
am. Qed.

Lemma target_our_mval : forall  y, ob a y->
target (our_mval y) = pointv y.
Proof.
ir. uf our_mval. 
rw target_cone_to_limit. tv. app is_cone_other_pt. 
app is_limit_pointl. 
rww socle_other_pt. rww socle_pointl. 
Qed.

Lemma target_our_mval2 : forall y, ob a y->
target (our_mval y) = fob plv y.
Proof.
ir. rw target_our_mval. rw fob_plv. tv. am. 
am. 
Qed.

Lemma comp_ntrans_pointl_our_mval : forall x y, ob c x -> ob a y ->
comp b (edge (pointl y) x) (our_mval y) =
edge (other_pt y) x.
Proof.
ir. uf our_mval. 
rw comp_edge_cone_to_limit. tv. 
app is_limit_pointl. 
app is_cone_other_pt. rw socle_other_pt. 
rw socle_pointl. tv. am. 
am. rww cone_target_pointl. rww cone_source_pointl. 
Qed.

Lemma weak_mor_fmor : forall bb ff uu,
Functor.axioms ff -> bb = target ff -> mor (source ff) uu -> 
mor bb (fmor ff uu).
Proof.
ir. rw H0. app mor_fmor. 
Qed.

Lemma our_mval_carre : forall u, mor a u -> 
comp b (fmor plv u) (our_mval (source u)) =
comp b (our_mval (target u)) (fmor otherv u).
Proof.
ir. uf our_mval. 
rw fmor_plv. 
assert (ob_src : ob a (source u)).
rww ob_source. 
assert (ob_trg : ob a (target u)).
rww ob_target. 
assert (mor_restr_u : mor b (restr u)).
ap mor_restr. am. 

assert (mor_fmor_otherv : mor b (fmor otherv u)).
app weak_mor_fmor. ap axioms_otherv. 
rww target_otherv. rww source_otherv. 

assert (lem1: is_limit (pointl (target u))).
ap is_limit_pointl. am. 
cp lem1. uh H0; ee. uh H0; ee. 
ap H2. uhg; ee. 
app is_cone_pointl. 
rww cone_target_pointl. rw mor_comp. tv.
am. 
ap mor_cone_to_limit. app is_cone_other_pt.
app is_limit_pointl. 
rww socle_other_pt. rww socle_pointl. 
rww cone_target_pointl. 
rww source_restr. 
rw target_cone_to_limit. 
rw vertex_pointl. tv. 

app is_cone_other_pt. 
app is_limit_pointl. 
rww socle_other_pt. rww socle_pointl. 
tv. rw target_comp. rww target_restr. 

am. 
ap mor_cone_to_limit. app is_cone_other_pt.
app is_limit_pointl. 
rww socle_other_pt. rww socle_pointl. 
rww cone_target_pointl. rww source_restr. 
rw target_cone_to_limit. 
rww vertex_pointl. 
app is_cone_other_pt. 
app is_limit_pointl. 
rww socle_other_pt. rww socle_pointl.


uhg; ee. app is_cone_pointl. 
rww cone_target_pointl. rw mor_comp. tv. 
ap mor_cone_to_limit. app is_cone_other_pt. 
app is_limit_pointl. 
rww socle_other_pt. rww socle_pointl. 
rww cone_target_pointl. 
assert (b = (target otherv)). rww target_otherv. 
rw H3. 
app mor_fmor. 
app axioms_otherv. rw source_otherv. am. 
rw source_cone_to_limit. 
rw vertex_other_pt. 
rw target_fmor. tv. 
ap axioms_otherv. rww source_otherv.  
am.  app is_cone_other_pt. 
app is_limit_pointl. 
rww socle_other_pt. rww socle_pointl. 
tv. rw target_comp. rw target_cone_to_limit. 
tv. app is_cone_other_pt. 
app is_limit_pointl. 
rww socle_other_pt. rww socle_pointl.
ap mor_cone_to_limit. 
app is_cone_other_pt. 
am. rww socle_other_pt.
rww socle_pointl. rww cone_target_pointl. 
app weak_mor_fmor. 
app axioms_otherv. rww target_otherv. 
rww source_otherv. 
rw source_cone_to_limit. rww vertex_other_pt.
rw target_fmor. tv. ap axioms_otherv. 
rww source_otherv. 
app is_cone_other_pt.
am. rww socle_other_pt.
rww socle_pointl.

assert (lem2 : b = cone_target (pointl (target u))).
rw cone_target_pointl. tv. am. 

rw lem2. 
wr cone_compose_cone_compose. 
wr cone_compose_cone_compose. 
rw cone_compose_cone_to_limit. 
uf restr. rw cone_compose_cone_to_limit. 
uf newcone. 
rw cone_compose_cone_transform. 
assert (cone_compose (pointl (source u))
(cone_to_limit (other_pt (source u)) (pointl (source u)))
=
other_pt (source u)).  



rw cone_compose_cone_to_limit. tv. 
app is_cone_other_pt. app is_limit_pointl.
rww socle_other_pt. 
rww socle_pointl. 
rw H3. 


uf  other_pt. 
ap cone_extensionality. 
ap is_cone_cone_transform. 
uhg; ee. 
ap is_cone_cone_pushdown. 
am. app point_functor_axioms. 
rww source_point_functor. 
rww cone_target_other. 
ap htrans_right_axioms. 
am. app point_trans_axioms. 
rww osource_point_trans. sy; am. 
rw source_htrans_right. rw source_point_trans. 
rw socle_cone_pushdown. rww socle_other. 
rww is_cone_cone_compose. 
uhg; ee. app is_cone_cone_pushdown. 
app point_functor_axioms. 
rww source_point_functor. 
sy; rww cone_target_other. 
rww cone_target_cone_pushdown. 
rww target_point_functor. 
rw vertex_cone_pushdown. 
rw fob_point_functor. 
rw target_fmor. tv. ap axioms_otherv. 
rww source_otherv. am. am. 
rw ob_functor_cat. uhg; ee. 
ap axioms_otherv. ap source_otherv. 
ap target_otherv. am. am. 
am. 
rw vertex_cone_transform. 
rw vertex_cone_pushdown. 
rw vertex_cone_compose. 
rw fob_point_functor. rw source_fmor. 
tv. ap axioms_otherv. rww source_otherv. 
am. am. 
rw ob_functor_cat. uhg; ee. 
ap axioms_otherv. ap source_otherv. 
ap target_otherv. am. am. 
am. 

rw socle_cone_transform. 
rw target_htrans_right. 
rw socle_cone_compose. rw socle_cone_pushdown. 
rw target_point_trans. rww socle_other. 

ir. 

rwi cone_source_cone_transform H4. 
rwi cone_source_cone_pushdown H4. 
rwi cone_source_other H4. 

assert (lem3 : source (edge other x) = otherv).
rw source_edge. tv. 
rw cone_source_other. am. 
am. 

assert (lem4 : target (edge other x) = fob f x).
rww  target_edge. rw socle_other. tv. 
rww cone_source_other. 

assert (lem5 : otarget (edge other x) = b). 
uf otarget. rw lem4. 
rw target_fob_f. tv. am. 

assert (lem6 : osource (edge other x) = a). 
uf osource. rw lem3. 
rw source_otherv. tv. 

assert (lem7 : Nat_Trans.axioms (edge other x)).
assert (nt2hom a b (edge other x)). 
wr mor_functor_cat. wr F2. wr socle_other.
change (mor (cone_target other) (edge other x)). 
ap mor_edge. rww cone_source_other. am. 
am. am. lu.  

assert (lem8 : mor (functor_cat a b) (edge other x)).
rw mor_functor_cat. uhg; ee. 
am. am. am. am. am. 

assert (lem9 : ob (functor_cat a b) (fob f x)). 
rw ob_functor_cat. uhg; ee. 
app axioms_fob_f. rww source_fob_f. rww target_fob_f. 
am. am. 



rw edge_cone_transform. 
rw cone_target_cone_pushdown. 
rw target_point_functor. 
rw ntrans_htrans_right. 
rw ntrans_point_trans. rw edge_cone_pushdown. 
rw fmor_point_functor. 
rw edge_cone_compose. 
rw cone_target_cone_pushdown. 
rw target_point_functor. rw edge_cone_pushdown. 
rw fmor_point_functor. 





wr lem5; wr lem4; wr lem3; sy. 


ap carre. 


am. rww lem6. 
wr F2. 
wr socle_other. 
change (mor (cone_target other) (edge other x)). 
ap mor_edge.
rww cone_source_other. am. 
rww cone_source_other. am. 
rw cone_source_cone_pushdown. 
rww cone_source_other. 
uhg; ee. 
app is_cone_cone_pushdown. app point_functor_axioms. 
rww source_point_functor. 
rww cone_target_other. 
rww cone_target_cone_pushdown. 
rww target_point_functor. 
rww vertex_cone_pushdown. 
rww fob_point_functor. rww target_fmor. 
ap axioms_otherv. rww source_otherv. 
rw ob_functor_cat. uhg; ee. 
ap axioms_otherv. 
ap source_otherv. ap target_otherv. 
am. am. 
am. 
rww cone_source_other. 
am. am. am. 
am. 
rw osource_htrans_right. am. 

uhg; ee. app is_cone_cone_pushdown. 
app  point_functor_axioms. rww source_point_functor.
rww cone_target_other. 
app htrans_right_axioms. app point_trans_axioms. 
rww osource_point_trans. sy; am. 

rw source_htrans_right. rw source_point_trans.
rw socle_cone_pushdown. rww socle_other. 

uhg; ee. 
app is_cone_cone_pushdown. app point_functor_axioms.
rww source_point_functor. rww cone_target_other. 
app htrans_right_axioms. app point_trans_axioms. 
rww osource_point_trans. sy; am. 

rw source_htrans_right. rw source_point_trans.
rw socle_cone_pushdown. rww socle_other. 

app is_cone_pointl. 

uhg; ee. app is_cone_pointl. 
rw cone_target_pointl. 
ap mor_cone_to_limit. 
app is_cone_other_pt. app is_limit_pointl. 
rww socle_other_pt. rww socle_pointl. 
rww cone_target_pointl. am. 

rw target_cone_to_limit. 
tv. app is_cone_other_pt. app is_limit_pointl. 
rww socle_other_pt. rww socle_pointl. 

uhg; ee. app is_cone_pointl. 
app htrans_right_axioms. app point_trans_axioms. 
rww osource_point_trans. sy; am. 

rw source_htrans_right. rw source_point_trans.
rw socle_pointl. tv. am. 
app is_cone_newcone. app is_limit_pointl. 
rw socle_newcone. rww socle_pointl. 
am. app is_cone_other_pt. app is_limit_pointl.
rww socle_other_pt. rww socle_pointl. 

uhg; ee. app is_cone_pointl. 
rw cone_target_pointl. 
ap mor_cone_to_limit. 
app is_cone_other_pt. app is_limit_pointl. 
rww socle_other_pt. rww socle_pointl. 
rww cone_target_pointl. am. 
rw target_cone_to_limit. tv. 
app is_cone_other_pt. app is_limit_pointl. 
rww socle_other_pt. rww socle_pointl. 

ap show_composable. rw cone_target_pointl.
ap mor_cone_to_limit. 
app is_cone_other_pt. app is_limit_pointl. 
rww socle_other_pt. rww socle_pointl. 
rww cone_target_pointl. am. 
rw cone_target_pointl. am. am. 

rw source_cone_to_limit. rw vertex_other_pt. 
rw target_fmor. tv. ap axioms_otherv. 
rww source_otherv. am. app is_cone_other_pt. 
app is_limit_pointl. 
rww socle_other_pt. rww socle_pointl. 

uhg; ee. app is_cone_pointl. 
rww cone_target_pointl. rww vertex_pointl. 
rww target_restr. 

ap show_composable. rww cone_target_pointl. 
rw cone_target_pointl. 
ap mor_cone_to_limit. 
app is_cone_other_pt. app is_limit_pointl. 
rww socle_other_pt. rww socle_pointl. 
rww cone_target_pointl. am. 
rw target_cone_to_limit. rw vertex_pointl. 
rww source_restr. app is_cone_other_pt. 
app is_limit_pointl. 
rww socle_other_pt. rww socle_pointl. am.  
Qed. 


Definition our_map := Nat_Trans.create otherv plv our_mval.

Lemma source_our_map : source our_map = otherv.
Proof.
uf our_map. rww Nat_Trans.source_create. 
Qed.

Lemma target_our_map : target our_map = plv.
Proof.
uf our_map. rww Nat_Trans.target_create. 
Qed.

Lemma ntrans_our_map : forall y, ob a y ->
ntrans our_map y = our_mval y.
Proof.
ir. uf our_map. rw ntrans_create. tv. 
rw source_otherv. lu. 
Qed.


Lemma mor_our_map : mor (functor_cat a b) our_map.
Proof.
rw mor_functor_cat. uf our_map.
uhg; ee. ap create_axioms. 
uhg; ee. ap axioms_otherv. 
ap plv_axioms. ir.
uf our_mval. 
rww source_otherv. rww source_plv. 
rw target_otherv; rww target_plv. 
ir. 
rwi source_otherv H.
uf our_mval. 


ap mor_cone_to_limit. 
app is_cone_other_pt. 
app is_limit_pointl. 
rww socle_other_pt; rww socle_pointl. 
rww cone_target_pointl. rww target_plv. 
ir. rwi source_otherv H. rww source_our_mval. 
ir. rwi source_otherv H. 
rww target_our_mval. rww fob_plv. 

ir. rwi source_otherv H. 
rw target_plv. sy; app our_mval_carre. 
rw osource_create. rww source_otherv. 
rw otarget_create. rww target_plv. am. am.  
Qed.

Lemma cone_compose_our_map : 
cone_compose plc our_map = other.
Proof.
ap cone_extensionality.
rww is_cone_cone_compose. uhg; ee. 
ap is_cone_plc. rww cone_target_plc. 
ap mor_our_map. rww target_our_map. rww vertex_plc. 
am. rww vertex_cone_compose. rww source_our_map. 
rww socle_cone_compose. rww socle_other. rww socle_plc. 
ir. 
rwi cone_source_cone_compose H. rwi cone_source_plc H. 



rw edge_cone_compose. 
rw cone_target_plc. rw comp_functor_cat. 
ap Nat_Trans.axioms_extensionality. 
rww vcompose_axioms. 
rw edge_plc. ap nat_trans_axioms_ple. am. am. 
cp mor_our_map. rwi mor_functor_cat H0. 
lu. am. am. 
rw edge_plc. rw source_ple. rww target_our_map. 
am. assert (mor (cone_target other) (edge other x)).
ap mor_edge. rww cone_source_other. 
am. rwi cone_target_other H0. rwi mor_functor_cat H0. 
lu. am. am. 
rw source_vcompose. rw source_edge. 
rw source_our_map. tv. rww cone_source_other. 
am. 
rw target_vcompose. rw edge_plc. rw target_edge.
rw socle_other. rw target_ple. tv. 
rww cone_source_other. am. am. 

ir. rwi osource_vcompose H0. 
ufi osource H0. rwi source_our_map H0. 
rwi source_otherv H0. 
rw ntrans_vcompose. 
rw edge_plc. 
rw otarget_ple. 
assert (ntrans our_map x0 = our_mval x0). 
rww ntrans_our_map. rw H1. 
rw ntrans_ple. 
uf our_mval. 

rw comp_edge_cone_to_limit. 

rw edge_other_pt. tv. 
am. am. app is_limit_pointl. 
app is_cone_other_pt. 
rw socle_other_pt. rww socle_pointl. am. 
rww cone_target_pointl. rww cone_source_pointl.
am. am. am. am. 
uf osource. rw source_our_map. 
rww source_otherv. am. am. 
rw mor_functor_cat. uhg; ee. rw edge_plc. 
ap nat_trans_axioms_ple. am. am. 
rw edge_plc. rww osource_ple. am. 
rw edge_plc. rww otarget_ple. am. 
am. am. ap mor_our_map. 
rw edge_plc. rw target_our_map. rww source_ple. 
am. rww cone_source_plc. 
uhg; ee. ap is_cone_plc. 
rw cone_target_plc. ap mor_our_map. 
rw target_our_map. rww vertex_plc. 
Qed.

Lemma versal_summary : 
source our_map = otherv &
target our_map = plv &
mor (functor_cat a b) our_map &
cone_compose plc our_map = other.
Proof.
ee. 
ap source_our_map. ap target_our_map. 
ap mor_our_map. 
ap cone_compose_our_map. 
Qed.




Variable another_map : E.
Hypothesis mor_another : mor (functor_cat a b) another_map.
Hypothesis source_another : source another_map = otherv.
Hypothesis target_another : target another_map = plv.
Hypothesis cone_compose_another :
cone_compose plc another_map = other.

Lemma osource_another : osource another_map = a.
Proof.
uf osource. rw source_another. rww source_otherv. 
Qed.

Lemma otarget_another : otarget another_map = b.
Proof.
uf otarget. rw target_another. rww target_plv. 
Qed.

Lemma presheaf_mor_axioms_another : 
Nat_Trans.axioms another_map.
Proof.
ir. cp mor_another. 
rwi mor_functor_cat H. lu. 
am. am. 
Qed. 

Lemma ntrans_edge_other : forall x y, ob c x ->
ob a y ->
ntrans (edge other x) y =
edge (cone_compose (pointl y) (ntrans another_map y)) x.
Proof.
ir. 
assert (lem1: Nat_Trans.axioms another_map).
cp mor_another. rwi mor_functor_cat H1. lu. 
am. am. 

wr cone_compose_another.
rw edge_cone_compose. 
rw edge_cone_compose. 
rw cone_target_plc. 
rw comp_functor_cat. 
rw cone_target_pointl. 
rw ntrans_vcompose.  
rw edge_plc. rw ntrans_ple. 
rw otarget_ple. 
tv. 
am. am. am. am. 
rww osource_another. am. am. 
am. rw edge_plc. 
rw mor_functor_cat. uhg; ee. 
ap nat_trans_axioms_ple. am. 
rww osource_ple. rww otarget_ple. 
am. am. am. 
am. 
rw target_another. rw edge_plc. rww source_ple. 
am. rww cone_source_pointl. 
uhg; ee. app  is_cone_pointl. 
rw cone_target_pointl. 
ap mor_ntrans. 
am. rww osource_another. 
rww otarget_another. am. 
rw target_ntrans. rw target_another. 
rw vertex_pointl. rw fob_plv. tv. 
am. am. 
rw osource_another. am. rww cone_source_plc. 
uhg; ee. app is_cone_plc. rww cone_target_plc. 
rww target_another. rww vertex_plc. 
Qed.



Lemma  pointwise_same : forall y, ob a y ->
ntrans another_map y = our_mval y.
Proof.
ir. 
assert (lem0: Nat_Trans.axioms another_map).
cp mor_another. rwi mor_functor_cat H0.
lu. am. am. 
assert (lem1: is_uni (pointl y)). 
cp (is_limit_pointl H). lu. 
uh lem1. ee. ap H1. 
uhg; ee. app is_cone_pointl. 
rw cone_target_pointl. 
ap mor_ntrans. 
am. rw osource_another. am. 
rww otarget_another. am. 
rw target_ntrans. 
rw target_another. rw fob_plv. 
rww vertex_pointl. am. am. 
rww osource_another. 


uhg; ee. app is_cone_pointl. rww cone_target_pointl. 
uf our_mval. ap mor_cone_to_limit. 
app is_cone_other_pt. 
app is_limit_pointl.
rw socle_other_pt. rw socle_pointl. 
reflexivity. am. am. 
rww cone_target_pointl. 
rw target_our_mval. rw vertex_pointl. tv.
am. 
ap cone_extensionality. 
rww is_cone_cone_compose. 
uhg; ee. 
app is_cone_pointl. rww cone_target_pointl. 
uf our_mval. ap mor_ntrans. am. 
rww osource_another. rww otarget_another. 
rww target_ntrans. rww target_another. 
 rw fob_plv. 
rww vertex_pointl. am. 
rww osource_another. 
rww is_cone_cone_compose. 
uhg; ee. app  is_cone_pointl. 
rww cone_target_pointl. 
uf our_mval. ap mor_cone_to_limit. 
app is_cone_other_pt. app is_limit_pointl.
rw socle_other_pt. rw socle_pointl. 
reflexivity. am. am. 
rww cone_target_pointl. rww target_our_mval.
rw vertex_cone_compose. 
rw vertex_cone_compose. rw source_ntrans.
rw source_another. rw source_our_mval. 
reflexivity. am. am. 
rww osource_another. 
rw socle_cone_compose. 
rw socle_cone_compose. reflexivity. 

ir. 
rwi cone_source_cone_compose H2. 
rwi cone_source_pointl H2. 
wrr ntrans_edge_other. 
rw edge_cone_compose. rw cone_target_pointl.
uf our_mval. 
rw comp_edge_cone_to_limit. 
rw edge_other_pt. tv. 
am. am. app is_limit_pointl. 
app is_cone_other_pt. 
rww socle_other_pt; rww socle_pointl. 
rww cone_target_pointl. 
rww cone_source_pointl. am. 
rww cone_source_pointl. 
uhg; ee. app is_cone_pointl. 
rww cone_target_pointl. 
uf our_mval. ap mor_cone_to_limit. 
app is_cone_other_pt. app is_limit_pointl.
rw socle_other_pt. rw socle_pointl. 
reflexivity. am. am. 
rww cone_target_pointl. rww target_our_mval.
am. 
Qed.

Lemma another_same : another_map = our_map.
Proof.
assert (lem0: Nat_Trans.axioms another_map).
cp mor_another. rwi mor_functor_cat H.
lu. am. am. 
ap Nat_Trans.axioms_extensionality. 
am. 
cp mor_our_map. rwi mor_functor_cat H.
lu. am. am. 
rw source_another. rw source_our_map. 
tv. rw target_another. rww target_our_map. 
ir. rwi osource_another H. 
rw ntrans_our_map. ap pointwise_same. 
am. am. 
Qed.




End Limit_Pr.

Lemma for_uni_plc : forall u,
cone_composable plc u -> u = our_map (cone_compose plc u).
Proof.
ir. 
assert (is_cone (cone_compose plc u)). 
rww is_cone_cone_compose. 
assert (socle (cone_compose plc u) = f). 
rw socle_cone_compose. rw socle_plc. tv. 
ap (another_same H0 H1). 
uh H; ee. rwi cone_target_plc H2. am. 
uf otherv. rw vertex_cone_compose. tv. 
uh H; ee. rw H3. rw vertex_plc. tv. tv. 
Qed.

Lemma is_limit_plc : is_limit plc.
Proof.
uhg; ee. 
uhg; ee; ir. ap is_cone_plc. 
rw (for_uni_plc H). 
rw H1. wr for_uni_plc. tv. am. 

uhg; ee. ap is_cone_plc. ir. 

sh (our_map b0). 
rwi socle_plc H0. 
cp (versal_summary H H0). ee. 
uhg; ee. ap is_cone_plc. 
rww cone_target_plc. rww vertex_plc. 
am.  
Qed.


Lemma cone_pushdown_point_functor_plc : forall y, ob a y ->
cone_pushdown (point_functor a b y) plc = pointl y.
Proof.
ir. 
ap cone_extensionality. 
ap is_cone_cone_pushdown. ap is_cone_plc. 
app point_functor_axioms. 
rw source_point_functor. rww cone_target_plc. 
app is_cone_pointl. 
rw vertex_cone_pushdown. rw fob_point_functor. 
rw vertex_pointl. rw vertex_plc. rw fob_plv. 
tv. am. am. am. rw vertex_plc. 
rw ob_functor_cat. uhg; ee. 
ap plv_axioms. rww source_plv. rww target_plv. 
am. am. am. 
rw socle_cone_pushdown. 
rw socle_pointl. rw socle_plc. tv. am. 


ir. rwi cone_source_cone_pushdown H0. rwi cone_source_plc H0. 
rw edge_cone_pushdown. 
rw edge_plc. rw fmor_point_functor. 
rw ntrans_ple. tv. am. am. 
rw mor_functor_cat. uhg; ee. 
app nat_trans_axioms_ple. rww osource_ple. rww otarget_ple. 
am. am. am. rww cone_source_plc. app is_cone_plc. 
Qed. 


Lemma presheaf_limit_criterion: 
has_limit f.
Proof.
uhg. 
sh plc. uhg; ee. 
ap is_limit_plc. 
rww socle_plc. 
Qed.

Lemma invertible_commutation_plc : forall y, ob a y ->
invertible b (commutation (point_functor a b y) plc (pointl y)).
Proof.
ir. 
assert (b = target (point_functor a b y)).
rww target_point_functor. 
set (k:=point_functor a b y).
rw H0. 
uf k. 
rw invertible_commutation_is_limit_cone_pushdown. 
rw cone_pushdown_point_functor_plc. 
app is_limit_pointl. am. 
ap is_cone_plc. 
app is_limit_pointl. 
rww source_point_functor. 
rww cone_target_plc. 
app point_functor_axioms. 
rw socle_plc. 
rww socle_pointl. 
tv. 
Qed.



Lemma invertible_cone_to_limit_plc :
invertible (functor_cat a b) 
(cone_to_limit plc (limit f)).
Proof.
ir. ap invertible_cone_to_limit. 
ap is_limit_plc. 
ap is_limit_limit. 
ap presheaf_limit_criterion. 
rww socle_plc. rww socle_limit. 
ap presheaf_limit_criterion. 
rww cone_target_plc. 
Qed. 

Lemma is_limit_cone_pushdown_point_functor : 
forall y, ob a y ->
is_limit (cone_pushdown (point_functor a b y) (limit f)).
Proof.
ir. 
assert (has_limit f). 
ap presheaf_limit_criterion. 
apply limit_preservation_invariance with plc. 
app point_functor_axioms. app is_limit_limit. 
ap is_limit_plc. 
rww socle_limit. 
rww socle_plc. rww source_point_functor. rww cone_target_plc. 
rww cone_pushdown_point_functor_plc. 
app is_limit_pointl. 
Qed. 

Lemma invertible_commutation_point_functor_limit :
forall y, ob a y ->
invertible b 
(commutation (point_functor a b y) (limit f) (pointl y)).
Proof.
ir. 
rw invertible_commutation_is_limit_cone_pushdown. 
ap  is_limit_cone_pushdown_point_functor. am. 
assert (is_limit (limit f)).
app is_limit_limit. 
ap presheaf_limit_criterion. 
lu. app is_limit_pointl. 
rww source_point_functor. 
uf cone_target. rww socle_limit. 
sy; am. ap presheaf_limit_criterion. 
app point_functor_axioms. 
rww socle_limit. rww socle_pointl. 
ap presheaf_limit_criterion. 
rww target_point_functor. 
Qed.

End MainResult. 

End MainResultMod. 
Import MainResultMod. 

Lemma has_limits_functor_cat : forall a b z, 
Category.axioms a -> Category.axioms b ->
Category.axioms z -> has_limits_over z b ->
has_limits_over z (functor_cat a b).
Proof.
ir. uhg; ee. 
ir. 
apply presheaf_limit_criterion with a b. 
am. am. am. am. 
ir. uh H2; ee. ap H2. 
app pointf_axioms. 
rww source_pointf. rww target_pointf. 
Qed.

(**** now by dualizing we get the theorem saying that functor cats
have colimits.  *******)


Lemma has_colimits_functor_cat : forall a b z,
Category.axioms a -> Category.axioms b ->
Category.axioms z -> has_colimits_over z b ->
has_colimits_over z (functor_cat a b).
Proof.
ir. 
assert (Category.axioms (opp a)).
app opp_axioms. 
assert (Category.axioms (opp b)).
app opp_axioms. 
assert (Category.axioms (opp z)).
app opp_axioms. 


assert (has_limits_over (opp z) (opp (functor_cat a b))).
apply has_limits_over_finverse_invariance
with (functor_cat (opp a) (opp b)). 
app functor_cat_axioms. 
ap opp_axioms. app functor_cat_axioms. 
am. app has_limits_functor_cat. 
app has_limits_over_opp. 
sh (fc_opp a b). sh (opp_fc a b). 
ee. app are_finverse_symm. 
app are_finverse_opp_fc_fc_opp. 
rw source_fc_opp. reflexivity. 
rw target_fc_opp. 
reflexivity. 

assert (z = opp (opp z)).
rww opp_opp. 
assert (functor_cat a b = opp (opp (functor_cat a b))).
sy; rw opp_opp. reflexivity. 

rw H7; rw H8. 

ap has_colimits_over_opp. ap opp_axioms. 
app functor_cat_axioms. 
am. am. 
Qed. 


End Functor_Cat_Limit. 

Export Functor_Cat_Limit. 

(************ todo: 

natural isos, (iso)equiv of cats 
(do adjoints first because the essential inverse
is the adjoint too) 
nat isos = isos in fc
products in functor_cat, switch etc

*******************)




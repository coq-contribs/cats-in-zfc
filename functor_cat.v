Set Implicit Arguments.
Unset Strict Implicit.

Require Import Arith.
Require Export nat_trans.



Module Functor_Cat.
Export Nat_Trans.

Definition fhom a b f := 
Functor.axioms f &
source f = a & target f = b.

Definition nthom f g u := 
Nat_Trans.axioms u &
source u = f & target u = g.

Definition nt2hom a b u :=
Nat_Trans.axioms u &
osource u = a & otarget u = b.


Lemma fhom_bounded : forall a b, 
Bounded.axioms (fhom a b).
Proof.
ir. 
cp (Bounded.trans_criterion (p:=fhom a b)
(f:=fun g => Arrow.create a b g) 
(x:=Function_Set.function_set (morphisms a) (fun z =>morphisms b))).
apply H. ir. 
sh (L (morphisms a) (fmor y)). ee. 
apply Function_Set.in_function_set_inc. 
apply Function_Set.in_fs_for_L. 
ir.
change (is_mor b (fmor y y0)). 
ap mor_is_mor. uh H0; ee. 
wr H3. app mor_fmor. rw H2. ap is_mor_mor. 
wr H2. lu. am. 
uh H0; ee. uh H0; ee. uh H0; ee. 
ufi Umorphism.create H0. 
set (k:= fmor y). wr H0. uf k. wr H1.
wr H2. ap uneq. 
ap Function.create_extensionality. 
tv. ir. tv.    
Qed.

Lemma nthom_bounded : forall f g, 
Bounded.axioms (nthom f g).
Proof.
ir. 
cp (Bounded.trans_criterion (p:=nthom f g)
(f:= fun u => 
Arrow.create f g (ntrans_arrow_create f (fun y => V y u)))
(x:= Function_Set.function_set (objects (source f)) 
(fun z => morphisms (target g)))). 
ap H. ir. 
sh (L (objects (source f)) (ntrans y)). ee.
apply Function_Set.in_function_set_inc. 
apply Function_Set.in_fs_for_L. 
ir.
assert (ob (source f) y0). ap is_ob_ob. 
uh H0; ee. wr H2. uh H0; ee.
exact H4.  am. 
change (is_mor (target g) (ntrans y y0)). 
ap mor_is_mor. ap mor_ntrans. lu. 
uh H0; ee. uf osource. rw H3. am. uf otarget.
uh H0; ee. rw H4.  
tv. 
uh H0; ee. assert (Nat_Trans.like y). 
lu. uh H3; ee. 
ufi create H3. 
set (k:=ntrans y). wr H3. uf k. wr H1. 
wr H2. ap uneq. uf ntrans_arrow_create. 
assert (Function.create (objects (source (source y)))
     (fun y0 : E =>
      V y0 
(Function.create (objects (source (source y))) (ntrans y))) 
=
Function.create (objects (source (source y))) (ntrans y)). 
ap Function.create_extensionality. tv. 
ir. 
rw create_V_rewrite. tv. am. rww H4. 
Qed. 


Definition functor_set a b:= (Bounded.create (fhom a b)).

Lemma inc_functor_set : forall a b u, 
inc u (functor_set a b) = fhom a b u.
Proof.
ir. uf functor_set. 
rw Bounded.inc_create. tv. ap fhom_bounded. 
Qed.

Definition nt_set f g:= (Bounded.create (nthom f g)).

Lemma inc_nt_set : forall f g u, 
inc u (nt_set f g) = nthom f g u.
Proof.
ir. uf nt_set. 
rw Bounded.inc_create. tv. ap nthom_bounded. 
Qed.



Lemma nt2hom_bounded : forall a b,
Bounded.axioms (nt2hom a b).
Proof.
ir. 
ap Bounded.criterion. 
sh (union (Image.create 
(Cartesian.product (functor_set a b) (functor_set a b))
(fun z => (nt_set (pr1 z) (pr2 z))))).
ir. 
apply union_inc with (nt_set (source y) (target y)).
rw inc_nt_set. 
uh H; ee. 
uhg; ee. am. tv. tv. 
rw Image.inc_rw. uh H; ee. 
sh (pair (source y) (target y)). ee. 
ap product_pair_inc. rw inc_functor_set. 
uhg; ee. uh H; ee. am. am. rww target_source. 
rw inc_functor_set. uhg; ee. 
uh H; ee; am. rww source_target. am. 
rw pr1_pair. rw pr2_pair. tv. 
Qed.


Definition nt2_set a b := (Bounded.create (nt2hom a b)). 

Lemma inc_nt2_set : forall a b u, 
inc u (nt2_set a b) = nt2hom a b u.
Proof.
ir. uf nt2_set. 
rw Bounded.inc_create. tv. ap nt2hom_bounded. 
Qed.

Definition functor_cat a b := 
Category.Notations.create 
(functor_set a b)
(nt2_set a b)
vcompose vident emptyset.

Lemma objects_functor_cat : forall a b,
objects (functor_cat a b) = functor_set a b.
Proof.
ir. uf functor_cat. rww objects_create. 
Qed.

Lemma morphisms_functor_cat : forall a b,
morphisms (functor_cat a b) = nt2_set a b.
Proof.
ir. uf functor_cat. rww morphisms_create. 
Qed.

Lemma is_ob_functor_cat : forall a b x,
is_ob (functor_cat a b) x = fhom a b x.
Proof.
ir. uf is_ob. rw objects_functor_cat. 
rww inc_functor_set. 
Qed.

Lemma is_mor_functor_cat : forall a b u,
is_mor (functor_cat a b) u = nt2hom a b u.
Proof.
ir. uf is_mor. rw morphisms_functor_cat. 
rww inc_nt2_set. 
Qed.

Lemma functor_cat_axioms : forall a b,
Category.axioms a -> Category.axioms b ->
Category.axioms (functor_cat a b).
Proof.
ir. uf functor_cat. 
ap Category.create_axioms. 
uhg; ee; ir. 
rw  inc_functor_set; app iff_eq; ir. 
uh H1; ee. uhg; ee. 
rw inc_functor_set. uhg; xd. 
rw inc_nt2_set. uhg; ee. rww vident_axioms. 
rww osource_vident. rww otarget_vident. 
rww source_vident. rww target_vident. 
uh H1; ee. rwi inc_functor_set H1. am. 

app iff_eq; ir. cp H1. rwi inc_nt2_set H2. 
uh H2; ee. uhg; ee. am. rw inc_functor_set. 
uhg; ee. uh H2; ee. am. am. rww target_source. 
rw inc_functor_set. uhg; ee. uh H2; ee; am. 
rww source_target. am. 
rww right_vident. rww left_vident. 
uh H2; ee. uh H2. 
ufi create H2. wr H2. 
rww Arrow.create_like. 
uh H1; ee. am. 
cp H1; cp H2. rwi inc_nt2_set H4. 
rwi inc_nt2_set H5. uh H4; uh H5; ee.
uhg; ee. am. am. am. 
rw inc_nt2_set. uhg; ee. rww vcompose_axioms. 
rww osource_vcompose. rww otarget_vcompose. 
rww source_vcompose. rww target_vcompose. 
rww vcompose_assoc. rwi inc_nt2_set H1. lu. 
rwi inc_nt2_set H2. lu. 
rwi inc_nt2_set H3. lu. 
Qed.

Lemma ob_functor_cat : forall a b x, 
Category.axioms a -> Category.axioms b ->
ob (functor_cat a b) x =
fhom a b x.
Proof.
ir. app iff_eq; ir. wr is_ob_functor_cat. 
lu. uhg; ee. 
app functor_cat_axioms. rww is_ob_functor_cat. 
Qed.

Lemma mor_functor_cat : forall a b u, 
Category.axioms a -> Category.axioms b ->
mor (functor_cat a b) u =
nt2hom a b u.
Proof.
ir. app iff_eq; ir. wr is_mor_functor_cat. 
lu. uhg; ee. 
app functor_cat_axioms. rww is_mor_functor_cat. 
Qed.


Lemma comp_functor_cat : forall a b u v,
Category.axioms a -> Category.axioms b ->
mor (functor_cat a b) u ->
mor (functor_cat a b) v ->
source u = target v -> 
comp (functor_cat a b) u v = vcompose u v.
Proof.
ir. uf functor_cat. 
rw comp_create. tv. 
rw inc_nt2_set. wrr mor_functor_cat. 
rw inc_nt2_set. wrr mor_functor_cat. 
am. 
Qed.

Lemma id_functor_cat : forall a b x,
Category.axioms a -> Category.axioms b ->
ob (functor_cat a b) x ->
id (functor_cat a b) x = vident x.
Proof.
ir. uf functor_cat; rw id_create. tv. 
rw inc_functor_set. wrr ob_functor_cat. 
Qed.


(**** we need point functors, point transfos etc. ***)

Definition point_functor a b x :=
Functor.create (functor_cat a b) b 
(fun u => ntrans u x).


Lemma source_point_functor : forall a b x,
source (point_functor a b x) = functor_cat a b.
Proof. ir. 
uf point_functor. rww Functor.source_create. 
Qed.


Lemma target_point_functor : forall a b x,
target (point_functor a b x) = b.
Proof. ir. uf point_functor. rww Functor.target_create. 
Qed.

Lemma fob_point_functor : forall a b x y,
Category.axioms a -> Category.axioms b ->
ob (functor_cat a b) y -> ob a x -> 
fob (point_functor a b x) y = fob y x.
Proof. ir.  
uf point_functor. 
rw Functor.fob_create. 
rw source_ntrans. rw source_id. tv. 
am. rw id_functor_cat. 
rww vident_axioms. rwi ob_functor_cat H1. lu. am. 
am. am. am. am. 
rw id_functor_cat. rw osource_vident. 
rwi ob_functor_cat H1. uh H1; ee. rww H3. 
am. am. am. am. am. am. 
Qed.

Lemma fmor_point_functor : forall a b x u,
mor (functor_cat a b) u -> 
fmor (point_functor a b x) u = ntrans u x.
Proof. ir. 
uf point_functor. 
rww fmor_create. 
Qed.

Lemma point_functor_axioms : forall a b x,
ob a x ->  Category.axioms b -> 
Functor.axioms (point_functor a b x).
Proof.
ir. 
assert (Category.axioms a). uh H; ee; am.  
uf point_functor. ap Functor.create_axioms.
sh (fun y => fob y x). 

uhg; dj. ap functor_cat_axioms. lu. am. am. 
rwi ob_functor_cat H4. 
uh H4; ee. wr H6. 
ap ob_fob. am. rww H5. am. am. 
rw id_functor_cat. rw ntrans_vident. 
rwi ob_functor_cat H5. uh H5; ee. 
rww H7. am. am. 
rwi ob_functor_cat H5. uh H5; ee. rww H6. 
am. am. am. am. am. 
rwi mor_functor_cat H6; ee. uh H6; ee. 
app mor_ntrans. rww H7. sy; am. am.
am. 
rww source_ntrans. 
rwi mor_functor_cat H7; uh H7; ee. am. am. 
am. rwi mor_functor_cat H7; uh H7; ee.
rww H8.  am. am. 
rww target_ntrans. rwi mor_functor_cat H8; uh H8; ee.
am. am. am. rwi mor_functor_cat H8; uh H8; ee.
rww H9. am. am. 

rw comp_functor_cat. rw ntrans_vcompose. 
rwi mor_functor_cat H9; uh H9; ee.
rww H13. am. am. 
rwi mor_functor_cat H10; uh H10; ee.
rww H12. am. am. am. am. 
am. am. am. 
Qed. 


Definition point_trans a b u :=
Nat_Trans.create (point_functor a b (source u))
(point_functor a b (target u))
(fun y => fmor y u).

Lemma source_point_trans: forall a b u,
source (point_trans a b u) = point_functor a b (source u).
Proof. ir. uf point_trans. rww Nat_Trans.source_create.
Qed.

Lemma target_point_trans : forall a b u,
target (point_trans a b u) = point_functor a b (target u).
Proof. ir. uf point_trans. rww Nat_Trans.target_create. 
Qed.

Lemma osource_point_trans : forall a b u,
osource (point_trans a b u) = functor_cat a b.
Proof. ir. 
uf osource. rw source_point_trans. 
rww source_point_functor. 
Qed.

Lemma otarget_point_trans : forall a b u,
otarget (point_trans a b u) = b.
Proof. ir. 
uf otarget. rw target_point_trans.
rww target_point_functor. 
Qed.

Lemma ntrans_point_trans : forall a b u y,
mor a u -> ob (functor_cat a b) y ->
ntrans (point_trans a b u) y = fmor y u.
Proof. ir. 
uf point_trans. rww ntrans_create.  
rw source_point_functor. 
change (is_ob (functor_cat a b) y). 
lu. 
Qed. 

Lemma point_trans_axioms : forall a b u,
mor a u -> Category.axioms b ->
Nat_Trans.axioms (point_trans a b u).
Proof.
ir. 
assert (lem1 : Category.axioms a). uh H; ee; am. 
uf point_trans. ap Nat_Trans.create_axioms. 
uhg; dj. ap point_functor_axioms. 
rwi mor_facts_rw H; lu. am. 
ap point_functor_axioms. 
rwi mor_facts_rw H; lu. am. 
rw source_point_functor. rw source_point_functor. tv. 
rw target_point_functor. rw target_point_functor. tv. 
rw target_point_functor. rwi source_point_functor H5.
rwi ob_functor_cat H5. uh H5; ee. 
wr H7. ap mor_fmor. am. rww H6. am. am. 
rwi source_point_functor H6. 
cp H6. rwi ob_functor_cat H7. uh H7; ee. 
rww fob_point_functor. rww source_fmor. 
rww H8. rww ob_source. am. am. 
rwi source_point_functor H7. cp H7. 
rwi ob_functor_cat H7. uh H7; ee. 
rww fob_point_functor. rww target_fmor. 
rww H9. rww ob_target. am. am. 

rwi source_point_functor H8. cp H8.
rwi mor_functor_cat H8. uh H8; ee. 

rww target_point_functor. 
rww fmor_point_functor. 
rww fmor_point_functor. wr H11. 
rw carre. tv. am. rww H10. am. am. 
Qed. 

Lemma vcompose_point_trans : forall a b u v,
composable a u v -> Category.axioms b ->
vcompose (point_trans a b u) (point_trans a b v) =
point_trans a b (comp a u v).
Proof.
ir. rwi composable_facts_rw H; uh H; ee. 
ap Nat_Trans.axioms_extensionality. 
rw vcompose_axioms. tv. ap point_trans_axioms. am. am. 
ap point_trans_axioms; am. 
rw source_point_trans. rw target_point_trans. 
rw H5; tv. ap point_trans_axioms. am. am. 
rw source_vcompose. rw source_point_trans. 
rw source_point_trans. rw source_comp. tv. 
am. am. am.  
rw target_vcompose. rw target_point_trans. 
rw target_point_trans. 
rw target_comp. tv. am. am. am. 
ir. rwi osource_vcompose H8. rwi osource_point_trans H8. 
rwi ob_functor_cat H8. 
rw ntrans_vcompose. 
rw otarget_point_trans. rw ntrans_point_trans. 
rw ntrans_point_trans. rw ntrans_point_trans. 
uh H8; ee. wr H10. 
rw comp_fmor. rww H9. am. rww H9. rww H9. am. 
am. rww ob_functor_cat. am. rww ob_functor_cat. am. 
rww ob_functor_cat. 
rww osource_point_trans. rww ob_functor_cat. am. am. 
Qed.


Lemma vident_point_functor : forall a b x,
ob a x -> Category.axioms b ->
vident (point_functor a b x) =
point_trans a b (id a x).
Proof.
ir. 
assert (lem1: Category.axioms a). uh H; ee; am. 
rwi ob_facts_rw H; uh H; ee. 
ap Nat_Trans.axioms_extensionality. 
rw vident_axioms. tv. ap point_functor_axioms. 
am. am. ap point_trans_axioms. am. am. 
rw source_vident. rw source_point_trans. 
rw H3. tv. 
rw target_vident. rw target_point_trans. 
rw H4; tv. 
ir. rwi osource_vident H8. rwi source_point_functor H8. 
cp H8. 
rwi ob_functor_cat H8. uh H8; ee. 
rw ntrans_vident. 
rw target_point_functor. rw fob_point_functor. 
rw ntrans_point_trans. wr H11. rw id_fob. 
rww H10. am. rww H10. am. 
rw ob_functor_cat. uhg; ee; am. am. am.  tv.
am. 

am. am. rw source_point_functor.
am. am. am. 
Qed.


Definition fc_opp a b :=
Functor.create (functor_cat (opp a) (opp b))
(opp (functor_cat a b)) 
(fun u => flip (oppnt u)).

Lemma source_fc_opp : forall a b,
source (fc_opp a b) = (functor_cat (opp a) (opp b)).
Proof.
ir. uf fc_opp. rw Functor.source_create. 
tv. 
Qed.

Lemma target_fc_opp : forall a b,
target (fc_opp a b) = (opp (functor_cat a b)).
Proof.
ir. uf fc_opp. rw Functor.target_create. 
tv. 
Qed.

Lemma fmor_fc_opp : forall a b u,
mor (functor_cat (opp a) (opp b)) u -> 
fmor (fc_opp a b) u = flip (oppnt u).
Proof.
ir. uf fc_opp. 
rw fmor_create. tv. am. 
Qed.

Lemma fob_fc_opp : forall a b f,
Category.axioms a -> Category.axioms b -> 
ob (functor_cat (opp a) (opp b)) f ->
fob (fc_opp a b) f = oppf f.
Proof.
ir. uf fob. 
rw fmor_fc_opp. rw source_flip. 
rw target_oppnt. rw source_id. tv. 
rw source_fc_opp. am. 
uf oppnt. uf create. 
rw source_fc_opp. 
rw id_functor_cat. 
rwi ob_functor_cat H1. uh H1; ee. 
rww vident_axioms. 
app  opp_axioms. app opp_axioms. 
app  opp_axioms. app opp_axioms. am. 
rw unfold_oppnt. 
uf oppnt'. uf create. 
rww Arrow.create_like. 
rw source_fc_opp. 
rw id_functor_cat. 
rwi ob_functor_cat H1. uh H1; ee. 
rww vident_axioms. 
app  opp_axioms. app opp_axioms. 
app  opp_axioms. app opp_axioms. am. 
rw source_fc_opp. ap mor_id. am. 
Qed.

Lemma fc_opp_axioms : forall a b,
Category.axioms a ->
Category.axioms b ->
Functor.axioms (fc_opp a b).
Proof.
ir. 
assert (oax : Category.axioms (opp a)).
app opp_axioms. 
assert (obx : Category.axioms (opp b)).
app opp_axioms. 
uhg; ee. 
uf fc_opp. 
uf Functor.create. 
app Umorphism.create_like. 
rw source_fc_opp. 
ap functor_cat_axioms. app opp_axioms. 
app opp_axioms. 
rw target_fc_opp. ap opp_axioms. 
ap functor_cat_axioms. am. am. 

ir. rwi source_fc_opp H1. 
cp H1. rwi ob_functor_cat H2. 
uh H2; ee. 
rw target_fc_opp. rw ob_opp. 
rw fob_fc_opp. rw ob_functor_cat. 
uhg; ee. ap oppf_axioms. am. 
rww source_oppf. rw H3. rww opp_opp. 
rw target_oppf. rw H4. rww opp_opp. 
am. am. 

am. am. am. 
rw ob_functor_cat. 
uhg; ee. am. am. am. 
app opp_axioms. app opp_axioms. 
am. am. 

ir. 
rwi source_fc_opp H1. 
cp H1. rwi ob_functor_cat H2. 
uh H2; ee. 
assert (ob (functor_cat a b) (oppf x)). 
rw ob_functor_cat. uhg; ee. 
app oppf_axioms. rw source_oppf. rw H3. 
rww opp_opp. 
am. rw target_oppf. rw H4. 
rww opp_opp. am. am. am. 
 


rw target_fc_opp. rw fob_fc_opp. 
rw fmor_fc_opp. rw source_fc_opp. 
rw id_opp. ap uneq. 
rw id_functor_cat. rw id_functor_cat. 
rw vident_oppf. tv. am. am. am. 
rw ob_functor_cat. uhg; ee; try am. 
am. am. am. am. am. 
 rw ob_opp. am. 
rw source_fc_opp. app mor_id. 
 am. am. am. am. am. 


ir. 
cp H1. rwi source_fc_opp H2. 
cp H2. rwi mor_functor_cat H3. 
uh H3. ee. 
assert (mor (functor_cat a b) (oppnt u)). 
rw mor_functor_cat. uhg; ee. 
app oppnt_axioms. rw osource_oppnt. 
rw H4. rww opp_opp. am. 
rw otarget_oppnt. 
rw H5. rww opp_opp. am. am. am. 

rw target_fc_opp. rw mor_opp. 
rw mor_functor_cat. 
uhg; ee. rw fmor_fc_opp. 
rw flip_flip. app oppnt_axioms. 
am. 
rw fmor_fc_opp. rw flip_flip. rw osource_oppnt. 
rw H4. rww opp_opp. am. 
am. 
rw fmor_fc_opp. rw flip_flip. rw otarget_oppnt. 
rw H5. rww opp_opp. am. 
am. am. am. am. am. 

ir. 
cp H1. rwi source_fc_opp H2. 
cp H2. rwi mor_functor_cat H3. 
uh H3. ee. 
assert (mor (functor_cat a b) (oppnt u)). 
rw mor_functor_cat. uhg; ee. 
app oppnt_axioms. rw osource_oppnt. 
rw H4. rww opp_opp. am. 
rw otarget_oppnt. 
rw H5. rww opp_opp. am. am. am. 

rw fmor_fc_opp. rw source_flip. rw fob_fc_opp. 
rw target_oppnt. tv. 
am. am. am. rww ob_source. 
rw unfold_oppnt. 
uf oppnt'. uf create. rww Arrow.create_like. am. 
am. am. am. 

ir. 
cp H1. rwi source_fc_opp H2. 
cp H2. rwi mor_functor_cat H3. 
uh H3. ee. 
assert (mor (functor_cat a b) (oppnt u)). 
rw mor_functor_cat. uhg; ee. 
app oppnt_axioms. rw osource_oppnt. 
rw H4. rww opp_opp. am. 
rw otarget_oppnt. 
rw H5. rww opp_opp. am. am. am. 

rw fmor_fc_opp. rw target_flip. rw fob_fc_opp. 
rw source_oppnt. tv. 
am. am. am. rw ob_target. tv. am. 
rw unfold_oppnt. 
uf oppnt'. uf create. rww Arrow.create_like. am. 
am. am. am. 

ir. 
cp H1. rwi source_fc_opp H4. 
cp H4. rwi mor_functor_cat H5. 
uh H5. ee. 
assert (mor (functor_cat a b) (oppnt u)). 
rw mor_functor_cat. uhg; ee. 
app oppnt_axioms. rw osource_oppnt. 
rw H6. rww opp_opp. am. 
rw otarget_oppnt. 
rw H7. rww opp_opp. am. am. am. 

cp H2. rwi source_fc_opp H9. 
cp H9. rwi mor_functor_cat H10. 
uh H10. ee. 
assert (mor (functor_cat a b) (oppnt v)). 
rw mor_functor_cat. uhg; ee. 
app oppnt_axioms. rw osource_oppnt. 
rw H11. rww opp_opp. am. 
rw otarget_oppnt. 
rw H12. rww opp_opp. am. am. am. 


rw target_fc_opp. rw fmor_fc_opp. 
rw fmor_fc_opp. rw comp_opp. 
rw fmor_fc_opp. ap uneq. rw source_fc_opp. 
rw flip_flip. rw flip_flip. 
rw comp_functor_cat. 
rw comp_functor_cat. rw vcompose_oppnt. 
tv. am. am. am. am. am. 
am. am. am. am. am. am. am. 
rw source_oppnt. rw target_oppnt. rw H3. tv. 

am. am. 
rw source_fc_opp. rw mor_comp. tv. 
am. am. am. reflexivity. 
rw mor_opp. 
rw flip_flip. am. 
rw mor_opp. rw flip_flip. am. 

rw source_flip. rw target_flip. 
rw target_oppnt. rw source_oppnt. 
rww H3. 
am. am. 
apply mor_arrow_like with (functor_cat a b). am. 
apply mor_arrow_like with (functor_cat a b). am. 
am. am. am. am. am. am. 
Qed.


Definition opp_fc a b := Functor.create
(opp (functor_cat a b)) (functor_cat (opp a) (opp b))
(fun u => oppnt (flip u)).
 
Lemma source_opp_fc : forall a b,
source (opp_fc a b) = opp (functor_cat a b).
Proof.
ir. uf opp_fc. rww Functor.source_create. 
Qed.

Lemma target_opp_fc : forall a b,
target (opp_fc a b) = functor_cat (opp a) (opp b).
Proof.
ir. uf opp_fc. rww Functor.target_create. 
Qed.

Lemma fmor_opp_fc : forall a b u,
mor (opp (functor_cat a b)) u -> 
fmor (opp_fc a b) u = oppnt (flip u).
Proof.
ir. uf opp_fc. 
rw fmor_create. tv. am. 
Qed. 

Lemma fob_opp_fc : forall a b x,
Category.axioms a -> Category.axioms b -> 
ob (opp (functor_cat a b)) x -> 
fob (opp_fc a b) x = oppf x.
Proof.
ir. uf fob. rw fmor_opp_fc. 
rw source_opp_fc. 
rw source_oppnt. rw target_flip. 
rw source_id. tv. am. 
apply mor_arrow_like with (opp (functor_cat a b)). 
ap mor_id. am. 
rw id_opp. rw flip_flip. 
rw id_functor_cat. 
rww vident_axioms. 
rwi ob_opp H1. rwi ob_functor_cat H1. 
uh H1; ee; am. am. am. am. am. 
rwi ob_opp H1. am. am. 
rw source_opp_fc. ap mor_id. am. 
Qed.

Lemma opp_fc_axioms : forall a b,
Category.axioms a -> Category.axioms b ->
Functor.axioms (opp_fc a b).
Proof.
ir. 
assert (oax : Category.axioms (opp a)). 
app opp_axioms. 
assert (obx :Category.axioms (opp b)). 
app opp_axioms. 
assert (fcox : Category.axioms (functor_cat (opp a) (opp b))).
ap functor_cat_axioms. am. am. 
assert (ofcx : Category.axioms (opp (functor_cat a b))).
ap opp_axioms. ap functor_cat_axioms. am. am. 
assert (sfcx : Category.axioms (source (opp_fc a b))).
rw source_opp_fc. am. 
assert (tfcx : Category.axioms (target (opp_fc a b))).
rw target_opp_fc. am. 
assert (fcx : Category.axioms (functor_cat a b)).
ap functor_cat_axioms. am. am. 

uhg; ee. 
uf opp_fc. uf Functor.create. ap Umorphism.create_like.
am. am. 

ir. 
cp H1. rwi source_opp_fc H2. 
cp H2. rwi ob_opp H3. cp H3. 
rwi ob_functor_cat H4. uh H4; ee. 
assert (ob (functor_cat (opp a) (opp b)) (oppf x)). 
rw ob_functor_cat. 
uhg; ee. ap oppf_axioms. am. rw source_oppf. rww H5. 
am. rw target_oppf. rww H6. am. am. am. 

rw target_opp_fc. 
rw fob_opp_fc. am. am. am. am. 
am. am. 


ir. 
cp H1. rwi source_opp_fc H2. 
cp H2. rwi ob_opp H3. cp H3. 
rwi ob_functor_cat H4. uh H4; ee. 
assert (ob (functor_cat (opp a) (opp b)) (oppf x)). 
rw ob_functor_cat. 

uhg; ee. ap oppf_axioms. am. rw source_oppf. rww H5. am. 
rw target_oppf.  rw H6. tv. am. am. am. 
rw target_opp_fc. rw fob_opp_fc. 
rw fmor_opp_fc. rw source_opp_fc. rw id_functor_cat. 
rw id_opp. rw flip_flip. rw id_functor_cat. 
rw vident_oppf. tv. am. am. am. 
am. rw ob_opp. am. am. am. am. 
rw source_opp_fc. ap mor_id. am. am. am. 
am. am. am. 

ir. 
cp H1. rwi source_opp_fc H2. 
cp H2. rwi mor_opp H3. cp H3. rwi mor_functor_cat H4. 
uh H4; ee. 
assert (axioms (oppnt (flip u))). 
ap oppnt_axioms. am. 

rw target_opp_fc. 
rw fmor_opp_fc. rw mor_functor_cat. 
uhg; ee. 
am. rw osource_oppnt. rww H5. am. 
rw otarget_oppnt. rww H6. am. am. am. 
am. am. am. 

ir. 
cp H1. rwi source_opp_fc H2. 
cp H2. rwi mor_opp H3. cp H3. rwi mor_functor_cat H4. 
uh H4; ee. 
assert (axioms (oppnt (flip u))). 
ap oppnt_axioms. am. 
assert (Arrow.like u). 
apply mor_arrow_like with (source (opp_fc a b)).
am. 

rw fmor_opp_fc. rw fob_opp_fc. rw source_oppnt. 
rww target_flip. rwi axioms_oppnt H7. am. 
am. am. rww ob_source. am. am. am. 


ir. 
cp H1. rwi source_opp_fc H2. 
cp H2. rwi mor_opp H3. cp H3. rwi mor_functor_cat H4. 
uh H4; ee. 
assert (axioms (oppnt (flip u))). 
ap oppnt_axioms. am. 
assert (Arrow.like u). 
apply mor_arrow_like with (source (opp_fc a b)).
am. 

rw fmor_opp_fc. rw fob_opp_fc. rw target_oppnt. 
rww source_flip. am.  am. am. 
rww ob_target. am. am. am.  


ir. 
cp H1. rwi source_opp_fc H4. 
cp H4. rwi mor_opp H5. cp H5. rwi mor_functor_cat H6. 
uh H6; ee. 
assert (axioms (oppnt (flip u))). 
ap oppnt_axioms. am. 
assert (Arrow.like u). 
apply mor_arrow_like with (source (opp_fc a b)).
am. 

cp H2. rwi source_opp_fc H11. 
cp H11. rwi mor_opp H12. cp H12. rwi mor_functor_cat H13. 
uh H13; ee. 
assert (axioms (oppnt (flip v))). 
ap oppnt_axioms. am. 
assert (Arrow.like v). 
apply mor_arrow_like with (source (opp_fc a b)).
am. 

assert (source (flip v) = target (flip u)). 
rw source_flip. rw target_flip. sy; am. am. am. 

assert (mor (functor_cat (opp a) (opp b)) (oppnt (flip u))).
rw mor_functor_cat. uhg; ee. am. 
rw osource_oppnt. rww H7. am. 
rw otarget_oppnt. ap uneq; am. am. am. am. 

assert (mor (functor_cat (opp a) (opp b)) (oppnt (flip v))).
rw mor_functor_cat. uhg; ee. am. 
rw osource_oppnt. ap uneq; am. am. 
rw otarget_oppnt. ap uneq; am. am. am. am. 


rw target_opp_fc. rw fmor_opp_fc. rw fmor_opp_fc. rw fmor_opp_fc.
rw source_opp_fc. rw comp_functor_cat. 
rw comp_opp. rw flip_flip. rw comp_functor_cat. 
rw vcompose_oppnt. reflexivity. 
am. am. am. am. am. am. am. am. 
am.  am. am. am. 
am. am. am. 
rw source_oppnt. rw target_oppnt. ap uneq. sy; am. 
am. am. rw source_opp_fc. rw mor_comp. tv. am. am. am. 
tv. am. am. am. am. am. am. 
Qed. 


Lemma are_finverse_opp_fc_fc_opp : forall a b,
Category.axioms a -> Category.axioms b ->
are_finverse (opp_fc a b) (fc_opp a b).
Proof.
ir. 
assert (Functor.axioms (opp_fc a b)). 
app opp_fc_axioms.
assert (Functor.axioms (fc_opp a b)). 
app fc_opp_axioms.
assert (source (fc_opp a b) = target (opp_fc a b)).
rw source_fc_opp. rww target_opp_fc. 
assert (source (opp_fc a b) = target (fc_opp a b)).
rw target_fc_opp. rww source_opp_fc. 


uhg; ee. am. am. am. am.  
ap Functor.axioms_extensionality. 
ap fcompose_axioms. am. am. am. 
rw fidentity_axioms. tv. 
rw source_fc_opp. ap functor_cat_axioms. 
app opp_axioms. app opp_axioms. 
rw source_fcompose. rw source_fidentity. 
reflexivity. 
rw target_fcompose. rw target_fidentity. sy; am. 

ir. 
rwi source_fcompose H5. 
cp H5. rwi source_fc_opp H6. 
cp H6. rwi mor_functor_cat H7. uh H7; ee. 
rw fmor_fcompose. rw fmor_fidentity. 
rw fmor_opp_fc. rw fmor_fc_opp. rw flip_flip. 
rw oppnt_oppnt. tv. am.  
wr target_fc_opp. ap mor_fmor. 
ap fc_opp_axioms. am. am. am. am. 
app opp_fc_axioms. app fc_opp_axioms. 
am. am. app opp_axioms. app opp_axioms. 


ap Functor.axioms_extensionality. 
ap fcompose_axioms. am. am. am. 
rw fidentity_axioms. tv. 
rw source_opp_fc. ap opp_axioms. app functor_cat_axioms. 
rw source_fcompose. rw source_fidentity. 
reflexivity. 
rw target_fcompose. rw target_fidentity. sy; am. 

ir. 
rwi source_fcompose H5. 
cp H5. rwi source_opp_fc H6. 
cp H6. rwi mor_opp H7. cp H7. rwi mor_functor_cat H8.
uh H8; ee. 
rw fmor_fcompose. rw fmor_fidentity. 
rw fmor_fc_opp. rw fmor_opp_fc.  
rw oppnt_oppnt. rw flip_flip. tv. am. 
wr target_opp_fc. ap mor_fmor. 
ap opp_fc_axioms. am. am. am. am. 
app fc_opp_axioms. app opp_fc_axioms. 
am. am. am. am. 
Qed. 

End Functor_Cat.






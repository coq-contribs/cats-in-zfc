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
Require Export cat_examples.
Require Export cardinal.
Require Export fc_limits.


Module From_Types.
Export Nat_Trans.

Record cat_type_data : Type := {
obsy : Type;
morsy : Type;
srcy : morsy -> obsy;
trgy : morsy -> obsy;
idy : obsy ->  morsy;
compy : morsy -> morsy -> morsy }.

Definition catyd_arrow d (u:morsy d) :=
Arrow.create (R (srcy u)) (R (trgy u)) (R u).

Definition catyd_arrow_set d :=
IM (catyd_arrow (d:=d)).

Lemma inc_catyd_arrow_set : forall d u,
inc u (catyd_arrow_set d) =
exists v:morsy d, u = catyd_arrow v.
Proof.
ir. ap iff_eq; ir. 
ufi catyd_arrow_set H. 
cp (IM_exists H). nin H0. sh x; sy; am. 
uf catyd_arrow_set. ap IM_inc. 
nin H. sh x; sy; am. 
Qed.

Lemma inc_catyd_arrow : forall d (u:morsy d),
inc (catyd_arrow u) (catyd_arrow_set d).
Proof.
ir. rw inc_catyd_arrow_set. 
sh u. tv. 
Qed.

Lemma arrow_catyd_arrow : forall d (u:morsy d),
arrow (catyd_arrow u) = (R u).
Proof.
ir. uf catyd_arrow. 
rw Arrow.arrow_create. tv. 
Qed.


Definition catyd_id d x := 
X (fun x0 => catyd_arrow (d:=d) (idy x0)) x.

Lemma catyd_id_R : forall d (x:obsy d),
catyd_id d (R x) = catyd_arrow (idy x).
Proof.
ir. 
uf catyd_id. 
rw X_rewrite. 
tv. 
Qed. 

Definition catyd_comp d u v :=
X (fun v0 => 
(X (fun u0 => catyd_arrow (d:=d) (compy u0 v0)) (arrow u))) 
(arrow v).



Lemma catyd_comp_catyd_arrow : forall d (u v:morsy d),
catyd_comp d (catyd_arrow u) (catyd_arrow v) = 
catyd_arrow (compy u v).
Proof.
ir. 
uf catyd_comp. rw arrow_catyd_arrow.
rw arrow_catyd_arrow. rw X_rewrite. 
rw X_rewrite. tv. 
Qed.

Lemma source_catyd_arrow : forall d (u:morsy d),
source (catyd_arrow u) = R (srcy u).
Proof.
ir. uf catyd_arrow. 
rw Arrow.source_create. tv. 
Qed.

Lemma target_catyd_arrow : forall d (u:morsy d),
target (catyd_arrow u) = R (trgy u).
Proof.
ir. uf catyd_arrow. 
rw Arrow.target_create. tv. 
Qed.



Definition catyd_property d :=
(forall (x:obsy d), srcy (idy x) = x) &
(forall (x:obsy d), trgy (idy x) = x) &
(forall (u v:morsy d), srcy u = trgy v -> 
srcy (compy u v) = srcy v) &
(forall (u v:morsy d), srcy u = trgy v -> 
trgy (compy u v) = trgy u) &
(forall (u:morsy d), compy (idy (trgy u)) u = u) &
(forall (u:morsy d), compy u (idy (srcy u)) = u) &
(forall u v w : morsy d, srcy u = trgy v -> 
srcy v = trgy w -> 
compy (compy u v) w = compy u (compy v w)).

Definition catyd d := Category.Notations.create
(obsy d) (catyd_arrow_set d) (catyd_comp d)
(catyd_id d) emptyset.

Lemma catyd_axioms : forall d,
catyd_property d -> Category.axioms (catyd d).
Proof.
ir. uf catyd. 
ap Category.create_axioms. 
uhg; ee. ir. 
ap iff_eq; ir. uhg. ee. am. 
nin H0. wr H0. rw catyd_id_R. 
ap inc_catyd_arrow. 
nin H0. wr H0. rw catyd_id_R. 
rww source_catyd_arrow. uh H; ee.
rw H. tv. 
nin H0. wr H0. rw catyd_id_R. 
rww target_catyd_arrow. uh H; ee.
rw H1. tv. 
uh H0; ee. am. 

ir. ap iff_eq; ir. 
rwi inc_catyd_arrow_set H0. nin H0. 
rw H0. 
uhg; ee; try (rw source_catyd_arrow);
try (rw target_catyd_arrow). 
rw inc_catyd_arrow_set. sh x. tv. 
ap R_inc. ap R_inc. 
rw catyd_id_R. 
rw catyd_comp_catyd_arrow. 
uh H; ee. rw H5. tv. 
rw catyd_id_R. rw catyd_comp_catyd_arrow. 
uh H; ee. rw H4. tv. 
uf catyd_arrow. rww Arrow.create_like. 
uh H0; ee; am. 

ir. rwi inc_catyd_arrow_set H0. 
rwi inc_catyd_arrow_set H1. nin H0; nin H1. 
rw H0; rw H1. 
uhg; ee. ap inc_catyd_arrow. ap inc_catyd_arrow. 
rw source_catyd_arrow. rw target_catyd_arrow. 
rwi H0 H2; rwi H1 H2. 
rwi source_catyd_arrow H2; rwi target_catyd_arrow H2. 
am. 
rw catyd_comp_catyd_arrow. ap inc_catyd_arrow. 
rw catyd_comp_catyd_arrow. rw source_catyd_arrow.
rw source_catyd_arrow. uh H; ee. 
util (H4 x x0). ap R_inj. rwi H0 H2; rwi H1 H2. 
rwi source_catyd_arrow H2; rwi target_catyd_arrow H2. 
am. rww H9. 
uh H; ee. 
util (H5 x x0). ap R_inj. rwi H0 H2; rwi H1 H2. 
rwi source_catyd_arrow H2; rwi target_catyd_arrow H2. 
am. rw catyd_comp_catyd_arrow. rw target_catyd_arrow.
rw target_catyd_arrow. rww H9. 

ir. 
rwi inc_catyd_arrow_set H0. 
rwi inc_catyd_arrow_set H1. 
rwi inc_catyd_arrow_set H2. 
nin H0; nin H1; nin H2. 
rwi H0 H3. rwi H1 H3. 
rwi H1 H4. rwi H2 H4. 
rwi source_catyd_arrow H3. 
rwi source_catyd_arrow H4. 
rwi target_catyd_arrow H3. 
rwi target_catyd_arrow H4. 
cp (R_inj H3). cp (R_inj H4). 
rw H0; rw H1; rw H2. 
rw catyd_comp_catyd_arrow. 
rw catyd_comp_catyd_arrow. 
rw catyd_comp_catyd_arrow. 
rw catyd_comp_catyd_arrow. 
uh H; ee. rw H12. 
reflexivity. am. am. 
Qed.

Lemma ob_catyd : forall d x,
catyd_property d -> 
ob (catyd d) x = 
(exists y:obsy d, x = R y).
Proof.
ir. ap iff_eq; ir. 
uh H0; ee. 
ufi catyd H1. 
rwi Category.is_ob_create H1. 
nin H1. sh x0. sy; am. 
nin H0. uf ob. ee. 
app catyd_axioms. 
uf catyd. rw Category.is_ob_create. 
rw H0. ap R_inc. 
Qed.

Lemma mor_catyd : forall d u,
catyd_property d ->
mor (catyd d) u = 
(exists v :  morsy d, u = catyd_arrow v).
Proof.
ir. ap iff_eq; ir. 
uh H0; ee. 
ufi catyd H1. 
rwi Category.is_mor_create H1. 
rwi inc_catyd_arrow_set H1. am. 
uhg; ee. 
app catyd_axioms. 
uf catyd. rw Category.is_mor_create. 
rw inc_catyd_arrow_set. am. 
Qed.

Lemma ob_catyd_R : forall d (x:obsy d),
catyd_property d -> 
ob (catyd d) (R x).
Proof.
ir. rw ob_catyd. sh x; tv. am. 
Qed. 

Lemma mor_catyd_catyd_arrow : forall d (u:morsy d),
catyd_property d ->
mor (catyd d) (catyd_arrow u).
Proof.
ir. rw mor_catyd. sh u; tv. am.
Qed. 




Definition ob_lift d x (H:ob (catyd d) x) : obsy d.
ir. 
assert (inc x (obsy d)). 
uh H; ee. ufi catyd H0. 
rwi Category.is_ob_create H0. am. 
exact (B H0).  
Defined. 

Lemma B_irrelevant : forall a x y (Hx : inc x a) (Hy : inc y a),
x=y -> B Hx = B Hy.
Proof.
ir. ap R_inj. rw B_eq. rw B_eq. am. 
Qed.



Lemma R_ob_lift : forall d x (H:ob (catyd d) x),
R (ob_lift H) = x.
Proof.
ir. 
assert (ob (catyd d) x).
am. 
uh H0; ee. 
ufi catyd H1. 
rwi Category.is_ob_create H1. 
assert (ob_lift H = B H1). 
uf ob_lift. 
ap B_irrelevant. tv. rw H2. rw B_eq. tv. 
Qed.

Lemma eq_ob_lift : forall d x (H:ob (catyd d) x) (y:(obsy d)),
x = R y -> y = ob_lift H.
Proof.
ir. ap R_inj. rw R_ob_lift. sy; am. 
Qed.

Definition mor_lift d u (H:mor (catyd d) u) : morsy d.
ir. 
assert (is_mor (catyd d) u). 
uh H; ee. am. ufi catyd H0. 
rwi Category.is_mor_create H0. 
ufi  catyd_arrow_set H0. 
exact (IM_lift (B H0)). 
Defined. 

Lemma unIM_lift : forall a (f:a->E) (x y:IM f),
x = y -> IM_lift x = IM_lift y.
Proof.
ir. rw H. tv. 
Qed.

Lemma catyd_arrow_mor_lift : forall d u (H: mor (catyd d) u),
catyd_arrow (mor_lift H) = u.
Proof.
ir. 
assert (mor (catyd d) u). am. 
uh H0; ee. ufi catyd H1. 
rwi is_mor_create H1. 
ufi catyd_arrow_set H1. 
assert (mor_lift H = IM_lift (B H1)). 
uf mor_lift. 
apply unIM_lift. 
ap B_irrelevant. tv. rw H2. 
rw IM_lift_pr. rw B_eq. tv. 
Qed.

Lemma R_srcy_mor_lift : forall d u (H:mor (catyd d) u),
R (srcy (mor_lift H)) = source u.
Proof.
ir. cp (catyd_arrow_mor_lift H).
assert (source u = source (catyd_arrow (d:=d) (mor_lift H))).
rww H0. 
rw H1. 
rw source_catyd_arrow. tv.  
Qed.

Lemma R_trgy_mor_lift : forall d u (H:mor (catyd d) u),
R (trgy (mor_lift H)) = target u.
Proof.
ir. cp (catyd_arrow_mor_lift H).
assert (target u = target (catyd_arrow (d:=d) (mor_lift H))).
rww H0. 
rw H1. 
rw target_catyd_arrow. tv.  
Qed.

Lemma inc_obsy : forall d x, ob (catyd d) x -> inc x (obsy d).
Proof.
ir. uh H; ee. ufi catyd H0. 
rwi is_ob_create H0. am. 
Qed.


Lemma show_inc_catyd_arrow_set : forall d u,
mor (catyd d) u -> inc u (catyd_arrow_set d).
Proof.
ir. uh H; ee. 
ufi catyd H0. 
rwi is_mor_create H0. am. 
Qed. 

Lemma comp_catyd : forall d u v,
mor (catyd d) u -> mor (catyd d) v ->
source u = target v -> 
comp (catyd d) u v = catyd_comp d u v.
Proof.
ir. uf catyd. 
rw comp_create. tv. 
app show_inc_catyd_arrow_set. 
app show_inc_catyd_arrow_set. 
am. 
Qed.

Lemma id_catyd : forall d x,
ob (catyd d) x -> 
id (catyd d) x = catyd_id d x.
Proof.
ir. uf catyd. rw id_create. tv. 
app inc_obsy. 
Qed. 

Lemma id_catyd_R : forall d (x:obsy d),
catyd_property d -> 
id (catyd d) (R x) = catyd_arrow (idy x).
Proof.
ir. rw id_catyd. 
rw catyd_id_R. tv. 
ap ob_catyd_R. am. 
Qed.


Lemma catyd_arrow_idy_ob_lift : forall d x (H:ob (catyd d) x),
catyd_arrow (idy (ob_lift H)) = id (catyd d) x.
Proof.
ir. cp (R_ob_lift H).
assert (id (catyd d) x = id (catyd d) (R (ob_lift H))). 
rww H0. 
rw H1. 
uf catyd. rw Category.id_create. rw catyd_id_R. tv. 
rw H0. cp H.  
app inc_obsy. 
Qed. 



Lemma catyd_arrow_compy_mor_lift : forall d u v
(Hu : mor (catyd d) u) (Hv : mor (catyd d) v),
source u = target v ->
catyd_arrow (compy (mor_lift Hu)  (mor_lift Hv)) =
comp (catyd d) u v.
Proof.
ir. cp (catyd_arrow_mor_lift Hu). 
cp (catyd_arrow_mor_lift Hv). 
assert (comp (catyd d) u v = comp (catyd d)
(catyd_arrow (d:=d) (mor_lift Hu))
(catyd_arrow (d:=d) (mor_lift Hv))).
rw H0; rww H1. 
rw H2. rw comp_catyd. 
rw catyd_comp_catyd_arrow. tv. 
rww H0. rww H1. 
rw catyd_arrow_mor_lift. 
rww catyd_arrow_mor_lift. 
Qed. 


Lemma comp_catyd_catyd_arrow : forall d (u v:morsy d),
catyd_property d -> srcy u = trgy v ->
comp (catyd d) (catyd_arrow u) (catyd_arrow v) =
catyd_arrow (compy u v).
Proof.
ir. rw comp_catyd. 
rw catyd_comp_catyd_arrow. tv. 
rw mor_catyd. sh u; tv. am. 
rw mor_catyd. sh v; tv. am. 
rw source_catyd_arrow. 
rw target_catyd_arrow. rww H0. 
Qed. 







Record fun_type_data (d:cat_type_data): Type := {
ft : E;
fo : obsy d -> E;
fm : morsy d -> E }.



Definition funtyd_fmor d (f:fun_type_data d) u :=
X (fm f) (arrow u).  


Definition funtyd_property d (f:fun_type_data d):=
Category.axioms (ft f) &
catyd_property d &
(forall (x:obsy d), ob (ft f) (fo f x) )&
(forall (u:morsy d), mor (ft f) (fm f u) )&
(forall (u:morsy d), source (fm f u) = fo f (srcy u) )&
(forall (u:morsy d), target (fm f u) = fo f (trgy u)) &
(forall (x:obsy d), id (ft f) (fo f x) = fm f (idy x)) &
(forall (u v:morsy d), srcy u = trgy v -> comp (ft f) 
(fm f u) (fm f v) =
fm f (compy u v)).



Definition funtyd d (f:fun_type_data d):=
Functor.create (catyd d) (ft f) (funtyd_fmor f).

Lemma source_funtyd : forall d (f:fun_type_data d),
source (funtyd f) = catyd d.
Proof.
ir. uf funtyd. rww Functor.source_create. 
Qed.

Lemma target_funtyd : forall d (f:fun_type_data d),
target (funtyd f) = (ft f).
Proof.
ir. uf funtyd. rww Functor.target_create. 
Qed.


Lemma fmor_funtyd : forall d (f:fun_type_data d) u,
mor (source (funtyd f)) u -> 
fmor (funtyd f) u = funtyd_fmor f u.
Proof.
ir. uf funtyd. rww fmor_create. 
rwi source_funtyd H. am. 
Qed.

Lemma fob_funtyd : forall d (f:fun_type_data d) x,
funtyd_property f ->
ob (source (funtyd f)) x -> 
fob (funtyd f) x = X (fo f) x.
Proof.
ir. 
uf fob. 
rww fmor_funtyd. 
rw source_funtyd. 
rwi source_funtyd H0. 

cp (R_ob_lift H0). 
wr H1. 
rw X_rewrite. 
uh H; ee. 
rw id_catyd. rw catyd_id_R. 
uf funtyd_fmor. rw arrow_catyd_arrow. 
rw X_rewrite. wr H7. rw source_id. tv. ap H3. 
rw R_ob_lift. am. 
rw source_funtyd. ap mor_id. 
rwi source_funtyd H0; am.   
Qed.




Lemma fob_funtyd_R : forall d (f:fun_type_data d) 
(x:obsy d),
funtyd_property f ->
fob (funtyd f) (R x) = fo f x.
Proof.
ir. 
rewrite fob_funtyd. ap X_rewrite. 
am. rw source_funtyd. ap ob_catyd_R. uh H; ee; am. 
Qed.

Lemma fmor_funtyd_catyd_arrow : 
forall d (f:fun_type_data d) (u:morsy d),
funtyd_property f -> 
fmor (funtyd f) (catyd_arrow u) = fm f u.
Proof.
ir. rw fmor_funtyd. 
uf funtyd_fmor. rw arrow_catyd_arrow. 
rw X_rewrite. tv. 
rw source_funtyd. 
ap mor_catyd_catyd_arrow. 
uh H; ee; am. 
Qed.




Lemma funtyd_axioms : forall d (f:fun_type_data d),
funtyd_property f -> Functor.axioms (funtyd f).
Proof.
ir. 
uhg; ee. 
uf funtyd. uf Functor.create. 
ap Umorphism.create_like. 
rw source_funtyd. ap catyd_axioms. 
uh H; ee; am. 
rw target_funtyd. uh H; ee; am. 
ir. rwi source_funtyd H0. 
rw target_funtyd. 
cp (R_ob_lift H0). wr H1. 
rw fob_funtyd_R. uh H; ee.
ap H3. am. 

ir. rwi source_funtyd H0. 
rw target_funtyd. 
rw source_funtyd. 
cp (R_ob_lift H0). 
wr H1. rw fob_funtyd_R. 
rw id_catyd_R. 
rw fmor_funtyd_catyd_arrow. 
uh H; ee. ap H7. 
am. uh H; ee; am. am. 

ir. rwi source_funtyd H0. 
rw target_funtyd. 
cp (catyd_arrow_mor_lift H0).
wr H1. 
rw fmor_funtyd_catyd_arrow. uh H; ee. 
ap H4. am. 

ir. rwi source_funtyd H0. 
cp (catyd_arrow_mor_lift H0).
wr H1. 
rw fmor_funtyd_catyd_arrow. 
rw source_catyd_arrow. 
rw fob_funtyd_R. 
uh H; ee. 
ap H5. am. am. 

ir. rwi source_funtyd H0. 
cp (catyd_arrow_mor_lift H0).
wr H1. 
rw fmor_funtyd_catyd_arrow. 
rw target_catyd_arrow. 
rw fob_funtyd_R. 
uh H; ee. 
ap H6. am. am. 

rw source_funtyd. 
rw target_funtyd. 

ir. 
cp (catyd_arrow_mor_lift H0).
cp (catyd_arrow_mor_lift H1).
wr H3; wr H4. 
rw fmor_funtyd_catyd_arrow. 
rw fmor_funtyd_catyd_arrow. 
rw comp_catyd_catyd_arrow. 
rw fmor_funtyd_catyd_arrow. 
uh H; ee. ap H11. 
ap R_inj. rw R_srcy_mor_lift. 
rw R_trgy_mor_lift. am. 
am. uh H; ee; am. 
ap R_inj. rw R_srcy_mor_lift. 
rw R_trgy_mor_lift. am. 
am. am. 
Qed.


Definition funtyd_lift d g :=
Build_fun_type_data 
(target g)
(fun (x:obsy d) => fob g (R x))
(fun (u:morsy d) => fmor g (catyd_arrow u)).



Lemma ft_funtyd_lift : forall d g,
ft (funtyd_lift d g) = (target g).
Proof.
ir. tv. 
Qed.

Lemma fo_funtyd_lift : forall d g (x:obsy d),
fo (funtyd_lift d g) x = fob g (R x).
Proof.
ir. tv. 
Qed.

Lemma fm_funtyd_lift : forall d g (u:morsy d),
fm (funtyd_lift d g) u = fmor g (catyd_arrow u).
Proof.
ir. tv. 
Qed.

Lemma funtyd_fmor_funtyd_lift : forall d g u,
Functor.axioms g -> catyd_property d ->
source g = catyd d -> 
mor (source g) u ->
funtyd_fmor (funtyd_lift d g) u = fmor g u.
Proof.
ir. 
uf funtyd_fmor. 
cp H2. rwi H1 H3. rwi mor_catyd H3. nin H3. 
rw H3. 
rw arrow_catyd_arrow. rw X_rewrite. 
rw fm_funtyd_lift. tv. am. 
Qed. 



Lemma funtyd_lift_property : 
forall d g,
Functor.axioms g -> catyd_property d ->
source g = catyd d -> 
funtyd_property (funtyd_lift d g).
Proof.
ir. 
uhg; ee; ir.
rw ft_funtyd_lift. 
uh H; ee; am. 
am. 
rw ft_funtyd_lift; rw fo_funtyd_lift. 
ap ob_fob. am. rw H1. ap ob_catyd_R. am. 
rw ft_funtyd_lift; rw fm_funtyd_lift. 
ap mor_fmor. am. rw H1. 
ap mor_catyd_catyd_arrow. am. 
rw fm_funtyd_lift;
rw fo_funtyd_lift. 
rw source_fmor. ap uneq. 
rw source_catyd_arrow. 
tv. am. 
rw H1. ap mor_catyd_catyd_arrow. am. 


rw fm_funtyd_lift. 
rw fo_funtyd_lift. rw target_fmor. 
rw target_catyd_arrow. 
tv. am. 
rw H1. ap mor_catyd_catyd_arrow. am. 

rw ft_funtyd_lift. rw fo_funtyd_lift. 
rw fm_funtyd_lift. rw id_fob. 
rw H1. rw id_catyd_R. reflexivity. 
am. am. rw H1. ap ob_catyd_R. am. 

rw ft_funtyd_lift. rw fm_funtyd_lift. 
rw fm_funtyd_lift. rw comp_fmor. 
rw fm_funtyd_lift. 
rw H1. rw comp_catyd_catyd_arrow. tv. 
am. am. am. 
rw H1. app mor_catyd_catyd_arrow. 
rw H1. app mor_catyd_catyd_arrow. 
rw source_catyd_arrow. 
rw target_catyd_arrow. 
rww H2.  
Qed.



Lemma funtyd_funtyd_lift : forall d g,
Functor.axioms g -> catyd_property d -> 
source g = catyd d ->
funtyd (funtyd_lift d g) = g.
Proof.
ir. 
ap Functor.axioms_extensionality. 
ap funtyd_axioms. app funtyd_lift_property. 
am. 
rww source_funtyd. 
sy; am. 
rw target_funtyd. rw ft_funtyd_lift. 
tv. 

ir. cp H2. rwi source_funtyd H2. 
rw fmor_funtyd. 

rww funtyd_fmor_funtyd_lift. rww H1. am. 
Qed. 




Definition nttyd d (f g : fun_type_data d) (n : obsy d -> E) :=
Nat_Trans.create (funtyd f) (funtyd g) (X n).

Lemma source_nttyd : forall d f g (n : obsy d -> E),
source (nttyd f g n) = (funtyd f).
Proof.
ir. uf nttyd. rw Nat_Trans.source_create.
tv. 
Qed.

Lemma target_nttyd : forall d f g (n : obsy d -> E),
target (nttyd f g n) = (funtyd g).
Proof.
ir. uf nttyd. rw Nat_Trans.target_create.
tv. 
Qed.

Lemma osource_nttyd : forall d f g (n : obsy d -> E),
osource (nttyd f g n) = catyd d.
Proof.
ir. uf osource. rw source_nttyd. rww source_funtyd. 

Qed. 

Lemma otarget_nttyd : forall d f g (n : obsy d -> E),
otarget (nttyd f g n) = ft g.
Proof.
ir. uf otarget. rw target_nttyd. rww target_funtyd. 
Qed. 


Lemma ntrans_nttyd : forall d f g (n : obsy d -> E) x,
ob (catyd d) x -> 
ntrans (nttyd f g n) x = X n x.
Proof.
ir. uf nttyd. rw ntrans_create. tv. 
rw source_funtyd. uh H; ee. am. 
Qed.

Lemma ntrans_nttyd_R : forall d f g (n : obsy d -> E) (x:obsy d),
catyd_property d -> 
ntrans (nttyd f g n) (R x) = n x.
Proof.
ir. rw ntrans_nttyd. rww X_rewrite. 
app ob_catyd_R. 
Qed. 

Definition nttyd_property d (f g:fun_type_data d) 
(n : obsy d -> E) :=
catyd_property d &
funtyd_property f &
funtyd_property g &
ft f = ft g &
(forall (x:obsy d), mor (ft f) (n x)) &
(forall (x:obsy d), source (n x) = fo f x) &
(forall (x:obsy d), target (n x) = fo g x) &
(forall (u:morsy d), 
comp (ft f) (n (trgy u)) (fm f u) =
comp (ft f) (fm g u) (n (srcy u))).

Lemma nttyd_axioms : forall d f g (n:obsy d -> E),
nttyd_property f g n ->
Nat_Trans.axioms (nttyd f g n).
Proof.
ir. 
assert (lem1: catyd_property d).
uh H; ee. uh H0; ee; am. 
assert (lem2: Category.axioms (catyd d)).
app catyd_axioms. 
assert (lem3 : funtyd_property f).
uh H; ee; am. 
assert (lem4 : funtyd_property g).
uh H; ee; am. 
assert (lem5 : Functor.axioms (funtyd f)).
app funtyd_axioms. 
assert (lem6 : Functor.axioms (funtyd g)).
app funtyd_axioms. 

uhg; ee. uf nttyd. 
ap create_like. rww osource_nttyd. 
rw otarget_nttyd. uh H; ee. 
uh H1; ee. am. 
rww source_nttyd. 
rww target_nttyd. 
rww target_nttyd. rww osource_nttyd. 
rww source_funtyd. 
rww source_nttyd. rww otarget_nttyd. 
rww target_funtyd. uh H; ee; am. 

ir. rw otarget_nttyd. rwi osource_nttyd H0. 
cp H0. rw ntrans_nttyd. rwi ob_catyd H1. 
nin H1. rw H1. rw X_rewrite. 
uh H; ee. wr H4; au. am. am. 

ir. rwi osource_nttyd H0. cp H0. rwi ob_catyd H0. 
nin H0. rww ntrans_nttyd. 
rww source_nttyd. rw H0. rw X_rewrite. 
rw fob_funtyd_R. uh H; ee. ap H6. am. am. 

ir.   rwi osource_nttyd H0. cp H0. rwi ob_catyd H0. 
nin H0. rw H0. rw ntrans_nttyd_R. rw target_nttyd. 
rw fob_funtyd_R. uh H; ee; au. am. am. am. 

ir. rwi osource_nttyd H0. cp H0. 
rwi mor_catyd H1. 
nin H1. rw H1. rw target_catyd_arrow. 
rw ntrans_nttyd_R. rw otarget_nttyd. 
rw source_nttyd. 
rw fmor_funtyd_catyd_arrow. rw target_nttyd. 
rw fmor_funtyd_catyd_arrow. 
rw source_catyd_arrow. rw ntrans_nttyd_R. 
uh H; ee. wr H4. ap H8. am. am. am. am. 
am.  
Qed.

Lemma nttyd_property_ntrans_R : forall d (f g:fun_type_data d) u, 
Nat_Trans.axioms u ->
funtyd_property f -> funtyd_property g ->
source u = funtyd f -> target u = funtyd g ->
nttyd_property f g (fun (x:obsy d) => ntrans u (R x)).
Proof.
ir. 
assert (lem1 : ft f = otarget u).
wr target_source. 
rw H2. rww target_funtyd. am. 
assert (lem2 : ft g = otarget u). 
uf otarget. rw H3. rww target_funtyd. 

assert (lem3 : osource u = catyd d).
uf osource. rw H2. rww source_funtyd. 

uhg; dj. 
uh H0; ee; am. am. am. 
rw lem1; rww lem2. 
rw lem1. ap mor_ntrans. am. 
rw lem3. ap ob_catyd_R. am. tv. 
rw source_ntrans. rw H2. 
rww fob_funtyd_R. am. 
rw lem3. ap ob_catyd_R. am. 
rw target_ntrans. rw H3. 
rww fob_funtyd_R. am. 
rw lem3. app ob_catyd_R. 

rw lem1. 
wr fmor_funtyd_catyd_arrow. 
wr fmor_funtyd_catyd_arrow. wr H2; wr H3. 
wr target_catyd_arrow. 
wr source_catyd_arrow. 
app carre. rw lem3. 
ap mor_catyd_catyd_arrow. am. am. am. 
Qed.

Lemma nttyd_ntrans_R : forall d (f g:fun_type_data d) u, 
Nat_Trans.axioms u ->
funtyd_property f -> funtyd_property g ->
source u = funtyd f -> target u = funtyd g ->
nttyd f g (fun (x:obsy d) => ntrans u (R x)) = u.
Proof.
ir. 
assert (lem0:catyd_property d).
uh H0; ee; am. 
assert (lem1 : ft f = otarget u).
wr target_source. 
rw H2. rww target_funtyd. am. 
assert (lem2 : ft g = otarget u). 
uf otarget. rw H3. rww target_funtyd. 

assert (lem3 : osource u = catyd d).
uf osource. rw H2. rww source_funtyd. 

ap Nat_Trans.axioms_extensionality. 
ap nttyd_axioms. app nttyd_property_ntrans_R. 
am. 
rw source_nttyd. sy; am. rw target_nttyd. sy; am. 

ir. rwi osource_nttyd H4. cp H4. 
rwi ob_catyd H5. nin H5. rw H5. 
rw ntrans_nttyd_R. tv. 
am. am. 
Qed.

(***** we now write a tactic which will verify
by direct computation that d satisfies catyd_property,
for objects d:cat_type_data where obsy d and morsy d
are finite inductive objects, and where the 
maps srcy d, trgy d, idsy d and compy d are defined by
a match construction. ******************************)

Ltac show_catyd_property :=
match goal with 
|- (catyd_property _) => 
uf catyd_property; ee; 
first [
solve 
[(intros fty_u fty_v fty_w fty_h1 fty_h2); 
nin fty_u; nin fty_v; nin fty_w;
try reflexivity; 
try (discriminate fty_h1); try (discriminate fty_h2)] |
solve 
[intros fty_u fty_v fty_h1; 
nin fty_u; nin fty_v;
try reflexivity; try (discriminate fty_h1)] | 
solve [intro fty_x; 
nin fty_x; reflexivity] ]
| |- _ => fail
end. 

Lemma ft_Build_fun_type_data : forall d a o m,
ft (Build_fun_type_data (d:=d) a o m) = a.
Proof.
ir. reflexivity. 
Qed.

Lemma fo_Build_fun_type_data : forall d a o m,
fo (Build_fun_type_data (d:=d) a o m) = o.
Proof.
ir. reflexivity. 
Qed.

Lemma fm_Build_fun_type_data : forall d a o m,
fm (Build_fun_type_data (d:=d) a o m) = m.
Proof.
ir. reflexivity. 
Qed.


(***** here is a tactic to start the proof of
funtyd_property f where f is an explicitly defined
fun_type_data; it generates a lot of subgoals
which then have to be treated by piping to other try tactics
according to the context *************************)

Ltac start_funtyd_proof :=
match goal with 
|- (funtyd_property _) =>
(uhg; ee; try (rw ft_Build_fun_type_data);
try (rw fo_Build_fun_type_data);
try (rw fm_Build_fun_type_data);
try show_catyd_property;
try (intros fu_x fu_y hyp1;
nin fu_x; nin fu_y; try (discriminate hyp1));
try (intros fu_x; nin fu_x))
| _ => fail
end.

(*** now here is a tactic to follow up start_funtyd_proof,
where we try to dispatch as many goals as possible;
for simple examples it should be sufficient (see below) ****)

Ltac funtyd_dispatch :=
try am; try (sy; am); try reflexivity;
match goal with 
|- (Category.axioms _) => lu 
| |- (ob _ (source _)) => rww ob_source
| |- (ob _ (target _)) => rww ob_target
| |- (mor _ (id _ _)) => app mor_id; funtyd_dispatch
| |- (source (id _ _) = _) => rww source_id; funtyd_dispatch
| |- (target (id _ _) = _) => rww target_id; funtyd_dispatch
| |- (comp _ (id _ _) _ = _) => rww left_id; funtyd_dispatch 
| |- (comp _ _ (id _ _) = _) => rww right_id; funtyd_dispatch
| _ => idtac
end. 


End From_Types.


Module Finite_Cat.
Export Map.
Export From_Types.
Export Cardinal. 
Export Functor_Cat.

Definition is_finite_cat a :=
Category.axioms a &
is_finite (objects a) &
is_finite (morphisms a).

Lemma objects_catyd : forall (d:cat_type_data),
objects (catyd d) = obsy d.
Proof.
ir. uf catyd. 
rw Notations.objects_create. tv. 
Qed. 

Lemma tcreate_axioms : forall x (f:x->E),
Function.axioms (tcreate f).
Proof.
ir. uf tcreate. 
ap Function.create_axioms. 
Qed. 

Lemma are_isomorphic_morphisms_catyd :
forall (d:cat_type_data), catyd_property d -> 
are_isomorphic (morsy d)
(morphisms (catyd d)).  
Proof.
ir. uhg. 
sh (Function.tcreate (fun y :morsy d => catyd_arrow y)). 
uhg; dj. 
uhg; ee. 
ap tcreate_axioms. 
rww domain_tcreate. 
uhg; ir. 
rwi range_inc_rw H0. 
nin H0. ee. rwi domain_tcreate H0. 
assert (x0 = R (B H0)).  
rww B_eq. 
rwi H2 H1. 
rwi tcreate_value_type H1. rw H1. 
change (is_mor (catyd d) (catyd_arrow (B H0))). 
ap mor_is_mor. ap mor_catyd_catyd_arrow. am. 
ap tcreate_axioms. 

uhg; ee. am. 
uhg. ir. sh (arrow x). ee. 
assert (mor (catyd d) x). 
ap is_mor_mor. app catyd_axioms. am. 
rwi mor_catyd H2. nin H2. 
rw H2. rw arrow_catyd_arrow.
ap R_inc. am. 

assert (mor (catyd d) x). 
ap is_mor_mor. app catyd_axioms. am. 
rwi mor_catyd H2. nin H2. 
rw H2. rw arrow_catyd_arrow.
rw tcreate_value_type. tv. am. 

uhg. ee; try am. 
uhg. ir. 
cp (B_eq H2). cp (B_eq H3). wri H5 H4. 
wri H6 H4. 
rwi tcreate_value_type H4. rwi tcreate_value_type H4. 
transitivity (arrow (catyd_arrow (B H2))). 
rww arrow_catyd_arrow. sy; am. 
rw H4. rw arrow_catyd_arrow. am. 
Qed.

Lemma is_finite_catyd : forall (d:cat_type_data),
catyd_property d -> 
is_finite (obsy d) -> is_finite (morsy d) ->
is_finite_cat (catyd d).
Proof.
ir. uhg. ee. 
app catyd_axioms. 
rww objects_catyd. ap finite_invariant.
sh (morsy d). ee. 
ap are_isomorphic_morphisms_catyd. am. am. 
Qed. 

Definition has_finite_limits b :=
Category.axioms b &
(forall c, is_finite_cat c -> has_limits_over c b).

Lemma has_finite_limits_functor_cat : forall a b,
Category.axioms a -> has_finite_limits b ->
has_finite_limits (functor_cat a b).
Proof.
ir. 
uh H0; uhg; ee. app functor_cat_axioms. 
ir. ap  has_limits_functor_cat. 
am. am. uh H2; ee; am. 
ap H1; am. 
Qed. 

Lemma opp_morphisms_isomorphic : forall a,
Category.axioms a -> are_isomorphic (morphisms a)
(morphisms (opp a)).
Proof.
ir. rw iso_trans_ex_rw. 
sh flip. uhg; dj. 
uhg. ir. assert (mor a x).
app is_mor_mor. 
change (is_mor (opp a) (flip x)). ap mor_is_mor.
rw mor_opp. rww flip_flip. 
uhg; ee. am. 
uhg. ir. 
assert (mor (opp a) x). 
ap is_mor_mor. app opp_axioms. 
am. sh (flip x). ee. 
change (is_mor a (flip x)). 
ap mor_is_mor. wr mor_opp. am. 
rww flip_flip. 
uhg; ee. am. uhg. ir. transitivity (flip (flip x)).
rww flip_flip. rw H4. rww flip_flip. 
Qed.




Lemma is_finite_cat_opp : forall a,
is_finite_cat a -> is_finite_cat (opp a).
Proof.
ir. 
uhg; dj. ap opp_axioms. uh H; ee; am. 
assert (objects (opp a) = objects a).
ap extensionality; uhg; ir. 
assert (ob (opp a) x). app is_ob_ob. 
ap ob_is_ob. wr ob_opp. am. 
assert (ob a x). ap is_ob_ob. 
wrr axioms_opp. am. ap ob_is_ob. 
rww ob_opp. 

rw H1. uh H; ee; am. 
ap finite_invariant. 
sh (morphisms a). ee. 
ap opp_morphisms_isomorphic. wrr axioms_opp. 
uh H; ee. am. 
Qed.


Definition has_finite_colimits b :=
Category.axioms b &
(forall c, is_finite_cat c -> has_colimits_over c b).

Lemma finite_colimits_finite_limits_opp : forall b,
has_finite_colimits b = has_finite_limits (opp b).
Proof.
ir. ap iff_eq; ir. 
uh H; uhg; ee. app opp_axioms. ir. 
assert (c = opp (opp c)). rww opp_opp.
rw H2. 
ap has_limits_over_opp. am. ap opp_axioms. 
uh H1; ee; am. ap H0. ap is_finite_cat_opp. am. 

uh H; uhg; ee. wrr axioms_opp. 
ir. 
assert (c = opp (opp c)). rww opp_opp.
assert (b = opp (opp b)). rww opp_opp.
rw H2; rw H3. 
ap has_colimits_over_opp. am. 
ap opp_axioms. uh H1; ee; am. 
ap H0. app is_finite_cat_opp. 
Qed.

Lemma has_finite_colimits_functor_cat : forall a b,
Category.axioms a -> has_finite_colimits b ->
has_finite_colimits (functor_cat a b).
Proof.
ir. 
uh H0; uhg; ee. app functor_cat_axioms. 
ir. 
ap  has_colimits_functor_cat. am. am. 
uh H2; ee; am. app H1. 
Qed. 





End Finite_Cat.





Module Twoarrow_Cat.
Export From_Types.
Export Finite_Cat. 

Inductive ta_obs : Set := 
o1 : ta_obs | o2 : ta_obs.

Inductive ta_maps : Set := 
i1 : ta_maps | i2 : ta_maps | a0 : ta_maps | a1 : ta_maps.

Definition ta_src u :=
match u with
i1 => o1 | i2 => o2 | a0 => o1 | a1 => o1 end.

Definition ta_trg u :=
match u with 
i1 => o1 | i2 => o2 | a0 => o2 | a1 => o2 end.

Definition ta_id x := 
match x with
o1 => i1 | o2 => i2 end.

Definition ta_comp u v :=
match (u, v) with
(i1, v') => v' |
(i2, v') => v' |
(u', i1) => u' |
(u', i2) => u' |
_ => i1 end.

Definition twoarrow_data := 
Build_cat_type_data ta_src ta_trg ta_id ta_comp. 


Lemma twoarrow_data_property : catyd_property twoarrow_data.
Proof.
show_catyd_property. 
Qed.

Definition twoarrow_cat := catyd twoarrow_data.

Lemma twoarrow_cat_axioms : Category.axioms twoarrow_cat.
Proof.
uf twoarrow_cat. ap catyd_axioms. ap twoarrow_data_property. 
Qed.



(*** the constructions (R o1) and (R o2) dont work
well with the implicit arguments mechanism because they
don't introduce the type (obsy _); it is better to redefine
the objects ***)

Definition o1' : obsy twoarrow_data := o1.
Definition o2' : obsy twoarrow_data := o2. 

Definition i1' : morsy twoarrow_data := i1.
Definition i2' : morsy twoarrow_data := i2.
Definition a0' : morsy twoarrow_data := a0.
Definition a1' : morsy twoarrow_data := a1.

Lemma ob_twoarrow_cat_or : forall x,
ob twoarrow_cat x = (x = (R o1') \/ x = (R o2')).
Proof.
ir. ap iff_eq; ir. 
ufi twoarrow_cat H. 
rwi ob_catyd H. nin H. nin x0. ap or_introl; am. 
ap or_intror; am. 
ap twoarrow_data_property. 
cp twoarrow_data_property. 
uf twoarrow_cat. 
nin H. rw H. 
app ob_catyd_R. 
rw H. 
app ob_catyd_R. 
Qed.

Lemma ob_twoarrow_cat : forall (x:obsy twoarrow_data),
ob twoarrow_cat (R x).
Proof.
ir. uf twoarrow_cat. app ob_catyd_R. ap twoarrow_data_property. 
Qed. 

Ltac or_first :=
match goal with 
|- (_ \/ _) => ap or_introl 
| _ => idtac
end.

Ltac or_show i :=
match i with 
O => or_first
| (S ?id1) => ap or_intror; or_show id1
end. 



Lemma mor_twoarrow_cat_or : forall u,
mor twoarrow_cat u = 
(u = (catyd_arrow  i1') \/
u = (catyd_arrow  i2') \/
u = (catyd_arrow  a0') \/
u = (catyd_arrow  a1')).
Proof.
ir. ap iff_eq; ir. 
ufi twoarrow_cat H; rwi mor_catyd H; nin H. 
nin x.
or_show 0; am.
or_show 1; am.
or_show 2; am.
or_show 3; am.

ap twoarrow_data_property. 
cp twoarrow_data_property. 
nin H. rw H. 
uf twoarrow_cat. app mor_catyd_catyd_arrow. 
nin H. rw H. 
uf twoarrow_cat. app mor_catyd_catyd_arrow. 
nin H. rw H. 
uf twoarrow_cat. app mor_catyd_catyd_arrow. 
rw H. 
uf twoarrow_cat. app mor_catyd_catyd_arrow. 
Qed.

Lemma mor_twoarrow_cat : forall (y:morsy twoarrow_data),
mor twoarrow_cat (catyd_arrow y).
Proof.
ir. 
uf twoarrow_cat. app mor_catyd_catyd_arrow. 
ap twoarrow_data_property. 
Qed. 

Lemma mor_twoarrow_cat_ex : forall u,
mor twoarrow_cat u = 
(exists y:morsy twoarrow_data, u = catyd_arrow y).
Proof.
ir. ap iff_eq; ir. ufi twoarrow_cat H; rwi mor_catyd H.
am. ap twoarrow_data_property. 
nin H. rw H. ap mor_twoarrow_cat. 
Qed. 

Lemma id_twoarrow_cat_R : forall (x:obsy twoarrow_data),
id twoarrow_cat (R x) =
match x with 
o1 => (catyd_arrow i1') |
o2 => (catyd_arrow i2')  end.
Proof. 
ir. nin x; uf twoarrow_cat;  
rww id_catyd_R; ap twoarrow_data_property. 
Qed.

Definition twoarrow_hypothesis a u v :=
mor a u & mor a v & source u = source v &
target u = target v.



Definition twoarrow_fun_data a u v :=
Build_fun_type_data (d:= twoarrow_data) a (fun x =>
match x with o1 => (source u) | o2 => (target u) end)
(fun y =>
match y with i1 => id a (source u) |
i2 => id a (target u) |
a0 => u | a1 => v end).

Lemma ft_twoarrow_fun_data : forall a u v,
ft (twoarrow_fun_data a u v) = a.
Proof.
ir. uf twoarrow_fun_data. rww ft_Build_fun_type_data.
Qed.

Lemma twoarrow_fun_data_property : forall a u v,
twoarrow_hypothesis a u v -> 
funtyd_property (twoarrow_fun_data a u v).
Proof.
ir. uh H; ee. 
uf twoarrow_fun_data. 
start_funtyd_proof; funtyd_dispatch. 
Qed. 

Definition twoarrow_functor a u v :=
funtyd (twoarrow_fun_data a u v).

Lemma twoarrow_functor_axioms : 
forall a u v, 
twoarrow_hypothesis a u v -> 
Functor.axioms (twoarrow_functor a u v).
Proof.
ir. uh H; ee. uf twoarrow_functor. 
ap funtyd_axioms. app twoarrow_fun_data_property. 
uhg; ee; am. 
Qed. 

Lemma source_twoarrow_functor : forall a u v,
source (twoarrow_functor a u v) = twoarrow_cat.
Proof.
ir. uf twoarrow_functor. 
rww source_funtyd. 
Qed.

Lemma target_twoarrow_functor : forall a u v,
target (twoarrow_functor a u v) = a.
Proof.
ir. uf twoarrow_functor. 
rww target_funtyd. 
Qed.


Lemma fob_twoarrow_functor_R : forall a u v (x:obsy twoarrow_data),
twoarrow_hypothesis a u v -> 
fob (twoarrow_functor a u v) (R x) = match x with
o1 => (source u) | o2 => (target u) end.
Proof.
ir. cp (twoarrow_fun_data_property H).
uf twoarrow_functor. nin x; rww fob_funtyd_R. 
Qed. 

Lemma fmor_twoarrow_functor_catyd_arrow :forall a u v 
(y:morsy twoarrow_data), twoarrow_hypothesis a u v -> 
fmor (twoarrow_functor a u v) (catyd_arrow y) = match y with
i1 =>  id a (source u) |
i2 =>  id a (target u) |
a0 =>  u |
a1 =>  v end.
Proof.
ir. cp (twoarrow_fun_data_property H).
uf twoarrow_functor. nin y; rww fmor_funtyd_catyd_arrow.
Qed. 


(**** every functor from twoarrow_cat is of the 
form twoarrow_functor _ _ _ **********************)

Lemma functor_twoarrow_hypothesis : forall f,
Functor.axioms f -> source f = twoarrow_cat ->
twoarrow_hypothesis (target f) (fmor f (catyd_arrow a0'))
(fmor f (catyd_arrow a1')).
Proof.
ir. uhg; ee. 
app mor_fmor. rw H0. 
ap mor_twoarrow_cat. 
app mor_fmor. rw H0. 
ap mor_twoarrow_cat. 
rww source_fmor. 
rw source_catyd_arrow. 

rww source_fmor. rww source_catyd_arrow. 
rw H0. ap mor_twoarrow_cat. 
rw H0. ap mor_twoarrow_cat. 
rww target_fmor. 
rw target_catyd_arrow. 
rww target_fmor. 
rww target_catyd_arrow. rw H0. 
ap mor_twoarrow_cat. 
rw H0. 
ap mor_twoarrow_cat. 
Qed.


Lemma functor_twoarrow_eq : forall f,
Functor.axioms f -> source f = twoarrow_cat ->
f = twoarrow_functor (target f) (fmor f (catyd_arrow a0'))
(fmor f (catyd_arrow a1')).
Proof.
ir. 
ap Functor.axioms_extensionality. am. 
ap twoarrow_functor_axioms. 
app functor_twoarrow_hypothesis. 

rww source_twoarrow_functor. rww target_twoarrow_functor.

ir. rwi H0 H1. 
set (p:= (fmor f (catyd_arrow (d:=twoarrow_data) a0'))).
set (q:= (fmor f (catyd_arrow (d:=twoarrow_data) a1'))).


rwi mor_twoarrow_cat_ex H1. nin H1. rw H1. 
rw fmor_twoarrow_functor_catyd_arrow. 
assert (catyd_arrow (d:= twoarrow_data) i1 = id twoarrow_cat (R o1')).
rw id_twoarrow_cat_R.
reflexivity. 
assert (catyd_arrow (d:= twoarrow_data) i2 = id twoarrow_cat (R o2')).
rw id_twoarrow_cat_R.
reflexivity. 

nin x. rw H2. wr H0. rw fmor_id. 
uf p. 
rw source_fmor. 
rw source_catyd_arrow. tv. am. 
rw H0. 
ap mor_twoarrow_cat.
am. tv. 
rw H0; ap ob_twoarrow_cat. 
rw H3. wr H0. rw fmor_id. 
uf p. rw target_fmor. 
rw target_catyd_arrow. reflexivity. am.
rw H0; ap mor_twoarrow_cat. am. tv. 
rw H0; ap ob_twoarrow_cat. 
reflexivity. reflexivity. uf p. 
uf q. app functor_twoarrow_hypothesis. 
Qed. 

Lemma functor_twoarrow_eq2 : forall a u v f,
Functor.axioms f -> source f = twoarrow_cat ->
a = target f -> u = (fmor f (catyd_arrow a0')) ->
v = (fmor f (catyd_arrow a1')) -> 
f = twoarrow_functor a u v.
Proof.
ir. rw H1; rw H2; rw H3; app functor_twoarrow_eq. 
Qed.

Lemma constant_functor_twoarrow_functor :
forall a b x, a = twoarrow_cat -> ob b x ->
constant_functor a b x = 
twoarrow_functor b (id b x) (id b x).
Proof.
ir. ap functor_twoarrow_eq2. 
ap constant_functor_axioms. rw H; ap twoarrow_cat_axioms.
uh H0; ee; am. am. 
rww source_constant_functor. 
rww target_constant_functor. 
rw fmor_constant_functor. tv. rw H. 
ap mor_twoarrow_cat. 
rw fmor_constant_functor. tv. rw H. 
ap mor_twoarrow_cat. 
Qed.

Lemma fidentity_twoarrow_cat : 
fidentity twoarrow_cat = 
twoarrow_functor twoarrow_cat
(catyd_arrow a0') (catyd_arrow a1').
Proof.
cp twoarrow_cat_axioms. 
app functor_twoarrow_eq2. 
rww fidentity_axioms. rww source_fidentity. 
rww target_fidentity. 
rww fmor_fidentity. ap mor_twoarrow_cat. 
rww fmor_fidentity; ap mor_twoarrow_cat. 
Qed.

Lemma fcompose_twoarrow_functor : forall a u v f,
twoarrow_hypothesis a u v -> 
Functor.axioms f -> source f = a ->
fcompose f (twoarrow_functor a u v) =
twoarrow_functor (target f) (fmor f u) (fmor f v).
Proof.
ir. 
ap functor_twoarrow_eq2. 
app fcompose_axioms. 
app twoarrow_functor_axioms. rww target_twoarrow_functor.
rww source_fcompose. rww source_twoarrow_functor. 
rww target_fcompose. 
rww fmor_fcompose. 
rww fmor_twoarrow_functor_catyd_arrow. 
app twoarrow_functor_axioms. 
rww target_twoarrow_functor. 
rww source_twoarrow_functor. 
ap mor_twoarrow_cat. 
rww fmor_fcompose. rww fmor_twoarrow_functor_catyd_arrow.
app twoarrow_functor_axioms. 
rww target_twoarrow_functor. 
rww source_twoarrow_functor. 
ap mor_twoarrow_cat. 
Qed.





Definition twoarrow_nt a u1 v1 u2 v2 r s :=
nttyd (twoarrow_fun_data a u1 v1) 
(twoarrow_fun_data a u2 v2) 
(fun x : (obsy twoarrow_data) => 
match x with 
o1 => r | o2 => s end).



Definition twoarrow_nt_hypothesis  a u1 v1 u2 v2 r s:=
Category.axioms a &
mor a u1 & mor a v1 &  mor a u2 & mor a v2 &
mor a r & mor a s &
source r = source u1 & target r = source u2 &
source s = target u1 & target s = target u2 &
source u1 = source v1 & target u1 = target v1 &
source u2 = source v2 & target u2 = target v2 &
comp a s u1 = comp a u2 r &
comp a s v1 = comp a v2 r.

Lemma twoarrow_nttyd_property : forall a u1 v1 u2 v2 r s,
twoarrow_nt_hypothesis a u1 v1 u2 v2 r s -> 
nttyd_property (twoarrow_fun_data a u1 v1) 
(twoarrow_fun_data a u2 v2) 
(fun x : (obsy twoarrow_data) => 
match x with o1 => r | o2 => s end).
Proof.
ir. uh H; ee. 
assert (lem1: twoarrow_hypothesis a u1 v1).
uhg; ee; am. 
assert (lem2: twoarrow_hypothesis a u2 v2).
uhg; ee; am. 

uhg; ee. ap twoarrow_data_property. 
app twoarrow_fun_data_property. 
app twoarrow_fun_data_property. 
rw ft_twoarrow_fun_data;
rww ft_twoarrow_fun_data. 

ir. rw ft_twoarrow_fun_data.
nin x. am. am. 
ir. nin x. 
rww H6. rww H8. 
ir. nin x. 
rww H7. rww H9. 
ir. 
rw ft_twoarrow_fun_data. 
nin u. 
change (comp a r (id a (source u1)) =
comp a (id a (source u2)) r).
rww right_id. rww left_id. 
rww ob_source. rww ob_source. 

change (comp a s (id a (target u1)) =
comp a (id a (target u2)) s).
rww left_id. rww right_id. 
rww ob_target. rww ob_target. 
am. am. 
Qed.

Lemma twoarrow_nt_axioms : forall a u1 v1 u2 v2 r s,
twoarrow_nt_hypothesis a u1 v1 u2 v2 r s -> 
Nat_Trans.axioms (twoarrow_nt a u1 v1 u2 v2 r s).
Proof.
ir. uf twoarrow_nt. ap nttyd_axioms. 
ap twoarrow_nttyd_property. am. 
Qed.


Lemma source_twoarrow_nt : forall a u1 v1 u2 v2 r s,
source (twoarrow_nt a u1 v1 u2 v2 r s) =
twoarrow_functor a u1 v1.
Proof.
ir. 
uf twoarrow_nt. rww source_nttyd. 
Qed.

Lemma target_twoarrow_nt : forall a u1 v1 u2 v2 r s,
target (twoarrow_nt a u1 v1 u2 v2 r s) =
twoarrow_functor a u2 v2.
Proof.
ir. 
uf twoarrow_nt. rww target_nttyd. 
Qed.

Lemma osource_twoarrow_nt : forall a u1 v1 u2 v2 r s,
osource (twoarrow_nt a u1 v1 u2 v2 r s) = twoarrow_cat.
Proof.
ir. uf osource. rw source_twoarrow_nt. 
rww source_twoarrow_functor. 
Qed.

Lemma otarget_twoarrow_nt : forall a u1 v1 u2 v2 r s,
otarget (twoarrow_nt a u1 v1 u2 v2 r s) = a.
Proof.
ir. uf otarget. rw target_twoarrow_nt. 
rww target_twoarrow_functor. 
Qed.

Lemma ntrans_twoarrow_nt_R : forall a u1 v1 u2 v2 r s
(x:obsy twoarrow_data),
ntrans (twoarrow_nt a u1 v1 u2 v2 r s) (R x) =
match x with
o1 => r | o2 => s end.
Proof.
ir. uf twoarrow_nt. 
rw ntrans_nttyd. rw X_rewrite. tv. 
rw ob_catyd. sh x; tv. ap twoarrow_data_property.  
Qed.

Lemma twoarrow_nt_hypothesis_ntrans : forall u,
Nat_Trans.axioms u -> osource u = twoarrow_cat ->
twoarrow_nt_hypothesis (otarget u)
(fmor (source u) (catyd_arrow a0'))
(fmor (source u) (catyd_arrow a1'))
(fmor (target u) (catyd_arrow a0'))
(fmor (target u) (catyd_arrow a1'))
(ntrans u (R o1')) (ntrans u (R o2')).
Proof.
ir. 
assert (Category.axioms (otarget u)).
rww category_axioms_otarget.
assert (Functor.axioms (source u)).
rww functor_axioms_source. 
assert (Functor.axioms (target u)).
rww functor_axioms_target. 



uhg; ee. am. 

wrr target_source. app mor_fmor. 
rw source_source. rw H0. 
ap mor_twoarrow_cat. 

wr target_source. app mor_fmor. 
rw source_source. rw H0. 
ap mor_twoarrow_cat. am. 


uf otarget. app mor_fmor. 
rw source_target. rw H0. 
ap mor_twoarrow_cat. am. 


uf otarget. app mor_fmor. 
rw source_target. rw H0. 
ap mor_twoarrow_cat. am. 


app mor_ntrans. rw H0. 
ap ob_twoarrow_cat.  
 
app mor_ntrans. rw H0. 
ap ob_twoarrow_cat.  

rww source_fmor. 
rww source_catyd_arrow. rww source_ntrans. rw H0. 
ap ob_twoarrow_cat.  

rw source_source; rw H0; ap mor_twoarrow_cat. 

rww target_ntrans. rww source_fmor. 
rww source_catyd_arrow. 
rww source_target. rw H0. ap mor_twoarrow_cat.  rw H0. 
ap ob_twoarrow_cat.  

rww source_ntrans. rww target_fmor. 
rww target_catyd_arrow. 
rw source_source; rw H0; ap mor_twoarrow_cat. rw H0. 
ap ob_twoarrow_cat.  

rww target_ntrans. rww target_fmor. 
rww target_catyd_arrow. 
rww source_target. rw H0. ap mor_twoarrow_cat. rw H0. 
ap ob_twoarrow_cat.  

rw source_fmor. rw source_catyd_arrow. 
rw source_fmor. rw source_catyd_arrow. 
reflexivity. am. 
rw source_source; rw H0; ap mor_twoarrow_cat.  am. 
rw source_source; rw H0; ap mor_twoarrow_cat. 

rw target_fmor. rw target_catyd_arrow. 
rw target_fmor. rw target_catyd_arrow. 
reflexivity. am. 
rw source_source; rw H0; ap mor_twoarrow_cat. am. 
rw source_source; rw H0; ap mor_twoarrow_cat. 

rw source_fmor. rw source_catyd_arrow. 
rw source_fmor. rw source_catyd_arrow. 
reflexivity. am. 
rw source_target.  rw H0; ap mor_twoarrow_cat. am. am. 
rww source_target; rw H0; ap mor_twoarrow_cat. 

rw target_fmor. rw target_catyd_arrow. 
rw target_fmor. rw target_catyd_arrow. 
reflexivity. am. 
rww source_target; rw H0; ap mor_twoarrow_cat. am. 
rww source_target; rw H0; ap mor_twoarrow_cat. 

assert (R o2' = target (catyd_arrow a0')). 
rww target_catyd_arrow. rw H4. 

rw carre. rw source_catyd_arrow. 
reflexivity. am. rw H0. ap mor_twoarrow_cat. 

assert (R o2' = target (catyd_arrow a1')).
rww target_catyd_arrow. rw H4. 

rw carre. rw source_catyd_arrow. 
reflexivity. am. rw H0. ap mor_twoarrow_cat. 
Qed.

Lemma twoarrow_nt_ntrans : forall u,
Nat_Trans.axioms u -> osource u = twoarrow_cat ->
twoarrow_nt (otarget u)
(fmor (source u) (catyd_arrow a0'))
(fmor (source u) (catyd_arrow a1'))
(fmor (target u) (catyd_arrow a0'))
(fmor (target u) (catyd_arrow a1'))
(ntrans u (R o1')) (ntrans u (R o2')) = u.
Proof.
ir. 

ap Nat_Trans.axioms_extensionality. 
ap twoarrow_nt_axioms. 
app twoarrow_nt_hypothesis_ntrans. am. 
rw source_twoarrow_nt. 
wr target_source. sy; ap functor_twoarrow_eq. 
uh H; ee. am. am. am. 

rw target_twoarrow_nt. uf otarget. 
sy; ap functor_twoarrow_eq. uh H; ee; am. 
rww source_target. 
ir. 
ufi osource H1. rwi source_twoarrow_nt H1. 
rwi source_twoarrow_functor H1. 
rwi ob_twoarrow_cat_or H1. nin H1. 
rw H1. 
rw ntrans_twoarrow_nt_R. reflexivity. 
rw H1. rw ntrans_twoarrow_nt_R. reflexivity. 
Qed.

Lemma eq_twoarrow_nt : forall u a u1 v1 u2 v2 r s,
Nat_Trans.axioms u -> osource u = twoarrow_cat ->
a = (otarget u) -> 
u1 = (fmor (source u) (catyd_arrow a0')) -> 
v1 =(fmor (source u) (catyd_arrow a1')) -> 
u2 =(fmor (target u) (catyd_arrow a0')) -> 
v2 =(fmor (target u) (catyd_arrow a1')) -> 
r =(ntrans u (R o1')) -> 
s =(ntrans u (R o2')) ->
u = twoarrow_nt a u1 v1 u2 v2 r s.
Proof.
ir.  rw H1; rw H2; rw H3; rw H4;
rw H5; rw H6; rw H7; rww twoarrow_nt_ntrans. 
Qed.

Lemma constant_nt_twoarrow_nt : forall a b u,
a = twoarrow_cat -> mor b u ->
constant_nt a b u = twoarrow_nt b 
(id b (source u)) (id b (source u))
(id b (target u)) (id b (target u))
u u.
Proof.
ir. rw H. ap eq_twoarrow_nt. 
app constant_nt_axioms. ap twoarrow_cat_axioms. 
uh H0; ee; am. 
rww osource_constant_nt. rww otarget_constant_nt. 
rw source_constant_nt. rw fmor_constant_functor. 
tv. ap mor_twoarrow_cat. 
rw source_constant_nt. rw fmor_constant_functor. 
tv. ap mor_twoarrow_cat. 
rw target_constant_nt. rw fmor_constant_functor. 
tv. ap mor_twoarrow_cat. 
rw target_constant_nt. rw fmor_constant_functor. 
tv. ap mor_twoarrow_cat. 
rww ntrans_constant_nt. ap ob_twoarrow_cat. 
rww ntrans_constant_nt. ap ob_twoarrow_cat. 
Qed. 

Lemma vident_twoarrow_functor : forall a u v,
twoarrow_hypothesis a u v -> 
vident (twoarrow_functor a u v) =
twoarrow_nt a u v u v (id a (source u)) (id a (target u)).
Proof.
ir. 
cp twoarrow_cat_axioms. 
cp (twoarrow_functor_axioms H). 
cp H; uh H; ee. 
assert (ob a (source u)). 
rww ob_source. 
assert (ob a (target u)). 
rww ob_target. 

assert (twoarrow_nt_hypothesis 
a u v u v (id a (source u)) (id a (target u))). 
uhg; ee. uh H; ee; am. 
am. am. am. am. 
app mor_id. app mor_id. 
rww source_id. rww target_id. rww source_id. 
rww target_id. am. am. am. am. 
rww left_id. rww right_id. rww left_id. rww right_id. 
sy; am. sy; am. 

ap Nat_Trans.axioms_extensionality. 
rww vident_axioms. 
ap twoarrow_nt_axioms. 
am. rww source_vident. 
rww source_twoarrow_nt. rww target_vident.
rww target_twoarrow_nt. 

ir. rwi osource_vident H9. rwi source_twoarrow_functor H9.
rw ntrans_vident. 
rww target_twoarrow_functor. 

rwi ob_twoarrow_cat_or H9. nin H9. 
rw H9. rw fob_twoarrow_functor_R. 
rw ntrans_twoarrow_nt_R. 
reflexivity. am. 
rw H9. rw fob_twoarrow_functor_R. 
rw ntrans_twoarrow_nt_R. 
reflexivity. am. 
rw source_twoarrow_functor. am. 
Qed.

Lemma vcompose_twoarrow_nt : forall a u1 v1 u2 v2 r s
u1' v1' u2' v2' r' s',
twoarrow_nt_hypothesis a u1 v1 u2 v2 r s ->
twoarrow_nt_hypothesis a u1' v1' u2' v2' r' s' ->
u1 = u2' -> v1 = v2' ->
vcompose (twoarrow_nt a u1 v1 u2 v2 r s)
(twoarrow_nt a u1' v1' u2' v2' r' s') =
twoarrow_nt a u1' v1' u2 v2 (comp a r r') (comp a s s').
Proof.
ir. wr H1. wr H2. wri H1 H0; wri H2 H0.
cp twoarrow_cat_axioms. 
cp H; cp H0.
uh H4; uh H5. ee. 
assert (twoarrow_hypothesis a u1 v1).
uhg; ee; am. 
assert (twoarrow_hypothesis a u2 v2).
uhg; ee; am. 
assert (twoarrow_hypothesis a u1' v1').
uhg; ee; am. 


cp (twoarrow_functor_axioms H38). 
cp (twoarrow_functor_axioms H39). 
cp (twoarrow_functor_axioms H40). 

assert (ob a (source u1)). rww ob_source. 
assert (ob a (target u1)). rww ob_target. 
assert (ob a (source u2)). rww ob_source. 
assert (ob a (target u2)). rww ob_target. 
assert (ob a (source u1')). rww ob_source. 
assert (ob a (target u1')). rww ob_target. 
cp (twoarrow_nt_axioms H).
cp (twoarrow_nt_axioms H0).

assert (source r = target r').
rww H13. 
assert (source s = target s'). 
rww H15. 

assert (twoarrow_nt_hypothesis
a u1' v1' u2 v2 (comp a r r') (comp a s s')). 
uhg; ee. uh H6; ee; am. am. am. 
am. am. rww mor_comp. 
rww mor_comp. rww source_comp. 
rww target_comp. rww source_comp. rww target_comp.
am. am. am. am. rww assoc. rw H20. wrr assoc.
rw H36. rww assoc. sy; am. sy; am. 
rww assoc. rw H21. wrr assoc. rw H37. 
rww assoc. wr H34. sy; am. wr H33. am. 
wr H32. sy; am. wr H17; am. 


ap Nat_Trans.axioms_extensionality. 
rw vcompose_axioms. tv. am. am. 
rw source_twoarrow_nt. 
rw target_twoarrow_nt. reflexivity. 
app twoarrow_nt_axioms. 
rw source_vcompose. 
rw source_twoarrow_nt. 
rw source_twoarrow_nt. reflexivity. 
rw target_vcompose. 
rw target_twoarrow_nt. 
rw target_twoarrow_nt. reflexivity. 

ir. rwi osource_vcompose H55. 
rwi osource_twoarrow_nt H55. 

rw ntrans_vcompose. rw otarget_twoarrow_nt. 
rwi ob_twoarrow_cat_or H55. 
nin H55.
rw H55. 
rw ntrans_twoarrow_nt_R. 
rw ntrans_twoarrow_nt_R. 
rw ntrans_twoarrow_nt_R. 
reflexivity. 
rw H55. 
rw ntrans_twoarrow_nt_R. 
rw ntrans_twoarrow_nt_R. 
rw ntrans_twoarrow_nt_R. 
reflexivity. 
rw osource_twoarrow_nt. am. 
Qed.


Lemma twoarrow_nt_hypothesis_for_htrans_left : 
forall u1 v1 u2 v2 r s f,
twoarrow_nt_hypothesis (source f) u1 v1 u2 v2 r s ->
Functor.axioms f  ->
twoarrow_nt_hypothesis (target f) (fmor f u1) (fmor f v1) (fmor f u2) 
(fmor f v2) (fmor f r) (fmor f s).
Proof.
ir. 
cp twoarrow_cat_axioms. 
cp H.
uh H2. ee. 
assert (twoarrow_hypothesis (source f) u1 v1).
uhg; ee; am. 
assert (twoarrow_hypothesis (source f) u2 v2).
uhg; ee; am. 
cp (twoarrow_functor_axioms H19). 
cp (twoarrow_functor_axioms H20). 

assert (ob (source f) (source u1)). rww ob_source.
assert (ob (source f) (source u2)). rww ob_source.
assert (ob (source f) (target u1)). rww ob_target.
assert (ob (source f) (target u2)). rww ob_target.
cp (twoarrow_nt_axioms H). 

uhg; ee; try (app mor_fmor);
try (rww source_fmor); try (rww source_fmor);
try (rww target_fmor); try (rww target_fmor);
try (app uneq).
uh H0; ee; am. 
rww comp_fmor. 
rww comp_fmor. app uneq. sy; am. 
 rww comp_fmor. 
rww comp_fmor. app uneq. rww H10. sy; am. 
wrr H14. 
Qed.

Lemma htrans_left_twoarrow_nt : forall a u1 v1 u2 v2 r s f,
twoarrow_nt_hypothesis a u1 v1 u2 v2 r s ->
Functor.axioms f -> source f = a ->
htrans_left f (twoarrow_nt a u1 v1 u2 v2 r s) =
twoarrow_nt (target f) (fmor f u1) (fmor f v1) (fmor f u2) 
(fmor f v2) (fmor f r) (fmor f s).
Proof.
ir. 
wr H1. wri H1 H. 
cp twoarrow_cat_axioms. 
cp H.
uh H3. ee. 
assert (twoarrow_hypothesis (source f) u1 v1).
uhg; ee; am. 
assert (twoarrow_hypothesis (source f) u2 v2).
uhg; ee; am. 
cp (twoarrow_functor_axioms H20). 
cp (twoarrow_functor_axioms H21). 

assert (ob (source f) (source u1)). rww ob_source.
assert (ob (source f) (source u2)). rww ob_source.
assert (ob (source f) (target u1)). rww ob_target.
assert (ob (source f) (target u2)). rww ob_target.
cp (twoarrow_nt_axioms H). 

ap Nat_Trans.axioms_extensionality. 
app htrans_left_axioms. 
rww otarget_twoarrow_nt. 
app twoarrow_nt_axioms. 
app twoarrow_nt_hypothesis_for_htrans_left. 
rww source_htrans_left. rww source_twoarrow_nt. 
rw source_twoarrow_nt. 
rw fcompose_twoarrow_functor. tv. 
am. am. tv. 

rw target_htrans_left. rw target_twoarrow_nt. 
rw fcompose_twoarrow_functor. rw target_twoarrow_nt. 
tv. am. am. tv. 

ir. rwi osource_htrans_left H29. rwi osource_twoarrow_nt H29. 

rw ntrans_htrans_left. 
rwi ob_twoarrow_cat_or H29. nin H29. rw H29. 
rw ntrans_twoarrow_nt_R. rw ntrans_twoarrow_nt_R. 
reflexivity. rw H29. 
rw ntrans_twoarrow_nt_R. rw ntrans_twoarrow_nt_R. 
reflexivity. 
rww osource_twoarrow_nt. 
Qed.

Lemma twoarrow_nt_hypothesis_for_htrans_right : 
forall y u v,
Nat_Trans.axioms y -> twoarrow_hypothesis (osource y) u v ->
twoarrow_nt_hypothesis 
(otarget y) (fmor (source y) u) (fmor (source y) v)
(fmor (target y) u) (fmor (target y) v) 
(ntrans y (source u)) (ntrans y (target u)).
Proof.
ir. 
cp twoarrow_cat_axioms. 
cp H0. uh H2; ee. 
assert (ob (osource y) (source u)). rww ob_source. 
assert (ob (osource y) (target u)). rww ob_target. 
assert (Functor.axioms (source y)).
rww functor_axioms_source. 
assert (Functor.axioms (target y)). 
rww functor_axioms_target. 
assert (Category.axioms (osource y)). 
rww category_axioms_osource. 
assert (Category.axioms (otarget y)). 
rww category_axioms_otarget. 

uhg; ee. am. 
wrr target_source; app mor_fmor. 
wrr target_source; app mor_fmor. 
wrr target_target; app mor_fmor; 
rww source_target. 
wrr target_target; app mor_fmor;  rww source_target. 
app mor_ntrans. app mor_ntrans. 
rww source_ntrans. rww source_fmor. 
 rww target_ntrans. rww source_fmor. 
rww source_target. 
rww source_ntrans. rww target_fmor. 
rww target_ntrans. rww target_fmor. 
rww source_target. 
rww source_fmor. rww source_fmor. rww H4. 
rww target_fmor. rww target_fmor. rww H5. 
rww source_fmor. rww source_fmor. rww H4. 
rww source_target. rww source_target. 
rww target_fmor. rww target_fmor. rww H5. 
rww source_target. rww source_target. 
rww carre. rw H4; rw H5. 
rww carre. 
Qed.

Lemma htrans_right_twoarrow_functor : forall y a u v,
Nat_Trans.axioms y -> twoarrow_hypothesis a u v ->
osource y = a ->
htrans_right y (twoarrow_functor a u v) =
twoarrow_nt (otarget y) (fmor (source y) u) (fmor (source y) v)
(fmor (target y) u) (fmor (target y) v) 
(ntrans y (source u)) (ntrans y (target u)).
Proof.
ir. 
wr H1. wri H1 H0. 
cp twoarrow_cat_axioms. 
cp H0. uh H3; ee. 
assert (ob (osource y) (source u)). rww ob_source. 
assert (ob (osource y) (target u)). rww ob_target. 
assert (Functor.axioms (source y)).
rww functor_axioms_source. 
assert (Functor.axioms (target y)). 
rww functor_axioms_target. 
assert (Category.axioms (osource y)). 
rww category_axioms_osource. 
assert (Category.axioms (otarget y)). 
rww category_axioms_otarget. 

ap Nat_Trans.axioms_extensionality. 
ap htrans_right_axioms. 
app twoarrow_functor_axioms. am. 
rww target_twoarrow_functor. 
ap twoarrow_nt_axioms. 
app twoarrow_nt_hypothesis_for_htrans_right. 
rw source_htrans_right. rw fcompose_twoarrow_functor.
rw source_twoarrow_nt. rww target_source. 
am. am. tv. 

rw target_htrans_right. rw fcompose_twoarrow_functor.
rw target_twoarrow_nt. reflexivity. am. am. 
rww source_target. 

ir. rwi osource_htrans_right H13. cp H13. 
rwi source_twoarrow_functor H14. 
rww ntrans_htrans_right. 

rwi ob_twoarrow_cat_or H14. nin H14; rw H14. 
rw fob_twoarrow_functor_R. 
rw ntrans_twoarrow_nt_R. reflexivity. am. 
rw fob_twoarrow_functor_R. 
rw ntrans_twoarrow_nt_R. reflexivity. am. 
Qed.

Lemma hcompose_twoarrow_nt1 : forall u a u1 v1 u2 v2 r s,
twoarrow_nt_hypothesis a u1 v1 u2 v2 r s ->
Nat_Trans.axioms u -> osource u = a ->
hcompose u (twoarrow_nt a u1 v1 u2 v2 r s) =
twoarrow_nt (otarget u) (fmor (source u) u1) (fmor (source u) v1)
(fmor (target u) u2) (fmor (target u) v2)
(comp (otarget u) (ntrans u (source u2)) (fmor (source u) r))
(comp (otarget u) (ntrans u (target u2)) (fmor (source u) s)).
Proof.
ir. uf hcompose. 
rw target_twoarrow_nt. 
util (htrans_right_twoarrow_functor (y:=u) (a:=a) (u:=u2) (v:=v2)).
am. uh H; uhg; xd. am. 
rw H2. 

util (htrans_left_twoarrow_nt (a:=a) (u1:=u1) (v1:=v1) (u2:=u2) (v2:=v2)
(r:=r) (s:=s) (f:=source u)). am. 
rww functor_axioms_source. am. 
rw H3. 

rw target_source. rw vcompose_twoarrow_nt.  
reflexivity.  

ap twoarrow_nt_hypothesis_for_htrans_right. 
am. rw H1. uh H; uhg; xd. 
wr target_source. 
ap twoarrow_nt_hypothesis_for_htrans_left. 
rw source_source; rw H1. am. 
rww functor_axioms_source. am. 
tv. tv. am. 
Qed.

Lemma hcompose_twoarrow_nt2 : forall u a u1 v1 u2 v2 r s,
twoarrow_nt_hypothesis a u1 v1 u2 v2 r s ->
Nat_Trans.axioms u -> osource u = a ->
hcompose u (twoarrow_nt a u1 v1 u2 v2 r s) =
twoarrow_nt (otarget u) (fmor (source u) u1) (fmor (source u) v1)
(fmor (target u) u2) (fmor (target u) v2)
(comp (otarget u) (fmor (target u) r) (ntrans u (source u1)) )
(comp (otarget u) (fmor (target u) s) (ntrans u (target u1)) ).
Proof.
ir. 
rw Nat_Trans.hcompose_other. 
uf hcompose1. 
rw source_twoarrow_nt. 
util (htrans_right_twoarrow_functor (y:=u) (a:=a) (u:=u1) (v:=v1)).
am. uh H; uhg; xd. am. 
rw H2. 

util (htrans_left_twoarrow_nt (a:=a) (u1:=u1) (v1:=v1) (u2:=u2) (v2:=v2)
(r:=r) (s:=s) (f:=target u)). am. 
rww functor_axioms_target. rww source_target.  
rw H3. 

rw target_target. rw vcompose_twoarrow_nt.  
reflexivity.  


wr target_target. 
ap twoarrow_nt_hypothesis_for_htrans_left. 
rw source_target. rw H1. am. am. 
rww functor_axioms_target. 

ap twoarrow_nt_hypothesis_for_htrans_right. 
am. rw H1. uh H; uhg; xd. 
tv. tv. 

uhg. ee. am. app twoarrow_nt_axioms. 
rww otarget_twoarrow_nt. 
Qed.


Lemma ta_obs_tack : tack (R o1) (tack (R o2) emptyset)
= ta_obs. 
Proof.
ap extensionality; uhg; ir. 
rwi tack_inc H. 
nin H. rwi tack_inc H. nin H. 
nin H. elim x0. rw H. ap R_inc. rw H. ap R_inc. 
nin H. wr H. 
nin x0. 
rw tack_inc. ap or_intror. tv. 
rw tack_inc. ap or_introl.  
rw tack_inc. ap or_intror; tv. 
Qed.

Lemma ta_maps_tack : 
tack (R i1) (tack (R i2) (tack (R a0) (tack (R a1) emptyset)))
= ta_maps. 
Proof.
ap extensionality; uhg; ir. 
rwi tack_inc H. 
nin H. rwi tack_inc H.
nin H. rwi tack_inc H. 
nin H. rwi tack_inc H. 
nin H. nin H. nin x0. 
rw H. ap R_inc. 
rw H. ap R_inc. 
rw H. ap R_inc. 
rw H. ap R_inc. 

rw tack_inc. 
rw tack_inc. rw tack_inc. 
rw tack_inc. 
nin H. wr H. 
nin x0. 
ap or_intror. tv. 
ap or_introl; ap or_intror; tv. 
ap or_introl; ap or_introl; ap or_intror; tv. 
ap or_introl; ap or_introl; ap or_introl. 
ap or_intror; tv. 
Qed. 




Lemma is_finite_ta_obs : is_finite (ta_obs).
Proof.
wr ta_obs_tack. 
ap finite_tack. ap finite_tack. 
ap finite_emptyset. 
Qed.

Lemma is_finite_ta_maps : is_finite (ta_maps).
Proof.
wr ta_maps_tack. 
ap finite_tack. ap finite_tack. 
ap finite_tack. ap finite_tack. 
ap finite_emptyset. 
Qed.

Lemma is_finite_twoarrow_cat : is_finite_cat twoarrow_cat.
Proof.
uf twoarrow_cat. 
ap is_finite_catyd. 
ap twoarrow_data_property. 
exact (is_finite_ta_obs). 
exact (is_finite_ta_maps). 
Qed. 


End Twoarrow_Cat.


Module Vee_Cat.
Export From_Types.
Export Finite_Cat.

(***** we hope to be able to basically recopy the previous
module with a minimum of changes *****)

Inductive vee_obs : Set := 
o1 : vee_obs | o2 : vee_obs | o3 : vee_obs.

Inductive vee_maps : Set := 
i1 : vee_maps | i2 : vee_maps |i3 : vee_maps | 
a12 : vee_maps | a32 : vee_maps.

Definition vee_src u :=
match u with
i1 => o1 | i2 => o2 | i3 => o3 | a12 => o1 | a32 => o3 end.

Definition vee_trg u :=
match u with 
i1 => o1 | i2 => o2 | i3 => o3 | a12 => o2 | a32 => o2 end.

Definition vee_id x := 
match x with
o1 => i1 | o2 => i2 | o3 => i3 end.

Definition vee_comp u v :=
match (u, v) with
(i1, v') => v' |
(i2, v') => v' |
(i3, v') => v' |
(u', i1) => u' |
(u', i2) => u' |
(u', i3) => u' |
_ => i1 end.

Definition vee_data := 
Build_cat_type_data vee_src vee_trg vee_id vee_comp. 


Lemma vee_data_property : catyd_property vee_data.
Proof.
show_catyd_property. 
Qed.

Definition vee_cat := catyd vee_data.

Lemma vee_cat_axioms : Category.axioms vee_cat.
Proof.
uf vee_cat. ap catyd_axioms. ap vee_data_property. 
Qed.



(*** the constructions (R o1) and (R o2) dont work
well with the implicit arguments mechanism because they
don't introduce the type (obsy _); it is better to redefine
the objects ***)

Definition o1' : obsy vee_data := o1.
Definition o2' : obsy vee_data := o2. 
Definition o3' : obsy vee_data := o3. 

Definition i1' : morsy vee_data := i1.
Definition i2' : morsy vee_data := i2.
Definition i3' : morsy vee_data := i3.
Definition a12' : morsy vee_data := a12.
Definition a32' : morsy vee_data := a32.


Lemma ob_vee_cat_ex : forall x,
ob vee_cat x = (exists x':obsy vee_data, x = R x').
Proof.
ir. 
uf vee_cat. rw ob_catyd. tv. ap vee_data_property. 
Qed.

Lemma ob_vee_cat : forall (x:obsy vee_data),
ob vee_cat (R x).
Proof.
ir. uf vee_cat. app ob_catyd_R. ap vee_data_property. 
Qed. 

Lemma mor_vee_cat : forall (y:morsy vee_data),
mor vee_cat (catyd_arrow y).
Proof.
ir. 
uf vee_cat. app mor_catyd_catyd_arrow. 
ap vee_data_property. 
Qed. 

Lemma mor_vee_cat_ex : forall u,
mor vee_cat u = 
(exists y:morsy vee_data, u = catyd_arrow y).
Proof.
ir. ap iff_eq; ir. ufi vee_cat H; rwi mor_catyd H.
am. ap vee_data_property. 
nin H. rw H. ap mor_vee_cat. 
Qed. 

Lemma id_vee_cat_R : forall (x:obsy vee_data),
id vee_cat (R x) =
match x with 
o1 => (catyd_arrow i1') |
o2 => (catyd_arrow i2') |
o3 => (catyd_arrow i3') end.
Proof. 
ir. nin x; uf vee_cat;  
rww id_catyd_R; ap vee_data_property. 
Qed.


Definition vee_hypothesis a u v :=
mor a u & mor a v & 
target u = target v.



Definition vee_fun_data a u v :=
Build_fun_type_data (d:= vee_data) a (fun x =>
match x with o1 => (source u) | o2 => (target u) |
o3 => (source v) end)
(fun y =>
match y with i1 => id a (source u) |
i2 => id a (target u) |
i3 => id a (source v) |
a12 => u | a32 => v end).

Lemma ft_vee_fun_data : forall a u v,
ft (vee_fun_data a u v) = a.
Proof.
ir. uf vee_fun_data. rww ft_Build_fun_type_data.
Qed.

Lemma vee_fun_data_property : forall a u v,
vee_hypothesis a u v -> 
funtyd_property (vee_fun_data a u v).
Proof.
ir. uh H; ee. 
uf vee_fun_data. 
start_funtyd_proof; funtyd_dispatch. 
Qed. 

Definition vee_functor a u v :=
funtyd (vee_fun_data a u v).

Lemma vee_functor_axioms : 
forall a u v, 
vee_hypothesis a u v -> 
Functor.axioms (vee_functor a u v).
Proof.
ir. uh H; ee. uf vee_functor. 
ap funtyd_axioms. app vee_fun_data_property. 
uhg; ee; am. 
Qed. 

Lemma source_vee_functor : forall a u v,
source (vee_functor a u v) = vee_cat.
Proof.
ir. uf vee_functor. 
rww source_funtyd. 
Qed.

Lemma target_vee_functor : forall a u v,
target (vee_functor a u v) = a.
Proof.
ir. uf vee_functor. 
rww target_funtyd. 
Qed.


Lemma fob_vee_functor_R : forall a u v (x:obsy vee_data),
vee_hypothesis a u v -> 
fob (vee_functor a u v) (R x) = match x with
o1 => (source u) | o2 => (target u) |
o3 => (source v) end.
Proof.
ir. cp (vee_fun_data_property H).
uf vee_functor. nin x; rww fob_funtyd_R. 
Qed. 

Lemma fmor_vee_functor_catyd_arrow :forall a u v 
(y:morsy vee_data), vee_hypothesis a u v -> 
fmor (vee_functor a u v) (catyd_arrow y) = match y with
i1 =>  id a (source u) |
i2 =>  id a (target u) |
i3 => id a (source v) |
a12 =>  u |
a32 =>  v end.
Proof.
ir. cp (vee_fun_data_property H).
uf vee_functor. nin y; rww fmor_funtyd_catyd_arrow.
Qed. 


(**** every functor from vee_cat is of the 
form vee_functor _ _ _ **********************)

Lemma functor_vee_hypothesis : forall f,
Functor.axioms f -> source f = vee_cat ->
vee_hypothesis (target f) (fmor f (catyd_arrow a12'))
(fmor f (catyd_arrow a32')).
Proof.
ir. uhg; ee. 
app mor_fmor. rw H0. 
ap mor_vee_cat. 
app mor_fmor. rw H0. 
ap mor_vee_cat. 



rww target_fmor. 
rw target_catyd_arrow. 
rww target_fmor. 
rww target_catyd_arrow. rw H0. 
ap mor_vee_cat. 
rw H0. 
ap mor_vee_cat. 
Qed.


Lemma functor_vee_eq : forall f,
Functor.axioms f -> source f = vee_cat ->
f = vee_functor (target f) (fmor f (catyd_arrow a12'))
(fmor f (catyd_arrow a32')).
Proof.
ir. 
ap Functor.axioms_extensionality. am. 
ap vee_functor_axioms. 
app functor_vee_hypothesis. 

rww source_vee_functor. rww target_vee_functor.

ir. rwi H0 H1. 
set (p:= (fmor f (catyd_arrow (d:=vee_data) a12'))).
set (q:= (fmor f (catyd_arrow (d:=vee_data) a32'))).


rwi mor_vee_cat_ex H1. nin H1. rw H1. 
rw fmor_vee_functor_catyd_arrow. 
assert (catyd_arrow (d:= vee_data) i1 = id vee_cat (R o1')).
rw id_vee_cat_R.
reflexivity. 
assert (catyd_arrow (d:= vee_data) i2 = id vee_cat (R o2')).
rw id_vee_cat_R.
reflexivity. 
assert (lem1: catyd_arrow (d:= vee_data) i3 = id vee_cat (R o3')).
rw id_vee_cat_R.
reflexivity. 

nin x. rw H2. wr H0. rw fmor_id. 
uf p. 
rw source_fmor. 
rw source_catyd_arrow. tv. am. 
rw H0. 
ap mor_vee_cat.
am. tv. 
rw H0; ap ob_vee_cat. 
rw H3. wr H0. rw fmor_id. 
uf p. rw target_fmor. 
rw target_catyd_arrow. reflexivity. am.
rw H0; ap mor_vee_cat. am. tv. 
rw H0; ap ob_vee_cat. 

rw lem1. wr H0. rw fmor_id. 
uf q. rw source_fmor. 
rw source_catyd_arrow. reflexivity. am.
rw H0; ap mor_vee_cat. am. tv. 
rw H0; ap ob_vee_cat. 

reflexivity. reflexivity. uf p. 
uf q. app functor_vee_hypothesis. 
Qed. 

Lemma functor_vee_eq2 : forall a u v f,
Functor.axioms f -> source f = vee_cat ->
a = target f -> u = (fmor f (catyd_arrow a12')) ->
v = (fmor f (catyd_arrow a32')) -> 
f = vee_functor a u v.
Proof.
ir. rw H1; rw H2; rw H3; app functor_vee_eq. 
Qed.

Lemma constant_functor_vee_functor :
forall a b x, a = vee_cat -> ob b x ->
constant_functor a b x = 
vee_functor b (id b x) (id b x).
Proof.
ir. ap functor_vee_eq2. 
ap constant_functor_axioms. rw H; ap vee_cat_axioms.
uh H0; ee; am. am. 
rww source_constant_functor. 
rww target_constant_functor. 
rw fmor_constant_functor. tv. rw H. 
ap mor_vee_cat. 
rw fmor_constant_functor. tv. rw H. 
ap mor_vee_cat. 
Qed.

Lemma fidentity_vee_cat : 
fidentity vee_cat = 
vee_functor vee_cat
(catyd_arrow a12') (catyd_arrow a32').
Proof.
cp vee_cat_axioms. 
app functor_vee_eq2. 
rww fidentity_axioms. rww source_fidentity. 
rww target_fidentity. 
rww fmor_fidentity. ap mor_vee_cat. 
rww fmor_fidentity; ap mor_vee_cat. 
Qed.

Lemma fcompose_vee_functor : forall a u v f,
vee_hypothesis a u v -> 
Functor.axioms f -> source f = a ->
fcompose f (vee_functor a u v) =
vee_functor (target f) (fmor f u) (fmor f v).
Proof.
ir. 
ap functor_vee_eq2. 
app fcompose_axioms. 
app vee_functor_axioms. rww target_vee_functor.
rww source_fcompose. rww source_vee_functor. 
rww target_fcompose. 
rww fmor_fcompose. 
rww fmor_vee_functor_catyd_arrow. 
app vee_functor_axioms. 
rww target_vee_functor. 
rww source_vee_functor. 
ap mor_vee_cat. 
rww fmor_fcompose. rww fmor_vee_functor_catyd_arrow.
app vee_functor_axioms. 
rww target_vee_functor. 
rww source_vee_functor. 
ap mor_vee_cat. 
Qed.





Definition vee_nt a u1 v1 u2 v2 r s t :=
nttyd (vee_fun_data a u1 v1) 
(vee_fun_data a u2 v2) 
(fun x : (obsy vee_data) => 
match x with 
o1 => r | o2 => s | o3 => t end).



Definition vee_nt_hypothesis  a u1 v1 u2 v2 r s t:=
Category.axioms a &
mor a u1 & mor a v1 &  mor a u2 & mor a v2 &
mor a r & mor a s & mor a t &
source r = source u1 & target r = source u2 &
source s = target u1 & target s = target u2 &
source t = source v1 & target t = source v2 &
target u1 = target v1 &
target u2 = target v2 &
comp a s u1 = comp a u2 r &
comp a s v1 = comp a v2 t.

Lemma vee_nttyd_property : forall a u1 v1 u2 v2 r s t,
vee_nt_hypothesis a u1 v1 u2 v2 r s t -> 
nttyd_property (vee_fun_data a u1 v1) 
(vee_fun_data a u2 v2) 
(fun x : (obsy vee_data) => 
match x with o1 => r | o2 => s | o3 => t end).
Proof.
ir. uh H; ee. 
assert (lem1: vee_hypothesis a u1 v1).
uhg; ee; am. 
assert (lem2: vee_hypothesis a u2 v2).
uhg; ee; am. 

uhg; ee. ap vee_data_property. 
app vee_fun_data_property. 
app vee_fun_data_property. 
rw ft_vee_fun_data;
rww ft_vee_fun_data. 

ir. rw ft_vee_fun_data.
nin x. am. am. am. 
ir. nin x. 
rww H7. rww H9. rww H11. 
ir. nin x. 
rww H8. rww H10. rww H12.  
ir. 
rw ft_vee_fun_data. 
nin u. 
change (comp a r (id a (source u1)) =
comp a (id a (source u2)) r).
rww right_id. rww left_id. 
rww ob_source. rww ob_source. 

change (comp a s (id a (target u1)) =
comp a (id a (target u2)) s).
rww left_id. rww right_id. 
rww ob_target. rww ob_target. 

change (comp a t (id a (source v1)) =
comp a (id a (source v2)) t).
rww left_id. rww right_id. 
rww ob_source. rww ob_source. 
am. am. 
Qed.

Lemma vee_nt_axioms : forall a u1 v1 u2 v2 r s t,
vee_nt_hypothesis a u1 v1 u2 v2 r s t-> 
Nat_Trans.axioms (vee_nt a u1 v1 u2 v2 r s t).
Proof.
ir. uf vee_nt. ap nttyd_axioms. 
ap vee_nttyd_property. am. 
Qed.


Lemma source_vee_nt : forall a u1 v1 u2 v2 r s t,
source (vee_nt a u1 v1 u2 v2 r s t) =
vee_functor a u1 v1.
Proof.
ir. 
uf vee_nt. rww source_nttyd. 
Qed.

Lemma target_vee_nt : forall a u1 v1 u2 v2 r s t,
target (vee_nt a u1 v1 u2 v2 r s t) =
vee_functor a u2 v2.
Proof.
ir. 
uf vee_nt. rww target_nttyd. 
Qed.

Lemma osource_vee_nt : forall a u1 v1 u2 v2 r s t,
osource (vee_nt a u1 v1 u2 v2 r s t) = vee_cat.
Proof.
ir. uf osource. rw source_vee_nt. 
rww source_vee_functor. 
Qed.

Lemma otarget_vee_nt : forall a u1 v1 u2 v2 r s t,
otarget (vee_nt a u1 v1 u2 v2 r s t) = a.
Proof.
ir. uf otarget. rw target_vee_nt. 
rww target_vee_functor. 
Qed.

Lemma ntrans_vee_nt_R : forall a u1 v1 u2 v2 r s t
(x:obsy vee_data),
ntrans (vee_nt a u1 v1 u2 v2 r s t) (R x) =
match x with
o1 => r | o2 => s | o3 => t end.
Proof.
ir. uf vee_nt. 
rw ntrans_nttyd. rw X_rewrite. tv. 
rw ob_catyd. sh x; tv. ap vee_data_property.  
Qed.

Lemma vee_nt_hypothesis_ntrans : forall u,
Nat_Trans.axioms u -> osource u = vee_cat ->
vee_nt_hypothesis (otarget u)
(fmor (source u) (catyd_arrow a12'))
(fmor (source u) (catyd_arrow a32'))
(fmor (target u) (catyd_arrow a12'))
(fmor (target u) (catyd_arrow a32'))
(ntrans u (R o1')) (ntrans u (R o2'))
(ntrans u (R o3')).
Proof.
ir. 
assert (Category.axioms (otarget u)).
rww category_axioms_otarget.
assert (Functor.axioms (source u)).
rww functor_axioms_source. 
assert (Functor.axioms (target u)).
rww functor_axioms_target. 



uhg; ee. am. 

wrr target_source. app mor_fmor. 
rw source_source. rw H0. 
ap mor_vee_cat. 

wr target_source. app mor_fmor. 
rw source_source. rw H0. 
ap mor_vee_cat. am. 


uf otarget. app mor_fmor. 
rw source_target. rw H0. 
ap mor_vee_cat. am. 


uf otarget. app mor_fmor. 
rw source_target. rw H0. 
ap mor_vee_cat. am. 


app mor_ntrans. rw H0. 
ap ob_vee_cat.  
 
app mor_ntrans. rw H0. 
ap ob_vee_cat.  

app mor_ntrans. rw H0. 
ap ob_vee_cat.  

rww source_fmor. 
rww source_catyd_arrow. rww source_ntrans. rw H0. 
ap ob_vee_cat.  

rw source_source; rw H0; ap mor_vee_cat. 

rww target_ntrans. rww source_fmor. 
rww source_catyd_arrow. 
rww source_target. rw H0. ap mor_vee_cat.  rw H0. 
ap ob_vee_cat.  

rww source_ntrans. rww target_fmor. 
rww target_catyd_arrow. 
rw source_source; rw H0; ap mor_vee_cat. rw H0. 
ap ob_vee_cat.  

rww target_ntrans. rww target_fmor. 
rww target_catyd_arrow. 
rww source_target. rw H0. ap mor_vee_cat. rw H0. 
ap ob_vee_cat. 

rww source_ntrans. rww source_fmor. 
rww source_catyd_arrow. rw source_source. 
rw H0. ap mor_vee_cat. rw H0. 
ap ob_vee_cat.  

rww target_ntrans. rww source_fmor. 
rww source_catyd_arrow. rw source_target. 
rw H0. ap mor_vee_cat. am. rw H0. 
ap ob_vee_cat.  


rw target_fmor. rw target_catyd_arrow. 
rw target_fmor. rw target_catyd_arrow. 
reflexivity. am. 
rw source_source; rw H0; ap mor_vee_cat. am. 
rw source_source; rw H0; ap mor_vee_cat. 



rw target_fmor. rw target_catyd_arrow. 
rw target_fmor. rw target_catyd_arrow. 
reflexivity. am. 
rww source_target; rw H0; ap mor_vee_cat. am. 
rww source_target; rw H0; ap mor_vee_cat. 

assert (R o2' = target (catyd_arrow a12')). 
rww target_catyd_arrow. rw H4. 

rw carre. rw source_catyd_arrow. 
reflexivity. am. rw H0. ap mor_vee_cat. 

assert (R o2' = target (catyd_arrow a32')).
rww target_catyd_arrow. rw H4. 

rw carre. rw source_catyd_arrow. 
reflexivity. am. rw H0. ap mor_vee_cat. 
Qed.

Lemma vee_nt_ntrans : forall u,
Nat_Trans.axioms u -> osource u = vee_cat ->
vee_nt (otarget u)
(fmor (source u) (catyd_arrow a12'))
(fmor (source u) (catyd_arrow a32'))
(fmor (target u) (catyd_arrow a12'))
(fmor (target u) (catyd_arrow a32'))
(ntrans u (R o1')) (ntrans u (R o2')) 
(ntrans u (R o3')) = u.
Proof.
ir. 

ap Nat_Trans.axioms_extensionality. 
ap vee_nt_axioms. 
app vee_nt_hypothesis_ntrans. am. 
rw source_vee_nt. 
wr target_source. sy; ap functor_vee_eq. 
uh H; ee. am. am. am. 

rw target_vee_nt. uf otarget. 
sy; ap functor_vee_eq. uh H; ee; am. 
rww source_target. 
ir. 
ufi osource H1. rwi source_vee_nt H1. 
rwi source_vee_functor H1. 
rwi ob_vee_cat_ex H1. nin H1. 
nin x0. 
rw H1. 
rw ntrans_vee_nt_R. reflexivity. 
rw H1. rw ntrans_vee_nt_R. reflexivity. 
rw H1. rw ntrans_vee_nt_R. reflexivity. 
Qed.

Lemma eq_vee_nt : forall u a u1 v1 u2 v2 r s t,
Nat_Trans.axioms u -> osource u = vee_cat ->
a = (otarget u) -> 
u1 = (fmor (source u) (catyd_arrow a12')) -> 
v1 =(fmor (source u) (catyd_arrow a32')) -> 
u2 =(fmor (target u) (catyd_arrow a12')) -> 
v2 =(fmor (target u) (catyd_arrow a32')) -> 
r =(ntrans u (R o1')) -> 
s =(ntrans u (R o2')) ->
t = (ntrans u (R o3')) -> 
u = vee_nt a u1 v1 u2 v2 r s t.
Proof.
ir.  rw H1; rw H2; rw H3; rw H4;
rw H5; rw H6; rw H7; rw H8;  rww vee_nt_ntrans. 
Qed.

Lemma constant_nt_vee_nt : forall a b u,
a = vee_cat -> mor b u ->
constant_nt a b u = vee_nt b 
(id b (source u)) (id b (source u))
(id b (target u)) (id b (target u))
u u u.
Proof.
ir. rw H. ap eq_vee_nt. 
app constant_nt_axioms. ap vee_cat_axioms. 
uh H0; ee; am. 
rww osource_constant_nt. rww otarget_constant_nt. 
rw source_constant_nt. rw fmor_constant_functor. 
tv. ap mor_vee_cat. 
rw source_constant_nt. rw fmor_constant_functor. 
tv. ap mor_vee_cat. 
rw target_constant_nt. rw fmor_constant_functor. 
tv. ap mor_vee_cat. 
rw target_constant_nt. rw fmor_constant_functor. 
tv. ap mor_vee_cat. 
rww ntrans_constant_nt. ap ob_vee_cat. 
rww ntrans_constant_nt. ap ob_vee_cat. 
rww ntrans_constant_nt. ap ob_vee_cat. 
Qed. 

Lemma vident_vee_functor : forall a u v,
vee_hypothesis a u v -> 
vident (vee_functor a u v) =
vee_nt a u v u v 
(id a (source u)) (id a (target u)) (id a (source v)).
Proof.
ir. 
cp vee_cat_axioms. 
cp (vee_functor_axioms H). 
cp H; uh H; ee. 
assert (ob a (source u)). 
rww ob_source. 
assert (ob a (target u)). 
rww ob_target. 
assert (ob a (source v)). 
rww ob_source. 

assert (vee_nt_hypothesis 
a u v u v (id a (source u)) (id a (target u)) (id a (source v))). 
uhg; ee. uh H; ee; am. 
am. am. am. am. 
app mor_id. app mor_id. 
app mor_id. 
rww source_id. rww target_id. rww source_id. 
rww target_id. rww source_id. rww target_id. 
am. am. 
rww left_id. rww right_id. rww left_id. rww right_id. 
sy; am. 

ap Nat_Trans.axioms_extensionality. 
rww vident_axioms. 
ap vee_nt_axioms. 
am. rww source_vident. 
rww source_vee_nt. rww target_vident.
rww target_vee_nt. 

ir. rwi osource_vident H9. rwi source_vee_functor H9.
rw ntrans_vident. 
rww target_vee_functor. 

rwi ob_vee_cat_ex H9. nin H9. 
nin x0. 
rw H9. rw fob_vee_functor_R. 
rw ntrans_vee_nt_R. 
reflexivity. am. 
rw H9. rw fob_vee_functor_R. 
rw ntrans_vee_nt_R. 
reflexivity. am. 
rw H9. rw fob_vee_functor_R. 
rw ntrans_vee_nt_R. 
reflexivity. am. 
rw source_vee_functor. am. 
Qed.

Lemma vcompose_vee_nt : forall a u1 v1 u2 v2 r s t
u1' v1' u2' v2' r' s' t',
vee_nt_hypothesis a u1 v1 u2 v2 r s t ->
vee_nt_hypothesis a u1' v1' u2' v2' r' s' t' ->
u1 = u2' -> v1 = v2' ->
vcompose (vee_nt a u1 v1 u2 v2 r s t)
(vee_nt a u1' v1' u2' v2' r' s' t') =
vee_nt a u1' v1' u2 v2 (comp a r r') (comp a s s')
(comp a t t').
Proof.
ir. wr H1. wr H2. wri H1 H0; wri H2 H0.
cp vee_cat_axioms. 
cp H; cp H0.
uh H4; uh H5. ee. 
assert (vee_hypothesis a u1 v1).
uhg; ee; am. 
assert (vee_hypothesis a u2 v2).
uhg; ee; am. 
assert (vee_hypothesis a u1' v1').
uhg; ee; am. 


cp (vee_functor_axioms H40). 
cp (vee_functor_axioms H41). 
cp (vee_functor_axioms H42). 

assert (ob a (source u1)). rww ob_source. 
assert (ob a (target u1)). rww ob_target. 
assert (ob a (source v1)). rww ob_source. 

assert (ob a (source u2)). rww ob_source. 
assert (ob a (target u2)). rww ob_target. 
assert (ob a (source v2)). rww ob_source. 

assert (ob a (source u1')). rww ob_source. 
assert (ob a (target u1')). rww ob_target. 
assert (ob a (source v1')). rww ob_source. 
cp (vee_nt_axioms H).
cp (vee_nt_axioms H0).

assert (source r = target r').
rww H14. 
assert (source s = target s'). 
rww H16. 
assert (source t = target t'). 
rww H18. 

assert (vee_nt_hypothesis
a u1' v1' u2 v2 (comp a r r') (comp a s s') (comp a t t')). 
uhg; ee. uh H6; ee; am. am. am. 
am. am. rww mor_comp. 
rww mor_comp. rww mor_comp. rww source_comp. 
rww target_comp. rww source_comp. rww target_comp.
rww source_comp. 
rww target_comp. 
am. am. rww assoc. rw H21. wrr assoc.
rw H38. rww assoc. sy; am. sy; am. 
rww assoc. rw H22. wrr assoc. rw H39. 
rww assoc. sy; am. wr H36. am. sy; am. 
wrr H19. 


ap Nat_Trans.axioms_extensionality. 
rw vcompose_axioms. tv. am. am. 
rw source_vee_nt. 
rw target_vee_nt. reflexivity. 
app vee_nt_axioms. 
rw source_vcompose. 
rw source_vee_nt. 
rw source_vee_nt. reflexivity. 
rw target_vcompose. 
rw target_vee_nt. 
rw target_vee_nt. reflexivity. 

ir. rwi osource_vcompose H61. 
rwi osource_vee_nt H61. 

rw ntrans_vcompose. rw otarget_vee_nt. 
rwi ob_vee_cat_ex H61. 
nin H61. nin x0. 
rw H61. 
rw ntrans_vee_nt_R. 
rw ntrans_vee_nt_R. 
rw ntrans_vee_nt_R. 
reflexivity. 
rw H61. 
rw ntrans_vee_nt_R. 
rw ntrans_vee_nt_R. 
rw ntrans_vee_nt_R. 
reflexivity. 
rw H61. 
rw ntrans_vee_nt_R. 
rw ntrans_vee_nt_R. 
rw ntrans_vee_nt_R. 
reflexivity. 
rw osource_vee_nt. am. 
Qed.


Lemma vee_nt_hypothesis_for_htrans_left : 
forall u1 v1 u2 v2 r s t f,
vee_nt_hypothesis (source f) u1 v1 u2 v2 r s t ->
Functor.axioms f  ->
vee_nt_hypothesis (target f) (fmor f u1) (fmor f v1) (fmor f u2) 
(fmor f v2) (fmor f r) (fmor f s) (fmor f t).
Proof.
ir. 
cp vee_cat_axioms. 
cp H.
uh H2. ee. 
assert (vee_hypothesis (source f) u1 v1).
uhg; ee; am. 
assert (vee_hypothesis (source f) u2 v2).
uhg; ee; am. 
cp (vee_functor_axioms H20). 
cp (vee_functor_axioms H21). 

assert (ob (source f) (source u1)). rww ob_source.
assert (ob (source f) (source u2)). rww ob_source.
assert (ob (source f) (target u1)). rww ob_target.
assert (ob (source f) (target u2)). rww ob_target.
assert (ob (source f) (source v1)). rww ob_source.
assert (ob (source f) (source v2)). rww ob_source.

cp (vee_nt_axioms H). 

uhg; ee; try (app mor_fmor);
try (rww source_fmor); try (rww source_fmor);
try (rww target_fmor); try (rww target_fmor);
try (app uneq).
uh H0; ee; am. 
rww comp_fmor. 
rww comp_fmor. app uneq. sy; am. 
 rww comp_fmor. 
rww comp_fmor. app uneq. sy; am. 
wrr H16. 
Qed.

Lemma htrans_left_vee_nt : forall a u1 v1 u2 v2 r s t f,
vee_nt_hypothesis a u1 v1 u2 v2 r s t ->
Functor.axioms f -> source f = a ->
htrans_left f (vee_nt a u1 v1 u2 v2 r s t) =
vee_nt (target f) (fmor f u1) (fmor f v1) (fmor f u2) 
(fmor f v2) (fmor f r) (fmor f s) (fmor f t).
Proof.
ir. 
wr H1. wri H1 H. 
cp vee_cat_axioms. 
cp H.
uh H3. ee. 
assert (vee_hypothesis (source f) u1 v1).
uhg; ee; am. 
assert (vee_hypothesis (source f) u2 v2).
uhg; ee; am. 
cp (vee_functor_axioms H21). 
cp (vee_functor_axioms H22). 

assert (ob (source f) (source u1)). rww ob_source.
assert (ob (source f) (source u2)). rww ob_source.
assert (ob (source f) (target u1)). rww ob_target.
assert (ob (source f) (target u2)). rww ob_target.
assert (ob (source f) (source v1)). rww ob_source.
assert (ob (source f) (source v2)). rww ob_source.
cp (vee_nt_axioms H). 

ap Nat_Trans.axioms_extensionality. 
app htrans_left_axioms. 
rww otarget_vee_nt. 
app vee_nt_axioms. 
app vee_nt_hypothesis_for_htrans_left. 
rww source_htrans_left. rww source_vee_nt. 
rw source_vee_nt. 
rw fcompose_vee_functor. tv. 
am. am. tv. 

rw target_htrans_left. rw target_vee_nt. 
rw fcompose_vee_functor. rw target_vee_nt. 
tv. am. am. tv. 

ir. rwi osource_htrans_left H32. rwi osource_vee_nt H32. 

rw ntrans_htrans_left. 
rwi ob_vee_cat_ex H32. nin H32. nin x0. 
rw H32. 
rw ntrans_vee_nt_R. rw ntrans_vee_nt_R. 
reflexivity. rw H32. 
rw ntrans_vee_nt_R. rw ntrans_vee_nt_R. 
reflexivity. rw H32. 
rw ntrans_vee_nt_R. rw ntrans_vee_nt_R. 
reflexivity. 
rww osource_vee_nt. 
Qed.

Lemma vee_nt_hypothesis_for_htrans_right : 
forall y u v,
Nat_Trans.axioms y -> vee_hypothesis (osource y) u v ->
vee_nt_hypothesis 
(otarget y) (fmor (source y) u) (fmor (source y) v)
(fmor (target y) u) (fmor (target y) v) 
(ntrans y (source u)) (ntrans y (target u))
(ntrans y (source v)).
Proof.
ir. 
cp vee_cat_axioms. 
cp H0. uh H2; ee. 
assert (ob (osource y) (source u)). rww ob_source. 
assert (ob (osource y) (target u)). rww ob_target.
assert (ob (osource y) (source v)). rww ob_source.  
assert (Functor.axioms (source y)).
rww functor_axioms_source. 
assert (Functor.axioms (target y)). 
rww functor_axioms_target. 
assert (Category.axioms (osource y)). 
rww category_axioms_osource. 
assert (Category.axioms (otarget y)). 
rww category_axioms_otarget. 

uhg; ee. am. 
wrr target_source; app mor_fmor. 
wrr target_source; app mor_fmor. 
wrr target_target; app mor_fmor; 
rww source_target. 
wrr target_target; app mor_fmor;  rww source_target. 
app mor_ntrans. app mor_ntrans. 
app mor_ntrans. 
rww source_ntrans. rww source_fmor. 
 rww target_ntrans. rww source_fmor. 
rww source_target. 
rww source_ntrans. rww target_fmor. 
rww target_ntrans. rww target_fmor. 
rww source_target. 
rww source_ntrans. rww source_fmor. 
rww target_ntrans. rww source_fmor. 
rww source_target. 
rww target_fmor. rww target_fmor. rww H4. 
rww target_fmor. rww target_fmor. rww H4. 
rww source_target. rww source_target. 
rww carre. rw H4. 
rww carre. 
Qed.

Lemma htrans_right_vee_functor : forall y a u v,
Nat_Trans.axioms y -> vee_hypothesis a u v ->
osource y = a ->
htrans_right y (vee_functor a u v) =
vee_nt (otarget y) (fmor (source y) u) (fmor (source y) v)
(fmor (target y) u) (fmor (target y) v) 
(ntrans y (source u)) (ntrans y (target u))
(ntrans y (source v)).
Proof.
ir. 
wr H1. wri H1 H0. 
cp vee_cat_axioms. 
cp H0. uh H3; ee. 
assert (ob (osource y) (source u)). rww ob_source. 
assert (ob (osource y) (target u)). rww ob_target. 
assert (Functor.axioms (source y)).
rww functor_axioms_source. 
assert (Functor.axioms (target y)). 
rww functor_axioms_target. 
assert (Category.axioms (osource y)). 
rww category_axioms_osource. 
assert (Category.axioms (otarget y)). 
rww category_axioms_otarget. 

ap Nat_Trans.axioms_extensionality. 
ap htrans_right_axioms. 
app vee_functor_axioms. am. 
rww target_vee_functor. 
ap vee_nt_axioms. 
app vee_nt_hypothesis_for_htrans_right. 
rw source_htrans_right. rw fcompose_vee_functor.
rw source_vee_nt. rww target_source. 
am. am. tv. 

rw target_htrans_right. rw fcompose_vee_functor.
rw target_vee_nt. reflexivity. am. am. 
rww source_target. 

ir. rwi osource_htrans_right H12. cp H12. 
rwi source_vee_functor H13. 
rww ntrans_htrans_right. 

rwi ob_vee_cat_ex H13. nin H13. nin x0; rw H13. 
rw fob_vee_functor_R. 
rw ntrans_vee_nt_R. reflexivity. am. 
rw fob_vee_functor_R. 
rw ntrans_vee_nt_R. reflexivity. am. 
rw fob_vee_functor_R. 
rw ntrans_vee_nt_R. reflexivity. am. 
Qed.

Lemma hcompose_vee_nt1 : forall u a u1 v1 u2 v2 r s t,
vee_nt_hypothesis a u1 v1 u2 v2 r s t ->
Nat_Trans.axioms u -> osource u = a ->
hcompose u (vee_nt a u1 v1 u2 v2 r s t) =
vee_nt (otarget u) (fmor (source u) u1) (fmor (source u) v1)
(fmor (target u) u2) (fmor (target u) v2)
(comp (otarget u) (ntrans u (source u2)) (fmor (source u) r))
(comp (otarget u) (ntrans u (target u2)) (fmor (source u) s))
(comp (otarget u) (ntrans u (source v2)) (fmor (source u) t)).
Proof.
ir. uf hcompose. 
rw target_vee_nt. 
util (htrans_right_vee_functor (y:=u) (a:=a) (u:=u2) (v:=v2)).
am. uh H; uhg; xd. am. 
rw H2. 

util (htrans_left_vee_nt (a:=a) (u1:=u1) (v1:=v1) (u2:=u2) (v2:=v2)
(r:=r) (s:=s) (t:=t) (f:=source u)). am. 
rww functor_axioms_source. am. 
rw H3. 

rw target_source. rw vcompose_vee_nt.  
reflexivity.  

ap vee_nt_hypothesis_for_htrans_right. 
am. rw H1. uh H; uhg; xd. 
wr target_source. 
ap vee_nt_hypothesis_for_htrans_left. 
rw source_source; rw H1. am. 
rww functor_axioms_source. am. 
tv. tv. am. 
Qed.

Lemma hcompose_vee_nt2 : forall u a u1 v1 u2 v2 r s t,
vee_nt_hypothesis a u1 v1 u2 v2 r s t ->
Nat_Trans.axioms u -> osource u = a ->
hcompose u (vee_nt a u1 v1 u2 v2 r s t) =
vee_nt (otarget u) (fmor (source u) u1) (fmor (source u) v1)
(fmor (target u) u2) (fmor (target u) v2)
(comp (otarget u) (fmor (target u) r) (ntrans u (source u1)) )
(comp (otarget u) (fmor (target u) s) (ntrans u (target u1)) )
(comp (otarget u) (fmor (target u) t) (ntrans u (source v1)) ).
Proof.
ir. 
rw Nat_Trans.hcompose_other. 
uf hcompose1. 
rw source_vee_nt. 
util (htrans_right_vee_functor (y:=u) (a:=a) (u:=u1) (v:=v1)).
am. uh H; uhg; xd. am. 
rw H2. 

util (htrans_left_vee_nt (a:=a) (u1:=u1) (v1:=v1) (u2:=u2) (v2:=v2)
(r:=r) (s:=s) (t:=t) (f:=target u)). am. 
rww functor_axioms_target. rww source_target.  
rw H3. 

rw target_target. rw vcompose_vee_nt.  
reflexivity.  


wr target_target. 
ap vee_nt_hypothesis_for_htrans_left. 
rw source_target. rw H1. am. am. 
rww functor_axioms_target. 

ap vee_nt_hypothesis_for_htrans_right. 
am. rw H1. uh H; uhg; xd. 
tv. tv. 

uhg. ee. am. app vee_nt_axioms. 
rww otarget_vee_nt. 
Qed.




Lemma vee_obs_tack : tack (R o1) (tack (R o2) 
(tack (R o3) emptyset))
= vee_obs. 
Proof.
ap extensionality; uhg; ir. 
rwi tack_inc H. 
nin H. rwi tack_inc H. nin H. rwi tack_inc H. nin H. 
nin H. elim x0. rw H. ap R_inc. rw H. ap R_inc. 
rw H. ap R_inc. 
nin H. wr H. 
nin x0. 
rw tack_inc. ap or_intror. tv. 
rw tack_inc. ap or_introl.  
rw tack_inc. ap or_intror; tv. 
rw tack_inc. ap  or_introl. 
rw tack_inc. ap or_introl. 
rw tack_inc. ap or_intror; tv. 
Qed.

Lemma vee_maps_tack : 
tack (R i1) (tack (R i2) (tack (R i3)
(tack (R a12) (tack (R a32) emptyset))))
= vee_maps. 
Proof.
ap extensionality; uhg; ir. 
rwi tack_inc H. 
nin H. rwi tack_inc H.
nin H. rwi tack_inc H. 
nin H. rwi tack_inc H. 
nin H. rwi tack_inc H. 
nin H. nin H. nin x0. 
rw H. ap R_inc. 
rw H. ap R_inc. 
rw H. ap R_inc. 
rw H. ap R_inc. 
rw H. ap R_inc. 

rw tack_inc. 
rw tack_inc. rw tack_inc. 
rw tack_inc. 
nin H. wr H. 
nin x0. 
ap or_intror. tv. 
ap or_introl; ap or_intror; tv. 
ap or_introl; ap or_introl; ap or_intror; tv. 
ap or_introl; ap or_introl; ap or_introl. 
ap or_intror; tv. 
ap or_introl; ap or_introl; ap or_introl; ap or_introl. 
rw tack_inc. ap or_intror; tv. 
Qed. 




Lemma is_finite_vee_obs : is_finite (vee_obs).
Proof.
wr vee_obs_tack. 
ap finite_tack. ap finite_tack. ap finite_tack. 
ap finite_emptyset. 
Qed.

Lemma is_finite_vee_maps : is_finite (vee_maps).
Proof.
wr vee_maps_tack. 
ap finite_tack. ap finite_tack. ap finite_tack. 
ap finite_tack. ap finite_tack. 
ap finite_emptyset. 
Qed.

Lemma is_finite_vee_cat : is_finite_cat vee_cat.
Proof.
uf vee_cat. 
ap is_finite_catyd. 
ap vee_data_property. 
exact (is_finite_vee_obs). 
exact (is_finite_vee_maps). 
Qed. 








End Vee_Cat.





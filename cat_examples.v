Set Implicit Arguments.
Unset Strict Implicit.

Require Import Arith.
Require Export ordinal.
Require Export nat_trans.


Module Subcategory.
Export Nat_Trans.


Definition subcategory a (obp morp:E->Prop) :=
Category.Notations.create (Z (objects a) obp)
(Z (morphisms a) morp)
(comp a) (id a) (structure a).

Lemma is_ob_subcategory : forall a (obp morp:E->Prop) x,
is_ob (subcategory a obp morp) x = 
(is_ob a x & obp x).
Proof.
ir. 
uf subcategory. rw is_ob_create. 
app iff_eq; ir. ee. 
Ztac. Ztac. ee. Ztac. 
Qed. 

Lemma is_mor_subcategory : forall a (obp morp:E->Prop) u,
is_mor (subcategory a obp morp) u =
(is_mor a u & morp u).
Proof.
ir. uf subcategory. 
rw is_mor_create. ap iff_eq; ir. 
ee. Ztac. Ztac. ee. Ztac. 
Qed.

Lemma structure_subcategory : forall a obp morp,
structure (subcategory a obp morp) = structure a.
Proof.
ir. uf subcategory. rw structure_create. tv. 
Qed. 


Definition subcategory_property a (obp morp:E->Prop) :=
(Category.axioms a) &
(forall u v, mor a u -> mor a v -> source u = target v ->
morp u -> morp v -> morp (comp a u v)) &
(forall x, ob a x -> obp x -> morp (id a x)) &
(forall u, mor a u -> morp u -> obp (source u)) &
(forall u, mor a u -> morp u -> obp (target u)).

Lemma subcategory_axioms : forall a obp morp,
subcategory_property a obp morp -> 
Category.axioms (subcategory a obp morp).
Proof.
ir. 
cp H. uh H0; ee. 
uf subcategory. 
ap Category.create_axioms. uhg; ee; ir. 
ap iff_eq; ir. Ztac. 
assert (ob a x). app is_ob_ob. 
uhg; ee. Ztac. ap Z_inc. ap mor_is_mor. app mor_id. 
app H2. rww source_id. rww target_id. 
uh H5; ee. ap Z_inc. pose (Z_all H5). ee. am. 
pose (Z_all H5); ee. am. 

ap iff_eq; ir. Ztac. assert (mor a u). 
ap is_mor_mor. am. am. 
uhg; ee. app Z_inc. 
app Z_inc. ap ob_is_ob. rww ob_source. app H3. 
ap Z_inc. ap ob_is_ob. rww ob_target. app H4. 
rww right_id. rww ob_source. rww left_id. 
rww ob_target. apply mor_arrow_like with a. am. 
uh H5; ee. pose (Z_all H5). ee. 
Ztac. 

Ztac. clear H6. Ztac. clear H5. 
assert (mor a u). app is_mor_mor. 
assert (mor a v). app is_mor_mor. 
uhg; ee. Ztac. Ztac. am. 
Ztac. ap mor_is_mor. rww mor_comp. 
rww source_comp. rww target_comp. 
assert (mor a u). 
pose (Z_all H5); ee; app is_mor_mor. 
assert (mor a v). 
pose (Z_all H6); ee; app is_mor_mor. 
assert (mor a w). 
pose (Z_all H7); ee; app is_mor_mor. 
rww assoc. 
Qed.

Lemma ob_subcategory : forall a obp morp x,
subcategory_property a obp morp -> 
ob (subcategory a obp morp) x = (ob a x & obp x).
Proof.
ir. app iff_eq; ir. 
assert (is_ob (subcategory a obp morp) x). 
app ob_is_ob. rwi is_ob_subcategory H1. 
xd. app is_ob_ob. uh H; ee; am. 
ap is_ob_ob. 
app subcategory_axioms. rw is_ob_subcategory. 
xd. app ob_is_ob. 
Qed.

Lemma mor_subcategory : forall a obp morp u,
subcategory_property a obp morp -> 
mor (subcategory a obp morp) u = (mor a u & morp u).
Proof.
ir. app iff_eq; ir. 
assert (is_mor (subcategory a obp morp) u). 
app mor_is_mor. rwi is_mor_subcategory H1. 
xd. app is_mor_mor. uh H; ee; am. 
ap is_mor_mor. 
app subcategory_axioms. rw is_mor_subcategory. 
xd. app mor_is_mor. 
Qed.

Definition is_subcategory a b :=
Category.axioms a &
Category.axioms b &
structure a = structure b &
(forall x, ob a x -> ob b x) &
(forall u, mor a u -> mor b u) &
(forall u v, mor a u -> mor a v -> source u = target v ->
comp a u v = comp b u v) &
(forall x, ob a x -> id a x = id b x).

(**** remark (2 sep 04): it is necessary to include the condition
about identity elements. To see this (we give the informal
proof rather than a construction in coq) look at the example
of a category with one object and two morphisms, one of
which is an idempotent and the other is the identity.
For example, the identity and an orthogonal projection matrix.
The sub-semicategory consisting of the same object and just the
idempotent is itself a category and satisfies the other 
conditions but the identities are not the same so it isn't a
subcategory (and the inclusion isn't a functor). ****)

Lemma is_subcategory_mor : forall b u,
(exists a, is_subcategory a b & mor a u) -> mor b u.
Proof.
ir. nin H. ee. uh H; ee. au. 
Qed.

Lemma is_subcategory_ob: forall b x,
(exists a, is_subcategory a b & ob a x) -> ob b x.
Proof.
ir. nin H. ee. uh H; ee. au.  
Qed.


Lemma is_subcategory_same_id : forall a b,
is_subcategory a b -> 
(forall x, ob a x ->
id a x = id b x).
Proof.
ir. uh H; ee. au. 
Qed. 

Lemma is_subcategory_same_comp : forall a b,
is_subcategory a b -> 
(forall u v, mor a u -> mor a v ->
source u = target v -> comp a u v = comp b u v).
Proof.
ir. uh H; ee. au. 
Qed. 

Lemma id_subcategory : forall a obp morp x,
subcategory_property a obp morp ->
ob a x -> obp x -> id (subcategory a obp morp) x = id a x.
Proof.
ir. 
uf subcategory. rw id_create. tv. 
Ztac. ap ob_is_ob. am. 
Qed.

Lemma comp_subcategory : forall a obp morp u v,
subcategory_property a obp morp ->
mor a u -> mor a v -> source u = target v ->
morp u -> morp v -> comp (subcategory a obp morp) u v = 
comp a u v.
Proof.
ir. uf subcategory. rw comp_create. 
tv. Ztac. app mor_is_mor. Ztac. app mor_is_mor. 
am. 
Qed. 

Lemma is_subcategory_property : forall a b,
is_subcategory a b ->
subcategory_property b (ob a) (mor a).
Proof.
ir. cp H.  uh H; ee. 
uhg; ee. am. ir. 
wr H5. rww mor_comp. am. am. am. 
ir. wr (is_subcategory_same_id H0). app mor_id. am. 
ir. rww ob_source. ir. rww ob_target. 
Qed.






Lemma subcategory_is_subcategory : forall a obp morp,
subcategory_property a obp morp -> 
is_subcategory (subcategory a obp morp) a.
Proof.
ir. cp H. uh H0; ee. 
uhg; ee. app subcategory_axioms. am. 
rww structure_subcategory. 
ir. rwi ob_subcategory H5. 
ee; am. am. 
ir. rwi mor_subcategory H5. ee; am. 
am. ir. 
rwi mor_subcategory H5. rwi mor_subcategory H6. ee. 
rww comp_subcategory. 
am. am. 
ir. rwi ob_subcategory H5. ee. 
rww id_subcategory. am. 
Qed.

Lemma is_subcategory_refl : forall a,
Category.axioms a -> is_subcategory a a.
Proof.
ir. uhg; ee. am. am. tv. 
ir; am. ir; am. ir; tv. ir; tv. 
Qed.

Lemma is_subcategory_trans : forall a b c,
is_subcategory a b -> is_subcategory b c -> 
is_subcategory a c.
Proof.
ir. uh H; uh H0; ee. 
uhg; ee; try am; try tv. 
transitivity (structure b); try am; try (sy; am). 
ir. au. ir. au. ir. 
rww H11. rww H5. au. au. 
ir. rww H12. rww H6. au. 
Qed.

Lemma is_subcategory_extensionality : forall a b,
is_subcategory a b -> is_subcategory b a ->
a = b.
Proof.
ir. cp H. cp H0. 
uh H; uh H0; ee. 
uh H; uh H9; ee. 
rw H22. sy. rw H18. 
ap Notations.create_extensionality. 
ap extensionality; uhg; ir. 
ap ob_is_ob. ap H5. app is_ob_ob. 
ap ob_is_ob. ap H11. app is_ob_ob. 

ap extensionality; uhg; ir. 
ap mor_is_mor. ap H6. app is_mor_mor. 
ap mor_is_mor. ap H12. app is_mor_mor. 

ir. 
app H7. app is_mor_mor. app is_mor_mor. 
ir. app H8. app is_ob_ob. am. 
Qed.

Lemma is_subcategory_eq : forall a b,
is_subcategory a b -> 
subcategory b (ob a) (mor a) = a.
Proof.
ir. 
assert (lem1 : subcategory_property b (ob a) (mor a)).
app is_subcategory_property. 
cp H. uh H0; ee. 
ap is_subcategory_extensionality. 
uhg; ee. app subcategory_axioms. 
am. rww structure_subcategory. sy; am. 
ir. rwi ob_subcategory H7; ee. am. 
am. 
ir. rwi mor_subcategory H7; ee; am. 
ir. rwi mor_subcategory H7; rwi mor_subcategory H8; ee.
rw comp_subcategory. sy; app H5. am. 
am. am. am. am. am. am. am. am. 
ir. rwi ob_subcategory H7; ee. 
rww id_subcategory. sy; app H6. am. 

uhg; ee. am. app subcategory_axioms. 
rww structure_subcategory. 
ir. rww ob_subcategory; ee; try am. au. 
ir. rww mor_subcategory; ee; au. 
ir. rww comp_subcategory. 
au. au. au. 
ir. rww id_subcategory. au. au. 
Qed.


Lemma source_inclusion : forall a b,
source (inclusion a b) = a.
Proof.
ir. uf inclusion. 
rww Umorphism.source_create. 
Qed.

Lemma target_inclusion : forall a b, 
target (inclusion a b) = b.
Proof.
ir. uf inclusion. 
rww Umorphism.target_create. 
Qed.


Lemma fmor_inclusion : forall a b u,
mor a u -> fmor (inclusion a b) u = u.
Proof.
ir. uf inclusion. 
uf fmor. rww Umorphism.ev_create. 
change (is_mor a u). app mor_is_mor. 
Qed.

Lemma fob_inclusion : forall a b x,
ob a x -> fob (inclusion a b) x = x.
Proof.
ir. uf fob. 
rw source_inclusion. 
rww fmor_inclusion. rww source_id. 
app mor_id. 
Qed.

Lemma subcategory_inclusion_axioms : forall a b,
is_subcategory a b -> 
Functor.axioms (Umorphism.inclusion a b).
Proof.
ir. uh H; ee. 
uhg; ee. uf inclusion. app Umorphism.create_like. 
rww source_inclusion. 
rww target_inclusion. 
ir. rw target_inclusion. rwi source_inclusion H6. 
rww fob_inclusion. au. 
ir. rwi source_inclusion H6. 
rw target_inclusion. rww fob_inclusion. 
rw source_inclusion. rww fmor_inclusion. 
sy; au. app mor_id. 
ir. rwi source_inclusion H6. 
rw target_inclusion. rww fmor_inclusion. 
au. 
ir. rwi source_inclusion H6. 
rww fmor_inclusion. rww fob_inclusion. rww ob_source. 
ir. rwi source_inclusion H6. 
rww fmor_inclusion. rww fob_inclusion. rww ob_target. 
ir. 
rwi source_inclusion H6. rwi source_inclusion H7. 
rw target_inclusion. rww fmor_inclusion. 
rww fmor_inclusion. 
rww source_inclusion. rww fmor_inclusion. 
sy; au. rww mor_comp. 
Qed.

Lemma subcategory_inclusion_refl : forall a,
Category.axioms a -> 
Umorphism.inclusion a a = fidentity a.
Proof.
ir. 
reflexivity. 
Qed.

Lemma umorphism_create_extensionality : forall a b f a1 b1 f1,
a = a1 -> b = b1 -> 
(forall x, inc x (U a) -> inc (f x) (U b)) ->
(forall x, inc x (U a) -> f x = f1 x) ->
Umorphism.create a b f = Umorphism.create a1 b1 f1.
Proof.
ir. 
assert (Umorphism.property a b f).
uhg; ee. uhg; ee. am. 
assert (Umorphism.property a1 b1 f1).
wr H. wr H0. uhg. uhg. 
ir. wr H2. au. am. 

ap Umorphism.extens. 
ap create_strong_axioms. am. 
ap create_strong_axioms. am. 
rw Umorphism.source_create. rww Umorphism.source_create. 
rww Umorphism.target_create. rww Umorphism.target_create. 
ir. rwi Umorphism.source_create H5. 
rwi Umorphism.source_create H6. 
rww ev_create. rww ev_create. au. 

Qed.


Lemma subcategory_inclusion_trans : forall a b c,
is_subcategory a b -> is_subcategory b c -> 
fcompose (Umorphism.inclusion b c) (Umorphism.inclusion a b) =
Umorphism.inclusion a c.
Proof.
ir. 
uf fcompose. 
uf compose. 
rw source_inclusion. rw target_inclusion. 
uf inclusion. 
assert (sub (U a) (U b)). 
uhg; ir. uh H; ee. change (is_mor b x).
app mor_is_mor. ap H5. app is_mor_mor. 
assert (sub (U b) (U c)). 
uhg; ir. uh H0; ee. change (is_mor c x).
app mor_is_mor. ap H6. app is_mor_mor. 
assert (sub (U a) (U c)).
apply sub_trans with (U b); try am. 


app umorphism_create_extensionality. 
ir. 
cp (H1 _ H4). cp (H3 _ H4). 
rww ev_create. rww ev_create. rww ev_create. 

ir. cp (H1 _ H4). cp (H3 _ H4). 
rww ev_create. rww ev_create. rww ev_create. 
Qed.


End Subcategory.

Export Subcategory.

Module From_Arrows.
Export Nat_Trans.

Section Construction.
Variable obs : E.
Variable homs : E -> E -> E.
Variable comps :  E -> E -> E.
Variable ids : E -> E.

Definition morphism_set_pool := 
Image.create (Cartesian.product obs obs) 
(fun q => homs (pr1 q) (pr2 q)).

Lemma inc_morphism_set_pool : forall r,
inc r morphism_set_pool = 
exists a, exists b, (inc a obs & inc b obs & r = (homs a b)).
Proof.
ir. 
uf morphism_set_pool. 
rw Image.inc_rw. 
app iff_eq; ir. nin H; ee. 
sh (pr1 x). sh (pr2 x). ee; try (sy; am). 
cp (Cartesian.product_pr H). ee. am. 
cp (Cartesian.product_pr H). ee. am. 
nin H. nin H. sh (pair x x0). ee. 
ap Cartesian.product_pair_inc. am. am. 
rw pr1_pair. rw pr2_pair. sy; am. 
Qed.   

Definition morphism_set := union morphism_set_pool.

Lemma inc_morphism_set1 : 
forall r,
inc r morphism_set = 
exists a, exists b, (inc a obs & inc b obs & inc r (homs a b)).
Proof.
ir. 
ap iff_eq; ir. 
ufi morphism_set H. nin (union_exists H). ee. 
rwi inc_morphism_set_pool H1. 
nin H1. nin H1. ee. sh x0. sh x1. ee; try am. wrr H3. 

nin H. nin H. ee. uf morphism_set. 
apply union_inc with (homs x x0). am. 
rw inc_morphism_set_pool. 
sh x. sh x0. ee; try am; try tv. 
Qed. 

Definition property := 
(forall a b u, inc u (homs a b) -> source u = a) &
(forall a b u, inc u (homs a b) -> target u = b) &
(forall a b u, inc u (homs a b) -> 
Arrow.like u) &
(forall a b c u v,
inc a obs -> inc b obs -> inc c obs ->
inc u (homs b c) -> inc v (homs a b) ->
inc (comps u v) (homs a c)) &
(forall a,
inc a obs -> inc (ids a) (homs a a)) &
(forall a b u,
inc a obs -> inc b obs -> inc u (homs a b) ->
comps u (ids a) = u) &
(forall a b u,
inc a obs -> inc b obs -> inc u (homs a b) ->
comps (ids b) u = u) &
(forall a b c d u v w,
inc a obs -> inc b obs -> inc c obs -> inc d obs ->
inc u (homs c d) -> inc v (homs b c) -> inc w (homs a b) ->
comps u (comps v w) = comps (comps u v) w).

Hypothesis property_hyp : property.


Lemma inc_morphism_set : forall r,
inc r morphism_set = 
(inc (source r) obs & inc (target r) obs & 
inc r (homs (source r) (target r))).
Proof.
ir. 
cp property_hyp. uh H; ee. 
ap iff_eq; ir. 
rwi inc_morphism_set1 H7. 
nin H7. nin H7. ee. rww (H _ _ _ H9). 
rww (H0 _ _ _ H9). 
rww (H _ _ _ H9). rww (H0 _ _ _ H9). 
ee. rw inc_morphism_set1. 
sh (source r). sh (target r). ee; try am. 
Qed.

Definition from_arrows := 
Category.Notations.create obs morphism_set comps ids emptyset.

Lemma structure_from_arrows : structure from_arrows = emptyset.
Proof.
uf from_arrows. rww structure_create. 
Qed.

Lemma is_ob_from_arrows : forall x, 
is_ob from_arrows x = inc x obs.
Proof.
ir. ap iff_eq; ir. ufi from_arrows H. 
rwi is_ob_create H. am. 
uf from_arrows. rww is_ob_create. 
Qed.

Lemma is_mor_from_arrows : forall u,
is_mor from_arrows u = 
(is_ob from_arrows (source u) &
is_ob from_arrows (target u) &
inc u (homs (source u) (target u))).
Proof.
ir. ap iff_eq; ir. ufi from_arrows H. 
rwi is_mor_create H. rwi inc_morphism_set H. 
xd. rww is_ob_from_arrows. rww is_ob_from_arrows. 
uf from_arrows; rw is_mor_create. 
rw inc_morphism_set. xd. rwi is_ob_from_arrows H; am.
rwi is_ob_from_arrows H0; am. 
Qed.

Lemma is_mor_from_arrows2 : forall u,
is_mor from_arrows u = inc u morphism_set.
Proof.
ir. ap iff_eq; ir. ufi from_arrows H. 
rwi is_mor_create H. am. 
uf from_arrows; rww is_mor_create. 
Qed. 

Lemma comp_from_arrows : forall u v,
is_mor from_arrows u -> is_mor from_arrows v -> source u = target v ->
comp from_arrows u v = comps u v.
Proof.
ir. uf from_arrows. 
rw comp_create. tv. 
rwi is_mor_from_arrows2 H; am. 
rwi is_mor_from_arrows2 H0; am. am. 
Qed.

Lemma id_from_arrows : forall x, is_ob from_arrows x ->
id from_arrows x = ids x.
Proof.
ir. uf from_arrows. 
rww id_create. rwi is_ob_from_arrows H; am. 
Qed.

Lemma inc_homs_is_mor : forall u,
(exists a, exists b, (inc a obs & inc b obs & inc u (homs a b)))->
is_mor from_arrows u.
Proof.
ir. nin H. nin H. ee. 
rw is_mor_from_arrows2. rw inc_morphism_set1. 
sh x. sh x0. ee; am. 
Qed. 

Lemma inc_homs_source : forall a u,
is_ob from_arrows a ->
(exists b, (is_ob from_arrows b & inc u (homs a b))) ->
source u = a.
Proof.
ir. nin H0. ee. rwi is_ob_from_arrows H. 
rwi is_ob_from_arrows H0. cp property_hyp.
uh H2; ee. exact (H2 _ _ _ H1). 
Qed.

Lemma inc_homs_target : forall a u,
is_ob from_arrows a ->
(exists b, (is_ob from_arrows b & inc u (homs b a))) ->
target u = a.
Proof.
ir. nin H0. ee. rwi is_ob_from_arrows H. 
rwi is_ob_from_arrows H0. cp property_hyp.
uh H2; ee. exact (H3 _ _ _ H1). 
Qed.

Lemma source_ids : forall x, 
inc x obs -> source (ids x) = x.
Proof.
ir. cp property_hyp. uh H0; ee. 
cp (H4 _ H). 
exact (H0 _ _ _ H8). 
Qed.

Lemma target_ids : forall x,
inc x obs -> target (ids x) = x.
Proof.
ir. cp property_hyp. uh H0; ee. 
cp (H4 _ H). 
exact (H1 _ _ _ H8). 
Qed.

Lemma is_mor_id_from_arrows : forall x,
is_ob from_arrows x -> is_mor from_arrows (id from_arrows x).
Proof.
ir. cp H. cp property_hyp.   rwi is_ob_from_arrows
H0. 
uh H1; ee.
rw  is_mor_from_arrows. rww id_from_arrows. 
rww source_ids. rww target_ids. 
ee; try am. app H5.  
Qed.

Lemma source_id_from_arrows : forall x,
is_ob from_arrows x -> source (id from_arrows x) = x.
Proof.
ir. rww id_from_arrows. rww source_ids. 
wrr is_ob_from_arrows. 
Qed.

Lemma target_id_from_arrows : forall x,
is_ob from_arrows x -> target (id from_arrows x) = x.
Proof.
ir. rww id_from_arrows. rww target_ids. 
wrr is_ob_from_arrows. 
Qed.

Lemma left_id_from_arrows : forall u,
is_mor from_arrows u -> 
comp from_arrows (id from_arrows (target u)) u = u.
Proof.
ir. cp property_hyp. cp H. rwi is_mor_from_arrows H1.
ee. cp H1; cp H2. 
rwi is_ob_from_arrows H4; rwi is_ob_from_arrows H5. 
rww comp_from_arrows. 
rww id_from_arrows. uh H0; ee. apply H11 with (source u). 
am. am. am. 
app is_mor_id_from_arrows. 
rww source_id_from_arrows. 
Qed.

Lemma right_id_from_arrows : forall u,
is_mor from_arrows u -> 
comp from_arrows u (id from_arrows (source u)) = u.
Proof.
ir. cp property_hyp. cp H. rwi is_mor_from_arrows H1.
ee. cp H1; cp H2. 
rwi is_ob_from_arrows H4; rwi is_ob_from_arrows H5. 
rww comp_from_arrows. 
rww id_from_arrows. uh H0; ee. apply H10 with (target u). 
am. am. am. 
app is_mor_id_from_arrows. 
rww target_id_from_arrows. 
Qed.



Lemma from_arrows_axioms : Category.axioms from_arrows.
Proof.
uhg; ee; ir. 
ap iff_eq; ir. uhg; ee. am. 
app is_mor_id_from_arrows. 
rww source_id_from_arrows. rww target_id_from_arrows. 
ir. wr H1. rww right_id_from_arrows. 
ir. wr H1. rww left_id_from_arrows. 
uh H; ee; am. 

ap iff_eq; ir. uhg; ee. am. 
rwi is_mor_from_arrows H. ee; am. 
rwi is_mor_from_arrows H. ee; am.  
rww left_id_from_arrows. rww right_id_from_arrows. 
rwi is_mor_from_arrows H; ee. cp property_hyp.
uh H2; ee.  exact (H4 _ _ _ H1). uh H; ee; am. 

ap iff_eq; ir. 
assert (lema : are_composable from_arrows u v).
am. 
uh H; ee. 
rwi is_mor_from_arrows H.
rwi is_mor_from_arrows H0. ee. 
cp property_hyp. uh H6; ee. 
util (H9 (source v) (source u) (target u) u v).
wrr is_ob_from_arrows. wrr is_ob_from_arrows. 
wrr is_ob_from_arrows. am. rww H1. 
util (inc_homs_source (a:= (source v)) (u:= (comps u v))). 
am. sh (target u). ee; am. 
util (inc_homs_target (a:= (target u)) (u:= (comps u v))). 
am. sh (source v). ee; am. 
assert (is_mor from_arrows u). rw is_mor_from_arrows; ee; am. 
assert (is_mor from_arrows v). rw is_mor_from_arrows; ee; am. 

uhg; ee. 
am. rw is_mor_from_arrows; ee. 
rw is_ob_from_arrows. rww comp_from_arrows. rw H15. 
wrr is_ob_from_arrows. 
rww comp_from_arrows. rw H16. am. 
rww comp_from_arrows. 
rw H15. rw H16. am. 
rww comp_from_arrows. rww comp_from_arrows. 
uh H; ee; am. 

uh H; uh H0; ee. cp H; cp H3; cp H1. 
rwi is_mor_from_arrows H5;
rwi is_mor_from_arrows H6;
rwi is_mor_from_arrows H7; ee. 

cp property_hyp. uh H14; ee. 
util (H17 (source v) (source u) (target u) u v).
wrr is_ob_from_arrows. wrr is_ob_from_arrows. 
wrr is_ob_from_arrows. am. rww H4. 

util (H17 (source w) (source v) (source u) v w).
wrr is_ob_from_arrows. wrr is_ob_from_arrows. 
wrr is_ob_from_arrows.  rww H4. rww H2. 
sy. 
rww comp_from_arrows. 
rww comp_from_arrows. rww comp_from_arrows. rww comp_from_arrows.

apply H21 with (source w) (source v) (source u) (target u).
wrr is_ob_from_arrows. 
wrr is_ob_from_arrows. 
wrr is_ob_from_arrows. 
wrr is_ob_from_arrows. 
am. rww H4. rww H2. 
rww comp_from_arrows. ap inc_homs_is_mor. 
sh (source v). sh (target u). ee. 

wrr is_ob_from_arrows. 
wrr is_ob_from_arrows. am. 
ap inc_homs_source. am. sh (target u). 
ee; try am. wrr H2. 
rww comp_from_arrows. 

rww comp_from_arrows. ap inc_homs_is_mor. 
sh (source w); sh (source u). ee. 
wrr is_ob_from_arrows. 
wrr is_ob_from_arrows. 
am. 
sy; ap inc_homs_target. 
am. sh (source w). ee; try am. 
rww comp_from_arrows. 

uf from_arrows. 
ap Notations.create_like. 
Qed.


Lemma ob_from_arrows : forall x, 
ob from_arrows x = inc x obs.
Proof.
ir. ap iff_eq; ir. wrr is_ob_from_arrows. 
app ob_is_ob. 
wri is_ob_from_arrows H. app is_ob_ob. 
ap from_arrows_axioms. 
Qed.

Lemma mor_from_arrows : forall u,
mor from_arrows u = 
(ob from_arrows (source u) &
ob from_arrows (target u) &
inc u (homs (source u) (target u))).
Proof.
ir. cp from_arrows_axioms. ap iff_eq; ir. 
assert (is_mor from_arrows u). 
app mor_is_mor. rwi is_mor_from_arrows H1. 
ee; try am.
app is_ob_ob. 
app is_ob_ob. 
ap is_mor_mor. ap from_arrows_axioms. 
rww is_mor_from_arrows. ee; try am. 
app ob_is_ob. app ob_is_ob. 
Qed.

End Construction.

End From_Arrows.

Export From_Arrows.



Module Function_Cat.
Export Function_Set.
Export Nat_Trans.


Definition function_arrow_set a b :=
Image.create 
(function_set a (fun x:E => b)) (fun u => Arrow.create a b u).

Lemma inc_function_arrow_set : forall a b u,
inc u (function_arrow_set a b) =
(Arrow.like u &
source u = a &
target u = b &
Function.axioms (arrow u) &
Function.domain (arrow u) = a &
sub (Function.range (arrow u)) b &
Map.axioms a b (arrow u)).
Proof.
ir. 
ap iff_eq; ir. 
ufi function_arrow_set H. 
rwi Image.inc_rw H. nin H. 
dj; ee; cp (function_set_pr H); ee. 
wr H0. rww Arrow.create_like. 
wr H1. rww Arrow.source_create. 
wr H2. rww Arrow.target_create. 
wr H3. rw Arrow.arrow_create. am. 
wr H4. rw Arrow.arrow_create. am. 
wr H5. rw Arrow.arrow_create. 
uhg; ir. nin (range_ex H7 H10). ee. 
wr H12. ap H9. wrr H8. 
uhg; ee. am. am. am. 

ee. uf function_arrow_set. rw Image.inc_rw. 
sh (arrow u). ee. 
ap function_set_inc. am. am. 
ir. ap H4. ap range_inc. am. 
sh y. ee; try tv; try am. rww H3. uh H. 
wr H0. wr H1. sy; am. 
Qed.

Definition fa_comp u v :=
Arrow.create (source v) (target u) 
(Function.compose (arrow u) (arrow v)).

Definition fa_id x := 
Arrow.create x x (Function.identity x).

Lemma source_fa_comp : forall u v,
source (fa_comp u v) = source v.
Proof.
ir. uf fa_comp. rww Arrow.source_create.
Qed.

Lemma target_fa_comp : forall u v,
target (fa_comp u v) = target u.
Proof.
ir. uf fa_comp. rww Arrow.target_create.
Qed.

Lemma arrow_fa_comp : forall u v,
arrow (fa_comp u v) = Function.compose (arrow u) (arrow v).
Proof.
ir. uf fa_comp. rww Arrow.arrow_create.
Qed.

Lemma arrow_fa_id : forall x, 
arrow (fa_id x) = Function.identity x.
Proof.
ir. uf fa_id. rww Arrow.arrow_create. 
Qed.

Lemma source_fa_id : forall x,
source (fa_id x) = x.
Proof.
ir. uf fa_id. rww Arrow.source_create. 
Qed.

Lemma target_fa_id : forall x,
target (fa_id x) = x.
Proof.
ir. uf fa_id. rww Arrow.target_create. 
Qed.

Lemma inc_fas_fa_id : forall x,
inc (fa_id x) (function_arrow_set x x).
Proof.
ir. rw inc_function_arrow_set. dj.  
uf fa_id. rww Arrow.create_like. 
rww source_fa_id. rww target_fa_id. 
rw arrow_fa_id. 
ap Function.identity_axioms. 
rw arrow_fa_id. rww Function.identity_domain. 
rw arrow_fa_id. 
uhg; ir. 
util (range_ex (f:= Function.identity x) (y:= x0)).
ap Function.identity_axioms. am. 
nin H5. ee. ufi Function.identity H6. 
rwi create_V_rewrite H6. wrr H6. 
rwi Function.identity_domain H5. am. 
rwi Function.identity_domain H5. am. 
uhg; ee; am. 
Qed.

Lemma inc_fas_fa_comp : forall a b u v,
inc u (function_arrow_set (source u) (target u)) ->
inc v (function_arrow_set (source v) (target v)) ->
source u = target v ->
a = source v -> b = target u -> 
inc (fa_comp u v) (function_arrow_set a b).
Proof.
ir. 
rw H2; rw H3. clear H2; clear H3. 
rwi inc_function_arrow_set H. 
rwi inc_function_arrow_set H0. ee. 
assert (Map.axioms (source v) (target u) (arrow (fa_comp u v))).
rw arrow_fa_comp. 
apply  Map.compose_axioms with (source u). 
am. rww H1. 
rw inc_function_arrow_set. ee. 
uf fa_comp. rww Arrow.create_like. 
rww source_fa_comp. rww target_fa_comp. 
uh H14; ee; am. uh H14; ee; am. uh H14; ee; am. 
am. 
Qed. 

Lemma fa_extensionality : forall u v,
inc u (function_arrow_set (source u) (target u)) ->
inc v (function_arrow_set (source v) (target v)) ->
source u = source v -> target u = target v ->
(forall x, inc x (source u) -> 
V x (arrow u) = V x (arrow v)) -> u = v.
Proof.
ir. 
rwi inc_function_arrow_set H;
rwi inc_function_arrow_set H0; ee. 
uh H; uh H0. rw H. rw H0.
rw H1. rw H2. ap uneq. 
ap function_extensionality. am. 
am. ir. ufi defined H16. ee. 
uhg; ee. am. rwi H13 H17. rw H7. wrr H1. 
ir. ufi defined H16. ee. 
uhg; ee. am. rwi H7 H17. rw H13. rww H1. 
ir. ap H3. uh H16; ee. wrr H13. 
Qed.

Lemma map_V_inc : forall f x b,
(exists a, (Map.axioms a b f & inc x a)) ->
inc (V x f) b.
Proof.
ir. nin H. ee. uh H; ee. ap H2. 
ap range_inc. am. 
sh x. ee. rww H1. tv. 
Qed.

Lemma V_fa_comp : forall u v x,
inc u (function_arrow_set (source u) (target u)) ->
inc v (function_arrow_set (source v) (target v)) ->
source u = target v -> 
inc x (source v) -> 
V x (arrow (fa_comp u v)) = V (V x (arrow v)) (arrow u).
Proof.
ir. 
rw arrow_fa_comp. 
rw compose_ev. tv. 
assert (inc (fa_comp u v) (function_arrow_set (source v) (target u))).
ap inc_fas_fa_comp. am. am. am. tv. tv. 
rwi inc_function_arrow_set H3. ee. 
wr arrow_fa_comp. rw H7. am.  
Qed.

Lemma V_fa_id : forall x y, 
inc x y -> 
V x (arrow (fa_id y)) = x.
Proof.
ir. rw arrow_fa_id. 
uf Function.identity. 
rw create_V_rewrite. tv. am. 
Qed. 

Lemma function_cat_property : forall z,
From_Arrows.property z function_arrow_set fa_comp fa_id. 
Proof.
ir. uhg; ee; ir. 
rwi inc_function_arrow_set H. ee; am. 
rwi inc_function_arrow_set H. ee; am. 
rwi inc_function_arrow_set H. ee; am. 

rwi inc_function_arrow_set H2. 
rwi inc_function_arrow_set H3. 
ee. 
rw inc_function_arrow_set. ee. 
uf fa_comp. rww Arrow.create_like. 
rww source_fa_comp. rww target_fa_comp. 
rw arrow_fa_comp. 
ap Function.compose_axioms. 
assert (Map.axioms a c (arrow (fa_comp u v))).
rw arrow_fa_comp. 
apply Map.compose_axioms with b. am. am. 
uh H16; ee. am. 
assert (Map.axioms a c (arrow (fa_comp u v))).
rw arrow_fa_comp. 
apply Map.compose_axioms with b. am. am. 
uh H16; ee. am. 
rw arrow_fa_comp. 
apply Map.compose_axioms with b. am. am. 

assert (Map.axioms a a (arrow (fa_id a))). 
rw arrow_fa_id. 
ap Map.identity_axioms. 
rw inc_function_arrow_set. ee. uf fa_id.
rww Arrow.create_like. 
rww source_fa_id. 
rww target_fa_id. uh H0; ee. am. uh H0; ee; am. 
uh H0; ee; am. am. 

cp H1. rwi inc_function_arrow_set H2; ee. 
ap fa_extensionality. 
ap inc_fas_fa_comp. rw H3; rww H4. 
rw source_fa_id. rw target_fa_id. 
ap inc_fas_fa_id. rww target_fa_id. 
rww source_fa_comp. rww target_fa_comp.
rw H3; rww H4. 
rw source_fa_comp. rww source_fa_id. sy; am. 
rww target_fa_comp. 

assert (inc (fa_comp u (fa_id a))
(function_arrow_set (source u) (target u))).
ap inc_fas_fa_comp. 
rw H3; rww H4. 
rw source_fa_id. rw target_fa_id. ap inc_fas_fa_id.
rww target_fa_id. rww source_fa_id. tv. 
cp H9. 
rwi inc_function_arrow_set H10; ee.


ir. rw arrow_fa_comp. 
rw arrow_fa_id. 
rw compose_ev. 
uf Function.identity. 
rw create_V_rewrite. tv. 
rwi source_fa_comp H17. rwi source_fa_id H17. 
am. 
rwi source_fa_comp H17. rwi source_fa_id H17. 
rwi arrow_fa_comp H14. 
rwi arrow_fa_id H14. rw H14. rww H3. 

cp H1. rwi inc_function_arrow_set H2. 
ee. 
assert (inc (fa_comp (fa_id b) u)
(function_arrow_set (source u) (target u))).
ap inc_fas_fa_comp. 
rw source_fa_id. rw target_fa_id. 
ap inc_fas_fa_id. 
rw H3; rww H4. 
rw source_fa_id. sy; am. tv. rw target_fa_id. am. 
cp H9. 
rwi inc_function_arrow_set H10; ee.
ap fa_extensionality. 
rw source_fa_comp. rw target_fa_comp. 
rw target_fa_id. 
ap inc_fas_fa_comp. 
rw source_fa_id. rw target_fa_id. ap inc_fas_fa_id. 
rw H3; rww H4. rww source_fa_id. sy; am. 
tv. sy; rww target_fa_id. 
rw H3; rww H4. 
rww source_fa_comp. 
rw target_fa_comp. rw target_fa_id. sy; am. 

ir. rw arrow_fa_comp. 
rw arrow_fa_id. 
rw compose_ev. uf Function.identity. 
rw create_V_rewrite. tv. 
rwi source_fa_comp H17. 
wr H4. 
ap map_V_inc. sh a. ee. rww H4. wrr H3. 
wr arrow_fa_id. wr arrow_fa_comp. rw H14. 
rwi source_fa_comp H17. am. 

cp H3; cp H4; cp H5. 
rwi inc_function_arrow_set H6.
rwi inc_function_arrow_set H7.
rwi inc_function_arrow_set H8.
ee. 
wri H21 H3; wri H22 H3. 
wri H15 H4; wri H16 H4. 
wri H9 H5; wri H10 H5. 
assert (source u = target v). 
rw H21; rww H16. 
assert (source v = target w).
rw H15; rww H10. 


assert (inc (fa_comp v w) (function_arrow_set a c)).
app inc_fas_fa_comp. sy; am. sy; am. 

assert (inc (fa_comp u v) (function_arrow_set b d)).
app inc_fas_fa_comp. sy; am. sy; am. 

ap fa_extensionality. 
ap inc_fas_fa_comp. am. 
app inc_fas_fa_comp. 
rww source_fa_comp. rww target_fa_comp. rww target_fa_comp. 
rw source_fa_comp. tv. 
rw target_fa_comp. tv. 
ap inc_fas_fa_comp. 
ap inc_fas_fa_comp. 
am. am. am. rww source_fa_comp. 
rww target_fa_comp. am. rww source_fa_comp. 
rww source_fa_comp. rww target_fa_comp. 
rw source_fa_comp. rw source_fa_comp. 
rw source_fa_comp. tv. 
rw target_fa_comp. 
rw target_fa_comp. 
rw target_fa_comp. tv. 

ir. 
rw V_fa_comp. rw V_fa_comp. rw V_fa_comp. rw V_fa_comp. 
tv. am. am. am. uh H14; ee. rw H15. 
ap H33. ap range_inc. 
am. sh x. ee. 
rwi source_fa_comp H31. rwi source_fa_comp H31. rw H12. 
wrr H9. tv. 
rw source_fa_comp. rw target_fa_comp. 
rw H15. rww H22. 
am. rww source_fa_comp. rwi source_fa_comp H31. 
rwi source_fa_comp H31. am. 
am. am. am. 
rwi source_fa_comp H31. 
rwi source_fa_comp H31. am. 
am. 
rw source_fa_comp. rw target_fa_comp. 
rw H9; rww H16. rww target_fa_comp. 
rwi source_fa_comp H31. am. 
Qed.


Definition function_cat z := 
From_Arrows.from_arrows z function_arrow_set fa_comp fa_id.

Lemma function_cat_axioms : forall z,
Category.axioms (function_cat z).
Proof.
ir. uf function_cat. 
ap From_Arrows.from_arrows_axioms. 
ap function_cat_property. 
Qed.

Lemma ob_function_cat : forall z x,
ob (function_cat z) x = inc x z.
Proof.
ir. uf function_cat. 
rww ob_from_arrows. 
ap function_cat_property. 
Qed.

Lemma mor_function_cat1 : forall z u,
mor (function_cat z) u =
(Arrow.like u &
inc (source u) z &
inc (target u) z &
inc u (function_arrow_set (source u) (target u))).
Proof.
ir. ap iff_eq. ir. ufi function_cat H.
rwi mor_from_arrows H. 
ee. rwi inc_function_arrow_set H1. ee; am. 
rwi ob_from_arrows H. am. 
ap function_cat_property. 
 rwi ob_from_arrows H0. am. 
ap function_cat_property. am. 
ap function_cat_property. 
ir. ee. 
uf function_cat. 
rw mor_from_arrows. 
ee. rw ob_from_arrows. 
am. ap function_cat_property. 
rw ob_from_arrows. 
am. ap function_cat_property. 
am. ap function_cat_property. 
Qed. 

Lemma mor_function_cat2 : forall z u,
mor (function_cat z) u = 
(Arrow.like u &
inc (source u) z &
inc (target u) z &
Map.axioms (source u) (target u) (arrow u)).
Proof.
ir. 
rw  mor_function_cat1. 
ap iff_eq; ir; xd. 
rwi inc_function_arrow_set H2; ee; am. 
rw inc_function_arrow_set. ee; try am. 
tv. tv. uh H2; ee; am. uh H2; ee; am. uh H2; ee; am. 
Qed.


Lemma mor_function_cat3 : forall z u,
mor (function_cat z) u = 
(Arrow.like u &
inc (source u) z &
inc (target u) z &
inc u (function_arrow_set (source u) (target u)) &
Map.axioms (source u) (target u) (arrow u)).
Proof.
ir. ap iff_eq; ir. 
cp H. rwi mor_function_cat1 H.
rwi mor_function_cat2 H0. xd. 
rw mor_function_cat1; xd.  
Qed.


Lemma comp_function_cat : forall z u v,
mor (function_cat z) u -> mor (function_cat z) v ->
source u = target v ->
comp (function_cat z) u v = fa_comp u v.
Proof.
ir. uf function_cat. 
rw comp_from_arrows. tv. 
app mor_is_mor. app mor_is_mor. am. 
Qed.

Lemma id_function_cat : forall z x,
inc x z -> id (function_cat z) x = fa_id x.
Proof.
ir. uf function_cat. rw id_from_arrows. tv. 
rw is_ob_from_arrows. am. 
Qed.

Lemma inc_V_arrow : forall u a x,
(exists z, mor (function_cat z) u) -> 
inc x (source u) -> a = target u ->
inc (V x (arrow u)) a.
Proof.
ir. nin H. rwi mor_function_cat3 H; ee. 
ap map_V_inc. sh (source u). ee; try am. 
rww H1. 
Qed.

Lemma inc_V_arrow2 : forall u a x,
inc u (function_arrow_set (source u) (target u)) ->
inc x (source u) -> a = target u ->
inc (V x (arrow u)) a.
Proof.
ir. 
ap map_V_inc. sh (source u). 
ee; try am. 
rwi inc_function_arrow_set H. 
rw H1; ee; am. 
Qed. 

Lemma fa_comp_assoc : forall u v w,
inc u (function_arrow_set (source u) (target u)) ->
inc v (function_arrow_set (source v) (target v)) ->
inc w (function_arrow_set (source w) (target w)) ->
source u = target v -> source v = target w ->
fa_comp (fa_comp u v) w = fa_comp u (fa_comp v w).
Proof.
ir. 
ap fa_extensionality. 
ap inc_fas_fa_comp. 
ap inc_fas_fa_comp. am. am. 
am. rww source_fa_comp. rww target_fa_comp. 
am. rww source_fa_comp. rww source_fa_comp. 
rww target_fa_comp. 
ap inc_fas_fa_comp. am. 
ap inc_fas_fa_comp.
am. am. am. rw source_fa_comp. tv. 
rww target_fa_comp. rww target_fa_comp. 

rww source_fa_comp. rww target_fa_comp. 
rww source_fa_comp. rww source_fa_comp. 
rww source_fa_comp. rw target_fa_comp.
rww target_fa_comp. rww target_fa_comp. 

ir. 
rw V_fa_comp. rw V_fa_comp. 
rw V_fa_comp. rw V_fa_comp. tv. 
am. am. am. rwi source_fa_comp H4. am. 
am. 
ap inc_fas_fa_comp.
am. am. am. rww source_fa_comp. rww target_fa_comp. 
rww target_fa_comp. rwi source_fa_comp H4. 
rww source_fa_comp. 
am. am. am. rwi source_fa_comp H4. 
ap inc_V_arrow2.   
am. am. am. 
ap inc_fas_fa_comp. 
am. am. am. 
rww source_fa_comp. rww target_fa_comp.
am. rww source_fa_comp. rwi source_fa_comp H4. 
am. 
Qed.

Lemma left_fa_id : forall u x,
inc u (function_arrow_set (source u) (target u)) ->
x = target u -> 
fa_comp (fa_id x) u = u.
Proof.
ir. 
cp H. rwi inc_function_arrow_set H1. 
ee. 
ap fa_extensionality. 
ap inc_fas_fa_comp. 
rw source_fa_id. rw target_fa_id. 
ap inc_fas_fa_id. 
am. rww source_fa_id. 
rww source_fa_comp. rww target_fa_comp. 
am. rww source_fa_comp. rww target_fa_comp.
rww target_fa_id. 

ir. rw V_fa_comp. 
rw V_fa_id. tv. 
ap inc_V_arrow2. 
am. rwi source_fa_comp H8. am. am. 
rw source_fa_id; rw target_fa_id. 
ap inc_fas_fa_id. 
am. rww source_fa_id. rwi source_fa_comp H8. 
am. 
Qed.

Lemma right_fa_id : forall u x,
inc u (function_arrow_set (source u) (target u)) ->
x = source u -> 
fa_comp u (fa_id x) = u.
Proof.
ir. 
cp H. rwi inc_function_arrow_set H1. 
ee. 
ap fa_extensionality. 
ap inc_fas_fa_comp. 
am. 
rw source_fa_id. rw target_fa_id. 
ap inc_fas_fa_id. 
rww target_fa_id. sy; am. 
rww source_fa_comp. rww target_fa_comp. 
am. rww source_fa_comp. rww source_fa_id. 

rww target_fa_comp. 

ir. rw V_fa_comp. 
rw V_fa_id. tv. 
rwi source_fa_comp H8. rwi source_fa_id H8.
am. am. rw source_fa_id; rw target_fa_id. 
ap inc_fas_fa_id. 
rww target_fa_id. sy; am. 
rwi source_fa_comp H8. am.
Qed.

Definition fa_create a b f :=
Arrow.create a b (Function.create a f).

Lemma source_fa_create : forall a b f,
source (fa_create a b f) = a.
Proof.
ir. uf fa_create. rww Arrow.source_create. 
Qed. 

Lemma target_fa_create : forall a b f,
target (fa_create a b f) = b.
Proof.
ir. uf fa_create. rww Arrow.target_create. 
Qed. 

Lemma arrow_fa_create : forall a b f,
arrow (fa_create a b f) = Function.create a f.
Proof.
ir. uf fa_create. rww Arrow.arrow_create. 
Qed.

Lemma V_arrow_fa_create : forall a b f x,
inc x a -> V x (arrow (fa_create a b f)) = f x.
Proof.
ir. rw arrow_fa_create. 
rw create_V_rewrite. tv. am.
Qed. 

Lemma inc_fa_create_fas : forall a b f,
Transformation.axioms a b f ->
inc (fa_create a b f) (function_arrow_set a b).
Proof.
ir. 
rw inc_function_arrow_set. 
dj. 
uf fa_create. rww Arrow.create_like. 
rww source_fa_create. 
rww target_fa_create. 
rw arrow_fa_create. 
ap Function.create_axioms. 
rw arrow_fa_create. 
rww Function.create_domain. 
uhg; ir. rwi range_inc_rw H5. nin H5.
ee. rwi arrow_fa_create H5. 
rwi Function.create_domain H5. 
uh H. 
rwi arrow_fa_create H6. 
rwi create_V_rewrite H6. 
rw H6. ap H. am. am. 
rw arrow_fa_create. 
ap Function.create_axioms. 
uhg; ee; am. 
Qed.

Lemma eq_fa_create1 : forall a b f u,
inc u (function_arrow_set a b)  ->
(forall x, inc x a -> f x = V x (arrow u)) ->
u = fa_create a b f.
Proof.
ir. 
cp H. rwi inc_function_arrow_set H1. ee. 
ap fa_extensionality.
rw H2; rww H3. 
rw source_fa_create. rw target_fa_create. 
ap inc_fa_create_fas. uh H7; ee. 
uhg. ir. rw H0. ap H6. 
ap range_inc. am. sh x. 
ee. rww H5. tv. am. 
rww source_fa_create. rww target_fa_create. 

ir. rw arrow_fa_create. 
rw create_V_rewrite. sy; ap H0. wrr H2. wrr H2.   
Qed.

Lemma mor_function_cat_fa_create : forall z a b f,
inc a z -> inc b z -> 
(forall x, inc x a -> inc (f x) b) -> 
mor (function_cat z) (fa_create a b f).
Proof.
ir. rw mor_function_cat1. ee.
uf fa_create; rww Arrow.create_like. 
rww source_fa_create. rww target_fa_create. 
rw source_fa_create. rw target_fa_create.
app inc_fa_create_fas. 
Qed.

Lemma eq_fa_create2 : forall a b f u,
(exists z, mor (function_cat z) u) ->
source u = a -> target u = b ->
(forall x, inc x a -> f x = V x (arrow u)) ->
u = fa_create a b f.
Proof.
ir. 
nin H. rwi mor_function_cat3 H; ee. 

ap eq_fa_create1. wr H0; wrr H1. 
am. 
Qed.

Lemma all_fa_create : forall z u,
mor (function_cat z) u -> 
u = fa_create (source u) (target u) (fun x => V x (arrow u)).
Proof.
ir. 
ap eq_fa_create2. sh z; am. 
tv. tv. tv. 
Qed.

Lemma mor_fc_extensionality : forall u v,
(exists z, (
mor (function_cat z) u & mor (function_cat z) v &
source u = source v & target u = target v &
(forall x, inc x (source u) -> V x (arrow u) = V x (arrow v))))->
u = v.
Proof.
ir. nin H. ee. 
rwi mor_function_cat3 H. 
rwi mor_function_cat3 H0; ee. 
ap fa_extensionality. am. am. 
am. am. am. 
Qed.


End Function_Cat.


Module Umorphism_Cat.
Export Function_Set.
Export Nat_Trans.

Definition umorphism_set a b :=
Image.create 
(function_set (U a) (fun x:E => (U b))) 
(fun u => Umorphism.create a b (fun x => V x u)).

Lemma inc_umorphism_set : forall a b u,
inc u (umorphism_set a b) =
(Umorphism.strong_axioms u &
source u = a &
target u = b).
Proof.
ir. ap iff_eq; ir. 
ufi umorphism_set H. 
rwi Image.inc_rw H. nin H. ee. 
wr H0. 
ap Umorphism.create_strong_axioms. uhg; ee. 
uhg. ir. 
cp (function_set_pr H). ee. ap H5. am. 
wr H0. rww Umorphism.source_create. 
wr H0. rww Umorphism.target_create. 
ee. uf umorphism_set. 
rw Image.inc_rw. sh (arrow u).
ee. uh H; ee. 
ap function_set_inc. 
uh H2; ee. wr H2. 
uf Umorphism.create. rw Arrow.arrow_create. 
ap Function.create_axioms. uh H2. wr H2. 
uf Umorphism.create. rw Arrow.arrow_create. 
rw Function.create_domain. rww H0. 

ir. change (inc (ev u y) (U b)). 
uh H. uh H; ee. uh H. wr H1. ap H. rww H0. 

uh H; ee. uh H2. 
transitivity (Umorphism.create (source u) (target u) (ev u)).
ap Umorphism.create_extens. sy; am. sy; am. 
ir. tv. am.  
Qed. 

Lemma V_arrow : forall x u, V x (arrow u) = ev u x.
Proof.
ir. reflexivity. 
Qed.

Lemma umorphism_cat_property : forall z,
From_Arrows.property z umorphism_set 
Umorphism.compose Umorphism.identity.
Proof.
ir. uhg; ee; ir. 
rwi inc_umorphism_set H; ee. am. 
rwi inc_umorphism_set H; ee. am. 
rwi inc_umorphism_set H; ee. uh H; ee. 
uh H2. wr H2. 
uf Umorphism.create. rww Arrow.create_like.
rwi inc_umorphism_set H2;
rwi inc_umorphism_set H3; ee.

rw inc_umorphism_set. ee. 
ap Umorphism.compose_strong_axioms. uhg; ee. 
 uh H2; ee; am. 
uh H3; ee; am. rw H6. rww H5. 
rw Umorphism.source_compose. am. 
rww Umorphism.target_compose. 

rw inc_umorphism_set. ee. 
ap Umorphism.identity_strong_axioms. 
rww Umorphism.source_identity. 
rww Umorphism.target_identity. 
assert (a = source u). 
rwi inc_umorphism_set H1. ee; sy; am. 
rw H2. 
rww Umorphism.right_identity. 
rwi inc_umorphism_set H1. ee; am. 
assert (b = target u). 
rwi inc_umorphism_set H1. ee; sy; am. 
rw H2. 
rww Umorphism.left_identity. 
rwi inc_umorphism_set H1. ee; am. 
rwi inc_umorphism_set H3;
rwi inc_umorphism_set H4;
rwi inc_umorphism_set H5; ee. 

rww Umorphism.associativity. 
uhg; ee. lu. lu. rw H10; rww H9. 
uhg; ee. lu. lu. rw H8; rww H7. 
Qed.

Definition umorphism_cat z :=
From_Arrows.from_arrows z umorphism_set 
Umorphism.compose Umorphism.identity.

Lemma umorphism_cat_axioms : forall z,
Category.axioms (umorphism_cat z). 
Proof.
ir. uf umorphism_cat. 
ap from_arrows_axioms. ap umorphism_cat_property. 
Qed.

Lemma ob_umorphism_cat : forall z x,
ob (umorphism_cat z) x = inc x z.
Proof.
ir. uf umorphism_cat. 
rww ob_from_arrows. 
ap umorphism_cat_property. 
Qed.

Lemma mor_umorphism_cat : forall z u,
mor (umorphism_cat z) u =
(Umorphism.strong_axioms u &
inc (source u) z & inc (target u) z).
Proof.
ir. 
cp (umorphism_cat_property z). uf umorphism_cat. 
rww mor_from_arrows. 
ap iff_eq; ir. 
ee. 
rwi inc_umorphism_set H2; ee; am. 
rwi ob_from_arrows H0. am. am. 
rwi ob_from_arrows H1; am. 
ee. 
rww ob_from_arrows. rww ob_from_arrows. 
rww inc_umorphism_set. ee; try am. tv. tv. 
Qed.

Lemma comp_umorphism_cat : forall z u v,
mor (umorphism_cat z) u -> mor (umorphism_cat z) v ->
source u = target v ->
comp (umorphism_cat z) u v = Umorphism.compose u v.
Proof.
ir. 
uf umorphism_cat. rw comp_from_arrows. tv. 
app mor_is_mor. app mor_is_mor. am. 
Qed.

Lemma id_umorphism_cat : forall z x,
inc x z -> id (umorphism_cat z) x = Umorphism.identity x.
Proof.
ir. uf umorphism_cat. rw id_from_arrows. tv. 
rw is_ob_from_arrows. am. 
Qed.



End Umorphism_Cat.


Module Empty_Cat.
Export Nat_Trans.

Definition empty_cat := Category.Notations.create emptyset emptyset
(fun u v=> u) (fun x => x) emptyset. 

Lemma is_ob_empty_cat : forall x,
is_ob empty_cat x = False.
Proof.
ir. ap iff_eq; ir.
uh H. 
ufi empty_cat H. 
rwi Notations.objects_create H. 
nin H. elim x0. elim H.  
Qed.

Lemma is_mor_empty_cat : forall x,
is_mor empty_cat x = False.
Proof.
ir. ap iff_eq; ir. 
ufi empty_cat H. 
rwi Category.is_mor_create H. 
nin H. elim x0. elim H. 
Qed.

Lemma structure_empty_cat : structure empty_cat = emptyset.
Proof.
uf empty_cat. 
rw Notations.structure_create. tv.  
Qed.

Lemma empty_cat_axioms : Category.axioms empty_cat.
Proof.
uf empty_cat. 
ap Category.create_axioms. uhg; ee. 
ir. ap iff_eq; ir. 
nin H. elim x0. uh H; ee; am. 
ir. ap iff_eq; ir. nin H. elim x. 
uh H; ee; am. 
ir. nin H. elim x. ir. nin  H. elim x. 
Qed.

Lemma ob_empty_cat : forall x,
ob empty_cat x = False.
Proof.
ir. ap iff_eq; ir. 
uh H; ee. rwi is_ob_empty_cat H0. am. 
elim H. 
Qed.

Lemma mor_empty_cat : forall x,
mor empty_cat x = False.
Proof.
ir. ap iff_eq; ir. 
uh H; ee. rwi is_mor_empty_cat H0. am. 
elim H. 
Qed.

Lemma show_empty_subcategory : forall a b,
Category.axioms a -> Category.axioms b ->
(forall x, ob a x -> False) -> 
structure a = structure b -> 
is_subcategory a b.
Proof.
ir. 
assert (forall u, mor a u -> False).
ir. apply H1 with (source u). rww  ob_source.
uhg; ee; try am. 
ir. elim (H1 _ H4). 
ir. elim (H3 _ H4). 
ir. elim (H3 _ H4). 
ir. elim (H1 _ H4). 
Qed.

Lemma eq_empty_cat : forall a,
Category.axioms a -> 
structure a = emptyset -> 
(forall x, ob a x -> False) -> 
a = empty_cat.
Proof.
ir. 
ap is_subcategory_extensionality. 
ap show_empty_subcategory. 
am. ap empty_cat_axioms. am. 
rww structure_empty_cat. 
ap show_empty_subcategory. 
ap empty_cat_axioms. am. 
ir. rwi ob_empty_cat H2. am. 
sy; rww structure_empty_cat. 
Qed.

Definition empty_functor a :=
Functor.create empty_cat a (fun u => u).

Lemma source_empty_functor : forall a,
source (empty_functor a) = empty_cat.
Proof.
ir. uf empty_functor. rww Functor.source_create. 
Qed.

Lemma target_empty_functor : forall a,
target (empty_functor a) = a.
Proof.
ir. uf empty_functor. rww Functor.target_create. 
Qed.

Lemma empty_functor_axioms : forall a,
Category.axioms a -> 
Functor.axioms (empty_functor a).
Proof.
ir. uf empty_functor. 
ap Functor.create_axioms. 
sh (fun (x:E) => x). 
uhg; ee. ap empty_cat_axioms. 
am. ir. 
rwi ob_empty_cat H0; nin H0. 
ir. rwi ob_empty_cat H0; elim H0. 
ir. rwi mor_empty_cat H0; elim H0. 
ir. rwi mor_empty_cat H0; elim H0. 
ir. rwi mor_empty_cat H0; elim H0. 
ir. rwi mor_empty_cat H0; elim H0. 
Qed. 

Lemma eq_empty_functor : forall a f,
Functor.axioms f -> source f = empty_cat ->
target f = a -> 
f = empty_functor a. 
Proof.
ir. 
ap Functor.axioms_extensionality. 
am. ap empty_functor_axioms. 
wr H1. rww category_axioms_target. 
rww source_empty_functor. rww target_empty_functor. 
ir. rwi H0 H2. rwi mor_empty_cat H2. elim H2. 
Qed.

Definition empty_nt a :=
Nat_Trans.create (empty_functor a) (empty_functor a) 
(fun (x : E) => x).

Lemma source_empty_nt : forall a,
source (empty_nt a) = empty_functor a.
Proof.
ir. uf empty_nt. rww Nat_Trans.source_create. 
Qed.

Lemma target_empty_nt : forall a,
target (empty_nt a) = empty_functor a.
Proof.
ir. uf empty_nt. rww Nat_Trans.target_create. 
Qed.

Lemma osource_empty_nt : forall a,
osource (empty_nt a) = empty_cat.
Proof.
ir. uf osource. rw source_empty_nt.
rww source_empty_functor.  
Qed.

Lemma otarget_empty_nt : forall a,
otarget (empty_nt a) = a.
Proof.
ir. uf otarget. rw target_empty_nt.
rww target_empty_functor.  
Qed.

Lemma empty_nt_axioms : forall a,
Category.axioms a ->
Nat_Trans.axioms (empty_nt a).
Proof.
ir. 
uf empty_nt. 
ap Nat_Trans.create_axioms. 
uhg; ee. app empty_functor_axioms. 
app empty_functor_axioms. 
tv. tv. 
ir. rwi source_empty_functor H0. rwi ob_empty_cat H0.
elim H0. 
ir. rwi source_empty_functor H0. rwi ob_empty_cat H0.
elim H0. 
ir. rwi source_empty_functor H0. rwi ob_empty_cat H0.
elim H0. 
ir. rwi source_empty_functor H0. rwi mor_empty_cat H0.
elim H0. 
Qed.

Lemma eq_empty_nt : forall a u,
Nat_Trans.axioms u ->
osource u = empty_cat ->
otarget u = a ->
u = empty_nt a.
Proof.
ir. 
assert (Category.axioms a).
wr H1. rww category_axioms_otarget. 
ap Nat_Trans.axioms_extensionality. 
am. 
app empty_nt_axioms. rww source_empty_nt. 
ap eq_empty_functor. rww functor_axioms_source. 
am. rww target_source. 
rw target_empty_nt. 
ap eq_empty_functor. 
rww functor_axioms_target. 
rww source_target. am. 
ir. rwi H0 H3. rwi ob_empty_cat H3. elim H3.  
Qed.



End Empty_Cat.

Module Discrete_Cat.
Export Function_Cat.

(*** discrete_cat z is the category of elements of z  
with only identity morphisms ***)

Definition is_id_fun_arrow u := 
u = fa_id (source u).


Definition discrete_cat z :=
subcategory (function_cat z) (fun x => True) 
is_id_fun_arrow.

Lemma is_id_fun_arrow_id_fc : forall z x,
inc x z -> 
is_id_fun_arrow (id (function_cat z) x).
Proof.
ir. uhg; ee. 
rw id_function_cat. 
uf fa_id. rw Arrow.source_create.  tv. am. 
Qed.

Lemma is_id_fun_arrow_rw : forall u,
is_id_fun_arrow u = 
(source u = target u & 
(forall z, inc (source u) z -> 
(u = (id (function_cat z) (source u))))).
Proof.
ir. ap iff_eq; ir. 
ee. ufi is_id_fun_arrow H. 
rw H. rw source_fa_id. rww target_fa_id.  
 

ir. uh H; ee. 
rw H. rw source_fa_id. 
rw id_function_cat. 
tv. am. 
uhg; ee. 
util (H0 (singleton (source u))). ap singleton_inc. 
rwi id_function_cat H1. am. 
ap singleton_inc. 
Qed. 

Lemma discrete_cat_property : forall z,
subcategory_property (function_cat z) (fun x => True) 
is_id_fun_arrow.
Proof.
ir. uhg; ee. 
ap function_cat_axioms. ir. 
uhg; ee. 
rw source_comp. 
cp H2; cp H3. 
rwi is_id_fun_arrow_rw H2. 
rwi is_id_fun_arrow_rw H3. 
ee. 
cp H. rwi mor_function_cat3 H8. 
ee. cp (H7 z H9). 
rw H13. 
rw left_id. 
uh H5. am. 
rww ob_function_cat. am. 
sy; am. tv. 
am. am. am. 


ir. clear H0. cp H. rwi ob_function_cat H0. 
rww id_function_cat. uhg. rww source_fa_id. 

ir. tv. 

ir. tv. 
Qed.

Lemma discrete_cat_axioms : forall z,
Category.axioms (discrete_cat z).
Proof.
ir. uf discrete_cat. 
ap subcategory_axioms. 
ap discrete_cat_property. 
Qed.


Lemma ob_discrete_cat : forall z x, 
ob (discrete_cat z) x = inc x z.
Proof.
ir. ap iff_eq; ir. 
ufi discrete_cat H. 
rwi ob_subcategory H. ee. 
rwi ob_function_cat H. am. 
ap discrete_cat_property. 
uf discrete_cat. 
rw ob_subcategory. ee; try tv. 
rww ob_function_cat. 
ap discrete_cat_property. 
Qed.

Lemma id_discrete_cat : forall z x,
inc x z -> id (discrete_cat z) x = id (function_cat z) x.
Proof.
ir. cp H. wri ob_discrete_cat H. 
uf discrete_cat. 
rw id_subcategory. tv. ap discrete_cat_property. 
rww ob_function_cat. tv. 
Qed.


Lemma mor_discrete_cat : forall z u,
mor (discrete_cat z) u = 
(inc (source u) z & is_id_fun_arrow u).
Proof.
ir. uf discrete_cat. 
rw mor_subcategory. ap iff_eq; ir. xd. 
rwi mor_function_cat3 H. ee; am. 
xd. uh H0; ee. 
assert (u = id (function_cat z) (source u)). 
rw id_function_cat. am. am. 
rw H1. ap mor_id. 
rww ob_function_cat. 
ap discrete_cat_property. 
Qed.

Lemma mor_discrete_cat3 : forall z u,
mor (discrete_cat z) u =
(inc (source u) z &
inc (target u) z &
source u = target u &
is_id_fun_arrow u &
u = id (discrete_cat z) (source u) &
u = id (function_cat z) (source u)).
Proof.
ir. rw mor_discrete_cat; ap iff_eq; ir; xd.
uh H0. rw H0. rw target_fa_id. am. 
uh H0. rw H0. 
rw source_fa_id. rww target_fa_id. 
rw id_discrete_cat. rw id_function_cat. am. 
am. am. 
rw id_function_cat. am. am. 
Qed. 


Lemma comp_discrete_cat : forall z u v,
mor (discrete_cat z) u -> mor (discrete_cat z) v ->
source u = target v -> 
comp (discrete_cat z) u v = u.
Proof.
ir. rwi mor_discrete_cat3 H;
rwi mor_discrete_cat3 H0. ee. 
rw H10. 
rw H1. rw left_id. wr H3. am. 
rw ob_discrete_cat. am. 
rw mor_discrete_cat. ee; am. 
tv. tv. 
Qed.

Lemma discrete_cat_mor_extens : forall u v,
source u = source v -> 
(exists z, (mor (discrete_cat z) u &
mor (discrete_cat z) v)) -> u = v.
Proof.
ir. nin H0. ee. 
rwi mor_discrete_cat3 H0. rwi mor_discrete_cat3 H1. 
ee. rw H10. rw H5.
rw H. reflexivity. 
Qed.

(*** functors and natural transformations on discrete_cat ***)

Definition discrete_functor z a f :=
Functor.create (discrete_cat z) a (fun u => id a (f (source u))).

Lemma source_discrete_functor : forall z a f,
source (discrete_functor z a f) = (discrete_cat z).
Proof.
ir. uf discrete_functor. 
rww Functor.source_create. 
Qed.

Lemma target_discrete_functor : forall z a f,
target (discrete_functor z a f) = a.
Proof.
ir. uf discrete_functor. 
rww Functor.target_create. 
Qed.

Lemma fmor_discrete_functor : forall z a f u,
mor (discrete_cat z) u -> fmor (discrete_functor z a f) u
= id a (f (source u)).
Proof.
ir. uf discrete_functor. 
rww fmor_create. 
Qed.

Definition discrete_functor_property z a f :=
Category.axioms a &
(forall x, inc x z -> ob a (f x)).

Lemma fob_discrete_functor : forall z a f x,
discrete_functor_property z a f ->
inc x z -> 
fob (discrete_functor z a f) x = f x.
Proof.
ir. 
uf fob. 
rw fmor_discrete_functor. 
rw source_discrete_functor. 
rw source_id. rw source_id. tv. 
rww ob_discrete_cat. 
rw source_id. uh H; ee. au. 
rww ob_discrete_cat. 
rw source_discrete_functor. 
app mor_id. rww ob_discrete_cat. 
Qed.

Lemma discrete_functor_axioms : forall z a f,
discrete_functor_property z a f ->
Functor.axioms (discrete_functor z a f).
Proof.
ir. 
uf discrete_functor. ap Functor.create_axioms.
sh (fob (discrete_functor z a f)). 
cp H. uh H0; ee. 
uhg; ee. ap discrete_cat_axioms. am. 

ir. 
cp H2. rwi ob_discrete_cat H3. 
rww fob_discrete_functor. au. 

ir. cp H2. rwi ob_discrete_cat H3. 
rww fob_discrete_functor. 
rww source_id. 

ir. cp H2. rwi mor_discrete_cat3 H3. 
ee. ap mor_id. ap H1. am. 

ir. cp H2. rwi mor_discrete_cat3 H3. ee. 
rww source_id. rww fob_discrete_functor. 
app H1. 

ir. cp H2. rwi mor_discrete_cat3 H3. ee. 
rww target_id. rww fob_discrete_functor. 
rww H5. au. 

ir. cp H2; cp H3. rwi mor_discrete_cat3 H5;
rwi mor_discrete_cat3 H6. ee. 
rw left_id. 
rww source_comp. au. app mor_id. au. 
rww target_id. rww H4. rww H8. 
au. tv.  
Qed.

Lemma eq_discrete_functor : forall z a f g,
Functor.axioms g -> 
discrete_functor_property z a f ->
source g = discrete_cat z ->
target g = a ->
(forall x, inc x z -> fob g x = f x) -> 
g = discrete_functor z a f.
Proof.
ir. 
assert (forall x, inc x z -> fmor g (id (discrete_cat z) x) 
= id a (f x)).
ir. rw fmor_id. rww H3. rww H2. am. am. 
rww ob_discrete_cat. 

ap Functor.axioms_extensionality. 
am. ap discrete_functor_axioms. am. 
rww source_discrete_functor. 
rww target_discrete_functor. 
ir. rww fmor_discrete_functor. 
rwi H1 H5. 
rwi mor_discrete_cat3 H5. ee. 
rw H9. 
rw H4. 
rw source_id. tv. rww ob_source. 
rw mor_discrete_cat; ee; am. am. 
wrr H1. 
Qed.

Lemma discrete_functor_property_fob : forall z a g,
Functor.axioms g -> source g = discrete_cat z ->
a = target g -> 
discrete_functor_property z a (fob g).
Proof.
ir. 
uhg; ee. 
uh H; ee. rww H1. ir. 
rw H1. ap ob_fob. am. 
rw H0. rw ob_discrete_cat. am. 
Qed.

Lemma all_functors_discrete : forall z g,
Functor.axioms g -> source g = discrete_cat z ->
g = discrete_functor z (target g) (fob g).
Proof.
ir. app eq_discrete_functor. 
app discrete_functor_property_fob. 
Qed.

Definition discrete_nt z a t :=
Nat_Trans.create (discrete_functor z a (fun x => source (t x)))
(discrete_functor z a (fun x => target (t x))) t.

Lemma source_discrete_nt : forall z a t,
source (discrete_nt z a t) = 
discrete_functor z a  (fun x => source (t x)).
Proof.
ir. 
uf discrete_nt. 
rw Nat_Trans.source_create. tv. 
Qed.

Lemma target_discrete_nt : forall z a t,
target (discrete_nt z a t) = 
discrete_functor z a  (fun x => target (t x)).
Proof.
ir. 
uf discrete_nt. 
rw Nat_Trans.target_create. tv. 
Qed.

Lemma osource_discrete_nt : forall z a t,
osource (discrete_nt z a t) = 
discrete_cat z.
Proof.
ir. uf osource. 
rw source_discrete_nt. 
rw source_discrete_functor. tv. 
Qed.

Lemma otarget_discrete_nt : forall z a t,
otarget (discrete_nt z a t) = a.
Proof.
ir. uf otarget. 
rw target_discrete_nt. 
rw target_discrete_functor. tv. 
Qed.

Lemma ntrans_discrete_nt : forall z a t x,
inc x z -> ntrans (discrete_nt z a t) x = (t x).
Proof.
ir. uf discrete_nt. 
rw Nat_Trans.ntrans_create. 
tv. rw source_discrete_functor. 
change (is_ob (discrete_cat z) x). 
ap ob_is_ob. rww ob_discrete_cat. 
Qed.

Definition discrete_nt_property z a t :=
Category.axioms a &
(forall x,  inc x z -> mor a (t x)).

Lemma discrete_nt_axioms : forall z a t,
discrete_nt_property z a t ->
Nat_Trans.axioms (discrete_nt z a t).
Proof.
ir. 
uh H; ee. 
uf discrete_nt. 
ap Nat_Trans.create_axioms. uhg; ee. 
ap discrete_functor_axioms. uhg; ee. 
am. ir. rw ob_source. tv. au. 
ap discrete_functor_axioms. uhg; ee. 
am. ir. rw ob_target. tv. au.
rw source_discrete_functor. 
rww source_discrete_functor. 
rw target_discrete_functor. 
rww target_discrete_functor. 
ir. rwi source_discrete_functor H1. 
rw target_discrete_functor. ap H0. 
wrr ob_discrete_cat. 
ir. rwi source_discrete_functor H1. 
rw fob_discrete_functor. tv. 
uhg; ee. am. ir. rww ob_source. ap H0. am. 
wrr ob_discrete_cat. 
ir. rwi source_discrete_functor H1. 
rw fob_discrete_functor. tv. 
uhg; ee. am. ir. rww ob_target. ap H0. am. 
wrr ob_discrete_cat. 

ir. rw target_discrete_functor. 
rwi source_discrete_functor H1. 
cp H1. rwi mor_discrete_cat3 H2. ee. 
rww fmor_discrete_functor. 
rww fmor_discrete_functor. wr H4. 
rw left_id. rw right_id. tv. 
rww ob_source. ap H0. am. 
app H0. tv. tv. 
rww ob_target. app H0. app H0. tv. tv. 
Qed.

Lemma discrete_nt_property_ntrans : forall z u,
Nat_Trans.axioms u -> osource u = discrete_cat z ->
discrete_nt_property z (otarget u) (ntrans u).
Proof.
ir. uhg; ee.
rww category_axioms_otarget. 
ir. ap mor_ntrans. am. 
rw H0. rww ob_discrete_cat. 
tv. 
Qed.

Lemma eq_discrete_nt : forall z a t u,
discrete_nt_property z a t ->
Nat_Trans.axioms u -> 
osource u = discrete_cat z ->
otarget u = a ->
(forall x, inc x z -> ntrans u x = t x) ->
u = discrete_nt z a t.
Proof.
ir. 
ap Nat_Trans.axioms_extensionality. 
am. app discrete_nt_axioms. 
rww source_discrete_nt. 
ap eq_discrete_functor. 
rww functor_axioms_source. 
uhg; ee. wr H2. rww category_axioms_otarget. 
ir. uh H; ee. rww ob_source. au. 
am. rww target_source. 
ir. wrr H3. 
rww source_ntrans. rw H1. 
rww ob_discrete_cat. 
rw target_discrete_nt. 
ap eq_discrete_functor. 
rww functor_axioms_target. 
uhg; ee. wr H2. rww category_axioms_otarget. 
ir. uh H; ee. rww ob_target. au. 
 rww source_target. am.  
ir. wrr H3. 
rww target_ntrans. rw H1. 
rww ob_discrete_cat. 

ir. rw ntrans_discrete_nt. ap H3. 
rwi H1 H4. rwi ob_discrete_cat H4; am. 
rwi H1 H4. rwi ob_discrete_cat H4; am. 
Qed.

Lemma all_nt_discrete : forall z u,
Nat_Trans.axioms u -> osource u = discrete_cat z ->
u = discrete_nt z (otarget u) (ntrans u).
Proof.
ir. ap eq_discrete_nt. 
ap discrete_nt_property_ntrans. am. am. am. am. 
tv. ir. tv. 
Qed.


End Discrete_Cat.

Module Inclusion_Cat.
Export Function_Cat.

(*** inclusion_cat z is the category of elements of z  
with only inclusions as morphisms ***)

Definition fa_inclusion a b := 
Arrow.create a b (Function.create a (fun (x:E) => x)).

Lemma source_fa_inclusion : forall a b,
source (fa_inclusion a b) = a.
Proof.
ir. uf fa_inclusion.
rww Arrow.source_create. 
Qed.

Lemma target_fa_inclusion : forall a b,
target (fa_inclusion a b) = b.
Proof.
ir. uf fa_inclusion.
rww Arrow.target_create. 
Qed.

Lemma arrow_fa_inclusion : forall a b,
arrow (fa_inclusion a b) = (Function.create a (fun (x:E) => x)).
Proof.
ir. uf fa_inclusion.
rww Arrow.arrow_create. 
Qed.


Lemma inc_fa_inclusion_fas : forall a b, sub a b ->
inc (fa_inclusion a b) (function_arrow_set a b).
Proof.
ir. 
assert (Map.axioms a b (arrow (fa_inclusion a b))).
uhg; ee. 
rw arrow_fa_inclusion. 
ap Function.create_axioms. 
rw arrow_fa_inclusion. 
rww Function.create_domain. 
rw arrow_fa_inclusion. 
uhg; ir. rwi range_inc_rw H0. 
nin H0. ee. rwi Function.create_domain H0. 
rwi create_V_rewrite H1. rw H1. ap H. am. 
am. ap Function.create_axioms. 

cp H0. uh H1; ee. 
rw inc_function_arrow_set; xd. 
uf fa_inclusion. 
rww Arrow.create_like. rww source_fa_inclusion. 
rww target_fa_inclusion. 
Qed.

Definition is_fa_inclusion u :=
(sub (source u) (target u) & 
u = fa_inclusion (source u) (target u)).

Lemma is_fa_inclusion_fa_id : forall x, 
is_fa_inclusion (fa_id x).
Proof.
ir. uhg; ee. 
rw source_fa_id. rw target_fa_id. 
uhg; ir; am. 
rw source_fa_id. rw target_fa_id. tv. 
Qed.

Lemma fa_inclusion_fa_id : forall x y,
x = y -> fa_inclusion x y = fa_id x.
Proof.
ir. rw H. tv. 
Qed.

Lemma fa_id_fa_inclusion : forall x,
fa_id x = fa_inclusion x x.
Proof.
ir. tv. 
Qed.

Lemma is_fa_inclusion_fa_comp : forall u v,
is_fa_inclusion u -> is_fa_inclusion v -> 
source u = target v -> is_fa_inclusion (fa_comp u v).
Proof.
ir. 
assert (inc (fa_comp u v) (function_arrow_set (source v) (target u))).
ap inc_fas_fa_comp. 
uh H. ee. rw H2. rw source_fa_inclusion. 
rw target_fa_inclusion. 
ap inc_fa_inclusion_fas. am. 
uh H0. ee. rw H2.
rw source_fa_inclusion. 
rw target_fa_inclusion. 
ap inc_fa_inclusion_fas. am. 
am. tv. tv. 

cp H2. rwi inc_function_arrow_set H3. ee. 
uhg; ee. rw source_fa_comp. rw target_fa_comp. 
uh H; uh H0; ee. 
apply sub_trans with (source u). 
rww H1. am. 

rw source_fa_comp. rw target_fa_comp. 

ap fa_extensionality. 
ap inc_fas_fa_comp. 
uh H; ee. rw H10.
rw source_fa_inclusion; rw target_fa_inclusion. 
ap inc_fa_inclusion_fas. am. 
uh H0; ee. rw H10.
rw source_fa_inclusion; rw target_fa_inclusion. 
ap inc_fa_inclusion_fas. am. am. 
rww source_fa_comp. rww target_fa_comp. 

rw source_fa_inclusion. rw target_fa_inclusion. 
ap inc_fa_inclusion_fas. 
apply sub_trans with (source u). 
rww H1. uh H0; ee; am. uh H; ee; am. 
rw source_fa_comp. rww source_fa_inclusion.
rw target_fa_comp. rww target_fa_inclusion.


ir. rw V_fa_comp. 
rw arrow_fa_inclusion. rw create_V_rewrite. 
uh H; uh H0; ee. rw H12; rw H11. 
rw arrow_fa_inclusion. rw arrow_fa_inclusion.
rw create_V_rewrite. 
rw create_V_rewrite. tv. rwi source_fa_comp H10. 
tv. 
rw create_V_rewrite. rwi source_fa_comp H10. rw H1. 
ap H0; am. rwi source_fa_comp H10. am. 
rwi source_fa_comp H10. am. 

uh H; ee. rw H11.
rw source_fa_inclusion; rw target_fa_inclusion. 
ap inc_fa_inclusion_fas. am. 
uh H0; ee. rw H11.
rw source_fa_inclusion; rw target_fa_inclusion. 
ap inc_fa_inclusion_fas. am. 
am. rwi source_fa_comp H10. am. 
Qed.

Lemma inclusion_cat_property : forall z,
subcategory_property (function_cat z) (fun x => True)
is_fa_inclusion.
Proof.
ir. 
uhg; ee. ap function_cat_axioms. 
ir. rw comp_function_cat. ap is_fa_inclusion_fa_comp.
am. am. am. am. am. am. 

ir. rw id_function_cat. ap  is_fa_inclusion_fa_id. 
rwi ob_function_cat H; am. 
ir; tv. ir; tv. 
Qed.

Definition inclusion_cat z :=
subcategory (function_cat z) (fun x => True)
is_fa_inclusion.

Lemma inclusion_cat_axioms : forall z,
Category.axioms (inclusion_cat z).
Proof.
ir. uf inclusion_cat. 
ap subcategory_axioms. ap inclusion_cat_property. 
Qed.

Lemma ob_inclusion_cat : forall z x,
ob (inclusion_cat z) x = inc x z.
Proof.
ir. uf inclusion_cat. 
rw ob_subcategory. ap iff_eq; ir; ee.
rwi ob_function_cat H; am. rww ob_function_cat.
tv. ap inclusion_cat_property. 
Qed.

Lemma mor_inclusion_cat : forall z u,
mor (inclusion_cat z) u = 
(inc (source u) z & inc (target u) z &
is_fa_inclusion u).
Proof.
ir. uf inclusion_cat. 
rw mor_subcategory. ap iff_eq; ir; xd. 
wr ob_function_cat. rww ob_source. 
wr ob_function_cat. rww ob_target. 
uh H1; ee. rw H2. 
rw mor_function_cat1. ee.
uf fa_inclusion. rww Arrow.create_like. 
rw source_fa_inclusion. am. rww target_fa_inclusion.
rw source_fa_inclusion. rw target_fa_inclusion. 
ap inc_fa_inclusion_fas. am. ap inclusion_cat_property. 
Qed.

Lemma id_inclusion_cat : forall z x, inc x z ->
id (inclusion_cat z) x = fa_id x.
Proof.
ir. uf inclusion_cat. rw id_subcategory. 
rww id_function_cat. 
ap inclusion_cat_property. rww ob_function_cat. tv. 
Qed.

Lemma inclusion_cat_mor_extens : forall u v,
source u = source v -> target u = target v ->
(exists z, (mor (inclusion_cat z) u & mor (inclusion_cat z) v))
-> u = v.
Proof.
ir. nin H1. ee. rwi mor_inclusion_cat H1. 
rwi mor_inclusion_cat H2. ee. 
uh H6; uh H4; ee. rw H8. rw H7. 
rw H; rw H0. reflexivity. 
Qed.

Lemma inclusion_cat_sub_trans : forall u v,
source u = target v ->
(exists z, (mor (inclusion_cat z) u & mor (inclusion_cat z) v))
-> sub (source v) (target u).
Proof.
ir. nin H0; ee. 
rwi mor_inclusion_cat H0. rwi mor_inclusion_cat H1.
ee. uh H5; uh H3; ee. apply sub_trans with (source u).
rww H. am. 
Qed.


Lemma comp_inclusion_cat : forall z u v,
mor (inclusion_cat z) u -> mor (inclusion_cat z) v ->
source u = target v -> 
comp (inclusion_cat z) u v = fa_inclusion (source v) (target u).
Proof.
ir. 
ap inclusion_cat_mor_extens. 
rww source_comp. 
rww source_fa_inclusion. 
rww target_comp. rww target_fa_inclusion. 
sh z. ee. 
rww mor_comp. 
rw mor_inclusion_cat. ee. 
rw source_fa_inclusion. 
wr ob_inclusion_cat. rww ob_source. 
rw target_fa_inclusion. wr ob_inclusion_cat. 
rww ob_target. 
uhg. ee. rw source_fa_inclusion. rw target_fa_inclusion.
app inclusion_cat_sub_trans. sh z; ee; try am.
rw source_fa_inclusion. rww target_fa_inclusion. 
Qed.


End Inclusion_Cat.


Module Small_Integer_Sets.
Export Function_Cat.


Lemma zero_emptyset : R 0 = emptyset.
Proof.
rww nat_zero_emptyset. 
Qed.

Lemma nat_succ_tack_on : forall (i:nat),
R (S i) = tack_on (R i) (R i).
Proof.
ir. ap extensionality; uhg; ir. 
rwi nat_realization_S H. 
rw tack_on_inc. am. 
rw nat_realization_S. 
rwi tack_on_inc H. am. 
Qed.

(*** later should say that nats are ordinals; we probably
want to reorganize this ********************************)

Lemma inc_one : forall x,
inc x (R 1) = (x = R 0).
Proof.
ir. 
rw nat_succ_tack_on. 
ap iff_eq; ir. rwi tack_on_inc H. nin H. 
rwi zero_emptyset H. nin H. elim x0. am. 
rw tack_on_inc. ap or_intror; am. 
Qed.

Lemma two_tack_on : R 2 = tack_on (R 1) (R 1).
Proof.
ap nat_succ_tack_on. 
Qed. 

Lemma inc_two : forall x,
inc x (R 2) = ((x = R 0) \/ (x = R 1)).
Proof.
ir. 
rw two_tack_on. 
ap iff_eq; ir. rwi tack_on_inc H. nin H. 
rwi inc_one H. ap or_introl; am. 
ap or_intror; am. 
rw tack_on_inc. nin H. ap or_introl.
rw inc_one. am. ap or_intror; am. 
Qed. 

Lemma sub_zero_any : forall x, sub (R 0) x.
Proof.
ir. uhg; ir. rwi zero_emptyset H. nin H. 
elim x1. 
Qed.

Lemma inc_zero_one : inc (R 0) (R 1).
Proof.
rw inc_one. tv. 
Qed.

Lemma inc_zero_two : inc (R 0) (R 2).
Proof.
rw inc_two. ap or_introl; tv. 
Qed.

Lemma inc_one_two : inc (R 1) (R 2).
Proof.
rw inc_two. ap or_intror; tv. 
Qed.

Lemma sub_one_two : sub (R 1) (R 2).
Proof.
uhg; ir. rwi inc_one H. rw inc_two.
ap or_introl; am. 
Qed.

Definition arrow_zero_to x := 
fa_create (R 0) x (fun (x:E) => x).

Lemma source_arrow_zero_to : forall x,
source (arrow_zero_to x) = (R 0).
Proof.
ir. uf arrow_zero_to.
rww source_fa_create.
Qed. 

Lemma target_arrow_zero_to : forall x,
target (arrow_zero_to x) = x.
Proof.
ir. uf arrow_zero_to.
rww target_fa_create.
Qed.

Lemma mor_fc_arrow_zero_to : forall z x,
inc (R 0) z -> inc x z ->
mor (function_cat z) (arrow_zero_to x).
Proof.
ir. rw mor_function_cat1. 
ee. uf arrow_zero_to. uf fa_create.
rww Arrow.create_like. 
rww source_arrow_zero_to. rww target_arrow_zero_to.
uf arrow_zero_to. 
rw source_fa_create. 
rw target_fa_create. 
ap inc_fa_create_fas. 
uhg. ir. rwi zero_emptyset H1. 
nin H1. nin x1. 
Qed.

Lemma all_arrow_zero_to : forall z u,
mor (function_cat z) u ->
source u = (R 0) ->
u = arrow_zero_to (target u).
Proof.
ir. 
ap mor_fc_extensionality. 
sh z. ee; try am. 
ap mor_fc_arrow_zero_to. 
wr H0. wr ob_function_cat. rww ob_source. 
wr ob_function_cat. rww ob_target. 
rww source_arrow_zero_to. rww target_arrow_zero_to.
ir. rwi H0 H1. rwi zero_emptyset H1. 
nin H1. nin x0. 
Qed.



Definition arrow_one_at x  y :=
fa_create (R 1) y (fun (t:E) => x).

Lemma source_arrow_one_at : forall x y,
source (arrow_one_at x y) = R 1.
Proof.
ir. uf arrow_one_at. 
rww source_fa_create. 
Qed.

Lemma target_arrow_one_at : forall x y,
target (arrow_one_at x y) = y.
Proof.
ir. uf arrow_one_at. 
rww target_fa_create. 
Qed.

Lemma mor_arrow_one_at : forall x y z,
inc (R 1) z -> inc y z -> inc x y ->
mor (function_cat z) (arrow_one_at x y).
Proof.
ir. 
uf arrow_one_at. 
ap mor_function_cat_fa_create. am. 
am. ir. am. 
Qed.


Lemma V_arrow_arrow_one_at : forall x y a,
inc y a -> inc x (R 1) -> 
V x (arrow (arrow_one_at y a)) = y.
Proof.
ir. uf arrow_one_at. 
rw V_arrow_fa_create. tv. am. 
Qed. 

Lemma all_arrow_one_at : forall z u,
mor (function_cat z) u ->
source u = (R 1) -> 
(exists x, (inc x (target u) & u = arrow_one_at x (target u))).
Proof.
ir. 
assert (inc (V (R 0) (arrow u)) (target u)).
ap inc_V_arrow. sh z; am. rw H0. ap inc_zero_one.
tv. 

assert (inc (R 1) z).
wr H0. 
wr ob_function_cat. rww ob_source. 

assert (inc (target u) z). 
wr ob_function_cat. rww ob_target. 
sh (V (R 0) (arrow u)). ee. am. 

ap mor_fc_extensionality. 
sh z; ee. am. 
ap mor_arrow_one_at. am. am. am. 
rww source_arrow_one_at. 
rww target_arrow_one_at. 

ir. rw V_arrow_arrow_one_at. 
rwi H0 H4. rwi inc_one H4. rww H4. 
ap inc_V_arrow. sh z; am. rw H0. ap inc_zero_one.
tv. wrr H0. 
Qed.

End Small_Integer_Sets.
Export Small_Integer_Sets.


Module Ordinals_Cat. 
Export Function_Cat.
Export Ordinal. 

(*** ordinals_cat a is the category of elements of a which
are ordinals, with morphisms being the order-preserving maps ***)

(*** not done yet (or even started...) ***********************)

End Ordinals_Cat.




(***** the following provides a good example of how not
to proceed: trying to define things concretely gives a big mess;
this suggests that it is better to use Coq's inductive objects
which we subsequently try in the next file *****************

Module Twoarrow_Cat. 
Export Function_Cat.

Definition twoarrow_objects := doubleton (R 1) (R 2).

Lemma inc_doubleton : forall x y z,
inc x (doubleton y z) = ((x = y) \/ (x = z)).
Proof.
ir. ap iff_eq; ir. 
cp (doubleton_or H). am. 
nin H. rw H; ap doubleton_first. 
rw H; ap doubleton_second. 
Qed.

Lemma inc_twoarrow_objects : forall x,
inc x twoarrow_objects = ((x = R 1) \/ (x = R 2)).
Proof.
ir. uf twoarrow_objects. rw inc_doubleton. 
tv. 
Qed.

Definition twoarrow_morp u :=
(u = fa_id (R 1)) \/ 
(u = fa_id (R 2)) \/
(u = arrow_one_at (R 0) (R 2)) \/
(u = arrow_one_at (R 1) (R 2)).

Lemma twoarrow_morp_rw : forall u,
twoarrow_morp u =
(mor (function_cat twoarrow_objects) u &
(source u = R 2 -> u = (fa_id (R 2)))).
Proof.
ir. ap iff_eq; ir. 
ee. 
uh H. nin H. 
assert (fa_id (R 1) = id (function_cat twoarrow_objects) (R 1)).
rww id_function_cat. 
rw inc_twoarrow_objects. ap or_introl; tv. 
rwi H0 H. rw H. ap mor_id. 
rw ob_function_cat. rw inc_twoarrow_objects. 
ap or_introl; tv. 

nin H. assert (fa_id (R 2) = id (function_cat twoarrow_objects) 
(R 2)).
rww id_function_cat. 
rw inc_twoarrow_objects. ap or_intror; tv. 
rwi H0 H. rw H. ap mor_id. 
rw ob_function_cat. rw inc_twoarrow_objects. 
ap or_intror; tv. 

nin H. rw H. 
ap mor_arrow_one_at. 
rw inc_twoarrow_objects. ap or_introl; tv. 
rw inc_twoarrow_objects. ap or_intror; tv. 
ap inc_zero_two. 

rw H. ap mor_arrow_one_at. 
rw inc_twoarrow_objects. ap or_introl; tv. 
rw inc_twoarrow_objects. ap or_intror; tv. 
ap inc_one_two. 

ir. nin H. rwi H H0. rwi source_fa_id H0. 
cp (R_inj H0). discriminate H1. 

nin H. tv. 
nin H. rwi H H0. rwi source_arrow_one_at H0. 
cp (R_inj H0). discriminate H1. 

rwi H H0. rwi source_arrow_one_at H0. 
cp (R_inj H0). discriminate H1. 


ee. cp H. 
rwi mor_function_cat3 H. ee. 
cp H2. rwi inc_twoarrow_objects H6. nin H6. 
cp (all_arrow_one_at H1 H6). nin H7. 
ee. rwi inc_twoarrow_objects H3. 
nin H3. rwi H3 H8. rwi H3 H7. 
rwi inc_one H7. rwi H7 H8. 
uhg. ap or_introl. 
util (all_arrow_one_at (z:= twoarrow_objects) (u := fa_id (R 1))).
rewrite <- id_function_cat with (z:=twoarrow_objects). 
ap mor_id. rw ob_function_cat. 
rw inc_twoarrow_objects. ap or_introl; tv. 
rw inc_twoarrow_objects. ap or_introl; tv. 
rww source_fa_id. 
nin H9. ee. rw H10. rw H8. 
rwi target_fa_id H9. rwi inc_one H9. 
rw H9. rw target_fa_id. reflexivity. 

rwi H3 H7; rwi H3 H8. 
rwi inc_two H7. nin H7. rwi H7 H8. 
rw H8. uhg; ee. ap or_intror. ap or_intror. 
ap or_introl; reflexivity. 
rwi H7 H8. rw H8. uhg. 
ap or_intror. ap or_intror. ap or_intror. 
reflexivity. 
cp (H0 H6). rw H7. 
uhg. ap or_intror. ap or_introl; reflexivity. 
Qed.



Definition twoarrow_cat := 
subcategory (function_cat twoarrow_objects) (fun x => True)
twoarrow_morp.

Lemma case_source_two : forall u,
twoarrow_morp u ->
source u = (R 2) -> 
u = fa_id (R 2).
Proof.
ir. rwi twoarrow_morp_rw H. ee. 
au. 
Qed.

Lemma case_target_one : forall u,
twoarrow_morp u ->
target u = (R 1) ->
u = fa_id (R 1).
Proof.
ir. uh H. nin H. 
am. nin H. rwi H H0. rwi target_fa_id H0.
cp (R_inj H0). discriminate H1. 
nin H. rwi H H0.
rwi target_arrow_one_at H0. cp (R_inj H0). 
discriminate H1. 
rwi H H0. 
rwi target_arrow_one_at H0. cp (R_inj H0). 
discriminate H1. 
Qed.

Lemma case_source_one_target_two : forall u,
twoarrow_morp u ->
source u = (R 1) ->
target u = (R 2) -> 
((u = arrow_one_at (R 0) (R 2)) \/
(u = arrow_one_at (R 1) (R 2))).
Proof.
ir. uh H.
nin H. rwi H H1. 
rwi target_fa_id H1.
cp (R_inj H1). discriminate H2. 
nin H. rwi H H0. 
rwi source_fa_id H0.
cp (R_inj H0). discriminate H2. 
exact H. 
Qed. 


Lemma twoarrow_property : 
subcategory_property (function_cat twoarrow_objects) (fun x => True)
twoarrow_morp.
Proof.
ir. uhg; ee. 
ap function_cat_axioms. 
ir. 
rww comp_function_cat. 

assert (inc (source u) twoarrow_objects).
rewrite <- ob_function_cat with (z:=twoarrow_objects). 
rww ob_source. 
assert (inc (target u) twoarrow_objects).
rewrite <- ob_function_cat with (z:=twoarrow_objects). 
rww ob_target. 
rwi inc_twoarrow_objects H4. 
nin H4. 
rwi H1 H4. 
cp (case_target_one H3 H4). rw H6. 

rw right_fa_id. am.  
rwi mor_function_cat1 H; ee; am. rw H1.  sy; am. 
cp (case_source_two H2 H4). 
rw H6. 
rw left_fa_id. am.  
rwi mor_function_cat1 H0; ee; am. wr H1.  sy; am.

ir. rw id_function_cat. 
rwi ob_function_cat H. 
rwi inc_twoarrow_objects H. nin H. rw H. 
uhg. ap or_introl; reflexivity. 
rw H. uhg. ap or_intror. 
ap or_introl. reflexivity. 
rwi ob_function_cat H. am. 
ir. tv. ir. tv. 
Qed.

Lemma twoarrow_cat_axioms :
Category.axioms twoarrow_cat. 
Proof.
uf twoarrow_cat. ap subcategory_axioms. 
ap twoarrow_property. 
Qed. 


Lemma ob_twoarrow_cat : forall x, 
ob twoarrow_cat x = 
(x = R 1 \/ x = R 2).
Proof.
ir. uf twoarrow_cat. 
rw ob_subcategory. ap iff_eq. 
ir. ee. rwi ob_function_cat H.
rwi inc_twoarrow_objects H. am. 
ir. rw ob_function_cat. ee. 
rw inc_twoarrow_objects. am. tv. 
ap twoarrow_property. 
Qed.

Lemma id_twoarrow_cat : forall x,
ob twoarrow_cat x -> id twoarrow_cat x = fa_id x.
Proof.
ir. uf twoarrow_cat. 
rw id_subcategory. rww id_function_cat. 
rw inc_twoarrow_objects. rwi ob_twoarrow_cat H. 
am. ap twoarrow_property. 
rw ob_function_cat. 
rw inc_twoarrow_objects. rwi ob_twoarrow_cat H. 
am. tv. 
Qed.

Lemma mor_twoarrow_cat1 : forall u,
mor twoarrow_cat u = 
((ob twoarrow_cat (source u) & u = id twoarrow_cat (source u)) 
\/ 
(u = arrow_one_at (R 0) (R 2) \/ u = arrow_one_at (R 1) (R 2))).
Proof.
ir. 
assert (lem1 : inc (R 1) twoarrow_objects).
rw inc_twoarrow_objects. ap or_introl; tv.
assert (lem1a : ob twoarrow_cat (R 1)).
rw ob_twoarrow_cat. ap or_introl; tv.
assert (lem2 : inc (R 2) twoarrow_objects).
rw inc_twoarrow_objects. ap or_intror; tv.
assert (lem2a : ob twoarrow_cat (R 2)).
rw ob_twoarrow_cat. ap or_intror; tv. 


ap iff_eq; ir. 
ufi twoarrow_cat H. 
rwi mor_subcategory H. ee. 
uh H0. nin H0. ap or_introl. 
ee. rw H0. rww source_fa_id.  rw H0. 
rw source_fa_id. uf twoarrow_cat.
rw id_subcategory. rww id_function_cat. 
ap twoarrow_property. 
rww ob_function_cat. tv. 

nin H0. rw H0. 
rw source_fa_id. ap or_introl. 
ee. am. uf twoarrow_cat. 
rw id_subcategory. rww id_function_cat. 
ap twoarrow_property. rww ob_function_cat. 
tv. 

nin H0. ap or_intror. app or_introl. 
ap or_intror. app or_intror. 
ap twoarrow_property. 

assert (twoarrow_morp u).
nin H. ee. 
rwi ob_twoarrow_cat H. nin H. rwi H H0. 
rwi id_twoarrow_cat H0. 
uhg; app or_introl. am. 
rwi id_twoarrow_cat H0. rwi H H0. 
uhg; ap or_intror; app or_introl. 
rww H. 
uhg; ap or_intror; app or_intror. 
uf twoarrow_cat. rw mor_subcategory. 
ee. rwi twoarrow_morp_rw H0. ee; am. am. 
ap twoarrow_property. 
Qed.

Lemma mor_twoarrow_cat2 : forall u,
mor twoarrow_cat u = 
(twoarrow_morp u &
mor (function_cat twoarrow_objects) u &
((ob twoarrow_cat (source u) & u = id twoarrow_cat (source u)) 
\/ 
(source u = R 1 & target u = R 2 & 
(u = arrow_one_at (R 0) (R 2) \/ u = arrow_one_at (R 1) (R 2))))).
Proof.
ir. ap iff_eq; ir. 
ee. ufi twoarrow_cat H. 
rwi mor_subcategory H. ee; am. 
ap twoarrow_property. 

ufi twoarrow_cat H. 
rwi mor_subcategory H. ee; am. 
ap twoarrow_property. 

rwi mor_twoarrow_cat1 H. 
nin H. app or_introl. 
ap or_intror. ee. 
nin H. rw H. rww source_arrow_one_at. 
rw H. rww source_arrow_one_at. 
nin H. rw H. rww target_arrow_one_at. 
rw H. rww target_arrow_one_at. 
am. 
rw mor_twoarrow_cat1. ee. 
nin H1. 
app or_introl. 
ee. app or_intror. 
Qed.



Lemma comp_twoarrow_cat : forall u v,
mor twoarrow_cat u -> mor twoarrow_cat v ->
source u = target v -> 
comp twoarrow_cat u v = fa_comp u v.
Proof.
ir. 
uf twoarrow_cat. 
rw comp_subcategory. 
rw comp_function_cat. tv. 
rwi mor_twoarrow_cat2 H. ee; am. 
rwi mor_twoarrow_cat2 H0; ee; am. am. 
ap twoarrow_property. 
rwi mor_twoarrow_cat2 H. ee; am. 
rwi mor_twoarrow_cat2 H0; ee; am. am. 
rwi mor_twoarrow_cat2 H. ee; am. 
rwi mor_twoarrow_cat2 H0; ee; am. 
Qed.

Lemma composable_twoarrow_cat : forall u v,
mor twoarrow_cat u -> mor twoarrow_cat v ->
source u = target v -> 
((source u = R 2 & u = id twoarrow_cat (source u) &
source u = target u & comp twoarrow_cat u v = v)
\/
(source u = R 1 & v = id twoarrow_cat (target v) &
source v = target v & comp twoarrow_cat u v = u)).
Proof.
ir. 
assert (ob twoarrow_cat (source u)). rww ob_source. 
rwi ob_twoarrow_cat H2. 
nin H2. ap or_intror. 
dj. am. 
rwi mor_twoarrow_cat2 H0. 
ee. rwi H1 H2. cp (case_target_one H0 H2). 
rw H2. rw id_twoarrow_cat. am. 
wr H2. wr H1. rww ob_source. 
rw H4. 
rw source_id. rw target_id. tv. 
rww ob_target. rww ob_target. 
rw H4. 
wr H5. 
rw right_id. tv. 
rww ob_source. am. rww H5. tv. 

ap or_introl. dj. am. 
rwi mor_twoarrow_cat2 H. ee. 
cp (case_source_two H H2). 
rw H2. rw id_twoarrow_cat. am. 
wr H2. rw H1. rww ob_target. 
rw H4. 
rw source_id. rww target_id. 
rww ob_source. rww ob_source. 
rw H4. 
rw left_id. tv. 
rww ob_source. am. sy; am. tv. 
Qed.

Lemma ob_ta_1 : ob twoarrow_cat (R 1).
Proof.
ir. rw ob_twoarrow_cat. app or_introl. 
Qed.

Lemma ob_ta_2 : ob twoarrow_cat (R 2).
Proof.
ir. rw ob_twoarrow_cat. app or_intror. 
Qed.

Lemma mor_ta_i1 : mor twoarrow_cat (fa_id (R 1)).
Proof.

Qed.

Lemma mor_ta_i2 : mor twoarrow_cat (fa_id (R 2)).
Proof.

Qed.

Lemma mor_ta_a0 : mor twoarrow_cat (arrow_one_at (R 0) (R 2)).
Proof.

Qed.

Lemma mor_ta_a1 : mor twoarrow_cat (arrow_one_at (R 1) (R 2)).
Proof.

Qed.



Definition twoarrow_functor u v a :=
Functor.create twoarrow_cat a 
(fun w => 
Y (w = fa_id (R 1)) (id a (source u))
(Y (w = fa_id (R 2)) (id a (target u))
(Y (w = arrow_one_at (R 0) (R 2)) u
v))).

Lemma source_twoarrow_functor : forall u v a,
source (twoarrow_functor u v a) = twoarrow_cat.
Proof.
ir. uf twoarrow_functor. 
rww Functor.source_create. 
Qed.

Lemma target_twoarrow_functor : forall u v a,
target (twoarrow_functor u v a) = a.
Proof.
ir. uf twoarrow_functor. 
rww Functor.target_create. 
Qed.



Lemma fmor_taf_i1 : forall u v a,
fmor (twoarrow_functor u v a) (fa_id (R 1)) = id a (source u).
Proof.
ir. uf twoarrow_functor. 
rw fmor_create. 
rw Y_if_rw. tv. tv. 

Qed.

Lemma fmor_taf_i2 :  forall u v a,
fmor (twoarrow_functor u v a) (fa_id (R 2)) = id a (target u).
Proof.

Qed.

Lemma fmor_taf_a0 : forall u v a, 
fmor (twoarrow_functor u v a) (arrow_one_at (R 0) (R 2)) = u.
Proof.

Qed.

Lemma fmor_taf_a1 : forall u v a, 
fmor (twoarrow_functor u v a) (arrow_one_at (R 1) (R 2)) = v.
Proof.

Qed.

Lemma fob_taf_1 : forall u v a,
fob (twoarrow_functor u v a) (R 1) = source u.
Proof.

Qed.

Lemma fob_taf_2 : forall u v a,
fob (twoarrow_functor u v a) (R 2) = target u.
Proof.

Qed.

Lemma twoarrow_functor_axioms : forall u v a,
mor a u -> mor a v -> 
source u = source v -> target u = target v ->
Functor.axioms (twoarrow_functor u v a).
Proof.
ir.  uhg; ee;
try (rw source_twoarrow_functor); 
try (rw target_twoarrow_functor). uf twoarrow_functor. 
uf Functor.create. 
ap Umorphism.create_like. 
ap twoarrow_cat_axioms. 
uh H; ee. am. 



Qed.




End Twoarrow_Cat. 

*******************************************)


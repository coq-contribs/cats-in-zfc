
Set Implicit Arguments.
Unset Strict Implicit.

Require Import Arith.
Require Export ordinal.

Module Cardinal.
Import Universe. 
Import Transformation.
Import Map. 
Export Ordinal.

Definition iso_sub x y :=
exists u, (are_isomorphic x u & sub u y).

Lemma iso_sub_trans_rw : forall x y,
iso_sub x y = (exists f, Transformation.injective x y f).
Proof.
ir. ap iff_eq; ir. uh H; nin H. ee. 
sh (isotrans x x0). 
rwi iso_isotrans_rw H. uh H; ee. 
cp (subidentity_injective H0). 
cp (compose_injective H2 H3). am. 
uhg. 
nin H. sh (Image.create x x0). 
ee. rw iso_trans_ex_rw. 
sh x0. apply trans_sub_bijective with x y. am. 
ap sub_refl. uhg; ir. rwi Image.inc_rw H0.
nin H0. ee. wr H1. uh H. ee. uh H. ap H. am. 
Qed. 
 
Lemma sub_iso_sub: forall a b, sub a b-> iso_sub a b.
Proof.
ir. 
uhg. sh a. ee. 
ap are_isomorphic_refl. am. 
Qed. 

(*** sow = smallest ordinal with the property in question **)
Definition cardinality x := 
sow (are_isomorphic x).

Definition card_isomap x := isomap x (cardinality x).
Definition card_isotrans x := isotrans x (cardinality x).

Lemma card_isomorphic : forall x,
are_isomorphic x (cardinality x).
Proof.
ir. uf cardinality. ap sow_property. 
cp (every_set_can_be_well_ordered x).
nin H. ee. 
sh (wo_ordinal x0). ee. ap wo_ordinal_is_ordinal. 
am. 
apply trans_bij_isomorphic with (wo_avatar x0).
wr H0. ap wo_avatar_bijective. am. 
Qed. 

Lemma card_isomap_bij : forall x,
Map.bijective x (cardinality x) (card_isomap x).
Proof. 
ir. uf card_isomap. 
ap isomap_bij. ap card_isomorphic. 
Qed. 

Lemma card_isotrans_bij : forall x,
Transformation.bijective 
x (cardinality x) (card_isotrans x).
Proof.
ir. uf card_isotrans. ap isotrans_bij. ap card_isomorphic. 
Qed. 

Lemma cardinality_ordinal : forall x,
is_ordinal (cardinality x).
Proof.
ir. uf cardinality. 
ap sow_ordinal. 
Qed.

Lemma cardinality_smallest : forall x o,
is_ordinal o -> are_isomorphic x o ->
ordinal_leq (cardinality x) o.
Proof.
ir. uf cardinality. ap sow_smallest. am. am. 
Qed. 



Lemma cardinality_invariant : forall x y,
are_isomorphic x y -> cardinality x = cardinality y.
Proof.
ir. ap ordinal_leq_leq_eq. 
ap cardinality_smallest. ap cardinality_ordinal. 
ap are_isomorphic_trans. sh y. ee; try am. 
ap card_isomorphic. 
ap cardinality_smallest. ap cardinality_ordinal. 
ap are_isomorphic_trans. sh x. ee; try am. 
ap are_isomorphic_symm. am. 
ap card_isomorphic. 
Qed. 




Lemma wo_ordinal_isomorphic : forall a,
is_well_ordered a -> 
are_isomorphic (U a) (wo_ordinal a).
Proof.
ir. rw iso_trans_ex_rw. 
sh (wo_avatar a). 
ap wo_avatar_bijective. am. 
Qed. 

Lemma wo_ordinal_cardinal_leq : forall a,
is_well_ordered a -> 
ordinal_leq (cardinality (U a)) (wo_ordinal a).
Proof.
ir. 
ap cardinality_smallest. ap wo_ordinal_is_ordinal. 
am. ap wo_ordinal_isomorphic; am. 
Qed. 

Lemma ordinal_leq_subset_wo_ordinal : forall a u,
is_well_ordered a -> sub u (U a) ->
ordinal_leq (cardinality u) (wo_ordinal a).
Proof.
ir. 
ap ordinal_leq_trans. 
pose (b:=suborder u a). 
sh (wo_ordinal b). 
assert (u = (U b)).
uf b; rw underlying_suborder. tv. ee. rw H1. 
uf b. 
ap wo_ordinal_cardinal_leq. 
ap suborder_well_ordered. am. am. 
uf b. 
ap suborder_wo_ordinal_decreasing. am. am. 
Qed. 

Lemma subset_ordinal_cardinal_leq : forall u o,
is_ordinal o -> sub u o ->
ordinal_leq (cardinality u) o.
Proof.
ir. 
cp (wo_ordinal_obi_rw H). wr H1. 
ap ordinal_leq_subset_wo_ordinal. 
cp (ordinal_obi_next_compatible H). lu. 
rw obi_U. am. 
Qed.

Lemma isomorphic_iso_sub : forall a b,
are_isomorphic a b -> iso_sub a b.
Proof.
ir. rwi iso_trans_ex_rw H. nin H. 
rw iso_sub_trans_rw. sh f; lu. 
Qed. 

Lemma iso_sub_trans : forall a c,
(exists b,
iso_sub a b & iso_sub b c) -> iso_sub a c.
Proof.
ir. nin H. ee. rwi iso_sub_trans_rw H0. nin H0.
rwi iso_sub_trans_rw H. nin H. 
rw iso_sub_trans_rw. 
sh (fun y => (x0 (x1 y))). 
apply compose_injective with x. am. am. 
Qed. 


Lemma iso_sub_ordinal_leq : forall u o,
is_ordinal o -> iso_sub u o ->
ordinal_leq (cardinality u) o.
Proof.
ir. uh H0. nin H0. 
ee. cp (cardinality_invariant H0). rw H2. 
ap subset_ordinal_cardinal_leq. am. am. 
Qed. 

Lemma iso_sub_cardinal_leq : forall x y,
iso_sub x y -> 
(ordinal_leq (cardinality x) (cardinality y)).
Proof.
ir. 
assert (iso_sub x (cardinality y)). 
cp (card_isomorphic y). 
cp (isomorphic_iso_sub H0). 
ap iso_sub_trans. sh y; ee; am. 
ap iso_sub_ordinal_leq. 
ap cardinality_ordinal. am. 
Qed. 

Lemma sub_cardinal_leq : forall x y,
sub x y -> 
(ordinal_leq (cardinality x) (cardinality y)).
Proof.
ir. ap iso_sub_cardinal_leq. ap sub_iso_sub; am. 
Qed. 

Lemma bernstein_cantor_schroeder : forall x y,
iso_sub x y -> iso_sub y x -> are_isomorphic x y.
Proof.
ir. cp (iso_sub_cardinal_leq H).
cp (iso_sub_cardinal_leq H0). 
cp (ordinal_leq_leq_eq H1 H2). 
cp (card_isomorphic x). 
cp (card_isomorphic y). 
ap are_isomorphic_trans. sh (cardinality x). 
ee; try am. rw H3. ap are_isomorphic_symm. am. 
Qed. 




Definition is_finite x := forall f,
Transformation.injective x x f -> 
Transformation.bijective x x f.

Definition is_infinite x := ~(is_finite x).

Lemma finite_invariant : forall y,
(exists x, are_isomorphic x y & is_finite x) -> 
is_finite y. 
Proof.
ir. nin H. ee. 
rwi iso_trans_ex_rw H. 
nin H. uhg. ir. 
pose (g:= fun z => (inverse x x0 (f (x0 z)))). 
cp (Transformation.bijective_inverse H).
assert (are_inverse y x (inverse x x0) x0).
uhg; ee; lu. 
cp (Transformation.inverse_bijective H3). 
uh H0. util (H0 g). 
uhg. ee. 
uf g. 
uhg; ir. 
uh H4; ee. uh H4. ap H4. 
uh H1; ee; uh H1. ap H1. 
uh H; ee; uh H; ap H. am. 
uf g; uhg; ir. 
uh H; ee. uh H9; ee. ap H10. am. am. 
uh H1; ee. ap H11.
ap H. am. ap H. am. 
uh H4; ee. uh H13; ee. ap H14. 
ap H1. ap H; am. ap H1; ap H; am. am. 
uhg; ee; try lu. 
uhg. ee; try lu. uhg. ir. 
uh H5; ee. uh H7; ee. util (H9 (inverse x x0 x1)). 
uh H4; ee. ap H4. am. 
nin H10; ee. 
sh (x0 x2). ee. 
uh H; ee; ap H. am. 
uh H4; ee. uh H13; ee. ap H14. 
uh H1; ee; ap H1. uh H; ee; ap H. am. am. 
am. 
Qed. 


Lemma finite_tack_on_case : forall x y f,
is_finite x -> 
Transformation.injective (tack_on x y) (tack_on x y) f ->
f y = y ->
Transformation.bijective (tack_on x y) (tack_on x y) f.
Proof.
ir. uhg; ee; try lu.
apply by_cases with (inc y x); ir. 
assert (tack_on x y = x).
ap extensionality; uhg; ir. rwi tack_on_inc H3; nin H3.
am. rw H3; am. rw tack_on_inc. ap or_introl; am. 
rw H3. rwi H3 H0. 
cp (H f H0). lu. 

util (H f). 
uhg; ee. uhg; ir. 
uh H0; ee. util (H0 x0). 
rw tack_on_inc; ap or_introl; am. 
rwi tack_on_inc H5; nin H5. am.
assert (x0 = y). ap H4. 
rw tack_on_inc. ap or_introl; am. 
rw tack_on_inc; ap or_intror; tv. rw H5; sy; am. 
assert False. ap H2. wr H6; am. elim H7.
uh H0; ee. uhg; ir. ap H3.
rw tack_on_inc; ap or_introl; am.
rw tack_on_inc; ap or_introl; am.
am. 
uhg; ee; try lu. 
uhg; ir. 
rwi tack_on_inc H4; nin H4. 
uh H3; ee. uh H5; ee. cp (H7 _ H4). nin H8.
ee. sh x1. ee; try am. rw tack_on_inc; ap or_introl; am. 
sh y; ee. rw tack_on_inc; ap or_intror; tv. rw H4. am.
Qed. 


Lemma finite_tack_on : forall x y,
is_finite x -> is_finite (tack_on x y).
Proof.
ir. 
uhg; ir. 
pose (g:= fun z => Transposition.create y (f y) (f z)).
util (finite_tack_on_case (x:=x) (y:=y) (f:=g)).
am. 
uhg; ee. uhg; ir. 
uh H0; ee. cp (H0 x0 H1). 
apply by_cases with (f x0 = f y); ir.
uf g. rw H4. 
rw Transposition.i_j_j. 
rw tack_on_inc; ap or_intror; tv. 
apply by_cases with (f x0 = y); ir. 
uf g. rw H5. 
rw Transposition.i_j_i. 
util (H0 y). rw tack_on_inc; ap or_intror; tv. am. 
uf g. 
rw Transposition.not_i_not_j; try am. 
uhg; ir. 
uh H0; ee. ap H4; try am. 
apply Transposition.inj with y (f y). am. 
uf g. rw Transposition.i_j_j. tv.
uhg; ee; try lu. 
uhg; ee; try lu. uhg; ir. 

assert (inc (Transposition.create y (f y) x0) (tack_on x y)).
apply by_cases with (x0 = y); ir. rw H3; 
rw Transposition.i_j_i. uh H0; ee; ap H0. 
rw tack_on_inc; ap or_intror; tv. 
apply by_cases with (x0 = f y); ir. 
rw H4; rw Transposition.i_j_j. 
rw tack_on_inc; ap or_intror; tv. 
rw Transposition.not_i_not_j; try am. 
uh H1; ee. uh H4; ee. cp (H6 _ H3). 
nin H7. sh x1; ee; try am.
apply Transposition.inj with y (f y). am. 
Qed. 

Lemma finite_emptyset : is_finite emptyset.
Proof.
ir. uhg. ir. uhg. dj. 
uhg. ir. nin H0. nin x0. uhg. 
ee; try am. uhg. ir. 
nin H1. nin x0. 
uhg. ee; try am. 
uhg. ir. nin H2. nin x0.  
Qed.

Lemma finite_tack : forall x y,
is_finite x -> is_finite (tack y x).
Proof.
ir. uf tack. app finite_tack_on.
Qed.

(****** the next things to prove **********
Lemma finite_induction: forall (p:EP) x,
(p emptyset) -> 
(forall y z, p y -> p (tack_on y z)) ->
is_finite x -> p x.
Proof.
Qed. 


Lemma subset_finite : forall x,
(exists y, (sub x y & is_finite y)) -> is_finite x.
Proof.

Qed. 

Lemma image_finite : forall x f,
is_finite x -> is_finite (Image.create x f).
Proof.

Qed.

****************************************)




End Cardinal. 

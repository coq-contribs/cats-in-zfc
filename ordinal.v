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
Require Export transfinite.

Module Ordinal.
Import Universe. 
Export Transfinite.


Definition ID (y:E):= y.

Definition is_ordinal (o:E):=is_leq_gen_scale ID o.

Lemma ordinal_union : forall z:E,
(forall u:E, inc u z -> is_ordinal u) -> is_ordinal (union z).
Proof.
ir. uhg. ap leq_gen_scale_union. ir. 
exact (H y H0).
Qed. 

Lemma emptyset_ordinal : is_ordinal emptyset. 
Proof.
assert (emptyset = union emptyset :> E).
ap extensionality; uhg; ir. elim (B H). 
cp (union_exists H). nin H0. ee. 
elim (B H1). rw H. ap ordinal_union; ir. 
elim (B H0). 
Qed. 

Lemma ordinal_tack_on : forall o:E, is_ordinal o ->
is_ordinal (tack_on o o).
Proof.
ir. uhg. 
apply by_cases with (inc o o); ir. 
assert (tack_on o o = o). ap extensionality; uhg; ir.
rwi tack_on_inc H1; nin H1. am. rw H1; am. 
rw tack_on_inc. ap or_introl; am. rw H1; am. 
change (is_leq_gen_scale ID (tack_on o (ID o))).
ap leq_gen_scale_tack_on. exact H. am. 
Qed. 

Lemma ordinal_sub_or : forall a o:E,
is_ordinal a -> is_ordinal o -> 
(sub a o \/ sub o a).
Proof.
ir. uh H; uh H0. cp (leq_gen_scale_or H H0). am.
Qed. 

Lemma ordinal_induction : forall (p:EP),
(forall z:E,(forall u:E, inc u z -> p u)-> p (union z)) ->
(forall u :E, p u -> p (tack_on u u)) -> 
(forall o:E, is_ordinal o -> p o).
Proof. 
ir. util (lgs_induction (f:=ID) (p:= p)). 
am. am. ap H2. am. 
Qed. 

Definition is_smallest_ordinal_with (p:EP)(o:E):=
(is_ordinal o & p o & 
(forall x:E, is_ordinal x -> p x -> sub o x)).

Lemma exists_smallest_ordinal_with : forall (p:EP),
(exists x:E, (is_ordinal x&p x)) ->
exists o:E, is_smallest_ordinal_with p o.
Proof.
ir. util (lgs_smallest_with_property (f:=ID)(p:=p)).
am. am. 
Qed. 






Lemma ordinal_not_inc : forall x o:E, is_ordinal o ->
inc x o -> ~inc x x.
Proof.
ir. util (ordinal_induction (p:= fun y:E=>(forall u:E,
inc u y -> ~inc u u))).
ir. cp (union_exists H2). nin H3; ee. 
cp (H1 x0 H4 u H3). am. 
ir. rwi tack_on_inc H2; nin H2. ap H1; am. uhg; ir. 
util (H1 u0). wr H2; am. ap H4; am. 
cbv beta in H1. apply H1 with o. am. am.
Qed. 

Lemma ordinal_inc_ordinal : forall x o:E, is_ordinal o ->
inc x o -> is_ordinal x.
Proof. 
ir. util (ordinal_induction (p:= fun y:E=>(is_ordinal y &
forall u:E,
inc u y -> is_ordinal u))); ir.
ee. ap ordinal_union. ir. cp (H1 u H2). ee; am. 
ir. nin (union_exists H2). ee. cp (H1 x0 H4). 
ee. ap H6; am. ee. 
ap ordinal_tack_on; am. ir.
rwi tack_on_inc H3; nin H3. 
ap H2; am. rw H3; am. 
cbv beta in H1. cp (H1 o H); ee.
ap H3; am. 
Qed. 

Lemma ordinal_not_inc_itself :forall o:E,
is_ordinal o -> ~inc o o. 
Proof. 
ir. uhg; ir. apply ordinal_not_inc with o o.
am. am. am. 
Qed. 

Lemma ordinal_strict_sub_inc : forall a o:E,
is_ordinal a -> is_ordinal o -> strict_sub a o -> inc a o.
Proof.
ir. uh H; uh H0. cp H; cp H0. 
uh H; uh H0; nin H; nin H0.
ee. assert (next x0 a= ID a). 
ap next_compatible_scale. am. 
apply leq_gen_scale_subset with ID. am. 
am. rw H0; uh H1; ee; am. rw H0; am.
wr H0. ufi ID H6. wr H6. ap next_inc_U. rw H0; am. 
uh H4; ee; am. 
Qed. 

Lemma ordinal_inc_rw : forall x o:E,
is_ordinal o -> 
(inc x o = (is_ordinal x & strict_sub x o)).
Proof. 
ir. ap iff_eq; ir. dj. apply ordinal_inc_ordinal with o; am. 
uhg; ee. uhg; uhg; ir. apply ordinal_not_inc_itself with o. 
am. rwi H2 H0. am. 
nin (ordinal_sub_or H H1). 
assert (inc x x). ap H2; am. assert False.
apply ordinal_not_inc_itself with x; am. elim H4. am. 
ee. ap ordinal_strict_sub_inc; am. 
Qed. 

Lemma ordinal_inc_sub : forall a o:E,
is_ordinal o -> inc a o -> sub a o.
Proof.
ir. rwi ordinal_inc_rw H0.  ee.
uh H1; ee; am. am. 
Qed. 

Definition ordinal_leq a o:= (is_ordinal a & is_ordinal o&
sub a o).

Definition ordinal_lt a o:= (ordinal_leq a o & a <> o).

Lemma ordinal_lt_rw : forall a o:E,
ordinal_lt a o = (is_ordinal o&inc a o).
Proof.
ir. uf ordinal_lt.
uf ordinal_leq; ap iff_eq; ir; xd. 
rw ordinal_inc_rw. uf strict_sub; xd. am. 
rwi ordinal_inc_rw H0; ee; am. rwi ordinal_inc_rw H0; ee. 
uh H1; ee; am. am. rwi ordinal_inc_rw H0; ee. uh H1; ee; am. am. 
Qed.

Lemma ordinal_leq_leq_or : forall a o:E,
is_ordinal a -> is_ordinal o -> 
(ordinal_leq a o \/ ordinal_leq o a).
Proof.
ir. nin (ordinal_sub_or H H0). ap or_introl.
uhg; ee; am. ap or_intror; uhg; ee; am.
Qed. 

Lemma ordinal_leq_leq_eq : forall a b,
ordinal_leq a b -> ordinal_leq b a -> a = b.
Proof.
ir. ap extensionality; lu. 
Qed. 

Lemma ordinal_leq_trans : forall a b,
(exists c, ordinal_leq a c & ordinal_leq c b)->
ordinal_leq a b.
Proof.
ir. nin H. ee. uhg; ee. lu. lu. 
apply sub_trans with x; lu. 
Qed.

Lemma ordinal_if_leq_or : forall a o:E,
ordinal_leq a o -> (ordinal_lt a o \/ a = o).
Proof.
ir. apply by_cases with (a = o); ir. ap or_intror; am. 
ap or_introl. uhg; uh H; xd. uhg; ee; am. 
Qed.  

Lemma ordinal_lt_lt_eq_or : forall a o:E,
is_ordinal a -> is_ordinal o -> 
(ordinal_lt a o \/ ordinal_lt o a \/ a=o).
Proof.
ir. nin (ordinal_leq_leq_or H H0). 
nin (ordinal_if_leq_or H1). ap or_introl. am. ap or_intror.
ap or_intror. am. 
nin (ordinal_if_leq_or H1). ap or_intror. ap or_introl; am. 
ap or_intror; ap or_intror; sy; am. 
Qed.

Lemma ordinal_lt_tack_on_leq : forall a o:E,
is_ordinal a -> (ordinal_lt a o = ordinal_leq (tack_on a a) o).
Proof.
ir. ap iff_eq; ir. cp H0. rwi ordinal_lt_rw H1. ee. 
uhg; ee. ap ordinal_tack_on; am. am. uhg; ir.
rwi tack_on_inc H3; nin H3. uh H0; ee. uh H0; ee. ap H6; am. 
rw H3; am. uhg; ee. uhg; ee; try am. uh H0; ee; am. 
uh H0; ee. uhg; ir. ap H2. rw tack_on_inc. ap or_introl; am. 
uhg; ir. uh H0; ee. apply ordinal_not_inc_itself with a.
am. rw H1. ap H3. rw tack_on_inc. ap or_intror; sy; am. 
Qed. 



Lemma exists_smallest_ordinal_without : forall (p:EP),
(exists x : E, (is_ordinal x & ~ p x))->
exists o:E, (is_ordinal o & ~ p o & forall y : E, inc y o -> p y).
Proof.
ir. 
util (exists_smallest_ordinal_with (p:= fun x => 
(is_ordinal x &~p x))).
nin H; ee. sh x; ee; am. nin H0.
uh H0. ee.  sh x. ee; try am. ir. ap excluded_middle; uhg; ir.
assert (x = y). ap extensionality. ap H2.
apply ordinal_inc_ordinal with x. am. am. 
ee. apply ordinal_inc_ordinal with x; am. am. 
ap ordinal_inc_sub. am. am. apply ordinal_not_inc_itself with x.
am. wri H6 H4; am. 
Qed. 



Definition is_sow (p:EP) o :=
is_ordinal o & (exists x, is_ordinal x & p x) -> 
is_smallest_ordinal_with p o.

Definition sow (p:EP) :=
choose (is_sow p). 

Lemma sow_exists : forall p, exists o, is_sow p o.
Proof.
ir. 
apply by_cases with (exists x, is_ordinal x & p x).
ir. 
sh (choose (is_smallest_ordinal_with p)). 
cp (exists_smallest_ordinal_with H). 
cp (choose_pr H0). 
cbv beta in H1. uhg; ee. 
uh H1; ee. am. ir. 
am. ir. sh emptyset.
uhg; ee. ap emptyset_ordinal. ir. 
elim (H H0). 
Qed. 

Lemma sow_is_sow : forall p, is_sow p (sow p). 
Proof.
ir. cp (sow_exists p). 
cp (choose_pr H). am. 
Qed. 

Lemma sow_ordinal : forall p, is_ordinal (sow p).
Proof. 
ir. cp (sow_is_sow p). uh H; ee. am.  
Qed. 

Lemma sow_property : forall p,
(exists x:E, (is_ordinal x & p x)) ->
p (sow p).
Proof.
ir. 
cp (sow_is_sow p). uh H0; ee. cp (H1 H). uh H2; ee. am. 
Qed.

Lemma sow_smallest : forall (p:EP) o,
is_ordinal o -> p o -> ordinal_leq (sow p) o.
Proof.
ir. 
cp (sow_is_sow p). uh H1; ee. util H2. 
sh o; ee; am. 
uh H3; ee. cp (H5 _ H H0). 
uhg; ee. ap sow_ordinal. am. am. 
Qed. 


Lemma ordinal_leq_gen_refl : forall o:E,
is_ordinal o -> leq_gen ID o o.
Proof.
ir. pose (q:= tack_on o o).
assert (is_ordinal q).
uf q; ap ordinal_tack_on. am. uh H0.
uh H0. nin H0; ee. 
assert (inc o (U x)). rw H0; uf q; rw tack_on_inc. 
ap or_intror; tv. 
rw (leq_gen_leq (f:=ID) (a:= x)). 
ap leq_refl. do 3 (uh H1; ee); am. 
am. am. am. am. 
Qed. 

Lemma ordinal_leq_gen_tack_on : forall o:E,
is_ordinal o -> leq_gen ID o (tack_on o o).
Proof.
ir. 
pose (u:=tack_on o o).
assert (is_ordinal u). uf u; ap ordinal_tack_on; am. 
assert (ordinal_lt o u). 
rw ordinal_lt_rw. ee; try am. uf u; rw tack_on_inc;
ap or_intror; tv. 

pose (q:= tack_on u u).
assert (is_ordinal q). uf q; ap ordinal_tack_on; am.
assert (ordinal_lt u q). 
rw ordinal_lt_rw. ee; try am. uf q; rw tack_on_inc;
ap or_intror; tv. 


cp H2; uh H4; uh H4; nin H4; ee. 

assert (u = next x u). sy; transitivity (ID u).
apply (next_compatible_scale (f:= ID)).
am. 
cp H0. uh H6; uh H6; nin H6; ee. wr H6. 
apply next_comp_sub_scale with (f:= ID). 
am. am. rw H6; rw H4. uh H3; ee. uh H3; ee; am. 
rw H4. rwi ordinal_lt_rw H3; ee. rwi ordinal_inc_rw H6;
ee; am. tv. 
rw (leq_gen_leq (f:=ID)(a:=x)). 
assert (lt x o u).
rw H6; ap next_compatible_lt. 
uh H0; uh H0; nin H0; ee. wr H0; 
apply next_comp_sub_scale with (f:= ID).
am. am. rw H0; rw H4.
uh H3; ee. uh H3; ee; am. rwi ordinal_lt_rw H3.
ee. rwi ordinal_inc_rw H7. ee. rw H4; am. am. 
rwi ordinal_lt_rw H1; ee; am. uh H7; ee; am. am. 
rw H4. uf q; rw tack_on_inc; ap or_introl.
uf u; rw tack_on_inc; ap or_intror; tv. rw H4;
uf q; rw tack_on_inc; ap or_intror; tv. 
Qed. 



Lemma leq_gen_ordinal : forall o:E, leq_gen ID o o ->
is_ordinal o. 
Proof. 
ir. uh H. nin H; ee. assert (is_ordinal (U x)).
uhg. uhg. sh x; ee; try tv; try am. 
apply ordinal_inc_ordinal with (U x). am. 
uh H0; ee; am. 
Qed. 

Lemma leq_gen_ordinal_leq : forall a o:E,
leq_gen ID a o -> ordinal_leq a o.
Proof.
ir. uhg; dj. ap leq_gen_ordinal. apply leq_gen_def1 with o; am. 
ap leq_gen_ordinal; apply leq_gen_def2 with a; am. 
nin (leq_gen_is_next H).
rw H2; uhg; ir; am. nin H2.
ee. ap ordinal_inc_sub. am. ufi ID H4. 
rw H4; am. 
Qed. 




Lemma ordinal_leq_leq_gen : forall a o:E,
ordinal_leq a o = leq_gen ID a o.
Proof.
ir. ap iff_eq; ir. 
assert (leq_gen ID a a).
ap ordinal_leq_gen_refl. uh H; ee; am. 
assert (leq_gen ID o o).
ap ordinal_leq_gen_refl. uh H; ee; am. 
cp (leq_gen_or H0 H1). nin H2. 
am. assert (ordinal_leq o a).
ap leq_gen_ordinal_leq. am. 
assert (a = o). ap extensionality.
uh H; ee; am. uh H3; ee; am. rw H4; am. 
ap leq_gen_ordinal_leq; am. 
Qed. 

Definition obi x := create x sub.

Lemma obi_U : forall x:E, (U (obi x)) = x.
Proof.
ir. uf obi. rw underlying_create; tv. 
Qed.

Lemma obi_leq : forall x u v:E, 
leq (obi x) u v = (inc u x & inc v x & sub u v).
Proof.
ir. uf obi; rw leq_create_all. tv. 
Qed. 

Lemma obi_axioms : forall x:E, axioms (obi x).
Proof.
ir. uf obi. ap create_axioms. 
uf property; dj. uhg; ir; am. ap extensionality; am.
apply sub_trans with y; am. 
Qed. 

Lemma ordinal_obi_leq : forall x u v:E,
is_ordinal x -> 
leq (obi x) u v = (inc u x & inc v x & ordinal_leq u v). 
Proof.
ir. rw obi_leq; uf ordinal_leq; ap iff_eq; ir; xd. 
apply ordinal_inc_ordinal with x; am. 
apply ordinal_inc_ordinal with x; am. 
Qed. 

Lemma ordinal_leq_inc_tack_on : forall o x:E,
is_ordinal o -> 
ordinal_leq x o = inc x (tack_on o o).
Proof. 
ir. ap iff_eq; ir. nin (ordinal_if_leq_or H0). 
rw tack_on_inc; ap or_introl. rwi ordinal_lt_rw H1. 
ee; am. rw tack_on_inc; ap or_intror. am. 
rwi tack_on_inc H0. nin H0. 
rwi ordinal_inc_rw H0. ee. uh H1; ee. uhg; ee; am. 
am. rw H0; uhg; ee. am. am. uhg; ir; am. 
Qed. 

Lemma ordinal_container : forall z:E,
(forall u:E, inc u z -> is_ordinal u) -> 
exists o:E, (is_ordinal o & sub z o).
Proof.
ir. 
pose (q:= (union z)). assert (is_ordinal q).
uf q; ap ordinal_union; am. 
sh (tack_on q q). ee. 
ap ordinal_tack_on; am. uhg; ir. 
assert (ordinal_leq x q). uhg; ee. 
ap H; am. am. uhg; ir. uf q; apply union_inc with x. 
am. am.  
wr ordinal_leq_inc_tack_on. am. am. 
Qed. 

Lemma ordinal_leq_obi : forall a x y,
next_compatible ID a -> inc x (U a) -> inc y (U a) ->
leq (obi (U a)) x y = leq a x y.
Proof.
ir. assert (is_ordinal (U a)). 
uhg; ee. uhg. sh a; ee; try tv; try am. 
ap iff_eq; ir. 
wr (leq_gen_leq (f:=ID)). 
rwi ordinal_obi_leq H3. ee. 
wr ordinal_leq_leq_gen. am. am. am. 
am. am. 
rw ordinal_obi_leq. ee; try am. 
wri (leq_gen_leq (f:=ID)) H3. 
rw ordinal_leq_leq_gen. am. am. am. am. am. 
Qed. 

Lemma ordinal_next : forall a x,
next_compatible ID a -> inc x (U a) ->
next a x = x. 
Proof.
ir. uh H; ee. cp (H1 _ H0). ufi ID H2. 
wr H2. 
wr next_punctured_downward. sy; am. am. am. 
Qed. 


Lemma punctured_downward_for_ord : forall a x,
next_compatible ID a -> inc x (U a) ->
punctured_downward_subset a x = x. 
Proof.
ir.  
util (ordinal_next (a:=a) (x:=x)). am. 
am. 
uh H. ee. ufi ID H2. ap H2. am. 
Qed. 

Lemma ordinal_obi_lt : forall o x y,
is_ordinal o ->
lt (obi o) x y = (inc x y & inc y o).
Proof.
ir. 
ap iff_eq; ir. ee. uh H0; ee. 
rwi obi_leq H0. ee. 
ap ordinal_strict_sub_inc. 
apply ordinal_inc_ordinal with o; am. 
apply ordinal_inc_ordinal with o; am. uhg; ee; am. 
uh H0; ee. uh H0; ee. rwi obi_U H2; am. 
ee. uhg; ee. rw obi_leq. ee; try am. 
cp ordinal_inc_sub. ufi sub H2. apply H2 with y. am. 
am. am. ap ordinal_inc_sub. apply ordinal_inc_ordinal
with o; am. am. uhg; ir. 
apply ordinal_not_inc_itself with x. apply ordinal_inc_ordinal
with o. am. rw H2; am. wri H2 H0; am. 
Qed. 

Lemma ordinal_inc_trans: forall o x,
(exists y, inc x y & inc y o) -> is_ordinal o ->
inc x o.
Proof.
ir. cp ordinal_inc_sub. ufi sub H1. 
nin H. ee. apply H1 with x0. am. am. am. 
Qed. 

Lemma ordinal_punctured_downward : forall o x,
is_ordinal o -> inc x o -> 
punctured_downward_subset (obi o) x = x.
Proof.
ir. 
uf punctured_downward_subset; ap extensionality;
uhg; ir. Ztac. 
rwi ordinal_obi_lt H3. ee; am. am. 
ap Z_inc. rw obi_U. 
ap ordinal_inc_trans. sh x. ee; am. am. 
rw ordinal_obi_lt. ee; am. am.  
Qed. 



Lemma ordinal_obi_next_compatible : forall o:E,
is_ordinal o -> next_compatible ID (obi o).
Proof.
ir. 
cp H; uh H. uh H. nin H. ee. 
assert (same_order x (obi o)). 
uhg; ee; ap show_is_suborder. 
do 5 (uh H1; ee; try am). ap obi_axioms. ir. 
wr H. rw ordinal_leq_obi. am. am. uh H2; ee; am. 
uh H2; ee; am. ap obi_axioms. 
do 5 (uh H1; ee; try am).
ir. 
wr ordinal_leq_obi. rw H; am. am. 
uh H2; ee. rwi obi_U H2; rw H; am. 
uh H2; ee. rwi obi_U H3; rw H; am. 
uhg; dj. apply wo_same_order with x. am. 
uh H1; ee; am. 
rw ordinal_punctured_downward. tv. am. rwi obi_U H4; am. 
Qed.




Lemma ordinal_inc : forall o x:E,
is_ordinal o -> 
inc x o = (leq_gen ID x o & x <> o).
Proof.
ir. ap iff_eq; ir. ee. wr ordinal_leq_leq_gen. 
uhg. ee; try am. 
apply ordinal_inc_ordinal with o; am. 
ap ordinal_inc_sub; am. uhg; ir. rwi H1 H0. 
apply ordinal_not_inc_itself with o; am.
ee.
wri ordinal_leq_leq_gen H0.
uh H0.
ee. ap ordinal_strict_sub_inc. am. am. 
uhg; ee; am. 
Qed. 

Lemma ordinal_chenille : forall o,
is_ordinal o -> chenille ID o = o.
Proof.
ir. ap extensionality; uhg; ir. 
rwi chenille_inc H0. 
wri ordinal_inc H0. am. am. 
rwi chenille_inc H0. 
ap ordinal_leq_gen_refl; am. ap ordinal_leq_gen_refl; am. 
rw chenille_inc. rwi ordinal_inc H0. am. am. 
ap ordinal_leq_gen_refl; am. 
Qed. 

Lemma ordinal_downward_lgs : forall o:E,
is_ordinal o -> downward_lgs ID o = tack_on o o.
Proof.
ir. wr chenille_tack_on. 
rw ordinal_chenille. tv. am. 
ap ordinal_leq_gen_refl; am. 
Qed. 

Export Transfinite_Mapping.

Lemma ordinal_inc_induction : forall (p:EP)(o:E),
(forall u:E, (forall x:E, inc x u -> p x)-> p u) -> 
is_ordinal o -> p o.
Proof.
ir. 
util (chenille_induction (f:=ID) (p:=p)).
ir. 
ap H. ir. ap H2. 
rw ordinal_chenille. am. 
ap leq_gen_ordinal. am. ap H1. 
ap ordinal_leq_gen_refl; am.  
Qed. 


Lemma ID_expansive : is_expansive ID.
Proof.
uhg. ir.  
uf ID. ap ordinal_not_inc_itself. am. 
Qed. 




Definition wo_avatar a := avatar (next a) ID.

Definition wo_ordinal a := (Image.create (U a) (wo_avatar a)).


Lemma wo_avatar_surjective : forall a,
is_well_ordered a -> 
Transformation.surjective (U a) (wo_ordinal a) (wo_avatar a).
Proof.
ir. 
uhg; ee. uhg. ir. uf wo_ordinal; rw Image.inc_rw. 
sh x; ee; try am. tv. 
uhg. ir. ufi wo_ordinal H0; rwi Image.inc_rw H0. 
nin H0. ee. sh x0; ee; am. 
Qed. 






Lemma wo_avatar_injective : forall a,
is_well_ordered a -> 
Transformation.injective (U a) (wo_ordinal a) (wo_avatar a).
Proof.
ir. 
uhg; ee. uhg. ir. uf wo_ordinal; rw Image.inc_rw. 
sh x; ee; try am. tv. 
uhg. ir. transitivity (avatar ID (next a) (wo_avatar a x)).
uf wo_avatar. rw avatar_trans. rw avatar_refl. tv. 
rw next_leq_gen_leq. ap leq_refl; lu. am. am. am. 
ap ID_expansive. rw next_leq_gen_leq. 
ap leq_refl; lu. am. am. am. rw H2. 
uf wo_avatar. rw avatar_trans. rw avatar_refl. tv.
rw next_leq_gen_leq; try am. ap leq_refl; lu. 
ap ID_expansive. rw next_leq_gen_leq; try am. 
ap leq_refl; lu.  
Qed. 

Lemma wo_avatar_bijective : forall a,
is_well_ordered a -> 
Transformation.bijective (U a) (wo_ordinal a) (wo_avatar a).
Proof.
ir. 
uhg; ee. uhg; ir. uf wo_ordinal; rw Image.inc_rw. 
sh x; ee; try am. tv. 
ap wo_avatar_surjective; am. ap wo_avatar_injective; am. 
Qed. 



Lemma wo_avatar_is_ordinal : forall a x,
is_well_ordered a -> inc x (U a) -> 
is_ordinal (wo_avatar a x).
Proof.
ir. uf wo_avatar. 
ap leq_gen_ordinal. ap avatar_leq_gen_def. 
rw next_leq_gen_leq; try am. ap leq_refl; lu. 
Qed. 


Lemma wo_ordinal_is_ordinal : forall a,
is_well_ordered a -> is_ordinal (wo_ordinal a). 
Proof.
ir. uf wo_ordinal. 
uhg. uf wo_avatar.  
ap lgs_avatar_image. 
apply scale_subset_is_leq_gen_scale with a. 
ap next_compatible_next. am. 
uhg; ee; try am. ap sub_refl. ir. uh H1; ee; am. 
Qed. 

Lemma wo_avatar_ordinal_leq : forall a x y,
is_well_ordered a -> inc x (U a) -> inc y (U a) ->
leq a x y -> ordinal_leq (wo_avatar a x) (wo_avatar a y).
Proof.
ir.  
uf wo_avatar. ap leq_gen_ordinal_leq; try am. 
ap avatar_leq_gen; try am.
ap ID_expansive. rw next_leq_gen_leq; try am. 

Qed. 



Lemma wo_avatar_obi_id : forall o x,
is_ordinal o -> inc x o ->
wo_avatar (obi o) x = x.
Proof.
ir. 
cp (ordinal_obi_next_compatible H). 
uf wo_avatar. 
rewrite<- next_compatible_avatar with (f:=ID). 
ap avatar_refl. 
ap ordinal_leq_gen_refl. 
apply ordinal_inc_ordinal with o; am. am. 
rw obi_U. am. 
Qed. 

Lemma wo_ordinal_obi_rw : forall o,
is_ordinal o -> 
wo_ordinal (obi o) = o.
Proof.
ir. uf wo_ordinal. 
ap extensionality; uhg; ir. 
rwi Image.inc_rw H0. nin H0. 
ee. rwi wo_avatar_obi_id H1. 
wr H1. rwi obi_U H0. am. am. 
rwi obi_U H0; am. 
rw Image.inc_rw. sh x. ee. rw obi_U; am. 
ap wo_avatar_obi_id. am. am. 
Qed. 

(*** thought we needed these for cardinal.v but didn't...
*******************************************************
Lemma wo_avatar_same_order : forall a b x,
is_well_ordered a -> same_order a b -> inc x (U b) ->
wo_avatar a x = wo_avatar b x.
Proof.

Qed. 

Lemma wo_ordinal_same_order : forall a b,
is_well_ordered a -> same_order a b ->
wo_ordinal a = wo_ordinal b.
Proof.

Qed. 

Lemma obi_suborder_same_order : forall o u,
is_ordinal o -> sub u o -> 
same_order (obi u) (suborder u (obi o)).
Proof.

Qed. 
***********************************************)


Lemma wo_leq_rw : forall a x y,
is_well_ordered a -> inc x (U a) -> inc y (U a) ->
leq a x y = ordinal_leq (wo_avatar a x) (wo_avatar a y).
Proof.
ir. ap iff_eq; ir. 
ap wo_avatar_ordinal_leq; try am. cp H. 
uh H; ee. uh H; ee.
cp (H5 _ _ H0 H1). nin H6. am. 
assert (ordinal_leq (wo_avatar a y) (wo_avatar a x)). 
ap wo_avatar_ordinal_leq; try am. 
uh H2. uh H7. ee. assert (x = y). 
util (wo_avatar_injective (a:=a)). am. 
uh H12; ee. uh H13. ap H13. am. am. 
ap extensionality; am. rw H12. ap leq_refl; try am; try lu. 
Qed.  
 


Lemma wo_lt_rw : forall a x y,
is_well_ordered a -> inc x (U a) -> inc y (U a) ->
lt a x y = ordinal_lt (wo_avatar a x) (wo_avatar a y).
Proof.
ir. ap iff_eq; ir. uhg; ee. wr wo_leq_rw. uh H2; ee; am. am. 
am. am. uhg; ir. uh H2; ee. ap H4. 
util (wo_avatar_injective (a:= a)). am. 
uh H5; ee. ap H6. am. am. am. uhg; ee. 
rw wo_leq_rw. uh H2; ee; am. am. am. am. 
uhg; ir. uh H2. ee. ap H4. rw H3; tv. 
Qed.


Lemma wo_punctured_downward : forall a x,
is_well_ordered a -> inc x (U a) ->
Image.create (punctured_downward_subset a x) (wo_avatar a)
= wo_avatar a x.
Proof. 
ir. rewrite<- chenille_punctured_downward with (f:=next a). 
uf wo_avatar. 
wr avatar_chenille. 
ap ordinal_chenille. 
change (is_ordinal (wo_avatar a x)). 
ap wo_avatar_is_ordinal. am. am. 
ap ID_expansive. 
rw next_leq_gen_leq. ap leq_refl; lu. am. am. am. 
ap next_compatible_next; am. am. 
Qed. 


Lemma suborder_wo_avatar_decreasing : forall u a x,
is_well_ordered a -> sub u (U a) -> inc x u ->
ordinal_leq (wo_avatar (suborder u a) x) (wo_avatar a x).
Proof.
ir. 
set (b:=suborder u a). 
assert (lem1: U b = u). 
uf b; rw underlying_suborder; tv. 
assert (lem2 : is_well_ordered b). 
uf b; ap suborder_well_ordered. am. am. 

util (wo_induction  lem2
(p:= fun y=>
(ordinal_leq (wo_avatar b y) (wo_avatar a y)))).
ir. 
uhg; ee. ap wo_avatar_is_ordinal. am.  am. 
ap wo_avatar_is_ordinal. am. 
ap H0. wr lem1; am. 
uhg; ir. 
wri wo_punctured_downward H4. 
rwi Image.inc_rw H4. nin H4. ee. 
ufi punctured_downward_subset H4. Ztac. 
cp (H3 _ H6 H7). 
rwi H5 H8. 
assert (lt a x2 x0). 
uh H7. uhg; ee; try am. 
ufi b H7. 
rwi leq_suborder_all H7. ee. am. lu. am. 
assert (ordinal_lt x1 (wo_avatar a x0)). 
uhg; ee. 
uhg; ee. uh H8; ee; am. ap wo_avatar_is_ordinal. 
am. ap H0. wr lem1; am. 
apply sub_trans with (wo_avatar a x2). 
uh H8; ee; am. 
uh H9; ee. rwi wo_leq_rw H9. 
lu. am. ap H0; wr lem1; am. lu. uhg; ir. 
rwi wo_lt_rw H9. uh H9; ee. ap H11. 
ap extensionality. lu. wr H10. lu. 
am. ap H0; wr lem1; am. 
ap H0; wr lem1; am. 
rwi ordinal_lt_rw H10. ee; am. am. am. 
wri lem1 H1. cp (H2 _ H1). am. 
Qed.  

Lemma ordinal_saturated : forall a b c,
is_ordinal c -> inc b c  -> ordinal_leq a b ->
inc a c.
Proof. 
ir. assert (ordinal_lt a c). 
uhg; ee. uhg; ee. lu. am. 
uh H1. ee. rwi ordinal_inc_rw H0. ee. 
uh H4. ee. apply sub_trans with b; am. am. 
uhg; ir. uh H1; ee. rwi H2 H4. 
apply ordinal_not_inc_itself with b. am. ap H4; am. 
rwi ordinal_lt_rw H2. ee; am.  
Qed. 

Lemma wo_avatar_ordinal_inc : forall a x,
is_well_ordered a -> inc x (U a) ->
inc (wo_avatar a x) (wo_ordinal a).
Proof.
ir. 
uf wo_ordinal. 
rw Image.inc_rw. 
sh x; ee; try am; try tv. 
Qed. 

Lemma suborder_wo_ordinal_decreasing : forall u a,
is_well_ordered a -> sub u (U a)-> 
ordinal_leq (wo_ordinal (suborder u a)) (wo_ordinal a).
Proof.
ir. 
uhg; ee. ap wo_ordinal_is_ordinal. 
ap suborder_well_ordered; am. 
ap wo_ordinal_is_ordinal; am. 
uhg; ir. ufi wo_ordinal H1. 
rwi Image.inc_rw H1. nin H1. 
ee. wr H2. 
apply ordinal_saturated with (wo_avatar a x0). 
ap wo_ordinal_is_ordinal. am. 
ap wo_avatar_ordinal_inc. am. 
ap H0. rwi underlying_suborder H1. am. 
ap suborder_wo_avatar_decreasing. am. am. 
rwi underlying_suborder H1. am. 
Qed. 
 

End Ordinal. 





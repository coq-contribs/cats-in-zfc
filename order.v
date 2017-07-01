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


(*** file order.v, version of november 10th, 2003---Carlos Simpson ***)

 
Require Export universe. 

Set Implicit Arguments.
Unset Strict Implicit. 



Module Order_notation.
Import Universe.


Definition Less_Than := R (l_(t_(h_ DOT))).


Definition less_than (x a b : E) := V a (V b (V Less_Than x)).

Definition leq (x a b : E) :=
  A (inc a (U x)) (A (inc b (U x)) (nonempty (less_than x a b))).

Definition lt (a x y : E) := A (leq a x y) (x <> y).

Section Construction.
Variables (x : E) (lq : E2P). 


Definition create :=
denote Underlying x (
denote Less_Than (binary x lq) 
stop). 



Lemma inc_create_u : forall u, 
Universe.axioms u -> inc x u -> inc create u.
Proof.
ir. uf create. 
app inc_denote_u. 
incdu. incdu. app inc_binary_u. 
ir. app inc_a_prop_u. drw_solve. 
Qed. 

Lemma underlying_create : U create = x. 
ir; uf U; uf create. drw. 
Qed. 

Lemma less_than_rw :
 forall a b : E, inc a x -> inc b x -> less_than create a b = lq a b.
ir; uf less_than; uf create. 
drw. aw. 
Qed.


Lemma leq_create :
 forall a b : E, inc a x -> inc b x -> leq create a b = lq a b.
ir. uf leq.
rw less_than_rw.
ap iff_eq; ir. ee. nin H3. exact (B H3). 
rw underlying_create. ee. am. am.
sh (R H1). 
ap R_inc. am. am. 
Qed.

Lemma leq_create_all :
 forall a b : E, leq create a b = A (inc a x) (A (inc b x) (lq a b)).
ir. ap iff_eq. 
uf leq. rw underlying_create. ir; ee. am. am.
rwi less_than_rw H1. nin H1. exact (B H1). am.
am. ir. rw leq_create; ee; am. 
Qed.


End Construction. 



Definition like (a : E) := a = create (U a) (leq a).

Lemma create_like : forall a : E, like (create (U a) (leq a)). 
ir. 
uf like. 
assert (U (create (U a) (leq a)) = U a). 
ap underlying_create. rw H. 
assert (leq (create (U a) (leq a)) = leq a). 
ap arrow_extensionality; ir. 
ap arrow_extensionality; ir. 
ap iff_eq; ir. rwi leq_create_all H0; ee; am. 
ufi leq H0. ee. rw leq_create_all; ee. am. 
am. uf leq; ee; am. 
rw H0. tv. 
Qed. 

Ltac cluc :=
  match goal with
  | id1:?X1 |- _ => rwi underlying_create id1; cluc
  |  |- ?X1 => rw underlying_create
  | _ => idtac
  end.

Lemma leq_create_then :
 forall (a : E) (l : E2P) (x y : E),
 leq (create a l) x y -> A (inc x a) (A (inc y a) (l x y)).
ir. rwi leq_create_all H. am. Qed.



Lemma leq_create_if :
 forall (a : E) (l : E2P) (x y : E),
 inc x a -> inc y a -> l x y -> leq (create a l) x y.
ir. rw leq_create; am. 
Qed. 


End Order_notation.





Module Order.
Import Universe.

Module Definitions. 
Export Order_notation.



Definition property (a : E) (l : E2P) :=
  A (forall x : E, inc x a -> l x x)
    (A (forall x y : E, inc x a -> inc y a -> l x y -> l y x -> x = y)
       (forall x y z : E,
        inc x a -> inc y a -> inc z a -> l x y -> l y z -> l x z)).

Definition axioms (a : E) :=
  A (forall x : E, inc x (U a) -> leq a x x)
    (A (forall x y : E, leq a x y -> inc x (U a))
       (A (forall x y : E, leq a x y -> inc y (U a))
          (A (forall x y : E, leq a x y -> leq a y x -> x = y)
             (forall x y z : E, leq a x y -> leq a y z -> leq a x z)))).

Lemma create_axioms :
 forall (a : E) (l : E2P), property a l -> axioms (create a l).
ir. uf axioms. dj. cluc. ap leq_create_if; try am. ufi property H.
ee. ap H; am. ufi leq H1. xe. ufi leq H2; xe. assert (inc x a).
lapply (H1 x y). ir. cluc. am. am. assert (inc y a).
lapply (H2 x y). ir; cluc; am. am. ufi property H; ee.
ap H7. am. am. rwi leq_create_all H3; xe. rwi leq_create_all H4; xe.
assert (inc x a). lapply (H1 x y); ir. cluc; am. am.
assert (inc y a). lapply (H2 x y). ir. cluc; am. am.
assert (inc z a). lapply (H2 y z); ir. cluc; am. am.
ufi property H; ee. ap leq_create_if. am. am. apply H10 with y.
am. am. am. rwi leq_create_all H4; xe. rwi leq_create_all H5; xe.
Qed. 





Lemma lt_leq_trans :
 forall a x y z : E, axioms a -> lt a x y -> leq a y z -> lt a x z.
ir. uf lt; ufi lt H0; ee. ufi axioms H; ee.
apply H6 with y; au. uf not; ir. rwi H3 H0.
ufi axioms H; ee. ap H2. rw H3. ap H6; au.
Qed.

Lemma leq_lt_trans :
 forall a x y z : E, axioms a -> leq a x y -> lt a y z -> lt a x z.
ir. uf lt; ufi lt H1; ee. ufi axioms H; ee.
apply H6 with y; au. uf not; ir. ap H2. wr H3.
wri H3 H1. ufi axioms H; ee. ap H6. exact H1. exact H0.
Qed.




Lemma leq_refl : forall a x : E, axioms a -> inc x (U a) -> leq a x x.
ir. ufi axioms H; xe. ap H; am.
Qed.

Lemma leq_trans :
 forall a x y z : E, axioms a -> leq a x y -> leq a y z -> leq a x z.
ir. ufi axioms H; ee. apply H5 with y. exact H0. exact H1.
Qed. 

Lemma leq_leq_eq :
 forall a x y : E, axioms a -> leq a x y -> leq a y x -> x = y.
intros.
unfold axioms in H; xe. ap H4; am.
Qed.



Lemma no_lt_leq :
 forall a x y : E, axioms a -> lt a x y -> leq a y x -> False.
ir. ufi axioms H; ufi lt H0; xe. ap H2; ap H5; am.
Qed. 

Lemma leq_eq_or_lt :
 forall a x y : E, axioms a -> leq a x y -> x = y \/ lt a x y.
ir. apply by_cases with (x = y). ir. ap or_introl; am.
ir. ap or_intror. uf lt; xe.
Qed. 

End Definitions.
Export Definitions. 

Module SetOfOrders.

Section orders_on_section. 
Variable x : E. 

Definition is_order_on (a : E) := A (axioms a) (A (U a = x) (like a)). 

Definition little_leq (lq : x -> x -> Prop) (u v : E) :=
  A (inc u x)
    (A (inc v x) (forall (hu : inc u x) (hv : inc v x), lq (B hu) (B hv))).

Definition lit_lq (a : E) (m n : x) := leq a (R m) (R n).

Lemma create_little_leq :
 forall a : E, is_order_on a -> a = create x (little_leq (lit_lq a)).
ir. 
assert (leq a = little_leq (lit_lq a)).
ap arrow_extensionality; intro u. 
ap arrow_extensionality; intro v. 
ap iff_eq; ir. ufk leq H0; ee. 
ufk is_order_on H; ee. 
uhg; ee. wr H3; am. wr H3; am. 
ir. uhg. rw B_eq. rw B_eq. am. 
ufi little_leq H0; ee. 
cp (H2 H0 H1).  ufi lit_lq H3. 
rwi B_eq H3. rwi B_eq H3. am. 

wr H0. uh H. ee. wr H1. 
exact H2. 
Qed. 


Lemma is_order_bounded : Bounded.axioms is_order_on. 
ir. 
apply
 Bounded.little_criterion
  with (x -> x -> Prop) (fun lq : x -> x -> Prop => create x (little_leq lq)). 
ir. sh (lit_lq y).
sy; ap create_little_leq. am. 
Qed. 

Definition orders_on := Bounded.create is_order_on. 
 


Lemma inc_orders_on : forall a : E, inc a orders_on = is_order_on a. 
ir. 
uf orders_on. 
ap Bounded.inc_create. 
ap is_order_bounded. 
Qed.

End orders_on_section.


End SetOfOrders. Export SetOfOrders. 


Module Morphisms. 


Definition mor_axioms (u : E) :=
  A (axioms (source u))
    (A (axioms (target u))
       (A (strong_axioms u)
          (forall x y : E,
           leq (source u) x y -> leq (target u) (ev u x) (ev u y)))).

Lemma mor_Umor : forall u : E, mor_axioms u -> strong_axioms u.
intros. unfold mor_axioms in H; ee. exact H1. 
Qed. 
Coercion mor_Umor_C := mor_Umor.

Lemma identity_axioms : forall a : E, axioms a -> mor_axioms (identity a).
ir. cx. uf mor_axioms; ee; clst. am. am.
ap identity_strong_axioms. ir. rw ev_identity. rw ev_identity.
am. 
lu. lu. 
Qed. 


Definition composable (u v : E) :=
  A (mor_axioms u) (A (mor_axioms v) (source u = target v)).

Lemma compose_axioms :
 forall u v : E, composable u v -> mor_axioms (compose u v).
intros.
unfold composable in H; ee.
unfold mor_axioms in H; ee.
unfold mor_axioms in H0; ee.
unfold mor_axioms in |- *; ee.
rewrite source_compose; au.

rewrite target_compose; au.

apply compose_strong_axioms.
unfold Umorphism.composable in |- *; ee.
apply axioms_from_strong; am.
apply axioms_from_strong; am.

am.

intros.
rewrite target_compose.
rewrite ev_compose.
rewrite ev_compose.
rewrite source_compose in H8.
apply H4.
rewrite H1.
apply H7.
am.

unfold axioms in H0; ee.
rewrite source_compose in H8.
lu.  

rewrite source_compose in H8.
unfold axioms in H0; ee.
lu. 
Qed.

End Morphisms. Export Morphisms. 

Module Suborders. 

Definition suborder (b a : E) := Order_notation.create b (leq a).

Lemma suborder_axioms :
 forall a b : E, axioms a -> sub b (U a) -> axioms (suborder b a).
intros.
unfold suborder in |- *.
apply create_axioms.
unfold property in |- *.
unfold axioms in H.
ee. ir; au.
ir. ap H3. exact H7. exact H8.
intros.
apply H4 with y; au.
Qed.

Lemma underlying_suborder : forall a b : E, U (suborder b a) = b.
intros.
unfold suborder in |- *; rewrite underlying_create; tv.
Qed. 

Lemma leq_suborder_if :
 forall a b x y : E,
 inc x b -> inc y b -> sub b (U a) -> leq a x y -> leq (suborder b a) x y.
intros.
unfold suborder in |- *.
apply leq_create_if; au.
Qed.

Lemma leq_suborder_then :
 forall a b x y : E,
 axioms a ->
 sub b (U a) ->
 leq (suborder b a) x y -> A (inc x b) (A (inc y b) (leq a x y)).
intros.
ee.
unfold suborder in H1.
pose (leq_create_then H1).
ee; am.

unfold suborder in H1.
pose (leq_create_then H1); ee; am.

unfold suborder in H1.
pose (leq_create_then H1); ee; am.
Qed.



Lemma leq_suborder_all :
 forall a b x y : E,
 axioms a ->
 sub b (U a) ->
 leq (suborder b a) x y = A (inc x b) (A (inc y b) (leq a x y)).
intros.
apply iff_eq; intros.
pose (leq_suborder_then H H0 H1).
ee; am.

apply leq_suborder_if; ee; am.
Qed.


Definition suborder_inclusion (b a : E) := inclusion (suborder b a) a.

Lemma suborder_inclusion_mor_axioms :
 forall a b : E,
 axioms a -> sub b (U a) -> mor_axioms (suborder_inclusion b a).
intros.
unfold suborder_inclusion in |- *.
unfold mor_axioms in |- *; ee.
unfold inclusion in |- *; rewrite source_create.
apply suborder_axioms; au.

unfold inclusion in |- *; rewrite target_create.
am.

unfold inclusion in |- *.
apply create_strong_axioms.
unfold Umorphism.property in |- *.
unfold Transformation.axioms in |- *.
intros.
rewrite underlying_suborder in H1.
apply H0; au.

intros.
unfold inclusion in |- *.
rewrite target_create.
repeat rewrite ev_create.
unfold inclusion in H1; rewrite source_create in H1.
rewrite leq_suborder_all in H1.
ee.

am.

am. am.

unfold inclusion in H1; rewrite source_create in H1.
rewrite leq_suborder_all in H1; au.
ee.
rewrite underlying_suborder; am.

unfold inclusion in H1; rewrite source_create in H1.
rewrite leq_suborder_all in H1; au.
ee.
rewrite underlying_suborder; au.
Qed.


Definition is_suborder (a b : E) :=
  A (axioms a)
    (A (axioms b) (A (sub (U a) (U b)) (mor_axioms (inclusion a b)))).

Lemma is_suborder_leq :
 forall a b x y : E, is_suborder a b -> leq a x y -> leq b x y.
ir.
ufi is_suborder H.
ee.
ufi mor_axioms H3; ee.
assert (b = target (inclusion a b)).
uf inclusion; rw target_create.
tv.

rw H7.
assert (x = ev (inclusion a b) x).
uf inclusion; rw ev_create; tv.
ufi leq H0.
ee.
am.

assert (y = ev (inclusion a b) y).
uf inclusion; rw ev_create; tv.
ufi leq H0; xe.

rw H8; rw H9.
ap H6.
uf inclusion; rw source_create; am.
Qed. 

Lemma show_is_suborder :
 forall a b : E,
 axioms a ->
 axioms b -> (forall x y : E, leq a x y -> leq b x y) -> is_suborder a b.
ir. uf is_suborder; ee. am. am. uf sub; ir. assert (leq b x x).
ap H1. ap leq_refl; am. ufi leq H3; xe. uf inclusion. uf mor_axioms. rw source_create.
rw target_create. ee. am. am. ap create_strong_axioms.
uf Umorphism.property. uf Transformation.axioms. ir. assert (leq b x x).
ap H1. ap leq_refl; am. ufi leq H3; xe. ir. rw ev_create.
rw ev_create. ap H1; am. ufi leq H2; xe. ufi leq H2; xe.
Qed. 

(*** note that this doesn't imply that the order on (U a) is the same as that induced by the
order on (U b) ****)

Lemma suborder_is_suborder :
 forall a b : E, axioms a -> sub b (U a) -> is_suborder (suborder b a) a.
ir. uf is_suborder. ee. ap suborder_axioms; am. uf suborder. am. uf suborder.
rw underlying_create. am.
change (mor_axioms (suborder_inclusion b a)) in |- *. ap suborder_inclusion_mor_axioms; am.
Qed.

Lemma is_suborder_refl : forall a : E, axioms a -> is_suborder a a.
ir. uf is_suborder; dj. am. am. uf sub; ir; am. uf mor_axioms; dj.
uf inclusion; rw source_create. am. uf inclusion; rw target_create; am.
uf inclusion; ap create_strong_axioms. uf Umorphism.property. uf Transformation.axioms; ir; am.
uf inclusion; rw ev_create. rw ev_create. rw target_create. ufi inclusion H6. rwi source_create H6. am.
ufi inclusion H6; rwi source_create H6. ufi leq H6; ee. am. ufi inclusion H6; rwi source_create H6.
ufi leq H6; ee; am.
Qed.

Lemma is_suborder_trans :
 forall a b c : E, is_suborder a b -> is_suborder b c -> is_suborder a c.
ir. ap show_is_suborder. ufi is_suborder H; xe. ufi is_suborder H0; xe.
ir. apply is_suborder_leq with b. am. apply is_suborder_leq with a.
exact H. exact H1.
Qed. 

Definition same_order (a b : E) := A (is_suborder a b) (is_suborder b a).

Lemma same_order_refl : forall a : E, axioms a -> same_order a a.
ir. uf same_order; ee. ap is_suborder_refl. am. ap is_suborder_refl; am.
Qed.

Lemma same_order_symm : forall a b : E, same_order a b -> same_order b a.
ir. ufi same_order H. uf same_order. ee. am. exact H.
Qed.

Lemma same_order_trans :
 forall a b c : E, same_order a b -> same_order b c -> same_order a c.
ir. ufi same_order H. ufi same_order H0. uf same_order. ee. apply is_suborder_trans with b.
exact H. exact H0. apply is_suborder_trans with b. exact H1. exact H2.
Qed.


Lemma same_underlying : forall a b : E, same_order a b -> U a = U b.
ir.
ufi same_order H; ee.
ufi is_suborder H.
ufi is_suborder H0.
ee.
ap extensionality.
am.

am.
Qed. 

Lemma same_leq_eq :
 forall a b x y : E, same_order a b -> leq a x y = leq b x y.
ir.
ap iff_eq; ir.
ufi same_order H.
ee.
apply is_suborder_leq with a; am.

ufi same_order H; ee.
apply is_suborder_leq with b; am.
Qed.  

Lemma same_order_extens :
 forall a b : E, same_order a b -> like a -> like b -> a = b. 
ir. assert (U a = U b). ap same_underlying; am. 
assert (leq a = leq b). ap arrow_extensionality. 
ir. ap arrow_extensionality. ir. 
ap same_leq_eq. am. uh H0. rw H0. rw H2. 
rw H3. sy. exact H1. 
Qed. 

Lemma same_as_suborder_is_suborder :
 forall a b x : E,
 sub x (U b) -> axioms b -> same_order a (suborder x b) -> is_suborder a b.
ir. apply is_suborder_trans with (suborder x b). ufi same_order H1; ee.
exact H1. ap suborder_is_suborder. exact H0. am.
Qed. 


Lemma suborder_trans :
 forall a b c : E,
 axioms c ->
 sub a b ->
 sub b (U c) -> same_order (suborder a (suborder b c)) (suborder a c).
ir. uf same_order; ee; ap show_is_suborder. ap suborder_axioms. ap suborder_axioms.
am. am. uf suborder; rw underlying_create. am. ap suborder_axioms. am. uf sub; ir; au.
ir. ap leq_suborder_if. rwi leq_suborder_all H2. ee; am. ap suborder_axioms; am.
uf suborder; rw underlying_create. am. rwi leq_suborder_all H2; ee. am.
ap suborder_axioms; am. uf suborder; rw underlying_create. am. uf sub; ir; au.
rwi leq_suborder_all H2; ee. rwi leq_suborder_all H4; ee. am. am. am. ap suborder_axioms; am.
uf suborder; rw underlying_create; uf sub; ir; au. ap suborder_axioms. am.
uf sub; ir; au. ap suborder_axioms. ap suborder_axioms; am. uf suborder; rw underlying_create.
am. ir. rwi leq_suborder_all H2; ee. ap leq_suborder_if; au. uf suborder; rw underlying_create; am.
ap leq_suborder_if. au. au. am. am. am. uf sub; ir; au.
Qed.



End Suborders. Export Suborders. 


Module Linear.


Definition is_linear (a : E) :=
  A (axioms a)
    (forall x y : E, inc x (U a) -> inc y (U a) -> leq a x y \/ leq a y x).

Lemma linear_axioms : forall a : E, is_linear a -> axioms a.
intros. unfold is_linear in H; ee; am. Qed.
Coercion linear_axioms_C := linear_axioms.

Lemma linear_not_lt_leq :
 forall a x y : E,
 is_linear a ->
 inc x (U a) -> inc y (U a) -> (lt a x y -> False) -> leq a y x.
intros.
unfold is_linear in H; ee.
pose (H3 _ _ H0 H1).
induction o.
pose (leq_eq_or_lt H H4).
induction o.
rewrite H5.
unfold axioms in H; ee. ap H; am.

elim (H2 H5).

am.
Qed.

Lemma injective_lt_lt :
 forall u x y : E,
 mor_axioms u ->
 injective u ->
 lt (source u) x y -> lt (target u) (ev u x) (ev u y).
ir.
ufi lt H1. uf lt; ee. ufi mor_axioms H; xe.
ap H5. am. uf not; intros. ufi injective H0; ee.
ufi Transformation.injective H4. ee. ufi Transformation.injects H5.
ap H2. ap H5. ufi mor_axioms H; ee. ufi axioms H; ee.
apply H9 with y. am. ufi mor_axioms H; ee.
ufi axioms H; ee. apply H10 with x; au. am.
Qed. 

Lemma linear_injective_leq_back :
 forall u x y : E,
 mor_axioms u ->
 injective u ->
 is_linear (source u) ->
 inc x (U (source u)) ->
 inc y (U (source u)) ->
 leq (target u) (ev u x) (ev u y) -> leq (source u) x y.
intros.
apply linear_not_lt_leq; au.
intros.
pose (injective_lt_lt H H0 H5).
apply no_lt_leq with (target u) (ev u y) (ev u x).
assert (mor_axioms u).
am.

unfold mor_axioms in H6; ee.

am.

am.

am.
Qed. 

Lemma linear_injective_lt_back :
 forall u x y : E,
 mor_axioms u ->
 injective u ->
 is_linear (source u) ->
 inc x (U (source u)) ->
 inc y (U (source u)) ->
 lt (target u) (ev u x) (ev u y) -> lt (source u) x y.
intros.
unfold lt in H4.
unfold lt in |- *; ee.
apply linear_injective_leq_back; au.

unfold not in |- *; intros.
apply H5.
rewrite H6; tv.
Qed. 


Definition is_linear_subset (a b : E) :=
  A (axioms a) (A (sub b (U a)) (is_linear (suborder b a))).

Lemma linear_sub :
 forall a b c : E, is_linear_subset a b -> sub c b -> is_linear_subset a c.
ir.
ufi is_linear_subset H; uf is_linear_subset; dj; ee.
am.

uf sub; ir; au.

ufi is_linear H4; uf is_linear; dj; ee.
ap suborder_axioms; am.

assert (inc x (U (suborder b a))).
rw underlying_suborder.
ap H0.
rwi underlying_suborder H6.
am.

assert (inc y (U (suborder b a))).
rw underlying_suborder.
ap H0.
rwi underlying_suborder H7; am.

cp (H8 x y H9 H10).
nin H11.
ap or_introl.
rwi underlying_suborder H6.
rwi underlying_suborder H7.
ap leq_suborder_if; try am.
rwi leq_suborder_all H11; ee.
am.

am.

am.

ap or_intror.
rwi underlying_suborder H6.
rwi underlying_suborder H7.
rw leq_suborder_all.
rwi leq_suborder_all H11.
xd.

am.

am.

am.

am.
Qed. 

End Linear. Export Linear. 

Module Bounds. 


Definition is_minimal (a b x : E) :=
  A (axioms a)
    (A (sub b (U a))
       (A (inc x b) (forall y : E, inc y b -> leq a y x -> y = x))).

Lemma minimal_axioms : forall a b x : E, is_minimal a b x -> axioms a.
intros. unfold is_minimal in H; ee; am. Qed.
Coercion minimal_axioms_C := minimal_axioms.


Definition is_maximal (a b x : E) :=
  A (axioms a)
    (A (sub b (U a))
       (A (inc x b) (forall y : E, inc y b -> leq a x y -> x = y))).

Lemma maximal_axioms : forall a b x : E, is_maximal a b x -> axioms a.
intros. unfold is_maximal in H; ee; am. Qed.
Coercion maximal_axioms_C := maximal_axioms.



Definition is_upper_bound (a b x : E) :=
  A (axioms a)
    (A (sub b (U a)) (A (inc x (U a)) (forall y : E, inc y b -> leq a y x))).

Lemma upper_bound_axioms : forall a b x : E, is_upper_bound a b x -> axioms a.
intros. unfold is_upper_bound in H; ee; am. Qed.
Coercion upper_bound_axiomsC := upper_bound_axioms.

Definition is_lower_bound (a b x : E) :=
  A (axioms a)
    (A (sub b (U a)) (A (inc x (U a)) (forall y : E, inc y b -> leq a x y))).

Lemma lower_bound_axioms : forall a b x : E, is_lower_bound a b x -> axioms a.
intros. unfold is_lower_bound in H; ee; am. Qed.
Coercion lower_bound_axiomsC := lower_bound_axioms.



Definition is_bottom_element (a b x : E) :=
  A (is_lower_bound a b x) (inc x b). 

Lemma bottom_element_lower_bound :
 forall a b x : E, is_bottom_element a b x -> is_lower_bound a b x.
intros. unfold is_bottom_element in H; ee; am. Qed.
Coercion bottom_element_lower_boundC := bottom_element_lower_bound.

Definition is_top_element (a b x : E) := A (is_upper_bound a b x) (inc x b).

Lemma top_element_upper_bound :
 forall a b x : E, is_top_element a b x -> is_upper_bound a b x.
intros. unfold is_top_element in H; ee; am. Qed.
Coercion top_element_upper_boundC := top_element_upper_bound.



Lemma top_element_maximal :
 forall a b x : E, is_top_element a b x -> is_maximal a b x.
intros. unfold is_top_element in H. unfold is_upper_bound in H. unfold is_maximal in |- *.
ee. intros. am. am. am. ir. ufi axioms H; ee. ap H8. am. ap H3; am.
Qed. 

Coercion top_element_maximalC := top_element_maximal. 

Lemma bottom_element_minimal :
 forall a b x : E, is_bottom_element a b x -> is_minimal a b x.
intros. unfold is_bottom_element in H. unfold is_lower_bound in H. unfold is_minimal in |- *.
xe. intros. unfold axioms in H; xe. ap H8. am. ap H3. am. 
Qed. 

Coercion bottom_element_minimalC := bottom_element_minimal.

Lemma top_element_unique :
 forall a b x y : E, is_top_element a b x -> is_top_element a b y -> x = y.
intros. unfold is_top_element in H, H0; xe. unfold is_upper_bound in H, H0; xe. unfold axioms in H; xe. ap H11.
ap H6; am.

ap H8; am.
Qed. 

Lemma bottom_element_unique :
 forall a b x y : E,
 is_bottom_element a b x -> is_bottom_element a b y -> x = y.
intros. unfold is_bottom_element in H, H0; xe. unfold is_lower_bound in H, H0; xe. unfold axioms in H; xe. ap H11.
ap H8; am.

ap H6; am.
Qed. 

Lemma linear_maximal_top_element :
 forall a b x : E, is_linear a -> is_maximal a b x -> is_top_element a b x.
intros. unfold is_linear in H. unfold is_maximal in H0. 
unfold is_top_element in |- *. unfold is_upper_bound in |- *. xd. intros. 
assert (inc x (U a)). apply H1; au. assert (inc y (U a)). apply H1; au. 
pose (H2 _ _ H6 H7). induction o. uh H. ee. 
 assert (x = y). 
apply H4; au. rewrite H13. ap H; am.  am. 
Qed.

Lemma linear_minimal_bottom_element :
 forall a b x : E, is_linear a -> is_minimal a b x -> is_bottom_element a b x.
intros. unfold is_linear in H. unfold is_minimal in H0. 
unfold is_bottom_element in |- *. unfold is_lower_bound in |- *. xd. intros. 
assert (inc x (U a)). apply H1; au. assert (inc y (U a)). apply H1; au. 
pose (H2 _ _ H6 H7). induction o. unfold axioms in H; xe. assert (y = x). 
apply H4; au. rewrite H9.  unfold axioms in H; ee.  ap H. am. 
Qed.


Definition downward_subset (a x : E) := Z (U a) (fun y : E => leq a y x).

Definition punctured_downward_subset (a x : E) :=
  Z (U a) (fun y : E => lt a y x).

Definition downward_suborder (a x : E) := suborder (downward_subset a x) a.

Definition punctured_downward_suborder (a x : E) :=
  suborder (punctured_downward_subset a x) a.




End Bounds. Export Bounds. 

Module WellOrdered. 


Definition is_well_ordered (a : E) :=
  A (is_linear a)
    (forall b : E,
     sub b (U a) ->
     nonempty b -> ex (fun x : E => is_bottom_element a b x)).

Lemma wo_linear : forall a : E, is_well_ordered a -> is_linear a.
intros. unfold is_well_ordered in H; xe. Qed.
Coercion wo_linear_C := wo_linear.







Lemma bottom_element_no_lt :
 forall a b x y : E, is_bottom_element a b x -> lt a y x -> inc y b -> False.
intros.
unfold is_bottom_element in H; ee.
unfold is_lower_bound in H; ee.
assert (leq a x y).
apply H5; am.
apply no_lt_leq with a y x; au.
Qed.




Definition choose_bottom_element (a b : E) :=
  choose (fun x : E => is_bottom_element a b x).

Lemma wo_choose_bottom :
 forall a b : E,
 is_well_ordered a ->
 sub b (U a) ->
 nonempty b -> is_bottom_element a b (choose_bottom_element a b).
intros.
unfold is_well_ordered in H; ee.
pose (H2 b H0 H1).
pose (choose_pr e).
am.
Qed.

Lemma wo_induction :
 forall (a : E) (H : is_well_ordered a) (p : EP),
 (forall x : E,
  inc x (U a) -> (forall y : E, inc y (U a) -> lt a y x -> p y) -> p x) ->
 forall x : E, inc x (U a) -> p x.
ir.
set (b := Z (U a) (fun z : E => ~ p z)). ap excluded_middle; uf not; ir.
assert (nonempty b). apply nonempty_intro with x. uf b.
Ztac. set (z := choose_bottom_element a b).
assert (is_bottom_element a b z). uf z; ap wo_choose_bottom.
am. uf b; ap Z_sub. am. assert (sub b (U a)). uf b; ap Z_sub.
assert (inc z b). ufi is_bottom_element H4; ee.
assert (inc z (U a)). ap H5; am. am. assert (~ p z).
ufi b H6. Ztac. ap H7. ap H0; ir. au. ap excluded_middle; uf not; ir. assert (inc y b). uf b; Ztac.
apply bottom_element_no_lt with a b z y; au.
Qed.



Definition is_wo_subset (a b : E) :=
  A (is_linear_subset a b) (is_well_ordered (suborder b a)).





Lemma wo_same_order :
 forall a b : E, same_order a b -> is_well_ordered a -> is_well_ordered b.
ir. uhg; dj. uhg; dj. 
ufi same_order H; ee. 
ufi is_suborder H; ee. 
am. assert (leq b x y = leq a x y).
sy; ap same_leq_eq. am. assert (leq b y x = leq a y x). sy; ap same_leq_eq; am.
rw H4. rw H5. uh H0. ee. uh H0; ee. ap H7. assert (U a = U b). ap same_underlying.
am. rw H8; am. assert (U a = U b). ap same_underlying; am. rw H8; am.
assert (U a = U b). ap same_underlying; am. assert (sub b0 (U a)). rw H4; am.
uh H0; ee. cp (H6 _ H5 H3). nin H7. sh x. uhg; ee. uhg; ee. uh H; ee. ufi is_suborder H; ee.
am. am. uh H7; ee. ap H2; am. ir. assert (leq b x y = leq a x y). sy. ap same_leq_eq.
am. rw H9. uh H7. ee. uh H7. ee. ap H13. am. uh H7. ee. am.
Qed. 





(*** a scale is a morphism between well ordered subsets that starts at the bottom and is injective with no gaps ***)

Definition is_scale (u : E) :=
  A (mor_axioms u)
    (A (injective u)
       (A (is_well_ordered (source u))
          (A (is_well_ordered (target u))
             (forall x y : E,
              inc x (U (source u)) ->
              leq (target u) y (ev u x) ->
              ex
                (fun z : E => A (inc z (U (source u))) (ev u z = y)))))).

Lemma scale_mor_axioms : forall u : E, is_scale u -> mor_axioms u.
intros. unfold is_scale in H; ee; am. Qed.
Coercion scale_mor_axiomsC := scale_mor_axioms.

Lemma scale_injective : forall u : E, is_scale u -> injective u.
intros. unfold is_scale in H; ee; am. Qed.
Coercion scale_injectiveC := scale_injective.



Lemma scale_leq_back :
 forall u x y : E,
 is_scale u ->
 inc x (U (source u)) ->
 inc y (U (source u)) ->
 leq (target u) (ev u x) (ev u y) -> leq (source u) x y.
intros.
unfold is_scale in H; ee.
unfold is_well_ordered in H4; ee.
apply linear_injective_leq_back; au.
Qed.


Lemma scale_lt_back :
 forall u x y : E,
 is_scale u ->
 inc x (U (source u)) ->
 inc y (U (source u)) ->
 lt (target u) (ev u x) (ev u y) -> lt (source u) x y.
intros.
unfold is_scale in H; ee.
unfold is_well_ordered in H4; ee.
apply linear_injective_lt_back; au.
Qed.



Lemma scale_leq_ev :
 forall u v x : E,
 is_scale u ->
 is_scale v ->
 source u = source v ->
 target u = target v ->
 inc x (U (source u)) -> leq (target v) (ev u x) (ev v x).
intros.
unfold is_scale in H, H0; ee.
apply
 (wo_induction H9
    (p:=fun w : E => leq (target v) (ev u w) (ev v w))).
intros.
unfold is_well_ordered in H10; ee.
unfold is_linear in H10; ee.
apply linear_not_lt_leq.
unfold is_well_ordered in H7; xe.

unfold mor_axioms in H0; ee.
unfold strong_axioms in H17; ee; unfold Umorphism.axioms in H17.
apply H17.
rewrite <- H1; am.

rewrite <- H2.
unfold mor_axioms in H; ee.
unfold strong_axioms in H17; ee.
ap H17; exact H12.

intros.
unfold lt in H16; ee.
rewrite <- H2 in H16.
pose (H11 _ _ H12 H16).
induction e.
ee.
assert (lt (source u) x1 x0).
apply scale_lt_back.
unfold is_scale in |- *; ee.
am. exact H5. exact H9. 
rewrite H2; am.

am.

am.
am. 
rewrite H19.
unfold lt in |- *; xe.

assert (lt (target v) (ev v x1) (ev v x0)).
apply injective_lt_lt.
am.

am.

rewrite <- H1; am.

assert (leq (target v) (ev u x1) (ev v x1)).
apply H13.
am.

am.

unfold lt in H21; ee.
apply H23.
apply leq_leq_eq with (target v).
wr H2.
am.

exact H21.

wr H19.
exact H22.

exact H3.
Qed.



Lemma scale_same_ev :
 forall u v x : E,
 is_scale u ->
 is_scale v ->
 source u = source v ->
 target u = target v -> inc x (U (source u)) -> ev u x = ev v x.
intros.
apply leq_leq_eq with (target u).
unfold is_scale in H; ee.
unfold mor_axioms in H; xe.

rewrite H2.
apply scale_leq_ev; au.

apply scale_leq_ev; au.
rewrite <- H1; am.
Qed.

Lemma scale_unique :
 forall u v : E,
 is_scale u ->
 is_scale v -> source u = source v -> target u = target v -> u = v.
intros.
apply extens.
unfold is_scale in H; ee.
unfold mor_axioms in H; xe.

unfold is_scale in H0; ee.
unfold mor_axioms in H0; xe.

am.

am.

intros.
apply scale_same_ev; au.
Qed. 

Definition scale_subset (a b : E) :=
  A (is_well_ordered b)
    (A (sub a (U b)) (forall x y : E, inc y a -> leq b x y -> inc x a)).





Lemma source_suborder_inclusion :
 forall a b : E, source (suborder_inclusion a b) = suborder a b.
ir.
uf suborder_inclusion.
uf inclusion; rw source_create.
tv.
Qed.

Lemma target_suborder_inclusion :
 forall a b : E, target (suborder_inclusion a b) = b.
ir.
uf suborder_inclusion.
uf inclusion; rw target_create.
tv.
Qed.

Lemma ev_suborder_inclusion :
 forall a b x : E, inc x a -> ev (suborder_inclusion a b) x = x.
ir.
uf suborder_inclusion.
uf inclusion; rw ev_create.
tv.
rw underlying_suborder; am.
Qed. 

Lemma suborder_well_ordered :
 forall a b : E,
 sub a (U b) -> is_well_ordered b -> is_well_ordered (suborder a b).
ir.
ufk is_well_ordered H0; ee.
ufk is_linear H0; ee.
uf is_well_ordered; dj.
uf is_linear; dj.
ap suborder_axioms; am.

rw leq_suborder_all.
rw leq_suborder_all.
cp (H2 x y).
lapply H6.
ir.
lapply H7; ir.
nin H8.
ap or_introl.
ee.
rwi underlying_suborder H4.
exact H4.

rwi underlying_suborder H5; ap H5.

am.

ap or_intror.
ee.
rwi underlying_suborder H5; ap H5.

rwi underlying_suborder H4; ap H4.

am.

ap H.
rwi underlying_suborder H5; ap H5.

ap H.
rwi underlying_suborder H4; ap H4.

am.

am.

am.

am.

assert (sub b0 (U b)).
uf sub; ir; ap H.
rwi underlying_suborder H4; ap H4.
am.

cp (H1 b0 H6 H5).
nin H7.
sh x.
uf is_bottom_element; dj.
uf is_lower_bound; dj.
ap suborder_axioms.
am.

am.

am.

ap H9.
ufi is_bottom_element H7; ee.
am.

rw leq_suborder_all; dj.
rwi underlying_suborder H9.
ap H9.
ufi is_bottom_element H7; ee.
am.

rwi underlying_suborder H9; ap H9; am.

ufi is_bottom_element H7; ee.
ufi is_lower_bound H7; ee.
ap H17.
am.

am.

am.

ufi is_bottom_element H7; ee; am.
Qed. 


Lemma wo_sub :
 forall a b c : E, is_wo_subset a b -> sub c b -> is_wo_subset a c.
ir. uh H. ee. uhg. dj. apply linear_sub with b. am. am.
apply wo_same_order with (suborder c (suborder b a)). ap suborder_trans.
uh H. ee. am. am. uh H. ee. am. ap suborder_well_ordered. rw underlying_suborder.
am. am.
Qed. 

Lemma wo_sub_bottom :
 forall a b : E,
 is_wo_subset a b ->
 nonempty b -> is_bottom_element a b (choose_bottom_element a b).
ir. assert (ex (fun x : E => is_bottom_element a b x)). uh H; ee.
set (y := choose_bottom_element (suborder b a) b). assert (is_bottom_element (suborder b a) b y).
uf y. ap wo_choose_bottom. am. rw underlying_suborder. uf sub; ir; am. am. sh y.
uh H2. ee. uh H2; ee. uhg. ee. uhg; ee. uh H; ee. am. uh H; ee. am. uh H; ee.
ap H7; am. ir. cp (H6 _ H7). rwi leq_suborder_all H8; ee. am. uh H; ee; am.
uh H; ee; am. am. cp (choose_pr H1). exact H2.
Qed. 

Lemma scale_suborder_inclusion :
 forall a b : E, scale_subset a b -> is_scale (suborder_inclusion a b).
ir.
ufi scale_subset H; ee.
ufk is_well_ordered H.
ee.
ufk is_linear H; ee.
ufk axioms H; ee.
uf is_scale; dj.
ap suborder_inclusion_mor_axioms.
am.

am.

uf injective.
dj.
ufi mor_axioms H8; ee.
ufi strong_axioms H10; ee.
exact H10.

uf Transformation.injective.
rw source_suborder_inclusion.
rw target_suborder_inclusion.
rw underlying_suborder.
dj.
uf Transformation.axioms.
ir.
rw ev_suborder_inclusion.
ap H0; am.

am.

uf Transformation.injects.
ir.
rwi ev_suborder_inclusion H13; try am.
rw H13.
rw ev_suborder_inclusion.
tv.

am.

rw source_suborder_inclusion.
ap suborder_well_ordered.
am.

am.

rw target_suborder_inclusion.
am.

sh y.
dj.
rw source_suborder_inclusion.
rw underlying_suborder.
apply H1 with x.
rwi source_suborder_inclusion H12.
rwi underlying_suborder H12.
exact H12.

rwi target_suborder_inclusion H13.
rwi ev_suborder_inclusion H13.
exact H13.

rwi source_suborder_inclusion H12.
rwi underlying_suborder H12.
exact H12.

rw ev_suborder_inclusion.
tv.

rwi source_suborder_inclusion H14.
rwi underlying_suborder H14.
exact H14.
Qed.


(*
Lemma empty_scale_subset : (a:E)(is_well_ordered a) -> (scale_subset emptyset a).

Qed.

Lemma scale_subset_intersection2 : (a,u,v:E)(scale_subset u a) -> (scale_subset v a) ->
(scale_subset (intersection2 u v) a).

Qed.

Definition is_scale_between := [a,b,f:E]
(A (is_well_ordered a)
(A (is_well_ordered b)
(A (is_scale f)
(A (source f) == a
   (target f) == b
)).

Lemma scale_between_compose : (a,b,c,f,g:E)(is_scale_between a b f) -> (is_scale_between b c g) ->
(is_scale_between a c (Umorphism.compose g f)).

Qed.

Lemma scale_between_identity : (a,f:E)(is_scale_between a a f) -> f == (Umorphism.identity a).

Qed.

Lemma scale_between_inverse : (a,b,f,g:E)(is_scale_between a b f) -> (is_scale_between b a g) ->
(Umorphism.are_inverse f g).

Qed.

Lemma scale_between_surjective_inverse : (a,b,f:E)(is_scale_between a b f) ->
(Umorphism.surjective f) -> (is_scale_between b a (Umorphism.inverse f)).

Qed.

Definition ordinal_leq := [a,b:E]
(exists [f:E](is_scale_between a b f)).


Lemma ordinal_leq_refl : (a:E)(is_well_ordered a) -> (ordinal_leq a a).

Qed.

Lemma ordinal_leq_trans : (a,b,c:E)(ordinal_leq a b) -> (ordinal_leq b c) -> (ordinal_leq a c).

Qed.

Definition same_ordinal := [a,b:E]
(A (ordinal_leq a b) (ordinal_leq b a)).

Lemma same_ordinal_refl : (a:E)(is_well_ordered a) -> (same_ordinal a a).

Qed.

Lemma same_ordinal_symm : (a,b:E)(same_ordinal a b) -> (same_ordinal b a).

Qed.

Lemma same_ordinal_trans : (a,b,c:E)(same_ordinal a b) -> (same_ordinal b c) -> (same_ordinal a c).

Qed.

Definition correspond := [a,b,x,y:E]
(A (is_well_ordered a)
(A (is_well_ordered b)
(A (inc x (U a))
(A (inc y (U b))
   (same_ordinal (downward_suborder a x) (downward_suborder b y))
)))).

Definition corresponding := [a,b,x:E](choose [y:E](correspond a b x y)).

Definition has_correspondant := [a,b,x:E](exists [y:E](correspond a b x y)).

Lemma correspond_symm : (a,b,x,y:E)(correspond a b x y) -> (correspond b a y x).

Qed.

Lemma correspond_refl : (a,x:E)(is_well_ordered a) -> (inc x (U a)) -> (correspond a a x x).

Qed.

Lemma correspond_trans : (a,b,c,x,y,z:E)(correspond a b x y) -> (correspond b c y z) ->
(correspond a c x z).

Qed.

Lemma corresponding_unique : (a,b,x,y:E)(correspond a b x y) -> (corresponding a b x) == y.

Qed.


Lemma scale_correspond : (a,b,f,x:E)(is_scale_between a b f) -> (inc x (U a)) ->
(correspond a b x (ev f x)).

Qed.

Lemma has_correspondant_leq : (a,b,x,u:E)(has_correspondant a b x) -> (leq a u x) ->
(has_correspondant a b u).

Qed.

Lemma has_correspondant_scale_subset : (a,b:E)(is_well_ordered a) -> (is_well_ordered b) ->
(scale_subset (Z (U a) [x:E](has_correspondant a b x)) a).

Qed.


Lemma have_correspondants_disj : (a,b:E)(is_well_ordered a) -> (is_well_ordered b) -> 
((x:E)(inc x (U a)) -> (has_correspondant a b x)) \/
((y:E)(inc y (U b)) -> (has_correspondant b a y)).

Qed.

Lemma ordinal_leq_disj : (a,b:E)(is_well_ordered a) -> (is_well_ordered b) ->
(ordinal_leq a b) \/ (ordinal_leq b a).

Qed.


*)


End WellOrdered. Export WellOrdered. 

Module Zorn.
 



Definition is_ultra_bound (a b x : E) := A (is_upper_bound a b x) (~ inc x b).  

Definition ultra_bound (a b : E) :=
  choose (fun x : E => is_ultra_bound a b x).
(*** here a is the order and b is the subset ***)

Definition eq_ultra_bound (a b x : E) :=
  A (is_ultra_bound a b x) (ultra_bound a b = x).

Definition is_ultra_zorn (a : E) :=
  A (axioms a)
    (forall b : E,
     is_linear_subset a b -> is_ultra_bound a b (ultra_bound a b)).

Definition is_ultra_linear_subset (a b : E) :=
  A (is_wo_subset a b)
    (forall x : E,
     inc x b ->
     eq_ultra_bound a (intersection2 b (punctured_downward_subset a x)) x).


Definition coincide_at (a b c x : E) :=
  A (inc x b)
    (A (inc x c)
       (A (forall y : E, inc y b -> leq a y x -> inc y c)
          (forall y : E, inc y c -> leq a y x -> inc y b))).

Definition coinciders (a b c : E) := Z b (fun x : E => coincide_at a b c x).


Lemma coinciders_symm : forall a b c : E, coinciders a b c = coinciders a c b.
assert (forall a b c x : E, coincide_at a b c x -> coincide_at a c b x).
ir. uh H; uhg; xd.
assert (forall a b c : E, sub (coinciders a b c) (coinciders a c b)).
ir. uf sub; ir. uf coinciders. ufi coinciders H0. Ztac. ap Z_inc. uh H2; xd.
ap H. am. ir. ap extensionality. ap H0. ap H0.
Qed.
 


Definition downward_saturated (a b c : E) :=
  A (axioms a)
    (A (sub b (U a))
       (A (sub c b)
          (forall x y : E, inc x c -> inc y b -> leq a y x -> inc y c))).

Lemma coinciders_saturated :
 forall a b c : E,
 is_ultra_linear_subset a b ->
 is_ultra_linear_subset a c -> downward_saturated a b (coinciders a b c).
ir.
uhg.
dj.
uh H; ee.
uh H; ee.
uh H; ee.
am.

uh H; ee.
uh H; ee.
uh H; ee.
am.

uhg; ir.
ufi coinciders H3; Ztac.

uf coinciders; ap Z_inc.
am.

uhg; ee.
am.

ufi coinciders H4.
Ztac.
uh H8; ee.
au.

ir.
ufi coinciders H4; Ztac.
uh H10.
ee.
ap H12.
am.

uh H1; ee.
apply H17 with y.
am.

am.

ir.
ufi coinciders H4.
Ztac.
uh H10; ee.
ap H13.
am.

uh H1; ee.
apply H17 with y.
am.

am.
Qed. 




Lemma scale_next :
 forall a b c z : E,
 is_ultra_linear_subset a b ->
 downward_saturated a b c ->
 is_bottom_element a (complement b c) z -> eq_ultra_bound a c z.
ir.
assert (intersection2 b (punctured_downward_subset a z) = c).
ap extensionality; uf sub; ir.
apply use_complement with b.
cp (intersection2_first H2).
am.

uf not; ir.
assert (inc x (punctured_downward_subset a z)).
cp (intersection2_second H2).
am.

ufi punctured_downward_subset H4; Ztac.
uh H1; ee.
uh H1; ee.
cp (H10 _ H3).
apply no_lt_leq with a x z.
am.

am.

am.

ap intersection2_inc.
uh H0; ee.
ap H4; am.

uf punctured_downward_subset; ap Z_inc.
uh H0; ee.
ap H3.
ap H4; am.

uh H.
ee.
uh H.
ee.
uh H; ee.
uh H6; ee.
assert (inc x (U (suborder b a))).
rw underlying_suborder.
uh H0; ee.
ap H9; am.

assert (inc z (U (suborder b a))).
rw underlying_suborder.
uh H1; ee.
uh H1; ee.
rwi inc_complement H9; ee.
am.

cp (H7 _ _ H8 H9).
nin H10.
rwi leq_suborder_all H10.
ee.
cp (leq_eq_or_lt H H12).
nin H13.
uh H1; ee.
rwi inc_complement H14.
ee.
assert False.
ap H15.
wr H13.
am.

elim H16.

am.

am.

am.

rwi leq_suborder_all H10; ee.
uh H0.
ee.
assert (inc z c).
apply H15 with x.
am.

am.

am.

uh H1.
ee.
rwi inc_complement H17; ee.
assert False.
ap H18; am.

elim H19.

am.

am.

wr H2.
uh H; ee.
ap H3.
uh H1.
ee.
rwi inc_complement H4.
ee.
am.
Qed.

Lemma next_eq :
 forall a b c d x y : E,
 is_ultra_linear_subset a b ->
 is_ultra_linear_subset a c ->
 downward_saturated a b d ->
 downward_saturated a c d ->
 is_bottom_element a (complement b d) x ->
 is_bottom_element a (complement c d) y -> x = y.
ir.
cp (scale_next H H1 H3).
cp (scale_next H0 H2 H4).
ufi eq_ultra_bound H5.
ufi eq_ultra_bound H6.
ee.
wr H8; am.
Qed.

Lemma next_or :
 forall a b c x y : E,
 is_ultra_linear_subset a b ->
 downward_saturated a b c ->
 is_bottom_element a (complement b c) x ->
 inc y b -> leq a y x -> x = y \/ inc y c.
ir.
assert (axioms a).
uh H.
ee.
uh H; ee.
uh H; ee.
am.

cp (leq_eq_or_lt H4 H3).
nin H5.
ap or_introl.
sy; am.

assert (x <> y -> inc y c).
ir.
apply use_complement with b.
am.

uf not; ir.
uh H1; ee.
uh H1; ee.
cp (H11 y H7).
assert (x = y).
apply leq_leq_eq with a.
am.

am.

am.

ap H6; am.

ap excluded_middle.
uf not; ir.
ap H7.
ap or_introl.
ap excluded_middle.
uf not; ir.
ap H7.
ap or_intror.
ap H6; am.
Qed. 



Lemma next_coincide :
 forall a b c d x y : E,
 is_ultra_linear_subset a b ->
 is_ultra_linear_subset a c ->
 downward_saturated a b d ->
 downward_saturated a c d ->
 is_bottom_element a (complement b d) x ->
 is_bottom_element a (complement c d) y -> coincide_at a b c x.
ir.
assert (x = y).
apply next_eq with a b c d; am.

uhg.
dj.
ufi is_bottom_element H3; ee.
rwi inc_complement H6; ee.
am.

ufi is_bottom_element H4; ee.
rwi inc_complement H7; ee.
rw H5; am.

cp (next_or H H1 H3 H8 H9).
nin H10.
wr H10.
am.

ufi downward_saturated H2; ee.
ap H12; am.

assert (leq a y0 y).
wr H5.
am.

cp (next_or H0 H2 H4 H9 H11).
nin H12.
wr H12.
wr H5; am.

ufi downward_saturated H1; ee.
ap H14.
am.
Qed. 


Lemma show_sub_or :
 forall b c : E,
 (nonempty (complement b c) -> nonempty (complement c b) -> False) ->
 sub b c \/ sub c b.
exact
 (fun (b c : E)
    (H : nonempty (complement b c) -> nonempty (complement c b) -> False) =>
  excluded_middle
    (fun H0 : sub b c \/ sub c b -> False =>
     H
       (excluded_middle
          (fun H1 : nonempty (complement b c) -> False =>
           H0
             (or_introl (sub c b)
                (fun (x : E) (H2 : inc x b) =>
                 excluded_middle
                   (fun H3 : inc x c -> False =>
                    H1
                      (nonempty_intro
                         (eq_ind_r (fun P : Prop => P) (
                            conj H2 H3) (inc_complement b c x))))))))
       (excluded_middle
          (fun H1 : nonempty (complement c b) -> False =>
           H0
             (or_intror (sub b c)
                (fun (x : E) (H2 : inc x c) =>
                 excluded_middle
                   (fun H3 : inc x b -> False =>
                    H1
                      (nonempty_intro
                         (eq_ind_r (fun P : Prop => P) (
                            conj H2 H3) (inc_complement c b x)))))))))).


Qed. 



Lemma wo_subset_choose_bottom :
 forall a b : E,
 is_wo_subset a b ->
 nonempty b -> is_bottom_element a b (choose_bottom_element a b).
ir.
assert (ex (fun x : E => is_bottom_element a b x)).
uh H.
ee.
uh H1; ee.
assert (sub b (U (suborder b a))).
rw underlying_suborder.
uf sub; ir; am.

cp (H2 b H3 H0).
nin H4.
sh x.
uhg.
ee.
uhg; ee.
uh H.
ee; am.

uh H; ee; am.

uh H4; ee.
uh H; ee.
ap H6; am.

ir.
uh H4; ee.
uh H4; ee.
cp (H9 y H5).
rwi leq_suborder_all H10; ee.
am.

uh H; ee; am.

uh H; ee; am.

uh H4; ee.
am.

cp (choose_pr H1).
exact H2.
Qed. 




Lemma uls_or :
 forall a b c : E,
 is_ultra_linear_subset a b ->
 is_ultra_linear_subset a c -> sub b c \/ sub c b.
ir.
set (d := coinciders a b c).
assert (downward_saturated a b d).
uf d; ap coinciders_saturated.


am.

am.

assert (downward_saturated a c d).
uf d.
assert (coinciders a b c = coinciders a c b).
ap coinciders_symm.

rw H2.
ap coinciders_saturated.

am.

am.

apply show_sub_or; ir.
assert (nonempty (complement b d)).
nin H3.
sh y.
rw inc_complement; ee.
rwi inc_complement H3; ee.
am.

uf not; ir.
rwi inc_complement H3; ee.
ap H6.
uh H2; ee.
ap H8; am.

assert (nonempty (complement c d)).
nin H4.
sh y.
rw inc_complement; ee.
rwi inc_complement H4; ee; am.

uf not; ir.
rwi inc_complement H4; ee.
ap H7.
uh H1; ee.
ap H9.
am.

ufk is_ultra_linear_subset H.
ufk is_ultra_linear_subset H0.
ee.

assert (is_wo_subset a (complement b d)).
apply wo_sub with b.
am.

uf sub; ir.
rwi inc_complement H9; ee; am.

assert (is_wo_subset a (complement c d)).
apply wo_sub with c.
am.

uf sub; ir.
rwi inc_complement H10; ee; am.

cp (wo_sub_bottom H9 H5).
cp (wo_sub_bottom H10 H6).
set (x := choose_bottom_element a (complement b d)) in *.
set (y := choose_bottom_element a (complement c d)) in *.
cp (next_eq X0 X1 H1 H2 H11 H12).
cp (next_coincide X0 X1 H1 H2 H11 H12).
assert (inc x d).
uf d.
uf coinciders.
ap Z_inc.
ufi is_bottom_element H11; ee.
rwi inc_complement H15; ee; am.

am.

ufi is_bottom_element H11.
ee.
rwi inc_complement H16.
ee.
ap H17; am.
Qed. 

Lemma uls_sub_downward_saturated :
 forall (a b c : E) (hyp : sub c b),
 is_ultra_linear_subset a b ->
 is_ultra_linear_subset a c -> downward_saturated a b c. 
ir.
set (d := coinciders a b c).
assert (downward_saturated a b d).
uf d; ap coinciders_saturated.


am.

am.

assert (downward_saturated a c d).
uf d.
assert (coinciders a b c = coinciders a c b).
ap coinciders_symm.

rw H2.
ap coinciders_saturated.

am.

am.

apply excluded_middle; uf not; ir. 
assert (nonempty (complement b d)). 
apply excluded_middle; uf not; ir. 
assert (sub b d). uf sub; ir. 
apply use_complement with b. am. uf not; ir. ap H4. 
sh x. am. assert (c = d). ap extensionality; uf sub; ir. 
ap H5.
ap hyp. am. ufi downward_saturated H2; ee. ap H8; am. 
ap H3. rw H6. am. 
assert (nonempty (complement c d)). 
apply excluded_middle; uf not; ir. 
assert (sub c d). uf sub; ir. 
apply use_complement with c. am. uf not; ir.
ap H5; sh x. am. assert (c = d). ap extensionality.
am. ufi downward_saturated H2; ee. am. 
ap H3. rw H7; exact H1. 



ufk is_ultra_linear_subset H.
ufk is_ultra_linear_subset H0.
ee.

assert (is_wo_subset a (complement b d)).
apply wo_sub with b.
am.

uf sub; ir.
rwi inc_complement H8; ee; am.

assert (is_wo_subset a (complement c d)).
apply wo_sub with c.
am.

uf sub; ir.
rwi inc_complement H9; ee; am.

cp (wo_sub_bottom H8 H4).
cp (wo_sub_bottom H9 H5).
set (x := choose_bottom_element a (complement b d)) in *.
set (y := choose_bottom_element a (complement c d)) in *.
cp (next_eq X0 X1 H1 H2 H10 H11).
cp (next_coincide X0 X1 H1 H2 H10 H11).
assert (inc x d).
uf d.
uf coinciders.
ap Z_inc.
ufi is_bottom_element H10; ee.
rwi inc_complement H14; ee; am.

am.

ufi is_bottom_element H11.
ee.
rwi inc_complement H15.
ee.
ap H16. wr H12.  am.
Qed.


Definition increasing_ds_family (a f : E) :=
  forall x y : E,
  inc x f -> inc y f -> downward_saturated a x y \/ downward_saturated a y x.

Lemma wo_subset_increasing_union :
 forall a f : E,
 axioms a ->
 increasing_ds_family a f ->
 (forall b : E, inc b f -> is_wo_subset a b) -> is_wo_subset a (union f).
ir. uhg. dj. uhg; dj. am. uhg; ir. 
cp (union_exists H3). nin H4; ee. cp (H1 x0 H5). 
ufi is_wo_subset H6. ee. ufi is_linear_subset H6; ee. 
ap H8; am. uhg; dj. 
ap suborder_axioms. am. am. rwi underlying_suborder H5. 
rwi underlying_suborder H6. 
cp (union_exists H5). nin H7. cp (union_exists H6). 
nin H8. ee. ufi increasing_ds_family H0. 
cp (H0 _ _ H10 H9). nin H11. 
assert (inc y x0). ufi downward_saturated H11. ee. 
ap H13; am. cp (H1 x0 H10). ufi is_wo_subset H13.
ee. ufi is_linear_subset H13; ee. 
ufi is_linear H16; ee. 
assert (inc x (U (suborder x0 a))). 
rw underlying_suborder. am. 
assert (inc y (U (suborder x0 a))). 
rw underlying_suborder. am. 
cp (H17 x y H18 H19). 
nin H20. ap or_introl. rwi leq_suborder_all H20. 
rw leq_suborder_all. ee; am. 
am. am. am. am. 
ap or_intror. rwi leq_suborder_all H20. 
rw leq_suborder_all. ee; am. 
am. am. am. am. 

assert (inc x x1). ufi downward_saturated H11. ee. 
ap H13; am. cp (H1 x1 H9). ufi is_wo_subset H13.
ee. ufi is_linear_subset H13; ee. 
ufi is_linear H16; ee. 
assert (inc x (U (suborder x1 a))). 
rw underlying_suborder. am. 
assert (inc y (U (suborder x1 a))). 
rw underlying_suborder. am. 
cp (H17 x y H18 H19). 
nin H20. ap or_introl. rwi leq_suborder_all H20. 
rw leq_suborder_all. ee; am. 
am. am. am. am. 
ap or_intror. rwi leq_suborder_all H20. 
rw leq_suborder_all. ee; am. 
am. am. am. am. 


uhg; dj. ufi is_linear_subset H2; ee. am. 
nin H5. assert (inc y (union f)). rwi underlying_suborder H4. 
ap H4. am. cp (union_exists H6). 
nin H7. ee. assert (is_wo_subset a x). ap H1; am.
ufi is_wo_subset H9. ee. 
assert (nonempty (intersection2 b x)). 
sh y. ap intersection2_inc. 
am. am. set (z := choose_bottom_element (suborder x a) (intersection2 b x)). assert (is_bottom_element (suborder x a) (intersection2 b x) z). 
uf z. ap wo_choose_bottom. am. 
uf sub; ir. cp (intersection2_second H12). 
rw underlying_suborder. am. am. 
sh z. ufi is_bottom_element H12. ee. 
assert (sub (union f) (U a)). 
uf sub; ir. cp (union_exists H14). 
nin H15; ee. assert (is_wo_subset a x1). 
ap H1; am. ufi is_wo_subset H17; ee. ufi is_linear_subset H17; ee. ap H19. am. 
uf is_bottom_element; dj. 
ufi is_lower_bound H12; uf is_lower_bound; ee. 
ap suborder_axioms. am. am. am. 
rw underlying_suborder. 
apply union_inc with x. rwi underlying_suborder H16; am.
am. ir. 
assert (inc y0 (union f)). rwi underlying_suborder H4.
ap H4; am.
cp (union_exists H19). nin H20; ee. 
ufi increasing_ds_family H0. 
cp (H0 x x0 H8 H21). nin H22. 
assert (leq (suborder x a) z y0). 
ap H17. ap intersection2_inc. am. ufi downward_saturated H22. ee. ap H24; am. rw leq_suborder_all. 
rwi leq_suborder_all H23. ee. apply union_inc with x. am. am. apply union_inc with x. am. 
am. am. am. ufi is_linear_subset H9; ee. am. am. 
am. 
ufi is_linear H3. ee. 
assert (leq (suborder (union f) a) z y0 \/ leq (suborder (union f) a) y0 z). 
ap H23. rw underlying_suborder. 
apply union_inc with x. apply intersection2_second with b. 
am. am. rw underlying_suborder. am. nin H24. 
am. 
assert (inc z x). apply intersection2_second with b.
exact H13. 
assert (inc y0 x).
ufi downward_saturated H22. ee. apply H28 with z. 
am. 
am. 
rwi leq_suborder_all H24; ee. am. am. 
am. assert (leq (suborder x a) z y0). 
ap H17. ap intersection2_inc. am. 
am. 
rw leq_suborder_all; ee. 
apply union_inc with x. am. am. 
apply union_inc with x. am. am. 
rwi leq_suborder_all H27; ee. 
am. am. ufi is_linear_subset H9; ee. exact H28.
am. am. apply intersection2_first with x.
am. 
Qed. 

Lemma uls_increasing_ds :
 forall a f : E,
 axioms a ->
 (forall x : E, inc x f -> is_ultra_linear_subset a x) ->
 increasing_ds_family a f.
ir. uhg. ir. assert (sub x y \/ sub y x).
apply uls_or with a; ap H0; am.
nin H3. ap or_intror. 
ap uls_sub_downward_saturated. am. 
ap H0; am. ap H0; am. 
ap or_introl. 
ap uls_sub_downward_saturated. am. 
ap H0; am. ap H0; am. 
Qed.

Lemma uls_union_downward :
 forall a f z : E,
 axioms a ->
 (forall x : E, inc x f -> is_ultra_linear_subset a x) ->
 inc z f -> downward_saturated a (union f) z. 
ir. uhg. ee. am. uf sub; ir. cp (union_exists H2). 
nin H3; ee. cp (H0 x0 H4). 
uh H5. ee. uh H5; ee. uh H5; ee. ap H8; am. 
uf sub; ir. apply union_inc with z. am. 
am. ir. cp (union_exists H3).
nin H5. ee. assert (sub x0 z \/ sub z x0).
apply uls_or with a. ap H0; am. ap H0; am. 
nin H7. ap H7; am. assert (downward_saturated a x0 z). 
ap uls_sub_downward_saturated. am. ap H0; am. 
ap H0; am. ufi downward_saturated H8. ee. 
apply H11 with x. am. am. am.  
Qed. 

Lemma uls_union_int_rw :
 forall a b x z : E,
 axioms a ->
 downward_saturated a b x ->
 inc z x ->
 intersection2 b (punctured_downward_subset a z) =
 intersection2 x (punctured_downward_subset a z).
ir. 
ap extensionality; uf sub; ir; cp (intersection2_first H2);
 cp (intersection2_second H2).  
ap intersection2_inc. 
ufi downward_saturated H0; ee. 
apply H7 with z. am. am. 
ufi punctured_downward_subset H4. Ztac. ufi lt H9; ee. 
am. am. 
ap intersection2_inc. ufi downward_saturated H0; ee. 
ap H6; am. am. 
Qed. 

Lemma ultra_linear_subset_union :
 forall a f : E,
 axioms a ->
 (forall x : E, inc x f -> is_ultra_linear_subset a x) ->
 is_ultra_linear_subset a (union f).
ir. 
assert (increasing_ds_family a f). 
ap uls_increasing_ds. am. am. 
uhg; dj. 
ap wo_subset_increasing_union. 
am. am. ir. cp (H0 b H2). 
ufi is_ultra_linear_subset H3.
ee. am. cp (union_exists H3). 
nin H4. ee. assert
  (intersection2 (union f) (punctured_downward_subset a x) =
   intersection2 x0 (punctured_downward_subset a x)). 
ap uls_union_int_rw. am. ap uls_union_downward. 
am. exact H0. am. am. rw H6. 
cp (H0 x0 H5). 
ufi is_ultra_linear_subset H7. 
ee. ap H8. am. 
Qed.




Lemma wo_subset_new :
 forall a b x : E,
 is_wo_subset a b ->
 ~ inc x b -> is_upper_bound a b x -> is_wo_subset a (union2 b (singleton x)). 
ir. ufk is_wo_subset H. ufk is_upper_bound H1. ee. ufk is_well_ordered H3.
ufk is_linear_subset H. ee. ufk is_linear H8. ee. uhg; dj. uhg; dj. am.
uf sub; ir. cp (union2_or H11). nin H12. ap H2. am.
cp (singleton_eq H12). rw H13; am. uhg; dj. ap suborder_axioms.
am. am. rwi underlying_suborder H13. rwi underlying_suborder H14.
cp (union2_or H13). cp (union2_or H14). nin H15. nin H16.
ufi is_linear X4. ee. assert (leq (suborder b a) x0 y \/ leq (suborder b a) y x0).
ap H18. rw underlying_suborder; am. rw underlying_suborder; am. nin H19.
ap or_introl. rw leq_suborder_all; ee. am. am. rwi leq_suborder_all H19.
ee. am. am. am. am. am. ap or_intror. rw leq_suborder_all; ee. am.
am. rwi leq_suborder_all H19. ee; am. am. am. am. am. cp (singleton_eq H16).
ap or_introl. rw leq_suborder_all; ee. am. am. rw H17.
ap H5. am. am. am. cp (singleton_eq H15). ap or_intror. rw leq_suborder_all; ee.
am. am. rw H17. nin H16. ap H5; am. cp (singleton_eq H16).
rw H18. ufi axioms H; ee. ap H. am. am. am. uhg. dj. ufi is_linear_subset H10.
ee. am. apply by_cases with (nonempty (intersection2 b0 b)). ir. ufi is_well_ordered X2.
ee. set (b1 := intersection2 b0 b) in *. assert (sub b1 (U (suborder b a))). rw underlying_suborder.
uf b1; uf sub; ir. apply intersection2_second with b0. am. cp (H16 b1 H17 H14).
nin H18. sh x0. uhg; dj. uhg; dj. ap suborder_axioms. am. uf sub; ir.
cp (union2_or H19). nin H20. ap H2; am. cp (singleton_eq H20). rw H21.
am. am. rw underlying_suborder. apply union2_first. rwi underlying_suborder H17.
ap H17. ufi is_bottom_element H18; ee. am. rw leq_suborder_all.
ee. rwi underlying_suborder H21. exact H21. rwi underlying_suborder H20. ap H20.
am. apply by_cases with (inc y b). ir. assert (inc y b1). uf b1; ap intersection2_inc; am.
ufi is_bottom_element H18; ee. ufi is_lower_bound H18; ee. cp (H28 y H24).
rwi leq_suborder_all H29. ee. am. am. am. ir. assert (inc y (union2 b (singleton x))).
rwi underlying_suborder H20. ap H20. am. cp (union2_or H24). nin H25.
assert False. ap H23; am. elim H26. cp (singleton_eq H25). rw H26.
assert (inc x0 (union2 b (singleton x))). rwi underlying_suborder H21; exact H21.
cp (union2_or H27). nin H28. ap H5. am. cp (singleton_eq H28).
rw H29. ufi axioms H1; ee. ap H1; am. am. uf sub; ir. cp (union2_or H23).
nin H24. ap H2; am. cp (singleton_eq H24). rw H25; am. ufi is_bottom_element H18.
ee. ufi b1 H20. apply intersection2_first with b; am. ir. assert (sub b0 (singleton x)).
uf sub; ir. rwi underlying_suborder H12. assert (inc x0 (union2 b (singleton x))).
ap H12. am. cp (union2_or H16). nin H17. assert False. ap H14. sh x0.
ap intersection2_inc; am. elim H18. am. assert (b0 = singleton x). ap extensionality.
am. uf sub; ir. cp (singleton_eq H16). rw H17. nin H13. assert (inc y (singleton x)).
ap H15; am. cp (singleton_eq H18). wr H19. am. rw H16. sh x. uhg; dj. uhg; dj.
ap suborder_axioms. am. ufi is_linear_subset H10; ee. am. uf sub; ir. rw underlying_suborder.
ap union2_second. am. rw underlying_suborder. ap union2_second. ap singleton_inc.
cp (singleton_eq H20). rw H21. rw leq_suborder_all. dj. ap union2_second; ap singleton_inc.
am. ufi axioms H1; ee; ap H1. am. am. ufi is_linear_subset H10; ee; am. ap singleton_inc.
Qed. 

Lemma uls_new :
 forall a b x : E,
 is_ultra_linear_subset a b ->
 eq_ultra_bound a b x -> is_ultra_linear_subset a (union2 b (singleton x)). 
ir. uhg; dj. ap wo_subset_new. uh H; ee. am. uh H0; ee. uh H0; ee.
am. uh H0; ee. uh H0; ee. am. cp (union2_or H2). nin H3.
assert
 (intersection2 (union2 b (singleton x)) (punctured_downward_subset a x0) =
  intersection2 b (punctured_downward_subset a x0)).
ap extensionality; uf sub; ir. cp (intersection2_first H4).
cp (intersection2_second H4). ap intersection2_inc. cp (union2_or H5).
nin H7. am. cp (singleton_eq H7). rw H8. ufi punctured_downward_subset H6.
Ztac. uh H0; ee. uh H0; ee. uh H0; ee. cp (H15 x0 H3). rwi H8 H10.
assert False. apply no_lt_leq with a x x0. am. am. am. elim H17. am.
cp (intersection2_first H4). cp (intersection2_second H4).
ap intersection2_inc. ap union2_first. am. am. rw H4. uh H; ee. ap H5.
am. cp (singleton_eq H3).
assert
 (intersection2 (union2 b (singleton x)) (punctured_downward_subset a x0) = b).
ap extensionality; uf sub; ir. cp (intersection2_first H5). cp (intersection2_second H5).
cp (union2_or H6). nin H8. am. cp (singleton_eq H8).
ufi punctured_downward_subset H7. Ztac. ufi lt H11. ee. assert False.
ap H12. rw H4; am. elim H13. ap intersection2_inc. ap union2_first; am.
uf punctured_downward_subset; ap Z_inc. uh H; ee. uh H; ee. uh H; ee.
ap H8; am. uh H0; ee. uh H0; ee. uh H0; ee. uf lt; ee. rw H4. ap H10; am.
uf not; ir. ap H7. wr H4. wr H11. am. rw H5. rw H4. am.
Qed. 



Definition uls_pool (a : E) :=
  Z (powerset (U a)) (fun b : E => is_ultra_linear_subset a b).

Lemma inc_uls_pool_rw :
 forall a b : E, inc b (uls_pool a) = is_ultra_linear_subset a b.
ir. ap iff_eq; ir. ufi uls_pool H. Ztac. uf uls_pool. ap Z_inc.
ap powerset_inc. uh H; ee. uh H; ee. uh H; ee. am. am.
Qed.

Definition max_uls (a : E) := union (uls_pool a).

Lemma uls_sub_uls_pool :
 forall a b : E, is_ultra_linear_subset a b -> sub b (max_uls a).
ir. uf sub; ir. uf max_uls. apply union_inc with b. am. rw inc_uls_pool_rw. am.
Qed.

Lemma max_uls_uls :
 forall a : E, axioms a -> is_ultra_linear_subset a (max_uls a).
ir. uf max_uls. ap ultra_linear_subset_union. am. ir. rwi inc_uls_pool_rw H0. am.
Qed. 

Lemma ub_inc_max_uls :
 forall a b x : E,
 is_ultra_linear_subset a b -> eq_ultra_bound a b x -> inc x (max_uls a).
ir. assert (sub (union2 b (singleton x)) (max_uls a)). ap uls_sub_uls_pool.
ap uls_new. am. am. ap H1. ap union2_second. ap singleton_inc.
Qed. 
 


Lemma no_ultra_zorn : forall a : E, ~ is_ultra_zorn a.
uf not; ir. uh H; ee. set (c := max_uls a) in *. assert (is_ultra_linear_subset a c).
uf c; ap max_uls_uls. am. set (x := ultra_bound a c) in *. assert (is_ultra_bound a c x).
uf x. ap H0. uh H1; ee. uh H1; ee. am. ufk is_ultra_bound H2.
ee. ap H3. uf c. apply ub_inc_max_uls with c. am. uhg; ee. am. tv.
Qed.


Lemma zorn :
 forall a : E,
 axioms a ->
 (forall b : E,
  is_linear_subset a b -> ex (fun x : E => is_upper_bound a b x)) ->
 ex (fun z : E => is_maximal a (U a) z).
ir. ap excluded_middle. uf not; ir. apply no_ultra_zorn with a. uhg; dj.
am. cp (H0 b H3). apply by_cases with (ex (fun y : E => is_ultra_bound a b y)).
ir. cp (choose_pr H5). am. ir. assert False. ap H1. nin H4.
sh x. uhg; dj. am. uf sub; ir; am. uh H4; ee. am. assert (is_upper_bound a b y).
uhg; ee. am. uh H3; ee. am. am. ir. uh H4; ee. uh H; ee. apply H18 with x.
ap H14; am. am. ap excluded_middle; uf not; ir. assert (is_top_element a b x).
uhg; ee. am. ap excluded_middle. uf not; ir. ap H5. sh x. uhg; ee. am.
am. assert (is_top_element a b y). uhg; ee. am. ap excluded_middle.
uf not; ir. ap H5. sh y. uhg; ee. am. am. cp (top_element_unique H13 H14).
ap H12; am. elim H6.
Qed. 

End Zorn. Export Zorn. 

End Order.


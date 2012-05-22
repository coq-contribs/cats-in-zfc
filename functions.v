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


Require Export set_theory.

Set Implicit Arguments.
Unset Strict Implicit.



Module Function.

Definition axioms (f : E) :=
  A (forall x : E, inc x f -> pair (pr1 x) (pr2 x) = x)
    (forall x y : E, inc x f -> inc y f -> pr1 x = pr1 y -> x = y).

Definition domain (f : E) := Image.create f P.
Definition range (f : E) := Image.create f Q.

Definition defined (f x : E) := A (axioms f) (inc x (domain f)).


Lemma sub_axioms : forall f g : E, axioms g -> sub f g -> axioms f.
ir. 
nin H. 
unfold sub in H0. 
unfold axioms in |- *; xd.
Qed.

Lemma sub_domain : forall f g : E, sub f g -> sub (domain f) (domain g).
ir. 
unfold sub in |- *. 
unfold domain in |- *. 
unfold sub in H.
ir. 
set (K := Image.ex H0) in *. 
nin K. 
nin H1.
rewrite <- H2. 
ap Image.incl. 
au.
Qed.

Lemma sub_range : forall f g : E, sub f g -> sub (range f) (range g).
ir. 
unfold sub in |- *. 
unfold range in |- *. 
unfold sub in H. 
ir.
set (K := Image.ex H0) in *. 
nin K. 
nin H1.
rewrite <- H2. 
ap Image.incl. 
au.
Qed.


Lemma range_inc :
 forall f z : E,
 axioms f ->
 ex (fun y : E => A (inc y (domain f)) (V y f = z)) -> inc z (range f). 
ir. nin H0. xd. unfold range in |- *. 
ap Image.show_inc. apply ex_intro with (pair x z).
xd. ap V_inc. 
unfold domain in H0.
pose (Image.ex H0). nin e; xd. 
apply ex_intro with (pr2 x0). 
rewrite <- H3. unfold axioms in H. xd. 
rewrite H. am. am. au. ap pr2_pair. 
Qed. 




Lemma defined_lem :
 forall f x : E, axioms f -> defined f x -> inc (pair x (V x f)) f.
ir.
unfold axioms in H.
unfold defined in H0.
xd.
unfold domain in H1.
set (K := Image.ex H1) in *.
nin K.
nin H3.
assert (ex (fun y : E => inc (pair x y) f)).
eapply ex_intro with (pr2 x0).
rewrite <- H4.
rewrite H.
am.
am.
set (K := choose_pr H5) in *.
am.
Qed.

Lemma lem1 :
 forall f x : E, axioms f -> inc x f -> x = pair (pr1 x) (V (pr1 x) f).
ir.
unfold axioms in H.
xd.
set (z := pr1 x) in *.
assert (ex (fun y : E => inc (pair z y) f)).
apply ex_intro with (pr2 x).
unfold z in |- *.
rewrite H.
am.
am.
set (K := choose_pr H2) in *.
assert (inc (pair z (V z f)) f).
am.
ap H1.
am.
am.
rewrite pr1_pair.
tv.
Qed.

Lemma lem2 : forall f x : E, axioms f -> inc x f -> inc (pr1 x) (domain f). 
ir. unfold domain in |- *. ap Image.incl. am. 
Qed. 

Lemma pr2_V : forall f x : E, axioms f -> inc x f -> pr2 x = V (pr1 x) f.
ir.
pose (lem1 H H0).
set (a := pr1 x) in *.
rewrite e.
rewrite pr2_pair.
tv.
Qed.

Lemma range_ex :
 forall f y : E,
 axioms f ->
 inc y (range f) -> ex (fun x : E => (inc x (domain f) & V x f = y)). 
ir. unfold range in H0. pose (Image.ex H0); nin e; xd. assert (axioms f).
am. unfold axioms in H; xd.
pose (H x H1). set (a := pr1 x) in *. set (b := pr2 x) in *. 
apply ex_intro with a. xd. unfold a in |- *; ap lem2; au. 
assert (x = pair a (V a f)). unfold a in |- *. ap lem1; au. 
rewrite <- H2. unfold b in |- *. rewrite H5. 
sy; ap pr2_pair. Qed. 

Lemma range_inc_rw : forall f y,
Function.axioms f -> 
inc y (range f) = (exists x, inc x (domain f) & y = V x f).
Proof.
ir. 
ap iff_eq; ir. cp (range_ex H H0). nin H1. 
sh x; xd. nin H0. ee. ap range_inc. am. sh x. 
xd. 
Qed.  

Lemma function_sub :
 forall f g : E,
 axioms f ->
 axioms g ->
 (forall x : E, defined f x -> defined g x) ->
 (forall x : E, defined f x -> V x f = V x g) -> sub f g.
ir.
unfold sub in |- *.
ir.
set (K := lem1 H H3) in *.
assert (defined f (pr1 x)).
unfold defined in |- *; xd.
unfold domain in |- *.
ap Image.incl.
am.
assert (V (pr1 x) f = V (pr1 x) g).
ap H2.
am.
rewrite K.
assert (defined g (pr1 x)).
ap H1.
am.
unfold defined in H6.
xd.
unfold domain in H7.
set (K1 := Image.ex H7) in *.
nin K1.
nin H8.
unfold axioms in H0.
set (K1 := lem1 H6 H8) in *.
rewrite H9 in K1.
rewrite H5.
rewrite <- K1.
am.
Qed.


Lemma function_extensionality :
 forall f g : E,
 axioms f ->
 axioms g ->
 (forall x : E, defined f x -> defined g x) ->
 (forall x : E, defined g x -> defined f x) ->
 (forall x : E, defined f x -> V x f = V x g) -> f = g.
ir.
ap extensionality.
ap function_sub; au.
ap function_sub; au.
ir.
sy.
ap H3.
ap H2.
am.
Qed.


Definition inverse_image (a f : E) :=
  Z (domain f) (fun x : E => inc (V x f) a). 


Lemma inverse_image_sub : forall a f : E, sub (inverse_image a f) (domain f).
ir. unfold inverse_image in |- *. ap Z_sub. 
Qed.

Lemma inverse_image_inc :
 forall a f x : E,
 inc x (domain f) -> inc (V x f) a -> inc x (inverse_image a f). 
ir. unfold inverse_image in |- *. ap Z_inc. am.
am. Qed. 

Lemma inverse_image_pr :
 forall a f x : E, inc x (inverse_image a f) -> inc (V x f) a. 
ir. unfold inverse_image in H. Ztac. 
Qed. 




Definition create (x : E) (p : E1) :=
  Image.create x (fun y : E => pair y (p y)).


Lemma elt_rewrite :
 forall (x : E) (p : E1) (y : E),
 inc y (create x p) -> y = pair (pr1 y) (p (pr1 y)).
ir. unfold create in H. pose (Image.ex H).
nin e. xd. assert (pr1 y = x0).
rewrite <- H1. ap pr1_pair. rewrite H2. au.
Qed. 

Lemma create_axioms : forall (p : E1) (x : E), axioms (create x p).
ir. unfold axioms in |- *; xd.
ir. ap pair_recov. unfold create in H. 
pose (Image.ex H). nin e. xd. 
rewrite <- H1. ap pair_is_pair. 
ir. unfold create in H. 
unfold create in H0. pose (Image.ex H).
pose (Image.ex H0). nin e. nin e0. 
xd. rewrite <- H5. assert (x1 = x2). 
transitivity (pr1 x0). rewrite <- H5. 
sy; ap pr1_pair. rewrite H1. rewrite <- H4. 
ap pr1_pair. rewrite H6; am. Qed. 

Lemma create_axioms_rw : forall p x,
axioms (create x p) = True.
Proof.
ir. app iff_eq; ir. ap create_axioms. 
Qed.

Hint Rewrite create_axioms_rw : aw. 

Lemma create_inc :
 forall (x y : E) (hyp : inc y x) (p : E1) (z : E),
 pair y (p y) = z -> inc z (create x p). 
ir. unfold create in |- *. ap Image.show_inc.
apply ex_intro with y; xd. 
Qed. 

Lemma create_domain : forall (x : E) (p : E1), domain (create x p) = x.
ir. unfold domain in |- *. ap extensionality; unfold sub in |- *; ir.
pose (Image.ex H); nin e; xd. 
unfold create in H0; pose (Image.ex H0); nin e; xd.
rewrite <- H1. assert (pr1 x1 = x2). 
rewrite <- H3; ap pr1_pair. rewrite H4; au. 
ap Image.show_inc. apply ex_intro with (pair x0 (p x0)). xd. 
ap (create_inc H); au. ap pr1_pair. Qed.


Hint Rewrite create_domain : aw. 

Lemma create_V_apply :
 forall (x : E) (p : E1) (y z : E),
 inc y x -> p y = z -> V y (create x p) = z.
ir. assert (inc (pair y (V y (create x p))) (create x p)).
ap V_inc. apply ex_intro with (p y). 
ap (create_inc H). tv. tv. 
assert (axioms (create x p)). ap create_axioms. 
unfold axioms in H2; xd. 
assert (pair y (V y (create x p)) = pair y z). 
ap H3. ap V_inc. apply ex_intro with (p y). 
ap (create_inc H). tv. tv. 
ap (create_inc H). rewrite H0; tv. rewrite pr1_pair.
rewrite pr1_pair. tv. transitivity (pr2 (pair y z)). 
rewrite <- H4. sy; ap pr2_pair. 
ap pr2_pair. Qed. 

Lemma create_V_rewrite :
 forall (x : E) (p : E1) (y : E), inc y x -> V y (create x p) = p y. 
ir. ap create_V_apply; au. Qed. 

Hint Rewrite create_V_rewrite : aw. 

Lemma create_range :
 forall (p : E1) (x : E), range (create x p) = Image.create x p.
ir. unfold range in |- *. ap extensionality; unfold sub in |- *; ir.
pose (Image.ex H); nin e; xd. ap Image.show_inc. 
unfold create in H0. pose (Image.ex H0); nin e; xd.
apply ex_intro with x2. xd.
rewrite <- H1. rewrite <- H3. sy; ap pr2_pair. 
pose (Image.ex H); nin e; xd. 
ap Image.show_inc. apply ex_intro with (pair x1 x0). 
xd. ap (create_inc H0). rewrite H1. tv. 
ap pr2_pair. 
Qed.

Lemma create_recovers :
 forall f : E, axioms f -> create (domain f) (fun x : E => V x f) = f.
ir. ap function_extensionality. 
ap create_axioms. am. ir. 
unfold defined in H0. xd. unfold defined in |- *.
xd. rewrite create_domain in H1. am.
ir. unfold defined in H0. xd. 
unfold defined in |- *; xd. ap create_axioms. 
rewrite create_domain. am. 
ir. unfold defined in H0; xd. rewrite create_domain in H1. ap create_V_apply; au. 
Qed. 


Lemma create_V_defined :
 forall (x : E) (p : E1) (y : E),
 defined (create x p) y -> V y (create x p) = p y. 
ir. ap create_V_apply. unfold defined in H. 
xd. rewrite create_domain in H0. am. 
tv. Qed. 


Lemma create_extensionality :
 forall (a b : E) (f g : E1),
 a = b ->
 (forall x : E, inc x a -> inc x b -> f x = g x) -> create a f = create b g.
ir.
assert (axioms (create a f)).
ap create_axioms.

assert (axioms (create b g)).
ap create_axioms.

ap function_extensionality; au.
unfold defined in |- *; ir.
xd.
rewrite create_domain.
rewrite <- H.
rewrite create_domain in H4.
am.

unfold defined in |- *.
ir; xd.
rewrite create_domain.
rewrite create_domain in H4.
rewrite H.
am.

ir.
assert (inc x a).
unfold defined in H3.
xd.
rewrite create_domain in H4; am.

repeat rewrite create_V_rewrite.
ap H0.
am.

rewrite <- H.
am.

rewrite <- H.
am.

am.
Qed.

Lemma create_create :
 forall (a : E) (f : E1),
 create a (fun x : E => V x (create a f)) = create a f.
ir.
ap create_extensionality.
tv.

ir.
ap create_V_rewrite.
am.
Qed.

Lemma create_rw : forall x f,
x = domain f -> 
axioms f -> 
create x (fun x => V x f) = f. 
Proof.
ir. rw H. 
util (create_recovers (f:= f)). am. am. 
Qed. 

Lemma create_V_out : forall x f y,
~inc y x -> V y (create x f) = emptyset.
Proof.
ir. cp (V_or y (create x f)). 
nin H0. 
assert (axioms (create x f)). app create_axioms. 
cp (lem2 H1 H0). rwi pr1_pair H2. 
rwi create_domain H2. nin (H H2). ee; am.  
Qed. 


Definition composable (f g : E) :=
axioms f & axioms g & sub (range g) (domain f). 



Definition compose (f g : E) :=
  create (inverse_image (domain f) g) (fun y : E => V (V y g) f).

Lemma compose_axioms : forall f g : E, axioms (compose f g).
ir. unfold compose in |- *. 
ap create_axioms. Qed. 


Lemma compose_domain :
 forall f g : E, domain (compose f g) = inverse_image (domain f) g.
ir. unfold compose in |- *. 
rewrite create_domain. tv. 
Qed.

Lemma composable_domain :
 forall f g : E, composable f g -> domain (compose f g) = domain g. 
ir. unfold compose in |- *. 
rewrite create_domain. ap extensionality. 
ap inverse_image_sub. 
unfold sub in |- *; ir. ap inverse_image_inc. am.
unfold composable in H. xd. 
ap H2. ap range_inc. am. 
apply ex_intro with x. xd. Qed. 



Lemma compose_ev :
 forall x f g : E,
 inc x (domain (compose f g)) -> V x (compose f g) = V (V x g) f.
ir. unfold compose in |- *. 
unfold compose in H. 
rewrite create_domain in H. ap create_V_apply. 
am. tv. Qed. 



Definition identity (x : E) := create x (fun y : E => y).


Lemma identity_axioms : forall x : E, axioms (identity x). 
ir; unfold identity in |- *; ap create_axioms. 
Qed. 


Lemma identity_domain : forall x : E, domain (identity x) = x.
ir; unfold identity in |- *; rewrite create_domain; tv. 
Qed. 


Lemma identity_ev : forall x a : E, inc x a -> V x (identity a) = x.
ir. unfold identity in |- *. ap create_V_apply; au. 
Qed.


(*** function restriction ****)

Definition restr f x :=
Z f (fun y=> inc (pr1 y) x).

Lemma restr_inc_rw : forall f x y,
inc y (restr f x) = (inc y f & inc (pr1 y) x).
Proof.
ir. ap iff_eq; ir. ufi restr H. Ztac. 
uf restr. ap Z_inc; xd. 
Qed.

Lemma restr_axioms : forall f x,
Function.axioms f -> Function.axioms (restr f x).
Proof.
ir. 
uhg; dj.
rwi restr_inc_rw H0. uh H; ee. ap H; am. 
uh H; ee. ap H4. rwi restr_inc_rw H1; xd. 
rwi restr_inc_rw H2; xd. am. 
Qed.

Lemma restr_domain : forall f x,
Function.axioms f -> 
domain (restr f x) = intersection2 (domain f) x.
Proof.
ir. 
ap extensionality; uhg; ir. ufi domain H0. 
rwi Image.inc_rw H0. nin H0; ee. 
ufi restr H0; Ztac. 
ap intersection2_inc. uf domain. 
rw Image.inc_rw. sh x1; ee. am. am. wr H1; am. 
cp (intersection2_first H0).
cp (intersection2_second H0). 
uf domain. rw Image.inc_rw. 
ufi domain H1. rwi Image.inc_rw H1. nin H1; ee. 
sh x1. ee; try am. uf restr; ap Z_inc. 
am. rw H3; am.  
Qed.

Lemma restr_sub : forall f x, sub (restr f x) f.
Proof.
ir.
uhg; ir. rwi restr_inc_rw H. ee; am. 
Qed.

Lemma function_sub_eq : forall r s, 
Function.axioms r -> Function.axioms s -> sub r s ->
sub (domain s) (domain r) -> r = s.
Proof.
ir. 
ap extensionality; try am. uhg; ir. 
cp (Function.lem1 H0 H3).
cp (Function.lem2 H0 H3).
assert (inc (pr1 x) (domain r)). 
ap H2; am. 
util (Function.defined_lem (f:=r) (x:=(pr1 x))). 
am. uhg; ee; am. 
assert (inc (pair (pr1 x) (V (pr1 x) r)) s).
ap H1; am. rwi H4 H3. uh H0; ee. 
assert (pair (pr1 x) (V (pr1 x) r) = pair (pr1 x) (V (pr1 x) s)).
ap H9. 
am. am. do 2 (rw pr1_pair). tv. rwi H10 H7. 
wri H4 H7. am. 
Qed. 

Lemma restr_to_domain : forall f g, 
Function.axioms f -> Function.axioms g -> sub f g ->
restr g (domain f) = f.
Proof.
ir. sy. ap function_sub_eq. am. ap restr_axioms. am. 
uhg; ir. uf restr; ap Z_inc. ap H1; am. uf domain.
rw Image.inc_rw. sh x; ee; try am; try tv. 
rw restr_domain. uhg; ir. cp (intersection2_second H2). am.
am.  
Qed. 

Lemma restr_ev : forall f u x,
Function.axioms f -> sub u (domain f) -> inc x u ->
V x (restr f u) = V x f.
Proof.
ir. util (Function.defined_lem (f:=f) (x:=x)). 
am. uhg. ee. am. ap H0; am. cp (restr_sub (f:=f) (x:= u)). 
assert (inc (pair x (V x f)) (restr f u)).
uf restr; ap Z_inc; ee. am. rw pr1_pair. am. 
cp Function.pr2_V. assert (Function.axioms (restr f u)).
ap restr_axioms; try am. cp (H5 _ _ H6 H4). 
rwi pr2_pair H7. rwi pr1_pair H7. sy; am. 
Qed. 

(*********************************)


Lemma function_glueing : forall z,
(forall f, inc f z -> Function.axioms f) -> 
(forall f g x, inc f z -> inc g z -> defined f x -> defined g x
-> (V x f) = (V x g)) -> 
Function.axioms (union z).
Proof.
ir. 
uhg; ee; ir. nin (union_exists H1); ee. 
cp (H _ H3). uh H4. ee. ap H4; am. 
nin (union_exists H1);  nin (union_exists H2); ee. 
cp (H _ H7); cp (H _ H6).
cp (Function.lem1 H8 H4).
cp (Function.lem1 H9 H5).
rw H10; rw H11. 
rw H3. 
assert (V (pr1 y) x0 = V (pr1 y) x1). 
ap H0. am. am. uhg; ee; try am. 
wr H3; 
ap Function.lem2; try am. 
uhg; ee; try am; ap Function.lem2; try am.
rw H12; tv. 
Qed. 

Lemma function_sub_V : forall f g x:E,
Function.axioms g -> defined f x -> sub f g ->
V x f = V x g.
Proof. 
ir. 
cp H0; uh H0; ee. 
cp (Function.defined_lem H0 H2).
cp (H1 _ H4). 
cp (Function.lem1 H H5). 
rwi pr1_pair H6. 
transitivity (pr2 (pair x (V x f))). 
rw pr2_pair; tv. rw H6. 
rw pr2_pair; tv. 
Qed. 

(*** nb Function.defined_lem should be changed as its 
axioms hypothesis is extraneous ***)


Lemma domain_union : forall z:E, domain (union z) =
union (Image.create z domain).
Proof.
ir. ap extensionality; uhg; ir. ufi domain H. 
rwi Image.inc_rw H. nin H. ee. 
nin (union_exists H). ee. 
apply union_inc with (domain x1). uf domain;
rw Image.inc_rw. sh x0; xd. 
rw Image.inc_rw. sh x1; xd. 
nin (union_exists H). ee. 
rwi Image.inc_rw H1. nin H1; ee. uf domain;
rw Image.inc_rw. 
ufi domain H2. wri H2 H0. rwi Image.inc_rw H0. 
nin H0; ee. sh x2; xd. apply union_inc with x1. 
am. am. 
Qed.  

Lemma domain_tack_on : forall f x y:E,
domain (tack_on f (pair x y)) = tack_on (domain f) x.
Proof.
ir. ap extensionality; uhg; ir. 
ufi domain H; rwi Image.inc_rw H; nin H; ee. 
rwi tack_on_inc H; nin H. 
rw tack_on_inc; ap or_introl. 
uf domain; rw Image.inc_rw. sh x1. xd. 
rw tack_on_inc; ap or_intror. 
wr H0; rw H. rw pr1_pair. tv. 
uf domain; rw Image.inc_rw. 
rwi tack_on_inc H; nin H. 
ufi domain H; rwi Image.inc_rw H; nin H; ee. sh x1.
ee; try am. rw tack_on_inc. ap or_introl;am. 
sh (pair x y). ee. rw tack_on_inc; ap or_intror; tv. 
rw pr1_pair. sy; am. 
Qed. 

Lemma range_union : forall z:E, range (union z) =
union (Image.create z range).
Proof.
ir. ap extensionality; uhg; ir. ufi range H. 
rwi Image.inc_rw H. nin H. ee. 
nin (union_exists H). ee. 
apply union_inc with (range x1). uf range;
rw Image.inc_rw. sh x0; xd. 
rw Image.inc_rw. sh x1; xd. 
nin (union_exists H). ee. 
rwi Image.inc_rw H1. nin H1; ee. uf range;
rw Image.inc_rw. 
ufi range H2. wri H2 H0. rwi Image.inc_rw H0. 
nin H0; ee. sh x2; xd. apply union_inc with x1. 
am. am. 
Qed.  

Lemma range_tack_on : forall f x y:E,
range (tack_on f (pair x y)) = tack_on (range f) y.
Proof.
ir. ap extensionality; uhg; ir. 
ufi range H; rwi Image.inc_rw H; nin H; ee. 
rwi tack_on_inc H; nin H. 
rw tack_on_inc; ap or_introl. 
uf range; rw Image.inc_rw. sh x1. xd. 
rw tack_on_inc; ap or_intror. 
wr H0; rw H. rw pr2_pair. tv. 
uf range; rw Image.inc_rw. 
rwi tack_on_inc H; nin H. 
ufi range H; rwi Image.inc_rw H; nin H; ee. sh x1.
ee; try am. rw tack_on_inc. ap or_introl; am. 
sh (pair x y). ee. rw tack_on_inc; ap or_intror; tv. 
rw pr2_pair. sy; am. 
Qed. 





Lemma function_tack_on_axioms : forall f x y:E,
Function.axioms f -> ~inc x (domain f) ->
Function.axioms (tack_on f (pair x y)).
Proof.
ir. uhg; ee; ir. rwi tack_on_inc H1.

nin H1. uh H; ee; au. rw H1. 
rw pr1_pair; rw pr2_pair; tv. 
rwi tack_on_inc H1; rwi tack_on_inc H2; nin H1; nin H2.
uh H; ee; au. assert False. 
ap H0. rwi H2 H3. 
rwi pr1_pair H3. wr H3. 
ap Function.lem2; try am. elim H4. 
assert False. ap H0. 
rwi H1 H3; rwi pr1_pair H3. rw H3. 
ap Function.lem2; try am.
elim H4. rw H2; am. 
Qed. 


(**** now we create a function given a set x and a map f : x->E ***)

Definition tcreate (x:E) (f:x->E) :=
create x (fun y => (Yy (fun (hyp : inc y x) => f (B hyp)) emptyset)).

Lemma tcreate_value_type : forall x (f:x->E) y,
V (R y) (tcreate f) = f y.
Proof.
ir. uf tcreate. 
rw create_V_rewrite. 
assert (inc (R y) x). 
ap R_inc. 
apply Yy_if with H.
rw B_back. 
tv. ap R_inc. 
Qed.

Lemma tcreate_value_inc : forall x (f:x->E) y (hyp : inc y x),
V y (tcreate f) = f (B hyp).
Proof.
ir. assert (y = R (B hyp)). rww B_eq. 
transitivity (V (R (B hyp)) (tcreate f)). 
wr H. tv. ap tcreate_value_type. 
Qed.

Lemma domain_tcreate : forall x (f:x->E), domain (tcreate f) = x.
Proof.
ir. uf tcreate. rw create_domain. tv. 
Qed.


End Function.

Notation L := Function.create.




Module Transformation.


Definition covers (a b : E) (f : E1) :=
  forall x : E, inc x b -> ex (fun y : E => A (inc y a) (f y = x)).
Definition injects (a : E) (f : E1) :=
  forall x y : E, inc x a -> inc y a -> f x = f y -> x = y.


Definition inverse (a : E) (f : E1) (y : E) :=
  choose (fun x : E => (inc x a & f x = y)).


Definition axioms (a b : E) (f : E1) := forall x : E, inc x a -> inc (f x) b.

Lemma compose_axioms :
 forall (a b c : E) (f g : E1),
 axioms b c f -> axioms a b g -> axioms a c (fun x : E => f (g x)).
ir.
unfold axioms in |- *.
ir.
unfold axioms in H.
unfold axioms in H0.
au.
Qed.


Lemma identity_axioms : forall a : E, axioms a a (fun x : E => x).
ir.
unfold axioms in |- *.
ir.
am.
Qed.

Definition surjective (a b : E) (f : E1) := 
(axioms a b f & covers a b f).

Lemma surjective_inverse_axioms :
 forall (a b : E) (f : E1), surjective a b f -> axioms b a (inverse a f).
ir.
unfold axioms in |- *.
ir.
unfold inverse in |- *.
unfold surjective in H; xd.
unfold covers in H1; xd.
pose (H1 x H0).
pose (choose_pr e).
assert
 (A (inc (choose (fun x0 : E => A (inc x0 a) (f x0 = x))) a)
    (f (choose (fun x0 : E => A (inc x0 a) (f x0 = x))) = x)). 
am.
xd.
Qed.


Lemma surjective_inverse_right :
 forall (a b : E) (f : E1) (x : E),
 surjective a b f -> inc x b -> f (inverse a f x) = x.
ir.
unfold inverse in |- *.
unfold surjective in H; xd.
unfold covers in H1; xd.
pose (H1 x H0).
pose (choose_pr e).
assert
( inc (choose (fun x0 : E => (inc x0 a & f x0 = x))) a
& f (choose (fun x0 : E => (inc x0 a & f x0 = x))) = x). 
am. 
xd.
Qed.


Definition injective (a b : E) (f : E1) := 
( axioms a b f 
& injects a f).

Definition bijective (a b : E) (f : E1) :=
( axioms a b f
& surjective a b f
& injective a b f).

Definition are_inverse (a b : E) (f g : E1) :=
  axioms a b f
& axioms b a g
& (forall x : E, inc x a -> g (f x) = x)
& (forall y : E, inc y b -> f (g y) = y).

Lemma bijective_inverse :
 forall (a b : E) (f : E1),
 bijective a b f -> are_inverse a b f (inverse a f).
ir.
unfold are_inverse in |- *; xd.
unfold bijective in H; xd.

ap surjective_inverse_axioms.
unfold bijective in H; xd.


ir.
unfold bijective in H; ee.
unfold injective in H2.
ee.

assert (axioms b a (inverse a f)).
ap surjective_inverse_axioms; au.
unfold axioms in H4.
ap H3.
ap H4.
ap H. 
am.

am.

pose surjective_inverse_right.
assert (inc (f x) b).
ap H; am. 

pose (e _ _ _ _ H1 H5).
am.

ir.
unfold bijective in H; xd.
apply surjective_inverse_right with b.
am.

am.
Qed.

Lemma inverse_bijective :
 forall (a b : E) (f g : E1), are_inverse a b f g -> bijective a b f.
ir.
unfold bijective in |- *.
unfold are_inverse in H.
xd.
unfold surjective in |- *; xd.
unfold covers in |- *.
ir.
apply ex_intro with (g x).
xd.



unfold injective in |- *; xd.
unfold injects in |- *; ir.
rewrite <- H1.
rewrite <- H5.
rewrite H1; au.

am.
Qed. 

Lemma trans_sub_bijective : forall x y f u,
Transformation.injective x y f -> sub u x ->
Transformation.bijective u (Image.create u f) f.
Proof.
ir. 
uhg; dj. uhg; ee. 
ir. rw Image.inc_rw. sh x0; ee; try tv. 
uhg; ee; try am. uhg. ir. 
rwi Image.inc_rw H2. nin H2; ee. sh x1; ee; am. 
uhg; ee; try am. uhg; ir. uh H; ee. uh H6; ee.
ap H6; try am. ap H0; am.
ap H0; am. 
Qed. 

Lemma identity_bijective : forall x, 
Transformation.bijective x x (fun y => y).
Proof.
ir. uhg; dj. 
ap Transformation.identity_axioms. 
uhg; ee. am. uhg; ir. sh x0. ee. 
am. tv. uhg; ee; try am. 
uhg; ir. am. 
Qed. 

Lemma subidentity_injective : forall x y,
sub x y ->
Transformation.injective x y (fun z => z). 
Proof.
ir. uhg; ee. 
uhg; ee. ir; ap H; am. 
uhg; ir. am. 
Qed. 

Lemma compose_injective : forall x y z f g,
Transformation.injective x y f -> 
Transformation.injective y z g ->
Transformation.injective x z (fun y=> g (f y)).
Proof.
ir. uhg; dj. apply Transformation.compose_axioms
with y. lu. lu. uhg; ir. uh H; uh H0. ee.
assert (f x0 = f y0). ap H5. ap H. 
am. ap H; am. am. ap H6. am. am. am. 
Qed. 

Lemma compose_surjective : forall x y z f g,
Transformation.surjective x y f -> 
Transformation.surjective y z g ->
Transformation.surjective x z (fun y=> g (f y)).
Proof.
ir; uhg; dj. apply Transformation.compose_axioms with y; 
try lu. uhg; ir. uh H; uh H0; ee.
nin (H3 x0). ee. nin (H4 x1); ee. sh x2; ee; try am. 
rw H8. am. am. am. 
Qed. 

Lemma compose_bijective : forall x y z f g,
Transformation.bijective x y f ->
Transformation.bijective y z g ->
Transformation.bijective x z (fun y => g (f y)).
Proof.
ir. uhg; ee. 
apply Transformation.compose_axioms with y; lu. 
apply compose_surjective with y; lu. 
apply compose_injective with y; lu. 
Qed. 


End Transformation.


Module Map.

Import Function. 
Import Transformation. 

Definition axioms (a b f : E) :=
  Function.axioms f
& Function.domain f = a
& sub (Function.range f) b.

Lemma compose_axioms :
 forall a b c f g : E,
 axioms b c f -> axioms a b g -> axioms a c (Function.compose f g).
ir. unfold axioms in H, H0; xd. 
assert (Function.composable f g). unfold Function.composable in |- *. 
xd. rewrite H3; am. 
unfold axioms in |- *; xd. ap Function.compose_axioms.
rewrite Function.composable_domain; au. 
unfold sub in |- *; ir. 
assert (Function.axioms (Function.compose f g)). 
ap Function.compose_axioms. pose (Function.range_ex H7 H6). 
nin e; xd. pose (Function.compose_ev H8). 
rewrite H9 in e. rewrite e. ap H4. ap Function.range_inc. 
am. apply ex_intro with (V x0 g); xd. 
unfold Function.composable in H5; xd. 
ap H11. ap Function.range_inc. am. 
apply ex_intro with x0; xd. 
assert (Function.domain (Function.compose f g) = Function.domain g). 
ap Function.composable_domain. 
unfold Function.composable in |- *; xd. rewrite <- H12. 
am. Qed. 



Lemma identity_axioms : forall a : E, axioms a a (Function.identity a).
ir. unfold axioms in |- *; xd. ap Function.identity_axioms. 
ap Function.identity_domain. unfold sub in |- *; ir. 
assert (Function.axioms (Function.identity a)). 
ap Function.identity_axioms. pose (Function.range_ex H0 H). 
nin e; xd. rewrite Function.identity_domain in H1. 
rewrite Function.identity_ev in H2. rewrite <- H2; am. 
am. Qed. 



Definition surjective (a b f : E) :=
  axioms a b f 
& Transformation.covers a b (fun x : E => V x f).

Definition injective (a b f : E) :=
axioms a b f
& Transformation.injects a (fun x : E => V x f).

Definition bijective (a b f : E) :=
axioms a b f
& surjective a b f
& injective a b f.


Definition isomap x y := 
choose (Map.bijective x y).

Definition isotrans x y u:=
V u (isomap x y).

Definition are_isomorphic x y :=
exists f, Map.bijective x y f.

Lemma trans_map_axioms : forall x y f,
Transformation.axioms x y f =
Map.axioms x y (Function.create x f).
Proof.
ir. ap iff_eq; ir. uhg; ee. 
ap create_axioms. 
rw create_domain. tv. uhg; ir. 
rwi create_range H0. 
rwi Image.inc_rw H0. nin H0. ee. wr H1. 
uh H; ee. ap H. am. 


uhg. ir. uh H; ee. uh H2. 
ap H2. rw create_range. rw Image.inc_rw. 
sh x0. ee; try am; try tv. 
Qed.

Lemma trans_map_injective : forall x y f,
Transformation.injective x y f =
Map.injective x y (Function.create x f).
Proof.
ir. ap iff_eq; ir. 
uhg; ee. wr trans_map_axioms. 
uh H; ee; am. 
uhg. ir. rwi create_V_rewrite H2. 
rwi create_V_rewrite H2. uh H. 
ee. ap H3. am. 
am. am. am. am. 

uhg; ee. rw trans_map_axioms. uh H; ee; am. 
uhg; ir. uh H; ee. 
uh H3. 
cp (H3 _ _ H0 H1). ap H4. rw create_V_rewrite. 
rw create_V_rewrite. am. am. am. 
Qed.

Lemma trans_map_surjective : forall x y f,
Transformation.surjective x y f =
Map.surjective x y (Function.create x f).
Proof.
ir. 
ap iff_eq; ir. 
uhg; ee. 
wr trans_map_axioms. uh H; ee; am. 
uhg. ir. uh H; ee. uh H1. cp (H1 _ H0). 
nin H2. sh x1; ee. am. rw create_V_rewrite.
am. am. 
uhg; ee. rw trans_map_axioms. uh H; ee; am. 
uhg; ir. uh H; ee. uh H1.
cp (H1 _ H0). nin H2.
sh x1; ee. am. rwi create_V_rewrite H3. 
am. am. 
Qed.



Lemma trans_map_bijective : forall x y f,
Transformation.bijective x y f =
Map.bijective x y (Function.create x f).
Proof.
ir.
ap iff_eq; ir. uhg; ee.
wr trans_map_axioms; uh H; ee; am. 
wr trans_map_surjective; uh H; ee; am.
wr trans_map_injective; uh H; ee; am.
uhg; ee. 
rw trans_map_axioms; uh H; ee; am.
rw trans_map_surjective; uh H; ee; am.
rw trans_map_injective; uh H; ee; am.
Qed.

Lemma trans_bij_isomorphic : forall x y f,
Transformation.bijective x y f -> are_isomorphic x y.
Proof.
ir. uhg. 
sh (Function.create x f). 
wr trans_map_bijective; am.
Qed. 

Lemma isomap_bij : forall x y,
are_isomorphic x y -> Map.bijective x y (isomap x y). 
Proof.
ir. uh H. cp (choose_pr H). 
am. 
Qed. 



Lemma isotrans_bij : forall x y,
are_isomorphic x y -> 
Transformation.bijective x y (isotrans x y).
Proof.
ir. 
cp (isomap_bij H). 
rw trans_map_bijective. 
assert (create x (isotrans x y)= isomap x y).
uf  isotrans. 
rw create_rw. tv. 
uh H0; ee. uh H0; ee. rw H3; tv. lu. rw H1; am.
Qed. 




Lemma isomap_isotrans_rw : forall x y,
are_isomorphic x y ->
isomap x y = Function.create x (isotrans x y).
Proof.
ir. uf isotrans. rw create_rw. tv. 
cp (isomap_bij H). uh H0; ee. uh H0; ee. rw H3; tv. 
cp (isomap_bij H). uh H0; ee.
uh H0; ee. am. 
Qed. 



Lemma iso_isotrans_rw : forall x y,
are_isomorphic x y = 
Transformation.bijective x y (isotrans x y).
Proof.
ir; ap iff_eq; ir. 
ap isotrans_bij; am. 
uhg. sh (Function.create x (isotrans x y)). 
wr trans_map_bijective. am. 
Qed. 

Lemma iso_trans_ex_rw : forall x y,
are_isomorphic x y =
(exists f, Transformation.bijective x y f).
Proof.
ir; ap iff_eq; ir. 
sh (isotrans x y). 
wr iso_isotrans_rw; am. 
nin H. uhg. sh (Function.create x x0). 
wr trans_map_bijective; am. 
Qed. 

Lemma are_isomorphic_refl : forall x, are_isomorphic x x.
Proof.
ir. 
uhg. 
sh (Function.create x (fun y => y)). 
wr trans_map_bijective. ap identity_bijective. 
Qed.

Lemma are_inverse_symm : forall x y f g,
Transformation.are_inverse x y f g ->
Transformation.are_inverse y x g f.
Proof.
ir. uh H; uhg; xd. 
Qed. 

Lemma are_isomorphic_symm : forall x y, 
are_isomorphic x y ->
are_isomorphic y x.
Proof.
ir. rwi iso_isotrans_rw H. 
uhg. sh 
(Function.create y (Transformation.inverse x (isotrans x y))).
wr trans_map_bijective. 
apply Transformation.inverse_bijective with (isotrans x y). 
apply are_inverse_symm. 
apply Transformation.bijective_inverse. 
am. 
Qed.

Lemma are_isomorphic_trans : forall x z,
(exists y, (are_isomorphic x y & are_isomorphic y z)) ->
are_isomorphic x z.
Proof.
ir. nin H. ee. 
rwi iso_isotrans_rw H. rwi iso_isotrans_rw H0. 
rw iso_trans_ex_rw. 
sh (fun a => (isotrans x0 z (isotrans x x0 a))). 
apply compose_bijective with x0. am. am. 
Qed. 

End Map.

Module Bounded.

Definition property (p : EP) (x : E) :=
  forall y : E, (p y -> inc y x) & (inc y x -> p y). 


Definition axioms (p : EP) := ex (property p).


Definition create (p : EP) := choose (property p). 


Lemma criterion :
 forall p : EP,
 ex (fun x : E => forall y : E, p y -> inc y x) -> axioms p. 
ir. nin H. unfold axioms in |- *.
eapply ex_intro with (Z x p). unfold property in |- *.
ir; xd; ir. 
ap Z_inc. ap H; au. au. 
apply Z_pr with x. am. Qed. 



Lemma lem1 : forall (p : EP) (y : E), axioms p -> inc y (create p) -> p y.
ir. unfold create in H0. unfold axioms in H. 
pose (choose_pr H). unfold property in H0. 
unfold property in (type of p0). pose (p0 y). 
xd. Qed. 

Lemma lem2 : forall (p : EP) (y : E), axioms p -> p y -> inc y (create p).
ir. unfold create in |- *. unfold axioms in H. pose (choose_pr H). set (K := choose (property p)) in *. unfold property in (type of p0). pose (p0 y); xd. Qed. 

Lemma inc_create :
 forall (p : EP) (y : E), axioms p -> inc y (create p) = p y. 
ir. 
ap iff_eq; ir. ap lem1; am. 
ap lem2; am. 
Qed. 

Lemma trans_criterion :
 forall (p : EP) (f : E1) (x : E),
 (forall y : E, p y -> ex (fun z : E => A (inc z x) (f z = y))) ->
 axioms p.
ir. 
ap criterion. 
sh (Image.create x f). 
ir. ap Image.show_inc. ap H. am. 
Qed. 

Lemma little_criterion :
 forall (p : EP) (x : E) (f : x -> E),
 (forall y : E, p y -> exists a : x, f a = y) -> axioms p. 
ir. 
ap criterion; sh (IM f). 
ir. ap IM_inc. ap H; am. 
Qed. 


End Bounded.


Module Quotient.


Definition is_part (a : E) (r : E2P) (y : E) :=
sub y a
& (forall x z : E, inc x y -> r x z -> inc z a -> inc z y)
& (forall x z : E, inc x y -> r z x -> inc z a -> inc z y). 

Definition is_class (a : E) (r : E2P) (y : E) :=
is_part a r y
& nonempty y
& (forall z : E, 
        is_part a r z -> nonempty (intersection2 y z) -> sub y z).

Lemma lem1 : forall (a : E) (r : E2P), is_part a r a.
ir.
unfold is_part in |- *; xd.
unfold sub in |- *; ir; au.
Qed.

Definition parts_containing (a : E) (r : E2P) (y : E) :=
  Z (powerset a) (fun z : E => (is_part a r z & inc y z)). 


Definition class_of (a : E) (r : E2P) (y : E) :=
  intersection (parts_containing a r y). 

Lemma inc_parts_containing :
 forall (a : E) (r : E2P) (y z : E),
 inc y z -> is_part a r z -> inc z (parts_containing a r y). 
ir. unfold parts_containing in |- *. ap Z_inc. 
ap powerset_inc. unfold is_part in H0; xd. 
xd. Qed. 

Lemma class_of_origin :
 forall (a : E) (r : E2P) (y : E), inc y a -> inc y (class_of a r y). 
ir. unfold class_of in |- *. ap intersection_inc. 
apply nonempty_intro with a. ap inc_parts_containing. 
am. ap lem1. ir. 
unfold parts_containing in H0. cp (Z_pr H0). cbv beta in H1.
xd; au. Qed. 


Lemma class_of_sub :
 forall (a : E) (r : E2P) (y z : E),
 inc y z -> is_part a r z -> sub (class_of a r y) z. 
ir. unfold class_of in |- *. ap intersection_sub. 
ap inc_parts_containing; au. Qed. 




Lemma class_of_part :
 forall (a : E) (r : E2P) (y : E), inc y a -> is_part a r (class_of a r y).
ir.
unfold is_part in |- *; xd; ir.
unfold class_of in |- *.
ap intersection_sub.
unfold parts_containing in |- *.
ap Z_inc.
ap powerset_inc.
unfold sub in |- *; ir; au.

xd.
ap lem1.

unfold class_of in |- *.
ap intersection_inc.
apply nonempty_intro with a.
unfold parts_containing in |- *.
ap Z_inc.
ap powerset_inc; unfold sub in |- *; ir; au.

xd.
ap lem1.


ir.
assert (is_part a r y0).
unfold parts_containing in H3.

cp (Z_pr H3). cbv beta in H4. 
xd.

unfold is_part in H4; xd.
apply H5 with x.
apply intersection_forall with (parts_containing a r y).
exact H0. am. am. am. 


unfold class_of in |- *.
ap intersection_inc.
apply nonempty_intro with a.
unfold parts_containing in |- *.
ap Z_inc.
ap powerset_inc; unfold sub in |- *; ir; au.

xd.
ap lem1.


ir.
assert (is_part a r y0).
unfold parts_containing in H3.

cp (Z_pr H3). cbv beta in H4. 
xd.

unfold is_part in H4; xd.
apply H6 with x.
apply intersection_forall with (parts_containing a r y).
exact H0.
am. am. am.

Qed.

Ltac Inbeta v :=
  match goal with
  | v:?X1 |- _ =>
      assert (inbeta_identx : X1);
       [ exact v
       | clear v; cbv beta in inbeta_identx; cp inbeta_identx;
          clear inbeta_identx ]
  end.

Ltac zpr b := set (zpr_identx := Z_pr b); Inbeta zpr_identx.

Ltac chpr b := set (zpr_identx := choose_pr b); Inbeta zpr_identx.


Lemma class_of_class :
 forall (a : E) (r : E2P) (y : E), inc y a -> is_class a r (class_of a r y).
ir.
unfold is_class in |- *; xd; ir.
ap class_of_part.
am.

apply nonempty_intro with y.
unfold class_of in |- *.
ap intersection_inc.
apply nonempty_intro with a.
unfold parts_containing in |- *; ap Z_inc; xd.
ap powerset_inc; unfold sub in |- *; ir; au.

ap lem1.

ir.
unfold parts_containing in H0.
zpr H0. 
xd.

unfold class_of in |- *.
ap intersection_sub.
unfold parts_containing in |- *.
ap Z_inc.
ap powerset_inc.
unfold is_part in H0.
xd.

xd.
nin H1.
pose (intersection2_first H1).
pose (intersection2_second H1).
ap excluded_middle; unfold not in |- *; ir.
pose (Z (class_of a r y) (fun v : E => inc v z -> False)). 
assert (is_part a r e). unfold is_part in |- *. 
xd. apply sub_trans with (class_of a r y). 
unfold e in |- *; ap Z_sub. unfold sub in |- *; ir. 
unfold class_of in H3. apply intersection_forall with (parts_containing a r y). am. unfold parts_containing in |- *. 
ap Z_inc. ap powerset_inc; unfold sub in |- *; ir; au. xd; try ap lem1; au. 

ir. unfold e in |- *; Ztac. unfold class_of in |- *. 
ap intersection_inc; ir. 
apply nonempty_intro with a.
unfold parts_containing in |- *; Ztac; xd.
ap powerset_inc; unfold sub in |- *; ir; au.

ap lem1. unfold parts_containing in H6. 
zpr H6. xd. assert (inc x (class_of a r y)). 
assert (sub e (class_of a r y)). unfold e in |- *; ap Z_sub. 
ap H9. am. unfold class_of in H9. 
assert (inc x y1). apply intersection_forall with (parts_containing a r y). am. unfold parts_containing in |- *; ap Z_inc. ap powerset_inc. 
unfold is_part in H7; xd; au. xd. 
unfold is_part in H7; xd. apply H11 with x; am. 
ir. assert (inc x z). unfold is_part in H0; xd. 
apply H8 with z0; au. assert (sub e a). 
apply sub_trans with (class_of a r y). 
unfold e in |- *; ap Z_sub. ap class_of_sub. 
am. ap lem1. ap H9; am. 
unfold e in H3. zpr H3. 
ap H8; am. 
ir. unfold e in |- *; ap Z_inc. 
assert (sub e (class_of a r y)). unfold e in |- *; ap Z_sub. 
ap H6. unfold e in |- *; ap Z_inc. 
assert (is_part a r (class_of a r y)). ap class_of_part.
am. unfold is_part in H7.
xd. apply H9 with x. ap H6. am. 
am. am. ir. assert (inc x z). 
unfold is_part in H0; xd. apply H8 with z0. 
am. am. assert (sub e a). apply sub_trans with (class_of a r y). unfold e in |- *; ap Z_sub. 
ap class_of_sub. am. ap lem1. ap H10; am. unfold e in H3. zpr H3. 
ap H9; am. 
ir.
assert (inc x z). unfold is_part in H0; xd. 
apply H7 with z0; au. assert (sub e a).
apply sub_trans with (class_of a r y). unfold e in |- *; ap Z_sub. 
ap class_of_sub. am. ap lem1.
ap H9; au. unfold e in H3. zpr H3. 
ap H8; au. assert (sub (class_of a r y) e). 
ap class_of_sub. unfold e in |- *; ap Z_inc. 
ap class_of_origin; au. am. am.
assert (inc y0 e).
ap H4. am. unfold e in H5. 
zpr H5. ap H6; au. 
Qed. 


Lemma class_rep_inc :
 forall (a : E) (r : E2P) (x : E), is_class a r x -> inc (rep x) x. 
ir. unfold is_class in H. xd. unfold rep in |- *. 
ap choose_pr. nin H0. 
apply ex_intro with y; au. Qed. 

Lemma class_eq_class_of :
 forall (a : E) (r : E2P) (y : E),
 is_class a r y -> forall x : E, inc x y -> class_of a r x = y.
ir. ap extensionality. ap class_of_sub; au. 
unfold is_class in H; xd; au. unfold is_class in H. 
xd. ap H2. ap class_of_part. unfold is_part in H; xd. apply nonempty_intro with x. 
ap intersection2_inc; au. ap class_of_origin. 
unfold is_part in H; xd. Qed. 






Lemma intersecting_classes_eq :
 forall (a : E) (r : E2P) (x y : E),
 is_class a r x -> is_class a r y -> nonempty (intersection2 x y) -> x = y.
ir. pose (class_eq_class_of H). pose (class_eq_class_of H0). 
nin H1. pose (intersection2_first H1). 
pose (intersection2_second H1). 
pose (e _ i). pose (e0 _ i0).
rewrite <- e1. rewrite <- e2.
tv. Qed.  


Lemma intersecting_classes_of_eq :
 forall (a : E) (r : E2P) (x y : E),
 inc x a ->
 inc y a ->
 nonempty (intersection2 (class_of a r x) (class_of a r y)) ->
 class_of a r x = class_of a r y.
ir.
pose class_of_class.
apply intersecting_classes_eq with a r; au.
Qed.



Definition quotient (a : E) (r : E2P) :=
  Z (powerset a) (fun y : E => is_class a r y).

Lemma in_quotient_is_class :
 forall (a : E) (r : E2P) (x : E), inc x (quotient a r) -> is_class a r x.
ir. unfold quotient in H. zpr H; au. 
Qed. 

Lemma is_class_in_quotient :
 forall (a : E) (r : E2P) (x : E), is_class a r x -> inc x (quotient a r).
ir. unfold quotient in |- *; ap Z_inc. 
ap powerset_inc. unfold is_class in H.
xd. unfold is_part in H; xd; au. am. 
Qed.


Lemma class_of_in_quotient :
 forall (a : E) (r : E2P) (x : E),
 inc x a -> inc (class_of a r x) (quotient a r).
ir. unfold quotient in |- *; ap Z_inc.
ap powerset_inc. ap class_of_sub; au. 
ap lem1. ap class_of_class; au. 
Qed. 


Lemma inc_class_of :
 forall (a : E) (r : E2P) (x y : E),
 inc x a -> inc y a -> r x y -> inc x (class_of a r y).
ir.
assert (is_part a r (class_of a r y)).
ap class_of_part.
am.

unfold is_part in H2.
xd.
set (x_ := class_of_origin).
apply H4 with y; au.
Qed.

Lemma related_classes_eq :
 forall (a : E) (r : E2P) (x y : E),
 inc x a -> inc y a -> r x y -> class_of a r x = class_of a r y.
ir.
ap intersecting_classes_of_eq; au.
apply nonempty_intro with x.
pose class_of_origin.
pose inc_class_of.
ap intersection2_inc; au.
Qed.


Definition class_in (q x : E) := choose (fun y : E => A (inc y q) (inc x y)).



Lemma class_of_eq_class :
 forall (a : E) (r : E2P) (x : E),
 inc x a -> class_of a r x = class_in (quotient a r) x.
ir. ap class_eq_class_of. 
assert (inc (class_in (quotient a r) x) (quotient a r)). 
unfold class_in in |- *. 
assert (ex (fun y : E => A (inc y (quotient a r)) (inc x y))). 
apply ex_intro with (class_of a r x). 
xd. ap class_of_in_quotient; au. 
ap class_of_origin; au. 
chpr H0. xd. unfold quotient in H0. 
zpr H0. am. 
assert (ex (fun y : E => A (inc y (quotient a r)) (inc x y))).
apply ex_intro with (class_of a r x). 
xd. ap class_of_in_quotient; au. 
ap class_of_origin; au. 
chpr H0. xd.  
Qed.

Lemma class_of_rep :
 forall (a : E) (r : E2P) (x : E),
 inc x (quotient a r) -> class_of a r (rep x) = x. 
ir. ap class_eq_class_of. ap in_quotient_is_class; au.
assert (is_class a r x). ap in_quotient_is_class; au.
unfold is_class in H0; xd. 
unfold rep in |- *. nin H1. ap choose_pr. 
apply ex_intro with y. am. 
Qed. 


Definition is_eq_reln (a : E) (r : E2P) :=
  (forall x : E, inc x a -> r x x)
& (forall x y : E, inc x a -> inc y a -> r x y -> r y x)
& (forall x y z : E,
        inc x a -> inc y a -> inc z a -> r x y -> r y z -> r x z).

Definition equivalent (a : E) (r : E2P) (x y : E) :=
  inc x a
& inc y a
& class_of a r x = class_of a r y.

Lemma equivalent_symm :
 forall (a : E) (r : E2P) (x y : E), equivalent a r x y -> equivalent a r y x.
ir.
unfold equivalent in H.
unfold equivalent in |- *. xd.
Qed.

Lemma equivalent_refl :
 forall (a : E) (r : E2P) (x : E), inc x a -> equivalent a r x x.
ir; unfold equivalent in |- *; xd.
Qed.

Lemma equivalent_trans :
 forall (a : E) (r : E2P) (x y z : E),
 equivalent a r x y -> equivalent a r y z -> equivalent a r x z.
unfold equivalent in |- *; ir; xd.
transitivity (class_of a r y); au.
Qed.

Lemma equivalent_is_eq_reln :
 forall (a : E) (r : E2P), is_eq_reln a (equivalent a r).
ir.
unfold is_eq_reln in |- *; xd; ir.
ap equivalent_refl; au.
ap equivalent_symm; au.
apply equivalent_trans with y; au.
Qed.

Lemma related_equivalent :
 forall (a : E) (r : E2P) (x y : E),
 inc x a -> inc y a -> r x y -> equivalent a r x y.
ir.
unfold equivalent in |- *; xd.
ap intersecting_classes_of_eq; au.
apply nonempty_intro with x.
ap intersection2_inc.
ap class_of_origin; au.
ap inc_class_of; au.
Qed.

Lemma equivalent_related :
 forall (a : E) (r : E2P) (x y : E),
 is_eq_reln a r -> equivalent a r x y -> r x y.
ir.
unfold is_eq_reln in H; xd.
set (z := Z a (fun u : E => r x u)).
assert (inc y z).
unfold equivalent in H0; xd.
assert (sub (class_of a r y) z).
rewrite <- H4.
ap class_of_sub.
unfold z in |- *; Ztac.

unfold is_part in |- *; xd.
unfold z in |- *; ap Z_sub.

ir.
unfold z in |- *; Ztac.
apply H2 with x0.
am.

assert (sub z a); [ unfold z in |- *; ap Z_sub | ap H8; au ].

au.

unfold z in H5; Ztac.

am.

ir.
unfold z in |- *; Ztac.
apply H2 with x0; au.
assert (sub z a); [ unfold z in |- *; ap Z_sub | ap H8; au ].

unfold z in H5; Ztac.

ap H1; au.
assert (sub z a); [ unfold z in |- *; ap Z_sub | ap H8; au ].

ap H5.
ap class_of_origin.
am.

unfold z in H3; Ztac.
Qed.


Lemma equivalent_to_rep :
 forall (a : E) (r : E2P) (x : E),
 inc x a -> equivalent a r x (rep (class_of a r x)).
ir.
unfold equivalent in |- *; xd.
assert (sub (class_of a r x) a).
ap class_of_sub; au.
ap lem1.

ap H0.
ap nonempty_rep.
apply nonempty_intro with x; ap class_of_origin.
am.

ap intersecting_classes_of_eq.
am.

assert (sub (class_of a r x) a).
set (x_ := lem1); ap class_of_sub; au.

ap H0.
ap nonempty_rep.
apply nonempty_intro with x; ap class_of_origin.
am.

apply nonempty_intro with (rep (class_of a r x)).
ap intersection2_inc.
ap nonempty_rep.
apply nonempty_intro with x; ap class_of_origin.
am.

ap class_of_origin.
assert (sub (class_of a r x) a).
ap class_of_sub.
au.

ap lem1.

ap H0.
ap nonempty_rep.
apply nonempty_intro with x.
ap class_of_origin.
am.
Qed.

Lemma equivalent_universal :
 forall (a : E) (r s : E2P),
 is_eq_reln a s ->
 (forall x y : E, inc x a -> inc y a -> r x y -> s x y) ->
 forall x y : E, equivalent a r x y -> s x y.
ir.
set (z := Z a (fun u : E => s x u)).
assert (sub z a).
unfold z in |- *; ap Z_sub.

unfold sub in H2.
unfold equivalent in H1; xd.
assert (sub (class_of a r y) z).
rewrite <- H4.
ap class_of_sub.
unfold z in |- *; Ztac.
unfold is_eq_reln in H; xd.

unfold is_part in |- *; xd.
ir.
unfold z in |- *; Ztac.
unfold is_eq_reln in H; xd.
apply H9 with x0; au.
unfold z in H5; Ztac.

ir.
unfold z in |- *; Ztac.
unfold is_eq_reln in H; xd.
apply H9 with x0; au.
unfold z in H5; Ztac.

assert (inc y z).
ap H5; ap class_of_origin.
au.

unfold z in H6; Ztac.
Qed.

Definition quotient_endo (q : E) (endo : E1) (x : E) :=
  class_in q (endo (rep x)).

Definition endo_within (a : E) (endo : E1) :=
  forall x : E, inc x a -> inc (endo x) a.

Definition endo_compatible (a : E) (r : E2P) (endo : E1) :=
  forall x y : E, inc x a -> inc y a -> r x y -> r (endo x) (endo y).

Definition endo_passes_to_quotient (q : E) (endo : E1) :=
  forall x a : E,
  inc x q -> inc a x -> class_in q (endo a) = quotient_endo q endo x.

Lemma endo_compatible_passes :
 forall (a : E) (r : E2P) (endo : E1),
 endo_within a endo ->
 endo_compatible a r endo -> endo_passes_to_quotient (quotient a r) endo.
ir.
unfold endo_passes_to_quotient in |- *.
set (q := quotient a r) in *.
ir.
assert (is_class a r x).
ap in_quotient_is_class.
am.

assert (class_of a r (rep x) = x).
ap class_of_rep.
am.

assert (class_of a r a0 = x).
ap class_eq_class_of.
am.

am.

set (z := Z a (fun u : E => class_in q (endo u) = quotient_endo q endo x)).
assert (sub z a). unfold z in |- *; ap Z_sub.

assert (sub (class_of a r (rep x)) z).
ap class_of_sub.
unfold z in |- *; Ztac.
unfold is_class in H3.
xd.
unfold is_part in H3; xd.
ap H3.
ap nonempty_rep.
am.

unfold is_part in |- *; xd.
ir.
unfold z in |- *; Ztac.
transitivity (class_in q (endo x0)).
unfold q in |- *.
assert (inc x0 a).
ap H6; au.

rewrite <- class_of_eq_class.
rewrite <- class_of_eq_class.
sy.
ap related_classes_eq.
ap H.
am.

ap H; am.

ap H0; au.

ap H.
au.

ap H; au.

unfold z in H7; Ztac.

ir.
unfold z in |- *; Ztac.
transitivity (class_in q (endo x0)).
assert (inc x0 a).
ap H6; au.

unfold q in |- *.
rewrite <- class_of_eq_class.
rewrite <- class_of_eq_class.
ap related_classes_eq.
ap H; au.

ap H; au.

ap H0; au.

ap H; au.

ap H; au.

unfold z in H7; Ztac.

assert (inc a0 z).
ap H7.
rewrite H4; au.

unfold z in H8; Ztac.
Qed.

Definition quotient_op (q : E) (op : E2) (x y : E) :=
  class_in q (op (rep x) (rep y)).

Definition op_within (a : E) (op : E2) :=
  forall x y : E, inc x a -> inc y a -> inc (op x y) a.

Definition op_left_compatible (a : E) (r : E2P) (op : E2) :=
  forall x y z : E,
  inc x a -> inc y a -> inc z a -> r x z -> r (op x y) (op z y).

Definition op_right_compatible (a : E) (r : E2P) (op : E2) :=
  forall x y z : E,
  inc x a -> inc y a -> inc z a -> r y z -> r (op x y) (op x z).

Definition op_passes_to_quotient (q : E) (op : E2) :=
  forall x y a b c d : E,
  inc x q ->
  inc y q -> inc a x -> inc b y -> class_in q (op a b) = quotient_op q op x y. 



Lemma op_left_very_compatible :
 forall (a : E) (r : E2P) (op : E2),
 op_within a op ->
 op_left_compatible a r op ->
 forall x b c d : E,
 inc x (quotient a r) ->
 inc b x ->
 inc c x ->
 inc d a ->
 class_in (quotient a r) (op b d) = class_in (quotient a r) (op c d).
ir.
set (f := fun u : E => op u d).
assert (endo_within a f).
unfold endo_within in |- *.
ir.
unfold f in |- *.
ap H; au.

assert (endo_compatible a r f).
unfold endo_compatible in |- *.
ir.
unfold f in |- *.
ap H0; au.

pose (endo_compatible_passes H5 H6).
unfold endo_passes_to_quotient in (type of e).
unfold f in (type of e).
transitivity (quotient_endo (quotient a r) (fun u : E => op u d) x).
ap e; au.

sy.
ap e; au.
Qed. 

Lemma op_right_very_compatible :
 forall (a : E) (r : E2P) (op : E2),
 op_within a op ->
 op_right_compatible a r op ->
 forall x b c d : E,
 inc x (quotient a r) ->
 inc b a ->
 inc c x ->
 inc d x ->
 class_in (quotient a r) (op b c) = class_in (quotient a r) (op b d).
ir.
set (f := fun u : E => op b u).
assert (endo_within a f).
unfold endo_within in |- *.
ir.
unfold f in |- *.
ap H; au.

assert (endo_compatible a r f).
unfold endo_compatible in |- *.
ir.
unfold f in |- *.
ap H0; au.

pose (endo_compatible_passes H5 H6).
unfold endo_passes_to_quotient in (type of e).
unfold f in (type of e).
transitivity (quotient_endo (quotient a r) (fun u : E => op b u) x).
ap e; au.

sy.
ap e; au.
Qed. 



Lemma op_compatible_passes :
 forall (a : E) (r : E2P) (op : E2),
 op_within a op ->
 op_left_compatible a r op ->
 op_right_compatible a r op -> op_passes_to_quotient (quotient a r) op.
ir.
unfold op_passes_to_quotient in |- *; ir.
unfold quotient_op in |- *.
assert (inc (rep x) x).
ap nonempty_rep.
apply nonempty_intro with a0.
am.

assert (inc (rep y) y).
ap nonempty_rep; apply nonempty_intro with b; au.

transitivity (class_in (quotient a r) (op a0 (rep y))).
apply op_right_very_compatible with y; au.
assert (inc x (powerset a)).
unfold quotient in H2; Ztac.

assert (sub x a).
ap powerset_sub.
am.

ap H9.
am.

apply op_left_very_compatible with x; au.
assert (sub y a).
ap powerset_sub.
unfold quotient in H3; Ztac.

ap H8; au.
Qed.

End Quotient.


Module Cartesian.

Definition in_record (a : E) (f : E1) (x : E) :=
  is_pair x
& inc (pr1 x) a
& inc (pr2 x) (f (pr1 x)).

Record recordRec (a : E) (f : E1) : E :=  {first : a; second : f (R first)}.

Definition recordMap (a : E) (f : E1) (i : recordRec a f) :=
  pair (R (first i)) (R (second i)).

Lemma in_record_ex :
 forall (a : E) (f : E1) (x : E),
 in_record a f x -> exists i : recordRec a f, recordMap i = x.
ir.
unfold in_record in H; xd.
set (u := B H0).
assert (R u = pr1 x).
unfold u in |- *.
ap B_eq.

assert (inc (pr2 x) (f (R u))).
rewrite H2; am.

set (v := B H3).
pose (Build_recordRec (a:=a) (f:=f) (first:=u) v).
apply ex_intro with r.
transitivity (pair (R u) (R v)).
tv.

assert (R v = pr2 x).
unfold v in |- *.
ap B_eq.

rewrite H4.
assert (R u = pr1 x); au.
rewrite H5.
ap pair_recov.
am.
Qed.

Lemma in_record_bounded :
 forall (a : E) (f : E1), Bounded.axioms (in_record a f).
ir.
ap Bounded.criterion.
apply ex_intro with (IM (recordMap (a:=a) (f:=f))).
ir.
ap IM_inc.
ap in_record_ex.
am.
Qed.

Definition record (a : E) (f : E1) := Bounded.create (in_record a f).

Lemma record_in :
 forall (a : E) (f : E1) (x : E), inc x (record a f) -> in_record a f x.
ir.
unfold record in H.
pose (in_record_bounded a f).
pose (Bounded.lem1 a0 H).
am.
Qed.

Lemma record_pr :
 forall (a : E) (f : E1) (x : E),
 inc x (record a f) ->
 (is_pair x & inc (pr1 x) a & inc (pr2 x) (f (pr1 x))).
ir. pose (record_in H). am.
Qed.

Lemma record_inc :
 forall (a : E) (f : E1) (x : E), in_record a f x -> inc x (record a f).
ir.
unfold record in |- *.
ap Bounded.lem2.
ap in_record_bounded.
am.
Qed.

Lemma record_pair_pr :
 forall (a : E) (f : E1) (x y : E),
 inc (pair x y) (record a f) -> (inc x a & inc y (f x)).
ir.
xd.
pose (record_in H).
unfold in_record in (type of i); xd.
rewrite pr1_pair in H1.
am.

pose (record_in H).
unfold in_record in (type of i); xd.
rewrite pr1_pair in H2.
rewrite pr2_pair in H2.
am.
Qed.

Lemma record_pair_inc :
 forall (a : E) (f : E1) (x y : E),
 inc x a -> inc y (f x) -> inc (pair x y) (record a f).
ir.
ap record_inc.
unfold in_record in |- *; xd.
ap pair_is_pair.
rewrite pr1_pair; am.
rewrite pr2_pair; rewrite pr1_pair; am.
Qed.

Definition product (a b : E) := record a (fun x : E => b).

Lemma product_pr :
 forall a b u : E,
 inc u (product a b) -> (is_pair u & inc (pr1 u) a & inc (pr2 u) b).
ir. unfold product in H. pose (record_pr H). xd.
Qed.

Lemma product_inc :
 forall a b u : E,
 is_pair u -> inc (pr1 u) a -> inc (pr2 u) b -> inc u (product a b).
ir. unfold product in |- *. ap record_inc. unfold in_record in |- *; xd.
Qed.

Lemma product_pair_pr :
 forall a b x y : E, inc (pair x y) (product a b) -> (inc x a & inc y b).
ir. unfold product in H. pose (record_pair_pr H). am.
Qed.

Lemma product_pair_inc :
 forall a b x y : E, inc x a -> inc y b -> inc (pair x y) (product a b).
ir. unfold product in |- *. ap record_pair_inc; au.
Qed.


End Cartesian.

Export Cartesian.

Module Function_Set.

Definition in_function_set (a : E) (f : E1) (u : E) :=
  Function.axioms u
& Function.domain u = a
& (forall y : E, inc y a -> inc (V y u) (f y)).

Lemma in_fs_sub_record :
 forall (a : E) (f : E1) (u : E), in_function_set a f u -> sub u (record a f).
ir.
unfold in_function_set in H; xd.
unfold sub in |- *; ir.
pose (Function.pr2_V H H2).
assert (Function.axioms u).
am.

unfold Function.axioms in H3; xd.
pose (H3 _ H2).
rewrite <- e0.
ap record_pair_inc.
rewrite <- H0.
ap Function.lem2; au.

rewrite e.
ap H1.
rewrite <- H0.
ap Function.lem2; au.
Qed.

Lemma in_fs_eq_L :
 forall (a : E) (f : E1) (u : E),
 in_function_set a f u -> u = Function.create a (fun y : E => V y u).
ir.
unfold in_function_set in H; xd.
rewrite <- H0.
sy.
ap Function.create_recovers.
am.
Qed.

Lemma in_fs_for_L :
 forall (a : E) (f v : E1),
 (forall y : E, inc y a -> inc (v y) (f y)) ->
 in_function_set a f (Function.create a v).
ir.
unfold in_function_set in |- *; xd.
ap Function.create_axioms.

ap Function.create_domain.

ir.
rewrite Function.create_V_rewrite.
ap H; au.

am.
Qed.

Lemma in_fs_bounded :
 forall (a : E) (f : E1), Bounded.axioms (in_function_set a f).
ir.
ap Bounded.criterion.
apply ex_intro with (powerset (record a f)).
ir.
ap powerset_inc.
ap in_fs_sub_record; au.
Qed.

Definition function_set (a : E) (f : E1) :=
  Bounded.create (in_function_set a f).

Lemma function_set_iff :
 forall (a : E) (f : E1) (u : E),
 inc u (function_set a f) <-> in_function_set a f u.
ir.
unfold iff in |- *; xd; ir.
unfold function_set in H.
ap Bounded.lem1.
ap in_fs_bounded.

am.

unfold function_set in |- *.
ap Bounded.lem2.
ap in_fs_bounded.

am.
Qed.

Lemma function_set_sub_powerset_record :
 forall (a : E) (f : E1), sub (function_set a f) (powerset (record a f)).
ir.
unfold sub in |- *; ir.
pose (function_set_iff a f x).
unfold iff in (type of i); xd.
pose (H0 H).
ap powerset_inc.
ap in_fs_sub_record; au.
Qed.

Lemma function_set_pr :
 forall (a : E) (f : E1) (u : E),
 inc u (function_set a f) ->
 (in_function_set a f u 
 & Function.axioms u
 & Function.domain u = a
 & (forall y : E, inc y a -> inc (V y u) (f y))).
ir.
assert (in_function_set a f u).
pose (function_set_iff a f u).
unfold iff in (type of i); xd.

unfold in_function_set in H0; xd.
unfold in_function_set in |- *; xd.
Qed.

Lemma function_set_inc :
 forall (a : E) (f : E1) (u : E),
 Function.axioms u ->
 Function.domain u = a ->
 (forall y : E, inc y a -> inc (V y u) (f y)) -> inc u (function_set a f).
ir.
pose (function_set_iff a f u).
unfold iff in (type of i); xd.
ap H3.
unfold in_function_set in |- *; xd.
Qed.


Lemma in_function_set_inc :
 forall (a : E) (f : E1) (u : E),
 in_function_set a f u -> inc u (function_set a f).
ir.
pose (function_set_iff a f u).
unfold iff in (type of i); xd.
Qed.


End Function_Set.







Set Implicit Arguments.
Unset Strict Implicit.

Require Import Arith.
Require Export functions.


Module String.

Inductive string : E := 
DOT : string |
a_:string->string |
b_:string->string |
c_:string->string |
d_:string->string |
e_:string->string |
f_:string->string |
g_:string->string |
h_:string->string |
i_:string->string |
j_:string->string |
k_:string->string |
l_:string->string |
m_:string->string |
n_:string->string |
o_:string->string |
p_:string->string |
q_:string->string |
r_:string->string |
s_:string->string |
t_:string->string |
u_:string->string |
v_:string->string |
w_:string->string |
x_:string->string |
y_:string->string |
z_:string->string .

End String. 




Module Notation.
Import Function.
Export String.


Definition mask (*: Prop -> E -> E *)  (P : Prop) (x : E) := 
Y P x emptyset.

Lemma mask_in : forall (P : Prop) (x : E), P -> mask P x = x. 
ir. uf mask. ap Y_if. am. tv. 
Qed. 

Lemma mask_out : forall (P : Prop) (x : E), ~ P -> 
mask P x = emptyset.
ir. uf mask. ap Y_if_not. am. tv.  
Qed. 

Definition is_notation f :=
Function.axioms f &
Function.domain f = string.

Definition stop := L string (fun s => emptyset).

Lemma is_notation_stop : is_notation stop.
Proof.
uhg; ee. uf stop. 
app create_axioms. 
uf stop. rww create_domain. 
Qed.

Lemma V_stop : forall x, V x stop = emptyset.
Proof.
ir. uf stop. 
apply by_cases with (inc x string); ir. 
rww create_V_rewrite. 
rww create_V_out. 
Qed.

Definition denote str obj old :=
L string (fun s => (Y (s = str) obj (V s old))).

Lemma is_notation_denote : forall str obj old,
is_notation old -> is_notation (denote str obj old).
Proof.
ir. uhg; ee. 
uf denote. aw.
uf denote. aw. 
Qed.

Lemma V_denote_new : forall str obj old x,
x = str -> inc x string -> V x (denote str obj old) = obj.
Proof.
ir. uf denote. 
aw. rww Y_if_rw. 
Qed.

Lemma V_denote_old : forall str obj old x,
~x=str -> inc x string -> V x (denote str obj old) = V x old.
Proof.
ir. uf denote. aw. rww Y_if_not_rw. 
Qed. 



Ltac show_string :=
match goal with
| |- inc ?X1 string  => try am; unfold X1; ap R_inc
| _ => fail
end.
 
Lemma R_string_inj : forall a b:string,
~a=b -> ~(R a = R b).
Proof.
ir. uhg; ir. ap H. ap R_inj. am. 
Qed.

Ltac show_different :=
match goal with
| |- ~(?X1 = ?X2) => 
(try (unfold X1); try (unfold X2);
ap R_string_inj; discriminate)
| _ => fail
end. 

Ltac drw_solve := solve [tv | show_different | am | show_string].

Ltac drw_new := 
rewrite V_denote_new; [idtac | drw_solve | drw_solve].

Ltac drw_old :=
rewrite V_denote_old; [idtac | drw_solve | drw_solve].

Ltac drw_stop := rewrite V_stop.

Ltac drw := first [
drw_new ; drw | drw_old; drw | drw_stop ; drw | 
tv | am | idtac].

(*
Ltac drw :=
first [
rewrite V_denote_new; solve [drw_solve |drw] |
rewrite V_denote_old; solve [drw_solve |drw] |
rewrite V_stop].
*)



Definition Underlying := R (u_(d_(r_ DOT))).  


Definition U (x : E) := V Underlying x.


Definition unary (x:E) (f:E1) := L x f.

Lemma V_unary : forall x f a, inc a x -> 
V a (unary x f) = f a.
Proof.
ir. uf unary. rww Function.create_V_rewrite. 
Qed. 

Definition binary (x:E) (f:E2) :=
L x (fun a => (L x (fun b => f b a))).

Lemma V_V_binary : forall x f a b,
inc a x -> inc b x -> V a (V b (binary x f)) = f a b.
Proof.
ir. uf binary. 
rww Function.create_V_rewrite. 
rww Function.create_V_rewrite.
Qed. 

Hint Rewrite V_unary : aw.
Hint Rewrite V_V_binary : aw. 

End Notation. 
Export Notation. 

Module Arrow.
Import Function. 



Definition Source  := R (s_(r_(c_(DOT )))).
Definition Target  := R (t_(r_(g_(DOT )))).
Definition Arrow := R (a_(r_(r_ DOT ))).


Definition source (x : E) := V Source x. 
Definition target (x : E) := V Target x. 
Definition arrow (x : E) := V Arrow x.

Definition create (x y a: E) :=
denote Source x (
denote Target y (
denote Arrow a (
stop))). 


Lemma source_create : forall x y a, 
source (create x y a) = x. 
Proof.
ir.
uf source; uf create.  
drw.  
Qed. 

Lemma target_create : forall x y a, 
target (create x y a) = y. 
Proof.
ir. uf target; uf create; drw. 
Qed. 

Lemma arrow_create : forall x y a, 
arrow (create x y a) = a. 
Proof.
ir; uf arrow; uf create; drw.
Qed. 

Hint Rewrite source_create target_create arrow_create : aw. 

Definition like a := a = create (source a) (target a) (arrow a).

Lemma create_like : forall s t a :E,
like (create s t a) = True.
Proof.
ir. 
app iff_eq; ir. 
uf like. rw source_create. 
rw target_create. 
rw arrow_create. tv. 
Qed. 

Hint Rewrite create_like : aw.

Definition flip a :=
Y (like a) (create (target a) (source a) (arrow a)) a.

Lemma source_flip : forall a,
like a -> source (flip a) = target a.
Proof.
ir. uf flip.  rw Y_if_rw. rw source_create. tv. am. 
Qed.

Lemma target_flip : forall a,
like a -> target (flip a) = source a.
Proof.
ir. uf flip.  rw Y_if_rw. rw target_create. tv. am. 
Qed.

Lemma flip_not_like : forall a, ~(like a) -> flip a = a.
Proof.
ir. uf flip. rw Y_if_not_rw. tv. am. 
Qed. 

Lemma arrow_flip : forall a, arrow (flip a) = arrow a.
Proof.
ir. apply by_cases with (like a); ir. 
uf flip. 
rw Y_if_rw. rw arrow_create. tv. am. 
rw flip_not_like. tv. am. 
Qed.

Lemma flip_like : forall a, like a -> 
flip a = create (target a) (source a) (arrow a).
Proof.
ir. 
uf flip. rw Y_if_rw. tv. am. 
Qed. 

Lemma like_flip : forall a, like a = like (flip a).
Proof.
ir. ap iff_eq; ir. uf flip. 
rw Y_if_rw. aw.  am. 
apply by_cases with (like a); ir. am. 
rwi flip_not_like H. am. am. 
Qed. 

Lemma flip_flip : forall a, flip (flip a) = a.
Proof.
ir. apply by_cases with (like a); ir. 
rw flip_like. 
rw target_flip. rw source_flip. rw arrow_flip. 
uh H. sy; am. am. am. wr like_flip. am. 
rw flip_not_like. rw flip_not_like. tv. am. 
uhg; ir. ap H. rw like_flip. am. 
Qed. 

Definition ev u x := V x (arrow u). 


Lemma flip_eq : forall a b, flip a = flip b ->
a = b.
Proof.
ir. transitivity (flip (flip a)). rww flip_flip.
rw H. rww flip_flip. 
Qed. 

End Arrow.





Module Umorphism.
Import Function.
Import Notation.
Import Arrow. 
 



Section Construction.
Variables (x y : E) (f : E1).

Definition create := Arrow.create x y (L (U x) f).


Lemma source_create : source create = x. 
Proof.
uf create. rw Arrow.source_create. tv. 
Qed. 

Lemma target_create : target create = y. 
Proof.
uf create. rw Arrow.target_create. tv. 
Qed. 

Lemma ev_create : forall a : E, inc a (U x) -> 
ev create a = f a.
Proof. 
ir. uf ev. uf create. 
rw Arrow.arrow_create. 
rw create_V_rewrite. tv. am. 
Qed. 

Lemma arrow_create : arrow create = 
L (U (source create)) (ev create).
Proof.
uf create. 
rw Arrow.arrow_create. rw Arrow.source_create. 
uf ev. ap Function.create_extensionality. 
tv. ir. rw Arrow.arrow_create. 
rw Function.create_V_rewrite. 
tv. am. 
Qed. 


End Construction.




Lemma create_extens :
 forall (x x' y y' : E) (f g : E1),
 x = x' ->
 y = y' ->
 (forall a : E, inc a (U x) -> f a = g a) -> create x y f = create x' y' g.
ir.
wr H; wr H0. uf create. 
ap uneq. ap create_extensionality. tv. 
ir. au. 
Qed.



Definition realizes (x y : E) (f : E1) (a : E) :=
  source a = x
  & target a = y
  & (forall z : E, inc z (U x) -> ev a z = f z).

Definition property (x y : E) (f : E1) := Transformation.axioms (U x) (U y) f.

Definition like (a : E) := create (source a) (target a) (ev a) = a.


Lemma create_like : forall (x y : E) (f : E1), like (create x y f).
ir.
uf like. ap create_extens. ap source_create. 
ap target_create. ir. ap ev_create. rwi source_create H. am. 
Qed. 

Lemma like_arrow_like : forall u, like u -> Arrow.like u.
Proof.
ir. uh H. uhg. 
ufi create H. 
set (f:=Function.create (U (source u)) (ev u)) in H. 
assert (arrow u = f). wr H. rw Arrow.arrow_create. tv. rw H0.
sy; am. 
Qed. 


Lemma create_realizes :
 forall (x y : E) (f : E1), realizes x y f (create x y f).
ir.
pose source_create.
pose target_create.
pose ev_create.
unfold realizes in |- *; xe.
ir. au. 
Qed.


Lemma realizes_like_eq :
 forall (x y : E) (f : E1) (a : E),
 like a -> realizes x y f a -> create x y f = a.
ir. ufi like H. wr H. ap create_extens; ufi realizes H0; xd. ir; sy; ap H2; am. 
Qed. 


Definition axioms (a : E) := property (source a) (target a) (ev a).
Definition strong_axioms (a : E) := (axioms a & like a).

Lemma axioms_from_strong : forall a : E, strong_axioms a -> axioms a.
ir. unfold strong_axioms in H; xe.
Qed.

Lemma create_strong_axioms :
 forall (x y : E) (f : E1), property x y f -> strong_axioms (create x y f).
ir.
unfold strong_axioms in |- *.
ee.
unfold axioms in |- *.
rw source_create.
rw target_create.
uf property.
uf Transformation.axioms.
ir.
rw ev_create. 
ufi property H.
ufi Transformation.axioms H.
ap H.
am.

am.

ap create_like.
Qed.

Lemma create_axioms :
 forall (x y : E) (f : E1), property x y f -> axioms (create x y f).
ir. ap axioms_from_strong. ap create_strong_axioms; au.
Qed.

Definition identity (x : E) := create x x (fun y : E => y).

Definition compose (a b : E) :=
  create (source b) (target a) (fun y : E => ev a (ev b y)).

Lemma identity_strong_axioms : forall x : E, strong_axioms (identity x).
ir.
uf identity.
ap create_strong_axioms.
uf property.
ap Transformation.identity_axioms.
Qed.

Lemma identity_axioms : forall x : E, axioms (identity x).
ir. cp (identity_strong_axioms x). 
ufi strong_axioms H; xe.
Qed.


Lemma left_identity :
 forall a : E, strong_axioms a -> compose (identity (target a)) a = a.
ir.
unfold compose in |- *.
ap realizes_like_eq.
unfold strong_axioms in H; xe.

unfold realizes in |- *.
xe.
unfold identity in |- *; rewrite target_create.
tv.

ir.
unfold identity in |- *.
rewrite ev_create.
tv.

unfold strong_axioms in H.
xd.
Qed.


Lemma right_identity :
 forall a : E, strong_axioms a -> compose a (identity (source a)) = a.
ir.
unfold compose in |- *.
ap realizes_like_eq.
unfold strong_axioms in H; xe.

unfold realizes in |- *.
xe.
unfold identity in |- *; rewrite source_create.
tv.

ir.
unfold identity in |- *; rewrite ev_create.
tv.

unfold identity in H0; rewrite source_create in H0.
am.
Qed.

Lemma source_identity : forall x : E, source (identity x) = x.
ir. unfold identity in |- *; rewrite source_create. tv.
Qed.

Lemma target_identity : forall x : E, target (identity x) = x.
ir. unfold identity in |- *; rewrite target_create. tv.
Qed.

Lemma ev_identity : forall x y : E, inc y (U x) -> ev (identity x) y = y.
ir. unfold identity in |- *; rewrite ev_create; au.
Qed.

Lemma source_compose : forall a b : E, source (compose a b) = source b.
ir. unfold compose in |- *; rewrite source_create; tv.
Qed.

Lemma target_compose : forall a b : E, target (compose a b) = target a.
ir. unfold compose in |- *; rewrite target_create; tv.
Qed.

Lemma ev_compose :
 forall a b y : E,
 inc y (U (source b)) -> ev (compose a b) y = ev a (ev b y).
ir. unfold compose in |- *; rewrite ev_create; au.
Qed.

Hint Rewrite source_compose target_compose
source_identity target_identity ev_identity ev_compose : aw.

Definition composable (a b : E) :=
(axioms a & axioms b & source a = target b).



Lemma compose_strong_axioms :
 forall a b : E, composable a b -> strong_axioms (compose a b).
ir.
unfold strong_axioms in |- *.
xe.
unfold axioms in |- *.
rewrite source_compose.
rewrite target_compose.
unfold property in |- *.
unfold Transformation.axioms in |- *.
ir.
rewrite ev_compose.
unfold composable in H.
xe.
unfold axioms in H.
unfold property in H.
unfold Transformation.axioms in H.
ap H.
unfold axioms in H1.
unfold property in H1.
unfold Transformation.axioms in H1.
rewrite H2.
ap H1.
am.

am.

unfold compose in |- *.
ap create_like.
Qed.

Lemma compose_axioms : forall a b : E, composable a b -> axioms (compose a b).
ir. set (K := compose_strong_axioms H). unfold strong_axioms in (type of K); xe.
Qed. 

Lemma extens :
 forall a b : E,
 strong_axioms a ->
 strong_axioms b ->
 source a = source b ->
 target a = target b ->
 (forall x : E,
  inc x (U (source a)) -> inc x (U (source b)) -> ev a x = ev b x) ->
 a = b.
ir.
unfold strong_axioms in H, H0.
xe.
unfold like in H5, H4.
rewrite <- H5.
ap realizes_like_eq; au.
unfold realizes in |- *.
xe.
ir.
sy; ap H3.
am.

rewrite <- H1.
am.
Qed.

Lemma associativity :
 forall a b c : E,
 composable a b ->
 composable b c -> compose (compose a b) c = compose a (compose b c).
ir.
ap extens.
ap compose_strong_axioms.
unfold composable in |- *.
xe.
ap compose_axioms; au.

unfold composable in H0; xe.

rewrite source_compose.
unfold composable in H0; xe.

ap compose_strong_axioms.
unfold composable in |- *; xe.
unfold composable in H; xe.

ap compose_axioms.
am.

rewrite target_compose.
unfold composable in H; xe.

repeat rewrite source_compose.
tv.

repeat rewrite target_compose; tv.

ir.
repeat rewrite ev_compose.
tv.

repeat rewrite source_compose in H1.
am.

rewrite source_compose in H2.
am.

repeat rewrite source_compose in H1.
unfold composable in H0.
xe.
rewrite H4.
ap H3.
am.

repeat rewrite source_compose in H1.
am.
Qed.


Definition inclusion (a b : E) := create a b (fun y : E => y).


Lemma inclusion_strong_axioms :
 forall a b : E, sub (U a) (U b) -> strong_axioms (inclusion a b).
ir.
unfold inclusion in |- *.
ap create_strong_axioms.
unfold property in |- *.
unfold Transformation.axioms in |- *.
ir.
ap H; au.
Qed.

Lemma inclusion_axioms :
 forall a b : E, sub (U a) (U b) -> axioms (inclusion a b).
ir. ap axioms_from_strong. ap inclusion_strong_axioms; au.
Qed.


Definition injective (u : E) :=
  axioms u
  & Transformation.injective (U (source u)) (U (target u)) (ev u).

Lemma injective_rewrite :
 forall u : E,
 axioms u ->
 injective u =
 (forall x y : E,
  inc x (U (source u)) ->
  inc y (U (source u)) -> ev u x = ev u y -> x = y).
ir.
ap iff_eq; ir.
unfold injective in H0.
xe.
unfold Transformation.injective in H4.
xe. au.

unfold injective in |- *; xe.
unfold Transformation.injective in |- *; xe.
Qed.

Lemma injective_compose_with :
 forall u v w : E,
 strong_axioms u ->
 strong_axioms v ->
 injective w ->
 composable w u -> composable w v -> compose w u = compose w v -> u = v.
ir.
ap extens; au.
transitivity (source (compose w u)).
rewrite source_compose; au.

rewrite H4.
rewrite source_compose; au.

unfold composable in H2, H3.
xe.
transitivity (source w); au.

ir.
unfold injective in H1.
xe.
unfold Transformation.injective in H7.
xe.
ap H8.
unfold strong_axioms in H.
xe.
unfold axioms in H.
unfold property in H.
unfold composable in H2.
xe.
rewrite H11.
ap H.
am.

unfold composable in H3; xe.
rewrite H10.
unfold strong_axioms in v; xe. au.

transitivity (ev (compose w u) x).
rewrite ev_compose; au.

rewrite H4.
rewrite ev_compose; au.
Qed. 

Definition surjective (u : E) :=
  axioms u
  & Transformation.surjective (U (source u)) (U (target u)) (ev u).

Lemma surjective_rewrite :
 forall u : E,
 axioms u ->
 surjective u =
 (forall x : E,
  inc x (U (target u)) ->
  ex (fun y : E => (inc y (U (source u)) & ev u y = x))).
ir.
ap iff_eq; ir.
unfold surjective in H0; xe.
unfold Transformation.surjective in H2; xe. au.

unfold surjective in |- *; xe.
unfold Transformation.surjective in |- *; xe.
Qed. 

Definition inverse (u : E) :=
  create (target u) (source u)
    (Transformation.inverse (U (source u)) (ev u)).

Lemma surjective_inverse_axioms :
 forall u : E, surjective u -> strong_axioms (inverse u).
ir.
unfold strong_axioms in |- *; xe.
unfold inverse in |- *.
ap create_axioms.
unfold property in |- *.
ap Transformation.surjective_inverse_axioms.
unfold surjective in H; xe.

unfold inverse in |- *.
ap create_like.
Qed. 

Lemma surjective_composable_left :
 forall u : E, surjective u -> composable (inverse u) u.
ir.
unfold composable in |- *.
xe.
ap axioms_from_strong.
ap surjective_inverse_axioms; au.

unfold surjective in H; xe.

unfold inverse in |- *.
rewrite source_create; tv.
Qed.

Lemma surjective_composable_right :
 forall u : E, surjective u -> composable u (inverse u).
ir.
unfold composable in |- *; xe.
unfold surjective in H; xe.

ap axioms_from_strong.
ap surjective_inverse_axioms; au.

unfold inverse in |- *; rewrite target_create; tv.
Qed. 

Lemma surjective_inverse_right :
 forall u : E, surjective u -> compose u (inverse u) = identity (target u).
ir.
assert (axioms u).
unfold surjective in H; xe.

ap extens.
ap compose_strong_axioms.
ap surjective_composable_right.
am.

ap identity_strong_axioms.

rewrite source_compose.
rewrite source_identity.
unfold inverse in |- *; rewrite source_create.
tv.

rewrite target_compose.
rewrite target_identity; tv.

ir.
rewrite ev_compose.
rewrite ev_identity.
unfold inverse in |- *.
rewrite ev_create.
unfold surjective in H.
xe.
rewrite source_identity in H2.
pose (Transformation.surjective_inverse_right H3 H2).
ap e.

rewrite source_identity in H2; am.

rewrite source_identity in H2; am.

rewrite source_compose in H1.  
am. Qed.

Definition bijective (u : E) := (injective u & surjective u).

Lemma bijective_transformation_bijective :
 forall u : E,
 bijective u ->
 Transformation.bijective (U (source u)) (U (target u)) (ev u).
ir.
unfold bijective in H; xe.
unfold injective in H.
unfold surjective in H0.
xe.
unfold axioms in H.
unfold property in H.
unfold Transformation.bijective in |- *; xe.
Qed. 

Lemma transformation_bijective_bijective :
 forall u : E,
 axioms u ->
 Transformation.bijective (U (source u)) (U (target u)) (ev u) ->
 bijective u.
ir.
unfold Transformation.bijective in H0.
unfold bijective in |- *.
xe.
unfold injective in |- *; xe.

unfold surjective in |- *; xe.
Qed. 

Definition are_inverse (u v : E) :=
  composable u v
  & composable v u
  & compose u v = identity (source v)
  & compose v u = identity (source u).

Lemma inverse_symm : forall u v : E, are_inverse u v -> are_inverse v u.
ir.
unfold are_inverse in |- *.
unfold are_inverse in H.
xe.
Qed. 

Lemma inverse_unique :
 forall u v w : E,
 strong_axioms v ->
 strong_axioms w -> are_inverse u v -> are_inverse u w -> v = w.
ir.
transitivity (compose v (identity (source v))).
sy.
ap right_identity.
am.

unfold are_inverse in H1, H2; ee.
assert (source v = target u).
unfold composable in H6; xe.

assert (source v = source w).
rewrite H9.
unfold composable in H3; xe.

rewrite H10.
rewrite <- H4.
rewrite <- associativity.
rewrite H8.
assert (source u = target w).
unfold composable in H2; xe.

rewrite H11.
ap left_identity.
am.

am.

am.
Qed. 

Definition has_inverse (u : E) := ex (fun v : E => are_inverse u v).

Lemma are_inverse_transfo_inverse :
 forall u v : E,
 are_inverse u v ->
 Transformation.are_inverse (U (source u)) (U (target u)) (
   ev u) (ev v).
ir.
unfold Transformation.are_inverse in |- *.
unfold are_inverse in H.
xe.
unfold composable in H; xe.

unfold composable in H, H0; xe.
rewrite <- H4.
rewrite H6.
am.

ir.
transitivity (ev (compose v u) x).
sy; ap ev_compose.
am.

rewrite H2.
ap ev_identity.
am.

ir.
assert (inc y (U (source v))).
unfold composable in H0; xe.
rewrite H5; am.

transitivity (ev (compose u v) y).
rewrite ev_compose.
tv.

am.

rewrite H1.
rewrite ev_identity.
tv.

am.
Qed. 

Lemma inverse_bijective : forall u v : E, are_inverse u v -> bijective u.
ir.
ap transformation_bijective_bijective.
unfold are_inverse in H; xe.
unfold composable in H; xe.

apply Transformation.inverse_bijective with (ev v).
ap are_inverse_transfo_inverse.
am.
Qed.

Lemma bijective_inverse :
 forall u : E, bijective u -> are_inverse u (inverse u).
ir.
unfold bijective in H; xe.
pose (surjective_composable_left H0).
pose (surjective_composable_right H0).
pose (surjective_inverse_right H0).
unfold are_inverse in |- *; ee. am. am. 
unfold composable in (type of c); ee. 
rewrite H3.
ap e.

apply injective_compose_with with u.
ap compose_strong_axioms; au.

ap identity_strong_axioms.

am.

unfold composable in |- *.
ee.
unfold injective in H; xe.

ap compose_axioms; au.

rewrite target_compose.
unfold composable in (type of c0); xe.

unfold composable in |- *; ee.
unfold injective in H; xe.

ap identity_axioms.

rewrite target_identity; tv.

rewrite <- associativity.
rewrite e.
ap extens.
ap compose_strong_axioms.
unfold composable in |- *; ee.
ap identity_axioms.

unfold injective in H; xe.

rewrite source_identity.
tv.

ap compose_strong_axioms.
unfold composable in |- *; ee.
unfold injective in H; xe.

ap identity_axioms.

rewrite target_identity; tv.

rewrite source_compose.
rewrite source_compose.
rewrite source_identity; tv.

repeat rewrite target_compose.
rewrite target_identity.
tv.

ir.
repeat rewrite ev_compose.
repeat rewrite ev_identity.
tv.

rewrite source_compose in H2.
rewrite source_identity in H2; am.

unfold injective in H; ee.
unfold axioms in H.
unfold property in H; xe.
ap H.
rewrite source_compose in H2.
rewrite source_identity in H2.
am.

rewrite source_compose in H2; am.

rewrite source_compose in H2.
rewrite source_identity in H2.
am.

am.

am.
Qed.


Lemma bijective_has_inverse : forall u : E, bijective u -> has_inverse u.
ir. unfold has_inverse in |- *. apply ex_intro with (inverse u).
ap bijective_inverse; au.
Qed. 


Lemma bijective_eq_has_inverse : forall u : E, bijective u = has_inverse u.
ir.
ap iff_eq; ir.
unfold has_inverse in |- *.
apply ex_intro with (inverse u).
ap bijective_inverse; au.

unfold has_inverse in H.
nin H.
apply inverse_bijective with x; au.
Qed.

Lemma bijective_eq_inverse :
 forall u : E, bijective u = are_inverse u (inverse u).
ir.
ap iff_eq; ir.
ap bijective_inverse.
am.

apply inverse_bijective with (inverse u); am.
Qed. 

Lemma has_inverse_eq_inverse :
 forall u : E, has_inverse u = are_inverse u (inverse u).
ir.
rewrite <- bijective_eq_inverse.
rewrite bijective_eq_has_inverse.
tv.
Qed. 




Definition Uempty := stop.


Definition Uempty_initial (a : E) := inclusion Uempty a.

Lemma underlying_Uempty : U Uempty = emptyset.
uf Uempty. uf U. drw. 
Qed. 

Lemma Uempty_initial_strong_axioms :
 forall a : E, strong_axioms (Uempty_initial a).
ir. uf Uempty_initial. ap inclusion_strong_axioms. rw underlying_Uempty. uf sub; ir.
nin H. elim x0. Qed. 

Lemma use_axioms :
 forall u x y a : E,
 axioms u ->
 source u = x -> target u = y -> inc a (U x) -> inc (ev u a) (U y).
ir. cx. wr H1. ap H. rw H0. am.
Qed. 

Ltac clst :=
  match goal with
  | id1:?X1 |- _ => first
  [ rewrite source_create in id1; clst
  | rewrite target_create in id1; clst
  | rewrite source_identity in id1; clst
  | rewrite target_identity in id1; clst
  | rewrite source_compose in id1; clst
  | rewrite target_compose in id1; clst ]
  |  |- _ => first
  [ rewrite source_create; clst
  | rewrite target_create; clst
  | rewrite source_identity; clst
  | rewrite target_identity; clst
  | rewrite source_compose; clst
  | rewrite target_compose; clst ]
  | _ => idtac
  end.




End Umorphism.








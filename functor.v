Set Implicit Arguments.
Unset Strict Implicit.

Require Import Arith.
Require Export category.

Ltac fw := autorewrite with fw; try tv; try am. 

Module Functor.
Export Umorphism. 
Export Category.

(**** creation and extraction ****)

Definition fmor f u := ev f u.

Definition fob f x := 
source (fmor f (id (source f) x)).

Definition create := Umorphism.create. 

Lemma source_create : forall a b fm,
source (create a b fm) = a.
Proof.
ir. uf create. uf Umorphism.create. 
rw Arrow.source_create. tv. 
Qed.

Lemma target_create : forall a b fm,
target (create a b fm) = b.
Proof.
ir. uf create. uf Umorphism.create. 
rww Arrow.target_create. 
Qed. 

Lemma fmor_create : forall a b fm u, 
mor a u -> fmor (create a b fm) u = (fm u).
Proof.
ir.  uf create. rw Umorphism.ev_create. tv. 
change (is_mor a u). lu. 
Qed.

Hint Rewrite source_create target_create fmor_create : fw.

Lemma fob_create : forall a b fm x, 
ob a x -> 
fob (create a b fm) x = source (fm (id a x)) .
Proof.
ir. uf fob. rw fmor_create. 
rw source_create. tv. rw source_create. cw. 
Qed.


Definition axioms f :=
let a := source f in
let b := target f in
(Umorphism.like f) &
(Category.axioms a) &
(Category.axioms b) &
(forall x, ob a x -> ob b (fob f x)) &
(forall x, ob a x -> id b (fob f x) = fmor f (id a x)) &
(forall u, mor a u -> mor b (fmor f u)) &
(forall u, mor a u -> source (fmor f u) = fob f (source u)) &
(forall u, mor a u -> target (fmor f u) = fob f (target u)) &
(forall u v, mor a u -> mor a v -> source u = target v -> 
   comp b (fmor f u) (fmor f v) = fmor f (comp a u v)).


Definition property a b fo fm :=
(Category.axioms a) &
(Category.axioms b) &
(forall x, ob a x -> ob b (fo x)) &
(forall x, ob a x -> id b (fo x) = fm (id a x)) &
(forall u, mor a u -> mor b (fm u)) &
(forall u, mor a u -> source (fm u) = fo (source u)) &
(forall u, mor a u -> target (fm u) = fo (target u)) &
(forall u v, mor a u -> mor a v -> source u = target v-> 
   comp b (fm u) (fm v) = fm (comp a u v)).

Lemma fob_property_create : forall a b fo fm x,
property a b fo fm -> ob a x -> 
fob (create a b fm) x = fo x.
Proof.
ir. rww fob_create. uh H; ee. 
rw H5. cw. cw. 
Qed. 

Lemma create_axioms : forall a b (fm:E1),
(exists fo, property a b fo fm) ->
axioms (create a b fm).
Proof.
ir. 
uhg.
do 50 (try (rw source_create)). 
do 50 (try (rw target_create)). 
do 50 (try (rw fmor_create)). 
nin H. 

ee; ir;  try (rw fmor_create); try (rw (fob_property_create (a:= a) (b:=b)
(fo := x) (fm := fm))). 
uf create.
ap Umorphism.create_like. 
lu. lu. uh H; ee. app H2.
am. am. 
uh H; ee. 
app H3. am. am. cw.  
uh H; ee. app H4. am. 
uh H; ee. app H5. am. cw. am. 
uh H; ee. app H6. am. cw. am. 
rww fmor_create. rww fmor_create. 
uh H; ee. rww H9. cw. am. 
Qed.

Lemma axioms_property : forall f, axioms f ->
property (source f) (target f) (fob f) (fmor f).
Proof.
ir. 
uh H; ee. 
uhg; xd. 
Qed. 

Lemma functor_arrow_like : forall f,
axioms f -> Arrow.like f.
Proof.
ir. uh H; ee. 
ap Umorphism.like_arrow_like. am. 
Qed. 

Lemma create_recovers : forall f,
axioms f -> create (source f) (target f) (fmor f) = f.
Proof.
ir. uh H; ee. uh H. am. 
Qed. 

Lemma axioms_extensionality : forall f g,
axioms f -> axioms g -> source f = source g ->
target f = target g -> 
(forall u, mor (source f) u-> fmor f u = fmor g u) ->
f = g.
Proof.
ir. 
wr (create_recovers H). 
wr (create_recovers H0). 
wr H1. wr H2. 
uf create. uf Umorphism.create. 
ap uneq. 
ap Function.create_extensionality. 
tv. ir. ap H3. change (is_mor (source f) x) in H4. 
app is_mor_mor. uh H; ee. am. 
Qed. 

Lemma category_axioms_source : forall f,
axioms f -> Category.axioms (source f) = True.
Proof.
ir. app iff_eq; ir. lu.  
Qed.

Lemma category_axioms_target : forall f,
axioms f -> Category.axioms (target f)= True.
Proof.
ir. app iff_eq; ir. lu.
Qed.

Hint Rewrite category_axioms_source category_axioms_target : fw.


Lemma ob_fob : forall f x,
axioms f -> ob (source f) x -> ob (target f) (fob f x).
Proof.
ir. uh H; ee. au. 
Qed.

Lemma ob_fobv : forall a f x,
axioms f -> ob (source f) x -> a = target f ->
ob a (fob f x) = True.
Proof.
ir. app iff_eq; ir. rw H1. ap ob_fob; am. 
Qed. 

Lemma mor_fmor : forall f u,
axioms f -> mor (source f) u -> mor (target f) (fmor f u).
Proof.
ir. uh H; ee. au. 
Qed. 

Lemma mor_fmorv : forall a f u,
axioms f -> mor (source f) u ->
a = target f -> mor a (fmor f u) = True.
Proof.
ir. app iff_eq; ir. rw H1. ap mor_fmor; am. 
Qed. 

Hint Rewrite ob_fobv mor_fmorv : fw.

Lemma source_fmor : forall f u,
axioms f -> mor (source f) u ->
source (fmor f u) = fob f (source u).
Proof.
ir. uh H; ee. au. 
Qed.

Lemma target_fmor : forall f u,
axioms f -> mor (source f) u ->
target  (fmor f u) = fob f (target u).
Proof.
ir. uh H; ee. au. 
Qed.

Hint Rewrite source_fmor target_fmor : fw. 

Lemma id_fob : forall f x,
axioms f -> ob (source f) x -> 
id (target f) (fob f x) = fmor f (id (source f) x).
Proof.
ir. uh H; ee. au. 
Qed. 

Lemma fmor_id : forall f a x,
axioms f -> source f = a -> ob a x -> 
fmor f (id a x) = id (target f) (fob f x).
Proof.
ir. wr H0.
wrr id_fob. 
rww H0. 
Qed.

Hint Rewrite fmor_id : fw. 


Lemma comp_fmor : forall f u v,
axioms f -> mor (source f) u ->
mor (source f) v -> source u = target v ->
comp (target f) (fmor f u) (fmor f v) = 
fmor f (comp (source f) u v).
Proof.
ir. uh H; ee. au. 
Qed. 

Lemma comp_fmorv : forall a f f1 u v,
axioms f -> f = f1 -> 
mor (source f) u -> mor (source f) v -> 
source u = target v ->
a = target f ->
comp a (fmor f u) (fmor f1 v) =
fmor f (comp (source f) u v).
Proof.
ir. rw H4. wr H0. ap comp_fmor; am. 
Qed.

Lemma fmor_compv : forall a f u v,
axioms f -> a = source f ->
mor a u -> mor a v -> source u = target v -> 
fmor f (comp a u v) = comp (target f) (fmor f u) (fmor f v).
Proof.
ir. rw H0. sy. rw comp_fmor. tv. am. wr H0; am. wrr H0.
am. 
Qed. 


Definition fcompose := Umorphism.compose. 


Lemma source_fcompose : forall f g,
source (fcompose f g) = source g.
Proof.
ir. uf fcompose. uf compose. 
fw. 
Qed.

Lemma target_fcompose : forall f g,
target (fcompose f g) = target f.
Proof.
ir. uf fcompose. uf compose. fw.  
Qed.

Hint Rewrite source_fcompose target_fcompose: fw.

Lemma fmor_fcompose : forall f g u,
axioms f -> axioms g ->
source f = target g -> mor (source g) u -> 
fmor (fcompose f g) u = fmor f (fmor g u).
Proof.
ir. uf fcompose. uf compose. rw fmor_create. tv.
am. Qed. 

Lemma fob_fcompose : forall f g x,
axioms f -> axioms g ->
source f = target g -> ob (source g) x -> 
fob (fcompose f g) x = fob f (fob g x).
Proof.
ir. uf fcompose. uf compose. rw fob_create. tv.
fw. cw. fw.   fw. am. Qed.



Hint Rewrite fob_fcompose fmor_fcompose : fw. 

Lemma fcompose_axioms : forall f g,
axioms f -> axioms g ->
source f = target g -> axioms (fcompose f g).
Proof.
ir. uf fcompose. 
change (axioms (create (source g) (target f) 
(fun y => fmor f (fmor g y)))). 
ap create_axioms. sh (fun x => fob f (fob g x)).


uhg; dj. uh H0; ee; am.
uh H; ee; am.  ap ob_fob. am. 
rw H1. ap ob_fob. am. am. 
rw id_fob. ap uneq.  rw H1. 
ap id_fob. am. am. am. rw H1; ap ob_fob; am. 
ap mor_fmor. am. rw H1. ap mor_fmor. am. am. 
rw source_fmor. ap uneq. 
rw source_fmor.
tv. am. am. am. rw H1; ap mor_fmor; am. 
rw target_fmor. ap uneq. rw target_fmor. 
tv. am. am. am. 
rw H1; ap mor_fmor; am. 
rw comp_fmor. ap uneq. rw H1. 
ap comp_fmor. am. am. am. am. am. rw H1. 
fw. rw H1. fw. fw. rww H11. 
Qed.

Lemma fcompose_axioms_rw : 
forall f g,
axioms f -> axioms g ->
source f = target g -> axioms (fcompose f g) = True.
Proof.
ir. app iff_eq; ir. app fcompose_axioms. 
Qed. 

Hint Rewrite fcompose_axioms_rw : fw. 

Lemma functor_umorphism_axioms : forall f,
axioms f -> Umorphism.axioms f.
Proof.
ir. uhg; ee. uhg; ee. 
uhg; ee. ir. change (is_mor (target f) (fmor f x)).
change (is_mor (source f) x) in H0.
assert (mor (target f) (fmor f x)). 
ap mor_fmor. am. ap is_mor_mor. lu. 
am. lu. 
Qed. 

Lemma fcompose_assoc : forall f g h,
axioms f -> axioms g -> axioms h ->
source f = target g ->
source g = target h ->
fcompose (fcompose f g) h = fcompose f (fcompose g h).
Proof.
ir. 
uf fcompose. ap Umorphism.associativity. 
uhg; ee; try am. 
ap functor_umorphism_axioms. am. 
app functor_umorphism_axioms. 
uhg; ee; try am. 
app functor_umorphism_axioms.
app functor_umorphism_axioms. 
Qed. 


Definition fidentity a := Umorphism.identity a.

 





Lemma source_fidentity : forall a,
source (fidentity a) = a.
Proof.
ir.
uf fidentity. rww Umorphism.source_identity. 
Qed.

Lemma target_fidentity : forall a,
target (fidentity a) = a.
Proof.
ir. uf fidentity. rww Umorphism.target_identity.
Qed.

Lemma fmor_fidentity : forall a u,
mor a u -> fmor (fidentity a) u = u.
Proof.
ir. uf fidentity; uf fmor. 
rww Umorphism.ev_identity. 
change (is_mor a u). lu. 
Qed.

Lemma fob_fidentity : forall a x,
ob a x -> fob (fidentity a) x = x.
Proof.
ir. uf fidentity. uf fob. 
uf fmor. rww Umorphism.source_identity.
rww Umorphism.ev_identity. rw source_id. tv.
am. change (is_mor a (id a x)). 
assert (mor a (id a x)). cw. lu. 
Qed.

Hint Rewrite source_fidentity target_fidentity
fmor_fidentity fob_fidentity : fw.

Lemma fidentity_axioms : forall a,
Category.axioms a -> axioms (fidentity a) = True.
Proof.
ir. app iff_eq; ir.
uhg; ee. uf fidentity. 
uf Umorphism.identity. 
app Umorphism.create_like.
fw. fw. ir. fw. rwi source_fidentity H1; am. 
rwi source_fidentity H1; am. 
ir; fw; try (rwi source_fidentity H1; cw). 
ir; fw; try (rwi source_fidentity H1; cw). 
ir; fw; try (rwi source_fidentity H1; cw). 
ir; fw; try (rwi source_fidentity H1; cw). 
ir; fw; 
try (rwi source_fidentity H1; cw);
try (rwi source_fidentity H2; cw).
Qed. 

Hint Rewrite fidentity_axioms : fw. 

Lemma left_fidentity : forall a f,
axioms f -> a = target f ->
fcompose (fidentity a) f = f.
Proof.
ir. rw H0; clear H0. 
ap axioms_extensionality; ir. 
fw. fw. fw. am. fw. fw. 
rwi source_fcompose H0. 
fw. fw. fw. 
Qed. 

Lemma right_fidentity : forall a f,
axioms f -> a = source f ->
fcompose f (fidentity a) = f.
Proof.
ir. rw H0; clear H0. 
ap axioms_extensionality; ir.
fw. fw. fw. am. 
rww source_fcompose. rww source_fidentity. 
rww target_fcompose. 
rwi source_fcompose H0. rwi source_fidentity H0. 
fw. 
fw. fw. fw. 
Qed. 

Hint Rewrite left_fidentity right_fidentity : fw. 



Lemma are_inverse_fmor : forall a f u v,
Functor.axioms f -> are_inverse (source f) u v ->
target f = a -> 
are_inverse a (fmor f u) (fmor f v).
Proof.
ir. wr H1. 
cp H0. uh H2; ee. uh H2; uh H3; ee. 
uhg; ee. 
fw.  app is_mor_mor. fw. app is_mor_mor. 
fw. rww H4. app is_mor_mor. app is_mor_mor. 
fw. rww H5. 
app is_mor_mor. app is_mor_mor. 
fw. rww comp_fmor. rww H6. fw. cw. 
app is_mor_mor. app is_mor_mor. app is_mor_mor. 
app is_mor_mor. rww comp_fmor. rww H7.
fw.  app is_mor_mor. cw. app is_mor_mor. app is_mor_mor. 
app is_mor_mor.  
Qed. 

Lemma invertible_fmor : forall a f u,
Functor.axioms f -> invertible (source f) u ->
target f = a -> 
invertible a (fmor f u).
Proof.
ir. 
wr H1. 
uhg. uh H0. nin H0.
sh (fmor f x). app are_inverse_fmor. 
Qed.

Lemma fmor_inverse : forall a f u,
Functor.axioms f -> invertible (source f) u ->
source f = a ->
fmor f (inverse a u) = inverse (target f) (fmor f u).
Proof.
ir. ap inverse_uni. sh (target f). sh (fmor f u). ee. 
app are_inverse_fmor. rw H1. 
app invertible_inverse. wrr H1. 
app invertible_inverse. app invertible_fmor. 
Qed. 

Lemma inverse_fmor : forall a f u,
Functor.axioms f -> invertible (source f) u ->
target f = a -> 
inverse a (fmor f u) = fmor f (inverse (source f) u).
Proof.
ir. wr H1. rww fmor_inverse. 
Qed. 



Definition constant_functor a b x :=
Functor.create a b (fun u:E => id b x).



Lemma source_constant_functor : forall a b x,
source (constant_functor a b x) = a.
Proof. ir. uf constant_functor.
fw.   Qed.

Lemma target_constant_functor : forall a b x,
target (constant_functor a b x) = b.
Proof. ir. uf constant_functor. fw.  Qed.

Lemma fmor_constant_functor : forall a b x u,
mor a u -> fmor (constant_functor a b x) u = id b x.
Proof. ir. uf constant_functor. 
fw.  Qed. 

Lemma fob_constant_functor : forall a b x y,
ob a y -> ob b x -> 
fob (constant_functor a b x) y = x.
Proof.
ir. uf constant_functor. rww fob_create.  
fw. cw. Qed. 

Hint Rewrite source_constant_functor target_constant_functor
fmor_constant_functor fob_constant_functor: fw.




Lemma constant_functor_axioms : forall a b x,
Category.axioms a -> Category.axioms b -> ob b x ->
Functor.axioms (constant_functor a b x).
Proof.
ir. uf constant_functor. 
ap Functor.create_axioms. 
sh (fun y:E => x). 
uhg; ee. am. am. ir. am. ir. tv. 
ir. cw. ir. cw. ir. cw. ir. cw. 
app mor_id. rww source_id. Qed. 

Definition is_constant f :=
Functor.axioms f &
(exists x, (ob (target f) x) &
f = constant_functor (source f) (target f) x).

(**** note that the trivial functor from the
empty category to the empty category is not constant
by  this definition since there has to exist an object of 
target f *************************************)


Lemma constant_functor_is_constant : forall a b x,
Category.axioms a -> ob b x -> 
is_constant (constant_functor a b x).
Proof.
ir. uhg. 
ee. ap constant_functor_axioms. 
am. lu. am. sh x; ee. fw. 
rw source_constant_functor. 
rw target_constant_functor. tv. 
Qed. 

Lemma constant_functor_criterion : forall a b x f,
source f = a ->
target f = b ->
Functor.axioms f ->
ob b x -> 
(forall u, mor a u -> fmor f u = id b x) ->
f = constant_functor a b x.
Proof.
ir. ap axioms_extensionality. 
am. 
app constant_functor_axioms. wr H. 
uh H1; ee; am.  wr H0; uh H1; ee; am. 
rww source_constant_functor. rww target_constant_functor.
ir. rww fmor_constant_functor. ap H3. wrr H. 
wrr H. 
Qed.  

Lemma fcompose_right_constant_functor : forall a b x f,
Functor.axioms f -> source f = b -> Category.axioms a ->
ob b x -> 
fcompose f (constant_functor a b x) = 
constant_functor  a (target f) (fob f x).
Proof.
ir. ap constant_functor_criterion. 
rw source_fcompose. rw source_constant_functor. tv.
rw target_fcompose. tv. 
ir. 
ap fcompose_axioms. am. 
ap constant_functor_axioms. am. wr H0; uh H; ee; am. 
am. rww target_constant_functor. fw. rww H0. 
ir. rww fmor_fcompose. 
rww fmor_constant_functor. fw. 
ap constant_functor_axioms. am. wr H0; uh H; ee; am. 
am. rww target_constant_functor. rww source_constant_functor.
Qed.

Lemma fcompose_left_constant_functor : forall a b x f,
Functor.axioms f -> target f = a -> Category.axioms b ->
ob b x -> 
fcompose (constant_functor a b x) f = 
constant_functor  (source f) b x.
Proof.
ir. ap constant_functor_criterion.
rww source_fcompose. 
rww target_fcompose. 
rww target_constant_functor. 
app fcompose_axioms. ap constant_functor_axioms. 
wr H0; uh H; ee; am. 
am. am. sy; rww source_constant_functor. am. 
ir. rw fmor_fcompose. rww fmor_constant_functor. 
wr H0; app mor_fmor. 
ap constant_functor_axioms. wr H0; uh H; ee; am. am. am. 
am. sy; rww source_constant_functor. am. 
Qed.  


Lemma is_constant_fcompose : forall f g,
Functor.axioms f -> Functor.axioms g -> 
source f = target g -> is_constant g ->
is_constant (fcompose f g).
Proof.
ir.  
uhg. ee. 
app fcompose_axioms. 
uh H2. 
ee. nin H3; ee. 
sh (fob f x). ee. fw. rww H1. 
rw source_fcompose. rw target_fcompose. 
ap constant_functor_criterion. 
rww source_fcompose. rww target_fcompose. 
app fcompose_axioms. app ob_fob. rww H1. 
ir. rww fmor_fcompose. rw H4. 
rww fmor_constant_functor. fw. 
Qed.



(*** oppf = opposite functor ****)

Definition oppf' f := Functor.create (opp (source f))
(opp (target f)) (fun u => flip (fmor f (flip u))).

Lemma source_oppf' : forall f, source (oppf' f) =
opp (source f). 
Proof.
ir. uf oppf'. rww source_create. 
Qed.

Lemma target_oppf' : forall f, target (oppf' f) =
opp (target f).
Proof.
ir. uf oppf'. rww target_create. 
Qed.

Lemma fmor_oppf' : forall f u, 
mor (source (oppf' f)) u ->
fmor (oppf' f) u = flip (fmor f (flip u)).
Proof.
ir. 
uf oppf'. 
rw fmor_create. tv. rwi source_oppf' H. am. 
Qed.

Lemma fob_oppf' : forall f x,
Functor.axioms f -> ob (source (oppf' f)) x ->
fob (oppf' f) x = fob f x.
Proof.
ir. 
rwi source_oppf' H0. rwi ob_opp H0. 
uf fob. rw fmor_oppf'. 
rw source_flip. rw source_oppf'. 
rw id_opp. rw flip_flip. 
rw target_fmor. rw source_fmor. 
rw target_id. rww source_id. am. am. 
app mor_id. am. app mor_id. 
rw ob_opp. am. 
apply mor_arrow_like with (target f).
ap mor_fmor. am. 
rw source_oppf'. rw id_opp. rw flip_flip. 
app mor_id.  rww ob_opp.  
rw source_oppf'. rw mor_opp. 
rw id_opp. rw flip_flip. app mor_id. 
rww ob_opp. 
Qed. 

Lemma oppf'_axioms : forall f, Functor.axioms f ->
Functor.axioms (oppf' f).
Proof.
ir. uhg; ee. uf oppf'. 
uf create. ap Umorphism.create_like. 
rw source_oppf'. ap opp_axioms. lu. 
rw target_oppf'. ap opp_axioms. lu. 
ir. rw target_oppf'. rw fob_oppf'. 
rw ob_opp. ap ob_fob. am. rwi source_oppf' H0.
rwi ob_opp H0. am. am. am. 
ir. cp H0. rwi source_oppf' H1. 
rwi ob_opp H1. 
rw target_oppf'. 
rw fmor_oppf'. rw source_oppf'. rw id_opp.
rw id_opp. rw flip_flip. 
rw fmor_id. rw fob_oppf'. tv. am. am. am. tv. 
am. rww ob_opp.  
rw ob_opp. rw fob_oppf'. 
app ob_fob. am. am. 
rw source_oppf'. rw id_opp. 
rw mor_opp. rw flip_flip. app mor_id.  
rww ob_opp. 
ir. rw target_oppf'. rw fmor_oppf'. 
rw mor_opp. rw flip_flip. ap mor_fmor. 
am. rwi source_oppf' H0. rwi mor_opp H0. 
am. uh H; ee; am. 
ir. rw fmor_oppf'. 
rw source_flip. 
rw target_fmor. rw target_flip. 
rw fob_oppf'. tv. am. 
rw source_oppf'. rw ob_opp. 
assert (source u = target (flip u)). 
rww target_flip. apply mor_arrow_like with (source (oppf' f)).
am. rw H1. 
rw ob_target. tv. 
rwi source_oppf' H0. rwi mor_opp H0. 
am. alike. am. 
rwi source_oppf' H0. rwi mor_opp H0. 
am. 
apply mor_arrow_like with (target f). 
ap mor_fmor. am. 
rwi source_oppf' H0. rwi mor_opp H0. am. uh H; ee; am.  

ir. rw fmor_oppf'. 
rw fob_oppf'. rw target_flip. 
rw source_fmor. rw source_flip. tv. 
apply mor_arrow_like with (source (oppf' f)). am. 
am. rwi source_oppf' H0. rwi mor_opp H0. am. 
apply mor_arrow_like with (target f). 
ap mor_fmor. am. rwi source_oppf' H0. 
rwi mor_opp H0. am. am. 
rw source_oppf'. rw ob_opp. 
assert (target u = source (flip u)). 
rww source_flip. 
apply mor_arrow_like with (source (oppf' f)). am. 
rw H1. rw ob_source. tv. 
rwi source_oppf' H0. 
rwi mor_opp H0. am. uh H; ee; am. 

ir. 
assert (Arrow.like u). 
apply mor_arrow_like with (source (oppf' f)). am. 
assert (Arrow.like v). 
apply mor_arrow_like with (source (oppf' f)). am. 
assert (mor (source f) (flip u)). 
rwi source_oppf' H0. rwi mor_opp H0. am. 
assert (mor (source f) (flip v)). 
rwi source_oppf' H1. rwi mor_opp H1. am.   

rw target_oppf'. rww fmor_oppf'. 
rww fmor_oppf'. 
rw comp_opp. rw flip_flip. rw flip_flip. 
rw fmor_oppf'. rw source_oppf'. 
rw comp_opp. rw flip_flip. 
rw comp_fmor. tv. am. am. am. 
rww source_flip. rww target_flip. sy; am. 
rww mor_opp. 
rww mor_opp.
am. 
rww mor_comp. 
rw mor_opp. 
rw flip_flip. app mor_fmor. 
rw mor_opp. 
rw flip_flip. app mor_fmor. 
rw source_flip. 
rw target_flip. rw target_fmor. 
rw source_fmor. 
ap uneq. rww target_flip. rww source_flip. 
am. am. am. am. 
apply mor_arrow_like with (target f). 
app mor_fmor. 
apply mor_arrow_like with (target f). 
app mor_fmor. 
Qed.



Lemma fcompose_oppf' : forall f g, Functor.axioms f ->
Functor.axioms g -> source f = target g ->
fcompose (oppf' f) (oppf' g) = oppf' (fcompose f g).
Proof.
ir. 
assert (axioms (oppf' f)). 
app oppf'_axioms. 
assert (axioms (oppf' g)).
app oppf'_axioms. 
assert (axioms (fcompose f g)). 
app fcompose_axioms. 

ap axioms_extensionality. 
ap fcompose_axioms. am. am. 
rw source_oppf'. rw target_oppf'. rww H1. 
ap oppf'_axioms. am. 
rw source_fcompose. rw source_oppf'. 
rw source_oppf'. rw source_fcompose. tv. 
rw target_fcompose. rw target_oppf'. 
rw target_oppf'. rw target_fcompose. tv. 

ir. rwi source_fcompose H5. 
cp H5. rwi source_oppf' H6. rwi mor_opp H6. 
rw fmor_fcompose. 
rw fmor_oppf'. rw fmor_oppf'. rw flip_flip.
rw fmor_oppf'. 
rw fmor_fcompose. 
tv. am. am. am. 
am. rw source_oppf'. rw source_fcompose. 
rw mor_opp. am.  am. 
assert (source (oppf' f) = target (oppf' g)).
rw source_oppf'. rw target_oppf'. rw H1. tv. 
rw H7. ap mor_fmor. am. am. am. am. 
rw source_oppf'. rw target_oppf'. rw H1. tv. am. 
Qed.

Lemma oppf'_fidentity : forall a, Category.axioms a ->
oppf' (fidentity a) = fidentity (opp a).
Proof.
ir. 
assert (Category.axioms (opp a)). 
app opp_axioms. 
assert (axioms (oppf' (fidentity a))). 
app oppf'_axioms. 
rww fidentity_axioms. 
ap axioms_extensionality. am. 
rww fidentity_axioms. 
rww source_oppf'. rww source_fidentity. 
rww source_fidentity.  
rww target_oppf'. rww target_fidentity. 
rww target_fidentity. 
ir. 
cp H2. rwi source_oppf' H3. cp H3. 
rwi mor_opp H4. rwi source_fidentity H4. 
rw fmor_oppf'. 
rw fmor_fidentity. rw fmor_fidentity. 
rww flip_flip. rw mor_opp. am. am. 
am. 
Qed.

Lemma oppf'_constant_functor : forall a b x,
Category.axioms a -> ob b x ->
oppf' (constant_functor a b x) =
constant_functor (opp a) (opp b) x.
Proof.
ir. 
assert (Category.axioms b). lu. 
ap constant_functor_criterion. 
rw source_oppf'. rw source_constant_functor. tv. 
rw target_oppf'. rw target_constant_functor. tv. 
ap  oppf'_axioms. ap constant_functor_axioms. 
am. am. am. rww ob_opp. 
ir. 
rw fmor_oppf'. rw fmor_constant_functor. 
rw id_opp. tv. rw ob_opp. am. 
wr mor_opp. am. 
rw source_oppf'. rw source_constant_functor. am. 
Qed.

Lemma oppf'_oppf' : forall f,
Functor.axioms f -> oppf' (oppf' f) = f.
Proof.
ir. ap axioms_extensionality. 
app oppf'_axioms. app oppf'_axioms. am. 
rw source_oppf'. rw source_oppf'. rw opp_opp. 
tv. 
rw target_oppf'. rw target_oppf'. 
rw opp_opp. tv. 
ir. 
rwi source_oppf' H0. 
rwi source_oppf' H0. rwi opp_opp H0. 
rw fmor_oppf'. rw fmor_oppf'. rw flip_flip.
rww flip_flip. 
rw source_oppf'. rw mor_opp. 
rw flip_flip. am. 
rw source_oppf'. rw source_oppf'. rw opp_opp. am. 
Qed.

Definition oppf f := Y (Functor.axioms f) (oppf' f) f.

Lemma unfold_oppf : forall f,
Functor.axioms f -> oppf f = oppf' f.
Proof.
ir. uf oppf. ap (Y_if H). tv. 
Qed. 



Lemma oppf_axioms : forall f, Functor.axioms f ->
Functor.axioms (oppf f).
Proof.
ir. rww unfold_oppf. app oppf'_axioms. 
Qed. 

Lemma oppf_oppf : forall f, oppf (oppf f) = f.
Proof.
ir. apply by_cases with (Functor.axioms f); ir. 
rw unfold_oppf. rw unfold_oppf. 
rww oppf'_oppf'. am. 
app oppf_axioms. 
assert (oppf f = f). 
uf oppf. ap (Y_if_not H). tv. rw H0. am. 
Qed.

Lemma axioms_oppf : forall f,
Functor.axioms (oppf f) = Functor.axioms f.
Proof.
ir. ap iff_eq; ir. wr oppf_oppf. app oppf_axioms. 
app oppf_axioms. 
Qed.


Lemma source_oppf : forall f, 
Functor.axioms f -> source (oppf f) =
opp (source f). 
Proof.
ir. rww unfold_oppf. rww source_oppf'. 
Qed.

Lemma target_oppf : forall f, 
Functor.axioms f -> target (oppf f) =
opp (target f).
Proof.
ir. rww unfold_oppf. rww target_oppf'. 
Qed.

Lemma fmor_oppf : forall f u, 
Functor.axioms f -> mor (source (oppf f)) u ->
fmor (oppf f) u = flip (fmor f (flip u)).
Proof.
ir. rww unfold_oppf. 
rww fmor_oppf'. wrr unfold_oppf. 
Qed.

Lemma fob_oppf : forall f x,
Functor.axioms f -> ob (source (oppf f)) x ->
fob (oppf f) x = fob f x.
Proof.
ir. rww unfold_oppf. 
rww fob_oppf'. wrr unfold_oppf. 
Qed. 



Lemma fcompose_oppf : forall f g, Functor.axioms f ->
Functor.axioms g -> source f = target g ->
fcompose (oppf f) (oppf g) = oppf (fcompose f g).
Proof.
ir. rww unfold_oppf. rww unfold_oppf. 
rw unfold_oppf. 
rww fcompose_oppf'. app fcompose_axioms. 
Qed.

Lemma oppf_fidentity : forall a, Category.axioms a ->
oppf (fidentity a) = fidentity (opp a).
Proof.
ir. rw unfold_oppf. app oppf'_fidentity. 
rww fidentity_axioms. 
Qed.

Lemma oppf_constant_functor : forall a b x,
Category.axioms a -> ob b x ->
oppf (constant_functor a b x) =
constant_functor (opp a) (opp b) x.
Proof.
ir. 
rw unfold_oppf. 
rww oppf'_constant_functor. ap constant_functor_axioms. 
am. uh H0; ee; am. am. 
Qed.






Definition are_finverse f g :=
Functor.axioms f &
Functor.axioms g &
source f = target g &
source g = target f &
fcompose f g = fidentity (source g) &
fcompose g f = fidentity (source f).

Definition has_finverse f :=
exists g, are_finverse f g.

Definition finverse f := choose (are_finverse f).

Lemma finverse_pr : forall f,
has_finverse f -> are_finverse f (finverse f).
Proof.
ir. exact (choose_pr H). 
Qed.


Lemma are_finverse_symm : forall f g,
are_finverse f g -> are_finverse g f.
Proof.
ir.
uh H; ee. 
uhg; ee; am. 
Qed.

Lemma are_finverse_umorphism_inverse : forall f g,
Functor.axioms f -> Functor.axioms g ->
are_finverse f g = Umorphism.are_inverse f g.
Proof.
ir.
app iff_eq; ir. 
uh H1; ee. 
uhg; ee. uhg; ee. 
app functor_umorphism_axioms. 
app functor_umorphism_axioms. 
am. 
uhg; ee. 
app functor_umorphism_axioms. 
app functor_umorphism_axioms. 
am. 
exact H5. exact H6. 
uh H1; ee. uh H1; ee. uh H2; ee. uhg; ee.  
am. am. am. am. exact H3. exact H4. 
Qed.

Lemma finverse_unique : forall f g h,
are_finverse f g -> are_finverse f h ->
g = h.
Proof.
ir. 
apply Umorphism.inverse_unique with f. 
cp H. uh H1; ee.
uhg; ee. app functor_umorphism_axioms.
uh H2; ee; am. uh H0; ee. 
uhg; ee. app functor_umorphism_axioms. 
uh H1; ee; am. 
wrr are_finverse_umorphism_inverse. uh H; ee; am. 
uh H; ee; am. 
wrr are_finverse_umorphism_inverse. uh H0; ee; am. 
uh H0; ee; am. 
Qed.


End Functor.


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
Require Export notation.


Module Universe.
Export Function.
Export Notation.
Export Arrow.
Export Umorphism. 


Definition axioms u :=
(forall x y, inc x u -> inc y x -> inc y u) &
(forall x (f:x->E), inc x u -> (sub (IM f) u) ->
inc (IM f) u) &
(forall x, inc x u -> inc (union x) u) &
(forall x, inc x u -> inc (powerset x) u) &
inc nat u &
inc string u.

Lemma inc_trans_u : forall x u, axioms u -> 
(exists y, (inc x y & inc y u)) -> inc x u.
Proof.
ir. nin H0. uh H; ee. 
app (H x0 x). 
Qed. 

Lemma inc_powerset_u : forall x u, axioms u ->  inc x u ->
inc (powerset x) u.
Proof.
ir. uh H; ee; au. 
Qed. 

Lemma inc_nat_u : forall u, axioms u -> inc nat u.
Proof.
ir. uh H; ee; au.
Qed.

Lemma inc_R_nat_u : forall (n:nat) u, axioms u -> inc (R n) u.
Proof.
ir. ap inc_trans_u. am. sh nat. 
ee. uf inc. sh n. tv. app inc_nat_u. 
Qed. 

Lemma inc_prop_u : forall u, axioms u -> inc Prop u.
Proof.
ir. wr R_two_prop. ap inc_R_nat_u. am. 
Qed.

Lemma inc_R_a_prop_u : forall u (p:Prop), axioms u -> 
inc (R p) u.
Proof.
ir. app inc_trans_u. sh Prop. ee. 
uf inc. sh p; tv. app inc_prop_u. 
Qed. 

Lemma inc_a_prop_u : forall u (p:Prop), axioms u -> inc p u.
Proof.
ir. 
assert (R p = p). rww prop_realization. wr H0. 
app inc_R_a_prop_u. 
Qed.

Lemma inc_proof_u : forall u (p:Prop) (t:p), axioms u ->
inc (R t) u. 
Proof.
ir. app inc_trans_u. 
sh p. ee. ap R_inc. app inc_a_prop_u. 
Qed. 


Lemma inc_string_u : forall u, axioms u -> inc string u.
Proof.
ir. uh H; ee; au.
Qed. 

Lemma inc_subset_u : forall x u, axioms u ->
(exists y, (inc y u & sub x y)) -> inc x u.
Proof. 
ir. nin H0. ee. ap inc_trans_u. am. 
sh (powerset x0). ee. ap powerset_inc. am. 
app inc_powerset_u. 
Qed. 

Lemma inc_emptyset_u : forall u, axioms u ->
inc emptyset u.
Proof.
ir. app inc_subset_u. sh nat. 
ee. app inc_nat_u. uhg; ir.
cp (B H0). nin X0 || nin H1. 
Qed. 

Lemma inc_IM_u : forall x (f:x->E) u,
axioms u -> inc x u -> sub (IM f) u ->
inc (IM f) u.
Proof.
ir. uh H; ee. ap H2. am. am. 
Qed. 


Definition doubleton_step :forall (x y:E) (n:nat), E.
ir. nin n. exact x. exact y. 
Defined. 

Lemma IM_doubleton_step: forall x y,
IM (doubleton_step x y) = (doubleton x y).
Proof.
ir. app extensionality; uhg; ir. 
cp (IM_exists H). nin H0. 
nin x1. assert (x = x0). am. wr H1. 
ap doubleton_first. 
assert (y = x0). am. wr H1. 
ap doubleton_second. 
ap IM_inc. 
cp (doubleton_or H). nin H0. sh 0. sy; am. 
sh 1. sy; am. 
Qed. 

Lemma inc_doubleton_u : forall x y u, 
axioms u -> inc x u -> inc y u -> inc (doubleton x y) u.
Proof.
ir. 
wr IM_doubleton_step. 
ap inc_IM_u. am. app inc_nat_u. 
rw IM_doubleton_step. uhg; ir. 
cp (doubleton_or H2). nin H3. rww H3.
rww H3. 
Qed.

Lemma inc_singleton_u : forall x u,
axioms u -> inc x u -> inc (singleton x) u.
Proof.
ir. wr doubleton_singleton. app inc_doubleton_u. 
Qed. 

Lemma inc_pair_u : forall x y u, 
axioms u -> inc x u -> inc y u -> inc (pair x y) u.
Proof.
ir. uf pair. 
app inc_doubleton_u. app inc_singleton_u. 
app inc_doubleton_u. app inc_emptyset_u. 
app inc_singleton_u. 
Qed.

Lemma sub_u : forall x u, axioms u -> inc x u ->
sub x u.
Proof.
ir. uhg; ir. app inc_trans_u. sh x; ee; am. 
Qed. 

Lemma inc_function_create_u : forall x f u,
axioms u -> inc x u -> 
(forall y, inc y x -> inc (f y) u) ->
inc (L x f) u.
Proof.
ir. uf Function.create. 
uf Image.create. ap inc_IM_u. am. am. 
uhg; ir. cp (IM_exists H2). nin H3. wr H3.
ap inc_pair_u. am. app inc_trans_u. 
sh x; ee; try am. ap R_inc. 
ap H1. ap R_inc. 
Qed. 

Lemma inc_function_tcreate_u : forall x (f:x->E) u,
axioms u -> inc x u -> 
(forall y, inc (f y) u) ->
inc (tcreate f) u. 
Proof.
ir. uf tcreate. 
ap inc_function_create_u. am. am. 
ir. 
assert ( (Yy (fun hyp : inc y x => f (B hyp)) emptyset) 
= f (B H2)). 
ap (Yy_if (hyp := H2)). tv. 
rw H3. ap H1. 
Qed. 





Lemma inc_pr1_of_pair_u : forall u x,
axioms u -> (exists y, inc (pair x y) u) -> inc x u.
Proof.
ir. nin H0. 
app inc_trans_u. sh (singleton x). 
ee. ap singleton_inc. 
app inc_trans_u. sh (pair x x0). ee. uf pair.
ap doubleton_first. am. 
Qed.

Lemma inc_pr2_of_pair_u : forall u y,
axioms u -> (exists x, inc (pair x y) u) -> inc y u.
Proof.
ir. nin H0. app inc_trans_u. sh (singleton y).
ee. ap singleton_inc. 
app inc_trans_u. 
sh (doubleton emptyset (singleton y)). ee. ap doubleton_second. 
app inc_trans_u. sh (pair x y). 
ee. uf pair; ap doubleton_second. am. 
Qed. 

Lemma inc_V_u : forall f x u,
axioms u -> inc f u -> inc x u -> inc (V x f) u.
Proof.
ir. cp (V_or x f). nin H2. 
app inc_pr2_of_pair_u. sh x. 
app inc_trans_u. sh f; ee; try am. 
ee. rw H3. app inc_emptyset_u. 
Qed. 

Lemma inc_denote_u : forall s x a u,
axioms u -> inc a u -> inc s string -> inc x u ->
inc (denote s x a) u.
Proof.
ir. uf denote. 
app inc_function_create_u. app inc_string_u. ir.
apply by_cases with (y=s);
ir. rww Y_if_rw. 
rww Y_if_not_rw. app inc_V_u. 
app inc_trans_u. sh string; ee; try am. 
app inc_string_u. 
Qed. 




Lemma inc_binary_u : forall x f u,
axioms u -> inc x u -> 
(forall y z, inc y x -> inc z x -> inc (f y z) u) ->
inc (binary x f) u.
Proof.
ir. uf binary. 
app inc_function_create_u. 
ir. app inc_function_create_u. ir. 
au. 
Qed. 

Lemma inc_stop_u : forall u,
axioms u -> inc stop u. 
Proof.
ir. uf stop. 
app inc_function_create_u. app inc_string_u. ir. 
app inc_emptyset_u. 
Qed. 

Ltac incdu := 
first [
app inc_denote_u; try drw_solve| app inc_stop_u].


Lemma inc_arrow_create_u : forall s t a u,
axioms u -> inc s u -> inc t u -> inc a u ->
inc (Arrow.create s t a) u. 
Proof.
ir. uf Arrow.create. 
incdu. incdu. incdu. incdu. 
Qed. 

Lemma inc_Uempty_u : forall u, axioms u ->
inc Umorphism.Uempty u.
Proof.
ir. uf Umorphism.Uempty. incdu. 
Qed. 

End Universe. 

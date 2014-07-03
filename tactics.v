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


Require Export axioms.

Set Implicit Arguments.
Unset Strict Implicit.




Module Tactics1.
Ltac ir := intros.

Ltac rw u := rewrite u.
Ltac rwi u h := rewrite u in h.

Ltac wr u := rewrite <- u.
Ltac wri u h := rewrite <- u in h.

Ltac ap h := apply h.

(*
Ltac EasyAssumption :=
  match goal with
  | id1:(?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X8) |-
  (?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X8) =>
      exact id1
  | id1:(?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7) |- (?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7) =>
      exact id1
  | id1:(?X1 ?X2 ?X3 ?X4 ?X5 ?X6) |- (?X1 ?X2 ?X3 ?X4 ?X5 ?X6) =>
      exact id1
  | id1:(?X1 ?X2 ?X3 ?X4 ?X5) |- (?X1 ?X2 ?X3 ?X4 ?X5) =>
      exact id1
  | id1:(?X1 ?X2 ?X3 ?X4) |- (?X1 ?X2 ?X3 ?X4) =>
      exact id1
  | id1:(?X1 ?X2 ?X3) |- (?X1 ?X2 ?X3) => exact id1
  | id1:(?X1 ?X2) |- (?X1 ?X2) => exact id1
  | id1:?X1 |- ?X2 => ap id1
  | _ => fail
  end.

Ltac am := solve [ EasyAssumption | assumption ].
*)

Ltac am := assumption.



Ltac au := first [ solve [ am ] | auto ].
Ltac eau := eauto. 
Ltac tv := trivial.
Ltac sy := symmetry  in |- *.

Ltac uf u := unfold u in |- *. Ltac ufi u h := unfold u in h.

Ltac nin h := induction h.




Ltac CompareTac a b :=
  assert (toclear : a = a); [ exact (refl_equal b) | clear toclear ].

Ltac UnfoldHead1 h :=
  match constr:h with
  | (?X1 ?X2) => unfold X1 in h
  | _ => fail
  end.

(*** we don't actually want to unfold certain things ***)
Ltac Good_Unfold g h :=
  match constr:g with
  | inc => fail
  | _ => unfold g in h
  end.

Ltac Unfold_Head_R g h :=
  match constr:g with
  | (?X1 _ _ _ _ _ _ _ _ _ _) => Good_Unfold X1 h
  | (?X1 _ _ _ _ _ _ _ _ _) => Good_Unfold X1 h
  | (?X1 _ _ _ _ _ _ _ _) => Good_Unfold X1 h
  | (?X1 _ _ _ _ _ _ _) => Good_Unfold X1 h
  | (?X1 _ _ _ _ _ _) => Good_Unfold X1 h
  | (?X1 _ _ _ _ _) => Good_Unfold X1 h
  | (?X1 _ _ _ _) => Good_Unfold X1 h
  | (?X1 _ _ _) => Good_Unfold X1 h
  | (?X1 _ _) => Good_Unfold X1 h
  | (?X1 _) => Good_Unfold X1 h
  | ?X1 => Good_Unfold X1 h
  end.


Ltac Unfold_Head h :=
  match goal with
  | id1:?X1 |- _ => CompareTac id1 h; Unfold_Head_R X1 h
  | _ => fail
  end.

Ltac Exploit h :=
  match goal with
  | id1:?X1 |- _ =>
      CompareTac id1 h; assert X1; [ am | Unfold_Head h; Exploit h ]
  | _ => idtac
  end.

Ltac xlt h := Exploit h.

Definition DONE (A : Type) (a : A) := a.
Definition TODO (A : Type) (a : A) := a.

Ltac TodoAll :=
  match goal with
  | id1:?X1 |- _ =>
      match constr:X1 with
      | (TODO _) => fail
      | _ => change (TODO X1) in id1; TodoAll
      end
  | _ => idtac
  end.

Definition CheckProp (P : Prop) := P.

Ltac CheckPropTac P := assert (toclear : CheckProp P); [ am | clear toclear ].




Notation E1 := (E -> E).
Notation E2 := (E -> E1).
Notation E3 := (E -> E2).
Notation E4 := (E -> E3).
Notation E5 := (E -> E4).
Notation E6 := (E -> E5).
(** thus for example E3 = E -> E -> E -> E **)

Notation EP := (E -> Prop).
Notation E2P := (E -> EP).
Notation E3P := (E -> E2P).
Notation E4P := (E -> E3P).


Definition A := and.
Infix "&":= and (right associativity, at level 100).

Ltac Deconj :=
  match goal with
  |  |- (A _ _) => unfold A in |- *; ap conj; [ Deconj | Deconj ]
  |  |- (_ & _) => ap conj; [ Deconj | Deconj ]
  |  |- (and _ _) => ap conj; [ Deconj | Deconj ]
  |  |- (_ /\ _) => ap conj; [ Deconj | Deconj ]
  |  |- _ => au
  end.

Ltac EasyDeconj :=
  match goal with
  |  |- (A _ _) => unfold A in |- *; ap conj; [ EasyDeconj | EasyDeconj ]
  |  |- (_ & _) => ap conj; [ EasyDeconj | EasyDeconj ]
  |  |- (and _ _) => ap conj; [ EasyDeconj | EasyDeconj ]
  |  |- (_ /\ _) => ap conj; [ EasyDeconj | EasyDeconj ]
  |  |- _ => idtac
  end.




Ltac Expand :=
  match goal with
  | id1:(A ?X1 ?X2) |- _ =>
      unfold A in id1; nin id1; Expand
  | id1:(?X1 & ?X2) |- _ => nin id1; Expand
  | id1:(and ?X1 ?X2) |- _ => nin id1; Expand
  | id1:(?X1 /\ ?X2) |- _ => nin id1; Expand
  |  |- _ => Deconj
  end.



(*** we write a tactic which is like Pose but which is anonymous ***)
Ltac Remind u :=
  set (recalx := u);
   match goal with
   | recalx:?X1 |- _ => assert X1; [ exact recalx | clear recalx ]
   end.

Ltac cp := Remind. 


Ltac EasyExpand :=
  match goal with
  | id1:(A ?X1 ?X2) |- _ =>
      unfold A in id1; nin id1; EasyExpand
  | id1:(?X1 /\ ?X2) |- _ => nin id1; EasyExpand
  | id1:(?X1 /\ ?X2) |- _ => nin id1; EasyExpand
  |  |- _ => EasyDeconj
  end.


Ltac ee := EasyExpand.

Ltac xd := Expand.




Ltac PreExplode n :=
  match constr:n with
  | 0 => idtac
  | (S ?X1) =>
      match goal with
      | id1:?X2 |- _ =>
          CheckPropTac X2;
           match constr:X2 with
           | (DONE ?X3) => fail
           | _ =>
               assert (DONE X2);
                [ unfold DONE in |- *; am
                | Unfold_Head id1; EasyExpand; PreExplode X1 ]
           end
      | _ => idtac
      end
  end.

Ltac ClearDone :=
  match goal with
  | id1:(DONE ?X1) |- _ => unfold DONE in id1; ClearDone
  | _ => idtac
  end.



Ltac Exp := PreExplode 5; ClearDone.
Ltac Expl := PreExplode 10; ClearDone. 
Ltac Explode := PreExplode 100; ClearDone.



Ltac CleanUp :=
  match goal with
  | id1:?X1,id2:?X1 |- _ => CheckPropTac X1; clear id2; CleanUp
  | _ => idtac
  end.

Ltac xde := Explode.
Ltac cx := Explode; CleanUp.

(***** we would like a general Cycle construction (can we parametrize tactics over tactics???) ***)


Ltac sh x := first
 [ ap nonemptyT_intro; exact x
 | apply ex_intro with x
 | apply ex_intro with x
 | apply nonempty_intro with x ].


Lemma seq_deconj : forall P Q : Prop, P -> (P -> Q) -> (P & Q). 
ir. xd. Qed. 

Ltac dj :=
  match goal with
  |  |- (A ?X1 ?X2) => ap seq_deconj; ir; dj
  |  |- (?X1 & ?X2) => ap seq_deconj; ir; dj
  | _ => idtac
  end. 



Ltac MiddleDeconj :=
  match goal with
  |  |- (A _ _) =>
      unfold A in |- *; ap conj; [ MiddleDeconj | MiddleDeconj ]
  |  |- (_ /\ _) => ap conj; [ MiddleDeconj | MiddleDeconj ]
  |  |- (_ /\ _) => ap conj; [ MiddleDeconj | MiddleDeconj ]
  |  |- _ => first
  [ solve [ trivial | am | sy; am ] | idtac ]
  end.



Ltac MiddleExpand :=
  match goal with
  | id1:(A ?X1 ?X2) |- _ =>
      unfold A in id1; nin id1; MiddleExpand
  | id1:(?X1 /\ ?X2) |- _ => nin id1; MiddleExpand
  | id1:(?X1 /\ ?X2) |- _ => nin id1; MiddleExpand
  |  |- _ => MiddleDeconj
  end.

Ltac xe := MiddleExpand.

Definition type_of (T : Type) (t : T) := T.

Ltac Copy a :=
  assert (type_of a);
   [ exact a | match goal with
               | id1:(type_of _) |- _ => ufi type_of id1
               end ].

Ltac ufk a b := Copy b; ufi a b. Ltac uh a := red in a.
(*** replaces Unfold_Head a. as mentionned by Hugo ***)

Ltac uhg := red in |- *. 
(*** Match Context With 
[|-(?1 ? ? ? ? ? ? ? ? ? ?)] -> Unfold ?1 |
[|-(?1 ? ? ? ? ? ? ? ? ?)] -> Unfold ?1 |
[|-(?1 ? ? ? ? ? ? ? ?)] -> Unfold ?1 |
[|-(?1 ? ? ? ? ? ? ?)] -> Unfold ?1 |
[|-(?1 ? ? ? ? ? ?)] -> Unfold ?1 |
[|-(?1 ? ? ? ? ?)] -> Unfold ?1 |
[|-(?1 ? ? ? ?)] -> Unfold ?1 |
[|-(?1 ? ? ?)] -> Unfold ?1 |
[|-(?1 ? ?)] -> Unfold ?1 |
[|-(?1 ?)] -> Unfold ?1 |
_-> Idtac.
***)

Ltac util a:=
match (type of a) with 
| (?X1 -> ?X2 -> ?X3 -> ?X4 -> ?X5 -> ?X6) => assert X6; [apply a |idtac]
| (?X1 -> ?X2 -> ?X3 -> ?X4 -> ?X5) => assert X5; [apply a |idtac]
| (?X1 -> ?X2 -> ?X3 -> ?X4) => assert X4; [apply a |idtac]
| (?X1 -> ?X2 -> ?X3) => assert X3; [apply a |idtac]
| (?X1 -> ?X2) => assert X2; [apply a |idtac]
| _ => fail
end. 


Lemma uneq : forall (f:E1) x y,
x = y -> f x = f y.
Proof.
ir. rw H; tv. 
Qed. 



Ltac LookUpErasing :=
lazymatch goal with 
| id1 : ?X1 |- _ => 
first [exact id1 | uh id1; ee; try tv; try am|clear id1]; LookUpErasing
| _ => fail
end. 

Ltac lu := LookUpErasing.
(*** not all that efficient for time so don't use too often ***)

Ltac app u :=
(ap u; try tv; try am).

Ltac rww u :=
(rw u; try tv; try am).

Ltac wrr u :=
(wr u; try tv; try am). 

Ltac orbr t :=
match goal with 
| |- (_ \/ _) => 
  solve [ap or_introl; (orbr t) | ap or_intror; (orbr t)]
| _ => t
end.



Lemma orbr_test : False \/ False \/ True \/ False \/ False.
Proof.
orbr tv. 
Qed.  


Module PWclear.
Ltac pw1 := fail.
Ltac pw2 := fail. 
Ltac pw3 := fail. 
Ltac pw4 := fail. 
Ltac pw5 := fail. 
Ltac pw6 := fail. 
Ltac pw7 := fail. 
Ltac pw8 := fail. 
Ltac pw9 := fail. 
Ltac pw10 := fail. 
Ltac pw11 := fail. 
Ltac pw12 := fail. 
Ltac pw13 := fail. 
Ltac pw14 := fail. 
Ltac pw15 := fail. 

End PWclear.

Ltac aw := 
autorewrite with aw; try tv; try am. 

Lemma forup : forall A B (f g:A -> B) (a b : A),
f = g -> a = b -> f a = g b.
Proof.
ir. rw H0. rw H. tv. 
Qed. 



Ltac up := 
apply forup with (A:= E); try tv; try am; try up.





End Tactics1.
Export Tactics1.




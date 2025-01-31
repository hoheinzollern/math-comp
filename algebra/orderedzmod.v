(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import ssrAC div fintype path bigop order finset fingroup.
From mathcomp Require Import ssralg poly.

(******************************************************************************)
(*                            Number structures                               *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* This file defines some classes to manipulate number structures, i.e,       *)
(* structures with an order and a norm. To use this file, insert              *)
(* "Import Num.Theory." before your scripts. You can also "Import Num.Def."   *)
(* to enjoy shorter notations (e.g., minr instead of Num.min, lerif instead   *)
(* of Num.leif, etc.).                                                        *)
(*                                                                            *)
(* This file defines the following number structures:                         *)
(*                                                                            *)
(*  porderZmodType == join of Order.POrder and GRing.Zmodule                  *)
(*                    The HB class is called POrderedZmodule.                 *)
(*  semiNormedZmodType == Zmodule with a semi-norm                            *)
(*                        The HB class is called SemiNormedZmodule.           *)
(*  normedZmodType == Zmodule with a norm                                     *)
(*                    The HB class is called NormedZmodule.                   *)
(*   numDomainType == Integral domain with an order and a norm                *)
(*                    The HB class is called NumDomain.                       *)
(*    numFieldType == Field with an order and a norm                          *)
(*                    The HB class is called NumField.                        *)
(* numClosedFieldType == Partially ordered Closed Field with conjugation      *)
(*                    The HB class is called ClosedField.                     *)
(*  realDomainType == Num domain where all elements are positive or negative  *)
(*                    The HB class is called RealDomain.                      *)
(*   realFieldType == Num Field where all elements are positive or negative   *)
(*                    The HB class is called RealField.                       *)
(*         rcfType == A Real Field with the real closed axiom                 *)
(*                    The HB class is called RealClosedField.                 *)
(*                                                                            *)
(* The ordering symbols and notations (<, <=, >, >=, _ <= _ ?= iff _,         *)
(* _ < _ ?<= if _, >=<, and ><) and lattice operations (meet and join)        *)
(* defined in order.v are redefined for the ring_display in the ring_scope    *)
(* (%R). 0-ary ordering symbols for the ring_display have the suffix "%R",    *)
(* e.g., <%R. All the other ordering notations are the same as order.v.       *)
(*                                                                            *)
(* Over these structures, we have the following operations:                   *)
(*             `|x| == norm of x                                              *)
(*         Num.sg x == sign of x: equal to 0 iff x = 0, to 1 iff x > 0, and   *)
(*                     to -1 in all other cases (including x < 0)             *)
(*  x \is a Num.pos <=> x is positive (:= x > 0)                              *)
(*  x \is a Num.neg <=> x is negative (:= x < 0)                              *)
(* x \is a Num.nneg <=> x is positive or 0 (:= x >= 0)                        *)
(* x \is a Num.npos <=> x is negative or 0 (:= x <= 0)                        *)
(* x \is a Num.real <=> x is real (:= x >= 0 or x < 0)                        *)
(*       Num.sqrt x == in a real-closed field, a positive square root of x if *)
(*                     x >= 0, or 0 otherwise                                 *)
(* For numeric algebraically closed fields we provide the generic definitions *)
(*         'i == the imaginary number (:= sqrtC (-1))                         *)
(*      'Re z == the real component of z                                      *)
(*      'Im z == the imaginary component of z                                 *)
(*        z^* == the complex conjugate of z (:= conjC z)                      *)
(*    sqrtC z == a nonnegative square root of z, i.e., 0 <= sqrt x if 0 <= x  *)
(*  n.-root z == more generally, for n > 0, an nth root of z, chosen with a   *)
(*               minimal non-negative argument for n > 1 (i.e., with a        *)
(*               maximal real part subject to a nonnegative imaginary part)   *)
(*               Note that n.-root (-1) is a primitive 2nth root of unity,    *)
(*               an thus not equal to -1 for n odd > 1 (this will be shown in *)
(*               file cyclotomic.v).                                          *)
(*                                                                            *)
(* - list of prefixes :                                                       *)
(*   p : positive                                                             *)
(*   n : negative                                                             *)
(*   sp : strictly positive                                                   *)
(*   sn : strictly negative                                                   *)
(*   i : interior = in [0, 1] or ]0, 1[                                       *)
(*   e : exterior = in [1, +oo[ or ]1; +oo[                                   *)
(*   w : non strict (weak) monotony                                           *)
(*                                                                            *)
(* Pdeg2.NumClosed : theory of the degree 2 polynomials on NumClosedField.    *)
(* Pdeg2.NumClosedMonic : theory of Pdeg2.NumClosed specialized to monic      *)
(*   polynomials.                                                             *)
(* Pdeg2.Real : theory of the degree 2 polynomials on RealField and rcfType.  *)
(* Pdeg2.RealMonic : theory of Pdeg2.Real specialized to monic polynomials.   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "n .-root" (at level 2, format "n .-root").
Reserved Notation "'i" (at level 0).
Reserved Notation "'Re z" (at level 10, z at level 8).
Reserved Notation "'Im z" (at level 10, z at level 8).

Reserved Notation "x %:E" (at level 2, format "x %:E").
Reserved Notation "x %:dE" (at level 2, format "x %:dE").
Reserved Notation "x +? y" (at level 50, format "x  +?  y").
Reserved Notation "x *? y" (at level 50, format "x  *?  y").
Reserved Notation "'\bar' x" (at level 2, format "'\bar'  x").
Reserved Notation "'\bar' '^d' x" (at level 2, format "'\bar' '^d'  x").
Reserved Notation "{ 'posnum' '\bar' R }" (at level 0,
  format "{ 'posnum'  '\bar'  R }").
Reserved Notation "{ 'nonneg' '\bar' R }" (at level 0,
  format "{ 'nonneg'  '\bar'  R }").

Declare Scope ereal_dual_scope.
Declare Scope ereal_scope.
Local Open Scope order_scope.
Local Open Scope ring_scope.

Import Order.TTheory GRing.Theory.


Fact ring_display : Order.disp_t. Proof. exact. Qed.

HB.mixin Record Nmodule_isPOrdered R of GRing.Nmodule R
   & Order.isPOrder ring_display R := {
  lerD2l : forall x : R, {mono +%R x : y z / y <= z}
}.

(* TODO provide the positive cone definition of porderZmodType *)
(* HB.factory Record ZmodulePositiveCone_isPOrdered of GRing.Zmodule R *)
(*    & Order.isPOrder ring_display R := { *)
(*   (* TODO: is posnum the right name? *) *)
(*   posnum : {pred R}; *)
(*   posnum0 :  *)

#[short(type="porderNmodType")]
HB.structure Definition POrderedNmodule :=
  { R of Order.isPOrder ring_display R & GRing.Nmodule R & Nmodule_isPOrdered R}.
#[short(type="porderZmodType")]
HB.structure Definition POrderedZmodule :=
  { R of Order.isPOrder ring_display R & GRing.Zmodule R & Nmodule_isPOrdered R}.

Bind Scope ring_scope with POrderedNmodule.sort.
Bind Scope ring_scope with POrderedZmodule.sort.

Module Import Def.

Notation ler := (@Order.le ring_display _) (only parsing).
Notation "@ 'ler' R" := (@Order.le ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation ltr := (@Order.lt ring_display _) (only parsing).
Notation "@ 'ltr' R" := (@Order.lt ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation ger := (@Order.ge ring_display _) (only parsing).
Notation "@ 'ger' R" := (@Order.ge ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation gtr := (@Order.gt ring_display _) (only parsing).
Notation "@ 'gtr' R" := (@Order.gt ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation lerif := (@Order.leif ring_display _) (only parsing).
Notation "@ 'lerif' R" := (@Order.leif ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation lterif := (@Order.lteif ring_display _) (only parsing).
Notation "@ 'lteif' R" := (@Order.lteif ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation comparabler := (@Order.comparable ring_display _) (only parsing).
Notation "@ 'comparabler' R" := (@Order.comparable ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation maxr := (@Order.max ring_display _).
Notation "@ 'maxr' R" := (@Order.max ring_display R)
    (at level 10, R at level 8, only parsing) : function_scope.
Notation minr := (@Order.min ring_display _).
Notation "@ 'minr' R" := (@Order.min ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.

Section OrderedZmodDef.
Context {R : porderNmodType}.

Definition Rpos_pred := fun x : R => 0 < x.
Definition Rpos : qualifier 0 R := [qualify x | Rpos_pred x].
Definition Rneg_pred := fun x : R => x < 0.
Definition Rneg : qualifier 0 R := [qualify x : R | Rneg_pred x].
Definition Rnneg_pred := fun x : R => 0 <= x.
Definition Rnneg : qualifier 0 R := [qualify x : R | Rnneg_pred x].
Definition Rnpos_pred := fun x : R => x <= 0.
Definition Rnpos : qualifier 0 R := [qualify x : R | Rnpos_pred x].
Definition Rreal_pred := fun x : R => (0 <= x) || (x <= 0).
Definition Rreal : qualifier 0 R := [qualify x : R | Rreal_pred x].

End OrderedZmodDef.

End Def.

Arguments Rpos_pred _ _ /.
Arguments Rneg_pred _ _ /.
Arguments Rnneg_pred _ _ /.
Arguments Rreal_pred _ _ /.

(* Shorter qualified names, when Num.Def is not imported. *)
Notation le := ler (only parsing).
Notation lt := ltr (only parsing).
Notation ge := ger (only parsing).
Notation gt := gtr (only parsing).
Notation leif := lerif (only parsing).
Notation lteif := lterif (only parsing).
Notation comparable := comparabler (only parsing).
Notation max := maxr.
Notation min := minr.
Notation pos := Rpos.
Notation neg := Rneg.
Notation nneg := Rnneg.
Notation npos := Rnpos.
Notation real := Rreal.

(* (Exported) symbolic syntax. *)
Module Import Syntax.
Import Def.

Notation "<=%R" := le : function_scope.
Notation ">=%R" := ge : function_scope.
Notation "<%R" := lt : function_scope.
Notation ">%R" := gt : function_scope.
Notation "<?=%R" := leif : function_scope.
Notation "<?<=%R" := lteif : function_scope.
Notation ">=<%R" := comparable : function_scope.
Notation "><%R" := (fun x y => ~~ (comparable x y)) : function_scope.

Notation "<= y" := (ge y) : ring_scope.
Notation "<= y :> T" := (<= (y : T)) (only parsing) : ring_scope.
Notation ">= y"  := (le y) : ring_scope.
Notation ">= y :> T" := (>= (y : T)) (only parsing) : ring_scope.

Notation "< y" := (gt y) : ring_scope.
Notation "< y :> T" := (< (y : T)) (only parsing) : ring_scope.
Notation "> y" := (lt y) : ring_scope.
Notation "> y :> T" := (> (y : T)) (only parsing) : ring_scope.

Notation "x <= y" := (le x y) : ring_scope.
Notation "x <= y :> T" := ((x : T) <= (y : T)) (only parsing) : ring_scope.
Notation "x >= y" := (y <= x) (only parsing) : ring_scope.
Notation "x >= y :> T" := ((x : T) >= (y : T)) (only parsing) : ring_scope.

Notation "x < y"  := (lt x y) : ring_scope.
Notation "x < y :> T" := ((x : T) < (y : T)) (only parsing) : ring_scope.
Notation "x > y"  := (y < x) (only parsing) : ring_scope.
Notation "x > y :> T" := ((x : T) > (y : T)) (only parsing) : ring_scope.

Notation "x <= y <= z" := ((x <= y) && (y <= z)) : ring_scope.
Notation "x < y <= z" := ((x < y) && (y <= z)) : ring_scope.
Notation "x <= y < z" := ((x <= y) && (y < z)) : ring_scope.
Notation "x < y < z" := ((x < y) && (y < z)) : ring_scope.

Notation "x <= y ?= 'iff' C" := (lerif x y C) : ring_scope.
Notation "x <= y ?= 'iff' C :> R" := ((x : R) <= (y : R) ?= iff C)
  (only parsing) : ring_scope.

Notation "x < y ?<= 'if' C" := (lterif x y C) : ring_scope.
Notation "x < y ?<= 'if' C :> R" := ((x : R) < (y : R) ?<= if C)
  (only parsing) : ring_scope.

Notation ">=< y" := [pred x | comparable x y] : ring_scope.
Notation ">=< y :> T" := (>=< (y : T)) (only parsing) : ring_scope.
Notation "x >=< y" := (comparable x y) : ring_scope.

Notation ">< y" := [pred x | ~~ comparable x y] : ring_scope.
Notation ">< y :> T" := (>< (y : T)) (only parsing) : ring_scope.
Notation "x >< y" := (~~ (comparable x y)) : ring_scope.

Export Order.POCoercions.

End Syntax.

Section porderZmodTypeTheory.
Variable (R : porderZmodType).
Implicit Types (x y : R).

Lemma lerD2r x : {mono +%R^~ x : y z / y <= z}.
Proof. by move=> y z; rewrite ![_ + x]addrC lerD2l. Qed.

Lemma ltrD2r x : {mono +%R^~ x : y z / y < z}.
Proof. by move=> y z; rewrite !lt_neqAle lerD2r (inj_eq (addIr _)). Qed.

Lemma ltrD2l x : {mono +%R x : y z / y < z}.
Proof. by move=> y z; rewrite !lt_neqAle lerD2l (inj_eq (addrI _)). Qed.

Lemma addr_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x + y.
Proof.
move=> x_ge0 y_ge0; have := lerD2r y 0 x.
by rewrite add0r x_ge0 => /(le_trans y_ge0).
Qed.

Lemma addr_gt0 x y : 0 < x -> 0 < y -> 0 < x + y.
Proof.
move=> x_gt0 y_gt0; have := ltrD2r y 0 x.
by rewrite add0r x_gt0 => /(lt_trans y_gt0).
Qed.

Lemma posrE x : (x \is pos) = (0 < x). Proof. by []. Qed.
Lemma nnegrE x : (x \is nneg) = (0 <= x). Proof. by []. Qed.
Lemma realE x : (x \is real) = (0 <= x) || (x <= 0). Proof. by []. Qed.
Lemma negrE x : (x \is neg) = (x < 0). Proof. by []. Qed.
Lemma nposrE x : (x \is npos) = (x <= 0). Proof. by []. Qed.

Lemma le0r x : (0 <= x) = (x == 0) || (0 < x).
Proof. by rewrite le_eqVlt eq_sym. Qed.
Lemma lt0r x : (0 < x) = (x != 0) && (0 <= x). Proof. exact: lt_def. Qed.

Lemma lt0r_neq0 (x : R) : 0 < x -> x != 0. Proof. by move=> /gt_eqF ->. Qed.
Lemma ltr0_neq0 (x : R) : x < 0 -> x != 0. Proof. by move=> /lt_eqF ->. Qed.

Lemma subr_ge0 x y : (0 <= x - y) = (y <= x).
Proof. by rewrite -(@lerD2r y) addrNK add0r. Qed.

Lemma oppr_ge0 x : (0 <= - x) = (x <= 0).
Proof. by rewrite -sub0r subr_ge0. Qed.

Lemma subr_gt0 x y : (0 < y - x) = (x < y).
Proof. by rewrite !lt_def subr_eq0 subr_ge0. Qed.

Lemma subr_le0  x y : (y - x <= 0) = (y <= x).
Proof. by rewrite -[LHS]subr_ge0 opprB add0r subr_ge0. Qed.  (* FIXME: rewrite pattern *)

Lemma subr_lt0  x y : (y - x < 0) = (y < x).
Proof. by rewrite -[LHS]subr_gt0 opprB add0r subr_gt0. Qed.  (* FIXME: rewrite pattern *)

Definition subr_lte0 := (subr_le0, subr_lt0).
Definition subr_gte0 := (subr_ge0, subr_gt0).
Definition subr_cp0 := (subr_lte0, subr_gte0).


Fact nneg_addr_closed : addr_closed (@nneg R).
Proof. by split; [apply: lexx | apply: addr_ge0]. Qed.
#[export]
HB.instance Definition _ := GRing.isAddClosed.Build R Rnneg_pred
  nneg_addr_closed.

Fact real_oppr_closed : oppr_closed (@real R).
Proof. by move=> x; rewrite /= !realE oppr_ge0 orbC -!oppr_ge0 opprK. Qed.
#[export]
HB.instance Definition _ := GRing.isOppClosed.Build R Rreal_pred
  real_oppr_closed.

(* Comparability in a numDomain *)

Lemma comparable0r x : (0 >=< x)%R = (x \is real). Proof. by []. Qed.

Lemma comparabler0 x : (x >=< 0)%R = (x \is real).
Proof. by rewrite comparable_sym. Qed.

Lemma subr_comparable0 x y : (x - y >=< 0)%R = (x >=< y)%R.
Proof. by rewrite /comparable subr_ge0 subr_le0. Qed.

Lemma comparablerE x y : (x >=< y)%R = (x - y \is real).
Proof. by rewrite -comparabler0 subr_comparable0. Qed.

(* Lemma  comparabler_trans : transitive (comparable : rel R). *)
(* Proof. *)
(* move=> y x z; rewrite !comparablerE => xBy_real yBz_real. *)
(* by have := rpredD xBy_real yBz_real; rewrite addrA addrNK. *)
(* Qed. *)

(* Ordered ring properties. *)

End porderZmodTypeTheory.

HB.mixin Record POrderedZmodule_hasTransComp R of GRing.Nmodule R
    & Order.isPOrder ring_display R := {
  comparabler_trans : transitive (comparable : rel R)
}.
#[short(type="comparableZmodType")]
HB.structure Definition ComparableZmodule :=
  {R of POrderedZmodule_hasTransComp R & POrderedZmodule R}.

Arguments comparabler_trans {_ _ _ _}.

Section ComparableZmoduleTheory.
Variable (R : comparableZmodType).
Implicit Types (x y : R).

Lemma ger_leVge x y : 0 <= x -> 0 <= y -> (x <= y) || (y <= x).
Proof.
by move=> /ge_comparable + /le_comparable => /comparabler_trans/[apply].
Qed.

Fact real_addr_closed : addr_closed (@real R).
Proof.
split=> [|x y Rx Ry]; first by rewrite realE lexx.
without loss{Rx} x_ge0: x y Ry / 0 <= x.
  case/orP: Rx => [? | x_le0]; first exact.
  by rewrite -rpredN opprD; apply; rewrite ?rpredN ?oppr_ge0.
case/orP: Ry => [y_ge0 | y_le0]; first by rewrite realE -nnegrE rpredD.
by rewrite realE -[y]opprK orbC -oppr_ge0 opprB !subr_ge0 ger_leVge ?oppr_ge0.
Qed.
#[export]
HB.instance Definition _ := GRing.isAddClosed.Build R Rreal_pred
  real_addr_closed.

End ComparableZmoduleTheory.

Variant extended (R : Type) := EFin of R | EPInf | ENInf.
Arguments EFin {R}.

Lemma EFin_inj T : injective (@EFin T).
Proof. by move=> a b; case. Qed.

Definition dual_extended := extended.

Definition dEFin : forall {R}, R -> dual_extended R := @EFin.

(* Notations in ereal_dual_scope should be kept *before* the
   corresponding notation in ereal_scope, otherwise when none of the
   scope is open (lte x y) would be displayed as (x < y)%dE, instead
   of (x < y)%E, for instance. *)
Notation "+oo" := (@EPInf _ : dual_extended _) : ereal_dual_scope.
Notation "+oo" := (@EPInf _) : ereal_scope.
Notation "-oo" := (@ENInf _ : dual_extended _) : ereal_dual_scope.
Notation "-oo" := (@ENInf _) : ereal_scope.
Notation "r %:dE" := (@EFin _ r%R : dual_extended _) : ereal_dual_scope.
Notation "r %:E" := (@EFin _ r%R : dual_extended _) : ereal_dual_scope.
Notation "r %:E" := (@EFin _ r%R).
Notation "'\bar' R" := (extended R) : type_scope.
Notation "'\bar' '^d' R" := (dual_extended R) : type_scope.
Notation "0" := (@GRing.zero (\bar^d _)) : ereal_dual_scope.
Notation "0" := (@GRing.zero (\bar _)) : ereal_scope.
Notation "1" := (1%R%:E : dual_extended _) : ereal_dual_scope.
Notation "1" := (1%R%:E) : ereal_scope.

Bind    Scope ereal_dual_scope with dual_extended.
Bind    Scope ereal_scope with extended.
Delimit Scope ereal_dual_scope with dE.
Delimit Scope ereal_scope with E.

Section ereal_theory.
Local Open Scope ereal_scope.

Definition er_map T T' (f : T -> T') (x : \bar T) : \bar T' :=
  match x with
  | r%:E => (f r)%:E
  | +oo => +oo
  | -oo => -oo
  end.

Lemma er_map_idfun T (x : \bar T) : er_map idfun x = x.
Proof. by case: x. Qed.

Definition fine {R : zmodType} x : R := if x is EFin v then v else 0.

Section EqEReal.
Variable (R : eqType).

Definition eq_ereal (x y : \bar R) :=
  match x, y with
    | x%:E, y%:E => x == y
    | +oo, +oo => true
    | -oo, -oo => true
    | _, _ => false
  end.

Lemma ereal_eqP : Equality.axiom eq_ereal.
Proof. by case=> [?||][?||]; apply: (iffP idP) => //= [/eqP|[]] ->. Qed.

HB.instance Definition _ := hasDecEq.Build (\bar R) ereal_eqP.

Lemma eqe (r1 r2 : R) : (r1%:E == r2%:E) = (r1 == r2). Proof. by []. Qed.

End EqEReal.

Section ERealChoice.
Variable (R : choiceType).

Definition code (x : \bar R) :=
  match x with
  | r%:E => GenTree.Node 0 [:: GenTree.Leaf r]
  | +oo => GenTree.Node 1 [::]
  | -oo => GenTree.Node 2 [::]
  end.

Definition decode (x : GenTree.tree R) : option (\bar R) :=
  match x with
  | GenTree.Node 0 [:: GenTree.Leaf r] => Some r%:E
  | GenTree.Node 1 [::] => Some +oo
  | GenTree.Node 2 [::] => Some -oo
  | _ => None
  end.

Lemma codeK : pcancel code decode. Proof. by case. Qed.

HB.instance Definition _ := Choice.copy (\bar R) (pcan_type codeK).

End ERealChoice.

Section ERealCount.
Variable (R : countType).

HB.instance Definition _ := PCanIsCountable (@codeK R).

End ERealCount.

Section ERealOrder.
Context {R : porderNmodType}.

Implicit Types x y : \bar R.

Definition le_ereal x1 x2 :=
  match x1, x2 with
  | -oo, r%:E | r%:E, +oo => r \is real
  | r1%:E, r2%:E => r1 <= r2
  | -oo, _    | _, +oo => true
  | +oo, _    | _, -oo => false
  end.

Definition lt_ereal x1 x2 :=
  match x1, x2 with
  | -oo, r%:E | r%:E, +oo => r \is real
  | r1%:E, r2%:E => r1 < r2
  | -oo, -oo  | +oo, +oo => false
  | +oo, _    | _  , -oo => false
  | -oo, _  => true
  end.

Lemma lt_def_ereal x y : lt_ereal x y = (y != x) && le_ereal x y.
Proof. by case: x y => [?||][?||] //=; rewrite lt_def eqe. Qed.

Lemma le_refl_ereal : reflexive le_ereal.
Proof. by case => /=. Qed.

Lemma le_anti_ereal : ssrbool.antisymmetric le_ereal.
Proof. by case=> [?||][?||]/=; rewrite ?andbF => // /le_anti ->. Qed.

End ERealOrder.

Section ERealComparable.
Context {R : comparableZmodType}.

Implicit Types x y : \bar R.

Lemma le_trans_ereal : ssrbool.transitive (@le_ereal R).
Proof.
case=> [?||][?||][?||] //=; rewrite -?comparabler0; first exact: le_trans.
  by move=> /le_comparable cmp /(comparabler_trans cmp).
by move=> cmp /ge_comparable /comparabler_trans; apply.
Qed.

Fact ereal_display : Order.disp_t. Proof. by []. Qed.

HB.instance Definition _ := Order.isPOrder.Build ereal_display (\bar R)
  lt_def_ereal le_refl_ereal le_anti_ereal le_trans_ereal.

Lemma leEereal x y : (x <= y)%O = le_ereal x y. Proof. by []. Qed.
Lemma ltEereal x y : (x < y)%O = lt_ereal x y. Proof. by []. Qed.

End ERealComparable.


Notation lee := (@Order.le ereal_display _) (only parsing).
Notation "@ 'lee' R" :=
  (@Order.le ereal_display R) (at level 10, R at level 8, only parsing).
Notation lte := (@Order.lt ereal_display _) (only parsing).
Notation "@ 'lte' R" :=
  (@Order.lt ereal_display R) (at level 10, R at level 8, only parsing).
Notation gee := (@Order.ge ereal_display _) (only parsing).
Notation "@ 'gee' R" :=
  (@Order.ge ereal_display R) (at level 10, R at level 8, only parsing).
Notation gte := (@Order.gt ereal_display _) (only parsing).
Notation "@ 'gte' R" :=
  (@Order.gt ereal_display R) (at level 10, R at level 8, only parsing).

Notation "x <= y" := (lee x y) (only printing) : ereal_dual_scope.
Notation "x <= y" := (lee x y) (only printing) : ereal_scope.
Notation "x < y"  := (lte x y) (only printing) : ereal_dual_scope.
Notation "x < y"  := (lte x y) (only printing) : ereal_scope.

Notation "x <= y <= z" := ((lee x y) && (lee y z)) (only printing) : ereal_dual_scope.
Notation "x <= y <= z" := ((lee x y) && (lee y z)) (only printing) : ereal_scope.
Notation "x < y <= z"  := ((lte x y) && (lee y z)) (only printing) : ereal_dual_scope.
Notation "x < y <= z"  := ((lte x y) && (lee y z)) (only printing) : ereal_scope.
Notation "x <= y < z"  := ((lee x y) && (lte y z)) (only printing) : ereal_dual_scope.
Notation "x <= y < z"  := ((lee x y) && (lte y z)) (only printing) : ereal_scope.
Notation "x < y < z"   := ((lte x y) && (lte y z)) (only printing) : ereal_dual_scope.
Notation "x < y < z"   := ((lte x y) && (lte y z)) (only printing) : ereal_scope.

Notation "x <= y" := (lee (x%dE : dual_extended _) (y%dE : dual_extended _)) : ereal_dual_scope.
Notation "x <= y" := (lee (x : extended _) (y : extended _)) : ereal_scope.
Notation "x < y"  := (lte (x%dE : dual_extended _) (y%dE : dual_extended _)) : ereal_dual_scope.
Notation "x < y"  := (lte (x : extended _) (y : extended _)) : ereal_scope.
Notation "x >= y" := (y <= x) (only parsing) : ereal_dual_scope.
Notation "x >= y" := (y <= x) (only parsing) : ereal_scope.
Notation "x > y"  := (y < x) (only parsing) : ereal_dual_scope.
Notation "x > y"  := (y < x) (only parsing) : ereal_scope.

Notation "x <= y <= z" := ((x <= y) && (y <= z)) : ereal_dual_scope.
Notation "x <= y <= z" := ((x <= y) && (y <= z)) : ereal_scope.
Notation "x < y <= z"  := ((x < y) && (y <= z)) : ereal_dual_scope.
Notation "x < y <= z"  := ((x < y) && (y <= z)) : ereal_scope.
Notation "x <= y < z"  := ((x <= y) && (y < z)) : ereal_dual_scope.
Notation "x <= y < z"  := ((x <= y) && (y < z)) : ereal_scope.
Notation "x < y < z"   := ((x < y) && (y < z)) : ereal_dual_scope.
Notation "x < y < z"   := ((x < y) && (y < z)) : ereal_scope.

Notation "x <= y :> T" := ((x : T) <= (y : T)) (only parsing) : ereal_scope.
Notation "x < y :> T" := ((x : T) < (y : T)) (only parsing) : ereal_scope.

Section ERealZsemimodule.
Context {R : nmodType}.
Implicit Types x y z : \bar R.

Definition adde x y :=
  match x, y with
  | x%:E , y%:E  => (x + y)%:E
  | -oo, _     => -oo
  | _    , -oo => -oo
  | +oo, _     => +oo
  | _    , +oo => +oo
  end.
Arguments adde : simpl never.

Definition dual_adde x y :=
  match x, y with
  | x%:E , y%:E  => (x + y)%R%:E
  | +oo, _     => +oo
  | _    , +oo => +oo
  | -oo, _     => -oo
  | _    , -oo => -oo
  end.
Arguments dual_adde : simpl never.

Lemma addeA_subproof : associative (S := \bar R) adde.
Proof. by case=> [x||] [y||] [z||] //; rewrite /adde /= addrA. Qed.

Lemma addeC_subproof : commutative (S := \bar R) adde.
Proof. by case=> [x||] [y||] //; rewrite /adde /= addrC. Qed.

Lemma add0e_subproof : left_id (0%:E : \bar R) adde.
Proof. by case=> // r; rewrite /adde /= add0r. Qed.

HB.instance Definition _ := GRing.isNmodule.Build (\bar R)
  addeA_subproof addeC_subproof add0e_subproof.

Lemma daddeA_subproof : associative (S := \bar^d R) dual_adde.
Proof. by case=> [x||] [y||] [z||] //; rewrite /dual_adde /= addrA. Qed.

Lemma daddeC_subproof : commutative (S := \bar^d R) dual_adde.
Proof. by case=> [x||] [y||] //; rewrite /dual_adde /= addrC. Qed.

Lemma dadd0e_subproof : left_id (0%:dE%dE : \bar^d R) dual_adde.
Proof. by case=> // r; rewrite /dual_adde /= add0r. Qed.

HB.instance Definition _ := Choice.on (\bar^d R).
HB.instance Definition _ := GRing.isNmodule.Build (\bar^d R)
  daddeA_subproof daddeC_subproof dadd0e_subproof.

Definition enatmul x n : \bar R := iterop n +%R x 0.

Definition ednatmul (x : \bar^d R) n : \bar^d R := iterop n +%R x 0.

End ERealZsemimodule.
Arguments adde : simpl never.
Arguments dual_adde : simpl never.

Section ERealOrder_comparableType.
Context {R : comparableZmodType}.
Implicit Types (x y : \bar R) (r : R).

Lemma lee_fin (r s : R) : (r%:E <= s%:E) = (r <= s)%R. Proof. by []. Qed.

Lemma lte_fin (r s : R) : (r%:E < s%:E) = (r < s)%R. Proof. by []. Qed.

Lemma leeNy_eq x : (x <= -oo) = (x == -oo). Proof. by case: x. Qed.

Lemma leye_eq x : (+oo <= x) = (x == +oo). Proof. by case: x. Qed.

Lemma lt0y : (0 : \bar R) < +oo. Proof. exact: real0. Qed.

Lemma ltNy0 : -oo < (0 : \bar R). Proof. exact: real0. Qed.

Lemma le0y : (0 : \bar R) <= +oo. Proof. exact: real0. Qed.

Lemma leNy0 : -oo <= (0 : \bar R). Proof. exact: real0. Qed.

Lemma cmp0y : ((0 : \bar R) >=< +oo%E)%O.
Proof. by rewrite /Order.comparable le0y. Qed.

Lemma cmp0Ny : ((0 : \bar R) >=< -oo%E)%O.
Proof. by rewrite /Order.comparable leNy0 orbT. Qed.

Lemma lt0e x : (0 < x) = (x != 0) && (0 <= x).
Proof. by case: x => [r| |]//; rewrite lte_fin lee_fin lt0r. Qed.

Lemma ereal_comparable x y : (0%E >=< x)%O -> (0%E >=< y)%O -> (x >=< y)%O.
Proof.
move: x y => [x||] [y||] //; rewrite /Order.comparable !lee_fin -!realE.
- exact: real_comparable.
- by rewrite /lee/= => ->.
- by rewrite /lee/= => _ ->.
Qed.

Lemma real_ltry r : r%:E < +oo = (r \is Num.real). Proof. by []. Qed.
Lemma real_ltNyr r : -oo < r%:E = (r \is Num.real). Proof. by []. Qed.

Lemma real_leey x : (x <= +oo) = (fine x \is Num.real).
Proof. by case: x => //=; rewrite real0. Qed.

Lemma real_leNye x : (-oo <= x) = (fine x \is Num.real).
Proof. by case: x => //=; rewrite real0. Qed.

Lemma minye : left_id (+oo : \bar R) Order.min.
Proof. by case. Qed.

Lemma real_miney (x : \bar R) : (0 >=< x)%O -> Order.min x +oo = x.
Proof.
by case: x => [x |//|//] rx; rewrite minEle real_leey [_ \in Num.real]rx.
Qed.

Lemma real_minNye (x : \bar R) : (0 >=< x)%O -> Order.min -oo%E x = -oo%E.
Proof.
by case: x => [x |//|//] rx; rewrite minEle real_leNye [_ \in Num.real]rx.
Qed.

Lemma mineNy : right_zero (-oo : \bar R) Order.min.
Proof. by case=> [x |//|//]; rewrite minElt. Qed.

Lemma maxye : left_zero (+oo : \bar R) Order.max.
Proof. by case. Qed.

Lemma real_maxey (x : \bar R) : (0 >=< x)%O -> Order.max x +oo = +oo.
Proof.
by case: x => [x |//|//] rx; rewrite maxEle real_leey [_ \in Num.real]rx.
Qed.

Lemma real_maxNye (x : \bar R) : (0 >=< x)%O -> Order.max -oo%E x = x.
Proof.
by case: x => [x |//|//] rx; rewrite maxEle real_leNye [_ \in Num.real]rx.
Qed.

Lemma maxeNy : right_id (-oo : \bar R) Order.max.
Proof. by case=> [x |//|//]; rewrite maxElt. Qed.

Lemma gee0P x : 0 <= x <-> x = +oo \/ exists2 r, (r >= 0)%R & x = r%:E.
Proof.
split=> [|[->|[r r0 ->//]]]; last by rewrite real_leey/=.
by case: x => [r r0 | _ |//]; [right; exists r|left].
Qed.

Lemma fine0 : fine 0 = 0%R :> R. Proof. by []. Qed.
Lemma fine1 : fine 1 = 1%R :> R. Proof. by []. Qed.

End ERealOrder_numDomainType.





(*STT nyelve implicit változókkal*)

Require Import List.
Require Import Arith.

(*Típusok nyelve*)

Inductive Typ : Set :=
  | Iota : Typ
  | Arrow : Typ -> Typ -> Typ.

Notation "'ι'" := Iota (at level 20).
Infix "→" := Arrow (at level 20, right associativity).

Definition Cntxt := list Typ.

Definition CntxExt (A : Typ) Γ  := A :: Γ.

Infix "▷" := CntxExt (at level 20, right associativity).

(* Külön vannak kifejezések (terminusok, termek)*)

Inductive Trm : Set :=
  | ind : nat -> Trm
  | lam : Typ -> Trm -> Trm
  | app : Trm -> Trm -> Trm.

Notation "x '$' y" := (app x y) (at level 20).

(* Mivel itt bizonyításokról, levezetsekről van szó (és ez szemléletesebb is), ezért an n-edik 
változót 

ind n 

jelöli. Ez viszont nem egy abszolút sorszám, hanem egy relatív.
A Γ = A_0::A_1::A_2::...::nil kontextusban ind 0 pl. az lista első elemére, 
az A_0 típusúváltozóra mutat. Ha Γ bővül egy elemmel, 
a sorrendek eltolódnak 1-gyel. 

lam-nál meg kell jelölni, hogy milyen típusú termet absztrahál, azaz lam egy Typ -> Trm -> Trm típusú lesz.

app problémamentes
*)

Inductive Tyty : Cntxt -> Trm -> Typ -> Prop :=
  | ND_ind0 : forall Γ A, Tyty (A :: Γ) (ind 0) A
  | ND_indS :
      forall Γ A B i,
      Tyty Γ (ind i) A -> Tyty (B :: Γ) (ind (S i)) A
  | ND_lam :
      forall Γ t A B,
      Tyty (A :: Γ) t B -> Tyty Γ (lam A t) (Arrow A B)
  | ND_app :
      forall Γ t s A B,
      Tyty Γ t (Arrow A B) -> Tyty Γ s A -> Tyty Γ (app t s) B.

Notation "G '⊢' t '[:]' A" := (Tyty G t A) (at level 70, no associativity) : type_scope.

Notation "'⊢' t '[:]' A" := (Tyty nil t A) (at level 70, no associativity) : type_scope.


Fixpoint lift_aux (n : nat) (t : Trm) (k : nat) {struct t} : Trm :=
   match t with
     | ind i => match (le_gt_dec k i) with
                  | left _ => (* k <= i *) ind (i + n)
                  | right _ => (* k > i *) ind i
                end
     | app M N => app (lift_aux n M k) (lift_aux n N k)
     | lam A M => lam A (lift_aux n M (S k))
   end.

(* A következő függvény az összes szabad változót lifteli n-nel *)

Definition lift P n := lift_aux n P 0.


Eval compute in lift (lam Iota (app (ind 0) (ind 1))) 1. 

Eval compute in lift (lam Iota (lam Iota (app (ind 0) (ind 1)))) 2.

Eval compute in lift (app (ind 0) (lam Iota (app (ind 0) (ind 1)))) 2.

(* Az alábbi függvény egy termsorozat minden elemét lifteli (azaz a benne
 szereplő szabad változók indexét emeli eggyel.) *)

Definition lift_seq (s : nat -> Trm) (k : nat) : Trm  :=
  match k with 
     | 0 => lift (s 0) 1
     | S m => lift (s (S m)) 1
  end.
  
(* Eltolja a termsorozatot 1-gyel és az első helyre berakja a ind 0-t. *)

Definition shift_seq (s : nat -> Trm) (k : nat) : Trm  :=
  match k with 
     | 0 => ind 0
     | S m => (s m)
  end.

(* A t term n-edik szabad változója helyére az s sorozat n. elemét helyettesíti *)

Fixpoint subst_aux (t : Trm) (n : nat) (s : nat -> Trm) {struct t} : Trm :=
  match t with
    | ind i => match (Nat.eq_dec n i)  with 
                 | left _ => s n
                 | right _ => ind i
               end
    | app M N => app (subst_aux M n s) (subst_aux N n s)
    | lam A M => lam A (subst_aux M (S n) (shift_seq ( lift_seq s)))
  end.
  
(* Ugyenez 0-val. *)
  
Definition subst P s := subst_aux P 0 s.

(* Ugyanez, azzal a sorozattal, amikor a 0. elem Q, a többi irreleváns *)

Definition subs P Q := subst_aux P 0 (fun k : nat => 
match k with | 0 => Q | S _ => ind 0 end).

Definition s1 (n : nat) : Trm :=
  match n with
    | 0 => app (ind 0) (ind 0)
    | S 0 => app (app (ind 0) (ind 0)) (ind 0) (* (ind 1 $ ind 1) $ ind 1 *)
    | S (S 0) => app (app (ind 0) (ind 0)) (app (ind 0) (ind 0))
    | S (S (S _)) => ind 0
  end.
  

Eval compute in subst (lam Iota (app (ind 2) (ind 1))) s1.

(*
      1  1
   2   *
     *
     λ
λ.2(11)
     *)

Eval compute in subs (lam Iota (app (ind 2) (ind 1))) (app (ind 0) (ind 0)).

Eval compute in subst_aux (lam Iota (app (ind 2) (ind 1))) 1 s1.


Eval compute in subst_aux (lam Iota (lam Iota (app (ind 0) (ind 2)))) 0 s1.

Eval compute in subs (lam Iota (lam Iota (app (ind 0) (ind 3)))) (app (ind 1) (ind 1)).

Eval compute in subs (lam Iota (lam Iota (app (ind 0) (ind 4)))) 
(lam Iota ( lam Iota (((app (ind 2) (ind 2)))))).

Inductive DefEqu : Cntxt -> Trm -> Trm -> Typ -> Prop :=

  (*Ekvivalencia*) 
  | DefEqu_refl : forall Γ t A, Tyty Γ t A -> DefEqu Γ t t A
  | DefEqu_simm : forall Γ t s A, DefEqu Γ t s A -> DefEqu Γ s t A
  | DefEqu_tran : forall Γ t s r A, DefEqu Γ t s A -> DefEqu Γ s r A -> DefEqu Γ t r A

  (*Kongruencia*)
  | DefEqu_app : forall Γ t1 t2 s1 s2 A B, DefEqu Γ t1 t2 (Arrow A B) -> DefEqu Γ s1 s2 A -> DefEqu Γ (app t1 s1) (app t2 s2) B
  | DefEqu_lam : forall Γ t s A B, DefEqu Γ s t B -> DefEqu Γ (lam A t) (lam A s) (Arrow A B)

  (*Komputációs szabályok*)
  | DefEqu_beta : forall Γ t s A B, Tyty (A :: Γ) t B ->  Tyty Γ s B -> DefEqu Γ (app (lam A t) s) (subs t s) B
  | DefEqu_eta : forall Γ f A B, Tyty  Γ f (A → B) -> DefEqu Γ (lam A (app f (ind 0)) ) f B.

(*

Parameter r : Trm.

Eval compute in (subst_aux (ind 1) 0 ((fun k : nat => 
match k with | 0 => r | S _ => ind 0 end))).

*)

(*seq_head (P : Trm) az a termsorozat, aminek az első eleme P, a többi az irreleváns ind 0.*)

Definition seq_head (P : Trm) := ((fun k : nat => 
match k with | 0 => P | S _ => ind 0 end)).

(*subs_lift_plus_one (t r : Trm) az a helyettesítés, amit úgy
 kapunk, hogy r-et a t term 1-gyel indexelt, tehát második
 szabad változójába helyettesítünk. r de Bruijn számai persze
 liftelődnek eggyel, mert . Erre a függvényre azért van
 szükség, mert a lambdán áthaladva a kontextus bővül eggyel és
 így nem az első, hanem a második szabad változóba kell
 behelyettesíteni.*)

Definition subs_lift_plus_one (t r : Trm) := subst_aux t (S 0) (shift_seq (lift_seq (seq_head r))).

Definition subs_lift_plus_one' (t r : Trm) := subst_aux t (S 0) ( (lift_seq (seq_head r))).

Theorem Sub_prop_1 : forall r, (subs (ind 0) r) = r.
Proof.
intros.
compute.
auto.
Defined.

Theorem Sub_prop_2 : forall r n, (subs (ind (S n)) r) = ind (S n).
Proof.
intros.
compute.
auto.
Defined.

Theorem Sub_prop_3 : forall r t s, (subs (app t s) r) = (app (subs t r) (subs s r)).
Proof.
intros.
induction t.
all: auto.
Defined.

Theorem Sub_prop_4 : forall r t A, subs (lam A t) r = lam A (subs_lift_plus_one t r).
Proof.
intros.
induction t.
all: auto.
Defined.














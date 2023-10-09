Require Import List.

Inductive Typ : Set :=
  | Top : Typ
  | Imp : Typ -> Typ -> Typ
  | Cnj : Typ -> Typ -> Typ.

Inductive Trm : Set :=
  | top : Trm
  | hyp : nat -> Trm
  | lam : Typ -> Trm -> Trm
  | app : Trm -> Trm -> Trm
  | cnj : Trm -> Trm -> Trm
  | proj_1 : Trm -> Trm
  | proj_2 : Trm -> Trm.

Definition  Cntxt := list Typ.

Inductive Tyty : Cntxt -> Trm -> Typ -> Prop :=
  | ND_top_intro : forall G, Tyty G top Top
  | ND_hypO : forall G A, Tyty (A :: G) (hyp 0) A
  | ND_hypS :
      forall G A B I,
      Tyty G (hyp I) A -> Tyty (B :: G) (hyp (S I)) A
  | ND_lam :
      forall G t A B,
      Tyty (A :: G) t B -> Tyty G (lam A t) (Imp A B)
  | ND_app :
      forall G t s A B,
      Tyty G t (Imp A B) -> Tyty G s A -> Tyty G (app t s) B
  | ND_cnj :
      forall G t s A B,
      Tyty G t A -> Tyty G s B -> Tyty G (cnj t s) (Cnj A B)
  | ND_proj_1 :
      forall G t A B,
      Tyty G t (Cnj A B) -> Tyty G (proj_1 t) A
  | ND_proj_2 :
      forall G t A B,
      Tyty G t (Cnj A B) -> Tyty G (proj_2 t) B.

Notation "G '⊢' t '[:]' A" := (Tyty G t A) (at level 70, no associativity) : type_scope.

Notation "'⊢' t '[:]' A" := (Tyty nil t A) (at level 70, no associativity) : type_scope.

Class Category := cat_mk {
  Obj : Type;
  uHom := Type : Type;
  Hom : Obj -> Obj -> uHom; (* morphism constructor *)
  Id : forall x, Hom x x; (* Id x := Hom x x *)
  Dom {x y} (f: Hom x y) := x; (* domain operator *)
  CoDom {x y} (f: Hom x y) := y; (* codomain operator *)
  Compose : forall {x y z}, (Hom y z)->(Hom x y)->(Hom x z); (* morhism compose operator *)
  EqMor : forall {x y}, (Hom x y) -> (Hom x y) -> Prop;


  (* equivalence relation properties *)
  Eq_ref : forall {x y} (f : Hom x y), EqMor f f;
  Eq_trans : forall {x y} (f g h : Hom x y), EqMor f g -> EqMor g h 
         -> EqMor f h;
  Eq_sim : forall {x y} (f g : Hom x y), EqMor f g -> EqMor g f;


  (* category laws: associativity of composition, composition of identities, composition preserves identity from both sides *)
  assoc : forall x y z w (f : (Hom z w)) (g:(Hom y z)) (h:(Hom x y)),
        EqMor (Compose f (Compose g h) ) (Compose (Compose f g) h);

  id_1 : forall x y (f : (Hom x y)), EqMor (Compose f (Id x)) f ;

  id_2 : forall x y (f : (Hom x y)), EqMor (Compose (Id y) f) f ;

  eq: forall {x y z} (f g: Hom y z) (h i : Hom x y), EqMor f g /\ EqMor h i ->
        EqMor (Compose f h) (Compose g i);
}.
Print EqMor.

Notation "x → y" := (Hom x y) (at level 90, right associativity) :
type_scope.

Notation "g ∘ f" := (Compose g f) (at level 40, left associativity) :
type_scope.

Notation "x ≡ y" := (EqMor x y) (at level 40, left associativity) :
type_scope. 

Require Import Coq.Setoids.Setoid.
Add Parametric Relation {C : Category} {A B: Obj} : (Hom A B) (EqMor)
  reflexivity proved by (Eq_ref)
  symmetry proved by (Eq_sim)
  transitivity proved by (Eq_trans)
  as eq_set_rel.

Add Parametric Morphism {C: Category} {a b c: @Obj C} : (@Compose C a b c)
  with signature (EqMor) ==> (EqMor) ==> (EqMor) as compose_keeps_equality.
Proof.
intros.
apply eq.
split.
exact H.
exact H0.
Qed.



Lemma eq_1 : forall {C: Category} {x y z} (f: Hom y z) (g h : Hom x y), EqMor g h ->
EqMor (Compose f g) (Compose f h).
Proof.
intros.
apply eq.
split.
reflexivity.
exact H.
Qed.

Lemma eq_2 : forall {C: Category} {x y z} (f: Hom x y) (g h : Hom y z), EqMor g h ->
        EqMor (Compose g f) (Compose h f).
Proof.
intros.
apply eq.
split.
exact H.
reflexivity.
Qed.



Context {CC : Category}.

Class CartClosed := {

(* terminal *)

  Top_obj : Obj;

  Top_mor : forall {x}, x → Top_obj;
 
  unique_top : forall {x} (f : x → Top_obj), f ≡ Top_mor;

(* szorzat *)

  Prod_obj : Obj -> Obj -> Obj;

  Prod_mor : forall {x y z} (f:x → y) (g:x → z), x → Prod_obj y z;

  First {x y} : (Prod_obj x y) → x;
  Second {x y} : (Prod_obj x y) → y;

  prod_ax : forall {x y z} (f : x → y) (g : x → z), 
    (First ∘ (Prod_mor f g) ≡ f) /\ (Second ∘ (Prod_mor f g) ≡ g);
  
  unique_prod : forall {x y z} (f : x → y) (g : x → z) (h : x → Prod_obj y
z),
    ((First ∘ h) ≡ f) /\ ((Second ∘ h) ≡ g) -> h ≡ Prod_mor f g;

(* exponenciális *)

  Exp_obj : Obj -> Obj -> Obj;

  Exp_app : forall {y z}, (Prod_obj (Exp_obj z y) y) → z;

  Lam : forall {x y z} (g : (Prod_obj x y) → z), x → (Exp_obj z y);

  exp_ax : forall {x y z} (g : (Prod_obj x y) → z), 
    Exp_app ∘ (Prod_mor (Compose (Lam g) First) (Compose (Id y) Second)) ≡ g;
  
  unique_exp : forall {x y z} (h : x → Exp_obj z y),
    Lam (Exp_app ∘ (Prod_mor (Compose h First) (Compose (Id y) Second))) ≡ h

}.


Notation "⊤" := (Top_obj) (at level 40, no
associativity) : type_scope.

Notation "'〈' x ',' y '〉'" := (Prod_mor x y) (at level 40, no
associativity) : type_scope.

Notation "x × y" := (Prod_obj x y) (at level 40, left associativity) :
type_scope. 

Notation "x 'e↑' y" := (Exp_obj x y) (at level 80, right associativity) :
type_scope. 

Notation "f '⊠' g" := (Prod_mor (Compose f First) (Compose g Second)) (at level 40, left associativity) :
type_scope.

Context {CCC : CartClosed}.

Structure VAL : Type := makeVAL 
  { V :> Typ -> Obj;
    VAL_top : V Top = Top_obj;
    VAL_imp : forall {A B}, V (Imp A B) = Exp_obj (V B) (V A);
    VAL_cnj : forall {A B}, V (Cnj A B) = Prod_obj (V A) (V B);
  }.


Fixpoint VAL_Cntxt (v : VAL) (G : list Typ) := 
  match G with 
    | nil => Top_obj
    | A :: G' => Prod_obj (VAL_Cntxt v G') (v A)  (* hogy kompatibilis legyen az exp-beli sorrenddel *)
  end.





Notation "'[[' G ']]_C' v" := (VAL_Cntxt v G) (at level 40, no associativity) :
type_scope.

Theorem soundness : forall v G A, (exists t, G ⊢ t [:] A) -> 
                           inhabited( Hom ([[ G ]]_C v) (v A)).
Proof.
  intros v G A H.
  elim H.
  intros. 
  induction H0.
  - apply inhabits.
  rewrite VAL_top.
  exact (Top_mor).
  - apply inhabits; simpl.
  exact (@Second (CCC) ([[ G ]]_C v) (v A) ).
  - assert (H1 : (exists t : Trm, G ⊢ t [:] A)). 
    { exists (hyp I). exact H0. } 
  apply IHTyty in H1.
  induction H1; apply inhabits.
  exact (Compose X (@First CCC ([[ G ]]_C v) (v B))).
  - assert (Inh : inhabited ([[A :: G ]]_C v → v B)). 
    { apply IHTyty; exists t; exact H0. } clear IHTyty H0 H t. 
  rewrite VAL_imp; simpl in Inh. 
  induction Inh; apply inhabits. 
  exact (@Lam CCC ([[G ]]_C v) (v A) (v B) X). 
  - assert (Inh1 : inhabited ([[G ]]_C v → v (Imp A B))).
    { apply IHTyty1; exists t; exact H0_. } clear IHTyty1 H0_.
  assert (Inh2 : inhabited ([[G ]]_C v → v A)).
  { apply IHTyty2; exists s; exact H0_0. } clear IHTyty2 H0_0 H t s.
  rewrite VAL_imp in Inh1.
  induction Inh1, Inh2; apply inhabits.
  assert (Y : ([[G ]]_C v → (v B e↑ v A) × v A )).
  { exact (@Prod_mor CCC ([[G ]]_C v) ((v B e↑ v A)) (v A) X X0 ). }
  assert (Z : (v B e↑ v A) × v A → v B ).
  { exact (@Exp_app CCC (v A) (v B)). }
  exact (Compose Z Y).
  - assert (Inh1 : inhabited ([[G ]]_C v → v A)).
    { apply IHTyty1; exists t; exact H0_. } clear IHTyty1 H0_.
  assert (Inh2 : inhabited ([[G ]]_C v → v B)).
  { apply IHTyty2; exists s; exact H0_0. } clear IHTyty2 H0_0 H t s.
  induction Inh1, Inh2; apply inhabits.
  rewrite VAL_cnj.
  exact (@Prod_mor CCC ([[G ]]_C v) (v A) (v B) X X0).
  - assert (Inh : inhabited ([[G ]]_C v → v (Cnj A B))).
    { apply IHTyty; exists t; exact H0. } clear IHTyty H0 H t.
  induction Inh; apply inhabits.
  rewrite VAL_cnj in X.
  assert (Y : v A × v B → v A).
  { exact (@First CCC (v A) (v B)). }
  exact (Compose Y X).
  - assert (Inh : inhabited ([[G ]]_C v → v (Cnj A B))).
    { apply IHTyty; exists t; exact H0. } clear IHTyty H0 H t.
  induction Inh; apply inhabits.
  rewrite VAL_cnj in X.
  assert (Y : v A × v B → v B).
  { exact (@Second CCC (v A) (v B)). }
  exact (Compose Y X).
Qed.

Fail Inductive tm :=
| app : tm -> tm -> tm
| abs : (tm -> tm) -> tm.

Module m1.
Inductive tm (V:Type) :=
| app : tm V -> tm V -> tm V
| abs : (V -> tm V) -> tm V.
End m1.

Module m2.
  
Inductive ty (V:Type) :=
| arr : ty V -> ty V -> ty V
| all : (V -> ty V) -> ty V.

Inductive tm (V W:Type) :=
| app : tm V W -> tm V W -> tm V W
| tapp : tm V W -> ty V -> tm V W
| vt : vl V W -> tm V W
with vl (V W:Type) :=
| lam : ty V -> (W -> tm V W) -> vl V W
| tlam : (V -> tm V W) -> vl V W.
End m2.

From MetaCoq.Template Require Import All.
Require Import String List.
Import ListNotations MonadNotation.
Open Scope string.

Module m3.
  Variables V W : Type.
  
  Inductive ty :=
  | arr : ty -> ty -> ty
  | all : (V -> ty) -> ty.

  Inductive tm :=
  | app : tm -> tm -> tm 
  | tapp : tm -> ty -> tm 
  | vt : vl -> tm 
  with vl :=
  | lam : ty -> (W -> tm) -> vl
  | tlam : (V -> tm) -> vl.

  Definition Autosubst_map := [(ty, V); (vl, W)].
  Definition Autosubst_sorts := [ty; tm].
End m3.


Definition printInductive (q : qualid): TemplateMonad unit :=
  kn <- tmLocate1 q ;;
  match kn with
  | IndRef ind => (tmQuoteInductive ind.(inductive_mind)) >>= tmPrint
  | _ => tmFail ("not an inductive")
  end.

MetaCoq Run (printInductive "m2.tm").

MetaCoq Run (printInductive "m3.tm").

Module m4.
  (* How would a language with dependent types look? *)
  Parameter V W : Type.
  
  (* and here we see we need more information from the user about which variable corresponds to which sort since there is no difference between all and dep *)
  Inductive ty :=
  | arr : ty -> ty -> ty
  | all : (V -> ty) -> ty
  | dep : (W -> ty) -> ty.

  Inductive tm :=
  | app : tm -> tm -> tm 
  | tapp : tm -> ty -> tm 
  | vt : vl -> tm 
  with vl :=
  | lam : ty -> (W -> tm) -> vl 
  | tlam : (V -> tm) -> vl.

  Parameter X : Type.
  Definition variadic (p: nat) (t:Type) := t.
  Notation " < p , t > " := (variadic p t) (t at next level).
  Inductive tm' :=
  | app' : tm' -> list tm' -> tm'
  | lam' : forall p:nat, ty -> (<p, X> -> tm') -> tm'
  | lam'' (p: nat): ty -> (<p, X> -> tm') -> tm'.
                                          

  (* if the user specifies this kind of list it should work.
   We can even check that it's the same variables that appear bound in the constructors. *)
  Definition Autosubst_map :=
    [ (V, ty); (W, vl) ].
  Definition Autosubst_sorts := [ ty; tm ].
End m4.

Module m5.
  (* How would a language with dependent types look? *)
  Parameter V W : Type.
  
  (* and here we see we need more information from the user about which variable corresponds to which sort since there is no difference between all and dep *)
  Inductive ty :=
  | arr : ty -> ty -> ty
  | all : (V -> ty) -> ty
  with ty2 :=
  | bla : ty2.

  Inductive tm :=
  | app : tm -> tm -> tm 
  | tapp : tm -> ty -> tm 
  | vt : vl -> tm 
  with vl :=
  | lam : ty -> (W -> tm) -> vl 
  | tlam : (V -> tm) -> vl.


  (* if the user specifies this kind of list it should work.
   We can even check that it's the same variables that appear bound in the constructors. *)
  Definition Autosubst_map :=
    [ (V, ty); (W, vl) ].
  Definition Autosubst_sorts := [ ty; tm ].
End m5.

Require Import hsig.
MetaCoq Test Quote m5.ty.

Fixpoint chain (actions: list (TemplateMonad unit)) : TemplateMonad unit :=
  match actions with
  | [] => tmReturn tt
  | a :: actions =>
    a;;
    chain actions
  end.

Fixpoint alternate {A:Type} (ms: list (TemplateMonad A)) : TemplateMonad (list A) :=
  match ms with
  | [] => tmReturn []
  | m :: ms =>
    a <- m;;
    as_ <- alternate ms;;
    tmReturn (a :: as_)
  end.

Definition tm_a_map {A B: Type} (f: A -> TemplateMonad B) (ms: list A) : TemplateMonad (list B) :=
  alternate (map f ms).

Definition get_inductives (slist: list Type) : TemplateMonad (list term) :=
  inductives <- tm_a_map (fun ind =>
                            indq <- tmQuote ind;;
                            tmReturn indq) slist;;
  tmReturn inductives.

MetaCoq Run (get_inductives m3.Autosubst_sorts >>= tmPrint).

Definition get_inductive_kernames (slist: list Type) : TemplateMonad (list kername) :=
  refs <- get_inductives slist;;
  kernames <- tm_a_map (fun t: term =>
                        match t return TemplateMonad kername with
                        | tInd {| inductive_mind := inductive_mind; inductive_ind := _ |} _ => tmReturn inductive_mind
                        | _ => tmFail ""
                        end) refs;;
  tmReturn kernames.

     
Definition flat_map {A B : Type} (f: A -> list B) : list A -> list B
  := fix flat_map (l : list A) : list B := match l with
                                             | [] => []
                                             | x :: t => (f x ++ flat_map t)%list
                                             end.

Definition get_inductive_bodies (slist: list Type) : TemplateMonad _ :=
  kernames <- get_inductive_kernames slist;;
  mutual_bodies <- tm_a_map tmQuoteInductive kernames;;
  let bodies := flat_map ind_bodies mutual_bodies in
  ebodies <- tmEval lazy bodies;;
  tmReturn ebodies.

(* working with inductive entries might be easier. TODO check what Marcel did *)
(*
Definition get_inductive_entries (slist: list Type) : TemplateMonad (list one_inductive_entry) :=
  kernames <- get_inductive_kernames slist;;
  mutual_bodies <- tm_a_map tmQuoteInductive kernames;;
  let mutual_entries := map mind_body_to_entry mutual_bodies in
  let entries := flat_map mind_entry_inds mutual_entries in
  eentries <- tmEval lazy entries;;
  tmReturn eentries.
 *)

MetaCoq Run (get_inductive_bodies m3.Autosubst_sorts >>= tmPrint).

(* MetaCoq Run (get_inductive_bodies [m4.tm'] >>= tmPrint). *)

Fixpoint translate_positions (sname: tId) (t: term) : list Position :=
  match t with
  (* base case since all constructors must end with a reference to their inductive type *)
  | tRel _ => []
  | tProd {| binder_name := nAnon; binder_relevance := _ |} t1 t2 =>
    let pos := match t1 with
               | tRel _ => {| pos_binders := []; pos_head := Atom sname |}
               | _ => bla
               end in
    pos :: (translate_positions sname t2)
  (* should really use error monad here *)
  | _ => []
  end.

Definition translate_constructor (ctor: (string * term) * nat) : Constructor :=
  let '((cname, ctype), _) := ctor in
  let positions := translate_positions ctype in
  {| con_parameters := []; con_name := cname; con_positions := positions |}.
                                                                 
Definition translate_inductive_body (b: one_inductive_body) : (tId * list Constructor) :=
  let ctors := map translate_constructor (ind_ctors b) in
  (ind_name b, ctors).
  
  
Definition translate_inductives (slist: list Type) (vlist: list (Type * Type)) : spec.
Admitted.

(* Definition quote_inductive (indref: term) := *)
(*   match indref with *)
(*   | tInd {| inductive_mind := } *)


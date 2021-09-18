(** * Module to parse HOAS using custom entry notations *)
From ASUB Require Import Language AssocList ErrorM SigAnalyzer Nterm Utils IdentParsing.
Require Import List String.
Import ListNotations.
#[ local ]
 Open Scope string.


Module Syntax.

  Record SyntaxSort := { hsort_name : string; hsort_var_name : option string }.
  Inductive SyntaxBinder :=
  | HSingle : tId -> SyntaxBinder
  | HBinderList : string -> tId -> SyntaxBinder.

  Inductive SyntaxArgHead := HAtom : tId -> SyntaxArgHead
                         | HFunApp : fId -> list nterm -> list SyntaxArgHead -> SyntaxArgHead.
  Record SyntaxPosition := { hpos_binders : list SyntaxBinder;
                           hpos_head : SyntaxArgHead }.
  Record SyntaxParameter := { hpar_name : string; hpar_sort : string }.
  Record SyntaxConstructor := { hcon_parameters : list SyntaxParameter;
                              hcon_name : string;
                              hcon_positions : list SyntaxPosition }.
  Record autosubstLanguage := { al_sorts : list SyntaxSort; al_ctors : list SyntaxConstructor }.

End Syntax.


Module SyntaxNotation.
  Export Syntax.

  Declare Custom Entry syntax_sorts.
  Declare Custom Entry syntax_ctors.
  Declare Custom Entry syntax_params.
  Declare Custom Entry syntax_positions.
  Declare Custom Entry syntax_head.
  Declare Custom Entry syntax_binder.
  Declare Custom Entry syntax_ident.
  Declare Custom Entry syntax_sexpr.

  Notation "a" := (ident_to_string a)
                    (in custom syntax_ident at level 0, a ident, only parsing).
  
  (** * Entry point for parsing sorts of our custom syntax *)
  Notation "'<{' e '}>'" := (e)
                              (e custom syntax_sorts).

  (** * Declaring a single sort *)
  Notation " x : 'Type' " :=
    {| hsort_name := x; hsort_var_name := None |}
      (in custom syntax_sorts at level 60, x custom syntax_ident, only parsing).
  Notation " x ( varname ) : 'Type' " :=
    {| hsort_name := x; hsort_var_name := Some varname |}
      (in custom syntax_sorts at level 60, x custom syntax_ident, varname custom syntax_ident, only parsing).
  Notation " x : 'Functor' " := (x)
                                  (in custom syntax_sorts at level 60, x custom syntax_ident, only parsing).
  (** * Declaring multiple sorts *)
  Notation " x ; .. ; z " := (cons x .. (cons z nil) .. )
                               (in custom syntax_sorts at level 70, x at level 60, z at level 60, only parsing).

  (*** Ctors *)
  (** * Entrypoint for parsing constructors of our custom syntax *)
  Notation "'{{' e '}}'" := (e) (e custom syntax_ctors).

  (** * Declaring multiple constructors *)
  Notation " y ; .. ; z " :=
    (@cons SyntaxConstructor y .. (@cons SyntaxConstructor z nil) .. )
      (in custom syntax_ctors at level 100, y at level 70, z at level 70, no associativity, only parsing).
  (** * Declaring a constructor with parameters *)
  Notation " x ( p0 , .. , p1 ) : y -> .. -> z " :=
    {| hcon_parameters := (@cons SyntaxParameter p0 .. (@cons SyntaxParameter p1 nil) .. );
        hcon_name:=x;
        hcon_positions := (@cons SyntaxPosition z .. (@cons SyntaxPosition y nil) ..) |}
      (in custom syntax_ctors at level 70, x custom syntax_ident, p0 custom syntax_params at level 2, p1 custom syntax_params at level 2, y custom syntax_positions at level 2, z custom syntax_positions at level 2, no associativity, only parsing).
  (** * Declaring a consturctor without parameters *)
  Notation " x : y -> .. -> z " :=
    {| hcon_parameters := nil;
        hcon_name:=x;
        hcon_positions := (@cons SyntaxPosition z .. (@cons SyntaxPosition y nil) ..) |}
      (in custom syntax_ctors at level 70, x custom syntax_ident, y custom syntax_positions at level 2, z custom syntax_positions at level 2, no associativity, only parsing).
  
  (*** Parameters *)
  (** * Declaring a  single parameter *)
  Notation " p : t  " := {| hpar_name:=p; hpar_sort:=t|}
                           (in custom syntax_params at level 2, p custom syntax_ident, t custom syntax_ident, only parsing).

  (*** Positions *)
  Notation " ( x ) " := (x)
                          (in custom syntax_positions at level 2, x custom syntax_positions at level 50, only parsing).
  (** * Declaring a constuctor argument with binders *)
  Notation "x" := {| hpos_binders := nil; hpos_head := x |}
                    (in custom syntax_positions at level 2, x custom syntax_head at level 70, only parsing).
  Notation " 'bind' x , .. , y 'in' z " :=
    {| hpos_binders:= (@cons SyntaxBinder x .. (@cons SyntaxBinder y (@nil SyntaxBinder)) ..);
       hpos_head:=z |}
      (in custom syntax_positions at level 50, x custom syntax_binder, y custom syntax_binder, z custom syntax_head at level 70, only parsing).
  

  (*** Binder *)
  Notation "a" := (HSingle a)
                    (in custom syntax_binder at level 1, a custom syntax_ident, only parsing).
  Notation " < p , x > " := (HBinderList p x)
                              (in custom syntax_binder at level 40, p custom syntax_ident, x custom syntax_ident, only parsing).

  (*** Head *)
  Notation " ( x ) " := (x)
                          (in custom syntax_head at level 2, only parsing).
  Notation "a" := (HAtom a)
                    (in custom syntax_head at level 1, a custom syntax_ident at level 1, only parsing).
  Notation " 'cod' arg ( head0 , .. , head1 ) " :=
    (HFunApp "cod" (cons arg nil) (@cons SyntaxArgHead head0 .. (@cons SyntaxArgHead head1 nil) ..))
      (in custom syntax_head at level 70, arg custom syntax_sexpr at level 2, head0 custom syntax_head at level 70, head1 custom syntax_head at level 70, no associativity, only parsing).
  Notation " 'list' ( head0 , .. , head1 ) " :=
    (HFunApp "list" nil (@cons SyntaxArgHead head0 .. (@cons SyntaxArgHead head1 nil) ..))
      (in custom syntax_head at level 70, head0 custom syntax_head at level 70, head1 custom syntax_head at level 70, no associativity, only parsing).


  (*** Sexpr *)
  Definition nApp1 s t := nApp s (cons t nil).
  Notation "x" := (nRef x)
                    (in custom syntax_sexpr at level 1, x custom syntax_ident at level 1, only parsing).
  Notation " a b " := (nApp1 a b)
                        (in custom syntax_sexpr at level 3, left associativity, only parsing).
  Notation " ( a ) " := (a)
                          (in custom syntax_sexpr at level 2, only parsing).
End SyntaxNotation.

Module SyntaxTranslation.
  (*** Translation *)
  Import ErrorM.Notations ErrorM.
  Export Syntax.

  Definition translate_binder (hb: SyntaxBinder) : Binder :=
    match hb with
    | HSingle x => Single x
    (* TODO add variadic binders *)
    | HBinderList p x => Single x
    end.

  Fixpoint translate_head (head: SyntaxArgHead) : ArgumentHead :=
    match head with
    | HAtom x => Atom x
    | HFunApp f staticArgs heads => FunApp f staticArgs (map translate_head heads)
    end.

  Definition translate_position (hp: SyntaxPosition) : Position :=
    {| pos_binders := map translate_binder hp.(hpos_binders);
       pos_head := translate_head hp.(hpos_head) |}.

  Definition translate_target (hp: SyntaxPosition) : ErrorM.t tId :=
    match hp with
    | {| hpos_binders := []; hpos_head := HAtom head |} =>
      pure head
    | _ => error "wrong target"
    end.

  Definition translate_arguments (hpositions: list SyntaxPosition) : ErrorM.t (tId * list Position) :=
    match hpositions with
    | [] => error "empty"
    | htarget :: hpositions =>
      target <- translate_target htarget;;
      pure (target, map translate_position hpositions)
    end.
           
  Definition translate_parameter (hp: SyntaxParameter) : string * tId :=
    (hp.(hpar_name), hp.(hpar_sort)).

  Definition translate_constructor (hc: SyntaxConstructor) : ErrorM.t (tId * Constructor)  :=
    '(target, positions) <- translate_arguments hc.(hcon_positions);;
    let c := {| con_parameters := map translate_parameter hc.(hcon_parameters);
                con_name := hc.(hcon_name);
                con_positions := positions |} in
    pure (target, c).


  Definition translate_spec (sorts: list tId) (hctors: list SyntaxConstructor) : ErrorM.t Spec :=
    ctors <- sequence (map translate_constructor hctors);;
    (* TODO fail if there is a constructor that does not in the declared sorts *)
    let spec_empty := SFMap.fromList (List.map (fun s => (s, [])) sorts) in
    let cs_by_sorts := List.fold_left (fun spec '(sort, ctor) =>
                                         SFMap.addCollect spec sort ctor)
                                      ctors spec_empty in
    pure (cs_by_sorts).

  Definition translate_signature (lang: autosubstLanguage) : ErrorM.t Signature :=
    let sorts := List.map hsort_name lang.(al_sorts) in
    (* TODO extract var ctor names *)
    spec <- translate_spec sorts lang.(al_ctors);;
    let canonical_order := sorts in
    build_signature None canonical_order spec.
End SyntaxTranslation.

Module SyntaxExample.
  Import Syntax SyntaxNotation SyntaxTranslation.
  
  Check {{ constr : tm }}.
  Check {{ app : (bind tm in tm) -> tm }}.
  Check {{ bla : (bind tm in tm) -> tm }}.
  Check {{ bla (p: nat) : tm -> tm }}.
  Check {{ bla (p: nat) : cod (fin p) (tm, tm) -> tm }}.
  Check {{ bla (p: nat) : tm -> list (tm, tm) -> tm }}.

  Definition bla_sorts := <{ ty : Type;
                             tm : Type }>.
  Check bla_sorts.
  Definition bla_ctors := {{ arr ( p : nat, k : nat ) : ty -> ty -> ty;
                             all : ty -> ty -> ty;
                             app : tm -> tm -> tm;
                             (* lam : (tm -> tm) |-> tm; *)
                             lam2 : (bind tm, tm in tm) -> tm;
                             vari : (bind < p, tm > in tm) -> tm;
                             const : tm
                          }}.
  Check bla_ctors.

  
  Definition fcbv_sorts :=
    <{ ty : Type;
       tm : Type;
       vl : Type }>.

  Definition fcbv_constrs :=
    {{ arr : ty -> ty -> ty;
       all : (bind ty in ty) -> ty;
       app : tm -> tm -> tm;
       tapp : tm -> ty -> tm;
       vt : vl -> tm;
       lam : ty -> (bind vl in tm) -> vl;
       tlam : (bind ty in tm) -> vl }}.

  
  (* Compute translate_spec fcbv_sorts fcbv_constrs. *)
  Definition lang := {| al_sorts := fcbv_sorts; al_ctors := fcbv_constrs |}.
  Compute ErrorM.run (translate_signature lang) tt tt.
End SyntaxExample.

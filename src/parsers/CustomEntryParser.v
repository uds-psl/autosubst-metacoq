(** * Module to parse HOAS using custom entry notations *)
Require Import List String.
Import ListNotations.
#[ local ]
 Open Scope string.

From MetaCoq.Template Require Import All.
From ASUB Require Import Language AssocList ErrorM SigAnalyzer Nterm Utils IdentParsing Termutil TemplateMonadUtils.
Import TemplateMonadNotations.


Module Syntax.

  Record SyntaxSort := { hsort_name : string; hsort_var_name : option string }.
  Inductive SyntaxBinder :=
   | HSingle : tId -> SyntaxBinder
   | HBinderList : string -> tId -> SyntaxBinder.
  Inductive SyntaxSexpr :=
   | SAtom : string -> SyntaxSexpr
   | SCons : SyntaxSexpr -> SyntaxSexpr -> SyntaxSexpr.

  Inductive SyntaxArgHead := HAtom : tId -> SyntaxArgHead
                           | HFunApp : AutosubstFunctor -> list SyntaxSexpr -> list SyntaxArgHead -> SyntaxArgHead.
  Record SyntaxPosition := { hpos_binders : list SyntaxBinder;
                             hpos_head : SyntaxArgHead }.
  Record SyntaxParameter := { hpar_name : string; hpar_sort : string }.
  Record SyntaxConstructor := { hcon_parameters : list SyntaxParameter;
                                hcon_name : string;
                                hcon_positions : list SyntaxPosition }.
  Record autosubstLanguage := { al_sorts : list SyntaxSort; al_ctors : list SyntaxConstructor }.

End Syntax.


Module SyntaxNotation.
  Import Syntax.

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
  Notation " 'codF' arg ( head0 , .. , head1 ) " :=
    (HFunApp AFCod (cons arg nil) (@cons SyntaxArgHead head0 .. (@cons SyntaxArgHead head1 nil) ..))
      (in custom syntax_head at level 70, arg custom syntax_sexpr at level 2, head0 custom syntax_head at level 70, head1 custom syntax_head at level 70, no associativity, only parsing).
  Notation " 'listF' ( head0 , .. , head1 ) " :=
    (HFunApp AFList nil (@cons SyntaxArgHead head0 .. (@cons SyntaxArgHead head1 nil) ..))
      (in custom syntax_head at level 70, head0 custom syntax_head at level 70, head1 custom syntax_head at level 70, no associativity, only parsing).

  (*** Sexpr *)
  Notation "x" := (SAtom x)
                    (in custom syntax_sexpr at level 1, x custom syntax_ident at level 1, only parsing).
  Notation " a b " := (SCons a b)
                        (in custom syntax_sexpr at level 3, left associativity, only parsing).
  Notation " ( a ) " := (a)
                          (in custom syntax_sexpr at level 2, only parsing).
End SyntaxNotation.

Module SyntaxTranslation.
  (*** Translation *)
  Import Syntax.

  Definition translate_binder (hb: SyntaxBinder) : Binder :=
    match hb with
    | HSingle x => Single x
    | HBinderList p x => BinderList p x
    end.

  (** * Try to get a reference to the given string.
   ** If it's not in the environment we just take it as a reference that will be
   ** connected to the environment later during the nterm -> term translation.
   ** 
   ** This happens for example if one references a parameter in a sexpr.
   ** e.g. from fol "Func (p : nat) : codF (fin p) (term) -> term"
   ** the fin can be turned into a ConstRef but p is not in the environment.
   *)
  Definition locate_name2 (name: string) : TemplateMonadSet nterm :=
    locs <- tmLocate name;;
    match locs with
    | [IndRef ind] => tmReturn (nTerm (tInd ind []))
    | [ConstructRef ind n] => tmReturn (nTerm (tConstruct ind n []))
    | [ConstRef kn] => tmReturn (nTerm (tConst kn []))
    | _ => tmReturn (nRef name)
    end.

  (** * Translate an S-expression
   ** the arguments to a functor can be arbitrary Coq terms so here we quote them
   *)
  Fixpoint translate_sexpr (sexpr: SyntaxSexpr) : TemplateMonadSet nterm :=
    match sexpr with
    | SAtom x => locate_name2 x
    | SCons x y =>
      x <- translate_sexpr x;;
      y <- translate_sexpr y;;
      tmReturn (nApp x [y])
    end.
  
  Fixpoint translate_head (head: SyntaxArgHead) : TemplateMonadSet ArgumentHead :=
    match head with
    | HAtom x => tmReturn (Atom x)
    | HFunApp f staticArgs heads =>
      staticArgs <- monad_map translate_sexpr staticArgs;;
      heads <- monad_map translate_head heads;;
      tmReturn (FunApp f staticArgs heads)
    end.

  Definition translate_position (hp: SyntaxPosition) : TemplateMonadSet Position :=
    head <- translate_head hp.(hpos_head);;
    tmReturn {| pos_binders := List.map translate_binder hp.(hpos_binders);
                pos_head := head |}.

  Definition translate_target (hp: SyntaxPosition) : TemplateMonadSet tId :=
    match hp with
    | {| hpos_binders := []; hpos_head := HAtom head |} => tmReturn head
    | _ => tmFail "wrong target"
    end.

  (** * Translate a list of syntax positions into the internal positions plus the target
   ** * We have to reverse the positions here because we parse them reversed so that the target is the head *)
  Definition translate_arguments (hpositions: list SyntaxPosition) : TemplateMonadSet (tId * list Position) :=
    match hpositions with
    | [] => tmFail "translate_arguments: empty position list"
    | htarget :: hpositions =>
      target <- translate_target htarget;;
      positions <- monad_map translate_position hpositions;;
      tmReturn (target, List.rev positions)
    end.
  
  Definition translate_parameter (hp: SyntaxParameter) : gallinaArg :=
    explArg hp.(hpar_name) (nRef hp.(hpar_sort)).

  Definition translate_constructor (hc: SyntaxConstructor) : TemplateMonadSet (tId * Constructor)  :=
    '(target, positions) <- translate_arguments hc.(hcon_positions);;
    let parameters := List.map translate_parameter hc.(hcon_parameters) in
    let c := {| con_parameters := parameters;
                con_name := hc.(hcon_name);
                con_positions := positions |} in
    tmReturn (target, c).


  Definition translate_spec (sorts: list tId) (hctors: list SyntaxConstructor) : TemplateMonadSet Spec :=
    ctors <- monad_map translate_constructor hctors;;
    (* TODO fail if there is a constructor that does not in the declared sorts *)
    let spec_empty := SFMap.fromList (List.map (fun s => (s, [])) sorts) in
    let cs_by_sorts := List.fold_left (fun spec '(sort, ctor) =>
                                         SFMap.addCollect spec sort ctor)
                                      ctors spec_empty in
    tmReturn (cs_by_sorts).

  Definition translate_signature (lang: autosubstLanguage) : TemplateMonadSet Signature :=
    let sorts := List.map hsort_name lang.(al_sorts) in
    (* TODO extract var ctor names *)
    spec <- translate_spec sorts lang.(al_ctors);;
    let canonical_order := sorts in
    match ErrorM.run (build_signature None canonical_order spec) tt tt with
    | inl e => tmFail e
    | inr (_, _, sig) =>
      sig <- tmEval all sig;;
      tmReturn sig
    end.
End SyntaxTranslation.

Module SyntaxExample.
  Import Syntax SyntaxNotation SyntaxTranslation.
  
  Check {{ constr : tm }}.
  Check {{ app : (bind tm in tm) -> tm }}.
  Check {{ bla : (bind tm in tm) -> tm }}.
  Check {{ bla (p: nat) : tm -> tm }}.
  Check {{ bla (p: nat) : codF (fin p) (tm, tm) -> tm }}.
  Check {{ bla (p: nat) : tm -> listF (tm, tm) -> tm }}.

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
  MetaCoq Run (translate_signature lang >>= tmPrint).

  Definition fol : autosubstLanguage :=
    {| al_sorts := <{ term : Type;
                      form : Type }>;
                                   al_ctors := {{ Func (f : nat) : codF (fin f) (term) -> term;
                                                  Fal : form;
                                                  Pred (p : nat) : codF (fin p) (term) -> form;
                                                  Impl : form -> form -> form;
                                                  Conj : form -> form -> form;
                                                  Disj : form -> form -> form;
                                                  All : (bind term in form) -> form;
                                                  Ex : (bind term in form) -> form }} |}.

  MetaCoq Run (translate_signature fol >>= tmPrint).

  
  Definition variadic : autosubstLanguage :=
    {| al_sorts := <{ tm : Type  }>;
                                  al_ctors := {{ app : tm -> listF (tm) -> tm;
                                                 lam (p: nat) : (bind <p, tm> in tm) -> tm }} |}.

  MetaCoq Run (translate_signature variadic >>= tmPrint).
End SyntaxExample.

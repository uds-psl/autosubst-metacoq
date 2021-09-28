(* bad interaction between keyword in custom entry and the coq parser.
 * There is a zulip discussion from January 2021 about it
 * https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/Bad.20interaction.20with.20notation.20and.20names
 * might be fixed in the future
 *)

Declare Custom Entry myentry.

Inductive list (A: Type) :=
| nil : list A
| cons : A -> list A -> list A. 
Arguments nil {A}.
Arguments cons {A}.

(* TODO
 * keywords in a custom entry still pollute the constr parser
 * Workaround: call it list' in the notation *)
Notation " 'listF' ( head0 , .. , head1 ) " :=
  (@cons nat head0 .. (@cons nat head1 nil) ..)
    (in custom myentry, head0 constr, head1 constr).
Notation " {{ e }} " := (e) (e custom myentry).

Check {{ listF (1, 2, 3) }}.

Inductive myind :=
| myctor : list nat -> myind.


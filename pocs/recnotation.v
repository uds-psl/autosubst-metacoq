Module m0.
  Notation "'bla' a -> .. -> b -> c" :=
    (c, (@cons nat a .. (@cons nat b nil) ..))
      (at level 70, no associativity, a at next level, b at next level, c at next level, only parsing).

  Check bla 1 -> 2 -> 3 -> 4 -> 5.

  Notation "'blub' a -> .. -> b -> c" :=
    (c, (@cons nat a .. (@cons nat b nil) ..))
      (at level 70, no associativity, a at level 71, b at level 71, c at level 71, only parsing).

  Check blub 1 -> 2 -> 3 -> 4 -> 5.
End m0.

Module m1.
  (* This is how my current parser works. just a and b in another entry does not work. Putting c also in the other entry also does not work *)
  Declare Custom Entry myentry.
  Declare Custom Entry myentry2.

  Notation "{{ x }}" := x (x custom myentry).
  Notation "'foo' a -> .. -> b -> c" :=
    (c, (@cons nat a .. (@cons nat b nil) ..))
      (in custom myentry at level 70, no associativity, a custom myentry2 at level 71, b custom myentry2 at level 71, c at level 71).
  Notation "a" := (S a) (in custom myentry2 at level 1, a constr, only parsing).

  Notation "'bar' a -> .. -> b -> c" :=
    (c, (@cons nat a .. (@cons nat b nil) ..))
      (in custom myentry at level 70, no associativity, a custom myentry2 at level 72, b custom myentry2 at level 72, c custom myentry2 at level 71).

  (* Check {{ foo 1 -> 2 -> 3 }}. *)
  (* Check {{ bar 1 -> 2 -> 3 }}. *)

End m1.

Module m2.

  Declare Custom Entry myentry.
  Declare Custom Entry myentry2.

  Notation "{{ x }}" := x (x custom myentry).
  Notation "'foo' arrows -> c" :=
    (c, arrows)
      (in custom myentry at level 70, no associativity, arrows custom myentry2 at level 50, c at level 71).
  Notation "a -> .. -> b" :=
    (@cons nat a .. (@cons nat b nil) ..)
    (in custom myentry2 at level 51, a constr, b constr, only parsing).

  (* Check {{ foo 1 -> 2 -> 3 }}. *)
End m2.

Require Import String.
From ASUB Require Import IdentParsing.
Module m3.
  Inductive wrapper := wrap : string -> wrapper.

  Declare Custom Entry myentry.
  Declare Custom Entry myentry2.
  Declare Custom Entry myident.


  Notation "{{ x }}" := x (x custom myentry).
  Notation " cname : a -> .. -> b" :=
    (cname, @cons wrapper a .. (@cons wrapper b nil) ..)
      (in custom myentry at level 70, cname custom myentry2, a custom myentry2 at level 2, b custom myentry2 at level 2, only parsing).

  Notation "a" := (wrap a) (in custom myentry2 at level 0, a custom myident at level 0, only parsing).
  Notation "a" := (ident_to_string a) (in custom myident at level 0, a ident, only parsing).

  (* Close Scope type. *)
  Open Scope string.

  (* Check fun a b c => {{ foo a -> b -> c }}. *)
  Check {{ foo : a -> b -> c }}.
End m3.

Module m3_5.

  Declare Custom Entry custom_ctor.
  Declare Custom Entry custom_ctor_args.
  Declare Custom Entry myident.


  Notation "{{ x }}" := x (x custom custom_ctor).
  Notation " cname : ctorargs " :=
    (cname, ctorargs)
      (in custom custom_ctor at level 70, cname custom myident, ctorargs custom custom_ctor_args at level 50, only parsing).

  Notation " a -> .. -> b " :=
    (@cons string a .. (@cons string b nil) ..)
      (in custom custom_ctor_args at level 50, a custom myident, b custom myident, only parsing ).

  Notation "a" := (ident_to_string a) (in custom myident at level 0, a constr at level 0, only parsing).
  (* Notation "a" := (a) (in custom myentry2 at level 0, a ident, only parsing). *)

  (* Close Scope type. *)
  Open Scope string.

  (* Check fun a b c => {{ foo a -> b -> c }}. *)
  Check {{ foo : a -> b -> c }}.
End m3_5.

Module m4.
  Import String.
  Inductive wrapper := wrap : string -> wrapper.

  Declare Custom Entry myentry.
  Declare Custom Entry ctorargentry.
  Declare Custom Entry argentry.

  Notation "{{ x }}" := x (x custom myentry).
  Notation "'foo' : ctorargs" := (ctorargs)
      (in custom myentry at level 70, no associativity, ctorargs custom ctorargentry at level 50, only parsing).

  Notation "a -> b" := (@cons wrapper b a) (in custom ctorargentry at level 49, b custom argentry, left associativity, only parsing).
  Notation "b" := (@cons wrapper (ident_to_string b) nil) (in custom ctorargentry at level 0, b ident, only parsing).

  Notation "a" := (wrap (ident_to_string a)) (in custom argentry at level 1, a constr, only parsing).

  (* Close Scope type. *)
  Open Scope string.

  (* Check {{ foo : a -> b -> c }}. *)
End m4.

Module m5.
  Import String.

  Declare Custom Entry myentry.
  Notation "{{ x }}" := x (x custom myentry).

  Notation " x ; .. ; y " :=
    (cons x .. (cons y nil) ..)
      (in custom myentry at level 100, x at level 95, y at level 95, only parsing, no associativity).

  Notation " x ( p0 , .. , p1 ) : arg0 -> .. -> arg1 " :=
    (x,
     (cons p0 .. (cons p1 nil) ..),
     (cons arg0 .. (cons arg1 nil) ..))
      (in custom myentry at level 90, p0 at next level, p1 at next level, arg0 at next level, arg1 at next level, only parsing).

  Notation "x" := x (in custom myentry at level 1, x constr, only parsing).

  Close Scope type.
  Open Scope string.
  (* Check {{ "foo" ( "p" ) : "a" -> "b" -> "c" }}. *)
End m5.
     
          


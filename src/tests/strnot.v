
Module strnot.
  (* I tried out string notations and in theory it would be possible. I could read in a whole constructor definition as a stirng and then parse it in Coq code. So you could write something like this
   "all := (ty -> ty) -> ty"
   Would have to write or find a parsing library in Coq though. *)
Definition HOASPosition_parse (bs: list Byte.byte) : option HOASPosition :=
  Some {| hpos_binders := []; hpos_head := string_of_list_byte bs |}.

Definition HOASPosition_print (p: HOASPosition) : list Byte.byte :=
  let '{| hpos_binders := _; hpos_head := head |} := p in
  list_byte_of_string head.

Declare Scope strnot_scope.
Delimit Scope strnot_scope with strnot.
String Notation HOASPosition HOASPosition_parse HOASPosition_print : strnot_scope.

Definition bla := "bla"%strnot.
Compute hpos_head bla.
Check "bla"%strnot.
End strnot.

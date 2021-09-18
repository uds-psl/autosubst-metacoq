
Inductive scope_type := Unscoped | Wellscoped.

Definition is_wellscoped (s: scope_type) :=
  match s with
  | Wellscoped => true
  | Unscoped => false
  end.

Record Flags := { fl_scope_type : scope_type }.
Definition default_flags := {| fl_scope_type := Unscoped |}.

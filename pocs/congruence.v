
    (* the type of each H references s and t so we first add them to the debruijn map to correctly
     generate the H's. Also have to take care to add a dummy binder each time since we "add" one bound H *)
    (* let '(_, eqs) := fold_left (fun '(dbmap, eqs) '(s, t) => *)
    (*                               let eq := eq_ ty_q (dbmap_get dbmap s) (dbmap_get dbmap t) in *)
    (*                               let dbmap := dbmap_add "dummy" dbmap in *)
    (*                               (dbmap, eq :: eqs)) *)
    (*                            (combine ss ts) (dbmap, []) in *)


    (* let impls := congr_interleave ss ts in *)
    (* let proof' := fold_right (fun '(((s, t), H), ((impl_args1, impl_args2), feq_args)) tm => *)
    (*                                 let impl1 := tApp ctor (map (dbmap_get dbmap) impl_args1) in *)
    (*                                 let impl2 := tApp ctor (map (dbmap_get dbmap) impl_args2) in *)
    (*                                 let feq_dbmap := dbmap_add "x" dbmap in *)
    (*                                 let feq_lam := lambda_ "x" ty_q *)
    (*                                                        (tApp ctor (map (dbmap_get feq_dbmap) feq_args)) in *)
    (*                                 let feq := tApp fequal_q [ty_q; ty_q; feq_lam; dbmap_get dbmap s; dbmap_get dbmap t; dbmap_get dbmap H] in *)
    (*                                 tApp eq_trans_q [ty_q; impl1; impl2; impl3; feq; tm] *)
    (*                              ) *)
    (*                              (tApp eq_refl_q [ty_q; impl3]) (combine (combine (combine ss ts) Hs) impls) in *)

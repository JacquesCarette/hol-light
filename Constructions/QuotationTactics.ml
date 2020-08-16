needs "Constructions/epsilon.ml";;

let rec STRING_FETCH tm = 
  let str_ty = mk_type("list",[mk_type ("char",[])]) in
    match tm with
      | Comb(Comb(Const("=",_),a),b) when type_of a = str_ty && type_of (snd(dest_comb a)) = str_ty -> [STRING_EQ_CONV(tm)]
      | Comb(a,b) -> union (STRING_FETCH a) (STRING_FETCH b)
      | Abs(a,b) -> (STRING_FETCH b)
      | Quote(e) -> (STRING_FETCH e)
      | Hole(e,ty) -> (STRING_FETCH e)
      | Eval(e,ty) -> (STRING_FETCH e)
      | _ -> [];; 

(*This tactic uses the above function to automatically reduce strings*)
let (STRING_FETCH_TAC: tactic) = fun (asm,gl) -> PURE_REWRITE_TAC (STRING_FETCH gl) (asm,gl);;

let (QUOTE_TO_CONSTRUCTION_TAC: tactic) = fun (asm,gl) -> CONV_TAC(QUOTE_TO_CONSTRUCTION_CONV) (asm,gl);;  
let (CONSTRUCTION_TO_QUOTE_TAC: tactic) = fun (asm,gl) -> CONV_TAC(CONSTRUCTION_TO_QUOTE_CONV) (asm,gl);; 
let (HOLE_ABSORB_TAC: tactic) = fun (asm,gl) -> CONV_TAC(HOLE_ABSORB_CONV) (asm,gl);;  
let (LAW_OF_DISQUO_TAC : tactic) = fun (asm,gl) -> CONV_TAC(LAW_OF_DISQUO_CONV) (asm,gl);;
let (LAW_OF_QUO_TAC : tactic) = fun (asm,gl) -> PURE_REWRITE_TAC[LAW_OF_QUO_CONV gl] (asm,gl);;
(*These tactics do the same as their original counterparts, but make use of the assumptions in the goal stack*)
let (ASM_QUOTE_TO_CONSTRUCTION_TAC: tactic) = fun (asm,gl) -> PURE_ASM_REWRITE_TAC[QUOTE_TO_CONSTRUCTION_CONV gl] (asm,gl);;  
let (ASM_CONSTRUCTION_TO_QUOTE_TAC: tactic) = fun (asm,gl) -> PURE_ASM_REWRITE_TAC[CONSTRUCTION_TO_QUOTE_CONV gl] (asm,gl);; 
let (ASM_HOLE_ABSORB_TAC: tactic) = fun (asm,gl) -> PURE_ASM_REWRITE_TAC[HOLE_ABSORB_CONV gl] (asm,gl);; 
let (ASM_LAW_OF_DISQUO_TAC : tactic) = fun (asm,gl) -> PURE_ASM_REWRITE_TAC[LAW_OF_DISQUO_CONV gl] (asm,gl);;
let (ASM_LAW_OF_QUO_TAC : tactic) = fun (asm,gl) -> PURE_ASM_REWRITE_TAC[LAW_OF_QUO_CONV gl] (asm,gl);;
let (ASM_EVAL_LAMBDA_TAC : tactic) = fun (asm,gl) -> PURE_ONCE_REWRITE_TAC[EVAL_GOAL_VSUB (top_goal())] (asm,gl);;

(* Creates an isExprType theorem for a proper term of a defined type *)
let IS_EXPR_TYPE_CONV tm = 
  match type_of tm with 
    | Tyapp("epsilon", []) when not (is_quote tm) -> failwith "Term cannot be a construction, please try IS_EXPR_TYPE_TAC" 
    | _ -> prove(rand(rator(concl(INST [termToConstruction tm, `e:epsilon`; matchType (type_of tm),`t:type`] isExprType))), 
           MP_TAC(INST [termToConstruction tm, `e:epsilon`; matchType (type_of tm),`t:type`] isExprType) THEN
           REWRITE_TAC[isExpr] THEN
           REWRITE_TAC[combinatoryType] THEN 
           REWRITE_TAC[isConst; isApp; isAbs;isVar] THEN 
           REWRITE_TAC[typeMismatch] THEN
           REWRITE_TAC[ep_constructor] THEN
           REWRITE_TAC[headFunc; isFunction;stripFunc] THEN
           REWRITE_TAC[typeInjective] THEN
           STRING_FETCH_TAC THEN 
           ASM_REWRITE_TAC[])

(* Tactic to prove isFreeIn theorems *)
let IS_FREE_IN_TAC = 
  ASM_REWRITE_TAC[isFreeIn] THEN 
  STRING_FETCH_TAC THEN
  REWRITE_TAC[] 

(* Tactic to prove isExprType theorems *)
let IS_EXPR_TYPE_TAC = 
  REWRITE_TAC[isExprType] THEN
  REWRITE_TAC[isExpr; combinatoryType] THEN
  REWRITE_TAC[isConst; isApp; isAbs;isVar] THEN 
  REWRITE_TAC[typeMismatch] THEN
  REWRITE_TAC[ep_constructor] THEN
  REWRITE_TAC[headFunc; isFunction;stripFunc] THEN
  REWRITE_TAC[typeInjective] THEN
  STRING_FETCH_TAC THEN 
  REWRITE_TAC[]

(* Tactic to prove isExpr theorems *)
let IS_EXPR_TAC = 
  REWRITE_TAC[isExpr; combinatoryType] THEN
  REWRITE_TAC[isConst; isApp; isAbs;isVar] THEN 
  REWRITE_TAC[typeMismatch] THEN
  REWRITE_TAC[ep_constructor] THEN
  REWRITE_TAC[headFunc; isFunction;stripFunc] THEN
  REWRITE_TAC[typeInjective] THEN
  STRING_FETCH_TAC THEN 
  REWRITE_TAC[]

let bound_not_free = 
  prove(`!v:epsilon. !P:epsilon. (isVar v) ==> ~ (isFreeIn v (Abs v P))`,
  MATCH_MP_TAC(lth) THEN
  REWRITE_TAC[isFreeIn] THEN
  REWRITE_TAC[isVar;ep_constructor] THEN  
  STRING_FETCH_TAC THEN
  REWRITE_TAC[]);;
                            
(* Creates theorem: ~ isFreeIn v (Abs v t) *)
let BOUND_NOT_FREE_CONV v t = 
  prove(rand(concl(SPECL [termToConstruction v; t] bound_not_free)), 
  MP_TAC(SPECL [termToConstruction v; t] bound_not_free) THEN 
  CONV_TAC(TRY_CONV QUOTE_TO_CONSTRUCTION_CONV) THEN 
  REWRITE_TAC[isVar;ep_constructor] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[]);; 

(* Creates theorem NOT-EFFECTIVE-IN(var, (Abs var tm), var_aux) *)
let NOT_FREE_ABS_NOT_EFFECTIVE_CONV var tm var_aux = 
  prove(mk_not_effective_in var (mk_abs(var,tm)) var_aux,
  CONV_TAC(ONCE_DEPTH_CONV BETA_RED_BY_SUB) THEN
  REWRITE_TAC[]);;

(* Creates theorem isFreeIn v v *)
let var_free_in_var =
  prove(`!v:epsilon. isVar v ==> isFreeIn v v`, 
  MATCH_MP_TAC(lth) THEN
  REWRITE_TAC[isVar; ep_constructor] THEN
  STRING_FETCH_TAC THEN
  REWRITE_TAC[isFreeIn]);;

(* Creates theorem !v A B:epsilon. isVar v /\ ~isFreeIn v A ==> ~isFreeIn v ((\v. B)A) *)
let comb_free_in = 
  prove(`!v:epsilon. !A:epsilon. !B:epsilon. isVar v /\ ~isFreeIn v A ==> ~isFreeIn v (App (Abs v B) A)`,
  REPEAT(GEN_TAC) THEN
  DISCH_TAC THEN
  MP_TAC(SPEC `v:epsilon` var_free_in_var) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN 
  REWRITE_TAC[isFreeIn] THEN
  ASM_REWRITE_TAC[]);;

(* Creates theorem  ~isFreeIn v ((\v. B:epsilon)A) when it is known ~isFreeIn v A *)
let COMB_FREE_IN_CONV var tm = 
  match tm with 
    | Comb(Abs(v, bod),arg) when (not(vfree_in v arg)) && var = v && type_of bod = ep_ty ->
        (prove(rand(concl(SPECL [termToConstruction v;termToConstruction arg;termToConstruction bod] comb_free_in)), 
        MP_TAC(SPECL [termToConstruction v;termToConstruction arg;termToConstruction bod] comb_free_in) THEN
        REWRITE_TAC[isFreeIn] THEN
        REWRITE_TAC[]))
    | _ -> failwith "COMB_FREE_IN_CONV: Term must be in the form (\x. (B:epsilon)) A"

(* Creates theorem [ (\x. eval B to beta)A = eval (\x B)A to beta ] when it is known ~isFreeIn v A  *)
let ABS_OF_EVAL_TO_EVAL_ABS_CONV tm = 
  match tm with 
    | Comb(Abs(v, Eval(ep,et)),arg) -> 
        (prove (rand(concl(BETA_REDUCE_EVAL v arg ep et)), 
        MP_TAC(BETA_REDUCE_EVAL v arg ep et) THEN 
        REWRITE_TAC[TERM_TO_CONSTRUCTION_CONV (mk_comb(mk_abs(v, ep), arg))] THEN
        REWRITE_TAC[IS_EXPR_TYPE_CONV (mk_comb(mk_abs(v, ep), arg))] THEN 
        PURE_REWRITE_TAC[COMB_FREE_IN_CONV v (mk_comb(mk_abs(v, ep), arg))] THEN 
        REWRITE_TAC[]))
    | _ -> failwith "ABS_OF_EVAL_TO_EVAL_ABS_CONV: Term must be in the form (\x. Eval(B,beta)) A" 

(* Creates theorem: eval Quo A to epsilon = A when it is known A is a proper construction *)
let QUO_DISQUO_CONV tm = 
  match type_of tm with 
    | Tyapp("epsilon", []) ->
        (prove(rand(concl(QUO_DISQUO tm)), 
        MP_TAC(QUO_DISQUO tm) THEN
        IS_EXPR_TYPE_TAC))
    | _ -> failwith "Term must be of type epsilon." 

let QUO_DISQUO_TAC = CONV_TAC(TOP_DEPTH_CONV(TRY_CONV QUO_DISQUO_CONV))

(* Creates theorem: eval app tm1 tm2 to beta = (eval tm1 to alpha -> beta)(eval tm2 to alpha) *)
let app_disquo_thm tm1 tm2 = 
  match type_of tm1, type_of tm2 with 
    | Tyapp("epsilon",[]),Tyapp("epsilon",[]) ->  
        (prove(rand(concl(APP_DISQUO tm1 tm2)),
        MP_TAC(APP_DISQUO tm1 tm2) THEN
        IS_EXPR_TYPE_TAC THEN
        DISCH_TAC THEN
        ASM_REWRITE_TAC[]))
    | _ -> failwith "Type mismatch!"

let APP_DISQUO_CONV tm = match tm with 
  | Eval(Comb(Comb(Const("App",_),t1),t2),_) -> app_disquo_thm t1 t2
  | _ -> failwith "Not applicable" 


(* Simplifies `eval App eps1 eps2` terms        *)
(* to `eval eps1` `eval eps2` when either       *) 
(* isExprType eps is trivial (ie. can be proven *)
(* with IS_EXPR_TYPE_TAC) or is an assumption   *)

let (APP_DISQUO_TAC:tactic) =
  fun (asl,w) ->
  let rec find_app tm = 
    match tm with 
      | Comb(Comb(Const("App",_),_),_) -> tm
      | Comb(t1,t2) ->
          (try find_app t1 with Failure _ -> 
          try  find_app t2 with Failure _ -> 
              failwith "Not applicable")
      | Abs(v,b) -> find_app b
      | Eval(e,_) -> find_app e 
      | Quote(e) -> find_app e 
      | Hole(e,_) -> find_app e  
      | _ -> failwith "Not applicable"
  in 
  let tac tm = 
    match tm with 
      | Comb(Comb(Const("App",_),t1),t2) ->
          (MP_TAC(APP_DISQUO t1 t2) THEN 
          ASM_REWRITE_TAC[] THEN 
          IS_EXPR_TYPE_TAC THEN 
          REPEAT DISCH_TAC THEN 
          ASM_REWRITE_TAC[]) 
  in
  (tac(find_app w)) (asl,w);;



let eval_beta_red_thm var arg body beta = 
  prove(rand(concl(BETA_REDUCE_EVAL var arg body beta)), 
  MP_TAC(BETA_REDUCE_EVAL var arg body beta) THEN 
  REWRITE_TAC[] THEN 
  TRY HOLE_ABSORB_TAC THEN 
  TRY QUOTE_TO_CONSTRUCTION_TAC THEN 
  IS_EXPR_TYPE_TAC THEN 
  IS_FREE_IN_TAC);;

let EVAL_BETA_RED_CONV tm = match tm with 
  | Comb(Abs(v,Eval(e,ty)),arg) ->  eval_beta_red_thm v arg e ty 
  | _ -> failwith "Not applicable"

let EVAL_BETA_RED_TAC = REPEAT(CONV_TAC(ONCE_DEPTH_CONV EVAL_BETA_RED_CONV))


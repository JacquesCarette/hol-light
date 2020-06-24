(*To make proofs easier, this function attempts to automatically match up string equalities, to do so,
it generates a list of calls to STRING_EQ_CONV for all strings in the term which can then be used with
REWRITE_TAC*)

let rec STRING_FETCH tm = match tm with
	| Comb(Comb(Const("=",_),a),b) when type_of a = mk_type("list",[mk_type ("char",[])]) -> [STRING_EQ_CONV(tm)]
	| Comb(a,b) -> (STRING_FETCH a) @ (STRING_FETCH b)
	| Abs(a,b) -> (STRING_FETCH a) @ (STRING_FETCH b)
	| Quote(e,ty) -> (STRING_FETCH e)
	| Hole(e,ty) -> (STRING_FETCH e)
	| Eval(e,ty) -> (STRING_FETCH e)
	| _ -> [];; 

(*This tactic uses the above function to automatically reduce strings*)
let (STRING_FETCH_TAC: tactic) = fun (asm,gl) -> PURE_REWRITE_TAC (STRING_FETCH gl) (asm,gl);;


let (QUOTE_TO_CONSTRUCTION_TAC: tactic) = fun (asm,gl) -> PURE_REWRITE_TAC[QUOTE_TO_CONSTRUCTION_CONV gl] (asm,gl);;  
let (UNQUOTE_TAC: tactic) = fun (asm,gl) -> PURE_REWRITE_TAC[UNQUOTE_CONV gl] (asm,gl);;  
let (LAW_OF_DISQUO_TAC : tactic) = fun (asm,gl) -> PURE_REWRITE_TAC[LAW_OF_DISQUO_CONV gl] (asm,gl);;
let (LAW_OF_QUO_TAC : tactic) = fun (asm,gl) -> PURE_REWRITE_TAC[LAW_OF_QUO_CONV gl] (asm,gl);;
(*These tactics do the same as their original counterparts, but make use of the assumptions in the goal stack*)
let (ASM_QUOTE_TO_CONSTRUCTION_TAC: tactic) = fun (asm,gl) -> PURE_ASM_REWRITE_TAC[QUOTE_TO_CONSTRUCTION_CONV gl] (asm,gl);;  
let (ASM_UNQUOTE_TAC: tactic) = fun (asm,gl) -> PURE_ASM_REWRITE_TAC[UNQUOTE_CONV gl] (asm,gl);; 
let (ASM_LAW_OF_DISQUO_TAC : tactic) = fun (asm,gl) -> PURE_ASM_REWRITE_TAC[LAW_OF_DISQUO_CONV gl] (asm,gl);;
let (ASM_LAW_OF_QUO_TAC : tactic) = fun (asm,gl) -> PURE_ASM_REWRITE_TAC[LAW_OF_QUO_CONV gl] (asm,gl);;
let (ASM_EVAL_LAMBDA_TAC : tactic) = fun (asm,gl) -> PURE_ONCE_REWRITE_TAC[EVAL_GOAL_VSUB (top_goal())] (asm,gl);

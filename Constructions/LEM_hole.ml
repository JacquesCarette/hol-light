needs "Constructions/QuotationTactics.ml";;

	(* Alternate LEM formula (with holes) *)

let holed_lem = 
	prove(`!x:epsilon. (isExprType x (TyBase "bool") ==> ((eval Q_ H_ x _H of bool \/ ~ (H_ x _H of bool) _Q to bool)))`,
	GEN_TAC THEN 
	QUOTE_TO_CONSTRUCTION_TAC THEN
	REWRITE_TAC[isExprType] THEN 
	REWRITE_TAC[IMP_CONJ] THEN
	REPEAT(DISCH_TAC) THEN 
	MP_TAC(APP_DISQUO 
	  `App (QuoConst "\\/" (TyBiCons "fun" (TyBase "bool") (TyBiCons "fun" (TyBase "bool") (TyBase "bool"))))(x:epsilon)`
	  `App (QuoConst "~" (TyBiCons "fun" (TyBase "bool") (TyBase "bool"))) (x:epsilon)`) THEN
	IS_EXPR_TYPE_TAC THEN 
	DISCH_TAC THEN
	ASM_REWRITE_TAC[] THEN
	MP_TAC(APP_DISQUO `QuoConst "\\/" (TyBiCons "fun" (TyBase "bool") (TyBiCons "fun" (TyBase "bool") (TyBase "bool")))` `x:epsilon`) THEN
	IS_EXPR_TYPE_TAC THEN 
	DISCH_TAC THEN
	ASM_REWRITE_TAC[] THEN 
	MP_TAC(APP_DISQUO `QuoConst "~" (TyBiCons "fun" (TyBase "bool") (TyBase "bool"))` `x:epsilon`) THEN
	IS_EXPR_TYPE_TAC THEN 
	DISCH_TAC THEN
	ASM_REWRITE_TAC[] THEN 
	CONSTRUCTION_TO_QUOTE_TAC THEN 
	LAW_OF_DISQUO_TAC THEN 
	REWRITE_TAC[EXCLUDED_MIDDLE]);;


let stmt = `Q_ (?n:num. !m:num. n > m) _Q`;;

(* Here is the trivial substution *)
concl(SPEC stmt holed_lem) = 
`isExprType Q_ (?n. !m. n > m) _Q (TyBase "bool") ==> (\x. (eval (Q_ (H_ (x) _H of bool \/ ~H_ (x) _H of bool) _Q) to (bool))) Q_ (?n. !m. n > m) _Q`;;

(* Apply axiom B11.2 to bring abstraction into the evaluation *)
rand(concl(ONCE_DEPTH_CONV(EVAL_BETA_RED_CONV) (concl(SPEC stmt holed_lem)))) = 
`isExprType Q_ (?n. !m. n > m) _Q (TyBase "bool") ==> (eval ((\x. Q_ (H_ (x) _H of bool \/ ~H_ (x) _H of bool) _Q) Q_ (?n. !m. n > m) _Q) to (bool))`;;

(* Simplify beta-reduction *)
rand(concl(ONCE_DEPTH_CONV(BETA_CONV) (rand(concl(ONCE_DEPTH_CONV(EVAL_BETA_RED_CONV) (concl(SPEC stmt holed_lem))))))) =
`isExprType Q_ (?n. !m. n > m) _Q (TyBase "bool") ==> (eval (Q_ (H_ (Q_ (?n. !m. n > m) _Q) _H of bool \/ ~H_ (Q_ (?n. !m. n > m) _Q) _H of bool) _Q) to (bool))`;;

(* Remove trivial hole *)
rand(concl(HOLE_ABSORB_CONV(rand(concl(ONCE_DEPTH_CONV(BETA_CONV) (rand(concl(ONCE_DEPTH_CONV(EVAL_BETA_RED_CONV) (concl(SPEC stmt holed_lem)))))))))) =
`isExprType Q_ (?n. !m. n > m) _Q (TyBase "bool") ==> (eval (Q_ ((?n. !m. n > m) \/ ~(?n. !m. n > m)) _Q) to (bool))`;;





	

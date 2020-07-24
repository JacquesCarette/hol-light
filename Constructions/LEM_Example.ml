needs "Constructions/QuotationTactics.ml";;
(* Law of excluded middle (LEM) *)

let lem = 
  prove(`!x:epsilon. isExprType x (TyBase "bool") ==> ((eval x to bool) \/ ~(eval x to bool))`,
  GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC[EXCLUDED_MIDDLE]);;

INST [`x:epsilon`,`x:epsilon`] lem = lem;;

INST [`y:epsilon`,`x:epsilon`] lem = lem;;

(*Proving what this means to be:*)
let startingPoint = SPEC `y:epsilon` lem;;
let appThm = BETA_CONV `(\x. x) y`;;
let rawBETA = BETA_REDUCE_EVAL `x:epsilon` `y:epsilon` `x:epsilon` `:bool`;;
let rawBETA_term = concl rawBETA;;
let rawBETA_equiv = ONCE_DEPTH_CONV BETA_CONV rawBETA_term;;
let desired_rawBETA = EQ_MP rawBETA_equiv rawBETA;;
let varFree = CONJUNCT1 isFreeIn;;

INST [`QuoConst "T" (TyBase "bool")`,`x:epsilon`] lem = lem;;

(* Proof of: (eval (QuoConst "T" (TyBase "bool")) to (bool)) \/ ~(eval (QuoConst "T" (TyBase "bool")) to (bool)) *)

let constLEM_with_assumption = SPEC `QuoConst "T" (TyBase "bool")` lem;;
(*desired_rawBETA is the statement that is needed to properly instantiate LEM with the QuoConst*)
let desired_rawBETA = EQ_MP (ONCE_DEPTH_CONV BETA_CONV (concl (BETA_REDUCE_EVAL `x:epsilon` `(QuoConst "T" (TyBase "bool"))` `x:epsilon` `:bool`))) (BETA_REDUCE_EVAL `x:epsilon` `(QuoConst "T" (TyBase "bool"))` `x:epsilon` `:bool`);;
(*Now what needs to be proven are the two antecedents of desired_rawBETA*)


(*FIRST ANTECEDENT: isExprType isExprType (QuoConst "T" (TyBase "bool")) (TyBase "bool")*)
let inst_isExpr = 
  prove(`isExprType (QuoConst "T" (TyBase "bool")) (TyBase "bool")`,
  IS_EXPR_TYPE_TAC);;

(*SECOND ANTECEDENT: ~isFreeIn (QuoVar "x" (TyBase "epsilon")) (QuoConst "T" (TyBase "bool"))*)
let notIsFree = 
  prove(`~isFreeIn (QuoVar "x" (TyBase "epsilon")) (QuoConst "T" (TyBase "bool"))`,IS_FREE_IN_TAC);;

(*Now we can easily prove the relationship between the abstracted version of the eval and the eval with QuoConst inside*)

let eval_abs_equivalence = 
  prove(`((\x. (eval (x) to (bool))) (QuoConst "T" (TyBase "bool")) <=> (eval (QuoConst "T" (TyBase "bool")) to (bool)))`,
  ASSUME_TAC (CONJ inst_isExpr notIsFree) THEN
  UNDISCH_TAC (concl (CONJ inst_isExpr notIsFree)) THEN
  REWRITE_TAC[desired_rawBETA]);;

(*Now, lets prove the abstracted version of LEM with QuoConst, no assumptions:*)
let abs_constLEM = 
  prove(`(\x. (eval (x) to (bool))) (QuoConst "T" (TyBase "bool")) \/ ~(\x. (eval (x) to (bool))) (QuoConst "T" (TyBase "bool"))`,
  ASSUME_TAC inst_isExpr THEN
  UNDISCH_TAC (concl inst_isExpr) THEN
  REWRITE_TAC[constLEM_with_assumption]);;

(*And finally, the theorem we've all been waiting for:*)

let trueLEM = 
  prove(`(eval (QuoConst "T" (TyBase "bool")) to (bool)) \/ ~(eval (QuoConst "T" (TyBase "bool")) to (bool))`,
  REWRITE_TAC[GSYM eval_abs_equivalence] THEN
  REWRITE_TAC[abs_constLEM]);;

let true_LEM = 
  prove(`(eval (QuoConst "T" (TyBase "bool")) to (bool)) \/ ~(eval (QuoConst "T" (TyBase "bool")) to (bool))`,
  REWRITE_TAC[EXCLUDED_MIDDLE]);;

INST [`QuoConst "F" (TyBase "bool")`,`x:epsilon`] lem = lem;;

let false_LEM = 
  prove(`(eval (QuoConst "F" (TyBase "bool")) to (bool)) \/ ~(eval (QuoConst "F" (TyBase "bool")) to (bool))`,
  REWRITE_TAC[EXCLUDED_MIDDLE]);;
	

(* INST does nothing since x is bound... *)
INST [`Q_ (0 = 0) _Q`,`x:epsilon`] lem = lem;;

(* Here is the trivial substution *)
concl(SPEC `Q_ (0 = 0) _Q` lem) = 
`isExprType Q_ (0 = 0) _Q (TyBase "bool") ==> (\x. (eval (x) to (bool))) Q_ (0 = 0) _Q \/ ~(\x. (eval (x) to (bool))) Q_ (0 = 0) _Q`;;

(* Apply axiom B11.2 to bring abstraction into the evaluation *)
rand(concl(ONCE_DEPTH_CONV(EVAL_BETA_RED_CONV) (concl(SPEC `Q_ (0 = 0) _Q` lem)))) = 
`isExprType Q_ (0 = 0) _Q (TyBase "bool") ==> (eval ((\x. x) Q_ (0 = 0) _Q) to (bool)) \/ ~(eval ((\x. x) Q_ (0 = 0) _Q) to (bool))`;;

(* Simplify trivial beta-reduction *)
rand(concl(ONCE_DEPTH_CONV(BETA_CONV) (rand(concl(ONCE_DEPTH_CONV(EVAL_BETA_RED_CONV) (concl(SPEC `Q_ (0 = 0) _Q` lem))))))) =
`isExprType Q_ (0 = 0) _Q (TyBase "bool") ==> (eval (Q_ (0 = 0) _Q) to (bool)) \/ ~(eval (Q_ (0 = 0) _Q) to (bool))`;;

	
(*The proof structure used previously requires a construction not a term, therefore we will do the proof with the right hand side of this equivalence, and them make the substitution at the end.*)
let quote_construct_equiv = QUOTE_TO_CONSTRUCTION_CONV `Q_ (0 = 0) _Q`;;
let construction_form = rhs (concl quote_construct_equiv);;

let quoteLEM_with_assumption = SPEC construction_form lem;;
(*desired_rawBETA is the statement that is needed to properly instantiate LEM with the QuoConst*)
let desired_rawBETA_quote = EQ_MP (ONCE_DEPTH_CONV BETA_CONV (concl (BETA_REDUCE_EVAL `x:epsilon` construction_form `x:epsilon` `:bool`))) (BETA_REDUCE_EVAL `x:epsilon` construction_form `x:epsilon` `:bool`);;
(*Now what needs to be proven are the two antecedents of desired_rawBETA*)


(*FIRST ANTECEDENT: isExprType isExprType construction_form*)
let inst_isExpr_quote = 
  prove(`isExprType (App (App (QuoConst "=" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "bool")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) (TyBase "bool")`,
  IS_EXPR_TYPE_TAC);;

(*SECOND ANTECEDENT: ~isFreeIn (QuoVar "x" (TyBase "epsilon")) (QuoConst "T" (TyBase "bool"))*)
let notIsFree_quote = 
  prove(`~isFreeIn (QuoVar "x" (TyBase "epsilon")) (App (App (QuoConst "=" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "bool")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num"))))`,
  REWRITE_TAC[isFreeIn]);;

(*Now we can easily prove the relationship between the abstracted version of the eval and the eval with QuoConst inside*)

let eval_abs_equivalence_quote = 
  prove(`((\x. (eval (x) to (bool))) (App (App (QuoConst "=" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "bool")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) <=> (eval (App (App (QuoConst "=" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "bool")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) to (bool)))`,
  ASSUME_TAC (CONJ inst_isExpr_quote notIsFree_quote) THEN
  UNDISCH_TAC (concl (CONJ inst_isExpr_quote notIsFree_quote)) THEN
  REWRITE_TAC[desired_rawBETA_quote]);;

(*Now, lets prove the abstracted version of LEM with QuoConst, no assumptions:*)
let abs_quoteLEM = 
  prove(`(\x. (eval (x) to (bool))) (App (App (QuoConst "=" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "bool")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num"))))  \/ ~(\x. (eval (x) to (bool))) (App (App (QuoConst "=" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "bool")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) `,
  ASSUME_TAC inst_isExpr_quote THEN
  UNDISCH_TAC (concl inst_isExpr_quote) THEN
  REWRITE_TAC[quoteLEM_with_assumption]);;

(*And finally, the theorem we've all been waiting for:*)

let quoteLEM = 
  prove(`(eval (App (App (QuoConst "=" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "bool")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) to (bool)) \/ ~(eval (App (App (QuoConst "=" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "bool")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) to (bool))`,
  REWRITE_TAC[GSYM eval_abs_equivalence_quote] THEN
  REWRITE_TAC[abs_quoteLEM]);;

let quoteLEM2 = 
  prove (`(eval (Q_ (0 = 0) _Q) to (bool)) \/ ~ (eval (Q_ (0 = 0) _Q) to (bool))`,
  REWRITE_TAC[quote_construct_equiv] THEN
  REWRITE_TAC[quoteLEM]);;




				


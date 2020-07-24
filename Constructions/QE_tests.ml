needs "Constructions/QuotationTactics.ml";;

(* When running this file there should be only `true` returns *)

(*                                              *)
(* Tests for NOT-EFFECTIVE-IN related functions *)
(*                                              *)


(* We want to ensure mk_not_effective_in creates the right formula, that the NEI formulas must be explicitly added to the NEI list, 
	and that we're able to verify that the variables are NEI their respective terms *)
let refl_of_eq = prove(mk_not_effective_in `x:aty` `(x:aty) = (x:aty)` `y:aty`, REWRITE_TAC[REFL `x:aty`]);;  

addNotEff refl_of_eq;;

not_effective_in `x:aty` `(x:aty) = (x:aty)` = true;;
concl refl_of_eq = `!y:aty. (\x:aty. (x:aty) = (x:aty)) y = ((x:aty) = (x:aty))` = true;;

let anteced1 = prove(`isExprType ((\y. Q_ (x:aty = x) _Q) z) (TyBase "bool")`, QUOTE_TO_CONSTRUCTION_TAC THEN IS_EXPR_TYPE_TAC);;
let anteced2 = prove(`~(isFreeIn (QuoVar "y" (TyVar "aty")) ((\y:aty. Q_ (x:aty = x) _Q)(z:aty)))`, QUOTE_TO_CONSTRUCTION_TAC THEN IS_FREE_IN_TAC);;
			
let eval_refl = 
  prove(mk_not_effective_in `y:aty` `eval Q_ (x:aty) = x _Q to bool` `z:aty`, 
  GEN_TAC THEN 
  (MP_TAC(BETA_REDUCE_EVAL `y:aty` `z:aty` `Q_ (x:aty) = x _Q` `:bool`)) THEN 
  REWRITE_TAC[anteced1;anteced2]);;
  
addNotEff eval_refl;;

let axiom_A4_6 = 
  prove(mk_not_effective_in `x:aty` `(\x:aty. P:aty)` `y:aty`, 
  GEN_TAC THEN CONV_TAC(RATOR_CONV(RAND_CONV(BETA_CONV))) THEN REFL_TAC);;
  
addNotEff axiom_A4_6;;
not_effective_in `x:aty` `(\x:aty. P:aty)`= true;;

let bound_by_quote = 
  prove(mk_not_effective_in `x:epsilon` `Q_ (x:epsilon) _Q` `y:epsilon`,
  GEN_TAC THEN CONV_TAC(RATOR_CONV(RAND_CONV(BETA_CONV))) THEN REFL_TAC);;
  
not_effective_in `x:epsilon` `Q_ (x:epsilon) _Q` = false;;
addNotEff bound_by_quote;;
not_effective_in `x:epsilon` `Q_ (x:epsilon) _Q`= true;;


(*                                              *)
(* Tests for eval and hole related functions    *)
(*                                              *)

(* Want to ensure holes and evals are detected and functions that require hole and/or eval-free terms work appropriately *)
not (hole_free `Q_ !x:epsilon. H_ x _H of bool \/ ~ (H_ x _H of bool) _Q`) = true;;
not (hole_free `Q_ Q_ Q_ H_ x:epsilon _H of bool _Q _Q _Q`) = true;;
hole_free (rand (concl (HOLE_ABSORB_CONV `(\x:epsilon. eval x to bool)(Q_ H_ Q_ T _Q _H of bool _Q)`))) = true;;
can HOLE_ABSORB_CONV `(\x:epsilon. eval x to bool)(Q_ H_ Q_ T _Q _H of num _Q)` = false;;

eval_free `Q_ !x:epsilon. H_ x _H of bool \/ ~ (H_ x _H of bool) _Q` = true;;
not (eval_free `(\x:epsilon. eval x to bool)(Q_ H_ Q_ T _Q _H of bool _Q)`) = true;;
eval_free (rand (concl (LAW_OF_DISQUO `p ==> q <=> ~ p \/ q`))) && not (eval_free (rator (concl (LAW_OF_DISQUO `p ==> q <=> ~ p \/ q`)))) = true;;    


(*                                              *)
(* Tests for substitution related functions     *)
(*                                              *)

vfree_in `x:aty` `\x:aty. P:aty` = false;;
vfree_in `x:aty` `Q_ H_ x:epsilon _H of aty _Q` = false;;
vfree_in `x:epsilon` `Q_ H_ x:epsilon _H of aty _Q` = true;;
vfree_in `x:epsilon` `Q_  x:epsilon _Q` = false;;
vfree_in `y:aty` `\x:aty. y:aty` = true;;
vfree_in `x:epsilon` `eval x:epsilon to bool` = true;;
vfree_in `x:bool` `(\x:bool. T = x)(x = z:bool)` = true;;

vsubst [(`F`, `x:bool`)] `(\x:bool. T = x)(x = z:bool)` = `(\x:bool. T = x)(F = z:bool)` = true;;
vsubst [(`F`, `x:bool`)] `(\y:bool. T = x)` = `(\y:bool. T = F)` = true;;
vsubst [(`y:aty`,`x:aty`)] `eval Q_ x:aty = x _Q to bool` = `(\x:aty. (eval (Q_ (x:aty = x) _Q) to (bool))) y:aty` = true;;
vsubst [(`y:aty`,`x:aty`)] `eval Q_ x:aty = x _Q to bool` = `(\x:aty. (eval (Q_ (x:aty = x) _Q) to (bool))) y:aty` = true;;
vsubst [(`y:aty`,`x:aty`)] `eval Q_ x:aty = x _Q to bool` = `(\x:aty. (eval (Q_ (x:aty = x) _Q) to (bool))) y:aty` = true;;

(* This example is due to the eval_refl theorem and shows the effects of axiom B11.2 *)
vsubst [(`z:aty`,`x:aty`)] `\z:aty. eval Q_ x:aty = x _Q to bool` = `(\x:aty z:aty. (eval (Q_ (x:aty = x) _Q) to (bool)))(z:aty)` = true;;
vsubst [(`z:aty`,`y:aty`)] `\z:aty. eval Q_ x:aty = x _Q to bool` = `(\z:aty. (\y:aty. (eval (Q_ (x:aty = x) _Q) to (bool))) (z:aty))` = true;;


(*                                                        *)
(* Tests for construction <-> quote related functions     *)
(*                                                        *)


rand(concl(QUOTE_TO_CONSTRUCTION_CONV `Q_ (\x:epsilon. isConst x) _Q`)) = 
`Abs (QuoVar "x" (TyBase "epsilon")) (App (QuoConst "isConst" (TyBiCons "fun" (TyBase "epsilon") (TyBase "bool"))) (QuoVar "x" (TyBase "epsilon")))` ;;

rand(concl(QUOTE_TO_CONSTRUCTION_CONV `Q_ Q_ Q_ (_0 + _0) _Q _Q _Q`)) = 
`Quo (Quo (App (App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) (QuoConst "_0" (TyBase "num"))) (QuoConst "_0" (TyBase "num"))))`

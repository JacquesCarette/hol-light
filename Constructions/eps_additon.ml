needs "Constructions/addition.ml";;
needs "Constructions/QuotationTactics.ml";;

(*                                                                       *)
(* Term builders : these functions allow members of the type `nat`       *)
(*                 (representing unary numbers) to be manipulated like   *)
(*                 binary numbers                                        *)
(*                                                                       *)

let one_def = define `(One = S Zero)`;;

let thenZero = define `
  (thenZero Zero = Zero) /\
  (thenZero (S Zero) = S (S Zero)) /\
  (thenZero (S (S x)) = add_unary (S (S x)) (S (S x)))`;;

let thenOne = define `
  (thenOne Zero = S Zero) /\
  (thenOne (S Zero) = S (S (S Zero))) /\
  (thenOne (S (S x)) = add_unary (add_unary (S (S x)) (S (S x))) (S Zero))`;;

(*
let ZERO = `QuoConst "Zero" (TyBase "nat")`;;

Comb(Comb(Const(constName,ty),firstArg),secondArg)

let add_me = define `add_me ZERO ZERO = ZERO` *)

(*                                                                       *)
(* Classification of the subset of constructions representing proper     *)
(* `nat` expressions (i.e. binary numbers beginning with a 1)            *)
(*                                                                       *)

let start_with_one = define `
  (start_with_one (QuoConst str ty) <=> 
  	((str = "One") /\ (ty = (TyBase "nat")))) /\
  (start_with_one (App eps1 eps2) <=> 
    (((eps1 = (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))) \/
  	(eps1 = (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))))) /\ 
	(start_with_one eps2))) /\
  (start_with_one (Abs eps1 eps2) = F) /\
  (start_with_one (QuoVar str ty) = F) /\
  (start_with_one (Quo e) = F)`;;

let proper_nat_construct = define `
  (proper_nat_construct (QuoConst str ty) <=> 
    (((str = "Zero") \/ (str = "One")) /\ (ty = (TyBase "nat")))) /\
  (proper_nat_construct (App eps1 eps2) <=> 
  	(((eps1 = (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))) \/
  	(eps1 = (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))))) /\ 
    proper_nat_construct eps2) /\
	(start_with_one eps2)) /\
  (proper_nat_construct (Quo eps) = F) /\
  (proper_nat_construct (Abs eps1 eps2) = F) /\
  (proper_nat_construct (QuoVar str ty) = F)` ;;

(*                                                                *)
(* Syntactical addition algorithm                                 *)
(*                                                                *)

let add_ebin = define `
  (add_ebin (QuoConst "Zero" (TyBase "nat")) x = x) /\
  (add_ebin x (QuoConst "Zero" (TyBase "nat")) = x) /\
  (add_ebin (QuoConst "One" (TyBase "nat")) 
    (QuoConst "One" (TyBase "nat")) = 
    (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) 
    (QuoConst "One" (TyBase "nat")))) /\
  (add_ebin (QuoConst "One" (TyBase "nat")) 
  	(App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x) = 
    (App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x)) /\
  (add_ebin (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x) 
  	(QuoConst "One" (TyBase "nat")) = 
    (App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x)) /\
  (add_ebin (QuoConst "One" (TyBase "nat")) 
  	(App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x) = 
    (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) 
    (add_ebin (QuoConst "One" (TyBase "nat")) x))) /\
  (add_ebin (App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x) 
  	(QuoConst "One" (TyBase "nat")) = 
    (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) 
    (add_ebin (QuoConst "One" (TyBase "nat")) x))) /\
  (add_ebin (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x) 
  	(App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) y) =
    (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) 
    (add_ebin x y))) /\
  (add_ebin (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x) 
  	(App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) y) =
    (App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) 
    (add_ebin x y))) /\
  (add_ebin (App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x) 
  	(App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) y) =
    (App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) 
    (add_ebin x y))) /\
  (add_ebin (App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x) 
  	(App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) y) =
    (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) 
    (add_ebin (QuoConst "One" (TyBase "nat")) (add_ebin x y))))`;; 


(* Tactics for proving theorems involving the `nat` type  *)

(* Used when each base case can be easily solved *)
let DOUBLE_NAT_INDUCT_TAC thml = 
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[thenOne;thenZero;one_def;add_unary] THEN 
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[thenOne;thenZero;one_def;add_unary] THEN 
  GEN_TAC THEN 
  REPEAT DISCH_TAC THEN 
  REWRITE_TAC thml;;

  
(*                                                                *)
(* Simple `nat` arithmetic lemmas translated to the epsilon type  *)
(*                                                                *)

let remove_one = prove(
  `!x:nat. add_unary One (thenZero x) = thenOne x`,
  DOUBLE_NAT_INDUCT_TAC[SPECL [`(Zero):nat`;`(add_unary (S (S a)) a):nat`] take_s;id_of_plus]
  );;

let carry_one = prove(
  `!x:nat. add_unary One (thenOne x) = thenZero (add_unary One x)`,
  DOUBLE_NAT_INDUCT_TAC[take_s;add_unary;id_of_plus]
  );;

let ebin_sym_add = prove(
  `!x:epsilon. !y:epsilon. proper_nat_construct x /\ proper_nat_construct y ==> 
  add_ebin x y = add_ebin y x`,
  MATCH_MP_TAC(lth) THEN 
  REWRITE_TAC[proper_nat_construct;IMP_CONJ] THEN 
  CONJ_TAC THEN
  GEN_TAC THEN 
  GEN_TAC THENL
  [MATCH_MP_TAC(lth) THEN 
  REWRITE_TAC[proper_nat_construct;IMP_CONJ] THEN 
  CONJ_TAC THEN 
  REPEAT GEN_TAC THENL
  [REPEAT DISCH_TAC THEN 
  TOP_DISJ_CASES_TAC THEN 
  ASM_REWRITE_TAC[add_ebin] THEN 
  BOTTOM_DISJ_CASES_TAC THEN 
  ASM_REWRITE_TAC[add_ebin]
  ;REPEAT DISCH_TAC THEN 
  TOP_DISJ_CASES_TAC THEN
  ASM_REWRITE_TAC[add_ebin] THEN
  BOTTOM_DISJ_CASES_TAC THEN 
  ASM_REWRITE_TAC[add_ebin] 
  ]
  ;REPEAT DISCH_TAC THEN 
  MATCH_MP_TAC(lth) THEN 
  REWRITE_TAC[proper_nat_construct;IMP_CONJ] THEN 
  CONJ_TAC THEN 
  REPEAT GEN_TAC THEN 
  REPEAT DISCH_TAC THENL
  [BOTTOM_DISJ_CASES_TAC THEN 
  ASM_REWRITE_TAC[add_ebin] THEN 
  TOP_DISJ_CASES_TAC THEN 
  ASM_REWRITE_TAC[add_ebin]
  ;TOP_DISJ_CASES_TAC THEN 
  BOTTOM_DISJ_CASES_TAC THEN 
  ASM_REWRITE_TAC[add_ebin] THEN
  MP_ASSUMPTION_TAC(SPEC `a1':epsilon` 
  (ASSUME `!y. proper_nat_construct a1
  ==> proper_nat_construct y
  ==> add_ebin a1 y = add_ebin y a1`)) THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[]
  ] 
  ]
  );;

let take_out_S = prove(
  `!x:nat. thenZero (S x) = S (S (add_unary x x))`,
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[add_unary;thenZero;take_s]
  );;

let take_out_s_thenOne = prove(
  `!x:nat. thenOne (S x) = S (S (S (add_unary x x)))`,
  MATCH_MP_TAC(nat_induct) THEN
  REWRITE_TAC[add_unary;thenOne;take_s]
  );;

let add_one_even = prove(
  `!x:nat. S (thenZero x) = thenOne x`,
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[thenZero;thenOne] THEN 
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[thenZero;thenOne;take_s;add_unary]
  );;

let add_even = prove(
  `!x:nat. !y:nat. thenZero (add_unary x y) = 
  add_unary (thenZero x) (thenZero y)`,
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[thenZero;id_of_plus] THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[thenZero;add_unary;take_s] THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN
  REWRITE_TAC[take_out_S;take_s;add_unary;assoc_add] THEN 
  REWRITE_TAC[SYM(SPECL [`a:nat`;`a':nat`;`a:nat`] assoc_add)] THEN 
  MP_TAC(SPECL [`a':nat`;`a:nat`] sym_add) THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  REWRITE_TAC[assoc_add]
  );;

let add_even_odd = prove(
  `!x:nat. !y:nat. thenOne (add_unary x y) = 
  add_unary (thenZero x) (thenOne y)`,
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[thenZero;thenOne;id_of_plus] THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[thenZero;add_unary;thenOne;add_one_even] THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN
  REWRITE_TAC[take_out_s_thenOne;add_unary;take_s;take_out_S] THEN
  MP_TAC(SYM(SPECL [`a:nat`;`a':nat`;`(add_unary a a'):nat`] assoc_add)) THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  MP_TAC(SPECL [`a':nat`;`(add_unary a a'):nat`] sym_add) THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  REWRITE_TAC[assoc_add]
  );;

let add_odd_even = prove(
  `!x:nat. !y:nat. thenOne (add_unary x y) = 
  add_unary (thenOne x) (thenZero y)`,
  REPEAT GEN_TAC THEN 
  MP_TAC(SPECL [`x:nat`;`y:nat`] sym_add) THEN
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  REWRITE_TAC[add_even_odd;sym_add]
  );;

let odd_to_even = prove(
  `!x:nat. S (thenOne x) = thenZero (S x)`,
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[thenZero;thenOne] THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  REWRITE_TAC[take_out_s_thenOne;add_unary;take_s]
  );;

(*                                                                *)
(* Results regarding the syntax of proper `nat` expressions       *)
(*                                                                *)

let lemma1 = prove(
  `!x:epsilon. proper_nat_construct x ==> 
  isExprType x (TyBase "nat")`,
  MATCH_MP_TAC(lth) THEN 
  REWRITE_TAC[proper_nat_construct] THEN
  CONJ_TAC THEN 
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN 
  REWRITE_TAC[isExprType] THEN
  REPEAT DISCH_TAC THEN 
  IS_EXPR_TYPE_TAC THEN 
  TOP_DISJ_CASES_TAC THEN
  ASM_REWRITE_TAC[
    ep_constructor;combinatoryType;isFunction;headFunc;isExpr;stripFunc] THEN 
  MP_ASSUMPTION_TAC(ASSUME 
    `proper_nat_construct a1 ==> 
  	isExpr a1 /\ combinatoryType a1 = TyBase "nat"`) THEN
  REWRITE_TAC[IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[]);; 

let lemma3 = prove(
  `!x:epsilon. start_with_one x ==> 
  start_with_one (add_ebin (QuoConst "One" (TyBase "nat")) x)`,
  MATCH_MP_TAC(lth) THEN 
  REWRITE_TAC[start_with_one] THEN
  CONJ_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN
  REPEAT DISCH_TAC THENL
  [ASM_REWRITE_TAC[add_ebin;start_with_one]
  ;TOP_DISJ_CASES_TAC THENL
  [ASM_REWRITE_TAC[add_ebin;start_with_one]
  ;ASM_REWRITE_TAC[add_ebin;start_with_one] THEN 
  MP_ASSUMPTION_TAC(ASSUME `start_with_one a1
    ==> start_with_one (add_ebin (QuoConst "One" (TyBase "nat")) a1)`) THEN
  REWRITE_TAC[]
  ] 
  ]
  );;

let lemma4 = prove( 
  `!x:epsilon. proper_nat_construct x ==> 
  proper_nat_construct (add_ebin (QuoConst "One" (TyBase "nat")) x)`,
  MATCH_MP_TAC(lth) THEN 
  REWRITE_TAC[proper_nat_construct] THEN
  CONJ_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN
  REPEAT DISCH_TAC THENL
  [TOP_DISJ_CASES_TAC THEN
  ASM_REWRITE_TAC[add_ebin;proper_nat_construct;start_with_one]
  ;TOP_DISJ_CASES_TAC THEN
  ASM_REWRITE_TAC[add_ebin;proper_nat_construct] THEN 
  MP_ASSUMPTION_TAC(ASSUME 
  	`proper_nat_construct a1 ==> 
  	proper_nat_construct (add_ebin (QuoConst "One" (TyBase "nat")) a1)`) THEN 
  MP_ASSUMPTION_TAC(SPEC `a1:epsilon` lemma3) THEN
  REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[]
  ]
  );;

let lemma5 = prove(
  `!x:epsilon. !y:epsilon. start_with_one x ==> 
  start_with_one y ==> start_with_one (add_ebin x y)`,
  MATCH_MP_TAC(lth) THEN 
  REWRITE_TAC[start_with_one] THEN 
  CONJ_TAC THENL 
  [REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  MP_ASSUMPTION_TAC(SPEC `y:epsilon` lemma3) 
  ;REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  MATCH_MP_TAC(lth) THEN
  REWRITE_TAC[start_with_one] THEN
  CONJ_TAC THEN 
  REPEAT GEN_TAC THEN 
  REWRITE_TAC[IMP_CONJ] THEN
  REPEAT DISCH_TAC THENL
  [TOP_DISJ_CASES_TAC THEN
  ASM_REWRITE_TAC[add_ebin;start_with_one] THEN 
  MP_ASSUMPTION_TAC(SPEC `a1:epsilon` lemma3) 
  ;BOTTOM_DISJ_CASES_TAC THEN 
  TOP_DISJ_CASES_TAC THEN 
  ASM_REWRITE_TAC[add_ebin;start_with_one] THEN
  MP_ASSUMPTION_TAC(SPEC `a1':epsilon` (ASSUME 
    `!y. start_with_one a1
    ==> start_with_one y
    ==> start_with_one (add_ebin a1 y)`)) THEN 
  DISCH_TAC THEN 
  MP_ASSUMPTION_TAC(SPEC `add_ebin (a1:epsilon) (a1':epsilon)` lemma3) THEN 
  REWRITE_TAC[]
  ]
  ]
  );;

let lemma6 = prove(
  `!x:epsilon. !y:epsilon. proper_nat_construct x ==> 
  proper_nat_construct y ==> proper_nat_construct (add_ebin x y)`,
  MATCH_MP_TAC(lth) THEN 
  REWRITE_TAC[proper_nat_construct] THEN 
  CONJ_TAC THENL 
  [GEN_TAC THEN
  GEN_TAC THEN 
  MATCH_MP_TAC(lth) THEN
  REWRITE_TAC[proper_nat_construct] THEN 
  CONJ_TAC THENL 
  [REWRITE_TAC[IMP_CONJ] THEN
  REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN
  TOP_DISJ_CASES_TAC THENL
  [ASM_REWRITE_TAC[add_ebin;proper_nat_construct] 
  ;BOTTOM_DISJ_CASES_TAC THEN
  ASM_REWRITE_TAC[add_ebin;proper_nat_construct;start_with_one]
  ]
  ;REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN
  REPEAT DISCH_TAC THEN 
  TOP_DISJ_CASES_TAC THENL
  [ASM_REWRITE_TAC[add_ebin;proper_nat_construct]
  ;BOTTOM_DISJ_CASES_TAC THEN
  ASM_REWRITE_TAC[add_ebin;proper_nat_construct;start_with_one] THEN
  MP_ASSUMPTION_TAC(SPEC `a1':epsilon` lemma3) THEN 
  MP_ASSUMPTION_TAC(ASSUME 
    `a0 = "Zero" \/ a0 = "One"
    ==> a1 = TyBase "nat"
    ==> proper_nat_construct a1'
    ==> proper_nat_construct (add_ebin (QuoConst a0 a1) a1')`) THEN 
  ASM_REWRITE_TAC[] THEN 
  REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[] 
  ]
  ]
  ;REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN
  REPEAT DISCH_TAC THEN
  MATCH_MP_TAC(lth) THEN 
  REWRITE_TAC[proper_nat_construct] THEN 
  CONJ_TAC THENL
  [REPEAT GEN_TAC THEN 
  REWRITE_TAC[IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  TOP_DISJ_CASES_TAC THEN
  BOTTOM_DISJ_CASES_TAC THEN 
  ASM_REWRITE_TAC[add_ebin;proper_nat_construct] THEN 
  MP_TAC(SPEC `a1:epsilon` lemma3) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  MP_TAC(SPEC `a1:epsilon` lemma4) THEN
  ASM_REWRITE_TAC[]
  ;REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  TOP_DISJ_CASES_TAC THEN 
  BOTTOM_DISJ_CASES_TAC THEN
  ASM_REWRITE_TAC[add_ebin;proper_nat_construct] THEN 
  ASM_REWRITE_TAC[add_ebin;proper_nat_construct] THEN 
  MP_ASSUMPTION_TAC(SPEC `a1':epsilon` (ASSUME 
  	`!y. proper_nat_construct a1 ==> 
  	proper_nat_construct y ==> 
  	proper_nat_construct (add_ebin a1 y)`)) THEN
  MP_ASSUMPTION_TAC(SPECL [`a1:epsilon`;`a1':epsilon`] lemma5) THEN 
  ASM_REWRITE_TAC[] THEN 
  REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_ASSUMPTION_TAC(SPEC `add_ebin (a1:epsilon) (a1':epsilon)` lemma3) THEN
  MP_ASSUMPTION_TAC(SPEC `add_ebin (a1:epsilon) (a1':epsilon)` lemma4) THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[]
  ]
  ] 
  );;
  
let thm1 = prove(
  `!x:epsilon. !y:epsilon. proper_nat_construct x ==> proper_nat_construct y 
  ==> isExprType(add_ebin x y) (TyBase "nat")`,
  REPEAT GEN_TAC THEN 
  REWRITE_TAC[IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  MP_TAC(SPECL [`x:epsilon`;`y:epsilon`] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  MP_TAC(SPEC `(add_ebin x y):epsilon` lemma1) THEN 
  ASM_REWRITE_TAC[]
  );;
  
let thm2 = prove(
  `!x:epsilon. !str:string. !ty:type. proper_nat_construct x 
  ==> ~isFreeIn (QuoVar str ty) x`,
  MATCH_MP_TAC(lth) THEN
  REWRITE_TAC[proper_nat_construct;isFreeIn] THEN 
  REPEAT GEN_TAC THEN 
  REWRITE_TAC[IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  GEN_TAC THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  DISCH_TAC THEN 
  DISCH_TAC THEN 
  REWRITE_TAC[DE_MORGAN_THM] THEN 
  MP_ASSUMPTION_TAC(SPECL [`str:string`;`ty:type`] (ASSUME 
    `!str ty. proper_nat_construct a1 
    ==> ~isFreeIn (QuoVar str ty) a1`)) THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  TOP_DISJ_CASES_TAC THEN 
  ASM_REWRITE_TAC[isFreeIn] 
  );;

(*                  *)
(* ADDITION TACTICS *)
(*                  *)

(* when proper_nat_construct x is an assumption, adds isExprType x nat to assumptions *)
let PROPER_TYPE_TAC tm = 
  MP_TAC(SPEC tm lemma1) THEN 
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC;; 

(* adds ~isFreeIn (QuoVar str ty) tm to assumptions *)
let PROPER_NOT_FREE_TAC tm str ty = 
  SUBGOAL_THEN (rand(concl (SPECL [tm;str;ty] thm2))) ASSUME_TAC THEN 
  MP_TAC(SPECL [tm;str;ty] thm2) THEN 
  ASM_REWRITE_TAC[proper_nat_construct;start_with_one] THEN 
  REWRITE_TAC[isExprType;isExpr];;

(* when isExprType and notFreeIn thms are assumtions *)
let NAT_BETA_EVAL_RED tm = 
  match tm with 
    | Comb(Abs(v, Eval(ep,et)),arg) -> 
        ((SUBGOAL_THEN (rand(concl(BETA_REDUCE_EVAL v arg ep et))) ASSUME_TAC) THEN  
        MP_TAC(BETA_REDUCE_EVAL v arg ep et) THEN 
        ASM_REWRITE_TAC[])
    | _ -> failwith "wrong input";;


(* Function which searches a term for abstractions (\x. B) and creates the trivial *)
(* NOT-EFFECTIVE-IN theorems stating x is NOT-EFFECTIVE-IN (\x. B)                 *)
let TRIV_NE tm =
  let rec add_all_ne_thms tm = match tm with 
    | Abs(v,bod) when not (eval_free tm) ->  
        let eff_thm = 
          NOT_FREE_ABS_NOT_EFFECTIVE_CONV v bod (variant (vars_in tm) (mk_var("w",(type_of v)))) 
        in(
        addNotEff eff_thm;
        add_all_ne_thms bod)
    | Comb(f,a) -> (add_all_ne_thms f; add_all_ne_thms a)
    | Eval(e,_) -> add_all_ne_thms e
    | Hole(e,_) -> add_all_ne_thms e
    | Quote(e) -> add_all_ne_thms e
    | _ -> ()
  in
  add_all_ne_thms tm;;

(* Creates therorem:                                                          *)
(* !j:epsilon. proper_nat_construct j ==>                                     *)
(*   (\tm. (eval (j) to (nat))) (w:type_of tm) = (eval ((\tm. j) w) to (nat)) *)
let proper_nat_beta_red tm = 
  if not (is_var tm) then failwith "Term must be a variable" else 
  let ty = type_of tm in 
  let ty_ty = matchType ty in 
  let arg = mk_var("w", ty) in
  let trm = mk_comb(`(!):(epsilon -> bool) -> bool`,mk_abs(mk_var("j",`:epsilon`),
    mk_comb(mk_comb(`(==>)`,`proper_nat_construct (j:epsilon)`),
    mk_comb(mk_comb(`(=):nat -> nat -> bool`,mk_comb(mk_abs(tm,`eval (j:epsilon) to (nat)`),
    mk_var("w", ty))),mk_eval(mk_comb(mk_abs(tm,mk_var("j",`:epsilon`)),
    mk_var("w", ty)),`:nat`))))) in 
  prove(
  trm,
  GEN_TAC THEN 
  DISCH_TAC THEN 
  MP_ASSUMPTION_TAC(SPEC `j:epsilon` lemma1) THEN 
  DISCH_TAC THEN 
  MP_TAC(BETA_REDUCE_EVAL tm arg `j:epsilon` `:nat`) THEN 
  ASM_REWRITE_TAC[] THEN 
  MP_ASSUMPTION_TAC(SPECL [`j:epsilon`;tmp_mk_string(explode(fst(dest_var tm)));ty_ty] thm2) THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[]);;

let taut_lemma = 
  TAUT `!p:bool. !q:bool. !r:bool. ((p ==> q) = (p ==> r)) <=> (p ==> (q = r))`;;

 (* Proves the theorem var N-E-I tm and adds it to the NE list *)
let ne_to_inst var tm arg thm = 
  let trm = mk_comb(mk_abs(var, tm),arg) in 
  let theorem = prove(mk_not_effective_in var tm arg,
  GEN_TAC THEN 
  REWRITE_TAC[BETA_RED_BY_SUB trm] THEN 
  REWRITE_TAC[thm]) in 
  addNotEff theorem;;


(*                                              *)
(* Theorem templates: used for similar theorems *)
(*                                              *)

let fin_beta_red tm1 tm2 var arg thm = 
  let tm = 
    mk_comb(mk_comb(`(=):bool->bool->bool`,
    mk_comb(mk_comb(`(==>)`,
    mk_comb(mk_comb(`(/\):bool->bool->bool`,
    mk_comb(`proper_nat_construct:epsilon -> bool`,tm1)),
    mk_comb(`proper_nat_construct:epsilon -> bool`,tm2))),
    mk_comb(mk_comb(`(=):nat -> nat -> bool`, 
    mk_comb(mk_abs(var,mk_eval(mk_comb(
    mk_comb(`add_ebin:epsilon -> epsilon -> epsilon`,tm1),tm2),`:nat`)),arg)),
    mk_comb(mk_comb(`add_unary:nat -> nat -> nat`, 
    mk_comb(mk_abs(var,mk_eval(tm1,`:nat`)),arg)),  
    mk_comb(mk_abs(var,mk_eval(tm2,`:nat`)),arg))))), 
    mk_comb(mk_comb(`(==>)`,
    mk_comb(mk_comb(`(/\):bool->bool->bool`,
    mk_comb(`proper_nat_construct:epsilon -> bool`, tm1)),
    mk_comb(`proper_nat_construct:epsilon -> bool`, tm2))),
    mk_comb(mk_comb(`(=):nat -> nat -> bool`,
    mk_eval(mk_comb(mk_comb(`add_ebin:epsilon -> epsilon -> epsilon`,
    tm1), tm2), `:nat`)), 
    mk_comb(mk_comb(`add_unary:nat -> nat -> nat`,
    mk_eval(tm1, `:nat`)),
    mk_eval(tm2, `:nat`))))) in
  let add_1_2 = mk_comb(mk_comb(
    `add_ebin:epsilon -> epsilon -> epsilon`,tm1),tm2) in
  prove(tm,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [tm1;tm2] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  MP_TAC(SPEC tm1 thm) THEN 
  MP_TAC(SPEC tm2 thm) THEN 
  MP_TAC(SPEC add_1_2 thm) THEN
  PROPER_TYPE_TAC(tm1) THEN 
  PROPER_TYPE_TAC(tm2) THEN 
  PROPER_TYPE_TAC(add_1_2) THEN 
  (PROPER_NOT_FREE_TAC tm1 `"j"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC tm2 `"j"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC add_1_2 `"j"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(mk_comb(`\j:epsilon. (eval (j) to (nat))`, tm1)) THEN 
  NAT_BETA_EVAL_RED(mk_comb(`\j:epsilon. (eval (j) to (nat))`, tm2)) THEN 
  NAT_BETA_EVAL_RED(mk_comb(`\j:epsilon. (eval (j) to (nat))`, add_1_2)) THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[]
  );;

let sub_x tm1 tm2 sub =
  let add_1_2 = mk_comb(mk_comb(`add_ebin`, tm1),tm2) in 
  let add_sub = mk_comb(mk_comb(`add_ebin`, sub),tm2) in  
  let tm = 
    mk_comb(mk_comb(`(=):bool->bool->bool`,
    mk_comb(mk_comb(`(==>)`,
    mk_comb(mk_comb(`(/\):bool->bool->bool`,
    mk_comb(`proper_nat_construct:epsilon -> bool`,sub)),
    mk_comb(`proper_nat_construct:epsilon -> bool`,tm2))),
    mk_comb(mk_comb(`(=):nat -> nat -> bool`, 
    mk_comb(mk_abs(tm1,mk_eval(mk_comb(
    mk_comb(`add_ebin:epsilon -> epsilon -> epsilon`,tm1),tm2),`:nat`)),sub)),
    mk_comb(mk_comb(`add_unary:nat -> nat -> nat`, 
    mk_comb(mk_abs(tm1,mk_eval(tm1,`:nat`)),sub)),  
    mk_comb(mk_abs(tm1,mk_eval(tm2,`:nat`)),sub))))), 
    mk_comb(mk_comb(`(==>)`,
    mk_comb(mk_comb(`(/\):bool->bool->bool`,
    mk_comb(`proper_nat_construct:epsilon -> bool`, sub)),
    mk_comb(`proper_nat_construct:epsilon -> bool`, tm2))),
    mk_comb(mk_comb(`(=):nat -> nat -> bool`,
    mk_eval(mk_comb(mk_comb(`add_ebin:epsilon -> epsilon -> epsilon`,
    sub), tm2), `:nat`)), 
	mk_comb(mk_comb(`add_unary:nat -> nat -> nat`,
	mk_eval(sub,`:nat`)),
	mk_eval(tm2,`:nat`))))) 
  in
  prove(tm, 
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  MP_TAC(SPECL [sub;tm2] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  PROPER_TYPE_TAC(sub) THEN 
  PROPER_TYPE_TAC(tm2) THEN 
  PROPER_TYPE_TAC(add_sub) THEN 
  (PROPER_NOT_FREE_TAC sub `"x"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC tm2 `"x"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC add_sub `"x"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(mk_comb(mk_abs(tm1,mk_eval(tm1,`:nat`)),sub)) THEN 
  NAT_BETA_EVAL_RED(mk_comb(mk_abs(tm1,mk_eval(tm2,`:nat`)),sub)) THEN 
  NAT_BETA_EVAL_RED(mk_comb(mk_abs(tm1,mk_eval(add_1_2,`:nat`)),sub)));;  
  

let sub_y tm1 tm2 sub =
  let add_1_2 = mk_comb(mk_comb(`add_ebin`, tm1),tm2) in 
  let add_sub = mk_comb(mk_comb(`add_ebin`, tm1),sub) in  
  let tm = 
    mk_comb(mk_comb(`(=):bool->bool->bool`,
    mk_comb(mk_comb(`(==>)`,
    mk_comb(mk_comb(`(/\):bool->bool->bool`,
    mk_comb(`proper_nat_construct:epsilon -> bool`,tm1)),
    mk_comb(`proper_nat_construct:epsilon -> bool`,sub))),
    mk_comb(mk_comb(`(=):nat -> nat -> bool`, 
    mk_comb(mk_abs(tm2,mk_eval(mk_comb(
    mk_comb(`add_ebin:epsilon -> epsilon -> epsilon`,tm1),tm2),`:nat`)),sub)),
    mk_comb(mk_comb(`add_unary:nat -> nat -> nat`, 
    mk_comb(mk_abs(tm2,mk_eval(tm1,`:nat`)),sub)),  
    mk_comb(mk_abs(tm2,mk_eval(tm2,`:nat`)),sub))))), 
    mk_comb(mk_comb(`(==>)`,
    mk_comb(mk_comb(`(/\):bool->bool->bool`,
    mk_comb(`proper_nat_construct:epsilon -> bool`, tm1)),
    mk_comb(`proper_nat_construct:epsilon -> bool`, sub))),
    mk_comb(mk_comb(`(=):nat -> nat -> bool`,
    mk_eval(mk_comb(mk_comb(`add_ebin:epsilon -> epsilon -> epsilon`,
    tm1),sub),`:nat`)), 
    mk_comb(mk_comb(`add_unary:nat -> nat -> nat`,
    mk_eval(tm1,`:nat`)),
    mk_eval(sub,`:nat`))))) 
  in
  prove(tm, 
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  MP_TAC(SPECL [tm1;sub] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  PROPER_TYPE_TAC(tm1) THEN 
  PROPER_TYPE_TAC(sub) THEN 
  PROPER_TYPE_TAC(add_sub) THEN 
  (PROPER_NOT_FREE_TAC tm1 `"y"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC sub `"y"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC add_sub `"y"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(mk_comb(mk_abs(tm2,mk_eval(tm1,`:nat`)),sub)) THEN 
  NAT_BETA_EVAL_RED(mk_comb(mk_abs(tm2,mk_eval(tm2,`:nat`)),sub)) THEN 
  NAT_BETA_EVAL_RED(mk_comb(mk_abs(tm2,mk_eval(add_1_2,`:nat`)),sub)));;  
  
let sub_add_one tm = 
  let var = mk_var("x",`:epsilon`) in 
  let add_one_sub = mk_comb(mk_comb(`add_ebin`,`QuoConst "One" (TyBase "nat")`),var) in
  let add_one_tm = mk_comb(mk_comb(`add_ebin`,`QuoConst "One" (TyBase "nat")`),tm) in
  let trm = 
    mk_comb(mk_comb(`(=):bool->bool->bool`,
    mk_comb(mk_comb(`(==>)`,
    mk_comb(`proper_nat_construct:epsilon -> bool`,tm)),
    mk_comb(mk_comb(`(=):nat -> nat -> bool`, 
    mk_comb(mk_abs(var,mk_eval(add_one_sub,`:nat`)),tm)),
    mk_comb(mk_comb(`add_unary:nat -> nat -> nat`, 
    `One`),  
    mk_comb(mk_abs(var,mk_eval(var,`:nat`)),tm))))), 
    mk_comb(mk_comb(`(==>)`,
    mk_comb(`proper_nat_construct:epsilon -> bool`, tm)),
    mk_comb(mk_comb(`(=):nat -> nat -> bool`,
    mk_eval(add_one_tm,`:nat`)), 
    mk_comb(mk_comb(`add_unary:nat -> nat -> nat`,
    `One`),
    mk_eval(tm,`:nat`))))) 
  in 
  prove(trm,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `proper_nat_construct (QuoConst "One" (TyBase "nat"))` ASSUME_TAC THEN 
  REWRITE_TAC[proper_nat_construct] THEN  
  MP_TAC(SPECL [`(QuoConst "One" (TyBase "nat")):epsilon`;tm] lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  PROPER_TYPE_TAC(`(QuoConst "One" (TyBase "nat")):epsilon`) THEN 
  PROPER_TYPE_TAC(tm) THEN 
  PROPER_TYPE_TAC(add_one_tm) THEN 
  (PROPER_NOT_FREE_TAC tm `"x"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC add_one_tm `"x"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(mk_comb(mk_abs(var,mk_eval(add_one_sub,`:nat`)),tm)) THEN 
  NAT_BETA_EVAL_RED(mk_comb(mk_abs(var,mk_eval(var,`:nat`)),tm))
  );;

let no_sub_add_one var sub = 
  let x = mk_var("x",`:epsilon`) in 
  let one = `QuoConst "One" (TyBase "nat")` in
  let add_one_tm = mk_comb(mk_comb(`add_ebin`,`QuoConst "One" (TyBase "nat")`),x) in
  let trm = 
    mk_comb(mk_comb(`(=):bool->bool->bool`,
    mk_comb(mk_comb(`(==>)`,
    mk_comb(`proper_nat_construct:epsilon -> bool`,x)),
    mk_comb(mk_comb(`(=):nat -> nat -> bool`, 
    mk_comb(mk_abs(var,mk_eval(add_one_tm,`:nat`)),sub)),
    mk_comb(mk_comb(`add_unary:nat -> nat -> nat`, 
    `One`),  
    mk_comb(mk_abs(var,mk_eval(x,`:nat`)),sub))))), 
    mk_comb(mk_comb(`(==>)`,
    mk_comb(`proper_nat_construct:epsilon -> bool`, x)),
    mk_comb(mk_comb(`(=):nat -> nat -> bool`,
    mk_eval(add_one_tm,`:nat`)), 
    mk_comb(mk_comb(`add_unary:nat -> nat -> nat`,
    `One`),
    mk_eval(x,`:nat`))))) 
  in 
  prove(trm,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  MP_TAC(SPECL [one;x] lemma6) THEN 
  ASM_REWRITE_TAC[proper_nat_construct] THEN 
  DISCH_TAC THEN 
  SUBGOAL_THEN `proper_nat_construct (QuoConst "One" (TyBase "nat"))` ASSUME_TAC THEN 
  REWRITE_TAC[proper_nat_construct] THEN 
  PROPER_TYPE_TAC(one) THEN 
  PROPER_TYPE_TAC(x) THEN 
  PROPER_TYPE_TAC(add_one_tm) THEN 
  (PROPER_NOT_FREE_TAC 
    one (tmp_mk_string(explode(fst(dest_var var)))) (matchType(type_of var))) THEN 
  (PROPER_NOT_FREE_TAC x (tmp_mk_string(explode(fst(dest_var var)))) (matchType(type_of var))) THEN 
  (PROPER_NOT_FREE_TAC 
    add_one_tm (tmp_mk_string(explode(fst(dest_var var)))) (matchType(type_of var))) THEN 
  NAT_BETA_EVAL_RED(mk_comb(mk_abs(var,mk_eval(one,`:nat`)),sub)) THEN 
  NAT_BETA_EVAL_RED(mk_comb(mk_abs(var,mk_eval(x,`:nat`)),sub)) THEN 
  NAT_BETA_EVAL_RED(mk_comb(mk_abs(var,mk_eval(add_one_tm,`:nat`)),sub))
  );;

(*                                         *)
(* NOT-EFFECTIVE-IN LEMMAS                 *)
(*                                         *)
  
let ne1 = TRIV_NE `\x:epsilon. proper_nat_construct (x:epsilon) ==> 
  (\a0:string. (eval (x:epsilon) to (nat))) (w:string) = eval (\a0. x) w to (nat)`

let ne21 = TRIV_NE `\x:epsilon. proper_nat_construct (x:epsilon) ==> 
  (\a1:type. (eval (x:epsilon) to (nat))) (w:type) = eval (\a1. x) w to (nat)`

let beta_red1 = proper_nat_beta_red (mk_var("a0", `:string`));;
let fin_beta_red1 = 
  fin_beta_red `x:epsilon` `y:epsilon` `a0:string` `w:string` beta_red1;;
let a0_ne = 
  ne_to_inst `a0:string` 
  `\x:epsilon. !y:epsilon. proper_nat_construct x /\ proper_nat_construct y ==>
  (eval (add_ebin x y) to (nat)) = 
  add_unary (eval (x) to (nat)) (eval (y) to (nat))` `w:string` fin_beta_red1;;

let beta_red2 = proper_nat_beta_red(mk_var("a1",`:type`));;
let fin_beta_red2 = 
  fin_beta_red `x:epsilon` `y:epsilon` `a1:type` `w:type` beta_red2;;
let a1_ne = 
  ne_to_inst `a1:type` 
  `\x:epsilon. !y:epsilon. proper_nat_construct x /\ proper_nat_construct y ==>
  (eval (add_ebin x y) to (nat)) = 
  add_unary (eval (x) to (nat)) (eval (y) to (nat))` `w:type` fin_beta_red2;;

let beta_red3 = proper_nat_beta_red(mk_var("b0",`:string`));;
let fin_beta_red3 = 
  fin_beta_red `QuoConst a0 a1` `y:epsilon` `b0:string` `w:string` beta_red3;;
let b0_ne = 
  ne_to_inst `b0:string` 
  `\y. proper_nat_construct (QuoConst a0 a1) /\ proper_nat_construct y
  ==> (eval (add_ebin (QuoConst a0 a1) y) to (nat)) =
  add_unary (eval (QuoConst a0 a1) to (nat)) (eval (y) to (nat))` `w:string` fin_beta_red3;;

let beta_red4 = proper_nat_beta_red(mk_var("b1",`:type`));;
let fin_beta_red4 = 
  fin_beta_red `QuoConst a0 a1` `y:epsilon` `b1:type` `w:type` beta_red4;;
let b1_ne = 
  ne_to_inst `b1:type` 
  `\y. proper_nat_construct (QuoConst a0 a1) /\ proper_nat_construct y
  ==> (eval (add_ebin (QuoConst a0 a1) y) to (nat)) =
  add_unary (eval (QuoConst a0 a1) to (nat)) (eval (y) to (nat))` `w:type` fin_beta_red4;;

let beta_red5 = proper_nat_beta_red(mk_var("b0",`:epsilon`));;
let fin_beta_red5 = 
  fin_beta_red `QuoConst a0 a1` `y:epsilon` `b0:epsilon` `w:epsilon` beta_red5;;
let b0_eps_ne = 
  ne_to_inst `b0:epsilon` 
  `\y. proper_nat_construct (QuoConst a0 a1) /\ proper_nat_construct y
  ==> (eval (add_ebin (QuoConst a0 a1) y) to (nat)) =
  add_unary (eval (QuoConst a0 a1) to (nat)) (eval (y) to (nat))` `w:epsilon` fin_beta_red5;;

let beta_red6 = proper_nat_beta_red(mk_var("a0",`:epsilon`));;
let fin_beta_red6 = 
  fin_beta_red `x:epsilon` `y:epsilon` `a0:epsilon` `w:epsilon` beta_red6;;
let a0_eps_ne = 
  ne_to_inst `a0:epsilon` 
  `\x. !y. proper_nat_construct x /\ proper_nat_construct y
  ==> (eval (add_ebin x y) to (nat)) =
  add_unary (eval (x) to (nat)) (eval (y) to (nat))` `w:epsilon` fin_beta_red6;;

let fin_beta_red7 =
  let tm = 
    fin_beta_red `App a0 a1` `y:epsilon` `b0:string` `w:string` beta_red3 
  in 
  EQ_MP (REWRITE_CONV[IMP_CONJ] (concl tm)) tm;;
let b0_app_ne = 
  ne_to_inst `b0:string` 
  `\y. proper_nat_construct (App a0 a1)
  ==> proper_nat_construct y
  ==> (eval (add_ebin (App a0 a1) y) to (nat)) =
  add_unary (eval (App a0 a1) to (nat)) (eval (y) to (nat))` `w:string` fin_beta_red7;;

let fin_beta_red8 =
  let tm = 
    fin_beta_red `App a0 a1` `y:epsilon` `b1:type` `w:type` beta_red4 
  in 
  EQ_MP (REWRITE_CONV[IMP_CONJ] (concl tm)) tm;;
let b1_app_ne = 
  ne_to_inst `b1:type` 
  `\y. proper_nat_construct (App a0 a1) ==> proper_nat_construct y
  ==> (eval (add_ebin (App a0 a1) y) to (nat)) =
  add_unary (eval (App a0 a1) to (nat)) (eval (y) to (nat))` `w:type` fin_beta_red8;;

let fin_beta_red9 =
  let tm = 
    fin_beta_red `App a0 a1` `y:epsilon` `b0:epsilon` `w:epsilon` beta_red5 
  in 
  EQ_MP (REWRITE_CONV[IMP_CONJ] (concl tm)) tm;;
let b0_eps_app_ne = 
  ne_to_inst `b0:epsilon` 
  `\y. proper_nat_construct (App a0 a1) ==> proper_nat_construct y
  ==> (eval (add_ebin (App a0 a1) y) to (nat)) =
  add_unary (eval (App a0 a1) to (nat)) (eval (y) to (nat))` `w:epsilon` fin_beta_red9;;

let beta_red10 = proper_nat_beta_red(mk_var("a1",`:epsilon`));;
let fin_beta_red10 = 
  fin_beta_red `x:epsilon` `y:epsilon` `a1:epsilon` `w:epsilon` beta_red10;;
let a1_eps_ne = 
  ne_to_inst `a1:epsilon` 
  `\x. !y. proper_nat_construct x /\ proper_nat_construct y
  ==> (eval (add_ebin x y) to (nat)) =
  add_unary (eval (x) to (nat)) (eval (y) to (nat))` `w:epsilon` fin_beta_red10;;

let beta_red11 = proper_nat_beta_red(mk_var("a",`:epsilon`));;
let fin_beta_red11 = 
  fin_beta_red `x:epsilon` `y:epsilon` `a:epsilon` `w:epsilon` beta_red11;;
let a1_eps_ne = 
  ne_to_inst `a:epsilon` 
  `\x. !y. proper_nat_construct x /\ proper_nat_construct y
  ==> (eval (add_ebin x y) to (nat)) =
  add_unary (eval (x) to (nat)) (eval (y) to (nat))` `w:epsilon` fin_beta_red11;;

let beta_red12 = proper_nat_beta_red(mk_var("b1",`:epsilon`));;
let fin_beta_red12 = 
  fin_beta_red `QuoConst a0 a1` `y:epsilon` `b1:epsilon` `w:epsilon` beta_red12;;
let b1_eps_ne =
  ne_to_inst `b1:epsilon` 
    `\y. proper_nat_construct (QuoConst a0 a1) /\ proper_nat_construct y
    ==> (eval (add_ebin (QuoConst a0 a1) y) to (nat)) =
    add_unary (eval (QuoConst a0 a1) to (nat)) (eval (y) to (nat))` `w:epsilon` fin_beta_red12;;

let fin_beta_red13 =
  let tm = 
    fin_beta_red `App a0 a1` `y:epsilon` `b1:epsilon` `w:epsilon` beta_red12 
  in 
  EQ_MP (REWRITE_CONV[IMP_CONJ] (concl tm)) tm;;
let b0_eps_app_ne = 
  ne_to_inst `b1:epsilon` 
  `\y. proper_nat_construct (App a0 a1) ==> proper_nat_construct y
  ==> (eval (add_ebin (App a0 a1) y) to (nat)) =
  add_unary (eval (App a0 a1) to (nat)) (eval (y) to (nat))` `w:epsilon` fin_beta_red13;;

let ind_1 = TRIV_NE `\x:epsilon. !y:epsilon. (((proper_nat_construct (x:epsilon)) /\ 
  (proper_nat_construct (y:epsilon))) ==> 
  (eval (add_ebin x y) to (nat) = 
  add_unary (eval x to (nat)) (eval y to (nat))))`;;

(* Need an induction theorem with different bound variables for second inductions *)
let eps_alt_ind = 
  EQ_MP (ALPHA (concl lth) 
  `!P. (!b0 b1. P (QuoVar b0 b1)) /\ (!b0 b1. P (QuoConst b0 b1)) /\
  (!b0 b1. P b0 /\ P b1 ==> P (App b0 b1)) /\
  (!b0 b1. P b0 /\ P b1 ==> P (Abs b0 b1)) /\
  (!b. P b ==> P (Quo b)) ==> (!b. P b)`) lth;;

let ind_y1 = TRIV_NE `\y:epsilon. proper_nat_construct (QuoConst a0 a1) /\ 
  proper_nat_construct y ==> (eval (add_ebin (QuoConst a0 a1) y) to (nat)) =
  add_unary (eval (QuoConst a0 a1) to (nat)) (eval (y) to (nat))`;;

let ind_y2 = TRIV_NE `\y:epsilon. proper_nat_construct (App a0 a1)
  ==> proper_nat_construct y
  ==> (eval (add_ebin (App a0 a1) y) to (nat)) =
  add_unary (eval (App a0 a1) to (nat)) (eval (y) to (nat))`;;


(* Simplyifying lemmas *)
let x_quoconst_sub = 
  sub_x `x:epsilon` `y:epsilon` `QuoConst a0 a1`;;

let y_quoconst_sub = 
  sub_y `QuoConst a0 a1` `y:epsilon` `QuoConst b0 b1`;;

let y_quoapp_sub =
  sub_y `QuoConst a0 a1` `y:epsilon` `App b0 b1`;;

let x_quoapp_sub = 
  sub_x `x:epsilon` `y:epsilon` `App a0 a1`;;

let y_quoconst2_sub = 
  let tm = sub_y `App a0 a1` `y:epsilon` `QuoConst b0 b1`
  in
  EQ_MP (REWRITE_CONV[IMP_CONJ] (concl tm)) tm;; 

let x_case1_sub = 
  sub_x `x:epsilon` `y:epsilon` `a0:epsilon`;;

let x_case2_sub = 
  sub_x `x:epsilon` `y:epsilon` `a1:epsilon`;;

let y_case1_sub = 
  let tm = sub_y `App a0 a1` `y:epsilon` `b0:epsilon` 
  in
  EQ_MP (REWRITE_CONV[IMP_CONJ] (concl tm)) tm;;

let y_case2_sub = 
  let tm = sub_y `App a0 a1` `y:epsilon` `b1:epsilon` 
  in
  EQ_MP (REWRITE_CONV[IMP_CONJ] (concl tm)) tm;;

let y_quoapp_app_sub = 
  let tm = sub_y `App a0 a1` `y:epsilon` `App b0 b1` 
  in
  EQ_MP (REWRITE_CONV[IMP_CONJ] (concl tm)) tm;;

let y_quoapp_case1_sub = 
  let tm = sub_y `a1:epsilon` `y:epsilon` `b1:epsilon` 
  in
  EQ_MP (REWRITE_CONV[IMP_CONJ] (concl tm)) tm;;

let fin_x_sub = 
  let tm = sub_add_one `add_ebin a1 b1` in
  EQ_MP (REWRITE_CONV[taut_lemma] (concl tm)) tm;;


(* Final theorem needed *)
let ind_3 = TRIV_NE `\x:epsilon. proper_nat_construct x ==> 
  eval (add_ebin (QuoConst "One" (TyBase "nat")) x) to (nat) = 
  add_unary One (eval x to (nat))`;;

let x_thm3_sub = no_sub_add_one `a0:string` `w:string`;;

let a0_ne_thm3 = 
  ne_to_inst `a0:string` 
  `\x. proper_nat_construct x
  ==> (eval (add_ebin (QuoConst "One" (TyBase "nat")) x) to (nat)) =
  add_unary One (eval (x) to (nat))` `w:string` x_thm3_sub;;

let a1_thm3_sub = no_sub_add_one `a1:type` `w:type`;;

let a1_ne_thm3 = 
  ne_to_inst `a1:type` 
  `\x. proper_nat_construct x
  ==> (eval (add_ebin (QuoConst "One" (TyBase "nat")) x) to (nat)) =
  add_unary One (eval (x) to (nat))` `w:type` a1_thm3_sub;;

let thm3_x_quoconst = sub_add_one `QuoConst a0 a1`;;

let x_eps_thm3_sub = no_sub_add_one `a0:epsilon` `w:epsilon`;;

let a0_eps_ne_thm3 = 
  ne_to_inst `a0:epsilon` 
  `\x. proper_nat_construct x
  ==> (eval (add_ebin (QuoConst "One" (TyBase "nat")) x) to (nat)) =
  add_unary One (eval (x) to (nat))` `w:epsilon` x_eps_thm3_sub;;

let a1_eps_ne_thm3 = 
  let tm = (mk_not_effective_in `a1:epsilon` 
    `\x. proper_nat_construct x
    ==> (eval (add_ebin (QuoConst "One" (TyBase "nat")) x) to (nat)) =
    add_unary One (eval (x) to (nat))` `w:epsilon`) 
  in
  EQ_MP (ALPHA (concl a0_eps_ne_thm3) tm) a0_eps_ne_thm3;;
addNotEff a1_eps_ne_thm3;;

let a_eps_ne_thm3 = 
  let tm = (mk_not_effective_in `a:epsilon` 
    `\x. proper_nat_construct x
    ==> (eval (add_ebin (QuoConst "One" (TyBase "nat")) x) to (nat)) =
    add_unary One (eval (x) to (nat))` `w:epsilon`) 
  in
  EQ_MP (ALPHA (concl a0_eps_ne_thm3) tm) a0_eps_ne_thm3;;
addNotEff a_eps_ne_thm3;;

let sub_a1_thm = sub_add_one `a1:epsilon`;;

let sub_app_thm = sub_add_one `App a0 a1`;;

let sub_b1_thm = sub_add_one `b1:epsilon`;;

let thm3 = prove(
  `!x:epsilon. proper_nat_construct x ==> 
  eval (add_ebin (QuoConst "One" (TyBase "nat")) x) to (nat) = 
  add_unary One (eval x to (nat))`,
  MATCH_MP_TAC(lth) THEN 
  CONJ_TAC THENL
  [REWRITE_TAC[proper_nat_construct]
  ;CONJ_TAC THENL
  [REPEAT GEN_TAC THEN 
  REWRITE_TAC[thm3_x_quoconst] THEN 
  REWRITE_TAC[proper_nat_construct;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  TOP_DISJ_CASES_TAC THEN 
  ASM_REWRITE_TAC[add_ebin] THEN 
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN 
  REWRITE_TAC[add_unary;thenZero;one_def]
  ;CONJ_TAC THENL
  [REPEAT GEN_TAC THEN 
  REWRITE_TAC[sub_a1_thm;sub_app_thm;IMP_CONJ] THEN 
  DISCH_TAC THEN 
  DISCH_TAC THEN 
  REWRITE_TAC[proper_nat_construct;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  TOP_DISJ_CASES_TAC THEN 
  ASM_REWRITE_TAC[add_ebin] THENL
  [MP_TAC(APP_DISQUO 
    `QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `a1:epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `a1:epsilon`) THEN 
  PROPER_TYPE_TAC(`a1:epsilon`) THEN 
  ASM_REWRITE_TAC[] THEN 
  IS_EXPR_TYPE_TAC THEN
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN 
  REWRITE_TAC[one_def;take_s;id_of_plus;add_one_even]
  ;MP_TAC(APP_DISQUO 
    `QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `a1:epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `(add_ebin (QuoConst "One" (TyBase "nat")) a1):epsilon`) THEN 
  PROPER_TYPE_TAC(`a1:epsilon`) THEN
  SUBGOAL_THEN 
    `proper_nat_construct (QuoConst "One" (TyBase "nat"))` ASSUME_TAC THEN 
  REWRITE_TAC[proper_nat_construct] THEN 
  MP_TAC(SPECL [`(QuoConst "One" (TyBase "nat"))`;`a1:epsilon`] thm1) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  IS_EXPR_TYPE_TAC THEN
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN 
  REWRITE_TAC[one_def;take_s;id_of_plus;add_one_even] THEN 
  MP_ASSUMPTION_TAC(ASSUME `proper_nat_construct a1
  ==> (eval (add_ebin (QuoConst "One" (TyBase "nat")) a1) to (nat)) =
  add_unary One (eval (a1) to (nat))`) THEN 
  DISCH_TAC THEN 
  QUOTE_TO_CONSTRUCTION_TAC THEN
  ASM_REWRITE_TAC[
    carry_one;one_def;take_s;id_of_plus;add_one_even;take_out_S;odd_to_even]
  ]
  ;REWRITE_TAC[proper_nat_construct]
  ]
  ]
  ]
  );;


(*                                                     *)
(* Meaning formula for addition                        *)
(*                                                     *)

let add_meaning = 
  let tm = 
    `(!x:epsilon y:epsilon. 
    (((proper_nat_construct x) /\ (proper_nat_construct y)) 
    ==> (eval (add_ebin x y) to (nat) =  
    add_unary (eval x to (nat)) (eval y to (nat)))))` 
  in 
  prove(tm, 
  MATCH_MP_TAC(lth) THEN 
  CONJ_TAC THENL
  [(* isVar x *)
  REWRITE_TAC[proper_nat_construct]
  ;CONJ_TAC THENL
  [(* isConst x  *)
  GEN_TAC THEN 
  GEN_TAC THEN 
  REWRITE_TAC[x_quoconst_sub] THEN 
  MATCH_MP_TAC(eps_alt_ind) THEN 
  CONJ_TAC THENL
  [(* isVar y  *)
  REWRITE_TAC[proper_nat_construct]
  ;CONJ_TAC THENL
  [(* isConst y *)
  REPEAT GEN_TAC THEN 
  REWRITE_TAC[y_quoconst_sub;proper_nat_construct;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  TOP_DISJ_CASES_TAC THEN 
  BOTTOM_DISJ_CASES_TAC THEN 
  ASM_REWRITE_TAC[add_ebin] THEN 
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN 
  REWRITE_TAC[one_def;add_unary;thenZero]
  ;CONJ_TAC THENL
  [(* isApp y *) 
  REPEAT GEN_TAC THEN
  REWRITE_TAC[y_quoapp_sub;proper_nat_construct;IMP_CONJ] THEN
  REPEAT DISCH_TAC THEN 
  TOP_DISJ_CASES_TAC THENL
  [ASM_REWRITE_TAC[add_ebin] THEN 
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN 
  REWRITE_TAC[id_of_plus]
  ;BOTTOM_DISJ_CASES_TAC THEN 
  ASM_REWRITE_TAC[add_ebin] THENL
  [

  MP_TAC(APP_DISQUO 
    `QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `b1:epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `b1:epsilon`) THEN
  PROPER_TYPE_TAC(`b1:epsilon`) THEN
  IS_EXPR_TYPE_TAC THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN




  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN
  REWRITE_TAC[remove_one]
  ;MP_TAC(APP_DISQUO 
    `QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `b1:epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `(add_ebin (QuoConst "One" (TyBase "nat")) b1):epsilon`) THEN
  MP_TAC(SPECL [`(QuoConst "One" (TyBase "nat"))`;`b1:epsilon`] thm1) THEN
  REWRITE_TAC[
    proper_nat_construct;
    ASSUME `proper_nat_construct (b1:epsilon)`] THEN
  DISCH_TAC THEN  
  ASM_REWRITE_TAC[] THEN
  PROPER_TYPE_TAC(`b1:epsilon`) THEN
  IS_EXPR_TYPE_TAC THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  MP_TAC(SPEC `b1:epsilon` thm3) THEN 
  REWRITE_TAC[sub_b1_thm;ASSUME `proper_nat_construct b1`] THEN
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN 
  REWRITE_TAC[carry_one]
  ]
  ]
  ;REWRITE_TAC[proper_nat_construct]
  ]
  ]
  ]
  ;CONJ_TAC THENL
  [(* isApp x *)
  REPEAT GEN_TAC THEN 
  REWRITE_TAC[IMP_CONJ;x_case1_sub;x_case2_sub;x_quoapp_sub] THEN 
  REPEAT DISCH_TAC THEN 
  MATCH_MP_TAC(eps_alt_ind) THEN 
  CONJ_TAC THENL
  [(* isVar y *)
  REWRITE_TAC[proper_nat_construct]
  ;CONJ_TAC THENL
  [(* isConst y *)
  REPEAT GEN_TAC THEN
  REWRITE_TAC[y_quoconst2_sub;proper_nat_construct] THEN
  REWRITE_TAC[IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  BOTTOM_DISJ_CASES_TAC THENL
  [ASM_REWRITE_TAC[add_ebin] THEN 
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN 
  REWRITE_TAC[add_unary]
  ;TOP_DISJ_CASES_TAC THEN 
  ASM_REWRITE_TAC[add_ebin] THENL
  [MP_TAC(APP_DISQUO 
    `QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `a1:epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))`  
    `a1:epsilon`) THEN
  PROPER_TYPE_TAC(`a1:epsilon`) THEN
  IS_EXPR_TYPE_TAC THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN
  REWRITE_TAC[sym_add;remove_one]
  ;MP_TAC(APP_DISQUO 
    `QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `a1:epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `(add_ebin (QuoConst "One" (TyBase "nat")) a1):epsilon`) THEN
  MP_TAC(SPECL [`a1:epsilon`;`(QuoConst "One" (TyBase "nat"))`] thm1) THEN
  MP_TAC(SPECL [`(QuoConst "One" (TyBase "nat"))`;`a1:epsilon`] thm1) THEN 
  REWRITE_TAC[
    ASSUME `proper_nat_construct (a1:epsilon)`;
    proper_nat_construct] THEN
  DISCH_TAC THEN  
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN
  PROPER_TYPE_TAC(`a1:epsilon`) THEN
  IS_EXPR_TYPE_TAC THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `a1:epsilon` thm3) THEN 
  REWRITE_TAC[sub_a1_thm;ASSUME `proper_nat_construct a1`] THEN
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN 
  REWRITE_TAC[sym_add;carry_one]
  ]
  ]
  ;CONJ_TAC THENL
  [(* isApp y *)
  REPEAT GEN_TAC THEN 
  REWRITE_TAC[y_case1_sub;y_case2_sub;y_quoapp_app_sub;IMP_CONJ] THEN
  DISCH_TAC THEN 
  DISCH_TAC THEN 
  REWRITE_TAC[proper_nat_construct] THEN 
  REWRITE_TAC[IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  TOP_DISJ_CASES_TAC THEN 
  BOTTOM_DISJ_CASES_TAC THEN
  ASM_REWRITE_TAC[add_ebin] THENL
  [MP_TAC(APP_DISQUO 
    `QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `(add_ebin a1 b1):epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `a1:epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `b1:epsilon`) THEN 
  PROPER_TYPE_TAC(`a1:epsilon`) THEN 
  PROPER_TYPE_TAC(`b1:epsilon`) THEN 
  MP_TAC(SPECL [`a1:epsilon`;`b1:epsilon`] thm1) THEN 
  REWRITE_TAC[
    ASSUME `proper_nat_construct a1`;
    ASSUME `proper_nat_construct b1`] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  IS_EXPR_TYPE_TAC THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN
  CONSTRUCTION_TO_QUOTE_TAC THEN
  LAW_OF_DISQUO_TAC THEN 
  MP_TAC(SPEC `b1:epsilon` (ASSUME `!y. proper_nat_construct a1
  ==> proper_nat_construct y
  ==> (eval (add_ebin a1 y) to (nat)) =
  add_unary (eval (a1) to (nat)) (eval (y) to (nat))`)) THEN 
  REWRITE_TAC[
    y_quoapp_case1_sub;
    ASSUME `proper_nat_construct a1`;
    ASSUME `proper_nat_construct b1`] THEN
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[add_even]
  ;MP_TAC(APP_DISQUO 
    `QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `a1:epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `b1:epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `(add_ebin a1 b1):epsilon`) THEN 
  PROPER_TYPE_TAC(`a1:epsilon`) THEN 
  PROPER_TYPE_TAC(`b1:epsilon`) THEN 
  MP_TAC(SPECL [`a1:epsilon`;`b1:epsilon`] thm1) THEN 
  REWRITE_TAC[
    ASSUME `proper_nat_construct a1`;
    ASSUME `proper_nat_construct b1`] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  IS_EXPR_TYPE_TAC THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN
  CONSTRUCTION_TO_QUOTE_TAC THEN
  LAW_OF_DISQUO_TAC THEN 
  MP_TAC(SPEC `b1:epsilon` (ASSUME 
    `!y. proper_nat_construct a1
    ==> proper_nat_construct y
    ==> (eval (add_ebin a1 y) to (nat)) =
    add_unary (eval (a1) to (nat)) (eval (y) to (nat))`)) THEN 
  REWRITE_TAC[
    y_quoapp_case1_sub;
    ASSUME `proper_nat_construct a1`;
    ASSUME `proper_nat_construct b1`] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[add_even_odd]
  ;MP_TAC(APP_DISQUO 
    `QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `a1:epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `b1:epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `(add_ebin a1 b1):epsilon`) THEN 
  PROPER_TYPE_TAC(`a1:epsilon`) THEN 
  PROPER_TYPE_TAC(`b1:epsilon`) THEN 
  MP_TAC(SPECL [`a1:epsilon`;`b1:epsilon`] thm1) THEN 
  REWRITE_TAC[
    ASSUME `proper_nat_construct a1`;
    ASSUME `proper_nat_construct b1`] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  IS_EXPR_TYPE_TAC THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN
  CONSTRUCTION_TO_QUOTE_TAC THEN
  LAW_OF_DISQUO_TAC THEN 
  MP_TAC(SPEC `b1:epsilon` (ASSUME 
    `!y. proper_nat_construct a1
    ==> proper_nat_construct y
    ==> (eval (add_ebin a1 y) to (nat)) =
    add_unary (eval (a1) to (nat)) (eval (y) to (nat))`)) THEN 
  REWRITE_TAC[
    y_quoapp_case1_sub;
    ASSUME `proper_nat_construct a1`;
    ASSUME `proper_nat_construct b1`] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[add_odd_even]
  ;MP_TAC(APP_DISQUO 
    `QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `a1:epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `b1:epsilon`) THEN 
  MP_TAC(APP_DISQUO 
    `QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))` 
    `(add_ebin (QuoConst "One" (TyBase "nat")) (add_ebin a1 b1)):epsilon`) THEN 
  PROPER_TYPE_TAC(`a1:epsilon`) THEN 
  PROPER_TYPE_TAC(`b1:epsilon`) THEN 
  MP_TAC(SPECL [`a1:epsilon`;`b1:epsilon`] thm1) THEN 
  REWRITE_TAC[
    ASSUME `proper_nat_construct a1`;
    ASSUME `proper_nat_construct b1`] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`a1:epsilon`;`b1:epsilon`] lemma6) THEN  
  REWRITE_TAC[
    ASSUME `proper_nat_construct a1`;
    ASSUME `proper_nat_construct b1`] THEN 
  DISCH_TAC THEN 
  MP_TAC(SPECL [
    `(QuoConst "One" (TyBase "nat")):epsilon`;
    `(add_ebin a1 b1):epsilon`] thm1) THEN 
  REWRITE_TAC[
    ASSUME `proper_nat_construct (add_ebin a1 b1)`;
    proper_nat_construct] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  IS_EXPR_TYPE_TAC THEN 
  REPEAT DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN
  CONSTRUCTION_TO_QUOTE_TAC THEN
  LAW_OF_DISQUO_TAC THEN  
  ASM_REWRITE_TAC[add_odd_even] THEN 
  QUOTE_TO_CONSTRUCTION_TAC THEN 
  MP_TAC(SPEC `(add_ebin a1 b1)` thm3) THEN 
  ASM_REWRITE_TAC[] THEN 
  MP_TAC(fin_x_sub) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  MP_TAC(SPEC `b1:epsilon` (ASSUME 
    `!y. proper_nat_construct a1
    ==> proper_nat_construct y
    ==> (eval (add_ebin a1 y) to (nat)) =
    add_unary (eval (a1) to (nat)) (eval (y) to (nat))`)) THEN 
  REWRITE_TAC[
    y_quoapp_case1_sub;
    ASSUME `proper_nat_construct a1`;
    ASSUME `proper_nat_construct b1`] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  MP_TAC(SYM(SPEC 
    `add_unary (eval (a1:epsilon) to (nat)) (eval (b1:epsilon) to (nat))` 
    carry_one)) THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  REWRITE_TAC[add_even_odd;one_def;take_s;id_of_plus] THEN
  REWRITE_TAC[put_s;add_one_even] 
  ]
  ;REWRITE_TAC[proper_nat_construct]
  ]
  ]
  ]
  ;REWRITE_TAC[proper_nat_construct]
  ]
  ]
  ]
  );;




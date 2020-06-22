(*Testing a few proofs to make sure this definition works*)

(*Trivial proof that x is effecitve in x + 3*)
prove(effectiveIn `x:num` `x + 3`,
	EXISTS_TAC `x + 1` THEN
	BETA_TAC THEN
	ARITH_TAC
);;

(*Trivial proof that x is not effective in x = x*)
prove(mk_neg (effectiveIn `x:bool` `x <=> x`),
	REWRITE_TAC[REFL `x`]
);; 

(*Helper lemmas for proving disquotation*)
let appsplitexpr = prove(`isExpr (App a0 a1) ==> isExpr a0 /\ isExpr a1`,
	MESON_TAC[isExpr]
);;

(*Attempting to define size of recursion to prove recursion is wellfounded*)
(*Fails to define because recursion is not proven to be well founded*)
let sizeOfQuo = define `
(sizeOfQuo (QuoConst s t) = 1) /\
(sizeOfQuo (QuoVar s t) = 1) /\ 
(sizeOfQuo (Abs a b) = sizeOfQuo a + sizeOfQuo b + 1) /\
(sizeOfQuo (App a b) = sizeOfQuo a + sizeOfQuo b + 1) /\
(sizeOfQuo (Quo a) = sizeOfQuo a + 1)
`;;


(*Definition of peano for inductive proof*)

let isPeano = define `
(isPeano (QuoConst "!" (TyBiCons "fun" (TyBiCons "fun" ty (TyBase "bool")) (TyBase "bool"))) = T) /\
(isPeano (QuoConst "?" (TyBiCons "fun" (TyBiCons "fun" ty (TyBase "bool")) (TyBase "bool"))) = T) /\
(isPeano (QuoConst "/\\" (TyBiCons "fun" (TyBase "bool") (TyBiCons "fun" (TyBase "bool") (TyBase "bool")))) = T) /\
(isPeano (QuoConst "\\/" (TyBiCons "fun" (TyBase "bool") (TyBiCons "fun" (TyBase "bool") (TyBase "bool")))) = T) /\
(isPeano (QuoConst "==>" (TyBiCons "fun" (TyBase "bool") (TyBiCons "fun" (TyBase "bool") (TyBase "bool")))) = T) /\
(isPeano (QuoConst "=" (TyBiCons "fun" ty (TyBiCons "fun" ty (TyBase "bool")))) = T) /\
(isPeano (QuoConst "<=>" (TyBiCons "fun" ty (TyBiCons "fun" ty (TyBase "bool")))) = T) /\
(isPeano (QuoConst "~" (TyBiCons "fun" (TyBase "bool") (TyBase "bool"))) = T) /\
(isPeano (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) = T) /\
(isPeano (QuoVar str ty) = T) /\
(isPeano (Abs a b) = (isPeano a /\ isPeano b)) /\
(isPeano (QuoConst "*" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) = T) /\
//HOL does not do greedy pattern matching, need to detect numbers like this
(isPeano (App a b) = 
	//Check is this is a number
	if a = (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) then
	  //Check that b is 1
	  (b = (App (QuoConst "BIT1" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num"))) 
	  	//or 0
	  	\/ b = (QuoConst "_0" (TyBase "num")))
	else
	//This is not a number, check that the function and it's argument are Peano arithemtic
	(isPeano a /\ isPeano b))
`;;

(*Function to take a term and turn it into a quoted form, then preface it with isPeano*)
let genIsPeano tm = mk_comb(`isPeano`,rhs (concl(TERM_TO_CONSTRUCTION_CONV (mk_quote tm))));;

prove(genIsPeano `0 + 1 = 0`,
REWRITE_TAC[isPeano;COND_ELIM_THM;epsilonDistinct;epsilonInjective;] THEN
STRING_FETCH_TAC THEN
REWRITE_TAC[]);;

prove(genIsPeano `0 + 1 = 1 ==> 1 = 0 <=> (1 = 1) /\ (0 = 0)`,
REWRITE_TAC[isPeano;COND_ELIM_THM;epsilonDistinct;epsilonInjective;] THEN
STRING_FETCH_TAC THEN
REWRITE_TAC[]);;

prove(genIsPeano `0 + 1 = 1 ==> 1 = 0 <=> (1 = 1) \/ (0 = 0)`,
REWRITE_TAC[isPeano;COND_ELIM_THM;epsilonDistinct;epsilonInjective;] THEN
STRING_FETCH_TAC THEN
REWRITE_TAC[]);;

prove(genIsPeano `0 + 1 = 1 ==> 1 = 0 <=> (1 = 1) \/ (0 = 0)`,
REWRITE_TAC[isPeano;COND_ELIM_THM;epsilonDistinct;epsilonInjective;] THEN
STRING_FETCH_TAC THEN
REWRITE_TAC[]);;

prove(genIsPeano `!x. x = 1  ==> (x = 0 \/ x = 1)`,
REWRITE_TAC[isPeano;COND_ELIM_THM;epsilonDistinct;epsilonInjective;] THEN
STRING_FETCH_TAC THEN
REWRITE_TAC[isPeano]);;

prove(genIsPeano `?x. x = 1  ==> (x = 0 \/ x = 1)`,
REWRITE_TAC[isPeano;COND_ELIM_THM;epsilonDistinct;epsilonInjective;] THEN
STRING_FETCH_TAC THEN
REWRITE_TAC[isPeano]);;

prove(genIsPeano `!x. (x + 1 * 1 = 1) ==> x = 0`,
REWRITE_TAC[isPeano;COND_ELIM_THM;epsilonDistinct;epsilonInjective;] THEN
STRING_FETCH_TAC THEN
REWRITE_TAC[isPeano]);;

prove(genIsPeano `!x. (x + 1 * 1 = 1) ==> ~(x = 0)`,
REWRITE_TAC[isPeano;COND_ELIM_THM;epsilonDistinct;epsilonInjective;] THEN
STRING_FETCH_TAC THEN
REWRITE_TAC[isPeano]);;

(* Specialize instance of induction on the natural numbers *)
let indinst = SPEC `P:num->bool` num_INDUCTION;;

(* Perform instantiation on indinst to get instantiated theorem *)
INST [`eval (f:epsilon) to (num->bool)`,`P:num->bool`] indinst;;

(* Induction schema for Peano arithmetic *)
let peanoIndSchema1 = `!f:epsilon. (isExprType (f:epsilon) (TyBiCons "fun" (TyBase "num") (TyBase "bool"))) /\ ~(isFreeIn (QuoVar "n" (TyBase "num")) (f:epsilon)) /\ (isPeano f) ==> (eval (f:epsilon) to (num->bool)) 0 /\ (!) ((\P:(num->bool) n:num. P n ==> P (SUC n)) (eval (f) to (num->bool))) ==> (!) ((\P n:num. P n) (eval (f) to (num->bool)))`;;

let peanoIndSchema1_thm = prove(peanoIndSchema1,
GEN_TAC THEN
DISCH_TAC THEN
REWRITE_TAC[INST [`eval (f:epsilon) to (num->bool)`,`P:num->bool`] indinst]
);;

(* Perform instantiation on peanoIndSchema1 to get instantiated induction schema *)
let peanoIndSchema1Body = SPEC `f:epsilon` peanoIndSchema1_thm;;
let peanoIndSchema1Inst = 
  INST [`Q_ \x:num . x + 1 = 1 + x _Q`,`f:epsilon`] peanoIndSchema1Body;;

(* Better, but harder to prove, induction schema for Peano arithmetic *)
let peanoIndSchema2 = `!f:epsilon. (isExprType (f:epsilon) (TyBiCons "fun" (TyBase "num") (TyBase "bool"))) /\ ~(isFreeIn (QuoVar "n" (TyBase "num")) (f:epsilon)) /\ (isPeano f) ==> (eval (f:epsilon) to (num->bool)) 0 /\ (!n:num. (eval (f:epsilon) to (num->bool)) n ==> (eval (f:epsilon) to (num->bool)) (SUC n)) ==> (!n:num. (eval (f:epsilon) to (num->bool)) n)`;;


(*PROOF OF THE SCHEMA*)
let peanoInd_forall_thm = (REWRITE_CONV[FORALL_DEF] THENC BETA_CONV THENC (ONCE_DEPTH_CONV BETA_CONV)) peanoIndSchema1;;
let peanoInd_forall = rhs (concl (peanoInd_forall_thm));;

(*Currently the abstractions are doubled up, to continue we need to seperate them so we can beta reduce. Axiom B13 does this*)
let first_B13 = BETA_REDUCE_ABS `P:(num->bool)` `x:(num->bool)` `n:num` `y:num` `(eval (f:epsilon) to (num->bool))` `(P:num->bool) (n:num) ==> (P:num->bool) (SUC (n:num))`;;
let second_B13 = BETA_REDUCE_ABS `P:(num->bool)` `x:(num->bool)` `n:num` `y:num` `(eval (f:epsilon) to (num->bool))` `(P:num->bool) (n:num)`;;

(*In order to use b13, we need to prove one of the two disjunct antecedents, the one that we can prove easily is 
		(!y. (\n. (eval (f) to (num->bool))) y = (eval (f) to (num->bool)))
	which will be proven using axiom B11.2, which moves abstraction inside the evaluation.
*)

let b11_2 = BETA_REDUCE_EVAL `n:num`  `y:num` `f:epsilon` `:(num->bool)`;;
(*For use in the proof, we need the assumptions to be seperated, which is done with the following tautology:*)
let AND_IMP_EQUIV = TAUT `a /\ b ==> x <=> a ==> b ==> x`;;
(*This step also reduces ( (\n. f) y ) to just f*)
let b11_2_reduced = UNDISCH_ALL (EQ_MP (REWRITE_CONV[AND_IMP_EQUIV] (concl b11_2)) b11_2);;
let b11_2_disch_forall = GEN `y:num` b11_2_reduced;;
(*Antecedent of axiom b13*)
let first_B13_antes = DISJ1 b11_2_disch_forall `(!x. (\P. P n ==> P (SUC n)) x <=> P n ==> P (SUC n))`;;
let first_b13_complete = SYM (MP first_B13 first_B13_antes);;

let second_B13_antes = DISJ1 b11_2_disch_forall `(!x:(num->bool). (\P:(num->bool). P n) x <=> P n)`;;
let second_b13_complete = SYM (MP second_B13 second_B13_antes);;

(*For the proof, we also have to seperate the eval f outside of the induction statement, in both cases*)
let beta_eval_suc = SYM (BETA_CONV `(\P:(num->bool). P n ==> P (SUC n)) (eval (f:epsilon) to (num->bool))`);;
let beta_eval = SYM (BETA_CONV `(\P:(num->bool). P n) (eval (f:epsilon) to (num->bool))`);;

(*Now we simply apply all these equivalences, and then finish the proof using the previously proven peanoIndSchema1_thm.*)
(*Attempted Proof*)
let peanoIndSchema2_thm = prove(peanoIndSchema2, 
	STRIP_TAC THEN STRIP_TAC THEN
	REWRITE_TAC[beta_eval_suc] THEN
	REWRITE_TAC[beta_eval] THEN
	REWRITE_TAC[FORALL_DEF] THEN
	REWRITE_TAC[first_b13_complete;second_b13_complete] THEN
	REWRITE_TAC[SYM FORALL_DEF] THEN
	UNDISCH_TAC `isPeano f` THEN UNDISCH_TAC `~isFreeIn (QuoVar "n" (TyBase "num")) f` THEN
	ONCE_REWRITE_TAC[SYM AND_IMP_EQUIV] THEN
	UNDISCH_TAC `isExprType f (TyBiCons "fun" (TyBase "num") (TyBase "bool"))` THEN
	ONCE_REWRITE_TAC[SYM AND_IMP_EQUIV] THEN
	REWRITE_TAC[SPEC `f:epsilon` peanoIndSchema1_thm]
);;

let peanoIndSchema2Inst = 
  vsubst [`Q_ \x:num . x + 1 = 1 + x _Q`,`f:epsilon`] (snd (dest_forall peanoIndSchema2));;


(* OLD FAULTY THEOREM

let peanoInduction = prove(`!f:epsilon. (isExprType (f:epsilon) (TyBiCons "fun" (TyVar "num") (TyBase "bool"))) /\ (isPeano f) ==> (eval (f:epsilon) to (num->bool)) 0 /\ (!n:num. (eval (f:epsilon) to (num->bool)) n ==> (eval (f:epsilon) to (num->bool)) (SUC n)) ==> (!n:num. (eval (f:epsilon) to (num->bool)) n)`,
	GEN_TAC THEN
	DISCH_TAC THEN
	REWRITE_TAC[INST [`eval (f:epsilon) to (num->bool)`,`P:num->bool`] indinst]
);;

*)
(*Similair to the tests for epsilon, this will prove a few theoremms to verify that _Q_ and Q_ _Q work as intended, along with a few tests with OCaml functions to ensure the Quote term is working correctly*)

(*This tests that quotations are correctly converted to epsilon terms*)
prove(`Q_ (x + 3) _Q = (App (App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) (QuoVar "x" (TyBase "num")))
    (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num")))
   (App (QuoConst "BIT1" (TyBiCons "fun" (TyBase "num") (TyBase "num")))
   (App (QuoConst "BIT1" (TyBiCons "fun" (TyBase "num") (TyBase "num")))
   (QuoConst "_0" (TyBase "num"))))))`,
TERM_TO_CONSTRUCTION_TAC THEN
REFL_TAC
);;

(*These tests ensure that OCaml functions behave correctly when dealing with quotations*)

(*Also testing substitutions into TERM_TO_CONSTRUCTION*)
assert ((concl (SUBS [ASSUME `x = 2`] (TERM_TO_CONSTRUCTION  `Q_ x + 3 _Q`))) = concl (TERM_TO_CONSTRUCTION `Q_ x + 3 _Q`));;

(*Instantiation should also not do anything to a quotation*)
assert ((concl (INST [`2`,`x:num`] (TERM_TO_CONSTRUCTION  `Q_ x + 3 _Q`))) = concl (TERM_TO_CONSTRUCTION `Q_ x + 3 _Q`));;

(*The above theorems were for substituting into proven theorems, these ones will test the respective operations on terms*)
(*Epsilon terms will not appear here as they have no variables that it is possible to substitute into
*)
assert (subst [`2`,`x:num`] (`Q_ x + 3 _Q`) = `Q_ x + 3 _Q`);;

(*It is possible to instantiate into type variables, this also should not be allowed to happen in quoted terms*)

assert (inst [`:num`,`:A`] (`Q_ (x:A) _Q`) = `Q_ (x:A) _Q`);;

(*Tests that hole terms can be created*)
`Q_ H_ Q_ x + 3 _Q _H _Q`;;

(*Tests that hole terms not of type epsilon cannot be created*)
try `Q_ H_ x + 3 _H _Q` with Failure _ -> `HOLE_EPSILON_TEST_SUCCESS:unit`;;

(*Tests that holes can be created and combined with non-hole terms*)
`Q_ H_ Q_ x + 3 _Q _H + 2 _Q`;

(*Tests that mistypes are still not allowed*)
try `Q_ H_ Q_ x + 3 _Q _H /\ T _Q` with Failure _ -> `HOLE_MISTYPE_TEST_SUCCESS:unit`;;

(*For testing, defines a function that takes an integer and recursively adds quotations until n is 0*)
let testFun = define `
    (testFun 0 = Q_ 0 _Q) /\
    (testFun (n + 1) = (Q_ H_ testFun(n) _H _Q))
`;;

let testFun2 = define `
    (testFun2 0 = Q_ 0 _Q) /\
    (testFun2 (n + 1) = (Q_ 2 + H_ testFun2(n) _H _Q))`;;

(*Combinator to make recursive proofs cleaner, works when a function takes one natural number argument*)
let rec genRecursiveProof def fname step num stop = 
	if num < 0 then failwith "Non-stop recursion" else 
	let genfun = mk_comb(mk_const(fname,[]),mk_numeral (Int num)) in
	if num > stop then
	let subone = mk_comb(mk_const(fname,[]),mk_comb(mk_comb(mk_const("+",[]),mk_numeral (Int (num - 1))),mk_numeral(Int(1)))) in
	REWRITE_TAC[REWRITE_CONV[ARITH_RULE (mk_eq (genfun,subone))] genfun] THEN
	REWRITE_TAC[def] THEN
	(genRecursiveProof def fname step (num-step) stop)
    else
    if num = stop then
	REWRITE_TAC[def]
    else
    failwith "Step overshoots stopping point";;


(*This tests that unquote tactics work even on long winded recursive functions*)
prove(`testFun 10 = Q_ 0 _Q`,
    (genRecursiveProof testFun "testFun" 1 10 0) THEN
    REPEAT UNQUOTE_TAC THEN
    REFL_TAC
);;

prove(`testFun2 10 = Q_ 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 0 _Q`,
    (genRecursiveProof testFun2 "testFun2" 1 10 0) THEN
    REPEAT UNQUOTE_TAC THEN
    REFL_TAC
);;

(*This tests that STRING_FETCH_TAC works as it should*)
(*Bottom rewrite tac is necessary because string_fetch_tac will evaluate to ~(F \/ F \/ F \/ F etc...),
basic rewrites needed to simplify this to just ~(F)*)
prove(`~(isValidConstName "NotAConstantName")`,
	REWRITE_TAC[EX;isValidConstName] THEN
	STRING_FETCH_TAC THEN
	REWRITE_TAC[]
);;

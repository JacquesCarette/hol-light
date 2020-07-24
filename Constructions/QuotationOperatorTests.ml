needs "Constructions/QuotationTactics.ml";;
(*Similar to the tests for epsilon, this will prove a few theorems to verify that _Q_ and Q_ _Q work as intended, along with a few tests with OCaml functions to ensure the Quote term is working correctly*)

(*This tests that quotations are correctly converted to epsilon terms*)
prove(
`Q_ (x + 3) _Q = (App (App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) (QuoVar "x" (TyBase "num")))
(App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num")))
(App (QuoConst "BIT1" (TyBiCons "fun" (TyBase "num") (TyBase "num")))
(App (QuoConst "BIT1" (TyBiCons "fun" (TyBase "num") (TyBase "num")))
(QuoConst "_0" (TyBase "num"))))))`,
QUOTE_TO_CONSTRUCTION_TAC THEN
REFL_TAC
);;

(*These tests ensure that OCaml functions behave correctly when dealing with quotations*)

(*Also testing substitutions into QUOTE_TO_CONSTRUCTION*)
assert ((concl (SUBS [ASSUME `x = 2`] (QUOTE_TO_CONSTRUCTION_CONV  `Q_ x + 3 _Q`))) = concl (QUOTE_TO_CONSTRUCTION_CONV `Q_ x + 3 _Q`));;

(*Instantiation should also not do anything to a quotation*)
assert ((concl (INST [`2`,`x:num`] (QUOTE_TO_CONSTRUCTION_CONV  `Q_ x + 3 _Q`))) = concl (QUOTE_TO_CONSTRUCTION_CONV `Q_ x + 3 _Q`));;

(*The above theorems were for substituting into proven theorems, these ones will test the respective operations on terms*)
(*Epsilon terms will not appear here as they have no variables that it is possible to substitute into
*)
assert (subst [`2`,`x:num`] (`Q_ x + 3 _Q`) = `Q_ x + 3 _Q`);;

(*It is possible to instantiate into type variables, this also should not be allowed to happen in quoted terms*)

assert (inst [`:num`,`:A`] (`Q_ (x:A) _Q`) = `Q_ (x:A) _Q`);;

(*Tests that hole terms can be created*)
`Q_ H_ Q_ x + 3 _Q _H of num _Q`;;

(*Tests that hole terms not of type epsilon cannot be created*)
try `Q_ H_ x + 3 _H of num _Q` with Failure _ -> `HOLE_EPSILON_TEST_SUCCESS:unit`;;

(*Tests that holes can be created and combined with non-hole terms*)
`Q_ H_ Q_ x + 3 _Q _H of num + 2 _Q`;

(*Tests that mistypes are still not allowed*)
try `Q_ H_ Q_ x + 3 _Q _H of num /\ T _Q` with Failure _ -> `HOLE_MISTYPE_TEST_SUCCESS:unit`;;

(*For testing, defines a function that takes an integer and recursively adds quotations until n is 0*)
let testFun = define `
    (testFun 0 = Q_ Q_ _0 _Q  _Q) /\
    (testFun (n + 1) = (Q_ testFun(n) _Q))`;;

let testFun2 = define `
    (testFun2 0 = Quo(QuoConst "_0" (TyBase "num"))) /\
    (testFun2 (n + 1) = Quo(testFun2(n)))`;;


(*This tests that Construction -> Quote tactics work*)
prove(`eval testFun 0 to epsilon = eval testFun2 0 to epsilon`,
REWRITE_TAC[testFun; testFun2] THEN 
CONSTRUCTION_TO_QUOTE_TAC THEN 
REFL_TAC
);;


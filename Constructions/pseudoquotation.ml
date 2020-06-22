(*Helper functions to make vital functions more readable*)
let makeGenericComb constName firstArg secondArg = mk_comb(mk_comb(mk_const(constName,[]),firstArg),secondArg);;
let makeQuoVarComb a b = makeGenericComb "QuoVar" (mk_string a) b;;
let makeQuoConstComb a b = makeGenericComb "QuoConst" (mk_string a) b;;
let makeAppComb a b = makeGenericComb "App" a b;;
let makeAbsComb a b = makeGenericComb "Abs" a b;;
let makeTyVarComb a = mk_comb(mk_const("TyVar",[]),mk_var((string_of_type a),mk_type("list",[`:char`])));;
let makeTyBaseComb a  = mk_comb(mk_const("TyBase",[]),(mk_string a));;
let makeTyMonoConsComb a b = makeGenericComb "TyMonoCons" (mk_string a) b;;
let makeTyBiConsComb a b c= mk_comb((makeGenericComb "TyBiCons" (mk_string a) b),c);;
let makeFunComb a b = makeTyBiConsComb "fun" a b;;
let makeQuoComb a = mk_comb(mk_const("Quo",[]),a);;

(*Converts HOL's types into the types defined inside the 'type' type*)
let rec matchTypes hType = 

	(*Cannot call dest_type on a variable type, so this must be checked and explicitly handled before getting to the main pattern matcher*)
	if (is_vartype hType) then makeTyVarComb hType else
	let a,b = (dest_type hType) in
	match length b with
	| 0 -> makeTyBaseComb(a)
	| 1 -> makeTyMonoConsComb a (matchTypes (hd b))
	| 2 -> makeTyBiConsComb a (matchTypes (hd b)) (matchTypes (hd (tl b)))
	| _ -> failwith "This is not a valid type";;

(*Function to actually handle conversion*)
let rec quoteRecursion = function
	| Var (vName, vType) -> makeQuoVarComb vName (matchTypes vType)
	| Const (cName, cType) -> makeQuoConstComb cName (matchTypes cType)
	| Comb(E1,E2) -> makeAppComb (quoteRecursion E1) (quoteRecursion E2)
	| Abs(E1, E2) -> makeAbsComb (quoteRecursion E1) (quoteRecursion E2)
	| Quote(E,T) -> makeQuoComb (quoteRecursion E);;

(*Function to take an expression, and convert it into a type of epsilon wrapped inside of a Quote*)
let quote a = makeQuoComb (quoteRecursion a);;


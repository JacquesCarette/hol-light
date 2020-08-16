(*Distinctness operator can do what strings were implemented to do: Prove that different types of terms and types are unequal*)
let typeDistinct = distinctness "type";;
let epsilonDistinct = distinctness "epsilon";; 
(*These two theorems say that for any elements of type or epsilon to be equal, their arguments must be equal*)
let typeInjective = injectivity "type";;
let epsilonInjective = injectivity "epsilon";;

(*** Function Definitions ***)
(*Mathematical function that can be used to inspect terms inside epsilon*)
(*This needs to be kept until I can find a way to make this function return just the raw function - type checker currently disallows it*)
let ep_constructor = define 
`(ep_constructor (QuoVar str ty) = "QuoVar") /\
 (ep_constructor (QuoConst str ty) = "QuoConst") /\
 (ep_constructor (Abs eps eps2) = "Abs") /\
 (ep_constructor (App eps eps2) = "App") /\
 (ep_constructor (Quo eps) = "Quo")`;;

 (*This function returns true if the given expression f appears free anywhere in e*)
(*Regarding abstractions: I assume that the structure of an abstraction will contain the variable to
bind on the left and expression on the right, therefore for a variable to be free in an abstraction it
must appear in the right while not appearing free in the left.*)
let isFreeIn = define
`(isFreeIn (QuoVar n1 t1) (QuoVar n2 t2) = (n1 = n2 /\ t1 = t2)) /\
 (isFreeIn qv (QuoConst str ty) = F) /\ 
 (isFreeIn qv (App eps eps2) = ((isFreeIn qv eps) \/ (isFreeIn qv eps2))) /\
 (isFreeIn qv (Abs eps eps2) = (~(isFreeIn qv eps) /\ (isFreeIn qv eps2))) /\
 (isFreeIn qv (Quo eps) = F)`;; 

 (*Mathematical function to inspect a member of epsilon's type*)
let ep_type = define
`(ep_type (QuoVar str ty) = (ty)) /\	
 (ep_type (QuoConst str ty) = (ty)) /\
 (ep_type (Quo eps) = (TyBase "epsilon"))`;;

(*This function takes a Fun type and takes off the first part of it - for use in calculating types of Abs/App*)
let stripFunc = define `stripFunc (TyBiCons "fun" T1 T2) = T2`

(*This function takes a function type and returns the first part of it*)
let headFunc = define `headFunc (TyBiCons "fun" T1 T2) = T1`;;

(*This function handles calculating the type of App and Abs expressions, necessary to handle function applications*)
(*Assuming that function will always be on left*)
let combinatoryType = define
`combinatoryType (App e1 e2) = (stripFunc (combinatoryType e1)) /\
combinatoryType (QuoConst str ty) = ty /\
combinatoryType (Abs (QuoVar str ty) e2) = (TyBiCons "fun" ty (combinatoryType e2)) /\
combinatoryType (QuoVar str ty) = ty /\
combinatoryType (Quo e) = TyBase "epsilon"`;;

(*Mathematical definition of what constitutes a variable*)
let isVar = define `isVar e = ((ep_constructor e) = "QuoVar")`;;

(*Mathematical definition of what constitutes a constant*)
let isConst = define `isConst e = ((ep_constructor e) = "QuoConst")`;;

(*Mathematical definition of what constitutes an abstraction*)
let isAbs = define `isAbs e = ((ep_constructor e) = "Abs")`;;

(*Mathematical definition of what constitutes an application*)
let isApp = define `isApp e = ((ep_constructor e) = "App")`;;

(*Mathematical definition of what constitutes a quotation*)
let isQuo = define `isQuo e = ((ep_constructor e) = "Quo")`;;

(*Checks if a given type is a function using a much cleaner method*)
let isFunction = define `
  (isFunction (TyVar str) = F) /\
  (isFunction (TyBase str) = F) /\
  (isFunction (TyMonoCons str ty) = F) /\
  (isFunction (TyBiCons str ty1 ty2) = (str = "fun"))`;; 

(*This function will take a variable term, and another term of type epsilon, and return whether or not the types mismatch. If the term is not found, false is returned.
i.e. true means that two variables of the same name but different types exist inside these terms*)
let typeMismatch = define `
(typeMismatch (QuoVar name ty) (QuoVar name2 ty2) = (name = name2 /\ ~(ty = ty2))) /\
(typeMismatch (QuoVar name ty) (QuoConst name2 ty2) = F) /\ 
(typeMismatch (QuoVar name ty) (App e1 e2) = ((typeMismatch (QuoVar name ty) e1) \/ (typeMismatch (QuoVar name ty) e2))) /\
(typeMismatch (QuoVar name ty) (Abs e1 e2) = ((typeMismatch (QuoVar name ty) e1) \/ (typeMismatch (QuoVar name ty) e2))) /\
(typeMismatch (QuoVar name ty) (Quo e) = (typeMismatch (QuoVar name ty) e))`;;

(*Checks soley if the construction represents a *possible* well-typed term*)
let isExpr = define 
`
	(isExpr (QuoVar str ty) = T) /\
	(isExpr (QuoConst str ty) = T) /\
	(isExpr (App e1 e2) = (((isConst e1) \/ (isApp e1) \/ (isAbs e1)) /\ (((headFunc (combinatoryType e1))) = (((combinatoryType e2)))) /\ (isFunction (combinatoryType e1)) /\ (isExpr e2) /\ (isExpr e1)))  /\
	(isExpr (Abs e1 e2) = ((isVar e1) /\ ~(typeMismatch e1 e2) /\ (isExpr e2) /\ (isExpr e1))) /\ 
	(isExpr (Quo e) = T) 
`;;
	
(*Mathematical definition for isVarType *)
let isVarType = define `isVarType e t = ((isVar e) /\ (t = (ep_type e)))`;;

(*Mathematical definition for isConstType*)
let isConstType = define `isConstType e t = ((isConst e) /\ (t = (ep_type e)))`;;

(*Mathematical definition of isExprType*)
let isExprType = define `isExprType e t = ((isExpr e) /\ (combinatoryType e = t))`;;

(*This is a sub part of the "is proper subexpression of" definition - it checks if the given first term appears anywhere inside the second *)
let isPartOf = define `
isPartOf (exp:epsilon) (QuoVar str ty) = (exp = (QuoVar str ty)) /\
isPartOf (exp:epsilon) (QuoConst str ty) = (exp = (QuoConst str ty)) /\
isPartOf (exp:epsilon) (App exp1 exp2) = ((isPartOf exp exp1) \/ (isPartOf exp exp2) \/ (exp = (App exp1 exp2))) /\
isPartOf (exp:epsilon) (Abs exp1 exp2) = ((isPartOf exp exp1) \/ (isPartOf exp exp2) \/ (exp = (Abs exp1 exp2))) /\
isPartOf (exp:epsilon) (Quo exp1) = ((isPartOf exp exp1) \/ (exp = (Quo exp1))) 
`;;

(*This defines the check to see if something is a proper subexpression of another expression*)
let isProperSubexpressionOf = define `isProperSubexpressionOf (exp1:epsilon) (exp2:epsilon) = ((isExpr exp1) /\ (isPartOf exp1 exp2))`;;

(*Definition of abstraction*)
(*This cannot be nammed because abs is already reserved by absolute value, so this is now e_abs for epsilon_abs*)
let e_abs = define `e_abs e1 e2 = Abs e1 e2`;;

(*Definition of application*)
let app = define `app e1 e2 = App e1 e2`;;

(*Definition of quo for epsilon types*)
let quo = define `quo eps = Quo eps`;;

(*Comparison to see if two types are equal*)
let eqTypes = define `eqTypes t1 t2 = (t1 = t2)`;;

(*Checks that a term is a valid construction*)
let isConstruction = define `
(isConstruction (QuoVar str ty) = T) /\ 
(isConstruction (QuoConst str ty) = T) /\
(isConstruction (App exp1 exp2) = ((isConstruction exp1) /\ (isConstruction (exp2)))) /\
(isConstruction (Abs exp1 exp2) = ((isConstruction exp1) /\ (isConstruction exp2))) /\
(isConstruction (Quo exp1) = (isConstruction exp1)) 
`;;

(*In-logic quotation theorems for constructions*)
let appQuo = new_axiom `quo (app a0 a1) = app (quo a0) (quo a1)`;;
let absQuo = new_axiom `quo (e_abs a0 a1) = e_abs (quo a0) (quo a1)`;;

(*** PROOFS FOR TESTING ***)
(*Proof that a variable not inside an expression is not free in that expression*)
prove(`isFreeIn (QuoVar "x" (TyBase "bool")) (QuoVar "y" (TyBase "bool")) <=> F`,
	REWRITE_TAC[isFreeIn] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"x" = "y"`)]
);;

(*Proof that a variable is free if the entire expression is just that variable*)
prove(`isFreeIn (QuoVar "x" (TyBase "bool")) (QuoVar "x" (TyBase "bool"))`,
	REWRITE_TAC[isFreeIn]
);;

(*Proof that a variable cannot be free inside a constant even if the names match*)
prove(`isFreeIn (QuoVar "x" (TyBase "bool")) (QuoConst "x" (TyBase "bool")) <=> F`,
	REWRITE_TAC[isFreeIn]
);;

(*Proof that a variable inside an application can be free*)
prove(`isFreeIn (QuoVar "x" (TyBase "real")) (App (App (QuoVar "x" (TyBase "real")) (QuoConst "+" (TyBiCons "fun" (TyBase "real") (TyBiCons "fun" (TyBase "real") (TyBase "real"))))) (QuoVar "y" (TyBase "real")))`,
	REWRITE_TAC[isFreeIn]
);;

(*Prove that a mistyped variable in an otherwise free context is not free
(Mathematically a mistyped variable makes no sense, this is just meant to test that typing is enforced)*)
prove(`isFreeIn (QuoVar "x" (TyBase "bool")) (App (App (QuoVar "x" (TyBase "real")) (QuoConst "+" (TyBiCons "fun" (TyBase "real") (TyBiCons "fun" (TyBase "real") (TyBase "real"))))) (QuoVar "y" (TyBase "real"))) <=> F`,
	REWRITE_TAC[isFreeIn] THEN
	REWRITE_TAC[typeInjective] THEN
	REWRITE_TAC[STRING_EQ_CONV `"bool" = "real"`]
);;

(*Proof that a variable inside an abstraction can be free if it is not bound*)
prove(`isFreeIn (QuoVar "x" (TyBase "real")) (Abs (QuoVar "y" (TyBase "real")) ((App (App (QuoVar "x" (TyBase "real")) (QuoConst "+" (TyBiCons "fun" (TyBase "real") (TyBiCons "fun" (TyBase "real") (TyBase "real"))))) (QuoVar "y" (TyBase "real")))))`,
	REWRITE_TAC[isFreeIn] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"x" = "y"`)]
);;

(*Proof that a variable inside an abstraction is not free if it is bound*)
prove(`isFreeIn (QuoVar "x" (TyBase "real")) (Abs (QuoVar "x" (TyBase "real")) ((App (App (QuoVar "x" (TyBase "real")) (QuoConst "+" (TyBiCons "fun" (TyBase "real") (TyBiCons "fun" (TyBase "real") (TyBase "real"))))) (QuoVar "y" (TyBase "real"))))) <=> F`,
	REWRITE_TAC[isFreeIn] 
);;

(*The next two proofs show that wrapping the previous two expressions inside a quotation makes them false*)
prove(`isFreeIn (QuoVar "x" (TyBase "real")) (Quo (Abs (QuoVar "y" (TyBase "real")) ((App (App (QuoVar "x" (TyBase "real")) (QuoConst "+" (TyBiCons "fun" (TyBase "real") (TyBiCons "fun" (TyBase "real") (TyBase "real"))))) (QuoVar "y" (TyBase "real")))))) <=> F`,
	REWRITE_TAC[isFreeIn]
);;

prove(`isFreeIn (QuoVar "x" (TyBase "real")) (Quo (Abs (QuoVar "x" (TyBase "real")) ((App (App (QuoVar "x" (TyBase "real")) (QuoConst "+" (TyBiCons "fun" (TyBase "real") (TyBiCons "fun" (TyBase "real") (TyBase "real"))))) (QuoVar "y" (TyBase "real")))))) <=> F`,
	REWRITE_TAC[isFreeIn] 
);;


(*A simple proof that variables are variables*)
prove(`isVar (QuoVar "ProveMe" (TyBase "bool")) = T`,
	REWRITE_TAC[isVar] THEN
	REWRITE_TAC[ep_constructor]
);;

(*A simple proof that another type of epsilon is NOT a variable*)
prove(`isVar (QuoConst "DontProveMe" (TyBase "bool")) = F`,
	REWRITE_TAC[isVar] THEN
	REWRITE_TAC[ep_constructor] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"QuoConst" = "QuoVar"`)]
);;

(*A simple proof that constants are constants*)
prove(`isConst (QuoConst "ProveMe" (TyBase "bool")) = T`,
	REWRITE_TAC[isConst] THEN
	REWRITE_TAC[ep_constructor]
);;

(*A simple proof that another type of epsilon is NOT a constant*)
prove(`isConst (QuoVar "DontProveMe" (TyBase "bool")) = F`,
	REWRITE_TAC[isConst] THEN
	REWRITE_TAC[ep_constructor] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"QuoVar" = "QuoConst"`)]
);;

(*Simple proof that an abstraction is recognized as an abstraction*)
prove(`isAbs (Abs (QuoVar "Prove" (TyBase "bool")) (QuoConst "Me" (TyBase "bool"))) = T`,
	REWRITE_TAC[isAbs] THEN
	REWRITE_TAC[ep_constructor]
);;

(*Simple proof that non-abstractions are not abstractions*)
prove(`isAbs (QuoVar "DontProveMe" (TyBase "bool")) = F`,
	REWRITE_TAC[isAbs] THEN
	REWRITE_TAC[ep_constructor] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"QuoVar" = "Abs"`)]
);;

(*Simple proof that an application is recognized as an application*)
prove(`isApp (App (QuoVar "Prove" (TyBase "bool")) (QuoConst "Me" (TyBase "bool"))) = T`,
	REWRITE_TAC[isApp] THEN
	REWRITE_TAC[ep_constructor]
);;

(*Simple proof that non-applications are not applications*)
prove(`isApp (QuoVar "DontProveMe" (TyBase "bool")) = F`,
	REWRITE_TAC[isApp] THEN
	REWRITE_TAC[ep_constructor] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"QuoVar" = "App"`)]
);;


(*Start by proving that isVarType is false when something is not a var*)
prove(`isVarType (QuoConst "Wrong" (TyVar "A")) (TyVar "A") <=> F`,
	REWRITE_TAC[isVarType] THEN
	REWRITE_TAC[isVar] THEN
	REWRITE_TAC[ep_constructor] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"QuoConst" = "QuoVar"`)]
);;

(*Now prove that isVarType with the wrong variable type is false*)
prove(`isVarType (QuoVar "Wrong" (TyVar "A")) (TyBase "bool") <=> F`,
	REWRITE_TAC[isVarType] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[typeDistinct]
);;

(*Now proves that isVarType with the right variable type is true*)
prove(`isVarType (QuoVar "Right" (TyVar "A")) (TyVar "A")`,
	REWRITE_TAC[isVarType] THEN
	REWRITE_TAC[ep_type;isVar] THEN
	REWRITE_TAC[ep_constructor]
);;

(*Test for failure when not a constant*)
prove(`isConstType (QuoVar "Wrong" (TyVar "A")) (TyVar "A") <=> F`,
	REWRITE_TAC[isConstType] THEN
	REWRITE_TAC[isConst] THEN
	REWRITE_TAC[ep_constructor] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"QuoVar" = "QuoConst"`)]
);;

(*Test for failure when the constant is of the wrong type*)
prove(`isConstType (QuoConst "Wrong" (TyBase "bool")) (TyVar "A") <=> F`,
	REWRITE_TAC[isConstType] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[typeDistinct]
);;

(*Proves that the right types result in true*)
prove(`isConstType (QuoConst "Right" (TyBiCons "fun" (TyBase "bool") (TyVar "A"))) (TyBiCons "fun" (TyBase "bool") (TyVar "A"))`,
	REWRITE_TAC[isConstType] THEN
	REWRITE_TAC[isConst;ep_type] THEN
	REWRITE_TAC[ep_constructor]
);;

(*The following proofs will test combinatoryType*)

(*(+) 3 is of type (TyBase "num")->(TyBase "num")*)
prove(`combinatoryType(App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) (QuoConst "3" (TyBase "num"))) = TyBiCons "fun" (TyBase "num") (TyBase "num")`,
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc]
);;

(* 2 + 3 is of type (TyBase "num") *)
prove(`combinatoryType(App (App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) (QuoConst "2" (TyBase "num"))) (QuoConst "3" (TyBase "num"))) = (TyBase "num")`,
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc]
);;

(*Binding x in (+) x gets a type of (TyBase "num")->(TyBase "num")->(TyBase "num")*)
prove(`combinatoryType (Abs (QuoVar "x" (TyBase "num")) (App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) (QuoVar "x" (TyBase "num")))) = TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num"))`,
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc]
);;

(*Binding x in 2 + x should make it (TyBase "num") -> (TyBase "num")*)
prove(`combinatoryType (Abs (QuoVar "x" (TyBase "num")) (App (App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) (QuoConst "2" (TyBase "num"))) (QuoVar "x" (TyBase "num")))) =  TyBiCons "fun" (TyBase "num") (TyBase "num")`,
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc]
);;


(*                                                                                                     *)
(* Below are all tests for isExpr - it is a very important function so it will be extensively tested*)
(*                                                                                                     *)


(*Prove that a variable is an expression*)
prove(`isExpr (QuoVar "x" (TyBase "bool"))`,
	REWRITE_TAC[isExpr]
);;

(*Prove that a constant is an expression*)
prove(`isExpr (QuoConst "T" (TyBase "bool"))`,
	REWRITE_TAC[isExpr]
);;

(*Prove that a simple function application is an expression*)
prove(`isExpr (App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) (QuoConst "NUMERAL" (TyBase "num")))`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isConst;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[isFunction] THEN
	EXISTS_TAC `TyBase "num"` THEN
	EXISTS_TAC `TyBiCons "fun" (TyBase "num") (TyBase "num")` THEN
	REFL_TAC
);;

(*Prove that recursed function applications are an expression*)
prove(`isExpr (App(App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) (QuoConst "NUMERAL" (TyBase "num"))) (QuoVar "x" (TyBase "num")))`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isApp;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[isConst;ep_constructor] THEN
	CONJ_TAC THEN
	EXISTS_TAC `TyBase "num"` THENL
	[EXISTS_TAC `TyBase "num"` THEN REFL_TAC; 
	EXISTS_TAC `TyBiCons "fun" (TyBase "num") (TyBase "num")` THEN REFL_TAC]);;


(*Prove that a malformed application is not an expression*)
prove(`isExpr(App (QuoVar "x" (TyBase "bool")) (QuoVar "y" (TyBase "bool"))) <=> F`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isConst;isApp;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[isAbs] THEN
	REWRITE_TAC[ep_constructor] THEN
	REWRITE_TAC[STRING_EQ_CONV(`"QuoVar" = "App"`)] THEN
	REWRITE_TAC[STRING_EQ_CONV(`"QuoVar" = "QuoConst"`)] THEN
	REWRITE_TAC[STRING_EQ_CONV(`"QuoVar" = "Abs"`)]
);;


(*Prove that a function application whose initial types match is an expression (i.e. this takes a number -> (TyBase "bool") -> number so it should work when giving it a single number)*)
prove(`isExpr (App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "bool") (TyBase "num")))) (QuoConst "NUMERAL" (TyBase "num")))`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isConst;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[isFunction] THEN
	EXISTS_TAC `TyBase "num"` THEN
	EXISTS_TAC `TyBiCons "fun" (TyBase "bool") (TyBase "num")` THEN
	REFL_TAC
);;

(*Proving that the above should no longer work when giving it a second number*)
prove(`isExpr (App(App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "bool") (TyBase "num")))) (QuoConst "3" (TyBase "num"))) (QuoVar "x" (TyBase "num"))) <=> F`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isConst;isApp;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[typeInjective] THEN
	REWRITE_TAC[STRING_EQ_CONV `"bool" = "num"`]
);;

(*Proving that function application does not work out of order*)
prove(`isExpr (App  (QuoConst "3" (TyBase "num")) (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num"))))) <=> F`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isConst;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[typeDistinct]
);;

(*A function application to an invalid expresion is also an invalid expression*)
prove(`isExpr (App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "bool") (TyBase "num")))) (App (QuoVar "x" (TyBase "bool")) (QuoVar "y" (TyBase "bool")))) <=> F`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[typeDistinct]
);;

(*An abstraction where the first expression is not a variable is invalid*)
prove(`isExpr (Abs (QuoConst "3" (TyBase "num")) (QuoVar "x" (TyBase "num"))) <=> F`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isVar] THEN
	REWRITE_TAC[ep_constructor] THEN
	REWRITE_TAC[STRING_EQ_CONV(`"QuoConst" = "QuoVar"`)]
);;

(*An abstraction where the abstracted variable makes no appearence in the second term is valid*)
prove(`isExpr (Abs (QuoVar "x" (TyBase "bool")) (QuoVar "y" (TyBase "bool")))`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isVar;ep_constructor] THEN
	REWRITE_TAC[typeMismatch]
);;

(*An abstraction where the abstracted variable appears and is the same type is valid*)
prove(`isExpr (Abs (QuoVar "x" (TyBase "bool")) (QuoVar "x" (TyBase "bool")))`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isVar;ep_constructor] THEN
	REWRITE_TAC[typeMismatch]
);;

(*An abstraction where the abstraced variable appears but is a different type is invalid*)
prove(`isExpr (Abs (QuoVar "x" (TyBase "bool")) (QuoVar "x" (TyBase "num"))) <=> F`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isVar;ep_constructor] THEN
	REWRITE_TAC[typeMismatch] THEN
	REWRITE_TAC[typeInjective] THEN
	REWRITE_TAC[STRING_EQ_CONV `"bool" = "num"`]
);;

(*Abstracting over an application is invalid in the case of a type mismatch*)
prove(`isExpr (Abs (QuoVar "x" (TyBase "bool")) (App(App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) (QuoConst "3" (TyBase "num"))) (QuoVar "x" (TyBase "num")))) <=> F`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isVar;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[isApp;ep_constructor] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[typeMismatch] THEN
	REWRITE_TAC[typeInjective] THEN
	REWRITE_TAC[STRING_EQ_CONV `"bool" = "num"`]
);;

(*Abstracting over an application is valid when the types do match*)

prove(`isExpr (Abs (QuoVar "x" (TyBase "num")) (App(App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) (QuoConst "3" (TyBase "num"))) (QuoVar "x" (TyBase "num"))))`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isVar;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[isApp;ep_constructor] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[typeMismatch] THEN
	REWRITE_TAC[isConst;ep_constructor] THEN
	CONJ_TAC THEN
	EXISTS_TAC `TyBase "num"` THENL
	[EXISTS_TAC `TyBase "num"` THEN REFL_TAC; 
	EXISTS_TAC `TyBiCons "fun" (TyBase "num") (TyBase "num")` THEN REFL_TAC]
);;


(*The following will test isExprType*)
prove(`isExprType (App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "bool") (TyBase "num")))) (QuoConst "NUMERAL" (TyBase "num"))) (TyBiCons "fun" (TyBase "bool") (TyBase "num"))`,
	REWRITE_TAC[isExprType] THEN
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isConst;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[isFunction] THEN
	EXISTS_TAC `TyBase "num"` THEN
	EXISTS_TAC `TyBiCons "fun" (TyBase "bool") (TyBase "num")` THEN
	REFL_TAC
);;

(*This tests that isExprType fails when the given expression is not an expression*)
prove(`isExprType (App (QuoConst "2" (TyBase "num")) (QuoConst "3" (TyBase "num"))) (TyBiCons "fun" (TyBase "bool") (TyBase "num")) <=> F`,
	REWRITE_TAC[isExprType] THEN
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[typeDistinct]
);;

(*This tests that isExprType fails when the types do not match*)
prove(`isExprType (App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "bool") (TyBase "num")))) (QuoConst "NUMERAL" (TyBase "num"))) (TyBase "bool") <=> F`,
	REWRITE_TAC[isExprType] THEN
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isConst;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[typeDistinct]
);;

(*This tests that isProperSubexpression returns false when the given subexpression is not a subexpression*)
prove(`isProperSubexpressionOf (QuoVar "x" (TyBase "bool")) (QuoVar "y" (TyBase "bool")) <=> F`,
	REWRITE_TAC[isProperSubexpressionOf] THEN
	REWRITE_TAC[isPartOf] THEN
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[epsilonInjective] THEN
	REWRITE_TAC[STRING_EQ_CONV `"x" = "y"`]
);;

(*This tests that isProperSubexpression returns false when the given subexpression is not an expression*)
prove(`isProperSubexpressionOf (App (QuoVar "x" (TyBase "bool")) (QuoConst "y" (TyBase "bool"))) (App (QuoVar "x" (TyBase "bool")) (QuoConst "y" (TyBase "bool"))) <=> F`,
	REWRITE_TAC[isProperSubexpressionOf] THEN
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[typeDistinct] 
);;


(*This tests that isProperSubexpression returns true even if the expresion on the right is improper*)
prove(`isProperSubexpressionOf (QuoVar "x" (TyBase "bool")) (App (QuoVar "x" (TyBase "bool")) (QuoConst "y" (TyBase "bool")))`,
	REWRITE_TAC[isProperSubexpressionOf] THEN
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isPartOf]
);;

(*Tests that isProperSubExpression works for large terms*)
prove(`isProperSubexpressionOf (App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) (QuoConst "NUMERAL" (TyBase "num"))) (App(App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) (QuoConst "NUMERAL" (TyBase "num"))) (QuoVar "x" (TyBase "num")))`,
	REWRITE_TAC[isProperSubexpressionOf] THEN
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isPartOf] THEN
	REWRITE_TAC[isConst;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[headFunc] THEN
	EXISTS_TAC `TyBase "num"` THEN
	EXISTS_TAC `TyBiCons "fun" (TyBase "num") (TyBase "num")` THEN
	REFL_TAC
);;

(*Final tests for this type - making sure that quote does not interfere with previous proofs*)
prove(`isExpr (Quo (Abs (QuoVar "x" (TyBase "num")) (App(App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) (QuoConst "3" (TyBase "num"))) (QuoVar "x" (TyBase "num")))))`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isVar;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[isApp;ep_constructor] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[typeMismatch] THEN
	EXISTS_TAC `TyBase "num"` THEN
	EXISTS_TAC `TyBase "num"` THEN
	REFL_TAC
);;

prove(`isExpr (Quo (Abs (QuoVar "x" (TyBase "bool")) (App(App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) (QuoConst "3" (TyBase "num"))) (QuoVar "x" (TyBase "num")))))`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isVar;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[isApp;ep_constructor] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[typeMismatch] THEN
	REWRITE_TAC[typeInjective] THEN
	REWRITE_TAC[STRING_EQ_CONV `"bool" = "num"`]
);;

prove(`isExprType (Quo ((App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "bool") (TyBase "num")))) (QuoConst "NUMERAL" (TyBase "num"))))) (TyBase "epsilon")`,
	REWRITE_TAC[isExprType] THEN
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isConst;ep_constructor] THEN
	REWRITE_TAC[combinatoryType]);;


prove(`isExprType (Quo(App (QuoConst "_0" (TyBase "num")) (QuoConst "_0" (TyBase "num")))) (TyBiCons "fun" (TyBase "bool") (TyBase "num")) <=> F`,
	REWRITE_TAC[isExprType] THEN
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[typeDistinct]);;


prove(`isExprType (Quo (App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "bool") (TyBase "num")))) (QuoConst "NUMERAL" (TyBase "num")))) (TyBase "bool") <=> F`,
	REWRITE_TAC[isExprType] THEN
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isConst;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[typeInjective] THEN 
	REWRITE_TAC[STRING_EQ_CONV `"epsilon" = "bool"`]
);;
    
prove(`isProperSubexpressionOf (QuoVar "x" (TyBase "bool")) (Quo (QuoVar "y" (TyBase "bool"))) <=> F`,
	REWRITE_TAC[isProperSubexpressionOf] THEN
	REWRITE_TAC[isPartOf] THEN
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[epsilonInjective] THEN
	REWRITE_TAC[epsilonDistinct] THEN
	REWRITE_TAC[STRING_EQ_CONV `"x" = "y"`]
);;

prove(`isProperSubexpressionOf (App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) (QuoConst "NUMERAL" (TyBase "num"))) (Quo(App(App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) (QuoConst "NUMERAL" (TyBase "num"))) (QuoVar "x" (TyBase "num"))))`,
	REWRITE_TAC[isProperSubexpressionOf] THEN
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isPartOf] THEN
	REWRITE_TAC[isConst;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[headFunc] THEN
	EXISTS_TAC `TyBase "num"` THEN
	EXISTS_TAC `TyBiCons "fun" (TyBase "num") (TyBase "num")` THEN
	REFL_TAC
);;

(*Got to this point before the meeting, debug below proofs*)

(*Proof that application works for basic expressions*)
prove(`app (QuoVar "x" (TyBase "bool")) (QuoVar "y" (TyBase "bool")) = App (QuoVar "x" (TyBase "bool")) (QuoVar "y" (TyBase "bool"))`,
	REWRITE_TAC[app]
);;

(*Testing it for bigger expressions*)
prove(`app (app (QuoVar "x" (TyBase "bool")) (QuoConst "/\\" (TyBiCons "fun" (TyBase "bool") (TyBiCons "fun" (TyBase "bool") (TyBase "bool"))))) (QuoConst "F" (TyBase "bool")) = App (App (QuoVar "x" (TyBase "bool")) (QuoConst "/\\" (TyBiCons "fun" (TyBase "bool") (TyBiCons "fun" (TyBase "bool") (TyBase "bool"))))) (QuoConst "F" (TyBase "bool"))`,
	REWRITE_TAC[app]
);;

(*Proof that abstraction works for basic expressions*)
prove(`e_abs (QuoVar "x" (TyBase "bool")) (QuoVar "y" (TyBase "bool")) = Abs (QuoVar "x" (TyBase "bool")) (QuoVar "y" (TyBase "bool"))`,
	REWRITE_TAC[e_abs]
);;

(*Testing it for bigger expressions, along with proving that x is free in the expression on it's own but is no longer free after applying e_abs*)
prove(`(e_abs (QuoVar "x" (TyBase "bool")) (App (App (QuoVar "x" (TyBase "bool")) (QuoConst "/\\" (TyBiCons "fun" (TyBase "bool") (TyBiCons "fun" (TyBase "bool") (TyBase "bool"))))) (QuoConst "F" (TyBase "bool"))) = 
	   Abs (QuoVar "x" (TyBase "bool")) (App (App (QuoVar "x" (TyBase "bool")) (QuoConst "/\\" (TyBiCons "fun" (TyBase "bool") (TyBiCons "fun" (TyBase "bool") (TyBase "bool"))))) (QuoConst "F" (TyBase "bool")))) /\ 
	   (~(isFreeIn (QuoVar "x" (TyBase "bool")) (e_abs (QuoVar "x" (TyBase "bool")) (app (app (QuoVar "x" (TyBase "bool")) (QuoConst "/\\" (TyBiCons "fun" (TyBase "bool") (TyBiCons "fun" (TyBase "bool") (TyBase "bool"))))) (QuoConst "F" (TyBase "bool")))))) /\
	   (isFreeIn (QuoVar "x" (TyBase "bool")) (App (App (QuoVar "x" (TyBase "bool")) (QuoConst "/\\" (TyBiCons "fun" (TyBase "bool") (TyBiCons "fun" (TyBase "bool") (TyBase "bool"))))) (QuoConst "F" (TyBase "bool"))))`,
	REWRITE_TAC[e_abs] THEN
	REWRITE_TAC[isFreeIn]
);;

(*Proof that quoting works as intended*)
prove(`quo (App (App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) (QuoConst "2" (TyBase "num"))) (QuoConst "3" (TyBase "num"))) = 
	Quo (App (App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) (QuoConst "2" (TyBase "num"))) (QuoConst "3" (TyBase "num")))`,
	REWRITE_TAC[quo]
);;

(*Proof that quotes can be quoted*)
prove(`quo (quo (App (App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) (QuoConst "2" (TyBase "num"))) (QuoConst "3" (TyBase "num")))) = 
	Quo (Quo (App (App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) (QuoConst "2" (TyBase "num"))) (QuoConst "3" (TyBase "num"))))`,
	REWRITE_TAC[quo]
);;


(*Proves that eqTypes returns true when the two types are equal*)
prove(`eqTypes (TyBase "bool") (TyBase "bool")`,REWRITE_TAC[eqTypes]);;

(*Proves that eqTypes returns false when the two types are not equal*)
prove(`eqTypes (TyBase "bool") (TyVar "A") <=> F`,
	REWRITE_TAC[eqTypes] THEN
	REWRITE_TAC[typeDistinct]
);;

prove(`isConstruction ((e_abs (QuoVar "x" (TyBase "bool")) (App (App (QuoVar "x" (TyBase "bool")) (QuoConst "/\\" (TyBiCons "fun" (TyBase "bool") (TyBiCons "fun" (TyBase "bool") (TyBase "bool"))))) (QuoConst "F" (TyBase "bool")))))`,
REWRITE_TAC[e_abs] THEN
REWRITE_TAC[isConstruction]
);;

prove(`isConstruction ((Abs (QuoVar "x" (TyBase "num")) (App (App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) (QuoConst "2" (TyBase "num"))) (QuoVar "x" (TyBase "num")))))`,
REWRITE_TAC[isConstruction]
);;

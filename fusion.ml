(* ========================================================================= *)
(* Complete HOL kernel of types, terms and theorems.                         *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "lib.ml";;

module type Hol_kernel =
  sig
      type hol_type = private
        Tyvar of string
      | Tyapp of string *  hol_type list

      type term = private
        Var of string * hol_type
      | Const of string * hol_type
      | Comb of term * term
      | Abs of term * term
      | Quote of term
      | Hole of term * hol_type
      | Eval of term * hol_type

      type check = private 
         Ok
       | Issue of term

      exception Problem of string * term 

      type thm

      val types: unit -> (string * int)list
      val get_type_arity : string -> int
      val new_type : (string * int) -> unit
      val mk_type: (string * hol_type list) -> hol_type
      val mk_vartype : string -> hol_type
      val dest_type : hol_type -> (string * hol_type list)
      val dest_vartype : hol_type -> string
      val is_type : hol_type -> bool
      val is_vartype : hol_type -> bool
      val tyvars : hol_type -> hol_type list
      val type_subst : (hol_type * hol_type)list -> hol_type -> hol_type
      val bool_ty : hol_type
      val ep_ty : hol_type
      val aty : hol_type

      val constants : unit -> (string * hol_type) list
      val not_eff : unit -> (term * term) list
      val addNotEff : thm -> unit 
      val get_const_type : string -> hol_type
      val new_constant : string * hol_type -> unit
      val type_of : term -> hol_type
      val fun_type_of : term -> hol_type
      val alphaorder : term -> term -> int
      val is_var : term -> bool
      val is_const : term -> bool
      val is_abs : term -> bool
      val is_comb : term -> bool
      val is_quote : term -> bool
      val is_hole : term -> bool
      val is_eval : term -> bool
      val mk_var : string * hol_type -> term
      val mk_const : string * (hol_type * hol_type) list -> term
      val mk_abs : term * term -> term
      val mk_comb : term * term -> term
      val mk_quote : term -> term
      val mk_hole : term * hol_type -> term
      val mk_eval : term * hol_type -> term
      val dest_var : term -> string * hol_type
      val dest_const : term -> string * hol_type
      val dest_comb : term -> term * term
      val dest_abs : term -> term * term
      val dest_quote: term -> term
      val dest_hole : term -> term * hol_type
      val dest_eval : term -> term * hol_type
      val frees : term -> term list
      val freesl : term list -> term list
      val freesin : term list -> term -> bool
      val vfree_in : term -> term -> bool
      val type_vars_in_term : term -> hol_type list
      val variant : term list -> term -> term
      val vsubst : (term * term) list -> term -> term
      val inst : (hol_type * hol_type) list -> term -> term
      val rand: term -> term
      val rator: term -> term
      val dest_eq: term -> term * term

      val isQuoteSame: term -> term -> bool
      val QSUB_CONV : (term->thm) -> term -> ((term->thm) -> term -> thm) -> thm
      val QBETA_CONV : term -> (term -> thm) -> thm

      val dest_thm : thm -> term list * term
      val hyp : thm -> term list
      val concl : thm -> term
      val orda: (term * term) list -> term -> term -> int
      val REFL : term -> thm
      val LAW_OF_QUO : term -> thm
      val LAW_OF_QUO_CONV : term -> thm
      val TRANS : thm -> thm -> thm
      val MK_COMB : thm * thm -> thm
      val ABS : term -> thm -> thm
      val BETA : term -> thm
      val ASSUME : term -> thm
      val EQ_MP : thm -> thm -> thm
      val DEDUCT_ANTISYM_RULE : thm -> thm -> thm
      val INST_TYPE : (hol_type * hol_type) list -> thm -> thm
      val INST : (term * term) list -> thm -> thm
      val axioms : unit -> thm list
      val new_axiom : term -> thm
      val definitions : unit -> thm list
      val new_basic_definition : term -> thm
      val new_basic_type_definition :
              string -> string * string -> thm -> thm * thm
      val getTyv : unit -> int
      val construction_type : term -> term 
      val termToConstruction : term -> term 
      val constructionToTerm : term -> term 
      val QUOTE_TO_CONSTRUCTION_CONV : term -> thm 
      val CONSTRUCTION_TO_QUOTE_CONV : term -> thm
      val CONSTRUCTION_TO_TERM_CONV : term -> thm 
      val TERM_TO_CONSTRUCTION_CONV : term -> thm 
      val HOLE_ABSORB : term -> thm
      val HOLE_ABSORB_CONV : term -> thm
      val LAW_OF_DISQUO : term -> thm
      val LAW_OF_DISQUO_CONV : term -> thm
      val matchType : hol_type -> term

      (*Debugging functions temporarily revealed for tracing go here*)
      val constructionToTerm : term -> term
      val qcheck_type_of : term -> hol_type
      val LAW_OF_QUO : term -> thm
      val QUO_DISQUO : term -> thm
      val ABS_DISQUO : term -> term -> thm
      val APP_DISQUO : term -> term -> thm
      val BETA_REDUCE_EVAL : term -> term -> term -> hol_type -> thm
      val EVAL_FREE_NOT_EFFECTIVE_IN: term -> term -> term -> thm
      val BETA_REDUCE_ABS : term -> term -> term -> term -> term -> term -> thm
      val BETA_RED_BY_SUB : term -> thm 
      val EVAL_VSUB : thm -> term -> thm
      val EVAL_GOAL_VSUB : term list * term -> thm 
      val is_eval_free : term -> check
      val eval_free : term -> bool
      val is_hole_free : term -> check
      val hole_free : term -> bool
      val mk_not_effective_in : term -> term -> term -> term
      val mk_effective_in : term -> term -> term -> term
      val stackAbs : (term * term) list -> term -> term
      val not_effective_in : term -> term -> bool 
end;;

(* ------------------------------------------------------------------------- *)
(* This is the implementation of those primitives.                           *)
(* ------------------------------------------------------------------------- *)

module Hol : Hol_kernel = struct

  type hol_type = Tyvar of string
                | Tyapp of string *  hol_type list

  type term = Var of string * hol_type
            | Const of string * hol_type
            | Comb of term * term
            | Abs of term * term
            | Quote of term
            | Hole of term * hol_type
            | Eval of term * hol_type

  type check = Ok
             | Issue of term

  type thm = Sequent of (term list * term)

  exception Problem of string * term 

(* ------------------------------------------------------------------------- *)
(* List of current type constants with their arities.                        *)
(*                                                                           *)
(* Initially we just have the boolean type, constructor type, and function   *)                   
(* space constructor. Later on we add as primitive the type of individuals.  *)
(* All other new types result from definitional extension.                   *)
(* ------------------------------------------------------------------------- *)

  let the_type_constants = ref ["bool",0; "fun",2]

(* ------------------------------------------------------------------------- *)
(* Return all the defined types.                                             *)
(* ------------------------------------------------------------------------- *)

  let types() = !the_type_constants

(* ------------------------------------------------------------------------- *)
(* Lookup function for type constants. Returns arity if it succeeds.         *)
(* ------------------------------------------------------------------------- *)

  let get_type_arity s = assoc s (!the_type_constants)

(* ------------------------------------------------------------------------- *)
(* Declare a new type.                                                       *)
(* ------------------------------------------------------------------------- *)

  let new_type(name,arity) =
    if can get_type_arity name then
      failwith ("new_type: type "^name^" has already been declared")
    else the_type_constants := (name,arity)::(!the_type_constants)

(* ------------------------------------------------------------------------- *)
(* Basic type constructors.                                                  *)
(* ------------------------------------------------------------------------- *)

  let mk_type(tyop,args) =
    let arity = try get_type_arity tyop with Failure _ ->
      failwith ("mk_type: type "^tyop^" has not been defined") in
    if arity = length args then
      Tyapp(tyop,args)
    else failwith ("mk_type: wrong number of arguments to "^tyop)

  let mk_vartype v = Tyvar(v)

(* ------------------------------------------------------------------------- *)
(* Basic type destructors.                                                   *)
(* ------------------------------------------------------------------------- *)

  let dest_type =
    function
        (Tyapp (s,ty)) -> s,ty
      | (Tyvar _) -> failwith "dest_type: type variable not a constructor"

  let dest_vartype =
    function
        (Tyapp(_,_)) -> failwith "dest_vartype: type constructor not a variable"
      | (Tyvar s) -> s

(* ------------------------------------------------------------------------- *)
(* Basic type discriminators.                                                *)
(* ------------------------------------------------------------------------- *)

  let is_type = can dest_type

  let is_vartype = can dest_vartype

(* ------------------------------------------------------------------------- *)
(* Return the type variables in a type and in a list of types.               *)
(* ------------------------------------------------------------------------- *)

  let rec tyvars =
      function
          (Tyapp(_,args)) -> itlist (union o tyvars) args []
        | (Tyvar v as tv) -> [tv]

  let is_defined_type ty = (tyvars ty = []) 

(* ------------------------------------------------------------------------- *)
(* Substitute types for type variables.                                      *)
(*                                                                           *)
(* NB: non-variables in subst list are just ignored (a check would be        *)
(* repeated many times), as are repetitions (first possibility is taken).    *)
(* ------------------------------------------------------------------------- *)

(*Todo: Remove the  prefix to restore normal operations*)

let rec type_subst i ty =
    match ty with
      Tyapp(tycon,args) ->
          let args' = qmap (type_subst i) args in
          if args' == args then ty else Tyapp(tycon,args')
      | _ -> rev_assocd ty i ty


  let bool_ty = Tyapp("bool",[])
  let ep_ty = Tyapp("epsilon",[])
  let aty = Tyvar "A"

(* ------------------------------------------------------------------------- *)
(* List of term constants and their types.                                   *)
(*                                                                           *)
(* We begin with just equality (over all types). Later, the Hilbert choice   *)
(* operator is added. All other new constants are defined.                   *)
(* ------------------------------------------------------------------------- *)


  let the_term_constants =
     ref [("=",Tyapp("fun",[aty;Tyapp("fun",[aty;bool_ty])]))]

  (*Check if two quotes are equal for use in match_type*)
  let rec isQuoteSame tm tm2 = match tm,tm2 with
    | Quote(e1),Quote(e2) -> isQuoteSame e1 e2
    | Comb(l,r),Comb(l2,r2) -> isQuoteSame l l2 && isQuoteSame r r2
    | Const(a,b),Const(c,d) | Var(a,b),Var(c,d)  -> a = c && b = d
    | Abs(a,b),Abs(c,d) -> a = c && b = d
    | Hole(a,b),Hole(c,d) -> a = c && b = d
    | _ -> false

  (*Need to move the faculties for generating variable types from preterm to here for quote conversion to work*)
  let tyv_num = ref 0;;

  let getTyv unit = let () = tyv_num := (!tyv_num + 1) in !tyv_num;;

  let not_effectives = ref ([]:(term * term) list);;

  let not_eff() = !not_effectives

  let not_effective_in var tm = exists (fun (v, t) -> var = v && tm = t) (!not_effectives) 

(* ------------------------------------------------------------------------- *)
(* Return all the defined constants with generic types.                      *)
(* ------------------------------------------------------------------------- *)

  let constants() = !the_term_constants

(* ------------------------------------------------------------------------- *)
(* Gets type of constant if it succeeds.                                     *)
(* ------------------------------------------------------------------------- *)

  let get_const_type s = assoc s (!the_term_constants)

(* ------------------------------------------------------------------------- *)
(* Declare a new constant.                                                   *)
(* ------------------------------------------------------------------------- *)

  let new_constant(name,ty) =
    if can get_const_type name then
      failwith ("new_constant: constant "^name^" has already been declared")
    else the_term_constants := (name,ty)::(!the_term_constants)

(* ------------------------------------------------------------------------- *)
(* Finds the type of a term (assumes it is well-typed).                      *)
(* ------------------------------------------------------------------------- *)

  (*This is used when checking quote types match the term types as holes should always be of type epsilon - type_of returns the type of the thing inside the quote so that they can be used more easily
  in the parser*)
  let rec qcheck_type_of = function
    | Var(_,ty) -> ty
    | Const(_,ty) -> ty
    | Comb(s,_) -> (match qcheck_type_of s with Tyapp("fun",[dty;rty]) -> rty | ep_ty -> ep_ty)
    | Abs(Var(_,ty),t) -> Tyapp("fun",[ty;qcheck_type_of t])
    | Quote(_) -> ep_ty
    | Hole(_,ty) -> ty
    | Eval(_,ty) -> ty
    | _ -> failwith "TYPE_OF: Invalid term. You should not see this error under normal use, if you do, the parser has allowed an ill formed term to be created."

  let rec type_of = function
    | Var(_,ty) -> ty
    | Const(_,ty) -> ty
    | Comb(s,_) -> (match type_of s with Tyapp("fun",[dty;rty]) -> rty| ep_ty -> ep_ty)
    | Abs(Var(_,ty),t) -> Tyapp("fun",[ty;type_of t])
    | Quote(_) -> ep_ty
    | Hole(_,ty) -> ty
    | Eval(_,ty) -> ty
    | _ -> failwith "TYPE_OF: Invalid term. You should not see this error under normal use, if you do, the parser has allowed an ill formed term to be created."

  (*Internal function to grab the type of an applied function*)
  let fun_type_of tm = 
    let rec ftype_of = function
    | Comb(l,_) -> ftype_of l
    | Const(n,t) | Var(n,t) when not (is_vartype t) && fst (dest_type t) = "fun" -> t  
    | _ -> failwith "Not a function"
  in
  match tm with
    | Comb(l,r) when type_of tm = ep_ty -> ftype_of l 
    | _ -> failwith "Incomplete or mistyped function"   

  (* Checks if a term is eval-free *)
  let rec is_eval_free tm = match tm with 
    | Var(_,_) -> Ok
    | Const(_,_) -> Ok
    | Comb(a,b) -> let ev_a = is_eval_free a in if ev_a = Ok then is_eval_free b else ev_a
    | Abs(a,b) -> let ev_a = is_eval_free a in if ev_a = Ok then is_eval_free b else ev_a
    | Quote(e) -> is_eval_free e
    | Hole(e,_) -> is_eval_free e
    | Eval(_,_) -> Issue tm 

  let eval_free tm = (is_eval_free tm = Ok)

  (* Checks if term is hole-free *)

  let rec is_hole_free tm = match tm with 
    | Var(_,_) -> Ok
    | Const(_,_) -> Ok
    | Comb(a,b) -> let hole_a = is_hole_free a in if hole_a = Ok then is_hole_free b else hole_a
    | Abs(a,b) -> is_hole_free b
    | Quote(e) -> is_hole_free e
    | Hole(_,_) -> Issue tm
    | Eval(e,_) -> is_hole_free e  

  let hole_free tm = (is_hole_free tm = Ok)

(* ------------------------------------------------------------------------- *)
(* Primitive discriminators.                                                 *)
(* ------------------------------------------------------------------------- *)

  let is_var = function (Var(_)) -> true | _ -> false

  let is_const = function (Const(_)) -> true | _ -> false

  let is_abs = function (Abs(_)) -> true | _ -> false

  let is_comb = function (Comb(_)) -> true | _ -> false

  let is_quote = function (Quote(_)) -> true | _ -> false

  let dest_quote =
    function (Quote(e)) -> e | _ -> failwith "dest_quote: not a quotation"

  let is_hole = function (Hole(_)) -> true | _ -> false

  let is_eval = function (Eval(_)) -> true | _ -> false

  let dest_hole = 
    function (Hole(e,ty)) -> e,ty | _ -> failwith "dest_hole: not a hole"


(* ------------------------------------------------------------------------- *)
(* Primitive constructors.                                                   *)
(* ------------------------------------------------------------------------- *)

  let mk_var(v,ty) = Var(v,ty)

  let mk_const(name,theta) =
    let uty = try get_const_type name with Failure _ ->
      failwith "mk_const: not a constant name" in
    Const(name,type_subst theta uty)

  let mk_abs(bvar,bod) =
    match bvar with
      Var(_) -> if not (is_hole bod) then Abs(bvar,bod) else failwith "mk_abs: body of an abstraction cannot be a hole"
    | _ -> failwith "mk_abs: not a variable"

  let mk_comb(f,a) =
    match type_of f with
      Tyapp("fun",[ty;ty2]) when Pervasives.compare ty (type_of a) = 0 
        -> Comb(f,a)
    | _ -> failwith "mk_comb: types do not agree"

  let mk_quote t = 
     match (is_eval_free t) with 
        | Ok -> Quote(t)
        | Issue tm -> raise (Problem("Cannot quote terms with evaluations. This term contains one:", tm))

  let mk_hole (t,ty) = 
      match (is_hole_free t) with 
        | Ok ->  if type_of t = ep_ty then Hole(t,ty) else failwith "Not an epsilon term"
        | Issue tm -> raise (Problem("Holes cannot contain holes, this term already has one here:", tm))

  let mk_eval (e,ty) = if type_of e = ep_ty then Eval(e,ty) else failwith "type mismatch"

(* ------------------------------------------------------------------------- *)
(* Primitive destructors.                                                    *)
(* ------------------------------------------------------------------------- *)

  let dest_var =
    function (Var(s,ty)) -> s,ty | _ -> failwith "dest_var: not a variable"

  let dest_const =
    function (Const(s,ty)) -> s,ty | _ -> failwith "dest_const: not a constant"

  let dest_comb =
    function (Comb(f,x)) -> f,x | _ -> failwith "dest_comb: not a combination"

  let dest_abs =
    function (Abs(v,b)) -> v,b | _ -> failwith "dest_abs: not an abstraction"

  let dest_eval = 
    function (Eval(e,ty)) -> e,ty | _ -> failwith "dest_eval: not an eval"

(* ------------------------------------------------------------------------- *)
(* Add to theorem & not-effective lists                                      *)
(* ------------------------------------------------------------------------- *)

  let addNotEff tm = match tm with 
      | Sequent(asl,c) ->  
          (match c with 
            | Comb(Const("!", t1),Abs(v_aux, (Comb(Comb(Const("=", t2), Comb(Abs(var,trm),v_aux')), trm')))) 
                when type_of v_aux = type_of var && v_aux = v_aux' && var <> v_aux && trm = trm' ->
                not_effectives := (var, trm) :: !not_effectives 
            | _ -> failwith "Not a NOT-EFFECTIVE-IN theorem")
      | _ -> failwith "Not a theorem";;

(* ------------------------------------------------------------------------- *)
(* Finds the variables free in a term (list of terms).                       *)
(* ------------------------------------------------------------------------- *)

  let rec frees tm =
    let rec qfrees = function
      | Hole(e,ty) -> frees e
      | Comb(l,r) -> union (qfrees l) (qfrees r)
      | Abs(v,b) -> subtract (qfrees b) [v]
      | Quote(e) -> qfrees e
      | _ -> []
    in
    match tm with
      Var(_,_) -> [tm]
    | Const(_,_) -> []
    | Abs(bv,bod) -> subtract (frees bod) [bv]
    | Comb(s,t) -> union (frees s) (frees t)
    | Quote(e) -> qfrees e
    | Hole(e,_) -> frees e
    | Eval(e,_) -> frees e

  let freesl tml = itlist (union o frees) tml []

(* ------------------------------------------------------------------------- *)
(* Whether all free variables in a term appear in a list.                    *)
(* ------------------------------------------------------------------------- *)

  let rec freesin acc tm =
    let rec qfreesin acc tm = match tm with
      | Hole(e,ty) -> freesin acc e
      | Comb(l,r) -> qfreesin acc l && qfreesin acc r
      | Abs(v,b) -> qfreesin (v::acc) b
      | Quote(e) -> qfreesin acc e
      | _ -> true
    in
    match tm with
      Var(_,_) -> mem tm acc
    | Const(_,_) -> true
    | Abs(bv,bod) -> freesin (bv::acc) bod
    | Comb(s,t) -> freesin acc s && freesin acc t
    | Quote(e) -> qfreesin acc e
    | Hole(e,_) -> freesin acc e
    | Eval(e,_) -> freesin acc e

(* ------------------------------------------------------------------------- *)
(* Whether a variable (or constant in fact) is free in a term.               *)
(* ------------------------------------------------------------------------- *)

  let rec vfree_in v tm =
    let rec qvfree_in v tm = match tm with
      | Hole(e,ty) -> vfree_in v e
      | Comb(l,r) -> qvfree_in v l || qvfree_in v r
      | Abs(var,b) -> v <> var && qvfree_in v b 
      | Quote(e) -> qvfree_in v e 
      | _ -> false
    in
    match tm with
      Abs(bv,bod) -> v <> bv && vfree_in v bod
    | Comb(s,t) -> vfree_in v s || vfree_in v t
    | Quote(e) -> if hole_free e then false else qvfree_in v e
    | Hole(e,_) -> qvfree_in v e
    | Eval(e,_) -> vfree_in v e
    | _ -> Pervasives.compare tm v = 0

(* ------------------------------------------------------------------------- *)
(* Finds the type variables (free) in a term.                                *)
(* ------------------------------------------------------------------------- *)

  let rec type_vars_in_term =
    let rec qtype_vars_in_term tm = match tm with
      | Hole(e,_) -> type_vars_in_term e
      | Quote(e) -> qtype_vars_in_term e
      | Comb(l,r) -> union (qtype_vars_in_term l) (qtype_vars_in_term r)
      | Abs(_,b) -> qtype_vars_in_term b
      | _ -> []
    in
    function
      Var(_,ty)        -> tyvars ty
    | Const(_,ty)      -> tyvars ty
    | Comb(s,t)        -> union (type_vars_in_term s) (type_vars_in_term t)
    | Abs(Var(_,ty),t) -> union (tyvars ty) (type_vars_in_term t)
    | Quote(e)         -> if hole_free e then [] else qtype_vars_in_term e
    | Hole(e,_)        -> type_vars_in_term e
    | Eval(e,ty)       -> union (type_vars_in_term e) (tyvars ty)
    | _                -> failwith "TYPE_VARS_IN_TERM: Invalid type."

(* ------------------------------------------------------------------------- *)
(* For name-carrying syntax, we need this early.                             *)
(* ------------------------------------------------------------------------- *)

  let rec variant avoid v =
    if not(exists (vfree_in v) avoid) then v else
    match v with
      Var(s,ty) -> variant avoid (Var(s^"'",ty))
    | _ -> failwith "variant: not a variable"

(* ------------------------------------------------------------------------- *)
(* Syntax operations for equations.                                          *)
(* ------------------------------------------------------------------------- *)

  let safe_mk_eq l r =
    let ty = type_of l in
    Comb(Comb(Const("=",Tyapp("fun",[ty;Tyapp("fun",[ty;bool_ty])])),l),r)

  let dest_eq tm =
    match tm with
      Comb(Comb(Const("=",_),l),r) -> l,r
    | _ -> failwith "dest_eq"

(* ------------------------------------------------------------------------- *)
(* Substitution primitive (substitution for variables only!)                 *)
(* ------------------------------------------------------------------------- *)

  (*Checks is a term is free in terms of another term*)

  let rec makeAbsSubst sl tm = 
    let com = dest_comb tm in
    let a = snd com in
    let abs = dest_abs (fst com) in
    let var = fst abs in
    let e = fst (dest_eval (snd abs)) in
    match sl with
    | (a,b) :: rest when a = b -> makeAbsSubst rest tm
    | (a,b) :: rest ->  if (vfree_in var (Comb(Abs(var,e),a))) then Comb(Abs(b,(makeAbsSubst rest tm)),a) else (makeAbsSubst rest (Eval(Comb(Abs(var,e),a),type_of ((Comb(Abs(var,e),a))))))
    | [] -> tm


  let rec stackAbs l tm = match l with
  | (a,b) :: rest when List.length l > 1 -> Comb(Abs(b,(stackAbs rest tm)),a)
  | [(a,b)] -> Comb(Abs(b,tm),a)
  | _ -> failwith "Bad substitution list" 

  let vsubst =
    let rec vsubst ilist tm =
      (*Function to handle substitutions in holes in quotations*)
      let rec holeSub ilist tm =
        match tm with 
          | Abs(v,s) -> Abs(v, holeSub ilist s)
          | Comb(f,a) -> Comb(holeSub ilist f, holeSub ilist a)
          | Quote(e) -> Quote(holeSub ilist e)
          | Hole(e,t) when not (is_quote e) -> Hole(vsubst ilist e, t)
          | _ -> tm 
      in 
      match tm with
      | Var(_,_) -> rev_assocd tm ilist tm
      | Const(_,_) -> tm
      | Quote(e) -> if hole_free e then tm 
                    else Quote(holeSub ilist e)
      | Eval(e,ty) -> (match ilist with
                       | [(t,x)] when t = x -> tm
                       | [(t,x)] -> Comb(Abs(x,tm),t)
                       | _ -> failwith "More than one substitution into an evaluation.")
      | Comb(s,t) -> let s' = vsubst ilist s and t' = vsubst ilist t in
                     if s' == s && t' == t then tm else Comb(s',t')
      | Abs(v,s) -> let ilist' = filter (fun (t,x) -> x <> v) ilist in
                    if ilist' = [] then tm else
                    let s' = vsubst ilist' s in
                    if s' == s then tm else 
                    let is_s_eval_free = eval_free s in     
                    let efficient_list = map (fun (t_term, x_var) -> (t_term,x_var,eval_free t_term,vfree_in v t_term, vfree_in x_var s)) ilist' in
                    (* There are no variable captures. *)
                    if forall (fun (t, x, is_ev_free_t, v_free_in_t, x_free_in_s) ->
                      (is_ev_free_t && (not (v_free_in_t))) || 
                      (is_s_eval_free && (not (x_free_in_s))) ||
                      not_effective_in v t ||
                      not_effective_in x s) efficient_list 
                    then Abs(v,s') 
                    else (* Resolvable Substitution. *)
                    if is_s_eval_free && forall (fun (_,_,is_ev_free_t,_,_) -> is_ev_free_t) efficient_list then 
                      let v' = variant [s'] v in
                      Abs(v',vsubst ((v',v)::ilist') s)
                    else (* There is a variable capture. *)
                    (match ilist with
                      | [(t,x)] -> Comb(Abs(x,tm),t)
                      | _ -> failwith "More than one substitution into an abstraction with a resolved substitution.") 
    in 
    fun theta ->
      if theta = [] then (fun tm -> tm) else
      if forall (function (t,Var(_,y)) -> Pervasives.compare (type_of t) y = 0 
                        | _ -> false) theta
      then vsubst theta else failwith "vsubst: Bad substitution list"

(* ------------------------------------------------------------------------- *)
(* Type instantiation primitive.                                             *)
(* ------------------------------------------------------------------------- *)

  exception Clash of term

  let rec qinst =

   let rec oinst env tyin tm =
      match tm with
        Var(n,ty)   -> let ty' = type_subst tyin ty in
                       let tm' = if ty' == ty then tm else Var(n,ty') in
                       if Pervasives.compare (rev_assocd tm' env tm) tm = 0
                       then tm'
                       else raise (Clash tm')
      | Const(c,ty) -> let ty' = type_subst tyin ty in
                       if ty' == ty then tm else Const(c,ty')
      | Quote(e)    -> let newquo = (qinst tyin e) in Quote(newquo) 
      | Comb(f,x)   -> let f' = oinst env tyin f and x' = oinst env tyin x in
                       if f' == f && x' == x then tm else Comb(f',x')
      | Abs(y,t)    -> let y' = oinst [] tyin y in
                       let env' = (y,y')::env in
                       try let t' = oinst env' tyin t in
                           if y' == y && t' == t then tm else Abs(y',t')
                       with (Clash(w') as ex) ->
                       if w' <> y' then raise ex else
                       let ifrees = map (oinst [] tyin) (frees t) in
                       let y'' = variant ifrees y' in
                       let z = Var(fst(dest_var y''),snd(dest_var y)) in
                       oinst env tyin (Abs(z,vsubst[z,y] t)) in

    let rec qinst env tyin tm =
       match tm with
        | Comb(l,r) -> Comb(qinst env tyin l, qinst env tyin r)
        | Hole(e,ty) -> Hole(oinst env tyin e,ty)
        | Quote(e) -> Quote(qinst env tyin e)
        | _ -> tm
    in

    fun tyin -> if tyin = [] then fun tm -> tm else qinst [] tyin



  let inst =

    let rec inst env tyin tm =
      match tm with
        Var(n,ty)   -> let ty' = type_subst tyin ty in
                       let tm' = if ty' == ty then tm else Var(n,ty') in
                       if Pervasives.compare (rev_assocd tm' env tm) tm = 0 
                       then tm'
                       else raise (Clash tm')
      | Const(c,ty) -> let ty' = type_subst tyin ty in
                       if ty' == ty then tm else Const(c,ty')
      | Quote(e)-> let newquo = (qinst tyin e) in Quote(newquo)
      | Comb(f,x)   -> let f' = inst env tyin f and x' = inst env tyin x in
                       if f' == f && x' == x then tm else Comb(f',x')
      | Abs(y,t)    -> (let y' = inst [] tyin y in
                       let env' = (y,y')::env in
                       try let t' = inst env' tyin t in
                           if y' == y && t' == t then tm else Abs(y',t')
                       with (Clash(w') as ex) ->
                       if w' <> y' then raise ex else
                       let ifrees = map (inst [] tyin) (frees t) in
                       let y'' = variant ifrees y' in
                       let z = Var(fst(dest_var y''),snd(dest_var y)) in
                       inst env tyin (Abs(z,vsubst[z,y] t))) 
      | Hole(e,ty) -> Hole(inst env tyin e,ty)
      | Eval(e,ty) -> Eval(inst env tyin e,ty)

      in

    fun tyin -> if tyin = [] then fun tm -> tm else inst [] tyin

(* ------------------------------------------------------------------------- *)
(* A few bits of general derived syntax.                                     *)
(* ------------------------------------------------------------------------- *)

  let rator tm =
    match tm with
      Comb(l,r) -> l
    | _ -> failwith "rator: Not a combination"

  let rand tm =
    match tm with
      Comb(l,r) -> r
    | _ -> failwith "rand: Not a combination"


(* ------------------------------------------------------------------------- *)
(* Useful to have term union modulo alpha-conversion for assumption lists.   *)
(* ------------------------------------------------------------------------- *)


  let rec ordav env x1 x2 =
    match env with
      [] -> Pervasives.compare x1 x2
    | (t1,t2)::oenv -> if Pervasives.compare x1 t1 = 0 
                       then if Pervasives.compare x2 t2 = 0 
                            then 0 else -1
                       else if Pervasives.compare x2 t2 = 0 then 1
                       else ordav oenv x1 x2

  let rec orda env tm1 tm2 =
    if tm1 == tm2 && forall (fun (x,y) -> x = y) env then 0 else
    match (tm1,tm2) with
      Var(x1,ty1),Var(x2,ty2) -> ordav env tm1 tm2
    | Const(x1,ty1),Const(x2,ty2) -> Pervasives.compare tm1 tm2
    | Comb(s1,t1),Comb(s2,t2) ->
          let c = orda env s1 s2 in if c <> 0 then c else orda env t1 t2
    | Abs(Var(_,ty1) as x1,t1),Abs(Var(_,ty2) as x2,t2) ->
          let c = Pervasives.compare ty1 ty2 in
          if c <> 0 then c else orda ((x1,x2)::env) t1 t2
    | Quote(e1),Quote(e2) -> orda env e1 e2
    | Hole(e1,t1),Hole(e2,t2) when t1 = t2 -> orda env e1 e2
    | Eval(e1,t1),Eval(e2,t2) when t1 = t2 -> orda env e1 e2 
    | Const(_,_),_ -> -1
    | _,Const(_,_) -> 1
    | Var(_,_),_ -> -1
    | _,Var(_,_) -> 1
    | Comb(_,_),_ -> -1
    | _,Comb(_,_) -> 1
    | Quote(_),_ -> -1
    | _,Quote(_) -> 1  
    | Hole(_,_),_ -> -1
    | _,Hole(_,_) -> 1
    | Eval(_,_),_ -> -1
    | _,Eval(_,_) -> 1

  let alphaorder = orda []

  let rec term_union l1 l2 =
    match (l1,l2) with
      ([],l2) -> l2
    | (l1,[]) -> l1
    | (h1::t1,h2::t2) -> let c = alphaorder h1 h2 in
                         if c = 0 then h1::(term_union t1 t2)
                         else if c < 0 then h1::(term_union t1 l2)
                         else h2::(term_union l1 t2)

  let rec term_remove t l =
    match l with
      s::ss -> let c = alphaorder t s in
               if c > 0 then
                 let ss' = term_remove t ss in
                 if ss' == ss then l else s::ss'
               else if c = 0 then ss else l
    | [] -> l

  let rec term_image f l =
    match l with
      h::t -> let h' = f h and t' = term_image f t in
              if h' == h && t' == t then l else term_union [h'] t'
    | [] -> l

(* ------------------------------------------------------------------------- *)
(* Basic theorem destructors.                                                *)
(* ------------------------------------------------------------------------- *)

  let dest_thm (Sequent(asl,c)) = (asl,c)

  let hyp (Sequent(asl,c)) = asl

  let concl (Sequent(asl,c)) = c

(* ------------------------------------------------------------------------- *)
(* Basic equality properties; TRANS is derivable but included for efficiency *)
(* ------------------------------------------------------------------------- *)

  let REFL tm =
    Sequent([],safe_mk_eq tm tm)

  let TRANS (Sequent(asl1,c1)) (Sequent(asl2,c2)) =
    match (c1,c2) with
      Comb((Comb(Const("=",_),_) as eql),m1),Comb(Comb(Const("=",_),m2),r)
        when alphaorder m1 m2 = 0 -> Sequent(term_union asl1 asl2,Comb(eql,r))
    | _ -> failwith "TRANS"

(* ------------------------------------------------------------------------- *)
(* Congruence properties of equality.                                        *)
(* ------------------------------------------------------------------------- *)

  let MK_COMB(Sequent(asl1,c1),Sequent(asl2,c2)) =
     match (c1,c2) with
       Comb(Comb(Const("=",_),l1),r1),Comb(Comb(Const("=",_),l2),r2) ->
        (match type_of r1 with
           Tyapp("fun",[ty;_]) when Pervasives.compare ty (type_of r2) = 0
             -> Sequent(term_union asl1 asl2,
                        safe_mk_eq (Comb(l1,l2)) (Comb(r1,r2)))
         | _ -> failwith "MK_COMB: types do not agree")
     | _ -> failwith "MK_COMB: not both equations"

  let ABS v (Sequent(asl,c)) =
    match (v,c) with
      Var(_,_),Comb(Comb(Const("=",_),l),r) when not(exists (vfree_in v) asl)
         -> Sequent(asl,safe_mk_eq (Abs(v,l)) (Abs(v,r)))
    | _ -> failwith "ABS";;

(* ------------------------------------------------------------------------- *)
(* Trivial case of lambda calculus beta-conversion.                          *)
(* ------------------------------------------------------------------------- *)

  let BETA tm =
    match tm with
      Comb(Abs(v,bod),arg) when Pervasives.compare arg v = 0 
        -> Sequent([],safe_mk_eq tm bod)
    | _ -> failwith "BETA: not a trivial beta-redex"

(* ------------------------------------------------------------------------- *)
(* Rules connected with deduction.                                           *)
(* ------------------------------------------------------------------------- *)

  let ASSUME tm =
    if Pervasives.compare (type_of tm) bool_ty = 0 then Sequent([tm],tm)
    else failwith "ASSUME: not a proposition"

  let EQ_MP (Sequent(asl1,eq)) (Sequent(asl2,c)) =
    match eq with
      Comb(Comb(Const("=",_),l),r) when alphaorder l c = 0
        -> Sequent(term_union asl1 asl2,r)
    | _ -> failwith "EQ_MP"

  let DEDUCT_ANTISYM_RULE (Sequent(asl1,c1)) (Sequent(asl2,c2)) =
    let asl1' = term_remove c2 asl1 and asl2' = term_remove c1 asl2 in
    Sequent(term_union asl1' asl2',safe_mk_eq c1 c2)

(* ------------------------------------------------------------------------- *)
(* Type and term instantiation.                                              *)
(* ------------------------------------------------------------------------- *)

  let INST_TYPE theta (Sequent(asl,c)) =
    let inst_fn = inst theta in
    Sequent(term_image inst_fn asl,inst_fn c)

  let INST theta (Sequent(asl,c)) =
    let inst_fun = vsubst theta in
    Sequent(term_image inst_fun asl,inst_fun c)


  let rec varInAsl asl = match asl with
  | a :: rest -> (is_var (fst (dest_eq (a)))) || (varInAsl rest)
  | [] -> false 

  (*Causing CONV_TAC error?*)
  let rec makeVarToSub asl tm = match asl with
  | a :: rest -> let l,r = dest_eq a in
  if is_var l then
  makeVarToSub rest (Comb(Abs(l,tm),r))
  else makeVarToSub rest tm
  | [] -> tm

  (*Conversion functions to handle hole rewrites on a lower level*)
  let rec QSUB_CONV (conv:term->thm) tm nConv = match tm with
    | Comb(l,r) -> let ls = (try QSUB_CONV conv l nConv with Failure _ -> REFL l) in
                   let rs = (try QSUB_CONV conv r nConv with Failure _ -> REFL r) in
                   let lasl,cl = dest_thm ls in
                   let rasl,cr = dest_thm rs in
                   let clls,clrs = dest_eq cl in
                   let crls,crrs = dest_eq cr in
                   if clls = clrs && crls = crrs then failwith "QSUB_CONV" else 
                   let convedComb = Comb(clrs,crrs) in
                   Sequent ((lasl @ rasl),safe_mk_eq tm convedComb)
    | Quote(e) -> let newThm = (QSUB_CONV conv e nConv) in 
                  let asl,c = dest_thm newThm in
                  let ls,rs = dest_eq c in
                  Sequent (asl,safe_mk_eq (mk_quote ls) (mk_quote rs))
    | Hole(e,ty) -> let newThm = (nConv conv e) in
                    let asl,c = dest_thm newThm in
                    let ls,rs = dest_eq c in
                    Sequent (asl,safe_mk_eq (mk_hole (ls, ty)) (mk_hole (rs, ty)))
    (*This should not cause any issues on the assumption that a quote will never contain an eval inside it*)
    | Eval(e,ty) -> if not (varInAsl (fst (dest_thm (conv e)))) then
                    let newThm = (nConv conv e) in
                    let asl,c = dest_thm newThm in
                    let ls,rs = dest_eq c in
                    (*The middle evaluates to nothing, check if the term itself can be switched out*)
                    if ls = rs then
                    let newThm = (nConv conv tm) in
                    let asl,c = dest_thm newThm in
                    let ls,rs = dest_eq c in 
                    Sequent (asl,safe_mk_eq ls rs)
                    else
                    Sequent (asl,safe_mk_eq (mk_eval (ls,ty)) (mk_eval (rs,ty)))
                    else
                    (*What to do when there is a variable substitution*)
                    let asl, c = dest_thm (nConv conv e) in
                    let ls,rs = dest_eq c in
                    Sequent (asl, safe_mk_eq (mk_eval (ls,ty)) (mk_eval (rs,ty)))
    | _ -> failwith "QSUB_CONV"

  (*Conversion function to handle hole rewrites on a lower level*)
  let rec QBETA_CONV tm nConv = match tm with
    | Comb(l,r) -> let ls = (try QBETA_CONV l nConv with Failure _ -> REFL l) in
                   let rs = (try QBETA_CONV r nConv with Failure _ -> REFL r) in
                   let lasl,cl = dest_thm ls in
                   let rasl,cr = dest_thm ls in
                   let clls,clrs = dest_eq cl in
                   let crls,crrs = dest_eq cr in
                   if clls = clrs && crls = crrs then failwith "QBETA_CONV" else 
                   let convedComb = Comb(snd(dest_eq(concl ls)),snd(dest_eq(concl rs))) in
                   Sequent ((lasl @ rasl),safe_mk_eq tm convedComb)
    | Quote(e) -> let newThm = (QBETA_CONV e nConv) in 
                     let asl,c = dest_thm newThm in
                     let ls,rs = dest_eq c in
                     Sequent (asl,safe_mk_eq (mk_quote ls) (mk_quote rs))
    | Hole(e,ty) -> let newThm = (nConv e) in
                    let asl,c = dest_thm newThm in
                    let ls,rs = dest_eq c in
                    Sequent (asl,safe_mk_eq (mk_hole (ls, ty)) (mk_hole (rs, ty)))
    | _ -> failwith "QBETA_CONV"


(* ------------------------------------------------------------------------- *)
(* Construction handling.                                                    *)
(* ------------------------------------------------------------------------- *)

(*First a bunch of definitions normally defined later during HOL's startup process must be defined*)
(*The purpose of all these is to implement an early version of mk_string so that epsilon's type types may be constructed*)
  let makeConstructedType name list = (Tyapp (name,list));;
  let makeBasicType name = makeConstructedType name [];;
  let makeFalse = Const("F",(makeBasicType "bool"));;
  let makeTrue = Const("T",(makeBasicType "bool"));;
  (*This makes a function called ASCII of type bool->bool->bool->bool->bool->bool->bool->bool->char*)
  let makeAscii = Const("ASCII",(makeConstructedType "fun" [(makeBasicType "bool");(makeConstructedType "fun" [(makeBasicType "bool");(makeConstructedType "fun" [(makeBasicType "bool");(makeConstructedType "fun" [
(makeBasicType "bool");(makeConstructedType "fun" [(makeBasicType "bool");(makeConstructedType "fun" [(makeBasicType "bool");(makeConstructedType "fun" [(makeBasicType "bool");(makeConstructedType "fun" [
(makeBasicType "bool");(makeBasicType "char")])])])])
])])])]));;

  (*This makes a function called CONS of type char -> (list)char -> list(char)*)
  let makeCONS = Const("CONS",makeConstructedType "fun" [makeBasicType "char"; makeConstructedType "fun" [makeConstructedType "list" [makeBasicType "char"];makeConstructedType "list" [makeBasicType "char"]]]);;
  
  let numToBool = function
    | 1 -> makeTrue
    | 0 -> makeFalse
    | _ -> failwith "Cannot convert this number to a boolean value"

(*Converts a char value to a combination of T's and F's representing the binary form of it's ASCII value (HOL stores it this way)*)

  let rec charToHOL c depth = if depth < 8 then Comb((charToHOL (c / 2) (depth + 1)),(numToBool (c mod 2)))
  else Comb(makeAscii,(numToBool (c mod 2)));;

(*Takes an exploded string and turns it into a HOL string*)
  let rec tmp_mk_string = function
    | [] -> Const("NIL",makeConstructedType "list" [makeBasicType "char"])
    | a :: rest -> Comb(Comb(makeCONS,(charToHOL (Char.code (a.[0])) 1)),(tmp_mk_string rest));;

(*Takes a list of eight 1s and 0s and reads it as a binary number to return a decimal number*)
 let binToDec l p = 
  let rec innerConv l p = 
    match l with
    | [] -> 0
    | a :: rest -> (int_of_float ((float_of_int a) *. (2. ** (float_of_int p)))) + (innerConv rest (p - 1))
  in
 if List.length l = 8 then innerConv l p else failwith "Cannot convert non 8-bit number";;

(*Reads a character back as HOL input*)
  let translateChar = function
    | Comb(Comb(Comb(Comb(Comb(Comb(Comb(Comb(Const("ASCII",_),b1),b2),b3),b4),b5),b6),b7),b8) -> String.make 1 (Char.chr (binToDec (List.map (fun a -> let b = fst (dest_const a) in if b = "T" then 1 else 0) [b1;b2;b3;b4;b5;b6;b7;b8]) 7))
    | _ -> failwith "Not an HOL character";;

(*Takes a string in HOL's list format and turns it back into an Ocaml string*)
  let rec readStringList = function
    | Comb(Comb(Const("CONS",_),str),next) -> translateChar str :: (readStringList next)
    | Const("NIL",_) -> []
    | _ -> failwith "Not a valid string";;

  (*Need a temporary implementation of mk_string and related functions*)

  (*Helper functions to make vital functions more readable*)
  let makeHolFunction a b = Tyapp("fun",[a;b]);;
  let makeHolType a b = Tyapp(a,b);;
  let makeGenericComb constName ty firstArg secondArg = Comb(Comb(Const(constName,ty),firstArg),secondArg);;
  let makeQuoVarComb a b = makeGenericComb "QuoVar" (makeHolFunction (makeHolType "list" [makeHolType "char" []]) (makeHolFunction (makeHolType "type" []) (ep_ty)) ) (tmp_mk_string (explode a)) b;;
  let makeQuoConstComb a b = makeGenericComb "QuoConst" (makeHolFunction (makeHolType "list" [makeHolType "char" []]) (makeHolFunction (makeHolType "type" []) (ep_ty)) ) (tmp_mk_string (explode a)) b;;
  let makeAppComb a b = makeGenericComb "App" (makeHolFunction (ep_ty) (makeHolFunction (ep_ty) (ep_ty))) a b;;
  let makeAbsComb a b = makeGenericComb "Abs" (makeHolFunction (ep_ty) (makeHolFunction (ep_ty) (ep_ty))) a b;;
  let makeTyVarComb a = Comb(Const("TyVar",makeConstructedType "fun" [makeConstructedType "list" [makeBasicType "char"];makeBasicType "type"]),(tmp_mk_string (explode a)));;
  let makeTyBaseComb a  = Comb(Const("TyBase",makeConstructedType "fun" [makeConstructedType "list" [makeBasicType "char"];makeBasicType "type"]),(tmp_mk_string (explode a)));;
  let makeTyMonoConsComb a b = makeGenericComb "TyMonoCons" (makeHolFunction (makeHolType "list" [makeHolType "char" []]) (makeHolFunction (makeHolType "type" []) (makeHolType "type" []))) (tmp_mk_string (explode a)) b;;
  let makeTyBiConsComb a b c= Comb((makeGenericComb "TyBiCons" (makeHolFunction (makeHolType "list" [makeHolType "char" []]) (makeHolFunction (makeHolType "type" []) (makeHolFunction (makeHolType "type" []) (makeHolType "type" [])))) (tmp_mk_string (explode a)) b),c);;
  let makeFunComb a b = makeTyBiConsComb "fun" a b;;
  let makeQuoComb a = Comb(Const("Quo",(makeHolFunction (ep_ty) (ep_ty))),a);;

  let rec construction_type tm = 
    let strip_func tm =
      match tm with 
        | Comb(Comb(Comb(Const("TyBiCons",ty),tyName),ty1),ty2) -> ty2
        | _ -> failwith "not a function type!"
    in
    match tm with 
      | Comb(Comb(Const("QuoVar",ty),vname),vty) -> vty
      | Comb(Comb(Const("QuoConst", ty), cname), cty) -> cty
      | Comb(Const("Quo", ty), e) -> makeTyBaseComb "epsilon"
      | Comb(Comb(Const("App", ty), func), arg) -> strip_func (construction_type func)
      | Comb(Comb(Const("Abs", ty), var), body) ->
          Comb((makeGenericComb "TyBiCons" (makeHolFunction (makeHolType "list" [makeHolType "char" []]) (makeHolFunction (makeHolType "type" []) (makeHolFunction (makeHolType "type" []) (makeHolType "type" [])))) (tmp_mk_string (explode "fun")) (construction_type var)),construction_type body)
      | _ -> failwith "Not a proper construction." 

(* type -> term (used in termToConstruction) *)
  let rec matchType ty = 
      if (is_vartype ty) then makeTyVarComb (dest_vartype ty) else
        let a,b = (dest_type ty) in
        match length b with
          | 0 -> makeTyBaseComb a
          | 1 -> makeTyMonoConsComb a (matchType (hd b))
          | 2 -> makeTyBiConsComb a (matchType (hd b)) (matchType (hd (tl b)))
          | _ -> failwith "This is not a valid type";;

(* term -> type (used in constructionToType) *)
  let rec revTypeMatch = function
      |  Comb(Const("TyVar",_),tName) -> Tyapp ((implode (readStringList tName)),[])
      |  Comb(Const("TyBase",_),tName) -> Tyapp((implode (readStringList tName)),[])
      |  Comb(Comb(Const("TyMonoCons",_),tName),sType) -> Tyapp ((implode (readStringList tName)),[revTypeMatch sType])
      |  Comb(Comb(Comb(Const("TyBiCons",_),tName),sType),tType) -> Tyapp ((implode (readStringList tName)),[revTypeMatch sType;revTypeMatch tType])
      | _ -> failwith "Invalid type";;


(* Checks if term is a proper instance of a defined constant for constructionToTerm *)
  let rec properConst tm = match tm with 
      | Const(cname, ty) -> 
        if can get_const_type cname then  
          let polyTy = get_const_type cname in 
          if is_defined_type ty then
            (* Checks if Constant is an instance of a defined term constant *)
            let rec occuranceOf polyTm tm (tyVar, tyApp) = match polyTm with
              | Const(nm, tp) ->
                if (type_vars_in_term polyTm) = [] then (polyTm = tm)
                else match (tyVar, tyApp) with
                  | (Tyapp(tyName, [x]), Tyapp(appName, [y])) when (tyName = appName) && not (is_defined_type x) -> 
                      occuranceOf polyTm tm (x, y) 
                  | (Tyapp (tyName, [x1;x2]), Tyapp(appName, [y1;y2])) when (tyName = appName) ->
                      if not (is_defined_type x1) then occuranceOf polyTm tm (x1, y1)
                      else if not (is_defined_type x2) then occuranceOf polyTm tm (x2, y2)
                      else polyTm = tm
                  | (Tyvar _, Tyapp _) ->
                      occuranceOf (Const(nm, type_subst [(tyApp, tyVar)] (type_of polyTm))) tm ((type_subst [(tyApp, tyVar)] (type_of polyTm)), type_of tm)
                  | _ -> failwith "Not a constant" in
            occuranceOf (Const(cname, polyTy)) tm (polyTy, ty)
          else failwith "Not a constant"
        else failwith "Not a constant"
      | _ -> failwith "Not a constant" 

  let rec termToConstruction = function
      |  Const(cName,cType) -> makeQuoConstComb cName (matchType cType)
      |  Var(vName,vType) -> makeQuoVarComb vName (matchType vType)
      |  Comb(exp1, exp2) -> makeAppComb (termToConstruction exp1) (termToConstruction exp2)
      |  Abs(exp1, exp2) -> makeAbsComb (termToConstruction exp1) (termToConstruction exp2)
      |  Quote(e) -> makeQuoComb (termToConstruction e)
      |  Hole(e,ty) -> e
      |  _ -> failwith "Malformed term cannot be made into a construction"

  let TERM_TO_CONSTRUCTION_CONV tm = 
    let termToCon = termToConstruction tm in 
    if termToCon = tm then failwith "TERM_TO_CONSTRUCTION_CONV: Already a construction."
    else Sequent([], safe_mk_eq tm termToCon)

  let rec constructionToTerm = function
      | Comb(Comb(Const("QuoConst",_),strList),tyConv) ->
          let con = (Const(implode(readStringList strList), revTypeMatch tyConv)) in
          if properConst con then con  
          else failwith "Not a proper construction" 
      | Comb(Comb(Const("QuoVar",_),strList),tyConv) -> mk_var(implode (readStringList strList),revTypeMatch tyConv)
      | Comb(Comb(Const("App",_),t1),t2) -> mk_comb(constructionToTerm t1,constructionToTerm t2)
      | Comb(Comb(Const("Abs",_),t1),t2) -> mk_abs(constructionToTerm t1,constructionToTerm t2)
      | Comb(Const("Quo",_),t) -> mk_quote(constructionToTerm t)
      | _ -> failwith "constructionToTerm: not a proper construction"

  let CONSTRUCTION_TO_TERM_CONV tm = 
    let rec ctt trm = 
      match trm with
        | Comb(f,a) ->
            if can constructionToTerm trm then constructionToTerm trm else Comb(ctt f, ctt a)
        | Abs(v,b) -> Abs(ctt v, ctt b) 
        | Eval(e,ty) -> Eval(ctt e, ty)
        | Quote(e) -> Quote(ctt e) 
        | _ -> trm
    in 
    let conToTerm = ctt tm in 
    if conToTerm = tm then failwith "CONSTRUCTION_TO_TERM_CONV: No constructions in term."
    else Sequent([], safe_mk_eq tm conToTerm)

  let rec is_construction tm = 
    match tm with 
      | Comb(Comb(Const("QuoVar",_),_),_) -> true
      | Comb(Comb(Const("QuoConst", _), _), _) -> true
      | Comb(Const("Quo", ty), e) -> is_construction e
      | Comb(Comb(Const("App", _), func), arg) -> is_construction func && is_construction arg
      | Comb(Comb(Const("Abs", _), var), body) -> is_construction var && is_construction body 
      | _ when type_of tm = ep_ty -> true 
      | _ -> failwith "Not a construction"

  let is_proper_construc c = can constructionToTerm c 

  let proper_e_term tm = is_proper_construc tm || is_quote tm || is_construction tm

(* ------------------------------------------------------------------------ *)
(* Inference rule of quotation.                                             *)
(* ------------------------------------------------------------------------ *)

  let LAW_OF_QUO tm = match tm with
    | Var(_) | Const(_) | Comb(_) | Abs(_) | Quote(_) | Hole(_) -> 
        (match is_eval_free tm with 
          | Ok -> Sequent([],safe_mk_eq (mk_quote tm) (termToConstruction tm))
          | Issue t -> raise (Problem("LAW_OF_QUO- Cannot quote terms with evaluations. This term contains one:", t)))
    | Eval(_) -> failwith "LAW_OF_QUO: Cannot quote an evaluation" 

  let LAW_OF_QUO_CONV = LAW_OF_QUO 

(* ------------------------------------------------------------------------- *)
(* Quotation handling.                                                       *)
(* ------------------------------------------------------------------------- *)

  let QUOTE_TO_CONSTRUCTION_CONV tm = 
    let rec qtc trm = 
      match trm with
        | Comb(f,a) -> Comb(qtc f, qtc a)
        | Abs(v,b) -> Abs(qtc v, qtc b) 
        | Eval(e,ty) -> Eval(qtc e, ty)
        | Quote(e) -> termToConstruction e 
        | _ -> trm
    in 
    let qToCon = qtc tm in 
    if qToCon = tm then failwith "QUOTE_TO_CONSTRUCTION_CONV: No quotations in term."
    else Sequent([], safe_mk_eq tm qToCon) 


  let CONSTRUCTION_TO_QUOTE_CONV tm =
    let rec ctq trm =  
      match trm with 
        | Comb(f,a) -> if can constructionToTerm trm then Quote(constructionToTerm trm)
                       else Comb(ctq f, ctq a)
        | Abs(v,b) -> Abs(v, ctq b)
        | Eval(e,ty) -> Eval(ctq e, ty)
        | Quote(e) -> Quote(ctq e)
        | Hole(e,ty) -> Hole(ctq e, ty)
        | _ -> trm 
    in
    let cToQ = ctq tm in 
    if cToQ = tm then failwith "CONSTRUCTION_TO_QUOTE_CONV: No constructions to convert to quotes."
    else Sequent([], safe_mk_eq tm cToQ) 

  (* These functions remove the holes from a term *) 
  let rec absorbFilledHoles = function
    | Const(a,ty) -> Const(a,ty)    
    | Var(a,ty) -> Var(a,ty)
    | Comb(l,r) -> Comb(absorbFilledHoles l, absorbFilledHoles r)
    | Abs(l,r) -> Abs(absorbFilledHoles l, absorbFilledHoles r)
    | Quote(a) -> Quote(absorbFilledHoles a) 
    | Hole(e,ty) when ((is_quote e) && (type_of (dest_quote e)) = ty) -> (dest_quote e)
    | _ -> failwith "no trivial holes to remove"

  (*HOLE_ABSORB will "cancel" out the hole and quotation operators*)
  (*For example, (Q_ H_ Q_ 3 _Q _H _Q) = Q_ 3 _Q*)
  let HOLE_ABSORB trm = match trm with
    | Quote(e) -> Sequent([],safe_mk_eq trm (absorbFilledHoles trm )) 
    | _ -> failwith "HOLE_ABSORB: THIS IS NOT A QUOTE"

  (*Convert to automatically HOLE_ABSORB any possible quotes in first "layer" of a term, will fail if any holes are not "filled in"*)
  let HOLE_ABSORB_CONV tm = 
    let rec unqint trm =
      (match trm with
        | Comb(a,b) -> Comb(unqint a, unqint b)
        | Abs(a,b) -> Abs(unqint a, unqint b)
        | Quote(e) when can absorbFilledHoles e -> let muq = absorbFilledHoles e in Quote(muq)
        | Hole(e,ty) -> failwith "HOLE_ABSORB_CONV: Hole outside quotaton"
        | Eval(e,ty) -> Eval(unqint e, ty)
        | other -> other) in
    let ntm = unqint tm in
    if tm = ntm then failwith "HOLE_ABSORB_CONV" else
    Sequent([],safe_mk_eq tm ntm)


(* ------------------------------------------------------------------------- *)
(* Inference rules of evaluation.                                            *)
(* ------------------------------------------------------------------------- *)

  let LAW_OF_DISQUO tm = 
    match (is_eval_free tm),(is_hole_free tm) with
      | (Ok,Ok) -> Sequent([], safe_mk_eq (mk_eval((mk_quote tm), type_of tm)) tm)
      | (Issue t,Ok) -> raise (Problem("Theorem only applies to eval-free terms, this term has an evaluation:", t))
      | (Ok, Issue t) -> raise (Problem("Theorem only applies to hole-free terms, this term has a hole:", t))
      | (Issue t1,Issue t2) -> 
          raise (Problem("Theorem only applies to hole and eval-free terms. This term has both! Here is the evaluation:", t1))

  let LAW_OF_DISQUO_CONV tm = 
    let rec disquo trm = match trm with 
      | Abs(v,b) -> Abs(disquo v, disquo b)
      | Comb(f,a) -> Comb(disquo f, disquo a)
      | Eval(e,ty) when is_quote e && hole_free e -> 
          if type_of (dest_quote e) = ty then (dest_quote e) 
          else failwith "Type of evaluation does not match the type of the term represented by the construction"
      | _ -> trm  
    in 
    let disquoTm = disquo tm in 
    if disquoTm = tm then failwith "LAW_OF_DISQUO_CONV: Nothing to diquote."
    else Sequent([], safe_mk_eq tm disquoTm)


  (*Defining functions and Constants for making axioms easier to implement*)
  let internal_make_conj a b = Comb(Comb(Const("/\\",makeHolFunction (bool_ty) (makeHolFunction (bool_ty) (bool_ty))),a),b)

  let internal_make_disj a b = Comb(Comb(Const("\\/",makeHolFunction (bool_ty) (makeHolFunction (bool_ty) (bool_ty))),a),b)

  let internal_make_imp a b = Comb(Comb(Const("==>",makeHolFunction (bool_ty) (makeHolFunction (bool_ty) (bool_ty))),a),b)

  let is_expr_ty = Const("isExprType",makeHolFunction (ep_ty) (makeHolFunction (makeHolType "type" []) (bool_ty)))

  (* Axiom B10, (B10.1 and 10.2 are subsumed by the LAW OF DISQUOTATION.) *)

  let QUO_DISQUO tm = 
    if type_of tm = ep_ty then 
      let term1,ty = (if is_construction tm then tm,(construction_type tm) 
                      else let q = dest_quote tm in (termToConstruction q), matchType (type_of q)) in   
      let iet = Comb(Comb(is_expr_ty,term1),ty) in
      Sequent([],(internal_make_imp iet (safe_mk_eq (Eval(Comb(Const("Quo",makeHolFunction (ep_ty) (ep_ty)),term1),ep_ty)) term1)))
    else failwith "QUO_DISQUO: term must be of type epsilon"

  (* Input 2 proper epsilon terms, the first of which MUST represent a variable *)
  let ABS_DISQUO var tm  =
    if (not (proper_e_term var)) or (not (proper_e_term tm)) then failwith "ABS_DISQUO: Invalid terms, they must either be quotations or proper constructions" 
    else 
      let v_term = (if is_proper_construc var then constructionToTerm var else dest_quote var) in
      let term1 = (if is_proper_construc var then var else termToConstruction(dest_quote var)) in
      let term2 = (if is_construction tm then tm else termToConstruction(dest_quote tm)) in 
      let fun_ty = makeHolFunction (type_of v_term) (revTypeMatch(construction_type term2)) in
      match fun_ty with
        | Tyapp("fun",[dom;ran]) -> 
            let ran_ty = matchType ran in 
            let iet =  mk_comb(mk_comb(is_expr_ty,term2),ran_ty) in
            let ifi = Comb(Const("~",(makeHolFunction bool_ty bool_ty)),Comb(Comb(Const("isFreeIn",makeHolFunction (ep_ty) (makeHolFunction (ep_ty) bool_ty)),term1),term2)) in
            let anticed = internal_make_conj iet ifi in 
            let conclud = safe_mk_eq (Eval(Comb(Comb(Const("Abs",makeHolFunction (ep_ty) (makeHolFunction (ep_ty) (ep_ty))),term1),term2),fun_ty)) (Abs(v_term,Eval(term2,ran))) in
            Sequent([], internal_make_imp anticed conclud) 
        | _ -> failwith "ABS_DISQUO: Improper type argument."


 (* Input 2 proper epsilon terms along with a function hol_type *)
  let APP_DISQUO tm1 tm2 = 
    if (not (proper_e_term tm1)) or (not (proper_e_term tm2)) then failwith "APP_DISQUO: Invalid terms, they must either be quotations or proper constructions" 
    else 
      let term1 = (if is_construction tm1 then tm1 else termToConstruction(dest_quote tm1)) in
      let term2 = (if is_construction tm2 then tm2 else termToConstruction(dest_quote tm2)) in 
      let fun_ty = revTypeMatch (construction_type term1) in
      match fun_ty with
        | Tyapp("fun",[dom;ran]) ->  
            let t1 = matchType fun_ty in
            let t2 = matchType dom in
            let iet1 =  Comb(Comb(is_expr_ty,term1),t1) in
            let iet2 =  Comb(Comb(is_expr_ty,term2),t2) in
            let anticed = internal_make_conj iet1 iet2 in  
            let conclud = safe_mk_eq (Eval(Comb(Comb(Const("App",makeHolFunction (ep_ty) (makeHolFunction (ep_ty) (ep_ty))),term1),term2),ran)) (Comb(Eval(term1,fun_ty),Eval(term2,dom))) in
            Sequent([], internal_make_imp anticed conclud)
        | _ -> failwith "APP_DISQUO: Third argument must be a function hol_type"


  (*Axiom B11.1 is subsumed by the BETA rule. *)

  (*Axiom B11.2*)

  let BETA_REDUCE_EVAL var arg body beta = 
    if not ((is_var var) && 
            ((type_of var) = (type_of arg)) &&
            ((type_of body) = ep_ty) &&
            ((is_type beta)))
    then failwith "BETA_REDUCE_EVAL: Improper arguments." 
    else
      let epsilonToTypeToBool = Tyapp ("fun",[(ep_ty);(Tyapp ("fun",[(Tyapp ("type",[]));(bool_ty)]))]) in
      let boolToBool = Tyapp ("fun",[(bool_ty);(bool_ty)]) in
      let epsilonToEpsilonToBool = Tyapp ("fun",[(ep_ty);(Tyapp ("fun",[(ep_ty);(bool_ty)]))]) in 
      let lambdaApp = Comb(Abs(var,body),arg) in 
      let iet = Comb(Comb(Const("isExprType",epsilonToTypeToBool),
                          lambdaApp),
                     (matchType beta)) in
      let ifi = Comb(Const("~",boolToBool),
                     Comb(Comb(Const("isFreeIn",epsilonToEpsilonToBool),
                               termToConstruction var),
                          lambdaApp)) in
      let lhs = Comb(Abs(var,Eval(body,beta)),arg) in
      let rhs = Eval(lambdaApp,beta) in
      let antecedent = internal_make_conj iet ifi in
      let succedent = safe_mk_eq lhs rhs in
      Sequent([], internal_make_imp antecedent succedent)


  (* Constructs a NOT-EFFECTIVE-IN term. *)
  let mk_not_effective_in var tm var_aux = 
    let mk_thm var tm var_aux varT = 
      let lhs = Comb(Abs(var,tm),var_aux) in 
      let body = safe_mk_eq lhs tm in
      let forallConst = Const("!", (Tyapp ("fun", [(Tyapp ("fun",[varT;bool_ty])); bool_ty]))) in
      let arg = Abs(var_aux, body) in
      Comb(forallConst,arg)
    in
    match var,var_aux with
      | Var(vN,vT),Var(avN,avT) when vN <> avN && vT = avT -> mk_thm var tm var_aux vT
      | _ -> failwith "mk_not_effective_in: Improper arguments"

  (* Constructs an EFFECTIVE-IN term *)
  let mk_effective_in var tm var_aux = Comb(Const("~",makeHolFunction bool_ty bool_ty),(mk_not_effective_in var tm var_aux))


  (*Axiom B12*)

  let EVAL_FREE_NOT_EFFECTIVE_IN var tm var_aux =
    if not ((is_var var) && 
            (is_var var_aux) && 
            ((type_of var) = (type_of var_aux)) &&
            (var <> var_aux) &&
            (eval_free tm))
    then failwith "EVAL_FREE_NOT_EFFECTIVE_IN: Improper arguments."
    else
      if vfree_in var tm
      then failwith ("EVAL_FREE_NOT_EFFECTIVE_IN: variable is free in term.")
      else Sequent([], mk_not_effective_in var tm var_aux)

  (*Axiom B13*)

  let BETA_REDUCE_ABS x x_aux y y_aux arg body =
    if not ((is_var x) && (is_var x_aux) && (is_var x) && (is_var y_aux) &&
            ((type_of x) = (type_of x_aux)) && ((type_of y) = (type_of y_aux)) &&
            (x <> x_aux) && (x <> y) && (x <> y_aux) &&
            (x_aux <> y) && (x_aux <> y_aux) && (y <> y_aux) &&
            ((type_of x) = type_of arg))
    then failwith "BETA_REDUCE_ABS: Improper arguments."
    else
      let nei1 = mk_not_effective_in y arg y_aux in
      let nei2 = mk_not_effective_in x body x_aux in
      let lhs = Comb(Abs(x,Abs(y,body)),arg) in
      let rhs = Abs(y,Comb(Abs(x,body),arg)) in
      let antecedent = internal_make_disj nei1 nei2 in
      let succedent = safe_mk_eq lhs rhs in
      Sequent([], internal_make_imp antecedent succedent)

  (* Theorem 6.2.1 (Beta-Reduction by Substitution) *)

  let BETA_RED_BY_SUB tm = 
    if is_comb tm && is_abs(fst(dest_comb tm)) then
      let ab,a = dest_comb tm in 
      let x,b = dest_abs ab in 
      Sequent([], safe_mk_eq tm (vsubst [(a,x)] b))
    else failwith "Improper arguments"  

  (*For evaluation substiution conversions to beta evaluations*)
  let EVAL_VSUB (tm:thm) (trm:term) = 
  if not (is_eval trm) then
  failwith "EVAL_VSUB"
  else
  let asl = fst (dest_thm tm) in
  if not (asl = []) then
  failwith "EVAL_VSUB: Assumptions not allowed in theorem"
  else
  let v,res = dest_eq (concl tm) in
  Sequent((fst (dest_thm tm)), (safe_mk_eq trm (Comb(Abs(v,trm),res))))

  let rec MATCH_ASMS_TO_EVAL asm tm full = 
      let rec VarInTerm vr trm = 
        let rec Q_VarInTerm vr trm = match trm with
          | Hole(t,ty) -> VarInTerm vr trm
          | Quote(t) -> Q_VarInTerm vr trm
          | Comb(a,b) -> (Q_VarInTerm vr trm) || (Q_VarInTerm vr trm)
          | _ -> false
        in
      match trm with
      | Var (_,_) -> (dest_var vr) = (dest_var trm)
      | Const (_,_) -> false
      | Comb (a,b) -> (VarInTerm vr a) || (VarInTerm vr b)
      | Abs (a,b) -> not ((dest_var vr) = (dest_var a)) && VarInTerm vr b
      | Quote (e) -> Q_VarInTerm vr e
      | Hole (e,ty) -> Q_VarInTerm vr e
      | Eval(e,ty) -> VarInTerm vr e
      in
      match asm with
      | a :: rest -> (try
      (*All failures result in skipping to the next item in the list*)
      let l,r = dest_eq a in 
      if not (is_var l) then fail() else
      if (VarInTerm l tm) then
      EVAL_VSUB (Sequent ([],safe_mk_eq l r)) tm
      else
      fail() 
    with Failure _ ->  MATCH_ASMS_TO_EVAL rest tm asm)
    | _ -> failwith "Unknown"
    | [] -> REFL tm
  (*Meant for use on goal states to apply assumptions availible in the goal to evals, such as when doing case analysis*)
  let rec EVAL_GOAL_VSUB (asm,tm) = 
  match tm with
  | Comb(a,b) | Abs(a,b) -> (try EVAL_GOAL_VSUB (asm,a) with Failure _ -> try EVAL_GOAL_VSUB (asm,b) with Failure _ -> failwith "EVAL_GOAL_VSUB")
  | Eval(e,b) -> (MATCH_ASMS_TO_EVAL asm tm asm)
  | _ -> failwith "EVAL_GOAL_VSUB"


(* ------------------------------------------------------------------------- *)
(* Handling of axioms.                                                       *)
(* ------------------------------------------------------------------------- *)

  let the_axioms = ref ([]:thm list)

  let axioms() = !the_axioms

  let new_axiom tm =
    if Pervasives.compare (type_of tm) bool_ty = 0 then
      let th = Sequent([],tm) in
       (the_axioms := th::(!the_axioms); th)
    else failwith "new_axiom: Not a proposition"

(* ------------------------------------------------------------------------- *)
(* Handling of (term) definitions.                                           *)
(* ------------------------------------------------------------------------- *)
  let the_definitions = ref ([]:thm list)

  let definitions() = !the_definitions

  let new_basic_definition tm =
    match tm with
      Comb(Comb(Const("=",_),Var(cname,ty)),r) ->
        if not(freesin [] r) then failwith "new_definition: term not closed"
        else if not (subset (type_vars_in_term r) (tyvars ty))
        then failwith "new_definition: Type variables not reflected in constant"
        else let c = new_constant(cname,ty); Const(cname,ty) in
             let dth = Sequent([],safe_mk_eq c r) in
             the_definitions := dth::(!the_definitions); dth
    | _ -> failwith "new_basic_definition"

(* ------------------------------------------------------------------------- *)
(* Handling of type definitions.                                             *)
(*                                                                           *)
(* This function now involves no logical constants beyond equality.          *)
(*                                                                           *)
(*             |- P t                                                        *)
(*    ---------------------------                                            *)
(*        |- abs(rep a) = a                                                  *)
(*     |- P r = (rep(abs r) = r)                                             *)
(*                                                                           *)
(* Where "abs" and "rep" are new constants with the nominated names.         *)
(* ------------------------------------------------------------------------- *)

  let new_basic_type_definition tyname (absname,repname) (Sequent(asl,c)) =
    if exists (can get_const_type) [absname; repname] then 
      failwith "new_basic_type_definition: Constant(s) already in use" else
    if not (asl = []) then
      failwith "new_basic_type_definition: Assumptions in theorem" else
    let P,x = try dest_comb c
              with Failure _ ->
                failwith "new_basic_type_definition: Not a combination" in
    if not(freesin [] P) then
      failwith "new_basic_type_definition: Predicate is not closed" else
    let tyvars = sort (<=) (type_vars_in_term P) in
    let _ = try new_type(tyname,length tyvars)
            with Failure _ ->
                failwith "new_basic_type_definition: Type already defined" in
    let aty = Tyapp(tyname,tyvars)
    and rty = type_of x in
    let absty = Tyapp("fun",[rty;aty]) and repty = Tyapp("fun",[aty;rty]) in
    let abs = (new_constant(absname,absty); Const(absname,absty))
    and rep = (new_constant(repname,repty); Const(repname,repty)) in
    let a = Var("a",aty) and r = Var("r",rty) in
    Sequent([],safe_mk_eq (Comb(abs,mk_comb(rep,a))) a),
    Sequent([],safe_mk_eq (Comb(P,r))
                          (safe_mk_eq (mk_comb(rep,mk_comb(abs,r))) r))

end;;

include Hol;;

(* ------------------------------------------------------------------------- *)
(* Stuff that didn't seem worth putting in.                                  *)
(* ------------------------------------------------------------------------- *)

let mk_fun_ty ty1 ty2 = mk_type("fun",[ty1; ty2]);;
let bty = mk_vartype "B";;

let is_eq tm =
  match tm with
    Comb(Comb(Const("=",_),_),_) -> true
  | _ -> false;;

let mk_eq =
  let eq = mk_const("=",[]) in
  fun (l,r) ->
    try let ty = type_of l in
        let eq_tm = inst [ty,aty] eq in
        mk_comb(mk_comb(eq_tm,l),r)
    with Failure _ -> failwith "mk_eq";;

(* ------------------------------------------------------------------------- *)
(* Tests for alpha-convertibility (equality ignoring names in abstractions). *)
(* ------------------------------------------------------------------------- *)

let aconv s t = alphaorder s t = 0;;

(* ------------------------------------------------------------------------- *)
(* Comparison function on theorems. Currently the same as equality, but      *)
(* it's useful to separate because in the proof-recording version it isn't.  *)
(* ------------------------------------------------------------------------- *)

let equals_thm th th' = dest_thm th = dest_thm th';;


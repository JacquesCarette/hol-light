(* Tactics that can be used outside of HOL Light QE *)


(* Searches assumption list top-down for first assumption of the form p \/ q  *)
(* and splits goal into subgoals with p and q added as respective assumptions *)
let (TOP_DISJ_CASES_TAC:tactic) =
  fun (asl,w) -> 
	let is_disj thm =  
      match (snd (dest_thm thm)) with 
        | Comb(Comb(Const("\\/",_),_),_) -> true
	    | _ -> false 
	in 
	match snd(dest_thm(find is_disj (snd(List.split (rev asl))))) with 
	  | Comb(_) as tm -> (DISJ_CASES_TAC(ASSUME tm)) (asl,w)
	  | _ -> failwith "No cases found.";;

(* Same as above but searches bottom-up *)
let (BOTTOM_DISJ_CASES_TAC:tactic) =
  fun (asl,w) -> 
	let is_disj thm =  
      match (snd (dest_thm thm)) with 
        | Comb(Comb(Const("\\/",_),_),_) -> true
	    | _ -> false 
	in 
	match snd(dest_thm(find is_disj (snd(List.split asl)))) with 
	  | Comb(_) as tm -> (DISJ_CASES_TAC(ASSUME tm)) (asl,w)
	  | _ -> failwith "No cases found.";;

(* Takes an implication theorem and removes all antecedants, as long as                *) 
(* they're in the assumption list, adding the conclusion to the antecedant of the goal *)
let MP_ASSUMPTION_TAC thm = 
  let rec remove_ante thm = 
    match snd(dest_thm thm) with 
      | Comb(Comb(Const("==>",_), t1),_) -> remove_ante(MP thm (ASSUME t1))
      | _ -> thm
  in 
  MP_TAC(remove_ante thm) THEN 
  REWRITE_TAC[];;



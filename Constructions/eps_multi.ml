needs "Constructions/eps_addition.ml";;

let mult_bin = define `
  (!x:bin. mult_bin Ze x = Ze) /\ 
  (!x:bin.mult_bin x Ze = Ze) /\ 
  (!x:bin. mult_bin On x = x) /\ 
  (!x:bin. mult_bin x On = x) /\ 
  (!x:bin y:bin. mult_bin (thenZe x) (thenZe y) = 
    thenZe (thenZe (mult_bin x y))) /\ 
  (!x:bin y:bin. mult_bin (thenZe x) (thenOn y) = 
    add_bin (thenZe x) (mult_bin (thenZe x) (thenZe y))) /\
  (!x:bin y:bin. mult_bin (thenOn x) (thenZe y) = 
    add_bin (thenZe y) (mult_bin (thenZe x) (thenZe y))) /\
  (!x:bin y:bin. mult_bin (thenOn x) (thenOn y) = 
    add_bin (thenOn x) (mult_bin (thenOn x) (thenZe y)))`;;

let mult_ebin = define `
  (mult_ebin (QuoConst "Zero" (TyBase "nat")) x = QuoConst "Zero" (TyBase "nat")) /\
  (mult_ebin x (QuoConst "Zero" (TyBase "nat")) = QuoConst "Zero" (TyBase "nat")) /\
  (mult_ebin x (QuoConst "One" (TyBase "nat")) = x) /\
  (mult_ebin (QuoConst "One" (TyBase "nat")) x = x) /\
  (mult_ebin 
    (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x) 
    (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) y) = 
    (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) 
    (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) 
    (mult_ebin x y)))) /\
  (mult_ebin
    (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x) 
    (App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) y) = 
    add_ebin (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x)
    (mult_ebin (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x)
    (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) y))) /\
  (mult_ebin 
    (App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x)
    (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) y) = 
    add_ebin (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) y)
    (mult_ebin (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x)
    (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) y))) /\
  (mult_ebin 
    (App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x)
    (App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) y) = 
    add_ebin (App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x)
    (mult_ebin (App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x)
    (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) y)))`;;

(* Lemmas regarding the syntax of proper `nat` constructions *)

let mult_lemma1 = prove(
  `!x:epsilon. start_with_one x ==> 
  start_with_one 
  (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x)`,
  MATCH_MP_TAC(lth) THEN 
  REWRITE_TAC[start_with_one]);;

let mult_lemma2 = prove(
  `!x:epsilon. start_with_one x ==> 
  start_with_one 
  (App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x)`,
  MATCH_MP_TAC(lth) THEN 
  REWRITE_TAC[start_with_one]);;

let mult_lemma3 = 
  let thm = prove(
    `!x:epsilon. proper_nat_construct x /\ start_with_one x ==> 
    proper_nat_construct 
    (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x)`,
    MATCH_MP_TAC(lth) THEN 
    REWRITE_TAC[proper_nat_construct] 
    )
  in 
  prove(
    `!x:epsilon. proper_nat_construct x ==> start_with_one x ==> 
    proper_nat_construct 
    (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x)`,
    MP_TAC(thm) THEN 
    REWRITE_TAC[IMP_CONJ]
    );;

let mult_lemma4 = 
  let thm = prove(
    `!x:epsilon. proper_nat_construct x /\ start_with_one x ==> 
    proper_nat_construct 
    (App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x)`,
    MATCH_MP_TAC(lth) THEN 
    REWRITE_TAC[proper_nat_construct] 
    )
  in 
  prove(
    `!x:epsilon. proper_nat_construct x ==> start_with_one x ==> 
    proper_nat_construct 
    (App (QuoConst "thenOne" (TyBiCons "fun" (TyBase "nat") (TyBase "nat"))) x)`,
    MP_TAC(thm) THEN 
    REWRITE_TAC[IMP_CONJ]
    );;

let mult_lemma5 = prove(
  `!x:epsilon. !y:epsilon. start_with_one x ==> 
  start_with_one y ==> start_with_one (mult_ebin x y)`,
  MATCH_MP_TAC(lth) THEN 
  REWRITE_TAC[start_with_one] THEN 
  CONJ_TAC THEN 
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN 
  REPEAT DISCH_TAC THENL 
  [ASM_REWRITE_TAC[mult_ebin]
  ;MATCH_MP_TAC(lth) THEN
  REWRITE_TAC[start_with_one] THEN
  CONJ_TAC THEN 
  REPEAT GEN_TAC THEN 
  REWRITE_TAC[IMP_CONJ] THEN
  REPEAT DISCH_TAC THENL
  [TOP_DISJ_CASES_TAC THEN
  ASM_REWRITE_TAC[mult_ebin;start_with_one]
  ;BOTTOM_DISJ_CASES_TAC THEN 
  TOP_DISJ_CASES_TAC THEN 
  ASM_REWRITE_TAC[mult_ebin;add_ebin;start_with_one] THEN
  MP_ASSUMPTION_TAC(SPEC `a1':epsilon` (ASSUME 
    `!y. start_with_one a1
    ==> start_with_one y
    ==> start_with_one (mult_ebin a1 y)`)) THEN 
  DISCH_TAC THEN
  MP_ASSUMPTION_TAC(SPEC `mult_ebin a1 a1'` mult_lemma1) THEN 
  DISCH_TAC THENL
  [MP_ASSUMPTION_TAC(SPECL [
    `a1':epsilon`;
    `App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))
     (mult_ebin a1 a1')`] lemma5)
  ;MP_ASSUMPTION_TAC(SPECL [
    `a1:epsilon`;
    `App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))
     (mult_ebin a1 a1')`] lemma5)
  ;MP_ASSUMPTION_TAC(SPECL [
    `a1':epsilon`;
    `App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))
     (mult_ebin a1 a1')`] lemma5) THEN 
  DISCH_TAC THEN 
  MP_ASSUMPTION_TAC(SPECL [
    `a1:epsilon`;
    `add_ebin a1' (App
    (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))
    (mult_ebin a1 a1'))`] lemma5) 
  ]
  ]
  ]
  );;

let mult_lemma6 = prove(
  `!x:epsilon. !y:epsilon. proper_nat_construct x ==> 
  proper_nat_construct y ==> proper_nat_construct (mult_ebin x y)`,
  MATCH_MP_TAC(lth) THEN 
  REWRITE_TAC[proper_nat_construct] THEN 
  CONJ_TAC THEN 
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THENL 
  [DISCH_TAC THEN 
  DISCH_TAC THEN 
  TOP_DISJ_CASES_TAC THEN 
  ASM_REWRITE_TAC[mult_ebin;proper_nat_construct]
  ;REPEAT DISCH_TAC THEN
  MATCH_MP_TAC(lth) THEN 
  REWRITE_TAC[proper_nat_construct] THEN 
  CONJ_TAC THENL
  [REPEAT GEN_TAC THEN 
  REWRITE_TAC[IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  TOP_DISJ_CASES_TAC THEN
  BOTTOM_DISJ_CASES_TAC THEN 
  ASM_REWRITE_TAC[mult_ebin;proper_nat_construct] 
  ;REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  TOP_DISJ_CASES_TAC THEN 
  BOTTOM_DISJ_CASES_TAC THEN
  ASM_REWRITE_TAC[mult_ebin;add_ebin;proper_nat_construct] THEN
  MP_ASSUMPTION_TAC(SPEC `a1':epsilon` (ASSUME 
    `!y. proper_nat_construct a1 ==> 
    proper_nat_construct y ==> 
    proper_nat_construct (mult_ebin a1 y)`)) THEN
  MP_ASSUMPTION_TAC(SPECL [`a1:epsilon`;`a1':epsilon`] mult_lemma5) THEN 
  REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_ASSUMPTION_TAC(SPEC `mult_ebin a1 a1'` mult_lemma1) THENL
  [DISCH_TAC THEN 
  MP_ASSUMPTION_TAC(SPEC `mult_ebin a1 a1'` mult_lemma3) THEN 
  DISCH_TAC THEN 
  MP_ASSUMPTION_TAC(SPECL [`a1:epsilon`;
    `App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))
    (mult_ebin a1 a1')`] lemma6) THEN 
  MP_ASSUMPTION_TAC(SPECL [`a1:epsilon`;
    `App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))
    (mult_ebin a1 a1')`] lemma5) THEN
  REPEAT DISCH_TAC THEN  
  ASM_REWRITE_TAC[]
  ;DISCH_TAC THEN 
  MP_ASSUMPTION_TAC(SPEC `mult_ebin a1 a1'` mult_lemma3) THEN 
  DISCH_TAC THEN 
  MP_ASSUMPTION_TAC(SPECL [`a1':epsilon`;
    `App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))
    (mult_ebin a1 a1')`] lemma6) THEN 
  MP_ASSUMPTION_TAC(SPECL [`a1':epsilon`;
    `App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))
    (mult_ebin a1 a1')`] lemma5) THEN
  REPEAT DISCH_TAC THEN  
  ASM_REWRITE_TAC[]
  ;DISCH_TAC THEN 
  MP_ASSUMPTION_TAC(SPEC `mult_ebin a1 a1'` mult_lemma3) THEN 
  DISCH_TAC THEN 
  MP_ASSUMPTION_TAC(SPECL [`a1':epsilon`;
    `App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))
    (mult_ebin a1 a1')`] lemma6) THEN 
  MP_ASSUMPTION_TAC(SPECL [`a1':epsilon`;
    `App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))
    (mult_ebin a1 a1')`] lemma5) THEN
  REPEAT DISCH_TAC THEN 
  MP_ASSUMPTION_TAC(SPECL [`a1:epsilon`;
    `add_ebin a1' 
    (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))
    (mult_ebin a1 a1'))`] lemma6) THEN 
  MP_ASSUMPTION_TAC(SPECL [`a1:epsilon`;
    `add_ebin a1'
    (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))
    (mult_ebin a1 a1'))`] lemma5) THEN 
  REPEAT DISCH_TAC THEN  
  ASM_REWRITE_TAC[]
  ] 
  ]
  ]
  );;

(* Multiplication and Nat Lemmas*)

let z_to_o = prove(
  `!x:nat. S (thenZero x) = thenOne x`,
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[thenZero;thenOne] THEN 
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[thenZero;thenOne;add_unary]
  );;

let def_of_thenZero = prove(
  `!x:nat. thenZero x = add_unary x x`,
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[add_unary;thenZero;take_s] THEN
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[add_unary;thenZero;take_s] THEN 
  REWRITE_TAC[ASSUME `!x. thenZero x = add_unary x x`]
  );;

let multi_even = prove(
  `!x:nat y:nat. thenZero (thenZero (mult_un x y)) = mult_un (thenZero x) (thenZero y)`,
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[mult_un;thenZero] THEN
  GEN_TAC THEN 
  DISCH_TAC THEN 
  MATCH_MP_TAC(nat_induct) THEN 
  CONV_TAC(RATOR_CONV(REWRITE_CONV[mult_un;thenZero])) THEN
  REWRITE_TAC[] THEN
  GEN_TAC THEN 
  REPEAT DISCH_TAC THEN 
  MP_TAC(SPEC `a':nat` take_out_S) THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[mult_un;add_even] THEN 
  REWRITE_TAC[ASSUME `thenZero (thenZero (mult_un (S a) a')) =
      mult_un (thenZero (S a)) (thenZero a')`;take_out_S;mult_un;
      add_unary;take_s;assoc_add;def_of_thenZero]
  );;

let mult_to_add = prove(
  `!x:nat y:nat. mult_un (thenZero x) (thenOne y) = 
  add_unary (thenZero x) (mult_un (thenZero x) (thenZero y))`,
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[thenZero;thenOne;add_unary;mult_un] THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[thenZero;thenOne;add_unary;mult_un;r_id_of_un_mult] THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  REWRITE_TAC[take_out_s_thenOne;take_out_S;mult_un;add_unary]
  );;

let mult_to_add2 = prove(
  `!x:nat y:nat. mult_un (thenOne x) (thenZero y) = 
  add_unary (thenZero y) (mult_un (thenZero x) (thenZero y))`,
  REPEAT GEN_TAC THEN 
  REWRITE_TAC[SPECL [`(thenOne x):nat`;`(thenZero y):nat`] mult_un_sym] THEN 
  REWRITE_TAC[mult_un_sym;mult_to_add]
  );;

let mult_to_add3 = prove(
  `!x:nat y:nat. mult_un (thenOne x) (thenOne y) = 
  add_unary (thenOne x) (mult_un (thenOne x) (thenZero y))`,
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[thenZero;thenOne;add_unary;mult_un;l_id_of_un_mult;take_s;id_of_plus;z_to_o] THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  MATCH_MP_TAC(nat_induct) THEN
  REWRITE_TAC[thenZero;thenOne;add_unary;mult_un;r_id_of_un_mult;take_s;id_of_plus;z_to_o] THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN
  REWRITE_TAC[take_out_s_thenOne;take_out_S;add_unary;mult_un] 
  );;




(* Theorem templates *)

let fin_mult_beta_red tm1 tm2 var arg thm = 
  let tm = 
    mk_comb(mk_comb(`(=):bool->bool->bool`,
    mk_comb(mk_comb(`(==>)`,
    mk_comb(mk_comb(`(/\):bool->bool->bool`,
    mk_comb(`proper_nat_construct:epsilon -> bool`,tm1)),
    mk_comb(`proper_nat_construct:epsilon -> bool`,tm2))),
    mk_comb(mk_comb(`(=):nat -> nat -> bool`, 
    mk_comb(mk_abs(var,mk_eval(mk_comb(
    mk_comb(`mult_ebin:epsilon -> epsilon -> epsilon`,tm1),tm2),`:nat`)),arg)),
    mk_comb(mk_comb(`mult_un:nat -> nat -> nat`, 
    mk_comb(mk_abs(var,mk_eval(tm1,`:nat`)),arg)),  
    mk_comb(mk_abs(var,mk_eval(tm2,`:nat`)),arg))))), 
    mk_comb(mk_comb(`(==>)`,
    mk_comb(mk_comb(`(/\):bool->bool->bool`,
    mk_comb(`proper_nat_construct:epsilon -> bool`, tm1)),
    mk_comb(`proper_nat_construct:epsilon -> bool`, tm2))),
    mk_comb(mk_comb(`(=):nat -> nat -> bool`,
    mk_eval(mk_comb(mk_comb(`mult_ebin:epsilon -> epsilon -> epsilon`,
    tm1), tm2), `:nat`)), 
    mk_comb(mk_comb(`mult_un:nat -> nat -> nat`,
    mk_eval(tm1, `:nat`)),
    mk_eval(tm2, `:nat`))))) in
  let add_1_2 = mk_comb(mk_comb(
    `mult_ebin:epsilon -> epsilon -> epsilon`,tm1),tm2) in
  prove(tm,
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [tm1;tm2] mult_lemma6) THEN 
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

let mult_sub_x tm1 tm2 sub =
  let add_1_2 = mk_comb(mk_comb(`mult_ebin`, tm1),tm2) in 
  let add_sub = mk_comb(mk_comb(`mult_ebin`, sub),tm2) in  
  let tm = 
    mk_comb(mk_comb(`(=):bool->bool->bool`,
    mk_comb(mk_comb(`(==>)`,
    mk_comb(mk_comb(`(/\):bool->bool->bool`,
    mk_comb(`proper_nat_construct:epsilon -> bool`,sub)),
    mk_comb(`proper_nat_construct:epsilon -> bool`,tm2))),
    mk_comb(mk_comb(`(=):nat -> nat -> bool`, 
    mk_comb(mk_abs(tm1,mk_eval(mk_comb(
    mk_comb(`mult_ebin:epsilon -> epsilon -> epsilon`,tm1),tm2),`:nat`)),sub)),
    mk_comb(mk_comb(`mult_un:nat -> nat -> nat`, 
    mk_comb(mk_abs(tm1,mk_eval(tm1,`:nat`)),sub)),  
    mk_comb(mk_abs(tm1,mk_eval(tm2,`:nat`)),sub))))), 
    mk_comb(mk_comb(`(==>)`,
    mk_comb(mk_comb(`(/\):bool->bool->bool`,
    mk_comb(`proper_nat_construct:epsilon -> bool`, sub)),
    mk_comb(`proper_nat_construct:epsilon -> bool`, tm2))),
    mk_comb(mk_comb(`(=):nat -> nat -> bool`,
    mk_eval(mk_comb(mk_comb(`mult_ebin:epsilon -> epsilon -> epsilon`,
    sub), tm2), `:nat`)), 
  mk_comb(mk_comb(`mult_un:nat -> nat -> nat`,
  mk_eval(sub,`:nat`)),
  mk_eval(tm2,`:nat`))))) 
  in
  prove(tm, 
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  MP_TAC(SPECL [sub;tm2] mult_lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  PROPER_TYPE_TAC(sub) THEN 
  TRY (PROPER_TYPE_TAC(tm2)) THEN 
  PROPER_TYPE_TAC(add_sub) THEN 
  (PROPER_NOT_FREE_TAC sub `"x"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC tm2 `"x"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC add_sub `"x"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(mk_comb(mk_abs(tm1,mk_eval(tm1,`:nat`)),sub)) THEN 
  NAT_BETA_EVAL_RED(mk_comb(mk_abs(tm1,mk_eval(tm2,`:nat`)),sub)) THEN 
  NAT_BETA_EVAL_RED(mk_comb(mk_abs(tm1,mk_eval(add_1_2,`:nat`)),sub)));;  

let mult_sub_y tm1 tm2 sub =
  let add_1_2 = mk_comb(mk_comb(`mult_ebin`, tm1),tm2) in 
  let add_sub = mk_comb(mk_comb(`mult_ebin`, tm1),sub) in  
  let tm = 
    mk_comb(mk_comb(`(=):bool->bool->bool`,
    mk_comb(mk_comb(`(==>)`,
    mk_comb(mk_comb(`(/\):bool->bool->bool`,
    mk_comb(`proper_nat_construct:epsilon -> bool`,tm1)),
    mk_comb(`proper_nat_construct:epsilon -> bool`,sub))),
    mk_comb(mk_comb(`(=):nat -> nat -> bool`, 
    mk_comb(mk_abs(tm2,mk_eval(mk_comb(
    mk_comb(`mult_ebin:epsilon -> epsilon -> epsilon`,tm1),tm2),`:nat`)),sub)),
    mk_comb(mk_comb(`mult_un:nat -> nat -> nat`, 
    mk_comb(mk_abs(tm2,mk_eval(tm1,`:nat`)),sub)),  
    mk_comb(mk_abs(tm2,mk_eval(tm2,`:nat`)),sub))))), 
    mk_comb(mk_comb(`(==>)`,
    mk_comb(mk_comb(`(/\):bool->bool->bool`,
    mk_comb(`proper_nat_construct:epsilon -> bool`, tm1)),
    mk_comb(`proper_nat_construct:epsilon -> bool`, sub))),
    mk_comb(mk_comb(`(=):nat -> nat -> bool`,
    mk_eval(mk_comb(mk_comb(`mult_ebin:epsilon -> epsilon -> epsilon`,
    tm1),sub),`:nat`)), 
    mk_comb(mk_comb(`mult_un:nat -> nat -> nat`,
    mk_eval(tm1,`:nat`)),
    mk_eval(sub,`:nat`))))) 
  in
  prove(tm, 
  REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  MP_TAC(SPECL [tm1;sub] mult_lemma6) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  PROPER_TYPE_TAC(tm1) THEN 
  TRY (PROPER_TYPE_TAC(sub)) THEN 
  PROPER_TYPE_TAC(add_sub) THEN 
  (PROPER_NOT_FREE_TAC tm1 `"y"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC sub `"y"` `TyBase "epsilon"`) THEN 
  (PROPER_NOT_FREE_TAC add_sub `"y"` `TyBase "epsilon"`) THEN 
  NAT_BETA_EVAL_RED(mk_comb(mk_abs(tm2,mk_eval(tm1,`:nat`)),sub)) THEN 
  NAT_BETA_EVAL_RED(mk_comb(mk_abs(tm2,mk_eval(tm2,`:nat`)),sub)) THEN 
  NAT_BETA_EVAL_RED(mk_comb(mk_abs(tm2,mk_eval(add_1_2,`:nat`)),sub)));;  


(* ALL NOT-EFFECTIVE-IN LEMMAS *)

TRIV_NE `(!x:epsilon y:epsilon. 
    (((proper_nat_construct x) /\ (proper_nat_construct y)) 
    ==> (eval (mult_ebin x y) to (nat) =  
    mult_un (eval x to (nat)) (eval y to (nat)))))`;;


let mult_fin_beta_red1 = 
  fin_mult_beta_red `x:epsilon` `y:epsilon` `a0:string` `w:string` beta_red1;;
let a0_ne = 
  ne_to_inst `a0:string` 
  `\x:epsilon. !y:epsilon. proper_nat_construct x /\ proper_nat_construct y ==>
  (eval (mult_ebin x y) to (nat)) = 
  mult_un (eval (x) to (nat)) (eval (y) to (nat))` `w:string` mult_fin_beta_red1;;

let mult_fin_beta_red2 = 
  fin_mult_beta_red `x:epsilon` `y:epsilon` `a1:type` `w:type` beta_red2;;
let a1_ne = 
  ne_to_inst `a1:type` 
  `\x:epsilon. !y:epsilon. proper_nat_construct x /\ proper_nat_construct y ==>
  (eval (mult_ebin x y) to (nat)) = 
  mult_un (eval (x) to (nat)) (eval (y) to (nat))` `w:type` mult_fin_beta_red2;;

let ind_y1 = TRIV_NE `\y:epsilon. proper_nat_construct (QuoConst a0 a1) /\ 
  proper_nat_construct y ==> (eval (mult_ebin (QuoConst a0 a1) y) to (nat)) =
  mult_un (eval (QuoConst a0 a1) to (nat)) (eval (y) to (nat))`;;

let mult_fin_beta_red3 = 
  fin_mult_beta_red `QuoConst a0 a1` `y:epsilon` `b0:string` `w:string` beta_red3;;
let b0_ne = 
  ne_to_inst `b0:string` 
  `\y. proper_nat_construct (QuoConst a0 a1) /\ proper_nat_construct y
  ==> (eval (mult_ebin (QuoConst a0 a1) y) to (nat)) =
  mult_un (eval (QuoConst a0 a1) to (nat)) (eval (y) to (nat))` `w:string` mult_fin_beta_red3;;

let mult_fin_beta_red4 = 
  fin_mult_beta_red `QuoConst a0 a1` `y:epsilon` `b1:type` `w:type` beta_red4;;
let b1_ne = 
  ne_to_inst `b1:type` 
  `\y. proper_nat_construct (QuoConst a0 a1) /\ proper_nat_construct y
  ==> (eval (mult_ebin (QuoConst a0 a1) y) to (nat)) =
  mult_un (eval (QuoConst a0 a1) to (nat)) (eval (y) to (nat))` `w:type` mult_fin_beta_red4;;

let mult_fin_beta_red5 = 
  fin_mult_beta_red `QuoConst a0 a1` `y:epsilon` `b0:epsilon` `w:epsilon` beta_red5;;
let b0_eps_ne = 
  ne_to_inst `b0:epsilon` 
  `\y. proper_nat_construct (QuoConst a0 a1) /\ proper_nat_construct y
  ==> (eval (mult_ebin (QuoConst a0 a1) y) to (nat)) =
  mult_un (eval (QuoConst a0 a1) to (nat)) (eval (y) to (nat))` `w:epsilon` mult_fin_beta_red5;;

let mult_fin_beta_red6 = 
  fin_mult_beta_red `QuoConst a0 a1` `y:epsilon` `b1:epsilon` `w:epsilon` beta_red12;;
let b1_eps_ne =
  ne_to_inst `b1:epsilon` 
    `\y. proper_nat_construct (QuoConst a0 a1) /\ proper_nat_construct y
    ==> (eval (mult_ebin (QuoConst a0 a1) y) to (nat)) =
    mult_un (eval (QuoConst a0 a1) to (nat)) (eval (y) to (nat))` `w:epsilon` mult_fin_beta_red6;;

let mult_fin_beta_red7 = 
  fin_mult_beta_red `x:epsilon` `y:epsilon` `a0:epsilon` `w:epsilon` beta_red6;;
let a0_eps_ne = 
  ne_to_inst `a0:epsilon` 
  `\x. !y. proper_nat_construct x /\ proper_nat_construct y
  ==> (eval (mult_ebin x y) to (nat)) =
  mult_un (eval (x) to (nat)) (eval (y) to (nat))` `w:epsilon` mult_fin_beta_red7;;

let mult_fin_beta_red8 = 
  fin_mult_beta_red `x:epsilon` `y:epsilon` `a1:epsilon` `w:epsilon` beta_red10;;
let a1_eps_ne = 
  ne_to_inst `a1:epsilon` 
  `\x. !y. proper_nat_construct x /\ proper_nat_construct y
  ==> (eval (mult_ebin x y) to (nat)) =
  mult_un (eval (x) to (nat)) (eval (y) to (nat))` `w:epsilon` mult_fin_beta_red8;;

let ind_y2 = TRIV_NE `\y:epsilon. proper_nat_construct (App a0 a1) /\ 
  proper_nat_construct y ==> (eval (mult_ebin (App a0 a1) y) to (nat)) =
  mult_un (eval (App a0 a1) to (nat)) (eval (y) to (nat))`;;

let mult_fin_beta_red9 =
  fin_mult_beta_red `App a0 a1` `y:epsilon` `b0:string` `w:string` beta_red3;;
let b0_app_ne = 
  ne_to_inst `b0:string` 
  `\y. proper_nat_construct (App a0 a1) /\ proper_nat_construct y
  ==> (eval (mult_ebin (App a0 a1) y) to (nat)) =
  mult_un (eval (App a0 a1) to (nat)) (eval (y) to (nat))` `w:string` mult_fin_beta_red9;;

let mult_fin_beta_red10 =
  fin_mult_beta_red `App a0 a1` `y:epsilon` `b1:type` `w:type` beta_red4;;
let b1_app_ne = 
  ne_to_inst `b1:type` 
  `\y. proper_nat_construct (App a0 a1) /\ proper_nat_construct y
  ==> (eval (mult_ebin (App a0 a1) y) to (nat)) =
  mult_un (eval (App a0 a1) to (nat)) (eval (y) to (nat))` `w:type` mult_fin_beta_red10;;

let mult_fin_beta_red11 =
  fin_mult_beta_red `App a0 a1` `y:epsilon` `b0:epsilon` `w:epsilon` beta_red5;;
let b0_eps_app_ne = 
  ne_to_inst `b0:epsilon` 
  `\y. proper_nat_construct (App a0 a1) /\ proper_nat_construct y
  ==> (eval (mult_ebin (App a0 a1) y) to (nat)) =
  mult_un (eval (App a0 a1) to (nat)) (eval (y) to (nat))` `w:epsilon` mult_fin_beta_red11;;

let mult_fin_beta_red12 =
  fin_mult_beta_red `App a0 a1` `y:epsilon` `b1:epsilon` `w:epsilon` beta_red12;;
let b0_eps_app_ne = 
  ne_to_inst `b1:epsilon` 
  `\y. proper_nat_construct (App a0 a1) /\ proper_nat_construct y
  ==> (eval (mult_ebin (App a0 a1) y) to (nat)) =
  mult_un (eval (App a0 a1) to (nat)) (eval (y) to (nat))` `w:epsilon` mult_fin_beta_red12;;

let mult_fin_beta_red13 = 
  fin_mult_beta_red `x:epsilon` `y:epsilon` `a:epsilon` `w:epsilon` beta_red11;;
let a1_eps_ne = 
  ne_to_inst `a:epsilon` 
  `\x. !y. proper_nat_construct x /\ proper_nat_construct y
  ==> (eval (mult_ebin x y) to (nat)) =
  mult_un (eval (x) to (nat)) (eval (y) to (nat))` `w:epsilon` mult_fin_beta_red13;;


(* Lemmas to simplify induction *)

let mult_constants = prove(
  `!a0:string b0:string a1:type b1:type. 
  proper_nat_construct (QuoConst a0 a1) /\
  proper_nat_construct (QuoConst b0 b1)
  ==> (eval (mult_ebin (QuoConst a0 a1) (QuoConst b0 b1)) to (nat)) =
  mult_un (eval (QuoConst a0 a1) to (nat))
  (eval (QuoConst b0 b1) to (nat))`,
  REPEAT GEN_TAC THEN 
  REWRITE_TAC[proper_nat_construct;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  TOP_DISJ_CASES_TAC THEN 
  BOTTOM_DISJ_CASES_TAC THEN
  ASM_REWRITE_TAC[mult_ebin] THEN 
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN 
  REWRITE_TAC[one_def;mult_un;add_unary]
 );;

let mult_con_app = prove(
  `!b0 b1.
  (proper_nat_construct (QuoConst a0 a1) /\ proper_nat_construct b0
  ==> (\y. (eval (mult_ebin (QuoConst a0 a1) y) to (nat))) b0 =
  mult_un ((\y. (eval (QuoConst a0 a1) to (nat))) b0)
  ((\y. (eval (y) to (nat))) b0)) /\
  (proper_nat_construct (QuoConst a0 a1) /\ proper_nat_construct b1
  ==> (\y. (eval (mult_ebin (QuoConst a0 a1) y) to (nat))) b1 =
  mult_un ((\y. (eval (QuoConst a0 a1) to (nat))) b1)
  ((\y. (eval (y) to (nat))) b1))
  ==> proper_nat_construct (QuoConst a0 a1) /\
  proper_nat_construct (App b0 b1)
  ==> (\y. (eval (mult_ebin (QuoConst a0 a1) y) to (nat))) (App b0 b1) =
  mult_un ((\y. (eval (QuoConst a0 a1) to (nat))) (App b0 b1))
  ((\y. (eval (y) to (nat))) (App b0 b1))`,
  REPEAT GEN_TAC THEN 
  REWRITE_TAC[IMP_CONJ;proper_nat_construct] THEN 
  REPEAT DISCH_TAC THEN 
  TOP_DISJ_CASES_TAC THEN 
  BOTTOM_DISJ_CASES_TAC THEN 
  ASM_REWRITE_TAC[mult_ebin] THEN 
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN 
  REWRITE_TAC[one_def;mult_un;add_unary;l_id_of_un_mult]
  );;

let mult_app_con = prove(
  `!b0 b1. proper_nat_construct (App a0 a1) /\
  proper_nat_construct (QuoConst b0 b1)
  ==> (\y. (eval (mult_ebin (App a0 a1) y) to (nat))) (QuoConst b0 b1) =
  mult_un ((\y. (eval (App a0 a1) to (nat))) (QuoConst b0 b1))
  ((\y. (eval (y) to (nat))) (QuoConst b0 b1))`,
  REPEAT GEN_TAC THEN  
  REWRITE_TAC[mult_sub_y `App a0 a1` `y:epsilon` `QuoConst b0 b1`] THEN 
  REWRITE_TAC[IMP_CONJ;proper_nat_construct] THEN 
  REPEAT DISCH_TAC THEN 
  TOP_DISJ_CASES_TAC THEN 
  BOTTOM_DISJ_CASES_TAC THEN 
  ASM_REWRITE_TAC[mult_ebin] THEN 
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN 
  REWRITE_TAC[one_def;mult_un;add_unary;r_id_of_un_mult]
  );;


(*                                *)
(* Multiplication meaning formula *)
(*                                *)

let mult_meaning = 
  let tm = 
    `(!x:epsilon y:epsilon. 
    (((proper_nat_construct x) /\ (proper_nat_construct y)) 
    ==> (eval (mult_ebin x y) to (nat) =  
    mult_un (eval x to (nat)) (eval y to (nat)))))` 
  in 
  prove(tm, 
  MATCH_MP_TAC(lth) THEN 
  CONJ_TAC THENL
  [ (* isVar x *)
  REWRITE_TAC[proper_nat_construct]
  ;CONJ_TAC THENL
  [ (* isConst x *)
  GEN_TAC THEN 
  GEN_TAC THEN 
  REWRITE_TAC[mult_sub_x `x:epsilon` `y:epsilon` `QuoConst a0 a1`] THEN 
  MATCH_MP_TAC(eps_alt_ind) THEN 
  CONJ_TAC THENL
  [ (* isVar y *)
  REWRITE_TAC[proper_nat_construct]
  ;CONJ_TAC THENL
  [ (* isConst y *)
  GEN_TAC THEN 
  GEN_TAC THEN 
  REWRITE_TAC[mult_sub_y `QuoConst a0 a1` `y:epsilon` `QuoConst b0 b1`] THEN 
  REWRITE_TAC[SPECL [`a0:string`;`b0:string`;`a1:type`;`b1:type`] mult_constants]
  ;CONJ_TAC THENL
  [ (* isApp y *)
  REWRITE_TAC[mult_con_app]
  ;REWRITE_TAC[proper_nat_construct]
  ]
  ]
  ]
  ;CONJ_TAC THENL
  [ (* isApp x *)
  REPEAT GEN_TAC THEN 
  REWRITE_TAC[mult_sub_x `x:epsilon` `y:epsilon` `a0:epsilon`] THEN 
  REWRITE_TAC[mult_sub_x `x:epsilon` `y:epsilon` `a1:epsilon`] THEN 
  REWRITE_TAC[IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  REWRITE_TAC[IMP_IMP] THEN 
  REWRITE_TAC[mult_sub_x `x:epsilon` `y:epsilon` `App a0 a1`] THEN 
  MATCH_MP_TAC(eps_alt_ind) THEN 
  CONJ_TAC THENL
  [ (* isVar y *)
  REWRITE_TAC[proper_nat_construct]
  ;CONJ_TAC THENL
  [ (* isConst y *)
  REWRITE_TAC[mult_app_con]
  ;CONJ_TAC THENL
  [ (* isApp y *)
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mult_sub_y `App a0 a1` `y:epsilon` `App b0 b1`] THEN 
  DISCH_TAC THEN 
  REWRITE_TAC[proper_nat_construct;IMP_CONJ] THEN 
  REPEAT DISCH_TAC THEN 
  TOP_DISJ_CASES_TAC THEN 
  BOTTOM_DISJ_CASES_TAC THEN 
  ASM_REWRITE_TAC[mult_ebin;add_ebin] THEN 
  PROPER_TYPE_TAC(`a1:epsilon`) THEN 
  PROPER_TYPE_TAC(`b1:epsilon`) THEN 
  MP_ASSUMPTION_TAC(SPECL [`a1:epsilon`;`b1:epsilon`] mult_lemma6) THEN
  DISCH_TAC THEN 
  PROPER_TYPE_TAC(`mult_ebin a1 b1`) THEN 
  MP_ASSUMPTION_TAC(SPECL [`a1:epsilon`;`b1:epsilon`] mult_lemma5) THEN 
  DISCH_TAC THEN 
  MP_ASSUMPTION_TAC(SPEC `mult_ebin a1 b1` mult_lemma3) THEN 
  DISCH_TAC THEN 
  PROPER_TYPE_TAC(
    `App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))
    (mult_ebin a1 b1)`) THEN 
  MP_TAC(SPEC `b1:epsilon` (ASSUME (`!y. proper_nat_construct a1
    ==> proper_nat_construct y
    ==> (eval (mult_ebin a1 y) to (nat)) =
    mult_un (eval (a1) to (nat)) (eval (y) to (nat))`))) THEN
  REWRITE_TAC[IMP_IMP;mult_sub_y `a1:epsilon` `y:epsilon` `b1:epsilon`] THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THENL
  [REPEAT APP_DISQUO_TAC THEN 
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN  
  ASM_REWRITE_TAC[multi_even] 
  ;MP_ASSUMPTION_TAC(SPECL [`a1:epsilon`;
    `App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))
    (mult_ebin a1 b1)`] lemma6) THEN 
  DISCH_TAC THEN 
  PROPER_TYPE_TAC(`add_ebin a1
    (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))
    (mult_ebin a1 b1))`) THEN 
  REPEAT APP_DISQUO_TAC THEN 
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN 
  QUOTE_TO_CONSTRUCTION_TAC THEN 
  MP_TAC(ADD_EBIN_INST `a1:epsilon`
    `App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))
    (mult_ebin a1 b1)`) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[add_even] THEN 
  APP_DISQUO_TAC THEN 
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN
  ASM_REWRITE_TAC[multi_even;mult_to_add] 
  ;MP_ASSUMPTION_TAC(SPECL [`b1:epsilon`;
    `App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))
    (mult_ebin a1 b1)`] lemma6) THEN 
  DISCH_TAC THEN 
  PROPER_TYPE_TAC(`add_ebin b1
    (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))
    (mult_ebin a1 b1))`) THEN 
  REPEAT APP_DISQUO_TAC THEN 
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN 
  QUOTE_TO_CONSTRUCTION_TAC THEN 
  MP_TAC(ADD_EBIN_INST `b1:epsilon`
    `App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))
    (mult_ebin a1 b1)`) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[add_even] THEN 
  APP_DISQUO_TAC THEN 
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN 
  ASM_REWRITE_TAC[multi_even;mult_to_add2]
  ;MP_ASSUMPTION_TAC(SPECL [`b1:epsilon`;
    `App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))
    (mult_ebin a1 b1)`] lemma6) THEN 
  DISCH_TAC THEN 
  PROPER_TYPE_TAC(`add_ebin b1
    (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))
    (mult_ebin a1 b1))`) THEN 
  MP_ASSUMPTION_TAC(SPECL [`a1:epsilon`;
    `add_ebin b1 (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))
    (mult_ebin a1 b1))`] lemma6) THEN 
  DISCH_TAC THEN 
  PROPER_TYPE_TAC(`add_ebin a1 (add_ebin b1
    (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))
    (mult_ebin a1 b1)))`) THEN 
  REPEAT APP_DISQUO_TAC THEN 
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN 
  QUOTE_TO_CONSTRUCTION_TAC THEN 
  MP_TAC(ADD_EBIN_INST `a1:epsilon`
    `add_ebin b1 (App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))
    (mult_ebin a1 b1))`) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  MP_TAC(ADD_EBIN_INST `b1:epsilon`
    `App (QuoConst "thenZero" (TyBiCons "fun" (TyBase "nat") (TyBase "nat")))
    (mult_ebin a1 b1)`) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  REPEAT APP_DISQUO_TAC THEN
  CONSTRUCTION_TO_QUOTE_TAC THEN 
  LAW_OF_DISQUO_TAC THEN 
  REWRITE_TAC[add_odd_even;add_even;multi_even;mult_to_add3;mult_to_add2]
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


(*                                   *)
(* Instantiating the meaning formula *)
(*                                   *)


(* Required to instantiate theorem *)
TRIV_NE (concl mult_meaning);;

(* To instantiate into the formula, input two terms of type nat or epsilon *)
let MULT_EBIN_INST tm1 tm2 = 
  let trm1 = 
    match tm1 with 
      | Quote(e) -> termToConstruction e
      | _ -> if type_of tm1 = ep_ty then tm1 else termToConstruction tm1
  in 
  let trm2 = 
    match tm2 with 
      | Quote(e) -> termToConstruction e
      | _ -> if type_of tm2 = ep_ty then tm2 else termToConstruction tm2
  in
  let prove_trm = rand(concl(mult_sub_y trm1 `y:epsilon` trm2)) in 
  let fst_inst = mk_comb(`(!):(epsilon -> bool) -> bool`,
    mk_abs(`y:epsilon`,rand(concl(mult_sub_x `x:epsilon` `y:epsilon` trm1)))) in 
  let thm1 = prove(fst_inst,
    GEN_TAC THEN 
    MP_TAC(SPECL [trm1;`y:epsilon`] mult_meaning) THEN 
    REWRITE_TAC[mult_sub_x `x:epsilon` `y:epsilon` trm1]) in 
  prove(prove_trm,
    REWRITE_TAC[taut_lemma;IMP_CONJ] THEN 
    REPEAT DISCH_TAC THEN 
    MP_TAC(SPEC trm2 thm1) THEN 
    ASM_REWRITE_TAC[] THEN 
    MP_ASSUMPTION_TAC(SPECL [trm1;trm2] mult_lemma6) THEN 
    DISCH_TAC THEN
    REPEAT NAT_RED_ALL
    );;

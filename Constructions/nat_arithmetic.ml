(* Unary Arithmetic *)


(* unary number type *)
let nat_induct, nat_recur = define_type "nat = Zero | S nat";;



(*Create functions to map from the num type to our nat type *)

(* nat_to_num : nat -> num *)
let nat_to_num = define ` 
  (nat_to_num Zero = 0) /\ 
  (nat_to_num (S n) = (nat_to_num n) + 1)`;;

(* num_to_nat : num -> nat *)
let num_to_nat = define `
  (num_to_nat 0 = Zero) /\ 
  (num_to_nat (n + 1) = S (num_to_nat n))`;;


(* Prove num and nat are isomorphic types *)
let num_bij = prove( 
  `!n : num. n = nat_to_num (num_to_nat n)`, 
  INDUCT_TAC THENL 
  [REWRITE_TAC[num_to_nat] THEN 
  REWRITE_TAC[nat_to_num]; 
  REWRITE_TAC[ARITH_RULE `!n. SUC n = n + 1`] THEN 
  REWRITE_TAC[num_to_nat] THEN 
  REWRITE_TAC[nat_to_num] THEN 
  REWRITE_TAC[SYM (ASSUME `n = nat_to_num (num_to_nat n)`)]]);;

let nat_bij = prove( 
  `!n : nat. n = num_to_nat (nat_to_num n)`, 
  MATCH_MP_TAC (nat_induct) THEN 
  CONJ_TAC THENL 
  [REWRITE_TAC[nat_to_num] THEN
  REWRITE_TAC[num_to_nat]; 
  GEN_TAC THEN DISCH_TAC THEN 
  REWRITE_TAC[nat_to_num] THEN 
  REWRITE_TAC[num_to_nat] THEN
  REWRITE_TAC[SYM (ASSUME `a = num_to_nat (nat_to_num a)`)]]);;

(* Deduce that... *)
let equiv_defn1 = prove(
  `!x y:num. x = y <=> num_to_nat x = num_to_nat y`, 
  REPEAT GEN_TAC THEN 
  EQ_TAC THEN 
  DISCH_TAC THENL 
  [ASM_REWRITE_TAC[];
  CONV_TAC(RAND_CONV(REWR_CONV num_bij)) THEN 
  CONV_TAC(LAND_CONV(REWR_CONV num_bij)) THEN
  ASM_REWRITE_TAC[nat_to_num]]);;

let equiv_defn2 = prove( 
  `!x y:nat. x = y <=> nat_to_num x = nat_to_num y`, 
  REPEAT GEN_TAC THEN 
  EQ_TAC THEN 
  DISCH_TAC THENL 
  [ASM_REWRITE_TAC[];
  CONV_TAC(RAND_CONV(REWR_CONV nat_bij)) THEN 
  CONV_TAC(LAND_CONV(REWR_CONV nat_bij)) THEN 
  ASM_REWRITE_TAC[num_to_nat]]);;



(* Addition in unary *)
let add_unary = define `
  (!x:nat. add_unary x Zero = x) /\ 
  (!x y:nat. add_unary x (S y) = S (add_unary x y))`;; 

(* Some addition properties... *)

let id_of_plus = prove( 
  `!x:nat. add_unary Zero x = x`, 
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[add_unary] THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[]);;

let sym_add = prove( 
  `!x:nat y:nat. add_unary x y = add_unary y x`, 
  MATCH_MP_TAC(nat_induct) THEN
  REWRITE_TAC[id_of_plus; add_unary] THEN
  GEN_TAC THEN 
  DISCH_TAC THEN 
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[id_of_plus; add_unary] THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  REWRITE_TAC[add_unary] THEN 
  REWRITE_TAC[(SYM(SPEC `(S a'):nat` (ASSUME `!y. add_unary a y = add_unary y a`)))] THEN 
  REWRITE_TAC[add_unary; ASSUME `add_unary (S a) a' = S (add_unary a' a)`] THEN  
  ASM_REWRITE_TAC[]);;

let switch_S = prove(
  `!x:nat y:nat. add_unary (S x) y = add_unary x (S y)`, 
  REPEAT(GEN_TAC) THEN
  REWRITE_TAC[add_unary] THEN 
  REWRITE_TAC[SPECL [`(S x) : nat`; `y:nat`] sym_add; add_unary;sym_add]);;
			
let take_s = prove( 
  `!x y:nat. add_unary (S x) y = S (add_unary x y)`, 
  REPEAT(GEN_TAC) THEN 
  REWRITE_TAC[switch_S;add_unary]);;

let put_s = prove( 
  `!x y:nat. S (add_unary x y) = add_unary (S x) y`,
  REWRITE_TAC[take_s]);;

let assoc_add = prove(
  `!x y z:nat. add_unary x (add_unary y z) = add_unary (add_unary x y) z`, 
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[sym_add; add_unary] THEN 
  REWRITE_TAC[id_of_plus] THEN
  GEN_TAC THEN 
  DISCH_TAC THEN 
  REWRITE_TAC[SPECL [`(S a):nat`; `(add_unary y z):nat`] sym_add; add_unary] THEN 
  REWRITE_TAC[sym_add] THEN
  ASM_REWRITE_TAC[]);;


(* Extend to Binary Arithmetic *)

(* binary number type *)
let bin_induct, bin_recur = 
  define_type "bin = Ze | On | thenZe bin | thenOn bin" ;;


(* binary -> unary *)
let get_nat = define `
  (get_nat x Zero = add_unary x x) /\ 
  (get_nat x (S Zero) = add_unary (add_unary x x) (S Zero))`;;

let bin_to_nat = define `
  (bin_to_nat Ze = Zero) /\ 
  (bin_to_nat On = S Zero) /\
  (bin_to_nat (thenZe x) = get_nat (bin_to_nat x) Zero) /\ 
  (bin_to_nat (thenOn x) = get_nat (bin_to_nat x) (S Zero))`;;


(* binary -> HOL num *)
let bin_to_num = define `
  (bin_to_num Ze = 0) /\ 
  (bin_to_num On = 1) /\ 
  (!x:bin. bin_to_num (thenZe x) = 2 * (bin_to_num x)) /\ 
  (!x:bin. bin_to_num (thenOn x) = (2 * (bin_to_num x)) + 1)`;;  


(* add binary numbers *)
let add_bin = define `
  (!x:bin. add_bin x Ze = x) /\ 
  (!x:bin. add_bin Ze x = x) /\ 
  (add_bin On On = thenZe On) /\  
  (!x:bin. add_bin (thenZe x) On = thenOn x) /\ 
  (!x:bin. add_bin On (thenZe x) = thenOn x) /\  
  (!x:bin. add_bin On (thenOn x) = thenZe (add_bin On x)) /\
  (!x:bin. add_bin (thenOn x) On = thenZe (add_bin On x)) /\
  (!x:bin y:bin. add_bin (thenZe x) (thenZe y) = thenZe (add_bin x y)) /\
  (!x:bin y:bin. add_bin (thenZe x) (thenOn y) = thenOn (add_bin x y)) /\
  (!x:bin y:bin. add_bin (thenOn x) (thenZe y) = thenOn (add_bin x y)) /\
  (!x:bin y:bin. add_bin (thenOn x) (thenOn y) = thenZe (add_bin On (add_bin x y)))`;; 


let one_more = prove( 
  `!x:bin. bin_to_nat (add_bin On x) = S (bin_to_nat x)`, 
  MATCH_MP_TAC(bin_induct) THEN
  REWRITE_TAC[add_bin; bin_to_nat;get_nat;add_unary] THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[add_unary; switch_S]);;


(* unary -> binary *)
let nat_to_bin = define `
  (nat_to_bin Zero = Ze) /\ 
  (nat_to_bin (S Zero) = On) /\ 
  (nat_to_bin (S (S x)) = add_bin (On) (nat_to_bin (S x)))`;; 


let bring_out_S = prove( 
  `!x:nat. bin_to_nat (nat_to_bin (S x)) = S (bin_to_nat (nat_to_bin x))`,
  MATCH_MP_TAC(nat_induct) THEN 
  CONJ_TAC THEN 
  REWRITE_TAC[nat_to_bin;bin_to_nat] THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  REWRITE_TAC[one_more]);; 

let add_order = prove( 
  `!w x y z:nat. add_unary (add_unary w x) (add_unary y z) = 
  (add_unary (add_unary w y) ( add_unary x z))`, 
  REPEAT GEN_TAC THEN 
  REWRITE_TAC[assoc_add] THEN 
  ASSUME_TAC(SYM(SPECL [`w:nat`;`x:nat`;`y:nat`] assoc_add)) THEN  
  ASSUME_TAC(SYM(SPECL [`w:nat`;`y:nat`;`x:nat`] assoc_add)) THEN 
  REWRITE_TAC[ASSUME `add_unary (add_unary w x) y = add_unary w (add_unary x y)`] THEN
  REWRITE_TAC[ASSUME `add_unary (add_unary w y) x = add_unary w (add_unary y x)`] THEN 
  REWRITE_TAC[sym_add]);;

let equiv_add = prove(
  `!x:bin y:bin. bin_to_nat (add_bin x y) = add_unary (bin_to_nat x) (bin_to_nat y)`, 
  (MATCH_MP_TAC(bin_induct) THEN 
  CONJ_TAC THEN 
  REWRITE_TAC[add_bin; bin_to_nat; add_unary; id_of_plus] THEN 
  CONJ_TAC THENL 
  [(MATCH_MP_TAC(bin_induct) THEN 
  (REWRITE_TAC[add_bin; bin_to_nat; add_unary; get_nat;one_more]) THEN 
  (REWRITE_TAC[switch_S; add_unary; id_of_plus])) 
  ;CONJ_TAC THENL 
  [GEN_TAC THEN 
  DISCH_TAC THEN
  (MATCH_MP_TAC(bin_induct)) THEN 
  (REWRITE_TAC[add_bin; bin_to_nat; add_unary; get_nat]) THEN 
  CONJ_TAC THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  (REWRITE_TAC[add_order]) THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN  
  (REWRITE_TAC[add_order])
  ;GEN_TAC THEN 
  DISCH_TAC THEN
  (MATCH_MP_TAC(bin_induct)) THEN 
  (REWRITE_TAC[add_bin; bin_to_nat; add_unary; get_nat; one_more; switch_S]) THEN 
  CONJ_TAC THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  (REWRITE_TAC[add_order]) THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN  
  (REWRITE_TAC[add_order])]]));;

let bin_sym = prove(
  `!x y:bin. add_bin x y = add_bin y x`, 
  MATCH_MP_TAC(bin_induct) THEN 
  REWRITE_TAC[add_bin] THEN 
  CONJ_TAC THENL 
  [MATCH_MP_TAC(bin_induct) THEN 
  REWRITE_TAC[add_bin] 
  ;CONJ_TAC THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  MATCH_MP_TAC(bin_induct) THEN 
  REWRITE_TAC[add_bin] THEN 
  ASM_REWRITE_TAC[]]);;

let one_assoc = prove( 
  `!x y:bin. (add_bin (add_bin On x) y) = (add_bin On (add_bin x y))`, 
  MATCH_MP_TAC(bin_induct) THEN 
  REWRITE_TAC[add_bin] THEN 
  CONJ_TAC THENL 
  [MATCH_MP_TAC(bin_induct) 
  THEN REWRITE_TAC[add_bin] 
  ;CONJ_TAC THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  MATCH_MP_TAC(bin_induct) THEN 
  REWRITE_TAC[add_bin; bin_sym] THEN 
  CONJ_TAC THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  REWRITE_TAC[SPECL [`a':bin`; `(add_bin a On):bin`] bin_sym] THEN 
  REWRITE_TAC[SPECL [`a:bin` ; `On:bin`] bin_sym] THEN 
  ASM_REWRITE_TAC[]]);;

let bin_assoc = prove(
  `!x y z:bin. add_bin (add_bin x y) z = add_bin x (add_bin y z)`,
  MATCH_MP_TAC(bin_induct) THEN 
  REWRITE_TAC[add_bin; one_assoc] THEN 
  CONJ_TAC THENL
  [GEN_TAC THEN 
  DISCH_TAC THEN 
  MATCH_MP_TAC(bin_induct) THEN 
  REWRITE_TAC[add_bin] THEN 
  CONJ_TAC THENL 
  [MATCH_MP_TAC(bin_induct) THEN 
  (REWRITE_TAC[add_bin;bin_sym;one_assoc]) THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  REWRITE_TAC[SYM(SPECL [`a':bin`; `On:bin`] 
    (ASSUME `!y z. add_bin (add_bin a y) z = add_bin a (add_bin y z)`));bin_sym]
  ;CONJ_TAC THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  MATCH_MP_TAC(bin_induct) THEN 
  REWRITE_TAC[add_bin] THENL 
  [CONJ_TAC THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] 
  ;CONJ_TAC THENL 
  [REWRITE_TAC[SPECL [`a:bin`;`(add_bin On a'):bin`] bin_sym] THEN 
  (REWRITE_TAC[one_assoc; bin_sym]) 
  ;ASM_REWRITE_TAC[] THEN 
  REWRITE_TAC[SYM(SPECL [`On:bin`;`(add_bin a' a''):bin`] 
    (ASSUME `!y z. add_bin (add_bin a y) z = add_bin a (add_bin y z)`))] THEN 
  (REWRITE_TAC[SPECL [`a:bin`; `On:bin`] bin_sym;one_assoc])]]]
  ;GEN_TAC THEN 
  DISCH_TAC THEN 
  MATCH_MP_TAC(bin_induct) THEN 
  REWRITE_TAC[add_bin] THEN 
  CONJ_TAC THENL 
  [MATCH_MP_TAC(bin_induct) THEN 
  REWRITE_TAC[add_bin;bin_sym] THEN 
  CONJ_TAC THEN 
  GEN_TAC THEN 
  DISCH_TAC THENL 
  [REWRITE_TAC[
    SPECL [`a:bin`;`On:bin`] bin_sym;
    SPECL [`a':bin`;`(add_bin On a):bin`] bin_sym;
    one_assoc] 
  ;REWRITE_TAC
    [SPECL [`a':bin`;`On:bin`] bin_sym ;
    SPECL [`a':bin`;`(add_bin a On):bin`] bin_sym;
    one_assoc] THEN 
  REWRITE_TAC[bin_sym]] 
  ;CONJ_TAC THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  MATCH_MP_TAC(bin_induct) THEN 
  REWRITE_TAC[add_bin;bin_sym;one_assoc] THENL 
  [CONJ_TAC THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN
  REWRITE_TAC[SPECL [`a'':bin`;`(add_bin a a'):bin`] bin_sym] THEN 
  ASM_REWRITE_TAC[bin_sym]
  ;CONJ_TAC THENL 
  [REWRITE_TAC[SYM(SPECL [`a':bin`;`On:bin`] 
    (ASSUME `!y z. add_bin (add_bin a y) z = add_bin a (add_bin y z)`));bin_sym] 
  ;CONJ_TAC THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  REWRITE_TAC[SPECL [`a'':bin`;`(add_bin a a'):bin`] bin_sym] THEN 
  ASM_REWRITE_TAC[bin_sym] THEN 
  REWRITE_TAC[SPECL[`a'':bin`;`(add_bin a a'):bin`] bin_sym] THEN
  REWRITE_TAC[SPECL [`(add_bin (add_bin a' a'') On):bin`;`a:bin`] bin_sym] THEN 
  REWRITE_TAC[SYM(SPECL [`(add_bin a' a''):bin`;`On:bin`] 
    (ASSUME `!y z. add_bin (add_bin a y) z = add_bin a (add_bin y z)`)); bin_sym]]]]]);;


let same_S = prove (
  `!x:nat. add_bin On (nat_to_bin x) = nat_to_bin (S x)`, 
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[nat_to_bin; add_bin]);;

let remove_and_add = prove(
  `!x:nat y:nat. add_bin (nat_to_bin (S x)) (nat_to_bin y) = 
  add_bin (nat_to_bin x) (nat_to_bin (S y))`,
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[nat_to_bin; add_bin; one_more] THEN
  REWRITE_TAC[same_S] THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  GEN_TAC THEN 
  REWRITE_TAC[SYM(SPEC `(S a):nat` same_S);SYM(SPEC `y:nat` same_S)] THEN 
  CONV_TAC(LAND_CONV(LAND_CONV(RAND_CONV(REWR_CONV(
    SPECL [`On:bin`;`(nat_to_bin a):bin`] bin_sym))))) THEN 
  REWRITE_TAC[bin_assoc]);;

let nat_equiv = prove(
  `!x:nat y:nat. (nat_to_bin (add_unary x y)) = 
  add_bin (nat_to_bin x) (nat_to_bin y)`, 
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[add_unary; nat_to_bin; add_bin;id_of_plus] THEN 
  GEN_TAC THEN
  DISCH_TAC THEN 
  REWRITE_TAC[switch_S;remove_and_add] THEN 
  ASM_REWRITE_TAC[]);; 

(* Remove `duplicates` from our set of bin numbers *)

let check_bin = define `
  (check_bin On = T) /\ 
  (check_bin Ze = F) /\
  (!x:bin. check_bin (thenZe x) = check_bin x) /\ 
  (!x:bin. check_bin (thenOn x) = check_bin x)`;;

let proper_bin = define `
  (proper_bin Ze = T) /\ 
  (proper_bin On = T) /\
  (!x:bin. proper_bin (thenZe x) = check_bin x) /\ 
  (!x:bin. proper_bin (thenOn x) = check_bin x)`;;

let not_proper = prove(
  `(~ (proper_bin (thenZe Ze)))`, 
  REWRITE_TAC[proper_bin; check_bin]);; 

let proper_property = prove(
  `!x:bin. (proper_bin (thenZe x) \/ proper_bin (thenOn x)) ==> proper_bin x`, 
  MATCH_MP_TAC(bin_induct) THEN 
  REWRITE_TAC[proper_bin;check_bin]);;

let must_check = prove(
  `!x:bin. proper_bin (add_bin On x) = check_bin (add_bin On x)`, 
  MATCH_MP_TAC(bin_induct) THEN 
  REWRITE_TAC[add_bin; proper_bin;check_bin]);;

let proper_add = prove(
  `!x:bin. proper_bin x ==> proper_bin (add_bin On x)`, 
  MATCH_MP_TAC(bin_induct) THEN 
  CONJ_TAC THENL 
  [REWRITE_TAC[add_bin; proper_bin; check_bin]
  ;CONJ_TAC THENL
  [REWRITE_TAC[add_bin; proper_bin; check_bin]
  ;CONJ_TAC THENL 
  [REWRITE_TAC[add_bin; proper_bin; check_bin]
  ;GEN_TAC THEN 
  REPEAT DISCH_TAC THEN 
  MP_TAC(SPEC `a:bin` proper_property) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  MP_TAC(MP (
    ASSUME `proper_bin a ==> proper_bin (add_bin On a)`) 
    (ASSUME `proper_bin a`)) THEN 
  REWRITE_TAC[add_bin; proper_bin;check_bin;must_check]]]]);; 

let always_proper = prove(
  `!x:nat. proper_bin (nat_to_bin x)`, 
  MATCH_MP_TAC(nat_induct) THEN 
  CONJ_TAC THENL
  [REWRITE_TAC[nat_to_bin; proper_bin] 
  ;MATCH_MP_TAC(nat_induct) THEN 
  CONJ_TAC THENL
  [REWRITE_TAC[nat_to_bin;proper_bin;check_bin]
  ;GEN_TAC THEN 
  DISCH_TAC THEN 
  DISCH_TAC THEN 
  REWRITE_TAC[nat_to_bin] THEN 
  MP_TAC(SPEC `nat_to_bin (S a):bin` proper_add) THEN 
  ASM_REWRITE_TAC[]]]);;

let other_prop_prop = prove( 
  `!x:bin. proper_bin (thenZe x) <=> proper_bin (thenOn x)`,
  MATCH_MP_TAC(bin_induct) THEN 
  REWRITE_TAC[proper_bin; check_bin]);;

let def_of_thenZe = prove( 
  `!x:bin. (proper_bin (thenZe x)) ==> (thenZe x = add_bin x x)`, 
  MATCH_MP_TAC(bin_induct) THEN 
  REWRITE_TAC[proper_bin;check_bin;add_bin] THEN 
  CONJ_TAC THEN 
  GEN_TAC THEN 
  REPEAT DISCH_TAC THENL 
  [(ASSUME_TAC(MP 
    (ASSUME `check_bin a ==> thenZe a = add_bin a a`) 
    (ASSUME `check_bin a`))) THEN 
  ASM_REWRITE_TAC[] 
  ;(ASSUME_TAC(SYM(MP 
    (ASSUME `check_bin a ==> thenZe a = add_bin a a`) 
    (ASSUME `check_bin a`)))) THEN 
  ASM_REWRITE_TAC[] THEN 
REWRITE_TAC[add_bin]]);;

let def_of_thenOn = prove( 
  `!x:bin. (proper_bin (thenOn x)) ==> (thenOn x = add_bin On (add_bin x x))`,
  MATCH_MP_TAC(bin_induct) THEN 
  REWRITE_TAC[proper_bin;check_bin;add_bin] THEN 
  CONJ_TAC THEN 
  GEN_TAC THEN 
  REPEAT DISCH_TAC THENL 
  [(MP_TAC(SPEC `a:bin` def_of_thenZe)) THEN 
  REWRITE_TAC[proper_bin;check_bin] THEN
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] 
  ;(ASSUME_TAC(MP 
    (ASSUME `check_bin a ==> thenOn a = add_bin On (add_bin a a)`) 
    (ASSUME `check_bin a`))) THEN 
  ASM_REWRITE_TAC[]]);;

(* show unary and binary types are (sort of) isomorphic *)

let natbin_bij = prove( 
  `!x:nat. x = bin_to_nat (nat_to_bin x)`, 
  (MATCH_MP_TAC(nat_induct) THEN 
  CONJ_TAC THENL
  [(REWRITE_TAC[nat_to_bin; bin_to_nat]) 
  ;GEN_TAC THEN 
  DISCH_TAC THEN 
  (REWRITE_TAC[bring_out_S]) THEN 
  (REWRITE_TAC[SYM(ASSUME `a = bin_to_nat (nat_to_bin a)`)])]));; 

let reverse_ntob = prove(
  `!x y:nat. (x = y) <=> (nat_to_bin x = nat_to_bin y)`, 
  (REPEAT(GEN_TAC) THEN 
  EQ_TAC THENL
  [DISCH_TAC THEN 
  ASM_REWRITE_TAC[]
  ;DISCH_TAC THEN 
  (ASSUME_TAC(SPEC `x:nat` natbin_bij)) THEN 
  (ASSUME_TAC(SPEC `y:nat` natbin_bij)) THEN 
  (CONV_TAC(LAND_CONV(REWR_CONV(ASSUME `x = bin_to_nat (nat_to_bin x)`)))) THEN 
  (CONV_TAC(RAND_CONV(REWR_CONV(ASSUME `y = bin_to_nat (nat_to_bin y)`)))) THEN 
  ASM_REWRITE_TAC[]]));;


(* The following statement is false because each unary number has *many* binary representations. *)
(*                               !x:bin. x = nat_to_bin (bin_to_nat x)                           *)
(* But if we restict the domain to only proper bin numbers then the relation holds               *)

let binnat_bij = prove( 
  `!x:bin. (proper_bin x) ==> (x = nat_to_bin (bin_to_nat x))`,
  (MATCH_MP_TAC(bin_induct) THEN  
  (REWRITE_TAC[bin_to_nat; nat_to_bin]) THEN 
  CONJ_TAC THENL 
  [GEN_TAC THEN 
  REPEAT(DISCH_TAC) THEN 
  REWRITE_TAC[get_nat] THEN 
  (ASSUME_TAC(SPEC `a:bin` def_of_thenZe)) THEN
  REWRITE_TAC[SPECL [`(bin_to_nat a):nat`; `(bin_to_nat a):nat`] nat_equiv] THEN 
  MP_TAC(SPEC `a:bin` proper_property) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  ASSUME_TAC(MP 
    (ASSUME `proper_bin (thenZe a) ==> thenZe a = add_bin a a`) 
    (ASSUME `proper_bin (thenZe a)`)) THEN 
  ASSUME_TAC(MP 
    (ASSUME `proper_bin a ==> a = nat_to_bin (bin_to_nat a)`) 
    (ASSUME `proper_bin a`)) THEN 
  ASM_REWRITE_TAC[SYM(ASSUME `a = nat_to_bin (bin_to_nat a)`)] 
  ;GEN_TAC THEN 
  REPEAT(DISCH_TAC) THEN 
  REWRITE_TAC[get_nat;add_unary] THEN 
  REWRITE_TAC[SYM(SPEC `(add_unary (bin_to_nat a) (bin_to_nat a)):nat` same_S)] THEN
  REWRITE_TAC[nat_equiv] THEN 
  MP_TAC(SPEC `a:bin` proper_property) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  ASSUME_TAC(MP 
    (ASSUME `proper_bin a ==> a = nat_to_bin (bin_to_nat a)`) 
    (ASSUME `proper_bin a`)) THEN 
  REWRITE_TAC[SYM(ASSUME `a = nat_to_bin (bin_to_nat a)`)] THEN
  REWRITE_TAC[MP (SPEC `a:bin` def_of_thenOn) (ASSUME `proper_bin (thenOn a)`)]]));;

let reverse_bton = prove(
  `!x y:bin. (proper_bin x) /\ (proper_bin y) ==> 
  (bin_to_nat x = bin_to_nat y ==> x = y)`,
  (REPEAT(GEN_TAC) THEN 
  REPEAT(DISCH_TAC) THEN 
  (MP_TAC(SPEC `x:bin` binnat_bij)) THEN  
  (ASSUME_TAC(SPEC `y:nat` natbin_bij)) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN
  ASSUME_TAC(CONJUNCT2 (ASSUME `proper_bin x /\ proper_bin y`)) THEN 
  MP_TAC(SPEC `y:bin` binnat_bij) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  REWRITE_TAC[SYM(ASSUME `y = nat_to_bin (bin_to_nat y)`)]));;

(* Multiplication! *)

let mult_un = define `
  (!x:nat. mult_un Zero x = Zero) /\ 
  (!x:nat. mult_un x Zero = Zero) /\
  (!x y:nat. mult_un (S x) (S y) = add_unary (S x) (mult_un (S x) y))`;;

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

let l_id_of_un_mult = prove(
  `!x:nat. mult_un (S Zero) x = x`,
  MATCH_MP_TAC(nat_induct) THEN
  REWRITE_TAC[mult_un; add_unary] THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[switch_S; id_of_plus]);;

let r_id_of_un_mult = prove(
  `!x:nat. mult_un x (S Zero) = x`, 
  MATCH_MP_TAC(nat_induct) THEN
  REWRITE_TAC[mult_un; add_unary] THEN 
  GEN_TAC THEN 
  DISCH_TAC);;

let dist_mult = prove(
  `!x y z:nat. mult_un x (add_unary y z) = 
  add_unary (mult_un x y) (mult_un x z)`,
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[add_unary; mult_un] THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[mult_un;id_of_plus;add_unary] THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[add_unary; mult_un] THEN 
  GEN_TAC THEN
  DISCH_TAC THEN 
  ASM_REWRITE_TAC[] THEN 
  REWRITE_TAC[SYM(SPECL [
    `(S a):nat`; 
    `(mult_un (S a) a'):nat`;
    `(add_unary (S a) (mult_un (S a) a'')):nat`] assoc_add)] THEN 
  REWRITE_TAC[assoc_add] THEN 
  REWRITE_TAC[SYM(SPECL [
    `(S a):nat`; 
    `(S a):nat`;
    `(mult_un (S a) a'):nat`] assoc_add)] THEN 
  REWRITE_TAC[SPECL [`(S a):nat`;`(mult_un (S a) a'):nat`] sym_add] THEN 
  REWRITE_TAC[assoc_add] THEN 
  REWRITE_TAC[SPECL [`(S a):nat`;`(mult_un (S a) a'):nat`] sym_add]);;

let s_sym = prove(
  `!x y:nat. mult_un (S x) (S y) = mult_un (S y) (S x)`, 
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[l_id_of_un_mult; r_id_of_un_mult] THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[l_id_of_un_mult; r_id_of_un_mult] THEN 
  GEN_TAC THEN
  DISCH_TAC THEN 
  REWRITE_TAC[SPECL [`(S a):nat`;`(S a'):nat`] (CONJUNCT2(CONJUNCT2(mult_un)))] THEN 
  ASM_REWRITE_TAC[] THEN  
  REWRITE_TAC[SPECL [`(S a):nat`;`(mult_un (S a') (S (S a))):nat`] take_s] THEN 
  REWRITE_TAC[SPECL [`(S a'):nat`;`(mult_un (S (S a')) (S a)):nat`] take_s] THEN 
  REWRITE_TAC[SPECL [`a':nat`;`(S a):nat`] (CONJUNCT2(CONJUNCT2(mult_un)))] THEN 
  REWRITE_TAC[
    SYM(SPEC `(S a'):nat` (ASSUME `!y. mult_un (S a) (S y) = mult_un (S y) (S a)`))] THEN 
  REWRITE_TAC[SPECL [`a:nat`;`(S a'):nat`] (CONJUNCT2(CONJUNCT2(mult_un)))] THEN 
  ASM_REWRITE_TAC[] THEN 
  REWRITE_TAC[assoc_add] THEN 
  REWRITE_TAC[sym_add]);;

let mult_un_sym = prove( 
  `!x y:nat. mult_un x y = mult_un y x`, 
  MATCH_MP_TAC(nat_induct) THEN
  REWRITE_TAC[mult_un] THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[s_sym] THEN 
  REWRITE_TAC[mult_un]);;

let bin_suc = prove( 
  `!x y:bin. (proper_bin x /\ proper_bin y) ==> 
  (mult_bin x (add_bin On y) = add_bin x (mult_bin x y))`,
  MATCH_MP_TAC(bin_induct) THEN 
  CONJ_TAC THEN 
  REWRITE_TAC[mult_bin; add_bin; l_id_of_un_mult] THEN 
  CONJ_TAC THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  MATCH_MP_TAC(bin_induct) THEN 
  REWRITE_TAC[mult_bin; add_bin; l_id_of_un_mult] THEN 
  CONJ_TAC THENL 
  [DISCH_TAC THEN 
  (ASSUME_TAC(CONJUNCT1 (ASSUME `proper_bin (thenZe a) /\ proper_bin On`))) THEN
  ASSUME_TAC(SPEC `a:bin` def_of_thenZe) THEN 
  ASSUME_TAC(MP 
    (ASSUME `proper_bin (thenZe a) ==> thenZe a = add_bin a a`) 
    (ASSUME `proper_bin (thenZe a)`)) THEN 
  ASM_REWRITE_TAC[] 
  ;GEN_TAC THEN 
  REPEAT(DISCH_TAC) THEN 		
  (ASSUME_TAC(CONJUNCT1 (ASSUME `proper_bin (thenZe a) /\ proper_bin (thenOn a')`))) THEN
  (MP_TAC(SPEC `a:bin` proper_property)) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  (ASSUME_TAC(CONJUNCT2 (ASSUME `proper_bin (thenZe a) /\ proper_bin (thenOn a')`))) THEN
  (MP_TAC(SPEC `a':bin` proper_property)) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  ASSUME_TAC(CONJ (ASSUME `proper_bin a`) (ASSUME `proper_bin a'`)) THEN 
  ASSUME_TAC(MP (SPEC `a':bin` (ASSUME 
    `!y. proper_bin a /\ proper_bin y ==> mult_bin a (add_bin On y) = 
    add_bin a (mult_bin a y)`)) 
  (ASSUME `proper_bin a /\ proper_bin a'`)) THEN 	
  ASSUME_TAC(SPEC `a:bin` def_of_thenZe) THEN 
  ASSUME_TAC(MP 
    (ASSUME `proper_bin (thenZe a) ==> thenZe a = add_bin a a`) 
    (ASSUME `proper_bin (thenZe a)`)) THEN 
  ASM_REWRITE_TAC[] THEN 
  REWRITE_TAC[SYM(SPECL 
    [`a:bin`;`a:bin`;`(thenZe (mult_bin a a')):bin`] bin_assoc)] THEN 
  REWRITE_TAC[SYM(ASSUME `thenZe a = add_bin a a`)] THEN 
  REWRITE_TAC[add_bin]
  ;DISCH_TAC THEN 
  (ASSUME_TAC(CONJUNCT1 (ASSUME `proper_bin (thenOn a) /\ proper_bin On`))) THEN
  ASSUME_TAC(EQ_MP (SYM(SPEC `a:bin` other_prop_prop)) (ASSUME `proper_bin (thenOn a)`)) THEN 
  ASSUME_TAC(MP (SPEC `a:bin` def_of_thenZe) (ASSUME `proper_bin (thenZe a)`)) THEN 
  REWRITE_TAC[SYM (ASSUME `thenZe a = add_bin a a`)] THEN 
  REWRITE_TAC[add_bin] 
  ;GEN_TAC THEN 
  REPEAT(DISCH_TAC) THEN
  (ASSUME_TAC(CONJUNCT1 (ASSUME `proper_bin (thenOn a) /\ proper_bin (thenOn a')`))) THEN
  (MP_TAC(SPEC `a:bin` proper_property)) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN 
  (ASSUME_TAC(CONJUNCT2 (ASSUME `proper_bin (thenOn a) /\ proper_bin (thenOn a')`))) THEN
  (MP_TAC(SPEC `a':bin` proper_property)) THEN 
  ASM_REWRITE_TAC[] THEN 
  DISCH_TAC THEN  
  ASSUME_TAC(CONJ (ASSUME `proper_bin a`) (ASSUME `proper_bin a'`)) THEN 
  ASSUME_TAC(MP (SPEC `a':bin` (ASSUME 
    `!y. proper_bin a /\ proper_bin y ==> mult_bin a (add_bin On y) = 
    add_bin a (mult_bin a y)`))
  (ASSUME `proper_bin a /\ proper_bin a'`)) THEN 
  ASM_REWRITE_TAC[] THEN 
  REWRITE_TAC[SYM(SPECL [`a:bin`;`a:bin`;`(add_bin a' (thenZe (mult_bin a a'))):bin`] bin_assoc)] THEN 
  ASSUME_TAC(EQ_MP (SYM(SPEC `a:bin` other_prop_prop)) (ASSUME `proper_bin (thenOn a)`)) THEN 
  ASSUME_TAC(MP (SPEC `a:bin` def_of_thenZe) (ASSUME `proper_bin (thenZe a)`)) THEN
  REWRITE_TAC[SYM (ASSUME `thenZe a = add_bin a a`)] THEN REWRITE_TAC[bin_assoc] THEN
  REWRITE_TAC[SYM(SPECL [`(thenZe a):bin`;`a':bin`;`(thenZe (mult_bin a a')):bin`] bin_assoc)] THEN 
  REWRITE_TAC[SPECL [`(thenZe a):bin`;`a':bin`] bin_sym] THEN 
  REWRITE_TAC[bin_assoc;add_bin]]);;


let nb_mult = prove(
  `!x:nat y:nat. nat_to_bin (mult_un x y) = 
  (mult_bin (nat_to_bin x) (nat_to_bin y))`,
  MATCH_MP_TAC(nat_induct) THEN 
  REWRITE_TAC[mult_un; nat_to_bin; mult_bin] THEN
  GEN_TAC THEN 
  DISCH_TAC THEN 
  MATCH_MP_TAC(nat_induct) THEN 
  CONJ_TAC THENL
  [REWRITE_TAC[mult_un; nat_to_bin; mult_bin;add_unary]
  ;GEN_TAC THEN 
  DISCH_TAC THEN 
  REWRITE_TAC[mult_un;nat_equiv] THEN 
  ASM_REWRITE_TAC[] THEN 
  ASSUME_TAC(SYM(SPEC `a':nat` same_S)) THEN 
  REWRITE_TAC[ASSUME `nat_to_bin (S a') = add_bin On (nat_to_bin a')`] THEN
  ASSUME_TAC(CONJ (SPEC `(S a):nat` always_proper) (SPEC `a':nat` always_proper)) THEN 
  MP_TAC(SPECL [`(nat_to_bin (S a)):bin`; `(nat_to_bin a'):bin`] bin_suc) THEN
  REWRITE_TAC[ASSUME (`proper_bin (nat_to_bin (S a)) /\ proper_bin (nat_to_bin a')`)] THEN 
  DISCH_TAC THEN 
  REWRITE_TAC[SYM(ASSUME 
    `mult_bin (nat_to_bin (S a)) (add_bin On (nat_to_bin a')) = 
    add_bin (nat_to_bin (S a)) (mult_bin (nat_to_bin (S a)) (nat_to_bin a'))`)]]);;

let bn_mult = prove( 
  `!x:bin y:bin. bin_to_nat (mult_bin x y) = 
  mult_un (bin_to_nat x) (bin_to_nat y)`,
  MATCH_MP_TAC(bin_induct) THEN 
  REWRITE_TAC[mult_bin; bin_to_nat; mult_un] THEN 
  CONJ_TAC THENL
  [MATCH_MP_TAC(bin_induct) THEN 
  REWRITE_TAC[bin_to_nat; mult_un;add_unary] THEN 
  CONJ_TAC THEN 
  GEN_TAC THEN 
  DISCH_TAC THEN 
  REWRITE_TAC[get_nat;l_id_of_un_mult]
  ;CONJ_TAC THEN 
  GEN_TAC THEN 
  DISCH_TAC THENL 
  [MATCH_MP_TAC(bin_induct) THEN 
  REWRITE_TAC[mult_bin; bin_to_nat;get_nat;mult_un;r_id_of_un_mult] THEN 
  CONJ_TAC THEN 
  GEN_TAC THEN 
  DISCH_TAC THENL 
  [REWRITE_TAC[dist_mult;mult_un_sym] THEN 
  REWRITE_TAC[SPECL [
    `(add_unary (bin_to_nat a) (bin_to_nat a)):nat`;
    `(bin_to_nat a'):nat`] mult_un_sym] THEN 
  REWRITE_TAC[dist_mult] THEN 
  ASM_REWRITE_TAC[] THEN 
  REWRITE_TAC[mult_un_sym]
  ;REWRITE_TAC[equiv_add] THEN 
  REWRITE_TAC[bin_to_nat;get_nat] THEN 
  REWRITE_TAC[dist_mult] THEN
  REWRITE_TAC[r_id_of_un_mult] THEN 
  REWRITE_TAC[SPECL [
    `(add_unary (bin_to_nat a) (bin_to_nat a)):nat`; 
    `(bin_to_nat a'):nat`] mult_un_sym] THEN 
  REWRITE_TAC[dist_mult] THEN 
  REWRITE_TAC[sym_add] THEN 
  ASM_REWRITE_TAC[] THEN 
  REWRITE_TAC[mult_un_sym]]
  ;MATCH_MP_TAC(bin_induct) THEN 
  REWRITE_TAC[mult_bin; bin_to_nat; mult_un; r_id_of_un_mult;get_nat] THEN 
  CONJ_TAC THEN 
  GEN_TAC THEN 
  DISCH_TAC THENL 
  [REWRITE_TAC[equiv_add;bin_to_nat; get_nat;dist_mult] THEN 
  REWRITE_TAC[SPECL [
    `(add_unary (add_unary (bin_to_nat a) (bin_to_nat a)) (S Zero)):nat`; 
    `(bin_to_nat a'):nat`] mult_un_sym] THEN 
  REWRITE_TAC[dist_mult;r_id_of_un_mult] THEN 
  REWRITE_TAC[SPECL [
    `(add_unary (mult_un (bin_to_nat a') (bin_to_nat a)) 
    (mult_un (bin_to_nat a') (bin_to_nat a))):nat`;
    `(bin_to_nat a'):nat`] sym_add] THEN  
  REWRITE_TAC[assoc_add] THEN 
  ASM_REWRITE_TAC[] THEN 
  REWRITE_TAC[SPECL [
    `(add_unary (add_unary (bin_to_nat a') (mult_un (bin_to_nat a') (bin_to_nat a)))
    (mult_un (bin_to_nat a') (bin_to_nat a))):nat`; 
    `(bin_to_nat a'):nat`] sym_add] THEN 
  REWRITE_TAC[assoc_add] THEN 
  REWRITE_TAC[mult_un_sym]
  ;REWRITE_TAC[equiv_add;bin_to_nat; get_nat;dist_mult] THEN 
  REWRITE_TAC[mult_un_sym] THEN 
  REWRITE_TAC[dist_mult;l_id_of_un_mult] THEN 
  REWRITE_TAC[SPECL [
    `(add_unary (add_unary (bin_to_nat a) (bin_to_nat a)) (S Zero)):nat`;
    `(bin_to_nat a'):nat`] mult_un_sym] THEN 
  REWRITE_TAC[dist_mult;r_id_of_un_mult] THEN 
  ASM_REWRITE_TAC[] THEN 
  REWRITE_TAC[sym_add] THEN 
  REWRITE_TAC[assoc_add] THEN 
  REWRITE_TAC[SPECL [
    `(add_unary (add_unary (add_unary (add_unary 
    (add_unary (S Zero) (bin_to_nat a)) (bin_to_nat a))
    (bin_to_nat a')) (mult_un (bin_to_nat a') (bin_to_nat a))) 
    (mult_un (bin_to_nat a') (bin_to_nat a))):nat`;
    `(bin_to_nat a'):nat`] sym_add] THEN 
  REWRITE_TAC[assoc_add] THEN 
  REWRITE_TAC[SPECL [`(bin_to_nat a'):nat`;`(S Zero):nat`] sym_add] THEN 
  REWRITE_TAC[SYM (SPECL [
    `(S Zero):nat`; 
    `(bin_to_nat a'):nat`; 
    `(bin_to_nat a):nat`] assoc_add)] THEN 
  REWRITE_TAC[SPECL [`(bin_to_nat a'):nat`; `(bin_to_nat a):nat`] sym_add] THEN 
  REWRITE_TAC[assoc_add] THEN 
  REWRITE_TAC[SYM(SPECL [
    `(add_unary (S Zero) (bin_to_nat a)):nat`; 
    `(bin_to_nat a'):nat`; 
    `(bin_to_nat a):nat`] assoc_add)] THEN 
  REWRITE_TAC[SPECL [`(bin_to_nat a'):nat`;`(bin_to_nat a):nat`] sym_add] THEN 
  REWRITE_TAC[assoc_add;mult_un_sym]]]]);;

   

	

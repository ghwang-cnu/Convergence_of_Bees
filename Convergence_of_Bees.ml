loads "Multivariate/make.ml";;
needs "Multivariate/realanalysis.ml";;
loads "CNU/sigmaalgebra.ml";;
loads "CNU/measurespace.ml";;
loads "CNU/probability.ml";;


(* --------------------------------------------------------- *)
(* Definition of fitness function and its influencing factors *)   
(* --------------------------------------------------------- *)

let UAV_perfomence_val = new_definition
    `(UAV_perfomence_val:real^N^M->real^N^M->real^N^M) g c = lambda i j. g$i$j * c$i$j`;;

let TASK_perfomence_val = new_definition
    `(TASK_perfomence_val:real^N^M->real^N^M->real^M) g c = lambda i. sum (1..dimindex(:N)) (\j. (UAV_perfomence_val g c)$i$j)`;;
    
let time_cost = new_definition
    `(time_cost:real^N^M->real^N^M->real^M) g c = lambda i. inv((TASK_perfomence_val g c)$i)`;;

let total_time_cost = new_definition
    `(total_time_cost:real^N^M->real^N^M->real) g c = sum (1..dimindex(:M)) (\i. (time_cost g c)$i)`;;

let norm_priority = new_definition
    `(norm_priority:real^M->real^M) f = lambda i. f$i * inv(sum (1..dimindex(:M)) (\i. f$i))`;;
    
let dist_cost = new_definition
    `(dist_cost:real^2^N->real^2^M->real^N^M) up tp = lambda i j. dist(up$j,tp$i)`;; 
    
let fitness = new_definition
    `(fitness:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->real^N^M) a b r f up tp g c =
    lambda i j. ((norm_priority f)$i pow a * inv((dist_cost up tp)$i$j) pow b *
                 (UAV_perfomence_val g c)$i$j pow r)
                * inv(sum (1..dimindex(:M)) (\i. (norm_priority f)$i pow a *
                                                 inv((dist_cost up tp)$i$j) pow b *
                                                 (UAV_perfomence_val g c)$i$j pow r))`;;
                                                 

(* ---------------------------------------------------------------------------- *)
(* The influencing factors and the property description of the fitness function *)   
(* ---------------------------------------------------------------------------- *)    

(* Vij *)
let RPERF_VALVE_COMPONENT = prove
    (`!g c:real^N^M i j. 1 <= i /\ i <= dimindex(:M) /\ 1 <= j /\ j <= dimindex(:N) ==> (UAV_perfomence_val g c)$i$j = g$i$j * c$i$j`,
    SIMP_TAC[UAV_perfomence_val;LAMBDA_BETA]);; 
    
let RPERF_VALVE_LADD_COMPONENT = prove
    (`!g1 g2 c:real^N^M i j. (UAV_perfomence_val (g1 + g2) c)$i$j = (UAV_perfomence_val g1  c)$i$j + (UAV_perfomence_val g2 c)$i$j`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    ASM_SIMP_TAC[matrix_add; LAMBDA_BETA;REAL_ADD_RDISTRIB;UAV_perfomence_val]);;
    
let RPERF_VALVE_RADD_COMPONENT = prove
    (`!g c1 c2:real^N^M i j. (UAV_perfomence_val g (c1 + c2))$i$j = (UAV_perfomence_val g c1)$i$j + (UAV_perfomence_val g c2)$i$j`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    ASM_SIMP_TAC[matrix_add; LAMBDA_BETA;REAL_ADD_LDISTRIB;UAV_perfomence_val]);;
    
let RPERF_VALVE_ADD_COMPONENT = prove
    (`!g1 g2 c1 c2:real^N^M i j. (UAV_perfomence_val (g1 + g2) (c1 + c2))$i$j = (UAV_perfomence_val g1 c1)$i$j + (UAV_perfomence_val g2 c2)$i$j + (UAV_perfomence_val g1 c2)$i$j + (UAV_perfomence_val g2 c1)$i$j`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k`
    CHOOSE_TAC THENL
     [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l`
    CHOOSE_TAC THENL
     [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    ASM_SIMP_TAC[matrix_add;LAMBDA_BETA;REAL_ADD_RDISTRIB;REAL_ADD_LDISTRIB;UAV_perfomence_val;REAL_ADD_AC]);;
    
let RPERF_VALVE_LADD = prove
    (`!g1 g2 c:real^N^M . UAV_perfomence_val (g1 + g2) c = UAV_perfomence_val g1  c + UAV_perfomence_val g2 c`,
    SIMP_TAC[RPERF_VALVE_COMPONENT;CART_EQ;REAL_ADD_RDISTRIB;MATRIX_ADD_COMPONENT]);;
    
let RPERF_VALVE_RADD = prove
    (`!g c1 c2:real^N^M. UAV_perfomence_val g (c1 + c2) = UAV_perfomence_val g c1 + UAV_perfomence_val g c2`,
    SIMP_TAC[RPERF_VALVE_COMPONENT;CART_EQ;REAL_ADD_LDISTRIB;MATRIX_ADD_COMPONENT]);;
    
let RPERF_VALVE_ADD = prove
    (`!g1 g2 c1 c2:real^N^M. UAV_perfomence_val (g1 + g2) (c1 + c2) = UAV_perfomence_val g1 c1 + UAV_perfomence_val g2 c2 + UAV_perfomence_val g1 c2 + UAV_perfomence_val g2 c1`,
    SIMP_TAC[RPERF_VALVE_COMPONENT;CART_EQ;REAL_ADD_RDISTRIB;REAL_ADD_LDISTRIB;MATRIX_ADD_COMPONENT;REAL_ADD_AC]);;
    
let RPERF_VALVE_LSUB_COMPONENT = prove
    (`!g1 g2 c:real^N^M i j. (UAV_perfomence_val (g1 - g2) c)$i$j = (UAV_perfomence_val g1  c)$i$j - (UAV_perfomence_val g2 c)$i$j`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    ASM_SIMP_TAC[matrix_sub; LAMBDA_BETA;REAL_SUB_RDISTRIB;UAV_perfomence_val]);;
    
let RPERF_VALVE_RSUB_COMPONENT = prove
    (`!g c1 c2:real^N^M i j. (UAV_perfomence_val g (c1 - c2))$i$j = (UAV_perfomence_val g c1)$i$j - (UAV_perfomence_val g c2)$i$j`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    ASM_SIMP_TAC[matrix_sub; LAMBDA_BETA;REAL_SUB_LDISTRIB;UAV_perfomence_val]);;
    
let RPERF_VALVE_SUB_COMPONENT = prove
    (`!g1 g2 c1 c2:real^N^M i j. (UAV_perfomence_val (g1 - g2) (c1 - c2))$i$j = (UAV_perfomence_val g1 c1)$i$j + (UAV_perfomence_val g2 c2)$i$j - (UAV_perfomence_val g1 c2)$i$j - (UAV_perfomence_val g2 c1)$i$j`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    ASM_SIMP_TAC[matrix_sub;LAMBDA_BETA;REAL_SUB_RDISTRIB;REAL_SUB_LDISTRIB;UAV_perfomence_val] THEN REAL_ARITH_TAC);;
    
let RPERF_VALVE_LSUB = prove
    (`!g1 g2 c:real^N^M . UAV_perfomence_val (g1 - g2) c = UAV_perfomence_val g1  c - UAV_perfomence_val g2 c`,
    SIMP_TAC[RPERF_VALVE_COMPONENT;CART_EQ;REAL_SUB_RDISTRIB;MATRIX_SUB_COMPONENT]
    );;

let RPERF_VALVE_RSUB = prove
    (`!g c1 c2:real^N^M . UAV_perfomence_val g (c1 - c2) = UAV_perfomence_val g c1 - UAV_perfomence_val g c2`,
    SIMP_TAC[RPERF_VALVE_COMPONENT;CART_EQ;REAL_SUB_LDISTRIB;MATRIX_SUB_COMPONENT]
    );;

let RPERF_VALVE_SUB = prove
    (`!g1 g2 c1 c2:real^N^M . UAV_perfomence_val (g1 - g2) (c1 - c2) = UAV_perfomence_val g1 c1 + UAV_perfomence_val g2 c2 - UAV_perfomence_val g1 c2 - UAV_perfomence_val g2 c1`,
    SIMP_TAC[RPERF_VALVE_COMPONENT;CART_EQ;REAL_SUB_RDISTRIB;REAL_SUB_LDISTRIB;MATRIX_SUB_COMPONENT;MATRIX_ADD_COMPONENT] THEN
    REAL_ARITH_TAC);;
    
let RPERF_VALVE_ZERO = prove
    (`!g:real^N^M . UAV_perfomence_val g (mat 0) = mat 0 /\ UAV_perfomence_val (mat 0) g = mat 0`,
    SIMP_TAC[CART_EQ;RPERF_VALVE_COMPONENT;MAT_0_COMPONENT;REAL_MUL_RZERO;REAL_MUL_LZERO]);;

let RPERF_VALVE_EQ_0 = prove
    (`!g c:real^N^M . UAV_perfomence_val g c = mat 0 <=> (!i j. 1 <= i /\ i <= dimindex(:M) /\ 1 <= j /\ j <= dimindex(:N) ==> g$i$j = &0 \/ c$i$j = &0)`,
    SIMP_TAC[CART_EQ;RPERF_VALVE_COMPONENT;MAT_0_COMPONENT;REAL_ENTIRE] THEN
    MESON_TAC[]);;
    
let RPERF_VALVE_EQ_COMPONENT = prove
    (`!g1 g2 c1 c2:real^N^M. UAV_perfomence_val g1 c1 = UAV_perfomence_val g2 c2 <=> (!i j. 1 <= i /\ i <= dimindex(:M) /\ 1 <= j /\ j <= dimindex(:N) ==> g1$i$j * c1$i$j = g2$i$j * c2$i$j)`,
    SIMP_TAC[CART_EQ;RPERF_VALVE_COMPONENT] THEN
    MESON_TAC[]);;
    
let RPERF_VALVE_CMUL_COMPONENT = prove
    (`!g c :real^N^M s i j. (s %% UAV_perfomence_val g c)$i$j = s * (UAV_perfomence_val g c)$i$j`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    ASM_SIMP_TAC[matrix_cmul; CART_EQ; LAMBDA_BETA]);;

let RPERF_VALVE_CMUL_LMUL = prove
    (`!g c :real^N^M s. s %% UAV_perfomence_val g c = UAV_perfomence_val (s %% g) c`,
    SIMP_TAC[CART_EQ;RPERF_VALVE_COMPONENT;RPERF_VALVE_CMUL_COMPONENT;MATRIX_CMUL_COMPONENT;REAL_MUL_ASSOC]);;
    
let RPERF_VALVE_CMUL_RMUL = prove
    (`!g c :real^N^M s. s %% UAV_perfomence_val g c = UAV_perfomence_val g (s %% c)`,
    SIMP_TAC[CART_EQ;RPERF_VALVE_COMPONENT;RPERF_VALVE_CMUL_COMPONENT;MATRIX_CMUL_COMPONENT;REAL_ARITH `s:real * g * c = g * s * c`]);;

let RPERF_VALVE_NEG_COMPONENT = prove
    (`!g c :real^N^M i j. (--(UAV_perfomence_val g c))$i$j = --(UAV_perfomence_val g c$i$j) `,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    ASM_SIMP_TAC[matrix_neg; LAMBDA_BETA]);;

let RPERF_VALVE_LNEG = prove
    (`!g c :real^N^M. --(UAV_perfomence_val g c) = UAV_perfomence_val (--g) c`,
    SIMP_TAC[CART_EQ;RPERF_VALVE_COMPONENT;RPERF_VALVE_NEG_COMPONENT;REAL_MUL_LNEG;MATRIX_NEG_COMPONENT]);;
    
let RPERF_VALVE_RNEG = prove
    (`!g c :real^N^M. --(UAV_perfomence_val g c) = UAV_perfomence_val g (--c)`,
    SIMP_TAC[CART_EQ;RPERF_VALVE_COMPONENT;RPERF_VALVE_NEG_COMPONENT;REAL_MUL_RNEG;MATRIX_NEG_COMPONENT]);;
    
    
    
(* Vi *)
let MPERF_VALVE_COMPONENT = prove
    (`!g c:real^N^M i. 1 <= i /\ i <= dimindex(:M) ==> (TASK_perfomence_val g c)$i = sum (1..dimindex(:N)) (\j. (UAV_perfomence_val g c)$i$j)`,
    SIMP_TAC[TASK_perfomence_val;LAMBDA_BETA;UAV_perfomence_val;CART_EQ;RPERF_VALVE_COMPONENT]);;

let MPERF_VALVE_COMPONENT_ALT = prove
    (`!g c:real^N^M i. 1 <= i /\ i <= dimindex(:M) ==> (TASK_perfomence_val g c)$i = sum (1..dimindex(:N)) (\j. g$i$j * c$i$j)`,
    SIMP_TAC[TASK_perfomence_val;LAMBDA_BETA;UAV_perfomence_val;CART_EQ;RPERF_VALVE_COMPONENT]);;

let MPERF_VALVE_LADD_COMPONENT = prove
    (`!g1 g2 c:real^N^M i. TASK_perfomence_val (g1 + g2) c$i = TASK_perfomence_val g1 c$i + TASK_perfomence_val g2 c$i`,
    SIMP_TAC[TASK_perfomence_val] THEN REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\  (!z:real^M. z$i = z$k)` CHOOSE_TAC THENL
    [REWRITE_TAC[FINITE_INDEX_INRANGE];ALL_TAC] THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN
    SIMP_TAC[FINITE_NUMSEG;SUM_ADD;RPERF_VALVE_LADD_COMPONENT]);;

let MPERF_VALVE_RADD_COMPONENT = prove
    (`!g c1 c2:real^N^M i. (TASK_perfomence_val g (c1 + c2))$i = (TASK_perfomence_val g c1)$i + (TASK_perfomence_val g c2)$i`,
    SIMP_TAC[TASK_perfomence_val] THEN REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\  (!z:real^M. z$i = z$k)` CHOOSE_TAC THENL
    [REWRITE_TAC[FINITE_INDEX_INRANGE];ALL_TAC] THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN
    SIMP_TAC[FINITE_NUMSEG;SUM_ADD;RPERF_VALVE_RADD_COMPONENT]);;

let MPERF_VALVE_ADD_COMPONENT = prove
    (`!g1 g2 c1 c2:real^N^M i. (TASK_perfomence_val (g1 + g2) (c1 + c2))$i = (TASK_perfomence_val g1 c1)$i + (TASK_perfomence_val g2 c2)$i + (TASK_perfomence_val g1 c2)$i + (TASK_perfomence_val g2 c1)$i`,
    SIMP_TAC[TASK_perfomence_val] THEN REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\  (!z:real^M. z$i = z$k)` CHOOSE_TAC THENL
    [REWRITE_TAC[FINITE_INDEX_INRANGE];ALL_TAC] THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN
    SIMP_TAC[FINITE_NUMSEG;SUM_ADD;RPERF_VALVE_RADD_COMPONENT;RPERF_VALVE_LADD_COMPONENT;REAL_ADD_AC]);;

let MPERF_VALVE_LADD = prove
    (`!g1 g2 c:real^N^M . TASK_perfomence_val (g1 + g2) c = TASK_perfomence_val g1  c + TASK_perfomence_val g2 c`,
    SIMP_TAC[RPERF_VALVE_COMPONENT;CART_EQ;MPERF_VALVE_LADD_COMPONENT;VECTOR_ADD_COMPONENT]);;

let MPERF_VALVE_RADD = prove
    (`!g c1 c2:real^N^M. TASK_perfomence_val g (c1 + c2) = TASK_perfomence_val g c1 + TASK_perfomence_val g c2`,
    SIMP_TAC[RPERF_VALVE_COMPONENT;CART_EQ;MPERF_VALVE_RADD_COMPONENT;VECTOR_ADD_COMPONENT]);;

let MPERF_VALVE_ADD = prove
    (`!g1 g2 c1 c2:real^N^M. TASK_perfomence_val (g1 + g2) (c1 + c2) = TASK_perfomence_val g1 c1 + TASK_perfomence_val g2 c2 + TASK_perfomence_val g1 c2 + TASK_perfomence_val g2 c1`,
    SIMP_TAC[RPERF_VALVE_COMPONENT;CART_EQ;MPERF_VALVE_ADD_COMPONENT;VECTOR_ADD_COMPONENT]);;

let MPERF_VALVE_LSUB_COMPONENT = prove
    (`!g1 g2 c:real^N^M i. (TASK_perfomence_val (g1 - g2) c)$i = (TASK_perfomence_val g1 c)$i - (TASK_perfomence_val g2 c)$i`,
    SIMP_TAC[TASK_perfomence_val] THEN REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\  (!z:real^M. z$i = z$k)` CHOOSE_TAC THENL
    [REWRITE_TAC[FINITE_INDEX_INRANGE];ALL_TAC] THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN
    SIMP_TAC[FINITE_NUMSEG;SUM_SUB;RPERF_VALVE_LSUB_COMPONENT]);;

let MPERF_VALVE_RSUB_COMPONENT = prove
    (`!g c1 c2:real^N^M i. (TASK_perfomence_val g (c1 - c2))$i = (TASK_perfomence_val g c1)$i - (TASK_perfomence_val g c2)$i`,
    SIMP_TAC[TASK_perfomence_val] THEN REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\  (!z:real^M. z$i = z$k)` CHOOSE_TAC THENL
    [REWRITE_TAC[FINITE_INDEX_INRANGE];ALL_TAC] THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN
    SIMP_TAC[FINITE_NUMSEG;SUM_SUB;RPERF_VALVE_RSUB_COMPONENT]);;

let MPERF_VALVE_SUB_COMPONENT = prove
    (`!g1 g2 c1 c2:real^N^M i. (TASK_perfomence_val (g1 - g2) (c1 - c2))$i = (TASK_perfomence_val g1 c1)$i + (TASK_perfomence_val g2 c2)$i - (TASK_perfomence_val g1 c2)$i - (TASK_perfomence_val g2 c1)$i`,
    SIMP_TAC[TASK_perfomence_val] THEN REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\  (!z:real^M. z$i = z$k)` CHOOSE_TAC THENL
    [REWRITE_TAC[FINITE_INDEX_INRANGE];ALL_TAC] THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN
    SIMP_TAC[FINITE_NUMSEG;SUM_SUB;SUM_ADD;RPERF_VALVE_SUB_COMPONENT]);;

let MPERF_VALVE_LSUB = prove
    (`!g1 g2 c:real^N^M. TASK_perfomence_val (g1 - g2) c = TASK_perfomence_val g1  c - TASK_perfomence_val g2 c`,
    SIMP_TAC[RPERF_VALVE_COMPONENT;CART_EQ;MPERF_VALVE_LSUB_COMPONENT;VECTOR_SUB_COMPONENT]);;

let MPERF_VALVE_RSUB = prove
    (`!g c1 c2:real^N^M. TASK_perfomence_val g (c1 - c2) = TASK_perfomence_val g c1 - TASK_perfomence_val g c2`,
    SIMP_TAC[RPERF_VALVE_COMPONENT;CART_EQ;MPERF_VALVE_RSUB_COMPONENT;VECTOR_SUB_COMPONENT]);;

let MPERF_VALVE_SUB = prove
    (`!g1 g2 c1 c2:real^N^M. TASK_perfomence_val (g1 - g2) (c1 - c2) = TASK_perfomence_val g1 c1 + TASK_perfomence_val g2 c2 - TASK_perfomence_val g1 c2 - TASK_perfomence_val g2 c1`,
    SIMP_TAC[RPERF_VALVE_COMPONENT;CART_EQ;MPERF_VALVE_SUB_COMPONENT;VECTOR_SUB_COMPONENT;VECTOR_ADD_COMPONENT]);;

let MPERF_VALVE_ZERO = prove
    (`!g:real^N^M. TASK_perfomence_val g (mat 0) = vec 0 /\ TASK_perfomence_val (mat 0) g = vec 0`,
    SIMP_TAC[CART_EQ;MPERF_VALVE_COMPONENT;RPERF_VALVE_ZERO;MAT_0_COMPONENT;VEC_COMPONENT;SUM_0]);;

let MPERF_VALVE_EQ_0 = prove
    (`!g c:real^N^M . TASK_perfomence_val g c = vec 0 <=> (!i. 1 <= i /\ i <= dimindex(:M) ==> sum (1..dimindex(:N)) (\j. (UAV_perfomence_val g c)$i$j) = &0)`,
    SIMP_TAC[CART_EQ;RPERF_VALVE_COMPONENT;TASK_perfomence_val;UAV_perfomence_val;LAMBDA_BETA;VEC_COMPONENT]);;

let MPERF_VALVE_EQ_COMPONENT = prove
    (`!g1:real^N^M g2 c1 c2:real^N^M. TASK_perfomence_val g1 c1 = TASK_perfomence_val g2 c2 <=> (!i. 1 <= i /\ i <= dimindex(:M) ==> sum (1..dimindex(:N)) (\j. (UAV_perfomence_val g1 c1)$i$j) = sum (1..dimindex(:N)) (\j. (UAV_perfomence_val g2 c2)$i$j))`,
    SIMP_TAC[CART_EQ;MPERF_VALVE_COMPONENT]);;

let MPERF_VALVE_CMUL_COMPONENT = prove
    (`!g c :real^N^M s i. (s % TASK_perfomence_val g c)$i = s * (TASK_perfomence_val g c)$i`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^M. A$i = A$k`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    ASM_SIMP_TAC[vector_mul; CART_EQ; LAMBDA_BETA]);;

let MPERF_VALVE_CMUL_LMUL = prove
    (`!g c :real^N^M s. s % TASK_perfomence_val g c = TASK_perfomence_val (s %% g) c`,
    SIMP_TAC[CART_EQ;MPERF_VALVE_CMUL_COMPONENT;MPERF_VALVE_COMPONENT;SUM_LMUL;RPERF_VALVE_CMUL_COMPONENT;GSYM RPERF_VALVE_CMUL_LMUL]);;

let MPERF_VALVE_CMUL_RMUL = prove
    (`!g c :real^N^M s. s % TASK_perfomence_val g c = TASK_perfomence_val g (s %% c)`,
    SIMP_TAC[CART_EQ;MPERF_VALVE_CMUL_COMPONENT;MPERF_VALVE_COMPONENT;SUM_LMUL;RPERF_VALVE_CMUL_COMPONENT;GSYM RPERF_VALVE_CMUL_RMUL]);;

let MPERF_VALVE_NEG_COMPONENT = prove
    (`!g c :real^N^M i. (--(TASK_perfomence_val g c))$i = --(TASK_perfomence_val g c$i)`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^M. A$i = A$k`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    ASM_SIMP_TAC[vector_neg; LAMBDA_BETA]);;

let MPERF_VALVE_LNEG = prove
    (`!g c :real^N^M. --(TASK_perfomence_val g c) = TASK_perfomence_val (--g) c`,
    SIMP_TAC[CART_EQ;MPERF_VALVE_COMPONENT;MPERF_VALVE_NEG_COMPONENT;TASK_perfomence_val;LAMBDA_BETA;RPERF_VALVE_LNEG;GSYM SUM_NEG;GSYM RPERF_VALVE_NEG_COMPONENT]);;

let MPERF_VALVE_RNEG = prove
    (`!g c :real^N^M. --(TASK_perfomence_val g c) = TASK_perfomence_val g (--c)`,
    SIMP_TAC[CART_EQ;MPERF_VALVE_COMPONENT;MPERF_VALVE_NEG_COMPONENT;TASK_perfomence_val;LAMBDA_BETA;RPERF_VALVE_RNEG;GSYM SUM_NEG;GSYM RPERF_VALVE_NEG_COMPONENT]);;
    
    
(* ti *)
let TIME_COST_COMPONENT = prove
    (`!g c:real^N^M i. 1 <= i /\ i <= dimindex(:M) ==> (time_cost g c)$i = inv((TASK_perfomence_val g c)$i)`,
    SIMP_TAC[time_cost;LAMBDA_BETA]);;

let TIME_COST_COMPONENT_ALT1 = prove
    (`!g c:real^N^M i. 1 <= i /\ i <= dimindex(:M) ==> (time_cost g c)$i = inv(sum (1..dimindex(:N)) (\j. (UAV_perfomence_val g c)$i$j))`,
    SIMP_TAC[time_cost;LAMBDA_BETA;MPERF_VALVE_COMPONENT]);;

let TIME_COST_COMPONENT_ALT2 = prove
    (`!g c:real^N^M i. 1 <= i /\ i <= dimindex(:M) ==> (time_cost g c)$i = inv(sum (1..dimindex(:N)) (\j. g$i$j * c$i$j))`,
    SIMP_TAC[time_cost;LAMBDA_BETA;MPERF_VALVE_COMPONENT_ALT]);;
    
let TIME_COST_LADD_COMPONENT = prove
    (`!g1 g2 c:real^N^M i. (time_cost (g1 + g2) c)$i = inv(TASK_perfomence_val g1 c$i + TASK_perfomence_val g2 c$i)`,
    SIMP_TAC[time_cost;MPERF_VALVE_LADD_COMPONENT] THEN REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\  (!z:real^M. z$i = z$k)` CHOOSE_TAC THENL
    [REWRITE_TAC[FINITE_INDEX_INRANGE];ALL_TAC] THEN
    ASM_SIMP_TAC[LAMBDA_BETA]);;

let TIME_COST_RADD_COMPONENT = prove
    (`!g c1 c2:real^N^M i. (time_cost g (c1 + c2))$i = inv((TASK_perfomence_val g c1)$i + (TASK_perfomence_val g c2)$i)`,
    SIMP_TAC[time_cost;MPERF_VALVE_RADD_COMPONENT] THEN REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\  (!z:real^M. z$i = z$k)` CHOOSE_TAC THENL
    [REWRITE_TAC[FINITE_INDEX_INRANGE];ALL_TAC] THEN
    ASM_SIMP_TAC[LAMBDA_BETA]);;
    
let TIME_COST_ADD_COMPONENT = prove
    (`!g1 g2 c1 c2:real^N^M i. (time_cost (g1 + g2) (c1 + c2))$i = inv((TASK_perfomence_val g1 c1)$i + (TASK_perfomence_val g2 c2)$i + (TASK_perfomence_val g1 c2)$i + (TASK_perfomence_val g2 c1)$i)`,
    SIMP_TAC[time_cost;MPERF_VALVE_ADD_COMPONENT] THEN REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\  (!z:real^M. z$i = z$k)` CHOOSE_TAC THENL
    [REWRITE_TAC[FINITE_INDEX_INRANGE];ALL_TAC] THEN
    ASM_SIMP_TAC[LAMBDA_BETA]);;
    
let TIME_COST_LSUB_COMPONENT = prove
    (`!g1 g2 c:real^N^M i. (time_cost (g1 - g2) c)$i = inv(TASK_perfomence_val g1 c$i - TASK_perfomence_val g2 c$i)`,
    SIMP_TAC[time_cost;MPERF_VALVE_LSUB_COMPONENT] THEN REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\  (!z:real^M. z$i = z$k)` CHOOSE_TAC THENL
    [REWRITE_TAC[FINITE_INDEX_INRANGE];ALL_TAC] THEN
    ASM_SIMP_TAC[LAMBDA_BETA]);;

let TIME_COST_RSUB_COMPONENT = prove
    (`!g c1 c2:real^N^M i. (time_cost g (c1 - c2))$i = inv((TASK_perfomence_val g c1)$i - (TASK_perfomence_val g c2)$i)`,
    SIMP_TAC[time_cost;MPERF_VALVE_RSUB_COMPONENT] THEN REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\  (!z:real^M. z$i = z$k)` CHOOSE_TAC THENL
    [REWRITE_TAC[FINITE_INDEX_INRANGE];ALL_TAC] THEN
    ASM_SIMP_TAC[LAMBDA_BETA]);;

let TIME_COST_SUB_COMPONENT = prove
    (`!g1 g2 c1 c2:real^N^M i. (time_cost (g1 - g2) (c1 - c2))$i = inv((TASK_perfomence_val g1 c1)$i + (TASK_perfomence_val g2 c2)$i - (TASK_perfomence_val g1 c2)$i - (TASK_perfomence_val g2 c1)$i)`,
    SIMP_TAC[time_cost;MPERF_VALVE_SUB_COMPONENT] THEN REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\  (!z:real^M. z$i = z$k)` CHOOSE_TAC THENL
    [REWRITE_TAC[FINITE_INDEX_INRANGE];ALL_TAC] THEN
    ASM_SIMP_TAC[LAMBDA_BETA]);;
    
let TIME_COST_EQ = prove
    (`!g1:real^N^M g2 c1 c2:real^N^M. time_cost g1 c1 = time_cost g2 c2 <=> TASK_perfomence_val g1 c1 = TASK_perfomence_val g2 c2`,
    SIMP_TAC[time_cost;CART_EQ;LAMBDA_BETA;REAL_EQ_INV2]);;

let TIME_COST_EQ_0 = prove
    (`!g c:real^N^M. time_cost g c = vec 0 <=> (!i. 1 <= i /\ i <= dimindex(:M) ==> (time_cost g c)$i = &0)`,
    SIMP_TAC[CART_EQ;TIME_COST_COMPONENT;LAMBDA_BETA;VEC_COMPONENT]);;
    
let TIME_COST_CMUL_COMPONENT = prove
    (`!g c :real^N^M s i. (s % time_cost g c)$i = s * (time_cost g c)$i`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^M. A$i = A$k`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    ASM_SIMP_TAC[vector_mul; CART_EQ; LAMBDA_BETA]);;

let TIME_COST_CMUL_LMUL = prove
    (`!g c :real^N^M s. inv(s) % time_cost g c = time_cost (s %% g) c`,
    SIMP_TAC[time_cost;GSYM MPERF_VALVE_CMUL_LMUL;VECTOR_ARITH `inv s % (lambda i. inv (TASK_perfomence_val g c$i)) = lambda i.  inv s * inv (TASK_perfomence_val g c$i)`;REAL_INV_MUL;MPERF_VALVE_CMUL_COMPONENT]);;

let TIME_COST_CMUL_RMUL = prove
    (`!g c :real^N^M s. inv(s) % time_cost g c = time_cost g (s %% c)`,
    SIMP_TAC[time_cost;GSYM MPERF_VALVE_CMUL_RMUL;VECTOR_ARITH `inv s % (lambda i. inv (TASK_perfomence_val g c$i)) = lambda i.  inv s * inv (TASK_perfomence_val g c$i)`;GSYM REAL_INV_MUL;MPERF_VALVE_CMUL_COMPONENT]);;

let TIME_COST_NEG_COMPONENT = prove
    (`!g c :real^N^M i. (--(time_cost g c))$i = --(time_cost g c$i)`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^M. A$i = A$k`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    ASM_SIMP_TAC[vector_neg; LAMBDA_BETA]);;

let TIME_COST_LNEG = prove
    (`!g c :real^N^M. --(time_cost g c) = time_cost (--g) c`,
    SIMP_TAC[time_cost;CART_EQ;TIME_COST_COMPONENT;TIME_COST_NEG_COMPONENT;LAMBDA_BETA;GSYM MPERF_VALVE_LNEG;MPERF_VALVE_NEG_COMPONENT;REAL_INV_NEG]);;

let TIME_COST_RNEG = prove
    (`!g c :real^N^M. --(time_cost g c) = time_cost g (--c)`,
    SIMP_TAC[time_cost;CART_EQ;TIME_COST_COMPONENT;TIME_COST_NEG_COMPONENT;LAMBDA_BETA;GSYM MPERF_VALVE_RNEG;MPERF_VALVE_NEG_COMPONENT;REAL_INV_NEG]);;
    
(* T *)
let TOTIME_COST_COMPONENT = prove
    (`!g c:real^N^M. total_time_cost g c = sum (1..dimindex(:M)) (\i.(time_cost g c)$i)`,
    SIMP_TAC[total_time_cost]);;

let TOTIME_COST_LADD_COMPONENT = prove
    (`!g1 g2 c:real^N^M. total_time_cost (g1 + g2) c = sum (1..dimindex(:M)) (\i. (inv((TASK_perfomence_val g1 c)$i + (TASK_perfomence_val g2 c)$i)))`,
    SIMP_TAC[total_time_cost;TIME_COST_LADD_COMPONENT]);;

let TOTIME_COST_RADD_COMPONENT = prove
    (`!g c1 c2:real^N^M. total_time_cost g (c1 + c2) = sum (1..dimindex(:M)) (\i. (inv((TASK_perfomence_val g c1)$i + (TASK_perfomence_val g c2)$i)))`,
    SIMP_TAC[total_time_cost;TIME_COST_RADD_COMPONENT]);;

let TOTIME_COST_ADD_COMPONENT = prove
    (`!g1 g2 c1 c2:real^N^M. total_time_cost (g1 + g2) (c1 + c2) = sum (1..dimindex(:M)) (\i. (inv((TASK_perfomence_val g1 c1)$i + (TASK_perfomence_val g2 c2)$i + (TASK_perfomence_val g1 c2)$i + (TASK_perfomence_val g2 c1)$i)))`,
    SIMP_TAC[total_time_cost;TIME_COST_ADD_COMPONENT]);;
    
let TOTIME_COST_LSUB_COMPONENT = prove
    (`!g1 g2 c:real^N^M. total_time_cost (g1 - g2) c = sum (1..dimindex(:M)) (\i. (inv((TASK_perfomence_val g1 c)$i - (TASK_perfomence_val g2 c)$i)))`,
    SIMP_TAC[total_time_cost;TIME_COST_LSUB_COMPONENT]);;

let TOTIME_COST_RSUB_COMPONENT = prove
    (`!g c1 c2:real^N^M. total_time_cost g (c1 - c2) = sum (1..dimindex(:M)) (\i. (inv((TASK_perfomence_val g c1)$i - (TASK_perfomence_val g c2)$i)))`,
    SIMP_TAC[total_time_cost;TIME_COST_RSUB_COMPONENT]);;

let TOTIME_COST_SUB_COMPONENT = prove
    (`!g1 g2 c1 c2:real^N^M. total_time_cost (g1 - g2) (c1 - c2) = sum (1..dimindex(:M)) (\i. (inv((TASK_perfomence_val g1 c1)$i + (TASK_perfomence_val g2 c2)$i - (TASK_perfomence_val g1 c2)$i - (TASK_perfomence_val g2 c1)$i)))`,
    SIMP_TAC[total_time_cost;TIME_COST_SUB_COMPONENT]);;
    
let TOTIME_COST_EQ_COMPONENT = prove
    (`!g1:real^N^M g2 c1 c2:real^N^M. total_time_cost g1 c1 = total_time_cost g2 c2 <=> sum (1..dimindex(:M)) (\i. (time_cost g1 c1)$i) = sum (1..dimindex(:M)) (\i. (time_cost g2 c2)$i)`,
    SIMP_TAC[total_time_cost]);;

let TOTIME_COST_EQ_0 = prove
    (`!g c:real^N^M.
    (!i. 1 <= i /\ i <= dimindex(:M)
         ==> &0 <= (TASK_perfomence_val g c)$i)
         ==> (total_time_cost g c = &0 <=> time_cost g c = vec 0)`,
    SIMP_TAC[CART_EQ;TOTIME_COST_COMPONENT;LAMBDA_BETA;TIME_COST_EQ_0] THEN
    REPEAT STRIP_TAC THEN EQ_TAC THENL
    [STRIP_TAC THEN MATCH_MP_TAC SUM_POS_EQ_0_NUMSEG THEN
    ASM_SIMP_TAC[time_cost;LAMBDA_BETA;REAL_LE_INV_EQ]; ALL_TAC] THEN
    SIMP_TAC[SUM_EQ_0_NUMSEG]);;

let TOTIME_COST_LNEG = prove
    (`!g c:real^N^M. --(total_time_cost g c) = total_time_cost (--g) c`,
     SIMP_TAC[total_time_cost;GSYM SUM_NEG;GSYM TIME_COST_NEG_COMPONENT;TIME_COST_LNEG]);;

let TOTIME_COST_RNEG = prove
    (`!g c:real^N^M. --(total_time_cost g c) = total_time_cost g (--c)`,
    SIMP_TAC[total_time_cost;GSYM SUM_NEG;GSYM TIME_COST_NEG_COMPONENT;TIME_COST_RNEG]);;
    

(* Fi *)
let NORM_PRIORITY_COMPONENT = prove
    (`!f:real^M i. 1 <= i /\ i <= dimindex(:M) ==> (norm_priority f)$i = f$i * inv(sum (1..dimindex(:M)) (\i. f$i))`,
    SIMP_TAC[norm_priority;LAMBDA_BETA]);;

let NORM_PRIORITY_ADD_COMPONENT = prove
    (`!f1 f2:real^M. (norm_priority (f1 + f2))$i = (f1 + f2)$i * inv(sum (1..dimindex(:M)) (\i. (f1 + f2)$i))`,
    SIMP_TAC[norm_priority] THEN REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\  (!z:real^M. z$i = z$k)` CHOOSE_TAC THENL
    [REWRITE_TAC[FINITE_INDEX_INRANGE];ALL_TAC] THEN
    ASM_SIMP_TAC[LAMBDA_BETA]);;

let NORM_PRIORITY_SUB_COMPONENT = prove
    (`!f1 f2:real^M. (norm_priority (f1 - f2))$i = (f1 - f2)$i * inv(sum (1..dimindex(:M)) (\i. (f1 - f2)$i))`,
    SIMP_TAC[norm_priority] THEN REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\  (!z:real^M. z$i = z$k)` CHOOSE_TAC THENL
    [REWRITE_TAC[FINITE_INDEX_INRANGE];ALL_TAC] THEN
    ASM_SIMP_TAC[LAMBDA_BETA]);;

let NORM_PRIORITY_ADD = prove
    (`!f1 f2:real^M. norm_priority (f1 + f2) = inv(sum (1..dimindex(:M)) (\i. (f1 + f2)$i)) % (f1 + f2)`,
    SIMP_TAC[norm_priority;CART_EQ;LAMBDA_BETA;VECTOR_MUL_COMPONENT;
    REAL_MUL_SYM]);;

let NORM_PRIORITY_SUB = prove
    (`!f1 f2:real^M. norm_priority (f1 - f2) = inv(sum (1..dimindex(:M)) (\i. (f1 - f2)$i)) %  (f1 - f2)`,
    SIMP_TAC[norm_priority;CART_EQ;LAMBDA_BETA;VECTOR_MUL_COMPONENT;
    REAL_MUL_SYM]);;

let NORM_PRIORITY_EQ_COMPONENT = prove
    (`!f1 f2:real^M. norm_priority f1 = norm_priority f2 <=> (!i. 1 <= i /\ i <= dimindex(:M) ==> (f1$i * inv(sum (1..dimindex(:M)) (\i. f1$i))) = (f2$i * inv(sum (1..dimindex(:M)) (\i. f2$i))))`,
    SIMP_TAC[norm_priority;CART_EQ;LAMBDA_BETA]);;

let NORM_PRIORITY_EQ_1 = prove
    (`!f:real^M. ~(sum (1..dimindex (:M)) (\i. f$i) = &0) ==> sum (1..dimindex(:M)) (\i. ((norm_priority f)$i)) = &1`,
    SIMP_TAC[norm_priority;LAMBDA_BETA;SUM_RMUL;REAL_MUL_RINV]);;

let NORM_PRIORITY_EQ_0 = prove
    (`!f:real^M. norm_priority f = vec 0 <=> ((!i. 1 <= i /\ i <= dimindex(:M) ==> f$i = &0) \/ sum (1..dimindex(:M)) (\i. f$i) = &0)`,
    SIMP_TAC[CART_EQ;LAMBDA_BETA;REAL_INV_EQ_0;VEC_COMPONENT;REAL_ENTIRE;REAL_INV_EQ_0;norm_priority] THEN
    MESON_TAC[]);;

let NORM_PRIORITY_CMUL_COMPONENT = prove
    (`!f:real^M s i. (s % norm_priority f)$i = s * (norm_priority f)$i`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^M. A$i = A$k`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    ASM_SIMP_TAC[vector_mul;CART_EQ;LAMBDA_BETA]);;

let NORM_PRIORITY_NEG_COMPONENT = prove
    (`!f:real^M i. (--(norm_priority f))$i = --(norm_priority f$i)`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^M. A$i = A$k`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    ASM_SIMP_TAC[vector_neg;LAMBDA_BETA]);;
    
(* Dij *)
let DIST_COST_COMPONENT = prove
    (`!up:real^2^N tp:real^2^M i j. 1 <= i /\ i <= dimindex(:M) /\ 1 <= j /\ j <= dimindex(:N) ==> (dist_cost up tp)$i$j = dist(up$j,tp$i)`,
    SIMP_TAC[dist_cost;LAMBDA_BETA]);;

let DIST_COST_COMPONENT_ALT = prove
    (`!up:real^2^N tp:real^2^M i j. 1 <= i /\ i <= dimindex(:M) /\ 1 <= j /\ j <= dimindex(:N) ==> (dist_cost up tp)$i$j = sqrt(((up$j$1 - tp$i$1) pow 2) + ((up$j$2 - tp$i$2) pow 2))`,
    SIMP_TAC[dist_cost;LAMBDA_BETA;dist;vector_norm;DOT_2;REAL_POW_2;VECTOR_SUB_COMPONENT]);;

let DIST_COST_POS_LE = prove
    (`!up:real^2^N tp:real^2^M i j. 1 <= i /\ i <= dimindex(:M) /\ 1 <= j /\ j <= dimindex(:N) ==> &0 <= dist_cost up tp$i$j`,
    SIMP_TAC[dist_cost;LAMBDA_BETA;DIST_POS_LE]);;

let DIST_COST_SYM = prove
    (`!up:real^2^N tp:real^2^M. dist_cost up tp = transp(dist_cost tp up)`,
    SIMP_TAC[transp;CART_EQ;LAMBDA_BETA;dist_cost;DIST_SYM]);;

let DIST_COST_TRIANGLE_COMPONENT = prove
    (`!up1 up2:real^2^N tp1 tp2:real^2^M i j. (dist_cost (up1 + up2) (tp1 + tp2))$i$j <= dist(up1$j,tp1$i) + dist(up2$j,tp2$i)`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ (!A:real^N^M. A$i = A$k) /\ (!B:real^2^M. B$i = B$k)`
    CHOOSE_TAC THENL
     [REWRITE_TAC[FINITE_INDEX_INRANGE_2]; ALL_TAC] THEN
    SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ (!z:real^N. z$j = z$l) /\ (!z:real^2^N. z$j = z$l)`
    CHOOSE_TAC THENL
     [REWRITE_TAC[FINITE_INDEX_INRANGE_2]; ALL_TAC] THEN
    ASM_SIMP_TAC[dist_cost;LAMBDA_BETA;matrix_add;GSYM vector_add;
    DIST_TRIANGLE_ADD]);;

let DIST_COST_ADD_COMPONENT = prove
    (`!up1 up2:real^2^N tp1 tp2:real^2^M i j. (dist_cost (up1 + up2) (tp1 + tp2))$i$j = sqrt((((up1 + up2)$j$1 - (tp1 + tp2)$i$1) pow 2) + (((up1 + up2)$j$2 - (tp1 + tp2)$i$2) pow 2))`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ (!A:real^N^M. A$i = A$k) /\ (!B:real^2^M. B$i = B$k)`
    CHOOSE_TAC THENL
     [REWRITE_TAC[FINITE_INDEX_INRANGE_2]; ALL_TAC] THEN
    SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ (!z:real^N. z$j = z$l) /\ (!z:real^2^N. z$j = z$l)`
    CHOOSE_TAC THENL
     [REWRITE_TAC[FINITE_INDEX_INRANGE_2]; ALL_TAC] THEN
    ASM_SIMP_TAC[DIST_COST_COMPONENT_ALT]);;

let DIST_COST_SUB_COMPONENT = prove
    (`!up1 up2:real^2^N tp1 tp2:real^2^M i j. (dist_cost (up1 - up2) (tp1 - tp2))$i$j = sqrt((((up1 - up2)$j$1 - (tp1 - tp2)$i$1) pow 2) + (((up1 - up2)$j$2 - (tp1 - tp2)$i$2) pow 2))`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ (!A:real^N^M. A$i = A$k) /\ (!B:real^2^M. B$i = B$k)`
    CHOOSE_TAC THENL
     [REWRITE_TAC[FINITE_INDEX_INRANGE_2]; ALL_TAC] THEN
    SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ (!z:real^N. z$j = z$l) /\ (!z:real^2^N. z$j = z$l)`
    CHOOSE_TAC THENL
     [REWRITE_TAC[FINITE_INDEX_INRANGE_2]; ALL_TAC] THEN
    ASM_SIMP_TAC[DIST_COST_COMPONENT_ALT]);;
    
let DIST_COST_EQ_COMPONENT = prove
    (`!up1 up2:real^2^N tp1 tp2:real^2^M. dist_cost up1 tp1 = dist_cost up2 tp2 <=> (!i j. 1 <= i /\ i <= dimindex(:M) /\ 1 <= j /\ j <= dimindex(:N) ==> dist(up1$j,tp1$i) pow 2 = dist(up2$j,tp2$i) pow 2)`,
    SIMP_TAC[dist_cost;CART_EQ;LAMBDA_BETA;RIGHT_IMP_FORALL_THM;GSYM IMP_CONJ; GSYM CONJ_ASSOC;DIST_EQ]);;

let DIST_COST_EQ_0 = prove
    (`!up:real^2^N tp:real^2^M. dist_cost up tp = mat 0 <=> (!i j. 1 <= i /\ i <= dimindex(:M) /\ 1 <= j /\ j <= dimindex(:N) ==> up$j = tp$i)`,
    SIMP_TAC[CART_EQ;LAMBDA_BETA;dist_cost;MAT_0_COMPONENT;DIST_EQ_0;RIGHT_IMP_FORALL_THM;GSYM IMP_CONJ;GSYM CONJ_ASSOC]);;

let DIST_COST_CMUL_COMPONENT = prove
    (`!up:real^2^N tp:real^2^M s i j. (s %% dist_cost up tp)$i$j = s * (dist_cost up tp)$i$j`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    ASM_SIMP_TAC[matrix_cmul; CART_EQ; LAMBDA_BETA]);;

let DIST_COST_NEG_COMPONENT = prove
    (`!up:real^2^N tp:real^2^M i j. (--(dist_cost up tp))$i$j = --(dist_cost up tp$i$j)`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    ASM_SIMP_TAC[matrix_neg; LAMBDA_BETA]);;
    

(* fitness *)
let FITNESS_COMPONENT = prove
    (`!a b r f:real^M up:real^2^N tp:real^2^M g:real^N^M c:real^N^M i j. 1 <= i /\ i <= dimindex(:M) /\ 1 <= j /\ j <= dimindex(:N) ==> (fitness a b r f up tp g c)$i$j  = (((norm_priority f)$i pow a * inv((dist_cost up tp)$i$j) pow b * (UAV_perfomence_val g c)$i$j pow r)) *
    (inv(sum (1..dimindex(:M)) (\i. (norm_priority f)$i pow a *
    inv((dist_cost up tp)$i$j) pow b *
    (UAV_perfomence_val g c)$i$j pow r)))`,
    SIMP_TAC[fitness;LAMBDA_BETA]);;

let FITNESS_SUM_EQ_1 = prove
    (`!a b r f:real^M up:real^2^N tp:real^2^M g:real^N^M c:real^N^M j.
    1 <= j /\ j <= dimindex(:N) /\
    ~(sum (1..dimindex (:M))
   (\i. ( f$i * inv (sum (1..dimindex (:M)) (\i. f$i))) pow a * inv (dist (up$j,tp$i)) pow b * (g$i$j * c$i$j) pow r) = &0)
   ==> sum(1..dimindex(:M))(\i. (fitness a b r f up tp g c)$i$j) = &1`,
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (REAL_ARITH `!a. x = a * (inv a) /\ a * inv a = &1 ==> x = &1`) THEN
    EXISTS_TAC `sum (1..dimindex (:M))
             (  \i. norm_priority (f:real^M)$i pow a *
                  inv   (dist_cost (up:real^2^N) (tp:real^2^M)$i$j) pow b *
                  UAV_perfomence_val (g:real^N^M) c$i$j pow r)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[GSYM SUM_RMUL;FITNESS_COMPONENT];ALL_TAC] THEN
    MATCH_MP_TAC REAL_MUL_RINV THEN POP_ASSUM MP_TAC THEN
    CONV_TAC CONTRAPOS_CONV THEN SIMP_TAC[] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    ASM_SIMP_TAC[NORM_PRIORITY_COMPONENT;DIST_COST_COMPONENT;RPERF_VALVE_COMPONENT]);;

let FITNESS_EQ_1_ALT = prove
    (`!a b r f:real^M up:real^2^N tp:real^2^M g:real^N^M c:real^N^M j.
    1 <= j /\ j <= dimindex(:N) /\
    ~(sum (1..dimindex (:M))
   (\i. ( f$i * inv (sum (1..dimindex (:M)) (\i. f$i))) pow a * inv (dist (up$j,tp$i)) pow b * (g$i$j * c$i$j) pow r) = &0)
   ==> sum(1..dimindex(:M))(\i. (fitness a b r f up tp g c)$i$j) = &1`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `sum(1..dimindex(:M))
                    (\i. (fitness a b r (f:real^M) (up:real^2^N) tp g c)$i$j)
                = sum(1..dimindex(:M))
                    (\i. ((f$i * inv (sum (1..dimindex (:M)) (\i. f$i))) pow a *
                          inv (dist (up$j,tp$i)) pow b * (g$i$j * c$i$j) pow r) *
                         inv(sum (1..dimindex (:M))
                            (\i. (f$i * inv (sum (1..dimindex (:M)) (\i. f$i))) pow a * inv (dist (up$j,tp$i)) pow b * (g$i$j * c$i$j) pow r)))` SUBST1_TAC THENL
    [MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    ASM_SIMP_TAC[NORM_PRIORITY_COMPONENT;DIST_COST_COMPONENT;RPERF_VALVE_COMPONENT;FITNESS_COMPONENT];ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV;SUM_RMUL]);;

let FITNESS_EQ_0 = prove
    (`!a b r f:real^M up:real^2^N tp:real^2^M g:real^N^M c:real^N^M.
	fitness a b r f up tp g c = mat 0 <=> (!i j. 1 <= i /\ i <= dimindex(:M) /\ 1 <= j /\ j <= dimindex(:N) ==>
	(( f$i * inv (sum (1..dimindex (:M)) (\i. f$i))) pow a * inv (dist (up$j,tp$i)) pow b * (g$i$j * c$i$j) pow r = &0) \/ (sum (1..dimindex (:M))
   (\i. ( f$i * inv (sum (1..dimindex (:M)) (\i. f$i))) pow a * inv (dist (up$j,tp$i)) pow b * (g$i$j * c$i$j) pow r) = &0))`,
    SIMP_TAC[FITNESS_COMPONENT;NORM_PRIORITY_COMPONENT;DIST_COST_COMPONENT;RPERF_VALVE_COMPONENT;CART_EQ;LAMBDA_BETA;REAL_INV_EQ_0;MAT_0_COMPONENT;REAL_ENTIRE] THEN
    MESON_TAC[]);;

let FITNESS_EQ_COMPONENT = prove
    (`!a1 b1 r1 f1 a2 b2 r2 f2:real^M up1 up2:real^2^N tp1 tp2:real^2^M g1 g2:real^N^M c1 c2:real^N^M. fitness a1 b1 r1 f1 up1 tp1 g1 c1 = fitness a2 b2 r2 f2 up2 tp2 g2 c2 <=> (!i j. 1 <= i /\ i <= dimindex(:M) /\ 1 <= j /\ j <= dimindex(:N) ==> (((norm_priority f1)$i pow a1 * inv((dist_cost up1 tp1)$i$j) pow b1 * (UAV_perfomence_val g1 c1)$i$j pow r1)) *
    (inv(sum (1..dimindex(:M)) (\i. (norm_priority f1)$i pow a1 *
    inv((dist_cost up1 tp1)$i$j) pow b1 *
    (UAV_perfomence_val g1 c1)$i$j pow r1)))
	= (((norm_priority f2)$i pow a2 * inv((dist_cost up2 tp2)$i$j) pow b2 * (UAV_perfomence_val g2 c2)$i$j pow r2)) *
    (inv(sum (1..dimindex(:M)) (\i. (norm_priority f2)$i pow a2 *
    inv((dist_cost up2 tp2)$i$j) pow b2 *
    (UAV_perfomence_val g2 c2)$i$j pow r2))))`,
    SIMP_TAC[fitness;CART_EQ;LAMBDA_BETA] THEN
    MESON_TAC[]);;

let FITNESS_ADD_COMPONENT = prove
    (`!a b r f1:real^M f2:real^M up1 up2:real^2^N tp1 tp2:real^2^M g1 g2:real^N^M c1 c2:real^N^M i j. (fitness a  b r (f1 + f2) (up1 + up2) (tp1 + tp2) (g1 + g2) (c1 + c2))$i$j =
    (((f1 + f2)$i * inv(sum (1..dimindex(:M)) (\i. (f1 + f2)$i))) pow a *
    inv (sqrt((((up1 + up2)$j$1 - (tp1 + tp2)$i$1) pow 2) + (((up1 + up2)$j$2 - (tp1 + tp2)$i$2) pow 2))) pow b *
    ((UAV_perfomence_val g1 c1)$i$j + (UAV_perfomence_val g2 c2)$i$j + (UAV_perfomence_val g1 c2)$i$j + (UAV_perfomence_val g2 c1)$i$j) pow r) *
     inv(sum (1..dimindex (:M))
        (\i. ((f1 + f2)$i * inv(sum (1..dimindex(:M)) (\i. (f1 + f2)$i))) pow a *
             inv (sqrt((((up1 + up2)$j$1 - (tp1 + tp2)$i$1) pow 2) + (((up1 + up2)$j$2 - (tp1 + tp2)$i$2) pow 2))) pow b *
            ((UAV_perfomence_val g1 c1)$i$j + (UAV_perfomence_val g2 c2)$i$j + (UAV_perfomence_val g1 c2)$i$j + (UAV_perfomence_val g2 c1)$i$j) pow r))`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ (!A:real^N^M. A$i = A$k) /\ (!B:real^M. B$i = B$k) /\ (!C:real^2^M. C$i = C$k)`
    CHOOSE_TAC THENL [REWRITE_TAC[finite_index] THEN MESON_TAC[FINITE_INDEX_WORKS]; ALL_TAC] THEN
    SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ (!z:real^N. z$j = z$l) /\ (!z:real^2^N. z$j = z$l)`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE_2]; ALL_TAC] THEN
    ASM_SIMP_TAC[fitness] THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN
    ASM_SIMP_TAC[NORM_PRIORITY_ADD_COMPONENT;DIST_COST_ADD_COMPONENT;RPERF_VALVE_ADD_COMPONENT]);;
    
let FITNESS_SUB_COMPONENT = prove
    (`!a b r f1:real^M f2:real^M up1 up2:real^2^N tp1 tp2:real^2^M g1 g2:real^N^M c1 c2:real^N^M i j. (fitness a  b r (f1 - f2) (up1 - up2) (tp1 - tp2) (g1 - g2) (c1 - c2))$i$j =
    (((f1 - f2)$i * inv(sum (1..dimindex(:M)) (\i. (f1 - f2)$i))) pow a *
    inv (sqrt((((up1 - up2)$j$1 - (tp1 - tp2)$i$1) pow 2) + (((up1 - up2)$j$2 - (tp1 - tp2)$i$2) pow 2))) pow b *
    ((UAV_perfomence_val g1 c1)$i$j + (UAV_perfomence_val g2 c2)$i$j - (UAV_perfomence_val g1 c2)$i$j - (UAV_perfomence_val g2 c1)$i$j) pow r) *
     inv(sum (1..dimindex (:M))
        (\i. ((f1 - f2)$i * inv(sum (1..dimindex(:M)) (\i. (f1 - f2)$i))) pow a *
             inv (sqrt((((up1 - up2)$j$1 - (tp1 - tp2)$i$1) pow 2) + (((up1 - up2)$j$2 - (tp1 - tp2)$i$2) pow 2))) pow b *
            ((UAV_perfomence_val g1 c1)$i$j + (UAV_perfomence_val g2 c2)$i$j - (UAV_perfomence_val g1 c2)$i$j - (UAV_perfomence_val g2 c1)$i$j) pow r))`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ (!A:real^N^M. A$i = A$k) /\ (!B:real^M. B$i = B$k) /\ (!C:real^2^M. C$i = C$k)`
    CHOOSE_TAC THENL [REWRITE_TAC[finite_index] THEN MESON_TAC[FINITE_INDEX_WORKS]; ALL_TAC] THEN
    SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ (!z:real^N. z$j = z$l) /\ (!z:real^2^N. z$j = z$l)`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE_2]; ALL_TAC] THEN
    ASM_SIMP_TAC[fitness] THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN
    ASM_SIMP_TAC[NORM_PRIORITY_SUB_COMPONENT;DIST_COST_SUB_COMPONENT;RPERF_VALVE_SUB_COMPONENT]);;

let FITNESS_CMUL_COMPONENT = prove
    (`!a b r f:real^M up:real^2^N tp:real^2^M g:real^N^M c:real^N^M s i j. (s %% fitness a b r f up tp g c)$i$j = s * (fitness a b r f up tp g c)$i$j`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    ASM_SIMP_TAC[matrix_cmul;CART_EQ;LAMBDA_BETA]);;

let FITNESS_NEG_COMPONENT = prove
    (`!a b r f:real^M up:real^2^N tp:real^2^M g:real^N^M c:real^N^M s i j. (--(fitness a b r f up tp g c))$i$j = --(fitness a b r f up tp g c$i$j)`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    ASM_SIMP_TAC[matrix_neg;LAMBDA_BETA]);;
    
(* -------------------------------------------------------------------------------------- *)
(* The mapping relationship forms the set of all feasible solutions (in matrix form).  R>M *)
(* -------------------------------------------------------------------------------------- *)

let set = new_definition
    `set (A:real^N^M) = 
        {C:real^N^M | ?f:num->num. SURJ f (1..dimindex(:N)) (1..dimindex(:M)) /\ 
            C = (lambda i j.  if i = f(j) then A$i$j else --(&1))}`;;

let set_of_feasible = new_definition
    `(set_of_feasible:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->real^N^M->bool) a b r f up tp g c = 
        set (fitness a b r (f: real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M))`;;
        
let SET_FIT_EMPTY = prove
    (`!a b r f:real^M up:real^2^N tp:real^2^M g:real^N^M c:real^N^M. 
        (&(dimindex (:N)) < &(dimindex (:M))) ==> set_of_feasible a b r f up tp g c = {}`,
    ONCE_SIMP_TAC[GSYM CONTRAPOS_THM] THEN
    SIMP_TAC[set_of_feasible;set;EXTENSION;IN_ELIM_THM;NOT_IN_EMPTY;NOT_FORALL_THM;REAL_NOT_LT;SURJ] THEN
    ONCE_REWRITE_TAC[GSYM SURJECTIVE_ON_IMAGE] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(1..dimindex(:M))`) THEN
    SIMP_TAC[SUBSET_REFL] THEN                   
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `CARD (1..dimindex (:M)) <= CARD(1..dimindex (:N))` MP_TAC THENL
    [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD (IMAGE (f':num->num) s)` THEN
     STRIP_TAC THENL [ASM_SIMP_TAC[LE_REFL];ALL_TAC] THEN
     MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD (s:num->bool)` THEN 
     STRIP_TAC THENL [MATCH_MP_TAC CARD_IMAGE_LE THEN 
                      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `(1..dimindex(:N))` THEN
                      ASM_SIMP_TAC[FINITE_NUMSEG]; ALL_TAC] THEN
     ASM_SIMP_TAC[FINITE_IMAGE;FINITE_NUMSEG;CARD_SUBSET]; ALL_TAC] THEN
     SIMP_TAC[CARD_NUMSEG;ADD_SUB;REAL_OF_NUM_LE]);;
     
let SET_FIT_EQ_1 = prove
    (`!a b r f:real^1 up:real^2^N tp:real^2^1 g:real^N^1 c:real^N^1. 
        CARD(set_of_feasible a b r f up tp g c) = 1`, 
let cardth1 = MESON [CARD_SING] `!A:real^N^M->bool a:real^N^M. A = {a} ==> CARD A = 1` in
REPEAT STRIP_TAC THEN MATCH_MP_TAC cardth1 THEN
SIMP_TAC[set_of_feasible;set;DIMINDEX_1;NUMSEG_SING;EXTENSION;IN_ELIM_THM;SURJ] THEN 
EXISTS_TAC `(fitness a b r f up tp g c):real^N^1` THEN  
REPEAT STRIP_TAC THEN
EQ_TAC THENL
[REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN
SIMP_TAC[IN_SING] THEN ASM_SIMP_TAC[] THEN
REPEAT STRIP_TAC THEN SIMP_TAC[CART_EQ;LAMBDA_BETA;DIMINDEX_1;FORALL_1] THEN
REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i':num`) THEN
ASM_SIMP_TAC[IN_NUMSEG;IN_SING];ALL_TAC] THEN SIMP_TAC[IN_SING] THEN
REPEAT STRIP_TAC THEN EXISTS_TAC `(\x:num. 1)` THEN
SIMP_TAC[] THEN SIMP_TAC[CART_EQ;LAMBDA_BETA;DIMINDEX_1;FORALL_1] THEN
REPEAT STRIP_TAC THEN EXISTS_TAC `1` THEN
SIMP_TAC[IN_NUMSEG;LE_REFL;DIMINDEX_GE_1]);;

(* ------------------------------------------------------------------------- *)
(* Formal modeling of the Bee algorithm                                      *)
(* ------------------------------------------------------------------------- *)

let global_search = new_definition
    `(global_search:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->real^N^M) a b r f up tp g c = 
    @C:real^N^M. C IN set_of_feasible a b r f up tp g c`;;
    
let nm_trans_n = new_definition
    `(nm_trans_n:real^N^M->real^N) A = lambda j. 
        &(@i. (1 <= i /\ i <= dimindex(:M)) /\  ~(A$i$j = --(&1)))`;;

let gnm_trans_n = new_definition
    `(gnm_trans_n:real^N^M->real^N) (global_search (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M)  (g:real^N^M) (c:real^N^M)) = 
      lambda j. &(@i. (1 <= i /\ i <= dimindex(:M)) /\  ~((global_search a b r f up tp g c)$i$j = --(&1)))`;; 
      
let rand_fun = new_definition
    `(rand_fun:real->real->real) a b = @x:real. x IN real_interval[a,b]`;;

let floor_down = new_definition
    `(floor_down:real->int) x = @m. (real_of_int m <= x /\ (x < (real_of_int (int_add m (&1)))))`;;
    
let floor_vec = new_definition
    `(floor_vec:real^N->real^N) a = lambda j. real_of_int (floor_down (a$j))`;;
        
let neighborhood_search = new_definition
    `(neighborhood_search:real^N->real^N->real^N) a ngh = floor_vec (a + (rand_fun (-- &1) (&1) % ngh) )`;;
    
let glocal_search = new_definition
    `(glocal_search:real^N->real^N->real^N) (gnm_trans_n (global_search a b r f up tp g c)) ngh = 
        floor_vec (gnm_trans_n (global_search a b r f up tp g c) + (rand_fun (-- &1) (&1) % ngh) )`;;

let is_solution = new_definition
    `(is_solution:real^N->(real^N^M->bool)->(real^N^M)->bool) a S A <=> 
            (A IN S /\ 
                (!i j. (1 <= j /\ j <= dimindex(:N)) /\ (&i = (a$j)) ==> 
                    ~(A$i$j = --(&1))) /\ 
                    (!i j. (1 <= i /\ i <= dimindex(:M)) /\ 
                            (1 <= j /\ j <= dimindex(:N)) /\
                                ~(&i = (a$j)) 
                                    ==> A$i$j = --(&1)))`;;
                                    
let n_trans_nm = new_definition
    `(n_trans_nm:real^N->(real^N^M->bool)->real^N^M) a S = 
        @A:real^N^M. is_solution a S A`;;
    
let ln_trans_nm = new_definition 
    `(ln_trans_nm:real^N->(real^N^M->bool)->real^N^M) (glocal_search (gnm_trans_n (global_search a b r f up tp g c)) ngh) (set_of_feasible a b r f up tp g c) = 
    @A:real^N^M. is_solution (glocal_search (gnm_trans_n (global_search a b r f up tp g c)) ngh) (set_of_feasible a b r f up tp g c) A`;;

let ngh_solution = new_definition
    `(ngh_solution:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->real^N->(real^N^M->bool)) a b r f up tp g c ngh = 
      {A:real^N^M| is_solution (neighborhood_search (nm_trans_n (global_search a b r f up tp g c)) ngh) (set_of_feasible a b r f up tp g c) A}`;;

let fitness_sum = new_definition
    `(fitness_sum:real^N^M->real) A = 
        sum (1..dimindex(:M)) (\i. sum (1..dimindex(:N)) (\j. A$i$j))`;;

let FITNESS_SUM_LE_RELF = prove
(`!A:real^N^M. 
    fitness_sum A <= fitness_sum A`,
GEN_TAC THEN SIMP_TAC[fitness_sum] THEN
MATCH_MP_TAC SUM_LE_NUMSEG THEN 
REAL_ARITH_TAC);;

let fitness_comp = new_definition
    `(fitness_comp:real^N^M->real^N^M->real^N^M) A B = 
            if fitness_sum B <= fitness_sum A
              then A 
            else B`;;
            
let gl_greedy_selection = new_definition
    `(gl_greedy_selection:real^N^M->real^N^M->real^N^M) (global_search (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M)  (g:real^N^M) (c:real^N^M)) (ln_trans_nm (glocal_search (gnm_trans_n (global_search a b r f up tp g c)) ngh) (set_of_feasible a b r f up tp g c))  = 
        if (fitness_sum (ln_trans_nm (glocal_search (gnm_trans_n (global_search a b r f up tp g c)) ngh) (set_of_feasible a b r f up tp g c))) <= 
            fitness_sum (global_search a b r f up tp g c)
              then global_search a b r f up tp g c 
        else (ln_trans_nm (glocal_search (gnm_trans_n (global_search a b r f up tp g c)) ngh) (set_of_feasible a b r f up tp g c))`;;

let greedy_select = new_definition
`(greedy_select:real^N^M->real^N->(real^N^M->bool)->real^N^M) A ngh B = 
    fitness_comp (n_trans_nm (neighborhood_search 
        (nm_trans_n A) ngh ) (B) ) A`;;
        
(* ------------------------------------------------------------------------- *)
(* Formal modeling of time-homogeneous Markov chains                         *)
(* ------------------------------------------------------------------------- *)

let cond_prob_def = new_definition
   `cond_prob p e1 e2 = (prob p (e1 INTER e2)) / (prob p e2)`;;

let distribution_def = new_definition
   `distribution p X = (\s. prob p ((PREIMAGE X s) INTER (p_space p)))`;;

let joint_pmf_def = new_definition
   `joint_pmf p X Y = (\((A:a->bool),(B:a->bool)). 
     prob p (PREIMAGE X A INTER PREIMAGE Y B INTER p_space p))`;;

let cond_pmf_def = new_definition 
   `cond_pmf p X Y = 
        (\((A:a->bool),(B:a->bool)).
               (joint_pmf p X Y (A,B)) / (distribution p Y B))`;;

let THREE_SETS_INTER = prove 
    (`!A B C. A INTER B INTER (C INTER B) = A INTER C INTER B`, 
     SET_TAC[]);;

let COND_PMF_EQ_COND_PROB = prove
  (`!p X i:a j:a s m n. 
    cond_pmf p (X m) (X n) ({j},{i}) = 
    cond_prob p (PREIMAGE (X m) {j} INTER (p_space p))
                     (PREIMAGE (X n) {i} INTER (p_space p))`,
    SIMP_TAC [cond_pmf_def;cond_prob_def;joint_pmf_def;distribution_def] THEN
    SUBGOAL_THEN  `PREIMAGE (X m) {j:a} INTER PREIMAGE (X n) {i:a} INTER p_space p = 
    PREIMAGE (X m) {j:a} INTER p_space p INTER (PREIMAGE (X n) {i:a} INTER p_space p)` SUBST1_TAC THENL
    [METIS_TAC[GSYM THREE_SETS_INTER];ALL_TAC] THEN 
    SIMP_TAC[INTER_ASSOC;INTER_ACI]);;

let COND_PROB_DISJOINT_ZERO = prove
  (`!A B p. 
    prob_space p /\ A IN events p /\ B IN events p /\ DISJOINT A B ==>
     (cond_prob p A B = &0)`,
    SIMP_TAC[cond_prob_def;PROB_EMPTY;REAL_DIV_EQ_0;DISJOINT;PROB_EMPTY]);;

let DISJOINT_PROC_INTER = prove
  (`!X p (t:num) i:a j:a. ~(i = j) ==>
         (DISJOINT (PREIMAGE (X t) {i} INTER p_space p) (PREIMAGE (X t) {j} INTER p_space p))`,
     SIMP_TAC[PREIMAGE;IN_SING] THEN SET_TAC[]);;

let trans_def = new_definition 
    `Trans X p s t n i j = 
    (if (i:a) IN space_s s /\ (j:a) IN space_s s then
         if ((n:num) = 0) then if (i = j) then &1 else &0
         else cond_prob p (PREIMAGE (X (t + n)) {j} INTER p_space p)
                (PREIMAGE (X t) {i} INTER p_space p)
    else &0)`;;

let increasing_seq_def = new_definition
    `Increasing_seq (t:num->num) = !i j:num. i < j ==> t i < t j`;;

let mc_property_def = new_definition 
    `mc_property X p s <=>
     (!(t:num). random_variable (X t) p s) /\ 
     (!f t (n:num). 
         Increasing_seq t /\ 
         ~(prob p (INTERS (IMAGE (\k. PREIMAGE (X (t k)) {f k} INTER p_space p) (0..n-1))) = &0) ==>
         (cond_pmf p (X (t (n + 1))) (X (t n)) ({f (n + 1)}, {f n}) =
          cond_prob p (PREIMAGE (X (t (n + 1))) {f (n + 1)} INTER p_space p)
                      (PREIMAGE (X (t n)) {f n} INTER p_space p INTER
                       INTERS (IMAGE (\k. PREIMAGE (X (t k)) {f k} INTER p_space p) (0..n-1)))))`;;
                       
let dtmc_def = new_definition 
    `dtmc X p s Linit Ltrans <=> 
    (mc_property X p s) /\ (!x. x IN space_s s ==> {x} IN subsets s) /\ 
    (!(i:a). i IN space_s s ==> (Linit i = distribution p (X (0:num)) {i})) /\
    (!(i:a) (j:a) (t:num). ~(distribution p (X t) {i} = &0) ==> 
           (Ltrans t i j = Trans X p s t 1 i j))`;;

let th_dtmc_def = new_definition 
    `th_dtmc X p s Linit Ltrans <=>
    dtmc X p s Linit Ltrans /\ FINITE (space_s s) /\ 
    (!t t' i:a j:a. ~(distribution p (X t) {i} = &0) /\ ~(distribution p (X t') {i} = &0) ==>
       (Trans X p s t 1 i j = Trans X p s t' 1 i j))`;;

let stationary_distribution_def = new_definition 
    `stationary_distribution p X f s <=>
        (sum (space_s s) (\k. f k) = &1) /\ 
    !i. i IN space_s s ==> (&0 <= f i) /\ 
    (!t:num. f i = sum (space_s s) (\k. (f k) * Trans X p s t 1 k i))`;;

let stationary_pmf_def = new_definition 
    `stationary_pmf X p s = 
        !f t w n. random_variable (X t) p s /\
    (prob p (INTERS (IMAGE (\k. (PREIMAGE (X (w + k)) {f k} INTER p_space p)) 
        (count n))) =
     prob p (INTERS (IMAGE (\k. (PREIMAGE (X (t + k)) {f k} INTER p_space p)) 
        (count n))))`;;

let detailed_balance_equations_def = new_definition 
    `detailed_balance_equations f X p s =
    !(i:'b) j (t:num).  (f i * Trans X p s t 1 i j = f j * Trans X p s t 1 j i)`;;

(* ------------------------------------------------------------------------- *)
(* Formal modeling of Markov chain for the bee algorithm                     *)
(* ------------------------------------------------------------------------- *)

let scoutbee_state = new_definition 
    `(scoutbee_state:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->real^N^M) a b r f up tp g c = 
        global_search a b r f up tp g c`;;
    
let state_iterate = define
    `!A:real^N^M ngh:real^N S:(real^N^M->bool).
    state_iterate A ngh S 0 = A /\
    (!t. state_iterate A ngh S (SUC t) 
         = greedy_select (state_iterate A ngh S t) ngh S)`;;

let scoutbee_state_iterate = define
    `!a b r:num f:real^M up:real^2^N tp:real^2^M g c:real^N^M ngh:real^N.
    scoutbee_state_iterate a b r f up tp g c ngh 0  
    = scoutbee_state a b r f up tp g c /\
    (!t. scoutbee_state_iterate a b r f up tp g c ngh (SUC t) 
         = greedy_select (scoutbee_state_iterate a b r f up tp g c ngh t) ngh (set_of_feasible a b r f up tp g c) )`;;

let scoutbee_state_iterate_test = new_definition
    `(scoutbee_state_iterate_test:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->real^N->num->real^N^M) a b r f up tp g c ngh t = 
     (state_iterate (scoutbee_state a b r f up tp g c) ngh (set_of_feasible a b r f up tp g c) t)`;;

let SCOUTBEE_STATE_ITERATE_TEST_EQ = prove
(`!t:num a b r:num f:real^M up:real^2^N tp:real^2^M g c:real^N^M ngh:real^N.
   (scoutbee_state_iterate_test a b r f up tp g c ngh t) = (state_iterate (scoutbee_state a b r f up tp g c) ngh (set_of_feasible a b r f up tp g c) t)`,
    INDUCT_TAC THEN 
    SIMP_TAC[state_iterate;scoutbee_state_iterate_test] THEN
    SIMP_TAC[state_iterate;scoutbee_state_iterate_test] THEN
    ASM_SIMP_TAC[]);;

let scoutbee_state_seq = new_definition 
    `(scoutbee_state_seq:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->real^N->num->(real^N^M->bool)) a b r f up tp g c ngh t =
    { scoutbee_state_iterate a b r f up tp g c ngh n | 0 <= n /\ n <= t }`;;

let INCREASING_SCOUTBEE_STATE_ITERATE = prove
(`!a:num b:num r:num f:real^M up:real^2^N tp:real^2^M g:real^N^M c:real^N^M ngh:real^N t:num.
    fitness_sum (scoutbee_state_iterate a b r f up tp g c ngh t) <= fitness_sum (scoutbee_state_iterate a b r f up tp g c ngh (SUC t))`,
REPLICATE_TAC 9 GEN_TAC THEN
INDUCT_TAC THENL 
[SIMP_TAC[scoutbee_state_iterate;state_iterate;greedy_select;fitness_comp;fitness_sum] THEN COND_CASES_TAC THEN
REAL_ARITH_TAC;ALL_TAC] THEN
SIMP_TAC[fitness_sum;scoutbee_state_iterate;state_iterate] THEN 
SIMP_TAC[greedy_select;fitness_comp] THEN
COND_CASES_TAC THENL 
[COND_CASES_TAC THENL
[POP_ASSUM MP_TAC THEN SIMP_TAC[fitness_sum;state_iterate];ALL_TAC] THEN
SIMP_TAC[state_iterate] THEN
MATCH_MP_TAC SUM_LE_NUMSEG THEN REAL_ARITH_TAC;ALL_TAC] THEN
MATCH_MP_TAC SUM_LE_NUMSEG THEN REAL_ARITH_TAC    
);;  

let distribution_equ = new_definition
` distribution_equ X p (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) (t:num) <=>
(!i. i IN scoutbee_state_seq (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) (t:num) ==> 
distribution p (X 0) {R | (i = scoutbee_state_iterate a b r f up tp g c ngh 0) /\ (R = i)} = distribution p (X 0) {i})`;;

let mc_property_st = new_definition
`mc_property_st X p (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) (t:num) <=>
    mc_property X p (scoutbee_state_seq (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) (t:num),POW (scoutbee_state_seq a b r f up tp g c ngh t))`;;

let trans_homo = new_definition
`trans_homo X p (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) (t:num) <=>  
  (!t':num t'':num i:real^N^M j:real^N^M. ~(distribution p (X t') {i} = &0) /\ ~(distribution p (X t'') {i} = &0) ==> 
  (Trans X p (scoutbee_state_seq (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) (t:num),
  POW (scoutbee_state_seq a b r f up tp g c ngh t)) t' 1 i j = 
    Trans X p (scoutbee_state_seq (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) (t:num), POW (scoutbee_state_seq a b r f up tp g c ngh t)) t'' 1 i j))`;;

let trans_mc = new_definition
`trans_mc X p (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) (t:num) <=>
(!i j t'. ~(distribution p (X t') {i} = &0) ==> 
(if (i:real^N^M) IN scoutbee_state_seq (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) (t:num) /\
    (j:real^N^M) IN scoutbee_state_seq (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) (t:num)
        then cond_prob p (PREIMAGE (X (t' + 1)) {R | (j = scoutbee_state_iterate a b r f up tp g c ngh (t' + 1)) /\ (R = j)} INTER p_space p) (PREIMAGE (X t') {R | (i = scoutbee_state_iterate a b r f up tp g c ngh t') /\ (R = i)} INTER p_space p) else &0) =
(Trans X p (scoutbee_state_seq a b r f up tp g c ngh t, POW (scoutbee_state_seq a b r f up tp g c ngh t)) t' 1 i j))`;;

let card_finite = new_definition
`card_finite (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) (t:num) <=> 
(CARD (scoutbee_state_seq a b r f up tp g c ngh t) <= t + 1)
 ==> FINITE (scoutbee_state_seq a b r f up tp g c ngh t)`;;
  
let SCOUTBEE_SEQ_CARD_LE = prove 
(`FINITE (scoutbee_state_seq (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) (t:num)) ==>
(CARD (scoutbee_state_seq (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) (t:num)) <= ((t:num) + 1))` ,
REPEAT STRIP_TAC THEN
SIMP_TAC[space_def;scoutbee_state_seq;GSYM IN_NUMSEG] THEN
SUBGOAL_THEN `{scoutbee_state_iterate (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) (n:num) | n IN 0..t} = IMAGE (\n. scoutbee_state_iterate (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) (n:num)) (0..t)` SUBST1_TAC THENL
[SET_TAC[];ALL_TAC] THEN
SUBGOAL_THEN `CARD
 (IMAGE (\n. scoutbee_state_iterate (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) (n:num)) (0..t)) <= CARD (0..t)` MP_TAC THENL
[MATCH_MP_TAC CARD_IMAGE_LE THEN SIMP_TAC[FINITE_NUMSEG];ALL_TAC] THEN
SIMP_TAC[CARD_NUMSEG; ARITH_RULE`((t:num) + 1) - 0 = ((t:num) + 1)`]);;

let SCOUTBEE_STATE_THDTMC = prove 
(`!X p a:num b:num r:num f:real^M up:real^2^N tp:real^2^M g:real^N^M c:real^N^M ngh:real^N t:num Linit Ltrans. 
    s = (((scoutbee_state_seq a b r f up tp g c ngh t),(POW (scoutbee_state_seq a b r f up tp g c ngh t))):(real^N^M->bool)#((real^N^M->bool)->bool)) /\ 
    Linit = (\i:real^N^M. distribution p (X (0:num)) {R |i = (scoutbee_state_iterate a b r f up tp g c ngh 0) /\ (R = i)}) /\ 
    Ltrans = (\t i j. 
    (if i IN space_s s /\ j IN space_s s
        then
         cond_prob p (PREIMAGE (X (t + 1)) {R |j = (scoutbee_state_iterate a b r f up tp g c ngh (t + 1)) /\ (R = j)} INTER p_space p)
                (PREIMAGE (X t) {R |i = (scoutbee_state_iterate a b r f up tp g c ngh t) /\ (R = i)} INTER p_space p)
    else &0)) /\
    card_finite a b r f up tp g c ngh t /\
    trans_homo X p a b r f up tp g c ngh t /\
    distribution_equ X p a b r f up tp g c ngh t /\
    trans_mc X p a b r f up tp g c ngh t /\
    mc_property_st X p a b r f up tp g c ngh t 
    ==> th_dtmc X p s Linit Ltrans`,
SIMP_TAC[] THEN 
SIMP_TAC[th_dtmc_def;dtmc_def] THEN
SIMP_TAC[space_def] THEN 
REPEAT GEN_TAC THEN
INTRO_TAC "a b c d e f g h" THEN 
REPEAT STRIP_TAC THENL
[USE_THEN "h" MP_TAC THEN SIMP_TAC[mc_property_st];
POP_ASSUM MP_TAC THEN SIMP_TAC[subsets_def;POW;SUBSET] THEN SET_TAC[];
POP_ASSUM MP_TAC THEN USE_THEN "f" MP_TAC THEN SIMP_TAC[distribution_equ];
POP_ASSUM MP_TAC THEN USE_THEN "g" MP_TAC THEN SIMP_TAC[trans_mc]; 

SUBGOAL_THEN `(CARD (space_s ((scoutbee_state_seq (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) (t:num),POW (scoutbee_state_seq a b r f up tp g c ngh t)))) <= ((t:num) + 1))` 
MP_TAC THENL
[REPEAT STRIP_TAC THEN
SIMP_TAC[space_def;scoutbee_state_seq;GSYM IN_NUMSEG] THEN
SUBGOAL_THEN `{scoutbee_state_iterate (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) (n:num) | n IN 0..t} = IMAGE (\n. scoutbee_state_iterate (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) (n:num)) (0..t)` SUBST1_TAC THENL
[SET_TAC[];ALL_TAC] THEN
SUBGOAL_THEN `CARD
 (IMAGE (\n. scoutbee_state_iterate (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) (n:num)) (0..t)) <= CARD (0..t)` MP_TAC THENL
[MATCH_MP_TAC CARD_IMAGE_LE THEN SIMP_TAC[FINITE_NUMSEG];ALL_TAC] THEN
SIMP_TAC[CARD_NUMSEG; ARITH_RULE`((t:num) + 1) - 0 = ((t:num) + 1)`];ALL_TAC] THEN
SIMP_TAC[space_def] THEN
USE_THEN "d" MP_TAC THEN
SIMP_TAC[card_finite]; 

POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN USE_THEN "e" MP_TAC THEN SIMP_TAC[trans_homo] THEN
DISCH_TAC THEN 
FIRST_ASSUM(MP_TAC o SPECL [`t':num`; `t'':num`; `i:real^N^M`; `j:real^N^M`]) THEN 
SIMP_TAC[]]);;


(* ----------------- Role classification of the scout bees -------------------------- *)

let all_scoutbee = new_definition
    `(all_scoutbee:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->(real^Q->bool)->real^N^M^Q) a b r f up tp g c (:real^Q) = 
        lambda k. scoutbee_state a b r f up tp g c`;;
        
let all_scoutbeeset = new_definition
`(all_scoutbeeset:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->(real^Q->bool)->(real^N^M->bool)) a b r f up tp g c (:real^Q) = {(all_scoutbee a b r f up tp g c (:real^Q))$i| 1 <= i /\ i <= (dimindex(:Q))}`;;

let sup_mat = new_definition
`sup_mat (S:real^N^M->bool) = @a:real^N^M. 
    (!x:real^N^M. x IN S ==> fitness_sum x <= fitness_sum a) /\
    !b:real^N^M. (!x:real^N^M. x IN S ==> fitness_sum x <= fitness_sum b) ==> fitness_sum a <= fitness_sum b`;;
 
let select_max = define
`!S:(real^N^M->bool).
    select_max S 0 = sup_mat S /\
    (!t. select_max S (SUC t) 
         = sup_mat (S DELETE (select_max S t)))`;;
         
let sort_allscoutbee = new_definition
`(sort_allscoutbee:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->(real^Q->bool)->real^N^M^Q) a b r f up tp g c (:real^Q) = 
lambda k. select_max (all_scoutbeeset a b r f up tp g c (:real^Q)) (k-1)`;;

let optimal_scoutbee = new_definition
    `(optimal_scoutbee:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->(real^Q->bool)->num->real^N^M) a b r f up tp g c (:real^Q) k =
    @(scoutbee_state a b r f up tp g c):real^N^M.
    1 <= k /\ k <= dimindex(:Q) /\ 
    (scoutbee_state a b r f up tp g c) IN { (sort_allscoutbee a b r f up tp g c (:real^Q))$i | 1 <= i /\ i <= k }`;;
    
let optimal_state_iterate = define
    `!a b r:num f:real^M up:real^2^N tp:real^2^M g c:real^N^M ngh:real^N k.
    optimal_state_iterate a b r f up tp g c ngh (:real^Q) k  0  
    = optimal_scoutbee a b r f up tp g c (:real^Q) k /\
    (!t. optimal_state_iterate a b r f up tp g c ngh (:real^Q) k (SUC t) 
         =
         greedy_select (optimal_state_iterate a b r f up tp g c ngh (:real^Q) k t) ngh (set_of_feasible a b r f up tp g c) )`;;

let OPTIMAL_STATE_ITERATE_EQ = prove
(`!t:num a b r:num f:real^M up:real^2^N tp:real^2^M g c:real^N^M ngh:real^N k:num. 
optimal_state_iterate a b r f up tp g c ngh (:real^Q) k t = (state_iterate (optimal_scoutbee a b r f up tp g c (:real^Q) k) ngh (set_of_feasible a b r f up tp g c) t)`,
INDUCT_TAC THEN
SIMP_TAC[optimal_state_iterate;state_iterate] THEN
SIMP_TAC[optimal_state_iterate;state_iterate] THEN
ASM_SIMP_TAC[]);;

let optimal_state_seq = new_definition 
    `(optimal_state_seq:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->real^N->(real^Q->bool)->num->num->(real^N^M->bool)) a b r f up tp g c ngh (:real^Q) k t =
    { optimal_state_iterate a b r f up tp g c ngh (:real^Q) k n | 0 <= n /\ n <= t }`;;

let INCREASING_OPTIMAL_STATE_ITERATE = prove
(`!a:num b:num r:num f:real^M up:real^2^N tp:real^2^M g:real^N^M c:real^N^M ngh:real^N k:num t:num .
    fitness_sum (optimal_state_iterate a b r f up tp g c ngh (:real^Q) k t) <= fitness_sum (optimal_state_iterate a b r f up tp g c ngh (:real^Q) k (SUC t))`,
REPLICATE_TAC 10 GEN_TAC THEN
INDUCT_TAC THENL 
[SIMP_TAC[optimal_state_iterate;greedy_select;fitness_comp;fitness_sum] THEN COND_CASES_TAC THEN
MATCH_MP_TAC SUM_LE_NUMSEG THEN REAL_ARITH_TAC;ALL_TAC] THEN
SIMP_TAC[fitness_sum;optimal_state_iterate] THEN 
SIMP_TAC[greedy_select;fitness_comp] THEN
COND_CASES_TAC THENL 
[COND_CASES_TAC THENL
[POP_ASSUM MP_TAC THEN SIMP_TAC[fitness_sum];ALL_TAC] THEN
MATCH_MP_TAC SUM_LE_NUMSEG THEN REAL_ARITH_TAC;ALL_TAC] THEN
MATCH_MP_TAC SUM_LE_NUMSEG THEN REAL_ARITH_TAC    
);; 

let better_scoutbee = new_definition
    `(better_scoutbee:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->(real^Q->bool)->num->num->real^N^M) a b r f up tp g c (:real^Q) k l =
    @(scoutbee_state a b r f up tp g c):real^N^M.
    1 <= k /\ k <= dimindex(:Q) /\ 
    1 <= l /\ l <= dimindex(:Q) /\
    k + l <= dimindex(:Q) /\
    (scoutbee_state a b r f up tp g c) IN { (sort_allscoutbee a b r f up tp g c (:real^Q))$i | (k + 1) <= i /\ i <= (k + l) }`;;

let better_state_iterate = define
    `!a b r:num f:real^M up:real^2^N tp:real^2^M g c:real^N^M ngh:real^N k l.
    better_state_iterate a b r f up tp g c ngh (:real^Q) k l 0  
    = better_scoutbee a b r f up tp g c (:real^Q) k l /\
    (!t. better_state_iterate a b r f up tp g c ngh (:real^Q) k l (SUC t) 
         =
         greedy_select (better_state_iterate a b r f up tp g c ngh (:real^Q) k l t) ngh (set_of_feasible a b r f up tp g c) )`;;

let BETTER_STATE_ITERATE_EQ = prove
(`!t:num a b r:num f:real^M up:real^2^N tp:real^2^M g c:real^N^M ngh:real^N k:num l:num. 
better_state_iterate a b r f up tp g c ngh (:real^Q) k l t = (state_iterate (better_scoutbee a b r f up tp g c (:real^Q) k l) ngh (set_of_feasible a b r f up tp g c) t)`,
INDUCT_TAC THEN
SIMP_TAC[better_state_iterate;state_iterate] THEN
SIMP_TAC[better_state_iterate;state_iterate] THEN
ASM_SIMP_TAC[]);;
         
let better_state_seq = new_definition 
    `(better_state_seq:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->real^N->(real^Q->bool)->num->num->num->(real^N^M->bool)) a b r f up tp g c ngh (:real^Q) k l t =
    { better_state_iterate a b r f up tp g c ngh (:real^Q) k l n | 0 <= n /\ n <= t }`;;

let INCREASING_BETTER_STATE_ITERATE = prove
(`!a:num b:num r:num f:real^M up:real^2^N tp:real^2^M g:real^N^M c:real^N^M ngh:real^N k:num l:num t:num .
    fitness_sum (better_state_iterate a b r f up tp g c ngh (:real^Q) k l t) <= fitness_sum (better_state_iterate a b r f up tp g c ngh (:real^Q) k l (SUC t))`,
REPLICATE_TAC 11 GEN_TAC THEN
INDUCT_TAC THENL 
[SIMP_TAC[better_state_iterate;greedy_select;fitness_comp;fitness_sum] THEN COND_CASES_TAC THEN
MATCH_MP_TAC SUM_LE_NUMSEG THEN REAL_ARITH_TAC;ALL_TAC] THEN
SIMP_TAC[fitness_sum;better_state_iterate] THEN 
SIMP_TAC[greedy_select;fitness_comp] THEN
COND_CASES_TAC THENL 
[COND_CASES_TAC THENL
[POP_ASSUM MP_TAC THEN SIMP_TAC[fitness_sum];ALL_TAC] THEN
MATCH_MP_TAC SUM_LE_NUMSEG THEN REAL_ARITH_TAC;ALL_TAC] THEN
MATCH_MP_TAC SUM_LE_NUMSEG THEN REAL_ARITH_TAC    
);;

let random_scoutbee = new_definition
    `(random_scoutbee:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->(real^Q->bool)->num->num->num->real^N^M) a b r f up tp g c (:real^Q) k l z =
    @(scoutbee_state a b r f up tp g c):real^N^M.
    1 <= k /\ k <= dimindex(:Q) /\ 
    1 <= l /\ l <= dimindex(:Q) /\
    1 <= z /\ z <= dimindex(:Q) /\
    k + l + z = dimindex(:Q) /\
    (scoutbee_state a b r f up tp g c) IN { (sort_allscoutbee a b r f up tp g c (:real^Q))$i | (k + l + 1) <= i /\ i <= dimindex(:Q) }`;;

let random_state_iterate = define
    `!a b r:num f:real^M up:real^2^N tp:real^2^M g c:real^N^M ngh:real^N k l z.
    random_state_iterate a b r f up tp g c ngh (:real^Q) k l z 0  
    = random_scoutbee a b r f up tp g c (:real^Q) k l z /\
    (!t. random_state_iterate a b r f up tp g c ngh (:real^Q) k l z (SUC t) 
         =
         greedy_select (random_state_iterate a b r f up tp g c ngh (:real^Q) k l z t) ngh (set_of_feasible a b r f up tp g c) )`;;
        
let RANDOM_STATE_ITERATE_EQ = prove
(`!t:num a b r:num f:real^M up:real^2^N tp:real^2^M g c:real^N^M ngh:real^N k:num l:num z:num. 
random_state_iterate a b r f up tp g c ngh (:real^Q) k l z t = (state_iterate (random_scoutbee a b r f up tp g c (:real^Q) k l z) ngh (set_of_feasible a b r f up tp g c) t)`,
INDUCT_TAC THEN
SIMP_TAC[random_state_iterate;state_iterate] THEN
SIMP_TAC[random_state_iterate;state_iterate] THEN
ASM_SIMP_TAC[]);;

let random_state_seq = new_definition 
    `(random_state_seq:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->real^N->(real^Q->bool)->num->num->num->num->(real^N^M->bool)) a b r f up tp g c ngh (:real^Q) k l z t =
    { random_state_iterate a b r f up tp g c ngh (:real^Q) k l z n | 0 <= n /\ n <= t }`;;
    
let INCREASING_RANDOM_STATE_ITERATE = prove
(`!a:num b:num r:num f:real^M up:real^2^N tp:real^2^M g:real^N^M c:real^N^M ngh:real^N k:num l:num z:num t:num.
    fitness_sum (random_state_iterate a b r f up tp g c ngh (:real^Q) k l z t) <= fitness_sum (random_state_iterate a b r f up tp g c ngh (:real^Q) k l z (SUC t))`,
REPLICATE_TAC 12 GEN_TAC THEN
INDUCT_TAC THENL 
[SIMP_TAC[random_state_iterate;greedy_select;fitness_comp;fitness_sum] THEN COND_CASES_TAC THEN
MATCH_MP_TAC SUM_LE_NUMSEG THEN REAL_ARITH_TAC;ALL_TAC] THEN
SIMP_TAC[fitness_sum;random_state_iterate] THEN 
SIMP_TAC[greedy_select;fitness_comp] THEN
COND_CASES_TAC THENL 
[COND_CASES_TAC THENL
[POP_ASSUM MP_TAC THEN SIMP_TAC[fitness_sum];ALL_TAC] THEN
MATCH_MP_TAC SUM_LE_NUMSEG THEN REAL_ARITH_TAC;ALL_TAC] THEN
MATCH_MP_TAC SUM_LE_NUMSEG THEN REAL_ARITH_TAC    
);;


(* ----------------- Calculate the transition probabilities of three scout bee roles ---------- *)

let subspace_num = new_definition 
    `(subspace_num:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->real^N->num) a b r f up tp g c ngh = CARD (ngh_solution a b r f up tp g c ngh)`;;

let q1_fun_optimal = new_definition
`(q1_fun_optimal:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->real^N->(real^Q->bool)->num->num->num->real->real) a b r f up tp g c ngh (:real^Q) k t n e =
    if ((optimal_state_iterate a b r f up tp g c ngh (:real^Q) k (t + n)) IN (ngh_solution a b r f up tp g c ngh)) /\ 
        ((fitness_sum (optimal_state_iterate a b r f up tp g c ngh (:real^Q) k t) + e) <=
           fitness_sum (optimal_state_iterate a b r f up tp g c ngh (:real^Q) k (t + n)))
    then &1 
    else &0`;;

let optimal_scoutbee_trans = new_definition 
    `optimal_scoutbee_trans X p (t:num) (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):(real^Q->bool)) (k:num) (n:num) = 
        Trans X p ((optimal_state_seq a b r f up tp g c ngh (:real^Q) k t),(POW (optimal_state_seq a b r f up tp g c ngh (:real^Q) k t))) t n (optimal_state_iterate a b r f up tp g c ngh (:real^Q) k t) (optimal_state_iterate a b r f up tp g c ngh (:real^Q) k (t+n))`;;

let optcond_prob_1 = new_definition
`(optcond_prob_1 X p (t:num) (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N)) ((:real^Q):(real^Q->bool)) (k:num) <=>
(cond_prob p 
        ({x | X (t + 1) x = (optimal_state_iterate a b r f up tp g c ngh (:real^Q) k (t + 1))} INTER p_space p)
        ({x | X t x = (optimal_state_iterate a b r f up tp g c ngh (:real^Q) k t)} INTER p_space p) = (&1))`;;
        
let OPTISCOUT_TRANS = prove
    (`!t:num X p a:num b:num r:num f:real^M up:real^2^N tp:real^2^M g:real^N^M c:real^N^M ngh:real^N nre:real k:num.
    ((&(subspace_num a b r f up tp g c ngh)) = nre ) /\ 
    (nre > (&0)) /\ 
    (optimal_state_iterate a b r f up tp g c ngh (:real^Q) k (SUC t) IN ngh_solution a b r f up tp g c ngh) /\
    (optimal_state_iterate a b r f up tp g c ngh (:real^Q) k (SUC t) IN optimal_state_seq a b r f up tp g c ngh (:real^Q) k t) /\
    optcond_prob_1 X p t a b r f up tp g c ngh (:real^Q) k
     ==>
        (optimal_scoutbee_trans X p t a b r f up tp g c ngh (:real^Q) k 1) =
            nre * inv(&(subspace_num a b r f up tp g c ngh)) *
                (q1_fun_optimal a b r f up tp g c ngh (:real^Q) k t 1 (&0))`,
    INDUCT_TAC THENL 
    [REPEAT STRIP_TAC THEN
    SIMP_TAC[optimal_scoutbee_trans;trans_def;space_def;optimal_state_seq;LE_ANTISYM;q1_fun_optimal] THEN 
    SIMP_TAC[ARITH_RULE `0 + 1 = SUC 0`;REAL_ADD_RID;INCREASING_OPTIMAL_STATE_ITERATE] THEN
    ASM_SIMP_TAC[ARITH;REAL_MUL_RID] THEN
    SUBGOAL_THEN `{optimal_state_iterate (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):(real^Q->bool)) (k:num) (n:num) | 0 = n} = {optimal_state_iterate a b r f up tp g c ngh (:real^Q) k 0}` SUBST1_TAC THENL [SET_TAC[];ALL_TAC] THEN
    SUBGOAL_THEN `nre * inv (nre) = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_MUL_RINV THEN
    UNDISCH_TAC `nre > &0` THEN REAL_ARITH_TAC;ALL_TAC] THEN
    
    POP_ASSUM MP_TAC THEN 
    SIMP_TAC[optimal_state_iterate;PREIMAGE;optcond_prob_1;ARITH;GSYM IN_SING] THEN
        
    POP_ASSUM MP_TAC THEN
    SIMP_TAC[optimal_state_seq;ARITH;LE_ANTISYM] THEN 
    SUBGOAL_THEN `{optimal_state_iterate (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):(real^Q->bool)) (k:num) (n:num) | 0 = n} = {optimal_state_iterate a b r f up tp g c ngh ((:real^Q):(real^Q->bool)) (k:num) 0}` SUBST1_TAC THENL [SET_TAC[];ALL_TAC] THEN
    SIMP_TAC[GSYM IN_SING;optimal_state_iterate;SET_RULE `!A:real^N^M. A IN {A}`] ;ALL_TAC] THEN
    
    REPEAT STRIP_TAC THEN
    SIMP_TAC[optimal_scoutbee_trans;trans_def;optimal_state_seq;space_def;q1_fun_optimal] THEN
    SIMP_TAC[ARITH_RULE `((t:num) + 1) = (SUC t:num)`; REAL_ADD_RID;INCREASING_OPTIMAL_STATE_ITERATE] THEN
    ASM_SIMP_TAC[ARITH;REAL_MUL_RID] THEN
    SUBGOAL_THEN `nre * inv (nre) = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_MUL_RINV THEN
    UNDISCH_TAC `nre > &0` THEN REAL_ARITH_TAC;ALL_TAC] THEN

    SUBGOAL_THEN `optimal_state_iterate (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):(real^Q->bool)) (k:num) (SUC (t:num)) IN
     {optimal_state_iterate (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):(real^Q->bool)) (k:num) (n:num) | 0 <= n /\ n <= SUC t}` MP_TAC THENL 
     [SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN
     EXISTS_TAC `SUC t:num` THEN ARITH_TAC;ALL_TAC] THEN 
     SIMP_TAC[] THEN 
     
     POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
     SIMP_TAC[optimal_state_seq;optcond_prob_1;ARITH;ARITH_RULE `((t:num) + 1) = (SUC t:num)`;PREIMAGE;IN_SING] 
);;

let q1_fun_better = new_definition
`(q1_fun_better:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->real^N->(real^Q->bool)->num->num->num->num->real->real) a b r f up tp g c ngh (:real^Q) k l t n e =
    if ((better_state_iterate a b r f up tp g c ngh (:real^Q) k l (t + n)) IN (ngh_solution a b r f up tp g c ngh)) /\ 
        ((fitness_sum (better_state_iterate a b r f up tp g c ngh (:real^Q) k l t) + e) <=
           fitness_sum (better_state_iterate a b r f up tp g c ngh (:real^Q) k l (t + n)))
    then &1 
    else &0`;;

let better_scoutbee_trans = new_definition 
    `better_scoutbee_trans X p (t:num) (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):(real^Q->bool)) (k:num) (l:num) (n:num)  = 
        Trans X p ((better_state_seq a b r f up tp g c ngh (:real^Q) k l t),(POW (better_state_seq a b r f up tp g c ngh (:real^Q) k l t))) t n (better_state_iterate a b r f up tp g c ngh (:real^Q) k l t) (better_state_iterate a b r f up tp g c ngh (:real^Q) k l (t+n))`;;

let betcond_prob_1 = new_definition
`(betcond_prob_1 X p (t:num) (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N)) ((:real^Q):(real^Q->bool)) (k:num) (l:num) <=>
(cond_prob p 
        ({x | X (t + 1) x = (better_state_iterate a b r f up tp g c ngh (:real^Q) k l (t + 1))} INTER p_space p)
        ({x | X t x = (better_state_iterate a b r f up tp g c ngh (:real^Q) k l t)} INTER p_space p) = (&1))`;;

let BETTSCOUT_TRANS = prove
    (`!t:num X p a:num b:num r:num f:real^M up:real^2^N tp:real^2^M g:real^N^M c:real^N^M ngh:real^N nrb:real k:num l:num.
    ((&(subspace_num a b r f up tp g c ngh)) = nrb ) /\ 
    (nrb > (&0)) /\ 
    (better_state_iterate a b r f up tp g c ngh (:real^Q) k l (SUC t) IN ngh_solution a b r f up tp g c ngh) /\
    (better_state_iterate a b r f up tp g c ngh (:real^Q) k l (SUC t) IN better_state_seq a b r f up tp g c ngh (:real^Q) k l t) /\
    betcond_prob_1 X p t a b r f up tp g c ngh (:real^Q) k l
     ==>
        (better_scoutbee_trans X p t a b r f up tp g c ngh (:real^Q) k l 1) =
            nrb * inv(&(subspace_num a b r f up tp g c ngh)) *
                (q1_fun_better a b r f up tp g c ngh (:real^Q) k l t 1 (&0))`,
    INDUCT_TAC THENL 
    [REPEAT STRIP_TAC THEN
    SIMP_TAC[better_scoutbee_trans;trans_def;space_def;better_state_seq;LE_ANTISYM;q1_fun_better] THEN 
    SIMP_TAC[ARITH_RULE `0 + 1 = SUC 0`;REAL_ADD_RID;INCREASING_BETTER_STATE_ITERATE] THEN
    ASM_SIMP_TAC[ARITH;REAL_MUL_RID] THEN
    SUBGOAL_THEN `{better_state_iterate (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):(real^Q->bool)) (k:num) (l:num) (n:num) | 0 = n} = {better_state_iterate a b r f up tp g c ngh (:real^Q) k l 0}` SUBST1_TAC THENL [SET_TAC[];ALL_TAC] THEN
    SUBGOAL_THEN `nrb * inv (nrb) = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_MUL_RINV THEN
    UNDISCH_TAC `nrb > &0` THEN REAL_ARITH_TAC;ALL_TAC] THEN
    
    POP_ASSUM MP_TAC THEN 
    SIMP_TAC[better_state_iterate;PREIMAGE;betcond_prob_1;ARITH;GSYM IN_SING] THEN
        
    POP_ASSUM MP_TAC THEN
    SIMP_TAC[better_state_seq;ARITH;LE_ANTISYM] THEN 
    SUBGOAL_THEN `{better_state_iterate (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):(real^Q->bool)) (k:num) (l:num) (n:num) | 0 = n} = {better_state_iterate a b r f up tp g c ngh ((:real^Q):(real^Q->bool)) (k:num) (l:num) 0}` SUBST1_TAC THENL [SET_TAC[];ALL_TAC] THEN
    SIMP_TAC[GSYM IN_SING;better_state_iterate;SET_RULE `!A:real^N^M. A IN {A}`] ;ALL_TAC] THEN
    
    REPEAT STRIP_TAC THEN
    SIMP_TAC[better_scoutbee_trans;trans_def;better_state_seq;space_def;q1_fun_better] THEN
    SIMP_TAC[ARITH_RULE `((t:num) + 1) = (SUC t:num)`; REAL_ADD_RID;INCREASING_BETTER_STATE_ITERATE] THEN
    ASM_SIMP_TAC[ARITH;REAL_MUL_RID] THEN
    SUBGOAL_THEN `nrb * inv (nrb) = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_MUL_RINV THEN
    UNDISCH_TAC `nrb > &0` THEN REAL_ARITH_TAC;ALL_TAC] THEN

    SUBGOAL_THEN `better_state_iterate (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):(real^Q->bool)) (k:num) (l:num) (SUC (t:num)) IN
     {better_state_iterate (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):(real^Q->bool)) (k:num) (l:num) (n:num) | 0 <= n /\ n <= SUC t}` MP_TAC THENL 
     [SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN
     EXISTS_TAC `SUC t:num` THEN ARITH_TAC;ALL_TAC] THEN 
     SIMP_TAC[] THEN 
     
     POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
     SIMP_TAC[better_state_seq;betcond_prob_1;ARITH;ARITH_RULE `((t:num) + 1) = (SUC t:num)`;PREIMAGE;IN_SING] 
);;

let q2_fun_random = new_definition
`(q2_fun_random:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->real^N->(real^Q->bool)->num->num->num->num->num->real->real) a b r f up tp g c ngh (:real^Q) k l z t n e =
    if ((fitness_sum (random_state_iterate a b r f up tp g c ngh (:real^Q) k l z t) + e) <=
           fitness_sum (random_state_iterate a b r f up tp g c ngh (:real^Q) k l z (t + n)))
    then &1 
    else &0`;;

let rand_scoutbee_trans = new_definition 
    `rand_scoutbee_trans X p (t:num) (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):(real^Q->bool)) (k:num) (l:num) (z:num) (n:num) = 
        Trans X p ((random_state_seq a b r f up tp g c ngh (:real^Q) k l z t),(POW (random_state_seq a b r f up tp g c ngh (:real^Q) k l z t))) t n (random_state_iterate a b r f up tp g c ngh (:real^Q) k l z t) (random_state_iterate a b r f up tp g c ngh (:real^Q) k l z (t+n))`;;
        
let cond_prob_card_setfit = new_definition
`(cond_prob_card_setfit X p (t:num) (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):(real^Q->bool)) (k:num) (l:num) (z:num)) <=>
(cond_prob p 
        ({x | X (t + 1) x = (random_state_iterate a b r f up tp g c ngh (:real^Q) k l z (t + 1))} INTER p_space p)
        ({x | X t x = (random_state_iterate a b r f up tp g c ngh (:real^Q) k l z t)} INTER p_space p) = 
    (inv(&(CARD (set_of_feasible a b r f up tp g c)))))`;;
    
let RANDSCOUT_TRANS = prove
    (`!t:num X p a:num b:num r:num f:real^M up:real^2^N tp:real^2^M g:real^N^M c:real^N^M ngh:real^N nrb:real k:num l:num z:num.
    (random_state_iterate a b r f up tp g c ngh (:real^Q) k l z (SUC t) IN random_state_seq a b r f up tp g c ngh (:real^Q) k l z t) /\
    cond_prob_card_setfit X p t a b r f up tp g c ngh (:real^Q) k l z
     ==>
        (rand_scoutbee_trans X p t a b r f up tp g c ngh (:real^Q) k l z 1) = 
            inv(&(CARD (set_of_feasible a b r f up tp g c))) * 
            (q2_fun_random a b r f up tp g c ngh (:real^Q) k l z t 1 (&0))`,
    INDUCT_TAC THENL 
    [REPEAT STRIP_TAC THEN
    SIMP_TAC[rand_scoutbee_trans;trans_def;space_def;random_state_seq;LE_ANTISYM;q2_fun_random] THEN 
    SIMP_TAC[ARITH_RULE `0 + 1 = SUC 0`;REAL_ADD_RID;INCREASING_RANDOM_STATE_ITERATE] THEN
    ASM_SIMP_TAC[ARITH;REAL_MUL_RID] THEN
    SUBGOAL_THEN `{random_state_iterate (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):(real^Q->bool)) (k:num) (l:num) (z:num) (n:num) | 0 = n} = {random_state_iterate a b r f up tp g c ngh (:real^Q) k l z 0}` SUBST1_TAC THENL [SET_TAC[];ALL_TAC] THEN
    
    POP_ASSUM MP_TAC THEN 
    SIMP_TAC[random_state_iterate;PREIMAGE;cond_prob_card_setfit;ARITH;GSYM IN_SING] THEN
        
    POP_ASSUM MP_TAC THEN
    SIMP_TAC[random_state_seq;ARITH;LE_ANTISYM] THEN 
    SUBGOAL_THEN `{random_state_iterate (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):(real^Q->bool)) (k:num) (l:num) (z:num) (n:num) | 0 = n} = {random_state_iterate a b r f up tp g c ngh (:real^Q) k l z 0}` SUBST1_TAC THENL [SET_TAC[];ALL_TAC] THEN
    SIMP_TAC[GSYM IN_SING;random_state_iterate;SET_RULE `!A:real^N^M. A IN {A}`] ;ALL_TAC] THEN
    
    REPEAT STRIP_TAC THEN
    SIMP_TAC[rand_scoutbee_trans;trans_def;random_state_seq;space_def;q2_fun_random] THEN
    SIMP_TAC[ARITH_RULE `((t:num) + 1) = (SUC t:num)`; REAL_ADD_RID;INCREASING_RANDOM_STATE_ITERATE] THEN
    ASM_SIMP_TAC[ARITH;REAL_MUL_RID] THEN

    SUBGOAL_THEN `random_state_iterate (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):(real^Q->bool)) (k:num) (l:num) (z:num) (SUC (t:num)) IN
     {random_state_iterate (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) (:real^Q) k l z (n:num) | 0 <= n /\ n <= SUC t}` MP_TAC THENL 
     [SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN
     EXISTS_TAC `SUC t:num` THEN ARITH_TAC;ALL_TAC] THEN 
     SIMP_TAC[] THEN 
     
     POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
     SIMP_TAC[random_state_seq;cond_prob_card_setfit;ARITH;ARITH_RULE `((t:num) + 1) = (SUC t:num)`;PREIMAGE;IN_SING]
);;


(* ----------------- Calculate the transition probability of the single state of the scout bee -------------------- *)

let scoutbee_trans = new_definition 
    `scoutbee_trans X p (t:num) (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) (n:num) = 
        Trans X p ((scoutbee_state_seq a b r f up tp g c ngh t),(POW (scoutbee_state_seq a b r f up tp g c ngh t))) t n (scoutbee_state_iterate a b r f up tp g c ngh t) (scoutbee_state_iterate a b r f up tp g c ngh (t+n))`;;

let optimal_equ = new_definition
`optimal_equ X p (t:num) (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):(real^Q->bool)) (n:num) (k:num) <=>
(!i:num. (1 <= i /\ i <= k) ==>
scoutbee_trans X p (t:num) (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) (n:num) =
optimal_scoutbee_trans X p (t:num) (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):(real^Q->bool)) (k:num) (n:num)) `;;

let better_equ = new_definition
`better_equ X p (t:num) (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):(real^Q->bool)) (n:num) (k:num) (l:num) <=>
(!i:num. ((k + 1) <= i /\ i <= (k + l)) ==>
scoutbee_trans X p (t:num) (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) (n:num) =
better_scoutbee_trans X p (t:num) (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):(real^Q->bool)) (k:num) (l:num) (n:num))`;;
    
let random_equ = new_definition
`random_equ X p (t:num) (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):(real^Q->bool)) (n:num) (k:num) (l:num) (z:num)<=>
(!i:num. ((k + l + 1) <= i /\ i <= dimindex(:Q)) ==>
scoutbee_trans X p (t:num) (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) (n:num) =
rand_scoutbee_trans X p (t:num) (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):(real^Q->bool)) (k:num) (l:num) (z:num) (n:num))`;;

let SCOUTBEE_TRANS_THREE = prove
(`!t:num X p a:num b:num r:num f:real^M up:real^2^N tp:real^2^M g:real^N^M c:real^N^M ngh:real^N k l z.
optimal_equ X p t a b r f up tp g c ngh (:real^Q) 1 k /\
better_equ X p t a b r f up tp g c ngh (:real^Q) 1 k l /\
random_equ X p t a b r f up tp g c ngh (:real^Q) 1 k l z ==>
(!i:num. (1 <= i /\ i <= k) ==> 
(scoutbee_trans X p t a b r f up tp g c ngh 1 =
    (optimal_scoutbee_trans X p t a b r f up tp g c ngh (:real^Q) k 1))) \/
(!i:num. ((k + 1) <= i /\ i <= (k + l)) ==>
scoutbee_trans X p t a b r f up tp g c ngh 1 =
    (better_scoutbee_trans X p t a b r f up tp g c ngh (:real^Q) k l 1)) \/
(!i:num. ((k + l + 1) <= i /\ i <= dimindex(:Q)) ==>
scoutbee_trans X p t a b r f up tp g c ngh 1 =
    (rand_scoutbee_trans X p t a b r f up tp g c ngh (:real^Q) k l z 1))`,
SIMP_TAC[optimal_equ;better_equ;random_equ] THEN
MESON_TAC[]);;

(*-----------------------------------------------------------------*)

let generation_state = new_definition
    `(generation_state:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->(real^Q->bool)->real^N^M^Q) a b r f up tp g c (:real^Q) = 
        lambda k. scoutbee_state a b r f up tp g c`;;
        
let generation_state_iterate = new_definition
    `(generation_state_iterate:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->real^N->(real^Q->bool)->num->real^N^M^Q) a b r f up tp g c ngh (:real^Q) t = 
        lambda k. (state_iterate ((generation_state a b r f up tp g c (:real^Q))$k) ngh (set_of_feasible a b r f up tp g c) t)`;;

let generation_state_seq = new_definition 
    `(generation_state_seq:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->real^N->(real^Q->bool)->num->(real^N^M^Q->bool)) a b r f up tp g c ngh (:real^Q) t =
       { generation_state_iterate a b r f up tp g c ngh (:real^Q) n | 0 <= n /\ n <= t }`;;

let GENERATION_SCOUTBEE_ITERATE_EQ = prove
(`!t:num a:num b:num r:num f:real^M up:real^2^N tp:real^2^M g:real^N^M c:real^N^M ngh:real^N  n:num.
    generation_state_iterate a b r f up tp g c ngh (:real^Q) t =
    (lambda k. scoutbee_state_iterate_test a b r f up tp g c ngh t)`,
SIMP_TAC[SCOUTBEE_STATE_ITERATE_TEST_EQ;generation_state_iterate;generation_state;LAMBDA_BETA;CART_EQ]);;

let all_best_state = new_definition
    `all_best_state (S:real^N^M->bool) = 
        @C:real^N^M. C IN S /\
            (!A. A IN S ==> fitness_sum A <= fitness_sum C)`;;

let scoutbee_best_state = new_definition 
`(scoutbee_best_state:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->real^N->num->real->num->real^N^M) a b r f up tp g c ngh t e n =
    @(scoutbee_state_iterate a b r f up tp g c ngh n):real^N^M.
    ((1 <= n /\ n <= t) /\
    (((fitness_sum (all_best_state (set_of_feasible a b r f up tp g c))) - e) <= fitness_sum (scoutbee_state_iterate a b r f up tp g c ngh n)) /\ 
    (fitness_sum (scoutbee_state_iterate a b r f up tp g c ngh n) <= 
                (fitness_sum (all_best_state (set_of_feasible a b r f up tp g c))) + e))`;;

let generation_best_state = new_definition 
`(generation_best_state:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->real^N->(real^Q->bool)->num->real->num->real^N^M^Q) a b r f up tp g c ngh (:real^Q) t e n =
      @(generation_state_iterate a b r f up tp g c ngh (:real^Q) n):real^N^M^Q. 
      (1 <= n /\ n <= t) /\
        (?k. (1<= k /\ k <= dimindex(:Q)) /\ 
            (((generation_state_iterate a b r f up tp g c ngh (:real^Q) n):real^N^M^Q)$k = (scoutbee_best_state a b r f up tp g c ngh t e n)))`;;
            
let generation_iterate_fitness = new_definition 
    `(generation_iterate_fitness:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->real^N->(real^Q->bool)->num->real) a b r f up tp g c ngh (:real^Q) t = 
    fitness_sum (all_best_state { (generation_state_iterate a b r f up tp g c ngh (:real^Q) t)$k | 1 <= k /\ k <= dimindex(:Q) })`;;

let generation_trans = new_definition
`generation_trans X p (t:num) (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):real^Q->bool) 1 = 
        product (1..dimindex(:Q)) (\k. Trans (\i B. (X i B)$k) p ((scoutbee_state_seq a b r f up tp g c ngh t),(POW (scoutbee_state_seq a b r f up tp g c ngh t))) t 1 ((generation_state_iterate a b r f up tp g c ngh (:real^Q) t)$k) ((generation_state_iterate a b r f up tp g c ngh (:real^Q) (t+1))$k) )`;;

let trans_homo2 = new_definition
`trans_homo2 X p (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):real^Q->bool) (t:num) <=>  
  (!t':num t'':num i:real^N^M^Q j:real^N^M^Q. ~(distribution p (X t') {i} = &0) /\ ~(distribution p (X t'') {i} = &0) ==> 
  (Trans X p (generation_state_seq (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):real^Q->bool) (t:num), POW (generation_state_seq a b r f up tp g c ngh (:real^Q) t)) t' 1 i j = 
    Trans X p (generation_state_seq (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):real^Q->bool) (t:num), POW (generation_state_seq a b r f up tp g c ngh (:real^Q) t)) t'' 1 i j))`;;
    
let trans_mc2 = new_definition
`trans_mc2 X p (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):real^Q->bool) (t:num) <=>
(!i j t'. (~(distribution p (X t') {i} = &0)) ==> 
((if (i:real^N^M^Q) IN generation_state_seq (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):real^Q->bool) (t:num) /\
    (j:real^N^M^Q) IN generation_state_seq (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):real^Q->bool) (t:num)
        then cond_prob p (PREIMAGE (X (t' + 1)) {R | j = generation_state_iterate(a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):real^Q->bool) (t' + 1) /\ R = j} INTER p_space p) (PREIMAGE (X t') {R | i = generation_state_iterate a b r f up tp g c ngh (:real^Q) t' /\ R = i} INTER p_space p)
            else &0) =
             Trans X p (generation_state_seq (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):real^Q->bool) (t:num), POW (generation_state_seq a b r f up tp g c ngh (:real^Q) t)) t' 1 i j))`;;

let distribution_equ2 = new_definition
` distribution_equ2 X p (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):real^Q->bool) (t:num) <=>
(!i. i IN generation_state_seq (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):real^Q->bool) (t:num) ==> 
distribution p (X 0) {R | i = generation_state_iterate a b r f up tp g c ngh (:real^Q) 0 /\ R = i} = distribution p (X 0) {i})`;;

let mc_property_st2 = new_definition
`mc_property_st2 X p (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):real^Q->bool) (t:num) <=>
(mc_property X p
      (generation_state_seq (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):real^Q->bool) (t:num), POW (generation_state_seq a b r f up tp g c ngh (:real^Q) t)))`;;     
      
let card_finite2 = new_definition
`card_finite2 (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N)((:real^Q):real^Q->bool) (t:num) <=> 
 (CARD (generation_state_seq a b r f up tp g c ngh (:real^Q) t) <= t + 1) ==>
 FINITE (generation_state_seq a b r f up tp g c ngh (:real^Q) t)`;;
 
let GENERATION_SEQ_CARD_LE = prove 
(`FINITE (generation_state_seq (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):real^Q->bool) (t:num)) ==>
(CARD (generation_state_seq (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):real^Q->bool) (t:num)) <= ((t:num) + 1))` ,
REPEAT STRIP_TAC THEN
SIMP_TAC[space_def;generation_state_seq;GSYM IN_NUMSEG] THEN
SUBGOAL_THEN `{generation_state_iterate (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):real^Q->bool) (n:num) | n IN 0..t} = IMAGE (\n. generation_state_iterate (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):real^Q->bool) (n:num)) (0..t)` SUBST1_TAC THENL
[SET_TAC[];ALL_TAC] THEN
SUBGOAL_THEN `CARD
 (IMAGE (\n. generation_state_iterate (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N)  ((:real^Q):real^Q->bool) (n:num)) (0..t)) <= CARD (0..t)` MP_TAC THENL
[MATCH_MP_TAC CARD_IMAGE_LE THEN SIMP_TAC[FINITE_NUMSEG];ALL_TAC] THEN
SIMP_TAC[CARD_NUMSEG; ARITH_RULE`((t:num) + 1) - 0 = ((t:num) + 1)`]);;
 
let GENERATION_STATE_THDTMC = prove 
(`!X p a:num b:num r:num f:real^M up:real^2^N tp:real^2^M g:real^N^M c:real^N^M ngh:real^N t:num Linit Ltrans.
    s = ((generation_state_seq a b r f up tp g c ngh (:real^Q) t),(POW (generation_state_seq a b r f up tp g c ngh (:real^Q) t))) /\
    Linit = (\i:real^N^M^Q. distribution p (X (0:num)) {R |i = (generation_state_iterate a b r f up tp g c ngh (:real^Q) 0) /\ (R = i)}) /\ 
    Ltrans = (\t i j. 
    (if i IN space_s s /\ j IN space_s s 
        then
         cond_prob p (PREIMAGE (X (t + 1)) {R |j = (generation_state_iterate a b r f up tp g c ngh (:real^Q) (t + 1)) /\ (R = j)} INTER p_space p)
                (PREIMAGE (X t) {R |i = (generation_state_iterate a b r f up tp g c ngh (:real^Q) t) /\ (R = i)} INTER p_space p)
    else &0)) /\
    card_finite2 a b r f up tp g c ngh (:real^Q) t /\
    trans_homo2 X p a b r f up tp g c ngh (:real^Q) t /\
    distribution_equ2 X p a b r f up tp g c ngh (:real^Q) t /\
    trans_mc2 X p a b r f up tp g c ngh (:real^Q) t /\
    mc_property_st2 X p a b r f up tp g c ngh (:real^Q) t
    ==>
        th_dtmc X p s Linit Ltrans`,

SIMP_TAC[] THEN 
SIMP_TAC[th_dtmc_def;dtmc_def] THEN
SIMP_TAC[space_def] THEN 
REPEAT GEN_TAC THEN
INTRO_TAC "a b c d e f g h" THEN 
REPEAT STRIP_TAC THENL
[USE_THEN "h" MP_TAC THEN SIMP_TAC[mc_property_st2];
POP_ASSUM MP_TAC THEN SIMP_TAC[subsets_def;POW;SUBSET] THEN SET_TAC[];
POP_ASSUM MP_TAC THEN USE_THEN "f" MP_TAC THEN SIMP_TAC[distribution_equ2];
POP_ASSUM MP_TAC THEN USE_THEN "g" MP_TAC THEN SIMP_TAC[trans_mc2]; 

SUBGOAL_THEN `(CARD (generation_state_seq (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):real^Q->bool) (t:num)) <= ((t:num) + 1))` MP_TAC THENL
[REPEAT STRIP_TAC THEN
SIMP_TAC[space_def;generation_state_seq;GSYM IN_NUMSEG] THEN
SUBGOAL_THEN `{generation_state_iterate (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):real^Q->bool) (n:num) | n IN 0..t} = IMAGE (\n. generation_state_iterate (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):real^Q->bool) (n:num)) (0..t)` SUBST1_TAC THENL
[SET_TAC[];ALL_TAC] THEN
SUBGOAL_THEN `CARD
 (IMAGE (\n. generation_state_iterate (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N)  ((:real^Q):real^Q->bool) (n:num)) (0..t)) <= CARD (0..t)` MP_TAC THENL
[MATCH_MP_TAC CARD_IMAGE_LE THEN SIMP_TAC[FINITE_NUMSEG];ALL_TAC] THEN
SIMP_TAC[CARD_NUMSEG; ARITH_RULE`((t:num) + 1) - 0 = ((t:num) + 1)`];ALL_TAC] THEN
SIMP_TAC[space_def] THEN
USE_THEN "d" MP_TAC THEN
SIMP_TAC[card_finite2]; 

POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN USE_THEN "e" MP_TAC THEN SIMP_TAC[trans_homo2] THEN
DISCH_TAC THEN 
FIRST_ASSUM(MP_TAC o SPECL [`t':num`; `t'':num`; `i:real^N^M^Q`; `j:real^N^M^Q`]) THEN 
SIMP_TAC[]]);;       
        
(*-----------------------------------------------------------------*)  

let allgeneration_iterate_fitvec = new_definition
    `(allgeneration_iterate_fitvec:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->real^N->(real^Q->bool)->(real^T->bool)->real^T) a b r f up tp g c ngh (:real^Q) (:real^T) = 
    lambda i. generation_iterate_fitness a b r f up tp g c ngh (:real^Q) i`;;
    
let allgeneration_iterate_sort = define
    `!A:real^T.  
    ((allgeneration_iterate_sort A 0) = &1) /\
    (!i. (allgeneration_iterate_sort A (SUC i)) =
          if A$(SUC (SUC i)) = A$(SUC i) 
          then (allgeneration_iterate_sort A i)
          else ((allgeneration_iterate_sort A i) + &1) )`;;

let allgeneration_iterate_sortvec = new_definition
    `(allgeneration_iterate_sortvec:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->real^N->(real^Q->bool)->(real^T->bool)->real^T) a b r f up tp g c ngh (:real^Q) (:real^T) = 
    lambda k. allgeneration_iterate_sort (allgeneration_iterate_fitvec a b r f up tp g c ngh (:real^Q) (:real^T)) (k - 1) `;;
    
let group_state = new_definition
    `(group_state:num->num->num->real^M->real^2^N->real^2^M->real^N^M->real^N^M->real^N->(real^Q->bool)->(real^T->bool)->(real^Ng->bool)->(real^N^M^Q->bool)^Ng) a b r f up tp g c ngh (:real^Q) (:real^T) (:real^Ng) =
    lambda i. {(generation_state_iterate a b r f up tp g c ngh (:real^Q) k) | ((1 <= k /\ k <= dimindex(:T)) /\ ((allgeneration_iterate_sortvec a b r f up tp g c ngh (:real^Q) (:real^T))$k = &i))}`;;
    
let group_trans = new_definition 
    `group_trans X p (t:num) (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):(real^Q->bool)) ((:real^T):(real^T->bool)) ((:real^Ng):(real^Ng->bool)) (n:num) (i:num) (j:num) = 
    (if i <= j  then 
        sum { k1 | (generation_state_iterate a b r f up tp g c ngh (:real^Q) k1) IN ((group_state a b r f up tp g c ngh (:real^Q) (:real^T) (:real^Ng))$i) }    
            (\k1. sum { k2 | (generation_state_iterate a b r f up tp g c ngh (:real^Q) k2) IN ((group_state a b r f up tp g c ngh (:real^Q) (:real^T) (:real^Ng))$j) } 
                (\k2. Trans X p ((generation_state_seq a b r f up tp g c ngh (:real^Q) t),(POW (generation_state_seq a b r f up tp g c ngh (:real^Q) t))) t n 
                (generation_state_iterate a b r f up tp g c ngh (:real^Q) k1)
                (generation_state_iterate a b r f up tp g c ngh (:real^Q) k2)))
    else &0)`;; 


(* ------------------------------------------------------------------------- *)
(* Formal verification of the convergence of the bee algorithm               *)
(* ------------------------------------------------------------------------- *)

let group_trans_mat = new_definition 
    `group_trans_mat X p (t:num) (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):(real^Q->bool)) ((:real^T):(real^T->bool)) ((:real^Ng):(real^Ng->bool)) (n:num) (i:num) (j:num) = 
        lambda k l. group_trans X p (t:num) (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):(real^Q->bool)) ((:real^T):(real^T->bool)) ((:real^Ng):(real^Ng->bool)) (n:num) (i:num) (j:num)`;;
        
let sum_spaces_s_eq = new_definition
`sum_spaces_s_eq X (t:num) j m Linit Ltrans p s <=>
sum (space_s s) (\k. cond_pmf p (X (t + m)) (X t) ({k},{j})) = &1`;;

let stationary_eq = new_definition
    `stationary_eq X p (t:num) (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):(real^Q->bool)) ((:real^T):(real^T->bool)) ((:real^Ng):(real^Ng->bool)) (n:num) (i:num) (j:num) (z:real^Ng) <=>
    (!k:num. sum (1..dimindex(:Ng)) (\k. (z:real^Ng)$k ) = &1) /\
        (!k l:num. z$k = sum (1..dimindex(:Ng)) 
            (\l. z$l * (column k ((group_trans_mat X p t a b r f up tp g c ngh ((:real^Q):(real^Q->bool)) ((:real^T):(real^T->bool)) ((:real^Ng):(real^Ng->bool)) n i j):real^Ng^Ng)$l)))
    ==> 
    (z = (lambda i. if i < dimindex(:Ng) then &0 else &1):real^Ng)`;;
    
let STATIONARY_DISTRIBUTION_EQ = prove 
    (`!X p (t:num) (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) (n:num) (i:num) (j:num) (z:real^Ng).
    stationary_eq  X p (t:num) (a:num) (b:num) (r:num) (f:real^M) (up:real^2^N) (tp:real^2^M) (g:real^N^M) (c:real^N^M) (ngh:real^N) ((:real^Q):(real^Q->bool)) ((:real^T):(real^T->bool)) ((:real^Ng):(real^Ng->bool)) (n:num) (i:num) (j:num) (z:real^Ng) /\
    (!k:num. sum (1..dimindex(:Ng)) (\k. (z:real^Ng)$k ) = &1) /\
    (!k l:num. z$k = sum (1..dimindex(:Ng)) 
            (\l. z$l * (column k ((group_trans_mat X p t a b r f up tp g c ngh ((:real^Q):(real^Q->bool)) ((:real^T):(real^T->bool)) ((:real^Ng):(real^Ng->bool)) n i j):real^Ng^Ng)$l)))
    ==> z = (lambda i. if i < dimindex(:Ng) then &0 else &1):real^Ng`,
REWRITE_TAC[stationary_eq] THEN
REPEAT STRIP_TAC THEN
POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
SIMP_TAC[GSYM IMP_CONJ] THEN
ASM_MESON_TAC[]
);;

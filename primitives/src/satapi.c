#include "satapi.h"


/******************************************************************************
 * We explain here the functions you need to implement
 *
 * Rules:
 * --You cannot change any parts of the function signatures
 * --You can/should define auxiliary functions to help implementation
 * --You can implement the functions in different files if you wish
 * --That is, you do not need to put everything in a single file
 * --You should carefully read the descriptions and must follow each requirement
 ******************************************************************************/


/******************************************************************************
 * Given a variable index i, you should return the corresponding variable
 * structure (notice you must return a pointer to the structure)
 *
 * Note variable indices range from 1 to n where n is the number of variables
 ******************************************************************************/
Var* index2varp(unsigned long i, SatState* sat_state) {
    return sat_state->variables[i - 1];
}


/******************************************************************************
 * Given a variable var, you should return
 * --its positive literal (pos_literal) 
 * --its negative literal (neg_literal) 
 *
 *
 * Given a literal lit, set_literal(lit) should return 
 * --1 if lit is set in the current setting
 * --0 if lit is free 
 *
 * Note a literal is set either by a decision or implication
 * Do not forget to update the status of literals when you run unit resolution
 ******************************************************************************/
Lit* pos_literal(Var* var) {
    if (var)
        return var->pos_literal;
    else {
        printf("Var is NULL\n");
        return NULL;
    }
}

Lit* neg_literal(Var* var) {
    if (var)
        return var->neg_literal;
    else {
        printf("Var is NULL\n");
        return NULL;
    }
}

BOOLEAN set_literal(Lit* lit) {
    if (lit)
        return lit->decision_level != 1;
    else {
        printf("Lit is NULL\n");
        return 0;
    }
}

/******************************************************************************
 * Given a clause index i, you should return the corresponding clause 
 * structure (notice you must return a pointer to the structure)
 *
 * Note clause indices range from 1 to m where m is the number of clauses 
 ******************************************************************************/
Clause* index2clausep(unsigned long i, SatState* sat_state) {
    ClauseNode* cur;
    if (i <= sat_state->m) cur = sat_state->CNF_clauses;
    else {
        cur = sat_state->learned_clauses;
        i -= sat_state->m;
    }
    while (i > 1) {
        cur = cur->next;
        --i;
    }
    return cur->clause;
}
 

/******************************************************************************
 * Given a clause, you should return 
 * --1 if the clause is subsumed in the current setting
 * --0 otherwise
 *
 * Note a clause is subsumed if at least one of its literals is implied
 * Do not forget to update the status of clauses when you run unit resolution
 ******************************************************************************/
BOOLEAN subsumed_clause(Clause* clause) {
    return clause->is_subsumed;
}


/******************************************************************************
 * A SatState should keep track of pretty much everything you will need to
 * condition/uncondition, perform unit resolution, and do clause learning
 *
 * Given a string cnf_fname, which is a file name of the input CNF, you should
 * construct a SatState
 *
 * This construction will depend on how you define a SatState 
 * Still, you should at least do the following:
 * --read a CNF (in DIMACS format) from the file
 * --initialize variables (n of them)
 * --initialize literals  (2n of them)
 *
 * Once a SatState is constructed, all of the functions that work on a SatState
 * should be ready to use
 *
 * You should also write a function that frees the memory allocated by a
 * SatState (free_sat_state)
 ******************************************************************************/

char* read_next_number(char* p, long* num) {
    long sign = 1;
    *num = 0;
    while (*p && !(*p >= '0' && *p <= '9') && *p != '-') ++p;
    if (*p == '-') {
        sign = -1;
        ++p;
    }
    while (*p >= '0' && *p <= '9') {
        *num = *num * 10 + (*p - '0');
        ++p;
    }
    *num = *num * sign;
    return p;
}

void print_state(SatState* state) {
    printf("# of variables: %lu\n", state->n);
    for(int i = 0; i < state->n; ++i)
        printf("%lu\n", state->variables[i]->index);
    printf("# of input clauses: %lu\n", state->m);
    ClauseNode* node = state->CNF_clauses;
    while (node != NULL) {
        LitNode* literals = node->clause->literals;
        while (literals != NULL) {
            printf("%ld ", literals->literal->index);
            literals = literals->prev;
        }
        printf("\n");
        node = node->prev;
    }
    printf("end\n");
}

SatState* construct_sat_state(char* cnf_fname) {
    FILE *fp = fopen(cnf_fname, "r");
    if (fp == NULL) {
        printf("Error: file %s cannot be open", cnf_fname);
        return NULL;
    }
    SatState* state = malloc(sizeof(SatState));
    char* line = (char*)malloc(sizeof(char) * (128 + 5));
    char* ptr = line;
    while (fgets(line, 128, fp) != NULL) {
        if (line[0] != 'p') continue;
        else {
            long tmp;
            line = read_next_number(line, &tmp);
            state->n = (unsigned long)tmp;
            line = read_next_number(line, &tmp);
            state->m = (unsigned long)tmp;
            // initialize n variables and literals
            state->variables = malloc(sizeof(Var*) * state->n);
            for(int i = 0; i < state->n; ++i) {
                Var* var = Var_new((unsigned long)i + 1);
                state->variables[i] = var;
            }
            state->CNF_clauses = NULL;
            state->learned_clauses = NULL;
            state->decided_literals = NULL;
            state->implied_literals = NULL;
            state->asserted_clause = NULL;
            for(int i = 1; i <= state->m; ++i) {
                ClauseNode* tail = state->CNF_clauses;
                LitNode* literals = NULL;
                line = ptr; // restore start position of buffer
                fgets(line, 128, fp);
                while (1) {
                    line = read_next_number(line, &tmp);
                    if (tmp == 0) break;
                    Lit* lit = NULL;
                    if (tmp > 0)
                        lit = pos_literal(index2varp(tmp, state));
                    else
                        lit = neg_literal(index2varp(-tmp, state));
                    LitNode* t = literals;
                    literals = LitNode_new(lit, t, NULL);
                    if (t != NULL)
                        t->next = literals;
                }
                Clause* clause = Clause_new(i, literals);
                state->CNF_clauses = ClauseNode_new(clause, tail, NULL);
                if (tail != NULL)
                    tail->next = state->CNF_clauses;
            }
            break; //while
        }
        line = ptr; // restore start position of buffer
    }
    free(ptr);
    fclose(fp);
    state->current_level = 1;
    //print_state(state);
    return state;
}

void free_sat_state(SatState* sat_state) {
    for(int i = 0; i < sat_state->n; ++i) {
        Var* var = index2varp(i + 1, sat_state);
        Var_delete(var);
    }
    free(sat_state->variables);
    ClauseNode* tail = sat_state->CNF_clauses;
    while (tail != NULL) {
        ClauseNode* del = tail;
        tail = tail->prev;
        ClauseNode_delete(del);
    }
    tail = sat_state->learned_clauses;
    while (tail != NULL) {
        ClauseNode* del = tail;
        tail = tail->prev;
        ClauseNode_delete(del);
    }
    LitNode* literals = sat_state->decided_literals;
    while (literals != NULL) {
        LitNode* del = literals;
        literals = literals->prev;
        LitNode_delete(del);
    }
    literals = sat_state->implied_literals;
    while (literals != NULL) {
        LitNode* del = literals;
        literals = literals->prev;
        LitNode_delete(del);
    }
    Clause_delete(sat_state->asserted_clause);
}


/******************************************************************************
 * Given a SatState, which should contain data related to the current setting
 * (i.e., decided literals, asserted literals, subsumed clauses, decision
 * level, etc.), this function should perform unit resolution at the current
 * decision level 
 *
 * It returns 1 if succeeds, 0 otherwise (after constructing an asserting
 * clause)
 *
 * There are three possible places where you should perform unit resolution: 
 * (1) after deciding on a new literal (i.e., decide_literal(SatState*)) 
 * (2) after adding an asserting clause (i.e., add_asserting_clause(SatState*)) 
 * (3) neither the above, which would imply literals appearing in unit clauses
 *
 * (3) would typically happen only once and before the other two cases 
 * It may be useful to distinguish between the above three cases
 * 
 * Note if the current decision level is L, then the literals implied by unit
 * resolution must have decision level L
 *
 * This implies that there must be a start level S, which will be the level
 * where the decision sequence would be empty
 *
 * We require you to choose S as 1, then literals implied by (3) would have 1 as
 * their decision level (this level will also be the assertion level of unit
 * clauses)
 *
 * Yet, the first decided literal must have 2 as its decision level
 ******************************************************************************/
BOOLEAN unit_resolution(SatState* sat_state) {

  // ... TO DO ..
 
  return 0; // dummy value
}


/******************************************************************************
 * This function should simply undo all set literals at the current decision
 * level
 ******************************************************************************/
void undo_unit_resolution(SatState* sat_state) {
    LitNode* cur = sat_state->implied_literals;
    while (cur != NULL) {
        Lit* lit = cur->literal;
        if (lit->decision_level == sat_state->current_level) {
            lit->decision_level = 1;
            LitNode* next = cur->next;
            LitNode* prev = cur->prev;
            if (prev != NULL) prev->next = next;
            if (next != NULL) next->prev = prev;
            LitNode_delete(cur);
            cur = prev;
        } else {
            cur = cur->prev;
        }
    }
}


/******************************************************************************
 * This function should set literal lit to true and then perform unit resolution
 * It returns 1 if unit resolution succeeds, 0 otherwise
 *
 * Note if the current decision level is L in the beginning of the call, it
 * should be updated to L+1 so that the decision level of lit and all other
 * literals implied by unit resolution is L+1
 ******************************************************************************/
BOOLEAN decide_literal(Lit* lit, SatState* sat_state) {
    lit->decision_level = sat_state->current_level;
    LitNode* node = LitNode_new(lit, sat_state->decided_literals, NULL);
    sat_state->decided_literals->next = node;
    sat_state->decided_literals = node;
    return unit_resolution(sat_state);
}


/******************************************************************************
 * This function should undo all set literals at the current decision level (you
 * can in fact call undo_unit_resolution(SatState*)) 
 *
 * Note if the current decision level is L in the beginning of the call, it
 * should be updated to L-1 before the call ends
 ******************************************************************************/
void undo_decide_literal(SatState* sat_state) {
    LitNode* cur = sat_state->decided_literals;
    sat_state->decided_literals = cur->prev;
    if (sat_state->decided_literals != NULL)
        sat_state->decided_literals->next = NULL;
    LitNode_delete(cur);
    undo_unit_resolution(sat_state);
    --sat_state->current_level;
}


/******************************************************************************
 * This function must be called after a contradiction has been found (by unit
 * resolution), an asserting clause constructed, and backtracking took place to
 * the assertion level (i.e., the current decision level is the same as the
 * assertion level of the asserting clause)
 *
 * This function should add the asserting clause into the set of learned clauses
 * (so that unit resolution from there on would also take into account the
 * asserting clause), and then perform unit resolution 
 *
 * It returns 1 if unit resolution succeeds, which means the conflict is
 * cleared, and 0 otherwise (that is, we have a new asserting clause with a new
 * assertion level)
 *
 * Note since the learned clause is asserting and we are at the assertion level
 * of the clause, it will become a unit clause under the current setting 
 *
 * Also, if the learned clause itself is a unit clause, its assertion level must
 * be the same as the start level S, which is 1 (i.e., the level in
 * which no decision is made) 
 ******************************************************************************/
BOOLEAN add_asserting_clause(SatState* sat_state) {
    ClauseNode* cur = ClauseNode_new(sat_state->asserted_clause,
                      sat_state->learned_clauses,
                      NULL);
    if (sat_state->learned_clauses != NULL)
        sat_state->learned_clauses->next = cur;
    sat_state->learned_clauses = cur;
    if (unit_resolution(sat_state)) {
        sat_state->asserted_clause = NULL;
        return 1;
    } else {
        return 0;
    }
}


/******************************************************************************
 * This function can be called after a contradiction has been found (by unit
 * resolution), an asserting clause constructed, and the conflict is not cleared
 * yet (that is, conflict_exists(SatState*) must return 1 at the time of call)
 *
 * It returns 1 if the current decision level is the same as the assertion level
 * of the asserting clause, 0 otherwise
 ******************************************************************************/
BOOLEAN at_assertion_level(SatState* sat_state) {
    return sat_state->asserted_clause->assertion_level == sat_state->current_level;
}


/******************************************************************************
 * It returns 1 if the current decision level is the same as the start level,
 * which is 1 (i.e., the level in which no decision is made), 0 otherwise
 ******************************************************************************/
BOOLEAN at_start_level(SatState* sat_state) {
    return sat_state->current_level == 1;
}


/******************************************************************************
 * It returns 1 if there is a conflict in the current setting, 0 otherwise
 *
 * --Initially there is no conflict
 * --If unit resolution finds a contradiction, then we have a conflict
 * --A conflict is cleared when we backtrack to the assertion level, add the
 * asserting clause into the set of learned clauses, and successfully perform
 * unit resolution (i.e., the call add_asserting_clause(SatState*) returns 1)
 ******************************************************************************/
BOOLEAN conflict_exists(SatState* sat_state) {
    return sat_state->asserted_clause != NULL;
}

/******************************************************************************
 * end
 ******************************************************************************/

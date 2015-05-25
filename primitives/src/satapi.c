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
 * Implement new and delete functions for the data structures
 ******************************************************************************/

Lit* Lit_new(signed long id) {
    Lit* literal = malloc(sizeof(Lit));
    literal->index = id;
    literal->decision_level = 0;
    literal->impled_by = NULL;
    literal->num_implied_by = 0;
    return literal;
}

void Lit_delete(Lit* lit) {
    if (lit) {
        if (lit->impled_by) free(lit->impled_by);
        free(lit);
    }
}

LitNode* LitNode_new(Lit* literal, LitNode* prev, LitNode* next) {
    LitNode* node = malloc(sizeof(LitNode));
    node->literal = literal;
    node->prev = prev;
    node->next = next;
    return node;
}

void LitNode_delete(LitNode* node) {
    if (node)
        free(node);
}

Var* Var_new(unsigned long id) {
    Var* var = malloc(sizeof(Var));
    var->index = id;
    var->pos_literal = Lit_new(id);
    var->neg_literal = Lit_new((signed long)id * -1);
    return var;
}

void Var_delete(Var* var) {
    if (var) {
        Lit_delete(var->pos_literal);
        Lit_delete(var->neg_literal);
        free(var);
    }
}

Clause* Clause_new(unsigned long id, LitNode* literals, unsigned long num_lits) {
    Clause* clause = malloc(sizeof(Clause));
    clause->index = id;
    clause->literals = literals;
    clause->is_subsumed = 0;
    clause->assertion_level = 1;
    clause->num_literals = num_lits;
    return clause;
}

void Clause_delete(Clause* clause) {
    if (clause) {
        LitNode* tail = clause->literals;
        while (tail != NULL) {
            LitNode* del = tail;
            tail = tail->prev;
            LitNode_delete(del);
        }
        free(clause);
    }
}

ClauseNode* ClauseNode_new(Clause* clause, ClauseNode* prev, ClauseNode* next) {
    ClauseNode* node = malloc(sizeof(ClauseNode));
    node->clause = clause;
    node->prev = prev;
    node->next = next;
    return node;
}

void ClauseNode_delete(ClauseNode* node) {
    if (node) {
        Clause_delete(node->clause);
        free(node);
    }
}

DAGNode* DAGNode_new(Lit* literal, DAGNode** from) {
    DAGNode* node = malloc(sizeof(DAGNode));
    node->literal = literal;
    node->from = from;
    return node;
}

void DAGNode_delete(DAGNode* node) {
    if (node) {
        if (node->from) free(node->from);
        free(node);
    }
}

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
        return lit->decision_level != 0;
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
        cur = cur->prev;
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
            state->n_clauses = state->m;
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
                int num_lits = 0;
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
                    num_lits ++;
                }
                Clause* clause = Clause_new(i, literals, num_lits);
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
        //printf("deleting: %ld\n",del->literal->index);
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
    unsigned long n_unset_lit = 0;
    unsigned long n_false_lit = 0;
    unsigned long n_total_lit = 0;
    int conflict = 0;
    Clause * conflict_clause = NULL;
    Lit * unset_lit = NULL;
    // Construct graph
    DAGNode ** lit_GNode_map = malloc(sizeof(DAGNode*) * (2*sat_state->n));
    for (int i = 0; i < 2*sat_state->n; i ++) lit_GNode_map[i] = DAGNode_new(NULL, NULL);
    LitNode * decided_lits = sat_state->decided_literals;
    while (decided_lits != NULL) {
        lit_GNode_map[decided_lits->literal->index+sat_state->n]->literal = decided_lits->literal;
        decided_lits = decided_lits->prev;
    }
    LitNode * implied_lits = sat_state->implied_literals;
    while (implied_lits != NULL) {
        lit_GNode_map[implied_lits->literal->index+sat_state->n]->literal = implied_lits->literal;
        if (implied_lits->literal->impled_by != NULL) {
            DAGNode ** dnode_array = malloc(sizeof(DAGNode*) * implied_lits->literal->num_implied_by);
            for (unsigned long i = 0; i < implied_lits->literal->num_implied_by; i ++) {
                dnode_array[i] = lit_GNode_map[implied_lits->literal->impled_by[i]->index+sat_state->n];
            }
            lit_GNode_map[implied_lits->literal->index+sat_state->n]->from = dnode_array;
        }
        implied_lits = implied_lits->prev;
    }
    for (unsigned long i = 1; i <= sat_state->n_clauses; i ++) {
        Clause* clause = index2clausep(i, sat_state);
        if (subsumed_clause(clause)) continue;
        n_unset_lit = 0;
        n_false_lit = 0;
        n_total_lit = 0;
        LitNode * lits = clause->literals;
        while (lits != NULL) {
            Lit* comp_lit = NULL;
            if (lits->literal->index < 0)
                comp_lit = pos_literal(index2varp(-lits->literal->index, sat_state));
            else
                comp_lit = neg_literal(index2varp(lits->literal->index, sat_state));
            if (set_literal(lits->literal)) {
                // A TRUE has been found, no need to continue on this clause
                clause->is_subsumed = 1;
                break;
            }
            else if (set_literal(comp_lit)) {
                // A FALSE has been found, continue
                n_false_lit ++;
            } else {
                // Lit has not been implied
                n_unset_lit ++;
                unset_lit = lits->literal;
            }
            lits = lits->prev;
            n_total_lit ++;
        }
        if (n_unset_lit == 1 && lits == NULL) {
            // Unit resolution implied unset_lit
            // WARNING: if decision_level is set 1 as default, then there would be problem
            // in the next sentence. So Song suggest set default decision_level to 0
            unset_lit->decision_level = sat_state->current_level;
            // Set implied_by && construct graph
            if (clause->num_literals != 1) {
                Lit ** implied_literals_array = malloc(sizeof(Lit *) * (clause->num_literals-1));
                int temp = 0;
                LitNode * lits = clause->literals;
                DAGNode ** dnode_array = malloc(sizeof(DAGNode*) * (clause->num_literals-1));
                while (lits != NULL) {
                    if (lits->literal == unset_lit) {
                        lits = lits->prev;
                        continue;
                    }
                    implied_literals_array[temp] = lits->literal;
                    dnode_array[temp] = lit_GNode_map[lits->literal->index+sat_state->n];
                    lits = lits->prev;
                    temp ++;
                }
                lit_GNode_map[unset_lit->index+sat_state->n]->from = dnode_array;
                unset_lit->impled_by = implied_literals_array;
                unset_lit->num_implied_by = clause->num_literals-1;
            }
            LitNode * node = LitNode_new(unset_lit, sat_state->implied_literals, NULL);
            if (sat_state->implied_literals != NULL) {
                sat_state->implied_literals->next = node;
            }
            sat_state->implied_literals = node;
            printf("implied_literals: %ld \n",node->literal->index);
            // To start over unit resolution
            i = 0;
        }
        if (lits == NULL && n_total_lit == n_false_lit) {
            // Unit resolution found conflict
            // Might need to save some variables here for finding assertion clause
            conflict_clause = clause;
            conflict = 1;
            break;
        }
    }
    if (conflict) {
        Clause* asserted_clause = NULL;
        LitNode * literals = conflict_clause->literals;
        while (literals != NULL) {
            DAGNode * dnode = lit_GNode_map[literals->literal->index+sat_state->n];
            printf("%ld\n",dnode->literal->index);
            literals = literals->prev;
        }
        sat_state->asserted_clause = asserted_clause;
        //return add_asserting_clause(sat_state);
        printf("contradiction found\n");
        for (unsigned long i = 0; i < 2*sat_state->n; i ++) DAGNode_delete(lit_GNode_map[i]);
        return 0;
    }
    for (unsigned long i = 0; i < 2*sat_state->n; i ++) DAGNode_delete(lit_GNode_map[i]);
    return 1;
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
            lit->decision_level = 0;
            lit->num_implied_by = 0;
            free(lit->impled_by);
            lit->impled_by = NULL;
            LitNode* next = cur->next;
            LitNode* prev = cur->prev;
            if (prev != NULL) prev->next = next;
            if (next != NULL) next->prev = prev;
            sat_state->implied_literals = prev;
            LitNode_delete(cur);
            cur = prev;
        } else {
            cur = cur->prev;
        }
    }
    // Reset all subsumed clause
    // May not be efficient
    for (unsigned long i = 1; i <= sat_state->n_clauses; i ++) {
        Clause* clause = index2clausep(i, sat_state);
        clause->is_subsumed = 0;
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
    ++sat_state->current_level;
    lit->decision_level = sat_state->current_level;
    LitNode* node = LitNode_new(lit, sat_state->decided_literals, NULL);
    if (sat_state->decided_literals != NULL)
        sat_state->decided_literals->next = node;
    sat_state->decided_literals = node;
    printf("literal %ld decided\n",node->literal->index);
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
    sat_state->n_clauses++;
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

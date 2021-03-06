#include "sat_api.h"

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
 * Variables
 ******************************************************************************/

Var* Var_new(c2dSize id) {
    Var* var = malloc(sizeof(Var));
    var->index = id;
    var->clauses = NULL;
    var->n_clauses = 0;
    var->clauses_buf_len = 0;
    var->mark = 0;
    return var;
}

void Var_delete(Var* var) {
    if (var) {
        if (var->clauses) free(var->clauses);
        free(var);
    }
}

//returns a variable structure for the corresponding index
Var* sat_index2var(c2dSize index, const SatState* sat_state) {
    return sat_state->variables[index - 1];
}

//returns the index of a variable
c2dSize sat_var_index(const Var* var) {
    return var->index;
}

//returns the variable of a literal
Var* sat_literal_var(const Lit* lit) {
    return lit->var;
}

//returns 1 if the variable is instantiated, 0 otherwise
//a variable is instantiated either by decision or implication (by unit resolution)
BOOLEAN sat_instantiated_var(const Var* var) {
    return sat_implied_literal(var->pos_literal) |
           sat_implied_literal(var->neg_literal);
}

//returns 1 if all the clauses mentioning the variable are subsumed, 0 otherwise
BOOLEAN sat_irrelevant_var(const Var* var) {
    c2dSize n = sat_var_occurences(var);
    for(c2dSize i = 0; i < n; ++i)
        if (!sat_subsumed_clause(sat_clause_of_var(i, var)))
            return 0;
    return 1;
}

//returns the number of variables in the cnf of sat state
c2dSize sat_var_count(const SatState* sat_state) {
    return sat_state->n;
}

//returns the number of clauses mentioning a variable
//a variable is mentioned by a clause if one of its literals appears in the clause
c2dSize sat_var_occurences(const Var* var) {
    return var->n_clauses;
}

//returns the index^th clause that mentions a variable
//index starts from 0, and is less than the number of clauses mentioning the variable
//this cannot be called on a variable that is not mentioned by any clause
Clause* sat_clause_of_var(c2dSize index, const Var* var) {
    return var->clauses[index];
}

/******************************************************************************
 * Literals 
 ******************************************************************************/

Lit* Lit_new(c2dLiteral id) {
    Lit* literal = malloc(sizeof(Lit));
    literal->index = id;
    literal->decision_level = 0;
    literal->implied_by = NULL;
    literal->n_implied_by = 0;
    literal->clauses = NULL;
    literal->n_clauses = 0;
    literal->clauses_buf_len = 0;
    return literal;
}

void Lit_delete(Lit* lit) {
    if (lit) {
        if (lit->implied_by) free(lit->implied_by);
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
    if (node) {
        free(node);
    }
}

//returns a literal structure for the corresponding index
Lit* sat_index2literal(c2dLiteral index, const SatState* sat_state) {
    if (index > 0) {
        return sat_state->pos_literals[index - 1];
    } else {
        return sat_state->neg_literals[-index - 1];
    }
}

//returns the index of a literal
c2dLiteral sat_literal_index(const Lit* lit) {
    return lit->index;
}

//returns the positive literal of a variable
Lit* sat_pos_literal(const Var* var) {
    return var->pos_literal;
}

//returns the negative literal of a variable
Lit* sat_neg_literal(const Var* var) {
    return var->neg_literal;
}

//returns 1 if the literal is implied, 0 otherwise
//a literal is implied by deciding its variable, or by inference using unit resolution
BOOLEAN sat_implied_literal(const Lit* lit) {
    return lit->decision_level > 0;
}

void modify_n_false(Lit* lit, SatState* sat_state, c2dLiteral x) {
    Lit* comp_lit = sat_index2literal(-sat_literal_index(lit), 
        sat_state);
    for(c2dSize i = 0; i < comp_lit->n_clauses; ++i)
        comp_lit->clauses[i]->n_false += x;
}

//sets the literal to true, and then runs unit resolution
//returns a learned clause if unit resolution detected a contradiction, NULL otherwise
//
//if the current decision level is L in the beginning of the call, it should be updated 
//to L+1 so that the decision level of lit and all other literals implied by unit resolution is L+1
Clause* sat_decide_literal(Lit* lit, SatState* sat_state) {
    ++sat_state->current_level;
    lit->decision_level = sat_state->current_level;
    LitNode* node = LitNode_new(lit, sat_state->decided_literals, NULL);
    if (sat_state->decided_literals != NULL)
        sat_state->decided_literals->next = node;
    sat_state->decided_literals = node;

    for(c2dSize i = 0; i < lit->n_clauses; ++i)
        if (lit->clauses[i]->subsumed_level == 0)
            lit->clauses[i]->subsumed_level = sat_state->current_level;
    modify_n_false(lit, sat_state, 1);

    //printf("literal %ld decided at level %ld\n",node->literal->index, sat_state->current_level);
    sat_state->from_decision = 1;
    if (sat_unit_resolution(sat_state)) {
        sat_state->asserted_clause = NULL;
        return NULL;
    } else {
        return sat_state->asserted_clause;
    }
}

//undoes the last literal decision and the corresponding implications obtained by unit resolution
//
//if the current decision level is L in the beginning of the call, it should be updated 
//to L-1 before the call ends
void sat_undo_decide_literal(SatState* sat_state) {
    LitNode* cur = sat_state->decided_literals;
    sat_state->decided_literals = cur->prev;
   
    // clear all the subsumed clause
    // this is incorrect? - Sheng
    for (c2dSize i = 0; i < cur->literal->n_clauses; i ++) {
        Clause* clause = cur->literal->clauses[i];
        if (clause->subsumed_level == sat_state->current_level)
            clause->subsumed_level = 0;
    }
    modify_n_false(cur->literal, sat_state, -1);
    
    cur->literal->decision_level = 0;
    if (sat_state->decided_literals != NULL)
        sat_state->decided_literals->next = NULL;
    LitNode_delete(cur);
    //printf("literal %ld undecided at level %ld\n",cur->literal->index, sat_state->current_level);
    sat_undo_unit_resolution(sat_state);
    --sat_state->current_level;
}

void imply_literal(Lit* unset_lit, Clause* clause, SatState* sat_state) {
    // set implied literal
    unset_lit->decision_level = sat_state->current_level;
    // if not unit clause
    if (sat_clause_size(clause) != 1) {
        Lit** implied_by_array = malloc(sizeof(Lit*) * 
                (sat_clause_size(clause) - 1));
        c2dSize temp = 0;
        Lit** lits = sat_clause_literals(clause);
        for(c2dSize i = 0; i < sat_clause_size(clause); ++i) {
            if (lits[i] == unset_lit) continue;
            implied_by_array[temp++] = 
                sat_index2literal(-sat_literal_index(lits[i]),sat_state);
        }
        unset_lit->implied_by = implied_by_array;
        unset_lit->n_implied_by = sat_clause_size(clause) - 1;
    }
    LitNode * lnode = LitNode_new(unset_lit, sat_state->implied_literals, 
        NULL);
    if (sat_state->implied_literals != NULL) {
        sat_state->implied_literals->next = lnode;
    }
    sat_state->implied_literals = lnode;
    //printf("literal %ld implied\n", unset_lit->index);
    // recursively search
    for(c2dSize i = 0; i < unset_lit->n_clauses; ++i)
        if (unset_lit->clauses[i]->subsumed_level == 0)
            unset_lit->clauses[i]->subsumed_level = 
                sat_state->current_level;
    modify_n_false(unset_lit, sat_state, 1);
} 


/******************************************************************************
 * Clauses 
 ******************************************************************************/

Clause* Clause_new(c2dSize id, Lit** literals, c2dSize n_literals, c2dSize m) {
    Clause* clause = malloc(sizeof(Clause));
    clause->index = id;
    clause->literals = literals;
    clause->n_literals = n_literals;
    for(c2dSize i = 0; i < n_literals; ++i) {
        Var* var = sat_literal_var(literals[i]);
        // var
        if (id <= m) {
            if (var->clauses_buf_len == 0) {
                var->clauses_buf_len = 1;
                var->n_clauses = 1;
                var->clauses = malloc(sizeof(Clause*) * var->clauses_buf_len);
                var->clauses[0] = clause;
            } else if (var->n_clauses == var->clauses_buf_len) {
                var->clauses_buf_len *= 2;
                Clause** tmp = malloc(sizeof(Clause*) * var->clauses_buf_len);
                for(c2dSize i = 0; i < var->n_clauses; ++i)
                    tmp[i] = var->clauses[i];
                tmp[var->n_clauses] = clause;
                ++var->n_clauses;
                free(var->clauses);
                var->clauses = tmp;
            } else {
                var->clauses[var->n_clauses] = clause;
                ++var->n_clauses;
            }
        }
        // literal
        Lit* lit = literals[i];
        if (lit->clauses_buf_len == 0) {
            lit->clauses_buf_len = 1;
            lit->n_clauses = 1;
            lit->clauses = malloc(sizeof(Clause*) * lit->clauses_buf_len);
            lit->clauses[0] = clause;
        } else if (lit->n_clauses == lit->clauses_buf_len) {
            lit->clauses_buf_len *= 2;
            Clause** tmp = malloc(sizeof(Clause*) * lit->clauses_buf_len);
            for(c2dSize i = 0; i < lit->n_clauses; ++i)
                tmp[i] = lit->clauses[i];
            tmp[lit->n_clauses] = clause;
            ++lit->n_clauses;
            free(lit->clauses);
            lit->clauses = tmp;
        } else {
            lit->clauses[lit->n_clauses] = clause;
            ++lit->n_clauses;
        }
    }
    clause->subsumed_level = 0;
    clause->assertion_level = 1;
    clause->mark = 0;
    clause->n_false = 0;
    if (n_literals > 1) {
        clause->watch_lit1 = literals[0];
        clause->watch_lit2 = literals[1];
    } else {
        clause->watch_lit1 = NULL;
        clause->watch_lit2 = NULL;
    }
    for(c2dSize i = 0; i < n_literals; i++) {
        Lit* lit = literals[i];
        Lit* comp_lit;
        if (lit->index > 0)
            comp_lit = lit->var->neg_literal;
        else
            comp_lit = lit->var->pos_literal;
        if (sat_implied_literal(lit)) {
            if (clause->subsumed_level == 0 || 
                clause->subsumed_level > lit->decision_level)
                clause->subsumed_level = lit->decision_level;
        }
        if (sat_implied_literal(comp_lit))
            ++clause->n_false;
    }
    return clause;
}

void Clause_delete(Clause* clause) {
    if (clause) {
        if (clause->literals) free(clause->literals);
        free(clause);
    }
}

//returns a clause structure for the corresponding index
Clause* sat_index2clause(c2dSize index, const SatState* sat_state) {
    if (index <= sat_state->m) {
        return sat_state->CNF_clauses[index - 1];
    } else {
        return sat_state->learned_clauses[index - sat_state->m - 1];
    }
}

//returns the index of a clause
c2dSize sat_clause_index(const Clause* clause) {
    return clause->index;
}

//returns the literals of a clause
Lit** sat_clause_literals(const Clause* clause) {
    return clause->literals;
}

//returns the number of literals in a clause
c2dSize sat_clause_size(const Clause* clause) {
    return clause->n_literals;
}

//returns 1 if the clause is subsumed, 0 otherwise
BOOLEAN sat_subsumed_clause(const Clause* clause) {
    return clause->subsumed_level > 0;
}

//returns the number of clauses in the cnf of sat state
c2dSize sat_clause_count(const SatState* sat_state) {
    return sat_state->m;
}

//returns the number of learned clauses in a sat state (0 when the sat state is constructed)
c2dSize sat_learned_clause_count(const SatState* sat_state) {
    return sat_state->n_learned_clauses;
}

//adds clause to the set of learned clauses, and runs unit resolution
//returns a learned clause if unit resolution finds a contradiction, NULL otherwise
//
//this function is called on a clause returned by sat_decide_literal() or sat_assert_clause()
//moreover, it should be called only if sat_at_assertion_level() succeeds
Clause* sat_assert_clause(Clause* clause, SatState* sat_state) {
    if (sat_state->learned_clauses_buf_len == 0) {
        sat_state->learned_clauses_buf_len = 1;
        sat_state->n_learned_clauses = 1;
        sat_state->learned_clauses = malloc(sizeof(Clause*) * 
            sat_state->learned_clauses_buf_len);
        sat_state->learned_clauses[0] = clause;
    } else if (sat_state->n_learned_clauses == 
               sat_state->learned_clauses_buf_len) {
        sat_state->learned_clauses_buf_len *= 2;
        Clause** tmp = malloc(sizeof(Clause*) * 
            sat_state->learned_clauses_buf_len);
        for(c2dSize i = 0; i < sat_state->n_learned_clauses; ++i)
            tmp[i] = sat_state->learned_clauses[i];
        tmp[sat_state->n_learned_clauses] = clause;
        ++sat_state->n_learned_clauses;
        free(sat_state->learned_clauses);
        sat_state->learned_clauses = tmp;
    } else {
        sat_state->learned_clauses[sat_state->n_learned_clauses] = clause;
        ++sat_state->n_learned_clauses;
    }
    clause->index = sat_clause_count(sat_state) + 
                    sat_learned_clause_count(sat_state);
    if (sat_unit_resolution(sat_state)) {
        sat_state->asserted_clause = NULL;
        return NULL;
    } else {
        return sat_state->asserted_clause;
    }
}

/******************************************************************************
 * A SatState should keep track of pretty much everything you will need to
 * condition/uncondition variables, perform unit resolution, and do clause learning
 *
 * Given an input cnf file you should construct a SatState
 *
 * This construction will depend on how you define a SatState
 * Still, you should at least do the following:
 * --read a cnf (in DIMACS format, possible with weights) from the file
 * --initialize variables (n of them)
 * --initialize literals  (2n of them)
 * --initialize clauses   (m of them)
 *
 * Once a SatState is constructed, all of the functions that work on a SatState
 * should be ready to use
 *
 * You should also write a function that frees the memory allocated by a
 * SatState (sat_state_free)
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
    printf("# of input clauses: %lu\n", state->m);
    for(c2dSize i = 0; i < state->m; ++i) {
        for(c2dSize j = 0; j < state->CNF_clauses[i]->n_literals; ++j)
            printf("%ld ", state->CNF_clauses[i]->literals[j]->index);
        printf("\n");
    }
    printf("end\n");
}


//constructs a SatState from an input cnf file
SatState* sat_state_new(const char* file_name) {
    FILE *fp = fopen(file_name, "r");
    if (fp == NULL) {
        printf("Error: file %s cannot be open", file_name);
        return NULL;
    }
    SatState* state = malloc(sizeof(SatState));
    char* line = (char*)malloc(sizeof(char) * (BUF_LEN + 5));
    char* ptr = line;
    while (fgets(line, BUF_LEN, fp) != NULL) {
        if (line[0] != 'p') continue;
        else {
            c2dLiteral tmp;
            line = read_next_number(line, &tmp);
            state->n = (c2dSize)tmp;
            line = read_next_number(line, &tmp);
            state->m = (c2dSize)tmp;
            // initialize n variables and literals
            state->variables = malloc(sizeof(Var*) * state->n);
            state->pos_literals = malloc(sizeof(Lit*) * state->n);
            state->neg_literals = malloc(sizeof(Lit*) * state->n);
            for(c2dSize i = 1; i <= state->n; ++i) {
                state->variables[i - 1] = Var_new(i);
                state->pos_literals[i - 1] = Lit_new((c2dLiteral)i);
                state->neg_literals[i - 1] = Lit_new(-((c2dLiteral)i));
                state->variables[i - 1]->pos_literal = state->pos_literals[i - 1];
                state->variables[i - 1]->neg_literal = state->neg_literals[i - 1];
                state->pos_literals[i - 1]->var = state->variables[i - 1];
                state->neg_literals[i - 1]->var = state->variables[i - 1];
            }
            state->n_learned_clauses = 0;
            state->CNF_clauses = malloc(sizeof(Clause*) * state->m);
            state->learned_clauses_buf_len = 0;
            state->learned_clauses = NULL;
            state->decided_literals = NULL;
            state->implied_literals = NULL;
            state->asserted_clause = NULL;
            for(c2dSize i = 1; i <= state->m; ++i) {
                line = ptr; // restore start position of buffer
                fgets(line, BUF_LEN, fp);
                c2dSize n_literals = 0;
                while (1) {
                    line = read_next_number(line, &tmp);
                    if (tmp == 0) break;
                    ++n_literals;
                }
                if (n_literals == 0) {
                    --i;
                    continue;
                }
                Lit** literals = malloc(sizeof(Lit*) * n_literals);
                line = ptr;
                for(c2dSize j = 0; j < n_literals; ++j) {
                    line = read_next_number(line, &tmp);
                    Lit* lit = NULL;
                    if (tmp > 0)
                        lit = sat_pos_literal(sat_index2var(tmp, state));
                    else
                        lit = sat_neg_literal(sat_index2var(-tmp, state));
                    literals[j] = lit;
                }
                state->CNF_clauses[i - 1] = Clause_new(i, literals, 
                                                  n_literals, state->m);
            }
            break; //while
        }
        line = ptr; // restore start position of buffer
    }
    free(ptr);
    fclose(fp);
    state->current_level = 1;
    state->from_decision = 0;
    //print_state(state);
    return state;
}

//frees the SatState
void sat_state_free(SatState* sat_state) {
    for(c2dSize i = 0; i < sat_state->n; ++i) {
        Var_delete(sat_state->variables[i]);
        Lit_delete(sat_state->pos_literals[i]);
        Lit_delete(sat_state->neg_literals[i]);
    }
    free(sat_state->variables);
    free(sat_state->pos_literals);
    free(sat_state->neg_literals);
    for(c2dSize i = 0; i < sat_state->m; ++i) {
        Clause_delete(sat_state->CNF_clauses[i]);
    }
    free(sat_state->CNF_clauses);
    for(c2dSize i = 0; i < sat_state->n_learned_clauses; ++i) {
        Clause_delete(sat_state->learned_clauses[i]);
    }
    free(sat_state->learned_clauses);
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
}

/******************************************************************************
 * Given a SatState, which should contain data related to the current setting
 * (i.e., decided literals, subsumed clauses, decision level, etc.), this function 
 * should perform unit resolution at the current decision level 
 *
 * It returns 1 if succeeds, 0 otherwise (after constructing an asserting
 * clause)
 *
 * There are three possible places where you should perform unit resolution:
 * (1) after deciding on a new literal (i.e., in sat_decide_literal())
 * (2) after adding an asserting clause (i.e., in sat_assert_clause(...)) 
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

// uip 0 - unset, 1 - cannot reach, 2 - can reach, 3 - removed
BOOLEAN uip_backtrack(Lit* cur, c2dSize* uip, c2dSize n, Lit* decide) {
    if (uip[cur->index+n] == 3) return 0;
    else if (cur == decide) return 1;
    else if (uip[cur->index + n] == 2) return 1;
    else if (uip[cur->index + n] == 1) return 0;
    else {
        Lit ** implied_by = cur->implied_by;
        for (c2dSize i = 0; i < cur->n_implied_by; i ++) {
            uip[cur->index + n] = 
                uip_backtrack(implied_by[i], uip, n, decide) == 0 ? 1 : 2;
            if (uip[cur->index + n] == 2) return 1;
        }
        return 0;
    }
}

Lit * uip_find(Clause * clause, SatState * sat_state) {
    Lit ** bfs_queue = malloc(sizeof(Lit*) * (2 * sat_state->n + 1));
    BOOLEAN * checked = malloc(sizeof(BOOLEAN) * (2 * sat_state->n + 1));
    for (c2dSize i = 0; i <= sat_state->n * 2; i ++) checked[i] = 0;
    c2dSize front = 0;
    c2dSize back = 0;
    Lit ** lits = clause->literals;
    Lit * conflict_lit = Lit_new(0);
    conflict_lit->n_implied_by = clause->n_literals;
    Lit ** clits = malloc(sizeof(Lit*) * clause->n_literals);
    for (c2dSize i = 0; i < clause->n_literals; i ++) {
        clits[i] = sat_index2literal(-lits[i]->index, sat_state);
    }
    conflict_lit->implied_by = clits;
    bfs_queue[back++] = conflict_lit;
    c2dSize * uip = malloc(sizeof(c2dSize) * (sat_state->n * 2 + 1));
    while (front != back) {
        for (c2dSize i = 0; i <= sat_state->n * 2; i ++) {
            uip[i] = 0;
        }
        uip[bfs_queue[front]->index+sat_state->n] = 3;
        if (bfs_queue[front] != conflict_lit &&
            !uip_backtrack(conflict_lit, uip, sat_state->n, sat_state->decided_literals->literal)) {
            Lit * res = bfs_queue[front];
            free(bfs_queue);
            free(checked);
            Lit_delete(conflict_lit);
            free(uip);
            return res;
        }
        Lit ** lits = bfs_queue[front]->implied_by;
        for (c2dSize i = 0; i < bfs_queue[front]->n_implied_by; i ++) {
            if (checked[lits[i]->index+sat_state->n] == 0) {
                bfs_queue[back++] = lits[i];
                checked[lits[i]->index+sat_state->n] = 1;
            }
        }
        front ++;
    }
    free(bfs_queue);
    free(checked);
    Lit_delete(conflict_lit);
    free(uip);
    return NULL;
}

void backtrack(Lit* cur, Lit** marks, c2dSize highest_level, 
        BOOLEAN* visited, c2dSize n, Lit * first_uip) {
    if (visited[cur->index + n]) return;
    visited[cur->index + n] = 1;
    if (cur->decision_level < highest_level ||
       (cur->decision_level == highest_level && cur->implied_by == NULL) || 
        (cur == first_uip)) {
        c2dSize id = cur->index + n;
        marks[id] = cur;
    } else {
        for(c2dSize i = 0; i < cur->n_implied_by; ++i)
            backtrack(cur->implied_by[i], marks, highest_level, visited, n, first_uip);
    }
     
}

Clause* construct_asserted_clause(Clause* clause, SatState* sat_state) {
    c2dSize highest_level = sat_state->current_level;
    if (highest_level == 1) return NULL;
    Lit** marks = malloc(sizeof(Lit*) * (sat_state->n * 2 + 1));
    BOOLEAN* visited = malloc(sizeof(BOOLEAN) * (sat_state->n * 2 + 1));
    for(c2dSize i = 0; i <= sat_state->n * 2; ++i) {
        marks[i] = NULL;
        visited[i] = 0;
    }
    // first_uip shouldn't be NULL here
    Lit * first_uip = uip_find(clause, sat_state);
    //Lit* first_uip = NULL;
    for(c2dSize i = 0; i < clause->n_literals; ++i)
        backtrack(sat_index2literal(-clause->literals[i]->index, sat_state),
                  marks, highest_level, visited, sat_state->n, first_uip);
    c2dSize cnt = 0;
    for(c2dSize i = 0; i <= sat_state->n * 2; ++i)
        if (marks[i] != NULL)
            ++cnt;
    Lit** lits = malloc(sizeof(Lit*) * cnt);
    cnt = 0;
    c2dSize assertion_level = 1;
    for(c2dSize i = 0; i <= sat_state->n * 2; ++i)
        if (marks[i] != NULL) {
            lits[cnt] = sat_index2literal(-marks[i]->index, sat_state);
            ++cnt;
            if (marks[i]->decision_level < highest_level &&
                marks[i]->decision_level > assertion_level)
                assertion_level = marks[i]->decision_level;
        }
    Clause* res = Clause_new(sat_clause_count(sat_state) + 
        sat_learned_clause_count(sat_state) + 1, lits, cnt, sat_state->m);
    res->assertion_level = cnt == 1 ? 1 : assertion_level;
    free(marks);
    free(visited);
    return res;
    
}


Clause* unit_find_watches(Clause * clause, c2dSize index, SatState * sat_state) {
    Lit ** literals = clause->literals;
    c2dSize i = 0;
    for ( ; i < clause->n_literals; i ++) {
        if (!sat_implied_literal(sat_index2literal(-literals[i]->index, sat_state))
            && literals[i] != (index == 1 ? clause->watch_lit2 : clause->watch_lit1)) {
            if (index == 1) clause->watch_lit1 = literals[i];
            else clause->watch_lit2 = literals[i];
            break;
        }
    }
    if (i == clause->n_literals) {
        Lit* other_watched = index == 1 ? clause->watch_lit2 : clause->watch_lit1;
        if (sat_implied_literal(other_watched)) {
            clause->subsumed_level = sat_state->current_level;
            return NULL;
        } else if (sat_implied_literal(sat_index2literal(-other_watched->index, sat_state))) {
            return clause;
        } else {
            clause->subsumed_level = sat_state->current_level;
            imply_literal(other_watched, clause, sat_state);
            return unit_resolution_helper(other_watched, sat_state);
        }
    }
    return NULL;
}

Clause* unit_resolution_helper(Lit* cur, SatState* sat_state) {
    c2dSize n_unset_lit = 0;
    c2dSize n_false_lit = 0;
    Lit * unset_lit = NULL;
    Clause * conflict_clause = NULL;
    //cur = sat_index2literal(-cur->index, sat_state);
    for(c2dSize i = 0; i < cur->n_clauses; ++i) {
        Clause* clause = cur->clauses[i];
        if (sat_subsumed_clause(clause)) continue;
        /*if (clause->watch_lit1 == cur) {
            conflict_clause = unit_find_watches(clause, 1, sat_state);
            if (conflict_clause != NULL) return conflict_clause;
        } else if (clause->watch_lit2 == cur) {
            conflict_clause = unit_find_watches(clause, 2, sat_state);
            if (conflict_clause != NULL) return conflict_clause;
        }*/
        /*n_unset_lit = 0;
        n_false_lit = 0;
        Lit ** lits = sat_clause_literals(clause);
        for (c2dSize j = 0; j < sat_clause_size(clause); j ++) {
            Lit * lit = lits[j];
            Lit * comp_lit = sat_index2literal(-sat_literal_index(lit), sat_state);
            if (sat_implied_literal(lit)) {
                clause->subsumed_level = sat_state->current_level;
                break;
            } else if (sat_implied_literal(comp_lit)) {
                n_false_lit ++;
            } else {
                n_unset_lit ++;
                unset_lit = lit;
            }
        }
        if (clause->n_false != n_false_lit)
            printf("%ld %ld\n", n_false_lit, clause->n_false);*/
        n_false_lit = clause->n_false;
        n_unset_lit = sat_clause_size(clause) - n_false_lit;
        if (n_unset_lit == 1 && !sat_subsumed_clause(clause)) {
            Lit ** lits = sat_clause_literals(clause);
            for (c2dSize j = 0; j < sat_clause_size(clause); j ++) {
                Lit * lit = lits[j];
                Lit * comp_lit = sat_index2literal(-sat_literal_index(lit),
                                 sat_state);
                if (!sat_implied_literal(lit) && 
                    !sat_implied_literal(comp_lit)) {
                    unset_lit = lit;
                    break;
                }
            }
            imply_literal(unset_lit, clause, sat_state);
            conflict_clause = unit_resolution_helper(
                sat_index2literal(-sat_literal_index(unset_lit), sat_state),
                sat_state);
            if (conflict_clause != NULL) return conflict_clause;
        } else if (n_false_lit == sat_clause_size(clause) && !sat_subsumed_clause(clause)) {
            conflict_clause = clause;
            return conflict_clause;
        }
    }
    return NULL;
}

//applies unit resolution to the cnf of sat state
//returns 1 if unit resolution succeeds, 0 if it finds a contradiction
BOOLEAN sat_unit_resolution(SatState* sat_state) {
    //clock_t t = clock();
    Clause * conflict_clause = NULL;
    /*if (sat_state->asserted_clause != NULL) {
        Clause * clause = sat_state->asserted_clause;
        clause->watch_lit1 = NULL;
        clause->watch_lit2 = NULL;
        if (clause->n_literals == 1) {
            clause->subsumed_level = sat_state->current_level;
            imply_literal(clause->literals[0], clause, sat_state);
            conflict_clause = unit_resolution_helper(clause->literals[0], sat_state);
        } else {
            Lit ** literals = clause->literals;
            for (c2dSize i = 0; i < clause->n_literals; i ++) {
                if (!sat_implied_literal(literals[i])
                    && ! sat_implied_literal(sat_index2literal(-literals[i]->index, sat_state))) {
                    if (clause->watch_lit1 == NULL) {
                        clause->watch_lit1 = literals[i];
                    } else if (clause->watch_lit2 == NULL) {
                        clause->watch_lit2 = literals[i];
                        break;
                    }
                    else break;
                }
            }
            if (clause->watch_lit1 == NULL) conflict_clause = clause;
            else if (clause->watch_lit2 == NULL) {
                clause->watch_lit2 = clause->watch_lit1;
                clause->subsumed_level = sat_state->current_level;
                imply_literal(clause->watch_lit1, clause, sat_state);
                conflict_clause = unit_resolution_helper(clause->watch_lit1, sat_state);
            } else conflict_clause = NULL;
        }
        
    } else if (sat_state->current_level == 1) {
        for (c2dSize i = 1; i < sat_clause_count(sat_state); i ++) {
            Clause * clause = sat_index2clause(i, sat_state);
            if (clause->n_literals == 1) {
                clause->subsumed_level = sat_state->current_level;
                imply_literal(clause->literals[0], clause, sat_state);
                conflict_clause = unit_resolution_helper(clause->literals[0], sat_state);
                if (conflict_clause != NULL) {
                    break;
                }
            }
        }
    } else {
        conflict_clause = unit_resolution_helper(sat_state->decided_literals->literal, sat_state);
    }*/
    
    c2dSize n_unset_lit = 0;
    c2dSize n_false_lit = 0;
    Lit * unset_lit = NULL;
   
    if (sat_state->from_decision) {
        sat_state->from_decision = 0;
        Lit* unset_lit = sat_state->decided_literals->literal;
        conflict_clause = unit_resolution_helper(
            sat_index2literal(-sat_literal_index(unset_lit), sat_state),
            sat_state);
    } else {
        for (c2dSize i = 1; i <= sat_clause_count(sat_state) + sat_learned_clause_count(sat_state); ++i) {
            Clause * clause = sat_index2clause(i, sat_state);
            if (sat_subsumed_clause(clause)) continue;
            /*n_unset_lit = 0;
            n_false_lit = 0;
            Lit ** lits = sat_clause_literals(clause);
            for (c2dSize j = 0; j < sat_clause_size(clause); j ++) {
                Lit * lit = lits[j];
                Lit * comp_lit = sat_index2literal(-sat_literal_index(lit), sat_state);
                if (sat_implied_literal(lit)) {
                    clause->subsumed_level = sat_state->current_level;
                    break;
                } else if (sat_implied_literal(comp_lit)) {
                    n_false_lit ++;
                } else {
                    n_unset_lit ++;
                    unset_lit = lit;
                }
            }*/
            n_false_lit = clause->n_false;
            n_unset_lit = sat_clause_size(clause) - n_false_lit;
            if (n_unset_lit == 1 && !sat_subsumed_clause(clause)) {
                Lit ** lits = sat_clause_literals(clause);
                for (c2dSize j = 0; j < sat_clause_size(clause); j ++) {
                    Lit * lit = lits[j];
                    Lit * comp_lit = sat_index2literal(-sat_literal_index(lit), sat_state);
                    if (!sat_implied_literal(lit) && 
                        !sat_implied_literal(comp_lit)) {
                        unset_lit = lit;
                        break;
                    }
                }
                imply_literal(unset_lit, clause, sat_state);
                conflict_clause = unit_resolution_helper(
                    sat_index2literal(-sat_literal_index(unset_lit), sat_state),
                    sat_state);
                if (conflict_clause != NULL) {
                    break;
                }
            } else if (n_false_lit == sat_clause_size(clause) && !sat_subsumed_clause(clause)) {
                conflict_clause = clause;
                break;
            }
            
        }
        }
    //unit_resolution_timer += clock() - t;
    //printf("unit:%ld\n",unit_resolution_timer);
    if (conflict_clause != NULL) {
        //t = clock();
        sat_state->asserted_clause = construct_asserted_clause(conflict_clause, sat_state);
    //backtrack_timer += clock() - t;
    //printf("backtrack:%ld\n",backtrack_timer);
        return 0;
    }
    
    return 1;
}

//undoes sat_unit_resolution(), leading to un-instantiating variables that have been instantiated
//after sat_unit_resolution()
void sat_undo_unit_resolution(SatState* sat_state) {
    LitNode* cur = sat_state->implied_literals;
    while (cur != NULL) {
        Lit* lit = cur->literal;
        if (lit->decision_level == sat_state->current_level) {
            lit->decision_level = 0;
            lit->n_implied_by = 0;
            if (lit->implied_by) free(lit->implied_by);
            lit->implied_by = NULL;
            
            // clear all the subsumed clause
            for (c2dSize i = 0; i < lit->n_clauses; i ++) {
                Clause* clause = lit->clauses[i];
                if (clause->subsumed_level == sat_state->current_level)
                    clause->subsumed_level = 0;
            }
            modify_n_false(lit, sat_state, -1);
            
            LitNode* next = cur->next;
            LitNode* prev = cur->prev;
            if (prev != NULL) prev->next = next;
            if (next != NULL) next->prev = prev;
            if (next == NULL) sat_state->implied_literals = prev;
            LitNode_delete(cur);
            cur = prev;
        } else {
            cur = cur->prev;
        }
    }
}

//returns 1 if the decision level of the sat state equals to the assertion level of clause,
//0 otherwise
//
//this function is called after sat_decide_literal() or sat_assert_clause() returns clause.
//it is used to decide whether the sat state is at the right decision level for adding clause.
BOOLEAN sat_at_assertion_level(const Clause* clause, const SatState* sat_state) {
    return clause->assertion_level == sat_state->current_level;
}

/******************************************************************************
 * The functions below are already implemented for you and MUST STAY AS IS
 ******************************************************************************/

//returns the weight of a literal (which is 1 for our purposes)
c2dWmc sat_literal_weight(const Lit* lit) {
  return 1;
}

//returns 1 if a variable is marked, 0 otherwise
BOOLEAN sat_marked_var(const Var* var) {
  return var->mark;
}

//marks a variable (which is not marked already)
void sat_mark_var(Var* var) {
  var->mark = 1;
}

//unmarks a variable (which is marked already)
void sat_unmark_var(Var* var) {
  var->mark = 0;
}

//returns 1 if a clause is marked, 0 otherwise
BOOLEAN sat_marked_clause(const Clause* clause) {
  return clause->mark;
}

//marks a clause (which is not marked already)
void sat_mark_clause(Clause* clause) {
  clause->mark = 1;
}
//unmarks a clause (which is marked already)
void sat_unmark_clause(Clause* clause) {
  clause->mark = 0;
}

/******************************************************************************
 * end
 ******************************************************************************/

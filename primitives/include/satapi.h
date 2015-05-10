#ifndef SATAPI_H_
#define SATAPI_H_

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/******************************************************************************
 * typedefs 
 ******************************************************************************/

typedef char BOOLEAN;


/******************************************************************************
 * Basic structures
 ******************************************************************************/

/******************************************************************************
 * Literals:
 * --You must represent literals using the following struct 
 * --Positive literals' indices range from 1 to n (n is the number of variables)
 * --Negative literals' indices range from -n to -1 (n is the number of variables)
 * --Index of a literal must be of type "signed long"
 ******************************************************************************/

typedef struct {
    signed long index;
    BOOLEAN is_set;
} Lit;

Lit* Lit_new(signed long id) {
    Lit* literal = malloc(sizeof(Lit));
    literal->index = id;
    literal->is_set = 0;
    return literal;
}

typedef struct LitNode {
    Lit* literal;
    struct LitNode* next;
    struct LitNode* prev;
} LitNode;

LitNode* LitNode_new(Lit* literal, LitNode* prev, LitNode* next) {
    LitNode* node = malloc(sizeof(LitNode));
    node->literal = literal;
    node->prev = prev;
    node->next = next;
    return node;
}


/******************************************************************************
 * Variables:
 * --You must represent variables using the following struct 
 * --Variable index must start at 1
 * --Index of a variable must be of type "unsigned long"
 ******************************************************************************/

typedef struct {
    unsigned long index;
    Lit* pos_literal;
    Lit* neg_literal;
} Var;

Var* Var_new(unsigned long id) {
    Var* var = malloc(sizeof(Var));
    var->index = id;
    var->pos_literal = Lit_new(id);
    var->pos_literal = Lit_new((signed long)id * -1);
    return var;
}

typedef struct VarNode {
    Var* var;
    struct VarNode* next;
    struct VarNode* prev;
} VarNode;

VarNode* VarNode_new(Var* var, VarNode* prev, VarNode* next) {
    VarNode* node = malloc(sizeof(VarNode));
    node->var = var;
    node->prev = prev;
    node->next = next;
    return node;
}

/******************************************************************************
 * Clauses: 
 * --You must represent clauses using the following struct 
 * --Clause index must start at 1
 * --Each clause must maintain a field to decide whether the clause is subsumed in
 * the current setting (i.e., if any literal of the clause is asserted)
 ******************************************************************************/

typedef struct {
    unsigned long index;
    VarNode* vars;
    BOOLEAN is_subsumed;
} Clause;

Clause* Clause_new(unsigned long id, VarNode* vars) {
    Clause* clause = malloc(sizeof(Clause));
    clause->index = id;
    clause->vars = vars;
    clause->is_subsumed = 0;
    return clause;
}

typedef struct ClauseNode {
    Clause* clause;
    struct ClauseNode* next;
    struct ClauseNode* prev;
} ClauseNode;

ClauseNode* ClauseNode_new(Clause* clause, ClauseNode* prev, ClauseNode* next) {
    ClauseNode* node = malloc(sizeof(ClauseNode));
    node->clause = clause;
    node->prev = prev;
    node->next = next;
    return node;
}

/******************************************************************************
 * SatState: 
 * --The following structure will keep track of the data needed to
 * condition/uncondition, perform unit resolution, and so on ...
 ******************************************************************************/

typedef struct {
    unsigned long n;    // number of variables
    unsigned long m;    // number of clauses
    Var** variables;
    ClauseNode* CNF_clauses;
    ClauseNode* learned_clauses;
    LitNode* implied_literals;
    Clause* asserted_clause;
} SatState;


/******************************************************************************
 * API: 
 * --Using the above structures you must implement the following functions 
 * --Detailed explanations of the functions can be found in satapi.c
 * --These functions are all you need for the knowledge compiler
 * --Note that most of the functions can be implemented in 1 line
 ******************************************************************************/

//Variables
Var* index2varp(unsigned long,SatState*);

//Literals
Lit* pos_literal(Var*);
Lit* neg_literal(Var*);
BOOLEAN set_literal(Lit*);

//Clauses
Clause* index2clausep(unsigned long,SatState*);
BOOLEAN subsumed_clause(Clause*);

//SatState
SatState* construct_sat_state(char*);
void free_sat_state(SatState*);
BOOLEAN unit_resolution(SatState*);
void undo_unit_resolution(SatState*);
BOOLEAN decide_literal(Lit*,SatState*);
void undo_decide_literal(SatState*);
BOOLEAN add_asserting_clause(SatState*);
BOOLEAN at_assertion_level(SatState*);
BOOLEAN at_start_level(SatState*);
BOOLEAN conflict_exists(SatState*);

#endif // SATAPI_H_

/******************************************************************************
 * end
 ******************************************************************************/

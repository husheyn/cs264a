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
    unsigned long decision_level;
} Lit;

Lit* Lit_new(signed long id);
void Lit_delete(Lit* lit);

typedef struct LitNode LitNode;
struct LitNode {
    Lit* literal;
    LitNode* next;
    LitNode* prev;
};

LitNode* LitNode_new(Lit* literal, LitNode* prev, LitNode* next);
// only delete the LitNode, does not touch the underlying literal
void LitNode_delete(LitNode* node);

typedef struct DAGNode DAGNode;
struct DAGNode {
    Lit* literal;
    DAGNode** from;
};

DAGNode* DAGNode_new(Lit* literal, DAGNode** from);
void DAGNode_delete(DAGNode* node);

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

Var* Var_new(unsigned long id);
// delete the variable and its corresponding literals
void Var_delete(Var* var);


/******************************************************************************
 * Clauses: 
 * --You must represent clauses using the following struct 
 * --Clause index must start at 1
 * --Each clause must maintain a field to decide whether the clause is subsumed in
 * the current setting (i.e., if any literal of the clause is asserted)
 ******************************************************************************/

typedef struct {
    unsigned long index;
    LitNode* literals;
    BOOLEAN is_subsumed;
    unsigned long assertion_level;
} Clause;

Clause* Clause_new(unsigned long id, LitNode* literals);
// delete the clause and the literal list inside it
void Clause_delete(Clause* clause);


typedef struct ClauseNode ClauseNode;
struct ClauseNode {
    Clause* clause;
    ClauseNode* next;
    ClauseNode* prev;
};

ClauseNode* ClauseNode_new(Clause* clause, ClauseNode* prev, ClauseNode* next);
// delete the ClauseNode and clause inside it
void ClauseNode_delete(ClauseNode* node);

/******************************************************************************
 * SatState: 
 * --The following structure will keep track of the data needed to
 * condition/uncondition, perform unit resolution, and so on ...
 ******************************************************************************/

typedef struct {
    unsigned long n;    // number of variables
    unsigned long m;    // number of input clauses
    // start level 1; first decided literal would have 2 
    // as its decision level
    unsigned long current_level; 
    unsigned long n_clauses;
    Var** variables;
    ClauseNode* CNF_clauses;
    ClauseNode* learned_clauses;
    LitNode* decided_literals;
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

/* 
 * Parser for modal formulae
*/

%error-verbose
 //%locations
%debug
%defines
%glr-parser
%expect 2
%pure-parser
%code requires {
#include "tree.h"
  
  extern tnode *root;
  extern tnode *create_tnode(int type, int id, tnode *left, tnode *right, formulalist *list);
  formulalist *tree_to_list(int type, tnode *left, tnode *right);
  
  char *getBoxName (char *);

  typedef struct axiom_list {
    int axiom;
    struct axiom_list *next;
  } axiom_list;

  typedef struct prop_list {
    char *prop;
    struct prop_list *next;
  } prop_list;

  void process_ordering(prop_list *props);
}


%{
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "prover.h"
#include "uthash.h"
#include "symbol_table.h"

  /* flex functions */

  extern int yylex () ;
  extern char *yytext;
  extern FILE *yyin;

  /* Max stack size for parsing */
  
#define YYMAXDEPTH 136854775807
    
  /* symbol table functions in symbol_table.c" */

#define MAX(X, Y) (((X) > (Y)) ? (X) : (Y))

  /* prototype for the error function */

  void yyerror (char const *s);
 
  /* global variables from tokenizer.l */

  extern int numtokens;
  extern int numlines;
  extern int numcolumns;

  /* global variables for parser.y */

  int numerrors = 0;  
  int numagents = 1;
  int numprops = 2; // 1 and -1 are reserved for CTRUE an CFALSE, 0 is reserved for CSTART
  int inputsize = 0;

  /* global variables for the prover */

  extern int configfile;

  extern prop_node *find_prop (int id);
  extern prop_node *create_p_node (char *name; int id;);
  extern agent_node *create_a_node (char *name; int id;);

  extern agent_node *insert_a_node (char *name);
  extern prop_node *insert_p_node (char *name);

  struct prop_node *propsname = NULL;
  struct prop_node *propsid = NULL;    /* important! initialize to NULL */
  struct agent_node *agentsname = NULL; 
  struct agent_node *agentsid = NULL;    
%}

%union{
  char *strValue;
  tnode *tnode;
  formulalist *formulalist;
  axiom_list *axiom_list;
  prop_list *prop_list;
}

%left TIFF 
%left TIMPLY 
%left TONLYIF 
%left TOR 
%left TAND
%right TNOT 
%right <strValue> TPOSSIBLE TNECESSARY
%right <strValue> TOBOX TODIA "modal operator delimiter (open)"
%left TCBOX TCDIA "modal operator delimiter (close)"

%token TIFF "double implication"
%token TIMPLY "implication"
%token TONLYIF "only if"
%token TOR "disjunction"
%token TAND "conjunction"
%token TNOT "negation"
%token TPOSSIBLE "diamond operator"
%token TNECESSARY "box operator"

%token <strValue> TNAME "identifier"
%token <strValue> TNUMBER "number"
%token <strValue> TSTART TTRUE TFALSE  "constant"

%token TSET "set option command"
%token TDOT "."
%token TCOMMA ","
%token TCLAUSES  "clauses"
%token TFORMULAS "formulas"
%token TSOS "sos"
%token TUSABLE "usable"
%token TEND "end of list"
%token TLPAREN "("
%token TRPAREN ")"

%type <strValue> modal_arg
%type <tnode> formula
%type <tnode> formulas
%type <tnode> clauses
%type <tnode> initial_clause
%type <tnode> literal_clause
%type <tnode> modal_clause
%type <tnode> disjunction_literals
%type <tnode> sets
%type <tnode> formulas_sets_tail
%type <tnode> clauses_sets_tail
%type <tnode> proposition
%type <tnode> literal

%type <axiom_list> axioms
%type <prop_list> propositions_list

%%

file : declarations sets
     {
       root = $2;
     }
     ;

declarations : // it can be empty
             | TSET TLPAREN option TRPAREN TDOT declarations
             | error TDOT declarations { numerrors++; }
             ;

option : TNAME
       {

	 free($1);

       }
       | TNAME TCOMMA TNUMBER
       {
	 free($1);
	 free($3);
       }
       | TNAME TCOMMA propositions_list
       {

       }
       | TNECESSARY modal_arg TCOMMA axioms
       {
       }
       | TNECESSARY TCOMMA axioms
       {
       }
       | error {numerrors++;}
       ;

axioms : {$$=NULL;}
       | TNAME
       {
       }
       | TNAME TCOMMA axioms {
      }
      ;

sets : {$$ = NULL;}
     | TSOS TLPAREN TFORMULAS TRPAREN TDOT formulas_sets_tail
     {
       $$ = $6;
       if ($$ != NULL) {
	 $$->id=SOS;
       }
     }
     | TUSABLE TLPAREN TFORMULAS TRPAREN TDOT formulas_sets_tail
     {
       $$ = $6;
       if ($$ != NULL) {
	 $$->id=USABLE;
       }
     }
     | TSOS TLPAREN TCLAUSES TRPAREN TDOT clauses_sets_tail
     {
       $$ = $6;
       if ($$ != NULL) {
	 $$->id=SOS;
       }
     }
     | TUSABLE TLPAREN TCLAUSES TRPAREN TDOT clauses_sets_tail
     {
       $$ = $6;
       if ($$ != NULL) {
	 $$->id=USABLE;
       }
     }
     ;

formulas_sets_tail : formulas TEND TDOT sets
                  {
		    tnode *new = create_tnode(SETF,SETF,$1,$4,NULL);
		    $$ = new;
		   }
                  ;

clauses_sets_tail : clauses TEND TDOT sets
                  {
		    tnode *new = create_tnode(SETC,SETC,$1,$4,NULL);
		    $$ = new;
		  }
                  ;

clauses : {$$ = NULL;}
        | initial_clause TDOT clauses
	{
	  if ($3 != NULL) {
	    formulalist *newlist = tree_to_list(CONJUNCTION,$1,$3);
	    tnode *new = create_tnode(CONJUNCTION,CONJUNCTION,NULL,NULL,newlist);
	    $$ = new;
	  }
	  else $$ = $1;
	}
	| literal_clause TDOT clauses
	{
	  if ($3 != NULL) {
	    formulalist *newlist = tree_to_list(CONJUNCTION,$1,$3);
	    tnode *new = create_tnode(CONJUNCTION,CONJUNCTION,NULL,NULL,newlist);
	    $$ = new;
	  }
	  else $$ = $1;
	}
	| modal_clause TDOT clauses
	{
	  if ($3 != NULL) {
	    formulalist *newlist = tree_to_list(CONJUNCTION,$1,$3);
	    tnode *new = create_tnode(CONJUNCTION,CONJUNCTION,NULL,NULL,newlist);
	    $$ = new;
	  }
	  else $$ = $1;
	}
        | error TDOT clauses {numerrors++;}
        ;

initial_clause : TSTART TIMPLY disjunction_literals
                 {
		   inputsize += 2;
	           tnode *newst = create_tnode(CONSTANT,CSTART,NULL,NULL,NULL);
		   tnode *new = create_tnode(IMPLICATION,CONJUNCTION,newst,$3,NULL);
		   $$ = new;
                 }
                 ;

literal_clause : TTRUE TIMPLY disjunction_literals %prec TIMPLY
                 {
		   inputsize += 2;
	           tnode *newconst = create_tnode(CONSTANT,CTRUE,NULL,NULL,NULL);
		   tnode *new = create_tnode(IMPLICATION,IMPLICATION,newconst,$3,NULL);
		   $$ = new;
                 }
                 | disjunction_literals
		 {
	           //tnode *newconst = create_tnode(CONSTANT,CTRUE,NULL,NULL,NULL);
		   //tnode *new = create_tnode(IMPLICATION,IMPLICATION,newconst,$1,NULL);
		   //$$ = new;
		 }
                 ;

// It looks awful, but I have tried to factor this and I get an ambiguous grammar.

modal_clause : literal TIMPLY TNECESSARY modal_arg literal
               {
		inputsize += 2;
	        agent_node *a;
                char *pname, *index;
                pname = strdup($3);
                if ($4 !=NULL) {index = strdup($4);} else index=NULL;
                char *s = malloc(snprintf(NULL, 0, "%s %s", pname, index) + 1);
	        sprintf(s, "%s %s", pname, index);
	        a=insert_a_node(s);
	        tnode *new = create_tnode(BOX,a->id,$5,NULL,NULL);
		tnode *newimp = create_tnode(IMPLICATION,IMPLICATION,$1,new,NULL);
		$$ = newimp;
		free($3);
		if (index != NULL) free($4);
	       }
               | literal TIMPLY TNECESSARY literal
	       { 
		 inputsize += 2;
		 agent_node *a;
		 char *pname;
		 pname = strdup($3);
		 a=insert_a_node(pname);
		 tnode *new = create_tnode(BOX,a->id,$4,NULL,NULL);
		 tnode *newimp = create_tnode(IMPLICATION,IMPLICATION,$1,new,NULL);
		 $$ = newimp;
		 free($3);
	       }
               | literal TIMPLY TOBOX modal_arg TCBOX literal
	       { 
		 inputsize += 2;
		 agent_node *a;
		 char *index;
		 if ($4 !=NULL) {index = strdup($4);} else index=NULL;
		 char *s = malloc(snprintf(NULL, 0, "box %s", index) + 1);
		 sprintf(s, "box %s", index);
		 a=insert_a_node(s);
		 tnode *new = create_tnode(BOX,a->id,$6,NULL,NULL);
		 tnode *newimp = create_tnode(IMPLICATION,IMPLICATION,$1,new,NULL);
		 $$ = newimp;
		 if (index != NULL) free($4);
	       }
               | literal TIMPLY TOBOX TCBOX literal
	       {
		 inputsize += 2;
		 agent_node *a;
		 char * s = malloc(snprintf(NULL, 0, "box") + 1);
		 sprintf(s, "box");	  
		 a=insert_a_node(s);
		 tnode *new = create_tnode(BOX,a->id,$5,NULL,NULL);
		 tnode *newimp = create_tnode(IMPLICATION,IMPLICATION,$1,new,NULL);
		 $$ = newimp;
	       }
               | literal TIMPLY TPOSSIBLE modal_arg literal
	       { 
		 inputsize += 2;
		 agent_node *a;
		 char *pname, *index;
		 pname = getBoxName(strdup($3));
		 if ($4 !=NULL) {index = strdup($4);} else index=NULL;
		 char *s = malloc(snprintf(NULL, 0, "%s %s", pname, index) + 1);
		 sprintf(s, "%s %s", pname, index);
		 a=insert_a_node(s);
		 tnode *new = create_tnode(DIAMOND,a->id,$5,NULL,NULL);
		 tnode *newimp = create_tnode(IMPLICATION,IMPLICATION,$1,new,NULL);
		 $$ = newimp;
		 free($3);
		 if (index != NULL) free($4);
	       }
               | literal TIMPLY TPOSSIBLE literal
	       { 
		 inputsize += 2;
		 agent_node *a;
		 char *pname;
		 pname = getBoxName(strdup($3));
		 a = insert_a_node(pname);
		 tnode *new = create_tnode(DIAMOND,a->id,$4,NULL,NULL);
		 tnode *newimp = create_tnode(IMPLICATION,IMPLICATION,$1,new,NULL);
		 $$ = newimp;
		 free($3);
	       }
               | literal TIMPLY TODIA modal_arg TCDIA literal
	       { 
		 inputsize += 2;
		 agent_node *a;
		 char *index;
		 if ($4 !=NULL) {index = strdup($4);} else index=NULL;
		 char *s = malloc(snprintf(NULL, 0, "box %s", index) + 1);
		 sprintf(s, "box %s", index);
		 a=insert_a_node(s);
		 tnode *new = create_tnode(DIAMOND,a->id,$6,NULL,NULL);
		 tnode *newimp = create_tnode(IMPLICATION,IMPLICATION,$1,new,NULL);
		 $$ = newimp;
		 if (index != NULL) free($4);
	       }
               | literal TIMPLY TODIA TCDIA literal
	       {
		 inputsize += 2;
		 agent_node *a;
		 char * s = malloc(snprintf(NULL, 0, "box") + 1);
		 sprintf(s, "box");	  
		 a=insert_a_node(s);
		 tnode *new = create_tnode(DIAMOND,a->id,$5,NULL,NULL);
		 tnode *newimp = create_tnode(IMPLICATION,IMPLICATION,$1,new,NULL);
		 $$ = newimp;
	       }
	       ;

disjunction_literals : {$$ = NULL;}
                     | literal TOR disjunction_literals
		     {
		       inputsize += 1;
		       if ($3 != NULL) {
			 formulalist *list = tree_to_list(DISJUNCTION,$1,$3);
			 tnode *new = create_tnode(DISJUNCTION,DISJUNCTION,NULL,NULL,list);
			 $$ = new;
		       }
		       else $$ =$1;
		     }
                     | literal 
		     {
		       formulalist *list = tree_to_list(DISJUNCTION,$1,NULL);
		       tnode *new = create_tnode(DISJUNCTION,DISJUNCTION,NULL,NULL,list);
		       $$ = new;
		     }
                     | TLPAREN disjunction_literals TRPAREN
		     {
		       formulalist *list = tree_to_list(DISJUNCTION,$2,NULL);
		       tnode *new = create_tnode(DISJUNCTION,DISJUNCTION,NULL,NULL,list);
		       $$ = new;
		     }
                     ;

literal : proposition {$$ = $1;}
        | TNOT literal 
        {
	  inputsize += 1;
	  tnode *new = create_tnode(NEGATION,NEGATION,$2,NULL,NULL);
	  $$ = new;
        }
        

formulas : {$$ = NULL;}
         | formula TDOT formulas
	 {
	   if ($3 != NULL) {
	     formulalist *newlist = tree_to_list(CONJUNCTION,$1,$3);
	     tnode *new = create_tnode(CONJUNCTION,CONJUNCTION,NULL,NULL,newlist);
	     $$ = new;
	   }
	   else $$ = $1;
	 }
	 | error TDOT formulas {numerrors++;}
         ;

formula : formula TIFF formula 
          { // double-implications are not treated as abbreviations.
            // I would have a dag if I didn't want to copy the whole tree. 
            // and I don't want to deal with polarity at this point. 
	    // I am postponing whatever is to be done to when I need to put the formula into NNF.
	  inputsize += 1;
	  tnode *new = create_tnode(DOUBLEIMP,DOUBLEIMP,$1,$3,NULL);
	  $$ = new;
        }
        | formula TIMPLY formula
        {
	  inputsize += 1;
	  tnode *new = create_tnode(IMPLICATION,IMPLICATION,$1,$3,NULL);
	  $$ = new;
        }
        | formula TONLYIF formula
        {
	  inputsize += 1;
	  tnode *new = create_tnode(IMPLICATION,IMPLICATION,$3,$1,NULL);
	  $$ = new;
        }
        | formula TOR formula
        {
	  inputsize += 1;
	  formulalist *newlist = tree_to_list(DISJUNCTION,$1,$3);
	  tnode *new = create_tnode(DISJUNCTION,DISJUNCTION,NULL,NULL,newlist);
	  $$ = new;
        }
        | formula TAND formula
        {
	  inputsize += 1;
	  formulalist *newlist = tree_to_list(CONJUNCTION,$1,$3);
	  tnode *new = create_tnode(CONJUNCTION,CONJUNCTION,NULL,NULL,newlist);
	  $$ = new;
        }
        | TNOT formula 
        {
	  // I was eliminating double negations here, but that changes the counting of the input formula. 
	  inputsize += 1;
          tnode *new = create_tnode(NEGATION,NEGATION,$2,NULL,NULL);
	  $$ = new;
	}
        | TOBOX modal_arg TCBOX formula
	{ 
	  inputsize += 1;
	  agent_node *a;
          char *index;
          if ($2 !=NULL) {index = strdup($2);} else index=NULL;
          char * s = malloc(snprintf(NULL, 0, "box %s", index) + 1);
	  sprintf(s, "box %s", index);
	  a=insert_a_node(s);
	  tnode *new = create_tnode(BOX,a->id,$4,NULL,NULL);
	  $$ = new;
	  if (index != NULL) {
	    free(index);
	    free($2);
	  }
	}
        | TNECESSARY modal_arg formula 
        { 
	  inputsize += 1;
	  agent_node *a;
          char *pname, *index;
          pname = strdup($1);
          if ($2 !=NULL) {index = strdup($2);} else index=NULL;
          char * s = malloc(snprintf(NULL, 0, "%s %s", pname, index) + 1);
	  sprintf(s, "%s %s", pname, index);
	  a=insert_a_node(s);
	  tnode *new = create_tnode(BOX,a->id,$3,NULL,NULL);
	  $$ = new;
	  free($1);
	  if (index != NULL) {
	    free(index);
	    free($2);
	  }
        }
	| TOBOX TCBOX formula
	{ 
	  inputsize += 1;
	  agent_node *a;
	  char * s = malloc(snprintf(NULL, 0, "box") + 1);
	  sprintf(s, "box");	  
	  a=insert_a_node(s);
          tnode *new = create_tnode(BOX,a->id,$3,NULL,NULL);
	  $$ = new;
        }
        | TNECESSARY formula
        { 
	  inputsize += 1;
	  agent_node *a;
          char *pname;
          pname = strdup($1);
	  a=insert_a_node(pname);
          tnode *new = create_tnode(BOX,a->id,$2,NULL,NULL);
	  $$ = new;
	  free($1);
        }
        | TODIA modal_arg TCDIA formula
	{ 
	  inputsize += 1;
	  agent_node *a;
          char *index;
          if ($2 !=NULL) {index = strdup($2);} else index=NULL;
          char *s = malloc(snprintf(NULL, 0, "box %s", index) + 1);
	  sprintf(s, "box %s", index);
	  a=insert_a_node(s);
	  //tnode *new = create_tnode(DIAMOND,a->id,$4,NULL,NULL);
	  tnode *new1 = create_tnode(NEGATION,NEGATION,$4,NULL,NULL);
	  tnode *new2 = create_tnode(BOX,a->id,new1,NULL,NULL);
	  tnode *new = create_tnode(NEGATION,NEGATION,new2,NULL,NULL);
	  $$ = new;
	  if (index != NULL) {
	    free(index);
	    free($2);
	  }
	}
        | TPOSSIBLE modal_arg formula
        { 
	  inputsize += 1; // the modal_args count as zero (as part of the operator);
	  agent_node *a;
          char *pname, *index;
          pname = getBoxName(strdup($1));
          if ($2 !=NULL) {index = strdup($2);} else index=NULL;
          char *s = malloc(snprintf(NULL, 0, "%s %s", pname, index) + 1);
	  sprintf(s, "%s %s", pname, index);
	  a=insert_a_node(s);
	  //tnode *new = create_tnode(DIAMOND,a->id,$3,NULL,NULL);

	  tnode *new1 = create_tnode(NEGATION,NEGATION,$3,NULL,NULL);
	  tnode *new2 = create_tnode(BOX,a->id,new1,NULL,NULL);
	  tnode *new = create_tnode(NEGATION,NEGATION,new2,NULL,NULL);
	  $$ = new;
	  free($1);
	  if (index != NULL) {
	    free(index);
	    free($2);
	  }
        }
        | TODIA TCDIA formula
	{ 
	  inputsize += 1;
	  agent_node *a;
	  char * s = malloc(snprintf(NULL, 0, "box") + 1);
	  sprintf(s, "box");
	  a=insert_a_node(s);
          tnode *new = create_tnode(DIAMOND,a->id,$3,NULL,NULL);

		  //tnode *new1 = create_tnode(NEGATION,NEGATION,$3,NULL,NULL);
		  //tnode *new2 = create_tnode(BOX,a->id,new1,NULL,NULL);
		  //tnode *new = create_tnode(NEGATION,NEGATION,new2,NULL,NULL);
	  $$ = new;
        }
        | TPOSSIBLE formula
        { 
	  inputsize += 1;
	  agent_node *a;
          char *pname;
          pname = getBoxName(strdup($1));
	  a = insert_a_node(pname);
	  tnode *new = create_tnode(DIAMOND,a->id,$2,NULL,NULL);

	  //tnode *new1 = create_tnode(NEGATION,NEGATION,$2,NULL,NULL);
	  //tnode *new2 = create_tnode(BOX,a->id,new1,NULL,NULL);
	  //tnode *new = create_tnode(NEGATION,NEGATION,new2,NULL,NULL);
	  $$ = new;
	  free($1);
	}
        | TLPAREN formula TRPAREN
        {
	  $$ = $2;
	}
        | proposition
	{ 
	  $$ = $1;
        }
        ;

propositions_list: TNAME
                 {
		   char *prop = strdup($1);
		   prop_list *new = malloc(sizeof(prop_list));
		   new->prop = prop;
		   new->next = NULL;
		   free($1);
		   $$ = new;
		 }  
                 | TNAME TCOMMA propositions_list
                 {
		   char *prop = strdup($1);
		   prop_list *new = malloc(sizeof(prop_list));
		   new->prop = prop;
		   new->next = $3;
		   free($1);
		   $$ = new;
		 }
                 ;

modal_arg : TNUMBER 
          | TNAME
          ;

proposition: TNAME
           {
	     inputsize += 1;
             prop_node *p;
             char *pname = strdup($1);

	     char *s = malloc(snprintf(NULL, 0, "%s", pname) + 1);
	     sprintf(s, "%s", pname);
	     
	     p = insert_p_node(s);
	     tnode *new = create_tnode(PROP,p->id,NULL,NULL,NULL);
	     $$ = new;
	     free(pname);
	     free($1);
	   }
           | TSTART
	   {
	     inputsize += 1;
	     // prop_node *p = find_prop(CSTART);
	     tnode *new = create_tnode(CONSTANT,CSTART,NULL,NULL,NULL);
	     $$  = new;
	   }
           | TTRUE
	   {
	     inputsize += 1;
	     //prop_node *p = find_prop(CTRUE);
	     tnode *new = create_tnode(CONSTANT,CTRUE,NULL,NULL,NULL);
	     $$  = new;
	   }
           | TFALSE
	   {
	     inputsize += 1;
	     //	     prop_node *p = find_prop(CFALSE);
	     tnode *new = create_tnode(CONSTANT,CFALSE,NULL,NULL,NULL);
	     $$ = new;
	   } 
           ;

%%


char *getBoxName(char *diamond) {

  //NECESSARY   "L"|(?i:box)|(?i:nec)|(?i:necessary)|(?i:k)
  //POSSIBLE    "M"|(?i:dia)|(?i:pos)|(?i:diamond)|(?i:possible)
  char *s = NULL;

  if (!strcmp(diamond,"m")) {
     s = (char *) malloc(2);
     snprintf(s, 2, "%s","l");
  }
  else if (!strcmp(diamond,"dia") || !strcmp(diamond,"diamond")) {
    s = (char *) malloc(4);
    snprintf(s, 4, "%s","box");
  }
  else if (!strcmp(diamond,"possible")) {
    s = (char *) malloc(10);
    snprintf(s, 4, "%s","necessary");
  }
  free(diamond);
  return s;
}

void yyerror (char const *s) {
  fprintf (stderr, "\n Error: %s, line %d, column %d\n",s,numlines,numcolumns);
}

void process_ordering(prop_list *props) {
  while(props != NULL) {
    if (strcmp(props->prop,"start") && strcmp(props->prop,"true") && strcmp(props->prop,"false")) {
      insert_p_node(props->prop);
    }
    // not freeing the name because it is used in the symbol table.
    prop_list *aux;
    aux = props;
    props = props->next;
    free(aux); 
  }
}


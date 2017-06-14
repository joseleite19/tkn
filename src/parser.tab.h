/* A Bison parser, made by GNU Bison 3.0.2.  */

/* Skeleton interface for Bison GLR parsers in C

   Copyright (C) 2002-2013 Free Software Foundation, Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

#ifndef YY_YY_PARSER_TAB_H_INCLUDED
# define YY_YY_PARSER_TAB_H_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 1
#endif
#if YYDEBUG
extern int yydebug;
#endif
/* "%code requires" blocks.  */
#line 12 "parser.y" /* glr.c:2555  */

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

#line 66 "parser.tab.h" /* glr.c:2555  */

/* Token type.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    TIFF = 258,
    TIMPLY = 259,
    TONLYIF = 260,
    TOR = 261,
    TAND = 262,
    TNOT = 263,
    TPOSSIBLE = 264,
    TNECESSARY = 265,
    TOBOX = 266,
    TODIA = 267,
    TCBOX = 269,
    TCDIA = 270,
    TNAME = 272,
    TNUMBER = 273,
    TSTART = 274,
    TTRUE = 275,
    TFALSE = 276,
    TSET = 277,
    TDOT = 278,
    TCOMMA = 279,
    TCLAUSES = 280,
    TFORMULAS = 281,
    TSOS = 282,
    TUSABLE = 283,
    TEND = 284,
    TLPAREN = 285,
    TRPAREN = 286
  };
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE YYSTYPE;
union YYSTYPE
{
#line 91 "parser.y" /* glr.c:2555  */

  char *strValue;
  tnode *tnode;
  formulalist *formulalist;
  axiom_list *axiom_list;
  prop_list *prop_list;

#line 116 "parser.tab.h" /* glr.c:2555  */
};
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif



int yyparse (void);

#endif /* !YY_YY_PARSER_TAB_H_INCLUDED  */

#include <stdlib.h>
#include <stdio.h>
#include "prover.h"
#include "tree.h"

extern tnode *create_tnode(int type, int id, tnode *left, tnode *right, formulalist *list);
extern tnode *copy_tree(tnode *s);
extern formulalist *tree_to_list(int type, tnode *left, tnode *right);
extern unsigned int hash_tree (tnode *t);
extern unsigned int hash_list (formulalist *l);
extern void sort_formulalist(formulalist **l);

tnode *get_nnf(tnode *s) {
  if (s == NULL)
    return NULL;
  else switch (s->type) {
    case SETC:
      {
	s->right = get_nnf(s->right);
	return s;
      }
      break;
    case SETF: 
      {
	s->left = get_nnf(s->left);
	s->right = get_nnf(s->right);
	return s;
      }
      break;
    case CONSTANT:
    case PROP:
      return s;
      break;
    case BOX:
    case DIAMOND:
      {
	s->left = get_nnf(s->left);
	s->value_number = hash_tree(s);
	return s;
      }
      break;
    case NEGATION:
      {
	if (s->left != NULL) {
	  if (s->left->type == NEGATION) { // simplifies double negations
	    tnode *aux = s->left->left;
	    free(s->left);
	    free(s);
	    s = aux;
	    s = get_nnf(s);
	  }
	  else if (s->left->type == CONSTANT) {
	    s->type = CONSTANT;
	    if (s->left->id == CTRUE)
	      s->id = CFALSE;
	    else s->id = CTRUE;
	    free(s->left);
	    s->left = NULL;
	    s->value_number = hash_tree(s);
	  }
	  else if (s->left->type == BOX) {
	    tnode *not = create_tnode(NEGATION,NEGATION,s->left->left,NULL,NULL);
	    s->left->type = DIAMOND;
	    s->left->left = not;
	    s->value_number = hash_tree(s);
	    tnode *aux = get_nnf(s->left);
	    free(s);
	    s = aux;
	  }
	  else if (s->left->type == DIAMOND) {
	    tnode *not = create_tnode(NEGATION,NEGATION,s->left->left,NULL,NULL);
	    s->left->type = BOX;
	    s->left->left = not;
	    s->value_number = hash_tree(s);
	    tnode *aux = get_nnf(s->left);
	    free(s);
	    s = aux;
	    /* size doesn't change */
	  }
	  else if (s->left->type == IMPLICATION) { // neg (p then q) = p and neg q
	    s->type = CONJUNCTION;
	    s->id = CONJUNCTION;
	    tnode *right = create_tnode(NEGATION,NEGATION,s->left->right,NULL,NULL);
	    s->left = get_nnf(s->left->left);
	    right = get_nnf(right);
	    s->list = tree_to_list(CONJUNCTION,s->left,right);
	    s->left = NULL;
	    s->right = NULL;
	    s->value_number = hash_tree(s);
	  }
	  else if (s->left->type == DISJUNCTION) { // neg (p or q) = neg p or neg q
	    s->type = CONJUNCTION;
	    s->id = CONJUNCTION;
	    formulalist *aux = s->left->list;
	    while (aux != NULL) {
	      aux->formula = create_tnode(NEGATION,NEGATION,aux->formula,NULL,NULL);
	      aux->formula = get_nnf(aux->formula);
	      aux = aux->next;
	    }
	    s->list = s->left->list;
	    free(s->left);
	    s->left = NULL;
	    sort_formulalist(&(s->list));
	    s->list->value_number = hash_list(s->list);
	    s->value_number = hash_tree(s);
	  }
	  else if (s->left->type == CONJUNCTION) { // neg (p and q) = neg p and neg q
	    s->type = DISJUNCTION;
	    s->id = DISJUNCTION;
	    formulalist *aux = s->left->list;

	    while (aux != NULL) {
	      aux->formula = create_tnode(NEGATION,NEGATION,aux->formula,NULL,NULL);
	      aux->formula = get_nnf(aux->formula);
	      aux = aux->next;
	    }
	    s->list = s->left->list;
	    free(s->left);
	    s->left = NULL;
	    sort_formulalist(&(s->list));
	    s->list->value_number = hash_list(s->list);
	    s->value_number = hash_tree(s);
	  }
	  else s->left = get_nnf(s->left);
	}
	return s;
      }
      break;
    case CONJUNCTION:
      {
	formulalist *aux = s->list;
	while (aux != NULL) {
	  aux->formula = get_nnf(aux->formula);
	  if (aux->formula->type == CONJUNCTION) {
	    formulalist *aux2 = aux->formula->list;
	    formulalist *aux3 = aux->formula->list;
	    while (aux3->next != NULL) {
	      aux3 = aux3->next;
	    }
	    aux3->next = aux->next;
	    aux->formula = aux2->formula;
	    aux->next = aux2->next;
	    free(aux2);
	    aux = aux3;
	  }
	  aux = aux->next;
	}
	sort_formulalist(&(s->list));
	s->list->value_number = hash_list(s->list);
	s->value_number = hash_tree(s);
	return s;
      }
      break;
    case DISJUNCTION:
      {
	formulalist *aux = s->list;
	while (aux != NULL) {
	  aux->formula = get_nnf(aux->formula);
	  if (aux->formula->type == DISJUNCTION) {
	    formulalist *aux2 = aux->formula->list;
	    formulalist *aux3 = aux->formula->list;
	    while (aux3->next != NULL) {
	      aux3 = aux3->next;
	    }
	    aux3->next = aux->next;
	    aux->formula = aux2->formula;
	    aux->next = aux2->next;
	    free(aux2);
	    aux = aux3;
	  }
	  aux = aux->next;
	}
	sort_formulalist(&(s->list));
	s->list->value_number = hash_list(s->list);
	s->value_number = hash_tree(s);
	return s;
      }
      break;
    case IMPLICATION:
      {
	s->type = DISJUNCTION;
	s->id = DISJUNCTION;
	s->left = create_tnode(NEGATION,NEGATION,s->left,NULL,NULL);
	s->left = get_nnf(s->left);
	s->right = get_nnf(s->right);
	s->list = tree_to_list(DISJUNCTION,s->left,s->right);
	s->left = NULL;
	s->right = NULL;
	sort_formulalist(&(s->list));
	s->list->value_number = hash_list(s->list);
	s->value_number = hash_tree(s);
	return s;
      }
      break;
    case DOUBLEIMP:
      {
	s->type = CONJUNCTION;
	s->id = CONJUNCTION;
	tnode *tmp = create_tnode(IMPLICATION,IMPLICATION,copy_tree(s->left),copy_tree(s->right),NULL);
	s->right = create_tnode(IMPLICATION,IMPLICATION,s->right,s->left,NULL);
	s->left = tmp;
	
	s->left = get_nnf(s->left);
	s->right = get_nnf(s->right);
	s->list = tree_to_list(CONJUNCTION,s->left,s->right);
	s->left = NULL;
	s->right = NULL;
	sort_formulalist(&(s->list));
	s->list->value_number = hash_list(s->list);
	s->value_number = hash_tree(s);
	return s;
      }

      break;
    default:
      printf("We have a problem, Houston. In NNF. %d %d\n", s->type, DOUBLEIMP);
      }
  return s;
}

// p <-> q
// (p -> q) & (q -> p)
// (-p | q) & (-q | p)
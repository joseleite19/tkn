#include <stdlib.h>
#include <stdio.h>
#include "prover.h"
#include "uthash.h"
#include "symbol_table.h"
#include "tree.h"

#define MAX(X, Y) (((X) > (Y)) ? (X) : (Y))

extern void print_agent (int id);
extern void print_prop (int id);
extern prop_node *find_prop (int id);
extern unsigned int hash_tree (tnode *t);
extern unsigned int hash_list (formulalist *l);

extern int phase;

tnode *free_tree(tnode *t);


int indentation = 1;
int tab = 4;

int size_tree(tnode *s);
int size_list(formulalist *s) {
  if (s == NULL) return 0;
  else return (size_tree(s->formula) + size_list(s->next));
}

int size_tree(tnode *s) {
  if (s == NULL) return 0;
  else return (1 + size_tree(s->left) + size_tree(s->right) + size_list(s->list));
}

int is_literal (tnode *t) {
  if (t != NULL) {
    if ((t->type == PROP) || (t->type == CONSTANT)) return t->id;
    else if (t->type == NEGATION)
      if (t->left != NULL)
	if ((t->left->type == PROP) || (t->left->type == CONSTANT)) return -(t->left->id);
  }
  return 0;
}

int is_box (tnode *t) {
  if (t != NULL)
    if (t->type == BOX)
      return t->id;
  return 0;
}

int is_diamond (tnode *t) {
  if (t != NULL) {
    if (t->type == DIAMOND)
      return t->id;
    else if (t->type == NEGATION && t->left->type == BOX)
      return t->left->id;
  }
  return 0;
}

// literal < box < dia < disjunctions < conjunctions
// lit1 < lit2 if |lit1->id| < |lit2->id|
// box1 < box2 if box1->id < box2->id
// dia1 < dia2 if dia1->id < dia2->id

int compare_sizes_lists(formulalist *l1, formulalist *l2) {
  int s1 = 0;
  int s2 = 0;
  formulalist *aux = l1;

  while (aux != NULL) {
    s1++;
    aux = aux->next;
  }
  
  aux = l2;
  while (l2 != NULL) {
    s2++;
    l2 = l2->next;
  }
  if (s1 < s2)
    return 1;
  else if (s1 == s2)
    return 0;
  else return -1;
}


int compare_formula_snf(tnode *t1, tnode *t2) {
  int id1, id2;
  if ((id1 = is_literal(t1)) && (id2 = is_literal(t2))) {
    if (id1 < 0) id1 = -id1;
    if (id2 < 0) id2 = -id2;
    return (id1 <= id2);
  }
  else if ((id1 = is_box(t1)) && (id2 = is_box(t2))) {
    if (id1 == id2) 
      return compare_formula_snf(t1->left,t2->left);
    else return (id1 <= id2);
  }
  else if ((id1 = is_diamond(t1)) && (id2 = is_diamond(t2))) {
    if (id1 == id2) {
      tnode *aux1, *aux2;
      if (t1->type == NEGATION)
	aux1 = t1->left->left;
      else aux1 = t1->left;
      if (t2->type == NEGATION)
	aux2 = t2->left->left;
      else aux2 = t2->left;
      return compare_formula_snf(aux1,aux2);
    }
    else return (id1 <= id2);
  }
  else if ((t1->type == CONJUNCTION && t2->type == CONJUNCTION) ||
	   (t1->type == DISJUNCTION && t2->type == DISJUNCTION)) {
    int size = compare_sizes_lists(t1->list,t2->list);
    if (size == 1) // t1 is smaller
      return 1;
    else if (size == 0) // t1 and t2 have the same size
      return (t1->value_number <= t2->value_number);
    else return 0;
  }
  else if ((id1 = is_literal(t1) && !(id2 = is_literal(t2))) ||
	   (is_box(t1) && is_diamond(t2)) ||
	   ((t1->type == CONJUNCTION || t1->type == DISJUNCTION) && ((id2 = is_box(t2)) || (id2 = is_diamond(t2)))) ||
	   (t1->type == CONJUNCTION && t2->type == DISJUNCTION))
    return 1;
  return 0;
}


int compare_formula_nnf(tnode *t1, tnode *t2) {
  int id1, id2;
  if ((id1 = is_literal(t1)) && (id2 = is_literal(t2))) {
    if (id1 < 0) id1 = -id1;
    if (id2 < 0) id2 = -id2;
    return (id1 <= id2);
  }
  else if ((id1 = is_box(t1)) && (id2 = is_box(t2))) {
    if (id1 == id2) 
      return compare_formula_nnf(t1->left,t2->left);
    else return (id1 <= id2);
  }
  else if ((id1 = is_diamond(t1)) && (id2 = is_diamond(t2))) {
    if (id1 == id2) {
      tnode *aux1, *aux2;
      if (t1->type == NEGATION)
	aux1 = t1->left->left;
      else aux1 = t1->left;
      if (t2->type == NEGATION)
	aux2 = t2->left->left;
      else aux2 = t2->left;
      return compare_formula_nnf(aux1,aux2);
    }
    else return (id1 <= id2);
  }
  else if ((t1->type == CONJUNCTION && t2->type == CONJUNCTION) ||
	   (t1->type == DISJUNCTION && t2->type == DISJUNCTION)) {
    int size = compare_sizes_lists(t1->list,t2->list);
    if (size == 1)
      return 1;
    else if (size == 0)
      return (t1->value_number <= t2->value_number);
    else return 0;
  }
  else if ((id1 = is_literal(t1) && !(id2 = is_literal(t2))) ||
	   ((id1 = is_box(t1)) && (is_diamond(t2) || t2->type == CONJUNCTION || t2->type == DISJUNCTION)) ||
	   ((id1 = is_diamond(t1)) && (t2->type == CONJUNCTION || t2->type == DISJUNCTION)) ||
	   (t1->type == CONJUNCTION && t2->type == DISJUNCTION))
    return 1;
  return 0;
}


void split_formulalist(formulalist *l, formulalist **left, formulalist **right) {
  formulalist *fast;
  formulalist *slow;

  if (l == NULL || l->next == NULL) {
    *left = l;
    *right = NULL;
  }
  else {
    slow = l;
    fast = l->next;
    while (fast != NULL) {
      fast = fast->next;
      if (fast != NULL) {
	slow = slow->next;
	fast = fast->next;
      }
    }
    *left = l;
    *right = slow->next;
    slow->next = NULL;
  }
}

formulalist *sorted_merge_formulalist(formulalist *left, formulalist *right) {
  formulalist *result = NULL;
  if (left == NULL)
    return right;
  else if (right == NULL)
    return left;
  else if ((phase != SNF && compare_formula_nnf(left->formula,right->formula)) ||
	   (phase == SNF && compare_formula_snf(left->formula,right->formula))) {
    result = left;
    result->next = sorted_merge_formulalist(left->next,right);
  }
  else {
    result = right;
    result->next = sorted_merge_formulalist(left,right->next);
  }
  return result;
}

void sort_formulalist(formulalist **l) {
  formulalist *head = *l;
  formulalist *left;
  formulalist *right;
  
  if (head == NULL || head->next == NULL)
    return;
  else {
    split_formulalist(head,&left,&right);
    sort_formulalist(&left);
    sort_formulalist(&right);
    *l = sorted_merge_formulalist(left,right);
  }
}

formulalist *tree_to_list(int type, tnode *left, tnode *right) {
  if (left == NULL)
    return NULL;
  formulalist *left_list = NULL;
  formulalist *right_list = tree_to_list(type,right,NULL);
  if (left->type != type) {
    left_list = malloc(sizeof(formulalist));
    left_list->formula = left;
    // left_list->mdepth = left->mdepth;
    left_list->next = NULL;
  }
  else {
    left_list = left->list;
    free(left);
  }
  
  formulalist *aux = left_list;
  while (aux->next != NULL) {
    aux = aux->next;
  }
  
  aux->next = right_list;

  sort_formulalist(&left_list);
  left_list->mlevel = 0;
  if (right_list != NULL) 
    // left_list->mdepth = MAX(left_list->mdepth,right_list->mdepth);
  left_list->value_number = hash_list(left_list);
  return left_list;
}

tnode *create_tnode(int type, int id, tnode *left, tnode *right, formulalist *list) {
  tnode *new = malloc(sizeof(tnode));
  new->type = type;
  new->id = id;
  new->left = left;
  new->right = right;
  new->list = list;
  new->size = size_tree(new);
  new->flag = 0;
  new->value_number = hash_tree(new);
  return new;
}


tnode *copy_tree(tnode *s);
formulalist *copy_list(formulalist *s) {
  if (s == NULL) return NULL;
  else {
    formulalist *l = malloc(sizeof(formulalist));
    l->formula = copy_tree(s->formula);
    // l->mdepth = s->mdepth;
    l->next = copy_list(s->next);
    return l;
  }
}

tnode *copy_tree(tnode *s) {
  if (s == NULL) return NULL;
  else {
    tnode *root = malloc(sizeof(tnode));
    root->type = s->type;
    root->id = s->id;
    // root->mdepth = s->mdepth;
    // root->mlevel = s->mlevel;
    // root->polarity = s->polarity;
    // root->afactor = s->afactor;
    // root->bfactor = s->bfactor;
    // root->pfunction = s->pfunction;
    // root->npfunction = s->npfunction;
    // root->rfunction = s->rfunction;
    // root->distribute = s->distribute;
    root->value_number = s->value_number;
    root->left = copy_tree(s->left);
    root->right = copy_tree(s->right);
    root->list = copy_list(s->list);
    return root;
  }
}

int print_tree(tnode *s);
int print_list(formulalist *s) {
  if (s == NULL)
    return 0;
  int size1 = print_tree(s->formula);
  return (size1 + print_list(s->next));
}

int print_tree(tnode *s) {  
  int i;
  int size1, size2;
  
  if (s != NULL) {
    for (i=0;i<indentation;i++) printf(" ");
  
    switch (s->type) {
    case SETF:
      if (s->id == SOS) 
	printf("\n\n Conjunction of formulae in the SOS:\n");
      else if (s->id == USABLE)
	printf("\n\n Conjunction of formulae in the Usable:\n");
      print_tree(s->left);
      print_tree(s->right);
      break;
    case SETC:
      if (s->id == SOS) 
	printf("\n\n Conjunction of clauses in the SOS:\n");
      else if (s->id == USABLE)
	printf("\n\n Conjunction of clauses in the Usable:\n");
      print_tree(s->left);
      print_tree(s->right);
      break;	  
    case CONSTANT:
      if (s->id == CTRUE) printf("TRUE (id:%d,vn:%u,mlevel:%d)\n",s->id,s->value_number, s->mlevel);
      else if (s->id == CFALSE) printf("FALSE (id:%d,vn:%u,mlevel:%d)\n",s->id,s->value_number, s->mlevel);
      else if (s->id == CSTART) printf("START (id:%d,vn:%u,mlevel:%d)\n",s->id,s->value_number, s->mlevel);
      return 1;
      break;
    case PROP: 
      printf("PROPOSITION: ");
      print_prop(s->id);
      printf(" (id:%d,vn:%u,mlevel:%d)\n",s->id,s->value_number,s->mlevel); 
      return 1;
      break;
    case BOX:
      printf("MODAL: ");
      print_agent(s->id);
      printf(" (id:%d,vn:%u,mlevel:%d)\n",s->id,s->value_number, s->mlevel);
      indentation += tab;
      size1 = print_tree(s->left);
      indentation -= tab;
      return size1 + 1;
      break;
    case DIAMOND:
      printf("MODAL: ~ ");
      print_agent(s->id);
      printf(" ~ (id:%d,vn:%u,mlevel:%d)\n",s->id,s->value_number, s->mlevel); 
      indentation += tab;
      size1 = print_tree(s->left);
      indentation -= tab;
      return size1 + 1;
      break;
    case NEGATION: 
      printf("NEGATION");
      printf(" (id:%d,vn:%u,mlevel:%d)\n",s->id,s->value_number, s->mlevel); 
      indentation += tab;
      size1 = print_tree(s->left);
      indentation -= tab;
      return size1 + 1;
      break;
    case CONJUNCTION:
      printf("CONJUNCTION");
      printf(" (id:%d,vn:%u,mlevel:%d)\n",s->id,s->value_number, s->mlevel); 
      indentation += tab;
      size1 = print_list(s->list);
      indentation -= tab;
      return size1 + 1;
      break;
    case DISJUNCTION:
      printf("DISJUNCTION");
      printf(" (id:%d,vn:%u,mlevel:%d)\n",s->id,s->value_number, s->mlevel); 
      indentation += tab;
      size1 = print_list(s->list);
      indentation -= tab;
      return size1 + 1;
      break;
    case IMPLICATION:
      printf("IMPLICATION");
      printf(" (id:%d,vn:%u,mlevel:%d)\n",s->id,s->value_number, s->mlevel); 
      indentation += tab;
      size1 = print_tree(s->left);
      size2 = print_tree(s->right);
      indentation -= tab;
      return size1 + size2 + 1;
      break;
    case DOUBLEIMP:
      printf("DOUBLE IMPLICATION");
      printf(" (id:%d,vn:%u,mlevel:%d)\n",s->id,s->value_number, s->mlevel); 
      indentation += tab;
      size1 = print_tree(s->left);
      size2 = print_tree(s->right);
      indentation -= tab;
      return size1 + size2 + 1;
      break;
    default:
      printf("We have a problem, Houston. Printing the tree. %d\n", s->type);
    }
  }
  return 0;
}

tnode *free_tnode(tnode *t);
formulalist *free_formulalist(formulalist *s) {
  if (s != NULL) {
    s->formula = free_tnode(s->formula);
    s->next = free_formulalist(s->next);
    free(s);
    s = NULL;
  }
  return s;
}

tnode *free_tnode(tnode *t) {
  if (t != NULL) {
    if (t->left != NULL)
      t->left = free_tnode(t->left);
    if (t->right != NULL)
      t->right = free_tnode(t->right);
    if (t->list != NULL)
      t->list = free_formulalist(t->list);
    free(t);
    t = NULL;
  }
  return t;
}

tnode *free_tree (tnode *s) {
  s = free_tnode(s);
  return s;
}


int same_list(formulalist *l1, formulalist *l2);

int same_tree (tnode *t1, tnode *t2) {
  if (t1 == NULL) {
    if (t2 == NULL) {
      return 1;
    }
  }
  else if (t2 == NULL) 
    return 0;
  else if (t1->type == t2->type && t1->id == t2->id && same_list(t1->list,t2->list))
    return (same_tree(t1->left,t2->left) && same_tree(t1->right,t2->right));
  return 0;
}

int same_list(formulalist *l1, formulalist *l2) {
  if (l1 == NULL) {
    if (l2 == NULL) {
      return 1;
    }
  }
  else if (l2 == NULL) 
    return 0;
  else if (same_tree(l1->formula,l2->formula))
    return (same_list(l1->next,l2->next));
  return 0;
}

tnode *tree_hash(tnode *node);

formulalist *list_hash(formulalist *l) {
  if (l != NULL) {
    int value = 0;
    formulalist *aux = l;
    while (aux != NULL) {
      value = 31*value + aux->formula->value_number;
      aux = aux->next;
    }
  }
  return l;
}

tnode *tree_hash(tnode *t) {
  if (t != NULL) {
    unsigned int aux;
    HASH_JEN(&(t->type),sizeof(int),2048,t->value_number,aux);
    if (t->type == PROP || t->type == CONSTANT || t->type == BOX || t->type == DIAMOND)
      t->value_number = 31*t->value_number + t->id;
    if (t->type != PROP && t->type !=  CONSTANT) {
      if (t->left != NULL) 
  t->value_number = 31*t->value_number + t->left->value_number;
      if (t->right != NULL) 
  t->value_number = 31*t->value_number + t->right->value_number;
      if (t->list != NULL) 
  t->value_number = 31*t->value_number + t->list->value_number;
    }
  }
  return t;
}

unsigned int hash_tree (tnode *t) {
  unsigned int aux;
  HASH_JEN(&(t->type),sizeof(int),2048,t->value_number,aux);
  if (t->type == PROP || t->type == CONSTANT || t->type == BOX || t->type == DIAMOND)
    t->value_number = 31*t->value_number + t->id;
  if (t->type != PROP && t->type !=  CONSTANT) {
    if (t->left != NULL) 
      t->value_number = 31*t->value_number + t->left->value_number;
    if (t->right != NULL) 
      t->value_number = 31*t->value_number + t->right->value_number;
    if (t->list != NULL) 
      t->value_number = 31*t->value_number + t->list->value_number;
  }
  return t->value_number;
}

unsigned int hash_list (formulalist *l) {
  int value = 0;
  formulalist *aux = l;
  while (aux != NULL) {
    value = 31*value + aux->formula->value_number;
    aux = aux->next;
  }
  return value;
}



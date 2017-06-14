#include "list.h"

tnode *back(header *h){
	return h->end->formula;
}

tnode *front(header *h){
	return h->begin->formula;
}

int empty(header *h){
	return h->begin == NULL;
}

void pop_back(header *h){
	list *tmp = h->end->prev;

	// free_tree(h->end->formula);
	free(h->end);

	if(tmp){
		tmp->next = NULL;
		h->end = tmp;
	}
	else h->end = h->begin = NULL;
}

void pop_front(header *h){
	list *tmp = h->begin->next;

	// free_tree(h->begin->formula);
	free(h->begin);

	if(tmp){
		tmp->prev = NULL;
		h->begin = tmp;
	}
	else h->begin = h->end = NULL;
}

void push_back(header *h, tnode *f){
	list *tmp = (list *)malloc(sizeof(list));

	tmp->prev = tmp->next = NULL;
	
	// tmp->formula = copy_tree(f);
	tmp->formula = f;

	if(empty(h)) h->begin = h->end = tmp;
	else{
		tmp->prev = h->end;
		h->end->next = tmp;
		h->end = tmp;
	}
}

void push_front(header *h, tnode *f){
	list *tmp = (list *)malloc(sizeof(list));

	tmp->prev = tmp->next = NULL;
	
	// tmp->formula = copy_tree(f);
	tmp->formula = f;

	if(empty(h)) h->begin = h->end = tmp;
	else{
		tmp->next = h->begin;
		h->begin->prev = tmp;
		h->begin = tmp;
	}
}

void print(header *h){
	list *tmp;

	for(tmp = h->begin; tmp; tmp = tmp->next)
		print_tree(tmp->formula);
}

header *create_list(){
	header *h = (header *) malloc(sizeof(header));
	h->begin = h->end = NULL;
	return h;
}

header *clean(header *h){
	if(h){
		list *tmp, *p;

		for(tmp = h->begin; tmp; ){
			p = tmp->next;

			// free_tree(tmp->formula);
			free(tmp);

			tmp = p;
		}

		free(h);
	}
	return NULL;
}

header *clean_free_tree(header *h){
	if(h){
		list *tmp, *p;

		for(tmp = h->begin; tmp; ){
			p = tmp->next;

			free_tree(tmp->formula);
			free(tmp);

			tmp = p;
		}

		free(h);
	}
	return NULL;
}

// void erase(header *h, tnode *f){
// 	list *tmp, *p;
// 	for(tmp = h->begin; tmp; ){
// 		p = tmp->next;

// 		if(same_tree(tmp->formula, f)){
// 			if(tmp->prev) tmp->prev->next = tmp->next;
// 			else h->begin = tmp->next;

// 			if(tmp->next) tmp->next->prev = tmp->prev;
// 			else h->end = tmp->prev;
			
// 			free_tree(tmp->formula);
// 			free(tmp);
// 		}

// 		tmp = p;
// 	}
// }

void erase(header *h, list *f){
	if(f->prev) f->prev->next = f->next;
	else h->begin = f->next;

	if(f->next) f->next->prev = f->prev;
	else h->end = f->prev;
}

void deserase(header *h, list *f){
	if(f->prev) f->prev->next = f;
	else h->begin = f;

	if(f->next) f->next->prev = f;
	else h->end = f;
}

header *copy_header(header *h){
	header *t = (header *) malloc(sizeof(header));
	t->end = t->begin = NULL;
	
	if(h->begin){
		t->begin = (list *)malloc(sizeof(list));
		// t->begin->formula = copy_tree(h->begin->formula);
		t->begin->formula = h->begin->formula;
		t->begin->prev = t->begin->next = NULL;
		list *p, *ptr;

		ptr = t->begin;

		for(p = h->begin->next; p; p = p->next){
			ptr->next = (list *)malloc(sizeof(list));
			ptr->next->prev = ptr;
			ptr->next->next = NULL;

			// ptr->next->formula = copy_tree(p->formula);
			ptr->next->formula = p->formula;

			ptr = ptr->next;
		}
		t->end = ptr;
	}
	return t;
}

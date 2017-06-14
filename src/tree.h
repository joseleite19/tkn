#ifndef TREE
#define TREE
typedef struct formulalist {
  int mdepth;
  int mlevel;
  int renamed_by;
  int definition_added;
  unsigned int value_number;
  struct tnode *formula;
  struct formulalist *next;
} formulalist;
  
typedef struct tnode {
  int type;
  int id;

  int size;
  
  int flag;

  // int mdepth;
  int mlevel;
  int polarity;
  // int renamed_by;
  // int definition_added;
  // int pfunction;
  // int npfunction;
  // int rfunction;
  // int afactor;
  // int bfactor;
  // int distribute;
  unsigned int value_number;
  struct tnode *left;
  struct tnode *right;
  struct formulalist *list;
} tnode;
#endif
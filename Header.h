//
//  Header.h/Users/gabriellewang/Desktop/emit/emit/main.c
//  emit
//
//  Created by Gabrielle Wang on 2018/11/29.
//  Copyright © 2018 Gabrielle Wang. All rights reserved.
//

#ifndef Header_h
#define Header_h



void insym(void);
void unsigned_integer(int i);
void integer(void);
int const_def_int(void);
int const_def_char(void);
void const_def(void);
void const_dclr(void);
void var_def(void);
void var_dclr(void);
void parameter(void);
void paralist(void);

void paravaluelist(void);

void statement(void);
void condition(void);
void statement_if(void);
void statement_while(void);
void statement_scanf(void);
void statement_printf(void);
void statement_return(void);
void statement_switch(void);
void default_subs(void);
void case_subs(void);
void casetable(void);
void constant(void);
void call_rfunc(void);
void statement_list(void);
void complex_statement(void);
void rfunc_def(void);
void vfunc_def(void);
void mainfunc_def(void);

void print_dagcode (int gx);
void enterdagpcode (int op, char* a, char* b, char* c,char* str);
void opt_dag (int begin);
int searchlist_no (int n);
int searchlist (char *a);
int searchtree(int op, int a, int b);
void create_trnode (int op, char *name, int l, int r);
void create_linode (int no, char *name);
int create_dag(int bkfront);
int nextwhitenode (int pos);
void dag_leaf (int nextdag);
int isactive (int front, char* ident);
void print_queue(int nextdag);
int isorphan (int no);
void init_queue (void);
int inqueue (int node);
void recurlc (int n);
void export_dag (int nextdag);
void init_dag (void);
void bkcut (int begin);
void testout (int debug);
#endif /* Header_h */

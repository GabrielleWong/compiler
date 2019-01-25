//
//  main.c
//  optimize
//
//  Created by Gabrielle Wang on 2018/12/11.
//  Copyright © 2018 Gabrielle Wang. All rights reserved.
//

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdlib.h>
#include <ctype.h>
#include "Header.h"
#pragma warning(disable:4996)
#define SPBASE          0x7fffeffc
#define GPBASE          0x10008000
#define DATABASE        0x10010000
#define IDMAX           1000 //          //标识符长度
#define INDEXMAX        32767      //数组上界
#define CHARSIZE        1000//        //读取单词大小
#define READLEN         1000         //读取行长度
#define KEYTYPECNT      13       //关键字数
#define SYMCNT          39          //单词数
#define ERRORTYPECNT    70     //错误类型数
#define FATALCNT        7          //符号表溢出类型数
#define PCODESIZE       5000////
#define MIPSSIZE        1000//
#define DAGSIZE         1000//
#define TMAX            1500           //tab
#define PARAMAX         50
#define CASEMAX         50
#define TMPMAX          5000
#define SREGNUM         8
#define TREGNUM         8
#define AREGNUM         3

#define NOTLOC          -1
#define MEMLOC          0
#define REGLOC          1
//定义部分

int debug = 3;

//debug 0
//1
//2
//3

//输入输出
FILE *fp;                   //测试文件
FILE *kp_tmp;               //其他输出信息
FILE *kp_pcode;             //输出文件——优化前中间代码
FILE *kp_dagcode;
FILE *kp_dagandconstcode;
FILE *kp_opt_pcode;         //输出文件——优化后中间代码
FILE *tp_mips;              //输出文件——目标代码
FILE *tp_dag_mips;
FILE *tp_opt_mips;
char path[200];             //读取文件路径

//词法、语法分析
int crtcc;                  //当前读入行的字符指针
int crtll;                  //当前读入行长度
char readln[READLEN];       //当前读入行
int readlncnt = 0;          //行计数器，用于报错
char token[IDMAX] = {0};         //存放单词字符串
char newtoken[IDMAX] = {0};         //单词字符串_
char crtch = ' ';           //current char当前读入的字符
int crtnum = 0;             //current num当前读入的整型数值，词法分析将数字字符转换为整数
int numzero = 0;            //单词0开头标记
int symbol;                 //当前识别单词类型
int slen = 0;               //字符串长度
int isreturnfunc = 0;
int ismain = 0;//main函数中间出现return
int fbright = 0;
enum typesy {                               //单词类型
    VOIDSY,INTSY,KEYCHARSY, CONSTSY,MAINSY,  //const int char void main
    IFSY,WHILESY,SWITCHSY,CASESY,DEFAULTSY, // if while switch case default
    SCANFSY,PRINTFSY,RETURNSY,              //scanf printf return
    IDSY,
    NUMSY, CHARSY, STRINGSY,
    PLUSSY, MINUSSY, TIMESSY,DIVSY,                 //+ - * /
    EQLSY,NEQSY,LESSY,LEQSY,GRTSY,GEQSY,            // == != < <= > >=
    LPARSY, RPARSY, LBKTSY, RBKTSY, LCRBSY, RCRBSY, //()[]{}
    SQUOTESY, DQUOTESY,                             //' "
    COMMASY, SEMISY, COLONSY, ASSIGNSY              //, ; : =
};
char *keysy[KEYTYPECNT] = {                    //关键字枚举
    "void","int","char","const","main",     //const int char void main
    "if","while","switch","case","default", //if while switch case default
    "scanf","printf","return"               //scanf printf return
};
char *syms[SYMCNT] = {                    //关键字枚举
    "void","int","char","const","main",     //const int char void main
    "if","while","switch","case","default", //if while switch case default
    "scanf","printf","return",               //scanf printf return
    "idnetifier","number","character","string",
    "plus","minus","times","div",
    "==","!=","<","<=",">",">=",
    "(",")","[","]","{","}",
    "singleqoute","doubleqoute",
    "comma","semi","colon","assign"
};

int programbegsys[4] = {CONSTSY,INTSY,KEYCHARSY,VOIDSY};
int expbegsys[6] = {PLUSSY,MINUSSY,IDSY,NUMSY,LPARSY,CHARSY};
int statebegsys[10] = {IFSY,WHILESY,LCRBSY,INTSY,IDSY,SCANFSY,PRINTFSY,SEMISY,SWITCHSY,RETURNSY};

typedef struct {
    int typ;    //int char
    int result; //calculate result
    int obj;  // const,var //default is const
    char inf[IDMAX];// context
}expr;

//符号表、运行栈
int tx = 0;                     //tab索引
int trear = 0;              //最后一个为空的
int tfront = 0;             //局部第一个
int px = 0;
int mprear = 0;             //mips index
int gmprear = 0;//dag mips index
int prear = 0;              //pcode index
int pout = 0;               //output pcode index
int gout = 0;               //dag
int prc = 0;                //pcode current index for mips
int gdx = 0;                //global index
int dx = 0;                 //运行栈索引
int strcnt = 0;
char strlab[10] = {0};
char tmp_name[IDMAX];
int tmp_obj;
int tmp_typ;
int tmp_global = 0;
int tmp_adr = 0;
int tmp_ah = 0;
int tmp_paranum = 0;
int tmp_paratype[PARAMAX] = {0};
char tmp_pa[IDMAX], tmp_pb[IDMAX], tmp_pc[IDMAX];
enum tab_obj {CONSTobj,VARobj,FUNCobj,PARAobj,TMPobj,MIPSREGobj};
enum tab_typ {VOIDtyp,INTtyp,CHARtyp,INTARRAYtyp,CHARARRAYtyp,NOtyp};//?
enum reg_typ {NREG,SREG,TREG,AREG,VREG};
char regtyp[10] = {'\0','s','t','a','v'};
typedef struct{
    int hasreg;
    int regno;//reg number
    int regtyp;//s,t,a,v
    int refcnt;
} regmsgintab;

struct {
    char name[IDMAX];
    int obj;
    int typ;
    int global;
    int adr;
    int ah;
    int ispara;
    int paranum;// para no.
    int paratype[PARAMAX];
    int paraalloc[PARAMAX];//if para alloc sreg
    regmsgintab regs;
    int savereg[30];
}tab[TMAX];

//中间代码
struct pcode {
    int dag;//opt
    int op;
    char a[IDMAX];
    char b[IDMAX];
    char c[IDMAX];
    char *str;
}pcode[PCODESIZE];




//代码生成

int curfunc = 0;

struct {
    int order;
    char a[IDMAX];
    char b[IDMAX];
    char c[IDMAX];
    char* str;
} mips[MIPSSIZE];

//错误处理
int errpos;
int skipflag;
int errcnt = 0;
int errs[ERRORTYPECNT] = {0};
int testsys[SYMCNT] = {0};
int skipsys[SYMCNT] = {0};
enum fataltype {TABOF,PCODEOF,MIPSOF};
enum errtype {//错误类型
    ZERONUM,
    CHTYPE,
    CHBACK,
    EMPTYSTR,
    STRTYPE,
    SINEXC,
    INVALIDSYM,
    IDENT,
    NUM,
    NOTZERO,
    CONSTEQ,

    CONSTCH,
    CONSTTYPE,
    IDENTTYPE,
    FUNCIDENTTYPE,
    SEMI,
    PARATYPE,
    EQ, LP, RP, RB, LC, RC,
    FACTORTYPE,
    COLON,
    LABELTYPE,
    CALLIDENT,
    STATETYPE,
    PROGRAMTYPE,
    MAINNOTEND,
    NOTCASE,
    DUPIDENT,
    ARRAYINDEXOF,
    NOID,
    CONSTID,
    PARAINVALID,
    WRONGVAL,
    IDNOTFUNC,
    DIVZERO,
    WRONGTYPEARRAY,
    AHNOTINT,
    WRONGARRAYINDEX,
    VOIDFUNC,
    PARANOTMATCH,
    WRONGPARANUM,
    CASELABELNOTMATCH,
    NODEFAULT,
    MULTILAB,
    VOIDHASRETURN,
    RETURNTYPE,
    NOTASSIGN,
    ASSIGNNOTMATCH,
    NORETURN,
    NOTENDMAIN,
    CONDITIONTYPE,
    INCOMPLETEFILE,
};
char *msg[ERRORTYPECNT] = {//错误信息
    "number begin at 0 (except 0)",
    "wrong ch type",
    "miss ch back \'",
    "string is empty",
    "wrong string type",
    "invalid single !, suppose to be != ",
    "invalid input sym",
    "not a identifier",
    "not a number",
    "input number is zero, suppose to be postive as array index",
    "miss '=' ^^^in const defination ",

    "wrong const assigned char type",
    "wrong ident type^^^in const def",
    "wrong ident type , suppose to be char or int",
    "wrong function name",
    "miss semicolon",
    "wrong parameter type",
    "miss '=' ", "miss '('", "miss ')'", "miss ']'", "miss '{'", "miss '}'",
    "wrong factor type",
    "miss ':'",
    "wrong constant type as a switch-case label",
    "not a identifier^^^in call function",
    "wrong statement type",
    "wrong program type",
    "main function is not the end",
    "not a case",
    "multiple def of identifier",
    "array index overflow",
    "no identifier",
    "wrong const id, renamed",
    "para not define",
    "wrong scanf para type",
    "call function name is not define",
    "div number is zero",
    "array type invalid",
    "array index is not int",
    "wrong array index field",
    "suppose to be returned function instead void",
    "call function parameter type is not match",
    "call function parameter number is not match",
    "case label type not match",
    "no default in switch-case",
    "redefine label in switch-case",
    "void function has return statement",
    "function return type not match",
    "only variable can be assigned",
    "assign type not match",
    "return without content",
    "function boundary error, not end of main",
    "condition type is char",
    "file boundary error,not end of } of main",

};

//函数部分
//错误处理操作
void error (int type) {
    if (errpos == 0)  fprintf(kp_tmp, "******error begin***\n");
    if (crtcc > errpos) {
        fprintf(kp_tmp, "error %d at line%d, pos%d, %s\n", type,readlncnt,crtcc,msg[type]);
        printf("error %d at line%d, pos%d, %s\n", type,readlncnt,crtcc,msg[type]);
    }
    errs[type] = 1;
    errpos = crtcc;

}

void errormsg () {
    fprintf(kp_tmp, "***error message***\n");
    int i;
    for (i = 1; i < errcnt; i++) {
        if (errs[i]) {
            fprintf(kp_tmp, "  %d %s \n", i, msg[i]);
            printf( "  %d %s \n", i, msg[i]);
            errs[i] = 0;
        }
    }
};

void skipmsg () {
    skipflag = 0;

    fprintf(kp_tmp, "****skip in line %d: from %d to%d \n***", readlncnt, errpos, crtcc);
    printf( "skip in line %d: from %d to%d \n", readlncnt, errpos, crtcc);
    while (crtcc<errpos) {
        fprintf(kp_tmp, "-");
        errpos++;
    }
    errpos = crtcc;

};

void skip (int *skipsys, int err, int sy) {
    error(err);
    skipflag = 1;
    while (skipsys[sy] != 1) {
        insym();
    }
    if (skipflag) skipmsg();
};

void sys_clr () {
    memset(testsys,0,SYMCNT);
    memset(skipsys,0,SYMCNT);
};

void test (int *testsys, int *skipsys, int err, int sy) {
    if (testsys[sy] != 1) {
        skip(skipsys, err, sy);
    }
};

enum grammartype{
    CONSTDEF,
    PARA,
    VARDEF,
    PROGRAM,
    CASEDEF
};

void test_uni (int tp) {
    sys_clr();

    switch (tp) {
        case CONSTDEF: {
            testsys[INTSY] = 1;
            testsys[KEYCHARSY] = 1;//test int char
            skipsys[INTSY] =1;
            skipsys[KEYCHARSY] =1;
            skipsys[VOIDSY] =1;
            skipsys[SEMISY] =1;//skip until int char void ;
            test(testsys,skipsys,CONSTTYPE,symbol);
            break;
        }
        case PARA: {
            testsys[INTSY] = 1;
            testsys[KEYCHARSY] = 1;//test int char
            skipsys[INTSY] =1;
            skipsys[KEYCHARSY] =1;
            skipsys[RPARSY] =1;
            skipsys[LCRBSY] =1;
            skipsys[SEMISY] =1;//skip until int char  ) { ;
            test(testsys,skipsys,PARATYPE,symbol);
            break;
        }
        case VARDEF: {
            testsys[INTSY] = 1;
            testsys[KEYCHARSY] = 1;//test int char
            skipsys[INTSY] =1;
            skipsys[KEYCHARSY] =1;
            skipsys[VOIDSY] =1;
            skipsys[SEMISY] =1;//skip until int char void ;
            test(testsys,skipsys,IDENTTYPE,symbol);
            break;
        }
        case PROGRAM: {
            testsys[MAINSY] = 1;
            testsys[IDSY] = 1;//test main ident
            skipsys[LCRBSY] =1;//skip until  ; next func
            test(testsys,skipsys,FUNCIDENTTYPE,symbol);
            break;
        }
        case CASEDEF: {
            testsys[CASESY] = 1;
            skipsys[SEMISY] =1;//skip until  ;
            test(testsys,skipsys,NOTCASE,symbol);
            break;
        }

        default:break;
    }
};

void finish_prj(void);
void fatal (int tp) {
    fprintf(kp_tmp,"\n");
    errormsg();
    char *fatalmsg[FATALCNT] = {
        "tab",
        "pcode",
        "mips"
    };
    fprintf(kp_tmp,"%s is too small", fatalmsg[tp]);
    finish_prj();
};

//符号表操作
void entertab () {
    int i,j;
    if (trear >= TMAX) fatal(TABOF);
    for (tx = trear - 1; tx >= tfront; tx--) {
        if (!strcmp(tab[tx].name, tmp_name)) {
            error(DUPIDENT);
            return;
        }
    }
    strcpy(tab[trear].name, tmp_name);
    tab[trear].obj = tmp_obj;
    tab[trear].typ = tmp_typ;
    tab[trear].global = tmp_global;
    tab[trear].adr = tmp_adr;
    tab[trear].ah = tmp_ah;
    tab[trear].ispara = 0;//
    tab[trear].paranum = tmp_paranum;
    tab[trear].regs.hasreg = 0;
    tab[trear].regs.refcnt = 0;
    tab[trear].regs.regno = -1;
    tab[trear].regs.regtyp = -1;

    for (j = 0; j < 30; j++) {
        tab[trear].savereg[j] = 0;
    }

    for (i = 0; i<tmp_paranum; i++) {
        tab[trear].paratype[i] = tmp_paratype[i];
    }


    if (tmp_global) {
        tfront = trear + 1;
        if (tmp_obj == VARobj) {
            tab[trear].adr = gdx;
            if ((tmp_typ == INTtyp) || (tmp_typ == CHARtyp)) {
                gdx = gdx - 4;
            }
            else if ((tmp_typ == INTARRAYtyp) || (tmp_typ == CHARARRAYtyp)){
                gdx = gdx - 4 * tmp_ah;
            }
            else printf("error in entertab:tab build has problem");
        }
        else if (tmp_obj == FUNCobj) dx = 0;//mips reg
    }
    else {
        if (tmp_obj == CONSTobj) {}
        /*else if (tmp_obj == MIPSREGobj) {
         tab[trear].adr = dx;
         dx = dx + 4*20;//8treg 8sreg 4areg
         }*/
        else {
            tab[trear].adr = dx;
            if ((tmp_typ == INTtyp) || (tmp_typ == CHARtyp)) {
                dx = dx + 4;
            }
            else if ((tmp_typ == INTARRAYtyp) || (tmp_typ == CHARARRAYtyp)){
                dx = dx + 4 * tmp_ah;
            }
            else printf("error in entertab:tab build has problem");
        }
    }
    trear++;
    tmp_adr = 0;
    tmp_paranum = -1;
    tmp_ah = 0;
};
void print_tab() {
    kp_tmp = fopen("tmpout.txt", "w");
    for (tx = tfront; tx <trear; tx++) {
        if (tab[tx].obj == VARobj) {
            switch(tab[tx].typ) {
                case INTtyp: {
                    fprintf(kp_tmp, "var int %s\n",tab[tx].name);
                    break;
                }
                case INTARRAYtyp: {
                    fprintf(kp_tmp, "var int %s[%d]\n",tab[tx].name,tab[tx].ah);
                    break;
                }
                case CHARtyp: {
                    fprintf(kp_tmp, "var char %s\n",tab[tx].name);
                    break;
                }
                case CHARARRAYtyp: {
                    fprintf(kp_tmp, "var char %s[%d]\n",tab[tx].name,tab[tx].ah);
                    break;
                }
                default:  fprintf(kp_tmp, "error ar print table: invalid vartype\n");
            }
        }
        else if (tab[tx].obj == CONSTobj) {
            fprintf(kp_tmp, "const %s %s = %d\n",keysy[tab[tx].typ],tab[tx].name,tab[tx].adr);
        }

    }
};

void leavetab () {
    print_tab();
    trear = tfront;
    tfront = 0;

};

int searchtab (char *target) {
    int i;

    for (i = trear-1; i >= 0; i--) {
        if (!strcmp(tab[i].name, target)) return i;
    }
    return -1;
};


//中间代码生成操作
typedef struct{
    int regnum;
    int regtyp;
}reginf;

struct {
    int sloc;//store in where reg or mem or not
    int adr;
    reginf regs;
} tempvar[TMPMAX];
void inittempvar () {
    int i =0;
    for (i = 0; i < TMPMAX; i++) {
        tempvar[i].sloc = NOTLOC;
        tempvar[i].regs.regnum = 0;
        tempvar[i].regs.regtyp = NREG;
    }
};
char nid_t[] = {'~','t',0,0,0,0,0,0};//debug
char nid[] = {'~','t',0,0,0,0,0,0};
int nid_cnt = 0;
char nlabel[] = {'L','a','b','e','l','_',0,0,0,0,0};
char nlabel_l[] = {'L','a','b','e','l','_',0,0,0,0,0};
int nlabel_cnt = 0;
void create_id (int type) {
    strcpy(nid,nid_t);//reset
    char tmp[10];
    nid_cnt++;
    sprintf(tmp,"%d",nid_cnt);
    strcat(nid, tmp);
    strcpy(tmp_name,nid);
    tmp_global = 0;//debug
    tmp_obj = TMPobj;//debug
    tmp_typ = type;
    entertab();
    tempvar[nid_cnt].adr = tab[trear-1].adr;
};

void create_label () {
    strcpy(nlabel,nlabel_l);//reset
    char tmp[10];
    nlabel_cnt++;
    sprintf(tmp,"%d",nlabel_cnt);
    strcat(nlabel, tmp);
};

enum pcode_op {
    NOPFC,
    FUNCFC,PARAFC,PUSHFC,CALLFC,FRETFC,
    RETFC,ARRLFC,ARRRFC,SCANFFC,PRINTFFC,
    PLUSFC,MINUSFC,TIMESFC,DIVFC,BEQFC,
    BNEFC,LESFC,GRTFC,GEQFC,LEQFC,
    ASSIGNFC,JUMPFC,
    LABELFC,SWITCHFC,CASEFC,LGFC,
    PRINTFSTRFC,RESTACKFC,OPSTACKFC,VRETFC,
    SASCENEFC,RESCENEFC,
};

void enterpcode (int op) {
    if (prear >= PCODESIZE) fatal(PCODEOF);
    pcode[prear].op = op;
    strcpy(pcode[prear].a,tmp_pa);
    strcpy(pcode[prear].b,tmp_pb);
    strcpy(pcode[prear].c,tmp_pc);
    if (op == PRINTFSTRFC) {
        pcode[prear].str = (char*)malloc(sizeof(char)*(strlen(token)+1));
        //pstr = pcode[prear].str;
        strcpy(pcode[prear].str,token);
    }
    prear++;
};


void print_pcode (int px) {

    //fprintf(kp_pcode,"\n\n");
    //fprintf(kp_pcode,"*****************PCODE*****************\n");
    //fprintf(kp_pcode,"\n\n");

    switch(pcode[px].op) {
        case LGFC: {
            fprintf(kp_pcode,"%s %s %s\n",pcode[px].a,pcode[px].c,pcode[px].b);
            //[exp] LGSY [exp]
            break;
        }

        case RESTACKFC:
        case OPSTACKFC:
        case SASCENEFC:
        case RESCENEFC: {
            //fprintf(kp_pcode,"%s %s()\n",pcode[px].a,pcode[px].b);
            //[type] [id] ()
            break;
        }

        case FUNCFC: {
            fprintf(kp_pcode,"%s %s()\n",pcode[px].b,pcode[px].a);
            //[type] [id] ()
            break;
        }
        case PARAFC: {
            fprintf(kp_pcode,"para %s %s\n",pcode[px].a,pcode[px].b);
            //para [type] [id]
            break;
        }
        case PUSHFC: {
            fprintf(kp_pcode,"push %s\n",pcode[px].a);
            //push [id] [空]
            break;
        }
        case CALLFC: {
            fprintf(kp_pcode,"call %s\n",pcode[px].a);
            //call [id] [空]
            break;
        }
        case FRETFC: {
            fprintf(kp_pcode,"%s = RET\n",pcode[px].a);
            //[id] = RET
            break;
        }
        case RETFC: {
            fprintf(kp_pcode,"ret %s\n",pcode[px].a);
            //ret [id]//pb save funcname
            break;
        }
        case VRETFC: {
            fprintf(kp_pcode,"ret \n");
            //ret [id]//pb save funcname
            break;
        }
        case ARRLFC: {
            fprintf(kp_pcode,"%s[%s] = %s\n",pcode[px].c,pcode[px].b,pcode[px].a);
            //push [id] [空]
            break;
        }
        case ARRRFC: {
            fprintf(kp_pcode,"%s = %s[%s]\n",pcode[px].c,pcode[px].a,pcode[px].b);
            //call [id] [空]
            break;
        }
        case CASEFC: {
            fprintf(kp_pcode,"%s == %s\n",pcode[px].a,pcode[px].b);
            //[exp] == [value]
            fprintf(kp_pcode,"BZ %s\n",pcode[px].c);
            break;
        }
        case ASSIGNFC: {
            fprintf(kp_pcode,"%s = %s\n",pcode[px].c,pcode[px].a);
            //[temp] = [exp]
            break;
        }
        case PLUSFC: {
            fprintf(kp_pcode,"%s = %s + %s\n",pcode[px].c,pcode[px].a,pcode[px].b);
            //[type] [id] ()
            break;
        }
        case MINUSFC: {
            fprintf(kp_pcode,"%s = %s - %s\n",pcode[px].c,pcode[px].a,pcode[px].b);
            //para [type] [id]
            break;
        }
        case TIMESFC: {
            fprintf(kp_pcode,"%s = %s * %s\n",pcode[px].c,pcode[px].a,pcode[px].b);
            //push [id] [空]
            break;
        }
        case DIVFC: {
            fprintf(kp_pcode,"%s = %s / %s\n",pcode[px].c,pcode[px].a,pcode[px].b);
            //call [id] [空]
            break;
        }
        case SCANFFC: {
            fprintf(kp_pcode,"read %s\n",pcode[px].a);
            // read id
            break;
        }
        case PRINTFFC: {
            fprintf(kp_pcode,"write  %s\n",pcode[px].a);
            //write  [content]
            break;
        }
        case PRINTFSTRFC: {
            fprintf(kp_pcode,"write %s \n",pcode[px].str);
            //free(pcode[px].str);
            //write [str]
            break;
        }
        case BNEFC: {
            fprintf(kp_pcode,"BNZ %s\n",pcode[px].c);//debug
            //BZ LABEL1
            break;
        }

        case BEQFC:
        case LESFC:
        case GRTFC:
        case GEQFC:
        case LEQFC: {
            fprintf(kp_pcode,"BZ %s\n",pcode[px].c);
            //BNZ LABEL1
            break;
        }
        case JUMPFC: {
            fprintf(kp_pcode,"GOTO %s\n",pcode[px].c);
            //GOTO LABEL1
            break;
        }
        case LABELFC: {
            fprintf(kp_pcode,"%s :\n",pcode[px].a);
            //Label_1:
            break;
        }
        case SWITCHFC:
        case NOPFC: {
            break;
        }
        default: {
            fprintf(kp_pcode,"error at print opcode: invalid opcode\n");
        }
    }

};



//代码优化


//dag
struct opt_pcode {
    int dag;//opt
    int op;
    char a[IDMAX];
    char b[IDMAX];
    char c[IDMAX];
    char *str;
}dagpcode[PCODESIZE],optpcode[PCODESIZE];

struct {
    int op;
    char name[IDMAX];
    int l;
    int r;
    int inq;// already in output queue
} tree[DAGSIZE];

struct {
    char name[IDMAX];
    int no;
} list[DAGSIZE];


int lirear = -1;//last one
int trrear = -1;
int dgx;
int dgpx;
int qx = -1;    //queue index
int queue[DAGSIZE];
int grear = 0;//dagpcode index//last empty one
int gfront = 0;

void print_newdagpcode (int px) {

    //fprintf(kp_dagandconstcode,"\n\n");
    //fprintf(kp_dagandconstcode,"*****************PCODE*****************\n");
    //fprintf(kp_dagandconstcode,"\n\n");

    switch(dagpcode[px].op) {
        case LGFC: {
            fprintf(kp_dagandconstcode,"%s %s %s\n",dagpcode[px].a,dagpcode[px].c,dagpcode[px].b);
            //[exp] LGSY [exp]
            break;
        }

        case RESTACKFC:
        case OPSTACKFC:
        case SASCENEFC:
        case RESCENEFC: {
            //fprintf(kp_dagandconstcode,"%s %s()\n",dagpcode[px].a,dagpcode[px].b);
            //[type] [id] ()
            break;
        }

        case FUNCFC: {
            fprintf(kp_dagandconstcode,"%s %s()\n",dagpcode[px].b,dagpcode[px].a);
            //[type] [id] ()
            break;
        }
        case PARAFC: {
            fprintf(kp_dagandconstcode,"para %s %s\n",dagpcode[px].a,dagpcode[px].b);
            //para [type] [id]
            break;
        }
        case PUSHFC: {
            fprintf(kp_dagandconstcode,"push %s\n",dagpcode[px].a);
            //push [id] [空]
            break;
        }
        case CALLFC: {
            fprintf(kp_dagandconstcode,"call %s\n",dagpcode[px].a);
            //call [id] [空]
            break;
        }
        case FRETFC: {
            fprintf(kp_dagandconstcode,"%s = RET\n",dagpcode[px].a);
            //[id] = RET
            break;
        }
        case RETFC: {
            fprintf(kp_dagandconstcode,"ret %s\n",dagpcode[px].a);
            //ret [id]//pb save funcname
            break;
        }
        case VRETFC: {
            fprintf(kp_dagandconstcode,"ret \n");
            //ret [id]//pb save funcname
            break;
        }
        case ARRLFC: {
            fprintf(kp_dagandconstcode,"%s[%s] = %s\n",dagpcode[px].c,dagpcode[px].b,dagpcode[px].a);
            //push [id] [空]
            break;
        }
        case ARRRFC: {
            fprintf(kp_dagandconstcode,"%s = %s[%s]\n",dagpcode[px].c,dagpcode[px].a,dagpcode[px].b);
            //call [id] [空]
            break;
        }
        case CASEFC: {
            fprintf(kp_dagandconstcode,"%s == %s\n",dagpcode[px].a,dagpcode[px].b);
            //[exp] == [value]
            fprintf(kp_dagandconstcode,"BZ %s\n",dagpcode[px].c);
            break;
        }
        case ASSIGNFC: {
            fprintf(kp_dagandconstcode,"%s = %s\n",dagpcode[px].c,dagpcode[px].a);
            //[temp] = [exp]
            break;
        }
        case PLUSFC: {
            fprintf(kp_dagandconstcode,"%s = %s + %s\n",dagpcode[px].c,dagpcode[px].a,dagpcode[px].b);
            //[type] [id] ()
            break;
        }
        case MINUSFC: {
            fprintf(kp_dagandconstcode,"%s = %s - %s\n",dagpcode[px].c,dagpcode[px].a,dagpcode[px].b);
            //para [type] [id]
            break;
        }
        case TIMESFC: {
            fprintf(kp_dagandconstcode,"%s = %s * %s\n",dagpcode[px].c,dagpcode[px].a,dagpcode[px].b);
            //push [id] [空]
            break;
        }
        case DIVFC: {
            fprintf(kp_dagandconstcode,"%s = %s / %s\n",dagpcode[px].c,dagpcode[px].a,dagpcode[px].b);
            //call [id] [空]
            break;
        }
        case SCANFFC: {
            fprintf(kp_dagandconstcode,"read %s\n",dagpcode[px].a);
            // read id
            break;
        }
        case PRINTFFC: {
            fprintf(kp_dagandconstcode,"write  %s\n",dagpcode[px].a);
            //write  [content]
            break;
        }
        case PRINTFSTRFC: {
            fprintf(kp_dagandconstcode,"write %s \n",dagpcode[px].str);
            //free(dagpcode[px].str);
            //write [str]
            break;
        }
        case BNEFC: {
            fprintf(kp_dagandconstcode,"BNZ %s\n",dagpcode[px].c);//debug
            //BZ LABEL1
            break;
        }

        case BEQFC:
        case LESFC:
        case GRTFC:
        case GEQFC:
        case LEQFC: {
            fprintf(kp_dagandconstcode,"BZ %s\n",dagpcode[px].c);
            //BNZ LABEL1
            break;
        }
        case JUMPFC: {
            fprintf(kp_dagandconstcode,"GOTO %s\n",dagpcode[px].c);
            //GOTO LABEL1
            break;
        }
        case LABELFC: {
            fprintf(kp_dagandconstcode,"%s :\n",dagpcode[px].a);
            //Label_1:
            break;
        }
        case SWITCHFC:
        case NOPFC: {
            break;
        }
        default: {
            fprintf(kp_dagandconstcode,"error at print opcode: invalid opcode\n");
        }
    }

};
void cpdagcodetopcode (int start) {
    int i;
    prear = grear;
    for (i = start; i < grear; i++) {
        strcpy(pcode[i].a,dagpcode[i].a);
        strcpy(pcode[i].b,dagpcode[i].b);
        strcpy(pcode[i].c,dagpcode[i].c);
        pcode[i].op = dagpcode[i].op;
        if (dagpcode[i].op == PRINTFSTRFC) {
            free(pcode[i].str);
            pcode[i].str = (char*)malloc(sizeof(char)*(strlen(dagpcode[grear].str)+1));
            strcpy(pcode[i].str,dagpcode[i].str);
        }
    }
};
void print_dagcode (int gx) {

    //fprintf(kp_dagcode,"\n\n");
    //fprintf(kp_dagcode,"*****************DAGPCODE*****************\n");
    //fprintf(kp_dagcode,"\n\n");

    switch(dagpcode[gx].op) {//debug gx <- px
        case LGFC: {
            fprintf(kp_dagcode,"%s %s %s\n",dagpcode[gx].a,dagpcode[gx].c,dagpcode[gx].b);
            //[exp] LGSY [exp]
            break;
        }

        case RESTACKFC:
        case OPSTACKFC:
        case SASCENEFC:
        case RESCENEFC: {
            //fprintf(kp_pcode,"%s %s()\n",pcode[gx].a,pcode[gx].b);
            //[type] [id] ()
            break;
        }

        case FUNCFC: {
            fprintf(kp_dagcode,"%s %s()\n",dagpcode[gx].b,dagpcode[gx].a);
            //[type] [id] ()
            break;
        }
        case PARAFC: {
            fprintf(kp_dagcode,"para %s %s\n",dagpcode[gx].a,dagpcode[gx].b);
            //para [type] [id]
            break;
        }
        case PUSHFC: {
            fprintf(kp_dagcode,"push %s\n",dagpcode[gx].a);
            //push [id] [空]
            break;
        }
        case CALLFC: {
            fprintf(kp_dagcode,"call %s\n",dagpcode[gx].a);
            //call [id] [空]
            break;
        }
        case FRETFC: {
            fprintf(kp_dagcode,"%s = RET\n",dagpcode[gx].a);
            //[id] = RET
            break;
        }
        case RETFC: {
            fprintf(kp_dagcode,"ret %s\n",dagpcode[gx].a);
            //ret [id]//pb save funcname
            break;
        }
        case VRETFC: {
            fprintf(kp_dagcode,"ret \n");
            //ret [id]//pb save funcname
            break;
        }
        case ARRLFC: {
            fprintf(kp_dagcode,"%s[%s] = %s\n",dagpcode[gx].c,dagpcode[gx].a,dagpcode[gx].b);
            //push [id] [空]
            break;
        }
        case ARRRFC: {
            fprintf(kp_dagcode,"%s = %s[%s]\n",dagpcode[gx].c,dagpcode[gx].a,dagpcode[gx].b);
            //call [id] [空]
            break;
        }
        case CASEFC: {
            fprintf(kp_dagcode,"%s == %s\n",dagpcode[gx].a,dagpcode[gx].b);
            //[exp] == [value]
            fprintf(kp_dagcode,"BZ %s\n",pcode[gx].c);
            break;
        }
        case ASSIGNFC: {
            fprintf(kp_dagcode,"%s = %s\n",dagpcode[gx].c,dagpcode[gx].a);
            //[temp] = [exp]
            break;
        }
        case PLUSFC: {
            fprintf(kp_dagcode,"%s = %s + %s\n",dagpcode[gx].c,dagpcode[gx].a,dagpcode[gx].b);
            //[type] [id] ()
            break;
        }
        case MINUSFC: {
            fprintf(kp_dagcode,"%s = %s - %s\n",dagpcode[gx].c,dagpcode[gx].a,dagpcode[gx].b);
            //para [type] [id]
            break;
        }
        case TIMESFC: {
            fprintf(kp_dagcode,"%s = %s * %s\n",dagpcode[gx].c,dagpcode[gx].a,dagpcode[gx].b);
            //push [id] [空]
            break;
        }
        case DIVFC: {
            fprintf(kp_dagcode,"%s = %s / %s\n",dagpcode[gx].c,dagpcode[gx].a,dagpcode[gx].b);
            //call [id] [空]
            break;
        }
        case SCANFFC: {
            fprintf(kp_dagcode,"read %s\n",dagpcode[gx].a);
            // read id
            break;
        }
        case PRINTFFC: {
            fprintf(kp_dagcode,"write  %s\n",dagpcode[gx].a);
            //write  [content]
            break;
        }
        case PRINTFSTRFC: {
            fprintf(kp_dagcode,"write %s \n",dagpcode[gx].str);
            //free(pcode[gx].str);
            //write [str]
            break;
        }
        case BNEFC: {
            fprintf(kp_dagcode,"BNZ %s\n",dagpcode[gx].c);//debug
            //BZ LABEL1
            break;
        }

        case BEQFC:
        case LESFC:
        case GRTFC:
        case GEQFC:
        case LEQFC: {
            fprintf(kp_dagcode,"BZ %s\n",dagpcode[gx].c);
            //BNZ LABEL1
            break;
        }
        case JUMPFC: {
            fprintf(kp_dagcode,"GOTO %s\n",dagpcode[gx].c);
            //GOTO LABEL1
            break;
        }
        case LABELFC: {
            fprintf(kp_dagcode,"%s :\n",dagpcode[gx].a);
            //Label_1:
            break;
        }
        case SWITCHFC:
        case NOPFC: {
            break;
        }
        default: {
            fprintf(kp_dagcode,"error at print opcode: invalid opcode\n");
        }
    }

};
void enterdagpcode (int op, char* a, char* b, char* c,char* str) {
    if (grear >= PCODESIZE) fatal(PCODEOF);
    dagpcode[grear].op = op;

    strcpy(dagpcode[grear].a,a);
    strcpy(dagpcode[grear].b,b);
    strcpy(dagpcode[grear].c,c);
    if (op == PRINTFSTRFC) {
        dagpcode[grear].str = (char*)malloc(sizeof(char)*(strlen(str)+1));
        //pstr = pcode[prear].str;
        strcpy(dagpcode[grear].str,str);
    }
    grear++;
};

void opt_dag (int begin) {
    int i;
    bkcut(begin);
    for (i = begin; i < prear; i++) {
        if (!pcode[i].dag) {//debug !
            init_dag();
            i = create_dag(i);//last is END:
            export_dag(i);
        }
        if ((i < prear) && (pcode[i].dag))  enterdagpcode(pcode[i].op,pcode[i].a,pcode[i].b,pcode[i].c,pcode[i].str);//same
    }
    for (i = gfront; i < grear; i++) {//debug grear <- prear
        print_dagcode(i);
    }
    gfront = grear;

};

int isdag(int op) {
    if  ((op == PLUSFC) || (op == MINUSFC) ||
         (op== TIMESFC) || (op == DIVFC) ||
         (op == ASSIGNFC))
        return 1;
    return 0;
};
void bkcut (int begin) {// 1 is cut
    int i;
    for (i = begin; i < prear; i++) {//?init fenduan buyiyang
        if (isdag(pcode[i].op))
            pcode[i].dag = 0;
        else
            pcode[i].dag = 1;
    }
};
void init_dag () {
    trrear = -1;
    lirear = -1;
};
int searchlist (char *a) {
    int i;
    for (i = 0; i <= lirear; i++) {
        if (!strcmp(list[i].name,a)) return i;
    }
    return -1;
};
int searchlist_no (int n) {
    int i;
    for (i = 0; i <= lirear; i++) {
        if (list[i].no == n) return i;
    }
    return -1;
};
int searchtree(int op, int a, int b) {
    int i;
    for (i = 0; i <= trrear; i++) {
        if ((tree[i].op == op) && (tree[i].l == a) && (tree[i].r == b)) return i;
    }
    return -1;
};
void create_trnode (int op, char *name, int l, int r) {
    trrear++;
    tree[trrear].op = op;
    tree[trrear].l = l;
    tree[trrear].r = r;
    tree[trrear].inq = 0;
    strcpy(tree[trrear].name,name);
};
void create_linode (int no, char *name) {
    lirear++;
    list[lirear].no = no;
    strcpy(list[lirear].name,name);//debug list <- tree
};


int create_dag(int bkfront) {
    int i,nextbk;
    int xi,yj,opk,zk;
    int tmpop;
    char tmpa[IDMAX],tmpb[IDMAX],tmpc[IDMAX];
    i = bkfront;

    while (!pcode[i].dag) {
        tmpop = pcode[i].op;//debug in while
        strcpy(tmpa,pcode[i].a);
        strcpy(tmpb,pcode[i].b);
        strcpy(tmpc,pcode[i].c);
        i++;
        if (tmpop == ASSIGNFC) {//c = a
            xi = searchlist(tmpa);//find a
            if (xi < 0) {
                create_trnode(NOPFC,tmpa, -1, -1);
                create_linode(trrear,tmpa);
                xi = list[lirear].no;
            }
            else xi = list[xi].no;

            zk = searchlist(tmpc);//find c
            if (zk < 0) create_linode(xi,tmpc);
            else list[zk].no = xi;
        }
        else {// c = a op b
            xi = searchlist(tmpa);//find a
            if (xi < 0) {
                create_trnode(NOPFC,tmpa, -1, -1);
                create_linode(trrear,tmpa);
                xi = list[lirear].no;
            }
            else xi = list[xi].no;
            yj = searchlist(tmpb);//find b
            if (yj < 0) {
                create_trnode(NOPFC,tmpb, -1, -1);
                create_linode(trrear,tmpb);
                yj = list[lirear].no;
            }
            else yj = list[yj].no;
            opk = searchtree(tmpop,xi,yj);//find op with x y
            if (opk < 0) {
                create_trnode(tmpop,"\0",xi,yj);//debug \0
                opk = trrear;
            }
            zk = searchlist(tmpc);//find c
            if (zk < 0) create_linode(opk,tmpc);
            else list[zk].no = opk;
        }
    }
    nextbk = i;
    return nextbk;
};

int nextwhitenode (int pos) {
    int i;
    for (i = (pos+1)%(trrear+1); i != pos; i = (i+1)%(trrear+1)) {
        if ((tree[i].op != NOPFC) && (!tree[i].inq)) return i;//debug no leaf
    }
    return -1;
};

void dag_leaf (int nextdag) {
    int i, j;
    //char tmp[10];
    int tp,tp2;
    for (i = 0; i <=trrear; i++) {//double leaf
        if (tree[i].op == NOPFC) {
            for (j=0; j<=lirear; j++) {
                if (!strcmp(tree[i].name,list[j].name)) {//init, a0 = a
                    if (list[j].no != i) {
                        tp = searchtab(tree[i].name);
                        create_id(tab[tp].typ);

                        enterdagpcode(ASSIGNFC,tree[i].name,"\0",nid,"\0");
                        strcpy(tree[i].name, nid);

                    }
                    break;
                }
            }
        }
    }
    for (i = 0; i <= lirear; i++) {//???????
        if (tree[list[i].no].op == NOPFC) {//leaf//????condition
            tp2 = searchtab(list[i].name);
            if (tab[tp2].obj == VARobj) {//debug global var
                if (strcmp(list[i].name,tree[list[i].no].name))// not equal
                    enterdagpcode(ASSIGNFC,tree[list[i].no].name,"\0",
                                  list[i].name,"\0");
            }
            else {
                if (isactive(nextdag,list[i].name)){//?
                    if (strcmp(list[i].name,tree[list[i].no].name))// not equal
                        enterdagpcode(ASSIGNFC,tree[list[i].no].name,"\0",
                                      list[i].name,"\0");
                }
            }

        }
    }


};

int isactive (int front, char* ident) {
    int i;

    for (i = front; i<prear; i++) {
        if ((!strcmp(ident,pcode[i].a)) || (!strcmp(ident,pcode[i].b)) || (!strcmp(ident,pcode[i].c))) return 1;
    }
    return 0;
};

void print_queue(int nextdag) {
    int i,j,tp = 0;
    int flag = 0;
    //char tmp[10];
    char tmpa[IDMAX], tmpb[IDMAX], tmpc[IDMAX];
    char tmpstr[1000] = {0};
    int tmpop;
    dag_leaf(nextdag);
    for (i = qx; i >= 0; i--) {//tranverse

        if (tree[tree[queue[i]].l].op != NOPFC)//middle node a
            strcpy(tmpa,list[searchlist_no(tree[queue[i]].l)].name);
        else
            strcpy(tmpa,tree[tree[queue[i]].l].name);//leaf a
        if (tree[tree[queue[i]].r].op != NOPFC)//middle node b
            strcpy(tmpb,list[searchlist_no(tree[queue[i]].r)].name);
        else
            strcpy(tmpb,tree[tree[queue[i]].r].name);
        tmpop = tree[queue[i]].op;// op

        for (j = 0; j <= lirear; j++) {//node c
            if (list[j].no == queue[i]) {
                tp = searchtab(list[j].name);
                if ((list[j].name[0] == '~') && (list[j].name[1] == 't')) {//tmpvar
                    if (isactive(nextdag,list[j].name)) {
                        strcpy(tmpc,list[j].name);
                        flag = 1;
                        break;
                    }
                    else list[j].no = -1;//inactive
                }
                else {
                    strcpy(tmpc,list[j].name);//var
                    flag = 1;
                    break;
                }
            }
        }
        if (!flag) {
            create_id(tab[tp].typ);
            create_linode(queue[i], nid);
            strcpy(tmpc,nid);

        }

        enterdagpcode(tmpop,tmpa,tmpb,tmpc,tmpstr);//the first one

        if (flag) {//other need to assign
            strcpy(tmpa,list[j].name);
            flag = 0;//reset
            for (j = j+1; j <= lirear; j++) {
                if (list[j].no == queue[i]) {
                    if ((list[j].name[0] == '~') && (list[j].name[1] == 't')) {//tmpvar
                        if (isactive(nextdag,list[j].name)) {
                            strcpy(tmpc,list[j].name);
                            enterdagpcode(ASSIGNFC,tmpa,"\0",tmpc,"\0");
                        }
                        else list[j].no = -1;//inactive
                    }
                    else {
                        strcpy(tmpc,list[j].name);//var
                        enterdagpcode(ASSIGNFC,tmpa,"\0",tmpc,"\0");
                    }
                }
            }
        }//flag
    }//queue
};
int isorphan (int no) {
    int i;
    for (i = 0; i <= trrear; i++) {
        if ((!tree[i].inq) && ((tree[i].l == no) || (tree[i].r == no))) return 0;
    }
    return 1;
};

void init_queue () {
    qx = -1;//debug
    memset(queue, 0, DAGSIZE);
    int i;
    for (i = 0; i <=trrear; i++) tree[i].inq = 0;//debug
};

int inqueue (int node) {
    tree[node].inq = 1;
    qx++;
    queue[qx] = node;
    return qx;
};

void recurlc (int n) {
    if ((tree[n].l == -1) || (!isorphan(n)) || (tree[n].inq)) return;
    else {
        inqueue(n);
        recurlc(tree[n].l);
    }
};

void export_dag (int nextdag) {
    int i;
    i = 0;//debug -1 to 0
    init_queue();
    i = nextwhitenode(i);
    while (i >= 0) {
        if (isorphan(i)) {
            inqueue(i);
            recurlc(tree[i].l);
        }
        i = nextwhitenode(i);
    }
    print_queue(nextdag);

};


//global reg allocation


typedef struct {
    int obj;//target type
    int id;//target temp name no.
    int alloc;// if alloc
    int save;//call func
    char name[IDMAX];
}mipsreg;

mipsreg treg[TREGNUM],sreg[SREGNUM],areg[AREGNUM],treg89[2];



void clr_regs () {
    int i = 0;
    while (i < SREGNUM) {
        sreg[i].alloc = 0;
        treg[i].alloc = 0;
        if (i < AREGNUM) areg[i].alloc = 0;
        i++;
    }
    while (i < TREGNUM) {

        treg[i].alloc = 0;
        i++;

    }
    treg89[0].alloc = 0;
    treg89[1].alloc = 0;
};
//sreg

int funcbk (int front) {
    int i;
    for (i = front; i <= trear; i++) {
        if (tab[i].obj == FUNCobj) break;
    }
    return i-1;//can be trear -1
};

int getrefmax(int f, int e) {
    int ret = f;
    int i = f+1;
    tab[f].regs.refcnt = -1;
    while (i <= e) {
        if ((tab[i].obj == VARobj) &&
            ((tab[i].typ == INTtyp) || (tab[i].typ == CHARtyp))) {
            if ((tab[i].regs.refcnt > tab[ret].regs.refcnt)
                && (!tab[i].regs.hasreg)) ret = i;
        }
        i++;
    }
    if ( tab[ret].regs.refcnt <= 0) return -1;
    return ret;
};

void alloc_globalreg (int begin) {
    int i,j;
    int f,e;//func front and
    int refmax;
    int tpa,tpb,tpc;
    for (i = begin; i < grear; i++) {//pcode
        tpc = searchtab(dagpcode[i].c);
        tpa = searchtab(dagpcode[i].a);
        tpb = searchtab(dagpcode[i].b);
        if ((tpa >= 0) && (tab[tpa].obj == VARobj)) tab[tpa].regs.refcnt++;//?VARobj
        if ((tpb >= 0) && (tab[tpb].obj == VARobj)) tab[tpb].regs.refcnt++;
        if ((tpc >= 0) && (tab[tpc].obj == VARobj)) tab[tpc].regs.refcnt++;//?
    }

    i = trear-1;
    while (i >= 0) {
        if (tab[i].obj == FUNCobj) break;
        i--;
    }
    f = i;//func tab
    e = trear;
    j = 0;
    while (j <= SREGNUM-1) {
        refmax = getrefmax(f,e);
        if (refmax == -1) break;//no need to alloc
        if (tab[refmax].ispara) {//para not alloc sreg
            goto allglo_next;
        }
        tab[refmax].regs.hasreg = 1;
        tab[refmax].regs.regno = j;
        tab[refmax].regs.regtyp = SREG;
        sreg[j].alloc = 1;
        strcpy(sreg[j].name,tab[refmax].name);


    allglo_next:
        j++;
    }

    /*for (i = 0; i < trear; i++) {
     if (tab[i].obj != FUNCobj) continue;
     else {
     f = i;
     i = funcbk(i) + 1;//next funcobj front
     e = i - 1;
     j = 0;



     }

     }*/
};

//treg
typedef struct{
    int op;
    int obj;
    char name[IDMAX];
}idinf;




void writeback_sreg() {
    int i = 0;
    int t;
    for (i = 0; i < SREGNUM; i++) {
        if (sreg[i].alloc) {
            t = searchtab(sreg[i].name);
            if (tab[t].global) {
                fprintf(tp_opt_mips,"sw $s%d, %d($gp)\n",i,tab[t].adr);

            }
            /*else {
             fprintf(tp_opt_mips,"sw $s%d, %d($sp)\n",i,tab[t].adr);
             }*/

        }
    }
};

int usetemp (int front, char* tmpname) {//debug dagcode
    int i = front;
    while (i < grear) {
        if ((dagpcode[i].a[0] == '~') && (dagpcode[i].a[1] == 't') && (!strcmp(dagpcode[i].a,tmpname))) return 1;
        if ((dagpcode[i].b[0] == '~') && (dagpcode[i].b[1] == 't') && (!strcmp(dagpcode[i].b,tmpname))) return 1;
        if ((dagpcode[i].c[0] == '~') && (dagpcode[i].c[1] == 't') && (!strcmp(dagpcode[i].c,tmpname))) return 1;
        i++;
    }
    return 0;
};
int usevar (int front, char* tmpname) {//debug dagcode
    int i = front + 1;//debug
    while (i < grear) {
        if (!strcmp(dagpcode[i].a,tmpname)) return 1;
        if (!strcmp(dagpcode[i].b,tmpname)) return 1;
        if (!strcmp(dagpcode[i].c,tmpname)) return 1;
        i++;
    }
    return 0;
};

reginf alloc_treg_tmp(int tmpno, char* tmpname) {
    reginf ret = {-1,-1};
    int i = 0;
    int sloc,regnum;
    int tp = searchtab(tmpname);
    sloc = tempvar[tmpno].sloc;
    regnum = tempvar[tmpno].regs.regnum;
    if (sloc == REGLOC) {//already in reg
        treg[regnum].alloc = 1;
        strcpy(treg[regnum].name,tmpname);
        ret.regnum = regnum;
        ret.regtyp = TREG;
        //?tab
        tab[tp].regs.hasreg = 1;
        tab[tp].regs.regno = regnum;
        tab[tp].regs.regtyp = TREG;
    }
    else {
        while (i < TREGNUM) {//has available tregs
            if (!treg[i].alloc) {//?
                if (sloc == MEMLOC) {//reg <- mem
                    fprintf(tp_opt_mips,"lw $t%d, %d($sp)\n",i,tab[tp].adr);//or tmpvar[]
                    treg[i].alloc = 1;
                    treg[i].obj = TMPobj;
                    treg[i].id = tmpno;
                    strcpy(treg[i].name,tmpname);

                    tempvar[tmpno].sloc = REGLOC;
                    tempvar[tmpno].regs.regnum = i;
                    tempvar[tmpno].regs.regtyp = TREG;

                    tab[tp].regs.hasreg = 1;//
                    tab[tp].regs.regtyp = TREG;//
                    tab[tp].regs.regno = i;//???

                    ret.regnum = i;
                    ret.regtyp = TREG;
                    break;
                }
                else {//first use
                    treg[i].alloc = 1;
                    treg[i].obj = TMPobj;
                    treg[i].id = tmpno;
                    strcpy(treg[i].name,tmpname);//debug i

                    tempvar[tmpno].sloc = REGLOC;
                    tempvar[tmpno].regs.regnum = i;
                    tempvar[tmpno].regs.regtyp = TREG;

                    tab[tp].regs.hasreg = 1;//
                    tab[tp].regs.regtyp = TREG;//
                    tab[tp].regs.regno = i;//???

                    ret.regnum = i;
                    ret.regtyp = TREG;
                    break;
                }
            }
            i++;//debug
        }//while
        if (i >= TREGNUM) {//no available tregs
            i = 0;
            while (i < TREGNUM) {//find a proper tregs to use
                if (!usetemp(prc,treg[i].name)) /*&& (!treg[i].alloc)*/{//?????alloc
                    if (sloc == MEMLOC) //reg <- mem
                        fprintf(tp_opt_mips,"lw $t%d, %d($sp)\n",i,tab[tp].adr);//or tmpvar[]

                    tempvar[treg[i].id].sloc = MEMLOC;//write back
                    tempvar[treg[i].id].regs.regnum = -1;
                    tempvar[treg[i].id].regs.regtyp = NREG;

                    treg[i].alloc = 1;//treg
                    treg[i].obj = TMPobj;
                    treg[i].id = tmpno;
                    strcpy(treg[i].name,tmpname);

                    tempvar[tmpno].sloc = REGLOC;//alloc
                    tempvar[tmpno].regs.regnum = i;
                    tempvar[tmpno].regs.regtyp = TREG;



                    tab[tp].regs.hasreg = 1;//
                    tab[tp].regs.regtyp = TREG;//
                    tab[tp].regs.regno = i;//???

                    ret.regnum = i;
                    ret.regtyp = TREG;
                    break;

                }
                i++;
            }//while
        }

        if (i >= TREGNUM) {//no not use tregs// write back and load
            i = tmpno%8;//change
            //while ((i < TREGNUM) && (i != tmpno%8)) {
            // i = (i+1)%8;
            //if (!treg[i].alloc) {//?

            fprintf(tp_opt_mips,"sw $t%d, %d($sp)\n",i,tempvar[treg[i].id].adr);//mem <- reg
            if (sloc == MEMLOC) //reg <- mem
                fprintf(tp_opt_mips,"lw $t%d, %d($sp)\n",i,tab[tp].adr);//or tmpvar[]

            tempvar[treg[i].id].sloc = MEMLOC;//write back
            tempvar[treg[i].id].regs.regnum = -1;
            tempvar[treg[i].id].regs.regtyp = NREG;


            treg[i].alloc = 1;//alloc
            treg[i].obj = TMPobj;
            treg[i].id = tmpno;
            strcpy(treg[regnum].name,tmpname);

            tempvar[tmpno].sloc = REGLOC;//alloc
            tempvar[tmpno].regs.regnum = i;
            tempvar[tmpno].regs.regtyp = TREG;


            tab[tp].regs.hasreg = 1;//
            tab[tp].regs.regtyp = TREG;//
            tab[tp].regs.regno = i;//???

            ret.regnum = i;
            ret.regtyp = TREG;
            // break;

            //}
            //}//while
        }//3 if
    }//else
    return ret;
};
void clr_globalvar_regs () {
    int i = 0;
    for (i = 0; i < trear; i++) {
        if (tab[i].global) {
            tab[i].regs.hasreg = 0;
        }
    }
};
reginf alloc_sreg_var(char *varname) {
    reginf ret = {-1,-1};
    int i = 0;
    int tp = searchtab(varname);
    if (tab[tp].regs.hasreg) {//already in reg// maybe areg debug
        if (tab[tp].regs.regtyp == AREG) {//para
            ret.regnum = tab[tp].regs.regno;
            ret.regtyp = tab[tp].regs.regtyp;//areg
            return ret;
        }
        if (!strcmp(sreg[tab[tp].regs.regno].name,tab[tp].name)) {//?debug
            ret.regnum = tab[tp].regs.regno;
            ret.regtyp = tab[tp].regs.regtyp;
        }
        else tab[tp].regs.hasreg = 0;

    }
    else {
        while (i < SREGNUM) {
            if (!sreg[i].alloc) {//??? //reg <- mem
                strcpy(sreg[i].name,varname);
                sreg[i].alloc = 1;
                tab[tp].regs.hasreg = 1;//
                tab[tp].regs.regtyp = SREG;//
                tab[tp].regs.regno = i;//???
                if (tab[tp].global) fprintf(tp_opt_mips,"lw $s%d, %d($gp)\n",i,tab[tp].adr);
                else fprintf(tp_opt_mips,"lw $s%d, %d($sp)\n",i,tab[tp].adr);

                ret.regnum = i;
                ret.regtyp = SREG;
                break;
            }
            i++;
        }
        /*if (i >= SREGNUM) {// no available //s7 special
            tab[tp].regs.hasreg = 0;//
            tab[tp].regs.regtyp = SREG;//
            tab[tp].regs.regno = 7;//???
            if (tab[tp].global) fprintf(tp_opt_mips,"lw $s%d, %d($gp)\n",i,tab[tp].adr);
            else fprintf(tp_opt_mips,"lw $s%d, %d($sp)\n",i,tab[tp].adr);
            ret.regnum = 7;
            ret.regtyp = SREG;
        }*/
    }
    return ret;
};
reginf alloc_treg_value(int value) {
    reginf ret = {-1,-1};
    if (value == 0) {
        ret.regnum = 0;
        ret.regtyp = NREG;
    }
    if (value != 0) {// t8 save number
        if (!treg89[0].alloc) {
            ret.regnum = 8;
            ret.regtyp = TREG;
            fprintf(tp_opt_mips,"addiu $t8, $0, %d\n",value);
            treg89[0].alloc = 1;
        }
        else if (!treg89[1].alloc) {
            ret.regnum = 8;
            ret.regtyp = TREG;
            fprintf(tp_opt_mips,"addiu $t9, $0, %d\n",value);
            treg89[1].alloc = 1;
        }

    }
    //?
    return ret;
};

reginf alloc_regs(idinf id){
    reginf ret = {-1,-1};
    char tmpno[IDMAX] = {0};
    int tid;
    //ret.op = regtk;
    //ret.obj = 2;
    /* if (id.op == RETFC) {//i = return
     ret.regnum = 0;
     ret.regtyp = VREG;//v1 waste??
     }*///debug
    if ((id.name[0] == '~') && (id.name[1] == 't')) {
        strncpy(tmpno,id.name+2,10);
        tid = atoi(tmpno);
        ret = alloc_treg_tmp(tid,id.name);//tmpvar
    }
    else if (id.obj == VARobj) ret = alloc_sreg_var(id.name);
    else if (id.obj == CONSTobj) ret = alloc_treg_value(atoi(id.name));
    else printf("******opt msg**********no alloc for this id\n");
    return ret;
}
//const integret and convey
void delete_dagpcode (int i) {
    dagpcode[i].op = NOPFC;
    strcpy(dagpcode[i].a," ");
    strcpy(dagpcode[i].b," ");
    strcpy(dagpcode[i].c," ");
};

void const_detect (int front) {
    int i = front;
    int tpa,tpb;
    char pa[IDMAX],pb[IDMAX];
    char value[10]= {0};

    while (i < prear) {//const value replace const
        strcpy(pa,dagpcode[i].a);
        strcpy(pb,dagpcode[i].b);
        tpa = searchtab(dagpcode[i].a);
        tpb = searchtab(dagpcode[i].b);
        if (isdag(dagpcode[i].op)) {
            if (dagpcode[i].op == ASSIGNFC) {
                if ((tpa >= 0) && (tab[tpa].obj == CONSTobj) &&
                    ((tab[tpa].typ == INTtyp) || (tab[tpa].typ == CHARtyp))) {
                    sprintf(value,"%d",tab[tpa].adr);
                    strcpy(dagpcode[i].a,value);
                }
            }
            else {//+-*/
                if ((tpa >= 0) && (tab[tpa].obj == CONSTobj) &&
                    ((tab[tpa].typ == INTtyp) || (tab[tpa].typ == CHARtyp))) {
                    sprintf(value,"%d",tab[tpa].adr);
                    strcpy(dagpcode[i].a,value);
                }
                if ((tpb >= 0) && (tab[tpb].obj == CONSTobj) &&
                    ((tab[tpb].typ == INTtyp) || (tab[tpb].typ == CHARtyp))) {
                    sprintf(value,"%d",tab[tpb].adr);
                    strcpy(dagpcode[i].b,value);
                }
            }
        }
        i++;
    }//while
};

int islgfc (int op) {
    if ((op == BEQFC) || (op == BNEFC) || (op == LEQFC) || (op == LESFC) || (op == GEQFC) || (op == GRTFC)) return 1;
    return 0;
};
void const_convey (int front, char* tmpname,char* value) {//tmpvar
    int i = front;
    while (i < grear) {
        if ((isdag(dagpcode[i].op)) && (!strcmp(dagpcode[i].c,tmpname))) break;//assign new value
        if ((dagpcode[i].op == SCANFFC) && (!strcmp(dagpcode[i].a,tmpname))) break;

        //c = a[b]
        if ((dagpcode[i].op == ARRRFC) && (!strcmp(dagpcode[i].c,tmpname))) break;

        if ((isdag(dagpcode[i].op)) || (islgfc(dagpcode[i].op))) {//???condition
            if (!strcmp(dagpcode[i].a,tmpname)) {
                strcpy(dagpcode[i].a,value);
                //const_merge(i);
            }
            if (!strcmp(dagpcode[i].b,tmpname)) {
                strcpy(dagpcode[i].b,value);//????c
                //const_merge(i);
            }
        }
        if (dagpcode[i].op == ARRLFC) {//c[b] = a
            if (!strcmp(dagpcode[i].a,tmpname)) {
                strcpy(dagpcode[i].a,value);
                //const_merge(i);
            }
            if (!strcmp(dagpcode[i].b,tmpname)) {
                strcpy(dagpcode[i].b,value);
                //const_merge(i);
            }
        }
        if (dagpcode[i].op == ARRRFC) {//c= a [b]

            if (!strcmp(dagpcode[i].b,tmpname)) {
                strcpy(dagpcode[i].b,value);
                //const_merge(i);
            }
        }

        i++;
    }
    //delete_dagpcode(front-1);

};

int strisnumber(char * str) {
    if (isdigit(str[0])) return 1;
    if ((str[0] == '+') ||  (str[0] == '-')) {
        if (isdigit(str[1])) return 1;
    }
    return 0;
};
void const_merge (int begin) {
    int tpa,tpb;
    int t1,t2;
    int res = 0;
    int i = begin;
    char pa[IDMAX],pb[IDMAX];
    char value[10]= {0};

    for (i = begin ; i < grear; i++) {
        strcpy(pa,dagpcode[i].a);
        strcpy(pb,dagpcode[i].b);
        tpa = searchtab(dagpcode[i].a);
        tpb = searchtab(dagpcode[i].b);

        //const replace orders as bne
        if (islgfc(dagpcode[i].op)) {// lgfc t1-t2
            if ((tpa >= 0) && (tab[tpa].obj == CONSTobj)) {// x = y + const
                sprintf(value,"%d",tab[tpa].adr);
                strcpy(dagpcode[i].a,value);
            }
            if ((tpb >= 0) && (tab[tpb].obj == CONSTobj)) {
                sprintf(value,"%d",tab[tpb].adr);
                strcpy(dagpcode[i].b,value);
            }//设计的mips生成和gp不需要这个//xiangcuole
        }

        if (dagpcode[i].op == ARRLFC) {// c[b] = a // c = a[b]
            if ((tpa >= 0) && (tab[tpa].obj == CONSTobj)) {// x = y + const
                sprintf(value,"%d",tab[tpa].adr);
                strcpy(dagpcode[i].a,value);
            }

        }

        // +-*/ merge
        if (isdag(dagpcode[i].op)) {
            if ((tpa >= 0) && (tab[tpa].obj == CONSTobj)) {// x = y + const
                sprintf(value,"%d",tab[tpa].adr);
                strcpy(dagpcode[i].a,value);
            }
            if ((tpb >= 0) && (tab[tpb].obj == CONSTobj)) {
                sprintf(value,"%d",tab[tpb].adr);
                strcpy(dagpcode[i].b,value);
            }

            if (//debug ch
                (((tpa >= 0) && (tab[tpa].obj == CONSTobj)) ||
                 (strisnumber(pa)) ||
                 (pa[0]  == '\''))
                &&
                (((tpb >= 0) && (tab[tpb].obj == CONSTobj)) ||
                 (strisnumber(pb)) ||
                 (pb[0]  == '\''))
                )
            {

                if (strisnumber(pa)) t1 = atoi(pa);
                else if (pa[0]  == '\'') t1 = (int)(pa[1]);
                else t1 = tab[tpa].adr;
                if (strisnumber(pb)) t2 = atoi(pb);
                else if (pb[0]  == '\'') t2 = (int)(pb[1]);
                else t2 = tab[tpb].adr;

                switch (dagpcode[i].op) {
                    case ASSIGNFC:break;
                    case PLUSFC:{
                        res = t1 + t2;
                        break;
                    }
                    case MINUSFC:{
                        res = t1 - t2;
                        break;
                    }
                    case TIMESFC:{
                        res = t1 * t2;
                        break;
                    }
                    case DIVFC:{
                        res = t1 / t2;
                        break;
                    }
                    default:break;
                }

                dagpcode[i].op = ASSIGNFC;
                sprintf(value,"%d",res);
                strcpy(dagpcode[i].a,value);
                strcpy(dagpcode[i].b,"0");
            }


        }//merge


        if  ((dagpcode[i].op == ASSIGNFC) &&
             (strisnumber(dagpcode[i].a)) &&
             (dagpcode[i].c[0] == '~') &&
             (dagpcode[i].c[1] == 't')) {//tmpvar = number //debug not old pa
            const_convey(i+1,dagpcode[i].c,dagpcode[i].a);



        }

    }

      for (i = begin ; i < grear; i++) {//dead code
          if  ((dagpcode[i].op == ASSIGNFC) &&
               (strisnumber(dagpcode[i].a)) &&
               (dagpcode[i].c[0] == '~') &&
               (dagpcode[i].c[1] == 't')) {
     if (!usetemp(i+1,dagpcode[i].c))
         delete_dagpcode(i);
          }
      }
};
int istempvar (char* name) {
    if ((name[0] == '~') && (name[1] == 't')) return 1;
    return 0;
};

void dedeadcode (int front) {
    int i = front;
    while (i <grear) {
        if ((dagpcode[i].op == ASSIGNFC) && (istempvar(dagpcode[i].c))) {
            if (!usetemp(i+1,dagpcode[i].c)) delete_dagpcode(i);
        }
        i++;
    }
};

void opt_minute (int front) {
    int i = front;
    while (i <grear) {
        //ret ret
        if (((dagpcode[i].op == RETFC) || (dagpcode[i].op == VRETFC)) &&
            ((dagpcode[i+1].op == RETFC) || (dagpcode[i+1].op == VRETFC))) delete_dagpcode(i+1);//debug
        //a = a



        //
        if (isdag(dagpcode[i].op))  {

              //a = a
            if ((dagpcode[i].op == ASSIGNFC) &&
                (!strcmp(dagpcode[i].a,dagpcode[i].c)) ) delete_dagpcode(i);

            else {// +-*/
                // x = a + 0 or 0 + a
                if (dagpcode[i].op == PLUSFC) {
                    if (strisnumber(dagpcode[i].a) && !(atoi(dagpcode[i].a))){
                        dagpcode[i].op = ASSIGNFC;
                        strcpy(dagpcode[i].a,dagpcode[i].b);
                    }
                    if (strisnumber(dagpcode[i].b) && !(atoi(dagpcode[i].b))){
                        dagpcode[i].op = ASSIGNFC;
                    }
                }
            }
        }

        i++;
    }
    i = front;
    dedeadcode(i);
};


//代码生成

int mrear = 0; //mips index
int initregflag = 0;


void update (char* name,reginf regs) {

    char tmpno[IDMAX] = {0};
    int tid;
    int tp = searchtab(name);


    if ((name[0] == '~') && (name[1] == 't')) {//tmpvar
        strncpy(tmpno,name+2,10);
        tid = atoi(tmpno);
        if ((tempvar[tid].sloc == REGLOC) && ((tempvar[tid].regs.regnum != regs.regnum) || (tempvar[tid].regs.regtyp != regs.regtyp)))///reg <- reg
            fprintf(tp_opt_mips,"addu $t%d, $0, $%c%d\n",
                    tempvar[tid].regs.regnum,regtyp[regs.regtyp],regs.regnum);//debug type

    }
    else if ((tp >= 0) && (tab[tp].obj == VARobj)){//var
        if ((tab[tp].regs.hasreg) && ((tab[tp].regs.regtyp != regs.regtyp) || (tab[tp].regs.regno != regs.regnum))) {///var is in reg //reg <- reg
            fprintf(tp_opt_mips,"addu $%c%d, $0, $%c%d\n",
                    regtyp[tab[tp].regs.regtyp],tab[tp].regs.regno,
                    regtyp[regs.regtyp],regs.regnum);
        }
        else {//var in mem // mem <- reg write back
            if (tab[tp].global) fprintf(tp_opt_mips,"sw $%c%d, %d($gp)\n",regtyp[regs.regtyp],regs.regnum,tab[tp].adr);
            else fprintf(tp_opt_mips,"sw $%c%d, %d($sp)\n",regtyp[regs.regtyp],regs.regnum,tab[tp].adr);
        }

    }
};
void update_treg (char *name, int tmpno) {
    int tp = searchtab(name);
    if (!((name[0] == '~') && (name[1] == 't'))) return;
    if (tempvar[tmpno].sloc != REGLOC) printf("****opt msg***** tmp is not in treg to update\n");
    //mem <- reg
    fprintf(tp_opt_mips,"sw $t%d, %d($sp)\n",tempvar[tmpno].regs.regnum,tab[tp].adr);
    treg[tempvar[tmpno].regs.regnum].alloc = 0;
    treg[tempvar[tmpno].regs.regnum].id = 0;
    tempvar[tmpno].sloc = MEMLOC;
    tempvar[tmpno].regs.regnum = -1;
    tempvar[tmpno].regs.regtyp = NREG;
};

void init_regstosave(int tabf) {
    int i = 0;
    while (i < SREGNUM) {
        sreg[i].save = 0;
        if (i < AREGNUM) areg[i].save = 0;
        i++;
    }
    i = 0;
    while (i < TREGNUM) {
        treg[i].save = 0;
        i++;
    }

    for (i = 0; i < 30; i++) {
        tab[tabf].savereg[i] = 0;
    }
};

void init_aregstosave () {
    int i = 0;
    while (i < AREGNUM){
        areg[i].save = 0;
    i++;
    }
};

int nextfunc(int begin) {
    int i = begin;
    while (i < trear) {
        if (tab[i].obj == FUNCobj) return i-1;
        i++;
    }
    return trear-1;
};
void saveregs (int tabf) {//stack
    int i = 0;
    int j;
    //int j = tabf;

        init_regstosave(tabf);
    while (i < TREGNUM) {//tregsave
        if (treg[i].alloc) {// treg is used, need to save //?id
            if (usetemp(prc,treg[i].name)) {//prc or prc+1???
                treg[i].save = 1;
                tab[tabf].savereg[7+i] = 1;

                fprintf(tp_opt_mips,"sw $t%d, %d($sp)\n",i,tab[tabf].adr+32+i*4);//save in stack
            }
        }
        i++;
    }
    i = 0;
    while (i < SREGNUM) {//sregsave

        if (sreg[i].alloc) {// treg is used, need to save //?id
           // if (usetemp(prc,treg[i].name)) {//prc or prc+1???

            j = searchtab(sreg[i].name);//global var
            if (tab[j].global)
                fprintf(tp_opt_mips,"sw $s%d, %d($gp)\n",i,tab[j].adr);//save///debug!!

                sreg[i].save = 1;
                tab[tabf].savereg[i] = 1;

            if (!tab[j].global)
                fprintf(tp_opt_mips,"sw $s%d, %d($sp)\n",i,tab[tabf].adr+i*4);//save in stack
           // }
        }
        i++;
    }

   /* j = nextfunc(j+1);
    while (j > tabf) {//sreg and areg
        if (tab[j].regs.hasreg) {
            if ((tab[j].regs.regtyp == SREG) || (tab[j].regs.regtyp == AREG)) {
                if (tab[j].regs.regtyp == SREG) {
                    sreg[tab[j].regs.regno].save = 1;
                    tab[tabf].savereg[tab[j].regs.regno] = 1;
                    fprintf(tp_opt_mips,"sw $%c%d, %d($sp)\n",regtyp[SREG],tab[j].regs.regno,tab[tabf].adr+tab[j].regs.regno*4);//save in stack
                }


            }
        }
        j--;
    }
    */
};

void save_areg (int n,int tabf) {


   areg[n].save = 1;
   tab[tabf].savereg[15+n] = 1;
    fprintf(tp_opt_mips,"sw $%c%d, %d($sp)\n",regtyp[AREG],n,tab[tabf].adr+64+n*4);//
//    fprintf(tp_opt_mips,"sw $%c%d, %d($sp)\n",regtyp[AREG],1,tab[tabf].adr+64+1*4);
//    fprintf(tp_opt_mips,"sw $%c%d, %d($sp)\n",regtyp[AREG],2,tab[tabf].adr+64+2*4);
//    fprintf(tp_opt_mips,"sw $%c%d, %d($sp)\n",regtyp[AREG],3,tab[tabf].adr+64+3*4);
};

void recoverregs (int tabf) {
    int i = 0;
    int j;
    while (i < TREGNUM) {
        if (treg[i].save) fprintf(tp_opt_mips,"lw $t%d, %d($sp)\n",i,tab[tabf].adr+32+i*4);//save in stack

        if (i < AREGNUM) {
            if (areg[i].save)
                fprintf(tp_opt_mips,"lw $a%d, %d($sp)\n",i,tab[tabf].adr+64+i*4);//save in stack
        }
        i++;
    }
    i = 0;
    while (i < SREGNUM) {


            if (sreg[i].save) {
                j = searchtab(sreg[i].name);//global var
                if (tab[j].global) {
                    fprintf(tp_opt_mips,"lw $s%d, %d($gp)\n",i,tab[j].adr);//save in stack
                }


                else fprintf(tp_opt_mips,"lw $s%d, %d($sp)\n",i,tab[tabf].adr+i*4);//save in stack
            }

        i++;
    }
};

void freereg(int typ, int no) {
    switch (typ) {
        case TREG:{
            treg[no].alloc =0;
            treg[no].id = 0;
            break;
        }
        case SREG:{
            sreg[no].alloc =0;
            sreg[no].id = 0;
            break;
        }
        case AREG:{
            areg[no].alloc =0;
            areg[no].id = 0;
            break;
        }
        default:break;
    }
};

void create_opt_mips (int index) {
    char funcname[IDMAX] = {0};
    int k;
    reginf a,b,c,t;
    idinf ida = {0,0,0},idb = {0,0,0},idc = {0,0,0};
    prc = index;
    int tpa,tpb,tpc,op,i;
    char pa[IDMAX],pb[IDMAX],pc[IDMAX];
    op = dagpcode[index].op;
    strcpy(pa,dagpcode[index].a);
    strcpy(pb,dagpcode[index].b);
    strcpy(pc,dagpcode[index].c);

    switch (op) {
        case SWITCHFC:break;//?
        case NOPFC:break;
        case LGFC:break;

        case PARAFC: {
            tpc = searchtab(pc);//func
            tpb = searchtab(pb);//id
            if (usevar(prc,pb)) {
                if (tab[tpb].paranum <= 3) {
                    if (tab[tpb].regs.hasreg) {//not happened
                        fprintf(tp_opt_mips,"addu $%c%d, $0, $a%d\n",
                                regtyp[tab[tpb].regs.regtyp],tab[tpb].regs.regno,
                                tab[tpb].paranum);
                         areg[tab[tpb].paranum].alloc = 0;//?
                    }
                    else {
                        tab[tpb].regs.hasreg = 1;
                        tab[tpb].regs.regtyp = AREG;
                        tab[tpb].regs.regno = tab[tpb].paranum;

                        areg[tab[tpb].paranum].alloc = 1;//debugfx


                    }
                }
                else {
                    if (tab[tpb].regs.hasreg) {//not happened
                        fprintf(tp_opt_mips,"lw $%c%d, %d($sp)\n",
                                regtyp[tab[tpb].regs.regtyp],tab[tpb].regs.regno,
                                tab[tpb].adr);
                    }
                    else {
                        //已经存在adr里
                    }
                }
            }

            break;
        }

        case PUSHFC: {//lw addr, lw para, sw para// a0-a4
            int cnt;
            tpc = searchtab(pc);//func
            tpa = searchtab(pa);//para
            cnt = atoi(pb);//cnt

            if (cnt == 0) init_aregstosave();//debug

            initregflag = 1;

            if (tpa < 0) {//number and char
                if (tab[tpc].paranum <= 4) {


                    if (areg[cnt].alloc == 1)
                       save_areg(cnt,curfunc);

                    tab[tpa].regs.hasreg = 1;
                    tab[tpa].regs.regtyp = AREG;
                    tab[tpa].regs.regno = cnt;
                    areg[cnt].alloc = 1;
                    if (strisnumber(pa))
                        fprintf(tp_opt_mips,"addiu $a%d, $0, %d\n",cnt,atoi(pa));
                    else  fprintf(tp_opt_mips,"addiu $a%d, $0, %d\n",cnt,(int)(pa[1]));
                }
                else {
                    if (cnt <= 3) {

                        if (areg[cnt].alloc == 1) save_areg(cnt,tpc);

                        tab[tpa].regs.hasreg = 1;
                        tab[tpa].regs.regtyp = AREG;
                        tab[tpa].regs.regno = cnt;
                        areg[cnt].alloc = 1;

                        if (strisnumber(pa))
                            fprintf(tp_opt_mips,"addiu $a%d, $0, %d\n",cnt,atoi(pa));
                        else  fprintf(tp_opt_mips,"addiu $a%d, $0, %d\n",cnt,(int)(pa[1]));

                    }
                    else {
                        fprintf(tp_opt_mips,"addiu $t9, $sp, %d\n",-(tab[tpc].adr+80+4-cnt*4));//func base
                        //fprintf( tp_opt_mips,"add $t1, $t1, $t0\n");//address
                        if (strisnumber(pa)) {
                            fprintf(tp_opt_mips,"li $t8, %d\n",atoi(pa));//debug
                            fprintf(tp_opt_mips,"sw $t8, 0($t9)\n");
                        }

                           // fprintf(tp_opt_mips,"sw %d, 0($t9)\n",atoi(pa));//sw
                        else  {
                            fprintf(tp_opt_mips,"li $t8, %d\n",(int)(pa[1]));//debug
                            fprintf(tp_opt_mips,"sw $t8, 0($t9)\n");
                        }
                        //fprintf(tp_opt_mips,"sw %d, 0($t9)\n",(int)(pa[1]));//sw

                    }
                }
            }

            else {//push id
                strcpy(ida.name,pa);
                ida.obj = tab[tpa].obj;
                ida.op = PUSHFC;
                a = alloc_regs(ida);



                if (tab[tpc].paranum <= 4) {

                    if (areg[cnt].alloc == 1) save_areg(cnt,curfunc);

                    tab[tpa].regs.hasreg = 1;
                    tab[tpa].regs.regtyp = AREG;
                    tab[tpa].regs.regno = cnt;
                    areg[cnt].alloc = 1;

                    if (a.regnum < 0) {//var in mem//??
                        if (tab[tpa].global) fprintf(tp_opt_mips,"lw $a%d, %d($gp)\n",cnt,tab[tpa].adr);
                        else fprintf(tp_opt_mips,"lw $a%d, %d($sp)\n",cnt,tab[tpa].adr);
                    }
                    else  fprintf(tp_opt_mips,"addu $a%d, $0, $%c%d\n",cnt,regtyp[a.regtyp],a.regnum);

                    //fprintf(tp_opt_mips,"addu $a%d, $0, $%c%d\n",cnt,regtyp[a.regtyp],a.regnum);
                }
                else {
                    if (cnt <= 3) {

                        if (areg[cnt].alloc == 1) save_areg(cnt,curfunc);

                        tab[tpa].regs.hasreg = 1;
                        tab[tpa].regs.regtyp = AREG;
                        tab[tpa].regs.regno = cnt;
                        areg[cnt].alloc = 1;

                        if (a.regnum < 0) {//var in mem//??
                            if (tab[tpa].global) fprintf(tp_opt_mips,"lw $a%d, %d($gp)\n",cnt,tab[tpa].adr);
                            else fprintf(tp_opt_mips,"lw $a%d, %d($sp)\n",cnt,tab[tpa].adr);
                        }
                        else  fprintf(tp_opt_mips,"addu $a%d, $0, $%c%d\n",cnt,regtyp[a.regtyp],a.regnum);
                        //fprintf(tp_opt_mips,"addu $a%d, $0, $%c%d\n",cnt,regtyp[a.regtyp],a.regnum);

                    }
                    else {
                        fprintf(tp_opt_mips,"addiu $t9, $sp, %d\n",-(tab[tpc].adr+80+4-cnt*4));//func base
                        //fprintf( tp_opt_mips,"add $t1, $t1, $t0\n");//address

                        if (a.regnum < 0) {//var in mem//??
                            if (tab[tpa].global) fprintf(tp_opt_mips,"lw $t8, %d($gp)\n",tab[tpa].adr);
                            else fprintf(tp_opt_mips,"lw $t8, %d($sp)\n",tab[tpa].adr);
                            fprintf(tp_opt_mips,"sw $t8, 0($t9)\n");//sw
                        }
                        else
                            fprintf(tp_opt_mips,"sw $%c%d, 0($t9)\n",regtyp[a.regtyp],a.regnum);//sw

                    }
                }
            }

            //push [id] [空]
            break;
        }

        case SASCENEFC: {


            saveregs(curfunc);

            fprintf(tp_opt_mips,"addiu $sp, $sp, -4\n");
            fprintf(tp_opt_mips,"sw $ra, 0($sp)\n");//save
            break;
        }
        case OPSTACKFC: {
            tpa = searchtab(pa);
            fprintf(tp_opt_mips,"addiu $sp, $sp, %d\n",-(tab[tpa].adr+20*4));//stack
            break;
        }
        case CALLFC: {// savecur instack call outstack retrive
            tpa = searchtab(pa);//funcname
            char func[IDMAX]={"_f\0"};
            strcat(pa,func);

            fprintf(tp_opt_mips,"jal %s\n",pa);//call

            break;

            //call [id] [空]
            break;
        }
        case RESTACKFC: {
            tpa = searchtab(pa);
            fprintf(tp_opt_mips,"addiu $sp, $sp, %d\n",tab[tpa].adr+20*4);//stack
            break;
        }

        case RESCENEFC: {
            fprintf(tp_opt_mips,"lw $ra, 0($sp)\n");
            fprintf(tp_opt_mips,"addiu $sp, $sp, 4\n");//re

            recoverregs(curfunc);

            break;
        }

        case FUNCFC: {//label:(function name)


            fprintf(tp_opt_mips,"%s:\n",pa);//rename once debug
            for (k = 0; k <IDMAX; k++) {
                if ((pa[k] == '_') && (pa[k+1] == 'f') && (pa[k+2] == '\0')) break;
            }
            strncpy(funcname,pa,k);//without_f
            tpa = searchtab(funcname);

            curfunc = tpa;
            i = tpa+1;

            /*for (i = 0; i< tab[tpa].paranum; i++) {
             update();
             }*/
            /*while (i < trear) {
             if (tab[i].obj == FUNCobj) break;
             i++;
             }
             while (i > tpa) {
             if (tab[i].regs.hasreg)// local var //reg <- mem

             fprintf(tp_opt_mips,"lw $%c%d, %d($sp)\n",
             regtyp[tab[i].regs.regtyp],tab[i].regs.regno,
             tab[i].adr);//re
             i--;
             }*///???
            break;
        }

        case VRETFC: {
            writeback_sreg();
            if (!strcmp(pa, "main")) fprintf(tp_opt_mips,"j END\n");//main func
            else fprintf(tp_opt_mips,"jr $ra\n");

            break;
        }
        case FRETFC: {////[id] = RET //temp

            tpa = searchtab(pa);
            t.regtyp = VREG;
            t.regnum = 0;

            strcpy(ida.name,pa);
            if ((tpa < 0) && (strisnumber(pa))) ida.obj = CONSTobj;//is a number
            else ida.obj = tab[tpa].obj;
            ida.op = RETFC;
            a = alloc_regs(ida);

            fprintf(tp_opt_mips,"addu $%c%d, $0, $v0 \n",regtyp[a.regtyp],a.regnum);
            //update(pa,t);//debug
            writeback_sreg();
            //[id] = RET
            break;
        }
        case RETFC: {//ret exp// is temp
            if (!strcmp(pa, " ")) {//void func
                if (!strcmp(pb, "main")) fprintf(tp_opt_mips,"j END\n");//main func
                else fprintf(tp_opt_mips,"jr $ra\n");
            }
            else {//return func
                tpa = searchtab(pa);

                strcpy(ida.name,pa);
                if ((tpa < 0) && (strisnumber(pa))) ida.obj = CONSTobj;//is a number
                else ida.obj = tab[tpa].obj;
                ida.op = RETFC;
                a = alloc_regs(ida);

                //? a alloc v0
                fprintf(tp_opt_mips,"addu $v0, $0, $%c%d\n",regtyp[a.regtyp],a.regnum);

                writeback_sreg();
                fprintf(tp_opt_mips,"jr $ra\n");
            }
            //save_regs();//???

            break;
        }
        case ARRLFC: {//c[b] = a //lw t0 b, lw t1 c,sw t2 to c[b]
            tpc = searchtab(pc);//t1
            tpa = searchtab(pa);//t2
            tpb = searchtab(pb);//t0 int

            //index b
            if ((tpb < 0) && (strisnumber(pb))) {//is a number

                fprintf(tp_opt_mips,"addiu $t8, $0, %d\n",atoi(pb)*4);//index in t8
                //fprintf(tp_opt_mips,"sll $t8, $t8, 2\n");//amend offset in t8
            }
            else {
                strcpy(idb.name,pb);
                idb.obj = tab[tpb].obj;
                idb.op = ARRLFC;
                b = alloc_regs(idb);//index

                if (b.regnum < 0) {//var in mem//??
                    if (tab[tpb].global)
                        fprintf(tp_opt_mips,"lw $t8, %d($gp)\n",tab[tpb].adr);
                    else fprintf(tp_opt_mips,"lw $t8, %d($sp)\n",tab[tpb].adr);
                }
                else  fprintf(tp_opt_mips,"addu $t8, $0, $%c%d\n",
                              regtyp[b.regtyp],b.regnum);//index in t8


               // fprintf(tp_opt_mips,"addu $t8, $0, $%c%d\n", regtyp[b.regtyp],b.regnum);//index in t8
                fprintf(tp_opt_mips,"sll $t8, $t8, 2\n");//amend offset in t8
            }

            //array
             fprintf(tp_opt_mips,"li $t9, %d\n",tab[tpc].adr);//array base lic t9

            //value
            if (tpa < 0) {
                if (strisnumber(pa)) {//is a number
                    if  (tab[tpc].global) {
                        fprintf(tp_opt_mips,"subu $t9, $t9, $t8\n");
                        fprintf(tp_opt_mips,"addu $t9, $t9, $gp\n");//debug
                        fprintf(tp_opt_mips,"li $t8, %d\n",atoi(pa));//debug
                        fprintf(tp_opt_mips,"sw $t8, 0($t9)\n");

                    }
                    else {
                        fprintf(tp_opt_mips,"addu $t9, $t9, $t8\n");
                        fprintf(tp_opt_mips,"addu $t9, $t9, $sp\n");
                        fprintf(tp_opt_mips,"li $t8, %d\n",atoi(pa));//debug
                        fprintf(tp_opt_mips,"sw $t8, 0($t9)\n");
                    }
                }
                else  {//ch
                    if  (tab[tpc].global) {
                        fprintf(tp_opt_mips,"subu $t9, $t9, $t8\n");
                        fprintf(tp_opt_mips,"addu $t9, $t9, $gp\n");//debug
                        fprintf(tp_opt_mips,"li $t8, %d\n",(int)(pa[1]));//debug
                        fprintf(tp_opt_mips,"sw $t8, 0($t9)\n");


                    }
                    else {
                        fprintf(tp_opt_mips,"addu $t9, $t9, $t8\n");
                        fprintf(tp_opt_mips,"addu $t9, $t9, $sp\n");
                        fprintf(tp_opt_mips,"li $t8, %d\n",(int)(pa[1]));//debug
                        fprintf(tp_opt_mips,"sw $t8, 0($t9)\n");
                    }
                }
            }


            else {
                strcpy(ida.name,pa);
                ida.obj = tab[tpa].obj;
                ida.op = ARRLFC;
                a = alloc_regs(ida);//value a





                if  (tab[tpc].global) {
                    fprintf(tp_opt_mips,"subu $t9, $t9, $t8\n");
                    fprintf(tp_opt_mips,"addu $t9, $t9, $gp\n");//debug


                    if (a.regnum < 0) {//var in mem//??
                        if (tab[tpa].global) fprintf(tp_opt_mips,"lw $t8, %d($gp)\n",tab[tpa].adr);
                        else fprintf(tp_opt_mips,"lw $t8, %d($sp)\n",tab[tpa].adr);
                        fprintf(tp_opt_mips,"sw $t8, 0($t9)\n");
                    }
                    else fprintf(tp_opt_mips,"sw $%c%d, 0($t9)\n",regtyp[a.regtyp],a.regnum);

                   // fprintf(tp_opt_mips,"sw $%c%d, 0($t9)\n",regtyp[a.regtyp],a.regnum);

                }
                else {
                    fprintf(tp_opt_mips,"addu $t9, $t9, $t8\n");
                    fprintf(tp_opt_mips,"addu $t9, $t9, $sp\n");

                    if (a.regnum < 0) {//var in mem//??
                        if (tab[tpa].global) fprintf(tp_opt_mips,"lw $t8, %d($gp)\n",tab[tpa].adr);
                        else fprintf(tp_opt_mips,"lw $t8, %d($sp)\n",tab[tpa].adr);
                        fprintf(tp_opt_mips,"sw $t8, 0($t9)\n");
                    }
                    else fprintf(tp_opt_mips,"sw $%c%d, 0($t9)\n",regtyp[a.regtyp],a.regnum);

                   // fprintf(tp_opt_mips,"sw $%c%d, 0($t9)\n",regtyp[a.regtyp],a.regnum);
                }
            }


            break;

        }
        case ARRRFC: {// c = a[b] //lw t0 b, lw t1 a,lw t3 a[b], sw t3
            tpc = searchtab(pc);//t2
            tpa = searchtab(pa);//t1
            tpb = searchtab(pb);//t0 int

            //index b
            if ((tpb < 0) && (strisnumber(pb))) {//is a number

                fprintf(tp_opt_mips,"addiu $t8, $0, %d\n",atoi(pb));//index in t8
                fprintf(tp_opt_mips,"sll $t8, $t8, 2\n");//amend offset in t8
            }
            else {
                strcpy(idb.name,pb);
                idb.obj = tab[tpb].obj;
                idb.op = ARRLFC;
                b = alloc_regs(idb);//index

                if (b.regnum < 0) {//var in mem//??
                    if (tab[tpb].global)
                        fprintf(tp_opt_mips,"lw $t8, %d($gp)\n",tab[tpb].adr);
                    else fprintf(tp_opt_mips,"lw $t8, %d($sp)\n",tab[tpb].adr);
                }
                else  fprintf(tp_opt_mips,"addu $t8, $0, $%c%d\n",
                              regtyp[b.regtyp],b.regnum);//index in t8


               // fprintf(tp_opt_mips,"addu $t8, $0, $%c%d\n", regtyp[b.regtyp],b.regnum);//index in t8
                fprintf(tp_opt_mips,"sll $t8, $t8, 2\n");//amend offset in t8
            }


            //target c
            strcpy(idc.name,pc);
            if ((tpc < 0) && (isdigit(atoi(pc)))) idc.obj = CONSTobj;//is a number
            else idc.obj = tab[tpc].obj;
            idc.op = ARRRFC;
            c = alloc_regs(idc);//target


            //array
            fprintf(tp_opt_mips,"li $t9, %d\n",tab[tpa].adr);//array base lic t9

            //save in c
            if  (tab[tpa].global) {//debug
                fprintf(tp_opt_mips,"subu $t9, $t9, $t8\n");
                fprintf(tp_opt_mips,"addu $t9, $t9, $gp\n");

                if (c.regnum < 0) {//var in mem//??
                    fprintf(tp_opt_mips,"lw $t8, 0($t9)\n");
                    t.regnum = 8;
                    t.regtyp = TREG;
                    update(pc,t);

                }
                else {
                    fprintf(tp_opt_mips,"lw $%c%d, 0($t9)\n",regtyp[c.regtyp],c.regnum);
                    update(pc,c);
                }


            }
            else {
                fprintf(tp_opt_mips,"addu $t9, $t9, $t8\n");
                fprintf(tp_opt_mips,"addu $t9, $t9, $sp\n");

                if (c.regnum < 0) {//var in mem//??
                    fprintf(tp_opt_mips,"lw $t8, 0($t9)\n");
                    t.regnum = 8;
                    t.regtyp = TREG;
                    update(pc,t);

                }
                else {
                    fprintf(tp_opt_mips,"lw $%c%d, 0($t9)\n",regtyp[c.regtyp],c.regnum);
                    update(pc,c);
                }

                //fprintf(tp_opt_mips,"lw $%c%d, 0($t9)\n",regtyp[c.regtyp],c.regnum);
            }

           // update(pc,c);

            break;

        }

        case ASSIGNFC: {// lw $t0 from p1, sw $t0 to p2
            tpa = searchtab(pa);// 'a' numberstr exp(temp var) const
            tpc = searchtab(pc);//int char array temp

            strcpy(idc.name,pc);
            if ((tpc < 0) && (isdigit(atoi(pc)))) idc.obj = CONSTobj;//is a number
            else idc.obj = tab[tpc].obj;
            idc.op = ASSIGNFC;
            c = alloc_regs(idc);


            if ((tpa < 0) && (pa[0] == '\'')) { //'a' [ch]

                if (c.regnum < 0) {
                    fprintf(tp_opt_mips,"li $t8, %d\n",
                            (int)(pa[1]));//ascii
                    if (tab[tpc].global)
                        fprintf(tp_opt_mips,"sw $t8, %d($gp)\n",
                                tab[tpc].adr);//ascii
                    else
                        fprintf(tp_opt_mips,"sw $t8, %d($sp)\n",
                                tab[tpc].adr);//ascii
                }


               else
                   fprintf(tp_opt_mips,"li $%c%d, %d\n",
                        regtyp[c.regtyp],c.regnum,(int)(pa[1]));//ascii
                //update(pc,t);
            }
            else if ((tpa < 0) && (strisnumber(pa))) {//debug -x
                //fprintf(tp_opt_mips,"li $t9, %d\n",atoi(pa));//number
                //t.regnum = 9;
                //t.regtyp = TREG;

                if (c.regnum < 0) {
                    fprintf(tp_opt_mips,"li $t8, %d\n",
                           atoi(pa));//ascii
                    if (tab[tpc].global)
                        fprintf(tp_opt_mips,"sw $t8, %d($gp)\n",
                                tab[tpc].adr);//ascii
                    else
                        fprintf(tp_opt_mips,"sw $t8, %d($sp)\n",
                                tab[tpc].adr);//ascii
                }


                else
                    fprintf(tp_opt_mips,"li $%c%d, %d\n",
                        regtyp[c.regtyp],c.regnum,atoi(pa));//number
                //update(pc,t);
            }
            else {
                strcpy(ida.name,pa);
                ida.obj = tab[tpa].obj;
                ida.op = ASSIGNFC;
                a = alloc_regs(ida);

                if (a.regnum < 0) {
                    if (tab[tpa].global)
                        fprintf(tp_opt_mips,"lw $t9, %d($gp)\n",
                                tab[tpa].adr);
                    else
                        fprintf(tp_opt_mips,"lw $t9, %d($sp)\n",
                            tab[tpa].adr);
                    t.regnum = 9;
                    t.regtyp = TREG;
                    update(pc,t);
                }
                else update(pc,a);
            }


            break;
        }
        case PLUSFC: {// lw t0, lw t1, add t2 t0 t1, sw t2
            tpc = searchtab(pc);//t2
            tpa = searchtab(pa);//t0
            tpb = searchtab(pb);//t1
            int t1 = 0, t2 = 0;
            strcpy(idc.name,pc);
            if ((tpc < 0) && (isdigit(atoi(pc)))) idc.obj = CONSTobj;//is a number
            else idc.obj = tab[tpc].obj;
            idc.op = MINUSFC;
            c = alloc_regs(idc);

            if (c.regnum < 0) {

                c.regnum = 9;
                c.regtyp = TREG;
            }

            int flag1 = 0,flag2 = 0;

            if (tpa < 0) {
                flag1 = 1;
                if ( strisnumber(pa)) {//number
                    t1 = atoi(pa);
                }
                else {//ch
                    t1 = (int)(pa[1]);
                }
            }

            else {
                strcpy(ida.name,pa);
                ida.obj = tab[tpa].obj;
                ida.op = BNEFC;
                a = alloc_regs(ida);

                if (a.regnum < 0) {
                    if (tab[tpa].global)
                        fprintf(tp_opt_mips,"lw $t8, %d($gp)\n",
                                tab[tpa].adr);
                    else
                        fprintf(tp_opt_mips,"lw $t8, %d($sp)\n",
                                tab[tpa].adr);
                    a.regnum = 8;
                    a.regtyp = TREG;
                }
            }


            if (tpb < 0) {
                flag2 = 1;
                if ( strisnumber(pb) ) {//number
                    t2 = atoi(pb);
                }
                else {//ch
                    t2 = (int)(pb[1]);
                }
            }
            else {
                strcpy(idb.name,pb);
                idb.obj = tab[tpb].obj;
                idb.op = BNEFC;
                b = alloc_regs(idb);

                if (b.regnum < 0) {
                    if (tab[tpb].global)
                        fprintf(tp_opt_mips,"lw $t9, %d($gp)\n",
                                tab[tpb].adr);
                    else
                        fprintf(tp_opt_mips,"lw $t9, %d($sp)\n",
                                tab[tpb].adr);
                    b.regnum = 9;
                    b.regtyp = TREG;
                }
            }

            if (flag1) {
                flag1 = 0;

                fprintf(tp_opt_mips,"addiu $%c%d, $%c%d, %d\n",
                        regtyp[c.regtyp],c.regnum,
                        regtyp[b.regtyp],b.regnum,
                        t1);

            }
            else {
                if (flag2) {
                    flag2 = 0;
                    fprintf(tp_opt_mips,"addiu $%c%d, $%c%d, %d\n",
                            regtyp[c.regtyp],c.regnum,
                            regtyp[a.regtyp],a.regnum,
                            t2);
                }
                else fprintf(tp_opt_mips,"addu $%c%d, $%c%d, $%c%d\n",
                             regtyp[c.regtyp],c.regnum,
                             regtyp[a.regtyp],a.regnum,
                             regtyp[b.regtyp],b.regnum);
            }
            update(pc,c);

            break;
        }
        case MINUSFC: {// lw t0, lw t1, sub t2 t0 t1, sw t2
            tpc = searchtab(dagpcode[index].c);//t2
            tpa = searchtab(dagpcode[index].a);//t0
            tpb = searchtab(dagpcode[index].b);//t1

            strcpy(idc.name,pc);
            if ((tpc < 0) && (isdigit(atoi(pc)))) idc.obj = CONSTobj;//is a number
            else idc.obj = tab[tpc].obj;
            idc.op = MINUSFC;
            c = alloc_regs(idc);

            if (c.regnum < 0) {

                c.regnum = 9;
                c.regtyp = TREG;
            }

            int flag1 = 0,flag2 = 0;

            int t1 = 0, t2 = 0;
            if (tpa < 0) {
                flag1 = 1;
                if ( strisnumber(pa)) {//number
                    t1 = atoi(pa);
                }
                else {//ch
                    t1 = (int)(pa[1]);
                }
            }

            else {
                strcpy(ida.name,pa);
                ida.obj = tab[tpa].obj;
                ida.op = BNEFC;
                a = alloc_regs(ida);

                if (a.regnum < 0) {
                    if (tab[tpa].global)
                        fprintf(tp_opt_mips,"lw $t8, %d($gp)\n",
                                tab[tpa].adr);
                    else
                        fprintf(tp_opt_mips,"lw $t8, %d($sp)\n",
                                tab[tpa].adr);
                    a.regnum = 8;
                    a.regtyp = TREG;
                }
            }


            if (tpb < 0) {
                flag2 = 1;
                if ( strisnumber(pb) ) {//number
                    t2 = atoi(pb);
                }
                else {//ch
                    t2 = (int)(pb[1]);
                }
            }
            else {
                strcpy(idb.name,pb);
                idb.obj = tab[tpb].obj;
                idb.op = BNEFC;
                b = alloc_regs(idb);

                if (b.regnum < 0) {
                    if (tab[tpb].global)
                        fprintf(tp_opt_mips,"lw $t9, %d($gp)\n",
                                tab[tpb].adr);
                    else
                        fprintf(tp_opt_mips,"lw $t9, %d($sp)\n",
                                tab[tpb].adr);
                    b.regnum = 9;
                    b.regtyp = TREG;
                }
            }

            if (flag1) {
                flag1 = 0;
                if (atoi(dagpcode[index].a) == 0) {
                    fprintf(tp_opt_mips,"subu $%c%d, $0, $%c%d\n",
                            regtyp[c.regtyp],c.regnum,
                            regtyp[b.regtyp],b.regnum);
                }
                else {//debug
                    fprintf(tp_opt_mips,"subu $%c%d, $0, $%c%d\n",
                            regtyp[c.regtyp],c.regnum,
                            regtyp[b.regtyp],b.regnum);
                    fprintf(tp_opt_mips,"addiu $%c%d, $%c%d, %d\n",
                            regtyp[c.regtyp],c.regnum,
                            regtyp[c.regtyp],c.regnum,t1);
                }


            }
            else {
                if (flag2) {
                    flag2 = 0;
                    t2 = -t2;
                    fprintf(tp_opt_mips,"addiu $%c%d, $%c%d, %d\n",
                            regtyp[c.regtyp],c.regnum,
                            regtyp[a.regtyp],a.regnum,
                            t2);
                }
                else fprintf(tp_opt_mips,"subu $%c%d, $%c%d, $%c%d\n",
                             regtyp[c.regtyp],c.regnum,
                             regtyp[a.regtyp],a.regnum,
                             regtyp[b.regtyp],b.regnum);
            }

            update(pc,c);


            break;
        }
        case TIMESFC: {// lw t0, lw t1, mult, mflo
            tpc = searchtab(pc);//t2
            tpa = searchtab(pa);//t0
            tpb = searchtab(pb);//t1

            int flag1 = 0,flag2 = 0;
            int t1 = 0, t2 = 0;
            if (tpa < 0) {
                flag1 = 1;
                if ( strisnumber(pa)) {//number

                    t1 = atoi(pa);
                }
                else {//ch
                    t1 = (int)(pa[1]);
                }
                 fprintf(tp_opt_mips,"li $t8, %d\n",t1);
            }

            else {
                strcpy(ida.name,pa);
                ida.obj = tab[tpa].obj;
                ida.op = BNEFC;
                a = alloc_regs(ida);

                if (a.regnum < 0) {
                    if (tab[tpa].global)
                        fprintf(tp_opt_mips,"lw $t8, %d($gp)\n",
                                tab[tpa].adr);
                    else
                        fprintf(tp_opt_mips,"lw $t8, %d($sp)\n",
                                tab[tpa].adr);
                    a.regnum = 8;
                    a.regtyp = TREG;
                }
            }


            if (tpb < 0) {
                flag2 = 1;
                if ( strisnumber(pb) ) {//number
                    t2 = atoi(pb);
                }
                else {//ch
                    t2 = (int)(pb[1]);
                }
                fprintf(tp_opt_mips,"li $t9, %d\n",t2);
            }
            else {
                strcpy(idb.name,pb);
                idb.obj = tab[tpb].obj;
                idb.op = BNEFC;
                b = alloc_regs(idb);

                if (b.regnum < 0) {
                    if (tab[tpb].global)
                        fprintf(tp_opt_mips,"lw $t9, %d($gp)\n",
                                tab[tpb].adr);
                    else
                        fprintf(tp_opt_mips,"lw $t9, %d($sp)\n",
                                tab[tpb].adr);
                    b.regnum = 9;
                    b.regtyp = TREG;
                }
            }


            if (flag1) {
                flag1 = 0;
                if (flag2) {
                    flag2 = 0;
                    fprintf(tp_opt_mips,"multu $t8, $t9\n");
                    //bne rs,rt,LABEL(offset)
                }
                else  fprintf(tp_opt_mips,"multu $t8, $%c%d\n",regtyp[b.regtyp],b.regnum);
                //bne rs,rt,LABEL(offset)
            }
            else {
                if (flag2) {
                    flag2 = 0;
                    fprintf(tp_opt_mips,"multu $%c%d, $t9\n",regtyp[a.regtyp],a.regnum);
                    //bne rs,rt,LABEL(offset)
                }
                else fprintf(tp_opt_mips,"multu $%c%d, $%c%d\n",
                             regtyp[a.regtyp],a.regnum,
                             regtyp[b.regtyp],b.regnum);
                //bne rs,rt,LABEL(offset)
            }

            strcpy(idc.name,pc);
            if ((tpc < 0) && (isdigit(atoi(pc)))) idc.obj = CONSTobj;//is a number
            else idc.obj = tab[tpc].obj;
            idc.op = TIMESFC;
            c = alloc_regs(idc);

            if (c.regnum < 0) {

                c.regnum = 9;
                c.regtyp = TREG;
            }

            fprintf(tp_opt_mips,"mflo $t9\n");//mul t2,t0,t1//mflo t9
            t.regnum = 9;
            t.regtyp = TREG;

            fprintf(tp_opt_mips,"addu $%c%d, $0, $t9\n",
                    regtyp[c.regtyp],c.regnum);//debug type

            update(pc,t);///????pc not c


            break;

        }
        case DIVFC: {
            tpc = searchtab(dagpcode[index].c);//t2
            tpa = searchtab(dagpcode[index].a);//t0
            tpb = searchtab(dagpcode[index].b);//t1

            int flag1 = 0,flag2 = 0;
            int t1 = 0, t2 = 0;
            if (tpa < 0) {
                flag1 = 1;
                if ( strisnumber(pa)) {//number

                    t1 = atoi(pa);
                }
                else {//ch
                    t1 = (int)(pa[1]);
                }
                fprintf(tp_opt_mips,"li $t8, %d\n",t1);
            }

            else {
                strcpy(ida.name,pa);
                ida.obj = tab[tpa].obj;
                ida.op = BNEFC;
                a = alloc_regs(ida);

                if (a.regnum < 0) {
                    if (tab[tpa].global)
                        fprintf(tp_opt_mips,"lw $t8, %d($gp)\n",
                                tab[tpa].adr);
                    else
                        fprintf(tp_opt_mips,"lw $t8, %d($sp)\n",
                                tab[tpa].adr);
                    a.regnum = 8;
                    a.regtyp = TREG;
                }
            }


            if (tpb < 0) {
                flag2 = 1;
                if ( strisnumber(pb) ) {//number
                    t2 = atoi(pb);
                }
                else {//ch
                    t2 = (int)(pb[1]);
                }
                fprintf(tp_opt_mips,"li $t9, %d\n",t2);
            }
            else {
                strcpy(idb.name,pb);
                idb.obj = tab[tpb].obj;
                idb.op = BNEFC;
                b = alloc_regs(idb);

                if (b.regnum < 0) {
                    if (tab[tpb].global)
                        fprintf(tp_opt_mips,"lw $t9, %d($gp)\n",
                                tab[tpb].adr);
                    else
                        fprintf(tp_opt_mips,"lw $t9, %d($sp)\n",
                                tab[tpb].adr);
                    b.regnum = 9;
                    b.regtyp = TREG;
                }
            }

            if (flag1) {
                flag1 = 0;
                if (flag2) {
                    flag2 = 0;
                    fprintf(tp_opt_mips,"div $t8, $t9\n");
                    //bne rs,rt,LABEL(offset)
                }
                else  fprintf(tp_opt_mips,"div $t8, $%c%d\n",regtyp[b.regtyp],b.regnum);
                //bne rs,rt,LABEL(offset)
            }
            else {
                if (flag2) {
                    flag2 = 0;
                    fprintf(tp_opt_mips,"div $%c%d, $t9\n",regtyp[a.regtyp],a.regnum);
                    //bne rs,rt,LABEL(offset)
                }
                else fprintf(tp_opt_mips,"div $%c%d, $%c%d\n",
                             regtyp[a.regtyp],a.regnum,
                             regtyp[b.regtyp],b.regnum);
                //bne rs,rt,LABEL(offset)
            }

            strcpy(idc.name,pc);
            if ((tpc < 0) && (isdigit(atoi(pc)))) idc.obj = CONSTobj;//is a number
            else idc.obj = tab[tpc].obj;
            idc.op = DIVFC;
            c = alloc_regs(idc);

            if (c.regnum < 0) {

                c.regnum = 9;
                c.regtyp = TREG;
            }

            fprintf(tp_opt_mips,"mflo $t9\n");//mul t2,t0,t1//mflo t9
            t.regnum = 9;
            t.regtyp = TREG;
            update(pc,t);///????pc not c

            break;
        }
        case SCANFFC: {

            tpa = searchtab(dagpcode[index].a);// var
            t.regnum = 0;
            t.regtyp = VREG;
            if (tab[tpa].typ == CHARtyp) {
                fprintf(tp_opt_mips,"li $v0 12\n");//read char in v0
                fprintf(tp_opt_mips,"syscall\n");
            }
            else if (tab[tpa].typ == INTtyp) {
                fprintf(tp_opt_mips,"li $v0 5\n");//read integer in v0
                fprintf(tp_opt_mips,"syscall\n");
            }
            update(pa,t);
            break;
        }
        case PRINTFFC: {// a0, syscall//temp?
            tpa = searchtab(pa);// temp var const

            if (areg[0].alloc)
                fprintf(tp_opt_mips,"addu $t8,$0,$a0\n");//t8 save a0

            strcpy(ida.name,pa);
            if ((tpa < 0) && (strisnumber(pa))) {
                fprintf(tp_opt_mips,"li $a0, %d\n",atoi(pa));
            }
            else {
                ida.obj = tab[tpa].obj;
                ida.op = PRINTFFC;
                a = alloc_regs(ida);

                fprintf(tp_opt_mips,"addu $a0, $0, $%c%d\n",regtyp[a.regtyp],a.regnum);
            }

            if ((tpa >= 0) && (tab[tpa].typ == CHARtyp)) {
                fprintf(tp_opt_mips,"li $v0, 11\n");//write char in a0
                fprintf(tp_opt_mips,"syscall\n");

            }
            else  {
                fprintf(tp_opt_mips,"li $v0, 1\n");//write int in a0
                fprintf(tp_opt_mips,"syscall\n");
            }
            //  else printf("error at mips SCANF, variable type\n");

            //!最后可以不要
            fprintf(tp_opt_mips,"li $a0, 10\n");//\n ascii is 10
            fprintf(tp_opt_mips,"li $v0, 11\n");//write \n
            fprintf(tp_opt_mips,"syscall\n");

            if (areg[0].alloc)
                fprintf(tp_opt_mips,"addu $a0,$0,$t8\n");//t8 recover a0
            break;
        }
        case PRINTFSTRFC: {
            if (areg[0].alloc)
                fprintf(tp_opt_mips,"addu $t8,$0,$a0\n");//t8 save a0

            fprintf(tp_opt_mips,".data\n");
            fprintf(tp_opt_mips,"str_%s: .asciiz \"%s\"\n",pa,dagpcode[index].str);
            fprintf(tp_opt_mips,".text\n");
            fprintf(tp_opt_mips,"la $a0, str_%s\n",pa);
            fprintf(tp_opt_mips,"li $v0, 4\n");//write str in a0
            fprintf(tp_opt_mips,"syscall\n");
            free(dagpcode[index].str);

            //最后可以不要！！！
            fprintf(tp_opt_mips,"li $a0, 10\n");//\n ascii is 10
            fprintf(tp_opt_mips,"li $v0, 11\n");//write \n
            fprintf(tp_opt_mips,"syscall\n");

            if (areg[0].alloc)
                fprintf(tp_opt_mips,"addu $a0,$0,$t8\n");//t8 recover a0
            break;
        }
        case CASEFC : {//is temp//?
            tpa = searchtab(pa);
            //tpb = searchtab(dagpcode[index].b);

            strcpy(ida.name,pa);
            if ((tpa < 0) && (strisnumber(pa))) ida.obj = CONSTobj;//is a number
            else ida.obj = tab[tpa].obj;
            ida.op = CASEFC;
            a = alloc_regs(ida);

            if (dagpcode[index].b[0] == '\''){// 'a' [ch]
                fprintf(tp_opt_mips,"li $t9, %d\n",(int)(pb[1]));//ascii
                fprintf(tp_opt_mips,"bne $%c%d, $t9, %s\n",regtyp[a.regtyp],a.regnum,pc);
                //bne rs,rt,LABEL(offset)

            }
            else {//number
                fprintf(tp_opt_mips,"li $t9, %d\n",atoi(pb));//ascii
                fprintf(tp_opt_mips,"bne $%c%d, $t9, %s\n",
                        regtyp[a.regtyp],a.regnum,pc);
                //bne rs,rt,LABEL(offset)
            }

            break;
        }
        case BNEFC: {

            tpa = searchtab(dagpcode[index].a);
            tpb = searchtab(dagpcode[index].b);

            int flag1 = 0,flag2 = 0;
            if ((tpa < 0) && (strisnumber(pa))) {//number
                fprintf(tp_opt_mips,"li $t8, %d\n",atoi(dagpcode[index].a));
                flag1 = 1;
            }
            else if ((tpa < 0) && (dagpcode[index].a[0] == '\'')){//'a' [ch]
                fprintf(tp_opt_mips,"li $t8, %d\n",(int)(dagpcode[index].a[1]));//ascii
                flag1 = 1;
            }
            else {
                strcpy(ida.name,pa);
                ida.obj = tab[tpa].obj;
                ida.op = BNEFC;
                a = alloc_regs(ida);

                if (a.regnum < 0) {
                    if (tab[tpa].global)
                        fprintf(tp_opt_mips,"lw $t8, %d($gp)\n",
                                tab[tpa].adr);
                    else
                        fprintf(tp_opt_mips,"lw $t8, %d($sp)\n",
                                tab[tpa].adr);
                    a.regnum = 8;
                    a.regtyp = TREG;
                }
            }

            if ((tpb < 0) && (strisnumber(pb))) {//number
                fprintf(tp_opt_mips,"li $t9, %d\n",atoi(dagpcode[index].b));
                flag2 = 1;
            }
            else if ((tpb < 0) && (dagpcode[index].b[0] == '\'')){//'a' [ch]
                fprintf(tp_opt_mips,"li $t9, %d\n",(int)(dagpcode[index].b[1]));//ascii
                flag2 = 1;
            }
            else {
                strcpy(idb.name,pb);
                idb.obj = tab[tpb].obj;
                idb.op = BNEFC;
                b = alloc_regs(idb);

                if (b.regnum < 0) {
                    if (tab[tpb].global)
                        fprintf(tp_opt_mips,"lw $t9, %d($gp)\n",
                                tab[tpb].adr);
                    else
                        fprintf(tp_opt_mips,"lw $t9, %d($sp)\n",
                                tab[tpb].adr);
                    b.regnum = 9;
                    b.regtyp = TREG;
                }
            }


            if (flag1) {
                flag1 = 0;
                if (flag2) {
                    flag2 = 0;
                    fprintf(tp_opt_mips,"beq $t8, $t9, %s\n",pc);
                    //bne rs,rt,LABEL(offset)
                }
                else  fprintf(tp_opt_mips,"beq $t8, $%c%d, %s\n",regtyp[b.regtyp],b.regnum,pc);
                //bne rs,rt,LABEL(offset)
            }
            else {
                if (flag2) {
                    flag2 = 0;
                    fprintf(tp_opt_mips,"beq $%c%d, $t9, %s\n",regtyp[a.regtyp],a.regnum,pc);
                    //bne rs,rt,LABEL(offset)
                }
                else fprintf(tp_opt_mips,"beq $%c%d, $%c%d, %s\n",
                             regtyp[a.regtyp],a.regnum,
                             regtyp[b.regtyp],b.regnum,pc);
                //bne rs,rt,LABEL(offset)
            }
            break;
        }
        case BEQFC: {
            tpa = searchtab(dagpcode[index].a);// temp var
            tpb = searchtab(dagpcode[index].b);

            int flag1 = 0,flag2 = 0;
            if ((tpa < 0) && (strisnumber(pa))) {//number
                fprintf(tp_opt_mips,"li $t8, %d\n",atoi(dagpcode[index].a));
                flag1 = 1;
            }
            else if ((tpa < 0) && (dagpcode[index].a[0] == '\'')){//'a' [ch]
                fprintf(tp_opt_mips,"li $t8, %d\n",(int)(dagpcode[index].a[1]));//ascii
                flag1 = 1;
            }
            else {
                strcpy(ida.name,pa);
                ida.obj = tab[tpa].obj;
                ida.op = BNEFC;
                a = alloc_regs(ida);


                if (a.regnum < 0) {
                    if (tab[tpa].global)
                        fprintf(tp_opt_mips,"lw $t8, %d($gp)\n",
                                tab[tpa].adr);
                    else
                        fprintf(tp_opt_mips,"lw $t8, %d($sp)\n",
                                tab[tpa].adr);
                    a.regnum = 8;
                    a.regtyp = TREG;
                }
            }

            if ((tpb < 0) && (strisnumber(pb))) {//number
                fprintf(tp_opt_mips,"li $t9, %d\n",atoi(dagpcode[index].b));
                flag2 = 1;
            }
            else if ((tpb < 0) && (dagpcode[index].b[0] == '\'')){//'a' [ch]
                fprintf(tp_opt_mips,"li $t9, %d\n",(int)(dagpcode[index].b[1]));//ascii
                flag2 = 1;
            }
            else {
                strcpy(idb.name,pb);
                idb.obj = tab[tpb].obj;
                idb.op = BNEFC;
                b = alloc_regs(idb);

                if (b.regnum < 0) {
                    if (tab[tpb].global)
                        fprintf(tp_opt_mips,"lw $t9, %d($gp)\n",
                                tab[tpb].adr);
                    else
                        fprintf(tp_opt_mips,"lw $t9, %d($sp)\n",
                                tab[tpb].adr);
                    b.regnum = 9;
                    b.regtyp = TREG;
                }
            }


            if (flag1) {
                flag1 = 0;
                if (flag2) {
                    flag2 = 0;
                    fprintf(tp_opt_mips,"bne $t8, $t9, %s\n",pc);
                    //bne rs,rt,LABEL(offset)
                }
                else  fprintf(tp_opt_mips,"bne $t8, $%c%d, %s\n",regtyp[b.regtyp],b.regnum,pc);
                //bne rs,rt,LABEL(offset)
            }
            else {
                if (flag2) {
                    flag2 = 0;
                    fprintf(tp_opt_mips,"bne $%c%d, $t9, %s\n",regtyp[a.regtyp],a.regnum,pc);
                    //bne rs,rt,LABEL(offset)
                }
                else fprintf(tp_opt_mips,"bne $%c%d, $%c%d, %s\n",
                             regtyp[a.regtyp],a.regnum,
                             regtyp[b.regtyp],b.regnum,pc);
                //bne rs,rt,LABEL(offset)
            }

            break;
        }
        case LESFC: {
            tpa = searchtab(dagpcode[index].a);// temp var
            tpb = searchtab(dagpcode[index].b);

            int flag1 = 0,flag2 = 0;
            if ((tpa < 0) && (strisnumber(pa))) {//number
                fprintf(tp_opt_mips,"li $t8, %d\n",atoi(dagpcode[index].a));
                flag1 = 1;
            }
            else if ((tpa < 0) && (dagpcode[index].a[0] == '\'')){//'a' [ch]
                fprintf(tp_opt_mips,"li $t8, %d\n",(int)(dagpcode[index].a[1]));//ascii
                flag1 = 1;
            }
            else {
                strcpy(ida.name,pa);
                ida.obj = tab[tpa].obj;
                ida.op = BNEFC;
                a = alloc_regs(ida);


                if (a.regnum < 0) {
                    if (tab[tpa].global)
                        fprintf(tp_opt_mips,"lw $t8, %d($gp)\n",
                                tab[tpa].adr);
                    else
                        fprintf(tp_opt_mips,"lw $t8, %d($sp)\n",
                                tab[tpa].adr);
                    a.regnum = 8;
                    a.regtyp = TREG;
                }
            }

            if ((tpb < 0) && (strisnumber(pb))) {//number
                fprintf(tp_opt_mips,"li $t9, %d\n",atoi(dagpcode[index].b));
                flag2 = 1;
            }
            else if ((tpb < 0) && (dagpcode[index].b[0] == '\'')){//'a' [ch]
                fprintf(tp_opt_mips,"li $t9, %d\n",(int)(dagpcode[index].b[1]));//ascii
                flag2 = 1;
            }
            else {
                strcpy(idb.name,pb);
                idb.obj = tab[tpb].obj;
                idb.op = BNEFC;
                b = alloc_regs(idb);

                if (b.regnum < 0) {
                    if (tab[tpb].global)
                        fprintf(tp_opt_mips,"lw $t9, %d($gp)\n",
                                tab[tpb].adr);
                    else
                        fprintf(tp_opt_mips,"lw $t9, %d($sp)\n",
                                tab[tpb].adr);
                    b.regnum = 9;
                    b.regtyp = TREG;
                }
            }


            if (flag1) {
                flag1 = 0;
                if (flag2) {
                    flag2 = 0;
                    fprintf(tp_opt_mips,"subu $t9, $t8, $t9\n");//0
                }
                else fprintf(tp_opt_mips,"subu $t9, $t8, $%c%d\n",
                             regtyp[b.regtyp],b.regnum);//0
                //bne rs,rt,LABEL(offset)
            }
            else {
                if (flag2) {
                    flag2 = 0;
                    fprintf(tp_opt_mips,"subu $t9, $%c%d, $t9\n",
                            regtyp[a.regtyp],a.regnum);//0
                }
                else fprintf(tp_opt_mips,"subu $t9, $%c%d, $%c%d\n",
                             regtyp[a.regtyp],a.regnum,
                             regtyp[b.regtyp],b.regnum);//0

            }

            fprintf(tp_opt_mips,"bgez $t9, %s\n",pc);//
            //bne rs,rt,LABEL(offset)
            break;
        }
        case GRTFC: {
            tpa = searchtab(dagpcode[index].a);// temp var
            tpb = searchtab(dagpcode[index].b);

            int flag1 = 0,flag2 = 0;
            if ((tpa < 0) && (strisnumber(pa))) {//number
                fprintf(tp_opt_mips,"li $t8, %d\n",atoi(dagpcode[index].a));
                flag1 = 1;
            }
            else if ((tpa < 0) && (dagpcode[index].a[0] == '\'')){//'a' [ch]
                fprintf(tp_opt_mips,"li $t8, %d\n",(int)(dagpcode[index].a[1]));//ascii
                flag1 = 1;
            }
            else {
                strcpy(ida.name,pa);
                ida.obj = tab[tpa].obj;
                ida.op = BNEFC;
                a = alloc_regs(ida);

                if (a.regnum < 0) {
                    if (tab[tpa].global)
                        fprintf(tp_opt_mips,"lw $t8, %d($gp)\n",
                                tab[tpa].adr);
                    else
                        fprintf(tp_opt_mips,"lw $t8, %d($sp)\n",
                                tab[tpa].adr);
                    a.regnum = 8;
                    a.regtyp = TREG;
                }
            }

            if ((tpb < 0) && (strisnumber(pb))) {//number
                fprintf(tp_opt_mips,"li $t9, %d\n",atoi(dagpcode[index].b));
                flag2 = 1;
            }
            else if ((tpb < 0) && (dagpcode[index].b[0] == '\'')){//'a' [ch]
                fprintf(tp_opt_mips,"li $t9, %d\n",(int)(dagpcode[index].b[1]));//ascii
                flag2 = 1;
            }
            else {
                strcpy(idb.name,pb);
                idb.obj = tab[tpb].obj;
                idb.op = BNEFC;
                b = alloc_regs(idb);

                if (b.regnum < 0) {
                    if (tab[tpb].global)
                        fprintf(tp_opt_mips,"lw $t9, %d($gp)\n",
                                tab[tpb].adr);
                    else
                        fprintf(tp_opt_mips,"lw $t9, %d($sp)\n",
                                tab[tpb].adr);
                    b.regnum = 9;
                    b.regtyp = TREG;
                }
            }


            if (flag1) {
                flag1 = 0;
                if (flag2) {
                    flag2 = 0;
                    fprintf(tp_opt_mips,"subu $t9, $t8, $t9\n");//0
                }
                else fprintf(tp_opt_mips,"subu $t9, $t8, $%c%d\n",
                             regtyp[b.regtyp],b.regnum);//0
                //bne rs,rt,LABEL(offset)
            }
            else {
                if (flag2) {
                    flag2 = 0;
                    fprintf(tp_opt_mips,"subu $t9, $%c%d, $t9\n",
                            regtyp[a.regtyp],a.regnum);//0
                }
                else fprintf(tp_opt_mips,"subu $t9, $%c%d, $%c%d\n",
                             regtyp[a.regtyp],a.regnum,
                             regtyp[b.regtyp],b.regnum);//0

            }

            fprintf(tp_opt_mips,"blez $t9, %s\n",pc);//bltz rs,offset
            //bne rs,rt,LABEL(offset)
            break;
        }
        case GEQFC: {
            tpa = searchtab(dagpcode[index].a);// temp var
            tpb = searchtab(dagpcode[index].b);

            int flag1 = 0,flag2 = 0;
            if ((tpa < 0) && (strisnumber(pa))) {//number
                fprintf(tp_opt_mips,"li $t8, %d\n",atoi(dagpcode[index].a));
                flag1 = 1;
            }
            else if ((tpa < 0) && (dagpcode[index].a[0] == '\'')){//'a' [ch]
                fprintf(tp_opt_mips,"li $t8, %d\n",(int)(dagpcode[index].a[1]));//ascii
                flag1 = 1;
            }
            else {
                strcpy(ida.name,pa);
                ida.obj = tab[tpa].obj;
                ida.op = BNEFC;
                a = alloc_regs(ida);

                if (a.regnum < 0) {
                    if (tab[tpa].global)
                        fprintf(tp_opt_mips,"lw $t8, %d($gp)\n",
                                tab[tpa].adr);
                    else
                        fprintf(tp_opt_mips,"lw $t8, %d($sp)\n",
                                tab[tpa].adr);
                    a.regnum = 8;
                    a.regtyp = TREG;
                }
            }

            if ((tpb < 0) && (strisnumber(pb))) {//number
                fprintf(tp_opt_mips,"li $t9, %d\n",atoi(dagpcode[index].b));
                flag2 = 1;
            }
            else if ((tpb < 0) && (dagpcode[index].b[0] == '\'')){//'a' [ch]
                fprintf(tp_opt_mips,"li $t9, %d\n",(int)(dagpcode[index].b[1]));//ascii
                flag2 = 1;
            }
            else {
                strcpy(idb.name,pb);
                idb.obj = tab[tpb].obj;
                idb.op = BNEFC;
                b = alloc_regs(idb);

                if (b.regnum < 0) {
                    if (tab[tpb].global)
                        fprintf(tp_opt_mips,"lw $t9, %d($gp)\n",
                                tab[tpb].adr);
                    else
                        fprintf(tp_opt_mips,"lw $t9, %d($sp)\n",
                                tab[tpb].adr);
                    b.regnum = 9;
                    b.regtyp = TREG;
                }
            }


            if (flag1) {
                flag1 = 0;
                if (flag2) {
                    flag2 = 0;
                    fprintf(tp_opt_mips,"subu $t9, $t8, $t9\n");//0
                }
                else fprintf(tp_opt_mips,"subu $t9, $t8, $%c%d\n",
                             regtyp[b.regtyp],b.regnum);//0
                //bne rs,rt,LABEL(offset)
            }
            else {
                if (flag2) {
                    flag2 = 0;
                    fprintf(tp_opt_mips,"subu $t9, $%c%d, $t9\n",
                            regtyp[a.regtyp],a.regnum);//0
                }
                else fprintf(tp_opt_mips,"subu $t9, $%c%d, $%c%d\n",
                             regtyp[a.regtyp],a.regnum,
                             regtyp[b.regtyp],b.regnum);//0

            }


            fprintf(tp_opt_mips,"bltz $t9, %s\n",pc);//bltz rs,offset
            //bne rs,rt,LABEL(offset)
            break;
        }
        case LEQFC: {
            tpa = searchtab(dagpcode[index].a);// temp var
            tpb = searchtab(dagpcode[index].b);

            int flag1 = 0,flag2 = 0;
            if ((tpa < 0) && (strisnumber(pa))) {//number
                fprintf(tp_opt_mips,"li $t8, %d\n",atoi(dagpcode[index].a));
                flag1 = 1;
            }
            else if ((tpa < 0) && (dagpcode[index].a[0] == '\'')){//'a' [ch]
                fprintf(tp_opt_mips,"li $t8, %d\n",(int)(dagpcode[index].a[1]));//ascii
                flag1 = 1;
            }
            else {
                strcpy(ida.name,pa);
                ida.obj = tab[tpa].obj;
                ida.op = BNEFC;
                a = alloc_regs(ida);

                if (a.regnum < 0) {
                    if (tab[tpa].global)
                        fprintf(tp_opt_mips,"lw $t8, %d($gp)\n",
                                tab[tpa].adr);
                    else
                        fprintf(tp_opt_mips,"lw $t8, %d($sp)\n",
                                tab[tpa].adr);
                    a.regnum = 8;
                    a.regtyp = TREG;
                }
            }

            if ((tpb < 0) && (strisnumber(pb))) {//number
                fprintf(tp_opt_mips,"li $t9, %d\n",atoi(dagpcode[index].b));
                flag2 = 1;
            }
            else if ((tpb < 0) && (dagpcode[index].b[0] == '\'')){//'a' [ch]
                fprintf(tp_opt_mips,"li $t9, %d\n",(int)(dagpcode[index].b[1]));//ascii
                flag2 = 1;
            }
            else {
                strcpy(idb.name,pb);
                idb.obj = tab[tpb].obj;
                idb.op = BNEFC;
                b = alloc_regs(idb);

                if (b.regnum < 0) {
                    if (tab[tpb].global)
                        fprintf(tp_opt_mips,"lw $t9, %d($gp)\n",
                                tab[tpb].adr);
                    else
                        fprintf(tp_opt_mips,"lw $t9, %d($sp)\n",
                                tab[tpb].adr);
                    b.regnum = 9;
                    b.regtyp = TREG;
                }
            }


            if (flag1) {
                flag1 = 0;
                if (flag2) {
                    flag2 = 0;
                    fprintf(tp_opt_mips,"subu $t9, $t8, $t9\n");//0
                }
                else fprintf(tp_opt_mips,"subu $t9, $t8, $%c%d\n",
                             regtyp[b.regtyp],b.regnum);//0
                //bne rs,rt,LABEL(offset)
            }
            else {
                if (flag2) {
                    flag2 = 0;
                    fprintf(tp_opt_mips,"subu $t9, $%c%d, $t9\n",
                            regtyp[a.regtyp],a.regnum);//0
                }
                else fprintf(tp_opt_mips,"subu $t9, $%c%d, $%c%d\n",
                             regtyp[a.regtyp],a.regnum,
                             regtyp[b.regtyp],b.regnum);//0

            }


            fprintf(tp_opt_mips,"bgtz $t9, %s\n",pc);//bltz rs,offset
            //bne rs,rt,LABEL(offset)
            break;
        }
        case JUMPFC: {
            fprintf(tp_opt_mips,"j %s\n",pc);
            //j label
            break;
        }
        case LABELFC: {
            fprintf(tp_opt_mips,"%s :\n",pa);
            //Label_1:
            break;
        }


        default: {
            fprintf(tp_opt_mips,"error at print mips: invalid op\n");
        }

    }


};



void create_dag_mips (int index) {
    int tpa,tpb,tpc,op;
    char pa[IDMAX],pb[IDMAX],pc[IDMAX];
    op = dagpcode[index].op;
    strcpy(pa,dagpcode[index].a);
    strcpy(pb,dagpcode[index].b);
    strcpy(pc,dagpcode[index].c);

    switch (op) {
        case LGFC: {
            //fprintf(kp_pcode,"%s %s %s\n",pcode[px].a,pcode[px].c,pcode[px].b);
            //[exp] LGSY [exp]
            break;
        }
        case VRETFC: {
            if (!strcmp(pa, "main")) fprintf(tp_dag_mips,"j END\n");//main func
            else fprintf(tp_dag_mips,"jr $ra\n");
            break;
        }

        case CALLFC: {// savecur instack call outstack retrive
            tpa = searchtab(pa);
            char func[IDMAX]={"_f\0"};
            strcat(pa,func);
            //fprintf(tp_dag_mips,"subi $sp, $sp, %d\n",tab[tpa].adr);//stack
            fprintf(tp_dag_mips,"jal %s\n",pa);//call
            //fprintf(tp_dag_mips,"addi $sp, $sp, %d\n",tab[tpa].adr);//stack
            break;

            //call [id] [空]
            break;
        }
        case RESTACKFC: {
            tpa = searchtab(pa);
            fprintf(tp_dag_mips,"addiu $sp, $sp, %d\n",tab[tpa].adr+80);//stack
            break;
        }
        case OPSTACKFC: {
            tpa = searchtab(pa);
            fprintf(tp_dag_mips,"addiu $sp, $sp, %d\n",-(tab[tpa].adr+80));//stack
            break;
        }
        case SASCENEFC: {
            fprintf(tp_dag_mips,"addiu $sp, $sp, -4\n");
            fprintf(tp_dag_mips,"sw $ra, 0($sp)\n");//save
            break;
        }
        case RESCENEFC: {
            fprintf(tp_dag_mips,"lw $ra, 0($sp)\n");
            fprintf(tp_dag_mips,"addiu $sp, $sp, 4\n");//re
            break;
        }
        case FUNCFC: {//label:(function name)//instack
            fprintf(tp_dag_mips,"%s:\n",pa);//rename once debug
            //tpa = searchtab(pa);//func
            //fprintf(tp_dag_mips,"subi $sp, $sp, %d\n",tab[tpa].adr);//stack
            //func_[name]:

            break;
        }
        case PARAFC: {//?
            //fprintf(kp_pcode,"para %s %s\n",pcode[px].a,pcode[px].b);
            //para [type] [id]
            break;
        }
        case PUSHFC: {//lw addr, lw para, sw para
            int cnt;
            tpc = searchtab(pc);//func
            tpa = searchtab(pa);//para
            cnt = atoi(pb);//cnt
            fprintf(tp_dag_mips,"li $t0, %d\n",cnt);
            fprintf( tp_dag_mips,"sll $t0, $t0, 2\n");//offset
            fprintf(tp_dag_mips,"addiu $t1, $sp, -4\n");//sp
            fprintf(tp_dag_mips,"addiu $t1, $t1, %d\n",-(tab[tpc].adr+80));//func base
            fprintf( tp_dag_mips,"addu $t1, $t1, $t0\n");//address

            if (tab[tpa].obj != CONSTobj) {//para
                if  (tab[tpa].global) {
                    fprintf(tp_dag_mips,"lw $t2, %d($gp)\n",tab[tpa].adr);
                }
                else fprintf(tp_dag_mips,"lw $t2, %d($sp)\n",tab[tpa].adr);
            }
            else fprintf(tp_dag_mips,"li $t2, %d\n",tab[tpa].adr);

            fprintf(tp_dag_mips,"sw $t2, 0($t1)\n");//sw
            //push [id] [空]
            break;
        }

        case FRETFC: {//
            tpa = searchtab(pa);

            if  (tab[tpa].global) {
                fprintf(tp_dag_mips,"sw $v0, %d($gp)\n",tab[tpa].adr);
            }
            else fprintf(tp_dag_mips,"sw $v0, %d($sp)\n",tab[tpa].adr);
            //[id] = RET
            break;
        }
        case RETFC: {
            if (!strcmp(pa, " ")) {//void func
                if (!strcmp(pb, "main")) fprintf(tp_dag_mips,"j END\n");//main func
                else fprintf(tp_dag_mips,"jr $ra\n");
            }
            else {//return func
                tpa = searchtab(pa);
                if (tab[tpa].obj != CONSTobj) {//offset
                    if  (tab[tpa].global) {
                        fprintf(tp_dag_mips,"lw $t0, %d($gp)\n",tab[tpa].adr);
                    }
                    else fprintf(tp_dag_mips,"lw $t0, %d($sp)\n",tab[tpa].adr);
                }
                else fprintf(tp_dag_mips,"li $t0, %d\n",tab[tpa].adr);

                fprintf(tp_dag_mips,"move $v0, $t0\n");
                fprintf(tp_dag_mips,"jr $ra\n");
            }
            break;
        }
        case ARRLFC: {//lw t0 b, lw t1 c,sw t2 to c[b]
            tpc = searchtab(pc);//t1
            tpa = searchtab(pa);//t2
            tpb = searchtab(pb);//t0 int
            if (tpb < 0) {
                if (pb[0] == '\'') {//'a' [ch]
                    fprintf(tp_dag_mips,"li $t0, %d\n",(int)(pb[1]));//ascii
                }
                else fprintf(tp_dag_mips,"li $t0, %d\n",atoi(pb));//crtnum_str to num
            }
            else {
            if (tab[tpb].obj != CONSTobj) {//offset
                if  (tab[tpb].global) {
                    fprintf(tp_dag_mips,"lw $t0, %d($gp)\n",tab[tpb].adr);
                }
                else fprintf(tp_dag_mips,"lw $t0, %d($sp)\n",tab[tpb].adr);
            }
            else fprintf(tp_dag_mips,"li $t0, %d\n",tab[tpb].adr);
            }

            fprintf(tp_dag_mips,"sll $t0, $t0, 2\n");//amend offset

            if (tpa < 0) {
                if (pa[0] == '\'') {//'a' [ch]
                    fprintf(tp_dag_mips,"li $t2, %d\n",(int)(pa[1]));//ascii
                }
                else fprintf(tp_dag_mips,"li $t2, %d\n",atoi(pa));//crtnum_str to num
            }

            else {
            if (tab[tpa].obj != CONSTobj) {//assign value
                if  (tab[tpa].global) {
                    fprintf(tp_dag_mips,"lw $t2, %d($gp)\n",tab[tpa].adr);
                }
                else fprintf(tp_dag_mips,"lw $t2, %d($sp)\n",tab[tpa].adr);
            }
            else fprintf(tp_dag_mips,"li $t2, %d\n",tab[tpa].adr);
            }

            fprintf(tp_dag_mips,"li $t1, %d\n",tab[tpc].adr);//array base lic

            if  (tab[tpc].global) {
                fprintf(tp_dag_mips,"subu $t3, $t1, $t0\n");
                fprintf(tp_dag_mips,"addu $t3, $t3, $gp\n");//debug
                fprintf(tp_dag_mips,"sw $t2, 0($t3)\n");

            }
            else {
                fprintf(tp_dag_mips,"addu $t3, $t1, $t0\n");
                fprintf(tp_dag_mips,"addu $t3, $t3, $sp\n");
                fprintf(tp_dag_mips,"sw $t2, 0($t3)\n");//debug
            }


            break;

        }
        case ARRRFC: {//lw t0 b, lw t1 a,lw t3 a[b], sw t3
            tpc = searchtab(pc);//t2
            tpa = searchtab(pa);//t1
            tpb = searchtab(pb);//t0 int
            if (tpb < 0) {
                if (pb[0] == '\'') {//'a' [ch]
                    fprintf(tp_dag_mips,"li $t0, %d\n",(int)(pb[1]));//ascii
                }
                else fprintf(tp_dag_mips,"li $t0, %d\n",atoi(pb));//crtnum_str to num
            }
            else {
            if (tab[tpb].obj != CONSTobj) {//exp offset
                if  (tab[tpb].global) {
                    fprintf(tp_dag_mips,"lw $t0 %d($gp)\n",tab[tpb].adr);
                }
                else fprintf(tp_dag_mips,"lw $t0 %d($sp)\n",tab[tpb].adr);

            }
            else fprintf(tp_dag_mips,"li $t0, %d\n",tab[tpb].adr);
            }
            fprintf(tp_dag_mips,"sll $t0, $t0, 2\n");//amend offset

            fprintf(tp_dag_mips,"li $t1, %d\n",tab[tpa].adr);//array base lic

            if  (tab[tpa].global) {//debug
                fprintf(tp_dag_mips,"subu $t2, $t1, $t0\n");
                fprintf(tp_dag_mips,"addu $t2, $t2, $gp\n");
                fprintf(tp_dag_mips,"lw $t3, 0($t2)\n");//debug

            }
            else {
                fprintf(tp_dag_mips,"addu $t2, $t1, $t0\n");
                fprintf(tp_dag_mips,"addu $t2, $t2, $sp\n");
                fprintf(tp_dag_mips,"lw $t3, 0($t2)\n");
            }





            if (tab[tpc].global) {
                fprintf(tp_dag_mips,"sw $t3, %d($gp)\n",tab[tpc].adr);
            }
            else {
                fprintf(tp_dag_mips,"sw $t3, %d($sp)\n",tab[tpc].adr);
            }

            break;

        }

        case ASSIGNFC: {// lw $t0 from p1, sw $t0 to p2
            tpa = searchtab(pa);// 'a' numberstr exp(temp var) const
            tpc = searchtab(pc);//int char array temp
            // if (tpc < 0) printf("error at mips ASSIGNFC, no variable in tab\n");
            // if (tab[tpc].obj != VARobj) printf("error at mips ASSIGNFC, not variable\n");
            if (tpa < 0) {
                if (pa[0] == '\'') {//'a' [ch]
                    fprintf(tp_dag_mips,"li $t0, %d\n",(int)(pa[1]));//ascii
                }
                else fprintf(tp_dag_mips,"li $t0, %d\n",atoi(pa));//crtnum_str to num
            }
            else {//const var
                if (tab[tpa].obj != CONSTobj) {
                    if  (tab[tpa].global) {
                        fprintf(tp_dag_mips,"lw $t0 %d($gp)\n",tab[tpa].adr);
                    }
                    else fprintf(tp_dag_mips,"lw $t0 %d($sp)\n",tab[tpa].adr);

                }
                else fprintf(tp_dag_mips,"li $t0, %d\n",tab[tpa].adr);

            }


            if (tab[tpc].global) {
                fprintf(tp_dag_mips,"sw $t0 %d($gp)\n",tab[tpc].adr);
            }
            else {
                fprintf(tp_dag_mips,"sw $t0 %d($sp)\n",tab[tpc].adr);
            }

            break;
        }
        case PLUSFC: {// lw t0, lw t1, add t2 t0 t1, sw t2

            tpc = searchtab(pc);//t2
            tpa = searchtab(pa);//t0
            tpb = searchtab(pb);//t1

            if (tpa < 0) {
                if (pa[0] == '\'') {//'a' [ch]
                    fprintf(tp_dag_mips,"li $t0, %d\n",(int)(pa[1]));//ascii
                }
                else fprintf(tp_dag_mips,"li $t0, %d\n",atoi(pa));//crtnum_str to num
            }
            else {
                if (tab[tpa].obj != CONSTobj) {// tmpvar var const
                    if  (tab[tpa].global) {
                        fprintf(tp_dag_mips,"lw $t0 %d($gp)\n",tab[tpa].adr);
                    }
                    else fprintf(tp_dag_mips,"lw $t0 %d($sp)\n",tab[tpa].adr);

                }
                else fprintf(tp_dag_mips,"li $t0, %d\n",tab[tpa].adr);
            }
            if (tpb < 0) {
                if (pb[0] == '\'') {//'a' [ch]
                    fprintf(tp_dag_mips,"li $t1, %d\n",(int)(pb[1]));//ascii
                }
                else fprintf(tp_dag_mips,"li $t1, %d\n",atoi(pb));//crtnum_str to num
            }
            else {
                if (tab[tpb].obj != CONSTobj) {
                    if  (tab[tpb].global) {
                        fprintf(tp_dag_mips,"lw $t1 %d($gp)\n",tab[tpb].adr);
                    }
                    else fprintf(tp_dag_mips,"lw $t1 %d($sp)\n",tab[tpb].adr);

                }
                else fprintf(tp_dag_mips,"li $t1, %d\n",tab[tpb].adr);
            }
            fprintf(tp_dag_mips,"addu $t2, $t0, $t1\n");//


            if (tab[tpc].global) {
                fprintf(tp_dag_mips,"sw $t2 %d($gp)\n",tab[tpc].adr);//debug
            }
            else {
                fprintf(tp_dag_mips,"sw $t2 %d($sp)\n",tab[tpc].adr);
            }

            break;
        }
        case MINUSFC: {// lw t0, lw t1, sub t2 t0 t1, sw t2
            tpc = searchtab(pc);//t2
            tpa = searchtab(pa);//t0
            tpb = searchtab(pb);//t1
            if (tpa < 0) {
                if (pa[0] == '\'') {//'a' [ch]
                    fprintf(tp_dag_mips,"li $t0, %d\n",(int)(pa[1]));//ascii
                }
                else fprintf(tp_dag_mips,"li $t0, %d\n",atoi(pa));//crtnum_str to num
            }
            else {
                if (tab[tpa].obj != CONSTobj) {// tmpvar var const
                    if  (tab[tpa].global) {
                        fprintf(tp_dag_mips,"lw $t0 %d($gp)\n",tab[tpa].adr);
                    }
                    else fprintf(tp_dag_mips,"lw $t0 %d($sp)\n",tab[tpa].adr);

                }
                else fprintf(tp_dag_mips,"li $t0, %d\n",tab[tpa].adr);
            }
            if (tpb < 0) {
                if (pb[0] == '\'') {//'a' [ch]
                    fprintf(tp_dag_mips,"li $t1, %d\n",(int)(pb[1]));//ascii
                }
                else fprintf(tp_dag_mips,"li $t1, %d\n",atoi(pb));//crtnum_str to num
            }
            else {
                if (tab[tpb].obj != CONSTobj) {
                    if  (tab[tpb].global) {
                        fprintf(tp_dag_mips,"lw $t1 %d($gp)\n",tab[tpb].adr);
                    }
                    else fprintf(tp_dag_mips,"lw $t1 %d($sp)\n",tab[tpb].adr);

                }
                else fprintf(tp_dag_mips,"li $t1, %d\n",tab[tpb].adr);
            }

            fprintf(tp_dag_mips,"sub $t2, $t0, $t1\n");//


            if (tab[tpc].global) {
                fprintf(tp_dag_mips,"sw $t2 %d($gp)\n",tab[tpc].adr);
            }
            else {
                fprintf(tp_dag_mips,"sw $t2 %d($sp)\n",tab[tpc].adr);
            }

            break;
        }
        case TIMESFC: {// lw t0, lw t1, mult, mflo
            tpc = searchtab(pc);//t2
            tpa = searchtab(pa);//t0
            tpb = searchtab(pb);//t1
            if (tpa < 0) {
                if (pa[0] == '\'') {//'a' [ch]
                    fprintf(tp_dag_mips,"li $t0, %d\n",(int)(pa[1]));//ascii
                }
                else fprintf(tp_dag_mips,"li $t0, %d\n",atoi(pa));//crtnum_str to num
            }
            else {
                if (tab[tpa].obj != CONSTobj) {// tmpvar var const
                    if  (tab[tpa].global) {
                        fprintf(tp_dag_mips,"lw $t0 %d($gp)\n",tab[tpa].adr);
                    }
                    else fprintf(tp_dag_mips,"lw $t0 %d($sp)\n",tab[tpa].adr);

                }
                else fprintf(tp_dag_mips,"li $t0, %d\n",tab[tpa].adr);
            }
            if (tpb < 0) {
                if (pb[0] == '\'') {//'a' [ch]
                    fprintf(tp_dag_mips,"li $t1, %d\n",(int)(pb[1]));//ascii
                }
                else fprintf(tp_dag_mips,"li $t1, %d\n",atoi(pb));//crtnum_str to num
            }
            else {
                if (tab[tpb].obj != CONSTobj) {
                    if  (tab[tpb].global) {
                        fprintf(tp_dag_mips,"lw $t1 %d($gp)\n",tab[tpb].adr);
                    }
                    else fprintf(tp_dag_mips,"lw $t1 %d($sp)\n",tab[tpb].adr);

                }
                else fprintf(tp_dag_mips,"li $t1, %d\n",tab[tpb].adr);
            }
            fprintf(tp_dag_mips,"mult $t0, $t1\n");
            fprintf(tp_dag_mips,"mflo $t2\n");//mul t2,t0,t1


            if (tab[tpc].global) {
                fprintf(tp_dag_mips,"sw $t2 %d($gp)\n",tab[tpc].adr);
            }
            else {
                fprintf(tp_dag_mips,"sw $t2 %d($sp)\n",tab[tpc].adr);
            }

            break;

        }
        case DIVFC: {
            tpc = searchtab(pc);//t2
            tpa = searchtab(pa);//t0
            tpb = searchtab(pb);//t1
            if (tpa < 0) {
                if (pa[0] == '\'') {//'a' [ch]
                    fprintf(tp_dag_mips,"li $t0, %d\n",(int)(pa[1]));//ascii
                }
                else fprintf(tp_dag_mips,"li $t0, %d\n",atoi(pa));//crtnum_str to num
            }
            else {
                if (tab[tpa].obj != CONSTobj) {// tmpvar var const
                    if  (tab[tpa].global) {
                        fprintf(tp_dag_mips,"lw $t0 %d($gp)\n",tab[tpa].adr);
                    }
                    else fprintf(tp_dag_mips,"lw $t0 %d($sp)\n",tab[tpa].adr);

                }
                else fprintf(tp_dag_mips,"li $t0, %d\n",tab[tpa].adr);
            }
            if (tpb < 0) {
                if (pb[0] == '\'') {//'a' [ch]
                    fprintf(tp_dag_mips,"li $t1, %d\n",(int)(pb[1]));//ascii
                }
                else fprintf(tp_dag_mips,"li $t1, %d\n",atoi(pb));//crtnum_str to num
            }
            else {
                if (tab[tpb].obj != CONSTobj) {
                    if  (tab[tpb].global) {
                        fprintf(tp_dag_mips,"lw $t1 %d($gp)\n",tab[tpb].adr);
                    }
                    else fprintf(tp_dag_mips,"lw $t1 %d($sp)\n",tab[tpb].adr);

                }
                else fprintf(tp_dag_mips,"li $t1, %d\n",tab[tpb].adr);
            }
            fprintf(tp_dag_mips,"div $t0, $t1\n");
            fprintf(tp_dag_mips,"mflo $t2\n");//div t2,t0,t1


            if (tab[tpc].global) {
                fprintf(tp_dag_mips,"sw $t2 %d($gp)\n",tab[tpc].adr);
            }
            else {
                fprintf(tp_dag_mips,"sw $t2 %d($sp)\n",tab[tpc].adr);
            }

            break;
        }
        case SCANFFC: {
            tpa = searchtab(pa);// var
            if (tab[tpa].typ == CHARtyp) {
                fprintf(tp_dag_mips,"li $v0 12\n");//read char in v0
                fprintf(tp_dag_mips,"syscall\n");
                if (tab[tpa].global) fprintf(tp_dag_mips,"sw $v0 %d($gp)\n",tab[tpa].adr);
                else fprintf(tp_dag_mips,"sw $v0 %d($sp)\n",tab[tpa].adr);
            }
            else if (tab[tpa].typ == INTtyp) {
                fprintf(tp_dag_mips,"li $v0 5\n");//read integer in v0
                fprintf(tp_dag_mips,"syscall\n");
                if (tab[tpa].global) fprintf(tp_dag_mips,"sw $v0 %d($gp)\n",tab[tpa].adr);
                else fprintf(tp_dag_mips,"sw $v0 %d($sp)\n",tab[tpa].adr);
            }
            //  else printf("error at mips SCANF, variable type\n");
            // read id
            break;
        }
        case PRINTFFC: {// a0, syscall
            tpa = searchtab(pa);// temp var const
            if (tab[tpa].obj != CONSTobj) {
                if  (tab[tpa].global) {
                    fprintf(tp_dag_mips,"lw $a0 %d($gp)\n",tab[tpa].adr);
                }
                else fprintf(tp_dag_mips,"lw $a0 %d($sp)\n",tab[tpa].adr);

            }
            else fprintf(tp_dag_mips,"li $a0, %d\n",tab[tpa].adr);
            if (tab[tpa].typ == CHARtyp) {
                fprintf(tp_dag_mips,"li $v0, 11\n");//write char in a0
                fprintf(tp_dag_mips,"syscall\n");

            }
            else if (tab[tpa].typ == INTtyp) {
                fprintf(tp_dag_mips,"li $v0, 1\n");//write int in a0
                fprintf(tp_dag_mips,"syscall\n");
            }
            //  else printf("error at mips SCANF, variable type\n");
            // read id
            fprintf(tp_dag_mips,"li $a0, 10\n");//\n ascii is 10
            fprintf(tp_dag_mips,"li $v0, 11\n");//write \n
            fprintf(tp_dag_mips,"syscall\n");
            break;
        }
        case PRINTFSTRFC: {
            fprintf(tp_dag_mips,".data\n");
            fprintf(tp_dag_mips,"str_%s: .asciiz \"%s\"\n",pa,dagpcode[index].str);//!
            fprintf(tp_dag_mips,".text\n");
            fprintf(tp_dag_mips,"la $a0, str_%s\n",pa);
            fprintf(tp_dag_mips,"li $v0, 4\n");//write str in a0
            fprintf(tp_dag_mips,"syscall\n");
            free(dagpcode[index].str);

            fprintf(tp_dag_mips,"li $a0, 10\n");//\n ascii is 10
            fprintf(tp_dag_mips,"li $v0, 11\n");//write \n
            fprintf(tp_dag_mips,"syscall\n");
            break;
        }
        case CASEFC : {
            tpa = searchtab(pa);
            tpb = searchtab(pb);
            if (tpa < 0) {
                if (pa[0] == '\'') {//'a' [ch]
                    fprintf(tp_dag_mips,"li $t0, %d\n",(int)(pa[1]));//ascii
                }
                else fprintf(tp_dag_mips,"li $t0, %d\n",atoi(pa));//crtnum_str to num
            }
            else {
                if (tab[tpa].obj != CONSTobj) {// tmpvar var const
                    if  (tab[tpa].global) {
                        fprintf(tp_dag_mips,"lw $t0 %d($gp)\n",tab[tpa].adr);
                    }
                    else fprintf(tp_dag_mips,"lw $t0 %d($sp)\n",tab[tpa].adr);

                }
                else fprintf(tp_dag_mips,"li $t0, %d\n",tab[tpa].adr);
            }
            if (tpb < 0) {
                if (pb[0] == '\'') {//'a' [ch]
                    fprintf(tp_dag_mips,"li $t1, %d\n",(int)(pb[1]));//ascii
                }
                else fprintf(tp_dag_mips,"li $t1, %d\n",atoi(pb));//crtnum_str to num
            }
            else {
                if (tab[tpb].obj != CONSTobj) {
                    if  (tab[tpb].global) {
                        fprintf(tp_dag_mips,"lw $t1 %d($gp)\n",tab[tpb].adr);
                    }
                    else fprintf(tp_dag_mips,"lw $t1 %d($sp)\n",tab[tpb].adr);

                }
                else fprintf(tp_dag_mips,"li $t1, %d\n",tab[tpb].adr);
            }
            fprintf(tp_dag_mips,"bne $t0, $t1, %s\n",pc);//
            break;
        }
        case BNEFC: {
            tpa = searchtab(pa);
            tpb = searchtab(pb);
            if (tpb < 0) {
                if (pb[0] == '\'') {//'a' [ch]
                    fprintf(tp_dag_mips,"li $t1, %d\n",(int)(pb[1]));//ascii
                }
                else fprintf(tp_dag_mips,"li $t1, %d\n",atoi(pb));//crtnum_str to num
            }
            else {
                if (tab[tpb].obj != CONSTobj) {
                    if  (tab[tpb].global) {
                        fprintf(tp_dag_mips,"lw $t1 %d($gp)\n",tab[tpb].adr);
                    }
                    else fprintf(tp_dag_mips,"lw $t1 %d($sp)\n",tab[tpb].adr);

                }
                else fprintf(tp_dag_mips,"li $t1, %d\n",tab[tpb].adr);
            }

            int flag1 = 0;

            if ((tpa < 0) && (strisnumber(pa))) {//number
                fprintf(tp_dag_mips,"li $t0, %d\n",atoi(dagpcode[index].a));
                flag1 = 1;
            }
            else if ((tpa < 0) && (dagpcode[index].a[0] == '\'')){//'a' [ch]
                fprintf(tp_dag_mips,"li $t0, %d\n",(int)(dagpcode[index].a[1]));//ascii
                flag1 = 1;
            }
            else {
                if (tab[tpa].obj != CONSTobj) {// tmpvar var const
                    if  (tab[tpa].global) {
                        fprintf(tp_dag_mips,"lw $t0 %d($gp)\n",tab[tpa].adr);
                    }
                    else fprintf(tp_dag_mips,"lw $t0 %d($sp)\n",tab[tpa].adr);

                }
                else fprintf(tp_dag_mips,"li $t0, %d\n",tab[tpa].adr);
            }
            fprintf(tp_dag_mips,"beq $t0, $t1, %s\n",pc);//debug
            //bne rs,rt,LABEL(offset)
            break;
        }
        case BEQFC: {
            tpa = searchtab(pa);// temp var
            tpb = searchtab(pb);

            int flag1 = 0,flag2 = 0;

            if ((tpa < 0) && (strisnumber(pa))) {//number
                fprintf(tp_dag_mips,"li $t0, %d\n",atoi(dagpcode[index].a));
                flag1 = 1;
            }
            else if ((tpa < 0) && (dagpcode[index].a[0] == '\'')){//'a' [ch]
                fprintf(tp_dag_mips,"li $t0, %d\n",(int)(dagpcode[index].a[1]));//ascii
                flag1 = 1;
            }
            else {
                if (tab[tpa].obj != CONSTobj) {// tmpvar var const
                    if  (tab[tpa].global) {
                        fprintf(tp_dag_mips,"lw $t0 %d($gp)\n",tab[tpa].adr);
                    }
                    else fprintf(tp_dag_mips,"lw $t0 %d($sp)\n",tab[tpa].adr);

                }
                else fprintf(tp_dag_mips,"li $t0, %d\n",tab[tpa].adr);
            }

            if ((tpb < 0) && (strisnumber(pb))) {//number
                fprintf(tp_dag_mips,"li $t1, %d\n",atoi(dagpcode[index].b));
                flag2 = 1;
            }
            else if ((tpb < 0) && (dagpcode[index].b[0] == '\'')){//'a' [ch]
                fprintf(tp_dag_mips,"li $t1, %d\n",(int)(dagpcode[index].b[1]));//ascii
                flag2 = 1;
            }
            else {
                if (tab[tpb].obj != CONSTobj) {
                    if  (tab[tpb].global) {
                        fprintf(tp_dag_mips,"lw $t1 %d($gp)\n",tab[tpb].adr);
                    }
                    else fprintf(tp_dag_mips,"lw $t1 %d($sp)\n",tab[tpb].adr);

                }
                else fprintf(tp_dag_mips,"li $t1, %d\n",tab[tpb].adr);
            }
            fprintf(tp_dag_mips,"bne $t0, $t1, %s\n",pc);//
            //bne rs,rt,LABEL(offset)
            break;
        }
        case LESFC: {
            tpa = searchtab(pa);// temp var
            tpb = searchtab(pb);

            int flag1 = 0,flag2 = 0;

            if ((tpa < 0) && (strisnumber(pa))) {//number
                fprintf(tp_dag_mips,"li $t0, %d\n",atoi(dagpcode[index].a));
                flag1 = 1;
            }
            else if ((tpa < 0) && (dagpcode[index].a[0] == '\'')){//'a' [ch]
                fprintf(tp_dag_mips,"li $t0, %d\n",(int)(dagpcode[index].a[1]));//ascii
                flag1 = 1;
            }
            else {
                if (tab[tpa].obj != CONSTobj) {// tmpvar var const
                    if  (tab[tpa].global) {
                        fprintf(tp_dag_mips,"lw $t0 %d($gp)\n",tab[tpa].adr);
                    }
                    else fprintf(tp_dag_mips,"lw $t0 %d($sp)\n",tab[tpa].adr);

                }
                else fprintf(tp_dag_mips,"li $t0, %d\n",tab[tpa].adr);
            }

            if ((tpb < 0) && (strisnumber(pb))) {//number
                fprintf(tp_dag_mips,"li $t1, %d\n",atoi(dagpcode[index].b));
                flag2 = 1;
            }
            else if ((tpb < 0) && (dagpcode[index].b[0] == '\'')){//'a' [ch]
                fprintf(tp_dag_mips,"li $t1, %d\n",(int)(dagpcode[index].b[1]));//ascii
                flag2 = 1;
            }
            else {
                if (tab[tpb].obj != CONSTobj) {
                    if  (tab[tpb].global) {
                        fprintf(tp_dag_mips,"lw $t1 %d($gp)\n",tab[tpb].adr);
                    }
                    else fprintf(tp_dag_mips,"lw $t1 %d($sp)\n",tab[tpb].adr);

                }
                else fprintf(tp_dag_mips,"li $t1, %d\n",tab[tpb].adr);
            }


            fprintf(tp_dag_mips,"subu $t2, $t0, $t1\n");//0
            fprintf(tp_dag_mips,"bgez $t2, %s\n",pc);//
            //bne rs,rt,LABEL(offset)
            break;
        }
        case GRTFC: {
            tpa = searchtab(pa);// temp var
            tpb = searchtab(pb);
            int flag1 = 0,flag2 = 0;

            if ((tpa < 0) && (strisnumber(pa))) {//number
                fprintf(tp_dag_mips,"li $t0, %d\n",atoi(dagpcode[index].a));
                flag1 = 1;
            }
            else if ((tpa < 0) && (dagpcode[index].a[0] == '\'')){//'a' [ch]
                fprintf(tp_dag_mips,"li $t0, %d\n",(int)(dagpcode[index].a[1]));//ascii
                flag1 = 1;
            }
            else {
                if (tab[tpa].obj != CONSTobj) {// tmpvar var const
                    if  (tab[tpa].global) {
                        fprintf(tp_dag_mips,"lw $t0 %d($gp)\n",tab[tpa].adr);
                    }
                    else fprintf(tp_dag_mips,"lw $t0 %d($sp)\n",tab[tpa].adr);

                }
                else fprintf(tp_dag_mips,"li $t0, %d\n",tab[tpa].adr);
            }
            if ((tpb < 0) && (strisnumber(pb))) {//number
                fprintf(tp_dag_mips,"li $t1, %d\n",atoi(dagpcode[index].b));
                flag2 = 1;
            }
            else if ((tpb < 0) && (dagpcode[index].b[0] == '\'')){//'a' [ch]
                fprintf(tp_dag_mips,"li $t1, %d\n",(int)(dagpcode[index].b[1]));//ascii
                flag2 = 1;
            }
            else {
                if (tab[tpb].obj != CONSTobj) {
                    if  (tab[tpb].global) {
                        fprintf(tp_dag_mips,"lw $t1 %d($gp)\n",tab[tpb].adr);
                    }
                    else fprintf(tp_dag_mips,"lw $t1 %d($sp)\n",tab[tpb].adr);

                }
                else fprintf(tp_dag_mips,"li $t1, %d\n",tab[tpb].adr);
            }
            fprintf(tp_dag_mips,"subu $t2, $t0, $t1 \n");//slt rd,rs,rt
            fprintf(tp_dag_mips,"blez $t2, %s\n",pc);//bltz rs,offset
            //bne rs,rt,LABEL(offset)
            break;
        }
        case GEQFC: {
            tpa = searchtab(pa);// temp var
            tpb = searchtab(pb);
            int flag1 = 0,flag2 = 0;

            if ((tpa < 0) && (strisnumber(pa))) {//number
                fprintf(tp_dag_mips,"li $t0, %d\n",atoi(dagpcode[index].a));
                flag1 = 1;
            }
            else if ((tpa < 0) && (dagpcode[index].a[0] == '\'')){//'a' [ch]
                fprintf(tp_dag_mips,"li $t0, %d\n",(int)(dagpcode[index].a[1]));//ascii
                flag1 = 1;
            }
            else {
                if (tab[tpa].obj != CONSTobj) {// tmpvar var const
                    if  (tab[tpa].global) {
                        fprintf(tp_dag_mips,"lw $t0 %d($gp)\n",tab[tpa].adr);
                    }
                    else fprintf(tp_dag_mips,"lw $t0 %d($sp)\n",tab[tpa].adr);

                }
                else fprintf(tp_dag_mips,"li $t0, %d\n",tab[tpa].adr);
            }

            if ((tpb < 0) && (strisnumber(pb))) {//number
                fprintf(tp_dag_mips,"li $t1, %d\n",atoi(dagpcode[index].b));
                flag2 = 1;
            }
            else if ((tpb < 0) && (dagpcode[index].b[0] == '\'')){//'a' [ch]
                fprintf(tp_dag_mips,"li $t1, %d\n",(int)(dagpcode[index].b[1]));//ascii
                flag2 = 1;
            }
            else {
                if (tab[tpb].obj != CONSTobj) {
                    if  (tab[tpb].global) {
                        fprintf(tp_dag_mips,"lw $t1 %d($gp)\n",tab[tpb].adr);
                    }
                    else fprintf(tp_dag_mips,"lw $t1 %d($sp)\n",tab[tpb].adr);

                }
                else fprintf(tp_dag_mips,"li $t1, %d\n",tab[tpb].adr);
            }
            fprintf(tp_dag_mips,"subu $t2, $t0, $t1 \n");//slt rd,rs,rt
            fprintf(tp_dag_mips,"bltz $t2, %s\n",pc);//bltz rs,offset
            //bne rs,rt,LABEL(offset)
            break;
        }
        case LEQFC: {
            tpa = searchtab(pa);// temp var
            tpb = searchtab(pb);
            int flag1  =0, flag2 = 0;
            if ((tpa < 0) && (strisnumber(pa))) {//number
                fprintf(tp_dag_mips,"li $t0, %d\n",atoi(dagpcode[index].a));
                flag1 = 1;
            }
            else if ((tpa < 0) && (dagpcode[index].a[0] == '\'')){//'a' [ch]
                fprintf(tp_dag_mips,"li $t0, %d\n",(int)(dagpcode[index].a[1]));//ascii
                flag1 = 1;
            }
            else {
                if (tab[tpa].obj != CONSTobj) {// tmpvar var const
                    if  (tab[tpa].global) {
                        fprintf(tp_dag_mips,"lw $t0 %d($gp)\n",tab[tpa].adr);
                    }
                    else fprintf(tp_dag_mips,"lw $t0 %d($sp)\n",tab[tpa].adr);

                }
                else fprintf(tp_dag_mips,"li $t0, %d\n",tab[tpa].adr);
            }
            if ((tpb < 0) && (strisnumber(pb))) {//number
                fprintf(tp_dag_mips,"li $t1, %d\n",atoi(dagpcode[index].b));
                flag2 = 1;
            }
            else if ((tpb < 0) && (dagpcode[index].b[0] == '\'')){//'a' [ch]
                fprintf(tp_dag_mips,"li $t1, %d\n",(int)(dagpcode[index].b[1]));//ascii
                flag2 = 1;
            }
            else {
                if (tab[tpb].obj != CONSTobj) {
                    if  (tab[tpb].global) {
                        fprintf(tp_dag_mips,"lw $t1 %d($gp)\n",tab[tpb].adr);
                    }
                    else fprintf(tp_dag_mips,"lw $t1 %d($sp)\n",tab[tpb].adr);

                }
                else fprintf(tp_dag_mips,"li $t1, %d\n",tab[tpb].adr);
            }
            fprintf(tp_dag_mips,"subu $t2, $t0, $t1 \n");//slt rd,rs,rt
            fprintf(tp_dag_mips,"bgtz $t2, %s\n",pc);//bltz rs,offset
            //bne rs,rt,LABEL(offset)
            break;
        }
        case JUMPFC: {
            fprintf(tp_dag_mips,"j %s\n",pc);
            //j label
            break;
        }
        case LABELFC: {
            fprintf(tp_dag_mips,"%s :\n",pa);
            //Label_1:
            break;
        }
        case SWITCHFC:break;
        case NOPFC: {
            //fprintf(tp_dag_mips,"nop\n");
            break;
        }
        default: {
            fprintf(tp_dag_mips,"error at print mips: invalid op\n");
        }

    }

};
void create_mips (int index) {
    int tpa,tpb,tpc,op;
    char pa[IDMAX],pb[IDMAX],pc[IDMAX];
    op = pcode[index].op;
    strcpy(pa,pcode[index].a);
    strcpy(pb,pcode[index].b);
    strcpy(pc,pcode[index].c);



    switch (op) {
        case LGFC: {
            //fprintf(kp_pcode,"%s %s %s\n",pcode[px].a,pcode[px].c,pcode[px].b);
            //[exp] LGSY [exp]
            break;
        }
        case VRETFC: {
            if (!strcmp(pa, "main")) fprintf(tp_mips,"j END\n");//main func
            else fprintf(tp_mips,"jr $ra\n");
            break;
        }

        case CALLFC: {// savecur instack call outstack retrive
            tpa = searchtab(pa);
            char func[IDMAX]={"_f\0"};
            strcat(pa,func);
            //fprintf(tp_mips,"subi $sp, $sp, %d\n",tab[tpa].adr);//stack
            fprintf(tp_mips,"jal %s\n",pa);//call
            //fprintf(tp_mips,"addi $sp, $sp, %d\n",tab[tpa].adr);//stack
            break;

            //call [id] [空]
            break;
        }
        case RESTACKFC: {
            tpa = searchtab(pa);
            fprintf(tp_mips,"addiu $sp, $sp, %d\n",tab[tpa].adr+80);//stack
            break;
        }
        case OPSTACKFC: {
            tpa = searchtab(pa);
            fprintf(tp_mips,"addiu $sp, $sp, %d\n",-(tab[tpa].adr+80));//stack
            break;
        }
        case SASCENEFC: {
            fprintf(tp_mips,"addiu $sp, $sp, -4\n");
            fprintf(tp_mips,"sw $ra, 0($sp)\n");//save
            break;
        }
        case RESCENEFC: {
            fprintf(tp_mips,"lw $ra, 0($sp)\n");
            fprintf(tp_mips,"addiu $sp, $sp, 4\n");//re
            break;
        }
        case FUNCFC: {//label:(function name)//instack
            fprintf(tp_mips,"%s:\n",pa);//rename once debug

            //tpa = searchtab(pa);//func
            //fprintf(tp_mips,"subi $sp, $sp, %d\n",tab[tpa].adr);//stack
            //func_[name]:

            break;
        }
        case PARAFC: {//?
            //fprintf(kp_pcode,"para %s %s\n",pcode[px].a,pcode[px].b);
            //para [type] [id]
            break;
        }
        case PUSHFC: {//lw addr, lw para, sw para
            int cnt;
            tpc = searchtab(pc);//func
            tpa = searchtab(pa);//para
            cnt = atoi(pb);//cnt
            fprintf(tp_mips,"li $t0, %d\n",cnt);
            fprintf( tp_mips,"sll $t0, $t0, 2\n");//offset
            fprintf(tp_mips,"addiu $t1, $sp, -4\n");//sp
            fprintf(tp_mips,"addiu $t1, $t1, %d\n",-(tab[tpc].adr+80));//func base
            fprintf( tp_mips,"addu $t1, $t1, $t0\n");//address

            if (tab[tpa].obj != CONSTobj) {//para
                if  (tab[tpa].global) {
                    fprintf(tp_mips,"lw $t2, %d($gp)\n",tab[tpa].adr);
                }
                else fprintf(tp_mips,"lw $t2, %d($sp)\n",tab[tpa].adr);
            }
            else fprintf(tp_mips,"li $t2, %d\n",tab[tpa].adr);

            fprintf(tp_mips,"sw $t2, 0($t1)\n");//sw
            //push [id] [空]
            break;
        }

        case FRETFC: {//
            tpa = searchtab(pa);

            if  (tab[tpa].global) {
                fprintf(tp_mips,"sw $v0, %d($gp)\n",tab[tpa].adr);
            }
            else fprintf(tp_mips,"sw $v0, %d($sp)\n",tab[tpa].adr);
            //[id] = RET
            break;
        }
        case RETFC: {
            if (!strcmp(pa, " ")) {//void func
                if (!strcmp(pb, "main")) fprintf(tp_mips,"j END\n");//main func
                else fprintf(tp_mips,"jr $ra\n");
            }
            else {//return func
                tpa = searchtab(pa);
                if (tab[tpa].obj != CONSTobj) {//offset
                    if  (tab[tpa].global) {
                        fprintf(tp_mips,"lw $t0, %d($gp)\n",tab[tpa].adr);
                    }
                    else fprintf(tp_mips,"lw $t0, %d($sp)\n",tab[tpa].adr);
                }
                else fprintf(tp_mips,"li $t0, %d\n",tab[tpa].adr);

                fprintf(tp_mips,"move $v0, $t0\n");
                fprintf(tp_mips,"jr $ra\n");
            }
            break;
        }
        case ARRLFC: {//lw t0 b, lw t1 c,sw t2 to c[b]
            tpc = searchtab(pc);//t1
            tpa = searchtab(pa);//t2
            tpb = searchtab(pb);//t0 int

            if (tab[tpb].obj != CONSTobj) {//offset
                if  (tab[tpb].global) {
                    fprintf(tp_mips,"lw $t0, %d($gp)\n",tab[tpb].adr);
                }
                else fprintf(tp_mips,"lw $t0, %d($sp)\n",tab[tpb].adr);
            }
            else fprintf(tp_mips,"li $t0, %d\n",tab[tpb].adr);
            fprintf(tp_mips,"sll $t0, $t0, 2\n");//amend offset

            if (tab[tpa].obj != CONSTobj) {//assign value
                if  (tab[tpa].global) {
                    fprintf(tp_mips,"lw $t2, %d($gp)\n",tab[tpa].adr);
                }
                else fprintf(tp_mips,"lw $t2, %d($sp)\n",tab[tpa].adr);
            }
            else fprintf(tp_mips,"li $t2, %d\n",tab[tpa].adr);

            fprintf(tp_mips,"li $t1, %d\n",tab[tpc].adr);//array base lic

            if  (tab[tpc].global) {
                fprintf(tp_mips,"subu $t3, $t1, $t0\n");
                fprintf(tp_mips,"addu $t3, $t3, $gp\n");//debug
                fprintf(tp_mips,"sw $t2, 0($t3)\n");

            }
            else {
                fprintf(tp_mips,"addu $t3, $t1, $t0\n");
                fprintf(tp_mips,"addu $t3, $t3, $sp\n");
                fprintf(tp_mips,"sw $t2, 0($t3)\n");//debug
            }


            break;

        }
        case ARRRFC: {//lw t0 b, lw t1 a,lw t3 a[b], sw t3
            tpc = searchtab(pc);//t2
            tpa = searchtab(pa);//t1
            tpb = searchtab(pb);//t0 int
            if (tab[tpb].obj != CONSTobj) {//exp offset
                if  (tab[tpb].global) {
                    fprintf(tp_mips,"lw $t0 %d($gp)\n",tab[tpb].adr);
                }
                else fprintf(tp_mips,"lw $t0 %d($sp)\n",tab[tpb].adr);

            }
            else fprintf(tp_mips,"li $t0, %d\n",tab[tpb].adr);
            fprintf(tp_mips,"sll $t0, $t0, 2\n");//amend offset

            fprintf(tp_mips,"li $t1, %d\n",tab[tpa].adr);//array base lic

            if  (tab[tpa].global) {//debug
                fprintf(tp_mips,"subu $t2, $t1, $t0\n");
                fprintf(tp_mips,"addu $t2, $t2, $gp\n");
                fprintf(tp_mips,"lw $t3, 0($t2)\n");//debug

            }
            else {
                fprintf(tp_mips,"addu $t2, $t1, $t0\n");
                fprintf(tp_mips,"addu $t2, $t2, $sp\n");
                fprintf(tp_mips,"lw $t3, 0($t2)\n");
            }





            if (tab[tpc].global) {
                fprintf(tp_mips,"sw $t3, %d($gp)\n",tab[tpc].adr);
            }
            else {
                fprintf(tp_mips,"sw $t3, %d($sp)\n",tab[tpc].adr);
            }

            break;

        }

        case ASSIGNFC: {// lw $t0 from p1, sw $t0 to p2
            tpa = searchtab(pa);// 'a' numberstr exp(temp var) const
            tpc = searchtab(pc);//int char array temp
            // if (tpc < 0) printf("error at mips ASSIGNFC, no variable in tab\n");
            // if (tab[tpc].obj != VARobj) printf("error at mips ASSIGNFC, not variable\n");
            if (tpa < 0) {
                if (pcode[index].a[0] == '\'') {//'a' [ch]
                    fprintf(tp_mips,"li $t0, %d\n",(int)(pa[1]));//ascii
                }
                else fprintf(tp_mips,"li $t0, %d\n",atoi(pa));//crtnum_str to num
            }
            else {//const var
                if (tab[tpa].obj != CONSTobj) {
                    if  (tab[tpa].global) {
                        fprintf(tp_mips,"lw $t0 %d($gp)\n",tab[tpa].adr);
                    }
                    else fprintf(tp_mips,"lw $t0 %d($sp)\n",tab[tpa].adr);

                }
                else fprintf(tp_mips,"li $t0, %d\n",tab[tpa].adr);

            }


            if (tab[tpc].global) {
                fprintf(tp_mips,"sw $t0 %d($gp)\n",tab[tpc].adr);
            }
            else {
                fprintf(tp_mips,"sw $t0 %d($sp)\n",tab[tpc].adr);
            }

            break;
        }
        case PLUSFC: {// lw t0, lw t1, add t2 t0 t1, sw t2
            tpc = searchtab(pcode[index].c);//t2
            tpa = searchtab(pcode[index].a);//t0
            tpb = searchtab(pcode[index].b);//t1
            if (tab[tpa].obj != CONSTobj) {// tmpvar var const
                if  (tab[tpa].global) {
                    fprintf(tp_mips,"lw $t0 %d($gp)\n",tab[tpa].adr);
                }
                else fprintf(tp_mips,"lw $t0 %d($sp)\n",tab[tpa].adr);

            }
            else fprintf(tp_mips,"li $t0, %d\n",tab[tpa].adr);
            if (tab[tpb].obj != CONSTobj) {
                if  (tab[tpb].global) {
                    fprintf(tp_mips,"lw $t1 %d($gp)\n",tab[tpb].adr);
                }
                else fprintf(tp_mips,"lw $t1 %d($sp)\n",tab[tpb].adr);

            }
            else fprintf(tp_mips,"li $t1, %d\n",tab[tpb].adr);

            fprintf(tp_mips,"addu $t2, $t0, $t1\n");//


            if (tab[tpc].global) {
                fprintf(tp_mips,"sw $t2 %d($gp)\n",tab[tpc].adr);//debug
            }
            else {
                fprintf(tp_mips,"sw $t2 %d($sp)\n",tab[tpc].adr);
            }

            break;
        }
        case MINUSFC: {// lw t0, lw t1, sub t2 t0 t1, sw t2
            tpc = searchtab(pcode[index].c);//t2
            tpa = searchtab(pcode[index].a);//t0
            tpb = searchtab(pcode[index].b);//t1
            if (tab[tpa].obj != CONSTobj) {// tmpvar var const
                if  (tab[tpa].global) {
                    fprintf(tp_mips,"lw $t0 %d($gp)\n",tab[tpa].adr);
                }
                else fprintf(tp_mips,"lw $t0 %d($sp)\n",tab[tpa].adr);

            }
            else fprintf(tp_mips,"li $t0, %d\n",tab[tpa].adr);
            if (tab[tpb].obj != CONSTobj) {
                if  (tab[tpb].global) {
                    fprintf(tp_mips,"lw $t1 %d($gp)\n",tab[tpb].adr);
                }
                else fprintf(tp_mips,"lw $t1 %d($sp)\n",tab[tpb].adr);

            }
            else fprintf(tp_mips,"li $t1, %d\n",tab[tpb].adr);

            fprintf(tp_mips,"sub $t2, $t0, $t1\n");//


            if (tab[tpc].global) {
                fprintf(tp_mips,"sw $t2 %d($gp)\n",tab[tpc].adr);
            }
            else {
                fprintf(tp_mips,"sw $t2 %d($sp)\n",tab[tpc].adr);
            }

            break;
        }
        case TIMESFC: {// lw t0, lw t1, mult, mflo
            tpc = searchtab(pcode[index].c);//t2
            tpa = searchtab(pcode[index].a);//t0
            tpb = searchtab(pcode[index].b);//t1
            if (tab[tpa].obj != CONSTobj) {// tmpvar var const
                if  (tab[tpa].global) {
                    fprintf(tp_mips,"lw $t0 %d($gp)\n",tab[tpa].adr);
                }
                else fprintf(tp_mips,"lw $t0 %d($sp)\n",tab[tpa].adr);

            }
            else fprintf(tp_mips,"li $t0, %d\n",tab[tpa].adr);
            if (tab[tpb].obj != CONSTobj) {
                if  (tab[tpb].global) {
                    fprintf(tp_mips,"lw $t1 %d($gp)\n",tab[tpb].adr);
                }
                else fprintf(tp_mips,"lw $t1 %d($sp)\n",tab[tpb].adr);

            }
            else fprintf(tp_mips,"li $t1, %d\n",tab[tpb].adr);

            fprintf(tp_mips,"mult $t0, $t1\n");
            fprintf(tp_mips,"mflo $t2\n");//mul t2,t0,t1


            if (tab[tpc].global) {
                fprintf(tp_mips,"sw $t2 %d($gp)\n",tab[tpc].adr);
            }
            else {
                fprintf(tp_mips,"sw $t2 %d($sp)\n",tab[tpc].adr);
            }

            break;

        }
        case DIVFC: {
            tpc = searchtab(pcode[index].c);//t2
            tpa = searchtab(pcode[index].a);//t0
            tpb = searchtab(pcode[index].b);//t1
            if (tab[tpa].obj != CONSTobj) {// tmpvar var const
                if  (tab[tpa].global) {
                    fprintf(tp_mips,"lw $t0 %d($gp)\n",tab[tpa].adr);
                }
                else fprintf(tp_mips,"lw $t0 %d($sp)\n",tab[tpa].adr);

            }
            else fprintf(tp_mips,"li $t0, %d\n",tab[tpa].adr);
            if (tab[tpb].obj != CONSTobj) {
                if  (tab[tpb].global) {
                    fprintf(tp_mips,"lw $t1 %d($gp)\n",tab[tpb].adr);
                }
                else fprintf(tp_mips,"lw $t1 %d($sp)\n",tab[tpb].adr);

            }
            else fprintf(tp_mips,"li $t1, %d\n",tab[tpb].adr);

            fprintf(tp_mips,"div $t0, $t1\n");
            fprintf(tp_mips,"mflo $t2\n");//div t2,t0,t1


            if (tab[tpc].global) {
                fprintf(tp_mips,"sw $t2 %d($gp)\n",tab[tpc].adr);
            }
            else {
                fprintf(tp_mips,"sw $t2 %d($sp)\n",tab[tpc].adr);
            }

            break;
        }
        case SCANFFC: {
            tpa = searchtab(pcode[index].a);// var
            if (tab[tpa].typ == CHARtyp) {
                fprintf(tp_mips,"li $v0 12\n");//read char in v0
                fprintf(tp_mips,"syscall\n");
                if (tab[tpa].global) fprintf(tp_mips,"sw $v0 %d($gp)\n",tab[tpa].adr);
                else fprintf(tp_mips,"sw $v0 %d($sp)\n",tab[tpa].adr);
            }
            else if (tab[tpa].typ == INTtyp) {
                fprintf(tp_mips,"li $v0 5\n");//read integer in v0
                fprintf(tp_mips,"syscall\n");
                if (tab[tpa].global) fprintf(tp_mips,"sw $v0 %d($gp)\n",tab[tpa].adr);
                else fprintf(tp_mips,"sw $v0 %d($sp)\n",tab[tpa].adr);
            }
            //  else printf("error at mips SCANF, variable type\n");
            // read id
            break;
        }
        case PRINTFFC: {// a0, syscall
            tpa = searchtab(pcode[index].a);// temp var const
            if (tab[tpa].obj != CONSTobj) {
                if  (tab[tpa].global) {
                    fprintf(tp_mips,"lw $a0 %d($gp)\n",tab[tpa].adr);
                }
                else fprintf(tp_mips,"lw $a0 %d($sp)\n",tab[tpa].adr);

            }
            else fprintf(tp_mips,"li $a0, %d\n",tab[tpa].adr);
            if (tab[tpa].typ == CHARtyp) {
                fprintf(tp_mips,"li $v0, 11\n");//write char in a0
                fprintf(tp_mips,"syscall\n");

            }
            else if (tab[tpa].typ == INTtyp) {
                fprintf(tp_mips,"li $v0, 1\n");//write int in a0
                fprintf(tp_mips,"syscall\n");
            }
            //  else printf("error at mips SCANF, variable type\n");
            // read id
            fprintf(tp_mips,"li $a0, 10\n");//\n ascii is 10
            fprintf(tp_mips,"li $v0, 11\n");//write \n
            fprintf(tp_mips,"syscall\n");
            break;
        }
        case PRINTFSTRFC: {
            fprintf(tp_mips,".data\n");
            fprintf(tp_mips,"str_%s: .asciiz \"%s\"\n",pcode[index].a,pcode[index].str);
            fprintf(tp_mips,".text\n");
            fprintf(tp_mips,"la $a0, str_%s\n",pcode[index].a);
            fprintf(tp_mips,"li $v0, 4\n");//write str in a0
            fprintf(tp_mips,"syscall\n");
            free(pcode[index].str);

            fprintf(tp_mips,"li $a0, 10\n");//\n ascii is 10
            fprintf(tp_mips,"li $v0, 11\n");//write \n
            fprintf(tp_mips,"syscall\n");
            break;
        }
        case CASEFC : {
            tpa = searchtab(pcode[index].a);
            tpb = searchtab(pcode[index].b);
            if (tpa < 0) {
                if (pcode[index].a[0] == '\'') {//'a' [ch]
                    fprintf(tp_mips,"li $t0, %d\n",(int)(pa[1]));//ascii
                }
                else fprintf(tp_mips,"li $t0, %d\n",atoi(pa));//crtnum_str to num
            }
            else {
                if (tab[tpa].obj != CONSTobj) {// tmpvar var const
                    if  (tab[tpa].global) {
                        fprintf(tp_mips,"lw $t0 %d($gp)\n",tab[tpa].adr);
                    }
                    else fprintf(tp_mips,"lw $t0 %d($sp)\n",tab[tpa].adr);

                }
                else fprintf(tp_mips,"li $t0, %d\n",tab[tpa].adr);
            }
            if (tpb < 0) {
                if (pcode[index].b[0] == '\'') {//'a' [ch]
                    fprintf(tp_mips,"li $t1, %d\n",(int)(pb[1]));//ascii
                }
                else fprintf(tp_mips,"li $t1, %d\n",atoi(pb));//crtnum_str to num
            }
            else {
                if (tab[tpb].obj != CONSTobj) {
                    if  (tab[tpb].global) {
                        fprintf(tp_mips,"lw $t1 %d($gp)\n",tab[tpb].adr);
                    }
                    else fprintf(tp_mips,"lw $t1 %d($sp)\n",tab[tpb].adr);

                }
                else fprintf(tp_mips,"li $t1, %d\n",tab[tpb].adr);
            }
            fprintf(tp_mips,"bne $t0, $t1, %s\n",pc);//
            break;
        }
        case BNEFC: {
            tpa = searchtab(pcode[index].a);
            tpb = searchtab(pcode[index].b);
            if (tpb < 0) {
                if (pcode[index].b[0] == '\'') {//'a' [ch]
                    fprintf(tp_mips,"li $t1, %d\n",(int)(pcode[index].b[1]));//ascii
                }
                else fprintf(tp_mips,"li $t1, %d\n",atoi(pcode[index].b));//crtnum_str to num
            }
            else {
                if (tab[tpb].obj != CONSTobj) {
                    if  (tab[tpb].global) {
                        fprintf(tp_mips,"lw $t1 %d($gp)\n",tab[tpb].adr);
                    }
                    else fprintf(tp_mips,"lw $t1 %d($sp)\n",tab[tpb].adr);

                }
                else fprintf(tp_mips,"li $t1, %d\n",tab[tpb].adr);
            }
            if (tab[tpa].obj != CONSTobj) {// tmpvar var const
                if  (tab[tpa].global) {
                    fprintf(tp_mips,"lw $t0 %d($gp)\n",tab[tpa].adr);
                }
                else fprintf(tp_mips,"lw $t0 %d($sp)\n",tab[tpa].adr);

            }
            else fprintf(tp_mips,"li $t0, %d\n",tab[tpa].adr);

            fprintf(tp_mips,"beq $t0, $t1, %s\n",pc);//debug
            //bne rs,rt,LABEL(offset)
            break;
        }
        case BEQFC: {
            tpa = searchtab(pcode[index].a);// temp var
            tpb = searchtab(pcode[index].b);
            if (tab[tpa].obj != CONSTobj) {// tmpvar var const
                if  (tab[tpa].global) {
                    fprintf(tp_mips,"lw $t0 %d($gp)\n",tab[tpa].adr);
                }
                else fprintf(tp_mips,"lw $t0 %d($sp)\n",tab[tpa].adr);

            }
            else fprintf(tp_mips,"li $t0, %d\n",tab[tpa].adr);

            if (tab[tpb].obj != CONSTobj) {
                if  (tab[tpb].global) {
                    fprintf(tp_mips,"lw $t1 %d($gp)\n",tab[tpb].adr);
                }
                else fprintf(tp_mips,"lw $t1 %d($sp)\n",tab[tpb].adr);

            }
            else fprintf(tp_mips,"li $t1, %d\n",tab[tpb].adr);

            fprintf(tp_mips,"bne $t0, $t1, %s\n",pc);//
            //bne rs,rt,LABEL(offset)
            break;
        }
        case LESFC: {
            tpa = searchtab(pcode[index].a);// temp var
            tpb = searchtab(pcode[index].b);
            if (tab[tpa].obj != CONSTobj) {// tmpvar var const
                if  (tab[tpa].global) {
                    fprintf(tp_mips,"lw $t0 %d($gp)\n",tab[tpa].adr);
                }
                else fprintf(tp_mips,"lw $t0 %d($sp)\n",tab[tpa].adr);

            }
            else fprintf(tp_mips,"li $t0, %d\n",tab[tpa].adr);

            if (tab[tpb].obj != CONSTobj) {
                if  (tab[tpb].global) {
                    fprintf(tp_mips,"lw $t1 %d($gp)\n",tab[tpb].adr);
                }
                else fprintf(tp_mips,"lw $t1 %d($sp)\n",tab[tpb].adr);

            }
            else fprintf(tp_mips,"li $t1, %d\n",tab[tpb].adr);

            fprintf(tp_mips,"subu $t2, $t0, $t1\n");//0
            fprintf(tp_mips,"bgez $t2, %s\n",pcode[index].c);//
            //bne rs,rt,LABEL(offset)
            break;
        }
        case GRTFC: {
            tpa = searchtab(pcode[index].a);// temp var
            tpb = searchtab(pcode[index].b);
            if (tab[tpa].obj != CONSTobj) {// tmpvar var const
                if  (tab[tpa].global) {
                    fprintf(tp_mips,"lw $t0 %d($gp)\n",tab[tpa].adr);
                }
                else fprintf(tp_mips,"lw $t0 %d($sp)\n",tab[tpa].adr);

            }
            else fprintf(tp_mips,"li $t0, %d\n",tab[tpa].adr);

            if (tab[tpb].obj != CONSTobj) {
                if  (tab[tpb].global) {
                    fprintf(tp_mips,"lw $t1 %d($gp)\n",tab[tpb].adr);
                }
                else fprintf(tp_mips,"lw $t1 %d($sp)\n",tab[tpb].adr);

            }
            else fprintf(tp_mips,"li $t1, %d\n",tab[tpb].adr);

            fprintf(tp_mips,"subu $t2, $t0, $t1 \n");//slt rd,rs,rt
            fprintf(tp_mips,"blez $t2, %s\n",pcode[index].c);//bltz rs,offset
            //bne rs,rt,LABEL(offset)
            break;
        }
        case GEQFC: {
            tpa = searchtab(pcode[index].a);// temp var
            tpb = searchtab(pcode[index].b);
            if (tab[tpa].obj != CONSTobj) {// tmpvar var const
                if  (tab[tpa].global) {
                    fprintf(tp_mips,"lw $t0 %d($gp)\n",tab[tpa].adr);
                }
                else fprintf(tp_mips,"lw $t0 %d($sp)\n",tab[tpa].adr);

            }
            else fprintf(tp_mips,"li $t0, %d\n",tab[tpa].adr);

            if (tab[tpb].obj != CONSTobj) {
                if  (tab[tpb].global) {
                    fprintf(tp_mips,"lw $t1 %d($gp)\n",tab[tpb].adr);
                }
                else fprintf(tp_mips,"lw $t1 %d($sp)\n",tab[tpb].adr);

            }
            else fprintf(tp_mips,"li $t1, %d\n",tab[tpb].adr);

            fprintf(tp_mips,"subu $t2, $t0, $t1 \n");//slt rd,rs,rt
            fprintf(tp_mips,"bltz $t2, %s\n",pcode[index].c);//bltz rs,offset
            //bne rs,rt,LABEL(offset)
            break;
        }
        case LEQFC: {
            tpa = searchtab(pcode[index].a);// temp var
            tpb = searchtab(pcode[index].b);
            if (tab[tpa].obj != CONSTobj) {// tmpvar var const
                if  (tab[tpa].global) {
                    fprintf(tp_mips,"lw $t0 %d($gp)\n",tab[tpa].adr);
                }
                else fprintf(tp_mips,"lw $t0 %d($sp)\n",tab[tpa].adr);

            }
            else fprintf(tp_mips,"li $t0, %d\n",tab[tpa].adr);

            if (tab[tpb].obj != CONSTobj) {
                if  (tab[tpb].global) {
                    fprintf(tp_mips,"lw $t1 %d($gp)\n",tab[tpb].adr);
                }
                else fprintf(tp_mips,"lw $t1 %d($sp)\n",tab[tpb].adr);

            }
            else fprintf(tp_mips,"li $t1, %d\n",tab[tpb].adr);
            fprintf(tp_mips,"subu $t2, $t0, $t1 \n");//slt rd,rs,rt
            fprintf(tp_mips,"bgtz $t2, %s\n",pc);//bltz rs,offset
            //bne rs,rt,LABEL(offset)
            break;
        }
        case JUMPFC: {
            fprintf(tp_mips,"j %s\n",pc);
            //j label
            break;
        }
        case LABELFC: {
            fprintf(tp_mips,"%s :\n",pa);
            //Label_1:
            break;
        }
        case SWITCHFC:break;
        case NOPFC: {
            //fprintf(tp_mips,"nop\n");
            break;
        }
        default: {
            fprintf(tp_mips,"error at print mips: invalid op\n");
        }

    }

};


//其他函数

void testout (int debug) {
    if (debug == 0) {//no
        //opt_dag(mprear);//opt dag

        while (pout < prear) {//pcode
            print_pcode (pout);
            pout++;
        }
        while(mprear < prear){//mips

            create_mips(mprear);
            //create_opt_mips(mprear);
            mprear++;
        }
    }
    else if (debug == 1) {//dag

        opt_dag(pout);//opt dag
        //const_merge(pout);

        while (pout < prear) {//pcode
            print_pcode (pout);
            pout++;
        }
        while(gmprear < grear){//mips
            //create_mips(mprear);
            create_dag_mips(gmprear);
            //create_opt_mips(mprear);
            gmprear++;
        }
    }
    else if (debug == 2) {//dag and const

        opt_dag(pout);//opt dag
        const_merge(gmprear);
        opt_minute(gmprear);//delete

        while (pout < prear) {//pcode
            print_pcode (pout);
            pout++;
        }

        // fprintf(kp_dagcode,"----------------new-----------------------\n");
        while (gout < grear) {//pcode
            print_newdagpcode (gout);
            gout++;
        }

        while(gmprear < grear){//mips
            //create_mips(mprear);
            create_dag_mips(gmprear);
            //create_opt_mips(mprear);
            gmprear++;
        }
    }
    else if (debug == 3) {///dag+const+regs+delete
        //fprintf(kp_dagcode,"----------old-----------------------\n");
        opt_dag(pout);//opt dag

        const_merge(gmprear);// on opt code
        opt_minute(gmprear);//delete


        while (pout < prear) {//pcode
            print_pcode (pout);
            pout++;
        }

       // fprintf(kp_dagcode,"----------------new-----------------------\n");
        while (gout < grear) {//pcode
            print_newdagpcode (gout);
            gout++;
        }

        clr_regs();//????
        clr_globalvar_regs();//??

        alloc_globalreg(gmprear);

        while(gmprear < grear){//mips regs
            //create_mips(mprear);
            create_opt_mips(gmprear);
            //create_opt_mips(mprear);
            gmprear++;
        }
    }

    else if (debug == 3) {//regs
        opt_dag(mprear);//opt dag

        const_merge(mprear);

        while (pout < prear) {//pcode
            print_pcode (pout);
            pout++;
        }
        alloc_globalreg(mprear);
        while(mprear < prear){//mips

            create_opt_mips(mprear);
            //create_opt_mips(mprear);
            mprear++;
        }
    }
};
void setup () {
    clr_regs();//????
    inittempvar ();

    if(debug == 2)
        fprintf(tp_dag_mips,"----------dag and const-----------------------\n");
    if(debug == 1)
        fprintf(tp_dag_mips,"----------dag-----------------------\n");

    //
};
void finish_prj () {

    //一些收尾工作
    if (!fbright) {//if has main
        fbright = 0;
        error(NOTENDMAIN);
    }

    //

    tfront = 0;
    print_tab();
    errormsg();
    //print_pcode ();
    //opt_dag(0);//test dag
    //print_mips();
    fclose(fp);


    fclose(kp_tmp);               //其他输出信息
    fclose(kp_pcode);             //输出文件——优化前中间代码
   fclose(kp_dagcode);
    fclose(kp_dagandconstcode);
//    fclose(kp_opt_pcode);         //输出文件——优化后中间代码
//    fclose(tp_mips);              //输出文件——目标代码
//    fclose(tp_dag_mips);
//    fclose(tp_opt_mips);
    //fclose(kp);
    exit(0);
}















// 词法分析
void clrtoken() {           //清空token字符串
    memset(token, 0, CHARSIZE);
};

int isrsv(char* s) {        //判断保留字
    int i;
    for (i = 0; i <= KEYTYPECNT - 1; i++) {
        if (!strcmp(s, keysy[i])) {
            symbol = i;
            return 1;
        }
    }
    symbol = IDSY;
    return 0;
};
int isstringtype (char ch) {//判断字符串内容：32,33,35-126
    if (isprint(ch)&&(ch != '\"')) return 1;
    else return 0;
}

void nextch() {
    char ch;
    if (crtcc >= crtll) {
        if (feof(fp)) {
            //return;
            if (strcmp(token,"}")) error(INCOMPLETEFILE);
            else return;
            printf("End of file\n");
            finish_prj();
        }
        if (errpos != 0) {
            if (skipflag) skipmsg();
            fprintf(kp_tmp, "skip empty line \n");
            errpos = 0;
        }
        readlncnt++;
        crtll = 0;
        crtcc = 0;

        ch = fgetc(fp);
        while ((ch != '\n') && (ch != EOF)) {
            readln[crtll++] = ch;
            //fprintf(kp_tmp, "%c", ch);
            ch = fgetc(fp);
        }
        readln[crtll] = ' ';
        //fprintf(kp_tmp, "\n");
    }
    crtch = readln[crtcc++];
};


void insym () {//词法分析
insymbol:
    clrtoken();//reset全局变量
    crtnum = 0;
    numzero = 0;

    while ((crtch == ' ') || (crtch == '\t') || (crtch == '\n')) {//跳过空格、tab和换行
        nextch();
    }//为了报错位置添加nextch按行读取？

    if ((crtch == '_') || isalpha(crtch)) {//标识符
        while ((crtch == '_') || isalnum(crtch)) {
            strcat(token, &crtch);
            nextch();
        }
        isrsv(token);
    }
    else if (isdigit(crtch)) {//数字
        symbol = NUMSY;
        strcat(token, &crtch);
        if (crtch == '0') numzero = 1;
        crtnum = crtch - '0';
        nextch();
        while (isdigit(crtch)) {
            if (numzero) {//0开头多位数报错
                error(ZERONUM);
                numzero = 0;//避免重复报错
            }
            strcat(token, &crtch);
            crtnum = crtnum * 10 + (crtch - '0');
            nextch();
        }
    }
    else if (crtch == '\'') {//字符 scanf限制？
        symbol = CHARSY;
        nextch();
        if ((crtch == '+') || (crtch == '-') || (crtch == '*') || (crtch == '/')
            || isalnum(crtch) || (crtch == '_')) {//debug '_'
            strcat(token, &crtch);
        }
        else {//字符类型错误
            error(CHTYPE);
            strcat(token, &crtch);
        }
        nextch();
        if (crtch != '\'') {//字符缺少‘后缀
            error(CHBACK);
        }
        else nextch();
    }
    else if (crtch == '"') {//字符串
        symbol = STRINGSY;
        nextch();
        if (crtch == '\"')  {
            error(EMPTYSTR);
            nextch();
            return;//?
        }//空字符串
        while (isstringtype(crtch)) {
            if (crtch == '\\') {
                strcat(token,"\\");//debug
            }
            strcat(token, &crtch);
            nextch();
        }
        if (crtch != '\"')  error(STRTYPE);//字符串内容不合法
        else nextch();

        //stab

        //其他错误？

    }
    else {//分界符部分
        switch (crtch) {
            case '+': symbol = PLUSSY; strcat(token, &crtch);nextch(); break;
            case '-': symbol = MINUSSY; strcat(token, &crtch);nextch(); break;
            case '*': symbol = TIMESSY; strcat(token, &crtch);nextch(); break;
            case '/': symbol = DIVSY; strcat(token, &crtch);nextch(); break;
            case '(': symbol = LPARSY; strcat(token, &crtch);nextch(); break;
            case ')': symbol = RPARSY; strcat(token, &crtch);nextch(); break;
            case '[': symbol = LBKTSY; strcat(token, &crtch);nextch(); break;
            case ']': symbol = RBKTSY; strcat(token, &crtch);nextch(); break;
            case '{': symbol = LCRBSY; strcat(token, &crtch);nextch(); break;
            case '}': symbol = RCRBSY; strcat(token, &crtch);nextch(); break;
            case ',': symbol = COMMASY; strcat(token, &crtch);nextch(); break;
            case ';': symbol = SEMISY; strcat(token, &crtch);nextch(); break;
            case ':': symbol = COLONSY; strcat(token, &crtch);nextch(); break;
            case '<': {
                symbol = LESSY;
                strcat(token, &crtch);
                nextch();
                if (crtch == '=') {
                    symbol = LEQSY;
                    strcat(token, &crtch);
                    nextch();
                }
                break;
            }
            case '>': {
                symbol = GRTSY;
                strcat(token, &crtch);
                nextch();
                if (crtch == '=') {
                    symbol = GEQSY;
                    strcat(token, &crtch);
                    nextch();
                }
                break;
            }
            case '!': {//!=
                strcat(token, &crtch);
                nextch();
                if (crtch == '=') {
                    symbol = NEQSY;
                    strcat(token, &crtch);
                    nextch();
                    break;
                }
                else {// single !
                    error(SINEXC);
                    goto insymbol;//再读一个
                }
            }
            case '=': {// ==或=
                strcat(token, &crtch);
                nextch();
                if (crtch == '=') {
                    symbol = EQLSY;//==
                    strcat(token, &crtch);
                    nextch();
                }
                else {
                    symbol = ASSIGNSY;//=
                }
                break;
            }
            case EOF: nextch();strcat(token, &crtch);break;//?
            default: {//非法字符
                strcat(token, &crtch);
                error(INVALIDSYM);
                nextch();
                goto insymbol;//重新读取
                break;
            }
        };//switch case
    }//分界符部分
}

//语法分析

//检查first是否合法
int  testbegsys (int *target, int len, int sym) {
    len--;
    while (len>=0) {
        if(sym == target[len]) return 1;
        len--;
    }
    return 0;
};

//＜参数＞ ::=  int|char＜标识符＞
void parameter () {
    //test_uni(PARA);

    if (symbol == INTSY) tab[tx].paratype[tmp_paranum] = INTtyp;
    else if (symbol == KEYCHARSY) tab[tx].paratype[tmp_paranum] = CHARtyp;
    else error(PARATYPE);//类型标识符
    insym();
    if (symbol != IDSY) error(IDENT);
    else {


        strcpy(tmp_name,token);
    }
    insym();
    printf("This is a parameter\n");
};

//＜参数表＞ ::= ＜参数＞{,＜参数＞}| ＜空>//没有空的判断，在调用前处理
void paralist () {
    tmp_paranum = 0;
    parameter();
    while (symbol == COMMASY) {
        insym();
        parameter();
    }
    printf("This is a paralist\n");
};

//＜无符号整数＞ ::= ＜非零数字＞｛＜数字＞｝| 0
void unsigned_integer(int i) {//是否非0
    if (symbol != NUMSY) error(NUM);
    if (i) if (crtnum == 0) error(NOTZERO);//非0
    //insym();
    printf("This is an unsigned integer\n");

};
//＜整数＞ ::= ［＋｜－］＜无符号整数＞
void integer() {
    int sign = 0;
    if ((symbol == PLUSSY) || (symbol == MINUSSY)) {
        sign = (symbol == PLUSSY)? 1: -1;
        insym();
        unsigned_integer(0);
        if (sign) crtnum = sign * crtnum;
    }
    else  unsigned_integer(0);
    printf("This is an integer\n");
};


expr expr_clr (expr i) {
    i.obj = 0;
    memset(i.inf, 0, IDMAX);
    i.result = 0;
    i.typ = NOtyp;
    return i;
};

expr factor(void);
//＜项＞ ::= ＜因子＞{＜乘法运算符＞＜因子＞}
expr term() {
    int sign = 0;
    expr ret_term = {0,0,0,{0}}, tmp_factor = {0,0,0,{0}};
    //ret_term = expr_clr(ret_term);
    ret_term = factor();
    while ((symbol == TIMESSY) || (symbol == DIVSY)) {
        sign = (symbol == TIMESSY)? 1 : -1;
        ret_term.typ = INTtyp;
        insym();
        tmp_factor = factor();
        if ((ret_term.typ == CONSTobj) && (tmp_factor.typ == CONSTobj)) {
            if (sign == 1) {//*
                ret_term.result = ret_term.result * tmp_factor.result;
            }
            else {// 除法
                if (tmp_factor.result == 0) {
                    error(DIVZERO);
                    ret_term.result = 0;
                    return ret_term;
                }
                else ret_term.result = ret_term.result / tmp_factor.result;
            }
        }
        else ret_term.typ = VARobj;

        create_id(INTtyp);
        strcpy(tmp_pc,nid);
        strcpy(tmp_pa,ret_term.inf);
        strcpy(tmp_pb,tmp_factor.inf);
        (sign == 1)? enterpcode(TIMESFC) : enterpcode(DIVFC);
        strcpy(ret_term.inf,nid);

    }
    printf("This is a term\n");

    return ret_term;
};

//＜表达式＞ ::= ［＋｜－］＜项＞{＜加法运算符＞＜项＞}   //[+|-]只作用于第一个<项>
expr expression () {
    int sign = 0;
    expr tmp_term = {0,0,0,{0}}, ret_exp = {0,0,0,{0}};
    //expr_clr(ret_exp);
    //if(!testbegsys(expbegsys,5,symbol)) error();
    if ((symbol == PLUSSY) || (symbol == MINUSSY)) {//［＋｜－］
        ret_exp.typ = INTtyp;
        sign = (symbol == PLUSSY)? 1 : -1;
        insym();
    }
    ret_exp = term();//＜项＞
    if (sign < 0) {//[-]
        create_id(INTtyp);
        strcpy(tmp_pc,nid);
        strcpy(tmp_pa,"0");
        strcpy(tmp_pb,"\0");
        enterpcode(ASSIGNFC);// temp = 0
        create_id(INTtyp);
        strcpy(tmp_pa,tmp_pc);
        strcpy(tmp_pc,nid);
        strcpy(tmp_pb,ret_exp.inf);
        enterpcode(MINUSFC);// temp2 = temp - [term]
        strcpy(ret_exp.inf,nid);// amend to [-term]
    }
    if (sign) {
        ret_exp.typ = INTtyp;//强制类型转换
        if (ret_exp.obj == CONSTobj) ret_exp.result = sign * ret_exp.result;
    }

    while ((symbol == PLUSSY) || (symbol == MINUSSY)) {//＜加法运算符＞
        sign = (symbol == PLUSSY)? 1 : -1;
        ret_exp.typ = INTtyp;//强制类型转换
        insym();
        tmp_term = term();//＜项＞
        if ((ret_exp.obj == CONSTobj) && (tmp_term.obj == CONSTobj)) {
            ret_exp.result = (sign == 1)? (ret_exp.result + tmp_term.result) : (ret_exp.result - tmp_term.result);
        }
        else ret_exp.obj = VARobj;
        create_id(INTtyp);
        strcpy(tmp_pc,nid);
        strcpy(tmp_pa,ret_exp.inf);
        strcpy(tmp_pb,tmp_term.inf);
        (sign == 1)? enterpcode(PLUSFC) : enterpcode(MINUSFC);
        strcpy(ret_exp.inf,nid);
    }
    printf("This is a expression\n");
    return ret_exp;
};

//＜因子＞ ::= ＜标识符＞｜＜标识符＞'['＜表达式＞']'|'('＜表达式＞')'｜＜整数＞|＜字符＞｜＜有返回值函数调用语句＞
expr factor() {
    int i = 0;
    int t = -1;
    char push[PARAMAX][IDMAX];
    int pcnt = 0;
    char crtnum_str[IDMAX];
    expr ret_factor = {0,0,0,{0}}, tmp_exp = {0,0,0,{0}}, tmp_para = {0,0,0,{0}};;
    //ret_factor = expr_clr(ret_factor);
    if (symbol == CHARSY) {//＜字符＞
        create_id(CHARtyp);
        strcpy(tmp_pc,nid);
        strcpy(tmp_pa,"\'");
        strcat(tmp_pa, token);
        strcat(tmp_pa,"\'");// '[ch]'
        strcpy(tmp_pb,"\0");
        enterpcode(ASSIGNFC);// temp = '[ch]'
        strcpy(ret_factor.inf,nid);
        ret_factor.typ = CHARtyp;
        ret_factor.result = token[0] - '0' + 48;//?
        insym();

    }
    else if (((symbol == PLUSSY) || (symbol == MINUSSY)) || (symbol == NUMSY)) {//＜整数＞
        integer();
        create_id(INTtyp);
        strcpy(tmp_pc,nid);
        sprintf(crtnum_str,"%d",crtnum);
        strcpy(tmp_pa,crtnum_str);
        strcpy(tmp_pb,"\0");
        enterpcode(ASSIGNFC);// temp = number
        strcpy(ret_factor.inf,nid);
        ret_factor.typ = INTtyp;
        ret_factor.result = crtnum;
        insym();
    }
    else if (symbol == LPARSY) {//(
        insym();
        ret_factor = expression();//'('＜表达式＞')'
        ret_factor.typ = INTtyp;//debug
        create_id(ret_factor.typ);
        strcpy(tmp_pc,nid);
        strcpy(tmp_pa,ret_factor.inf);
        strcpy(tmp_pb,"\0");
        enterpcode(ASSIGNFC);//temp = [exp]
        strcpy(ret_factor.inf,nid);//amend
        if (symbol != RPARSY) error(RP);//)
        insym();//next
    }
    else if (symbol == IDSY) {//＜标识符＞
        t = searchtab(token);
        if (t < 0) {
            error(NOID);
        }
        ret_factor.typ = tab[t].typ;
        strcpy(ret_factor.inf,tab[t].name);
        if (tab[t].obj == VARobj) {
            ret_factor.obj =  VARobj;
        }
        else if (tab[t].obj == CONSTobj) {
            //?
            ret_factor.obj =  CONSTobj;
            ret_factor.result = tab[t].adr;
        }
        insym();

        if (symbol == LBKTSY) {//＜标识符＞'['＜表达式＞']'
            if ((tab[t].typ == INTARRAYtyp) || (tab[t].typ == CHARARRAYtyp)) ret_factor.typ = (tab[t].typ == INTARRAYtyp)? INTtyp : CHARtyp;
            else {
                error(WRONGTYPEARRAY);
                ret_factor.typ = NOtyp;
            }
            insym();
            tmp_exp = expression();
            if (tmp_exp.typ != INTtyp) {
                error(AHNOTINT);//?
            }
            if (tmp_exp.obj == CONSTobj) {
                if ((tmp_exp.result >= tab[t].ah) || (tmp_exp.result < 0)) {
                    error(WRONGARRAYINDEX);
                }
            }

            create_id(ret_factor.typ);
            strcpy(tmp_pc,nid);
            strcpy(tmp_pa,tab[t].name);
            strcpy(tmp_pb,tmp_exp.inf);
            enterpcode(ARRRFC);// temp = a[]
            strcpy(ret_factor.inf,nid);

            if (symbol != RBKTSY) error(RB);//]
            insym();//next
        }

        //＜有返回值函数调用语句＞ ::= ＜标识符＞'('＜值参数表＞')'
        if (symbol == LPARSY) {//＜有返回值函数调用语句＞
            if (tab[t].obj != FUNCobj) {
                error(FUNCIDENTTYPE);
            }
            if (tab[t].typ == VOIDtyp) {
                error(VOIDFUNC);
            }
            ret_factor.typ = tab[t].typ;
            insym();
            if (symbol != RPARSY) {//不为空
                tmp_para = expression();
                if (tmp_para.typ != tab[t].paratype[i++]) {
                    error(PARANOTMATCH);
                }
                strcpy(push[pcnt++],tmp_para.inf);
                while (symbol == COMMASY) {
                    insym();
                    tmp_para = expression();
                    if (tmp_para.typ != tab[t].paratype[i++]) {
                        error(PARANOTMATCH);
                    }
                    strcpy(push[pcnt++],tmp_para.inf);
                }
                if (symbol != RPARSY) error(RP);//)
                if (i != tab[t].paranum) {
                    error(WRONGPARANUM);
                }
            }
            else if (tab[t].paranum) {
                error(WRONGPARANUM);
            }
            strcpy(tmp_pc,tab[t].name);//debug for mips
            char str_i[10];
            for (i = 0; i < pcnt; i++) {
                strcpy(tmp_pa,push[i]);
                sprintf(str_i,"%d",i);
                strcpy(tmp_pb,str_i);
                enterpcode(PUSHFC);//paraname cnt funcname
            }
            strcpy(tmp_pa,tab[t].name);
            strcpy(tmp_pb,"\0");
            strcpy(tmp_pc,"\0");
            enterpcode(SASCENEFC);
            enterpcode(OPSTACKFC);
            enterpcode(CALLFC);
            enterpcode(RESTACKFC);
            enterpcode(RESCENEFC);

            create_id(tab[t].typ);
            strcpy(tmp_pa,nid);//debug
            enterpcode(FRETFC);//temp = RET
            strcpy(ret_factor.inf,nid);//amend
            insym();//next
            printf("This is a called returned function statement^^^^^as a factor\n");
        }
        else {//just ident
            create_id(ret_factor.typ);
            strcpy(tmp_pc,nid);
            strcpy(tmp_pb,"\0");
            strcpy(tmp_pa,ret_factor.inf);
            enterpcode(ASSIGNFC);// temp = ident
            strcpy(ret_factor.inf,nid);
        }
    }
    else {
        error(FACTORTYPE);
        insym();
    }
    printf("This is a factor\n");
    return ret_factor;

};


//＜值参数表＞   ::= ＜表达式＞{,＜表达式＞}｜＜空＞//调用时已经处理空情况
void paravaluelist () {
    expression();
    while (symbol == COMMASY) {
        insym();
        expression();
    }
    printf("This is a paravalue list\n");
};





//＜条件＞ ::= ＜表达式＞＜关系运算符＞＜表达式＞｜＜表达式＞ //表达式为0条件为假，否则为真
void condition () {
    expr ret_exp,tmp_exp;
    int lgsy;
    char lab[10];
    strcpy(lab,nlabel);
    strcpy(tmp_pc,lab);
    ret_exp = expression();
    if (ret_exp.typ == CHARtyp) error(CONDITIONTYPE);
    //EQLSY,NEQSY,LESSY,LEQSY,GRTSY,GEQSY,
    if ((symbol == EQLSY) || (symbol == NEQSY) ||
        (symbol == LESSY) || (symbol == LEQSY) ||
        (symbol == GRTSY) || (symbol == GEQSY)) {//＜关系运算符＞
        lgsy = symbol;
        insym();
        tmp_exp = expression();
        if (ret_exp.typ == CHARtyp) error(CONDITIONTYPE);
        strcpy(tmp_pa,ret_exp.inf);
        strcpy(tmp_pc,syms[lgsy]);
        strcpy(tmp_pb,tmp_exp.inf);
        enterpcode(LGFC);// [exp] [LG] [exp]
        strcpy(tmp_pc,lab);//debug
        switch(lgsy) {//debug
            case NEQSY:enterpcode(BNEFC);break;
            case EQLSY:enterpcode(BEQFC);break;
            case LESSY:enterpcode(LESFC);break;
            case LEQSY:enterpcode(LEQFC);break;
            case GRTSY:enterpcode(GRTFC);break;
            case GEQSY:enterpcode(GEQFC);break;
            default: break;
        }
    }
    else {//＜表达式＞
        strcpy(tmp_pa,ret_exp.inf);
        strcpy(tmp_pc,"==");
        strcpy(tmp_pb,"0");
        enterpcode(LGFC);// [exp] == 0 //debug
        strcpy(tmp_pc,lab);//debug
        strcpy(tmp_pa,ret_exp.inf);
        strcpy(tmp_pb,"0");
        enterpcode(BNEFC);
    }
    printf("This is a condition exp\n");
};

//＜条件语句＞ ::=  if '('＜条件＞')'＜语句＞
void statement_if () {
    //判断过first之后跳转到此函数
    char lab[10];
    create_label();
    strcpy(lab,nlabel);
    insym();
    if (symbol != LPARSY) error(LP);//(
    insym();
    condition();
    if (symbol != RPARSY) error(RP);//)
    insym();
    statement();
    strcpy(tmp_pa,lab);
    strcpy(tmp_pc,"\0");
    strcpy(tmp_pb,"\0");
    enterpcode(LABELFC);
    printf("This is a if-condition statement\n");
};

//＜循环语句＞ ::= while '('＜条件＞')'＜语句＞
void statement_while () {
    char lab_while[10],lab_next[10];
    create_label();
    strcpy(lab_while,nlabel);
    strcpy(tmp_pa,lab_while);
    strcpy(tmp_pc,"\0");
    strcpy(tmp_pb,"\0");
    enterpcode(LABELFC);
    create_label();
    strcpy(lab_next,nlabel);
    strcpy(tmp_pa,lab_next);
    insym();
    if (symbol != LPARSY) error(LP);//(
    insym();
    condition();
    if (symbol != RPARSY) error(RP);//)
    insym();
    statement();
    strcpy(tmp_pc,lab_while);
    strcpy(tmp_pa,"\0");
    strcpy(tmp_pb,"\0");
    enterpcode(JUMPFC);
    strcpy(tmp_pc,"\0");
    strcpy(tmp_pb,"\0");
    strcpy(tmp_pa,lab_next);//debug
    enterpcode(LABELFC);
    printf("This is a while statement\n");
};

//＜读语句＞ ::=  scanf '('＜标识符＞{,＜标识符＞}')'
void statement_scanf () {
    int t;
    insym();
    if (symbol != LPARSY) error(LP);//(
    insym();
label_scanf_1:
    if (symbol != IDSY) {
        ;
        error(IDENT);
        insym();
    }
    else {
        t = searchtab(token);
        if (t < 0) error(PARAINVALID);
        if ((tab[t].obj != VARobj) ||
            ((tab[t].typ != INTtyp) && (tab[t].typ != CHARtyp))) error(WRONGVAL);
        strcpy(tmp_pa,tab[t].name);
        strcpy(tmp_pb,"\0");
        strcpy(tmp_pc,"\0");

        enterpcode(SCANFFC);// read [var]
        insym();
    }
    while (symbol == COMMASY) {
        insym();
        goto label_scanf_1;
    }
    if (symbol != RPARSY) error(RP);//)
    insym();
    printf("This is a scanf statement\n");
};
//＜写语句＞ ::= printf '(' ＜字符串＞,＜表达式＞ ')'| printf '('＜字符串＞ ')'| printf '('＜表达式＞')'

void statement_printf () {
    expr tmp_exp;
    insym();
    if (symbol != LPARSY) error(LP);//(
    insym();
    if (symbol == STRINGSY) {//＜字符串＞
        strcnt++;
        sprintf(strlab,"%d",strcnt);
        strcpy(tmp_pa,strlab);//debug
        strcpy(tmp_pc,"\0");
        strcpy(tmp_pb,"\0");
        enterpcode(PRINTFSTRFC);

        insym();
        if (symbol == COMMASY) {//,
            insym();
            tmp_exp = expression();//＜表达式＞
            strcpy(tmp_pa,tmp_exp.inf);
            strcpy(tmp_pc,"\0");
            strcpy(tmp_pb,"\0");
            enterpcode(PRINTFFC);
        }
    }
    else {//＜表达式＞
        tmp_exp = expression();
        strcpy(tmp_pa,tmp_exp.inf);
        strcpy(tmp_pc,"\0");
        strcpy(tmp_pb,"\0");
        enterpcode(PRINTFFC);
    }
    if (symbol != RPARSY) error(RP);//)
    insym();
    printf("This is a printf statement\n");
};

//＜缺省＞ ::=  default : ＜语句＞//
void default_subs() {
    insym();
    if (symbol != COLONSY) error(COLON);
    insym();
    statement();
    printf("This is a default\n");
};


//＜常量＞   ::=  ＜整数＞|＜字符＞
void constant () {
    if ((symbol == PLUSSY) || (symbol == MINUSSY) || (symbol == NUMSY)) integer();
    else if (symbol != CHARSY) {
        error(LABELTYPE);
    }
    else insym();//next
    printf("This is a constant as a label\n");
};

//＜情况子语句＞  ::=  case＜常量＞：＜语句＞
void case_subs() {
    if (symbol != CASESY) error(NOTCASE);
    insym();
    constant();
    if (symbol != COLONSY) error(COLON);//:
    insym();
    statement();
    printf("This is a case sub-statement\n");
};


//＜情况表＞ ::= ＜情况子语句＞{＜情况子语句＞}
void casetable () {
    case_subs();//debug
    while (symbol == CASESY) {
        case_subs();
    }
    printf("This is a case table\n");
};


//＜情况语句＞ ::= switch '('＜表达式＞')' '{'＜情况表＞＜缺省＞ '}'
void statement_switch () {
    int i;
    char labs[CASEMAX][IDMAX];
    int labcnt = 0;
    char label_nextcase[IDMAX],label_end[IDMAX];
    char crtnum_ch[IDMAX];
    expr tmp_exp;
    create_label();
    strcpy(label_end,nlabel);
    insym();
    if (symbol != LPARSY) error(LP);//(
    insym();
    tmp_exp = expression();//＜表达式＞
    create_id(tmp_exp.typ);
    strcpy(tmp_pa,tmp_exp.inf);
    strcpy(tmp_pc,nid);
    strcpy(tmp_pb,"\0");
    enterpcode(ASSIGNFC);// temp = [exp]
    strcpy(tmp_exp.inf,nid);// amend
    if (symbol != RPARSY) error(RP);//)
    insym();
    if (symbol != LCRBSY) error(LC);//{
    insym();
    // test_uni(CASEDEF);
    if (symbol != CASESY) {
        error(NOTCASE);
        insym();
    }
label_switch_1:
    insym();
    if ((symbol == PLUSSY) || (symbol == MINUSSY) || (symbol == NUMSY)) {
        integer();
        sprintf(crtnum_ch,"%d",crtnum);
        if (tmp_exp.typ != INTtyp) error(CASELABELNOTMATCH);
        for (i = 0; i< labcnt; i++) {
            if (!strcmp(crtnum_ch, labs[i])) {
                error(MULTILAB);
                break;
            }
        }
        strcpy(labs[labcnt++],crtnum_ch);

        strcpy(tmp_pa,tmp_exp.inf);
        strcpy(tmp_pb,crtnum_ch);
        create_label();
        strcpy(label_nextcase,nlabel);
        strcpy(tmp_pc,label_nextcase);
        enterpcode(CASEFC);// temp == num


    }
    else if (symbol == CHARSY) {
        if (tmp_exp.typ != CHARtyp)  error(CASELABELNOTMATCH);
        for (i = 0; i< labcnt; i++) {
            if (!strcmp(crtnum_ch, labs[i])) {
                error(MULTILAB);
                break;
            }
        }
        strcpy(labs[labcnt++],token);

        strcpy(tmp_pa,tmp_exp.inf);
        strcpy(tmp_pb,"\'");
        strcat(tmp_pb, token);
        strcat(tmp_pb,"\'");// '[ch]'

        create_label();
        strcpy(label_nextcase,nlabel);
        strcpy(tmp_pc,label_nextcase);

        enterpcode(CASEFC);// temp == '[ch]'



    }
    else {
        //error(LABELTYPE);//next
        int skips[] = {SEMISY};
        skip(skips,LABELTYPE,symbol);
        insym();
        goto label_switch_next;//
    }
    insym();
    if (symbol != COLONSY) error(COLON);//:
    insym();
    statement();
    strcpy(tmp_pc,label_end);
    strcpy(tmp_pa,"\0");
    strcpy(tmp_pb,"\0");
    enterpcode(JUMPFC);// goto end
    strcpy(tmp_pa,label_nextcase);
    strcpy(tmp_pc,"\0");
    strcpy(tmp_pb,"\0");
    enterpcode(LABELFC);//label_next:
label_switch_next:
    while (symbol == CASESY) {
        goto label_switch_1;
    }
    if (symbol != RCRBSY) {//default不为空
        if (symbol != DEFAULTSY) {
            error(NODEFAULT);
            int skips[] = {RCRBSY};
            skip(skips,LABELTYPE,symbol);
            insym();
            return;
        }
        insym();
        if (symbol != COLONSY) error(COLON);//:
        insym();
        statement();
        printf("This is a default\n");
        if (symbol != RCRBSY) error(RC);//}
    }
    strcpy(tmp_pa,label_end);//debug
    strcpy(tmp_pc,"\0");
    strcpy(tmp_pb,"\0");
    enterpcode(LABELFC);//label_end:
    insym();//next
    printf("This is a switch-case statement\n");
};

//＜返回语句＞ ::= return ['('＜表达式＞')']//[]可有可无
void statement_return () {
    expr tmp_exp = {0,0,0,{0}};
    //if (!isreturnfunc) error(VOIDHASRETURN);//debug
    insym();
    if (symbol == LPARSY) {// (
        insym();
        tmp_exp = expression();//＜表达式＞
        if (tmp_exp.typ != isreturnfunc) error(RETURNTYPE);
        if (symbol != RPARSY) error(RP);// )
        strcpy(tmp_pa,tmp_exp.inf);
        strcpy(tmp_pb,"\0");
        strcpy(tmp_pc,"\0");
        enterpcode(RETFC);//ret [expres]
        insym();
    }
    else if (symbol == SEMISY) {//return ;
        if (isreturnfunc) error(NORETURN);

        //?
        strcpy(tmp_pa,"\0");
        strcpy(tmp_pb,"\0");
        strcpy(tmp_pc,"\0");
        if (ismain) {
            strcpy(tmp_pa,"main");
            enterpcode(RESTACKFC);
        }
        enterpcode(VRETFC);//ret;


    }
    else error(NORETURN);
    printf("This is a return statement\n");
};




//＜有返回值函数调用语句＞ ::= ＜标识符＞'('＜值参数表＞')'
//＜无返回值函数调用语句＞ ::= ＜标识符＞'('＜值参数表＞')'
void call_rfunc() {
    if (symbol != IDSY) error(CALLIDENT);//＜标识符＞
    insym();
    if (symbol != LPARSY) error(LP);//(
    insym();
    if (symbol != RPARSY) {//值参数表不为空
        paravaluelist();
        if (symbol != RPARSY) error(RP);//)
        insym();
    }
    else insym();//值参数表为空
    printf("This is a call returned function statement\n");
};

//＜语句＞ ::= ＜条件语句＞｜＜循环语句＞| '{'＜语句列＞'}'
//           |＜有返回值函数调用语句＞;|＜无返回值函数调用语句＞;
//          ｜＜赋值语句＞;｜＜读语句＞;｜＜写语句＞;｜＜空＞;|＜情况语句＞｜＜返回语句＞;

void statement() {
    int i = 0;
    int t;
    expr tmp_para;
    char push[PARAMAX][IDMAX];
    int pcnt = 0;
    if (symbol == LCRBSY) {//'{'＜语句列＞'}'
        insym();
        statement_list();
        if (symbol != RCRBSY)  error(RC);//}
        insym();//next
    }
    else if (symbol == SEMISY) {//＜空＞;
        insym();//next
        printf("This is a empty statement, it's fine\n");
        return;
    }
    else if (symbol == IFSY) {//＜条件语句＞
        statement_if();
    }
    else if (symbol == WHILESY) {//＜循环语句＞
        statement_while();
    }
    else if (symbol == SWITCHSY) {//＜情况语句＞
        statement_switch();
    }
    else if (symbol == SCANFSY) {//＜读语句＞;
        statement_scanf();
        if (symbol != SEMISY) error(SEMI);//;
        insym();
    }
    else if (symbol == PRINTFSY) {//＜写语句＞;
        statement_printf();
        if (symbol != SEMISY) error(SEMI);//;
        insym();
    }
    else if (symbol == RETURNSY) {//＜返回语句＞;
        statement_return();
        if (symbol != SEMISY) error(SEMI);//;
        insym();
    }
    else if (symbol == IDSY) {//标识符
        t = searchtab(token);
        if (t < 0) error(PARAINVALID);
        insym();
        //＜有返回值函数调用语句＞ ::= ＜标识符＞'('＜值参数表＞')'
        //＜无返回值函数调用语句＞ ::= ＜标识符＞'('＜值参数表＞')'
        if (symbol == LPARSY) {// '('
            if (tab[t].obj != FUNCobj) {
                error(FUNCIDENTTYPE);
            }
            insym();
            if (symbol != RPARSY) {//值参数表不为空
            label_state_1:
                tmp_para = expression();
                if (tmp_para.typ != tab[t].paratype[i++]) {
                    error(PARANOTMATCH);
                }
                strcpy(push[pcnt++],tmp_para.inf);
                while (symbol == COMMASY) {
                    insym();
                    goto label_state_1;
                }
                if (i != tab[t].paranum) {
                    error(WRONGPARANUM);
                }
                if (symbol != RPARSY) error(RP);//)
                insym();
                if (symbol != SEMISY) error(SEMI);//;
            }
            else {//值参数表为空
                if (tab[t].paranum) {
                    error(WRONGPARANUM);
                }
                insym();
                if (symbol != SEMISY) error(SEMI);//;
            }
            char str_i[10];
            strcpy(tmp_pc,tab[t].name);
            for (i = 0; i < pcnt; i++) {
                strcpy(tmp_pa,push[i]);
                sprintf(str_i,"%d",i);
                strcpy(tmp_pb,str_i);

                enterpcode(PUSHFC);
            }
            strcpy(tmp_pa,tab[t].name);
            enterpcode(SASCENEFC);
            enterpcode(OPSTACKFC);
            enterpcode(CALLFC);
            enterpcode(RESTACKFC);
            enterpcode(RESCENEFC);

            /* if ((tab[t].typ == INTtyp) || (tab[t].typ == CHARtyp)){
             create_id(tab[t].typ);
             strcpy(tmp_pa,nid);
             enterpcode(FRETFC);//temp = RET
             }*/
            insym();
            printf("This is a call function statement\n");

        }
        //＜赋值语句＞ ::= ＜标识符＞＝＜表达式＞|＜标识符＞'['＜表达式＞']'=＜表达式＞
        else if ((symbol == ASSIGNSY)||(symbol == LBKTSY)) {//= [
            expr tmp_exp;
            expr tmp_exp2;
            if (tab[t].obj != VARobj) {
                error(NOTASSIGN);//debug
            }

            if (symbol == ASSIGNSY) {//=
                if ((tab[t].typ != INTtyp) && (tab[t].typ != CHARtyp)) error(NOTASSIGN);//debug
                insym();
                tmp_exp = expression();
                if (tmp_exp.typ != tab[t].typ) error(ASSIGNNOTMATCH);
                strcpy(tmp_pc,tab[t].name);//debug
                strcpy(tmp_pa,tmp_exp.inf);
                strcpy(tmp_pb,"\0");
                enterpcode(ASSIGNFC);// [id] = [exp]
            }//?char = int

            else if (symbol == LBKTSY) {//[
                if ((tab[t].typ != INTARRAYtyp) && (tab[t].typ != CHARARRAYtyp)) error(NOTASSIGN);//debug
                insym();
                tmp_exp = expression();
                if (tmp_exp.typ != INTtyp) error(AHNOTINT);
                if ((tmp_exp.obj == CONSTobj) && ((tmp_exp.result >= tab[t].ah) || (tmp_exp.result < 0))) {
                    error(WRONGARRAYINDEX);//debug
                }

                if (symbol != RBKTSY) error(RB);//]
                insym();
                if (symbol != ASSIGNSY) error(EQ);//=
                insym();
                tmp_exp2 = expression();
                if (((tab[t].typ == INTtyp) || (tab[t].typ ==INTARRAYtyp)) && (tmp_exp2.typ != INTtyp)) error(ASSIGNNOTMATCH);
                if (((tab[t].typ == CHARtyp) || (tab[t].typ ==CHARARRAYtyp)) && (tmp_exp2.typ != CHARtyp)) error(ASSIGNNOTMATCH);//debug
                strcpy(tmp_pa,tmp_exp2.inf);
                strcpy(tmp_pc,tab[t].name);
                strcpy(tmp_pb,tmp_exp.inf);
                enterpcode(ARRLFC);// a[exp] = [exp2]
            }
            if (symbol != SEMISY) error(SEMI);//;
            insym();
            printf("This is a assign statement\n");
        }
    }
    else {
        error(STATETYPE);
        insym();
    }
    //pritnf("This is a statement\n");
};



//＜语句列＞ ::=｛＜语句＞｝//语句列空的情况在调用时已处理，此时不用处理空
void statement_list() {
    //if (!testbegsys(statebegsys,10,symbol)) error();
    while (testbegsys(statebegsys,10,symbol)){//判断语句的begsys
        statement();
    }
    printf("This is a statement list\n");
};



//＜变量定义＞ ::=int|char (＜标识符＞|＜标识符＞'['＜无符号整数＞']')
//              {,(＜标识符＞|＜标识符＞'['＜无符号整数＞']' )}
//  ＜无符号整数＞表示数组元素的个数，其值需大于0
void var_def() {
    int typ;
    //test_uni(VARDEF);
    if ((symbol == INTSY) || (symbol == KEYCHARSY)){
        tmp_typ = (symbol == INTSY)? INTtyp :CHARtyp;
        typ = tmp_typ;
        insym();
    label_vard_1:
        if (symbol != IDSY) {

            error(IDENT);
            insym();
        }
        else {

            strcpy(tmp_name,token);

            tmp_typ = typ;
            insym();
            if (symbol == LBKTSY) {//[
                insym();
                unsigned_integer(1);//无符号整数
                tmp_ah = crtnum;//debug
                insym();
                tmp_typ = (tmp_typ == INTtyp)? INTARRAYtyp : CHARARRAYtyp;

                if (symbol != RBKTSY) error(RB);//]
                insym();//next
            }
            entertab();
            while (symbol == COMMASY) {//,
                insym();
                goto label_vard_1;
            }
        }
    }
    else error (IDENTTYPE);
    printf("This is a variable defination\n");
};

//＜变量说明＞ ::= ＜变量定义＞;{＜变量定义＞;}
void var_dclr() {
    tmp_global = 0;
    tmp_obj = VARobj;
    while ((symbol == INTSY) || (symbol == KEYCHARSY)) {//varbegsys
        var_def();//＜变量定义＞
        if (symbol != SEMISY)  error(SEMI);//;
        insym();
    }
    printf("This is a variable declaration\n");
};


//＜复合语句＞ ::=［＜常量说明＞］［＜变量说明＞］＜语句列＞
void complex_statement () {
    if (symbol == CONSTSY) {//有［＜常量说明＞］
        const_dclr();
    }
    if ((symbol == INTSY) || (symbol == KEYCHARSY)) {//有［＜变量说明＞］
        var_dclr();
    }
    if (testbegsys(statebegsys,10,symbol)) {//语句列不为空
        statement_list();
    }
    else if (symbol != RCRBSY) error(RC);
    //复合语句为空，此时symbol = ‘}’
    printf("This is a complex statments\n");
};




//＜有返回值函数定义＞ ::=  ＜标识符＞'('＜参数表＞')' '{'＜复合语句＞'}'
void rfunc_def () {
    char funcname[IDMAX] = {0};
    tmp_typ = (symbol == INTSY)? INTtyp : CHARtyp;
    isreturnfunc = tmp_typ;
    int t = -1;
    int i = 0;

    insym();
    if (symbol != IDSY) {

        error(IDENT);
        insym();
    }
    else {
        strcpy(tmp_name,token);
        t = trear;//函数头字符表位置
        strcpy(tmp_pb, keysy[tmp_typ]);//type
        strcpy(tmp_pa,tmp_name);//id
        strcat(tmp_pa,"_f");//rename func with_f
        strcpy(tmp_pc,"\0");

        strcpy(funcname,tmp_name);//id

        enterpcode(FUNCFC);
        entertab();




        tmp_global = 0;
        tmp_obj = VARobj;//debug
        insym();
        if (symbol != LPARSY) error(LP);// '('
        insym();
        if (symbol == RPARSY) {// ')' 参数为空
            tfront = trear;
            insym();
            if (symbol != LCRBSY)  error(LC);//{
            insym();
            tmp_obj = VARobj;//debug
            complex_statement();//复合语句
            if (symbol != RCRBSY)  error(RC);//}

        }
        else {//参数不为空
        label_pro_2:
            //test_uni(PARA);
            if ((symbol != INTSY) && (symbol != KEYCHARSY)) {
                error(PARATYPE);
                return;
            }
            if(symbol == INTSY){
                tmp_typ = INTtyp;
                tab[t].paratype[i++] = INTtyp;
            }
            else if (symbol == KEYCHARSY){
                tmp_typ = CHARtyp;
                tab[t].paratype[i++] = CHARtyp;
            }
            insym();
            if (symbol != IDSY) {
                ;
                error(IDENT);
                insym();
            }
            else {
                strcpy(tmp_name,token);
                strcpy(tmp_pa, keysy[tmp_typ]);//type
                strcpy(tmp_pb,tmp_name);//id

                strcpy(tmp_pc,funcname);//func

                tab[t].paranum++;
                enterpcode(PARAFC);//参数生成pcode:para [type] [id]
                entertab();//参数入符号表
                tab[trear-1].ispara = 1;
                tab[trear-1].paranum = tab[t].paranum-1;
                insym();
            }

            while (symbol == COMMASY) {
                insym();
                goto label_pro_2;
            }
            if (symbol != RPARSY)  error(RP);//)
            insym();
            if (symbol != LCRBSY)  error(LC);//{
            insym();
            tmp_obj = VARobj;//debug
            complex_statement();
            if (symbol != RCRBSY)  error(RC);//}
        }
    }
    strcpy(tmp_pa,tab[t].name);//funcname//not main is ok

    strcpy(tmp_pb,"\0");
    strcpy(tmp_pc,"\0");
    enterpcode(VRETFC);
    tab[t].adr = dx;//debug

    testout(debug);

    leavetab();
    insym();//next
    printf("This is a returned function defination\n");
    return;
};


//＜无返回值函数定义＞ ::= '('＜参数表＞')''{'＜复合语句＞'}'
void vfunc_def () {
    char funcname[IDMAX] = {0};
    int t;
    int i = 0;
    isreturnfunc = 0;
    tmp_typ = VOIDtyp;
    strcpy(tmp_name, token);
    t = trear;//函数头字符表位置
    strcpy(tmp_pb, keysy[tmp_typ]);//type
    strcpy(tmp_pa,tmp_name);//id
    strcat(tmp_pa,"_f");//rename func with_f
    strcpy(tmp_pc,"\0");

    strcpy(funcname,tmp_name);//id

    enterpcode(FUNCFC);
    entertab();
    tmp_global = 0;
    tmp_obj = VARobj;//debug
    insym();
    if (symbol != LPARSY) error(LP);// '('
    insym();
    if (symbol == RPARSY) {// ')' 参数为空
        tfront = trear;
        insym();
        if (symbol != LCRBSY)  error(LC);//{
        insym();
        complex_statement();//复合语句
        if (symbol != RCRBSY)  error(RC);//}

    }
    else {//参数不为空
    label_pro_2:
        //test_uni(PARA);
        tmp_obj = VARobj;//debug
        if ((symbol != INTSY) && (symbol != KEYCHARSY)) {
            error(PARATYPE);
            return;
        }
        if(symbol == INTSY){
            tmp_typ = INTtyp;
            tab[t].paratype[i++] = INTtyp;
        }
        else if (symbol == KEYCHARSY){
            tmp_typ = CHARtyp;
            tab[t].paratype[i++] = CHARtyp;
        }
        insym();
        if (symbol != IDSY) {
            ;
            error(IDENT);
            insym();
        }
        else {
            strcpy(tmp_name,token);
            strcpy(tmp_pa, keysy[tmp_typ]);//type
            strcpy(tmp_pb,tmp_name);//id

            strcpy(tmp_pc,tab[t].name);//func
            tab[t].paranum++;
            enterpcode(PARAFC);//参数生成pcode:para [type] [id]
            entertab();//参数入符号表
            tab[trear-1].ispara = 1;
            tab[trear-1].paranum = tab[t].paranum-1;
            insym();
        }

        while (symbol == COMMASY) {
            insym();
            goto label_pro_2;
        }
        if (symbol != RPARSY)  error(RP);//)
        insym();
        if (symbol != LCRBSY)  error(LC);//{
        insym();
        tmp_obj = VARobj;//debug
        complex_statement();
        if (symbol != RCRBSY)  error(RC);//}
    }
    strcpy(tmp_pa,tab[t].name);//funcname//not main is ok

    strcpy(tmp_pb,"\0");
    strcpy(tmp_pc,"\0");
    enterpcode(VRETFC);

    tab[t].adr = dx;

    testout(debug);

    leavetab();
    insym();//next
    printf("This is a void function defination\n");
    return;
};

//＜主函数＞ ::= '('')''{'＜复合语句＞'}'//void main已处理
void mainfunc_def() {
    int t;
    ismain = 1;
    isreturnfunc = 0;
    tmp_global = 1;
    strcpy(tmp_name,"main");
    tmp_typ = VOIDtyp;
    t = trear;//func tab index
    entertab();         //main函数入符号表
    strcpy(tmp_pb,"void");
    strcpy(tmp_pa,"main");
    strcpy(tmp_pc,"\0");
    enterpcode(FUNCFC); //生成四元式 void main （）
    enterpcode(OPSTACKFC);
    tfront = trear;

    insym();
    if (symbol != LPARSY) error(LP);//(
    insym();
    if (symbol != RPARSY) error(RP);//)
    insym();
    if (symbol != LCRBSY)  error(LC);//{
    insym();
    complex_statement();
    if (symbol != RCRBSY)  error(RC);//}

    tab[t].adr = dx;//

    strcpy(tmp_pa,"main");
    strcpy(tmp_pb," ");

    strcpy(tmp_pc,"\0");
    enterpcode(RESTACKFC);
    enterpcode(VRETFC);//ret;
    strcpy(tmp_pa,"END");
    enterpcode(LABELFC);//END

    testout(debug);

    leavetab();
    printf("This is a main function\n");

    return;
    //insym();//next,suppose to be EOF
    //error(MAINNOTEND);
};




//＜标识符＞＝＜整数＞
int const_def_int () {
    tmp_typ = INTtyp;
    if (symbol != IDSY) {
        error(IDENT);
        return -1;
    }
    strcpy(tmp_name, token);
    insym();
    if (symbol != ASSIGNSY) {
        error(CONSTEQ);//=
        return -1;
    }
    insym();
    integer();//number
    tmp_adr = crtnum;//debug
    entertab();
    insym();//next
    return 1;
};
//＜标识符＞＝＜字符＞
int const_def_char () {
    tmp_typ = CHARtyp;
    if (symbol != IDSY) {
        error(IDENT);
        return -1;
    }
    strcpy(tmp_name, token);
    insym();
    if (symbol != ASSIGNSY) {
        error(CONSTEQ);//=
        return -1;
    }
    insym();
    if (symbol != CHARSY)  {
        error(CONSTCH);//ch
        tmp_adr = -1;
    }
    tmp_adr = (int)token[0];
    entertab();
    insym();//next
    return 1;
};
//＜常量定义＞ ::= int＜标识符＞＝＜整数＞{,＜标识符＞＝＜整数＞}
//             | char＜标识符＞＝＜字符＞{,＜标识符＞＝＜字符＞}
void const_def () {
    test_uni(CONSTDEF);
    if (symbol == INTSY) {//int
        insym();
        if (const_def_int() < 0) return;//＜标识符＞＝＜整数＞
        while (symbol == COMMASY) {//,
            insym();
            const_def_int();
        }
    }
    else if (symbol == KEYCHARSY) {//char
        insym();
        if (const_def_char() < 0) return;//＜标识符＞＝＜字符＞
        while (symbol == COMMASY) {//,
            insym();
            const_def_char();
        }
    }
    else {
        error(CONSTTYPE);
        insym();//next
    }
    printf("This is a constant defination\n");
};

//＜常量说明＞ ::= const＜常量定义＞;{ const＜常量定义＞;}
void const_dclr () {
    tmp_global = 0;
    tmp_obj = CONSTobj;
    while (symbol == CONSTSY) {
        insym();
        const_def();
        if (symbol != SEMISY)  error(SEMI);//当作有，继续读取
        insym();
    }
    printf("This is a constant declaration\n");
};

//＜程序＞::= ［＜常量说明＞］［＜变量说明＞］{＜有返回值函数定义＞|＜无返回值函数定义＞}＜主函数＞
void program () {
    int typ;
    int t;
    int i = 0;


    if (debug == 0) {
        fprintf(tp_mips,".text\n");
        fprintf(tp_mips,"j main\n");//
    }
    else if (debug == 1) {
        fprintf(tp_dag_mips,".text\n");
        fprintf(tp_dag_mips,"j main\n");//
    }
    else if (debug == 2) {
        fprintf(tp_dag_mips,".text\n");
        fprintf(tp_dag_mips,"j main\n");//
    }
    else if (debug == 3) {
        fprintf(tp_opt_mips,".text\n");
        fprintf(tp_opt_mips,"j main\n");//
    }

    tmp_global = 1;
    tmp_typ = NOtyp;

    if (!testbegsys(programbegsys,4,symbol)) error(PROGRAMTYPE);

    if (symbol == CONSTSY) {//有［＜常量说明＞］
        const_dclr();
        for (t = 0; t < trear; t++) {
            tab[t].global = 1;
        }
    }
    tfront = trear;
    //［＜变量说明＞］{＜有返回值函数定义＞|＜无返回值函数定义＞}＜主函数＞
    while ((symbol == INTSY) || (symbol == KEYCHARSY)) {
        tmp_global = 1;
        tmp_typ = (symbol == INTSY)? INTtyp : CHARtyp;
        typ = tmp_typ;
        insym();
        if (symbol != IDSY) {
            ;
            error(IDENT);
            insym();
        }
        else {
            strcpy(tmp_name,token);
            insym();
            if (symbol == LPARSY) {// '(' 说明是有返回值函数定义
                isreturnfunc = tmp_typ;
                t = trear;//函数头字符表位置
                tmp_obj = FUNCobj;
                tmp_paranum = 0;
                strcpy(tmp_pb, keysy[tmp_typ]);//type
                strcpy(tmp_pa,tmp_name);//id
                strcat(tmp_pa,"_f");//rename func with_f
                strcpy(tmp_pc,"\0");
                entertab();
                enterpcode(FUNCFC);
                tfront = trear;
                tmp_global = 0;
                tmp_obj = VARobj;//debug
                insym();
                if (symbol == RPARSY) {// ')' 参数为空
                    tfront = trear;
                    insym();
                    if (symbol != LCRBSY)  error(LC);//{
                    insym();
                    complex_statement();//复合语句
                    if (symbol != RCRBSY)  error(RC);//}

                }
                else {//参数不为空
                label_pro_2:
                    //test_uni(PARA);
                    tmp_obj = VARobj;//debug
                    if ((symbol != INTSY) && (symbol != KEYCHARSY)) {
                        error(PARATYPE);
                        break;
                    }
                    if(symbol == INTSY){
                        tmp_typ = INTtyp;
                        tab[t].paratype[i++] = INTtyp;
                    }
                    else if (symbol == KEYCHARSY){
                        tmp_typ = CHARtyp;
                        tab[t].paratype[i++] = CHARtyp;
                    }
                    insym();
                    if (symbol != IDSY) {
                        ;
                        error(IDENT);
                        insym();
                    }
                    else {
                        strcpy(tmp_name,token);
                        strcpy(tmp_pa, keysy[tmp_typ]);//type
                        strcpy(tmp_pb,tmp_name);//id
                        strcpy(tmp_pc,tab[t].name);//func
                        tab[t].paranum++;
                        enterpcode(PARAFC);//参数生成pcode:para [type] [id]
                        entertab();//参数入符号表
                        tab[trear-1].ispara = 1;
                        tab[trear-1].paranum = tab[t].paranum-1;
                        insym();
                    }

                    while (symbol == COMMASY) {
                        insym();
                        goto label_pro_2;
                    }
                    if (symbol != RPARSY)  error(RP);//)
                    insym();
                    if (symbol != LCRBSY)  error(LC);//{
                    insym();
                    tmp_obj = VARobj;//debug
                    complex_statement();
                    if (symbol != RCRBSY)  error(RC);//}
                }
                strcpy(tmp_pa,tab[t].name);//funcname//not main is ok

                strcpy(tmp_pb,"\0");
                strcpy(tmp_pc,"\0");
                enterpcode(VRETFC);
                isreturnfunc = 0;
                tab[t].adr = dx;

                testout(debug);

                leavetab();
                insym();//next
                printf("This is a returned function defination\n");
                break;//不能再出现变量定义
            }
            else {//变量说明:int x之后
                tmp_obj = VARobj;
            label_pro_1:
                tmp_typ = typ;
                if (symbol == LBKTSY) {//'[' 变量定义:数组
                    tmp_typ = (tmp_typ == INTtyp)? INTARRAYtyp : CHARARRAYtyp;
                    insym();
                    unsigned_integer(1);//无符号整数
                    tmp_ah = crtnum;
                    insym();
                    if (symbol != RBKTSY)  error(RB);//]
                    insym();
                }
                entertab();
                while (symbol == COMMASY) {//,一条变量定义内的多个变量处理
                    insym();
                    if (symbol != IDSY) {
                        ;
                        error(IDENT);
                        insym();
                    }
                    else {
                        strcpy(tmp_name, token);
                        insym();
                        goto label_pro_1;
                    }
                }
                if (symbol != SEMISY) error(SEMI);//;一条处理完毕
                insym();//next
                printf("This is a variable defination\n");
            }
        }

    }
    tfront = trear;
    while ((symbol == INTSY) || (symbol == KEYCHARSY) || (symbol == VOIDSY)) {//＜函数定义＞ ＜主函数＞
        tmp_global = 1;
        tmp_obj = FUNCobj;
        tmp_paranum = 0;
        if ((symbol == INTSY) || (symbol == KEYCHARSY)) {//返回值函数
            rfunc_def();
        }
        else {
            insym();
            //test_uni(PROGRAM);
            if (symbol == MAINSY) {//主函数
                mainfunc_def();
                fbright = 1;
                break;
            }
            else if (symbol == IDSY) {//void函数
                vfunc_def();
            }
            else {
                error(FUNCIDENTTYPE);
                insym();
            }
        }
    }
    if (!fbright) {
        fbright = 0;
        error(NOTENDMAIN);
    }
    printf("This is a program\n");
    return;
};





int main(int argc, const char * argv[]) {

    printf("please input read file path\n");
    scanf("%s",path);//输入测试文件路径
    //path = "";
    fp = fopen(path, "r");//打开测试文件
    kp_tmp = fopen("tmpout.txt", "w");

    if (debug == 0) {
        tp_mips = fopen("0_old_mips.txt", "w");
       kp_pcode =  fopen("_origin_pcode_out.txt", "w");
    }
    else if (debug ==1) {
        tp_dag_mips = fopen("12_dag_new_mips.txt", "w");

        kp_pcode =  fopen("_origin_pcode_out.txt", "w");
        kp_dagcode = fopen("123_dag_pcode_out.txt", "w");
    }

    else if (debug ==2) {
        tp_dag_mips = fopen("12_dag_new_mips.txt", "w");

        kp_pcode =  fopen("_origin_pcode_out.txt", "w");
        kp_dagcode = fopen("123_dag_pcode_out.txt", "w");
         kp_dagandconstcode = fopen("23_dag_and_const__pcode_out.txt", "w");
    }

    else if (debug ==3) {

        kp_pcode =  fopen("_origin_pcode_out.txt", "w");
        kp_dagcode = fopen("123_dag_pcode_out.txt", "w");
         kp_dagandconstcode = fopen("23_dag_and_const__pcode_out.txt", "w");
         tp_opt_mips =  fopen("3_new_mips.txt", "w");
    }






    if (fp == NULL) printf( "error at file open \n");
    else printf( "test file is open \n");

    setup();
    insym();
    program();
    printf("End of file\n");
    finish_prj();

}





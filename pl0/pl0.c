// pl0 compiler source code


#pragma warning(disable:4996)


#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#include "PL0.h"
#include "set.c"

//////////////////////////////////////////////////////////////////////
// print error message.
void error(int n)
{
	int i;

	printf("      ");
	for (i = 1; i <= cc - 1; i++)
		printf(" ");
	printf("^\n");
	printf("Error %3d: %s\n", n, err_msg[n]);
	err++;
} // error

//////////////////////////////////////////////////////////////////////
//词法分析
//读取一行中下一个还未读取的字符，并将该字符存放在全局量ch中返回
//如果该行已读完
//	1.打印改行的程序
//	2.读入下一行，并通过ch返回下一行的第一个字符
void getch(void)
{	
	//ll是该行总字符数，cc是最后读入的字符的位置
	if (cc == ll)//该行已经读完，下面开始读新的一行
	{
		if (feof(infile))//文件已结束，说明文件不完整
		{
			printf("\nPROGRAM INCOMPLETE\n");
			exit(1);
		}
		ll = cc = 0;
		printf("%5d  ", cx);//产生一份程序列表，输出相应行号或指令计数器的值
		while ( (!feof(infile)) //读取新的一行并存放在line中
			    && ((ch = getc(infile)) != '\n'))
		{
			printf("%c", ch);
			line[++ll] = ch;
		} // while
		printf("\n");
		line[++ll] = ' ';
	}
	ch = line[++cc];//该行未读完，返回该行中的下一个未读取字符
} // getch

//////////////////////////////////////////////////////////////////////
/*
识别下一个symbol，并将类别名存放在全局变量sym中
若该记号为标识符，还将该标识符的字符序列存放在id中
若为数字，还将该数字的值存放在num中
*/
void getsym(void)
{
	int i, k;
	char a[MAXIDLEN + 1]; //a[]用于存放标识符

	while (ch == ' '||ch == '\t') //跳过分隔符
		getch();

	//识别保留符和标志符
	//若为保留字，sym等于该保留字
	//若为标识符，将标识符序列赋给id，sym置为SYM_IDENTIFIER
	if (isalpha(ch))
	{ // symbol is a reserved word or an identifier.
		k = 0;
		do//读取完整的保留符号或标识符
		{
			if (k < MAXIDLEN)
				a[k++] = ch;
			getch();
		}
		while (isalpha(ch) || isdigit(ch));
		a[k] = 0;
		strcpy(id, a);
		word[0] = id;
		i = NRW; //NRW: number of reserved words
		while (strcmp(id, word[i--]));
		if (++i)
			sym = wsym[i]; // symbol is a reserved word
		else
			sym = SYM_IDENTIFIER;   // symbol is an identifier
	}
	//识别数字
	//将数字的值赋给NUM，sym置为SYM_NUMBER
	else if (isdigit(ch))
	{ // symbol is a number.
		k = num = 0;
		sym = SYM_NUMBER;
		do
		{
			num = num * 10 + ch - '0';
			k++;
			getch();
		}
		while (isdigit(ch));
		if (k > MAXNUMLEN)
			error(25);     // The number is too great.
	}
	//识别各类操作符
	else if (ch == ':')
	{
		getch();
		if (ch == '=')
		{
			sym = SYM_BECOMES; // :=
			getch();
		}
		else
		{
			sym = SYM_NULL;       // illegal?
		}
	}
	else if (ch == '>')
	{
		getch();
		if (ch == '=')
		{
			sym = SYM_GEQ;     // >=
			getch();
		}
		else
		{
			sym = SYM_GTR;     // >
		}
	}
	else if (ch == '<')
	{
		getch();
		if (ch == '=')
		{
			sym = SYM_LEQ;     // <=
			getch();
		}
		else if (ch == '>')
		{
			sym = SYM_NEQ;     // <>
			getch();
		}
		else
		{
			sym = SYM_LES;     // <
		}
	}
	else
	{ // other tokens
		i = NSYM;
		csym[0] = ch;
		while (csym[i--] != ch);
		if (++i)
		{
			sym = ssym[i];
			getch();
		}
		else
		{
			printf("Fatal Error: Unknown character.\n");
			exit(1);
		}
	}
} // getsym

//////////////////////////////////////////////////////////////////////
//根据输入的三个值组合成下一条汇编代码，并存放在全局数组code[]中
void gen(int instruction_name, int level_diff, int address)
{	
	if (cx > CXMAX)
	{
		printf("Fatal Error: Program too long.\n");
		exit(1);
	}
	code[cx].f = instruction_name;
	code[cx].l = level_diff;
	code[cx++].a = address;
} // gen

//////////////////////////////////////////////////////////////////////
// test：错误诊断处理
// tests if error occurs and skips all symbols that do not belongs to s1 or s2.
void test(symset s1, symset s2, int n)
{
	symset s;

	if (! inset(sym, s1))
	{
		error(n);
		s = uniteset(s1, s2);
		while(! inset(sym, s))
			getsym();
		destroyset(s);
	}
} // test

//////////////////////////////////////////////////////////////////////
int dx;  // data allocation index

//enter()：读入待添加符号的类型，然后向符号表中添加新的符号，以及新符号的有关属性
void enter(int kind)
{
	mask* mk;

	tx++;
	strcpy(table[tx].name, id);
	table[tx].kind = kind;
	switch (kind)
	{
	case ID_CONSTANT:	//如果是常数则将该常数的值加到符号表中
		if (num > MAXADDRESS)
		{
			error(25); // The number is too great.
			num = 0;
		}
		table[tx].value = num; 
		break;
	case ID_VARIABLE:	//如果是变量则将该变量定义点的静态层次level和偏移量dx添加到符号表中
		mk = (mask*) &table[tx];
		mk->level = level;
		mk->address = dx++;
		break;
	case ID_PROCEDURE: //如果是过程，则将过程的静态层次添加到符号表中
		mk = (mask*) &table[tx];
		mk->level = level;
		break;
	} // switch
} // enter

//////////////////////////////////////////////////////////////////////
//返回符号在符号表中的下标
int position(char* id)
{
	int i;
	strcpy(table[0].name, id);
	i = tx + 1;
	while (strcmp(table[--i].name, id) != 0);
	return i;
} // position

//////////////////////////////////////////////////////////////////////
//constdeclaration():进行常量的声明
//	先检测输入的代码是否符合常量声明的格式
//	若符合，则将该常量的符号名和数值添加到符号表中去
void constdeclaration()
{
	if (sym == SYM_IDENTIFIER)
	{
		getsym();
		if (sym == SYM_EQU || sym == SYM_BECOMES)
		{
			if (sym == SYM_BECOMES)
				error(1); // Found ':=' when expecting '='.
			getsym();
			if (sym == SYM_NUMBER)//输入格式正确，将该常量添加到符号表中
			{
				enter(ID_CONSTANT);
				getsym();
			}
			else
			{
				error(2); // There must be a number to follow '='.
			}
		}
		else
		{
			error(3); // There must be an '=' to follow the identifier.
		}
	} else	error(4);
	 // There must be an identifier to follow 'const', 'var', or 'procedure'.
} // constdeclaration

//////////////////////////////////////////////////////////////////////
//vardeclaration()：进行变量的声明
//	将变量添加到符号表中
void vardeclaration(void)
{
	if (sym == SYM_IDENTIFIER)
	{
		enter(ID_VARIABLE);
		getsym();
	}
	else
	{
		error(4); // There must be an identifier to follow 'const', 'var', or 'procedure'.
	}
} // vardeclaration

//////////////////////////////////////////////////////////////////////
//listcode：每一个分程序（过程）编译结束后，列出该部分的PL0程序代码
void listcode(int from, int to)
{
	int i;
	
	printf("\n");
	for (i = from; i < to; i++)
	{
		printf("%5d %s\t%d\t%d\n", i, mnemonic[code[i].f], code[i].l, code[i].a);
	}
	printf("\n");
} // listcode

//////////////////////////////////////////////////////////////////////
//factor()：匹配非终结符factor(因子)的合适的产生式
//	对“因子”进行翻译
//	产生相应的汇编代码
void factor(symset fsys)
{
	void expression(symset fsys);
	int i;
	symset set;
	
	test(facbegsys, fsys, 24); // The symbol can not be as the beginning of an expression.

	if (inset(sym, facbegsys))
	{
		if (sym == SYM_IDENTIFIER)// 如果读入的是identifier，则情况为：因子 -> ident
		{
			if ((i = position(id)) == 0)
			{
				error(11); // Undeclared identifier.
			}
			else
			{
				switch (table[i].kind)
				{
					mask* mk;
				case ID_CONSTANT:	//如果该ident是常数名则产生“将常数的值置于栈顶“的汇编代码
					gen(LIT, 0, table[i].value);
					break;
				case ID_VARIABLE:	//如果该ident是变量名则产生“将该变量的值置于栈顶”的汇编代码
					mk = (mask*) &table[i];
					gen(LOD, level - mk->level, mk->address);
					break;
				case ID_PROCEDURE:	//如果该ident是过程名则报错
					error(21); // Procedure identifier can not be in an expression.
					break;
				} // switch
			}
			getsym();
		}
		else if (sym == SYM_NUMBER) //如果是数字，则情况为：因子 -> 数字
									//则产生“将该数字置于栈顶”的汇编代码
		{
			if (num > MAXADDRESS)
			{
				error(25); // The number is too great.
				num = 0;
			}
			gen(LIT, 0, num); 
			getsym();
		}
		else if (sym == SYM_LPAREN)// 如果是读入的是左括号，则情况为：因子 -> ( expression )
									//则读入做括号后对expression进行翻译
									//然后在匹配 )
		{
			getsym();
			set = uniteset(createset(SYM_RPAREN, SYM_NULL), fsys);
			expression(set);
			destroyset(set);
			if (sym == SYM_RPAREN)
			{
				getsym();
			}
			else
			{
				error(22); // Missing ')'.
			}
		}
		else if(sym == SYM_MINUS) // 如果读入的是 -，则情况为：因子 -> - 因子
									//在对“因子”进行翻译
									//再产生“将单目运算符 - 置于栈顶”的汇编代码
		{  
			 getsym();
			 factor(fsys);
			 gen(OPR, 0, OPR_NEG); //将单目运算符 - 置于栈顶
		}
		test(fsys, createset(SYM_LPAREN, SYM_NULL), 23);
	} // if
} // factor

//////////////////////////////////////////////////////////////////////
//term():匹配非终结符term合适的产生式
//	对term进行递归下降翻译
void term(symset fsys)
{
	int mulop;
	symset set;
	
	set = uniteset(fsys, createset(SYM_TIMES, SYM_SLASH, SYM_NULL));
	factor(set);
	while (sym == SYM_TIMES || sym == SYM_SLASH) //如果读到了 * 或者 /，则不能选择 term -> factor进行匹配 
	{
		mulop = sym;
		getsym();
		factor(set); //对 * 或 / 后面的内容按照factor的产生式进行匹配
		if (mulop == SYM_TIMES)
		{
			gen(OPR, 0, OPR_MUL); 	//产生相应的汇编代码
		}
		else
		{
			gen(OPR, 0, OPR_DIV);	//产生相应的汇编代码
		}
	} // while
	destroyset(set);
} // term

//////////////////////////////////////////////////////////////////////
// expression():对非终结符expression进行递归下降翻译
//	并产生相应的汇编代码
void expression(symset fsys)
{
	int addop;
	symset set;

	set = uniteset(fsys, createset(SYM_PLUS, SYM_MINUS, SYM_NULL));
	
	term(set); //对term进行递归下降翻译
	while (sym == SYM_PLUS || sym == SYM_MINUS)//如果读到了 + 或者 -，则不能选择 expression -> term进行匹配 
	{
		addop = sym;
		getsym();
		term(set);	//对 + 或 - 后面的内容按照term的产生式进行递归下降翻译
		if (addop == SYM_PLUS)
		{
			gen(OPR, 0, OPR_ADD);	//产生相应的汇编代码
		}
		else
		{
			gen(OPR, 0, OPR_MIN);	//产生相应的汇编代码
		}
	} // while

	destroyset(set);
} // expression

//////////////////////////////////////////////////////////////////////
// condition()：对非终结符condition进行递归下降翻译
//	并产生相应的汇编代码
void condition(symset fsys)
{
	int relop;
	symset set;

	if (sym == SYM_ODD)// 如果读入的是odd，则按照产生式condition -> odd expression进行翻译
	{
		getsym();
		expression(fsys);
		gen(OPR, 0, 6);
	}
	else	//否则按照产生式 condition -> expression =/<>/</>/<=/>= expression 进行翻译
	{
		set = uniteset(relset, fsys);
		expression(set);// 先对第一个expression进行递归翻译
		destroyset(set);
		if (! inset(sym, relset))
		{
			error(20);
		}
		else
		{
			relop = sym;
			getsym();
			expression(fsys); //再对第而个expression进行递归翻译
			switch (relop)// 匹配相应的操作符，并产生相应的汇编代码
			{
			case SYM_EQU:
				gen(OPR, 0, OPR_EQU);
				break;
			case SYM_NEQ:
				gen(OPR, 0, OPR_NEQ);
				break;
			case SYM_LES:
				gen(OPR, 0, OPR_LES);
				break;
			case SYM_GEQ:
				gen(OPR, 0, OPR_GEQ);
				break;
			case SYM_GTR:
				gen(OPR, 0, OPR_GTR);
				break;
			case SYM_LEQ:
				gen(OPR, 0, OPR_LEQ);
				break;
			} // switch
		} // else
	} // else
} // condition

//////////////////////////////////////////////////////////////////////
// statement()：对非终结符statememt进行递归下降翻译
//	并产生相应的汇编代码
void statement(symset fsys)
{
	int i, cx1, cx2;
	symset set1, set;


	if (sym == SYM_IDENTIFIER)// 如果读入的是ident，则按照产生式statement -> ident := expression进行递归下降翻译
	{ // variable assignment
		mask* mk;
		if (! (i = position(id)))
		{
			error(11); // Undeclared identifier.
		}
		else if (table[i].kind != ID_VARIABLE)
		{
			error(12); // Illegal assignment.
			i = 0;
		}
		getsym();
		if (sym == SYM_BECOMES)
		{
			getsym();
		}
		else
		{
			error(13); // ':=' expected.
		}
		expression(fsys); //对 := 后对expression进行递归下降翻译
		mk = (mask*) &table[i];
		if (i)
		{
			gen(STO, level - mk->level, mk->address); //产生相应的汇编代码
		}
	}
	else if (sym == SYM_CALL)	//如果读入的是call，则按照产生式 statement -> call ident 进行递归下降翻译
	{ // procedure call
		getsym();
		if (sym != SYM_IDENTIFIER)
		{
			error(14); // There must be an identifier to follow the 'call'.
		}
		else
		{
			if (! (i = position(id)))
			{
				error(11); // Undeclared identifier.
			}
			else if (table[i].kind == ID_PROCEDURE)
			{
				mask* mk;
				mk = (mask*) &table[i];
				gen(CAL, level - mk->level, mk->address);	//产生相应的会汇编代码
			}
			else
			{
				error(15); // A constant or variable can not be called. 
			}
			getsym();
		}
	} 
	else if (sym == SYM_IF)	//如果读入的是if，则按照产生式statement -> if condition then statement进行递归下降翻译
	{ // if statement
		getsym();
		set1 = createset(SYM_THEN, SYM_DO, SYM_ELSE, SYM_NULL);
		set = uniteset(set1, fsys);
		condition(set);	//对if后的condition进行递归下降翻译
		destroyset(set1);	
		destroyset(set);
		if (sym == SYM_THEN)
		{
			//printf("Read then");
			getsym();
			
		}
		else
		{
			error(16); // 'then' expected.
		}
		cx1 = cx;
		gen(JPC, 0, 0);	//产生相应的汇编代码
		statement(fsys);	//对then后面的statement进行递归下降翻译

		//printf("Read statement after then");
		//printf("%d", sym);

		//getsym();
		cx2 = cx;
		gen( JMP, 0, 0);

		code[cx1].a = cx;	//产生条件语句语句不满足时的跳转地址
		
		if( sym == SYM_ELSE ){	//为else语句添加翻译过程
			//printf("Read else");
			getsym();
			statement( fsys );
			code[cx2].a = cx;	//if条件满足时，执行完相关代码后的跳转地址
		}
		//else getsym();
		
	}
	else if (sym == SYM_BEGIN)	//如果读到的是begin，则按照产生式statement -> begin statement_sequence end 进行递归下降翻译
	{ // block
		getsym();
		set1 = createset(SYM_SEMICOLON, SYM_END, SYM_NULL);
		set = uniteset(set1, fsys);

		//对statemnt_sequence按照产生式statemnt_sequence -> statement(;statement)* 进行递归下降翻译
		statement(set);	//先对产生式右部的第一个statement进行递归下降翻译
		while (sym == SYM_SEMICOLON || inset(sym, statbegsys))	//在对(;statement)*进行递归下降翻译
		{
			if (sym == SYM_SEMICOLON) //匹配;
			{
				getsym();
			}
			else
			{
				error(10);
			}
			statement(set);
		} // while
		destroyset(set1);
		destroyset(set);
		if (sym == SYM_END)	//匹配end
		{
			getsym();
		}
		else
		{
			error(17); // ';' or 'end' expected.
		}
	}
	else if (sym == SYM_WHILE)	//如果读入的是while，则按照产生式statement -> while conditoin do statement进行递归下降翻译
	{ // while statement
		cx1 = cx;
		getsym();
		set1 = createset(SYM_DO, SYM_NULL);
		set = uniteset(set1, fsys);
		condition(set);	//对condition进行递归下降翻译
		destroyset(set1);
		destroyset(set);
		cx2 = cx;
		gen(JPC, 0, 0);
		if (sym == SYM_DO)
		{
			getsym();
		}
		else
		{
			error(18); // 'do' expected.
		}
		statement(fsys);	//对do后面的statement进行递归下降翻译
		gen(JMP, 0, cx1);	//产生“跳转至while语句的条件判断代码”的汇编代码
		code[cx2].a = cx;	//产生当while语句的条件不满足时跳转的地址
		if( if_break == 1 ){
			if_break = 0;
			code[ break_cx ].a = cx; 
		}
		if( if_continue == 1 ){
			if_continue = 0;
			code[ continue_cx ].a = cx1;
		}
	}
	else if ( sym == SYM_BREAK ){
		//printf("Read break");
		getsym();
		//getsym();
		if_break = 1;
		break_cx = cx;
		gen( JMP, 0, 0);
	}
	else if ( sym == SYM_CONTINUE ){
		printf("Read Continue");
		getsym();
		if_continue = 1;
		continue_cx = cx;
		gen(JMP, 0, 0);
	}
	test(fsys, phi, 19);
} // statement
			
//////////////////////////////////////////////////////////////////////
// block()：对非终结符block进行递归下降分析
//	并产生相应的汇编代码
void block(symset fsys)
{
	int cx0; // initial code index
	mask* mk;
	int block_dx;
	int savedTx;
	symset set1, set;

	dx = 3;	//每个数据区包含三个内部变量RA, DL, SL
	block_dx = dx;
	mk = (mask*) &table[tx];
	mk->address = cx;
	gen(JMP, 0, 0);
	if (level > MAXLEVEL)
	{
		error(32); // There are too many levels.
	}
	do
	{
		if (sym == SYM_CONST)	//如果读入的是const，则按照产生式block -> const (ident = number ,)* ident = number;进行递归下降分析
		{ // constant declarations
			getsym();
			do
			{
				constdeclaration();
				while (sym == SYM_COMMA)
				{
					getsym();
					constdeclaration();
				}
				if (sym == SYM_SEMICOLON)
				{
					getsym();
				}
				else
				{
					error(5); // Missing ',' or ';'.
				}
			}
			while (sym == SYM_IDENTIFIER);
		} // if

		if (sym == SYM_VAR)	//如果读入的是var，则按照产生式block -> var (ident, )* ident;进行递归下降分析
		{ // variable declarations
			getsym();
			do
			{
				vardeclaration();
				while (sym == SYM_COMMA)
				{
					getsym();
					vardeclaration();
				}
				if (sym == SYM_SEMICOLON)
				{
					getsym();
				}
				else
				{
					error(5); // Missing ',' or ';'.
				}
			}
			while (sym == SYM_IDENTIFIER);
		} // if
		block_dx = dx; //save dx before handling procedure call!
		while (sym == SYM_PROCEDURE)	//如果读入的是procedure，则按照产生式block -> procedure ident ; block ;对进行递归下降分析
		{ // procedure declarations
			getsym();
			if (sym == SYM_IDENTIFIER)
			{
				enter(ID_PROCEDURE);
				getsym();
			}
			else
			{
				error(4); // There must be an identifier to follow 'const', 'var', or 'procedure'.
			}


			if (sym == SYM_SEMICOLON)
			{
				getsym();
			}
			else
			{
				error(5); // Missing ',' or ';'.
			}

			level++;
			savedTx = tx;
			set1 = createset(SYM_SEMICOLON, SYM_NULL);
			set = uniteset(set1, fsys);
			block(set);
			destroyset(set1);
			destroyset(set);
			tx = savedTx;
			level--;

			if (sym == SYM_SEMICOLON)
			{
				getsym();
				set1 = createset(SYM_IDENTIFIER, SYM_PROCEDURE, SYM_NULL);
				set = uniteset(statbegsys, set1);
				test(set, fsys, 6);
				destroyset(set1);
				destroyset(set);
			}
			else
			{
				error(5); // Missing ',' or ';'.
			}
		} // while
		dx = block_dx; //restore dx after handling procedure call!
		set1 = createset(SYM_IDENTIFIER, SYM_NULL);
		set = uniteset(statbegsys, set1);
		test(set, declbegsys, 7);
		destroyset(set1);
		destroyset(set);
	}
	while (inset(sym, declbegsys));

	code[mk->address].a = cx;
	mk->address = cx;
	cx0 = cx;
	gen(INT, 0, block_dx);
	set1 = createset(SYM_SEMICOLON, SYM_END, SYM_NULL);
	set = uniteset(set1, fsys);
	statement(set);
	destroyset(set1);
	destroyset(set);
	gen(OPR, 0, OPR_RET); // return
	test(fsys, phi, 8); // test for error: Follow the statement is an incorrect symbol.
	listcode(cx0, cx);
} // block

//////////////////////////////////////////////////////////////////////
// base()：根据currentlevel和levelDiff沿静态链查找，并返回某一数据区的地址
int base(int stack[], int currentLevel, int levelDiff)
{
	int b = currentLevel;
	
	while (levelDiff--)
		b = stack[b];
	return b;
} // base

//////////////////////////////////////////////////////////////////////
// interprets and executes codes.
void interpret()
{
	int pc;        // program counter
	int stack[STACKSIZE];
	int top;       // top of stack
	int b;         // program, base, and top-stack register
	instruction i; // instruction register

	printf("Begin executing PL/0 program.\n");

	pc = 0;
	b = 1;
	top = 3;
	stack[1] = stack[2] = stack[3] = 0;
	do
	{
		i = code[pc++];
		switch (i.f)
		{
		case LIT:
			stack[++top] = i.a;
			break;
		case OPR:
			switch (i.a) // operator
			{
			case OPR_RET:
				top = b - 1;
				pc = stack[top + 3];
				b = stack[top + 2];
				break;
			case OPR_NEG:
				stack[top] = -stack[top];
				break;
			case OPR_ADD:
				top--;
				stack[top] += stack[top + 1];
				break;
			case OPR_MIN:
				top--;
				stack[top] -= stack[top + 1];
				break;
			case OPR_MUL:
				top--;
				stack[top] *= stack[top + 1];
				break;
			case OPR_DIV:
				top--;
				if (stack[top + 1] == 0)
				{
					fprintf(stderr, "Runtime Error: Divided by zero.\n");
					fprintf(stderr, "Program terminated.\n");
					continue;
				}
				stack[top] /= stack[top + 1];
				break;
			case OPR_ODD:
				stack[top] %= 2;
				break;
			case OPR_EQU:
				top--;
				stack[top] = stack[top] == stack[top + 1];
				break;
			case OPR_NEQ:
				top--;
				stack[top] = stack[top] != stack[top + 1];
				break;
			case OPR_LES:
				top--;
				stack[top] = stack[top] < stack[top + 1];
				break;
			case OPR_GEQ:
				top--;
				stack[top] = stack[top] >= stack[top + 1];
				break;
			case OPR_GTR:
				top--;
				stack[top] = stack[top] > stack[top + 1];
				break;
			case OPR_LEQ:
				top--;
				stack[top] = stack[top] <= stack[top + 1];
				break;
			} // switch
			break;
		case LOD:
			stack[++top] = stack[base(stack, b, i.l) + i.a];
			break;
		case STO:
			stack[base(stack, b, i.l) + i.a] = stack[top];
			printf("%d\n", stack[top]);
			top--;
			break;
		case CAL:
			stack[top + 1] = base(stack, b, i.l);
			// generate new block mark
			stack[top + 2] = b;
			stack[top + 3] = pc;
			b = top + 1;
			pc = i.a;
			break;
		case INT:
			top += i.a;
			break;
		case JMP:
			pc = i.a;
			break;
		case JPC:
			if (stack[top] == 0)
				pc = i.a;
			top--;
			break;
		} // switch
	}
	while (pc);

	printf("End executing PL/0 program.\n");
} // interpret

//////////////////////////////////////////////////////////////////////
void main ()
{
	FILE* hbin;
	char s[80];
	int i;
	symset set, set1, set2;

	printf("Please input source file name: "); // get file name to be compiled
	scanf("%s", s);
	if ((infile = fopen(s, "r")) == NULL)
	{
		printf("File %s can't be opened.\n", s);
		exit(1);
	}

	phi = createset(SYM_NULL);
	relset = createset(SYM_EQU, SYM_NEQ, SYM_LES, SYM_LEQ, SYM_GTR, SYM_GEQ, SYM_NULL);
	
	// create begin symbol sets
	declbegsys = createset(SYM_CONST, SYM_VAR, SYM_PROCEDURE, SYM_NULL);
	statbegsys = createset(SYM_BEGIN, SYM_CALL, SYM_IF, SYM_WHILE, SYM_NULL, SYM_BREAK, SYM_CONTINUE, SYM_IDENTIFIER);
	facbegsys = createset(SYM_IDENTIFIER, SYM_NUMBER, SYM_LPAREN, SYM_MINUS, SYM_NULL);

	err = cc = cx = ll = 0; // initialize global variables
	ch = ' ';
	kk = MAXIDLEN;

	getsym();

	set1 = createset(SYM_PERIOD, SYM_NULL);
	set2 = uniteset(declbegsys, statbegsys);
	set = uniteset(set1, set2);
	block(set);
	destroyset(set1);
	destroyset(set2);
	destroyset(set);
	destroyset(phi);
	destroyset(relset);
	destroyset(declbegsys);
	destroyset(statbegsys);
	destroyset(facbegsys);

	if (sym != SYM_PERIOD)
		error(9); // '.' expected.
	if (err == 0)
	{
		hbin = fopen("hbin.txt", "w");
		for (i = 0; i < cx; i++)
			fwrite(&code[i], sizeof(instruction), 1, hbin);
		fclose(hbin);
	}
	if (err == 0)
		interpret();
	else
		printf("There are %d error(s) in PL/0 program.\n", err);
	listcode(0, cx);
} // main

//////////////////////////////////////////////////////////////////////
// eof pl0.c

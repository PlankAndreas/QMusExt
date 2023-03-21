#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <ctype.h>
#include "../qdpll.h"
#include "../qdpll_internals.h"
//#include "../qdpll_app.c"



#define QDPLL_ABORT_APP(cond,msg) \
  do {                                  \
    if (cond)                                                                \
      {                                                                        \
        fprintf (stderr, "[QDPLL-APP] %s at line %d: %s\n", __func__,        \
                 __LINE__, msg);                                        \
        fflush (stderr);                                                \
        abort();                                                        \
      }                                                                        \
  } while (0)



/* -------------------- START: PARSING -------------------- */
#define PARSER_READ_NUM(num, c)                        \
  assert (isdigit (c));                                \
  num = 0;					       \
  do						       \
    {						       \
      num = num * 10 + (c - '0');		       \
    }						       \
  while (isdigit ((c = getc (in))));

#define PARSER_SKIP_SPACE_DO_WHILE(c)		     \
  do						     \
    {                                                \
      c = getc (in);				     \
    }                                                \
  while (isspace (c));

#define PARSER_SKIP_SPACE_WHILE(c)		     \
  while (isspace (c))                                \
    c = getc (in);

static int num_clauses;
static int num_variables;

static void
parse (QDPLL * qdpll, FILE * in, int trace)
{
  int col = 0, line = 0, neg = 0, preamble_found = 0;
  LitID num = 0;
  QDPLLQuantifierType scope_type = QDPLL_QTYPE_UNDEF;

  assert (in);

  int c;
  while ((c = getc (in)) != EOF)
    {
     // printf("character %c \n",c);
      PARSER_SKIP_SPACE_WHILE (c);

      while (c == 'c')
        {
          while ((c = getc (in)) != '\n' && c != EOF)
            ;
          c = getc (in);
        }

      PARSER_SKIP_SPACE_WHILE (c);

      if (c == 'p')
        {
          //printf("parsing preamble \n");
          /* parse preamble */
          PARSER_SKIP_SPACE_DO_WHILE (c);
          if (c != 'c')
            goto MALFORMED_PREAMBLE;
          PARSER_SKIP_SPACE_DO_WHILE (c);
          if (c != 'n')
            goto MALFORMED_PREAMBLE;
          PARSER_SKIP_SPACE_DO_WHILE (c);
          if (c != 'f')
            goto MALFORMED_PREAMBLE;
          PARSER_SKIP_SPACE_DO_WHILE (c);
          if (!isdigit (c))
            goto MALFORMED_PREAMBLE;

          /* read number of variables */
          PARSER_READ_NUM (num, c);
          num_variables=num;
          if (trace == TRACE_QRP)
            fprintf (stdout, "p qrp %u", num);
          else if (trace == TRACE_BQRP)
            fprintf (stdout, "p bqrp %u", num);

          PARSER_SKIP_SPACE_WHILE (c);
          if (!isdigit (c))
            goto MALFORMED_PREAMBLE;

          /* read number of clauses */
          PARSER_READ_NUM (num, c);
          num_clauses = num;

          /* NOTE: number of steps is number of orig. clauses, as we can't tell
             the actual, future number of steps when tracing on-the-fly! */
          if (trace)
            fprintf (stdout, " %u%c", num, trace == TRACE_QRP ? '\n' : 0);

          preamble_found = 1;
          goto PARSE_SCOPE_OR_CLAUSE;

        MALFORMED_PREAMBLE:
          QDPLL_ABORT_APP (1, "malformed preamble!\n");
          return;
        }
      else
        {
          QDPLL_ABORT_APP (1, "expecting preamble!\n");
          return;
        }

    PARSE_SCOPE_OR_CLAUSE:

      PARSER_SKIP_SPACE_WHILE (c);

      if (c == 'a' || c == 'e')
        {
          /* open a new scope */
          if (c == 'a')
            scope_type = QDPLL_QTYPE_FORALL;
          else
            scope_type = QDPLL_QTYPE_EXISTS;

          qdpll_new_scope (qdpll, scope_type);

          PARSER_SKIP_SPACE_DO_WHILE (c);
        }

      if (!isdigit (c) && c != '-')
        {
          if (c == EOF)
            return;
          QDPLL_ABORT_APP (1, "expecting digit or '-'!\n");
          return;
        }
      else
        {
          if (c == '-')
            {
              neg = 1;
              if (!isdigit ((c = getc (in))))
                {
                  QDPLL_ABORT_APP (1, "expecting digit!\n");
                  return;
                }
            }

          /* parse a literal or variable ID */
          PARSER_READ_NUM (num, c);
          num = neg ? -num : num;

          qdpll_add (qdpll, num);

          neg = 0;

          goto PARSE_SCOPE_OR_CLAUSE;
        }
    }

  if (!preamble_found)
    QDPLL_ABORT_APP (1, "preamble missing!\n");
}

/* -------------------- END: PARSING -------------------- */

static void
add_assumptions_to_file (QDPLL * qdpll, FILE * in, int trace, FILE *out)
{
  int col = 0, line = 0, neg = 0, preamble_found = 0;
  LitID num = 0;
  QDPLLQuantifierType scope_type = QDPLL_QTYPE_UNDEF;

  assert (in);
  int preamble_started = 0;
  int line_ended = 0;
  int line_ended_add_assumption = 0;

  int c_flag=0;
  int n_flag=0;
  int f_flag=0;
  int num_var_flag=0;
  int num_clauses_flag=0;
  int num_var_temp=0;
  int num_var_temp2=0;
  int num_clauses_temp=0;
  int existentials_added=0;
  int existentials_added2=0;
  int commentflag=0;
  int j=0;



  int c;
  while ((c = getc (in)) != EOF)
    {


      if(commentflag==0){
        PARSER_SKIP_SPACE_WHILE (c);
       while (c == 'c')
        {
          while ((c = getc (in)) != '\n' && c != EOF)
            ;
          c = getc (in);
        }
        PARSER_SKIP_SPACE_WHILE (c);

      }


      if (c == 'p'){
        commentflag=1;
      }


      if (c == 'a' || c == 'e'){
        preamble_started=1;
      }
      /*
      if(c == '0'){
        line_ended = 1;
      }
      */

      if(c=='f'&&c_flag==1&&n_flag==1){
        f_flag=1;
      }else if(c_flag==1&&n_flag==1){
        c_flag=0;
        n_flag=1;
      }

      if(c=='n'&&c_flag==1){
        n_flag=1;
      }else if(c_flag==1){
        c_flag=0;
      }

      if(c=='c'){
        c_flag=1;
      }




      if(num_var_flag==1){
        if(isdigit(c)){
          PARSER_READ_NUM (num, c);
          num_clauses_temp=num;
          num_var_flag=0;
          num_clauses_flag=1;
          fprintf(out, "%d", num_var_temp + num_clauses_temp);
          putc(' ',out);
          fprintf(out, "%d", num_clauses_temp);
        }
      }


      if(f_flag==1 &&num_var_flag!=1&&num_clauses_flag!=1){
        if(isdigit(c)){

          PARSER_READ_NUM (num, c);
          num_var_temp=num;
          //num_var_temp2=num;
          num_var_temp2=0;
          f_flag=0;
          num_var_flag=1;
        }

      }


      if(num_var_flag==1){
        continue;
      }



      if((c=='a' || c== 'e') &&  line_ended==1 && preamble_started==1){
        line_ended=0;
      }else if(line_ended==1 && preamble_started==1){
        putc('e', out);
        int i;
        for(i=num_var_temp+1;i<=num_clauses_temp+num_var_temp;i++){
          putc(' ', out);
          fprintf(out, "%d", i);
        }
        putc(' ', out);
        putc('0', out);
        putc('\n', out);
        preamble_started=0;
        line_ended=0;
        existentials_added=1;
        existentials_added2=1;
      }

      if(existentials_added2!=1){
        fputc (c, out);
      }


      if(c == '\n' && preamble_started){
        line_ended = 1;
      }else if(c=='\n'){
        line_ended_add_assumption=1;
      }


      if(existentials_added2||(existentials_added&&line_ended_add_assumption)){
        line_ended_add_assumption=0;
        num_var_temp2++;
        if(num_var_temp2<=num_var_temp+num_clauses_temp){
          fprintf(out, "{%d}", num_var_temp2);
          fputc(' ', out);
        }

      }

      if(existentials_added2==1){
        fputc (c, out);
        existentials_added2=0;
      }


    }
}

int main (int argc, char** argv)
{

  FILE *fp;
  FILE *outputp;
  /* The header file 'qdpll.h' has some comments regarding the usage of the
     API. */

  /* Please see also the file 'basic-manual-selectors.c'. */

  /* Create solver instance. */
  QDPLL *depqbf = qdpll_create ();

  /* Use the linear ordering of the quantifier prefix. */
  qdpll_configure (depqbf, "--dep-man=simple");
  /* Enable incremental solving. */
  qdpll_configure (depqbf, "--incremental-use");




  if (argc !=2){
    fp = fopen("../fuzzy_output","r"); //file pointer opens the file in read mode
  }else{
    fp = fopen(argv[1],"r"); //file pointer opens the file in read mode
  }

  outputp = fopen("/home/andreas/Documents/GitLabProjects/depqbf/examples/Check-Files/sample", "w");
  //outputp = fopen("sample", "w");
  //FILE *fp = fopen("../fuzzy_output","r"); //file pointer opens the file in read mode
  /*int ch = getc(fp);

  printf("read file \n");
  while (ch != EOF)
  {
    putchar(ch);
    ch = getc(fp);
  }
*/

  //add_assumptions_to_file(fp,outputp);
  add_assumptions_to_file(depqbf, fp, TRACE_QRP, outputp);
  fclose(outputp);

  /*
  outputp = fopen("sample", "r");
  //rewind(outputp);

  //parse (depqbf, fp, TRACE_QRP);
  parse(depqbf, outputp, TRACE_QRP);

  fclose(fp);
  fclose(outputp);




  printf("number of variables %d \n", num_variables);
  printf("number of clauses %d \n", num_clauses);
  //qdpll_print (depqbf, stdout);

  //qdpll_reset(depqbf);

  //qdpll_assume (depqbf, -5);




  int* marked_initial_vars;
  marked_initial_vars = (int*)malloc(num_clauses * sizeof(int));

  int i;
  int j;
  int assumption_var_start=((num_variables-num_clauses)+1);

  for(j=assumption_var_start;j<=num_variables;j++){
    marked_initial_vars[j-assumption_var_start]=1;

    qdpll_assume (depqbf, -j);

  }

  QDPLLResult res = qdpll_sat (depqbf);
  if(res==10){
    printf("Input-Formula is SAT \n");
    //return 0;
  }else{
    printf("Input-Formula is UNSAT \n");
  }


  for(j=assumption_var_start;j<=num_variables;j++){
    qdpll_reset(depqbf);
    for(i=assumption_var_start;i<=num_variables;i++){
      //printf("d= %d \n",i);
      if(i==j){
        //printf("%d=1, ",i-assumption_var_start+1);
        continue;
      }
      if(marked_initial_vars[i-assumption_var_start]==1){
        //printf("minus-assuming clause %d\n",i);
        qdpll_assume (depqbf, -i);
        //printf("%d=0, ",i-assumption_var_start+1);
      }else{
        //printf("%d=1, ",i-assumption_var_start+1);
      }

    }
    res = qdpll_sat (depqbf);
    if(res==10){
      marked_initial_vars[j-assumption_var_start]=1;
      //printf("Clause %d is SAT \n",j-assumption_var_start+1);
    }else{
      marked_initial_vars[j-assumption_var_start]=0;
      //printf("Clause %d is UNSAT \n",j-assumption_var_start+1);
    }
  }

  printf("-----------------------\n");
  printf("Resultat des Check Programmes\n");

  printf("-----------------------\n");
  printf("\n");



  FILE *fptr;
  fptr = (fopen("./Check-Files/check_result","w+"));
  if(fptr == NULL)
  {
    printf("Error!");
    exit(1);
  }

  for(i=0;i<num_clauses;i++)
  {

    fprintf(fptr,"%d \n", marked_initial_vars[i]);
  }

 fclose(fptr);



  free(marked_initial_vars);


  // res == 10 means satisfiable, res == 20 means unsatisfiable.
  //printf("number of variables %d \n", num_variables);
  //printf("number of clauses %d \n", num_clauses);
  //printf ("result is: %d\n", res);

  //qdpll_print_qdimacs_output (depqbf);


  qdpll_delete (depqbf);
*/
}

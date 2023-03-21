#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include "../qdpll.h"

int main (int argc, char** argv)
{
  /* The header file 'qdpll.h' has some comments regarding the usage of the
     API. */

  /* Please see also the file 'basic-manual-selectors.c'. */

  /* Create solver instance. */
  QDPLL *depqbf = qdpll_create ();

  /* Use the linear ordering of the quantifier prefix. */
  qdpll_configure (depqbf, "--dep-man=simple");
    //Enable incremental solving.

    qdpll_configure (depqbf, "--incremental-use");


    qdpll_configure (depqbf, "--traditional-qcdcl");
    qdpll_configure (depqbf, "--trace=qrp");
    qdpll_configure (depqbf, "--qbce-witness-max-occs=0");
    qdpll_configure (depqbf, "--qbce-max-clause-size=0");

    /*
    char *buffer; //for open_memstream
    size_t size;
    FILE *memstream = open_memstream(&buffer, &size);
    int stdout_copy = dup(1); //save stdout

    stdout = memstream; //redirection
*/
    /*
  // Add and open a new leftmost universal block at nesting level 1.

  qdpll_new_scope_at_nesting (depqbf, QDPLL_QTYPE_FORALL, 1);

  // Add a fresh variable with 'id == 1' to the open block.
  qdpll_add (depqbf, 1);
  // Close open scope.
  qdpll_add (depqbf, 0);

  // Add a new existential block at nesting level 2.
  qdpll_new_scope_at_nesting (depqbf, QDPLL_QTYPE_EXISTS, 2);
  // Add a fresh variable with 'id == 2' to the existential block.
  qdpll_add (depqbf, 2);
  // Close open scope.
  qdpll_add (depqbf, 0);

  // Add clause: 1 -2 0
  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, -2);
  qdpll_add (depqbf, 0);

  // Add clause: -1 2 0
  qdpll_add (depqbf, -1);
  qdpll_add (depqbf, 2);
  qdpll_add (depqbf, 0);
*/
  /* At this point, the formula looks as follows:
     p cnf 2 3
     a 1 0
     e 2 0
     1 -2 0
     -1 2 0 */

  /* Print formula. */
  //sqdpll_print (depqbf, stdout);


  int num_clauses = 13;
  ClauseGroupID* clausegroups = (ClauseGroupID*)malloc(num_clauses * sizeof(ClauseGroupID));

  qdpll_new_scope_at_nesting (depqbf, QDPLL_QTYPE_EXISTS, 1);
  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, 2);
  qdpll_add (depqbf, 4);
  qdpll_add (depqbf, 0);

  //clause 1
  clausegroups[0]=qdpll_new_clause_group(depqbf);
  qdpll_open_clause_group (depqbf, clausegroups[0]);
  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, -2);
  qdpll_add (depqbf, 4);
  qdpll_add (depqbf, 0);
  qdpll_close_clause_group (depqbf, clausegroups[0]);

  //clause 2
  clausegroups[1]=qdpll_new_clause_group(depqbf);
  qdpll_open_clause_group (depqbf, clausegroups[1]);
  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, 2);
  qdpll_add (depqbf, 4);
  qdpll_add (depqbf, 0);
  qdpll_close_clause_group (depqbf, clausegroups[1]);

  //clause 3
  clausegroups[2]=qdpll_new_clause_group(depqbf);
  qdpll_open_clause_group (depqbf, clausegroups[2]);
  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, 2);
  qdpll_add (depqbf, -4);
  qdpll_add (depqbf, 0);
  qdpll_close_clause_group (depqbf, clausegroups[2]);

  //clause 4
  clausegroups[3]=qdpll_new_clause_group(depqbf);
  qdpll_open_clause_group (depqbf, clausegroups[3]);
  qdpll_add (depqbf, 2);
  qdpll_add (depqbf, -3);
  qdpll_add (depqbf, 0);
  qdpll_close_clause_group (depqbf, clausegroups[3]);

  //clause 5
  clausegroups[4]=qdpll_new_clause_group(depqbf);
  qdpll_open_clause_group (depqbf, clausegroups[4]);
  qdpll_add (depqbf, -1);
  qdpll_add (depqbf, 3);
  qdpll_add (depqbf, 0);
  qdpll_close_clause_group (depqbf, clausegroups[4]);

  //clause 6
  clausegroups[5]=qdpll_new_clause_group(depqbf);
  qdpll_open_clause_group (depqbf, clausegroups[5]);
  qdpll_add (depqbf, -1);
  qdpll_add (depqbf, -3);
  qdpll_add (depqbf, 0);
  qdpll_close_clause_group (depqbf, clausegroups[5]);

  //clause 7
  clausegroups[6]=qdpll_new_clause_group(depqbf);
  qdpll_open_clause_group (depqbf, clausegroups[6]);
  qdpll_add (depqbf, -2);
  qdpll_add (depqbf, 0);
  qdpll_close_clause_group (depqbf, clausegroups[6]);


  //clause 8
  clausegroups[7]=qdpll_new_clause_group(depqbf);
  qdpll_open_clause_group (depqbf, clausegroups[7]);
  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, 4);
  qdpll_add (depqbf, 0);
  qdpll_close_clause_group (depqbf, clausegroups[7]);


  //clause 9
  clausegroups[8]=qdpll_new_clause_group(depqbf);
  qdpll_open_clause_group (depqbf, clausegroups[8]);
  qdpll_add (depqbf, -1);
  qdpll_add (depqbf, 2);
  qdpll_add (depqbf, 0);
  qdpll_close_clause_group (depqbf, clausegroups[8]);

  //clause 10
  clausegroups[9]=qdpll_new_clause_group(depqbf);
  qdpll_open_clause_group (depqbf, clausegroups[9]);
  qdpll_add (depqbf, 2);
  qdpll_add (depqbf, -4);
  qdpll_add (depqbf, 0);
  qdpll_close_clause_group (depqbf, clausegroups[9]);

  //clause 11
  clausegroups[10]=qdpll_new_clause_group(depqbf);
  qdpll_open_clause_group (depqbf, clausegroups[10]);
  qdpll_add (depqbf, -1);
  qdpll_add (depqbf, 0);
  qdpll_close_clause_group (depqbf, clausegroups[10]);


  //clause 12
  clausegroups[11]=qdpll_new_clause_group(depqbf);
  qdpll_open_clause_group (depqbf, clausegroups[11]);
  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, 2);
  qdpll_add (depqbf, 0);
  qdpll_close_clause_group (depqbf, clausegroups[11]);



  //clause 13
  clausegroups[12]=qdpll_new_clause_group(depqbf);
  qdpll_open_clause_group (depqbf, clausegroups[12]);
  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, 0);
  qdpll_close_clause_group (depqbf, clausegroups[12]);





  //qdpll_print(depqbf,stdout);
printf("vor res \n");
  QDPLLResult res = qdpll_sat (depqbf);
  printf("nach res \n");
/*
  fclose(memstream);

  stdout = fdopen(stdout_copy ,"w+");
  printf("stream: %s , size: %d\n", buffer,(int)size);

  free(buffer);
  */



  /* Expecting that the formula is satisfiable. */
  //assert (res == QDPLL_RESULT_SAT);
  /* res == 10 means satisfiable, res == 20 means unsatisfiable. */
  printf ("result is: %d\n", res);

  /* Delete solver instance. */

  qdpll_delete (depqbf);
}

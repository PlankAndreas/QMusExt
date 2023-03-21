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
  /* Enable incremental solving. */
  qdpll_configure (depqbf, "--incremental-use");


  qdpll_new_scope_at_nesting (depqbf, QDPLL_QTYPE_EXISTS, 1);
  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, 0);

  qdpll_new_scope_at_nesting (depqbf, QDPLL_QTYPE_FORALL, 2);
  qdpll_add (depqbf, 3);
  qdpll_add (depqbf, 6);
  qdpll_add (depqbf, 4);
  qdpll_add (depqbf, 7);
  qdpll_add (depqbf, 5);
  qdpll_add (depqbf, 0);

  qdpll_new_scope_at_nesting (depqbf, QDPLL_QTYPE_EXISTS, 3);
  qdpll_add (depqbf, 8);
  qdpll_add (depqbf, 2);
  qdpll_add (depqbf, 0);

  /*
  qdpll_new_scope_at_nesting (depqbf, QDPLL_QTYPE_EXISTS, 4);
  qdpll_add (depqbf, 9);
  qdpll_add (depqbf, 10);
  qdpll_add (depqbf, 11);
  qdpll_add (depqbf, 12);
  qdpll_add (depqbf, 13);
  qdpll_add (depqbf, 14);
  qdpll_add (depqbf, 15);
  qdpll_add (depqbf, 16);
  qdpll_add (depqbf, 17);
  qdpll_add (depqbf, 18);
  qdpll_add (depqbf, 0);
  */

  /*
  //Add clause: -1 -2 6 9 0
  qdpll_add (depqbf, -1);
  qdpll_add (depqbf, -2);
  qdpll_add (depqbf, 6);
  //qdpll_add (depqbf, 9);
  qdpll_add (depqbf, 0);

  //Add clause: 3 8 10 0
  qdpll_add (depqbf, 3);
  qdpll_add (depqbf, 8);
  //qdpll_add (depqbf, 10);
  qdpll_add (depqbf, 0);

  //Add clause: 1 8 11 0
  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, 8);
  //qdpll_add (depqbf, 11);
  qdpll_add (depqbf, 0);

  //Add clause: -2 -4 -7 8 12 0
  qdpll_add (depqbf, -2);
  qdpll_add (depqbf, -4);
  qdpll_add (depqbf, -7);
  qdpll_add (depqbf, 8);
  //qdpll_add (depqbf, 12);
  qdpll_add (depqbf, 0);

  */

  /*
  //Add clause: 2 8 13 0
  qdpll_add (depqbf, 2);
  qdpll_add (depqbf, 8);
  //qdpll_add (depqbf, 13);
  qdpll_add (depqbf, 0);
*/

  //Add clause: 1 -2 14 0
  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, -2);
  //qdpll_add (depqbf, 14);
  qdpll_add (depqbf, 0);


  //Add clause: 1 -8 15 0
  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, -8);
  //qdpll_add (depqbf, 15);
  qdpll_add (depqbf, 0);

  //Add clause: -1 -2 -5 16 0
  qdpll_add (depqbf, -1);
  qdpll_add (depqbf, -2);
  qdpll_add (depqbf, -5);
  //qdpll_add (depqbf, 16);
  qdpll_add (depqbf, 0);

  //Add clause: 1 -2 8 17 0
  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, -2);
  qdpll_add (depqbf, 8);
  //qdpll_add (depqbf, 17);
  qdpll_add (depqbf, 0);

  //Add clause: -1 -8 18 0
  qdpll_add (depqbf, -1);
  qdpll_add (depqbf, -8);
  //qdpll_add (depqbf, 18);
  qdpll_add (depqbf, 0);

  /* At this point, the formula looks as follows:
     p cnf 2 3
     a 1 0
     e 2 0
     1 -2 0
     -1 2 0 */

  /* Print formula. */
  qdpll_print (depqbf, stdout);

  qdpll_configure (depqbf, "--trace");
  /* Enable incremental solving. */
  qdpll_configure (depqbf, "--traditional-qcdcl");

  QDPLLResult res = qdpll_sat (depqbf);
  /* Expecting that the formula is unsatisfiable. */
  //assert (res == QDPLL_RESULT_UNSAT);
  /* res == 10 means satisfiable, res == 20 means unsatisfiable. */
  printf ("result is: %d\n", res);

  /* Delete solver instance. */
  qdpll_delete (depqbf);
}

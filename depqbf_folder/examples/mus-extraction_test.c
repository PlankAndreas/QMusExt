#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include "../qdpll.h"
#include "../qdpll_mem.h"
#include "../qdpll_pcnf.h"
#include "../qdpll_exit.h"
#include "../qdpll_stack.h"
#include "../qdpll_internals.h"
#include "../qdpll_dep_man_generic.h"
#include "../qdpll_dep_man_qdag.h"
#include "../qdpll_config.h"
#include "../qdpll_dynamic_nenofex.h"
#include ".././picosat/picosat.h"



#define QDPLL_ABORT_QDPLL(cond,msg)					\
  do {									\
    if (cond)								\
      {									\
        fprintf (stderr, "[QDPLL] %s at line %d: %s\n", __func__,	\
                 __LINE__, msg);                                        \
        fflush (stderr);                                                \
        abort();                                                        \
      }									\
  } while (0)

static void
print_lit_notify_lists_info2 (QDPLL * qdpll)
{
  Var *p, *e;
  for (p = qdpll->pcnf.vars, e = p + qdpll->pcnf.size_vars; p < e; p++)
    {
      if (p->id)
        {
          fprintf (stderr, "Var %d, pos:\n", p->id);
          print_lit_notify_lists (qdpll, &(p->pos_notify_lit_watchers));
          fprintf (stderr, "Var %d, neg:\n", p->id);
          print_lit_notify_lists (qdpll, &(p->neg_notify_lit_watchers));
        }
    }
}


/* Helper function. */
static void
print_relevant_clause_groups (ClauseGroupID * clause_group_ids)
{
  ClauseGroupID *p;
  for (p = clause_group_ids; *p; p++)
    printf ("%d ", *p);
  printf ("0");
}

/* Helper function. */
static unsigned int
count_relevant_clause_groups (ClauseGroupID * clause_group_ids)
{
  unsigned int cnt = 0;
  ClauseGroupID *p;
  for (p = clause_group_ids; *p; p++)
    cnt++;
  return cnt;
}

/*
ClauseGroupID *
qdpll_get_relevant_clause_groups_test (QDPLL * qdpll)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL (!qdpll->options.incremental_use,
                     "Must configure by '--incremental-use' to enable clause groups API!");
  qdpll->state.clause_group_api_called = 1;
  QDPLL_ABORT_QDPLL (qdpll->state.push_pop_api_called,
                     "Must not mix calls of push/pop API and clause groups API!");
  QDPLL_ABORT_QDPLL (qdpll->result == QDPLL_RESULT_UNKNOWN,
                     "Formula must be solved before calling this function!");
  QDPLL_ABORT_QDPLL (qdpll->result != QDPLL_RESULT_UNSAT,
                     "Formula must be unsatisfiable when calling this function!");
  QDPLL_ABORT_QDPLL(!qdpll->assumption_lits_constraint,
                    "Unexpected error: no assumption subset computed!");
  QDPLL_ABORT_QDPLL(!(qdpll->assumption_lits_constraint && qdpll->state.assumptions_given),
                    "Unexpected error: cannot retrieve relevant assumptions.");
  QDPLL_ABORT_QDPLL(qdpll->assumption_lits_constraint->is_cube,
                    "Unexpected error: assumption-lits constraint is a cube.");

  ClauseGroupIDStack clause_group_ids;
  QDPLL_INIT_STACK(clause_group_ids);

  LitID *p, *e;
  for (p = qdpll->assumption_lits_constraint->lits,
         e = p + qdpll->assumption_lits_constraint->num_lits;
       p < e; p++)
    {
      LitID a_lit = *p;
      Var *a_var = LIT2VARPTR(qdpll->pcnf.vars, a_lit);
      if (a_var->is_internal)
        {

          assert (a_var->is_cur_used_internal_var);
          assert (!a_var->is_cur_inactive_group_selector);
          assert (a_var->assignment == QDPLL_ASSIGNMENT_FALSE);
          ClauseGroupID group_id = a_var->clause_group_id;
          assert (qdpll_exists_clause_group (qdpll, group_id));
          assert (!clause_group_to_var_ptr
                  (qdpll, group_id)->is_cur_inactive_group_selector);
          assert (qdpll->state.cur_used_internal_vars.start[group_id - 1] == a_var->id);
          QDPLL_PUSH_STACK(qdpll->mm, clause_group_ids, group_id);
        }
    }

  unsigned int size =
    (QDPLL_COUNT_STACK(clause_group_ids) + 1) * sizeof (ClauseGroupID);

  ClauseGroupID *relevant_clause_groups = malloc (size);
  memset (relevant_clause_groups, 0, size);

  ClauseGroupID *gp, *ge, *dest = relevant_clause_groups;
  for (gp = clause_group_ids.start, ge = clause_group_ids.top;
       gp < ge; gp++, dest++)
    *dest = *gp;
  assert (dest ==
          relevant_clause_groups + QDPLL_COUNT_STACK(clause_group_ids));
  assert (!*dest);

  QDPLL_DELETE_STACK(qdpll->mm, clause_group_ids);

  return relevant_clause_groups;
}
*/
int
main (int argc, char **argv)
{
  QDPLL *depqbf = qdpll_create ();

  qdpll_configure (depqbf, "--dep-man=simple");
  qdpll_configure (depqbf, "--incremental-use");
  //qdpll_configure (depqbf, "--dep-man=simple");
  //qdpll_configure (depqbf, "--traditional-qcdcl");
  //qdpll_configure (depqbf, "--trace=qrp");


  /* Given the following unsatisfiable formula:

     p cnf 4 3
     a 1 2 0
     e 3 4 0
     -1 -3 0
     1 2 4 0
     1 -4 0

     The first clause will be put in one clause group and the last two clauses in
     another group. That last two clauses are unsatisfiable, thus deleting the
     first clause preserves unsatisfiability.
   */

  /* Declare outermost universal block with variables 1 and 2. */
  qdpll_new_scope_at_nesting (depqbf, QDPLL_QTYPE_FORALL, 1);
  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, 2);
  qdpll_add (depqbf, 0);

  /* Declare existential block with variables 3 and 4. */
  qdpll_new_scope_at_nesting (depqbf, QDPLL_QTYPE_EXISTS, 2);
  qdpll_add (depqbf, 3);
  qdpll_add (depqbf, 4);
  qdpll_add (depqbf, 0);

  /* Create a new clause group with ID 'id1'. The ID of a clause group is used
     as its handle and can be passed to API functions. */
  ClauseGroupID id1 = qdpll_new_clause_group (depqbf);
  /* Newly created clause groups are closed. */
  assert (!qdpll_get_open_clause_group (depqbf));
  /* A clause group must be opened before clauses can be added to it. Only one
     clause group can be open at a time. */
  qdpll_open_clause_group (depqbf, id1);
  assert (qdpll_get_open_clause_group (depqbf) == id1);
  /* Add the clause '-1 -3 0' to the currently open clause group 'id1'. */
  qdpll_add (depqbf, -1);
  qdpll_add (depqbf, -3);
  qdpll_add (depqbf, 0);
  /* The currently open clause group must be closed before creating or opening
     another clause group. */
  qdpll_close_clause_group (depqbf, id1);
  assert (!qdpll_get_open_clause_group (depqbf));

  /* Create another clause group 'id2'. */
  ClauseGroupID id2 = qdpll_new_clause_group (depqbf);
  assert (!qdpll_get_open_clause_group (depqbf));
  qdpll_open_clause_group (depqbf, id2);
  assert (qdpll_get_open_clause_group (depqbf) == id2);
  /* Add the clauses '1 2 4 0' and '1 -4 0' to the currently open clause group
     'id2'. */
  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, 2);
  qdpll_add (depqbf, 4);
  qdpll_add (depqbf, 0);

  qdpll_close_clause_group (depqbf, id2);
  assert (!qdpll_get_open_clause_group (depqbf));

  /* Create another clause group 'id3'. */
  ClauseGroupID id3 = qdpll_new_clause_group (depqbf);
  assert (!qdpll_get_open_clause_group (depqbf));
  qdpll_open_clause_group (depqbf, id3);
  assert (qdpll_get_open_clause_group (depqbf) == id3);

  //---------------------
  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, -4);
  qdpll_add (depqbf, 0);
  qdpll_close_clause_group (depqbf, id3);
  assert (!qdpll_get_open_clause_group (depqbf));

  qdpll_print (depqbf, stdout);

  /* Solve the formula, which is unsatisfiable. */
  QDPLLResult res = qdpll_sat (depqbf);
  assert (res == QDPLL_RESULT_UNSAT);
  printf ("result is %d\n", res);




  print_lit_notify_lists_info2 (QDPLL * qdpll);

/*
  ClauseGroupID *relevant_clause_groups =
    qdpll_get_relevant_clause_groups_test(depqbf);*/
  /* We must reset the solver AFTER retrieving the relevant groups. */
  qdpll_reset (depqbf);
  /* In our example, the clauses in the group 'id2' are relevant for
     unsatisfiability. (The clause '-1 -3 0' in 'id1' cannot be part of a resolution
     refutation found by the solver.) */
  assert (count_relevant_clause_groups (relevant_clause_groups) == 2);
  //assert (relevant_clause_groups[0] == id2);
  printf ("printing zero-terminated relevant clause group IDs: ");
  print_relevant_clause_groups (relevant_clause_groups);
  printf ("\n");

  /* Temporarily remove the clause group 'id2' by deactivating it. */
  printf ("deactivating group 2 and 3 with clauses 1 2 4 0 and 1 -4 0\n");
  qdpll_deactivate_clause_group (depqbf, relevant_clause_groups[0]);
  qdpll_deactivate_clause_group (depqbf, relevant_clause_groups[1]);

  /* Calling 'qdpll_gc()' removes superfluous variables and
     quantifiers from the prefix. HOWEVER, in this case, we have
     deactivated -- not deleted -- group 'id2' and hence calling
     'qdpll_gc()' has no effect. */
  qdpll_gc (depqbf);
  qdpll_print (depqbf, stdout);

  /* The formula where group 'id2' has been deactivated is satisfiable. */
  res = qdpll_sat (depqbf);
  assert (res == QDPLL_RESULT_SAT);
  printf ("result is %d\n", res);
  qdpll_reset (depqbf);
  /* Activate group 'id2' again, which makes the formula unsatisfiable. */
  printf ("activating group 2 and 3 again\n");
  qdpll_activate_clause_group (depqbf, relevant_clause_groups[0]);
  qdpll_activate_clause_group (depqbf, relevant_clause_groups[1]);

  /* Free memory of array returned by 'qdpll_get_relevant_clause_groups'.
     This is the caller's responsibility. */
  free (relevant_clause_groups);

  /* Permanently remove the group 'id1'. This operation cannot be undone and
     is in contrast to deactivating a group. */
  printf ("deleting group 1 with clause -1 -3 0\n");
  qdpll_delete_clause_group (depqbf, id1);
  /* Deleting a group invalidates its ID, which can be checked by
     'qdpll_exists_clause_group'. */
  assert (!qdpll_exists_clause_group (depqbf, id1));

  /* Different from the first call of 'qdpll_gc' above, this time variable 3
     will be removed from the quantifier prefix. We deleted group 'id1' which
     contains the only clause where variable 3 occurs. Hence calling 'qdpll_gc'
     removes variable 3 because it does not occur any more in the formula. */
  qdpll_gc (depqbf);
  assert (!qdpll_is_var_declared (depqbf, 3));
  qdpll_print (depqbf, stdout);

  /* After deleting the group 'id1', the formula consisting only of the
     clauses in group 'id2' is unsatisfiable. */
  res = qdpll_sat (depqbf);
  assert (res == QDPLL_RESULT_UNSAT);
  printf ("result is %d\n", res);

  qdpll_delete (depqbf);
}

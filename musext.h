/*  MusExt: Tool for extracting a minimal unsatisfiable core from Q-resolution proofs.
 *
 *  Copyright (c) 2011-2012 Mathias Preiner.
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

  #include <stdlib.h>
  #include <stdio.h>
  #include <sys/unistd.h>

  #define QRP_COMMENT '#'
  #define QRP_PREAMBLE 'p'
  #define QRP_PREAMBLE_BQRP "bqrp"
  #define QRP_PREAMBLE_QRP "qrp"
  #define QRP_RESULT_S 's'
  #define QRP_RESULT 'r'
  #define QRP_RESULT_SAT "sat"
  #define QRP_RESULT_U 'u'
  #define QRP_RESULT_UNSAT "unsat"
  #define QRP_FORALL 'a'
  #define QRP_EXISTS 'e'
  #define QRP_DELIM '0'
  #define BQRP_DELIM 0
  #define MINUS '-'

  #define QRPCERT_PABORT(cond, msg, ...)                                      \
    do                                                                        \
    {                                                                         \
      if (cond)                                                               \
      {                                                                       \
        fprintf (stderr, "[QMUSExt] %s:%u:%u: ", reader.filename, reader.line,\
                 reader.col);                                                 \
        fprintf (stderr, msg, ## __VA_ARGS__);                                \
        fprintf (stderr, "\n");                                               \
        if (options.out_filename != NULL)                                     \
          unlink (options.out_filename);                                      \
        cleanup ();                                                           \
        abort ();                                                             \
      }                                                                       \
    }                                                                         \
    while (0)

  #define QRPCERT_ABORT(cond, msg, ...)                \
    do                                                 \
    {                                                  \
      if (cond)                                        \
      {                                                \
        fprintf (stderr, "[QMUSExt] %s: ", __func__);  \
        fprintf (stderr, msg, ## __VA_ARGS__);         \
        fprintf (stderr, "\n");                        \
        if (options.out_filename != NULL)              \
          unlink (options.out_filename);               \
        cleanup ();                                    \
        abort ();                                      \
      }                                                \
    }                                                  \
    while (0)

  #define QRPCERT_REALLOC(a, new, old, mem_val)                             \
    do                                                                      \
    {                                                                       \
      a = (typeof (a)) realloc (a, (new) * sizeof (typeof (*a)));           \
      QRPCERT_ABORT (a == NULL, "memory reallocation failed");              \
      if ((unsigned) (new) > (old))                                         \
        memset (a + old, mem_val, ((new) - (old)) * sizeof (typeof (*a)));  \
    }                                                                       \
    while (0)

  #define GET_INNERMOST_VAR(vertex_id)\
    ((proof_type == PTYPE_SAT) ? kh_value(h, kh_get(khIntVer, h, vertex_id)).innermost_a \
                               : kh_value(h, kh_get(khIntVer, h, vertex_id)).innermost_e)

  typedef int VarId;
  typedef VarId Lit;
  typedef int VertexId;

  static int get_non_ws_ch (void);
  static int stdin_getnextch (void);
  static int mmap_getnextch (void);
  static unsigned qrp_read_num (void);
  static Lit qrp_read_lit (void);
  static void cleanup (void);


  static void parse_qrp (void);
  static void parse_preamble (VarId *, VertexId *);
  static void parse_qsets (void);
  static void parse_vertices (int);


  //STACK_DECLARE (VarId);
  //STACK_DECLARE (VertexId);

  typedef enum
  {
    QTYPE_EXISTS = -1,
    QTYPE_UNDEF = 0,
    QTYPE_FORALL = 1
  } QType;

  typedef enum
  {
    PTYPE_UNDEF,
    PTYPE_SAT,
    PTYPE_UNSAT
  } PType;

  typedef enum
  {
    BTYPE_UNDEF,
    BTYPE_TRUE,
    BTYPE_FALSE
  } BType;

  typedef struct
  {
    VarId id;
    QType type;
    BType val;
    unsigned s_level;
  } Var_m;

  typedef struct
  {
    VertexId id;
    unsigned isactive;
    BType val;

    unsigned num_lits;

    Lit *lits;
    unsigned lits_size;
    VarId innermost_e;
    VarId innermost_a;

    unsigned num_ants;
    VertexId ants[2];

    unsigned num_children;
    unsigned children_size;
    VertexId *children;
  } Vertex;

  typedef struct
    {
      unsigned line;
      unsigned col;
      char qrp_binary;
      int ch;
      int delim;
      unsigned num;
      Lit lit;
      int (*getch)(void);
      int (*getnextch)(void);
      unsigned (*getnum)(void);
      Lit (*getlit)(void);
      char *filename;
      char *mmap;
      size_t mmap_size;
      unsigned long mmap_pos;
    } QRPReader;


    typedef struct
    {
      char statistics:1;
      char simplify:1;
      char extract:1;
      char aiger_binary:1;
      char print_rfao;
      char qrp;
      char *out_filename;
      char *in_filename;
      size_t incr_size;
    } QRPCertOptions;

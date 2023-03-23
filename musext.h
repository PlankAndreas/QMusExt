/*  MusExt: Tool for extracting a minimal unsatisfiable core from Q-resolution proofs.
 *
 *  Copyright (c) 2022-2023 Andreas Plank.
 *
 */

  #include <stdlib.h>
  #include <stdio.h>
  #include <sys/unistd.h>


  #define REALLOC(address, new_value, old_value, mem_val)                             \
    do                                                                      \
    {                                                                       \
      address = (typeof (address)) realloc (address, (new_value) * sizeof (typeof (*address)));            \
      if ((unsigned) (new_value) > (old_value))                                         \
        memset (address + old_value, mem_val, ((new_value) - (old_value)) * sizeof (typeof (*address)));  \
    }                                                                       \
    while (0)


  static int get_non_ws_ch (void);
  static int stdin_getnextch (void);
  static int mmap_getnextch (void);
  static unsigned getnum_function (void);
  static int getlit_function (void);


  static void parse_qrp (void);
  static void parse_preamble (int *, int *);
  static void parse_qsets (void);
  static void parse_vertices (int);


  typedef struct
  {
    int id;
    int type;
    int val;
    unsigned s_level;
  } Var_m;

  typedef struct
  {
    int id;
    unsigned isactive;
    int val;

    unsigned num_lits;

    int *lits;
    unsigned lits_size;
    int innermost_e;
    int innermost_a;

    unsigned num_ants;
    int ants[2];

    unsigned num_children;
    unsigned children_size;
    int *children;
  } Vertex;

  typedef struct
    {
      unsigned line;
      unsigned col;
      int ch;
      int delimiter;
      unsigned num;
      int lit;
      int (*get_cur_ch)(void);
      int (*getnextch)(void);
      unsigned (*getnum)(void);
      int (*getlit)(void);
      char *filename;
      char *mmap;
      size_t inputmap_size;
      unsigned long inputmap_pos;
    } QParser;


    typedef struct
    {
      char *out_filename;
      char *in_filename;
    } Options;

/*  MusExt: Tool for extracting a minimal unsatisfiable core from Q-resolution proofs.
 *
 *  Copyright (c) 2022-2023 Andreas Plank.
 *
 */


//------------Include Section -------------------//

#include "musext.h"
#include <time.h>
#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <sys/mman.h>
#include "./libs/khash.h"
#include <sys/stat.h>
#include <fcntl.h>
#include <assert.h>
#include<sys/wait.h>
#include "./libs/depqbf/qdpll.h"
#include "./libs/depqbf/qdpll_internals.h"



//------------Static Variables and Structs and Functions -------------------//

static FILE *out = NULL;
int output_flag=0;
static Var_m *vars = NULL;
static unsigned vars_size = 0;
FILE* myStream;
FILE* quantifierStream;
char *quantifier_buffer; //for open_memstream
size_t quantifier_size;
//static Vertex *vertices = NULL;

static unsigned vertices_size = 0;
static unsigned long long num_literals = 0;
static unsigned num_vars = 0;
static unsigned num_vertices = 0;
static unsigned num_vertices_total = 0;
static int *map_var = NULL;
static unsigned map_var_size = 0;
static int *map_c2v = NULL;
static unsigned map_c2v_size = 0;
static char *var_lookup = NULL;
static int proof_type = 0;
static int empty_vertex = 0;
int global_offset=1;
int debug_var=0;
int return_code=0;

static int max_var_index = 0;

static QParser parser =
{
    .line = 1,
    .col = 0,
    .delimiter= '0',
    .get_cur_ch = get_non_ws_ch,
    .getnextch = stdin_getnextch,
    .getnum = getnum_function,
    .getlit = getlit_function,
    .filename = "stdin",
    .mmap = NULL,
    .inputmap_size = 0,
    .inputmap_pos = 0,
};

static Options options =
{
    .out_filename = NULL,
    .in_filename = NULL
};


static int
get_non_ws_ch (void)
{
    while (isspace (parser.getnextch ()));

    return parser.ch;
}

static int
stdin_getnextch (void)
{
    parser.ch = getc (stdin);

    if (parser.ch == '\n')
    {

        parser.col = 0;
        parser.line = parser.line + 1;
    }
    else
        parser.col =parser.col +1;

    return parser.ch;
}

static int
mmap_getnextch (void)
{
    if (parser.inputmap_pos == parser.inputmap_size)
        parser.ch = EOF;
    else
        parser.ch = (unsigned char) parser.mmap[parser.inputmap_pos++];

    if (parser.ch == '\n')
    {

        parser.col = 0;
        parser.line = parser.line + 1;
    }
    else
        parser.col = parser.col + 1;

    return parser.ch;
}



static unsigned
getnum_function (void)
{
    if (!isdigit (parser.ch))
        parser.get_cur_ch ();

    parser.num = 0;
    do
    {
        if (!isdigit (parser.ch)){
           fprintf(stderr,"no digit");
           abort();
        }
        parser.num = parser.num * 10 + (parser.ch - '0');
    }
    while (!isspace (parser.getnextch ()) &&
            (parser.ch != 0));

    return parser.num;
}

static int
getlit_function (void)
{
    int neg;

    if (isspace (parser.ch))
        parser.get_cur_ch ();

    neg = parser.ch == '-';
    parser.getnum ();
    parser.lit = neg ? -parser.num : parser.num;
    return parser.lit;
}




int comp (const void * elem1, const void * elem2)
{
    int f = *((int*)elem1);
    int s = *((int*)elem2);
    if (f > s) return  1;
    if (f < s) return -1;
    return 0;
}

void SortArray(int Size, int* parr)
{
    int i, j, temp;

    for (i = 0; i < Size; i++)
    {
        for (j = i + 1; j < Size; j++)
        {
            if(*(parr + j) < *(parr + i))
            {
                temp = *(parr + i);
                *(parr + i) = *(parr + j);
                *(parr + j) = temp;
            }
        }
    }
}

long getUnsignedRightShift(long value,int s)
{
    return (long)((ulong)value >> s);
}


static void
parse_options (int argc, char **argv, char *path, char* mmap_array)
{
    int i;
    char *option;

    for  (i = 1; i < argc; i++)
    {
        option = argv[i];

        if (strcmp (option, "-o") == 0)
        {
            if(i + 1 >= argc){
                fprintf(stderr,"no -o filename given");
                abort();
            }
            options.out_filename = argv[++i];
            if(options.out_filename[0] == '-'){
                fprintf(stderr,"no -o filename given");
                abort();
            }
            output_flag=1;

        }

        else if (option[0] == '-')
        {
            fprintf(stderr, "no option given");
            abort();
        }
        else
        {
            int in_mmap_fd;
            struct stat s;
            options.in_filename=option;

            in_mmap_fd = open (option, O_RDONLY);
            if(in_mmap_fd==-1){
                fprintf(stderr,"input file not opened");
                abort();
            }
            fstat (in_mmap_fd, &s);
            parser.inputmap_size = s.st_size;
            parser.mmap = (char *) mmap (0, parser.inputmap_size, PROT_READ,
                                         MAP_PRIVATE | MAP_NORESERVE, in_mmap_fd, 0);
            close (in_mmap_fd);

            parser.getnextch = mmap_getnextch;
            parser.filename = option;
        }
    }




}

//------------Hash Functionalities ------------------//

// shorthand way to get the key from hashtable or defVal if not found
#define kh_get_val(kname, hash, key, defVal) ({k =kh_get(kname, hash, key);(k !=kh_end(hash)?kh_val(hash,k ):defVal);})

// shorthand way to set value in hash with single line command.  Returns value
// returns 0=replaced existing item, 1=bucket empty (new key), 2-adding element previously deleted
#define kh_set(kname, hash, key, val) ({int ret; k_iter  = kh_put(kname, hash,key,&ret); kh_value(hash,k_iter ) = val; ret;})



#define \
    mx_hf(a) ({ \
      int result=0; \
      int i; \
      for (i = 0; i < (a).num_lits; i++) { \
        result = (result << 5) | getUnsignedRightShift(result,27); \
        result += (a).lits[i]; \
      }\
      result;\
    })

#define \
    mx_hf3(a) ({ \
      int result=0; \
      result = (a).id; \
      (int) result;\
    })


#define \
    mx_eq4(a,b) \
    ({ \
        int result; \
        result=1;\
        int eq_i;\
        qsort((a).lits,(a).num_lits, sizeof(int),comp);\
        qsort((b).lits,(b).num_lits, sizeof(int),comp);\
        if((a).num_lits != (b).num_lits){\
          result=0;\
        }else{\
          for(eq_i=0;eq_i<(a).num_lits;eq_i++)\
          {\
            if((a).lits[eq_i]!=(b).lits[eq_i])\
              {\
                result=0;\
                break;\
              }\
          }\
        };\
        result; \
    })

#define hash_eq(a, b) ((a) == (b))
#define hash_func(a) ((a))

#define mx_eq2(a, b) ((a).id == (b).id)
#define mx_hf2(a) ((a).id)

const int khVerInt = 33;
const int khIntVer = 34;
const int khIntInt = 35;
const int khInt = 36;
const int khIntStr = 37;



//KHASH_INIT(iun, int_unpack_t, char, 0, hash_func, hash_eq)

KHASH_INIT(khVerInt, Vertex, int, 1, mx_hf3, mx_eq4)
KHASH_INIT(khIntVer, int, Vertex, 1, hash_func, hash_eq)


KHASH_MAP_INIT_INT(khIntInt, int)
KHASH_SET_INIT_INT(khInt)
KHASH_MAP_INIT_INT(khIntStr, char*)

static khash_t(khIntVer) *h = NULL;
static khash_t(khVerInt) *h_lookup = NULL;
static khash_t(khIntInt) *initial_vars = NULL;
static khash_t(khInt) *current_cone = NULL;
static khash_t(khInt) *deactivated_clausegroups = NULL;
static khash_t(khIntInt) *map_vert_clause = NULL;
static khash_t(khInt) *new_vertices = NULL;
static khash_t(khIntInt) *map_cid_ver = NULL;
static khash_t(khIntVer) *cid_backup = NULL;
static khash_t(khIntInt) *map_id_ants_output = NULL;

static int ret;
static khiter_t k1;
static khiter_t k2;



//------------Parse Functions -------------------//




static void
new_var (int id, int type, int s_level)
{

    if (id > max_var_index)
    {
        REALLOC (map_var, id + 1, map_var_size, 0);
        map_var_size = id + 1;
        max_var_index = id;
    }

    if (num_vars + 1 >= vars_size)
    {
        REALLOC (vars, vars_size + 1, vars_size, 0);
        vars_size += 1;
    }
    assert (map_var[id] == 0);

    int vid = ++num_vars;
    map_var[id] = vid;
    memset (vars + vid, 0, sizeof (Var_m));

    vars[vid].id = id;
    vars[vid].type = type;
    vars[vid].s_level = s_level;
    vars[vid].val = 0;
}

static int
new_vertex (int id, int parsing_position)
{

    assert (map_c2v != NULL);


    if ((unsigned) id >= map_c2v_size)
    {
        REALLOC (map_c2v, id * 1.5 + 1, map_c2v_size, 0);
        map_c2v_size = id * 1.5;
    }


    int vid;
    num_vertices++;
    vid = ++num_vertices_total;

    map_c2v[id] = vid;
    if(parsing_position==1||parsing_position==2)
    {
        khiter_t temp_iterator;
        temp_iterator = kh_put(khIntInt,map_cid_ver,id,&ret);
        kh_value(map_cid_ver,temp_iterator)=vid;

    }



    Vertex v;
    memset (&v, 0, sizeof(Vertex));

    v.id=vid;
    v.isactive=1;
    v.lits_size = 4;
    v.num_lits=0;



    REALLOC (v.lits, v.lits_size, 0, 0);
    v.children_size = 4;
    v.num_children=0;
    v.num_ants=0;
    REALLOC (v.children, v.children_size, 0, 0);
    v.val = 0;

    if(parsing_position!=2)
    {
        k1 = kh_put(khIntVer, h, vid, &ret);
        kh_value(h, k1)=v;
    }
    else
    {
        k1 = kh_put(khIntVer, cid_backup, vid, &ret);
        kh_value(cid_backup, k1)=v;
    }

    return vid;
}

khiter_t
move_from_backup_to_active(khiter_t k_temp_aid, int parsing_position,int aid,int id)
{
    unsigned old_size, new_size, pos;
    k_temp_aid=kh_get(khIntVer,cid_backup,aid);
    khiter_t backup_iter;
    backup_iter=kh_put(khIntVer,h,kh_key(cid_backup,k_temp_aid),&ret);
    kh_value(h,backup_iter)=kh_value(cid_backup,k_temp_aid);

    if(parsing_position==2)
    {
        kh_put(khInt,new_vertices,kh_key(cid_backup,k_temp_aid),&ret);
    }

    k_temp_aid=backup_iter;



    if (kh_val(h,k_temp_aid).children_size == kh_val(h,k_temp_aid).num_children)
    {
        old_size = kh_val(h,k_temp_aid).children_size;
        new_size = old_size + (old_size >> 2) + 1;
        REALLOC (kh_val(h,k_temp_aid).children, new_size, old_size, 0);
        kh_val(h,k_temp_aid).children_size = new_size;
    }

    assert (kh_val(h,k_temp_aid).num_children + 1 <= kh_val(h,k_temp_aid).children_size);


    if (kh_val(h,k_temp_aid).children_size == kh_val(h,k_temp_aid).num_children)
    {
        old_size = kh_val(h,k_temp_aid).children_size;
        new_size = old_size + (old_size >> 2) + 1;
        REALLOC (kh_val(h,k_temp_aid).children, new_size, old_size, 0);
        kh_val(h,k_temp_aid).children_size = new_size;
    }

    assert (kh_val(h,k_temp_aid).num_children + 1 <= kh_val(h,k_temp_aid).children_size);

    pos = kh_val(h,k_temp_aid).num_children;
    kh_val(h,k_temp_aid).children[pos] = id;
    kh_val(h,k_temp_aid).num_children += 1;

    int i;
    khiter_t k_temp_aid_2;
    for(i=0; i<kh_val(h,k_temp_aid).num_ants; i++)
    {
        aid=kh_val(h,k_temp_aid).ants[i];
        k_temp_aid_2 = kh_get(khIntVer, h, aid);
        if(k_temp_aid_2==kh_end(h))
        {
            move_from_backup_to_active(k_temp_aid_2, parsing_position,aid,id);
        }
    }

    return k_temp_aid;
}

static void
vertex_add_antecedent (int id, int aid, int parsing_position)
{
    unsigned pos, new_size, old_size;
    khiter_t k_temp, k_temp_aid;

    if(parsing_position!=2)
    {
        k_temp = kh_get(khIntVer, h, id);



        assert (kh_val(h,k_temp).num_ants <= 2);
        kh_val(h,k_temp).ants[kh_val(h,k_temp).num_ants] = aid;
        kh_val(h,k_temp).num_ants += 1;
        k_temp_aid = kh_get(khIntVer, h, aid);

        if(k_temp_aid==kh_end(h))
        {
            //check if we have already parsed the vertex, we did not need before. If so we have to transfer it from the backup to  the real hash map
            //the setting of the ants is then done by the move function.
            k_temp_aid=move_from_backup_to_active(k_temp_aid, parsing_position,aid,id);
            return;




        }


        if (kh_val(h,k_temp_aid).children_size == kh_val(h,k_temp_aid).num_children)
        {
            old_size = kh_val(h,k_temp_aid).children_size;
            new_size = old_size + (old_size >> 2) + 1;
            REALLOC (kh_val(h,k_temp_aid).children, new_size, old_size, 0);
            kh_val(h,k_temp_aid).children_size = new_size;
        }

        assert (kh_val(h,k_temp_aid).num_children + 1 <= kh_val(h,k_temp_aid).children_size);

        pos = kh_val(h,k_temp_aid).num_children;
        kh_val(h,k_temp_aid).children[pos] = id;
        kh_val(h,k_temp_aid).num_children += 1;
    }
    else
    {
        k_temp = kh_get(khIntVer, cid_backup, id);



        assert (kh_val(cid_backup,k_temp).num_ants <= 2);
        kh_val(cid_backup,k_temp).ants[kh_val(cid_backup,k_temp).num_ants] = aid;
        kh_val(cid_backup,k_temp).num_ants += 1;

        k_temp_aid = kh_get(khIntVer, cid_backup, aid);
    }



}

static void
vertex_add_literal (int vid, int lit, int parsing_position)
{

    if(parsing_position!=2)
    {
        unsigned pos, new_size, old_size;

        khiter_t k_temp;

        k_temp = kh_get(khIntVer, h, vid);



        if (kh_val(h,k_temp).num_lits == kh_val(h,k_temp).lits_size-1)
        {
            old_size = kh_val(h,k_temp).lits_size;
            new_size = old_size + (old_size >> 2);
            REALLOC (kh_val(h,k_temp).lits, new_size, old_size, 0);
            kh_val(h,k_temp).lits_size = new_size;
        }

        assert (kh_val(h,k_temp).num_lits + 1 <= kh_val(h,k_temp).lits_size);

        pos = kh_val(h,k_temp).num_lits;
        kh_val(h,k_temp).lits[pos] = lit;


        kh_val(h,k_temp).num_lits += 1;

        if (vars[abs (lit)].type == -1 &&
                kh_val(h,k_temp).innermost_e < abs (lit))
            kh_val(h,k_temp).innermost_e = abs (lit);
        else if (vars[abs (lit)].type == 1 &&
                 kh_val(h,k_temp).innermost_a < abs (lit))
            kh_val(h,k_temp).innermost_a = abs (lit);
    }
    else
    {
        unsigned pos, new_size, old_size;

        khiter_t k_temp;

        k_temp = kh_get(khIntVer, cid_backup, vid);



        if (kh_val(cid_backup,k_temp).num_lits == kh_val(cid_backup,k_temp).lits_size-1)
        {
            old_size = kh_val(cid_backup,k_temp).lits_size;
            new_size = old_size + (old_size >> 2);
            REALLOC (kh_val(cid_backup,k_temp).lits, new_size, old_size, 0);
            kh_val(cid_backup,k_temp).lits_size = new_size;
        }

        assert (kh_val(cid_backup,k_temp).num_lits + 1 <= kh_val(cid_backup,k_temp).lits_size);

        pos = kh_val(cid_backup,k_temp).num_lits;
        kh_val(cid_backup,k_temp).lits[pos] = lit;


        kh_val(cid_backup,k_temp).num_lits += 1;

        if (vars[abs (lit)].type == -1 &&
                kh_val(cid_backup,k_temp).innermost_e < abs (lit))
            kh_val(cid_backup,k_temp).innermost_e = abs (lit);
        else if (vars[abs (lit)].type == 1 &&
                 kh_val(cid_backup,k_temp).innermost_a < abs (lit))
            kh_val(cid_backup,k_temp).innermost_a = abs (lit);
    }





}



static void
parse_qrp (void)
{
    int max_vertex_index;

    parse_preamble (&max_var_index, &max_vertex_index);

    REALLOC (map_var, max_var_index + 1, 0, 0);
    map_var_size = max_var_index + 1;
    REALLOC (vars, max_var_index + 1, 0, 0);
    vars_size = max_var_index + 1;
    REALLOC (map_c2v, max_vertex_index + 1, 0, 0);
    map_c2v_size = max_vertex_index + 1;
    vertices_size = max_vertex_index + 1;

    parse_qsets ();
    parse_vertices (0);


    /* parse result line  */
    if(parser.ch != 'r')
    {
        fprintf(stderr,"I expected a result!");
        abort();
    };

    if (tolower (parser.get_cur_ch ()) == 's')
    {
        proof_type = 1;
    }
    else if (tolower (parser.ch) == 'u')
    {
        proof_type = 2;
    }


    if (parser.mmap != NULL)
    {
        munmap (parser.mmap, parser.inputmap_size);
        parser.mmap = NULL;
    }
}

static void
parse_preamble (int *max_var_index, int *max_vertex_index)
{
    assert (max_var_index != NULL);
    assert (max_vertex_index != NULL);

    char *str;
    unsigned i;

    if(parser.get_cur_ch () == EOF)
    {
        fprintf(stderr,"Empty file give!");
        abort();
    };

    /* skip comments  */
    while (parser.ch == '#')
    {
        while (parser.getnextch () != '\n' && parser.ch != EOF);
        parser.get_cur_ch ();
    }

    /* preamble  */
    if(parser.ch != 'p')
    {
        fprintf(stderr,"Preamble missing");
        abort();
    };

    str = "qrp";
    for (i = 0; str[i] != '\0'; i++)
    {
        parser.get_cur_ch ();
    }
    *max_var_index = parser.getnum ();
    *max_vertex_index = parser.getnum ();

}

static void
parse_qsets (void)
{
    unsigned s_level = 1;
    int type;

    quantifierStream = open_memstream(&quantifier_buffer, &quantifier_size);      //the trace output will be saved in the memstream

    /* parser.ch contains either '\n' or B'0' */
    for (;;)
    {
        /* check beginning of binary quantifiers set  */
        if (0 && parser.get_cur_ch () != parser.delimiter)
            break;

        /* get quantifier symbol  */
        parser.get_cur_ch ();
        if(parser.ch=='e'||parser.ch=='a')
        {
            fprintf(quantifierStream,"%c ",parser.ch);
        }



        if(return_code==20)
        {
            if (parser.ch == 'a')
                type = 1;
            else if (parser.ch == 'e')
                type = -1;
            else
                break;
        }
        else if(return_code==10)
        {
            if (parser.ch == 'a')
                type = -1;
            else if (parser.ch == 'e')
                type = 1;
            else
                break;
        }

        /* parser.ch contains 'a' or 'e'  */
        /* parse variables in quantifier set  */
        while (parser.get_cur_ch () != parser.delimiter)
        {
            int newlit=parser.getnum();
            fprintf(quantifierStream,"%d ",newlit);
            new_var (newlit, type, s_level);
        }
        fprintf(quantifierStream,"0\n");


        s_level += 1;
    }
    fclose(quantifierStream);

    /* no quantifier set parsed  */
    if(s_level==1)
    {
        fprintf(stderr,"We have no quantifier set");
        abort();
    }
}

static void
parse_vertices (int parsing_position)
{


    int vid, aid;

    if(parsing_position!=1&&parsing_position!=2)
    {
        assert (var_lookup == NULL);
        REALLOC (var_lookup, num_vars + 1, 0, 0);
    }




    /* parser.ch contains first digit of first vertex id  */
    for (;;)
    {
        long temp_vid=parser.getnum ();




        vid = new_vertex (temp_vid, parsing_position);


        if(parsing_position==1)
        {
            kh_put(khInt,new_vertices,vid,&ret);
        }




        memset (var_lookup, 0, (num_vars + 1) * sizeof (char));

        /* parse literals  */
        /* parser.ch contains either a whitespace or last digit of vid  */
        for (;;)
        {
            if (parser.get_cur_ch () == parser.delimiter)
                break;

            parser.getlit ();


            if(parsing_position==1||parsing_position==2)
            {
                if(parser.num > (unsigned) max_var_index)
                {
                    continue;
                }
            }



            if (var_lookup[map_var[abs (parser.lit)]] == 1)
                continue;

            var_lookup[map_var[abs (parser.lit)]] = 1;


            if(return_code==20)
            {
                vertex_add_literal (vid, parser.lit < 0 ? -map_var[-parser.lit]
                                    : map_var[parser.lit],parsing_position);
            }
            else if(return_code==10)
            {
                vertex_add_literal (vid, parser.lit < 0 ? map_var[-parser.lit]
                                    : -map_var[parser.lit],parsing_position);
            }


            num_literals += 1;
        }

        khiter_t k_ret;
        Vertex v_lookup;
        if(parsing_position!=2)
        {
            k_ret = kh_get(khIntVer, h, vid);
            v_lookup = kh_val(h, k_ret);
        }
        else
        {
            k_ret = kh_get(khIntVer, cid_backup, vid);
            v_lookup = kh_val(cid_backup, k_ret);
        }

        k2 = kh_get(khVerInt, h_lookup, v_lookup); // get the iterator
        if(parsing_position!=2)
        {
            k2 = kh_put(khVerInt, h_lookup, v_lookup, &ret);
            kh_value(h_lookup, k2)=vid;
        }










        /* parse antecedents  */
        /* parser.ch contains parser.delimiter  */
        for (;;)
        {
            if (parser.get_cur_ch () == parser.delimiter)
                break;

            aid=parser.getnum();


            if(parsing_position==1||parsing_position==2)
            {
                aid=kh_value(map_cid_ver,kh_get(khIntInt,map_cid_ver,aid));
            }



            if(parsing_position!=2)
            {
                if(kh_val(h,kh_get(khIntVer, h, vid)).num_ants >= 2){
                    fprintf(stderr,"wrong number of ants given");
                    abort();
                }
            }
            else
            {
                if(kh_val(cid_backup,kh_get(khIntVer, cid_backup, vid)).num_ants >= 2){
                    fprintf(stderr,"wrong number of ants given");
                    abort();
                }
            }

            vertex_add_antecedent (vid, aid,parsing_position);
        }

        /* empty clause/cube  */
        if(parsing_position!=2)
        {
            if (kh_val(h,kh_get(khIntVer, h, vid)).num_lits == 0)
            {
                //assert (empty_vertex == 0);
                empty_vertex = vid;
            }
        }
        else
        {
            if (kh_val(cid_backup,kh_get(khIntVer, cid_backup, vid)).num_lits == 0)
            {
                empty_vertex = vid;
            }
        }


        /* parser.ch contains parser.delimiter  */
        parser.get_cur_ch ();

        if ((parser.ch == 'r') || parser.ch == EOF)
            break;

        /* check for binary result statement  */
        if (0 && parser.ch == parser.delimiter)
        {
            if (parser.get_cur_ch () == 'r' || parser.ch == EOF)
                break;
        }
    }
}


void check_connected(int vid, int *temparray)
{
    unsigned i;
    temparray[vid]=1;
    Vertex v=kh_val(h,kh_get(khIntVer, h, vid));
    for(i=0; i<v.num_ants; i++)
    {
        check_connected(v.ants[i], temparray);
    }
}


void deactivate_cone(int vid)
{

    kh_put(khInt, current_cone, vid, &ret);
    int i;

    for(i=0; i<kh_value(h,kh_get(khIntVer, h, vid)).num_children; i++)
    {
        deactivate_cone(kh_value(h,kh_get(khIntVer, h, vid)).children[i]);
    }

}


//------------global variables used for the computation of the mus -------------------//

unsigned num_initial_var = 0;
unsigned deleted_initials = 0;



int* connected_to_empty_arr;


//
static int num_clauses;
//static int num_variables;
ClauseGroupID* unsat_core;
ClauseGroupID* clausegroups;
int count_clausegroups=0;
int preamble_flag=0;





//------------Main Function -------------------//

int main(int argc, char **argv)
{

    char* buffer_mcreturn = NULL;
    //iterator variables used for loops over hash tables
    khiter_t k_loop;
    khiter_t k_loop2;
    khiter_t k_loop3;

    //initialize some hash maps
    map_cid_ver = kh_init(khIntInt); //hash map with vert.id used by the solver instance as key and internal vert.id as values
    cid_backup = kh_init(khIntVer);
    h = kh_init(khIntVer);  //hash map containing vertices.id as keys and the internal vertices as values
    h_lookup = kh_init(khVerInt);   //hash map containing vertices as keys and the vertices.id as value


    //parse the inputs given to the programm


    parse_options(argc,argv,NULL,NULL);


    size_t bufferSize_mcreturn = 0;
    myStream = open_memstream(&buffer_mcreturn, &bufferSize_mcreturn);

    int my_pipe[2];
    if(pipe(my_pipe) == -1)
    {
        fprintf(stderr, "Error creating pipe\n");
    }

    pid_t child_id;
    child_id = fork();
    if(child_id == -1)
    {
        fprintf(stderr, "Fork error\n");
    }
    if(child_id == 0)
    {
        close(my_pipe[0]);
        dup2(my_pipe[1], STDOUT_FILENO);
        printf("filename %s",options.in_filename);

        char* argv3[] = { "./bin/depqbf", "--no-dynamic-nenofex","--no-qbce-dynamic","--qbce-max-clause-size=0","--incremental-use","--trace=qrp","--dep-man=simple","--traditional-qcdcl", options.in_filename,NULL};


        execv(argv3[0], argv3);
        fprintf(stderr, "Exec failed\n");
    }
    else
    {
        close(my_pipe[1]);

        char reading_buf[10];

        while(read(my_pipe[0], reading_buf, 1) > 0)
        {
            fprintf(myStream,"%s",reading_buf);
        }
        close(my_pipe[0]);

        int waitstatus;
        wait(&waitstatus);
        return_code = WEXITSTATUS(waitstatus);

    }
    fclose(myStream);
    parser.mmap=buffer_mcreturn;
    parser.inputmap_size=bufferSize_mcreturn;
    parser.getnextch = mmap_getnextch;




    parse_qrp ();



    //initialize the arrays used for keeping track of the initial variables
    initial_vars = kh_init(khIntInt);   //hashmap that holds the vertex id of all vertices that are initial ids as keys;
    map_vert_clause = kh_init(khIntInt);    //hashmap that has internal vert.id as keys and clause.group numbers as values





    //iterate over all vertices and set the initial vars array for the vertices without any ants

    khiter_t variter;
    for (k_loop = kh_begin(h); k_loop != kh_end(h); ++k_loop)           //we iterate over the iterator of a hashmap in order to conduct the iterations
    {
        if (kh_exist(h, k_loop))                                        //check if the key is in the hash map (it should be for our application)
        {
            Vertex vert = kh_value(h, k_loop);                          //get the vertex belonging to the current iterator
            if(vert.num_ants==0&&vert.num_lits>0)                       //only add not empty vertices without antecendents
            {
                variter = kh_put(khIntInt, initial_vars, vert.id, &ret); // add the key
                kh_value(initial_vars, variter) = 1; // set the value of the key
                num_initial_var++;
            }
        }
    }



    //initialize array that indicates if vertex is connected to the empty vertex
    connected_to_empty_arr = (int*)malloc((num_vertices+1) * sizeof(int));
    for (k_loop = kh_begin(h); k_loop != kh_end(h); ++k_loop)
    {
        if (kh_exist(h, k_loop))
        {
            connected_to_empty_arr[kh_key(h,k_loop)]=0;
        }
    }

    //recursive function that sets and index if vertex is connected to the empty vertex
    check_connected(num_vertices,connected_to_empty_arr);



    //index variables used for different for loops
    int i;
    int j;
    int k;
    int l;

    //we now delete vertices that are not connected to the empty vertex
    for (k_loop = kh_begin(h); k_loop != kh_end(h); ++k_loop)
    {
        if (kh_exist(h, k_loop))
        {

            i=kh_key(h,k_loop);
            //if they are not connected to the empty set we need to do something
            if(connected_to_empty_arr[i]==0)
            {

                //if the current vertex (not connected to empty) is a children of another vertex you have to remove it from that vertex and reduce the children count
                for (k_loop2 = kh_begin(h); k_loop2 <=i; ++k_loop2)     //iterate over all vertices up to the current vertex
                {
                    if (kh_exist(h, k_loop2))
                    {
                        for(k=0; k<kh_value(h, k_loop2).num_children; k++)  //iterate over all children of the vertex
                        {
                            if(kh_value(h, k_loop2).children[k]==(int)i)    //check if the children is the vertex to delte
                            {
                                for(l=k; l<kh_value(h, k_loop2).num_children-1; l++)    //if yes delete it
                                {
                                    kh_value(h, k_loop2).children[l]=kh_value(h, k_loop2).children[l+1];
                                }
                                kh_value(h, k_loop2).num_children-=1;       //reduce the number of children of the vertex
                            }
                        }
                    }
                }


                //free the lits and children arrays and delete the vertex from the hash map
                //get iterator for deletion of lookup entries
                k2 = kh_get(khVerInt,h_lookup,kh_value(h, kh_get(khIntVer, h, i)));
                kh_del(khVerInt, h_lookup, k2);

                //free the memory of the children and lits array of the vertex to delete
                free(kh_value(h, kh_get(khIntVer, h, i)).lits);
                free(kh_value(h, kh_get(khIntVer, h, i)).children);


                num_vertices--;

                //if the vertex was an initial one, remove it from the inital vars hash map
                if(kh_get(khIntInt,initial_vars,i)!=kh_end(initial_vars))
                {
                    kh_value(initial_vars, kh_get(khIntInt, initial_vars, kh_value(h, kh_get(khIntVer, h, i)).id))=0;
                    num_initial_var--;
                }
                kh_del(khIntVer, h, kh_get(khIntVer, h, i));        //delete the vertex

            }
        }
    }




    //create the solver instance and parse the current vertices
    QDPLL *qdpll = qdpll_create ();



    //configure the QBF solver
    qdpll_configure (qdpll, "--dep-man=simple");    //Use the linear ordering of the quantifier prefix.
    qdpll_configure (qdpll, "--incremental-use");   //Enable incremental solving.
    qdpll_configure (qdpll, "--traditional-qcdcl"); //traditional qcdcl is need for outputing the trace
    qdpll_configure (qdpll, "--qbce-witness-max-occs=0");
    qdpll_configure (qdpll, "--qbce-max-clause-size=0");


    //parse the vertices to the solver
    num_clauses = num_vertices;     //number of clauses stored by the solver instance
    clausegroups = (ClauseGroupID*)malloc(num_clauses * sizeof(ClauseGroupID)); //array that holds all clausegroup-ids (basically every clause is its own clausegroup)
    deactivated_clausegroups = kh_init(khInt);  //hash map that holds the clausegroup-id of all currently deactivated clause groups

    QDPLLQuantifierType scope_type = QDPLL_QTYPE_UNDEF;

    //parse all variables with the according quantifiers
    for(i=1; i<=num_vars; i++)
    {
        if (vars[i].type==1)
        {
            scope_type = QDPLL_QTYPE_FORALL;
        }
        else
        {
            scope_type = QDPLL_QTYPE_EXISTS;
        }
        qdpll_new_scope (qdpll, scope_type);

        qdpll_add(qdpll,vars[i].id);
        qdpll_add(qdpll,0);
    }



    //parse all to vertices to the solver
    for (k_loop = kh_begin(h); k_loop != kh_end(h); ++k_loop)       //iterate over the internal vertices
    {
        if (kh_exist(h, k_loop))
        {
            clausegroups[count_clausegroups]=qdpll_new_clause_group(qdpll);         //create a new clausegroup for each clause
            qdpll_open_clause_group (qdpll, clausegroups[count_clausegroups]);      //open the just created clausegroup
            for(j=0; j<kh_value(h, k_loop).num_lits; j++)                           //iterate over every literal and add it to the clause of the solver
            {
                long temp_lit=0;
                if(kh_value(h,k_loop).lits[j] < 0)
                {
                    temp_lit=-vars[-kh_value(h,k_loop).lits[j]].id;
                }
                else
                {
                    temp_lit=vars[kh_value(h,k_loop).lits[j]].id;
                }
                qdpll_add(qdpll,temp_lit);

            }
            qdpll_add(qdpll,0);                                                     //delimiterit the current clause

            //add the new clause to the internal vertices clausegroup array map; We do not need to add +1 here as we are refering to the clausegroup array
            khiter_t  k_tempiter2;
            k_tempiter2 = kh_put(khIntInt, map_vert_clause, kh_value(h, k_loop).id, &ret);

            kh_value(map_vert_clause, k_tempiter2)=count_clausegroups;

            //add the new clause to the solver clause id to the internal vertices map; i.e. the map of the internal vertitices  to the real id used by the solver
            //the solver starts at 1 with the first clause id so we need to add 1 (count_clausegroup+1), to get the right value
            khiter_t temp_iterator;
            temp_iterator = kh_put(khIntInt,map_cid_ver,count_clausegroups+1,&ret);
            kh_value(map_cid_ver,temp_iterator)=kh_value(h, k_loop).id;

            //add the new clause group to the clausgroup-hashset
            assert (qdpll_get_open_clause_group (qdpll) == clausegroups[count_clausegroups]);
            qdpll_close_clause_group (qdpll, clausegroups[count_clausegroups]);
            count_clausegroups++;
        }
    }


    //invoke the solver
    QDPLLResult res = qdpll_sat (qdpll);






    int initial_temp_index;     //id of the currently processed initial vertex

    //we now start to iterate through the initial vertices and temporarly deactivate the according cones
    for (k_loop = kh_begin(initial_vars); k_loop != kh_end(initial_vars); ++k_loop)
    {

        if (kh_exist(initial_vars, k_loop))
        {

            initial_temp_index = kh_key(initial_vars,k_loop);


            qdpll_reset(qdpll);     //the solver has to be reset for each iteration

            qdpll_configure (qdpll, "--dep-man=simple");
            qdpll_configure (qdpll, "--incremental-use");
            qdpll_configure (qdpll, "--trace=qrp");             //for the iterations we need to export the trace
            qdpll_configure (qdpll, "--traditional-qcdcl");
            qdpll_configure (qdpll, "--qbce-witness-max-occs=0");
            qdpll_configure (qdpll, "--qbce-max-clause-size=0");



            //skip the initial variable if it was already deleted
            if(kh_value(initial_vars,k_loop)==0)
            {
                continue;
            }


            //initialize hash-sets that hold the current cone and new vertices(given by the trace)
            current_cone = kh_init(khInt);
            new_vertices = kh_init(khInt);


            //compute the cone of the current initial vertex
            deactivate_cone(initial_temp_index);

            //deactivate the clauses of the cone in the already parsed clauses of the solver
            for(k_loop2=kh_begin(current_cone); k_loop2!=kh_end(current_cone); ++k_loop2)
            {

                if(kh_exist(current_cone,k_loop2))
                {
                    int ind;
                    ind = kh_value(map_vert_clause,kh_get(khIntInt,map_vert_clause,kh_key(current_cone,k_loop2))); //get the index of the right clausegroup of the
                    // continuation: clausegroup array, corresponding to the internal id returned by the current_cone

                    if(kh_get(khInt,deactivated_clausegroups,ind)==kh_end(deactivated_clausegroups))    //only deactivate it if was not already deactivated before
                        qdpll_deactivate_clause_group (qdpll, clausegroups[ind]);
                    kh_put(khInt, deactivated_clausegroups, ind, &ret);
                }
            }


            char *buffer; //for open_memstream
            size_t size;
            FILE * stdsave=stdout;

            FILE * memstream = open_memstream(&buffer, &size);      //the trace output will be saved in the memstream
            stdout=memstream;      //redirect stdout to the memstream

            //invoke the sat solver
            res = qdpll_sat (qdpll);



            fclose(memstream);      //close the memstream after trace has been writen (this sets the buffer and the size)




            //reopen stdout
            stdout=stdsave;



            //set the source of parser to the newly created buffer array in order to parse the vertex output
            parser.inputmap_size = (int) size;
            parser.mmap = buffer;
            parser.inputmap_pos = 0;

            //save trace in case vertex is reused, this is important as the solver also takes these ids into consideration when giving out new ids
            if(res==10)
            {
                parse_vertices(2);

            }



            qdpll_reset(qdpll);


            //check if the restult is SAT and continue accordingly
            if(res==10)
            {

                //if the result is satisfying we know that the vertex was necessary, hence we reactivate the according clause group
                for(k_loop2=kh_begin(current_cone); k_loop2!=kh_end(current_cone); ++k_loop2)
                {
                    if(kh_exist(current_cone,k_loop2))
                    {
                        int ind;
                        ind = kh_value(map_vert_clause,kh_get(khIntInt,map_vert_clause,kh_key(current_cone,k_loop2)));

                        qdpll_activate_clause_group (qdpll, clausegroups[ind]);
                        kh_del(khInt,deactivated_clausegroups,kh_get(khInt,deactivated_clausegroups,ind));      //we need to remove the clause from the deactivated-clausegroup hashset accordingly

                    }
                }
            }
            else
            {

                //if the result is not satisfying we know the vertex was not necessary, hence we can remove the vertex and its cone from the tree
                for(k_loop2=kh_begin(current_cone); k_loop2!=kh_end(current_cone); ++k_loop2)
                {
                    if(kh_exist(current_cone,k_loop2))
                    {


                        i=kh_key(current_cone,k_loop2);





                        //if the current vertex (not connected to empty) is a children of another vertex you have to remove it from that vertex and reduce the children count (same as before)
                        for (k_loop3 = kh_begin(h); k_loop3 !=kh_end(h); ++k_loop3)
                        {
                            if (kh_exist(h, k_loop3))
                            {
                                for(k=0; k<kh_value(h, k_loop3).num_children; k++)
                                {
                                    if(kh_value(h, k_loop3).children[k]==(int)i)
                                    {
                                        for(l=k; l<kh_value(h, k_loop3).num_children-1; l++)
                                        {
                                            kh_value(h, k_loop3).children[l]=kh_value(h, k_loop3).children[l+1];
                                        }
                                        kh_value(h, k_loop3).num_children-=1;
                                    }
                                }
                            }
                        }




                        //mark the initial vars in the cone (if there are any) as not necessary
                        if(kh_end(initial_vars)!=kh_get(khIntInt, initial_vars, kh_key(current_cone,k_loop2)))
                        {
                            kh_value(initial_vars,kh_get(khIntInt, initial_vars, kh_key(current_cone,k_loop2)))=0;
                        }

                        //delete the vertex from the hash maps (the vertex hash map and the reverse hash map)
                        int vid = kh_key(current_cone,k_loop2);

                        khiter_t k_ret;
                        k_ret = kh_get(khIntVer, h, vid);

                        khiter_t k1 = kh_put(khIntVer, cid_backup, vid, &ret);
                        kh_value(cid_backup, k1)=kh_value(h,k_ret);


                        if (k_ret!=kh_end(h))
                        {
                            kh_del(khIntVer, h, k_ret);  // then delete it.
                        }
                        Vertex v_lookup = kh_val(h, k_ret);
                        k2 = kh_get(khVerInt, h_lookup, v_lookup); // get the ieterator
                        if (k2 != kh_end(h_lookup))    // if it is found
                        {

                            kh_del(khVerInt, h_lookup, k2);
                        }
                    }
                }


                //if we got a trace we need to parse it
                if((int)size>0)
                {

                    FILE *fptr;
                    fptr = fopen("./buffer_debug_file","w");
                    fprintf(fptr,"buffer=%s\n",buffer);
                    fclose(fptr);
                    parse_vertices(1);  //parse the vertices (with argument that indicates we called the parse vertex here)

                    int old_cid=0;
                    //loop over all newly parsed vertices
                    for(k_loop2=kh_begin(new_vertices); k_loop2!=kh_end(new_vertices); ++k_loop2)
                    {
                        if(kh_exist(new_vertices,k_loop2))
                        {

                            //resize the clausegroups array
                            if(num_clauses<=count_clausegroups)
                            {
                                REALLOC (clausegroups, (int)num_clauses*1.5, num_clauses, 0);
                                num_clauses = (int) num_clauses*1.5;
                            }



                            debug_var++;

                            //reroute the stdout again (as before), we need to know the clause id for the solver for our hash map
                            char *buffer2; //for open_memstream
                            size_t size2;
                            FILE* stdsave2=stdout;
                            FILE * memstream2 = open_memstream(&buffer2, &size2);
                            stdout=memstream2;



                            //add the clause to the solver instance
                            clausegroups[count_clausegroups]=qdpll_new_clause_group(qdpll);
                            qdpll_open_clause_group (qdpll, clausegroups[count_clausegroups]);


                            for(j=0; j<kh_value(h,kh_get(khIntVer,h,kh_key(new_vertices,k_loop2))).num_lits; j++)
                            {
                                qdpll_add(qdpll,kh_value(h,kh_get(khIntVer,h,kh_key(new_vertices,k_loop2))).lits[j]);
                            }
                            qdpll_add(qdpll,0);

                            fclose(stdout);
                            stdout=stdsave2;



                            //set the source of the parser
                            parser.inputmap_size = (int) size2;
                            parser.mmap = buffer2;
                            parser.inputmap_pos = 0;


                            //read the solver instance clause id
                            int cid = parser.getnum();


                            //sometimes the solver does optimizations so it gives back more than one new clause id
                            //we check in the for loop if we skipped new ids and set them to the same value as the clause id before belately
                            int additional_solver_ids; //runindex for the loop that indicates the additional ids.
                            if(old_cid!=0&&(old_cid+1)<cid)
                            {
                                for(additional_solver_ids=(old_cid+1); additional_solver_ids<cid; additional_solver_ids++)
                                {
                                    khiter_t temp_iterator;
                                    temp_iterator = kh_put(khIntInt,map_cid_ver,additional_solver_ids,&ret);

                                    kh_value(map_cid_ver,temp_iterator)=kh_value(h,kh_get(khIntVer,h,kh_key(new_vertices,k_loop2))).id;

                                }
                            }


                            free(buffer2);

                            //add the solver instance clause id (key) and internal vertex id (value) to the hash map
                            khiter_t temp_iterator;
                            temp_iterator = kh_put(khIntInt,map_cid_ver,cid,&ret);
                            kh_value(map_cid_ver,temp_iterator)=kh_value(h,kh_get(khIntVer,h,kh_key(new_vertices,k_loop2))).id;


                            //add the internal vertex id (key) and clause group id (value) to the hash map
                            khiter_t  k_tempiter2;
                            k_tempiter2 = kh_put(khIntInt, map_vert_clause, kh_value(h,kh_get(khIntVer,h,kh_key(new_vertices,k_loop2))).id, &ret);
                            kh_value(map_vert_clause, k_tempiter2)=count_clausegroups;


                            assert (qdpll_get_open_clause_group (qdpll) == clausegroups[count_clausegroups]);
                            qdpll_close_clause_group (qdpll, clausegroups[count_clausegroups]);
                            count_clausegroups++;
                            old_cid=cid;


                        }


                    }



                }

            }
            free(buffer);




            kh_destroy(khInt,current_cone);
            kh_destroy(khInt,new_vertices);
        }
    }



    qdpll_reset(qdpll);
    qdpll_delete(qdpll);

    int mus_size=0;
    for (k_loop = kh_begin(initial_vars); k_loop != kh_end(initial_vars); ++k_loop)
    {
        if (kh_exist(initial_vars, k_loop))
        {
            mus_size +=kh_value(initial_vars,k_loop);

        }
    }


    //following is a part where we output the new qrp
    int mode = 1;


    map_id_ants_output = kh_init(khIntInt);
    char *output_buffer; //for open_memstream
    size_t output_size;
    FILE * outstream = open_memstream(&output_buffer, &output_size);      //the trace output will be saved in the memstream
    int ind=0;



    if(mode==0)
    {
        fprintf(outstream,"p qrp %d %d\n",num_vars,mus_size);
        fprintf(outstream,"%s",quantifier_buffer);
        for (k_loop = kh_begin(h); k_loop != kh_end(h); ++k_loop)
        {
            if (kh_exist(h, k_loop))
            {
                ind++;
                int id = kh_key(h,k_loop);

                khiter_t temp_iterator;
                temp_iterator = kh_put(khIntInt,map_id_ants_output,id,&ret);
                kh_value(map_id_ants_output,temp_iterator)=ind;

                fprintf(outstream,"%d ",ind);
                for(j=0; j<kh_value(h, k_loop).num_lits; j++)                           //iterate over every literal and print them to stream
                {
                    long temp_lit=0;
                    if(kh_value(h,k_loop).lits[j] < 0)
                    {
                        temp_lit=-vars[-kh_value(h,k_loop).lits[j]].id;
                    }
                    else
                    {
                        temp_lit=vars[kh_value(h,k_loop).lits[j]].id;
                    }
                    if(return_code==10)
                    {
                        temp_lit=temp_lit*1;
                    }
                    fprintf(outstream,"%ld ",temp_lit);
                }
                fprintf(outstream,"0 ");
                for(j=0; j<kh_value(h, k_loop).num_ants; j++)                           //iterate over every literal and print them to stream
                {
                    int temp_lit2=kh_value(h,k_loop).ants[j];

                    int temp_lit3;
                    khiter_t zwischenschritt=kh_get(khIntInt,map_id_ants_output,temp_lit2);
                    temp_lit3=kh_value(map_id_ants_output,zwischenschritt);
                    fprintf(outstream,"%d ",temp_lit3);
                }
                fprintf(outstream,"0\n");

            }
        }
        if(proof_type == 2)
        {
            fprintf(outstream,"r UNSAT");
        }
        else
        {
            fprintf(outstream,"r SAT");
        }


        fclose(outstream);      //close the memstream after trace has been writen (this sets the buffer and the size)
    }
    else if(mode==1)
    {
        fprintf(outstream,"p cnf %d %d\n",num_vars,mus_size);
        if(return_code==20)
        {
            fprintf(outstream,"%s",quantifier_buffer);
        }
        else
        {
            int quantindex=0;
            for(quantindex=0; quantindex<quantifier_size; quantindex++)
            {
                if(quantifier_buffer[quantindex]=='e')
                {
                    fprintf(outstream,"a");
                }
                else if(quantifier_buffer[quantindex]=='a')
                {
                    fprintf(outstream,"e");
                }
                else
                {
                    fprintf(outstream,"%c",quantifier_buffer[quantindex]);
                }
            }
        }


        for (k_loop = kh_begin(initial_vars); k_loop != kh_end(initial_vars); ++k_loop)
        {
            if (kh_exist(initial_vars, k_loop))
            {
                if(kh_value(initial_vars,k_loop)==1)
                {
                    Vertex v=kh_value(h,kh_get(khIntVer,h,kh_key(initial_vars,k_loop)));
                    for(j=0; j<v.num_lits; j++)                           //iterate over every literal and print them to stream
                    {
                        long temp_lit=0;
                        if(v.lits[j] < 0)
                        {
                            temp_lit=-vars[-v.lits[j]].id;
                        }
                        else
                        {
                            temp_lit=vars[v.lits[j]].id;
                        }
                        fprintf(outstream,"%ld ",temp_lit);
                    }
                    fprintf(outstream,"0\n");
                }
            }
        }
        fclose(outstream);
    }
    if(output_flag==1)
    {
        out = fopen (options.out_filename, "w");
        if(out==NULL){
            fprintf(stderr,"no output file with name '%s' given",options.out_filename);
            abort();
        }
        fprintf(out,"%s",output_buffer);
        fclose(out);
    }



    free(quantifier_buffer);
    free(output_buffer);






    kh_destroy(khIntInt, initial_vars);

    kh_destroy(khInt, deactivated_clausegroups);
    free(buffer_mcreturn);

    //printf("mus size = %d\n", mus_size);
    printf("mus size = %d\n", num_initial_var);



    return 0;
}

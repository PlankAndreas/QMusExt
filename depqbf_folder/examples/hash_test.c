#include <stdint.h>
#include <stdio.h>

#include "/home/andreas/Documents/Programming-Projects/C-Projects/klib-master/khash.h"

// shorthand way to get the key from hashtable or defVal if not found
#define kh_get_val(kname, hash, key, defVal) ({k_iter =kh_get(kname, hash, key);(k_iter !=kh_end(hash)?kh_val(hash,k_iter ):defVal);})

// shorthand way to set value in hash with single line command.  Returns value
// returns 0=replaced existing item, 1=bucket empty (new key), 2-adding element previously deleted
#define kh_set(kname, hash, key, val) ({int ret; k_iter  = kh_put(kname, hash,key,&ret); kh_value(hash,k_iter ) = val; ret;})


struct MyStruct { int key, info, num_lits; int* lits;};

#define \
    mx_eq(a,b) \
    ({ \
        int result; \
        result=1;\
        int i;\
        if(a.num_lits==b.num_lits){\
          qsort(a.lits,a.num_lits, sizeof(int),comp);\
          qsort(b.lits,b.num_lits, sizeof(int),comp);\
          for(i=0;i<a.num_lits;i++)\
          {\
            if(a.lits[i]!=b.lits[i])\
            {\
              result=0;\
              break;\
            }\
          }\
        }else{\
          result=0;\
        }\
        result; \
    })

  #define \
    mx_hf(a) ({ \
      int result=0; \
      int i; \
      for (i = 0; i < a.num_lits; i++) { \
        result = (result << 5) | getUnsignedRightShift(result,27); \
        result += a.lits[i]; \
      }\
      result;\
    })

int comp (const void * elem1, const void * elem2)
{
    int f = *((int*)elem1);
    int s = *((int*)elem2);
    if (f > s) return  1;
    if (f < s) return -1;
    return 0;
}

long getUnsignedRightShift(long value,int s)
  {
      return (long)((ulong)value >> s);
  }

const int khStrInt = 34;
KHASH_MAP_INIT_STR(khStrInt, int) // setup khash to handle string key with int payload

const int khVertex = 35;
KHASH_INIT(khVertex, struct MyStruct, struct MyStruct, 0 , mx_hf, mx_eq) // setup khash to handle string key with int payload



int main(void) {
  int ret, tval;
  khiter_t k_iter;
  khash_t(khStrInt) *h = kh_init(khStrInt);

  k_iter = kh_put(khStrInt, h, "apple", &ret); // add the key
  kh_value(h, k_iter ) = 10; // set the value of the key


  k_iter  = kh_get(khStrInt, h, "apple");  // first have to get ieter
  if (k_iter  == kh_end(h)) {  // k will be equal to kh_end if key not present
    printf("no key found for apple");
  } else {
    printf ("key at apple=%d\n", kh_val(h,k_iter )); // next have to fetch  the actual value
  }



  k_iter  = kh_get(khStrInt, h, "apple"); // get the ieterator
  if (k_iter  != kh_end(h)) {  // if it is found
    printf("deleting key apple\n");
    kh_del(khStrInt, h, k_iter );  // then delete it.
  }

  tval = kh_get_val(khStrInt, h, "apple", -1);
  printf ("after delete tval for apple = %d\n", tval);


  kh_destroy(khStrInt, h);

  int ret2, tval2;
  khiter_t k_iter;
  khash_t(khStrInt) *h = kh_init(khStrInt);

  k_iter = kh_put(khStrInt, h, "apple", &ret); // add the key
  kh_value(h, k_iter ) = 10; // set the value of the key



}

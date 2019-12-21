#include <assert.h>
#include <stdio.h>
#include <limits.h>
#include <stdlib.h>

#include "lib/xalloc.h"
#include "lib/stack.h"
#include "lib/contracts.h"
#include "lib/c0v_stack.h"
#include "lib/c0vm.h"
#include "lib/c0vm_c0ffi.h"
#include "lib/c0vm_abort.h"


/* call stack frames */
typedef struct frame_info frame;
struct frame_info {
  c0v_stack_t S; /* Operand stack of C0 values */
  ubyte *P;      /* Function body */
  size_t pc;     /* Program counter */
  c0_value *V;   /* The local variables */
};

int execute(struct bc0_file *bc0) {
  REQUIRES(bc0 != NULL);

  /* Variables */
  c0v_stack_t S = c0v_stack_new(); /* Operand stack of C0 values */
  ubyte *P = bc0 -> function_pool -> code; /* Array of bytes that make up the current function */
  size_t pc = 0; /* Current location within the current byte array P */
  c0_value *V = xcalloc(bc0 -> function_pool -> num_vars, sizeof(c0_value));   
  /* Local variables (you won't need this till Task 2) */
  (void) V;

  /* The call stack, a generic stack that should contain pointers to frames */
  /* You won't need this until you implement functions. */
  gstack_t callStack = stack_new();
  (void) callStack;


  while (true) {

#ifdef DEBUG
    /* You can add extra debugging information here */
    fprintf(stderr, "Opcode %x -- Stack size: %zu -- PC: %zu\n",
            P[pc], c0v_stack_size(S), pc);
#endif

    switch (P[pc]) {

    /* Additional stack operation: */

    case POP: {
      pc++;
      c0v_pop(S);
      break;
    }

    case DUP: {
      pc++;
      c0_value v = c0v_pop(S);
      c0v_push(S,v);
      c0v_push(S,v);
      break;
    }

    case SWAP: {
      pc++;
      c0_value v2 = c0v_pop(S);
      c0_value v1 = c0v_pop(S);
      c0v_push(S, v2);
      c0v_push(S, v1);
      break;
    }


    /* Returning from a function.
     * This currently has a memory leak! You will need to make a slight
     * change for the initial tasks to avoid leaking memory.  You will
     * need to be revise it further when you write INVOKESTATIC. */

    case RETURN: {
      c0_value retval = c0v_pop(S);
      assert(c0v_stack_empty(S));
      // Free everything before returning from the execute function!
      free(V);
      c0v_stack_free(S);
      if (stack_empty(callStack)) 
      {
        stack_free(callStack, &free);
#ifdef DEBUG
      fprintf(stderr, "Returning %d from execute()\n", val2int(retval));
#endif
        return val2int(retval);
      }
      else {
        frame *F = (frame*)pop(callStack);
        V = F -> V;
        S = F -> S;
        P = F -> P;
        pc = F -> pc;
        free(F);
        c0v_push(S, retval);
      }
      break;
    }

    /* Arithmetic and Logical operations */

    case IADD: {
      pc++;
      int32_t y = val2int(c0v_pop(S));
      int32_t x = val2int(c0v_pop(S));
      c0v_push(S, int2val(x + y));
      break;
    }

    case ISUB: {
      pc++;
      int32_t y = val2int(c0v_pop(S));
      int32_t x = val2int(c0v_pop(S));
      c0v_push(S, int2val(x - y));
      break;
    }

    case IMUL: {
      pc++;
      int32_t y = val2int(c0v_pop(S));
      int32_t x = val2int(c0v_pop(S));
      c0v_push(S, int2val(x * y));
      break;
    }

    case IDIV: {
      pc++;
      int32_t y = val2int(c0v_pop(S));
      int32_t x = val2int(c0v_pop(S));
      if (y == 0) c0_arith_error("division error: y is 0");
      if (x == INT_MIN && y == -1) c0_arith_error("division error");
      c0v_push(S, int2val(x / y));
      break;
    }

    case IREM: {
      pc++;
      int32_t y = val2int(c0v_pop(S));
      int32_t x = val2int(c0v_pop(S));
      if (y == 0) c0_arith_error("modulus error: y is 0");
      if (x == INT_MIN && y == -1) c0_arith_error("modulus error");
      c0v_push(S, int2val(x % y));
      break;
    }

    case IAND: {
      pc++;
      int32_t y = val2int(c0v_pop(S));
      int32_t x = val2int(c0v_pop(S));
      c0v_push(S, int2val(x & y));
      break;
    }

    case IOR: {
      pc++;
      int32_t y = val2int(c0v_pop(S));
      int32_t x = val2int(c0v_pop(S));
      c0v_push(S, int2val(x | y));
      break;
    }

    case IXOR: {
      pc++;
      int32_t y = val2int(c0v_pop(S));
      int32_t x = val2int(c0v_pop(S));
      c0v_push(S, int2val(x ^ y));
      break;
    }

    case ISHL: {
      pc++;
      int32_t y = val2int(c0v_pop(S));
      int32_t x = val2int(c0v_pop(S));
      if (y < 0 || 32 <= y) c0_arith_error("left shift error");
      c0v_push(S, int2val(x << y));
      break;
    }

    case ISHR: {
      pc++;
      int32_t y = val2int(c0v_pop(S));
      int32_t x = val2int(c0v_pop(S));
      if (y < 0 || 32 <= y) c0_arith_error("right shift error");
      c0v_push(S, int2val(x >> y));
      break;
    }

    /* Pushing constants */

    case BIPUSH: {
      pc++;
      int32_t x = (int8_t)P[pc];
      c0v_push(S, int2val(x));
      pc++;
      break;
    }

    case ILDC: {
      pc++;
      uint8_t c1 = P[pc];
      pc++;
      uint8_t c2 = P[pc];
      uint16_t i = (uint16_t)((c1 << 8) | c2);
      if (i > bc0 -> int_count) c0_memory_error("ildc error: index out of bounds");
      int32_t x = (int32_t)(bc0 -> int_pool[i]);
      c0v_push(S, int2val(x));
      pc++;
      break;
    }

    case ALDC: {
      pc++;
      uint8_t c1 = P[pc];
      pc++;
      uint8_t c2 = P[pc];
      uint16_t i = (uint16_t)((c1 << 8) | c2);
      if (i > bc0 -> string_count) c0_memory_error("aldc error: index out of bounds");
      void *x = (void*)(&bc0 -> string_pool[i]);
      c0v_push(S, ptr2val(x));
      pc++;
      break;
    }

    case ACONST_NULL: {
      pc++;
      c0v_push(S, ptr2val((void*)NULL));
      break;
    }


    /* Operations on local variables */

    case VLOAD: {
      pc++;
      uint8_t i = P[pc];
      c0_value v = V[i];
      c0v_push(S, v);
      pc++;
      break;
    }

    case VSTORE: {
      pc++;
      uint8_t i = P[pc];
      V[i] = c0v_pop(S);
      pc++;
      break;
    }

    /* Assertions and errors */

    case ATHROW: {
      pc++;
      char* s = (char*)val2ptr(c0v_pop(S));
      c0_user_error(s);
      break;
    }

    case ASSERT: {
      pc++;
      char* s = (char*)val2ptr(c0v_pop(S));
      int32_t x = val2int(c0v_pop(S));
      if (x == 0) c0_assertion_failure(s);
      break;
    }


    /* Control flow operations */

    case NOP: {
      pc++;
      break;
    }

    case IF_CMPEQ: {
      uint8_t o1 = P[pc + 1];
      uint8_t o2 = P[pc + 2];
      c0_value v2 = c0v_pop(S);
      c0_value v1 = c0v_pop(S);
      int16_t off = o1 << 8 | o2;
      if (val_equal(v1, v2))
      {
        pc = pc + off;
      }
      else pc += 3;
      break;
    }

    case IF_CMPNE: {
      uint8_t o1 = P[pc + 1];
      uint8_t o2 = P[pc + 2];
      c0_value v2 = c0v_pop(S);
      c0_value v1 = c0v_pop(S);
      int16_t off = o1 << 8 | o2;
      if (!val_equal(v1, v2))
      {
        pc = pc + off;
      }
      else pc += 3;
      break;
    }

    case IF_ICMPLT: {
      uint8_t o1 = P[pc + 1];
      uint8_t o2 = P[pc + 2];
      int32_t y = val2int(c0v_pop(S));
      int32_t x = val2int(c0v_pop(S));
      int16_t off = (int16_t)(o1 << 8 | o2);
      if (x < y)
      {
        pc = pc + off;
      }
      else pc += 3;
      break;
    }

    case IF_ICMPGE: {
      uint8_t o1 = P[pc + 1];
      uint8_t o2 = P[pc + 2];
      int32_t y = val2int(c0v_pop(S));
      int32_t x = val2int(c0v_pop(S));
      int16_t off = (int16_t)(o1 << 8 | o2);
      if (x >= y)
      {
        pc = pc + off;
      }
      else pc += 3;
      break;
    }

    case IF_ICMPGT: {
      uint8_t o1 = P[pc + 1];
      uint8_t o2 = P[pc + 2];
      int32_t y = val2int(c0v_pop(S));
      int32_t x = val2int(c0v_pop(S));
      int16_t off = (int16_t)(o1 << 8 | o2);
      if (x > y)
      {
        pc = pc + off;
      }
      else pc += 3;
      break;
    }

    case IF_ICMPLE: {
      uint8_t o1 = P[pc + 1];
      uint8_t o2 = P[pc + 2];
      int32_t y = val2int(c0v_pop(S));
      int32_t x = val2int(c0v_pop(S));
      int16_t off = (int16_t)(o1 << 8 | o2);
      if (x <= y)
      {
        pc = pc + off;
      }
      else pc += 3;
      break;
    }

    case GOTO: {
      uint8_t o1 = P[pc + 1];
      uint8_t o2 = P[pc + 2];
      int16_t off = (int16_t)(o1 << 8 | o2);
      pc = pc + off;
      break;
    }


    /* Function call operations: */

    case INVOKESTATIC: {
      frame *f = xmalloc(sizeof(frame));
      f -> S = S;
      f -> P = P;
      f -> pc = pc + 3;
      f -> V = V;
      push(callStack, (void*)f);

      uint8_t c1 = P[pc + 1];
      uint8_t c2 = P[pc + 2];
      uint16_t i = (uint16_t)((c1 << 8) | c2);
      struct function_info g = bc0 -> function_pool[i];

      V = xcalloc(g.num_vars, sizeof(c0_value));
      for (int j = g.num_args - 1; j >= 0; j--)
      {
        V[j] = c0v_pop(S);
      }
      S = c0v_stack_new();
      P = g.code;
      pc = 0;
      break;
    }

    case INVOKENATIVE: {
      uint8_t c1 = P[pc + 1];
      uint8_t c2 = P[pc + 2];
      uint16_t i = (uint16_t)((c1 << 8) | c2);
      struct native_info nat = bc0 -> native_pool[i];
      
      c0_value *newA = xcalloc(nat.num_args, sizeof(c0_value));
      for (int j = nat.num_args - 1; j >= 0; j--)
      {
        newA[j] = c0v_pop(S);
      }
      native_fn* newAdd = native_function_table[nat.function_table_index];
      c0_value result = (*newAdd)(newA);
      c0v_push(S, result);
      free(newA);
      pc += 3;
      break;
    }


    /* Memory allocation operations: */

    case NEW: {
      pc++;
      uint8_t s = P[pc];
      uint8_t *a = xcalloc(s, sizeof(uint8_t));
      c0v_push(S, ptr2val(a));
      pc++;
      break;
    }

    case NEWARRAY: {
      pc++;
      uint8_t s = P[pc];
      int32_t n = val2int(c0v_pop(S));
      if (n < 0) c0_memory_error("newarray: negative array size");
      c0_array *a = xmalloc(sizeof(c0_array));
      a -> count = n;
      a -> elt_size = s;
      a -> elems = xcalloc(n, s);
      c0v_push(S, ptr2val(a));
      pc++;
      break;
    }

    case ARRAYLENGTH: {
      pc++;
      c0_array *a = (c0_array*)val2ptr(c0v_pop(S));
      if (a == NULL) c0_memory_error("arraylength: a is NULL");
      int32_t n = (int32_t)a -> count;
      c0v_push(S, int2val(n));
      break;
    }


    /* Memory access operations: */

    case AADDF: {
      pc++;
      uint8_t f = P[pc];
      void *a = val2ptr(c0v_pop(S));
      if (a == NULL) c0_memory_error("aaddf: a is NULL");
      c0v_push(S, ptr2val((void*)((char*)a+f)));
      pc++;
      break;
    }

    case AADDS: {
      pc++;
      int32_t i = val2int(c0v_pop(S));
      c0_array *a = (c0_array*)val2ptr(c0v_pop(S));
      if (a == NULL) c0_memory_error("aadds: a is NULL");
      if (i < 0 || a -> count <= i) c0_memory_error("aadds: not valid index");
      int off = a -> elt_size * i;
      c0v_push(S, ptr2val((void*)((char*)(a -> elems) + off)));
      break;
    }

    case IMLOAD: {
      pc++;
      int32_t *a = (int32_t*)(val2ptr(c0v_pop(S)));
      if (a == NULL) c0_memory_error("imload: a is NULL");
      c0v_push(S, int2val(*a));
      break;
    }

    case IMSTORE: {
      pc++;
      int32_t x = val2int(c0v_pop(S));
      int32_t *a = (int32_t*)(val2ptr(c0v_pop(S)));
      if (a == NULL) c0_memory_error("imstore: a is NULL");
      *a = x;
      break;
    }

    case AMLOAD: {
      pc++;
      void **a = val2ptr(c0v_pop(S));
      if (a == NULL) c0_memory_error("amload: a is NULL");
      void* b = *a;
      c0v_push(S, ptr2val(b));
      break;
    }

    case AMSTORE: {
      pc++;
      void *b = val2ptr(c0v_pop(S));
      void **a = val2ptr(c0v_pop(S));
      if (a == NULL) c0_memory_error("amstore: a is NULL");
      *a = b;
      break;
    }

    case CMLOAD: {
      pc++;
      char *a = (char*)val2ptr(c0v_pop(S));
      if (a == NULL) c0_memory_error("cmload: a is NULL");
      int32_t x = (int32_t)(*a);
      c0v_push(S, int2val(x));
      break;
    }

    case CMSTORE: {
      pc++;
      int32_t x = val2int(c0v_pop(S));
      char* a = (char*)val2ptr(c0v_pop(S));
      if (a == NULL) c0_memory_error("cmstore: a is NULL");
      *a = x & 0x7f;
      break;
    }

    default:
      fprintf(stderr, "invalid opcode: 0x%02x\n", P[pc]);
      abort();
    }
  }

  /* cannot get here from infinite loop */
  assert(false);
}

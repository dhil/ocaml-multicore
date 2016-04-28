#include <stdlib.h>

#include "mlvalues.h"
#include "memory.h"
#include "fail.h"
#include "shared_heap.h"
#include "memory.h"
#include "roots.h"
#include "globroots.h"
#include "domain.h"
#include "fiber.h"
#include "addrmap.h"

#define MARK_STACK_SIZE (1 << 20)

typedef enum { Phase_idle, Phase_marking } gc_phase_t;

/* Phase of the current domain's GC. Phases are not necessarily
   synchronised between domains. */
static __thread gc_phase_t gc_phase = Phase_idle;

__thread value* caml_mark_stack;
__thread int caml_mark_stack_count;

__thread uintnat caml_allocated_words;

static __thread uintnat stat_blocks_marked = 0;

uintnat caml_percent_free = Percent_free_def;

void caml_init_major_gc() {
  caml_mark_stack = caml_stat_alloc(MARK_STACK_SIZE * sizeof(value));
  caml_mark_stack_count = 0;
}

static uintnat default_slice_budget() {
  /*
     Free memory at the start of the GC cycle (garbage + free list) (assumed):
                 FM = caml_stat_heap_size * caml_percent_free
                      / (100 + caml_percent_free)

     Assuming steady state and enforcing a constant allocation rate, then
     FM is divided in 2/3 for garbage and 1/3 for free list.
                 G = 2 * FM / 3
     G is also the amount of memory that will be used during this cycle
     (still assuming steady state).

     Proportion of G consumed since the previous slice:
                 PH = caml_allocated_words / G
                    = caml_allocated_words * 3 * (100 + caml_percent_free)
                      / (2 * caml_stat_heap_size * caml_percent_free)
     Proportion of extra-heap resources consumed since the previous slice:
                 PE = caml_extra_heap_resources
     Proportion of total work to do in this slice:
                 P  = max (PH, PE)
     Amount of marking work for the GC cycle:
                 MW = caml_stat_heap_size * 100 / (100 + caml_percent_free)
     Amount of sweeping work for the GC cycle:
                 SW = caml_stat_heap_size

     Total amount of work for the GC cycle:
                 TW = MW + SW

     Amount of work to do for this slice:
                 W = P * TW
  */
  uintnat heap_size = caml_heap_size(caml_domain_self()->shared_heap);
  double heap_words = (double)Wsize_bsize(heap_size);
  double p = (double) caml_allocated_words * 3.0 * (100 + caml_percent_free)
      / heap_words / caml_percent_free / 2.0;

  double total_work =
    heap_words * 100 / (100 + caml_percent_free) /* marking */
    + heap_words; /* sweeping */

  return (intnat)(p * total_work);
  //return 1ll << 50;
}

static void mark_stack_prune();

static void mark_stack_push(value v) {
  Assert(Is_block(v));
  if (caml_mark_stack_count >= MARK_STACK_SIZE)
    mark_stack_prune();
  caml_mark_stack[caml_mark_stack_count++] = v;
}

static int mark_stack_pop(value* ret) {
  if (caml_mark_stack_count == 0) 
    return 0;
  *ret = caml_mark_stack[--caml_mark_stack_count];
  return 1;
}

#define Is_markable(v) (Is_block(v) && !Is_minor(v))

static value mark_normalise(value v) {
  Assert(Is_markable(v));
  if (Tag_val(v) == Forward_tag) {
    /* FIXME: short-circuiting lazy values is a useful optimisation */
  } else if (Tag_val(v) == Infix_tag) {
    v -= Infix_offset_val(v);
  }
  return v;
}

static intnat mark(value initial, intnat budget) {
  value next = initial;
  int found_next = 1;
  while (budget > 0 && found_next) {
    value v = next;
    header_t hd_v;
    found_next = 0;

    Assert(Is_markable(v));
    Assert(v == mark_normalise(v));

    stat_blocks_marked++;
    /* mark the current object */
    hd_v = Hd_val(v);
    if (Tag_hd (hd_v) == Stack_tag) {
      caml_scan_stack(&caml_darken, v);
    } else if (Tag_hd (hd_v) < No_scan_tag) {
      int i;
      for (i = 0; i < Wosize_hd(hd_v); i++) {
        value child = Field(v, i);
        if (Is_markable(child)) {
          child = mark_normalise(child);
          if (caml_mark_object(child)) {
            if (!found_next) {
              next = child;
              found_next = 1;
            } else {
              mark_stack_push(child);
            }
          }
        }
      }
    }
    budget -= Whsize_hd(hd_v);
    
    /* if we haven't found any markable children, pop an object to mark */
    if (!found_next) {
      found_next = mark_stack_pop(&next);
    }
  }
  if (found_next) {
    mark_stack_push(next);
  }
  return budget;
}

void caml_darken(value v, value* ignored) {
  /* Assert (Is_markable(v)); */
  if (!Is_markable (v)) return; /* foreign stack, at least */

  v = mark_normalise(v);
  if (caml_mark_object(v)) mark_stack_push(v);
}

intnat caml_major_collection_slice(intnat howmuch)
{
  intnat computed_work = howmuch ? howmuch : default_slice_budget();
  intnat budget = computed_work;
  intnat sweep_work, mark_work;
  uintnat blocks_marked_before = stat_blocks_marked;
  value v;

  caml_save_stack_gc();

  sweep_work = budget;
  budget = caml_sweep(caml_domain_self()->shared_heap, budget);
  sweep_work -= budget;

  if (gc_phase == Phase_idle) {
    caml_do_local_roots(&caml_darken, caml_domain_self());
    caml_scan_global_roots(&caml_darken);
    gc_phase = Phase_marking;
  }

  mark_work = budget;
  if (mark_stack_pop(&v))
    budget = mark(v, budget);
  mark_work -= budget;

  caml_gc_log("Major slice: %lu alloc, %ld work, %ld sweep, %ld mark (%lu blocks)",
              (unsigned long)caml_allocated_words,
              (long)computed_work, (long)sweep_work, (long)mark_work,
              (unsigned long)(stat_blocks_marked - blocks_marked_before));
  caml_allocated_words = 0;
  caml_restore_stack_gc();

  if (budget > 0) {
    caml_trigger_stw_gc();
    caml_handle_gc_interrupt();
  }


  return computed_work;
}

void caml_finish_marking () {
  caml_save_stack_gc();
  caml_do_local_roots(&caml_darken, caml_domain_self());
  caml_scan_global_roots(&caml_darken);
  caml_empty_mark_stack();
  caml_allocated_words = 0;
  caml_restore_stack_gc();
}

void caml_empty_mark_stack () {
  value v;

  while (mark_stack_pop(&v)) mark(v, 10000000);

  if (stat_blocks_marked) 
    caml_gc_log("Finished marking major heap. Marked %u blocks", (unsigned)stat_blocks_marked);
  stat_blocks_marked = 0;
}



struct pool_count {
  struct pool* pool;
  int occurs;
};

static int pool_count_cmp(const void* a, const void* b)
{
  const struct pool_count* p = a;
  const struct pool_count* q = b;
  return p->occurs - q->occurs;
}

#define Prune_table_max 1000
static void mark_stack_prune ()
{
  struct addrmap t = ADDRMAP_INIT;
  int count = 0, entry;
  addrmap_iterator i;
  for (entry = 0; entry < caml_mark_stack_count; entry++) {
    struct pool* pool = caml_pool_of_shared_block(caml_mark_stack[entry]);
    if (!pool) continue;
    value p = (value)pool;
    if (caml_addrmap_contains(&t, p)) {
      (*caml_addrmap_insert_pos(&t, p)) ++;
    } else if (count < Prune_table_max) {
      *caml_addrmap_insert_pos(&t, p) = 1;
      count++;
    } else {
      /* decrease all entries by 1 */
      struct addrmap s = ADDRMAP_INIT;
      int scount = 0;
      for (i = caml_addrmap_iterator(&t);
           caml_addrmap_iter_ok(&t, i);
           i = caml_addrmap_next(&t, i)) {
        value k = caml_addrmap_iter_key(&t, i);
        value v = caml_addrmap_iter_value(&t, i);
        if (v > 1) {
          *caml_addrmap_insert_pos(&s, k) = v - 1;
          scount++;
        }
      }
      caml_addrmap_clear(&t);
      t = s;
      count = scount;
    }
  }

  struct pool_count* pools = caml_stat_alloc(count * sizeof(struct pool_count));
  int pos = 0;
  for (i = caml_addrmap_iterator(&t);
       caml_addrmap_iter_ok(&t, i);
       i = caml_addrmap_next(&t, i)) {
    struct pool_count* p = &pools[pos++];
    p->pool = (struct pool*)caml_addrmap_iter_key(&t, i);
    p->occurs = (int)caml_addrmap_iter_value(&t, i);
  }
  Assert(pos == count);
  caml_addrmap_clear(&t);


  qsort(pools, count, sizeof(struct pool_count), &pool_count_cmp);

  int start = count, total = 0;
  int desired_total = caml_mark_stack_count / 10;
  while (start > 0 && total < desired_total) {
    start--;
    total += pools[start].occurs;
  }

  caml_gc_log("Mark stack overflow. Removing %d pools containing %.1f%% of stack.",
              count-start, 100. * (double)total / (double)caml_mark_stack_count);


  for (; start < count; start++) {
    *caml_addrmap_insert_pos(&t, (value)pools[start].pool) = 1;
  }
  int out = 0;
  for (entry = 0; entry < caml_mark_stack_count; entry++) {
    value v = caml_mark_stack[entry];
    if (caml_addrmap_lookup(&t, v)) {
      caml_mark_stack[out++] = v;
    }
  }
  caml_mark_stack_count = out;


  

  caml_fatal_error("nope");
}

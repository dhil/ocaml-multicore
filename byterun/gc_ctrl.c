/***********************************************************************/
/*                                                                     */
/*                                OCaml                                */
/*                                                                     */
/*             Damien Doligez, projet Para, INRIA Rocquencourt         */
/*                                                                     */
/*  Copyright 1996 Institut National de Recherche en Informatique et   */
/*  en Automatique.  All rights reserved.  This file is distributed    */
/*  under the terms of the GNU Library General Public License, with    */
/*  the special exception on linking described in file ../LICENSE.     */
/*                                                                     */
/***********************************************************************/

#include "caml/alloc.h"
#include "caml/custom.h"
#include "caml/finalise.h"
#include "caml/gc.h"
#include "caml/gc_ctrl.h"
#include "caml/major_gc.h"
#include "caml/minor_gc.h"
#include "caml/shared_heap.h"
#include "caml/misc.h"
#include "caml/mlvalues.h"
#ifdef NATIVE_CODE
#include "stack.h"
#include "frame_descriptors.h"
#else
#include "caml/fiber.h"
#endif
#include "caml/domain.h"
#include "caml/globroots.h"
#include "caml/signals.h"
#include "caml/startup.h"

uintnat caml_max_stack_size;
uintnat caml_fiber_wsz;

double caml_stat_minor_words = 0.0,
       caml_stat_promoted_words = 0.0,
       caml_stat_major_words = 0.0;

intnat caml_stat_minor_collections = 0,
       caml_stat_major_collections = 0,
       caml_stat_heap_size = 0,              /* bytes */
       caml_stat_top_heap_size = 0,          /* bytes */
       caml_stat_compactions = 0,
       caml_stat_heap_chunks = 0;

extern uintnat caml_major_heap_increment; /* percent or words; see major_gc.c */
extern uintnat caml_percent_free;         /*        see major_gc.c */
extern uintnat caml_percent_max;          /*        see compact.c */
extern uintnat caml_allocation_policy;    /*        see freelist.c */

#define Next(hp) ((hp) + Bhsize_hp (hp))

/* Check the heap structure (if compiled in debug mode) and
   gather statistics; return the stats if [returnstats] is true,
   otherwise return [Val_unit].
*/
#if 0
static value heap_stats (int returnstats)
{
  CAMLparam0 ();
  intnat live_words = 0, live_blocks = 0,
         free_words = 0, free_blocks = 0, largest_free = 0,
         fragments = 0, heap_chunks = 0;
  char *chunk = caml_heap_start, *chunk_end;
  char *cur_hp;
#ifdef DEBUG
  char *prev_hp;
#endif
  header_t cur_hd;

#ifdef DEBUG
  caml_gc_message (-1, "### OCaml runtime: heap check ###\n", 0);
#endif

  while (chunk != NULL){
    ++ heap_chunks;
    chunk_end = chunk + Chunk_size (chunk);
#ifdef DEBUG
    prev_hp = NULL;
#endif
    cur_hp = chunk;
    while (cur_hp < chunk_end){
      cur_hd = Hd_hp (cur_hp);
                                           Assert (Next (cur_hp) <= chunk_end);
      switch (Color_hd (cur_hd)){
      case Caml_white:
        if (Wosize_hd (cur_hd) == 0){
          ++ fragments;
          Assert (prev_hp == NULL
                  || Color_hp (prev_hp) != Caml_blue
                  || cur_hp == caml_gc_sweep_hp);
        }else{
          if (caml_gc_phase == Phase_sweep && cur_hp >= caml_gc_sweep_hp){
            ++ free_blocks;
            free_words += Whsize_hd (cur_hd);
            if (Whsize_hd (cur_hd) > largest_free){
              largest_free = Whsize_hd (cur_hd);
            }
          }else{
            ++ live_blocks;
            live_words += Whsize_hd (cur_hd);
#ifdef DEBUG
            check_block (cur_hp);
#endif
          }
        }
        break;
      case Caml_gray: case Caml_black:
        Assert (Wosize_hd (cur_hd) > 0);
        ++ live_blocks;
        live_words += Whsize_hd (cur_hd);
#ifdef DEBUG
        check_block (cur_hp);
#endif
        break;
      case Caml_blue:
        Assert (Wosize_hd (cur_hd) > 0);
        ++ free_blocks;
        free_words += Whsize_hd (cur_hd);
        if (Whsize_hd (cur_hd) > largest_free){
          largest_free = Whsize_hd (cur_hd);
        }
        /* not true any more with big heap chunks
        Assert (prev_hp == NULL
                || (Color_hp (prev_hp) != Caml_blue && Wosize_hp (prev_hp) > 0)
                || cur_hp == caml_gc_sweep_hp);
        Assert (Next (cur_hp) == chunk_end
                || (Color_hp (Next (cur_hp)) != Caml_blue
                    && Wosize_hp (Next (cur_hp)) > 0)
                || (Whsize_hd (cur_hd) + Wosize_hp (Next (cur_hp)) > Max_wosize)
                || Next (cur_hp) == caml_gc_sweep_hp);
        */
        break;
      }
#ifdef DEBUG
      prev_hp = cur_hp;
#endif
      cur_hp = Next (cur_hp);
    }                                          Assert (cur_hp == chunk_end);
    chunk = Chunk_next (chunk);
  }

  Assert (heap_chunks == caml_stat_heap_chunks);
  Assert (live_words + free_words + fragments
          == Wsize_bsize (caml_stat_heap_size));

  if (returnstats){
    CAMLlocal1 (res);

    /* get a copy of these before allocating anything... */
    double minwords = caml_stat_minor_words
                      + (double) Wsize_bsize (caml_young_end - caml_young_ptr);
    double prowords = caml_stat_promoted_words;
    double majwords = caml_stat_major_words + (double) caml_allocated_words;
    intnat mincoll = caml_stat_minor_collections;
    intnat majcoll = caml_stat_major_collections;
    intnat heap_words = Wsize_bsize (caml_stat_heap_size);
    intnat cpct = caml_stat_compactions;
    intnat top_heap_words = Wsize_bsize (caml_stat_top_heap_size);

    res = caml_alloc_tuple (16);
    Store_field (res, 0, caml_copy_double (minwords));
    Store_field (res, 1, caml_copy_double (prowords));
    Store_field (res, 2, caml_copy_double (majwords));
    Store_field (res, 3, Val_long (mincoll));
    Store_field (res, 4, Val_long (majcoll));
    Store_field (res, 5, Val_long (heap_words));
    Store_field (res, 6, Val_long (heap_chunks));
    Store_field (res, 7, Val_long (live_words));
    Store_field (res, 8, Val_long (live_blocks));
    Store_field (res, 9, Val_long (free_words));
    Store_field (res, 10, Val_long (free_blocks));
    Store_field (res, 11, Val_long (largest_free));
    Store_field (res, 12, Val_long (fragments));
    Store_field (res, 13, Val_long (cpct));
    Store_field (res, 14, Val_long (top_heap_words));
    Store_field (res, 15, Val_long (caml_stack_usage()));
    CAMLreturn (res);
  }else{
    CAMLreturn (Val_unit);
  }
}
#endif

#ifdef DEBUG
void caml_heap_check (void)
{
  /* !! heap_stats (0); */
}
#endif

CAMLprim value caml_gc_stat(value v)
{
  Assert (v == Val_unit);
  return /* !! heap_stats (1); */ Val_unit;
}

CAMLprim value caml_gc_quick_stat(value v)
{
  return Val_unit;
#if 0
  CAMLparam0 ();
  CAMLlocal1 (res);

  /* get a copy of these before allocating anything... */
  double minwords = caml_stat_minor_words
                    + (double) Wsize_bsize (caml_young_end - caml_young_ptr);
  double prowords = caml_stat_promoted_words;
  double majwords = caml_stat_major_words + (double) caml_allocated_words;
  intnat mincoll = caml_stat_minor_collections;
  intnat majcoll = caml_stat_major_collections;
  intnat heap_words = caml_stat_heap_size / sizeof (value);
  intnat top_heap_words = caml_stat_top_heap_size / sizeof (value);
  intnat cpct = caml_stat_compactions;
  intnat heap_chunks = caml_stat_heap_chunks;

  res = caml_alloc_tuple (16);
  Store_field (res, 0, caml_copy_double (minwords));
  Store_field (res, 1, caml_copy_double (prowords));
  Store_field (res, 2, caml_copy_double (majwords));
  Store_field (res, 3, Val_long (mincoll));
  Store_field (res, 4, Val_long (majcoll));
  Store_field (res, 5, Val_long (heap_words));
  Store_field (res, 6, Val_long (heap_chunks));
  Store_field (res, 7, Val_long (0));
  Store_field (res, 8, Val_long (0));
  Store_field (res, 9, Val_long (0));
  Store_field (res, 10, Val_long (0));
  Store_field (res, 11, Val_long (0));
  Store_field (res, 12, Val_long (0));
  Store_field (res, 13, Val_long (cpct));
  Store_field (res, 14, Val_long (top_heap_words));
  Store_field (res, 15, Val_long (caml_stack_usage()));
  CAMLreturn (res);
#endif
}

CAMLprim value caml_gc_counters(value v)
{
  return Val_unit;
#if 0
  CAMLparam0 ();   /* v is ignored */
  CAMLlocal1 (res);

  /* get a copy of these before allocating anything... */
  double minwords = caml_stat_minor_words
                    + (double) Wsize_bsize (caml_young_end - caml_young_ptr);
  double prowords = caml_stat_promoted_words;
  double majwords = caml_stat_major_words + (double) caml_allocated_words;

  res = caml_alloc_tuple (3);
  Store_field (res, 0, caml_copy_double (minwords));
  Store_field (res, 1, caml_copy_double (prowords));
  Store_field (res, 2, caml_copy_double (majwords));
  CAMLreturn (res);
#endif
}

CAMLprim value caml_gc_get(value v)
{
  CAMLparam0 ();   /* v is ignored */
  CAMLlocal1 (res);

  res = caml_alloc_tuple (7);
#ifndef NATIVE_CODE
  Store_field (res, 5, Val_long (caml_max_stack_size));                 /* l */
#else
  Store_field (res, 5, Val_long (0));
#endif

  CAMLreturn (res);

#if 0
  CAMLparam0 ();   /* v is ignored */
  CAMLlocal1 (res);

  res = caml_alloc_tuple (7);
  Store_field (res, 0, Val_long (Wsize_bsize (caml_minor_heap_size)));  /* s */
  Store_field (res, 1, Val_long (caml_major_heap_increment));           /* i */
  Store_field (res, 2, Val_long (caml_percent_free));                   /* o */
  Store_field (res, 3, Val_long (caml_startup_params.verb_gc));         /* v */
  Store_field (res, 4, Val_long (caml_percent_max));                    /* O */
#ifndef NATIVE_CODE
  Store_field (res, 5, Val_long (caml_max_stack_size));                 /* l */
#else
  Store_field (res, 5, Val_long (0));
#endif
  Store_field (res, 6, Val_long (caml_allocation_policy));              /* a */
  CAMLreturn (res);
#endif
}

#define Max(x,y) ((x) < (y) ? (y) : (x))

static uintnat norm_pfree (uintnat p)
{
  return Max (p, 1);
}

static uintnat norm_pmax (uintnat p)
{
  return p;
}

CAMLprim value caml_gc_set(value v)
{
  return Val_unit;
#if 0
  uintnat newpf, newpm;
  asize_t newheapincr;
  asize_t newminsize;
  uintnat oldpolicy;

  caml_startup_params.verb_gc = Long_field (v, 3);

#ifndef NATIVE_CODE
  caml_change_max_stack_size (Long_field (v, 5));
#endif

  newpf = norm_pfree (Long_field (v, 2));
  if (newpf != caml_percent_free){
    caml_percent_free = newpf;
    caml_gc_message (0x20, "New space overhead: %d%%\n", caml_percent_free);
  }

  newpm = norm_pmax (Long_field (v, 4));
  if (newpm != caml_percent_max){
    caml_percent_max = newpm;
    caml_gc_message (0x20, "New max overhead: %d%%\n", caml_percent_max);
  }

  newheapincr = Long_field (v, 1);
  if (newheapincr != caml_major_heap_increment){
    caml_major_heap_increment = newheapincr;
    if (newheapincr > 1000){
      caml_gc_message (0x20, "New heap increment size: %luk words\n",
                       caml_major_heap_increment/1024);
    }else{
      caml_gc_message (0x20, "New heap increment size: %lu%%\n",
                       caml_major_heap_increment);
    }
  }
  oldpolicy = caml_allocation_policy;
  caml_set_allocation_policy (Long_field (v, 6));
  if (oldpolicy != caml_allocation_policy){
    caml_gc_message (0x20, "New allocation policy: %d\n",
                     caml_allocation_policy);
  }

    /* Minor heap size comes last because it will trigger a minor collection
       (thus invalidating [v]) and it can raise [Out_of_memory]. */
  newminsize = caml_norm_minor_heap_size (Long_field (v, 0));
  if (newminsize != caml_minor_heap_size){
    caml_gc_message (0x20, "New minor heap size: %luk bytes\n",
                     newminsize/1024);
    caml_set_minor_heap_size (newminsize);
  }
  return Val_unit;
#endif
}

CAMLprim value caml_gc_minor(value v)
{                                                    Assert (v == Val_unit);
  caml_minor_collection ();
  return Val_unit;
}

CAMLprim value caml_gc_major(value v)
{                                                    Assert (v == Val_unit);
  caml_gc_log ("Major GC cycle requested");
  caml_empty_minor_heap ();
  caml_trigger_stw_gc ();
  caml_handle_gc_interrupt ();
  /* !! caml_final_do_calls (); */
  return Val_unit;
}

CAMLprim value caml_gc_full_major(value v)
{
  return caml_gc_major(v);
}

CAMLprim value caml_gc_major_slice (value v)
{
  Assert (Is_long (v));
  caml_empty_minor_heap ();
  return Val_long (caml_major_collection_slice (Long_val (v)));
}

CAMLprim value caml_gc_compaction(value v)
{
  return caml_gc_major(v);
}

uintnat caml_normalize_heap_increment (uintnat i)
{
  if (i < Bsize_wsize (Heap_chunk_min)){
    i = Bsize_wsize (Heap_chunk_min);
  }
  return ((i + Page_size - 1) >> Page_log) << Page_log;
}

void caml_init_gc ()
{
/*  uintnat major_heap_size =
      Bsize_wsize (caml_normalize_heap_increment (caml_startup_params.heap_size_init)); */

  caml_max_stack_size = caml_startup_params.max_stack_init;
  caml_fiber_wsz = caml_startup_params.fiber_wsz_init;
  caml_percent_free = norm_pfree (caml_startup_params.percent_free_init);
  caml_gc_log ("Initial stack limit: %luk bytes",
               caml_max_stack_size / 1024 * sizeof (value));

  caml_init_domains(caml_startup_params.minor_heap_init);
  #ifdef NATIVE_CODE
  caml_init_frame_descriptors();
  #endif
/*
  caml_major_heap_increment = major_incr;
  caml_percent_free = norm_pfree (percent_fr);
  caml_percent_max = norm_pmax (percent_m);
  caml_init_major_heap (major_heap_size);
  caml_gc_message (0x20, "Initial minor heap size: %luk bytes\n",
                   caml_minor_heap_size / 1024);
  caml_gc_message (0x20, "Initial major heap size: %luk bytes\n",
                   major_heap_size / 1024);
  caml_gc_message (0x20, "Initial space overhead: %lu%%\n", caml_percent_free);
  caml_gc_message (0x20, "Initial max overhead: %lu%%\n", caml_percent_max);
  if (caml_major_heap_increment > 1000){
    caml_gc_message (0x20, "Initial heap increment: %luk words\n",
                     caml_major_heap_increment / 1024);
  }else{
    caml_gc_message (0x20, "Initial heap increment: %lu%%\n",
                     caml_major_heap_increment);
  }
  caml_gc_message (0x20, "Initial allocation policy: %d\n",
                   caml_allocation_policy);
*/
}

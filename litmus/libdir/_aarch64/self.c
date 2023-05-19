/****************************************************************************/
/*                           the diy toolsuite                              */
/*                                                                          */
/* Jade Alglave, University College London, UK.                             */
/* Luc Maranget, INRIA Paris-Rocquencourt, France.                          */
/*                                                                          */
/* Copyright 2019-present Institut National de Recherche en Informatique et */
/* en Automatique and the authors. All rights reserved.                     */
/*                                                                          */
/* This software is governed by the CeCILL-B license under French law and   */
/* abiding by the rules of distribution of free software. You can use,      */
/* modify and/ or redistribute the software under the terms of the CeCILL-B */
/* license as circulated by CEA, CNRS and INRIA at the following URL        */
/* "http://www.cecill.info". We also give a copy in LICENSE.txt.            */
/****************************************************************************/

/***********************************/
/* Support for self-modifying code */
/***********************************/

static uint32_t getcachelinesize(void) {
  uint64_t csz;
  asm __volatile__ (
                    "mrs %[r],CTR_EL0"
                    :[r] "=&r" (csz)
                    :
                    :"cc","memory"
                    );
  uint64_t sz1 = csz & 0xf;
  uint64_t sz2 = (csz >> 16 ) & 0xf;
  uint32_t x = (uint32_t) (sz1 >= sz2 ? sz1 : sz2);
  return (1 << x) * 4 ;
}

static uint32_t cache_line_size;

inline static void selfbar(void *p) {
  asm __volatile__
    ("dc cvau,%[p]\n\t" "dsb ish\n\t" "ic ivau,%[p]\n\t" "dsb ish\n\t" "isb"
     ::[p]"r"(p): "memory");
}

inline static void isync(void) {
  asm __volatile__ ("isb" ::: "memory");
}

#ifdef KVM

static void litmus_icache_sync(unsigned long vaddr, unsigned long vaddr_end)
{
  while (vaddr < vaddr_end) {
    selfbar((void *)vaddr);
    vaddr += cache_line_size;
  }
}

static size_t code_size(ins_t *p,int skip) {
  return (find_ins(getret(), p, skip) + 1) * sizeof(ins_t);
}

static void litmus_pte_unset_el0(unsigned long vaddr, unsigned long vaddr_end)
{
  while (vaddr < vaddr_end) {
    pteval_t *pte = litmus_tr_pte((void *)vaddr);
    litmus_set_pte_safe((void *)vaddr, pte, *pte & ~msk_el0);
    vaddr += LITMUS_PAGE_SIZE;
  }
  asm __volatile__ (
    "dsb ish\n\t"
    "isb"
    ::: "memory"
  );
}

static void code_init(void *code, void *src, size_t sz)
{
  size_t sz_pages = (sz - 1) / LITMUS_PAGE_SIZE + 1;
  memcpy(code, src, sz);
  litmus_icache_sync((unsigned long)code, (unsigned long)code + sz);
  /* Armv8 requires that code shared between EL1 and EL0 is read-only.
   * We need write access and therefore, we have to ensure that the
   * the memory we use for code won't be accessible from EL0 */
  litmus_pte_unset_el0((unsigned long)code, (unsigned long)code + sz_pages);
}

#endif

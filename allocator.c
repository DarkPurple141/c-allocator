//
//  COMP1927 Assignment 1 - Vlad: the memory allocator
//  allocator.c ... implementation
//  z3420752, Alexander Hinds
// 
//  Originally created by Liam O'Connor on 18/07/12.
//  Modified by John Shepherd in August 2014, August 2015
//  Copyright (c) 2012-2015 UNSW. All rights reserved.
//

#include "allocator.h"
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#define FREE_HEADER_SIZE  sizeof(struct free_list_header)  
#define ALLOC_HEADER_SIZE sizeof(struct alloc_block_header)  
#define MAGIC_FREE     0xDEADBEEF
#define MAGIC_ALLOC    0xBEEFDEAD
#define MIN_REQUEST    8

#define BEST_FIT       1
#define WORST_FIT      2
#define RANDOM_FIT     3
#define TRUE 1
#define FALSE 0

typedef unsigned char byte;
typedef u_int32_t vsize_t;
typedef u_int32_t vlink_t;
typedef u_int32_t vaddr_t;

typedef struct free_list_header {
   u_int32_t magic;  // ought to contain MAGIC_FREE
   vsize_t size;     // # bytes in this block (including header)
   vlink_t next;     // memory[] index of next free block
   vlink_t prev;     // memory[] index of previous free block
} free_header_t;

typedef struct alloc_block_header {
   u_int32_t magic;  // ought to contain MAGIC_ALLOC
   vsize_t size;     // # bytes in this block (including header)
} alloc_header_t;

// Global data

static byte *memory = NULL;   // pointer to start of allocator memory
static vaddr_t free_list_ptr; // index in memory[] of first block in free list
static vsize_t memory_size;   // number of bytes malloc'd in memory[]
static u_int32_t strategy;    // allocation strategy (by default BEST_FIT)

// Private functions

static void vlad_merge();
static vsize_t determine_index (void * p);
static u_int32_t determine_size (u_int32_t n);
static void change_free_header (free_header_t *head,vsize_t size, 
      vlink_t next, vlink_t prev);
static void check_corruption(free_header_t * f);
static void change_alloc_header(alloc_header_t * head, vsize_t size);
static void change_flist_pointer(free_header_t * p);

// Input: size - number of bytes to make available to the allocator
// Output: none              
// Precondition: Size >= 1024
// Postcondition: `size` bytes are now available to the allocator
// 
// (If the allocator is already initialised, this function does nothing,
//  even if it was initialised with different size)

void vlad_init(u_int32_t size)
{
   if (memory != NULL) {
      return;
   }

   u_int32_t newsize;
   if (size < 1024) size = 1024;
   
   // initial setup
   for (newsize=1;newsize<size;newsize*=2);
   free_list_ptr = (vaddr_t)0;
   memory_size = newsize;
   strategy = BEST_FIT;

   memory = (byte*)malloc(newsize);
   if (memory == NULL) {
      fprintf(stderr, "vlad_init: Insufficient memory\n");
      exit(EXIT_FAILURE);
   }
   free_header_t *header = (free_header_t*)memory;
   change_free_header(header,newsize,0,0);
   
}

// Input: n - number of bytes requested
// Output: p - a pointer, or NULL
// Precondition: n < size of largest available free block
// Postcondition: If a region of size n or greater cannot be found, p = NULL 
//                Else, p points to a location immediately after a header block
//                      for a newly-allocated region of some size >= 
//                      n + header size.

void *vlad_malloc(u_int32_t n) {
   
   byte *bestPtr = &memory[free_list_ptr];
   free_header_t * freemem = (free_header_t*)bestPtr;
   u_int32_t bestFit;
   u_int32_t counter = 1;
   // setup
   if (n < MIN_REQUEST) n = MIN_REQUEST;
   u_int32_t actual_size = determine_size(n);
   u_int32_t threshold = actual_size + 2*FREE_HEADER_SIZE;

   if (actual_size < memory_size) {   
      // search through free headers and find a block which is both
      // big enough and a good fit --- first case is a setup.

         if (freemem->size >= actual_size) {
            bestFit = freemem->size;
            bestPtr = (byte*)freemem;
         } else {
            bestFit = memory_size;
            bestPtr = NULL;
         }
         freemem=(free_header_t*)&memory[freemem->next];
         check_corruption(freemem);

      while (freemem != (free_header_t*)&memory[free_list_ptr]) {

         if (freemem->size >= actual_size) {
            if (freemem->size < bestFit) {
               bestFit=freemem->size;
               bestPtr=(byte*)freemem;
            }
         }
         counter++;
         freemem=(free_header_t*)&memory[freemem->next];
         check_corruption(freemem);
      }

      freemem = (free_header_t*)bestPtr;

      // if loop completes without re-assigning bestptr there is insufficient
      // memory in the system
      if (bestPtr==NULL) {
         //
         return NULL;
      } else if (freemem->size >= threshold) {
         // need to split memory.
         //re-assign free header, create alloc header
         vsize_t diff = freemem->size - actual_size;
         free_header_t * temp = freemem;
         freemem = (free_header_t*)((byte *)freemem + actual_size);
         vaddr_t ref = 0;

         while ((byte*)freemem!=&memory[ref]) {
            ref++;
         }
         
         if (counter == 1) {
            change_free_header(freemem,diff,ref,ref);
            check_corruption(freemem);
            free_list_ptr = ref;

         } else {

            ((free_header_t*)&memory[temp->next])->prev=ref;
            ((free_header_t*)&memory[temp->prev])->next=ref;

            change_free_header(freemem,diff,temp->next,temp->prev);
            check_corruption(freemem);
            change_flist_pointer(freemem);
         }
         // create new alloc
         change_alloc_header((alloc_header_t*)bestPtr,actual_size);
         
      } else {
         // no splt needed 
         // re-assign free header, create alloc header
         if (counter == 1 && FREE_HEADER_SIZE+actual_size > freemem->size) {
            // single free header and no space to re-assign header
            return NULL;
         } else if (counter > 1) {

            // more than 1 free header
            ((free_header_t*)&memory[freemem->next])->prev=freemem->prev;
            ((free_header_t*)&memory[freemem->prev])->next=freemem->next;

            // change flist_pointer if needed
            change_flist_pointer((free_header_t*)&memory[freemem->next]);
            //create alloc
            if (freemem->size > actual_size) actual_size = freemem->size;
            change_alloc_header((alloc_header_t*)freemem,actual_size);   
         } else {

            return NULL;
            
         }

      }

   } else {
      // request bigger than has been vlad_init'd.
      return NULL;
   }

   return ((void*)(bestPtr + ALLOC_HEADER_SIZE));
}

void vlad_free(void *object) {
   
   vsize_t i=0; vsize_t j=0;
   char a= FALSE;
   free_header_t * temp; free_header_t * new_free;
   alloc_header_t * test;
   vlink_t next; vlink_t prev;

   while (i < memory_size) {
      if (object == &memory[i]) {
         a = TRUE;
         break;
      }
      i++;
   }

   i = i-ALLOC_HEADER_SIZE;
   test = (alloc_header_t *)&memory[i];
   determine_index(test);

   // if a is false, then *object is not in memory, 
   // else check 8 bytes before object for magic_alloc
   if (a == FALSE) {
      fprintf(stderr, "vlad_free: Attempt to free via invalid pointer\n");
      exit(EXIT_FAILURE);
   } else if (test->magic != MAGIC_ALLOC) {
      fprintf(stderr, "vlad_free: Attempt to free non-allocated memory\n");
      exit(EXIT_FAILURE);
   }

   // setup variables 
   prev = next = j = i;
   temp = (free_header_t*)&memory[free_list_ptr];
   new_free = (free_header_t*)&memory[i];

   if (j < free_list_ptr) {

      // j becomes free_list_ptr, special case where j is new first
      ((free_header_t*)&memory[temp->prev])->next = j;
      new_free->prev = temp->prev;
      new_free->next = free_list_ptr;
      temp->prev = j;

   } else {
      while (temp->next!=free_list_ptr) {
            if (determine_index(temp) < j && temp->next < j) {
               // Either case new item goes after temp.
               temp = (free_header_t*)(&memory[temp->next]);
               continue;
            } else if (temp->next > j && determine_index(temp) < j) {
               // spot found exit loop
               break;
            }
      }

      new_free->next=temp->next;
      new_free->prev=((free_header_t *)&memory[temp->prev])->next;
      temp->next = j;
      ((free_header_t *)&memory[new_free->next])->prev=j;
   } 

   next = new_free->next;
   prev = new_free->prev;

   if (i < free_list_ptr) free_list_ptr = i;
   change_free_header((free_header_t*)(&memory[i]),
      test->size,next,prev);
   
   // call merge to merge any small segments
   vlad_merge();
}

// Input: current state of the memory[]
// Output: new state, where any adjacent blocks in the free list
//            have been combined into a single larger block; after this,
//            there should be no region in the free list whose next
//            reference is to a location just past the end of the region

static void vlad_merge() {
   
   free_header_t * start = (free_header_t *)&memory[free_list_ptr];
   free_header_t * temp = start;
   free_header_t * i = (free_header_t *)&memory[start->next];
   // for the 2 item list case
   if (temp->next == temp->prev) {
      // consecutive item check
      if (temp->next == determine_index(temp)+temp->size) {
         start->size += i->size;
         start->next = start->prev = free_list_ptr;
         return;
      }
   }

   while (determine_index(i)!=free_list_ptr) {

      if ((byte*)temp+temp->size == &memory[temp->next]) {
         
         temp->size += ((free_header_t *)&memory[temp->next])->size;
         temp->next = ((free_header_t *)&memory[temp->next])->next;
         vaddr_t prev = determine_index(temp);
         ((free_header_t *)&memory[temp->next])->prev = prev;

         // recursive merge call if a merge candidate  is found
         vlad_merge();
      }
      temp = (free_header_t *)&memory[temp->next];
      i = (free_header_t *)&memory[temp->next];
   }

}

// Stop the allocator, so that it can be init'ed again:
// Precondition: allocator memory was once allocated by vlad_init()
// Postcondition: allocator is unusable until vlad_int() executed again

void vlad_end(void) {
   
   assert(memory!=NULL);
   assert(memory_size!=0);
   free(memory);
   memory_size=0;
   memory=NULL;
}

// Precondition: allocator has been vlad_init()'d
// Postcondition: allocator stats displayed on stdout

void vlad_stats(void)
{
   int i;
   int count;

   count=0;
   printf("\n\nData array:\n");

   for (i=0; i<memory_size; i++) {
      printf("%d  |  ", memory[i]);
      count++;
      if (count == 8) {
         printf("\n");
         count=0;
      }
   }

}

// figure out size of request for malloc
static u_int32_t determine_size (u_int32_t n) {
   u_int32_t size = n+ALLOC_HEADER_SIZE;
   vsize_t mod = size%4;

   // to change to 4 byte request
   if (mod != 0) size+=(4-mod);

   return size;
}

// change the memory position of the free-header and change pointers
static void change_free_header (free_header_t *head,vsize_t size, 
   vlink_t next, vlink_t prev) {
      
   free_header_t * freehead = head;
   freehead->magic = MAGIC_FREE;
   freehead->size = size;
   freehead->next = next;
   freehead->prev = prev;
}

// make sure no corruptions have occurred in memory re-allocs
static void check_corruption(free_header_t * f) {    
   if (f->magic != MAGIC_FREE) {
      fprintf(stderr, "vald_alloc: Memory corruption\n");
      exit(EXIT_FAILURE);
   }
}

// adjust alloc header/ free headers
static void change_alloc_header(alloc_header_t * head, vsize_t size) {
   free_header_t * temp = (free_header_t *)head;
   temp->prev = temp->next = temp->size = 0;
   head->magic=MAGIC_ALLOC;
   head->size=size;
}

static void change_flist_pointer(free_header_t * p) {

      if (p->next == p->prev) {
         if (determine_index(p) < p->next) {
            free_list_ptr = determine_index(p);
         } else {
            free_list_ptr = p->next;
         }
         return;
      } else if (p->next == determine_index(p)) {
         free_list_ptr = determine_index(p);
         return;
      }

      vsize_t min = p->next;
      free_header_t * temp = (free_header_t*)(&memory[p->next]);
      
      while (temp->next!=p->next) {
         if (temp->next < min) {
            min = temp->next;
         }
         //progress pointer
         temp = (free_header_t*)(&memory[temp->next]);
      }
         assert(min <= free_list_ptr);
         free_list_ptr = min;
}

static vsize_t determine_index (void * p) {
      return (byte*)p - memory;
}


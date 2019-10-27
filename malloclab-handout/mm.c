/*
 *
 * Khanhly Nguyen
 * U0822847
 *
 * mm-naive.c - The least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by allocating a
 * new page as needed.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused.
 *
 * Implementation of the functionality of a malloc. The baseline functionality of this code
 * relies on pages and heaps in which the heap grown and shrunk whenever a call to malloc is
 * made by the user. Freed blocks are then stored within an implementation of an explicit
 * doubly linked list and is traversed until the first big enough or perfectly sized  block
 * is found. If the free block that is found is too large, a splitting of the block is done
 * and is remapped accordingly. Paddings and sentinals are placed within each page to allow
 * a 16-byte allignment. Optimizations were made such as doubling the size of pages if the
 * desired size allocation is larger than a previously called size. This doubling behavior
 * is capped off at a threshold of a single page size (4096) multiplied by 60.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/* always use 16-byte alignment */
#define ALIGNMENT 16

#define WSIZE 8
#define DSIZE 16
#define CHUNKSIZE (1<<12)  // maximum page size
#define PAGE_OVERHEAD 32
#define THRESHOLD (4096*60)

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~(ALIGNMENT-1))

#define MAX(a,b) ((a)>(b) ? (a) : (b))

/* rounds up to the nearest multiple of mem_pagesize() */
#define PAGE_ALIGN(size) (((size) + (mem_pagesize()-1)) & ~(mem_pagesize()-1))

#define OVERHEAD (sizeof(block_header)+sizeof(block_footer))

// Given a payload pointer, get the header or footer pointer
#define HDRP(bp) ((char*)(bp) - sizeof(block_header))
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - OVERHEAD)

// Given a payload pointer, get the next or previous payload pointer
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE((char*)(bp)-OVERHEAD))
#define NEXT_FREE(bp) (*(void**)(bp + WSIZE))
#define PREV_FREE(bp) (*(void**)(bp))

// Given a pointer to a header, get or set its value
#define GET(p)      (*(size_t *)(p))
#define PUT(p, val) (*(size_t *)(p) = (val))

// Combine a size and alloc bit
#define PACK(size, alloc) ((size) | (alloc))

// Given a header pionter, get the alloc or size
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_SIZE(p)  (GET(p) & ~0xF)

typedef size_t block_header;
typedef size_t block_footer;

typedef struct list_node{
  struct list_node* prev;
  struct list_node* next;
}list_node;

struct list_node* list_head;
size_t initial_mapped;

static void* coalesce(void* bp);
static void* extend(size_t s);
static void add_node(void* bp);
static void delete_node(void* bp);
static void* find_fit(size_t asize);
static void set_allocated(void* bp, size_t size);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void){
  list_head = NULL;
  return 0;
}


/* 
 * mm_malloc - Allocate a block by using bytes from current_avail,
 *     grabbing a new page if necessary.
 */
void* mm_malloc(size_t size)
{
  size_t full_size = ALIGN(size + OVERHEAD); 
  void* free_block = NULL;   
  
  // check our free_list to see if we have a block on the current page to allocate
  if((free_block = find_fit(full_size)) != NULL) 
    set_allocated(free_block, full_size);
  else {
    if((free_block = extend(full_size)) != NULL) {
      free_block = list_head;
      set_allocated(free_block, full_size);
    }
  }
  return free_block;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void* ptr)
{
  void* pointer;
  
  size_t size = GET_SIZE(HDRP(ptr));
  PUT(HDRP(ptr), PACK(size, 0));
  PUT(FTRP(ptr), PACK(size, 0));
  pointer = coalesce(ptr);

  // get existing size
  if(((GET_SIZE(pointer - 24)) == OVERHEAD) && ((GET_SIZE(FTRP(pointer) + 8) == 0))) {
    if(GET_SIZE(HDRP(pointer)) >= (4096*10)){
      delete_node(pointer);
      size_t map_size = GET_SIZE(HDRP(pointer)) + PAGE_OVERHEAD;
      mem_unmap(pointer-PAGE_OVERHEAD, map_size);
    }
  }
}

// ******Recommended helper functions******
/* These functios will provide a high-level recommended structure to your program.
 * Fill them in as needed, and create additional helper functions depending on your design.
 */

/* Set a block to allocated
 * Update block headers/footers as needed
 * Update free list if applicable
 * Split block if applicable
 */
static void set_allocated(void* bp, size_t size) {
  size_t initial_size = GET_SIZE(HDRP(bp));
  size_t difference = initial_size - size;
  delete_node(bp);
  // split
  if(difference > PAGE_OVERHEAD) {
    PUT(HDRP(bp), PACK(size, 1));
    PUT(FTRP(bp), PACK(size, 1));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(difference, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(difference, 0));
    add_node(NEXT_BLKP(bp));
  }
  else {
    PUT(HDRP(bp), PACK(initial_size, 1));   
    PUT(FTRP(bp), PACK(initial_size, 1));
  }
}

/*
 * Request more memory by calling mem_map
 * Initialize the new chunk of memory as applicable
 * Update free list if applicable
 */
static void* extend(size_t s) {
  size_t size;
  size_t initial_size = PAGE_ALIGN((initial_mapped*2) + PAGE_OVERHEAD);
  size_t page_size = PAGE_ALIGN(s + PAGE_OVERHEAD);

  if(page_size > initial_size) {
    size = page_size;
    initial_mapped = size;
  }
  else if(initial_size <= THRESHOLD
) {
    size = initial_size;
    initial_mapped = size;
  }
  else
    size = initial_mapped;
  size = PAGE_ALIGN(size + PAGE_OVERHEAD);
  
  void* bp = mem_map(size);
    // return NULL;
  
  PUT(bp, 0);                                  // padding
  bp +=8;
  PUT(bp, PACK(16, 1));                          // header sentinel
  bp +=8;
  PUT(bp, PACK(16, 1));                          // footer sentinel
  bp+=8;
  PUT(bp, PACK(size-PAGE_OVERHEAD, 0));           // header
  bp+=8;
  PUT(FTRP(bp), PACK(size-PAGE_OVERHEAD, 0));     // footer
  PUT((FTRP(bp)+0x8), PACK(0,1));                      // terminator
  // add bp to free list
  add_node(bp);

  return bp;
}

/*
 * Coalesce a free block if applicable
 * Returns pointer to new coalesced block
 */

static void* coalesce(void* bp) {
  size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  if (prev_alloc && next_alloc)
    add_node(bp);

  else if (prev_alloc && !next_alloc) {
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    delete_node(NEXT_BLKP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    add_node(bp);
  }
  else if (!prev_alloc && next_alloc) {
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }
  else {
    size += GET_SIZE(HDRP(NEXT_BLKP(bp))) + GET_SIZE(HDRP(PREV_BLKP(bp)));
    delete_node(NEXT_BLKP(bp));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }
  return bp;
}

/*
 * Insert node into linked list
 */
static void add_node(void* bp) {
  // size_t block_size = GET_SIZE(HDRP(bp));
  




  list_node* new_node = (list_node*)bp;

  new_node->next = list_head;
  if(list_head != NULL)
    list_head->prev = new_node;
  new_node->prev = NULL;
  list_head = new_node;
}

static void delete_node(void* bp) {
  list_node* current_node = (list_node*)bp;
  
  if(current_node->prev == NULL) {
    if(current_node->next == NULL)
      list_head = NULL;
    else {
      list_head = current_node->next;
      current_node->next->prev = NULL;
    }
  }
  else {
    if(current_node->next == NULL) {
      current_node->prev->next = NULL;
    }
    else {
      current_node->prev->next = current_node->next;
      current_node->next->prev = current_node->prev;
    }
  }
}

static void *find_fit(size_t asize) {
  struct list_node* current = list_head;

  while (current) {
    if (GET_SIZE(HDRP(current)) >= asize)
      return (void*)current;
    else
      current = current->next;
  }
  return NULL;
}

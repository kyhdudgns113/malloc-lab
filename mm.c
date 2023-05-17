/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "Team_5",
    /* First member's full name */
    "Young Hoon Kang",
    /* First member's email address */
    "dudgns113@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE               8
#define DSIZE               16

#define CHUNKSIZE           (1 << 12)

#define MAX(x, y)           ((x) > (y) ? (x) : (y))

#define PACK(size, alloc)   ((unsigned long)(size) | (alloc))      //  힙에 할당할 메모리 크기와 alloc bit 을 합친다.

#define GET(p)              (*(unsigned long *)(p))              //  *p 값을 부른다.
#define PUT(p, val)         (*(unsigned long *)(p) = (unsigned long)(val))      //  *p 에 val 을 넣는다.

#define GET_SIZE(p)         (GET(p) & ~0x7)         //  Header 인 p 에서 size 만 추출한다.    
#define GET_ALLOC(p)        (GET(p) & 0x1)          //  Header 인 p 에서 alloc bit 만 추출한다.

//  bp 의 header 의 주소
//  당초에 bp 가 header 다음에 있다.
#define HDRP(bp)            ((char *)(bp) - WSIZE)  

//  bp 의 footer 의 주소
//  bp + GET_SIZE(HDRP(bp)) 를 하면 footer의 시작주소에서 WSIZE 2개만큼 뒤로 간다.
//  그림 9.37 을 참조한다.
#define FTRP(bp)            ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

//  다음 블록의 포인터는 현재 bp 에서 헤더에 담긴 크기만큼 이동하면 된다.
#define NEXT_BLKP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)))

//  이전 블록의 포인터는 이전 블록의 footer 에 담겨있다.
//  이전 블록 footer 의 주소는 bp 에서 bp 의 헤더(WSIZE) 와 이전 포인터의 푸터(WSIZE) 를 뺀 곳의 주소이다.
#define PREV_BLKP(bp)       ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

//  Pred(이전 Free 블록) 의 포인터는 bp 에 있다.
#define PRED_PTR(bp)        ((char *)(bp))

//  Succ(다음 Free 블록) 의 포인터는 bp + WSIZE 에 있다.
#define SUCC_PTR(bp)        ((char *)(bp) + WSIZE)

#define GET_PRED_BLKP(bp)   ((char *)GET(PRED_PTR(bp)))
#define GET_SUCC_BLKP(bp)   ((char *)GET(SUCC_PTR(bp)))

#define NEXT_PRED_BLKP(bp)      ((char *)GET(PRED_PTR(NEXT_BLKP(bp))))
#define NEXT_SUCC_BLKP(bp)      ((char *)GET(SUCC_PTR(NEXT_BLKP(bp))))

#define PREV_PRED_BLKP(bp)      ((char *)GET(PRED_PTR(PREV_BLKP(bp))))
#define PREV_SUCC_BLKP(bp)      ((char *)GET(SUCC_PTR(PREV_BLKP(bp))))


static void *extend_heap(size_t);
static void *coalesce(void *);
static void *find_fit(size_t);
static void place(void *, size_t);

static void dont_show_check_ptr();
static void test_check_ptr();
static void test_check_ptr_from_head();
static void test_show_header(void *);

static void *heap_listp;    //  Heap 의 시작 포인터
static void *ptr_free_head;
static void *ptr_free_tail;

//
//  mm_init : initialize malloc package
//  Finished
//
int mm_init(void)
{
    printf("\nInit Start\n");

    if ((heap_listp = mem_sbrk(10*WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp + (0*WSIZE), 0);
    PUT(heap_listp + (1*WSIZE), PACK(4*WSIZE, 1));
    PUT(heap_listp + (2*WSIZE), 0);
    PUT(heap_listp + (3*WSIZE), heap_listp + 6*WSIZE);
    PUT(heap_listp + (4*WSIZE), PACK(4*WSIZE, 1));

    ptr_free_head = heap_listp + 2*WSIZE;

    PUT(heap_listp + (5*WSIZE), PACK(4*WSIZE, 0));
    PUT(heap_listp + (6*WSIZE), PACK(ptr_free_head, 0));
    PUT(heap_listp + (7*WSIZE), PACK(0, 0));
    PUT(heap_listp + (8*WSIZE), PACK(4*WSIZE, 0));

    PUT(heap_listp + (9*WSIZE), PACK(DSIZE, 1));

    ptr_free_tail = heap_listp + 6*WSIZE;

    printf("Init head is %p, tail is %p\n", ptr_free_head, ptr_free_tail);
    dont_show_check_ptr();
    // test_check_ptr();
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

// 
// mm_malloc - Allocate a block by incrementing the brk pointer.
//     Always allocate a block whose size is a multiple of the alignment.
//
void *mm_malloc(size_t size)
{
    //
    //  asize : 실제로 데이터를 할당할 사이즈
    //  extendsize : 
    //
    printf("mm_malloc start\n");
    size_t asize = 0;
    size_t extendsize = 0;
    char *bp = NULL;

    if (size == 0)
        return NULL;
    
    if (size <= 2*DSIZE)
        asize = 2*DSIZE;
    else {
        //  2*DSIZE 를 넘게 할당하면
        //  오버헤드 바이트를 추가하고 (+DSIZE)
        //  가장 가까운 DSIZE 배수로 올림한다. (+DSIZE - 1)
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / (DSIZE));
    }

    // printf("num of words is %d\n", (int)(asize/DSIZE));
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);

    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

//
// mm_free - Freeing a block does nothing.
//
void mm_free(void *bp)
{
    printf("free start\n");
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    dont_show_check_ptr();
    coalesce(bp);
}

//
// mm_realloc - Implemented simply in terms of mm_malloc and mm_free
// 
void *mm_realloc(void *ptr, size_t size)
{
    printf("realloc start\n");
    void *oldptr = ptr;
    void *newptr = NULL;
    size_t copySize = 0;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

//  words 개수만큼 WSIZE 의 블록을 늘린다.
//  그리고 tail 에 넣어준다.
//  Finished
static void *extend_heap(size_t words)
{
    printf("extend_heap start\n");
    char *bp = NULL;

    size_t size = 0;

    //  4의 배수가 아닌 경우는 용납하지 않는다.
    size = (words % 4) ? (words + 4 - (words % 4)) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    //  헤더와 푸터에 값을 입력한다.
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    //  다음 블록을 할당되었다고 가정해버린다.
    //  다음 블록을 할당하지 않게하기 위함
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    PUT(PRED_PTR(NEXT_BLKP(bp)), bp);
    PUT(SUCC_PTR(NEXT_BLKP(bp)), PACK(0, 0));

    dont_show_check_ptr();
    return coalesce(bp);
}

//  bp 가 해제될 때 호출된다.
//  bp 와 이전블록, 이후블록을 합친다.
//  4개의 경우에 따라 나뉜다.
//  합친 뒤의 시작 포인터를 리턴한다.
static void *coalesce(void *bp)
{
    printf("coal start in %p, tail %p, head %p\n", bp, ptr_free_tail, ptr_free_head);
    void *next_blkp = NEXT_BLKP(bp);
    void *prev_blkp = PREV_BLKP(bp);
    void *next_pred = NULL;
    void *next_succ = NULL;
    void *prev_pred = NULL;
    void *prev_succ = NULL;

    size_t prev_alloc = GET_ALLOC(FTRP(prev_blkp));
    size_t next_alloc = GET_ALLOC(HDRP(next_blkp));
    size_t size = GET_SIZE(HDRP(bp));
    if (prev_alloc && next_alloc) {
        printf("c1\n");
        PUT(SUCC_PTR(ptr_free_tail), bp);

        PUT(PRED_PTR(bp), ptr_free_tail);
        PUT(SUCC_PTR(bp), PACK(0, 0));
    }
    else if (prev_alloc) {
        printf("c2\n");
        size += GET_SIZE(HDRP(next_blkp));

        next_pred = GET_PRED_BLKP(next_blkp);
        next_succ = GET_SUCC_BLKP(next_blkp);

        if (next_blkp != ptr_free_tail && next_succ != ptr_free_tail) {
            PUT(SUCC_PTR(ptr_free_tail), bp);

            PUT(HDRP(bp), size);
            PUT(PRED_PTR(bp), ptr_free_tail);
            PUT(SUCC_PTR(bp), PACK(0, 0));
            PUT(FTRP(bp), size);

            PUT(PRED_PTR(next_succ), next_pred);
            PUT(SUCC_PTR(next_pred), next_succ);
        }
        else if (next_succ == ptr_free_tail) {
            PUT(SUCC_PTR(ptr_free_tail), bp);

            PUT(HDRP(bp), size);
            PUT(PRED_PTR(bp), ptr_free_tail);
            PUT(SUCC_PTR(bp), PACK(0, 0));
            PUT(FTRP(bp), size);

            PUT(PRED_PTR(next_succ), next_pred);
            PUT(SUCC_PTR(next_pred), next_succ);
        }
        else {
            PUT(HDRP(bp), size);
            PUT(PRED_PTR(bp), next_pred);
            PUT(SUCC_PTR(bp), PACK(0, 0));
            PUT(FTRP(bp), size);

            PUT(SUCC_PTR(next_pred), bp);
        }
    }
    else if(next_alloc) {
        printf("c3\n");
        size += GET_SIZE(HDRP(prev_blkp));

        prev_pred = GET_PRED_BLKP(prev_blkp);
        prev_succ = GET_SUCC_BLKP(prev_blkp);

        bp = prev_blkp;

        if (prev_blkp != ptr_free_tail && prev_succ != ptr_free_tail) {
            PUT(SUCC_PTR(ptr_free_tail), bp);

            PUT(HDRP(bp), size);
            PUT(PRED_PTR(bp), ptr_free_tail);
            PUT(SUCC_PTR(bp), PACK(0, 0));
            PUT(FTRP(bp), size);

            PUT(PRED_PTR(prev_succ), prev_pred);
            PUT(SUCC_PTR(prev_pred), prev_succ);
        }
        else if (prev_succ == ptr_free_tail) {
            PUT(SUCC_PTR(ptr_free_tail), bp);

            PUT(HDRP(bp), size);
            PUT(PRED_PTR(bp), ptr_free_tail);
            PUT(SUCC_PTR(bp), PACK(0, 0));
            PUT(FTRP(bp), size);

            PUT(PRED_PTR(prev_succ), prev_pred);
            PUT(SUCC_PTR(prev_pred), prev_succ);
        }
        else {
            PUT(HDRP(bp), size);
            PUT(PRED_PTR(bp), prev_pred);   //  주석처리 ㅆㄱㄴ?
            PUT(SUCC_PTR(bp), PACK(0, 0));
            PUT(FTRP(bp), size);

            PUT(SUCC_PTR(prev_pred), bp);   //  주석처리 ㅆㄱㄴ?
        }
    }
    else {
        printf("c4\n");

        size += GET_SIZE(HDRP(next_blkp)) + GET_SIZE(HDRP(prev_blkp));

        next_pred = GET_PRED_BLKP(next_blkp);
        next_succ = GET_SUCC_BLKP(next_blkp);

        prev_pred = GET_PRED_BLKP(prev_blkp);
        prev_succ = GET_SUCC_BLKP(prev_blkp);

        bp = prev_blkp;

        if (next_blkp != ptr_free_tail && next_succ != ptr_free_tail &&
            prev_blkp != ptr_free_tail && prev_succ != ptr_free_tail) {

            printf("cc1\n");
            
            PUT(SUCC_PTR(ptr_free_tail), bp);

            PUT(HDRP(bp), size);
            PUT(PRED_PTR(bp), ptr_free_tail);
            PUT(SUCC_PTR(bp), PACK(0, 0));
            PUT(FTRP(bp), size);

            PUT(PRED_PTR(next_succ), next_pred);
            PUT(SUCC_PTR(next_pred), next_succ);

            PUT(PRED_PTR(prev_succ), prev_pred);
            PUT(SUCC_PTR(prev_pred), prev_succ);
        }
        else if (next_blkp == ptr_free_tail) {
            printf("cc2\n");

            PUT(SUCC_PTR(next_pred), bp);

            PUT(HDRP(bp), size);
            PUT(PRED_PTR(bp), next_pred);
            PUT(SUCC_PTR(bp), PACK(0, 0));
            PUT(FTRP(bp), size);

            if (prev_succ == ptr_free_tail) {
                printf("ccc1\n");
                PUT(PRED_PTR(bp), prev_pred);
                PUT(SUCC_PTR(prev_pred), bp);
            }
            else {
                printf("ccc2\n");
                PUT(PRED_PTR(prev_succ), prev_pred);
                PUT(SUCC_PTR(prev_pred), prev_succ);
            }
            
        }
        else if (prev_blkp == ptr_free_tail) {
            printf("cc3\n");

            PUT(SUCC_PTR(prev_pred), bp);

            PUT(HDRP(bp), size);
            PUT(PRED_PTR(bp), prev_pred);
            PUT(SUCC_PTR(bp), PACK(0, 0));
            PUT(FTRP(bp), size);

            if (next_succ == ptr_free_tail) {
                PUT(PRED_PTR(bp), next_pred);
                PUT(SUCC_PTR(next_pred), bp);
            }
            else {
                PUT(PRED_PTR(next_succ), next_pred);
                PUT(SUCC_PTR(next_pred), next_succ);
            }
        }
        else if (next_succ == ptr_free_tail) {
            printf("cc4\n");

            PUT(SUCC_PTR(ptr_free_tail), bp);

            PUT(HDRP(bp), size);
            PUT(PRED_PTR(bp), ptr_free_tail);
            PUT(SUCC_PTR(bp), PACK(0, 0));
            PUT(FTRP(bp), size);

            if (prev_succ != next_blkp) {
                PUT(PRED_PTR(next_succ), next_pred);
                PUT(SUCC_PTR(next_pred), next_succ);

                PUT(PRED_PTR(prev_succ), prev_pred);
                PUT(SUCC_PTR(prev_pred), prev_succ);
            }
            else {
                PUT(PRED_PTR(ptr_free_tail), prev_pred);
                PUT(SUCC_PTR(prev_pred), ptr_free_tail);
            }
            
        }
        else if (prev_succ == ptr_free_tail) {
            printf("cc5\n");

            PUT(SUCC_PTR(ptr_free_tail), bp);

            PUT(HDRP(bp), size);
            PUT(PRED_PTR(bp), ptr_free_tail);
            PUT(SUCC_PTR(bp), PACK(0, 0));
            PUT(FTRP(bp), size);

            if (next_succ != prev_blkp) {
                PUT(PRED_PTR(next_succ), next_pred);
                PUT(SUCC_PTR(next_pred), next_succ);

                PUT(PRED_PTR(prev_succ), prev_pred);
                PUT(SUCC_PTR(prev_pred), prev_succ);
            }
            else {
                PUT(PRED_PTR(ptr_free_tail), next_pred);
                PUT(SUCC_PTR(next_pred), ptr_free_tail);
            }
            
        }
        else {
            printf("Assertion in etc case\n");
            exit(0);
        }
        
    }

    ptr_free_tail = bp;
    dont_show_check_ptr();
    return bp;
}



static void *find_fit(size_t asize)
{
    printf("find_fit start\n");
    void *bp = NULL;
    // test_check_ptr();
    for (bp = ptr_free_tail; bp != ptr_free_head && bp != NULL; bp = GET(PRED_PTR(bp))) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL;
}

//
//  bp 에 asize 만큼 공간을 할당한다.
//
static void place(void *bp, size_t asize)
{
    //  c_size : 원래 bp 에 할당되어 있던 사이즈, asize 보단 무조건 크다.
    //  a_size : 내가 할당하려고 하는 사이즈
    printf("place start in %p, tail %p\n", bp, ptr_free_tail);
    void *pred_bp = GET(PRED_PTR(bp));
    void *succ_bp = GET(SUCC_PTR(bp));
    size_t csize = GET_SIZE(HDRP(bp));
    int is_tail_changed = 0;
    if ((csize - asize) >= (2*DSIZE)) {
        // printf("p1\n");
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        if (bp == ptr_free_tail)  {
            // printf("pp1\n");
            bp = NEXT_BLKP(bp);
            PUT(HDRP(bp), csize - asize);
            PUT(PRED_PTR(bp), pred_bp);
            PUT(SUCC_PTR(bp), succ_bp);
            PUT(FTRP(bp), csize - asize);

            PUT(SUCC_PTR(pred_bp), bp);

            ptr_free_tail = bp;
        }
        else {
            // printf("pp2\n");
            bp = NEXT_BLKP(bp);
            PUT(HDRP(bp), csize - asize);
            PUT(PRED_PTR(bp), pred_bp);
            PUT(SUCC_PTR(bp), succ_bp);
            PUT(FTRP(bp), csize - asize);

            PUT(SUCC_PTR(pred_bp), bp);
            PUT(PRED_PTR(succ_bp), bp);
        }
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));

        if (bp == ptr_free_tail) {
            // printf("pp1\n");
            ptr_free_tail = pred_bp;
            PUT(SUCC_PTR(ptr_free_tail), PACK(0, 0));
        }
        else {
            // printf("pp2\n");
            PUT(SUCC_PTR(pred_bp), succ_bp);
            PUT(PRED_PTR(succ_bp), pred_bp);
        }
    }
    dont_show_check_ptr();
    // test_show_header(ptr_free_tail);
}

static void dont_show_check_ptr() {
    void *bp = ptr_free_tail;
    int i = 0;
    for (; bp != ptr_free_head; bp = GET(PRED_PTR(bp))) {
        // printf("%p vs %p in %d, tail = %p\n", bp, GET(PRED_PTR(bp)), i, ptr_free_tail);
        PUT(HDRP(bp), GET(HDRP(bp)));
        PUT(PRED_PTR(bp), GET(PRED_PTR(bp)));
        PUT(SUCC_PTR(bp), GET(SUCC_PTR(bp)));
        PUT(FTRP(bp), GET(FTRP(bp)));

        PUT(HDRP(PREV_BLKP(bp)), GET(HDRP(PREV_BLKP(bp))));
        if (GET(HDRP(bp)) != GET(FTRP(bp))) {
            printf("Assertion 'header == footer' failed in %d\n", i);
            exit(0);
        }
        if (bp == GET(PRED_PTR(bp))) {
            printf("Assertion 'bp != GET(PRED_PTR(bp))' failed in %d\n", i);
            exit(0);
        }
        if (GET(PRED_PTR(bp)) == NULL) {
            printf("Assertion 'pred(bp) != NULL' failed in %d\n", i);
            exit(0);
        }

        i++;
    }
}

static void test_check_ptr() {
    void *bp = ptr_free_tail;
    printf("    FROM TAIL\n");
    printf("    head %p, tail %p\n", ptr_free_head, ptr_free_tail);
    for (; bp != ptr_free_head && bp != NULL; bp = GET(PRED_PTR(bp))) {
        sleep(1);
        printf("        HEAD %p -> 0x%lx\n", HDRP(bp), GET(HDRP(bp)));
        printf("        PRED %p -> 0x%lx\n", PRED_PTR(bp), GET(PRED_PTR(bp)));
        printf("        SUCC %p -> 0x%lx\n", SUCC_PTR(bp), GET(SUCC_PTR(bp)));
        printf("        FOOT %p -> 0x%lx\n", FTRP(bp), GET(FTRP(bp)));
        printf("\n");

    }
}

static void test_check_ptr_from_head() {
    void *bp = ptr_free_head;
    printf("    FROM HEAD\n");
    printf("    head %p, tail %p\n", ptr_free_head, ptr_free_tail);
    for (; bp != ptr_free_tail && bp != NULL; bp = GET(SUCC_PTR(bp))) {
        sleep(1);
        printf("        HEAD %p -> 0x%lx\n", HDRP(bp), GET(HDRP(bp)));
        printf("        PRED %p -> 0x%lx\n", PRED_PTR(bp), GET(PRED_PTR(bp)));
        printf("        SUCC %p -> 0x%lx\n", SUCC_PTR(bp), GET(SUCC_PTR(bp)));
        printf("        FOOT %p -> 0x%lx\n", FTRP(bp), GET(FTRP(bp)));
        printf("\n");


    }
}

static void test_show_header(void *bp) {
    printf("    TEST TEST TEST\n");
    printf("        HEAD %p -> 0x%lx\n", HDRP(bp), GET(HDRP(bp)));
    printf("        PRED %p -> 0x%lx\n", PRED_PTR(bp), GET(PRED_PTR(bp)));
    printf("        SUCC %p -> 0x%lx\n", SUCC_PTR(bp), GET(SUCC_PTR(bp)));
    printf("        FOOT %p -> 0x%lx\n", FTRP(bp), GET(FTRP(bp)));
    printf("\n");
}






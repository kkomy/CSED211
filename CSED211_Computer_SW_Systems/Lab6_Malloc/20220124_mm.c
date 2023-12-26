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

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros - 교재 참조 */
#define WSIZE 4      
#define DSIZE 8
#define CHUNKSIZE (1<<12) 

#define MAX(x, y) ((x) > (y)? (x) : (y))  

#define PACK(size, alloc)  ((size) | (alloc))

#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

#define GET_SIZE(p)  (GET(p) & ~0x7) 
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp)       ((char *)(bp) - WSIZE)  
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))


static char *heap_listp;
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void freemake(void* bp);

static void* prev_list(void* bp);
static void* next_list(void* bp);
static void connection(void* bp);

static char *root; // Explicit method의 free list의 root


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void) 
{
    if ((heap_listp = mem_sbrk(6*WSIZE)) == (void *)-1){ // 6word 만큼 heap 배치
        return -1;
    }

    PUT(heap_listp, 0); //align을 위한 padding
    PUT(heap_listp + (1*WSIZE), 0);  // previous free 블록을 가리키는 포인터
    PUT(heap_listp + (2*WSIZE), 0);  // next free 블록을 가리키는 포인터
    PUT(heap_listp + (3*WSIZE), PACK(DSIZE, 1)); //prologue header
    PUT(heap_listp + (4*WSIZE), PACK(DSIZE, 1)); //prologue footer
    PUT(heap_listp + (5*WSIZE), PACK(0, 1)); //epilogue header
    root = heap_listp + WSIZE; // free list의 root 세팅
    heap_listp += (4*WSIZE); // 포인터를 prologue footer로 옮긴다.

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL){ // 힙 크기를 CHUNKSIZE만큼 늘려준다.
        return -1;
    }

    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) 
{
    size_t asize; 
    size_t extendsize; 
    char *bp;      

    if (heap_listp == 0){ // heap_listp가 처음 그대로라면(0), mm_init을 통해 초기화를 먼저 진행한다.
        mm_init();
    }

    if (size == 0){ // 할당하려는 크기가 0이라면, NULL 반환
        return NULL;
    }

    asize = ALIGN(size + DSIZE); // 할당하려는 블록의 크기의 align을 맞춰준다.

    if ((bp = find_fit(asize)) != NULL) { // allocate하기 적합한 free 블록을 찾기 위해 find_fit 함수 진행
        place(bp, asize); // 있다면 할당!
        return bp;
    }
    else{// 없다면 heap을 추가적으로 늘이기!
        extendsize = MAX(asize,CHUNKSIZE); // 정해진 크기(CHUNKSIZE)보다 블록 크기가 클 경우 블록 크기만큼 더 확장한다.

        if ((bp = extend_heap(extendsize/WSIZE)) == NULL){ 
            return NULL;
        }
    
        place(bp, asize); // 확장한 공간에 할당
        return bp;
    }
} 

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size;
    size = GET_SIZE(HDRP(ptr)); // bp 크기
    PUT(HDRP(ptr), PACK(size, 0)); // free할 블록의 header 0으로 변환
    PUT(FTRP(ptr), PACK(size, 0)); // free할 블록의 footer 0으로 변환

    PUT(next_list(ptr), 0); // 이전 블록 연결 끊기
    PUT(prev_list(ptr), 0); // 다음 블록 연결 끊기
    coalesce(ptr); // previous/next 블록이 free인 경우 coalesce
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t oldsize;
    void *newptr;
    void *next;
    size_t expsize;
    size_t sum;

    if(size == 0){ // 할당할 크기가 0이므로 아무것도 할당x, 즉 free로 처리
        mm_free(ptr);
        return 0;
    }

    if(ptr == NULL){ // ptr이 NULL이라면 새롭게 할당
        return mm_malloc(size);
    }

    oldsize = GET_SIZE(HDRP(ptr)); // realloc 전 기존 블록의 크기
    next = NEXT_BLKP(ptr);

    expsize = size + 2*WSIZE; // size + 2*WSIZE, Explicit으로 인해 추가된 next, previous block 포인터 공간


    if(expsize > oldsize){ // 기존 블록 크기가 realloc한 새로운 블록의 크기보다 작다면
        if(!GET_ALLOC(HDRP(next)) && (oldsize + GET_SIZE(HDRP(next)) >= expsize)){ // 만약 다음블록이 free이고, next block과 기존 블록의 합친 크기가 새로운 블록의 크기보다 클 경우

            connection(next); // 이전 block과 병합 진행:
            PUT(HDRP(ptr), PACK(oldsize + GET_SIZE(HDRP(next)), 1)); 
            PUT(FTRP(ptr), PACK(oldsize + GET_SIZE(HDRP(next)), 1));

            return ptr;
        }

        else{ // 합치지 못할 경우 새로 할당
            newptr = mm_malloc(expsize);
            place(newptr, expsize); // newptr에 expsize 크기만큼 할당
            memcpy(newptr, ptr, expsize); // 기존 정보 복사


            mm_free(ptr); // 기존 블록 할당 해제
            return newptr;
        }
    }
    else{
        return ptr;
    }
}

static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;

    
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; // align 작업

    if ((bp = mem_sbrk(size)) == -1)  // mem_sbrk로 heap 공간 확장
        return NULL;
    
    PUT(HDRP(bp), PACK(size, 0)); // 새로 확장된 heap 공간 0으로 초기화
    PUT(FTRP(bp), PACK(size, 0));  
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    PUT(next_list(bp), 0);
    PUT(prev_list(bp), 0);

    return coalesce(bp); // 새로운 free block이 생겼으므로 다시 coalesce

}

static void *find_fit(size_t asize) // 강의 pdf dynamic memory allocation - basic concept의 first fit 부분을 참조함
{

    void *bp;
    
    for (bp = GET(root); bp != NULL; bp = GET(next_list(bp))) { // bp를 heap의 앞부분(heap_listp)으로 설정, 블록 크기가 0이 아닐때까지 다음 블록 조회(NEXT_BLKP)
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) { // 만약 할당되지 않았고, 블록 크기가 할당하고자 하는 크기보다 크거나 같은 경우
            return bp; // 해당 블록의 위치를 반환
        }
    }
    return NULL;
}

static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));


    if(prev_alloc && next_alloc){ // next, previous 둘 다 allocated일 경우
        freemake(bp);
    }
    else if (prev_alloc && !next_alloc) { // next만 free block일 경우
        connection(NEXT_BLKP(bp));

        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // next블록 크기만큼 free block의 크기 증가시킴
        
        PUT(HDRP(bp), PACK(size, 0)); 
        PUT(FTRP(bp), PACK(size, 0)); 

        freemake(bp);
    }

    else if (!prev_alloc && next_alloc) { // previous만 free block일 경우
        connection(PREV_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp))); // previous 크기만큼 free block 확장

        PUT(FTRP(bp), PACK(size, 0)); 
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); 
        bp = PREV_BLKP(bp);

        freemake(bp);
    }

    else{ // next, previous 둘 다 free block일 경우
        connection(PREV_BLKP(bp));
        connection(NEXT_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // prev, next 크기만큼 free block 크기 증가
        
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);

        freemake(bp);
    }
    return bp;
}


static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 할당하고자하는 위치의 블록 크기
    connection(bp); // bp 공간에 할당할 예정이므로 더이상 free block이 아님, 따라서 free block list에서 삭제

    if ((csize - asize) >= (2*DSIZE)) {  //할당하려는 크기와 할당하려는 블록의 크기 차이가 Align 2칸보다 크다면, spliiting 진행
        PUT(HDRP(bp), PACK(asize, 1)); // allocate
        PUT(FTRP(bp), PACK(asize, 1)); // allocate
        bp = NEXT_BLKP(bp); // 다음 블록, 즉 할당 후 남는 공간
        PUT(next_list(bp), 0); // free list 초기화
        PUT(prev_list(bp), 0); 

        PUT(HDRP(bp), PACK(csize-asize, 0)); // 블록 정보 업데이트
        PUT(FTRP(bp), PACK(csize-asize, 0)); // 블록 정보 업데이트

        coalesce(bp); // 새롭게 free block이 나왔으므로 coalesce 진행
    }
    else { // 크지 않다면, spliiting 진행하지 않고 바로 진행
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

static void* prev_list(void* bp) { // 이전 블록으로 이동
    return (void*)bp;
}

static void* next_list(void* bp) { // previous free block 다음 워드가 next free block을 가리키므로 + WSIZE
    return (void*)bp + WSIZE;
}


static void freemake(void* bp)
{
    void* rootmp= GET(root); //free list의 시작 포인터를 받아온다
    if (rootmp != NULL) //null이 아니면
    {
        PUT(prev_list(rootmp), bp); // 그 이전을 가리키는 포인터에 넣고자 하는 포인터를 저장하고
    }
    PUT(next_list(bp), rootmp); // 원래 시작과 연결해주어서 링크드 리스트에서 (새로운 포인터) -> (기존 시작 포인터) 가 되게끔 한다
    PUT(root, bp); // free list 시작을 업데이트 해준다
}

static void connection(void* bp){
    void *prev = prev_list(bp);
    void *next = next_list(bp);

    if(GET(prev) && GET(next)){ // 둘 다 블록이 존재할 경우
        PUT(prev_list(GET(next)), GET(prev)); //previous의 next 블록이 기존 블록의 next가 되도록
        PUT(next_list(GET(prev)), GET(next)); // next의 previous 블록이 기존 블록의 previous가 되도록
    }

    else if(!GET(prev) && GET(next)){ // next 블록만 존재할 경우, 즉 root일 경우
        PUT(prev_list(GET(next)), 0);
        PUT(root, GET(next));
    }

    else if(GET(prev) && !GET(next)){ // previous 블록만 존재할 경우, 즉 맨 뒤일 경우
        PUT(next_list(GET(prev)), GET(next));
    
    }
    else {// 주변에 아무것도 없을 경우
        PUT(root, GET(next));
    }
    PUT(next_list(bp), 0);
    PUT(prev_list(bp), 0); 

    return;
    

}
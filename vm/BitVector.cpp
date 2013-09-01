/*
 * Copyright (C) 2008 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/*
 * Implementation of an expandable bit vector.
 */
#include "Dalvik.h"

#include <stdlib.h>
#include <strings.h>

#define kBitVectorGrowth    4   /* increase by 4 u4s when limit hit */


/*
 * Allocate a bit vector with enough space to hold at least the specified
 * number of bits.
 */
BitVector* dvmAllocBitVector(int startBits, bool expandable)
{
    BitVector* bv;
    int count;

    assert(sizeof(bv->storage[0]) == 4);        /* assuming 32-bit units */
    assert(startBits >= 0);

    bv = (BitVector*) malloc(sizeof(BitVector));

    count = (startBits + 31) >> 5;

    bv->storageSize = count;
    bv->expandable = expandable;
    bv->storage = (u4*) malloc(count * sizeof(u4));
    memset(bv->storage, 0x00, count * sizeof(u4));
    return bv;
}

/*
 * Free a BitVector.
 */
void dvmFreeBitVector(BitVector* pBits)
{
    if (pBits == NULL)
        return;

    free(pBits->storage);
    free(pBits);
}

/*
 * "Allocate" the first-available bit in the bitmap.
 *
 * This is not synchronized.  The caller is expected to hold some sort of
 * lock that prevents multiple threads from executing simultaneously in
 * dvmAllocBit/dvmFreeBit.
 */
int dvmAllocBit(BitVector* pBits)
{
    int word, bit;

retry:
    for (word = 0; word < pBits->storageSize; word++) {
        if (pBits->storage[word] != 0xffffffff) {
            /*
             * There are unallocated bits in this word.  Return the first.
             */
            bit = ffs(~(pBits->storage[word])) -1;
            assert(bit >= 0 && bit < 32);
            pBits->storage[word] |= 1 << bit;
            return (word << 5) | bit;
        }
    }

    /*
     * Ran out of space, allocate more if we're allowed to.
     */
    if (!pBits->expandable)
        return -1;

    pBits->storage = (u4*)realloc(pBits->storage,
                    (pBits->storageSize + kBitVectorGrowth) * sizeof(u4));
    memset(&pBits->storage[pBits->storageSize], 0x00,
        kBitVectorGrowth * sizeof(u4));
    pBits->storageSize += kBitVectorGrowth;
    goto retry;
}

/*
 * Mark the specified bit as "set".
 */
bool dvmSetBit(BitVector* pBits, int num)
{
    assert(num >= 0);
    if (num >= pBits->storageSize * (int)sizeof(u4) * 8) {
        if (!pBits->expandable)
            return false;

        int newSize = (num + 31) >> 5;
        assert(newSize > pBits->storageSize);
        pBits->storage = (u4*) realloc(pBits->storage, newSize * sizeof(u4));
        memset(&pBits->storage[pBits->storageSize], 0x00,
            (newSize - pBits->storageSize) * sizeof(u4));
        pBits->storageSize = newSize;
    }

    pBits->storage[num >> 5] |= 1 << (num & 0x1f);
    return true;
}

/*
 * Mark the specified bit as "clear".
 */
void dvmClearBit(BitVector* pBits, int num)
{
    assert(num >= 0 && num < (int) pBits->storageSize * (int)sizeof(u4) * 8);

    pBits->storage[num >> 5] &= ~(1 << (num & 0x1f));
}

/*
 * Mark all bits bit as "clear".
 */
void dvmClearAllBits(BitVector* pBits)
{
    int count = pBits->storageSize;
    memset(pBits->storage, 0, count * sizeof(u4));
}

/*
 * Determine whether or not the specified bit is set.
 */
bool dvmIsBitSet(const BitVector* pBits, int num)
{
    assert(num >= 0 && num < (int) pBits->storageSize * (int)sizeof(u4) * 8);

    int val = pBits->storage[num >> 5] & (1 << (num & 0x1f));
    return (val != 0);
}

/*
 * Count the number of bits that are set.
 */
int dvmCountSetBits(const BitVector* pBits)
{
    int word;
    int count = 0;

    for (word = 0; word < pBits->storageSize; word++) {
        u4 val = pBits->storage[word];

        if (val != 0) {
            if (val == 0xffffffff) {
                count += 32;
            } else {
                /* count the number of '1' bits */
                while (val != 0) {
                    val &= val - 1;
                    count++;
                }
            }
        }
    }

    return count;
}


/*
 * Copy a whole vector to the other. Only do that when the both vectors have
 * the same size and attribute.
 */
bool dvmCopyBitVector(BitVector *dest, const BitVector *src)
{
    if (dest->storageSize != src->storageSize ||
        dest->expandable != src->expandable)
        return false;
    memcpy(dest->storage, src->storage, sizeof(u4) * dest->storageSize);
    return true;
}

/*
 * Intersect two bit vectores and merge the result on top of the pre-existing
 * value in the dest vector.
 */
bool dvmIntersectBitVectors(BitVector *dest, const BitVector *src1,
                            const BitVector *src2)
{
    if (dest->storageSize != src1->storageSize ||
        dest->storageSize != src2->storageSize ||
        dest->expandable != src1->expandable ||
        dest->expandable != src2->expandable)
        return false;

    int i;
    for (i = 0; i < dest->storageSize; i++) {
        dest->storage[i] |= src1->storage[i] & src2->storage[i];
    }
    return true;
}


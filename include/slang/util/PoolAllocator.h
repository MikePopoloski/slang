//------------------------------------------------------------------------------
//! @file PoolAllocator.h
//! @brief An allocator that saves recycled objects in a pool
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/BumpAllocator.h"

namespace slang {

template<typename T, size_t Size = sizeof(T), size_t Align = alignof(T)>
class PoolAllocator {
public:
    explicit PoolAllocator(BumpAllocator& alloc) : alloc(alloc) {}

    template<typename TSubClass, typename... Args>
    TSubClass* emplace(Args&&... args) {
        static_assert(sizeof(TSubClass) <= Size);
        static_assert(alignof(TSubClass) <= Align);
        static_assert(std::is_trivially_destructible_v<TSubClass>);
        auto mem = freeList ? reinterpret_cast<TSubClass*>(pop())
                            : reinterpret_cast<TSubClass*>(alloc.allocate(Size, Align));
        return new (mem) TSubClass(std::forward<Args>(args)...);
    }

    template<typename... Args>
    T* emplace(Args&&... args) {
        return emplace<T>(std::forward<Args>(args)...);
    }

    template<typename TSubClass>
    void destroy(TSubClass* elem) {
        static_assert(Size >= sizeof(FreeNode));
        static_assert(Align >= alignof(FreeNode));
        elem->~TSubClass();
        push(reinterpret_cast<FreeNode*>(elem));
    }

private:
    struct FreeNode {
        FreeNode* next;
    };

    FreeNode* pop() {
        ASSERT(freeList);
        auto result = freeList;
        freeList = freeList->next;
        return result;
    }

    void push(FreeNode* node) {
        node->next = freeList;
        freeList = node;
    }

    BumpAllocator& alloc;
    FreeNode* freeList = nullptr;
};

} // namespace slang

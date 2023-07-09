//------------------------------------------------------------------------------
//! @file ThreadPool.h
//! @brief Lightweight thread pool class
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <atomic>
#include <deque>
#include <functional>
#include <future>
#include <memory>
#include <mutex>
#include <thread>
#include <type_traits>
#include <vector>

#include "slang/util/Util.h"

namespace slang {

/// A lightweight thread pool for running concurrent jobs.
class ThreadPool {
public:
    /// @brief Constructs a new ThreadPool.
    ///
    /// @param threadCount The number of threads to create in the pool. If zero (the default)
    ///                    the number of threads will be set to the number of concurrent threads
    ///                    supported by the system.
    explicit ThreadPool(unsigned threadCount = 0) {
        if (threadCount == 0) {
            threadCount = std::thread::hardware_concurrency();
            if (threadCount == 0)
                threadCount = 1;
        }

        {
            std::unique_lock lock(mutex);
            waiting = false;
            running = true;
        }

        for (unsigned i = 0; i < threadCount; i++)
            threads.emplace_back(&ThreadPool::worker, this);
    }

    /// Destroys the thread pool, blocking until all threads have exited.
    ~ThreadPool() {
        waitForAll();

        {
            std::unique_lock lock(mutex);
            running = false;
        }

        taskAvailable.notify_all();
        for (auto& thread : threads)
            thread.join();
    }

    /// Gets the number of threads in the thread pool.
    size_t getThreadCount() const { return threads.size(); }

    /// @brief Pushes a new task into the pool for execution.
    ///
    /// There is no way to wait for the pushed task to complete aside from
    /// calling @a waitForAll and waiting for all tasks in the pool to complete.
    template<typename TFunc, typename... TArgs>
    void pushTask(TFunc&& task, TArgs&&... args) {
        {
            std::unique_lock lock(mutex);
            tasks.emplace_back(std::bind(std::forward<TFunc>(task), std::forward<TArgs>(args)...));
        }

        taskAvailable.notify_one();
    }

    /// @brief Submits a task into the pool for execution and returns a future
    /// for tracking completion.
    ///
    /// @returns A std::future that will eventually contain the result of the task.
    template<typename TFunc, typename... TArgs,
             typename TResult = std::invoke_result_t<std::decay_t<TFunc>, std::decay_t<TArgs>...>>
    [[nodiscard]] std::future<TResult> submit(TFunc&& task, TArgs&&... args) {
        auto taskPromise = std::make_shared<std::promise<TResult>>();
        pushTask([func = std::bind(std::forward<TFunc>(task), std::forward<TArgs>(args)...),
                  taskPromise] {
            SLANG_TRY {
                if constexpr (std::is_void_v<TResult>) {
                    std::invoke(func);
                    taskPromise->set_value();
                }
                else {
                    taskPromise->set_value(std::invoke(func));
                }
            }
            SLANG_CATCH(...) {
                SLANG_TRY {
                    taskPromise->set_exception(std::current_exception());
                }
                SLANG_CATCH(...) {
                }
            }
        });

        return taskPromise->get_future();
    }

    /// @brief Pushes several tasks into the pool in order to parallelize
    /// the loop given by [from, to).
    ///
    /// The loop will be broken into a number of blocks as specified by
    /// @a numBlocks -- or if zero, the number of blocks will be set to
    /// the number of threads in the pool.
    template<typename TIndex, typename TFunc>
    void pushLoop(TIndex from, TIndex to, TFunc&& body, size_t numBlocks = 0) {
        SLANG_ASSERT(to >= from);
        if (!numBlocks)
            numBlocks = getThreadCount();

        const size_t totalSize = size_t(to - from);
        if (!totalSize)
            return;

        size_t blockSize = totalSize / numBlocks;
        if (blockSize == 0) {
            blockSize = 1;
            numBlocks = totalSize;
        }

        for (size_t i = 0; i < numBlocks; i++) {
            const TIndex start = TIndex(i * blockSize) + from;
            const TIndex end = i == numBlocks - 1 ? to : TIndex(start + blockSize);
            pushTask(std::forward<TFunc>(body), start, end);
        }
    }

    /// Blocks the calling thread until all running tasks are complete.
    void waitForAll() {
        std::unique_lock lock(mutex);
        waiting = true;
        taskDone.wait(lock, [this] { return !currentTasks && tasks.empty(); });
        waiting = false;
    }

    /// Blocks the calling thread until all running tasks are complete, or
    /// until the provided duration is passed.
    /// @returns true if all tasks completed, or false if the timeout was reached first
    template<typename R, typename P>
    bool waitForAll(const std::chrono::duration<R, P>& duration) {
        std::unique_lock lock(mutex);
        waiting = true;
        const bool status = taskDone.wait_for(lock, duration,
                                              [this] { return !currentTasks && tasks.empty(); });
        waiting = false;
        return status;
    }

private:
    void worker() {
        while (true) {
            std::unique_lock lock(mutex);
            taskAvailable.wait(lock, [this] { return !tasks.empty() || !running; });
            if (!running)
                break;

            auto task = std::move(tasks.front());
            tasks.pop_front();
            ++currentTasks;
            lock.unlock();
            task();
            lock.lock();
            --currentTasks;

            if (waiting && !currentTasks && tasks.empty())
                taskDone.notify_all();
        }
    }

    std::mutex mutex;
    std::deque<std::function<void()>> tasks;
    std::condition_variable taskAvailable;
    std::condition_variable taskDone;
    std::vector<std::thread> threads;
    size_t currentTasks = 0;
    bool running;
    bool waiting;
};

} // namespace slang

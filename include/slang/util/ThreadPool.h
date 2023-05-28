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

    /// Blocks the calling thread until all running tasks are complete.
    void waitForAll() {
        std::unique_lock lock(mutex);
        waiting = true;
        taskDone.wait(lock, [this] { return tasks.empty(); });
        waiting = false;
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
            lock.unlock();
            task();
            lock.lock();

            if (waiting && tasks.empty())
                taskDone.notify_one();
        }
    }

    std::mutex mutex;
    std::deque<std::function<void()>> tasks;
    std::condition_variable taskAvailable;
    std::condition_variable taskDone;
    std::vector<std::thread> threads;
    bool running;
    bool waiting;
};

} // namespace slang

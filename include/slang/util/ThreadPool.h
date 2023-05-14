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

        waiting = false;
        running = true;

        for (unsigned i = 0; i < threadCount; i++)
            threads.emplace_back(&ThreadPool::worker, this);
    }

    /// Destroys the thread pool, blocking until all threads have exited.
    ~ThreadPool() {
        waitForAll();

        running = false;
        {
            std::unique_lock lock(mutex);
            taskAvailable.notify_all();
        }

        for (auto& thread : threads)
            thread.join();
    }

    /// @brief Pushes a new task into the pool for execution.
    ///
    /// There is no way to wait for the pushed task to complete aside from
    /// calling @a waitForAll and waiting for all tasks in the pool to complete.
    template<typename TFunc, typename... TArgs>
    void pushTask(TFunc&& task, TArgs&&... args) {
        std::function<void()> func = std::bind(std::forward<TFunc>(task),
                                               std::forward<TArgs>(args)...);
        {
            std::unique_lock lock(mutex);
            tasks.emplace_back(std::move(func));
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
        std::function<TResult()> func = std::bind(std::forward<TFunc>(task),
                                                  std::forward<TArgs>(args)...);
        auto taskPromise = std::make_shared<std::promise<TResult>>();

        pushTask([func = std::move(func), taskPromise] {
            try {
                if constexpr (std::is_void_v<TResult>) {
                    std::invoke(func);
                    taskPromise->set_value();
                }
                else {
                    taskPromise->set_value(std::invoke(func));
                }
            }
            catch (...) {
                try {
                    taskPromise->set_exception(std::current_exception());
                }
                catch (...) {
                }
            }
        });

        return taskPromise->get_future();
    }

    /// Blocks the calling thread until all running tasks are complete.
    void waitForAll() {
        if (!waiting) {
            waiting = true;
            std::unique_lock lock(mutex);
            taskDone.wait(lock, [this] { return tasks.empty(); });
            waiting = false;
        }
    }

private:
    void worker() {
        while (running) {
            std::unique_lock lock(mutex);
            taskAvailable.wait(lock, [this] { return !tasks.empty() || !running; });

            if (!tasks.empty()) {
                auto task = std::move(tasks.front());
                tasks.pop_front();
                lock.unlock();
                task();
                lock.lock();

                if (waiting)
                    taskDone.notify_one();
            }
        }
    }

    std::mutex mutex;
    std::deque<std::function<void()>> tasks;
    std::atomic<bool> running;
    std::atomic<bool> waiting;
    std::condition_variable taskAvailable;
    std::condition_variable taskDone;
    std::vector<std::thread> threads;
};

} // namespace slang

//------------------------------------------------------------------------------
// TimeTrace.cpp
// Time tracing for profiling performance
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/util/TimeTrace.h"

#include <chrono>
#include <fmt/core.h>
#include <mutex>
#include <ostream>
#include <thread>
#include <vector>

#include "slang/text/CharInfo.h"
#include "slang/util/Hash.h"

using namespace std::chrono;

namespace slang {

std::unique_ptr<TimeTrace::Profiler> TimeTrace::profiler = nullptr;

using DurationType = duration<steady_clock::rep, steady_clock::period>;

static std::string escapeString(std::string_view src) {
    std::string result;
    for (char c : src) {
        switch (c) {
            case '"':
            case '/':
            case '\\':
            case '\b':
            case '\f':
            case '\n':
            case '\r':
            case '\t':
                result += '\\';
                result += c;
                break;
            default:
                if (isPrintableASCII(c))
                    result += c;
                break;
        }
    }
    return result;
}

struct Entry {
    time_point<steady_clock> start;
    DurationType duration;
    std::thread::id threadId;
    std::string name;
    std::string detail;
};

struct TimeTrace::Profiler {
    static thread_local std::vector<Entry> stack;
    std::vector<Entry> entries;
    time_point<steady_clock> startTime;
    std::mutex mut;

    Profiler() {
        entries.reserve(128);
        startTime = steady_clock::now();
    }

    void begin(std::string name, function_ref<std::string()> detail) {
        stack.push_back(
            Entry{steady_clock::now(), {}, std::this_thread::get_id(), std::move(name), detail()});
    }

    void end() {
        SLANG_ASSERT(!stack.empty());
        SLANG_ASSERT(stack.back().threadId == std::this_thread::get_id());

        auto&& entry = stack.back();
        entry.duration = steady_clock::now() - entry.start;

        // Only include sections longer than 500us.
        if (duration_cast<microseconds>(entry.duration).count() > 500) {
            std::scoped_lock lock(mut);
            entries.emplace_back(std::move(entry));
        }

        stack.pop_back();
    }

    void write(std::ostream& os) {
        SLANG_ASSERT(stack.empty());
        std::scoped_lock lock(mut);

        // std::thread::id isn't convertible to an integer, so put it in
        // a table to generate nice ids for output.
        flat_hash_map<std::thread::id, int> threadIdMap;
        int nextThreadId = 0;
        auto getTID = [&](std::thread::id id) {
            auto [it, inserted] = threadIdMap.try_emplace(id, nextThreadId);
            if (inserted)
                ++nextThreadId;
            return it->second;
        };

        // Make sure this thread (presumably the main thread) has ID 0.
        getTID(std::this_thread::get_id());

        os << "{ \"traceEvents\": [\n";

        for (auto& entry : entries) {
            auto startUs = duration_cast<microseconds>(entry.start - startTime).count();
            auto durationUs = duration_cast<microseconds>(entry.duration).count();
            os << fmt::format("{{ \"pid\":1, \"tid\":{}, \"ph\":\"X\", \"ts\":{}, "
                              "\"dur\":{}, \"name\":\"{}\", \"args\":{{ \"detail\":\"{}\" }} }},\n",
                              getTID(entry.threadId), startUs, durationUs, escapeString(entry.name),
                              escapeString(entry.detail));
        }

        // Emit metadata event with process name.
        os << "{ \"cat\":\"\", \"pid\":1, \"tid\":0, \"ts\":0, \"ph\":\"M\", "
              "\"name\":\"process_name\", \"args\":{ \"name\":\"slang\" } }\n";
        os << "] }\n";
    }
};

thread_local std::vector<Entry> TimeTrace::Profiler::stack;

void TimeTrace::initialize() {
    SLANG_ASSERT(!profiler);
    profiler = std::make_unique<Profiler>();
}

void TimeTrace::write(std::ostream& os) {
    SLANG_ASSERT(profiler);
    profiler->write(os);
}

void TimeTrace::beginTrace(std::string_view name, std::string_view detail) {
    if (profiler)
        profiler->begin(std::string(name), [&] { return std::string(detail); });
}

void TimeTrace::beginTrace(std::string_view name, function_ref<std::string()> detail) {
    if (profiler)
        profiler->begin(std::string(name), detail);
}

void TimeTrace::endTrace() {
    if (profiler)
        profiler->end();
}

} // namespace slang

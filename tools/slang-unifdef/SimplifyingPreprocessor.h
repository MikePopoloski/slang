//------------------------------------------------------------------------------
//! @file SimplifyingPreprocessor.h
//! @brief Redaction of `ifdef / `ifndef conditional blocks
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <stdexcept>
#include <string>

#include "slang/util/FlatMap.h"

namespace slang {
class SourceManager;
struct SourceBuffer;
} // namespace slang

/// Thrown when a redaction macro is used in a way the redactor cannot safely handle.
class RedactionError : public std::runtime_error {
public:
    using std::runtime_error::runtime_error;
};

/// Simplifies preprocessor conditionals by treating selected macros as forced defined
/// or undefined.
///
/// This runs directly over source text using slang's lexer to identify directive tokens.
/// When a conditional branch is decided by one of the forced macro values, the directive
/// scaffolding and inactive branch text are omitted and the surviving branch is inlined.
class SimplifyingPreprocessor {
public:
    explicit SimplifyingPreprocessor(slang::SourceManager& sourceManager) :
        sourceManager(sourceManager) {}

    /// Adds a macro name with the forced value to use while simplifying conditionals.
    void setMacroValue(std::string_view macro, bool value) {
        macroValues[std::string(macro)] = value;
    }

    /// Redact the provided source buffer and append it to the internal output.
    SimplifyingPreprocessor& redact(slang::SourceBuffer buffer);

    /// @return a copy of the internal text buffer.
    std::string str() const { return output; }

private:
    slang::SourceManager& sourceManager;
    slang::flat_hash_map<std::string, bool> macroValues;
    std::string output;
};

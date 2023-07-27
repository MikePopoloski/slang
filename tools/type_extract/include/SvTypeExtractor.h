#pragma once

#include "CppEmitter.h"

#include "slang/ast/Compilation.h"

class SvTypeExtractor {
public:
    explicit SvTypeExtractor(std::unique_ptr<slang::ast::Compilation> compilation, bool verbose,
                             bool noSystemC) :
        compilation(std::move(compilation)),
        verbose(verbose), noSystemC(noSystemC), cppEmitter(noSystemC) {}

    void extract();

    inline std::string emit() { return cppEmitter.emit(); }
    inline void emitToFile(const fs::path& path) { cppEmitter.emitToFile(path); }

private:
    bool verbose;
    bool noSystemC;
    CppEmitter cppEmitter;
    std::unique_ptr<slang::ast::Compilation> compilation;
};

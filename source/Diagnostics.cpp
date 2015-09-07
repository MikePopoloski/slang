#include <cstdint>
#include <memory>

#include "Buffer.h"
#include "Diagnostics.h"

namespace slang {

Diagnostics::Diagnostics()
    : syntaxErrors(128) {
}

void Diagnostics::add(const SyntaxError& error) {
    syntaxErrors.append(error);
}

}
#include "slang.h"

namespace slang {

Diagnostics::Diagnostics()
    : syntaxErrors(128) {
}

void Diagnostics::add(const SyntaxError& error) {
    syntaxErrors.append(error);
}

}
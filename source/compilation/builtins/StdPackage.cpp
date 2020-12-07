//------------------------------------------------------------------------------
// StdPackage.cpp
// Definitions for the built-in 'std' package
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/compilation/Compilation.h"
#include "slang/symbols/ClassSymbols.h"
#include "slang/symbols/CompilationUnitSymbols.h"
#include "slang/symbols/MemberSymbols.h"
#include "slang/types/AllTypes.h"

namespace slang::Builtins {

#define NL SourceLocation::NoLocation

static const Symbol& createProcessClass(Compilation& c) {
    auto ct = c.emplace<ClassType>(c, "process", NL);

    auto stateEnum = c.emplace<EnumType>(c, NL, c.getIntType(), LookupLocation(ct, 1), *ct);
    stateEnum->systemId = INT32_MAX - 2048;

    int index = 0;
    for (auto name : { "FINISHED", "RUNNING", "WAITING", "SUSPENDED", "KILLED" }) {
        auto ev = c.emplace<EnumValueSymbol>(name, NL);
        stateEnum->addMember(*ev);
        ev->setValue(SVInt(32, index++, true));

        // Manually add these to the containing scope as well.
        ct->addMember(*c.emplace<TransparentMemberSymbol>(*ev));
    }

    auto stateTypedef = c.emplace<TypeAliasType>("state", NL);
    stateTypedef->targetType.setType(*stateEnum);
    ct->addMember(*stateTypedef);

    // TODO: other members
    return *ct;
}

const PackageSymbol& createStdPackage(Compilation& c) {
    auto pkg = c.emplace<PackageSymbol>(c, "std", NL, c.getWireNetType());
    pkg->addMember(createProcessClass(c));
    return *pkg;
}

} // namespace slang::Builtins

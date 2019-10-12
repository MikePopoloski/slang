#include "Test.h"

#include "slang/util/CommandLine.h"

TEST_CASE("Test CommandLine") {
    CommandLine cmdLine;
    cmdLine.parse("-d --hello -abc/foo/bar --baz=\"asdf\""sv);
}
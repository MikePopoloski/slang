// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/text/SourceManager.h"
#include "slang/util/CommandLine.h"

TEST_CASE("Test CommandLine -- basic") {
    std::optional<bool> a, b, longFlag, longFlag2;
    std::optional<std::string> c;
    std::optional<int32_t> d;
    std::optional<uint64_t> ext;
    std::optional<double> ext2;
    std::optional<uint32_t> unused1;
    std::optional<int64_t> unused2;
    std::optional<uint32_t> used1;
    std::optional<int64_t> used2;
    std::vector<std::string> multi;
    std::vector<std::string> vals;
    int someCounter = 0;

    CommandLine cmdLine;
    cmdLine.add("-a", a, "SDF");
    cmdLine.add("-b", b, "SDF");
    cmdLine.add("-z,-y,-x,--longFlag", longFlag, "This flag does fun stuff");
    cmdLine.add("--longFlag2", longFlag2, "Another\ngood\nthing");
    cmdLine.add("-c", c, "SDF");
    cmdLine.add("-d", d, "SDF");
    cmdLine.add("-e,--ext", ext, "Definitely should set me");
    cmdLine.add("-f,--ext2", ext2, "Me too!", "<value>");
    cmdLine.add("--biz,--baz", unused1, "SDF", "<entry>");
    cmdLine.add("--buz,--boz", unused2, "SDF", "=<val>");
    cmdLine.add("--fiz,--faz", used1, "SDF");
    cmdLine.add("--fuz,--foz", used2, "SDF");
    cmdLine.add("-m,+multi", multi, "SDF");
    cmdLine.add(
        "--count",
        [&](std::string_view) {
            someCounter++;
            return "";
        },
        "asdf");
    cmdLine.setPositional(vals, "vals");

    CHECK(cmdLine.parse(
        "prog -a -b --longFlag=False pos1 pos2 -c asdf -d -1234 --ext=9876 "
        "--ext2 9999.1234e12 pos3 --fiz=4321 --foz=-4321    - pos5 "
        "--longFlag2=true -ma +multi+b+cd+ef --count=foo --count=bar -- --buz --boz"sv));

    CHECK(cmdLine.getProgramName() == "prog");
    cmdLine.setProgramName("asdf");
    CHECK(cmdLine.getProgramName() == "asdf");

    CHECK(a);
    CHECK(b);
    CHECK(longFlag);
    CHECK(longFlag2);
    CHECK(c);
    CHECK(d);
    CHECK(ext);
    CHECK(ext2);
    CHECK(!unused1);
    CHECK(!unused2);
    CHECK(used1);
    CHECK(used2);

    CHECK(*a == true);
    CHECK(*b == true);
    CHECK(*longFlag == false);
    CHECK(*longFlag2 == true);
    CHECK(*c == "asdf");
    CHECK(*d == -1234);
    CHECK(*ext == 9876);
    CHECK(*ext2 == 9999.1234e12);
    CHECK(used1 == 4321u);
    CHECK(used2 == -4321);
    CHECK(someCounter == 2);

    REQUIRE(multi.size() == 4);
    CHECK(multi[0] == "a");
    CHECK(multi[1] == "b");
    CHECK(multi[2] == "cd");
    CHECK(multi[3] == "ef");

    REQUIRE(vals.size() == 7);
    CHECK(vals[0] == "pos1");
    CHECK(vals[1] == "pos2");
    CHECK(vals[2] == "pos3");
    CHECK(vals[3] == "-");
    CHECK(vals[4] == "pos5");
    CHECK(vals[5] == "--buz");
    CHECK(vals[6] == "--boz");

    auto help = "\n" + cmdLine.getHelpText("prog - A fun program!!");
    CHECK(help == R"(
OVERVIEW: prog - A fun program!!

USAGE: asdf [options] vals...

OPTIONS:
  -a                   SDF
  -b                   SDF
  -z,-y,-x,--longFlag  This flag does fun stuff
  --longFlag2          Another
                       good
                       thing
  -c                   SDF
  -d                   SDF
  -e,--ext             Definitely should set me
  -f,--ext2 <value>    Me too!
  --biz,--baz <entry>  SDF
  --buz,--boz=<val>    SDF
  --fiz,--faz          SDF
  --fuz,--foz          SDF
  -m,+multi            SDF
  --count              asdf
)");
}

TEST_CASE("Test CommandLine -- backslash at EOL") {
    std::optional<bool> a, b, c;
    CommandLine cmdLine;
    cmdLine.add("-a", a, "SDF");
    cmdLine.add("-b", b, "SDF");
    cmdLine.add("-c", c, "SDF");

    // Check for backslash at EOL
    // Check for backslash plus whitespace(s) at EOL
    // Check for backslash at end of command line args
    CHECK(cmdLine.parse("prog -a\\\n -b -c\\"sv));
    CHECK(cmdLine.getProgramName() == "prog");
    CHECK(a);
    CHECK(b);
    CHECK(c);
}

TEST_CASE("Test CommandLine -- nonspan") {
    std::optional<bool> a;
    CommandLine cmdLine;
    cmdLine.add("-a", a, "SDF");

    std::array args = {"prog", "-a"};
    CHECK(cmdLine.parse((int)args.size(), args.data()));

    CHECK(a == true);
}

TEST_CASE("Test CommandLine -- vectors") {
    std::vector<int32_t> groupa;
    std::vector<int64_t> groupb;
    std::vector<uint32_t> groupc;
    std::vector<uint64_t> groupd;
    std::vector<double> groupe;
    std::vector<std::string> groupf;

    CommandLine cmdLine;
    cmdLine.add("-a,--longa", groupa, "SDF");
    cmdLine.add("-b,--longb", groupb, "SDF");
    cmdLine.add("-c,--longc", groupc, "SDF");
    cmdLine.add("-d,--longd", groupd, "SDF");
    cmdLine.add("-e,--longe", groupe, "SDF");
    cmdLine.add("-f,--longf", groupf, "SDF");

    CHECK(cmdLine.parse("prog -a 1 --longa 99 -f fff --longf=ffff -e 4.1 "
                        "-d 5 -d 5 -d 5 --longc 8 -c 9 -b -42 -b -43"sv));

    CHECK(groupa == std::vector<int32_t>{1, 99});
    CHECK(groupb == std::vector<int64_t>{-42ll, -43ll});
    CHECK(groupc == std::vector<uint32_t>{8u, 9u});
    CHECK(groupd == std::vector<uint64_t>{5ull, 5ull, 5ull});
    CHECK(groupe == std::vector{4.1});
    CHECK(groupf == std::vector{"fff"s, "ffff"s});
}

TEST_CASE("Test CommandLine -- vectors with comma lists") {
    std::vector<int32_t> groupa;
    std::vector<double> groupb;
    std::vector<std::string> groupc;

    CommandLine cmdLine;
    cmdLine.add("-a,--longa", groupa, "SDF", "", CommandLineFlags::CommaList);
    cmdLine.add("-b,--longb", groupb, "SDF", "", CommandLineFlags::CommaList);
    cmdLine.add(
        "-c,--longc",
        [&](std::string_view val) {
            groupc.push_back(std::string(val));
            return "";
        },
        "SDF", "", CommandLineFlags::CommaList);

    CHECK(cmdLine.parse("prog -a 1,2,3 --longa=4,5,6 -b 3.14,4.15 -c foo,bar,baz"sv));

    CHECK(groupa == std::vector<int32_t>{1, 2, 3, 4, 5, 6});
    CHECK(groupb == std::vector{3.14, 4.15});
    CHECK(groupc == std::vector{"foo"s, "bar"s, "baz"s});
}

TEST_CASE("Test CommandLine -- splitting") {
    std::vector<std::string> stuff;

    CommandLine cmdLine;
    cmdLine.add("-a,--longa", stuff, "SDF", "val");

    auto args = R"(prog -a \ -a \-a asdf '--longa=bar baz bif \' -a "f foo \" biz \\" -a 1)"sv;
    CHECK(cmdLine.parse(args));

    CHECK(stuff == std::vector{" -a"s, "asdf"s, "bar baz bif \\"s, "f foo \" biz \\"s, "1"s});
}

TEST_CASE("Test CommandLine -- comments") {
    std::vector<std::string> stuff;

    CommandLine cmdLine;
    cmdLine.add("-a,--longa", stuff, "SDF", "val");

    CommandLine::ParseOptions options;
    options.supportComments = true;

    auto args = R"(prog -a
foo#comment!!
-a foo/bar//not_comment //this is a comment!
-a foo/bar/*/not_comment/* -a
/*comment! / * /* asdf*/ value#asdf
)"sv;
    CHECK(cmdLine.parse(args, options));

    CHECK(stuff ==
          std::vector{"foo"s, "foo/bar//not_comment"s, "foo/bar/*/not_comment/*"s, "value"s});
}

TEST_CASE("Test CommandLine -- env vars") {
    std::vector<std::string> stuff;

    CommandLine cmdLine;
    cmdLine.add("-a,--longa", stuff, "SDF", "val");
    cmdLine.setPositional(stuff, "stuff");

    CommandLine::ParseOptions options;
    options.ignoreProgramName = true;
    options.expandEnvVars = true;

    putenv((char*)"FOO_456=abc 123");
    putenv((char*)"BAR#=some string");
    putenv((char*)"BAZ=987654");

    auto args = R"qq(
$&
asdf/$FOO_456/bar "$(BAR#)" ${UNK} ${BAZ} ${
$)qq"sv;
    CHECK(cmdLine.parse(args, options));

    CHECK(stuff ==
          std::vector{"$&"s, "asdf/abc"s, "123/bar"s, "some string"s, "987654"s, "${"s, "$"s});
}

#if __cpp_exceptions
TEST_CASE("Test CommandLine -- programmer errors") {
    std::optional<bool> foo;

    CommandLine cmdLine;

    CHECK_THROWS(cmdLine.parse("prog"));
    CHECK_THROWS(cmdLine.add("", foo, "SDF"));
    CHECK_THROWS(cmdLine.add(",--asdf1", foo, "SDF"));
    CHECK_THROWS(cmdLine.add("--asdf2,--asdf3,", foo, "SDF"));
    CHECK_THROWS(cmdLine.add("--asdf6,--asdf6", foo, "SDF"));
    CHECK_THROWS(cmdLine.add("foo", foo, "SDF"));
    CHECK_THROWS(cmdLine.add("-", foo, "SDF"));
    CHECK_THROWS(cmdLine.add("--", foo, "SDF"));
    CHECK_THROWS(cmdLine.add("-foo", foo, "SDF"));

    std::vector<std::string> vals;
    cmdLine.setPositional(vals, "vals");
    CHECK_THROWS(cmdLine.setPositional(vals, "vals2"));

    CHECK_THROWS(cmdLine.parse(std::string_view()));
}
#endif

TEST_CASE("Test CommandLine -- user errors") {
    std::optional<int32_t> foo;
    std::optional<double> bar;
    std::optional<bool> frob;
    std::vector<std::string> multi;

    CommandLine cmdLine;
    cmdLine.add("--foo", foo, "");
    cmdLine.add("--bar", bar, "");
    cmdLine.add("--frob", frob, "");
    cmdLine.add("-m,+multi", multi, "SDF");

    CHECK(!cmdLine.parse("prog --foo \"\" --foo 123f4 --bar \"\" --bar 123.45g "
                         "--frob=asdf --foo 1 --foo 2 asdf -D --frib --bar"));

    auto errors = cmdLine.getErrors();
    REQUIRE(errors.size() == 9);
    CHECK(errors[0] == "prog: expected value for argument '--foo'"s);
    CHECK(errors[1] == "prog: invalid value '123f4' for integer argument '--foo'"s);
    CHECK(errors[2] == "prog: expected value for argument '--bar'"s);
    CHECK(errors[3] == "prog: invalid value '123.45g' for float argument '--bar'"s);
    CHECK(errors[4] == "prog: invalid value 'asdf' for boolean argument '--frob=asdf'"s);
    CHECK(errors[5] == "prog: more than one value provided for argument '--foo'"s);
    CHECK(errors[6] == "prog: unknown command line argument '-D'"s);
    CHECK(errors[7] == "prog: unknown command line argument '--frib', did you mean '--frob'?"s);
    CHECK(errors[8] == "prog: no value provided for argument '--bar'"s);
}

TEST_CASE("Test CommandLine -- grouping") {
    std::optional<bool> a;
    std::optional<bool> b;
    std::optional<std::string> foo;

    CommandLine cmdLine;
    cmdLine.add("-a", a, "");
    cmdLine.add("-b", b, "");
    cmdLine.add("-c", foo, "");

    CHECK(cmdLine.parse("prog -abcasdf"));

    CHECK(a == true);
    CHECK(b == true);
    CHECK(foo == "asdf");
}

TEST_CASE("Test CommandLine -- grouping with space") {
    std::optional<bool> a;
    std::optional<bool> b;
    std::optional<std::string> foo;

    CommandLine cmdLine;
    cmdLine.add("-a", a, "");
    cmdLine.add("-b", b, "");
    cmdLine.add("-c", foo, "");

    CHECK(cmdLine.parse("prog -abc asdf"));

    CHECK(a == true);
    CHECK(b == true);
    CHECK(foo == "asdf");
}

TEST_CASE("Test CommandLine -- grouping with equals") {
    std::optional<bool> a;
    std::optional<bool> b;
    std::optional<std::string> foo;

    CommandLine cmdLine;
    cmdLine.add("-a", a, "");
    cmdLine.add("-b", b, "");
    cmdLine.add("-c", foo, "");

    CHECK(cmdLine.parse("prog -abc=asdf"));

    CHECK(a == true);
    CHECK(b == true);
    CHECK(foo == "asdf");
}

TEST_CASE("Test CommandLine -- grouping no value") {
    std::optional<bool> a;
    std::optional<bool> b;
    std::optional<bool> c;

    CommandLine cmdLine;
    cmdLine.add("-a", a, "");
    cmdLine.add("-b", b, "");
    cmdLine.add("-c", c, "");

    CHECK(cmdLine.parse("prog -abc"));

    CHECK(a == true);
    CHECK(b == true);
    CHECK(c == true);
}

TEST_CASE("Test CommandLine -- grouping error") {
    std::optional<bool> a;
    std::optional<std::string> foo;

    CommandLine cmdLine;
    cmdLine.add("-a", a, "");
    cmdLine.add("-c", foo, "");

    CHECK(!cmdLine.parse("prog -abc"));

    auto errors = cmdLine.getErrors();
    REQUIRE(errors.size() == 1);
    CHECK(errors[0] == "prog: unknown command line argument '-abc', did you mean '-a'?"s);
}

TEST_CASE("Test CommandLine -- grouping trailing error") {
    std::optional<bool> a;
    std::optional<bool> b;
    std::optional<std::string> foo;

    CommandLine cmdLine;
    cmdLine.add("-a", a, "");
    cmdLine.add("-b", b, "");
    cmdLine.add("-c", foo, "");

    CHECK(!cmdLine.parse("prog -abc"));

    auto errors = cmdLine.getErrors();
    REQUIRE(errors.size() == 1);
    CHECK(errors[0] == "prog: no value provided for argument 'c'"s);
}

TEST_CASE("Test CommandLine -- nearest match tests") {
    std::optional<std::string> foo;

    CommandLine cmdLine;
    cmdLine.add("--foo", foo, "");

    CHECK(!cmdLine.parse("prog --asdfasdf=asdfasdf --fooey asdf"));

    auto errors = cmdLine.getErrors();
    REQUIRE(errors.size() == 2);
    CHECK(errors[0] == "prog: unknown command line argument '--asdfasdf=asdfasdf'"s);
    CHECK(errors[1] == "prog: unknown command line argument '--fooey', did you mean '--foo'?"s);
}

TEST_CASE("Test CommandLine -- positional not allowed") {
    std::optional<std::string> foo;

    CommandLine cmdLine;
    cmdLine.add("--foo", foo, "");

    CHECK(!cmdLine.parse("prog asdf baz bar"));

    auto errors = cmdLine.getErrors();
    REQUIRE(errors.size() == 1);
    CHECK(errors[0] == "prog: positional arguments are not allowed (see e.g. 'asdf')"s);
}

TEST_CASE("Test CommandLine -- plusarg errors") {
    std::optional<bool> flag;
    std::optional<std::string> foo;
    std::optional<double> num;

    CommandLine cmdLine;
    cmdLine.add("+flag", flag, "");
    cmdLine.add("+foo", foo, "");
    cmdLine.add("+num", num, "");

    CHECK(!cmdLine.parse("prog +unknown+asdf +foo +flag +num+asdf"));

    auto errors = cmdLine.getErrors();
    REQUIRE(errors.size() == 3);
    CHECK(errors[0] == "prog: unknown command line argument '+unknown'"s);
    CHECK(errors[1] == "prog: no value provided for argument '+foo'"s);
    CHECK(errors[2] == "prog: invalid value 'asdf' for float argument '+num'"s);
}

TEST_CASE("Test CommandLine -- file names") {
    std::optional<std::string> foo;

    CommandLine cmdLine;
    cmdLine.add("+foo", foo, "", "", CommandLineFlags::FilePath);

    CHECK(cmdLine.parse("prog +foo+../something/bar/baz"));

    CHECK(fs::path(*foo).is_absolute());
}

TEST_CASE("Test CommandLine -- ignore duplicates") {
    std::optional<int32_t> foo;

    CommandLine cmdLine;
    cmdLine.add("--foo", foo, "");

    CommandLine::ParseOptions options;
    options.ignoreDuplicates = true;

    CHECK(cmdLine.parse("prog --foo 123 --foo 456", options));

    CHECK(foo == 123);
}

TEST_CASE("Test CommandLine -- check setIgnoreCommand()") {
    std::optional<int32_t> foo;

    CommandLine cmdLine;
    cmdLine.add("--foo", foo, "");
    cmdLine.addIgnoreCommand("--xxx,0");
    cmdLine.addIgnoreCommand("--yyy,2");
    cmdLine.addIgnoreCommand("+zzz,0");
    cmdLine.addIgnoreCommand("-baz,0");

    CHECK(cmdLine.parse("prog --yyy --foo 456 --foo 123 --xxx +zzz+123+abc+456 -baz=blah"));
    // --foo 456 is skipped because it's not a real flag, it's --yyy's two parameters,
    // which are ignored
    CHECK(foo == 123);

    auto errors = cmdLine.getErrors();
    REQUIRE(errors.empty());
}

TEST_CASE("Test CommandLine -- check setRenameCommand()") {
    std::optional<int32_t> foo;
    std::optional<int32_t> bar;

    CommandLine cmdLine;
    cmdLine.add("--foo", foo, "");
    cmdLine.add("--bar", bar, "");
    cmdLine.addRenameCommand("--xxx,--foo");
    cmdLine.addRenameCommand("--yyy,--bar");

    CHECK(cmdLine.parse("prog --xxx 123 --yyy=456"));
    CHECK(foo == 123);
    CHECK(bar == 456);

    auto errors = cmdLine.getErrors();
    REQUIRE(errors.empty());
}

TEST_CASE("Test CommandLine -- ignore and rename errors") {
    CommandLine cmdLine;
    CHECK(cmdLine.addRenameCommand("--xxx").find("missing or extra comma") != std::string::npos);
    CHECK(cmdLine.addIgnoreCommand("--yyy,--bar,baz").find("missing or extra comma") !=
          std::string::npos);
}

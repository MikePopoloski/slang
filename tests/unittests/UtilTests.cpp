#include "Test.h"

#include "slang/util/CommandLine.h"

TEST_CASE("Test CommandLine -- basic") {
    optional<bool> a, b, longFlag, longFlag2;
    optional<std::string> c;
    optional<int32_t> d;
    optional<uint64_t> ext;
    optional<double> ext2;
    optional<uint32_t> unused1;
    optional<int64_t> unused2;
    optional<uint32_t> used1;
    optional<int64_t> used2;
    std::vector<std::string> vals;

    CommandLine cmdLine;
    cmdLine.add("-a", a, "SDF");
    cmdLine.add("-b", b, "SDF");
    cmdLine.add("-z,-y,-x,--longFlag", longFlag, "This flag does fun stuff");
    cmdLine.add("--longFlag2", longFlag2, "Another good thing");
    cmdLine.add("-c", c, "SDF");
    cmdLine.add("-d", d, "SDF");
    cmdLine.add("-e,--ext", ext, "Definitely should set me");
    cmdLine.add("-f,--ext2", ext2, "Me too!", "<value>");
    cmdLine.add("--biz,--baz", unused1, "SDF", "<entry>");
    cmdLine.add("--buz,--boz", unused2, "SDF", "=<val>");
    cmdLine.add("--fiz,--faz", used1, "SDF");
    cmdLine.add("--fuz,--foz", used2, "SDF");
    cmdLine.setPositional(vals, "vals");

    CHECK(cmdLine.parse("prog -a -b --longFlag=False pos1 pos2 -c asdf -d -1234 --ext=9876 "
                        "--ext2 9999.1234e12 pos3 --fiz=4321 --foz=-4321    - pos5 "
                        "--longFlag2=true -- --buz --boz"sv));

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
    CHECK(used1 == 4321);
    CHECK(used2 == -4321);

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
  --longFlag2          Another good thing
  -c                   SDF
  -d                   SDF
  -e,--ext             Definitely should set me
  -f,--ext2 <value>    Me too!
  --biz,--baz <entry>  SDF
  --buz,--boz=<val>    SDF
  --fiz,--faz          SDF
  --fuz,--foz          SDF
)");
}

TEST_CASE("Test CommandLine -- nonspan") {
    optional<bool> a;
    CommandLine cmdLine;
    cmdLine.add("-a", a, "SDF");

    std::array args = { "prog", "-a" };
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

    CHECK(groupa == std::vector<int32_t>{ 1, 99 });
    CHECK(groupb == std::vector<int64_t>{ -42ll, -43ll });
    CHECK(groupc == std::vector<uint32_t>{ 8u, 9u });
    CHECK(groupd == std::vector<uint64_t>{ 5ull, 5ull, 5ull });
    CHECK(groupe == std::vector{ 4.1 });
    CHECK(groupf == std::vector{ "fff"s, "ffff"s });
}

TEST_CASE("Test CommandLine -- splitting") {
    std::vector<std::string> stuff;

    CommandLine cmdLine;
    cmdLine.add("-a,--longa", stuff, "SDF", "val");

    auto args = R"(prog -a \ -a \-a asdf '--longa=bar baz bif \' -a "f foo \" biz \\" -a 1)"sv;
    CHECK(cmdLine.parse(args));

    CHECK(stuff == std::vector{ " -a"s, "asdf"s, "bar baz bif \\"s, "f foo \" biz \\"s, "1"s });
}

TEST_CASE("Test CommandLine -- programmer errors") {
    optional<bool> foo;

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

    CHECK_THROWS(cmdLine.parse(string_view()));
}

TEST_CASE("Test CommandLine -- user errors") {
    optional<int32_t> foo;
    optional<double> bar;
    optional<bool> frob;

    CommandLine cmdLine;
    cmdLine.add("--foo", foo, "");
    cmdLine.add("--bar", bar, "");
    cmdLine.add("--frob", frob, "");

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
    optional<bool> a;
    optional<bool> b;
    optional<std::string> foo;

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
    optional<bool> a;
    optional<bool> b;
    optional<std::string> foo;

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
    optional<bool> a;
    optional<bool> b;
    optional<std::string> foo;

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
    optional<bool> a;
    optional<bool> b;
    optional<bool> c;

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
    optional<bool> a;
    optional<bool> b;
    optional<std::string> foo;

    CommandLine cmdLine;
    cmdLine.add("-a", a, "");
    cmdLine.add("-c", foo, "");

    CHECK(!cmdLine.parse("prog -abc"));

    auto errors = cmdLine.getErrors();
    REQUIRE(errors.size() == 1);
    CHECK(errors[0] == "prog: unknown command line argument '-abc', did you mean '-a'?"s);
}

TEST_CASE("Test CommandLine -- grouping trailing error") {
    optional<bool> a;
    optional<bool> b;
    optional<std::string> foo;

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
    optional<std::string> foo;

    CommandLine cmdLine;
    cmdLine.add("--foo", foo, "");

    CHECK(!cmdLine.parse("prog --asdfasdf=asdfasdf --fooey asdf"));

    auto errors = cmdLine.getErrors();
    REQUIRE(errors.size() == 2);
    CHECK(errors[0] == "prog: unknown command line argument '--asdfasdf=asdfasdf'"s);
    CHECK(errors[1] == "prog: unknown command line argument '--fooey', did you mean '--foo'?"s);
}

TEST_CASE("Test CommandLine -- positional not allowed") {
    optional<std::string> foo;

    CommandLine cmdLine;
    cmdLine.add("--foo", foo, "");

    CHECK(!cmdLine.parse("prog asdf baz bar"));

    auto errors = cmdLine.getErrors();
    REQUIRE(errors.size() == 1);
    CHECK(errors[0] == "prog: positional arguments are not allowed (see e.g. 'asdf')"s);
}
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyConfigPrinter.h"
#include "TidyFactory.h"
#include <filesystem>
#include <fstream>
#include <iostream>
#include <iterator>
#include <string>

#include "slang/util/OS.h"

bool filesEqual(const std::string& file1, const std::string& file2) {
    std::ifstream f1(file1, std::ios::binary);
    std::ifstream f2(file2, std::ios::binary);

    if (!f1.is_open() || !f2.is_open()) {
        std::cerr << "Error opening one of the files.\n";
        return false;
    }

    std::istreambuf_iterator<char> begin1(f1);
    std::istreambuf_iterator<char> begin2(f2);
    std::istreambuf_iterator<char> end;

    return std::equal(begin1, end, begin2);
}

TEST_CASE("Round trip config file") {

    std::error_code ec;
    auto p = fs::temp_directory_path(ec);
    fs::current_path(p, ec);

    TidyConfig config;
    OS::writeFile("tidy-config1", TidyConfigPrinter::dumpConfig(config).str());

    auto newConfig = TidyConfigParser(std::filesystem::path("tidy-config1")).getConfig();
    OS::writeFile("tidy-config2", TidyConfigPrinter::dumpConfig(newConfig).str());

    CHECK(filesEqual("tidy-config1", "tidy-config2"));
}

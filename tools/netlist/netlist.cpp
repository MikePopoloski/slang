//------------------------------------------------------------------------------
//! @file netlist.cpp
//! @brief The slang netlist tool
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include "fmt/color.h"
#include "fmt/format.h"
#include <unordered_set>
#include <fstream>
#include <iostream>
#include <utility>
#include <vector>

#include "slang/ast/ASTSerializer.h"
#include "slang/driver/Driver.h"
#include "slang/text/Json.h"
#include "slang/util/TimeTrace.h"
#include "slang/util/Version.h"
#include "slang/util/Util.h"
#include "slang/text/FormatBuffer.h"

#include "Netlist.h"
#include "NetlistVisitor.h"
#include "SplitVariables.h"

using namespace slang;
using namespace slang::ast;
using namespace slang::driver;
using namespace netlist;

void writeToFile(std::string_view fileName, std::string_view contents);

void printJson(Compilation& compilation, const std::string& fileName,
               const std::vector<std::string>& scopes) {
    JsonWriter writer;
    writer.setPrettyPrint(true);
    ASTSerializer serializer(compilation, writer);
    if (scopes.empty()) {
      serializer.serialize(compilation.getRoot());
    } else {
      for (auto& scopeName : scopes) {
        auto sym = compilation.getRoot().lookupName(scopeName);
        if (sym) {
          serializer.serialize(*sym);
        }
      }
    }
    writeToFile(fileName, writer.view());
}

void printDOT(const Netlist &netlist, const std::string &fileName) {
  slang::FormatBuffer buffer;
  buffer.append("digraph {\n");
  for (auto &node : netlist) {
    buffer.format("  N{} [label=\"{}\",shape=circle]\n", node->ID, node->toString());
  }
  for (auto &node : netlist) {
    for (auto &edge : node->getEdges()) {
      buffer.format("  N{} -> N{}\n", node->ID, edge->getTargetNode().ID);
    }
  }
  buffer.append("}\n");
  writeToFile(fileName, std::string_view(buffer.data()));
}

template<typename Stream, typename String>
void writeToFile(Stream& os, std::string_view fileName, String contents) {
  os.write(contents.data(), contents.size());
  os.flush();
  if (!os) {
    throw std::runtime_error(fmt::format("Unable to write AST to '{}'", fileName));
  }
}

void writeToFile(std::string_view fileName, std::string_view contents) {
  if (fileName == "-") {
    writeToFile(std::cout, "stdout", contents);
  } else {
    std::ofstream file{std::string(fileName)};
    writeToFile(file, fileName, contents);
  }
}

int main(int argc, char** argv) {

  driver::Driver driver;
  driver.addStandardArgs();

  std::optional<bool> showHelp;
  std::optional<bool> showVersion;
  std::optional<bool> quiet;
  std::optional<bool> debug;
  driver.cmdLine.add("-h,--help", showHelp, "Display available options");
  driver.cmdLine.add("--version", showVersion, "Display version information and exit");
  driver.cmdLine.add("-q,--quiet", quiet, "Suppress non-essential output");
  driver.cmdLine.add("-d,--debug", debug, "Output debugging information");

  std::optional<std::string> astJsonFile;
  driver.cmdLine.add("--ast-json", astJsonFile,
                     "Dump the compiled AST in JSON format to the specified file, or '-' for stdout", "<file>",
                     /* isFileName */ true);

  std::vector<std::string> astJsonScopes;
  driver.cmdLine.add("--ast-json-scope", astJsonScopes,
                     "When dumping AST to JSON, include only the scopes specified by the "
                     "given hierarchical paths",
                     "<path>");

  std::optional<std::string> netlistDotFile;
  driver.cmdLine.add("--netlist-dot", netlistDotFile,
                     "Dump the netlist in DOT format to the specified file, or '-' for stdout", "<file>",
                     /* isFileName */ true);

  if (!driver.parseCommandLine(argc, argv)) {
    return 1;
  }

  if (showHelp == true) {
    printf("%s\n", driver.cmdLine.getHelpText("slang SystemVerilog compiler").c_str());
    return 0;
  }

  if (showVersion == true) {
    printf("slang version %d.%d.%d+%s\n", VersionInfo::getMajor(),
        VersionInfo::getMinor(), VersionInfo::getPatch(),
        std::string(VersionInfo::getHash()).c_str());
    return 0;
  }

  if (!driver.processOptions()) {
    return 2;
  }

  if (debug) {
    Config::getInstance().debugEnabled = true;
  }

  try {

    bool ok = driver.parseAllSources();

    auto compilation = driver.createCompilation();
    ok &= driver.reportCompilation(*compilation, quiet == true);

    if (!ok) {
      return ok;
    }

    if (astJsonFile) {
      printJson(*compilation, *astJsonFile, astJsonScopes);
      return 0;
    }

    // Create the netlist by traversing the AST.
    Netlist netlist;
    NetlistVisitor visitor(*compilation, netlist);
    compilation->getRoot().visit(visitor);
    SplitVariables splitVariables(netlist);
    std::cout << fmt::format("Netlist has {} nodes and {} edges\n",
                             netlist.numNodes(), netlist.numEdges());

    if (netlistDotFile) {
      printDOT(netlist, *netlistDotFile);
      return 0;
    }

  } catch (const std::exception& e) {
    OS::printE(fmt::format("{}\n", e.what()));
    return 3;
  }

  return 0;
}

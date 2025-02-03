# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

import sys

from pyslang import CommandLineOptions, Driver


def main():
    """Reads a list of files as command line arguments and parses them using the slang driver.

    After compilation/elaboration, any diagnostics (e.g., syntax errors) are reported to the console.
    Writes to both stderr and stdout.
    """
    # Create a slang driver with default command line arguments
    driver = Driver()
    driver.addStandardArgs()

    # Parse command line arguments
    args = " ".join(sys.argv)
    if not driver.parseCommandLine(args, CommandLineOptions()):
        return

    # Process options and parse all provided sources
    if not driver.processOptions() or not driver.parseAllSources():
        return

    # Perform elaboration and report all diagnostics
    compilation = driver.createCompilation()
    driver.reportCompilation(compilation, quiet=False)


if __name__ == "__main__":
    main()

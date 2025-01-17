import sys

from pyslang import *


def main():
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
    driver.reportCompilation(compilation, False)


if __name__ == "__main__":
    main()

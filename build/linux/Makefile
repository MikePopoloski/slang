TOP:=../..
OUTDIR:=$(TOP)/bin/linux

CXX?=clang++-3.9
CXXFLAGS?=-std=c++1z -MMD -MP -g
INCLUDES:=-I$(TOP)/external -I$(TOP)/include -I./
AR?=llvm-ar-3.9
ARFLAGS?=rs

FMTLIB_SOURCES:=$(wildcard $(TOP)/external/fmt/*.cc)
SLANG_SOURCES:=$(wildcard $(TOP)/source/*.cpp) $(wildcard $(TOP)/external/ppk_assert/*.cpp)
UNITTEST_SOURCES:=$(wildcard $(TOP)/tests/unit_tests/*.cpp)
FILETEST_SOURCES:=$(wildcard $(TOP)/tests/file_tests/*.cpp)
REWRITER_SOURCES:=$(wildcard $(TOP)/tools/param_rewriter/*.cpp)
SHELL_SOURCES:=$(wildcard $(TOP)/tools/shell.cpp)

FMTLIB_OBJECTS:=$(patsubst $(TOP)/%.cc,obj/%.o,$(FMTLIB_SOURCES))
SLANG_OBJECTS:=$(patsubst $(TOP)/%.cpp,obj/%.o,$(SLANG_SOURCES))
UNITTEST_OBJECTS:=$(patsubst $(TOP)/%.cpp,obj/%.o,$(UNITTEST_SOURCES))
FILETEST_OBJECTS:=$(patsubst $(TOP)/%.cpp,obj/%.o,$(FILETEST_SOURCES))
REWRITER_OBJECTS:=$(patsubst $(TOP)/%.cpp,obj/%.o,$(REWRITER_SOURCES))
SHELL_OBJECTS:=$(patsubst $(TOP)/%.cpp,obj/%.o,$(SHELL_SOURCES))

ALL_CPP_OBJS:=$(SLANG_OBJECTS) $(UNITTEST_OBJECTS) $(FILETEST_OBJECTS) $(REWRITER_OBJECTS) $(SHELL_OBJECTS)
DEPS:=$(ALL_OBJECTS:.o=.d)

-include $(DEPS)

.PHONY: clean test all
.DEFAULT_GOAL := all

all: $(OUTDIR)/unittests $(OUTDIR)/filetests $(OUTDIR)/param_rewriter $(TOP)/bin/linux/shell

test: all
	cd $(TOP); ./bin/linux/unittests
	cd $(TOP); ./bin/linux/filetests

$(ALL_CPP_OBJS): obj/%.o: $(TOP)/%.cpp
	mkdir -p $(dir $@)
	$(CXX) $(CXXFLAGS) -c $< $(INCLUDES) -o $@

$(SHELL_OBJECTS): obj/%.o: $(TOP)/%.cpp
	mkdir -p $(dir $@)
	$(CXX) $(CXXFLAGS) -c $< $(INCLUDES) -o $@

$(FMTLIB_OBJECTS): obj/%.o: $(TOP)/%.cc
	mkdir -p $(dir $@)
	$(CXX) $(CXXFLAGS) -c $< $(INCLUDES) -o $@

$(OUTDIR)/libslang.a: $(FMTLIB_OBJECTS) $(SLANG_OBJECTS)
	mkdir -p $(dir $@)
	$(AR) $(ARFLAGS) $@ $^

$(OUTDIR)/unittests: $(UNITTEST_OBJECTS) $(OUTDIR)/libslang.a
	$(CXX) $(CXXFLAGS) $^ $(INCLUDES) -o $@

$(OUTDIR)/filetests: $(FILETEST_OBJECTS) $(OUTDIR)/libslang.a
	$(CXX) $(CXXFLAGS) $^ $(INCLUDES) -o $@

$(OUTDIR)/param_rewriter: $(REWRITER_OBJECTS) $(OUTDIR)/libslang.a
	$(CXX) $(CXXFLAGS) $^ $(INCLUDES) -o $@

$(TOP)/bin/linux/shell: $(SHELL_OBJECTS) $(TOP)/bin/linux/libslang.a
	$(CXX) $(CXXFLAGS) $^ $(INCLUDES) -o $@ -lncurses -ledit

clean:
	rm -f $(ALL_OBJECTS)
	rm -f $(OUTDIR)/unittests $(OUTDIR)/filetests $(OUTDIR)/param_rewriter $(TOP)/bin/linux/shell

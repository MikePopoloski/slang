TOP:=../..

CXX?=clang++-3.9
CXXFLAGS?=-std=c++1z -MMD -MP -g
INCLUDES:=-I$(TOP)/external -I$(TOP)/include -I./
AR?=llvm-ar-3.9
ARFLAGS?=rs

FMTLIB_SOURCES:=$(wildcard $(TOP)/external/fmt/*.cc)
SLANG_SOURCES:=$(wildcard $(TOP)/source/*.cpp) $(wildcard $(TOP)/external/ppk_assert/*.cpp)
UNITTEST_SOURCES:=$(wildcard $(TOP)/tests/unit_tests/*.cpp)
FILETEST_SOURCES:=$(wildcard $(TOP)/tests/file_tests/*.cpp)

FMTLIB_OBJECTS:=$(patsubst $(TOP)/%.cc,obj/%.o,$(FMTLIB_SOURCES))
SLANG_OBJECTS:=$(patsubst $(TOP)/%.cpp,obj/%.o,$(SLANG_SOURCES))
UNITTEST_OBJECTS:=$(patsubst $(TOP)/%.cpp,obj/%.o,$(UNITTEST_SOURCES))
FILETEST_OBJECTS:=$(patsubst $(TOP)/%.cpp,obj/%.o,$(FILETEST_SOURCES))

ALL_OBJECTS:=$(FMTLIB_OBJECTS) $(SLANG_OBJECTS) $(UNITTEST_OBJECTS) $(FILETEST_OBJECTS)
DEPS:=$(ALL_OBJECTS:.o=.d)

-include $(DEPS)

$(SLANG_OBJECTS): obj/%.o: $(TOP)/%.cpp
	mkdir -p $(dir $@)
	$(CXX) $(CXXFLAGS) -c $< $(INCLUDES) -o $@

$(UNITTEST_OBJECTS): obj/%.o: $(TOP)/%.cpp
	mkdir -p $(dir $@)
	$(CXX) $(CXXFLAGS) -c $< $(INCLUDES) -o $@

$(FILETEST_OBJECTS): obj/%.o: $(TOP)/%.cpp
	mkdir -p $(dir $@)
	$(CXX) $(CXXFLAGS) -c $< $(INCLUDES) -o $@

$(FMTLIB_OBJECTS): obj/%.o: $(TOP)/%.cc
	mkdir -p $(dir $@)
	$(CXX) $(CXXFLAGS) -c $< $(INCLUDES) -o $@

$(TOP)/bin/linux/libslang.a: $(FMTLIB_OBJECTS) $(SLANG_OBJECTS)
	mkdir -p $(dir $@)
	$(AR) $(ARFLAGS) $@ $^

$(TOP)/bin/linux/unittests: $(UNITTEST_OBJECTS) $(TOP)/bin/linux/libslang.a
	$(CXX) $(CXXFLAGS) $^ $(INCLUDES) -o $@

$(TOP)/bin/linux/filetests: $(FILETEST_OBJECTS) $(TOP)/bin/linux/libslang.a
	$(CXX) $(CXXFLAGS) $^ $(INCLUDES) -o $@

clean:
	rm -f $(ALL_OBJECTS)
	rm -f $(TOP)/bin/linux/unittests $(TOP)/bin/linux/filetests

.PHONY: clean
.DEFAULT_GOAL:= $(TOP)/bin/linux/unittests $(TOP)/bin/linux/filetests

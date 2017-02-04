TOP:=../..
CXX?=clang++-3.9
CXXFLAGS:=-std=c++1z -MMD -MP
INCLUDES:=-I$(TOP)/external -I$(TOP)/include -I./
ARFLAGS:=-rs

FMTLIB_SOURCES:=$(wildcard $(TOP)/external/fmt/*.cc)
SLANG_SOURCES:=$(wildcard $(TOP)/source/*.cpp) $(wildcard $(TOP)/external/ppk_assert/*.cpp)
UNITTEST_SOURCES:=$(wildcard $(TOP)/tests/unit_tests/*.cpp)

FMTLIB_OBJECTS:=$(patsubst $(TOP)/%.cc,obj/%.o,$(FMTLIB_SOURCES))
SLANG_OBJECTS:=$(patsubst $(TOP)/%.cpp,obj/%.o,$(SLANG_SOURCES))
UNITTEST_OBJECTS:=$(patsubst $(TOP)/%.cpp,obj/%.o,$(UNITTEST_SOURCES))

ALL_OBJECTS:=$(FMTLIB_OBJECTS) $(SLANG_OBJECTS) $(UNITTEST_OBJECTS)
DEPS:=$(ALL_OBJECTS:.o=.d)

-include $(DEPS)

$(SLANG_OBJECTS): obj/%.o: $(TOP)/%.cpp
	mkdir -p $(dir $@)
	$(CXX) $(CXXFLAGS) -c $< $(INCLUDES) -o $@

$(UNITTEST_OBJECTS): obj/%.o: $(TOP)/%.cpp
	mkdir -p $(dir $@)
	$(CXX) $(CXXFLAGS) -c $< $(INCLUDES) -o $@

$(FMTLIB_OBJECTS): obj/%.o: $(TOP)/%.cc
	mkdir -p $(dir $@)
	$(CXX) $(CXXFLAGS) -c $< $(INCLUDES) -o $@

$(TOP)/bin/linux/libslang.a: $(FMTLIB_OBJECTS) $(SLANG_OBJECTS) | $(TOP)/bin/linux
	mkdir -p $(dir $@)
	ar $(ARFLAGS) $@ $^

$(TOP)/bin/linux/unittests: $(UNITTEST_OBJECTS) $(TOP)/bin/linux/libslang.a
	$(CXX) $(CXXFLAGS) $^ $(INCLUDES) -o $@

clean:
	rm -r obj
	rm -r $(TOP)/bin/linux

.PHONY: clean
.DEFAULT_GOAL:= $(TOP)/bin/linux/unittests
TOP:=../..
CXX=clang++-3.9
CXXFLAGS:=-std=c++1z -MMD -MP
INCLUDES:=-I$(TOP)/external -I$(TOP)/include -I./
ARFLAGS:=-rs

SOURCES:=$(wildcard $(TOP)/source/*.cpp) $(wildcard $(TOP)/external/ppk_assert/*.cpp) $(wildcard $(TOP)/external/fmt/*.cc)
CPP_OBJECTS:=$(patsubst $(TOP)/%.cpp,obj/%.o,$(filter %.cpp,$(SOURCES)))
CC_OBJECTS:=$(patsubst $(TOP)/%.cc,obj/%.o,$(filter %.cc,$(SOURCES)))
OBJECTS:=$(CPP_OBJECTS) $(CC_OBJECTS)
DEPS:=$(OBJECTS:.o=.d)

-include $(DEPS)

$(TOP)/bin/linux/libslang.a: $(OBJECTS) | $(TOP)/bin/linux
	ar $(ARFLAGS) $@ $^

$(CPP_OBJECTS): obj/%.o: $(TOP)/%.cpp
	mkdir -p $(dir $@)
	$(CXX) $(CXXFLAGS) -c $< $(INCLUDES) -o $@

$(CC_OBJECTS): obj/%.o: $(TOP)/%.cc
	mkdir -p $(dir $@)
	$(CXX) $(CXXFLAGS) -c $< $(INCLUDES) -o $@

$(TOP)/bin/linux:
	mkdir -p $@

clean:
	rm -r obj
	rm -r $(TOP)/bin/linux

.PHONY: clean
.DEFAULT_GOAL:= $(TOP)/bin/linux/libslang.a
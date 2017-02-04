TOP:=../..
CXX=clang++-3.9
CXXFLAGS:=-std=c++1z -MMD -MP
INCLUDES:=-I$(TOP)/external -I$(TOP)/include -I./
ARFLAGS:=-rvs

SOURCES:=$(wildcard $(TOP)/source/*.cpp) $(wildcard $(TOP)/external/ppk_assert/*.cpp) $(wildcard $(TOP)/external/fmt/*.cc)
SOURCES_CPP:=$(SOURCES:.cc=.cpp)
OBJECTS:=$(patsubst $(TOP)/%,obj/%,$(SOURCES_CPP:%.cpp=%.o))
DEPS:=$(OBJECTS:.o=.d)

-include $(DEPS)

$(TOP)/bin/linux/libslang.a: $(OBJECTS) | $(TOP)/bin/linux
	ar $(ARFLAGS) $@ $^

$(OBJECTS): obj/%.o: $(TOP)/%.cpp
	mkdir -p $(dir $@)
	$(CXX) $(CXXFLAGS) -c $< $(INCLUDES) -o $@

$(TOP)/bin/linux:
	mkdir -p $@

clean:
	rm -r obj
	rm -r $(TOP)/bin/linux

.PHONY: clean
.DEFAULT_GOAL:= $(TOP)/bin/linux/libslang.a
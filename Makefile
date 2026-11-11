CXX ?= g++
CXXFLAGS ?= -std=c++14 -O3 -DNDEBUG -flto -flto-partition=one -Wall -Wextra
CPPFLAGS += -MMD -MP
LDFLAGS ?= -flto -flto-partition=one

TARGET := ARC_SCS
SRCS := main.cpp Graph.cpp ARCSCSSolver.cpp CapacitySearch.cpp Index/OfflineIndex.cpp Index/IndexBuilder.cpp HeuristicSearch.cpp AdaptiveReduction.cpp
OBJS := $(SRCS:.cpp=.o)
DEPS := $(OBJS:.o=.d)

.DEFAULT_GOAL := all
.PHONY: all graph-tool check clean
all: $(TARGET)
graph-tool: tools/graph_tool
check: all graph-tool
	python3 tests/smoke.py

$(TARGET): $(OBJS)
	$(CXX) $(LDFLAGS) -o $@ $^
%.o: %.cpp
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) -c $< -o $@
tools/graph_tool: tools/graph_tool.cpp
	$(CXX) -std=c++14 -O3 -Wall -Wextra -Wpedantic $< -o $@
clean:
	rm -f $(OBJS) $(DEPS) $(TARGET) tools/graph_tool

-include $(DEPS)

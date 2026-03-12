CXX=g++

TBUDDY_DIR := tbuddy
TBUDDY_LIB := $(TBUDDY_DIR)/tbuddy.a
CADICAL_DIR := cadical
CADICAL_BUILD_DIR := $(CADICAL_DIR)/build
CADICAL_BUILD_MAKEFILE := $(CADICAL_BUILD_DIR)/makefile
CADICAL_LIB := $(CADICAL_BUILD_DIR)/libcadical.a
CADICAL_SOURCES := $(wildcard $(CADICAL_DIR)/src/*.cpp $(CADICAL_DIR)/src/*.hpp $(CADICAL_DIR)/contrib/*.cpp $(CADICAL_DIR)/contrib/*.hpp)

# Set DEBUG=1 for debug build, DEBUG=0 for release build
DEBUG=0

ifeq ($(DEBUG), 1)
    OPT = -O0
    CFLAGS=-g -fsanitize=address -fno-omit-frame-pointer $(OPT) -Wno-nullability-completeness $(DFLAGS)
    LDFLAGS = -L$(CADICAL_BUILD_DIR) -fsanitize=address
else
    OPT = -O2
    CFLAGS=-g $(OPT) -Wno-nullability-completeness $(DFLAGS)
    LDFLAGS = -L$(CADICAL_BUILD_DIR)
endif

CXXFLAGS=-std=c++11
INC = -I$(TBUDDY_DIR) -I$(CADICAL_DIR)/src
LIB = $(TBUDDY_LIB)
LIBS = -lcadical

OBJECTS = cnf2knf.o parse.o sat_simulation.o bdd_analyze.o

all: cnf2knf

cnf2knf: $(OBJECTS) $(LIB) $(CADICAL_LIB)
	$(CXX) $(CFLAGS) $(OBJECTS) -o cnf2knf $(LIB) $(LDFLAGS) $(LIBS)

$(TBUDDY_LIB): FORCE
	$(MAKE) -C $(TBUDDY_DIR) tbuddy.a

$(CADICAL_BUILD_MAKEFILE):
	cd $(CADICAL_DIR) && ./configure

$(CADICAL_LIB): $(CADICAL_BUILD_MAKEFILE) $(CADICAL_SOURCES)
	$(MAKE) -C $(CADICAL_BUILD_DIR) libcadical.a

FORCE:

# Auto-generate header dependencies
%.o: %.cpp
	$(CXX) $(CFLAGS) $(CXXFLAGS) $(INC) -MMD -MP -c $< -o $@

# Include the dependency files
-include $(OBJECTS:.o=.d)

clean:
	rm -f cnf2knf $(OBJECTS) $(OBJECTS:.o=.d)
	rm -f *~
	$(MAKE) -C $(TBUDDY_DIR) clean
	$(MAKE) -C $(CADICAL_DIR) clean

#
# Indicate where we are relative to the top of the source tree.
#
LEVEL=../../..

#
# Give the name of a library.  This will build a dynamic version.
#
LIBRARYNAME=CLRedundancy

#ifneq ($(OS),Cygwin)
#ifneq ($(OS),MingW)
SHARED_LIBRARY := 1
LOADABLE_MODULE := 1
#endif
#endif

USEDLIBS = Search.a SFReach.a CFGUtility.a Invariant.a Dependence.a ID.a LiveAnalysis.a Utility.a Config.a LinkList.a Array.a Loop.a SEWrapper.a

#
# Include Makefile.common so we know what to do.
#
include $(LEVEL)/Makefile.common

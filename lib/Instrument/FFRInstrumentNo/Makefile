
#
# Indicate where we are relative to the top of the source tree.
#
LEVEL=../../..

#
# Give the name of a library.  This will build a dynamic version.
#
LIBRARYNAME=FFRInstrumentNo

#ifneq ($(OS),Cygwin)
#ifneq ($(OS),MingW)
SHARED_LIBRARY := 1
LOADABLE_MODULE := 1
#endif
#endif

USEDLIBS = Search.a Utility.a Config.a Clone.a

#
# Include Makefile.common so we know what to do.
#
include $(LEVEL)/Makefile.common

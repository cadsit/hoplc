#
# File:   Makefile
# Author: Connor Adsit
# Date:   2015-01-28
#


.PHONY: all lang comp interp
all: lang comp interp

lang:
	$(MAKE) -C lang-src/ all 

comp:
	$(MAKE) -C comp-src all 

interp:
	$(MAKE) -C interp-src all 

.PHONY: clean clean-lang clean-comp clean-interp
clean: clean-lang clean-comp clean-interp

clean-lang:
	$(MAKE) -C lang-src/ clean

clean-comp:
	$(MAKE) -C comp-src/ clean

clean-interp:
	$(MAKE) -C interp-src/ clean

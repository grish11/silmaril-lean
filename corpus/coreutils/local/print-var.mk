# local/print-var.mk -- repository-authored helper (ours). Why: build.sh builds only seven programs
# (`make src/true ...`), but automake builds $(BUILT_SOURCES) (generated headers such as lib/stdio.h,
# src/version.h) only for `make all`; this lets build.sh ask the generated Makefile for that list:
#   make -s -f Makefile -f print-var.mk print-BUILT_SOURCES
print-%:
	@echo $($*)

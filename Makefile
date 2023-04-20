# Using the example from https://coq.inria.fr/refman/practical-tools/utilities.html#reusing-extending-the-generated-makefile

# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile all sym_exa

# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: Makefile _CoqProject
	git submodule init
	git submodule update
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)

###########################################################
##		      Your targets here			 ##
###########################################################

QWIRE := src/com/QWIRE
reQWIRE := src/com

QIMP := src/sym


COQ_OPTS := -R . Top



# Built by 'make sym_exa'

# Using a custom clean target to remove files from subdirectories
#clean:
#	rm -rf CoqMakefile CoqMakefile.conf */*/*.vo* */*/*.glob */*/*.aux .lia.cache

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
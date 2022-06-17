# run "make -B" because caching botches running SoftType.v
FILES=Vector.v EVarsScratchwork.v Logic/V.v Logic/Term.v \
	SoftType/Radix.v SoftType/Attribute.v SoftType/Adjective.v \
	SoftType/SoftType.v SoftType/JudgementType.v SoftType/LocalContext.v SoftType/GlobalContext.v \
	SoftType.v \
	Logic/Predicate.v Logic/Formula.v Logic/Subcontext.v Logic.v VariadicQuantifiers.v \
	Translation.v

current_dir = $(shell pwd)

%.v: FORCE
	coqc "-topfile" "$(current_dir)/ST/$@" "-R" "$(current_dir)" "ST" "$(current_dir)/ST/$@"

all: $(FILES)

# In case you/I forget to include the "-B" flag, simply force the Makefile to re-check everything
FORCE: ;

clean:
	-rm ST/*.vo ST/*.vos ST/*.vok
	-rm ST/Logic/*.vo ST/Logic/*.vos ST/Logic/*.vok
	-rm ST/SoftType/*.vo ST/SoftType/*.vos ST/SoftType/*.vok
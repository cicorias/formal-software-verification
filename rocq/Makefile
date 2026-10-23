# Check the Rocq files:  make -C rocq
ROCQ ?= rocq
FILES = Basics.v Machine.v Exercises.v Solutions.v

all: $(FILES:.v=.vo)

%.vo: %.v
	$(ROCQ) compile -Q . Metal $<

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux .lia.cache

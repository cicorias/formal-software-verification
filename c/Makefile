# The C side of the course.
#
#   make asm         RISC-V assembly for every function (needs clang with the RISC-V target)
#   make fuzz        build the random-fuzzer binaries with AddressSanitizer (gcc or clang)
#   make demo        run them: watch what random testing finds, and what it misses
#   make libfuzzer   coverage-guided fuzzers (needs clang + libFuzzer runtime)
#
# The RISC-V flags are exactly the ones used to produce the programs in Metal/.

CC      ?= cc
CLANG   ?= clang
RVFLAGS  = --target=riscv32-unknown-elf -march=rv32i -mabi=ilp32 -O1 -S
FZFLAGS  = -g -O1 -fsanitize=address -fno-omit-frame-pointer
B        = build

.PHONY: all asm fuzz demo libfuzzer clean
all: asm fuzz

$(B):
	mkdir -p $(B)

asm: | $(B)
	for f in sum harness_buggy harness_fixed examples; do \
	  $(CLANG) $(RVFLAGS) $$f.c -o $(B)/$$f.s ; done
	@echo "--- harness_buggy.s vs harness_fixed.s (one instruction differs):"
	-diff $(B)/harness_buggy.s $(B)/harness_fixed.s | grep '^[<>]' | grep -v '\.file\|ident'

fuzz: | $(B)
	$(CC) $(FZFLAGS) harness_buggy.c fuzz_driver.c -o $(B)/fuzz_harness_buggy
	$(CC) $(FZFLAGS) harness_fixed.c fuzz_driver.c -o $(B)/fuzz_harness_fixed
	$(CC) $(FZFLAGS) -DRLE_BUG rle.c fuzz_driver.c -o $(B)/fuzz_rle_buggy
	$(CC) $(FZFLAGS) rle.c fuzz_driver.c -o $(B)/fuzz_rle_fixed

demo: fuzz
	@echo "== The off-by-one harness: random inputs find it almost immediately"
	-ASAN_OPTIONS=detect_leaks=0 ./$(B)/fuzz_harness_buggy 100000 16 2>&1 | grep -m2 -E 'ERROR|READ|no crash'
	@echo "== The fixed harness"
	./$(B)/fuzz_harness_fixed 100000 16
	@echo "== The RLE codec with the 256-run bug: random inputs never find it"
	./$(B)/fuzz_rle_buggy 200000 600 4
	@echo "== ...but one hand-picked input does (Stage 3's counterexample: 256 x 0x07)"
	head -c 256 /dev/zero | tr '\000' '\007' > $(B)/run256.bin
	-$(CC) $(FZFLAGS) -DRLE_BUG rle.c run_one.c -o $(B)/run_rle_buggy
	-ASAN_OPTIONS=detect_leaks=0 ./$(B)/run_rle_buggy $(B)/run256.bin 2>&1 | grep -m1 -E 'PROPERTY|ok:'

libfuzzer: | $(B)
	$(CLANG) -g -O1 -fsanitize=fuzzer,address harness_buggy.c -o $(B)/lf_harness_buggy
	$(CLANG) -g -O1 -fsanitize=fuzzer,address -DRLE_BUG rle.c -o $(B)/lf_rle_buggy
	@echo "run e.g.:  ./$(B)/lf_rle_buggy -max_len=4096 -max_total_time=60"

clean:
	rm -rf $(B)

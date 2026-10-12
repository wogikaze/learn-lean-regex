export PATH := $(HOME)/.elan/bin:$(PATH)

.PHONY: build test bench clean

build:
	lake build

test:
	lake build tests
	./.lake/build/bin/tests

## Race the derivative engine against the backtracker.
bench:
	lake build bench
	./.lake/build/bin/bench

clean:
	lake clean

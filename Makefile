export PATH := $(HOME)/.elan/bin:$(PATH)

.PHONY: build test clean

build:
	lake build

test:
	lake build tests
	./.lake/build/bin/tests

clean:
	lake clean

all: compile

compile:
	mix compile

test:
	mix test

format:
	mix format

.PHONY: all compile format test

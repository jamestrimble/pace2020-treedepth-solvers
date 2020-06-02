all: solve

solve: solve.c ../include/bitset.h
	${CC} -O3 -g -ggdb -Wall -Wpedantic -Werror=vla -I../include -o solve solve.c naurng.c libmetis.a -mpopcnt -lm

clean:
	rm -f solve

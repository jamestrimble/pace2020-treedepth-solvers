all: solve

solve: solve.c
	${CC} -O3 -march=native -static -g -ggdb -Wall -Wpedantic -Wextra -Werror=vla -o solve solve.c naurng.c -mpopcnt libmetis.a -mpopcnt -lm

clean:
	rm -f solve

scheme: main.c
	gcc -std=c99 -Wall main.c mpc/mpc.c -ledit -lm -o scheme

clean: 
	rm -f scheme

CC=gcc
CFLAGSOPT=-O3 -W  -DNDEBUG 
ASAN_FLAGS=-fsanitize=address
CFLAGSDEF=  -Wall -g 


all: debug

opt: musext.c 
	${CC} ${CFLAGSDEF} musext.c -o musext -L./depqbf_folder -lqdpll

debug: musext.c
	${CC} ${CFLAGSDEF} ${ASAN_FLAGS} musext.c -o musext -L./depqbf_folder -lqdpll
	
Debug: musext.c
	${CC} ${CFLAGSDEF} ${ASAN_FLAGS} musext.c -o ./bin/Debug/MusExt -L./depqbf_folder -lqdpll

clean:
	rm -f *.o
	rm -f musext

.PHONY: all clean 

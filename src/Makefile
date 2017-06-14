BISON=bison
BISONFLAGS=-v
FLEX=flex

CC=gcc

LIBS=-lm -lpthread
EXTRALIBS= -l:libtcmalloc.so.4

# production

# CFLAGS=-O3 -lpthread
# LFLAGS=-O3
# PFLAGS=-O3

# Some other hash functions:

#CFLAGS=-c -DHASH_FUNCTION=HASH_BER -O3 -o
#CFLAGS=-c -DHASH_FUNCTION=HASH_OAT -O3 -o
#CFLAGS=-c -DHASH_FUNCTION=HASH_SAX -O3 -o

# debugging and testing

CFLAGS=-Wall -O3
LFLAGS=-Wall -O3
PFLAGS=-O3

# for debugging the hashes

#CFLAGS=-Wall -g -c -DHASH_DEBUG=1 -o
# for testing keys using utash/tests/keystats
# compile with flags
#CFLAGS=-Wall -g -c -DHASH_EMIT_KEYS=3 -O3 -o
# then run and send descriptions to file handler 3, e.g.
#./prover -c cord.conf -i ../benchmarks/qbfML/C10-V8-D4/p-qbf-modKLadn-K4-C10-V8-D4.1.ksp 3> prover.keys
# then run uthash/tests/keystats on it.
# ideal closer to 100 means better chances of getting constant time

# define the C source files

SRCS = tree.c symbol_table.c prover.c list.c nnf.c prenex.c input_preprocessing.c nnf_simp.c bnf.c bnf_simp.c bit.c

# define the parser files

PARSERC = lex.yy.c parser.tab.c

# define the C object files

OBJS = $(SRCS:.c=.o)
PARSEROBJS = lex.yy.o parser.tab.o

TARGET = ksp

.PHONY: depend clean

all:	$(TARGET)
	cp $(TARGET) ../.

$(TARGET): $(PARSEROBJS) $(OBJS)
	$(CC) $(CFLAGS) $(PARSEROBJS) $(OBJS) $(LFLAGS) $(LIBS) $(EXTRALIBS) -o $(TARGET)

lex.yy.o: $(PARSERC)
	$(CC) -c $(PFLAGS) $(EXTRALIBS) lex.yy.c -o lex.yy.o

parser.tab.o: $(PARSERC)
	$(CC) -c $(CFLAGS) $(EXTRALIBS) parser.tab.c -o parser.tab.o

lex.yy.c:
	$(FLEX) tokenizer.l

parser.tab.c:
	$(BISON) $(BISONFLAGS) parser.y

.c.o:	
	$(CC) $(CFLAGS) $(EXTRALIBS) -c $<  -o $@


clean:
	rm *.o
	rm $(TARGET)
	rm ../$(TARGET)
	rm *~

clean_parser:
	rm lex.yy.c parser.tab.c
	rm lex.yy.o parser.tab.o

depend: $(SRCS)
	makedepend $^

# DO NOT DELETE THIS LINE -- make depend needs it


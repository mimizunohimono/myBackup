T1 = bnlj.exe

CC = g++
CFLAGS = -c -Wall -g -O0
LDFLAGS =

OBJ1 = bnlj.o

#
# Rules for make
#
all: $(T1) 

$(T1): $(OBJ1) 
	$(CC) -o $@ $^ $(LDFLAGS)

.cc.o:
	$(CC) $(CFLAGS) $<

clean:
	rm -f *~ *.o *.exe *.stackdump

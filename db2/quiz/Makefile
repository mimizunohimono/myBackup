T1 = 2pl.exe
T2 = s2pl.exe

CC = g++
CFLAGS = -c -Wall -g -O0
LDFLAGS = -lpthread

O1 = 2pl.o
O2 = s2pl.o

#
# Rules for make
#
all: $(T1) $(T2) 

$(T1): $(O1) 
	$(CC) -o $@ $^ $(LDFLAGS)
$(T2): $(O2) 
	$(CC) -o $@ $^ $(LDFLAGS)

.cc.o:
	$(CC) $(CFLAGS) $<

clean:
	rm -f *~ *.o *.exe *.stackdump

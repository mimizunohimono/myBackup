#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>
#include <pthread.h>
#include <iostream>
#include "debug.h"
using namespace std;

typedef struct _TUPLE {
  int key;
  int val;
} TUPLE;

int
main(int argc, char *argv[])
{
  if (argc != 2) {
    cout << "Usage: program numberOfTuples" << endl;
    exit(1);
  }

  int fd;
  TUPLE t;
  int max = atoi(argv[1]);
  fd = open("R", O_WRONLY|O_CREAT|O_TRUNC|O_APPEND, 0644);
  if (fd == -1) ERR;

  for (int i = 0; i < max; i++) {
    t.key = i;
    t.val = i; 
    write(fd, &t, sizeof(TUPLE));
  }
  close(fd);

  fd = open("S", O_WRONLY|O_CREAT|O_TRUNC|O_APPEND, 0644);
  if (fd == -1) ERR;

  for (int i = 0; i < max; i++) {
    t.key = i; 
    if (i < 1000) t.val = i;
    else t.val = max; 
    write(fd, &t, sizeof(TUPLE));
  }
  close(fd);
}

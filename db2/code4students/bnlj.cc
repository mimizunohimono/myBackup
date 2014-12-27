#include <stdio.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <pthread.h>
#include <sys/time.h>
#include "debug.h"


#define SZ_PAGE 4096
#define NB_BUFR (SZ_PAGE * 2 / sizeof(TUPLE))
#define NB_BUFS (SZ_PAGE * 16 / sizeof(TUPLE))


typedef struct _TUPLE {
  int key;
  int val;
} TUPLE;

typedef struct _RESULT {
  int rkey;
  int rval;
  int skey;
  int sval;
} RESULT;

void
printDiff(struct timeval begin, struct timeval end)
{
  long diff;

  diff = (end.tv_sec - begin.tv_sec) * 1000 * 1000 + (end.tv_usec - begin.tv_usec);
  printf("Diff: %ld us (%ld ms)\n", diff, diff/1000);
}

long
calcDiff(struct timeval begin, struct timeval end)
{
  long diff;
  diff = (end.tv_sec - begin.tv_sec) * 1000 * 1000 + (end.tv_usec - begin.tv_usec);
  return diff;
}


int main(void)
{
  int rfd;
  int sfd;
  int nr;
  int ns;
  TUPLE bufR[NB_BUFR];
  TUPLE bufS[NB_BUFS];
  int resultVal = 0;
  struct timeval begin, end, bio, eio, bjoin, ejoin;
  long iodiff = 0, joindiff = 0;
  RESULT rs[NB_BUFR];
  int cnt = 0;


  rfd = open("R", O_RDONLY); if (rfd == -1) ERR;
  sfd = open("S", O_RDONLY); if (sfd == -1) ERR;

  gettimeofday(&begin, NULL);
  while (true) {

    
    nr = read(rfd, bufR, NB_BUFR * sizeof(TUPLE));
    if (nr == -1) ERR; else if (nr == 0) break;

    if ((lseek(sfd, 0, SEEK_SET)) == -1) ERR;
    while (true) {

      gettimeofday(&bio, NULL);
      ns = read(sfd, bufS, NB_BUFS * sizeof(TUPLE));
      if (ns == -1) ERR; else if (ns == 0) break;
      gettimeofday(&eio, NULL);
      iodiff += calcDiff(bio, eio);

      cnt++;
      gettimeofday(&bjoin, NULL);
      for (int i = 0; i < nr/(int)sizeof(TUPLE); i++) {
	for (int j = 0; j < ns/(int)sizeof(TUPLE); j++) {
	  // Write your code here, please.
	  if(bufR[i].key == bufS[j].key){
	    rs[cnt].rkey = bufR[i].key;
	    rs[cnt].rval = bufR[i].val;
	    rs[cnt].skey = bufS[i].key;
	    rs[cnt].sval = bufS[i].val;
	    cnt++;
	    resultVal += bufR[i].val;
	    resultVal += bufS[j].val;
	  }
	}
      }
      gettimeofday(&ejoin, NULL);
      joindiff += calcDiff(bjoin, ejoin);
    }
  }
  gettimeofday(&end, NULL);
  printDiff(begin, end);
  //  printf("Result: %d\n", resultVal);
  printf("iodiff: %ld\n", iodiff);
  printf("joindiff: %ld\n", joindiff);

  return 0;
}

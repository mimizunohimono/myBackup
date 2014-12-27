#include "hash-bnlj.h"

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

int 
main(void)
{
  int rfd;
  int sfd;
  int nr;
  int ns;
  TUPLE bufR[NB_BUFR];
  TUPLE bufS[NB_BUFS];
  RESULT result;
  int resultVal = 0;
  struct timeval begin, end;
  BUCKET bucket[NB_BUCKET];

  gettimeofday(&begin, NULL);
  rfd = open("R", O_RDONLY); 
  if (rfd == -1) ERR;
  sfd = open("S", O_RDONLY); 
  if (sfd == -1) ERR;
  bzero(bucket, sizeof(BUCKET) * NB_BUCKET);

  int cnt = 0;
  long iodiff = 0;
  long joindiff = 0;
  int countVal = 0;
  
  while (true) {
    nr = read(rfd, bufR, NB_BUFR * sizeof(TUPLE)); // read 1 block of R
    if (nr == -1) ERR; else if (nr == 0) break;
    
    // init index
    for (unsigned int i = 0; i < NB_BUCKET; i++) {
      while (bucket[i].head.nxt) {
	HASHOBJ *tmp = bucket[i].head.nxt;
	bucket[i].head.nxt = bucket[i].head.nxt->nxt;
	free(tmp);
      }
      bucket[i].tail = &bucket[i].head;
    }

    // create index of R
    for (int i = 0; i < nr/(int)sizeof(TUPLE); i++) { // loop number of tuples
      int hkey = bufR[i].val % NB_BUCKET;
      if (!(bucket[hkey].tail->nxt = (HASHOBJ *)calloc(1, sizeof(HASHOBJ)))) ERR;
      bucket[hkey].tail = bucket[hkey].tail->nxt;
      bucket[hkey].tail->tuple = bufR[i]; // connect index and R block with pointer
    }

    int nl = lseek(sfd, 0, SEEK_SET);
    if (nl == -1) ERR;
    while (true) {
      struct timeval bio, eio;
      struct timeval bjoin, ejoin;

      gettimeofday(&bio, NULL);
      ns = read(sfd, bufS, NB_BUFS * sizeof(TUPLE)); // read 1 block of S
      if (ns == -1) ERR; else if (ns == 0) break;
      gettimeofday(&eio, NULL);
      iodiff += calcDiff(bio, eio);

      cnt++;

      // join
      gettimeofday(&bjoin, NULL);
      for (int j = 0; j < ns/(int)sizeof(TUPLE); j++) { // loop number of tuples
	int hash = bufS[j].val % NB_BUCKET; // search the correct bucket in index
	for (HASHOBJ *o = bucket[hash].head.nxt; o; o = o->nxt) { // search correct val in 1 bucket in index
	  if (o->tuple.val == bufS[j].val) { // if values are same, join R and S
	    result.rkey = o->tuple.key;
	    result.rval = o->tuple.val;
	    result.skey = bufS[j].key;
	    result.sval = bufS[j].val;
	    countVal++;
	  }
	}
      }
      gettimeofday(&ejoin, NULL);
      joindiff += calcDiff(bjoin, ejoin);
    }
  }
  gettimeofday(&end, NULL);

  printDiff(begin, end);
  printf("countVal: %d\n", countVal);
  printf("iodiff: %ld\n", iodiff);
  printf("joindiff: %ld\n", joindiff);

  return 0;
}

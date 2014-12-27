#include <stdio.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/time.h>
#include <pthread.h>
#include "debug.h"
#include <iostream>
using namespace std;

#define MAX_OBJ (10)

static bool *Stat;
static pthread_mutex_t LkBgn;
static bool Go = false;
static int Running;

/* Data Area */
static pthread_mutex_t LkObj[MAX_OBJ];
static int DataObj[MAX_OBJ];

static void *
func(void *arg)
{
  int i;
  bool go;
  int *myid = (int *)arg;

  if (pthread_mutex_lock(&LkBgn)) ERR;
  Running++;
  if (pthread_mutex_unlock(&LkBgn)) ERR;

  /* Wait for running */
  while (true) {
    if (pthread_mutex_lock(&LkBgn)) ERR;
    go = Go;
    if (pthread_mutex_unlock(&LkBgn)) ERR;
    if (go == true) break;
    else usleep(100);
  }

  /* Growing Phase */
  for (i = 0; i < MAX_OBJ; i++) {
    if (pthread_mutex_lock(&LkObj[i])) ERR;
  }

  // Shringking Phase
  for (i = 0; i < MAX_OBJ; i++) {

    // Workload A 
    DataObj[i]++;

    if (pthread_mutex_unlock(&LkObj[i])) ERR;

    // Workload B
    usleep(100 * 1000);
  }

  Stat[*myid] = true;
  delete myid;

  return NULL;
}

static void
threadCreat(int id)
{
  pthread_t t;
  int *myid;

  try {
    myid = new int;
    *myid = id;
  } catch(bad_alloc) {ERR;}

  if (pthread_create(&t, NULL, func, (void *)myid)) ERR;
  if (pthread_detach(t)) ERR;
}

static void
chkArg(const int argc)
{
  if (argc != 2) {
    printf("Usage: program #threads\n");
    exit(0);
  }
}

static void
initStat(const int nthread)
{
  int i;
  try {
    Stat = new bool[nthread];
  } catch (bad_alloc) {ERR;}
  for (i = 0; i < nthread; i++) {
    Stat[i] = false;
  }
}

static void
init(int nthread)
{
  int i;

  if (pthread_mutex_init(&LkBgn, NULL)) ERR;
  for (i = 0; i < MAX_OBJ; i++) {
    if (pthread_mutex_init(&LkObj[i], NULL)) ERR;
  }
  Running = 0;
  initStat(nthread);
}

static void
prtRslt(struct timeval bgn, struct timeval end, int nthread)
{
  long usec;
  double sec;

  usec = (end.tv_sec - bgn.tv_sec) * 1000 * 1000 + (end.tv_usec - bgn.tv_usec);
  sec = (double)usec / 1000.0 / 1000.0;
  printf("Throughput: %f (trans/sec)\n", (double)nthread / sec);

}

static void
chkBgn(const int nthread)
{
  int r;

  while (true) {
    if (pthread_mutex_lock(&LkBgn)) ERR;
    r = Running;
    if (pthread_mutex_unlock(&LkBgn)) ERR;
    if (r == nthread) break;
    usleep(100);
  }

  if (pthread_mutex_lock(&LkBgn)) ERR;
  Go = true;
  if (pthread_mutex_unlock(&LkBgn)) ERR;
}

static void
chkFin(const int nthread)
{
  int i;

  while (true) {
    for (i = 0; i < nthread; i++) {
      if (Stat[i] == false) break;
    }
    if (i == nthread) break;
    usleep(1000);
  }
}

extern int
main(int argc, char *argv[])
{
  int i, nthread;
  struct timeval bgn, end;

  chkArg(argc);
  nthread = atoi(argv[1]);
  init(nthread);

  for (i = 0; i < nthread; i++) {
    threadCreat(i);
  }
  chkBgn(nthread);

  gettimeofday(&bgn, NULL);
  chkFin(nthread);
  gettimeofday(&end, NULL);

  prtRslt(bgn, end, nthread);
  
  return 0;
}

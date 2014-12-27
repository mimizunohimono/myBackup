#include <iostream>
#include <stdlib.h>
using namespace std;

#define NUM 100

void show_tape(int *tape)
{
  for(int i = 0; i < NUM; i++)
    cout << tape[i] << " " << endl;

  cout << endl;
}

int main(int argc, char *argv[])
{
  int tape[NUM] = {0};
  int a, b, head = 0;

  if(argc == 3){
    a = atoi(argv[1]);
    b = atoi(argv[2]);
  }else{
    exit(1);
  }

  cout << a << " " << b << endl;

  //Initialize
  tape[head] = a;
  head++;
  tape[head] = b;
  head--;

  while(1){

    show_tape(tape);
    if(tape[head] == 0){
      head++;

      // 0 0 r -> terminate
      if(tape[head] == 0)break;
 
      //0 b-r r
      head++;

      //0 b-r r -> r b 0
      while(tape[head] != 0){
	head--;
	head--;
	tape[head]++;
	head++;
	tape[head]++;
	head++;
	tape[head]--;
      }
	  
      head--;
      head--;

      //r b 0 -> 0 b r
      while(tape[head] != 0){
	head--;
	head--;
	tape[head]--;
	head++;
	head++;
	tape[head]++;
      }
    }

    //a b 0 -> a-b 0 b
    while(tape[head] != 0){
      head--;
      tape[head]--;
      head++;
      tape[head]--;
      head++;
      tape[head]++;
      head--;
    }

    head++;
    // a-b 0 b -> a-b b 0
    while(tape[head] != 0){
      tape[head]--;
      head--;
      tape[head]++;
      head++;
    }
    head--;
  }

  head++;
  cout << tape[head] << endl;
  return 0;

}


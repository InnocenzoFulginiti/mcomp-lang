#include <stdio.h>
#include <stdlib.h>

int _prelude_getint(){
    char buffer[32];
    if(fgets(buffer, 32, stdin) == NULL)
      return 0;
    return atoi(buffer);
}

void _prelude_print(int n){
  printf("%d\n", n);
}
#include <assert.h>

struct S
{
  void *a;
  void *b;
};

typedef void (*fptr)(struct S);

extern fptr A[1];

struct real_S
{
  int *a;
  int *c;
};

void foo(struct real_S g)
{
  assert(*g.a == 42);
  assert(*g.c == 41);
}

void bar()
{
  int x = 42;
  struct real_S s;
  s.a = &x;
  s.c = &x;
  A[0]((struct S){s.a, s.c});
}

#!/usr/bin/ruby
def gcd(a = 1, b = 1)
  aa = a
  bb = b
  if aa < bb then
    tmp = aa
    aa = bb
    bb = tmp
  end
  r = aa % bb
  while r != 0
    aa = bb
    bb = r
    r = aa % bb
  end
  return bb
end

def make_rand(x = 0, n)
  c = 11
  return (x*x + c) % n
end

def abs(x)
  if x < 0 then return -x
  else return x
  end
end

def pollard(n = 114514)
  x = 2
  y = 2
  d = 1
  while d == 1
    x = make_rand(x, n)
    y = make_rand(make_rand(y, n), n)
    d = gcd(abs(x - y), n)
  end
  if d == n then
    return 0
  else
    return d
  end
end

p pollard(18446744073709551617)

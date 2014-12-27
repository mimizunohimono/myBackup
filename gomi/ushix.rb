#!/usr/bin/ruby

def func(x)
  return x + (x/2).floor
end

x = 2
(1..100).each do
  x = func(x)
  print x%2
end

#!/usr/bin/octave
#result.m

#Ax = b
n = 10;
m = 10;
lm = 0.6;
delta = 0.2;
A = round(rand(m, n) + delta)
x = ones(m, 1) / m;
b = A * x;
p = zeros(m, 1);
p(:,1) = ceil(b(:, 1) - lm);
optx = x;
optp = p;

optx
optp

#make a val matrix
Val = zeros(m, 1);
weiA = sum(sum(A));
for i = 1:n
	  Val(i) = sum(A(:,i)) / weiA;
end
for j = 1:m
	  tmp = (1 / sum(A(j, :))) / m;
	  for i = 1:n
		    Val(j) = Val(j) + tmp * A(j, i);
end
end

mnVal = mean(Val);
Val = (Val - mnVal) / 2.0;
Val = round(Val * 100) / 100
  sum(Val)

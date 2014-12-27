#!/usr/bin/octave
#pagerank.m

M = [0, 0, 1/2, 0, 1/5 ,0;
      1/4, 0, 0, 1/2, 1/5, 0;
      1/4, 1, 0, 0, 1/5, 0;
      1/4, 0, 1/2, 0, 1/5, 0;
      0, 0, 0, 1/2, 0, 1;
      1/4, 0, 0, 0, 1/5, 0;
     ]

     [V, D] = eig(M)
     tmp = abs(diag(D))
     EigenVector = V(:, find(tmp) == max(tmp))
     PageRank = EigenVector ./ norm(EigenVector, 1)
     elapsed_time = toc()

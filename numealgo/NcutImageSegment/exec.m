% exec.m for Exercise 09 of Computational Algorithms [GB20201]
% 
% This script is modified version of NcutImageSegment.m and demo2.m
% from Naotoshi Seo's NcutImageSegment
% http://note.sonots.com/SciSoftware/NcutImageSegmentation.html
% 
clear all;
filename = 'img/test.jpg';

% parameters
SI    = 5;%    param for gen W
SX    = 6;%    param for gen W
r     = 1.5;%  param for gen W
sNcut = 0.14;% param for partition
sArea = 220;%  param for partition

% read image from filename
img = imread(filename);
[nRow, nCol, c] = size(img);
N = nRow * nCol;
V = reshape(img, N, c); % connect up-to-down way. Vertices of Graph

% Step 1. Compute weight matrix W, and D
W = NcutComputeW(img, SI, SX, r);


% Step 5. recursively repartition
Seg = (1:N)'; % the first segment has whole nodes. [1 2 3 ... N]'
[Seg Id Ncut] = NcutPartition(Seg, W, sNcut, sArea, 'ROOT');

% % Convert node ids into images
% for i=1:length(Seg)
%     subV = zeros(N, c); %ones(N, c) * 255;
%     subV(Seg{i}, :) = V(Seg{i}, :);
%     SegI{i} = uint8(reshape(subV, nRow, nCol, c));
%     fprintf('%s. Ncut = %f\n', Id{i}, Ncut{i});
% end

% represent the segments
res = zeros(N,1);
for k=1:length(Seg)
    res(Seg{k}) = k;
end

figure();

subplot(2,1,1);
imagesc(img);
colormap gray;
axis equal;
axis off;
freezeColors;

subplot(2,1,2);
imagesc(reshape(res, nRow, nCol));
colormap jet;
axis equal;
axis off;

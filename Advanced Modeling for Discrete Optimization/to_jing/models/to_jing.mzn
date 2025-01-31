% Liu Bei forsees that Yuan Shiu will be defeated by Cao Cao
% He needs to find a route to safety in Jin province before the defeat
% But Cao Cao's soldiers are everywhere

int: nrow;
set of int: ROW = 1..nrow;
int: ncol;
set of int: COL = 1..ncol;

% Plains, Mountain, Forest, City, River
enum TERRAIN = { P, M, F, C, R };
array[TERRAIN] of int: delay;
int: timelimit;

array[ROW,COL] of TERRAIN: terrain;
array[ROW,COL] of int: soldier;
array[ROW,COL] of bool: Jin;

int: start_row;
int: start_col;

int: maxstep;
set of int: STEP = 1..maxstep;
set of int: STEP0 = 0..maxstep;

var STEP: steps;
array[ROW,COL] of var STEP0: visit; % which step do we visit position or 0 if not visited

array[STEP] of var COL: colpos;
array[STEP] of var ROW: rowpos;

% start at start position
constraint visit[start_row,start_col] = 1;

constraint forall(s in 1..steps-1) (
    visit[rowpos[s], colpos[s]] = s /\ visit[rowpos[s + 1], colpos[s + 1]] = s + 1
);

% only use steps moves
constraint sum(r in ROW, c in COL)(visit[r,c] >= 1) <= steps;

% reach Jin province
constraint sum(r in ROW, c in COL)(Jin[r,c] * visit[r,c]) > 0;


% visit at most one city
include "count.mzn";
constraint count([terrain[r, c] | r in ROW, c in COL where visit[r, c] != 0], C) <= 1;

% cant enter Mountain
constraint count([terrain[r, c] | r in ROW, c in COL where visit[r, c] != 0], M) = 0;

% visit only one place in every step
include "all_different_except_0.mzn";
constraint all_different_except_0([visit[r, c] | r in ROW, c in COL]);

constraint forall(s in 1..steps-1) (
    abs(colpos[s] - colpos[s+1]) + abs(rowpos[s] - rowpos[s+1]) = 1 
);


% no shortcuts
constraint forall(r1, r2 in ROW, c1, c2 in COL where abs(r1-r2) + abs(c1-c2) = 1)(
  visit[r1,c1] = 0 \/ visit[r2,c2] = 0 \/ abs(visit[r1,c1] - visit[r2,c2]) = 1
);
%  constraint forall(s in 1..steps-1)(
%    abs(visit[rowpos[s], colpos[s]] - visit[rowpos[s + 1], colpos[s + 1]]) = 1
% );
% constraint forall(r1,r2 in ROW, c1,c2 in COL)
%                  (abs(r1-r2) + abs(c1-c2) = 1 ->
%                   visit[r1,c1] = 0 \/ visit[r2,c2] = 0 \/
%                   abs(visit[r1,c1] - visit[r2,c2]) = 1);

% not too much delay
constraint time <= timelimit;
var int: time = sum(r in ROW, c in COL)(delay[terrain[r,c]]*(visit[r,c] >= 1));

% minimize the number of soldiers traversed
solve minimize sum(r in ROW, c in COL)((visit[r,c] > 0)*soldier[r,c]);


array[TERRAIN] of string: ter = [".", "#", "^", "C", "~"];

output
      [ " " ++ ter[fix(terrain[r,c])] ++ if c = ncol then "\n" else "" endif
      | r in ROW, c in COL ]
      ++ ["\n"] ++
      [ if soldier[r,c] > 0 then show_int(2,soldier[r,c]) else " ." endif
          ++ if c = ncol then "\n" else "" endif
      | r in ROW, c in COL ]
      ++ ["\n"] ++
      [ if fix(visit[r,c]) > 0 then show_int(2,visit[r,c]) else " ." endif
          ++ if c = ncol then "\n" else "" endif
      | r in ROW, c in COL ];

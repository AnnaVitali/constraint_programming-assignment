include "all_different.mzn";
% assignment 2
% select a set of raiding warrior
enum WARRIOR;
WARRIOR: dummy;
enum CLAN; % the clan they belong too

int: l; % minimum raid party size
int: u; % maximum raid party size
int: m; % limit of hatreds

array[WARRIOR] of int: strength;
array[WARRIOR] of CLAN: clan;

array[CLAN,CLAN] of 0..1: hates;
var int: obj;

array[1..u] of var WARRIOR: selected;


constraint forall(i in 1..l)(selected[i] > dummy);

constraint forall(i in 1..u-1)(selected[i] >= selected[i+1] + (selected[i+1] != dummy));

constraint length(selected) >= l /\ length(selected) <= u;

constraint sum(i,j in 1..u where i < j)(hates[clan[selected[i]],clan[selected[j]]]) <= m;

constraint obj = sum([strength[selected[i]] | i in 1..length(selected)]);


set of WARRIOR: raid ::output_only =
{ fix(selected[i]) | i in 1..length(selected) where fix(selected[i]) != dummy };

solve maximize obj


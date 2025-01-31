include "inverse.mzn";
include "all_different.mzn";
include "global_cardinality.mzn";
include "global_cardinality_low_up_closed.mzn";

int: n; % number of court members
set of int: COURT = 1..n;
int: emperor = 1;
array[COURT] of int: rank;
array[COURT] of int: ability;

int: m; % number of horses
set of int: HORSE = 1..m;
array[HORSE] of int: beauty;
array[HORSE] of int: speed;

array[COURT,HORSE] of int: enjoy;

int: dummy = 0;

set of int: COURT0 = 0..n;
set of int: HORSE0 = 0..m;

array[COURT] of var HORSE0: horse;
array[HORSE] of var COURT0: court;
var int: violations;

constraint forall(c in COURT where horse[c]!= dummy) (court[horse[c]] = c);
constraint forall(h in HORSE where court[h]!= dummy) (horse[court[h]] = h);

constraint if n>=m then global_cardinality(horse, [i | i in HORSE],  [1 | i in HORSE])
else global_cardinality_low_up_closed(horse, [i | i in HORSE], [dummy | i in HORSE], [1 | i in HORSE])   endif;

constraint forall(i in COURT where horse[i] != dummy)(enjoy[i, horse[i]] >= 0);

constraint forall(i in COURT where horse[i] != dummy /\ i != emperor)(enjoy[emperor, horse[emperor]] > enjoy[i, horse[i]]);

constraint forall(i, j in COURT where i!=j) ((rank[i]>rank[j]) -> (beauty[horse[i]] >= beauty[horse[j]] \/ horse[j]= dummy));

constraint violations = sum(i, j in HORSE where i != j)(not((speed[i] > speed[j]) -> (court[i] = dummy \/ ability[court[i]] >= ability[court[j]])));


var int: obj = sum([enjoy[i, horse[i]] | i in COURT where horse[i] != dummy]) - violations * 100;
solve maximize obj;
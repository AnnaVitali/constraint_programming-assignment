int: T; % maximum time allowed;
set of int: TIME = 1..T;
set of int: TIME0 = 0..T;

int: E; % weight of elephant in STONES;
set of int: STONE = 0..E;

int: G; % number of guards
set of int: GUARD = 1..G;
array[GUARD] of STONE: easy;
array[GUARD] of STONE: hard;
array[GUARD] of TIME: tired;

GUARD: p; % maximum people on pier;
GUARD: b; % maximum people on boat;

enum POS = {Bank, Boat};

array[GUARD, TIME0] of var POS: pos; % guard position

array[TIME] of var -E..E: move_stone;

var TIME: end;

set of int: ACT = -1..E; % -1 = goto bank, 0 = wait, > 0 carry stones
int: wait = 0;
int: to_bank = -1;
array[GUARD,TIME] of var ACT: act;        % action at time t

predicate guard_pos(var POS: now, var POS: next, var ACT: action) = 
          if action = wait then next = now
          elseif now = Boat /\ action = to_bank then next = Bank
          elseif now = Bank /\ action > 0 then next = Boat
          else true endif;
                
predicate guard_move(var TIME: time, var GUARD: guard ) = (act[guard, time] != wait);

predicate guard_tired(var TIME: time, var GUARD: guard) = (act[guard, time] > easy[guard]);

predicate guard_rest(var TIME: time, var GUARD:guard) = 
          (let {var int: trest = min(time + tired[guard], T);} in 
          forall(i in time+1..trest)(act[guard, i] <= 0)); %= wait \/ 
         % sum(i in time..trest_bank)(act[guard, i]) = to_bank);
   
% All guard are on the Bank at the beginning
constraint forall(g in GUARD)(pos[g, 0] = Bank);

% Guard can't carry more than hard stones
constraint forall(g in GUARD, t in TIME)(act[g, t] <= hard[g]);

% The guards on the pier should be maximum p, so guards moving should be maximum p
constraint forall(t in TIME)(sum(g in GUARD)(guard_move(t, g)) <= p );

% The guards on the boat should be maximum b
constraint forall(t in TIME)(sum(g in GUARD)(pos[g, t] = Boat) <= b );

% No action can be performed after the end
constraint forall(t in TIME)(t > end -> move_stone[t] = 0);
constraint forall(t in TIME, g in GUARD)(t > end -> act[g, t] = wait);
  
% At the end the stone opn boat should be at least E  
constraint forall (t in TIME) (move_stone[t] = sum(g in GUARD where act[g,t] > 0) (act[g,t]));
constraint sum(t in TIME, g in GUARD where act[g, t] > 0)(act[g, t]) = E;

% Guard can move in the same direction only, and from boat to bank or viceversa
constraint forall(t in TIME, g1,g2 in GUARD)(act[g1, t] * act[g2, t] >= 0);

constraint forall(t in TIME, g in GUARD)(
  guard_pos(pos[g, t-1], pos[g, t], act[g, t])
);

constraint forall(t in TIME, g in GUARD)(act[g, t] = to_bank -> pos[g, t - 1] = Boat);
constraint forall(t in TIME, g in GUARD)(act[g, t] > 0 -> pos[g, t - 1] = Bank);


% If a guard has carried hard stones it must rest for tired steps
constraint forall(t in TIME, g in GUARD)(
  guard_tired(t, g) -> guard_rest(t, g)
) ;

solve minimize end;



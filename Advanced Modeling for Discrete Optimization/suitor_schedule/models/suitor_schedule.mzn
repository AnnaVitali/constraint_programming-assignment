% scheduling suitors
enum SUITOR;
SUITOR: LiuBei; % which suitor is LiuBei
int: n; % number of meetings
set of int: MEETING = 1..n;
array[MEETING] of SUITOR: suitor;

enum ROOM = { Red, Gold, Blue };
array[SUITOR,ROOM] of int: mintime;
array[SUITOR,ROOM] of int: maxtime;
constraint forall(s in SUITOR, r in ROOM)
                 (assert(mintime[s,r] >= 1 /\ maxtime[s,r] >= mintime[s,r],
                  "error in mintime/maxtime at [\(s),\(r)]\n"));

array[ROOM,ROOM] of int: move;
constraint forall(r in ROOM)(assert(move[r,r] = 0,"move[\(r),\(r)] != 0\n"));

int: ndays; % number of days
set of int: DAY = 1..ndays;
int: earliest; % time for earliest meeting start
int: latest;  % time for end of latest meeting

int: lessontime; % time for kung fu lesson;
int: minsep;     % minimum time between consecutive kung fu lessons

array[ROOM] of int: usedstart;  % time others use each room each day
array[ROOM] of int: useddur;    % durations of others use

enum STAGE = {A,B,C};
STAGE: stage;

set of int: TIME = 0..24*ndays;

array[MEETING] of var TIME: start;
array[MEETING] of var TIME: dur;    % duration in false schedule
array[MEETING] of var ROOM: room;
set of int: KUNGFU = 1..n;
array[KUNGFU] of var int: kungfu;  % start time for each lesson
   % unused lessons have start times after 24*ndays
int: unused_lesson = 24*ndays + lessontime;

array[MEETING] of var 0..1: kungfu_lesson;
array[KUNGFU] of var 0..n: kungfu_meeting;
   
predicate room_moovement(var ROOM: room1, var ROOM: room2, var TIME: start1, var TIME: start2, var TIME: dur1) = 
          let { var int: moovment_time = move[room1, room2]; } in
          start2 >= start1 + dur1 + moovment_time;

%not overlap meeting  
include "disjunctive.mzn";
constraint disjunctive(start, dur);

%respect precedence between meeting with same suitor
constraint forall(s in SUITOR)
            (
              forall(m1, m2 in MEETING where m1 < m2)
              (
                (suitor[m1] = s /\ suitor[m2] = s) -> start[m1] < start[m2]
              )
            );

%respect mintime and maxtime meeting and also that should start at least at earliest time and at most they should finish at latest time           
constraint forall(m in MEETING)
           (
            start[m] mod 24 >= earliest /\
            start[m] mod 24 <= latest /\
            ((start[m] + dur[m]) mod 24) >= earliest /\
            ((start[m] + dur[m]) mod 24) <= latest
            );

constraint forall(m in MEETING)
           (
            dur[m] - kungfu_lesson[m] * lessontime >= mintime[suitor[m], room[m]] /\ 
            dur[m] <= maxtime[suitor[m], room[m]]
           );

%respect time of mooving from one room to another  
constraint stage in {B, C} -> forall(m1, m2 in MEETING where m1 < m2)
           (
            move[room[m1], room[m2]] > 0 -> room_moovement(room[m1], room[m2], start[m1], start[m2], dur[m1])
           );

%can't use room when they are busy           
constraint forall(m in MEETING)
           (
            (start[m] + dur[m]) mod 24 <= usedstart[room[m]] \/ start[m] mod 24 >= (usedstart[room[m]] + useddur[room[m]])
           );
           
% Just assume than kungfu all greater than 0
constraint forall(k in KUNGFU) (
    kungfu[k] > 0 /\
    kungfu[k] <= 24*ndays + n*(minsep+lessontime)
);

% in stage A and B should not schedule kungfu hours           
constraint stage in {A, B} -> forall(k in KUNGFU)
                          (
                            kungfu[k] > 24*ndays /\ kungfu_meeting[k] = 0
                          );
                          
constraint stage in {A, B} -> forall(m in MEETING)
                              (
                                kungfu_lesson[m] = 0
                              );
 
%kungfu lessons should not overlap                          
constraint forall(k in 1..n-1)
                           (
                            kungfu[k+1] >= kungfu[k] + minsep + lessontime
                           );               
                           
%schedule kungfu lessons                           
constraint stage in {C} -> forall(k in KUNGFU)
                           (kungfu[k] <= 24*ndays -> exists(m in MEETING)(kungfu[k] + lessontime = start[m] + dur[m] /\ kungfu_meeting[k] = m));
                           
constraint stage in {C} -> forall(m in MEETING)
                          (if exists(k in KUNGFU)(kungfu_meeting[k]=m) then kungfu_lesson[m]=1 else kungfu_lesson[m]=0 endif);
                          

var TIME: liu_bei_time_ab = sum([dur[m] | m in MEETING where suitor[m] = LiuBei]);
var TIME: liu_bei_time_c = sum([dur[m] - kungfu_lesson[m] * lessontime | m in MEETING where suitor[m] = LiuBei]);
var TIME: kungfu_lessons = sum([1 | k in KUNGFU where kungfu[k] < 24*ndays]);

var int: obj = if stage = C then liu_bei_time_c + 100*kungfu_lessons else liu_bei_time_ab endif;
solve maximize obj;

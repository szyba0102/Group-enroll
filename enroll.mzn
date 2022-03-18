% Parameters
int: n_students;
int: n_days;
int: n_classes;
int: n_groups;
int: n_locations;
int: n_time_units_in_hour;
int: exclusion = -1;

set of int: Student = 1..n_students;
set of int: Class = 1..n_classes;
set of int: Group = 1..n_groups;
set of int: Day = 1..n_days;
set of int: Location = 1..n_locations;
set of int: Time = 0..n_time_units_in_hour * 24;
set of int: WorkTime = 0..max(Time)*n_days;
set of int: Preference = exclusion..max([student_prefers[s,g] | s in Student, g in Group]);

array[Student] of 0..5: student_break_importance;
array[Student, Group] of int: student_prefers;

array[Class] of Time: class_duration;
array[Class] of int: class_size;
array[Group] of Class: group_class;
array[Group] of Time: group_start;
array[Group] of Location: group_location;
array[Group] of Day: group_day;
array[int] of set of Group: group_cohabitats;
array[Location, Location] of Time: travel_duration;


% helper function
function var int: ceil_div(var int: x, var int: y) =
  x div y + ((x mod y) > 0);
  
% array[Student, Class] of var 0..n_groups: assignment; for each student, for each class containt ID of assigned group, 0 means student doesn't attend this class 
array[Student, Class] of var 0..n_groups: assignment; 
constraint forall(s in Student, c in Class)(if maximum_group_preference[s,c] = -1 then assignment[s,c] = 0 else assignment[s,c] != 0 endif); 
  
  
  
  
% Break disappointment part

array[Group,Group] of var int: breaks_length;

predicate cohabitate(var Group: group1, var Group: group2) = exists([group1 in k /\ group2 in k | k in group_cohabitats]);



constraint forall(i in Group, j in Group where i=j \/ cohabitate(i,j) \/ group_day[i] != group_day[j])(breaks_length[i,j] = 1000000);

constraint forall(i in Group)(
             forall(j in Group where i<j /\ group_day[i] = group_day[j] /\ not cohabitate(i,j))(
             let {
             var int: gEnd = min(group_end[i],group_end[j]);
             var int: gStart = max(group_start[i],group_start[j])
             } in 
if gEnd <= gStart then breaks_length[j,i] = gStart-gEnd /\ breaks_length[i,j] = gStart-gEnd else breaks_length[j,i] = -1 /\ breaks_length[i,j] = -1 endif));
                    
% constraint that makes sure that students are never late
constraint forall(i in Student)(
              forall(j in Class where assignment[i,j] != 0)(
                forall(k in Class where j<k /\ assignment[i,k] != 0 )(
                    breaks_length[assignment[i,j],assignment[i,k]] >= travel_duration[group_location[assignment[i,j]],group_location[assignment[i,k]]]
)));              
   
%Evaluating break disappointment
array[Student] of var 0..infinity: break_disappointment; %normalised value (in hours)
var 0..infinity: total_break_disappointment;

array[Group] of var Time: group_end;
array[Student,Day] of var bool: student_at_campus;
array[Student, Day] of var Time: arrival_at_campus_time;
array[Student, Day] of var Time: campus_leaving_time;
array[Student, Day] of var Time: time_at_campus;
array[Student] of var WorkTime: time_at_campus_in_week;
array[Student] of var WorkTime: summed_classes_length_in_week;


function var WorkTime: common_time(var Group: g1, var Group: g2) = class_duration[group_class[g1]] + class_duration[group_class[g2]] - (max(group_end[g1], group_end[g2]) - min(group_start[g1], group_start[g2]));


constraint forall(i in Student, c in Class where assignment[i,c] != 0)(student_at_campus[i,group_day[assignment[i,c]]] = true);

constraint forall(sID in Student, dID in Day where student_at_campus[sID,dID] =true)(arrival_at_campus_time[sID, dID] = 
  min([group_start[assignment[sID, c]] | c in Class where assignment[sID, c]!= 0 /\group_day[assignment[sID, c]] = dID]));

constraint forall(gID in Group)(group_end[gID] = group_start[gID] + class_duration[group_class[gID]]);

constraint forall(sID in Student, dID in Day where student_at_campus[sID,dID] =true)(campus_leaving_time[sID, dID] =
  max([group_end[assignment[sID, c]] | c in Class where assignment[sID, c]!= 0  /\group_day[assignment[sID, c]] = dID ]));
  
constraint forall(sID in Student, dID in Day)(time_at_campus[sID, dID] = campus_leaving_time[sID, dID] - arrival_at_campus_time[sID, dID]);

constraint forall(sID in Student)(time_at_campus_in_week[sID] = sum(row(time_at_campus, sID)));

 
constraint forall(s in Student)(summed_classes_length_in_week[s] = sum([class_duration[group_class[assignment[s,c]]] | c in Class where assignment[s,c] != 0]) - 
sum([common_time(assignment[s, c1], assignment[s, c2]) | c1 in Class, c2 in Class where c1<c2 /\ cohabitate(assignment[s,c1], assignment[s,c2])]));


constraint forall(sID in Student)(break_disappointment[sID] =
  ceil_div(time_at_campus_in_week[sID] - summed_classes_length_in_week[sID], n_time_units_in_hour));
  
constraint total_break_disappointment = sum(break_disappointment);    

 
             
%Preference disappointment part

% array that contains preference disappointment for each student
array[Student] of var int: preference_disappointment;
array[Student,Class] of var Preference: maximum_group_preference;
% array that contains difference of preference value for each class and each student
array[Student,Class] of var int: difference_preference;
var 0..infinity: total_preference_disappointment;
set of int: Possible_group_size = 0..max(class_size);

constraint forall(k in Student, i in Class)(maximum_group_preference[k,i] = max([student_prefers[k,j] | j in Group where group_class[j] = i]));
                     
constraint forall(k in Student,i in Class)(if maximum_group_preference[k,i] != -1 then difference_preference[k,i] = maximum_group_preference[k,i] - student_prefers[k,assignment[k,i]] else difference_preference[k,i] = 0 endif);
                                            
constraint forall(i in Student)(preference_disappointment[i] = sum([difference_preference[i,k] | k in Class]));
                     
constraint total_preference_disappointment = sum(preference_disappointment);

%group in column of specific Class has to belong to this Class
constraint forall(sID in Student, cID in Class where assignment[sID, cID] != 0)(group_class[assignment[sID, cID]] = cID);

%Number of people in group has to be lower or equal to class_size[group_class[group]]
function var int: num_of_assigned_students(var Group: gID) = count([assignment[st, group_class[gID]] = gID | st in Student]);
constraint forall(gID in Group)(num_of_assigned_students(gID) <= class_size[group_class[gID]]);



%Evaluating total objective
array[Student] of var int: total_disappointment;
constraint forall(sID in Student)
  (total_disappointment[sID] = ceil_div((student_break_importance[sID] * break_disappointment[sID] +
                                        (10 - student_break_importance[sID]) * preference_disappointment[sID]), 10));
                                     
var int: objective = sum([total_disappointment[sID] * total_disappointment[sID] | sID in Student]);



solve:: seq_search([
 int_search(preference_disappointment, largest, indomain_min),
 int_search(break_disappointment, largest, indomain_min)]) minimize objective;
% output                                
% ["arrival_at_campus_time = ", show(arrival_at_campus_time), ";\n"] ++
% ["campus_leaving_time = ", show(campus_leaving_time), ";\n"] ++         
% ["breaks_length = ", show(breaks_length), ";\n"] ++          
% ["group_end = ", show(group_end), ";\n"] ++  
% ["assignment = ", show(assignment), ";\n"] ++
% ["maximum_group_preference  = ", show(maximum_group_preference), ";\n"] ++
% ["total_break_disappointment = ", show(total_break_disappointment), ";\n"] ++
% ["total_preference_disappointment = ", show(total_preference_disappointment), ";\n"] ++
% ["objective = ", show(objective), ";\n"];

  
output    
["assignment = ["] ++ 
[ if c == 1 then "{" else "" endif ++ 
  if c != 1 /\ fix(assignment[s, c]) != 0 /\ exists([fix(assignment[s, cl]) != 0 | cl in 1..c-1]) then "," else "" endif ++
  if fix(assignment[s, c]) != 0 then show(assignment[s, c]) else "" endif ++ 
  if c == n_classes then if s != n_students then "}," else "}" endif else "" endif 
| s in Student, c in Class] ++
["];\n"] ++
["total_break_disappointment = " ++ show(total_break_disappointment) ++ ";\n"] ++
["total_preference_disappointment = " ++ show(total_preference_disappointment) ++ ";\n"] ++
["objective = " ++ show(objective) ++ ";\n"]
%  ++
% ["first slot " ++ show(earliest_group_first_slot) ++ ";\n"] ++
% ["last slot = " ++ show(latest_group_last_slot) ++ ";\n"] ++
% ["student is at some class: "] ++ [show(student_is_at_some_class[1,1,t]) | t in PossibleGroupTime] ++ [";\n"]

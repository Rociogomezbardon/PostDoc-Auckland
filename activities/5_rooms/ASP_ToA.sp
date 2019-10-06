#const max_name = 39.
%#const max_len = 17.
%#const numSteps = 18.
#const max_len = 22.
#const numSteps = 23.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  sorts
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
#secure_room = {library}.
#room = #secure_room + {kitchen, office1,office2,office3}.
%#room = #secure_room + {kitchen, office1,office2}.
#robot = {rob1}.
#book = {book1, book2}.
#object = #book.
#thing = #object + #robot.

#boolean = {true, false}.
#step = 0..numSteps.


#physical_inertial_fluent = loc(#thing, #room) + in_hand(#robot, #object) + locked(#secure_room).

#physical_agent_action = move(#robot, #room) + pickup(#robot, #object)
	+ put_down(#robot, #object) + unlock(#robot, #secure_room).
#exo_action = exo_move(#object,#room) + exo_lock(#secure_room).


#possible_goal = tidy_all(#room) + tidy_book(#book,#room).
#physical_defined_fluent = #possible_goal + missing_book(#room).

#activity_name = 1..max_name.
#positive_index = 1..max_len.      
#index = #positive_index + {neg1, 0}.

#mental_agent_action = select_activity(#activity_name).
#mental_inertial_fluent = current_action_index(#activity_name,#index).
#mental_defined_fluent = next_action(#activity_name,#physical_agent_action).


#inertial_fluent = #physical_inertial_fluent + #mental_inertial_fluent.
#defined_fluent = #physical_defined_fluent + #mental_defined_fluent.
#fluent = #inertial_fluent + #defined_fluent.
#agent_action = #physical_agent_action + #mental_agent_action.

#action = #agent_action + #exo_action.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
predicates
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
next_to(#room,#room).

holds(#fluent,#step).
occurs(#action,#step).

obs(#fluent, #boolean, #step).
hpd(#action, #step).


success().



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% predicates for activity axioms
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
selected_goal(#possible_goal).
candidate(#activity_name).
existing_candidate(#activity_name).
new_candidate(#activity_name).
has_component(#activity_name,#index).
next_available_name(#activity_name).
needs_new_activity().
impossible(#action,#step).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% activities defining-predicates
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
activity_component(#activity_name,#index,#physical_agent_action).
activity_length(#activity_name,#index).
activity_goal(#activity_name,#possible_goal).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 rules
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Physical static relations.
next_to(office3,office2).
next_to(office2,office1).
next_to(office1,kitchen).
next_to(kitchen,library).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Causal Laws %%
%% Moving changes location to target room (if the door is not locked).
holds(loc(R, L), I+1) :- occurs(move(R, L), I).

%% Grasping an object causes object to be in hand.
holds(in_hand(R, O), I+1) :- occurs(pickup(R, O), I).

%% Putting an object down causes it to no longer be in hand.
-holds(in_hand(R, O), I+1) :- occurs(put_down(R, O), I).

%% Unlocking a room causes it to be not be locked.
-holds(locked(L),I+1) :- occurs(unlock(R, L),I).

%% Exogenous locking causes the door to be locked.
holds(locked(L), I+1) :- occurs(exo_lock(L), I).

%% Exogenous moving an object causes the object to be in a different location.
holds(loc(O,L),I+1) :- occurs(exo_move(O,L),I).

holds(current_action_index(AN,0),I+1) :- occurs(select_activity(AN),I).
holds(current_action_index(AN,K+1),I+1) :- occurs(PAA,I), 
		holds(next_action(AN,PAA),I), 
		holds(current_action_index(AN,K),I), 
		activity_component(AN,K+1,PAA).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% State Constraints %%

%% Reflexive property of next_to relation.
next_to(L1,L2) :- next_to(L2,L1).
-next_to(L1,L2) :- not next_to(L1,L2).

%% Any object exists in only one location.
-holds(loc(T, L2), I) :- holds(loc(T, L1), I), L1!=L2.

%% If a robot is holding an object, they have the same location.
holds(loc(O, L), I) :- holds(loc(R, L), I), holds(in_hand(R, O), I).

%% Only one object can be held at any time.
-holds(in_hand(R, O2), I) :- holds(in_hand(R, O1), I), O1 != O2.


%% only one current_action_index for each activity.
-holds(current_action_index(AN,K1),I):-holds(current_action_index(AN,K2),I), K1!=K2.

%% the next action of an activity is defined in terms of the activity current action index.
holds(next_action(AN,PAA),I) :- holds(current_action_index(AN,K),I), activity_component(AN,K+1,PAA).


%% defining the possible goals.
holds(tidy_book(B,R),I) :- holds(loc(B,R),I), -holds(in_hand(rob1,B),I).
holds(missing_book(R),I) :- -holds(tidy_book(B,R),I).
holds(tidy_all(R),I) :- not holds(missing_book(R),I).

%% initial condition constraint
holds(current_action_index(AN,neg1),0).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Executability Conditions %%
%% Cannot move to a location if you are already there.
-occurs(move(R, L), I) :- holds(loc(R, L), I).

%% Cannot move to a location if it is not next to it.
-occurs(move(R, L2), I) :- holds(loc(R, L1), I), -next_to(L1,L2).

%% Cannot move to a location if it is locked.
-occurs(move(R, L), I) :- holds(locked(L), I).

%% Cannot from a location if it is locked.
-occurs(move(R, L2), I) :- holds(loc(R,L1), I), holds(locked(L1), I).

%% Cannot unlock if it is not locked.
-occurs(unlock(R, L), I) :- -holds(locked(L), I).

%% Cannot unlock a room L1 if it's in a room L2 which is not either same as L1, or next to L1.
-occurs(unlock(R, L1), I) :- holds(loc(R,L2), I), -next_to(L1,L2), L1 != L2.

%% Cannot put down an object unless it is in hand.
-occurs(put_down(R, O), I) :-  -holds(in_hand(R, O), I).

%% Cannot pick up an object if it has something in hand.
-occurs(pickup(R, O1), I) :- holds(in_hand(R, O2), I).

%% Cannot pick up an object if you are not in the same room.
-occurs(pickup(R, O), I) :- holds(loc(R, L1), I),
			    holds(loc(O, L2), I), L1 != L2.


%% An exogenous move of an object cannot be done to the same location.
-occurs(exo_move(O,L),I) :- holds(loc(O,L),I).

%% An exogenous move of an object cannot be done to a locked room.
-occurs(exo_move(O,L),I) :- holds(locked(L),I).

%% An exogenous move of an object cannot happen if it is being in hand
-occurs(exo_move(O,L),I) :- holds(in_hand(R,O),I).

%% An exogenous move of an object cannot be done from a locked room.
-occurs(exo_move(O,L1),I) :- holds(loc(O,L),I), holds(locked(L),I).

%% An exogenous lock cannot be done to a locked room.
-occurs(exo_lock(L),I) :- holds(locked(L),I).




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% impossible condition
-occurs(A,I) :- impossible(A,I).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Inertial axiom + CWA

%% General inertia axioms.
holds(F,I+1) :- #inertial_fluent(F),
                holds(F,I),
                not -holds(F,I+1).

-holds(F,I+1) :- #inertial_fluent(F),
                 -holds(F,I),
                 not holds(F,I+1).

%% CWA for Actions.
-occurs(A,I) :- not occurs(A,I).

%% CWA for defined fluents
-holds(F,I) :- not holds(F,I), #defined_fluent(F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% History and initial state rules

%% Take what actually happened into account.
occurs(A,I) :- hpd(A,I).

%% Reality check axioms.
:- obs(F, true, I), -holds(F, I).
:- obs(F, false, I), holds(F, I).

%% Awareness axiom.
holds(F, 0) | -holds(F, 0) :- #inertial_fluent(F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Defning candidates:
%% Activity AN is defined as an existing candidate if the goal of the activity is the selected goal and, either its name/number is less than the next available name or if all names have been taken. 
existing_candidate(AN) :- activity_goal(AN,G), 
	selected_goal(G),
	not new_candidate(AN).

%% we define AN as the new candidate if AN is the next new available name and there are no existing candidates
new_candidate(max_name) :- needs_new_activity.

candidate(AN) :- new_candidate(AN).
candidate(AN) :- existing_candidate(AN).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Creating activities as new candidates
 activity_goal(AN,G) :- new_candidate(AN), selected_goal(G).
 activity_component(AN,I,PAA) :- new_candidate(AN), occurs(PAA,I), 0<I.
 :- new_candidate(AN), activity_component(AN,K,PAA1), activity_component(AN,K,PAA2), PAA1!=PAA2.
 has_component(AN,K):-new_candidate(AN), activity_component(AN,K,C).
 activity_length(AN,K):- new_candidate(AN),  has_component(AN,K), not has_component(AN,K+1).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Selecting candidates.
%% If it is possible to select a candidate, then it will be selected.
 occurs(select_activity(AN),0) :- candidate(AN), not impossible(select_activity(AN),0).

%% It is impossible to select two different activities and it is impossible to select and activity 
%% which correspoinding goal is not selected
impossible(select_activity(AN1),I1) :- occurs(select_activity(AN2),I2), AN1 != AN2.
impossible(select_activity(AN),0) :- not candidate(AN).
impossible(select_activity(AN),I) :- I>0.
impossible(select_activity(AN),0) :- activity_goal(AN,G), holds(G,0).

%% This rule ensures that the selected existing activity is athe minimal activity that reaches the goal:
 occurs(PAA,I) :+ not needs_new_activity, existing_candidate(AN), occurs(select_activity(AN),0), holds(next_action(AN,PAA),I), occurs(A,I-1), 0<I. 


%% This ensures that if a new candidate is being selected, this candidate activity will be a minimal activity.
 occurs(PAA,I) :+  new_candidate(AN), occurs(select_activity(AN),0), occurs(A,I-1), 0<I, #physical_agent_action(PAA).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Planning Module
success :- holds(G,I), selected_goal(G).
:- not success.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Goal
selected_goal(tidy_all(library)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Initial Conditions
-holds(locked(library),0).
holds(loc(rob1,office3),0).
holds(loc(book1,office3),0).
holds(loc(book2,office1),0).
holds(in_hand(rob1,book1),0).
-holds(in_hand(rob1,book2),0).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Needs New Activity?

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Existing Activities
activity_goal(1,tidy_all(library)).
activity_component(1,1,move(rob1,library)).
activity_component(1,2,put_down(rob1,book2)).
activity_component(1,3,move(rob1,kitchen)).
activity_component(1,4,move(rob1,office1)).
activity_component(1,5,move(rob1,office2)).
activity_component(1,6,move(rob1,office3)).
activity_component(1,7,pickup(rob1,book1)).
activity_component(1,8,move(rob1,office2)).
activity_component(1,9,move(rob1,office1)).
activity_component(1,10,move(rob1,kitchen)).
activity_component(1,11,move(rob1,library)).
activity_component(1,12,put_down(rob1,book1)).
activity_length(1,12).

activity_goal(2,tidy_all(library)).
activity_component(2,1,put_down(rob1,book2)).
activity_component(2,2,unlock(rob1,library)).
activity_component(2,3,move(rob1,kitchen)).
activity_component(2,4,move(rob1,office1)).
activity_component(2,5,move(rob1,office2)).
activity_component(2,6,move(rob1,office3)).
activity_component(2,7,pickup(rob1,book1)).
activity_component(2,8,move(rob1,office2)).
activity_component(2,9,move(rob1,office1)).
activity_component(2,10,move(rob1,kitchen)).
activity_component(2,11,move(rob1,library)).
activity_component(2,12,put_down(rob1,book1)).
activity_length(2,12).

activity_goal(3,tidy_all(library)).
activity_component(3,1,pickup(rob1,book2)).
activity_component(3,2,move(rob1,office2)).
activity_component(3,3,move(rob1,office1)).
activity_component(3,4,move(rob1,kitchen)).
activity_component(3,5,unlock(rob1,library)).
activity_component(3,6,move(rob1,library)).
activity_component(3,7,put_down(rob1,book2)).
activity_component(3,8,move(rob1,kitchen)).
activity_component(3,9,pickup(rob1,book1)).
activity_component(3,10,move(rob1,library)).
activity_component(3,11,put_down(rob1,book1)).
activity_length(3,11).

activity_goal(4,tidy_all(library)).
activity_component(4,1,move(rob1,kitchen)).
activity_component(4,2,move(rob1,library)).
activity_component(4,3,put_down(rob1,book2)).
activity_component(4,4,move(rob1,kitchen)).
activity_component(4,5,move(rob1,office1)).
activity_component(4,6,move(rob1,office2)).
activity_component(4,7,pickup(rob1,book1)).
activity_component(4,8,move(rob1,office1)).
activity_component(4,9,move(rob1,kitchen)).
activity_component(4,10,move(rob1,library)).
activity_component(4,11,put_down(rob1,book1)).
activity_length(4,11).

activity_goal(5,tidy_all(library)).
activity_component(5,1,move(rob1,office3)).
activity_component(5,2,pickup(rob1,book2)).
activity_component(5,3,move(rob1,office2)).
activity_component(5,4,move(rob1,office1)).
activity_component(5,5,move(rob1,kitchen)).
activity_component(5,6,unlock(rob1,library)).
activity_component(5,7,move(rob1,library)).
activity_component(5,8,put_down(rob1,book2)).
activity_component(5,9,move(rob1,kitchen)).
activity_component(5,10,pickup(rob1,book1)).
activity_component(5,11,move(rob1,library)).
activity_component(5,12,put_down(rob1,book1)).
activity_length(5,12).

activity_goal(6,tidy_all(library)).
activity_component(6,1,move(rob1,office2)).
activity_component(6,2,move(rob1,office1)).
activity_component(6,3,move(rob1,kitchen)).
activity_component(6,4,unlock(rob1,library)).
activity_component(6,5,move(rob1,library)).
activity_component(6,6,put_down(rob1,book1)).
activity_component(6,7,move(rob1,kitchen)).
activity_component(6,8,move(rob1,office1)).
activity_component(6,9,pickup(rob1,book2)).
activity_component(6,10,move(rob1,kitchen)).
activity_component(6,11,move(rob1,library)).
activity_component(6,12,put_down(rob1,book2)).
activity_length(6,12).

activity_goal(7,tidy_all(library)).
activity_component(7,1,pickup(rob1,book1)).
activity_component(7,2,move(rob1,office1)).
activity_component(7,3,move(rob1,kitchen)).
activity_component(7,4,unlock(rob1,library)).
activity_component(7,5,move(rob1,library)).
activity_component(7,6,put_down(rob1,book1)).
activity_component(7,7,move(rob1,kitchen)).
activity_component(7,8,pickup(rob1,book2)).
activity_component(7,9,move(rob1,library)).
activity_component(7,10,put_down(rob1,book2)).
activity_length(7,10).

activity_goal(8,tidy_all(library)).
activity_component(8,1,move(rob1,office2)).
activity_component(8,2,move(rob1,office1)).
activity_component(8,3,pickup(rob1,book2)).
activity_component(8,4,move(rob1,kitchen)).
activity_component(8,5,unlock(rob1,library)).
activity_component(8,6,move(rob1,library)).
activity_component(8,7,put_down(rob1,book2)).
activity_component(8,8,move(rob1,kitchen)).
activity_component(8,9,pickup(rob1,book1)).
activity_component(8,10,move(rob1,library)).
activity_component(8,11,put_down(rob1,book1)).
activity_length(8,11).

activity_goal(9,tidy_all(library)).
activity_component(9,1,unlock(rob1,library)).
activity_component(9,2,move(rob1,office1)).
activity_component(9,3,move(rob1,office2)).
activity_component(9,4,pickup(rob1,book1)).
activity_component(9,5,move(rob1,office1)).
activity_component(9,6,move(rob1,kitchen)).
activity_component(9,7,move(rob1,library)).
activity_component(9,8,put_down(rob1,book1)).
activity_component(9,9,move(rob1,kitchen)).
activity_component(9,10,pickup(rob1,book2)).
activity_component(9,11,move(rob1,library)).
activity_component(9,12,put_down(rob1,book2)).
activity_length(9,12).

activity_goal(10,tidy_all(library)).
activity_component(10,1,move(rob1,office2)).
activity_component(10,2,move(rob1,office1)).
activity_component(10,3,move(rob1,kitchen)).
activity_component(10,4,move(rob1,library)).
activity_component(10,5,put_down(rob1,book1)).
activity_component(10,6,move(rob1,kitchen)).
activity_component(10,7,move(rob1,office1)).
activity_component(10,8,pickup(rob1,book2)).
activity_component(10,9,move(rob1,kitchen)).
activity_component(10,10,move(rob1,library)).
activity_component(10,11,put_down(rob1,book2)).
activity_length(10,11).

activity_goal(11,tidy_all(library)).
activity_component(11,1,move(rob1,kitchen)).
activity_component(11,2,unlock(rob1,library)).
activity_component(11,3,move(rob1,library)).
activity_component(11,4,put_down(rob1,book2)).
activity_component(11,5,move(rob1,kitchen)).
activity_component(11,6,move(rob1,office1)).
activity_component(11,7,pickup(rob1,book1)).
activity_component(11,8,move(rob1,kitchen)).
activity_component(11,9,move(rob1,library)).
activity_component(11,10,put_down(rob1,book1)).
activity_length(11,10).

activity_goal(12,tidy_all(library)).
activity_component(12,1,unlock(rob1,library)).
activity_component(12,2,put_down(rob1,book2)).
activity_component(12,3,move(rob1,kitchen)).
activity_component(12,4,move(rob1,office1)).
activity_component(12,5,move(rob1,office2)).
activity_component(12,6,pickup(rob1,book1)).
activity_component(12,7,move(rob1,office1)).
activity_component(12,8,move(rob1,kitchen)).
activity_component(12,9,move(rob1,library)).
activity_component(12,10,put_down(rob1,book1)).
activity_length(12,10).

activity_goal(13,tidy_all(library)).
activity_component(13,1,put_down(rob1,book1)).
activity_component(13,2,unlock(rob1,library)).
activity_component(13,3,move(rob1,kitchen)).
activity_component(13,4,move(rob1,office1)).
activity_component(13,5,move(rob1,office2)).
activity_component(13,6,pickup(rob1,book2)).
activity_component(13,7,move(rob1,office1)).
activity_component(13,8,move(rob1,kitchen)).
activity_component(13,9,move(rob1,library)).
activity_component(13,10,put_down(rob1,book2)).
activity_length(13,10).

activity_goal(14,tidy_all(library)).
activity_component(14,1,pickup(rob1,book1)).
activity_component(14,2,move(rob1,kitchen)).
activity_component(14,3,unlock(rob1,library)).
activity_component(14,4,move(rob1,library)).
activity_component(14,5,put_down(rob1,book1)).
activity_component(14,6,move(rob1,kitchen)).
activity_component(14,7,move(rob1,office1)).
activity_component(14,8,pickup(rob1,book2)).
activity_component(14,9,move(rob1,kitchen)).
activity_component(14,10,move(rob1,library)).
activity_component(14,11,put_down(rob1,book2)).
activity_length(14,11).

activity_goal(15,tidy_all(library)).
activity_component(15,1,move(rob1,kitchen)).
activity_component(15,2,move(rob1,library)).
activity_component(15,3,put_down(rob1,book1)).
activity_component(15,4,move(rob1,kitchen)).
activity_component(15,5,move(rob1,office1)).
activity_component(15,6,move(rob1,office2)).
activity_component(15,7,pickup(rob1,book2)).
activity_component(15,8,move(rob1,office1)).
activity_component(15,9,move(rob1,kitchen)).
activity_component(15,10,move(rob1,library)).
activity_component(15,11,put_down(rob1,book2)).
activity_length(15,11).

activity_goal(16,tidy_all(library)).
activity_component(16,1,move(rob1,office1)).
activity_component(16,2,pickup(rob1,book2)).
activity_component(16,3,move(rob1,kitchen)).
activity_component(16,4,unlock(rob1,library)).
activity_component(16,5,move(rob1,library)).
activity_component(16,6,put_down(rob1,book2)).
activity_component(16,7,move(rob1,kitchen)).
activity_component(16,8,pickup(rob1,book1)).
activity_component(16,9,move(rob1,library)).
activity_component(16,10,put_down(rob1,book1)).
activity_length(16,10).

activity_goal(17,tidy_all(library)).
activity_component(17,1,pickup(rob1,book2)).
activity_component(17,2,move(rob1,office1)).
activity_component(17,3,move(rob1,kitchen)).
activity_component(17,4,unlock(rob1,library)).
activity_component(17,5,move(rob1,library)).
activity_component(17,6,put_down(rob1,book2)).
activity_component(17,7,move(rob1,kitchen)).
activity_component(17,8,move(rob1,office1)).
activity_component(17,9,pickup(rob1,book1)).
activity_component(17,10,move(rob1,kitchen)).
activity_component(17,11,move(rob1,library)).
activity_component(17,12,put_down(rob1,book1)).
activity_length(17,12).

activity_goal(18,tidy_all(library)).
activity_component(18,1,move(rob1,office1)).
activity_component(18,2,move(rob1,kitchen)).
activity_component(18,3,move(rob1,library)).
activity_component(18,4,put_down(rob1,book2)).
activity_component(18,5,move(rob1,kitchen)).
activity_component(18,6,move(rob1,office1)).
activity_component(18,7,move(rob1,office2)).
activity_component(18,8,pickup(rob1,book1)).
activity_component(18,9,move(rob1,office1)).
activity_component(18,10,move(rob1,kitchen)).
activity_component(18,11,move(rob1,library)).
activity_component(18,12,put_down(rob1,book1)).
activity_length(18,12).

activity_goal(19,tidy_all(library)).
activity_component(19,1,pickup(rob1,book1)).
activity_component(19,2,move(rob1,office1)).
activity_component(19,3,move(rob1,kitchen)).
activity_component(19,4,unlock(rob1,library)).
activity_component(19,5,move(rob1,library)).
activity_component(19,6,put_down(rob1,book1)).
activity_component(19,7,move(rob1,kitchen)).
activity_component(19,8,move(rob1,office1)).
activity_component(19,9,pickup(rob1,book2)).
activity_component(19,10,move(rob1,kitchen)).
activity_component(19,11,move(rob1,library)).
activity_component(19,12,put_down(rob1,book2)).
activity_length(19,12).

activity_goal(20,tidy_all(library)).
activity_component(20,1,move(rob1,library)).
activity_component(20,2,put_down(rob1,book1)).
activity_component(20,3,move(rob1,kitchen)).
activity_component(20,4,move(rob1,office1)).
activity_component(20,5,move(rob1,office2)).
activity_component(20,6,pickup(rob1,book2)).
activity_component(20,7,move(rob1,office1)).
activity_component(20,8,move(rob1,kitchen)).
activity_component(20,9,move(rob1,library)).
activity_component(20,10,put_down(rob1,book2)).
activity_length(20,10).

activity_goal(21,tidy_all(library)).
activity_component(21,1,unlock(rob1,library)).
activity_component(21,2,pickup(rob1,book1)).
activity_component(21,3,move(rob1,library)).
activity_component(21,4,put_down(rob1,book1)).
activity_component(21,5,move(rob1,kitchen)).
activity_component(21,6,move(rob1,office1)).
activity_component(21,7,move(rob1,office2)).
activity_component(21,8,pickup(rob1,book2)).
activity_component(21,9,move(rob1,office1)).
activity_component(21,10,move(rob1,kitchen)).
activity_component(21,11,move(rob1,library)).
activity_component(21,12,put_down(rob1,book2)).
activity_length(21,12).

activity_goal(22,tidy_all(library)).
activity_component(22,1,move(rob1,office1)).
activity_component(22,2,move(rob1,kitchen)).
activity_component(22,3,move(rob1,library)).
activity_component(22,4,put_down(rob1,book2)).
activity_component(22,5,move(rob1,kitchen)).
activity_component(22,6,move(rob1,office1)).
activity_component(22,7,pickup(rob1,book1)).
activity_component(22,8,move(rob1,kitchen)).
activity_component(22,9,move(rob1,library)).
activity_component(22,10,put_down(rob1,book1)).
activity_length(22,10).

activity_goal(23,tidy_all(library)).
activity_component(23,1,move(rob1,office2)).
activity_component(23,2,move(rob1,office1)).
activity_component(23,3,move(rob1,kitchen)).
activity_component(23,4,unlock(rob1,library)).
activity_component(23,5,move(rob1,library)).
activity_component(23,6,put_down(rob1,book1)).
activity_component(23,7,move(rob1,kitchen)).
activity_component(23,8,pickup(rob1,book2)).
activity_component(23,9,move(rob1,library)).
activity_component(23,10,put_down(rob1,book2)).
activity_length(23,10).

activity_goal(24,tidy_all(library)).
activity_component(24,1,move(rob1,kitchen)).
activity_component(24,2,unlock(rob1,library)).
activity_component(24,3,move(rob1,library)).
activity_component(24,4,put_down(rob1,book1)).
activity_component(24,5,move(rob1,kitchen)).
activity_component(24,6,move(rob1,office1)).
activity_component(24,7,move(rob1,office2)).
activity_component(24,8,pickup(rob1,book2)).
activity_component(24,9,move(rob1,office1)).
activity_component(24,10,move(rob1,kitchen)).
activity_component(24,11,move(rob1,library)).
activity_component(24,12,put_down(rob1,book2)).
activity_length(24,12).

activity_goal(25,tidy_all(library)).
activity_component(25,1,move(rob1,office1)).
activity_component(25,2,pickup(rob1,book2)).
activity_component(25,3,move(rob1,kitchen)).
activity_component(25,4,unlock(rob1,library)).
activity_component(25,5,move(rob1,library)).
activity_component(25,6,put_down(rob1,book2)).
activity_component(25,7,move(rob1,kitchen)).
activity_component(25,8,move(rob1,office1)).
activity_component(25,9,pickup(rob1,book1)).
activity_component(25,10,move(rob1,kitchen)).
activity_component(25,11,move(rob1,library)).
activity_component(25,12,put_down(rob1,book1)).
activity_length(25,12).

activity_goal(26,tidy_all(library)).
activity_component(26,1,move(rob1,office2)).
activity_component(26,2,move(rob1,office1)).
activity_component(26,3,move(rob1,kitchen)).
activity_component(26,4,move(rob1,library)).
activity_component(26,5,put_down(rob1,book2)).
activity_component(26,6,move(rob1,kitchen)).
activity_component(26,7,move(rob1,office1)).
activity_component(26,8,pickup(rob1,book1)).
activity_component(26,9,move(rob1,kitchen)).
activity_component(26,10,move(rob1,library)).
activity_component(26,11,put_down(rob1,book1)).
activity_length(26,11).

activity_goal(27,tidy_all(library)).
activity_component(27,1,move(rob1,office2)).
activity_component(27,2,pickup(rob1,book2)).
activity_component(27,3,move(rob1,office1)).
activity_component(27,4,move(rob1,kitchen)).
activity_component(27,5,unlock(rob1,library)).
activity_component(27,6,move(rob1,library)).
activity_component(27,7,put_down(rob1,book2)).
activity_component(27,8,move(rob1,kitchen)).
activity_component(27,9,pickup(rob1,book1)).
activity_component(27,10,move(rob1,library)).
activity_component(27,11,put_down(rob1,book1)).
activity_length(27,11).

activity_goal(28,tidy_all(library)).
activity_component(28,1,move(rob1,office2)).
activity_component(28,2,move(rob1,office1)).
activity_component(28,3,move(rob1,kitchen)).
activity_component(28,4,unlock(rob1,library)).
activity_component(28,5,move(rob1,library)).
activity_component(28,6,put_down(rob1,book2)).
activity_component(28,7,move(rob1,kitchen)).
activity_component(28,8,move(rob1,office1)).
activity_component(28,9,pickup(rob1,book1)).
activity_component(28,10,move(rob1,kitchen)).
activity_component(28,11,move(rob1,library)).
activity_component(28,12,put_down(rob1,book1)).
activity_length(28,12).

activity_goal(29,tidy_all(library)).
activity_component(29,1,move(rob1,office2)).
activity_component(29,2,move(rob1,office1)).
activity_component(29,3,move(rob1,kitchen)).
activity_component(29,4,unlock(rob1,library)).
activity_component(29,5,move(rob1,library)).
activity_component(29,6,put_down(rob1,book2)).
activity_component(29,7,move(rob1,kitchen)).
activity_component(29,8,pickup(rob1,book1)).
activity_component(29,9,move(rob1,library)).
activity_component(29,10,put_down(rob1,book1)).
activity_length(29,10).

activity_goal(30,tidy_all(library)).
activity_component(30,1,move(rob1,office3)).
activity_component(30,2,pickup(rob1,book1)).
activity_component(30,3,move(rob1,office2)).
activity_component(30,4,move(rob1,office1)).
activity_component(30,5,move(rob1,kitchen)).
activity_component(30,6,unlock(rob1,library)).
activity_component(30,7,move(rob1,library)).
activity_component(30,8,put_down(rob1,book1)).
activity_component(30,9,move(rob1,kitchen)).
activity_component(30,10,pickup(rob1,book2)).
activity_component(30,11,move(rob1,library)).
activity_component(30,12,put_down(rob1,book2)).
activity_length(30,12).

activity_goal(31,tidy_all(library)).
activity_component(31,1,move(rob1,office1)).
activity_component(31,2,move(rob1,kitchen)).
activity_component(31,3,move(rob1,library)).
activity_component(31,4,put_down(rob1,book1)).
activity_component(31,5,move(rob1,kitchen)).
activity_component(31,6,move(rob1,office1)).
activity_component(31,7,move(rob1,office2)).
activity_component(31,8,pickup(rob1,book2)).
activity_component(31,9,move(rob1,office1)).
activity_component(31,10,move(rob1,kitchen)).
activity_component(31,11,move(rob1,library)).
activity_component(31,12,put_down(rob1,book2)).
activity_length(31,12).

activity_goal(32,tidy_all(library)).
activity_component(32,1,unlock(rob1,library)).
activity_component(32,2,move(rob1,library)).
activity_component(32,3,put_down(rob1,book2)).
activity_component(32,4,move(rob1,kitchen)).
activity_component(32,5,move(rob1,office1)).
activity_component(32,6,move(rob1,office2)).
activity_component(32,7,pickup(rob1,book1)).
activity_component(32,8,move(rob1,office1)).
activity_component(32,9,move(rob1,kitchen)).
activity_component(32,10,move(rob1,library)).
activity_component(32,11,put_down(rob1,book1)).
activity_length(32,11).

activity_goal(33,tidy_all(library)).
activity_component(33,1,move(rob1,office2)).
activity_component(33,2,pickup(rob1,book1)).
activity_component(33,3,move(rob1,office1)).
activity_component(33,4,move(rob1,kitchen)).
activity_component(33,5,unlock(rob1,library)).
activity_component(33,6,move(rob1,library)).
activity_component(33,7,put_down(rob1,book1)).
activity_component(33,8,move(rob1,kitchen)).
activity_component(33,9,pickup(rob1,book2)).
activity_component(33,10,move(rob1,library)).
activity_component(33,11,put_down(rob1,book2)).
activity_length(33,11).

activity_goal(34,tidy_all(library)).
activity_component(34,1,move(rob1,office2)).
activity_component(34,2,move(rob1,office1)).
activity_component(34,3,move(rob1,kitchen)).
activity_component(34,4,unlock(rob1,library)).
activity_component(34,5,pickup(rob1,book1)).
activity_component(34,6,move(rob1,library)).
activity_component(34,7,put_down(rob1,book1)).
activity_component(34,8,move(rob1,kitchen)).
activity_component(34,9,pickup(rob1,book2)).
activity_component(34,10,move(rob1,library)).
activity_component(34,11,put_down(rob1,book2)).
activity_length(34,11).

activity_goal(35,tidy_all(library)).
activity_component(35,1,unlock(rob1,library)).
activity_component(35,2,move(rob1,office1)).
activity_component(35,3,move(rob1,office2)).
activity_component(35,4,move(rob1,office3)).
activity_component(35,5,pickup(rob1,book1)).
activity_component(35,6,move(rob1,office2)).
activity_component(35,7,move(rob1,office1)).
activity_component(35,8,move(rob1,kitchen)).
activity_component(35,9,move(rob1,library)).
activity_component(35,10,put_down(rob1,book1)).
activity_length(35,10).

activity_goal(36,tidy_all(library)).
activity_component(36,1,pickup(rob1,book2)).
activity_component(36,2,move(rob1,office1)).
activity_component(36,3,move(rob1,kitchen)).
activity_component(36,4,unlock(rob1,library)).
activity_component(36,5,move(rob1,library)).
activity_component(36,6,put_down(rob1,book2)).
activity_component(36,7,move(rob1,kitchen)).
activity_component(36,8,pickup(rob1,book1)).
activity_component(36,9,move(rob1,library)).
activity_component(36,10,put_down(rob1,book1)).
activity_length(36,10).

activity_goal(37,tidy_all(library)).
activity_component(37,1,unlock(rob1,library)).
activity_component(37,2,put_down(rob1,book1)).
activity_component(37,3,move(rob1,kitchen)).
activity_component(37,4,move(rob1,office1)).
activity_component(37,5,move(rob1,office2)).
activity_component(37,6,move(rob1,office3)).
activity_component(37,7,pickup(rob1,book2)).
activity_component(37,8,move(rob1,office2)).
activity_component(37,9,move(rob1,office1)).
activity_component(37,10,move(rob1,kitchen)).
activity_component(37,11,move(rob1,library)).
activity_component(37,12,put_down(rob1,book2)).
activity_length(37,12).

activity_goal(38,tidy_all(library)).
activity_component(38,1,move(rob1,office1)).
activity_component(38,2,move(rob1,kitchen)).
activity_component(38,3,unlock(rob1,library)).
activity_component(38,4,pickup(rob1,book1)).
activity_component(38,5,move(rob1,library)).
activity_component(38,6,put_down(rob1,book1)).
activity_component(38,7,move(rob1,kitchen)).
activity_component(38,8,pickup(rob1,book2)).
activity_component(38,9,move(rob1,library)).
activity_component(38,10,put_down(rob1,book2)).
activity_length(38,10).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
display
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
occurs(select_activity(AN),I).

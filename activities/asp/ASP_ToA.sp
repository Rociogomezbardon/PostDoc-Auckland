#const max_name = 5.
#const max_len = 17.
#const numSteps = 18.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  sorts
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
#secure_room = {library}.
#room = #secure_room + {kitchen, office1,office2}.
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
holds(locked(library),0).
holds(loc(rob1,library),0).
holds(loc(book1,office2),0).
holds(loc(book2,office2),0).
-holds(in_hand(rob1,book1),0).
-holds(in_hand(rob1,book2),0).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Needs New Activity?

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Existing Activities
activity_goal(1,tidy_all(library)).
activity_component(1,1,move(rob1,office1)).
activity_component(1,2,move(rob1,office2)).
activity_component(1,3,pickup(rob1,book2)).
activity_component(1,4,move(rob1,office1)).
activity_component(1,5,move(rob1,kitchen)).
activity_component(1,6,move(rob1,library)).
activity_component(1,7,put_down(rob1,book2)).
activity_component(1,8,move(rob1,kitchen)).
activity_component(1,9,move(rob1,office1)).
activity_component(1,10,move(rob1,office2)).
activity_component(1,11,pickup(rob1,book1)).
activity_component(1,12,move(rob1,office1)).
activity_component(1,13,move(rob1,kitchen)).
activity_component(1,14,move(rob1,library)).
activity_component(1,15,put_down(rob1,book1)).
activity_length(1,15).

activity_goal(2,tidy_all(library)).
activity_component(2,1,unlock(rob1,library)).
activity_component(2,2,move(rob1,kitchen)).
activity_component(2,3,move(rob1,office1)).
activity_component(2,4,move(rob1,office2)).
activity_component(2,5,pickup(rob1,book1)).
activity_component(2,6,move(rob1,office1)).
activity_component(2,7,move(rob1,kitchen)).
activity_component(2,8,move(rob1,library)).
activity_component(2,9,put_down(rob1,book1)).
activity_component(2,10,move(rob1,kitchen)).
activity_component(2,11,move(rob1,office1)).
activity_component(2,12,move(rob1,office2)).
activity_component(2,13,pickup(rob1,book2)).
activity_component(2,14,move(rob1,office1)).
activity_component(2,15,move(rob1,kitchen)).
activity_component(2,16,move(rob1,library)).
activity_component(2,17,put_down(rob1,book2)).

activity_goal(3,tidy_all(library)).
activity_component(3,1,move(rob1,kitchen)).
activity_component(3,2,move(rob1,office1)).
activity_component(3,3,move(rob1,office2)).
activity_component(3,4,pickup(rob1,book2)).
activity_component(3,5,move(rob1,office1)).
activity_component(3,6,move(rob1,kitchen)).
activity_component(3,7,move(rob1,library)).
activity_component(3,8,put_down(rob1,book2)).
activity_component(3,9,move(rob1,kitchen)).
activity_component(3,10,move(rob1,office1)).
activity_component(3,11,move(rob1,office2)).
activity_component(3,12,pickup(rob1,book1)).
activity_component(3,13,move(rob1,office1)).
activity_component(3,14,move(rob1,kitchen)).
activity_component(3,15,move(rob1,library)).
activity_component(3,16,put_down(rob1,book1)).
activity_length(3,16).

activity_goal(4,tidy_all(library)).
activity_component(4,1,move(rob1,office1)).
activity_component(4,2,move(rob1,office2)).
activity_component(4,3,pickup(rob1,book2)).
activity_component(4,4,move(rob1,office1)).
activity_component(4,5,move(rob1,kitchen)).
activity_component(4,6,unlock(rob1,library)).
activity_component(4,7,move(rob1,library)).
activity_component(4,8,put_down(rob1,book2)).
activity_component(4,9,move(rob1,kitchen)).
activity_component(4,10,move(rob1,office1)).
activity_component(4,11,move(rob1,office2)).
activity_component(4,12,pickup(rob1,book1)).
activity_component(4,13,move(rob1,office1)).
activity_component(4,14,move(rob1,kitchen)).
activity_component(4,15,move(rob1,library)).
activity_component(4,16,put_down(rob1,book1)).
activity_length(4,16).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
display
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
occurs(select_activity(AN),I).

#const max_name = 21.

#const max_len = 22.
#const numSteps = 23.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  sorts
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
#secure_room = {library}.
#room = #secure_room + {kitchen, office1,office2,office3}.
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



#inertial_fluent = #physical_inertial_fluent.
#defined_fluent = #physical_defined_fluent.
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
impossible(#action,#step).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% activities defining-predicates
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
activity_component(#activity_name,#index,#physical_agent_action).
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




%% defining the possible goals.
holds(tidy_book(B,R),I) :- holds(loc(B,R),I), -holds(in_hand(rob1,B),I).
holds(missing_book(R),I) :- -holds(tidy_book(B,R),I).
holds(tidy_all(R),I) :- not holds(missing_book(R),I).

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
candidate(AN) :- activity_goal(AN,G),  selected_goal(G).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Selecting candidates.
%% If it is possible to select a candidate, then it will be selected.
 occurs(select_activity(AN),0) :- not impossible(select_activity(AN),0).

%% It is impossible to select two different activities and it is impossible to select and activity 
%% which correspoinding goal is not selected
impossible(select_activity(AN1),I1) :- occurs(select_activity(AN2),I2), AN1 != AN2.
impossible(select_activity(AN),0) :- not candidate(AN).
impossible(select_activity(AN),I) :- I>0.
impossible(select_activity(AN),0) :- holds(G,0), selected_goal(G).

%% This rule ensures that the selected existing activity has the minimal sequences that reaches the goal among all existing activities:
 occurs(PAA,I) :+  occurs(select_activity(AN),0), activity_component(AN,I,PAA), occurs(A,I-1), 0<I. 

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
holds(loc(rob1,office2),0).
holds(loc(book1,office1),0).
holds(loc(book2,office1),0).
-holds(in_hand(rob1,book1),0).
-holds(in_hand(rob1,book2),0).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Existing Activities
activity_goal(1,tidy_all(library)).
activity_component(1,1,move(rob1,office2)).
activity_component(1,2,pickup(rob1,book2)).
activity_component(1,3,move(rob1,office1)).
activity_component(1,4,move(rob1,kitchen)).
activity_component(1,5,unlock(rob1,library)).
activity_component(1,6,move(rob1,library)).
activity_component(1,7,put_down(rob1,book2)).
activity_component(1,8,move(rob1,kitchen)).
activity_component(1,9,pickup(rob1,book1)).
activity_component(1,10,move(rob1,library)).
activity_component(1,11,put_down(rob1,book1)).

activity_goal(2,tidy_all(library)).
activity_component(2,1,move(rob1,office2)).
activity_component(2,2,pickup(rob1,book1)).
activity_component(2,3,move(rob1,office1)).
activity_component(2,4,move(rob1,kitchen)).
activity_component(2,5,unlock(rob1,library)).
activity_component(2,6,move(rob1,library)).
activity_component(2,7,put_down(rob1,book1)).
activity_component(2,8,move(rob1,kitchen)).
activity_component(2,9,pickup(rob1,book2)).
activity_component(2,10,move(rob1,library)).
activity_component(2,11,put_down(rob1,book2)).

activity_goal(3,tidy_all(library)).
activity_component(3,1,move(rob1,office1)).
activity_component(3,2,move(rob1,kitchen)).
activity_component(3,3,unlock(rob1,library)).
activity_component(3,4,move(rob1,library)).
activity_component(3,5,put_down(rob1,book1)).
activity_component(3,6,move(rob1,kitchen)).
activity_component(3,7,move(rob1,office1)).
activity_component(3,8,pickup(rob1,book2)).
activity_component(3,9,move(rob1,kitchen)).
activity_component(3,10,move(rob1,library)).
activity_component(3,11,put_down(rob1,book2)).

activity_goal(4,tidy_all(library)).
activity_component(4,1,unlock(rob1,library)).
activity_component(4,2,move(rob1,kitchen)).
activity_component(4,3,move(rob1,office1)).
activity_component(4,4,pickup(rob1,book2)).
activity_component(4,5,move(rob1,kitchen)).
activity_component(4,6,move(rob1,library)).
activity_component(4,7,put_down(rob1,book2)).
activity_component(4,8,move(rob1,kitchen)).
activity_component(4,9,pickup(rob1,book1)).
activity_component(4,10,move(rob1,library)).
activity_component(4,11,put_down(rob1,book1)).

activity_goal(5,tidy_all(library)).
activity_component(5,1,move(rob1,office1)).
activity_component(5,2,pickup(rob1,book2)).
activity_component(5,3,move(rob1,kitchen)).
activity_component(5,4,move(rob1,library)).
activity_component(5,5,put_down(rob1,book2)).
activity_component(5,6,move(rob1,kitchen)).
activity_component(5,7,move(rob1,office1)).
activity_component(5,8,pickup(rob1,book1)).
activity_component(5,9,move(rob1,kitchen)).
activity_component(5,10,move(rob1,library)).
activity_component(5,11,put_down(rob1,book1)).

activity_goal(6,tidy_all(library)).
activity_component(6,1,move(rob1,office3)).
activity_component(6,2,pickup(rob1,book1)).
activity_component(6,3,move(rob1,office2)).
activity_component(6,4,move(rob1,office1)).
activity_component(6,5,move(rob1,kitchen)).
activity_component(6,6,move(rob1,library)).
activity_component(6,7,put_down(rob1,book1)).
activity_component(6,8,move(rob1,kitchen)).
activity_component(6,9,pickup(rob1,book2)).
activity_component(6,10,move(rob1,library)).
activity_component(6,11,put_down(rob1,book2)).

activity_goal(7,tidy_all(library)).
activity_component(7,1,pickup(rob1,book1)).
activity_component(7,2,move(rob1,office2)).
activity_component(7,3,move(rob1,office1)).
activity_component(7,4,move(rob1,kitchen)).
activity_component(7,5,unlock(rob1,library)).
activity_component(7,6,move(rob1,library)).
activity_component(7,7,put_down(rob1,book1)).
activity_component(7,8,move(rob1,kitchen)).
activity_component(7,9,pickup(rob1,book2)).
activity_component(7,10,move(rob1,library)).
activity_component(7,11,put_down(rob1,book2)).

activity_goal(8,tidy_all(library)).
activity_component(8,1,unlock(rob1,library)).
activity_component(8,2,move(rob1,kitchen)).
activity_component(8,3,pickup(rob1,book2)).
activity_component(8,4,move(rob1,library)).
activity_component(8,5,put_down(rob1,book2)).
activity_component(8,6,move(rob1,kitchen)).
activity_component(8,7,move(rob1,office1)).
activity_component(8,8,pickup(rob1,book1)).
activity_component(8,9,move(rob1,kitchen)).
activity_component(8,10,move(rob1,library)).
activity_component(8,11,put_down(rob1,book1)).

activity_goal(9,tidy_all(library)).
activity_component(9,1,move(rob1,office1)).
activity_component(9,2,move(rob1,kitchen)).
activity_component(9,3,unlock(rob1,library)).
activity_component(9,4,move(rob1,library)).
activity_component(9,5,put_down(rob1,book2)).
activity_component(9,6,move(rob1,kitchen)).
activity_component(9,7,move(rob1,office1)).
activity_component(9,8,pickup(rob1,book1)).
activity_component(9,9,move(rob1,kitchen)).
activity_component(9,10,move(rob1,library)).
activity_component(9,11,put_down(rob1,book1)).

activity_goal(10,tidy_all(library)).
activity_component(10,1,unlock(rob1,library)).
activity_component(10,2,move(rob1,kitchen)).
activity_component(10,3,move(rob1,office1)).
activity_component(10,4,move(rob1,office2)).
activity_component(10,5,move(rob1,office3)).
activity_component(10,6,pickup(rob1,book1)).
activity_component(10,7,move(rob1,office2)).
activity_component(10,8,move(rob1,office1)).
activity_component(10,9,move(rob1,kitchen)).
activity_component(10,10,move(rob1,library)).
activity_component(10,11,put_down(rob1,book1)).

activity_goal(11,tidy_all(library)).
activity_component(11,1,pickup(rob1,book1)).
activity_component(11,2,move(rob1,office1)).
activity_component(11,3,move(rob1,kitchen)).
activity_component(11,4,move(rob1,library)).
activity_component(11,5,put_down(rob1,book1)).
activity_component(11,6,move(rob1,kitchen)).
activity_component(11,7,move(rob1,office1)).
activity_component(11,8,pickup(rob1,book2)).
activity_component(11,9,move(rob1,kitchen)).
activity_component(11,10,move(rob1,library)).
activity_component(11,11,put_down(rob1,book2)).

activity_goal(12,tidy_all(library)).
activity_component(12,1,move(rob1,office3)).
activity_component(12,2,pickup(rob1,book2)).
activity_component(12,3,move(rob1,office2)).
activity_component(12,4,move(rob1,office1)).
activity_component(12,5,move(rob1,kitchen)).
activity_component(12,6,move(rob1,library)).
activity_component(12,7,put_down(rob1,book2)).
activity_component(12,8,move(rob1,kitchen)).
activity_component(12,9,pickup(rob1,book1)).
activity_component(12,10,move(rob1,library)).
activity_component(12,11,put_down(rob1,book1)).

activity_goal(13,tidy_all(library)).
activity_component(13,1,move(rob1,office2)).
activity_component(13,2,move(rob1,office1)).
activity_component(13,3,move(rob1,kitchen)).
activity_component(13,4,move(rob1,library)).
activity_component(13,5,put_down(rob1,book1)).
activity_component(13,6,move(rob1,kitchen)).
activity_component(13,7,move(rob1,office1)).
activity_component(13,8,pickup(rob1,book2)).
activity_component(13,9,move(rob1,kitchen)).
activity_component(13,10,move(rob1,library)).
activity_component(13,11,put_down(rob1,book2)).

activity_goal(14,tidy_all(library)).
activity_component(14,1,put_down(rob1,book1)).
activity_component(14,2,move(rob1,kitchen)).
activity_component(14,3,move(rob1,office1)).
activity_component(14,4,move(rob1,office2)).
activity_component(14,5,move(rob1,office3)).
activity_component(14,6,pickup(rob1,book2)).
activity_component(14,7,move(rob1,office2)).
activity_component(14,8,move(rob1,office1)).
activity_component(14,9,move(rob1,kitchen)).
activity_component(14,10,move(rob1,library)).
activity_component(14,11,put_down(rob1,book2)).

activity_goal(15,tidy_all(library)).
activity_component(15,1,move(rob1,kitchen)).
activity_component(15,2,move(rob1,library)).
activity_component(15,3,put_down(rob1,book2)).
activity_component(15,4,move(rob1,kitchen)).
activity_component(15,5,move(rob1,office1)).
activity_component(15,6,move(rob1,office2)).
activity_component(15,7,pickup(rob1,book1)).
activity_component(15,8,move(rob1,office1)).
activity_component(15,9,move(rob1,kitchen)).
activity_component(15,10,move(rob1,library)).
activity_component(15,11,put_down(rob1,book1)).

activity_goal(16,tidy_all(library)).
activity_component(16,1,move(rob1,office2)).
activity_component(16,2,move(rob1,office1)).
activity_component(16,3,move(rob1,kitchen)).
activity_component(16,4,move(rob1,library)).
activity_component(16,5,put_down(rob1,book2)).
activity_component(16,6,move(rob1,kitchen)).
activity_component(16,7,move(rob1,office1)).
activity_component(16,8,pickup(rob1,book1)).
activity_component(16,9,move(rob1,kitchen)).
activity_component(16,10,move(rob1,library)).
activity_component(16,11,put_down(rob1,book1)).

activity_goal(17,tidy_all(library)).
activity_component(17,1,move(rob1,kitchen)).
activity_component(17,2,move(rob1,library)).
activity_component(17,3,put_down(rob1,book1)).
activity_component(17,4,move(rob1,kitchen)).
activity_component(17,5,move(rob1,office1)).
activity_component(17,6,move(rob1,office2)).
activity_component(17,7,pickup(rob1,book2)).
activity_component(17,8,move(rob1,office1)).
activity_component(17,9,move(rob1,kitchen)).
activity_component(17,10,move(rob1,library)).
activity_component(17,11,put_down(rob1,book2)).

activity_goal(18,tidy_all(library)).
activity_component(18,1,unlock(rob1,library)).
activity_component(18,2,move(rob1,library)).
activity_component(18,3,put_down(rob1,book2)).
activity_component(18,4,move(rob1,kitchen)).
activity_component(18,5,move(rob1,office1)).
activity_component(18,6,move(rob1,office2)).
activity_component(18,7,pickup(rob1,book1)).
activity_component(18,8,move(rob1,office1)).
activity_component(18,9,move(rob1,kitchen)).
activity_component(18,10,move(rob1,library)).
activity_component(18,11,put_down(rob1,book1)).

activity_goal(19,tidy_all(library)).
activity_component(19,1,move(rob1,office2)).
activity_component(19,2,move(rob1,office1)).
activity_component(19,3,pickup(rob1,book2)).
activity_component(19,4,move(rob1,kitchen)).
activity_component(19,5,unlock(rob1,library)).
activity_component(19,6,move(rob1,library)).
activity_component(19,7,put_down(rob1,book2)).
activity_component(19,8,move(rob1,kitchen)).
activity_component(19,9,pickup(rob1,book1)).
activity_component(19,10,move(rob1,library)).
activity_component(19,11,put_down(rob1,book1)).

activity_goal(20,tidy_all(library)).
activity_component(20,1,unlock(rob1,library)).
activity_component(20,2,move(rob1,library)).
activity_component(20,3,put_down(rob1,book1)).
activity_component(20,4,move(rob1,kitchen)).
activity_component(20,5,move(rob1,office1)).
activity_component(20,6,move(rob1,office2)).
activity_component(20,7,pickup(rob1,book2)).
activity_component(20,8,move(rob1,office1)).
activity_component(20,9,move(rob1,kitchen)).
activity_component(20,10,move(rob1,library)).
activity_component(20,11,put_down(rob1,book2)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
display
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
occurs(select_activity(AN),I).
occurs(move(R, L),I).
occurs(pickup(R,B),I).
occurs(put_down(R,B),I).
occurs(unlock(R,L),I).

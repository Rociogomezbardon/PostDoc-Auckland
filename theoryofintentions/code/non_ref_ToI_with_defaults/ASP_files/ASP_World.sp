#const numSteps = 1.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  sorts
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
#secure_room = {library}.
#room = #secure_room + {kitchen, office1, office2}.
#robot = {rob1}.
#book = {book1, book2}.
#object = #book.
#thing = #object + #robot.

#boolean = {true, false}.
#step = 0..numSteps.

#inertial_fluent = loc(#thing, #room) + in_hand(#robot, #object) + locked(#secure_room).
#fluent = #inertial_fluent.

#rob_action = move(#robot, #room) + pickup(#robot, #object)
	+ put_down(#robot, #object) + unlock(#robot, #secure_room).
#exo_action = exo_move(#object,#room) + exo_lock(#secure_room).
#action = #rob_action + #exo_action.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
predicates
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
next_to(#room,#room).

holds(#fluent,#step).
occurs(#action,#step).

obs(#fluent, #boolean, #step).
hpd(#action, #step).

attempt(#action, #step).
impossible(#action,#step).
try_observing(#robot,#fluent,#step).
directly_observed(#robot,#fluent,#boolean,#step).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 rules
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
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



%% State Constraints %%
-next_to(L1,L2) :- not next_to(L1,L2).

%% Reflexive property of next_to relation.
next_to(L1,L2) :- next_to(L2,L1).

%% Any object exists in only one location.
-holds(loc(T, L2), I) :- holds(loc(T, L1), I), L1!=L2.

%% If a robot is holding an object, they have the same location.
holds(loc(O, L), I) :- holds(loc(R, L), I), holds(in_hand(R, O), I).

%% Only one object can be held at any time.
-holds(in_hand(R, O2), I) :- holds(in_hand(R, O1), I), O1 != O2.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Executability Conditions %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-occurs(A,I) :- impossible(A,I).

%% Cannot move to a location if you are already there.
impossible(move(R, L), I) :- holds(loc(R, L), I).

%% Cannot move to a location if it is not next to it.
impossible(move(R, L2), I) :- holds(loc(R, L1), I), -next_to(L1,L2).

%% Cannot move to a location if it is locked.
impossible(move(R, L), I) :- holds(locked(L), I).

%% Cannot from a location if it is locked.
impossible(move(R, L2), I) :- holds(loc(R,L1), I), holds(locked(L1), I).

%% Cannot unlock if it is not locked.
impossible(unlock(R, L), I) :- -holds(locked(L), I).

%% Cannot unlock a room L1 if it's in a room L2 which is not either same as L1, or next to L1.
impossible(unlock(R, L1), I) :- holds(loc(R,L2), I), -next_to(L1,L2), L1 != L2.

%% Cannot put down an object unless it is in hand.
impossible(put_down(R, O), I) :-  -holds(in_hand(R, O), I).

%% Cannot pick up an object if it has something in hand.
impossible(pickup(R, O1), I) :- holds(in_hand(R, O2), I).

%% Cannot pick up an object if you are not in the same room.
impossible(pickup(R, O), I) :- holds(loc(R, L1), I),
			    holds(loc(O, L2), I), L1 != L2.

%% An exogenous move of an object cannot be done to the same location.
impossible(exo_move(O,L),I) :- holds(loc(O,L),I).

%% An exogenous move of an object cannot be done to a locked room.
%impossible(exo_move(O,L),I) :- holds(locked(L),I).

%% An exogenous move of an object cannot happen if it is being in hand
impossible(exo_move(O,L),I) :- holds(in_hand(R,O),I).

%% An exogenous move of an object cannot be done from a locked room.
%impossible(exo_move(O,L1),I) :- holds(loc(O,L),I), holds(locked(L),I).

%% An exogenous lock cannot be done to a locked room.
impossible(exo_lock(L),I) :- holds(locked(L),I).

%% An exogeneous move of an object and the robot picking up the object cannot be concurrent actions.
%% The preference is for the robot to pick the object.
impossible(exo_move(O,L),I) :- occurs(pickup(R,O),I).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Observation rules:


%%% oberving fluents relevant to the requested observation.
directly_observed(R,loc(R,L2),true,I) :- try_observing(R,loc(R,L),I), holds(loc(R,L2),I).

directly_observed(R,loc(O,L2),false,I) :- try_observing(R,loc(O,L),I), holds(loc(R,L2),I), -holds(loc(O,L2),I).
directly_observed(R,loc(O,L2),true,I) :- try_observing(R,loc(O,L),I), holds(loc(R,L2),I), holds(loc(O,L2),I).

directly_observed(R,in_hand(R,O2),true,I) :- try_observing(R,in_hand(R,O1),I), holds(in_hand(R,O2),I).
directly_observed(R,in_hand(R,O),false,I) :- try_observing(R,in_hand(R,O),I), -holds(in_hand(R,O),I).

directly_observed(R,locked(L),true,I) :- try_observing(R,locked(L),I), holds(loc(R,K),I), next_to(K,L), holds(locked(L),I).
directly_observed(R,locked(L),true,I) :- try_observing(R,locked(L),I), holds(loc(R,L),I), holds(locked(L),I).
directly_observed(R,locked(L),false,I) :- try_observing(R,locked(L),I), holds(loc(R,K),I), next_to(K,L), -holds(locked(L),I).
directly_observed(R,locked(L),false,I) :- try_observing(R,locked(L),I), holds(loc(R,L),I), -holds(locked(L),I).


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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% History and initial state rules

%% Take what actually happened into account.
occurs(A,I) :- hpd(A,I).


%% Reality check axioms.
:- obs(F, true, I), -holds(F, I).
:- obs(F, false, I), holds(F, I).

%% Awareness axiom.
holds(F, 0) | -holds(F, 0) :- #inertial_fluent(F).


occurs(A,I) :- attempt(A,I), not impossible(A,I).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Attributes.
next_to(office2,office1).
next_to(office1,kitchen).
next_to(kitchen,library).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%
%% History:
%%%%%%%%%%%%
%% HISTORY GOES HERE
holds(locked(library),0).
holds(loc(book2,office2),0).
holds(loc(rob1,library),0).
holds(in_hand(rob1,book1),0).
holds(loc(book1,library),0).
try_observing(rob1,loc(book2,kitchen),0).
try_observing(rob1,loc(rob1,kitchen),0).
try_observing(rob1,loc(rob1,office1),0).
try_observing(rob1,loc(book2,office2),0).
try_observing(rob1,loc(book2,library),0).
try_observing(rob1,locked(library),0).
try_observing(rob1,loc(book1,library),0).
try_observing(rob1,loc(book2,office1),0).
try_observing(rob1,loc(book1,kitchen),0).
try_observing(rob1,loc(book1,office1),0).
try_observing(rob1,loc(rob1,library),0).
try_observing(rob1,in_hand(rob1,book1),0).
try_observing(rob1,loc(book1,office2),0).
try_observing(rob1,in_hand(rob1,book2),0).
try_observing(rob1,loc(rob1,office2),0).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
display
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
holds(F,1).
occurs(A,0).
directly_observed.

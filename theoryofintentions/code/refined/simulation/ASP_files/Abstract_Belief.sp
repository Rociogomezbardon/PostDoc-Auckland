#const numSteps = 1.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% This ASP is used to update the abstract belief of the ControllerToI.
%% It does not have planning module.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
sorts
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
#step = 0..numSteps.

#object = {pen3, noteBook1, noteBook2, noteBook3, noteBook4, book1, book2, book3, book4, cup1, cup2, cup3, cup4, pen2, pen4, markerPen3, markerPen2, pen1, markerPen1, markerPen4, plate2, plate3, plate1, plate4}.
#place = {kitchen, library, office2, office1, storage_room}.
#robot = {rob1}.
#thing = #object + #robot.
#boolean = {true, false}.

#inertial_fluent = loc(#thing, #place) + in_hand(#robot, #object).
#fluent = #inertial_fluent.
#rob_action = move(#robot, #place) + pickup(#robot, #object)
	+ put_down(#robot, #object).
#exo_action = exo_move(#object,#place).
#action = #rob_action + #exo_action.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
predicates
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
next_to(#place,#place).
holds(#fluent,#step).
occurs(#action,#step).
obs(#fluent, #boolean, #step).

hpd(#action, #step).
diag(#exo_action, #step).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 rules
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%
%% Causal Laws %%
%%%%%%%%%%%%%%%%%
%% Moving changes location to target room (if the door is not locked).
holds(loc(R, L), I+1) :- occurs(move(R, L), I).

%% Grasping an object causes object to be in hand.
holds(in_hand(R, O), I+1) :- occurs(pickup(R, O), I).

%% Putting an object down causes it to no longer be in hand.
-holds(in_hand(R, O), I+1) :- occurs(put_down(R, O), I).

%% Exogenous moving an object causes the object to be in a different location.
holds(loc(O,L),I+1) :- occurs(exo_move(O,L),I).


%%%%%%%%%%%%%%%%%%%%%%%
%% State Constraints %%
%%%%%%%%%%%%%%%%%%%%%%%
%% Reflexive property of next_to relation.
next_to(L1,L2) :- next_to(L2,L1).

%% Any object exists in only one location.
-holds(loc(T, L2), I) :- holds(loc(T, L1), I), L1!=L2.

%% If a robot is holding an object, they have the same location.
holds(loc(O, L), I) :- holds(loc(R, L), I), holds(in_hand(R, O), I).

%% Only one object can be held at any time.
-holds(in_hand(R, O2), I) :- holds(in_hand(R, O1), I), O1 != O2.

%% a room is not next to another unless specified.
-next_to(L1,L2) :- not next_to(L1,L2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Executability Conditions %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Cannot move to a location if you are already there.
-occurs(move(R, L), I) :- holds(loc(R, L), I).

%% Cannot move to a location if it is not next to it.
-occurs(move(R, L2), I) :- holds(loc(R, L1), I), -next_to(L1,L2).

%% Cannot put down an object unless it is in hand.
-occurs(put_down(R, O), I) :-  -holds(in_hand(R, O), I).

%% Cannot pick up an object if it has something in hand.
-occurs(pickup(R, O1), I) :- holds(in_hand(R, O2), I).

%% Cannot pick up an object if you are not in the same room.
-occurs(pickup(R, O), I) :- holds(loc(R, L), I), not holds(loc(O, L), I).

%% An exogenous move of an object cannot be done to the same location.
-occurs(exo_move(O,L),I) :- holds(loc(O,L),I).

%% An exogenous move of an object cannot happen if it is being in hand
-occurs(exo_move(O,L),I) :- holds(in_hand(R,O),I).




%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Inertial axiom + CWA %%
%%%%%%%%%%%%%%%%%%%%%%%%%%
%% General inertia axioms.
holds(F,I+1) :- #inertial_fluent(F),
                holds(F,I),
                not -holds(F,I+1).

-holds(F,I+1) :- #inertial_fluent(F),
                 -holds(F,I),
                 not holds(F,I+1).

%% CWA for Actions.
-occurs(A,I) :- not occurs(A,I).

%% CWA for Defined Fluents.(Not defined in this domain.)
%%-holds(F,I) :- #defined_fluent(F), not holds(F,I).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% History and initial state rules %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Take what actually happened into account.
occurs(A,I) :- hpd(A,I).


%% Reality check axioms.
:- obs(F, true, I), -holds(F, I).
:- obs(F, false, I), holds(F, I).

%% Awareness axiom.
holds(F,0) | -holds(F,0) :- #inertial_fluent(F).


%%%%%%%%%%%%%%
%% Diagnosis
%%%%%%%%%%%%%%
occurs(A,I) :+ #exo_action(A), I<numSteps.
diag(A,I) :- occurs(A,I),
		not hpd(A,I),
		#exo_action(A).

%%%%%%%%%%%%%%%%
%% Attributes.
%%%%%%%%%%%%%%%%
next_to(library, kitchen).
next_to(kitchen, office1).
next_to(office1, office2).
next_to(office2, storage_room).

%%%%%%%%%%%%
%% History:
%%%%%%%%%%%%
-holds(in_hand(rob1,cup4),0).
-holds(in_hand(rob1,markerPen2),0).
-holds(in_hand(rob1,cup3),0).
-holds(in_hand(rob1,plate3),0).
holds(loc(book3,office1),0).
holds(loc(book1,library),0).
holds(loc(pen1,office1),0).
holds(loc(book4,storage_room),0).
holds(loc(noteBook3,storage_room),0).
-holds(in_hand(rob1,book2),0).
holds(loc(cup4,office1),0).
holds(loc(noteBook4,office2),0).
holds(loc(markerPen3,storage_room),0).
holds(loc(pen4,storage_room),0).
-holds(in_hand(rob1,pen1),0).
holds(loc(pen3,storage_room),0).
holds(loc(plate1,kitchen),0).
holds(loc(markerPen4,office1),0).
-holds(in_hand(rob1,cup1),0).
-holds(in_hand(rob1,plate4),0).
holds(loc(markerPen1,office1),0).
holds(loc(plate3,office1),0).
-holds(in_hand(rob1,noteBook3),0).
-holds(in_hand(rob1,noteBook4),0).
holds(loc(plate4,storage_room),0).
-holds(in_hand(rob1,plate1),0).
holds(loc(book2,storage_room),0).
-holds(in_hand(rob1,markerPen3),0).
holds(loc(cup3,library),0).
-holds(in_hand(rob1,book3),0).
holds(loc(noteBook1,library),0).
-holds(in_hand(rob1,pen3),0).
-holds(in_hand(rob1,markerPen4),0).
-holds(in_hand(rob1,cup2),0).
-holds(in_hand(rob1,book1),0).
-holds(in_hand(rob1,noteBook2),0).
holds(loc(cup1,office2),0).
holds(in_hand(rob1,pen2),0).
-holds(in_hand(rob1,noteBook1),0).
-holds(in_hand(rob1,plate2),0).
-holds(in_hand(rob1,book4),0).
-holds(in_hand(rob1,pen4),0).
holds(loc(rob1,office1),0).
holds(loc(cup2,storage_room),0).
holds(loc(noteBook2,library),0).
holds(loc(plate2,office1),0).
holds(loc(pen2,office1),0).
-holds(in_hand(rob1,markerPen1),0).
holds(loc(markerPen2,kitchen),0).

%%%%%%%%%%
display
%%%%%%%%%%
diag(A,I).
holds(F,numSteps).
-holds(in_hand(rob1,B), numSteps).

#const numSteps = 1.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% This ASP is used to update the abstract belief of the ControllerToI.
%% It does not have planning module.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
sorts
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
#step = 0..numSteps.
#integer = 0..numSteps.
#object = {book1, book2, book3, book4}.
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
unobserved(#exo_action, #step).
number_explained(#integer).

ab_d1(#object). % default d1 is: books are in the office1.
ab_d2(#object). % default d2 is: books are in office2.
ab_dL(#object). % default dL is: books are in the library.
defined_by_default(#inertial_fluent).
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
unobserved(A,I) :- occurs(A,I),
		not hpd(A,I),
		#exo_action(A).

number_explained(N) :- N = #count{EX:unobserved(EX,IX)}.
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
-holds(in_hand(rob1,book3),0).
holds(loc(book2,library),0).
-holds(in_hand(rob1,book4),0).
holds(in_hand(rob1,book1),0).
holds(loc(book4,office1),0).
holds(loc(book3,library),0).
holds(loc(rob1,library),0).
holds(loc(book1,library),0).
-holds(in_hand(rob1,book2),0).
hpd(move(rob1,kitchen), 0).

%%%%%%%%%%
display
%%%%%%%%%%
number_explained(N).
holds(F,numSteps).
-holds(in_hand(rob1,B), numSteps).

#const numSteps = 25.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
sorts
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
#step = 0..numSteps.
#boolean = {true, false}.

#book = {book_1, book_2}.
#cup = {cup_1, cup_2}.
#object = #book + #cup.
#room = {office_1, office_2, kitchen, library}.
#corridor = {corridor_1, corridor_2}.
#lift = {lift}.
#passing_space = #lift + #corridor.
#place = #room + #passing_space.
#robot = {rob}.
#thing = #object + #robot.

#shelf = {bookshelf_1, bookshelf_2, bookshelf_L, cupboard}.

#inertial_fluent = loc(#thing, #place) + in_hand(#robot, #object) + on_shelf(#object, #shelf) + lift_door_open(#lift, #corridor).
#defined_fluent =  on_some_shelf(#object).
#fluent = #inertial_fluent + #defined_fluent.
#rob_action = move(#robot, #place) + pickup(#robot, #object) + call_lift(#robot, #lift, #corridor) + request_move(#robot, #lift, #corridor) + put_on_shelf(#robot,#object,#shelf).
#exo_action = exo_move(#object,#place).
#action = #rob_action + #exo_action.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
predicates
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
next_to(#place, #place).
in_room(#shelf, #room).
holds(#fluent, #step).
occurs(#action, #step).

obs(#fluent, #boolean, #step).
hpd(#action, #step).

planning().
diagnosing().
finding_defaults().

success().
goal(#step).
something_happened(#step).

diag(#exo_action, #step).

ab_db(#book). % default db is: books are in the library's bookshelf.
ab_dc(#cup). % default dc is: cups are in the kitchen's cupboard.
ab_do(#object). % default do is: objects are not in hand.
ab_do2(#object). % default do2 is: objects are on shelves.
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

%% Calling the lift makes it come and open the door.
holds(lift_door_open(L, C), I+1) :- occurs(call_lift(R, L, C), I).

%% requesting the lift's button to move to a corridor makes the door open to that corridor.
holds(lift_door_open(L, C), I+1) :- occurs(request_move(R, L, C), I).

%% when the robot puts on something on a shelf, the object is on the shelf and not in hand any more.
holds(on_shelf(O, S), I+1) :- occurs(put_on_shelf(R, O, S), I).

%% when there is an exo_move the loc of the object changes, and it will not be on any shelf.
holds(loc(O,L), I+1) :- occurs(exo_move(O,L),I).
-holds(on_some_shelf(O), I+1) :- occurs(exo_move(O,L),I).


%%%%%%%%%%%%%%%%%%%%%%%
%% State Constraints %%
%%%%%%%%%%%%%%%%%%%%%%%
%% Reflexive property of next_to relation.
next_to(L1, L2) :- next_to(L2, L1).

%% a room is not next to another unless specified.
-next_to(L1, L2) :- not next_to(L1, L2).

%% Any object exists in only one location.
-holds(loc(T, L2), I) :- holds(loc(T, L1), I), L1!=L2.

%% If a robot is holding an object, they have the same location.
holds(loc(O, L), I) :- holds(loc(R, L), I), holds(in_hand(R, O), I).

%% Only one object can be held at any time.
-holds(in_hand(R, O2), I) :- holds(in_hand(R, O1), I), O1 != O2.

%% The lift's door is open only on one corridor.
-holds(lift_door_open(L, C1), I) :- holds(lift_door_open(L, C2), I), C1 != C2.

%% The lift closes automatically after oppening.
-holds(lift_door_open(L, C), I+1) :- holds(lift_door_open(L, C), I).


%% If a book is in a particular shelf, then it is in the room where the shelf is located in.
holds(loc(O,L), I) :- holds(on_shelf(O, S), I), in_room(S,L).

%% An object cannot be in two shelves at the same time.
-holds(on_shelf(O,S1), I) :- holds(on_shelf(O,S2), I), S1 != S2.

%% An object cannot be on shelf and in hand at the same time.
-holds(in_hand(R,O), I) :- holds(on_some_shelf(O), I).
-holds(on_shelf(O,S), I) :- holds(in_hand(R,O), I).


%%%%%%%%%%%%%%%%%%%%%%%
%% Defining Fluents  %%
%%%%%%%%%%%%%%%%%%%%%%%

%% If an object is in a particular shelf, then it is on_some_shelf.
holds(on_some_shelf(O), I) :- holds(on_shelf(O, S), I).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Executability Conditions %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Cannot move to a location if you are already there.
-occurs(move(R, L), I) :- holds(loc(R, L), I).

%% Cannot move to a location if it is not next to it.
-occurs(move(R, L2), I) :- holds(loc(R, L1), I), -next_to(L1, L2).

%% Cannot move to/from the lift from/to a corridor uless the door is open.
-occurs(move(R, L), I) :-  -holds(lift_door_open(L, C), I), holds(loc(R, C), I).
-occurs(move(R, C), I) :-  -holds(lift_door_open(L, C), I), holds(loc(R, L), I).

%% Cannot pick up an object if it has something in hand.
-occurs(pickup(R, O1), I) :- holds(in_hand(R, O2), I).

%% Cannot pick up an object if you are not in the same room.
-occurs(pickup(R, O), I) :- holds(loc(R, L), I), not holds(loc(O, L), I).

%% Cannot call a lift from a corridor that the robot is not in, or from a corridor the lift is not next to.
-occurs(call_lift(R, L, C), I) :- not holds(loc(R, C), I).
-occurs(call_lift(R, L, C), I) :- not next_to(L, C).

%% Cannot request the lift's button to move unless the robot is in the lift.
-occurs(request_move(R, L, C), I) :- not holds(loc(R, L), I).

%% Cannot put an object on a paticular shelf if the object is not in the robot's hand.
-occurs(put_on_shelf(R, O, S), I) :- -holds(in_hand(R,O), I).

%% Cannot put an object on a paticular shelf that is not located in that room.
-occurs(put_on_shelf(R, O, S), I) :- -holds(loc(R,L), I), in_room(S,L).

%% Cannot have an exo_move if the object is in the robot's hand.
-occurs(exo_move(O,L), I) :- holds(in_hand(R, O), I).

%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Inertial axiom + CWA %%
%%%%%%%%%%%%%%%%%%%%%%%%%%
%% General inertia axioms.
holds(F, I+1) :- #inertial_fluent(F),
                holds(F, I),
                not -holds(F, I+1).

-holds(F, I+1) :- #inertial_fluent(F),
                 -holds(F, I),
                 not holds(F, I+1).

%% CWA for Actions.
-occurs(A, I) :- not occurs(A, I).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% History and initial state rules %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Take what actually happened into account.
occurs(A, I) :- hpd(A, I).

%% Reality check axioms.
:- obs(F, true, I), -holds(F, I).
:- obs(F, false, I), holds(F, I).

%% Awareness axiom.
holds(F, 0) | -holds(F, 0) :- #inertial_fluent(F).


%%%%%%%%%%%
%% Flags %%
%%%%%%%%%%%
-planning :- finding_defaults.
-diagnosing :- finding_defaults.
-finding_defaults :- planning.
-diagnosing :- planning.
-planning :- diagnosing.
-finding_defaults :- diagnosing.

finding_defaults | planning | diagnosing.


%%%%%%%%%%%%%%%%%%%%
%% Planning Module
%%%%%%%%%%%%%%%%%%%%
%% Failure is not an option.
success :- goal(I), planning.
:- not success, planning.
%% Plan Actions minimally
occurs(A, I):+ not goal(I), #rob_action(A), planning.
%% Preventing preASP_refined_domain_no_planning
something_happened(I) :- occurs(A, I), planning.
:- not goal(I), not something_happened(I), planning.
:- not something_happened(0), planning.
% Cannot execute two actions at the same time.
:- occurs(A1, I), occurs(A2, I), A1 != A2, #rob_action(A1), #rob_action(A2), planning.

%%%%%%%%%%%%%%%%%%%%
%% Diagnosing Module
%%%%%%%%%%%%%%%%%%%%
occurs(A,I) :+ #exo_action(A), I<numSteps, diagnosing.
diag(A,I) :- occurs(A,I), not hpd(A,I), #exo_action(A), diagnosing.


%%%%%%%%%%%%%%%%
%% Attributes.
%%%%%%%%%%%%%%%%
next_to(office_1, library).
next_to(office_1, corridor_1).
next_to(corridor_1, library).
next_to(lift, corridor_1).

next_to(office_2, kitchen).
next_to(office_2, corridor_2).
next_to(corridor_2, kitchen).
next_to(lift, corridor_2).

in_room(bookshelf_1, office_1).
in_room(bookshelf_2, office_2).
in_room(bookshelf_L, library).
in_room(cupboard, kitchen).

%%%%%%%%%
%% Goal:
%%%%%%%%%
goal(I) :- holds(loc(book_1,library),I), holds(loc(book_2,library),I), -holds(in_hand(rob,book_1),I), -holds(in_hand(rob,book_2),I) .


%%%%%%%%%%%%%%
%% Defaults %%
%%%%%%%%%%%%%%
holds(loc(B,library),0):- #book(B), not ab_db(B), finding_defaults.
ab_db(B) :+ #book(B), -holds(loc(B,library),0), finding_defaults.
defined_by_default(loc(B,library)) :- holds(loc(B,library),0), #book(B), not ab_db(B), finding_defaults.

holds(loc(C,kitchen),0):- #cup(C), not ab_dc(C), finding_defaults.
ab_dc(C) :+ #book(C), -holds(loc(C,kitchen),0), finding_defaults.
defined_by_default(loc(C,kitchen)) :- holds(loc(C,kitchen),0), #cup(C), not ab_dc(C), finding_defaults.

holds(in_hand(rob,O),0):- #object(O), not ab_do(O), finding_defaults.
ab_do(O) :+ #object(O), -holds(in_hand(rob,O),0), finding_defaults.
defined_by_default(in_hand(rob,O)) :- holds(in_hand(rob,O),0), #object(O), not ab_do(O), finding_defaults.

holds(on_shelf(O,S),0):- #object(O), holds(loc(O,R),0), in_room(S,R), not ab_do2(O), finding_defaults.
ab_do2(O) :+ #object(O), -holds(on_some_shelf(O),0), finding_defaults.
defined_by_default(on_shelf(O,S)) :- holds(on_shelf(O,S),0), #object(O), not ab_do2(O), finding_defaults.

%by default it is on the shelf, and if not, it will be in hand (prefer do2 over do)
ab_do(O) :-  #object(O), holds(loc(O,R),0), in_room(S,R), not ab_do2(O), finding_defaults.

%by default it is in hand, if not, it is in the default location (pefer do over db and do over dc)
ab_db(B) :- #book(B), not ab_do(B), finding_defaults.
ab_dc(C) :- #cup(C), not ab_do(C), finding_defaults.


%%%%%%%%%%%%%%%%%
%% Initial State:
%%%%%%%%%%%%%%%%%
obs(loc(rob,lift),true,0).
obs(on_shelf(book_2,cupboard),true,0).
obs(on_shelf(book_1,bookshelf_2),true,0).
obs(loc(cup_1,office_1),true,0).
obs(on_shelf(cup_2,bookshelf_1),true,0).
obs(on_some_shelf(cup_1),false,0).
obs(in_hand(rob,book_1),false,0).
obs(in_hand(rob,book_2),false,0).
obs(in_hand(rob,cup_1),false,0).
obs(in_hand(rob,cup_2),false,0).
obs(lift_door_open(lift,corridor_1),false,0).
obs(lift_door_open(lift,corridor_2),false,0).
planning.


%%%%%%%%%%
display
%%%%%%%%%%

occurs.
holds(on_shelf(O,S),0).

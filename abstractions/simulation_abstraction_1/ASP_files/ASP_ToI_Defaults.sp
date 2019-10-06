#const n = 9. % maximum number of steps.
#const max_len = 8. % maximum activity_length of an activity.
#const max_name = 1.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
sorts
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
#step = 0..n.
#positive_index = 1..max_len.
#index = #positive_index + {neg1, 0}.
#activity_name = 1..max_name.
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

#physical_inertial_fluent = loc(#thing, #place) + in_hand(#robot, #object) + on_shelf(#object, #shelf) + lift_door_open(#lift, #corridor).
#possible_goal = {my_goal}.
#physical_defined_fluent =  on_some_shelf(#object) + #possible_goal.

#physical_fluent = #physical_inertial_fluent + #physical_defined_fluent.

#physical_agent_action  = move(#robot, #place) + pickup(#robot, #object) + call_lift(#robot, #lift, #corridor) + request_move(#robot, #lift, #corridor) + put_on_shelf(#robot,#object,#shelf).
#physical_exogenous_action = exo_move(#object,#place).
#mental_agent_action = start(#activity_name) + stop(#activity_name).

#mental_exogenous_action = select(#possible_goal) + abandon(#possible_goal).
#exogenous_action = #mental_exogenous_action + #physical_exogenous_action.
#agent_action = #physical_agent_action + #mental_agent_action + {finish}.
#action = #agent_action + #exogenous_action.

#mental_defined_fluent = active_activity(#activity_name) + in_progress_activity(#activity_name) +
 in_progress_goal(#possible_goal) + next_action(#activity_name, #action).
#defined_fluent = #mental_defined_fluent + #physical_defined_fluent.

#mental_inertial_fluent = active_goal(#possible_goal) + current_action_index(#activity_name, #index) + next_available_name(#activity_name).
#inertial_fluent = #physical_inertial_fluent + #mental_inertial_fluent.

#fluent = #inertial_fluent + #defined_fluent.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
predicates
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

next_to(#place, #place).
in_room(#shelf, #room).
activity_goal(#activity_name,#possible_goal).
activity_component(#activity_name,#index,#physical_agent_action).
activity_length(#activity_name,#index).


holds(#fluent,#step).
occurs(#action,#step).


%% used in history
obs(#fluent, #boolean, #step).
hpd(#action, #boolean, #step).
attempt(#action,#step).
impossible(#action, #step).
current_step(#step).
unobserved(#physical_exogenous_action, #step).

%% flags
finding_defaults(#step).
diagnosing(#step).
planning(#step).

%% three different situations determined by history
no_goal_for_activity(#activity_name, #step).
active_goal_activity(#activity_name, #step).
no_activity_for_goal(#possible_goal, #step).


%% used to create a new plan
active_goal_or_activity(#step).
some_action_occurred(#step).
intended_action(#agent_action, #step).
projected_success(#activity_name,#step).
has_intention(#step).

candidate(#activity_name,#step).
has_component(#activity_name,#index).
equal_activities(#activity_name,#activity_name).
equal_components(#activity_name,#activity_name).
different_component(#activity_name,#activity_name).

futile_activity(#activity_name,#step).

selected_goal_holds(#possible_goal,#step).
assumed_initial_condition(#physical_inertial_fluent).

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
holds(loc(R, L), I+1) :- occurs(move(R, L), I).
holds(in_hand(R, O), I+1) :- occurs(pickup(R, O), I).
holds(lift_door_open(L, C), I+1) :- occurs(call_lift(R, L, C), I).
holds(lift_door_open(L, C), I+1) :- occurs(request_move(R, L, C), I).
holds(on_shelf(O, S), I+1) :- occurs(put_on_shelf(R, O, S), I).
holds(loc(O,L), I+1) :- occurs(exo_move(O,L),I).
-holds(on_shelf(O,S), I+1) :- occurs(exo_move(O,L),I).

%%%%%%%%%%%%%%%%%%%%%%%
%% State Constraints %%
%%%%%%%%%%%%%%%%%%%%%%%
next_to(L1, L2) :- next_to(L2, L1).
-next_to(L1, L2) :- not next_to(L1, L2).
-holds(loc(T, L2), I) :- holds(loc(T, L1), I), L1!=L2.
holds(loc(O, L), I) :- holds(loc(R, L), I), holds(in_hand(R, O), I).
-holds(in_hand(R, O2), I) :- holds(in_hand(R, O1), I), O1 != O2.
-holds(lift_door_open(L, C1), I) :- holds(lift_door_open(L, C2), I), C1 != C2.
-holds(lift_door_open(L, C), I+1) :- holds(lift_door_open(L, C), I), occurs(A,I), #physical_agent_action(A).
holds(loc(O,L), I) :- holds(on_shelf(O, S), I), in_room(S,L).
-holds(on_shelf(O,S1), I) :- holds(on_shelf(O,S2), I), S1 != S2.
-holds(in_hand(R,O), I) :- holds(on_some_shelf(O), I).
-holds(on_shelf(O,S), I) :- holds(in_hand(R,O), I).

%%%%%%%%%%%%%%%%%%%%%%%
%% Defining Fluents  %%
%%%%%%%%%%%%%%%%%%%%%%%
holds(on_some_shelf(O), I) :- holds(on_shelf(O, S), I).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Executability Conditions %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-occurs(A,I) :- impossible(A,I).
impossible(move(R, L), I) :- holds(loc(R, L), I).
impossible(move(R, L2), I) :- holds(loc(R, L1), I), -next_to(L1, L2).
impossible(move(R, L), I) :-  -holds(lift_door_open(L, C), I), holds(loc(R, C), I).
impossible(move(R, C), I) :-  -holds(lift_door_open(L, C), I), holds(loc(R, L), I).
impossible(pickup(R, O1), I) :- holds(in_hand(R, O2), I).
impossible(pickup(R, O), I) :- holds(loc(R, L), I), not holds(loc(O, L), I).
impossible(call_lift(R, L, C), I) :- not holds(loc(R, C), I).
impossible(call_lift(R,L,C), I) :- not next_to(L,C).
impossible(request_move(R, L, C), I) :- not holds(loc(R, L), I).
impossible(put_on_shelf(R, O, S), I) :- -holds(in_hand(R,O), I).
impossible(put_on_shelf(R, O, S), I) :- -holds(loc(R,L), I), in_room(S,L).
impossible(exo_move(O,L), I) :- holds(in_hand(R, O), I).
impossible(exo_move(R, L), I) :- holds(loc(R, L), I).

%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Inertial axiom + CWA %%
%%%%%%%%%%%%%%%%%%%%%%%%%%
%% CWA for Defined Fluents (Thesis: 2.12)
-holds(F,I) :- #defined_fluent(F),
               not holds(F,I).

%%  General inertia axioms... (Thesis: 2.15)
holds(F,I+1) :- #inertial_fluent(F),
                holds(F,I),
                not -holds(F,I+1).
-holds(F,I+1) :- #inertial_fluent(F),
                 -holds(F,I),
                 not holds(F,I+1).

%%  CWA for Actions... (Thesis: 2.16)
-occurs(A,I) :- not occurs(A,I).

%% Awareness axiom.
holds(F, 0) | -holds(F, 0) :- #inertial_fluent(F).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% Theory of Intention %%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% (1)
holds(current_action_index(AN,0), I+1) :- occurs(start(AN),I).
holds(current_action_index(AN,neg1), I+1) :- occurs(stop(AN),I).


%% (2)
holds(active_goal(G),I+1) :- occurs(select(G),I), not holds(G,I).
-holds(active_goal(G),I+1) :- occurs(abandon(G),I).

%% (3)
holds(current_action_index(AN,K+1),I+1) :- occurs(PAA,I),
				holds(next_action(AN,PAA),I),
				holds(current_action_index(AN,K),I),
				activity_component(AN,K+1,PAA),
				#physical_agent_action(PAA).

%% (4)
holds(next_available_name(AN+1),I+1) :- holds(next_available_name(AN),I), occurs(start(AN),I).

%% (5)
-holds(current_action_index(AN,K1),I) :- holds(current_action_index(AN,K2),I),
					K1 != K2.

%% (6)
holds(active_activity(AN),I) :- -holds(current_action_index(AN,neg1),I).

%% (7)
-holds(active_goal(G),I) :- holds(G,I).

%% (8)
holds(in_progress_activity(AN),I) :- holds(active_activity(AN),I),
			holds(active_goal(G),I),
			activity_goal(AN,G).
holds(in_progress_goal(G),I) :- holds(active_activity(AN),I),
			holds(active_goal(G),I),
			activity_goal(AN,G).

%% (9)
holds(next_action(AN,PAA),I) :- holds(current_action_index(AN,K),I),
				activity_component(AN,K+1,PAA),
				holds(in_progress_activity(AN),I),
				#physical_agent_action(PAA).

%% (10)
-holds(next_available_name(AN),I) :- holds(next_available_name(AN1), I), AN != AN1.

%% (11) definition of my_goal: Included a the end.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Executability Conditions %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% (12)
impossible(start(AN), I) :- holds(active_activity(AN), I).
impossible(stop(AN), I) :- -holds(active_activity(AN), I).

%% (13)
impossible(PAA,I) :- occurs(MAA,I), #physical_agent_action(PAA), #mental_agent_action(MAA).
impossible(MAA,I) :- occurs(PAA,I), #physical_agent_action(PAA), #mental_agent_action(MAA).
impossible(MAA1,I) :- occurs(MAA2,I), #mental_agent_action(MAA1), #mental_agent_action(MAA2), MAA1 != MAA2.

%% (14) %impossible(wait,I) :- occurs(A1,I),  #physical_agent_action(A1).
%impossible(PAA,I) :- occurs(finish,I),  #physical_agent_action(PAA).
%impossible(MAA,I) :- occurs(finish,I),  #mental_agent_action(MAA).


%% (15)
impossible(select(G), I) :- holds(active_goal(G), I).
impossible(abandon(G), I) :- -holds(active_goal(G), I).

%% (16)
impossible(PAA,I) :- occurs(MEA,I), #mental_exogenous_action(MEA), #physical_agent_action(PAA).
impossible(MEA,I) :- occurs(PAA,I), #mental_exogenous_action(MEA), #physical_agent_action(PAA).

impossible(PEA,I) :- occurs(MEA,I), #mental_exogenous_action(MEA), #physical_exogenous_action(PEA).
impossible(MEA,I) :- occurs(PEA,I), #mental_exogenous_action(MEA), #physical_exogenous_action(PEA).

impossible(MAA,I) :- occurs(MEA,I), #mental_exogenous_action(MEA), #mental_agent_action(MAA).
impossible(MEA,I) :- occurs(MAA,I), #mental_exogenous_action(MEA), #mental_agent_action(MAA).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%% Automatic Behaviour %%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% History records and initial state rules %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% new rules
assumed_initial_condition(F) :- not defined_by_default(F), not obs(F,true,0), holds(F,0), diagnosing(I), current_step(I).
holds(F,0) :- assumed_initial_condition(F), planning(I), current_step(I).
holds(F,0) :- defined_by_default(F), not finding_defaults(I), current_step(I).
occurs(A,I) :- unobserved(A,I).

%%  (17)
holds(F, 0) :- obs(F, true, 0).
-holds(F, 0) :- obs(F, false, 0).

%% (18)
:-current_step(I1), I <= I1, obs(F, false, I), holds(F,I).
:-current_step(I1), I <= I1, obs(F, true, I), -holds(F,I).

%% (19)
occurs(A,I) :- hpd(A, true, I), current_step(I1), I<I1.
-occurs(A,I) :- hpd(A, false, I), current_step(I1), I<I1.

% (20)
occurs(AA,I) :- current_step(I1),
   		I<I1,
   		attempt(AA,I),
   		not impossible(AA,I),
      #agent_action(AA).

:- current_step(I1),
	I<I1,
  	occurs(AA,I),
 	not attempt(AA,I),
  	#agent_action(AA).

%% (21)
impossible(select(G),I) :- current_step(I1),
			I<I1,
      occurs(select(G1),I),
			G1 != G.
impossible(select(G),I) :- current_step(I1),
			I<I1,
      holds(active_activity(AN),I).
impossible(select(G),I) :- current_step(I1),
			I<I1,
      holds(active_goal(G1),I).

%  (22)
holds(current_action_index(AN,neg1),0).
-holds(active_goal(G),0).
holds(next_available_name(1),0).


% (24)
:- current_step(I1),
	I<=I1,
	occurs(select(G),I),
	not hpd(select(G),true,I).

:- current_step(I1),
	I<=I1,
	occurs(abandon(G),I),
	not hpd(abandon(G),true,I).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Diagnosys Generation %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% (25)
occurs(PEA,I) :- unobserved(PEA,I).

%%(26)
unobserved(PEA,I1) :+ current_step(I),
		diagnosing(I),
		I1<I,
		not hpd(PEA,true,I1),
		#physical_exogenous_action(PEA).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Rules for determining intended action %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% (28)
different_component(AN,AN1) :- activity_component(AN,K,AA),
	activity_component(AN1,K,AA1),
	AA != AA1.
equal_components(AN,AN1) :- activity_length(AN,L),
			activity_length(AN1,L),
			not different_component(AN,AN1).

equal_activities(AN,AN1) :- activity_goal(AN,G),
			activity_goal(AN1,G),
			equal_components(AN,AN1).

:- equal_activities(AN,AN1), AN != AN1.




%  (29)
no_activity_for_goal(G,I) :- current_step(I),
			planning(I),
			holds(active_goal(G),I),
      -holds(in_progress_goal(G),I).

%% (30)
no_goal_for_activity(AN,I) :- current_step(I),
			planning(I),
			holds(active_activity(AN),I),
			activity_goal(AN,G),
			-holds(active_goal(G),I).

%% (31)
active_goal_activity(AN,I) :- current_step(I),
			planning(I),
			holds(in_progress_activity(AN),I).


% (32)
intended_action(finish,I) :- current_step(I),
			planning(I),
			no_goal_for_activity(AN,I).



% (33)
selected_goal_holds(G,I) :- current_step(I),
    holds(G,I),
    occurs(select(G),I1),
    planning(I),
    I1 <= I.

% (34)
intended_action(finish,I) :- current_step(I),
    planning(I),
    selected_goal_holds(G,I).


%%%%%% Finding intended action for active_goal_activity
%% (35)
occurs(AA,I1) :- current_step(I),
		planning(I),
		I <= I1,
		active_goal_activity(AN,I),
		holds(in_progress_activity(AN),I1),
		holds(next_action(AN,AA),I1),
		not impossible(AA,I1),
		#agent_action(AA).

% (36)
projected_success(AN,I) :- current_step(I),
			planning(I),
			I < I1,
      holds(active_activity(AN),I1),
      activity_goal(AN,G),
 			holds(G,I1).
% (37)
-projected_success(AN,I) :-  current_step(I),
			planning(I),
			not projected_success(AN,I).


%% (38)
intended_action(AA,I) :- current_step(I),
			planning(I),
      active_goal_activity(AN,I),
			holds(next_action(AN,AA),I),
			projected_success(AN,I),
			#agent_action(AA).

%% (39)
:- current_step(I),
	planning(I),
	active_goal_activity(AN,I),
	-projected_success(AN,I),
	not futile_activity(AN,I).

%% (40)
futile_activity(AN,I) :+ current_step(I),
	planning(I),
  active_goal_activity(AN,I),
	-projected_success(AN,I).

%% (41)
intended_action(stop(AN),I) :- current_step(I),
	planning(I),
	active_goal_activity(AN,I),
	futile_activity(AN,I).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Creating a new activity by specifying its goal, activity_components and activity_length.%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% (42)
candidate(AN,I) :-  current_step(I),
		planning(I),
		no_activity_for_goal(G,I),
		holds(next_available_name(AN),I).


%% (43)
activity_goal(AN,G) :-  current_step(I),
		planning(I),
    no_activity_for_goal(G,I),
		candidate(AN,I).

%%  (44)
impossible(start(AN),I) :-  current_step(I),
			planning(I),
      no_activity_for_goal(G,I),
      activity_goal(AN,G),
			occurs(start(AN1),I),
	 		AN != AN1.

%%  (45)
occurs(start(AN),I) :- current_step(I),
			planning(I),
      no_activity_for_goal(G,I),
			candidate(AN,I),
      activity_goal(AN,G),
			not impossible(start(AN),I).


%% (46)
some_action_occurred(I1) :-  current_step(I),
			planning(I),
			I <= I1,
			occurs(A,I1).


%% (47) original
occurs(PAA,I1) :+ current_step(I),
		planning(I),
    no_activity_for_goal(G,I),
		candidate(AN,I),
		occurs(start(AN),I),
		I < I1,
		some_action_occurred(I1-1),
		#physical_agent_action(PAA).



% (48)
activity_component(AN,I1-I,PAA) :- current_step(I),
		planning(I),
		I < I1,
		no_activity_for_goal(G,I),
		candidate(AN,I),
		occurs(start(AN),I),
		occurs(PAA,I1),
		#physical_agent_action(PAA).

% (49)
:- current_step(I),
	planning(I),
	no_activity_for_goal(G,I),
	candidate(AN,I),
	activity_component(AN,K,PAA1),
	activity_component(AN,K,PAA2),
	PAA1 != PAA2,
	#physical_agent_action(PAA1),
	#physical_agent_action(PAA2).

% (50)
has_component(AN,K) :- current_step(I),
		planning(I),
                no_activity_for_goal(G,I),
		candidate(AN,I),
		occurs(start(AN),I),
		activity_component(AN,K,C).

% (51)
activity_length(AN,K) :- current_step(I),
		planning(I),
    no_activity_for_goal(G,I),
		candidate(AN,I),
		occurs(start(AN),I),
		has_component(AN,K),
    not has_component(AN,K+1).

% (52)
intended_action(start(AN),I) :- current_step(I),
		planning(I),
		no_activity_for_goal(G,I),
		candidate(AN,I),
		occurs(start(AN),I),
		projected_success(AN,I).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%% Engine %%%%%%%%%%%%%%%%
% (53)
has_intention(I) :- intended_action(A,I).
:- current_step(I),
	planning(I),
	0<I,
	not has_intention(I).

%%%%%%%%%%%
%% Flags %%
%%%%%%%%%%%

finding_defaults(I) | planning(I) | diagnosing(I) :- current_step(I).

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

%%%%%%%%%%%%%%
%% Defaults %%
%%%%%%%%%%%%%%
%by default books are int eh library
holds(loc(B,library),0):- #book(B), not ab_db(B), finding_defaults(I).
ab_db(B) :+ #book(B), -holds(loc(B,library),0), finding_defaults(I).
defined_by_default(loc(B,library)) :- holds(loc(B,library),0), #book(B), not ab_db(B), finding_defaults(I).

%by default cups are in the kitchen
holds(loc(C,kitchen),0):- #cup(C), not ab_dc(C), finding_defaults(I).
ab_dc(C) :+ #cup(C), -holds(loc(C,kitchen),0), finding_defaults(I).
defined_by_default(loc(C,kitchen)) :- holds(loc(C,kitchen),0), #cup(C), not ab_dc(C), finding_defaults(I).

%by default robot is holding the object
holds(in_hand(rob,O),0):- #object(O), not ab_do(O), finding_defaults(I).
ab_do(O) :+ #object(O), -holds(in_hand(rob,O),0), finding_defaults(I).
defined_by_default(in_hand(rob,O)) :- holds(in_hand(rob,O),0), #object(O), not ab_do(O), finding_defaults(I).

%by default if an object is in a room with a shelf, the object will be on the self.
holds(on_shelf(O,S),0):- #object(O), holds(loc(O,R),0), in_room(S,R), not ab_do2(O), finding_defaults(I).
ab_do2(O) :+ #object(O), -holds(on_some_shelf(O),0), finding_defaults(I).
defined_by_default(on_shelf(O,S)) :- holds(on_shelf(O,S),0), #object(O), not ab_do2(O), finding_defaults(I).

%by default it is on the shelf, and if not, it will be in hand (prefer do2 over do)
ab_do(O) :-  #object(O), holds(loc(O,R),0), in_room(S,R), not ab_do2(O), holds(loc(rob,R),0), finding_defaults(I).

%by default it is in hand, if not, it is in the default location, i.e. kitchen if it is a cup and library if it is a book (pefer do over db and do over dc)
ab_db(B) :- #book(B), not ab_do(B), finding_defaults(I).
ab_dc(C) :- #cup(C), not ab_do(C), finding_defaults(I).

%%%%%%%%%
%% Goal:
%%%%%%%%%
%% GOAL GOES HERE
holds(my_goal,I) :- holds(loc(book_1,library),I), holds(loc(book_2,library),I), -holds(in_hand(rob,book_1),I), -holds(in_hand(rob,book_2),I) .

%%%%%%%%%%%%%%%%%
%% Current Step:
%%%%%%%%%%%%%%%%%
%% CURRENT STEP GOES HERE
current_step(8).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Initial State and history:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% HISTORY GOES HERE
obs(loc(rob,office_1),true,0).
obs(in_hand(rob,book_1),true,0).
obs(loc(book_2,office_1),true,0).
obs(loc(cup_1,office_1),true,0).
obs(loc(cup_2,office_1),true,0).
obs(in_hand(rob,cup_1),false,0).
obs(loc(rob,office_1),true,0).
obs(in_hand(rob,book_2),false,0).
obs(in_hand(rob,cup_2),false,0).
obs(loc(book_1,office_1),true,0).
hpd(select(my_goal), true,0).
activity_goal(1,my_goal).
activity_component(1,1,move(rob,library)).
activity_component(1,4,pickup(rob,book_2)).
activity_component(1,2,put_on_shelf(rob,book_1,bookshelf_L)).
activity_component(1,6,put_on_shelf(rob,book_2,bookshelf_L)).
activity_component(1,3,move(rob,office_1)).
activity_component(1,5,move(rob,library)).
activity_length(1,6).
attempt(start(1),1).
attempt(move(rob,library),2).
obs(loc(book_1,library),true,3).
obs(loc(book_2,library),false,3).
obs(in_hand(rob,book_1),true,3).
obs(loc(rob,library),true,3).
obs(in_hand(rob,book_2),false,3).
attempt(put_on_shelf(rob,book_1,bookshelf_L),3).
obs(loc(book_1,library),true,4).
obs(in_hand(rob,book_1),false,4).
obs(in_hand(rob,book_1),true,3).
obs(loc(book_2,library),false,4).
obs(in_hand(rob,book_2),false,4).
attempt(move(rob,office_1),4).
obs(in_hand(rob,book_1),false,5).
obs(loc(book_1,office_1),false,5).
obs(loc(rob,office_1),true,5).
obs(in_hand(rob,book_2),false,5).
obs(loc(book_2,office_1),true,5).
attempt(pickup(rob,book_2),5).
obs(in_hand(rob,book_1),false,6).
obs(loc(book_2,office_1),true,6).
obs(in_hand(rob,book_2),true,6).
obs(loc(book_1,office_1),false,6).
attempt(move(rob,library),6).
obs(loc(rob,library),true,7).
obs(in_hand(rob,book_1),false,7).
obs(loc(book_1,library),true,7).
obs(in_hand(rob,book_2),true,7).
obs(loc(book_2,library),true,7).
attempt(put_on_shelf(rob,book_2,bookshelf_L),7).
obs(loc(book_2,library),true,8).
obs(in_hand(rob,book_2),false,8).
obs(in_hand(rob,book_1),false,8).
obs(loc(book_1,library),true,8).
obs(in_hand(rob,book_2),true,7).
finding_defaults(8).
%%%%%%
display
%%%%%%
defined_by_default.
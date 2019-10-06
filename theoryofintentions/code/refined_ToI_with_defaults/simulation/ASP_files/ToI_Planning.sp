#const numSteps = 9. % maximum number of steps.
#const max_len = 8. % maximum activity_length of an activity.
#const max_name = 1.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% This ASP is used to plan with ToI and to Diagnose with ToI.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
sorts
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
#step = 0..numSteps.
#book = {book1, book2, book3, book4}.
#object = #book.
#place = {kitchen, library, office2, office1, storage_room}.
#robot = {rob1}.
#thing = #object + #robot.

#boolean = {true, false}.

#integer = 0..numSteps.
#positive_index = 1..max_len.
#index = #positive_index + {neg1, 0}.
#activity_name = 1..max_name.

#physical_inertial_fluent = loc(#thing, #place) + in_hand(#robot, #object).
#possible_goal = {my_goal}.
#physical_defined_fluent = #possible_goal.

#physical_fluent = #physical_inertial_fluent + #physical_defined_fluent.

#physical_agent_action = move(#robot,#place) + pickup(#robot,#object) + put_down(#robot,#object).
#physical_exogenous_action = exo_move(#object, #place).
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

%%%%%%%%%%%%%
predicates
%%%%%%%%%%%%%
%% static relations
next_to(#place,#place).
holds(#fluent,#step).
occurs(#action,#step).
activity_goal(#activity_name,#possible_goal).
activity_component(#activity_name,#index,#physical_agent_action).
activity_length(#activity_name,#index).

%% used in history
obs(#fluent, #boolean, #step).
hpd(#action, #boolean, #step).
attempt(#action,#step).
impossible(#action, #step).
current_step(#step).
unobserved(#physical_exogenous_action, #step).

%% flags
planning(#step).
explaining(#step).


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

ab_d1(#object). % default d1 is: books are in the office1.
ab_d2(#object). % default d2 is: books are in office2.
ab_dL(#object). % default dL is: books are in the library.
defined_by_default(#inertial_fluent).

need_explanation(#integer,#step).
number_unobserved(#integer,#step).

current_state(#physical_fluent,#step).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
rules
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Physical Causal Laws %%
%%%%%%%%%%%%%%%%%%%%%%%%%%
holds(loc(R, L), I+1) :- occurs(move(R, L), I).
holds(in_hand(R,O),I+1) :- occurs(pickup(R,O), I).
-holds(in_hand(R,O),I+1) :- occurs(put_down(R,O), I).
holds(loc(O,L),I+1) :- occurs(exo_move(O,L),I).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Physical State Constraints %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
next_to(L1,L2) :- next_to(L2,L1).
-holds(loc(T, L2), I) :- holds(loc(T, L1), I), L1!=L2.
holds(loc(O,L), I) :- holds(loc(R,L), I) , holds(in_hand(R,O),I).
-holds(in_hand(R, O2), I) :- holds(in_hand(R, O1), I), O1!=O2.
-next_to(L1,L2) :- not next_to(L1,L2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Physical Executability Condition %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-occurs(A,I) :- impossible(A,I).
%% (Desc: 10 - 14)
impossible(move(R,L),I) :- holds(loc(R,L),I).
impossible(move(R,L2),I) :- holds(loc(R,L1),I), -next_to(L1,L2).
impossible(put_down(R,O), I) :- -holds(in_hand(R,O), I).
impossible(pickup(R,O1), I) :- holds(in_hand(R,O2), I).
impossible(pickup(R,O), I) :- holds(loc(R,L), I), not holds(loc(O,L), I).
impossible(exo_move(O,L),I) :- holds(loc(O,L),I).
impossible(exo_move(O,L),I) :- holds(in_hand(R,L),I).


%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Inertial axiom + CWA %%
%%%%%%%%%%%%%%%%%%%%%%%%%%
%% CWA for Defined Fluents (Thesis: 2.12)
-holds(F,I) :- #defined_fluent(F), not holds(F,I).

%%  General inertia axioms... (Thesis: 2.15)
holds(F,I+1) :- #inertial_fluent(F),  holds(F,I), not -holds(F,I+1).
-holds(F,I+1) :- #inertial_fluent(F), -holds(F,I), not holds(F,I+1).

%%  CWA for Actions... (Thesis: 2.16)
-occurs(A,I) :- not occurs(A,I).

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
-holds(current_action_index(AN,K1),I) :- holds(current_action_index(AN,K2),I),	K1 != K2.

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
impossible(PEA,I) :- occurs(MAA,I), #physical_exogenous_action(PEA), #mental_agent_action(MAA).


%%%%%%%%%%%%%%%%%%%%%%%%%
%% Automatic Behaviour %%
%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% History records and initial state rules %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Awareness axiom.
holds(F,0) | -holds(F,0) :- #physical_inertial_fluent(F).

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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Rules for determining intended action %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% (29)
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

%  (30)
no_activity_for_goal(G,I) :- current_step(I),
			planning(I),
			holds(active_goal(G),I),
                        -holds(in_progress_goal(G),I).

%% (31)
no_goal_for_activity(AN,I) :- current_step(I),
			planning(I),
			holds(active_activity(AN),I),
			activity_goal(AN,G),
			-holds(active_goal(G),I).

%% (32)
active_goal_activity(AN,I) :- current_step(I),
			planning(I),
			holds(in_progress_activity(AN),I).


% (22)
intended_action(finish,I) :- current_step(I),
			planning(I),
			no_goal_for_activity(AN,I).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Finding intended action for active_goal_activity
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% (34)
occurs(AA,I1) :- current_step(I),
		planning(I),
		I <= I1,
		active_goal_activity(AN,I),
		holds(in_progress_activity(AN),I1),
		holds(next_action(AN,AA),I1),
		not impossible(AA,I1),
		#agent_action(AA).

% (35)
projected_success(AN,I) :- current_step(I),
			planning(I),
			I < I1,
		     	holds(active_activity(AN),I1),
		     	activity_goal(AN,G),
 			holds(G,I1).
% (36)
-projected_success(AN,I) :-  current_step(I),
			planning(I),
			not projected_success(AN,I).


%% (37)
intended_action(AA,I) :- current_step(I),
			planning(I),
                        active_goal_activity(AN,I),
			holds(next_action(AN,AA),I),
			projected_success(AN,I),
			#agent_action(AA).

%% (38)
:- current_step(I),
	planning(I),
	active_goal_activity(AN,I),
	-projected_success(AN,I),
	not futile_activity(AN,I).

%% (39)
futile_activity(AN,I) :+ current_step(I),
	planning(I),
        active_goal_activity(AN,I),
	-projected_success(AN,I).

%% (40)
intended_action(stop(AN),I) :- current_step(I),
	planning(I),
	active_goal_activity(AN,I),
	futile_activity(AN,I).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Creating a new activity by specifying its goal, activity_components and activity_length.%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% (41)
candidate(AN,I) :-  current_step(I),
		planning(I),
		no_activity_for_goal(G,I),
		holds(next_available_name(AN),I).

%% (42)
activity_goal(AN,G) :-  current_step(I),
		planning(I),
            	no_activity_for_goal(G,I),
		candidate(AN,I).

%%  (43)
impossible(start(AN),I) :-  current_step(I),
			planning(I),
      no_activity_for_goal(G,I),
      activity_goal(AN,G),
			occurs(start(AN1),I),
	 		AN != AN1.

%%  (44)
occurs(start(AN),I) :- current_step(I),
			planning(I),
   	  no_activity_for_goal(G,I),
			candidate(AN,I),
   	  activity_goal(AN,G),
			not impossible(start(AN),I).

%% (48)
some_action_occurred(I1) :-  current_step(I),
			planning(I),
			I <= I1,
			occurs(A,I1).

%% (49) original
occurs(PAA,I1) :+ current_step(I),
		planning(I),
    no_activity_for_goal(G,I),
		candidate(AN,I),
		occurs(start(AN),I),
		I < I1,
		some_action_occurred(I1-1),
		#physical_agent_action(PAA).

% (50)
activity_component(AN,I1-I,PAA) :- current_step(I),
		planning(I),
		I < I1,
		no_activity_for_goal(G,I),
		candidate(AN,I),
		occurs(start(AN),I),
		occurs(PAA,I1),
		#physical_agent_action(PAA).

% (51)
:- current_step(I),
	planning(I),
	no_activity_for_goal(G,I),
	candidate(AN,I),
	activity_component(AN,K,PAA1),
	activity_component(AN,K,PAA2),
	PAA1 != PAA2,
	#physical_agent_action(PAA1),
	#physical_agent_action(PAA2).

% (52)
has_component(AN,K) :- current_step(I),
		planning(I),
    no_activity_for_goal(G,I),
		candidate(AN,I),
		occurs(start(AN),I),
		activity_component(AN,K,C).

% (53)
activity_length(AN,K) :- current_step(I),
		planning(I),
    no_activity_for_goal(G,I),
		candidate(AN,I),
		occurs(start(AN),I),
		has_component(AN,K),
    not has_component(AN,K+1).

% (54)
intended_action(start(AN),I) :- current_step(I),
		planning(I),
		no_activity_for_goal(G,I),
		candidate(AN,I),
		occurs(start(AN),I),
		projected_success(AN,I).

%% latest addition
selected_goal_holds(G,I) :- current_step(I),
		holds(G,I),
		occurs(select(G),I1),
		I1 <= I.

intended_action(finish,I) :- current_step(I),
			planning(I),
			selected_goal_holds(G,I).


%%%%%%%%%%%%%%
%% Defaults %%
%%%%%%%%%%%%%%
holds(loc(B,office1),0):- #book(B), not ab_d1(B),  current_step(I).
ab_d1(B) :+ #book(B), -holds(loc(B,office1),0), explaining(I), current_step(I).
defined_by_default(loc(B,office1)) :- holds(loc(B,office1),0), #book(B), not ab_d1(B), current_step(I).

holds(loc(B,library),0):- #book(B), not ab_dL(B), current_step(I).
ab_dL(B) :+ #book(B), -holds(loc(B,library),0), explaining(I), current_step(I).
defined_by_default(loc(B,library)) :- holds(loc(B,library),0), #book(B), not ab_dL(B), current_step(I).

%% Initial choices of undetermined fluents.
holds(loc(B,library),0) | holds(loc(B,kitchen),0) | holds(loc(B,office1),0) | holds(loc(B,office2),0) | holds(loc(B,storage_room),0):- #book(B).

-holds(loc(B,office1),0) :- ab_d1(B), not explaining(I).
-holds(loc(B,library),0) :- ab_dL(B), not explaining(I).
holds(F,0) :- defined_by_default(F), not explaining(I).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Diagnosys Generation %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% (25)
occurs(PEA,I) :- unobserved(PEA,I).

%%(26)
unobserved(PEA,I1) :+ current_step(I),
		explaining(I),
		I1<I,
		not hpd(PEA,true,I1),
		#physical_exogenous_action(PEA).

%%(27)
number_unobserved(N,I) :- current_step(I),
    explaining(I),
		N = #count{EX:unobserved(EX,IX)}.

%%(28)
    :-current_step(I),
    planning(I),
    explaining(I),
    number_unobserved(N,I),
    need_explanation(X,I),
    N!= X.


%%%%%%%%%%%%
%% Engine %%
%%%%%%%%%%%%
% (55)
has_intention(I) :- intended_action(A,I).
:- current_step(I),
	planning(I),
	0<I,
	not has_intention(I).


%% Informative:
current_state(F,I) :- holds(F,I), current_step(I), #physical_fluent(F), F != my_goal.
-current_state(F,I) :- -holds(F,I), current_step(I), #physical_fluent(F), F != my_goal.


%%%%%%%%%%%%%%%%
%% Attributes.
%%%%%%%%%%%%%%%%
next_to(library, kitchen).
next_to(kitchen, office1).
next_to(office1, office2).
next_to(office2, storage_room).


%%%%%%%%%
%% Goal:
%%%%%%%%%
holds(my_goal,I) :- holds(loc(book4,library),I).


%%%%%%%%%%%%%%%%%
%% Current Step:
%%%%%%%%%%%%%%%%%
current_step(3).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Initial State and history:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

defined_by_default(loc(book3,library)).
defined_by_default(loc(book1,library)).
defined_by_default(loc(book2,library)).
defined_by_default(loc(book4,office1)).
ab_d1(book3).
ab_d1(book2).
ab_d1(book1).
ab_dL(book4).
-holds(in_hand(rob1,book4),0).
holds(in_hand(rob1,book1),0).
-holds(in_hand(rob1,book3),0).
holds(loc(rob1,library),0).
-holds(in_hand(rob1,book2),0).
hpd(select(my_goal), true,0).
attempt(finish,1).
obs(my_goal,false,1).
attempt(start(1),2).
activity_goal(1,my_goal).
activity_length(1,6).
activity_component(1,1,move(rob1,kitchen)).
activity_component(1,2,put_down(rob1,book1)).
activity_component(1,3,move(rob1,office1)).
activity_component(1,4,pickup(rob1,book4)).
activity_component(1,5,move(rob1,kitchen)).
activity_component(1,6,move(rob1,library)).
activity_goal(1,my_goal).
activity_length(1,6).
activity_component(1,1,move(rob1,kitchen)).
activity_component(1,2,put_down(rob1,book1)).
activity_component(1,3,move(rob1,office1)).
activity_component(1,4,pickup(rob1,book4)).
activity_component(1,5,move(rob1,kitchen)).
activity_component(1,6,move(rob1,library)).
planning(3).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
display
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

activity_goal.
activity_component.
futile_activity.
activity_length.
intended_action.
selected_goal_holds.
unobserved.
current_state.
-current_state.

#const numSteps = 27.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
sorts
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
#step = 0..numSteps.
%% SORTS GO HERE
#coarse_place = {storage_room}.
#coarse_object = {book4}.
#object = {ref1_book4,ref2_book4,ref3_book4,ref4_book4}.
#place = {c25,c26,c27,c28,c29,c30}.
#robot = {rob1}.
#coarse_thing = #coarse_object + #robot.
#thing = #object + #robot.
#boolean = {false,true}.
#outcome = {false,true,undet}.
#physical_inertial_fluent = loc(#thing,#place) + in_hand(#robot,#object).
#physical_defined_fluent = coarse_loc(#coarse_thing,#coarse_place) + coarse_in_hand(#robot,#coarse_object).
#physical_fluent = #physical_inertial_fluent + #physical_defined_fluent.
#knowledge_inertial_fluent = directly_observed(#robot,#physical_inertial_fluent,#outcome) + can_be_tested(#robot,#physical_inertial_fluent,#boolean).
#knowledge_defined_fluent = observed(#robot,#physical_fluent,#outcome) + may_discover(#robot,#physical_defined_fluent,#boolean) + indirectly_observed(#robot,#physical_defined_fluent,#outcome).
#inertial_fluent = #knowledge_inertial_fluent + #physical_inertial_fluent.
#defined_fluent = #knowledge_defined_fluent + #physical_defined_fluent.
#fluent = #inertial_fluent + #defined_fluent.
#rob_action = test(#robot,#physical_inertial_fluent,#boolean) + pickup(#robot,#object) + move(#robot,#place) + put_down(#robot,#object).
#exo_action = exo_move(#object,#place).
#action = #exo_action + #rob_action.
#refined_component = #object + #place.
#coarse_component = #coarse_object + #coarse_place.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
predicates
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
comp(#refined_component, #coarse_component).
holds(#fluent, #step).

%% NEXT LINES NOT RELEVANT TO INFERRING
next_to(#place, #place).
coarse_next_to(#coarse_place, #coarse_place).
occurs(#action, #step).
obs(#fluent, #boolean, #step).
hpd(#action, #step).
success().
goal(#step).
something_happened(#step).
%% NEXT LINES ARE RELEVANT TO INFERRING
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 rules
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% NEXT LINES NOT RELEVANT TO INFERRING

%%%%%%%%%%%%%%%%%
%% Causal Laws %%
%%%%%%%%%%%%%%%%%
%% CAUSAL LAWS GO HERE
% Moving changes location to target room (if the door is not locked).
holds(loc(R, C), I+1) :- occurs(move(R, C), I).

% Grasping an object causes object to be in hand.
holds(in_hand(R, OP), I+1) :- occurs(pickup(R, OP), I).

% Putting an object down causes it to no longer be in hand.
-holds(in_hand(R, OP), I+1) :- occurs(put_down(R, OP), I).


%%%%%%%%%%%%%%%%%%%%%%%
%% State Constraints %%
%%%%%%%%%%%%%%%%%%%%%%%
%% STATE CONSTRAINTS GO HERE
% Reflexive property of next_to relation.
next_to(C1, C2) :- next_to(C2, C1), #place(C1), #place(C2).
coarse_next_to(Z1, Z2) :- next_to(C1, C2), comp(C1, Z1), comp(C2, Z2), Z1!=Z2, #place(C1), #place(C2).

% Any object exists in only one refined location.
-holds(loc(T, C2), I) :- holds(loc(T, C1), I), C1!=C2.

% If a robot is holding an object, they have the same location.
holds(loc(OP, C), I) :- holds(loc(R, C), I), holds(in_hand(R, OP), I).

% Only one object can be held at any time.
-holds(in_hand(R, OP2), I) :- holds(in_hand(R, OP1), I), OP1!=OP2.
-holds(coarse_in_hand(R, OP2), I) :- holds(coarse_in_hand(R, OP1), I), OP1!=OP2.

% A place/coarse_place is not next to another unless specified.
-next_to(L1,L2) :- not next_to(L1,L2), #place(L1), #place(L2).
-coarse_next_to(L1,L2) :- not coarse_next_to(L1,L2), #coarse_place(L1), #coarse_place(L2).

% A thing cannot be at two places at the same time.
-holds(coarse_loc(T, C2), I) :- holds(coarse_loc(T, C1), I), C1!=C2.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Executability Conditions %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Cannot move to a location if you are already there.
-occurs(move(R, C), I) :- holds(loc(R, C), I).

% Cannot move to a location if it is not next to it.
-occurs(move(R, C2), I) :- holds(loc(R, C1), I), -next_to(C1,C2).

% Cannot put down an object unless it is in hand.
-occurs(put_down(R, OP), I) :-  -holds(in_hand(R, OP), I).

% Cannot pick up an object if it has something in hand.
-occurs(pickup(R, O), I) :- holds(in_hand(R, CO), I).

% Cannot pick up an object if you are not in the same room.
-occurs(pickup(R, OP), I) :- holds(loc(R, C), I), not holds(loc(OP, C), I).

% Cannot execute two actions at the same time.
:- occurs(A1,I), occurs(A2,I), A1 != A2, #rob_action(A1), #rob_action(A2).

%%%%%%%%%%%%%%%%%%%
%% CWA for Actions.
%%%%%%%%%%%%%%%%%%%
-occurs(A,I) :- not occurs(A,I).

%%%%%%%%%%%%%%%%%%%%%%%%
%% Axioms for testing %%
%%%%%%%%%%%%%%%%%%%%%%%%
holds(can_be_tested(rob1, loc(T, C), V), I) :- holds(loc(rob1, C), I).
holds(can_be_tested(rob1, in_hand(rob1, OP), V), I).
holds(directly_observed(rob1, F, true), I+1) :- holds(F, I), occurs(test(rob1, F, true), I).
holds(directly_observed(rob1, F, false), I+1) :- -holds(F, I), occurs(test(rob1, F, false), I).
-occurs(test(rob1, F, O), I) :- -holds(can_be_tested(rob1, F, O), I).

%%%%%%%%%%%%%%%%%%%
%% Testing Actions
%%%%%%%%%%%%%%%%%%%
% Make sure the outcome of any concrete action is tested
occurs(test(R, loc(R, C), true), I+1) :- occurs(move(R, C), I).
occurs(test(R, in_hand(R, O), true), I+1) :- occurs(pickup(R, O), I).
occurs(test(R, in_hand(R, O), false), I+1) :- occurs(put_down(R, O), I).
-occurs(pickup(rob1, OP), I) :- holds(loc(rob1, C), I), not occurs(test(rob1, loc(OP, C), true), I-1).
-occurs(pickup(rob1, OP), I) :- I = 0.

%%%%%%%%%%%%%%%%%%%
%% Awareness axiom.
%%%%%%%%%%%%%%%%%%%
holds(F, 0) | -holds(F, 0) :- #physical_inertial_fluent(F).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% History and initial state rules
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Take what actually happened into account.
occurs(A,I) :- hpd(A,I).

%% Reality check axioms.
:- obs(F, true, I), -holds(F, I).
:- obs(F, false, I), holds(F, I).

%% NEXT LINES ARE RELEVANT TO INFERRING
%%%%%%%%%%%%%%%%%%%
%% Inertia Axioms.
%%%%%%%%%%%%%%%%%%%
holds(F,I+1) :- #inertial_fluent(F), holds(F,I), not -holds(F,I+1).
-holds(F,I+1) :- #inertial_fluent(F), -holds(F,I), not holds(F,I+1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% CWA for Actions and Defined Fluents.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-holds(F,I) :- #defined_fluent(F), not holds(F,I).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Coarse-resolution attributes and fine-resolution counterparts %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
holds(coarse_loc(T, Z), I) :- holds(loc(T, C), I), comp(C, Z).
holds(coarse_loc(B, Z),I) :- holds(loc(RB,C), I), comp(RB,B), comp(C,Z).
holds(coarse_in_hand(rob1, O), I) :- holds(in_hand(rob1, OP), I), comp(OP, O).
holds(loc(RB2, C) ,I) :- holds(loc(RB1, C), I), comp(RB1, B), comp(RB2,B).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Axioms for inferrnig observations %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
holds(indirectly_observed(rob1, coarse_loc(T, R), true), I) :- holds(directly_observed(rob1, loc(T, C), true), I), comp(C, R).
holds(indirectly_observed(rob1, coarse_loc(T, R), true), I) :- holds(directly_observed(rob1, loc(Z, C), true), I), comp(C,R), comp(Z,T).
holds(indirectly_observed(rob1, coarse_in_hand(rob1, O), true), I) :- holds(directly_observed(rob1, in_hand(rob1, OP), true), I), comp(OP, O).

holds(indirectly_observed(rob1, coarse_loc(T, R), false), I) :- -holds(indirectly_observed(rob1, coarse_loc(T, R), true), I), -holds(may_discover(rob1, coarse_loc(T, R), true), I).
holds(indirectly_observed(rob1, coarse_in_hand(rob1, O), false), I) :- -holds(indirectly_observed(rob1, coarse_in_hand(rob1, O), true), I), -holds(may_discover(R, coarse_in_hand(rob1, O), true), I).
holds(may_discover(rob1, coarse_loc(T, R), true), I) :- -holds(indirectly_observed(rob1, coarse_loc(T, R), true), I), comp(C, R), holds(directly_observed(rob1, loc(T, C), undet), I).
holds(may_discover(rob1, coarse_in_hand(rob1, O), true), I) :- -holds(indirectly_observed(rob1, coarse_in_hand(rob1, O), true), I), comp(OP, O), holds(directly_observed(rob1, in_hand(rob1, OP), undet), I).
holds(directly_observed(rob1, F, undet), I) :- not holds(directly_observed(rob1, F, true), I), not holds(directly_observed(rob1, F, false), I).
holds(observed(rob1, F, O), I) :- holds(directly_observed(rob1, F, O), I).
holds(observed(rob1, F, O), I) :- holds(indirectly_observed(rob1, F, O), I).

-holds(indirectly_observed(R,F,O),I) :- not holds(indirectly_observed(R,F,O),I).
-holds(may_discover(R,F,B),I) :- not holds(may_discover(R,F,B),I).
-holds(directly_observed(rob1, F, undet), I) :- holds(directly_observed(rob1, F, true), I).
-holds(directly_observed(rob1, F, undet), I) :- holds(directly_observed(rob1, F, false), I).
-holds(directly_observed(R,loc(O,C1),true),I) :- holds(directly_observed(R,loc(O,C2),true),I), C1!=C2.


%%%%%%%%%%%%%%%%%%%%
%% Planning Module
%%%%%%%%%%%%%%%%%%%%
%% Failure is not an option.
success :- goal(I).
:- not success.
%% Plan Actions minimally
occurs(A,I):+ not goal(I).
%% Preventing preASP_refined_domain_no_planning
something_happened(I) :- occurs(A, I).
:- not goal(I), not something_happened(I).
:- not something_happened(0).

%%%%%%%%%%%%%%%
%% Attributes:
%%%%%%%%%%%%%%%








next_to(c25, c26).
next_to(c28, c28).
next_to(c29, c30).
next_to(c25, c28).
next_to(c26, c29).
next_to(c27, c30).
comp(c25, storage_room).
comp(c26, storage_room).
comp(c27, storage_room).
comp(c28, storage_room).
comp(c29, storage_room).
comp(c30, storage_room).

comp(ref1_book4, book4).
comp(ref2_book4, book4).
comp(ref3_book4, book4).
comp(ref4_book4, book4).


%%%%%%%%%
%% Goal:
%%%%%%%%%
%% GOAL GOES HERE
goal(I) :- holds(coarse_in_hand(rob1,book4),I), holds(coarse_loc(rob1,storage_room),I), holds(coarse_loc(book4,storage_room),I).

%%%%%%%%%%%%%%%%%
%% History:
%%%%%%%%%%%%%%%%%
obs(loc(ref1_book4,c28),false,0).
hpd(test(rob1,loc(ref1_book4,c28),true),0).
holds(loc(rob1,c28),0).
holds(coarse_loc(rob1,storage_room),0).
holds(coarse_loc(book4,storage_room),0).
-holds(coarse_in_hand(rob1,book4),0).
hpd(move(rob1,c25),1).
obs(loc(rob1,c25),true,2).
hpd(test(rob1,loc(rob1,c25),true),2).
obs(loc(ref1_book4,c25),false,3).
hpd(test(rob1,loc(ref1_book4,c25),true),3).
hpd(move(rob1,c26),4).
obs(loc(rob1,c26),true,5).
hpd(test(rob1,loc(rob1,c26),true),5).
obs(loc(ref1_book4,c26),false,6).
hpd(test(rob1,loc(ref1_book4,c26),true),6).
hpd(move(rob1,c29),7).
obs(loc(rob1,c29),true,8).
hpd(test(rob1,loc(rob1,c29),true),8).
obs(loc(ref1_book4,c29),false,9).
hpd(test(rob1,loc(ref1_book4,c29),true),9).
hpd(move(rob1,c30),10).
obs(loc(rob1,c30),true,11).
hpd(test(rob1,loc(rob1,c30),true),11).
obs(loc(ref1_book4,c30),false,12).
hpd(test(rob1,loc(ref1_book4,c30),true),12).
hpd(move(rob1,c27),13).
obs(loc(rob1,c27),true,14).
hpd(test(rob1,loc(rob1,c27),true),14).
obs(loc(ref4_book4,c27),false,15).
hpd(test(rob1,loc(ref4_book4,c27),true),15).

%%%%%%%%%
display
%%%%%%%%%

occurs.

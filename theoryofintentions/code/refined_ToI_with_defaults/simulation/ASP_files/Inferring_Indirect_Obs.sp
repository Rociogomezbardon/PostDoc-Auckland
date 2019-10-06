#const numSteps = 16.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
sorts
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
#step = 0..numSteps.
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
#refined_component = #object + #place.
#coarse_component = #coarse_object + #coarse_place.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
predicates
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
comp(#refined_component, #coarse_component).
holds(#fluent, #step).

%% NEXT LINES ARE RELEVANT TO INFERRING
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
rules
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
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
holds(may_discover(rob1, coarse_loc(O, R), true), I) :- -holds(indirectly_observed(rob1, coarse_loc(O, R), true), I), holds(directly_observed(rob1, loc(P, C), undet), I), comp(C, R), comp(P,O) .
holds(may_discover(rob1, coarse_loc(rob1, R), true), I) :- -holds(indirectly_observed(rob1, coarse_loc(rob1, R), true), I), holds(directly_observed(rob1, loc(rob1, C), undet), I), comp(C, R).
holds(may_discover(rob1, coarse_in_hand(rob1, O), true), I) :- -holds(indirectly_observed(rob1, coarse_in_hand(rob1, O), true), I), comp(OP, O), holds(directly_observed(rob1, in_hand(rob1, OP), undet), I).
holds(directly_observed(rob1, F, undet), I) :- not holds(directly_observed(rob1, F, true), I), not holds(directly_observed(rob1, F, false), I).
holds(observed(rob1, F, O), I) :- holds(directly_observed(rob1, F, O), I).
holds(observed(rob1, F, O), I) :- holds(indirectly_observed(rob1, F, O), I).
-holds(indirectly_observed(R,F,O),I) :- not holds(indirectly_observed(R,F,O),I).
-holds(may_discover(R,F,B),I) :- not holds(may_discover(R,F,B),I).
-holds(directly_observed(rob1, F, undet), I) :- holds(directly_observed(rob1, F, true), I).
-holds(directly_observed(rob1, F, undet), I) :- holds(directly_observed(rob1, F, false), I).
-holds(directly_observed(R,loc(O,C1),true),I) :- holds(directly_observed(R,loc(O,C2),true),I), C1!=C2.

holds(directly_observed(rob1,loc(P1,C),V),I) :- holds(directly_observed(rob1,loc(P2,C),V),I), comp(P1,P), comp(P2,P).
holds(directly_observed(rob1, in_hand(R, P1), V), I) :- holds(directly_observed(rob1, in_hand(R, P2), V), I), comp(P1,P), comp(P2,P).


%%%%%%%%%%%%%%%%%%%%
%% Planning Module
%%%%%%%%%%%%%%%%%%%%
%% PLANNING RULES GO HERE

%%%%%%%%%%%%%%%
%% Attributes:
%%%%%%%%%%%%%%%
comp(c26,storage_room).
comp(c27,storage_room).
comp(c25,storage_room).
comp(c28,storage_room).
comp(c29,storage_room).
comp(ref3_book4,book4).
comp(ref1_book4,book4).
comp(ref4_book4,book4).
comp(c30,storage_room).
comp(ref2_book4,book4).

%%%%%%%%%
%% Goal:
%%%%%%%%%
%% GOAL GOES HERE

%%%%%%%%%%%%%%%%%
%% History:
%%%%%%%%%%%%%%%%%
holds(directly_observed(rob1,loc(ref1_book4,c25),false),3).
holds(directly_observed(rob1,loc(ref1_book4,c28),false),0).
holds(directly_observed(rob1,loc(ref4_book4,c27),false),16).
holds(directly_observed(rob1,loc(ref1_book4,c27),false),16).
holds(directly_observed(rob1,loc(rob1,c25),true),2).
holds(directly_observed(rob1,loc(ref1_book4,c30),false),12).
holds(directly_observed(rob1,loc(rob1,c30),true),11).
holds(directly_observed(rob1,loc(rob1,c27),true),14).
holds(directly_observed(rob1,loc(ref1_book4,c29),false),9).
holds(directly_observed(rob1,loc(ref3_book4,c27),false),16).
holds(directly_observed(rob1,loc(ref4_book4,c27),false),15).
holds(directly_observed(rob1,loc(ref2_book4,c27),false),16).
holds(directly_observed(rob1,loc(rob1,c26),true),5).
holds(directly_observed(rob1,loc(rob1,c29),true),8).
holds(directly_observed(rob1,loc(ref1_book4,c26),false),6).

%%%%%%%%%
display
%%%%%%%%%
holds(indirectly_observed(rob1,B,C),numSteps).

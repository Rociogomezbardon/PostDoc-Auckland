'''
The reasoning at abstract level is done in one or two phases.
First we run a ToI_Explaining without diagnosis and planning rules, using abstract
history (toi_history) as input aswell as assumptions
such as defined by defaults, abnormalities in defaults and any exogeneous actions previously diganosed.
If ToI_Explaining is consistent (i.e. can create a model of history) then we run planning ToI_planning
with the same input (toi_histoy and toi_assumptions). If the ToI_Explaining.sp is inconsistent
then we will run this again with the diagnosing rules (using the flag explaining(I)) and we keep in memory
1. the new assumptions about defaults (defined_by_default and abnormalities) and the number of exogeneous
actions necessary to create a model of history. We use this number of exogeneouse actions, the new assumptions
and the toi_history as input for running the toI_planning. This thime the ToI_planning will use
the planning rules and the explaining rules. If we get any exogeneous actions in the explanation,
these will aslo be added to the list of toi_assumptions.
'''
from datetime import datetime
import subprocess
from realWorld import World
from sets import Set

import re
import numpy
import random
import itertools
def controllerToI(new_domain_info_formatting, newGoal, new_executer, initial_knowledge):
	global executer
	global maxPlanLength
	global numberSteps
	global goal
	global numberActivities
	global currentStep
	global toi_history
	global toi_activities
	global goal_correction
	global current_assumptions #holds diagnosis and abnormalities
	global domain_info_formatting
	global robot_name
	global diagnosis_times_file
	diagnosis_times_file = open('results/diagnosis_time.txt', 'a')
	diagnosis_times_file.write('Number Diagnosis, Time, Steps in planning\n')

	domain_info_formatting = new_domain_info_formatting
	robot_name = list(domain_info_formatting.get_all_constant_subsorts('#robot'))[0]
	numberActivities = 1
	numberSteps = 4
	executer = new_executer
	goal = newGoal
	goal_correction = 0
	current_assumptions = []
	toi_activities = []

	print 'Initial knowledge: ' + str(initial_knowledge)
	observed = initial_observation()
	print 'Initial observation: ' + str(observed)
	preparePreASP_string_lists()
	toi_history = Set(initial_knowledge + [v+'.' for v in observed])
	toi_history.add('hpd(select(my_goal), true,0).')

   	currentStep = 1

	finish = False
	while(finish == False):
		inputForPlanning = diagnose()
		nextAction = planning(inputForPlanning)

		actionObservations = []
		if(nextAction == 'finish'):
			if check_goal_feedback():
				print '\nCheck goal feedback ' + str(check_goal_feedback())
				finish = True
				break
			else:
				goal_correction += 1
				while(nextAction == 'finish'):
					toi_history.update(['obs(my_goal,false,' + str(n) + ').' for n in range(currentStep+1)])
					print('Wrong assumption - goal not reached !!!!! ')
					inputForPlanning = diagnose()
					nextAction = planning(inputForPlanning)

		if(nextAction == None):
#	    		toi_history.add('Goal is futile')
			finish = True
			break

		toi_history.add('attempt('+nextAction+','+str(currentStep)+').')
		if(nextAction[0:4] == 'stop'):
			numberActivities += 1
			numberSteps += 1
		elif(nextAction[0:5] == 'start'): pass
		else:
			step_obs = executer.observe(robot_name,get_fluents_relevant_before_action(nextAction),currentStep)
			executer.executeAction(nextAction)
			step_obs.update(executer.observe(robot_name,get_fluents_relevant_after_action(nextAction),currentStep+1))
			print 'Observations relevant to action: '
			print step_obs
			goal_obs = executer.observe(robot_name,get_fluents_relevant_to_goal(),currentStep+1)
			print 'Observations relevant to goal:'
			print goal_obs
			step_obs.update(goal_obs)
			toi_history.update([obs+'.' for obs in list(step_obs)])
		currentStep += 1



	return (toi_history, toi_activities, [], numberActivities, goal_correction)

def initial_observation():
	#the robot controller is going to request to observe all possible fluents and values combinations. Only those
	#fluents that can be observed will be returned by the executer.
	initial_observations_request = Set()
	all_fluents = domain_info_formatting.get_all_function_subsorts('#fluent')
	for a in all_fluents:
		paramters_a = domain_info_formatting.abstract_signature_dic[a]
		all_values_sets = [domain_info_formatting.get_all_constant_subsorts(p) for p in paramters_a]
		values_combinations = list(itertools.product(*all_values_sets))
		grounded_fluents = [a+'('+','.join(c)+')' for c in values_combinations ]
		initial_observations_request.update(grounded_fluents)
	return executer.observe(robot_name,initial_observations_request,0)

def check_goal_feedback():
	return executer.get_real_values(get_fluents_relevant_to_goal(),currentStep) == goal_as_current_obs_set()

def goal_as_current_obs_set():
	return Set([entry.replace('holds','obs').replace('I',str('-' not in entry).lower()+','+str(currentStep)).replace('-','') for entry in goal.rstrip(' .').split(', ')])

def planning(diagOutput):
	global diagnosis_times_file
	global numberSteps
	global preASP_toi_split
	global toi_history
	global believes_goal_holds
	global toi_activities
	global current_assumptions

	flags = ['planning('+str(currentStep)+').']
	if 'need_explanation' in diagOutput:  flags.append('diagnosing('+str(currentStep)+').')

	nextAction = None
	input = [diagOutput] + current_assumptions + get_toi_history_sorted_list() + toi_activities + flags
	current_asp_split = preASP_toi_split[:toi_beginning_history_index +1] + input + preASP_toi_split[toi_beginning_history_index +1:]
	asp = '\n'.join(current_asp_split)
	asp_file = domain_info_formatting.asp_ToI_planning_file
	f1 = open(asp_file, 'w')
	f1.write(asp)
	f1.close()
	print '\n' + asp_file
	starttime = datetime.now()
	answerSet = subprocess.check_output('java -jar '+domain_info_formatting.sparc_file + ' ' + asp_file +' -A ',shell=True)
	if answerSet == '':
		toi_history.add('Too many answers at ' + asp_file)
		return
	while('intended_action' not in answerSet and 'selected_goal_holds' not in answerSet and numberSteps < currentStep + domain_info_formatting.max_number_steps_ToI_planning+3):
		current_asp_split[0] = '#const n = '+str(numberSteps+1)+'. % maximum number of steps.'
		current_asp_split[1] = '#const max_len = '+str(numberSteps)+'. % maximum activity_length of an activity.'
		asp = '\n'.join(current_asp_split)
        	f1 = open(asp_file, 'w')
		f1.write(asp)
		f1.close()
		print ('\n' + asp_file +' - Increasing numberSteps. ASP_ToI_Planning with ' + str(numberSteps) +' number of steps.')
		answerSet = subprocess.check_output('java -jar ' + domain_info_formatting.sparc_file + ' ' + asp_file +' -A ',shell=True)

		if answerSet == '':
			toi_history.add('Too many answers at ' + asp_file)
			return
		numberSteps +=1
        possibleAnswers = answerSet.rstrip().split('\n\n')
	totalTime = datetime.now()-starttime
	if 'need_explanation' in diagOutput: diagnosis_times_file.write(diagOutput[17:diagOutput.find(',')] + ', ' + str(int(totalTime.total_seconds()))+', '+str(numberSteps-currentStep) + '\n')


	chosenAnswer = possibleAnswers[0]
	split_answer = chosenAnswer.strip('}').strip('{').split(', ')
	believes_goal_holds = 'selected_goal_holds' in chosenAnswer
	new_activity_name = None
	for line in split_answer:
		if('intended_action' in line):
			nextAction = line[16:line.rfind(',')]
			if 'start' in nextAction:
				new_activity_name = nextAction[nextAction.find('(')+1:nextAction.find(')')]
		if 'need_explanation' in diagOutput and 'unobserved' in line:
			current_assumptions.append(line+'.')

	print('Next action with ToI: ' +str(nextAction) +'  at step '+ str(currentStep))
	if new_activity_name:
		new_activity_info = sort_activity_info([line+'.' for line in split_answer if 'activity' in line and '('+new_activity_name+',' in line])
		toi_activities = toi_activities + new_activity_info
		print 'New activity name: ' + new_activity_name
		print 'Activity actions: ' + ', '.join([v.strip('.') for v in new_activity_info if 'component' in v])
	print('Assumptions: ' + str(current_assumptions))
	return nextAction

def get_fluents_relevant_after_action(action):
	if 'move' in action: return {action.replace('move','loc')}
	if 'pickup' in action: return {action.replace('pickup','in_hand')}
	if 'put_down' in action: return {action.replace('put_down','in_hand')}
	if 'unlock' in action: return {action.replace('unlock('+robot_name+',','locked(')}

def get_fluents_relevant_before_action(action):
	if 'put_down' in action: return {action.replace('put_down','in_hand')}
	if 'unlock' in action: return {action.replace('unlock('+robot_name+',','locked(')}
	if 'move' in action and ('library' in action or 'kitchen' in action): return {action.replace('move','loc'),'locked(library)'}


def get_fluents_relevant_to_goal():
	return Set([domain_info_formatting.get_fluent(entry) for entry in goal.split(', ') ])


def get_toi_history_sorted_list():
	global toi_history
	historyInfoSplit = [entry.rstrip(').').split(',') for entry in toi_history]
	historyInfoSplit.sort(key=lambda x:x[0],reverse=True)
	historyInfoSplit.sort(key=lambda x:int(x[-1]))
	return [','.join(entry)+').' for entry in historyInfoSplit]

def sort_activity_info(new_activity_info):
	activity_components_split = [v.split(',') for v in new_activity_info if 'activity_component' in v]
	activity_components_split.sort(key=lambda x:int(x[1]))
	activity_components_sorted = [','.join(v) for v in activity_components_split]
	return [a for a in new_activity_info if not 'component' in a] + activity_components_sorted

def diagnose():
	global toi_history
	global current_assumptions
	preASP_toi_split[toi_current_step_index +1] = 'current_step('+str(currentStep)+').'
	preASP_toi_split[0] = '#const n = '+str(numberSteps+1)+'. % maximum number of steps.'
	preASP_toi_split[1] = '#const max_len = '+str(numberSteps)+'. % maximum activity_length of an activity.'
	preASP_toi_split[2] = '#const max_name = ' + str(numberActivities) + '.'
	displayLines = ['\n%%%%%%\ndisplay\n%%%%%%']
	flag = [] #at first I will run only rules wihout planning and without diagnosing to see if it is consistent
	input = current_assumptions + get_toi_history_sorted_list() + toi_activities + flag + displayLines
	current_asp_split = preASP_toi_split[: toi_beginning_history_index +1] + input
	asp = '\n'.join(current_asp_split)
	asp_file = domain_info_formatting.asp_ToI_diagnosing_file
	f1 = open(asp_file, 'w')
	f1.write(asp)
	f1.close()
	print ('\n' + asp_file)
	answerSet = subprocess.check_output('java -jar '+domain_info_formatting.sparc_file + ' ' + asp_file +' -A ',shell=True)

	if answerSet == '\n':
		print 'Unconsistent history and/or assumptions. Need to diagnose.'
		current_assumptions = []
		flag = ['diagnosing('+str(currentStep)+').']
		displayLines = ['\n%%%%%%\ndisplay\n%%%%%%','number_explained.', 'defined_by_default.', 'ab_d1.', 'ab_d2.', 'ab_dL.']
		input = current_assumptions + get_toi_history_sorted_list() + toi_activities + flag + displayLines
		current_asp_split = preASP_toi_split[: toi_beginning_history_index +1] + input
		asp = '\n'.join(current_asp_split)
		asp_file = domain_info_formatting.asp_ToI_diagnosing_file
		f1 = open(asp_file, 'w')
		f1.write(asp)
		f1.close()
		print ('\n' + asp_file)
		answerSet = subprocess.check_output('java -jar '+domain_info_formatting.sparc_file + ' ' + asp_file +' -A ',shell=True)
		if answerSet == '':
			toi_history.add('Too many answers at ' + asp_file)
			#raw_input()
		if answerSet == '\n':
			print '!!! Inconsistency in ' + asp_file
			#raw_input()
		chosenAnswer = answerSet.rstrip().split('\n\n')[0]
		answer = chosenAnswer.strip('{}').replace('number_explained','need_explanation').split(', ')
		current_assumptions = [a+'.' for a in answer if 'need_explanation' not in a]
		need_explanation_string = [s+'.' for s in answer if 'need_explanation' in s][0]
		return need_explanation_string

	return ''

def preparePreASP_string_lists():
	global preASP_toi_split
	global toi_beginning_history_index
	global toi_current_step_index
	reader = open(domain_info_formatting.preASP_toi_file, 'r')
	preASP_toi = reader.read()
	reader.close()
	preASP_toi_split = preASP_toi.split('\n')
	index_goal = preASP_toi_split.index(domain_info_formatting.goal_marker)
	preASP_toi_split.insert(index_goal+1,  'holds(my_goal,I) :- '+ goal)
	toi_beginning_history_index = preASP_toi_split.index(domain_info_formatting.history_marker)
	toi_current_step_index = preASP_toi_split.index(domain_info_formatting.current_step_marker)

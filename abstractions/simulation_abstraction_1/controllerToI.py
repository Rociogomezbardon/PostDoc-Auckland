#this controller assumes only one exogeneous action will occur during the run.
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
	global inputForPlanning
	global goal_correction
	global current_diagnosis
	global current_assumptions #this conditions are created by the ASP, and include the initial_knowledge. The value of some fluents may have to be assumed by choice.
	global current_defaults
	global current_inferred_condtions
	global domain_info_formatting
	global other_relevant_information
	global robot_name

	domain_info_formatting = new_domain_info_formatting
	robot_name = list(domain_info_formatting.get_all_constant_subsorts('#robot'))[0]
	numberActivities = 1
	numberSteps = 4
	executer = new_executer
	goal = newGoal
	goal_correction = 0
	current_diagnosis = Set()
	current_defaults = Set()
	current_assumptions = Set()
	current_inferred_condtions = Set()
	defaults_history = []
	diagnosis_history = []
	assumptions_history = []
	inferred_conditions_history = []
	other_relevant_information = {}

	print 'Initial knowledge: ' + str(initial_knowledge)
	observed = initial_observation(initial_knowledge)
	print 'Initial observation: ' + str(observed)
	preparePreASP_string_lists()
	toi_history = initial_knowledge + [v+'.' for v in observed]
	toi_history.append('hpd(select(my_goal), true,0).')

   	currentStep = 1
	other_relevant_information[currentStep] = []

	finish = False
	while(finish == False):
		defaultsOutput = checkingDefaults()
		inputForPlanning = diagnose(defaultsOutput)
		nextAction = planning(inputForPlanning)

		actionObservations = []
		if(nextAction == 'finish'):
			if check_goal_feedback():
				print '\nCheck goal feedback ' + str(check_goal_feedback())
				toi_history.append('finish')
				finish = True
				break
			else:
				goal_correction += 1
				while(nextAction == 'finish'):
					toi_history.append('obs(my_goal,false,'+str(currentStep)+').')
					print('Wrong assumption - goal not reached !!!!! ')
					defaultsOutput = checkingDefaults()
					inputForPlanning = diagnose(defaultsOutput)
					nextAction = planning(inputForPlanning)

		if(nextAction == None):
	    		toi_history.append('Goal is futile')
			finish = True
			break


		toi_history.append('attempt('+nextAction+','+str(currentStep)+').')
		if(nextAction[0:4] == 'stop'):
			numberActivities += 1
			numberSteps += 1
		elif(nextAction[0:5] == 'start'): pass
		else:
			step_obs = executer.observe(robot_name,get_fluents_relevant_before_action(nextAction),currentStep)
			executer.executeAction(nextAction)
			step_obs.update(executer.observe(robot_name,get_fluents_relevant_after_action(nextAction),currentStep+1))
			goal_obs = executer.observe(robot_name,get_fluents_relevant_to_goal(),currentStep+1)
			step_obs.update(goal_obs)
			toi_history = toi_history + [obs+'.' for obs in list(step_obs)]
		currentStep += 1
		other_relevant_information[currentStep] = []


	other_relevant_information_list	= []
	for step in range(currentStep):
		step +=1
		if other_relevant_information[step] != []:
			other_relevant_information_list.append('\nReasoning information from step ' + str(step) + ': ')
			other_relevant_information_list = other_relevant_information_list + other_relevant_information[step]


	return (toi_history, other_relevant_information_list, numberActivities, goal_correction)

def initial_observation(initial_knowledge):
	#the robot controller is going to request to observe all possible fluents and values combinations. Only those
	#fluents that can be observed will be returned by the executer.
	initial_observations_request = Set()
	all_fluents = domain_info_formatting.get_all_function_subsorts('#fluent')
	for a in all_fluents:
		paramters_a = domain_info_formatting.refined_sorts_hierarchy_dic[a]
		all_values_sets = [domain_info_formatting.get_all_constant_subsorts(p) for p in paramters_a]
		values_combinations = list(itertools.product(*all_values_sets))
		grounded_fluents = [a+'('+','.join(c)+')' for c in values_combinations ]
		initial_observations_request.update(grounded_fluents)
	return executer.observe(robot_name,initial_observations_request,0)


def check_goal_feedback():
	return executer.get_real_values(get_fluents_relevant_to_goal(),currentStep) == goal_as_current_obs_set()

def goal_as_current_obs_set():
	return Set([entry.replace('holds','obs').replace('I',str('-' not in entry).lower()+','+str(currentStep)).replace('-','') for entry in goal.rstrip(' .').split(', ')])

def planning(outputDefaultsAndDiagnosis):
	global numberSteps
	global preASP_toi_split
	global toi_history
	global believes_goal_holds
	nextAction = None
	input = outputDefaultsAndDiagnosis + toi_history +['planning('+str(currentStep)+').']
	current_asp_split = preASP_toi_split[:toi_beginning_history_index +1] + input + preASP_toi_split[toi_beginning_history_index +1:]
	asp = '\n'.join(current_asp_split)
	asp_file = domain_info_formatting.asp_ToI_planning_file
	f1 = open(asp_file, 'w')
	f1.write(asp)
	f1.close()
	print '\n' + asp_file
	answerSet = subprocess.check_output('java -jar '+domain_info_formatting.sparc_path + ' ' + asp_file +' -A ',shell=True)
	while( 'intended_action' not in answerSet and 'selected_goal_holds' not in answerSet and numberSteps < currentStep + domain_info_formatting.max_number_steps_ToI_planning+3):
		current_asp_split[0] = '#const n = '+str(numberSteps+1)+'. % maximum number of steps.'
		current_asp_split[1] = '#const max_len = '+str(numberSteps)+'. % maximum activity_length of an activity.'
		asp = '\n'.join(current_asp_split)
        	f1 = open(asp_file, 'w')
		f1.write(asp)
		f1.close()
		print ('\n' + asp_file +' - Increasing numberSteps. ASP_ToI_Planning with ' + str(numberSteps) +' number of steps.')
		answerSet = subprocess.check_output('java -jar '+domain_info_formatting.sparc_path + ' ' + asp_file +' -A ',shell=True)
		numberSteps +=1

        possibleAnswers = answerSet.rstrip().split('\n\n')

	chosenAnswer = possibleAnswers[0]
	split_answer = chosenAnswer.strip('}').strip('{').split(', ')
	believes_goal_holds = 'selected_goal_holds' in chosenAnswer
	new_activity_name = None
	for line in split_answer:
		if('intended_action' in line):
			nextAction = line[16:line.rfind(',')]
			if 'start' in nextAction:
				new_activity_name = nextAction[nextAction.find('(')+1:nextAction.find(')')]

	print('Next action with ToI: ' +str(nextAction) +'  at step '+ str(currentStep))
	if new_activity_name:
		activity_info = [line+'.' for line in split_answer if 'activity' in line and '('+new_activity_name+',' in line]
		toi_history = toi_history + activity_info
		activity_name =  [v[v.find('(')+1:v.find(',')] for v in activity_info if 'activity_goal' in v][0]
		print 'New activity name: ' + activity_name
		activity_components_split = [v.split(',') for v in activity_info if 'activity_component' in v]
		activity_components_split.sort(key=lambda x:int(x[1]))
		activity_components_sorted = [','.join(v[2:])[:-2] for v in activity_components_split]
		print 'Activity actions: ' + ', '.join(activity_components_sorted)
	return nextAction

## TODO needs testing
def get_fluents_relevant_after_action(action):
	if 'request_move' in action: return {action.replace('request_move('+robot_name+',','lift_door_open(')}
	elif 'call_lift' in action in action: return {action.replace('call_lift('+robot_name+',','lift_door_open(')}
	elif 'move' in action: return {action.replace('move','loc')}
	elif 'pickup' in action: return {action.replace('pickup','in_hand')}
	elif 'put_on_shelf' in action: return {action.replace('put_on_shelf('+robot_name+',','on_shelf(')}

## TODO needs testing
def get_fluents_relevant_before_action(action):
	if 'put_on_shelf' in action:
		return {(action[:action.rfind(',')]+')').replace('put_on_shelf','in_hand')}
	if 'call_lift' in action in action: return {action.replace('call_lift('+robot_name+',','lift_door_open(')}
	elif 'request_move' in action: return {action.replace('request_move('+robot_name+',','lift_door_open(')}

def get_fluents_relevant_to_goal():
	return Set([domain_info_formatting.get_fluent(entry) for entry in goal.split(', ') ])

def checkingDefaults():
	global current_defaults
	global other_relevant_information
	preASP_toi_split[toi_current_step_index +1] = 'current_step('+str(currentStep)+').'
	preASP_toi_split[0] = '#const n = '+str(numberSteps+1)+'. % maximum number of steps.'
	preASP_toi_split[1] = '#const max_len = '+str(numberSteps)+'. % maximum activity_length of an activity.'
	preASP_toi_split[2] = '#const max_name = ' + str(numberActivities) + '.'
	previous_defaults = current_defaults
	current_defaults = Set()

	checkingDefaultsFlag = 'finding_defaults('+str(currentStep)+').'
	checkingDefaultsDisplayLines = ['%%%%%%\ndisplay\n%%%%%%','defined_by_default.']
	current_asp_split = preASP_toi_split[: toi_beginning_history_index +1] + toi_history + [checkingDefaultsFlag] + checkingDefaultsDisplayLines
	asp_file = domain_info_formatting.asp_ToI_defaults_file
	f1 = open(asp_file, 'w')
	f1.write('\n'.join(current_asp_split))
	f1.close()
	print ('\n' + asp_file)
	answerSet = subprocess.check_output('java -jar '+domain_info_formatting.sparc_path + ' ' + asp_file +' -A ',shell=True)

	if answerSet == '' or answerSet == '\n':
		diagnosingFlag = 'diagnosing('+str(currentStep)+').'
		current_asp_split = preASP_toi_split[: toi_beginning_history_index +1] + toi_history + [checkingDefaultsFlag] +[diagnosingFlag]+ checkingDefaultsDisplayLines + ['unobserved.']
		asp_file = domain_info_formatting.asp_ToI_defaults_file
		f1 = open(asp_file, 'w')
		f1.write('\n'.join(current_asp_split))
		f1.close()
		print ('\nIncluding diagnosis and running: ' + asp_file)
		answerSet = subprocess.check_output('java -jar '+domain_info_formatting.sparc_path + ' ' + asp_file +' -A ',shell=True)


	if '{}' in answerSet:
		if current_defaults != previous_defaults: print 'New Current Defaults: '
		return []

	answers = answerSet.rstrip().split('\n\n')

	for a in [answer for answer in answers if answer]:
		answer_defaults = Set([v for v in a.strip('{}\n').split(', ') if 'unobserved' not in v])
		if previous_defaults==answer_defaults:
			current_defaults = answer_defaults
			break
		elif previous_defaults.issubset(answer_defaults):
			current_defaults = answer_defaults
			break

	if not current_defaults and answers[0]:
		current_defaults = Set([v for v in answers[0].strip('{}\n').split(', ') if 'unobserved' not in v])

	if current_defaults != previous_defaults:
		other_relevant_information[currentStep] = other_relevant_information[currentStep] + list(current_defaults)
		print 'New Current Defaults: ' + '. '.join(current_defaults)
	return [e+'.' for e in current_defaults]

def diagnose(defaultsOutput):
	global current_diagnosis
	global current_assumptions
	global current_inferred_condtions
	global other_relevant_information
	last_diagnosis = current_diagnosis
	last_assumptions = current_assumptions
	last_inferred_conditions = current_inferred_condtions
	diagnosingFlag = 'diagnosing('+str(currentStep)+').'
	diagnosingDisplayLines = ['\n%%%%%%\ndisplay\n%%%%%%','unobserved.','assumed_initial_condition.']

	current_asp_split = preASP_toi_split[: toi_beginning_history_index +1] + defaultsOutput + toi_history +[diagnosingFlag]  + diagnosingDisplayLines
	asp = '\n'.join(current_asp_split)
	asp_file = domain_info_formatting.asp_ToI_diagnosing_file
	f1 = open(asp_file, 'w')
	f1.write(asp)
	f1.close()

	# running only diagnosis
	print ('\n' + asp_file)
	answerSet = subprocess.check_output('java -jar '+domain_info_formatting.sparc_path + ' ' + asp_file +' -A ',shell=True)
	if answerSet == '' or answerSet == '\n':
		print '!!! Something went wrong in ' + asp_file
		raw_input()
	answers = answerSet.rstrip().split('\n\n')

	#re-defining assumend_initial_conditions that are commont to all answers as current_inferred_condtions
	any_answer = answers[0]
	any_answer = any_answer.strip('{}').split(', ')
	current_inferred_condtions = Set([f for f in any_answer if 'assumed_initial_condition' in f and all([f in answer for answer in answers])])

	# for each answer, I will split it in single strings, remove the current_inferred_condtions, and split these
	# set into a tuple that holds two different sets, the first set holds assumed initial contions and the second one unobserved actions.
	sorted_answers = []
	for a in answers:
		a = Set(a.strip('{}').split(', ')) - current_inferred_condtions
		sorted_answer = (Set([v for v in a if 'assumed_initial_condition' in v]) , Set([v for v in a if 'unobserved' in v]))
		sorted_answers.append(sorted_answer)

	chosenAnswer = None
	for sorted_a in sorted_answers:
		if current_assumptions == sorted_a[0] and current_diagnosis == sorted_a[1]: chosenAnswer = sorted_a
	if not chosenAnswer:
		for sorted_a in sorted_answers:
			if current_assumptions == sorted_a[0] and current_diagnosis.issubset(sorted_a[1]): chosenAnswer = sorted_a
	if not chosenAnswer:
		for a in answers:
			if current_assumptions.issubset(sorted_a[0]) and current_diagnosis == sorted_a[1]: chosenAnswer = sorted_a
	if not chosenAnswer:
		for a in answers:
			if current_assumptions.issubset(sorted_a[0]) and current_diagnosis.issubset(sorted_a[1]): chosenAnswer = sorted_a
	if not chosenAnswer:
		for a in answers:
			if current_assumptions.issubset(sorted_a[0]): chosenAnswer = sorted_a
	if not chosenAnswer:
		for a in answers:
			if current_diagnosis.issubset(sorted_a[1]): chosenAnswer = sorted_a
	if not chosenAnswer: chosenAnswer = sorted_answers[0]

	current_assumptions = chosenAnswer[0]
	current_diagnosis = chosenAnswer[1]


	if current_inferred_condtions != last_inferred_conditions:
		other_relevant_information[currentStep] = other_relevant_information[currentStep] + list(current_inferred_condtions)
		print 'New Inferred initial conditions: ' + ', '.join([v[:-1].replace('assumed_initial_condition(','') for v in current_inferred_condtions])
	if current_assumptions != last_assumptions:
		other_relevant_information[currentStep] = other_relevant_information[currentStep] + list(current_assumptions)
		print 'Current assumptions: ' + ', '.join([v[:-1].replace('assumed_initial_condition(','') for v in current_assumptions])
	if current_diagnosis != last_diagnosis:
		other_relevant_information[currentStep] = other_relevant_information[currentStep] + list(current_diagnosis)
		print 'Current diagnosis: ' + ', '.join(current_diagnosis)

	diagnosisAndDefaultsOutput = defaultsOutput + [e + '.' for e in current_assumptions|current_diagnosis]
	return diagnosisAndDefaultsOutput

def preparePreASP_string_lists():
	global preASP_toi_split
	global toi_beginning_history_index
	global toi_current_step_index
	reader = open(domain_info_formatting.preASP_ToI_file, 'r')
	preASP_toi = reader.read()
	reader.close()
	preASP_toi_split = preASP_toi.split('\n')
	index_goal = preASP_toi_split.index(domain_info_formatting.goal_marker)
	preASP_toi_split.insert(index_goal+1,  'holds(my_goal,I) :- '+ goal)
	toi_beginning_history_index = preASP_toi_split.index(domain_info_formatting.history_marker)
	toi_current_step_index = preASP_toi_split.index(domain_info_formatting.current_step_marker)

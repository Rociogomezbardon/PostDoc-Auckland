# -*- coding: utf-8 -*-
'''Python program to run trials in the agent reasoning programs with ToI
1. Select all possible valid initial states for the objects in the domain.
2. Run each initial state.

How I classify trial results according to different scenarios in realWorld.py:

# scenario 1 - just planning, everything goes fine, no unexpected changes in the world.
# scenario 2 - unexpected achievement of goal.
# scenario 3 - unexpected false observation that leads to not expected achievement of goal, diagnosis and replan.
# scenario 4 - unexpected true observation that leads to not expected achievement of goal, diagnosis and replan.
# scenario 5 - Failure to achieve goal, diagnosis, and re-planning.
# scenario 6 - Failure to execute, diagnosis and replaning.
'''


from datetime import datetime
from realWorld import World
import controllerToI
from domain_info_formatting import DomainInfoFormatting
from executer import Executer
import random
from sets import Set


global goal

maxPlanLength = 17
textfile = None
boolean = ['true', 'false']


runCount = 0

def run_and_write(dic_initial_condition, initial_knowledge):
	global runCount
	runCount +=1

	history_toi = [""]
	time_planning_toi = 0
	time_executing_toi = 0
	scenarioRecreated_toi = 0
	length = 0


	randomSeed = runCount
	start_time_toi = datetime.now()
	world_toi = World(domain_info_formatting ,dic_initial_condition,randomSeed)
	executer = Executer(world_toi)
	history_toi, other_relevant_information, numberPlans_toi, goal_correction_toi = controllerToI.controllerToI(domain_info_formatting,goal, executer,initial_knowledge)
	end_time_toi = datetime.now()
	time_planning_toi = (end_time_toi - start_time_toi).total_seconds()
	historyWorld_toi = world_toi.getHistory()
	time_executing_toi = world_toi.getExecutionTimeUnits()
	steps_executed_toi = world_toi.getExecutedSteps()
	exo_action = str(world_toi.get_exo_action_happened())[0]
	achieved_goal_toi = str(controllerToI.check_goal_feedback())[0].capitalize()


	toi_exo_action = ''
	toi_exo_move_book = ''
	toi_exo_move_room = ''
	toi_exo_lock = ''
	for item in historyWorld_toi:
		if('exo' in item):
			toi_exo_action = item
			break

	if('move' in toi_exo_action):
		toi_exo_move_book = item[9:14]
		toi_exo_move_room = item[15:-1]
	if('lock' in toi_exo_action): toi_exo_lock = 'true'



	activityInfo=[]
	historyInfo=[]
	firstActivityLength = 0
	secondActivity = False
	firstStop = 0

	##working out what scenario it has been run.
	for item in history_toi:
		if('activity' in item or 'finish' in item or 'selected_goal_holds' in item or 'Goal is futile' in item or 'Goal holds' in item or 'unobserved' in item):
			activityInfo.append(item)
			if('activity_length(1' in item): firstActivityLength = int(item[item.rfind(',')+1:-2])
		else:
			if('attempt(stop(1),' in item): firstStop = int(item[16:-2])
			if('attempt(start(2),' in item): secondActivity = True
			split_item = [''] * 2

			split_item[0] = item[:item.rfind(',')]
			split_item[1] = item[item.rfind(',')+1:-2]
			historyInfo.append(split_item)
	if(firstActivityLength + 2 == firstStop): scenarioRecreated_toi = 5
	elif(secondActivity == False and steps_executed_toi < firstActivityLength and achieved_goal_toi): scenarioRecreated_toi = 2
	elif(steps_executed_toi == firstActivityLength and secondActivity == False): scenarioRecreated_toi = 1

	elif(firstStop > 0 and firstStop < firstActivityLength + 2 and secondActivity == True):
		if(toi_exo_lock == 'true'):
			scenarioRecreated_toi = 6
		elif(toi_exo_move_book != ''):
			if(['obs(loc('+toi_exo_move_book+','+toi_exo_move_room+'),true' , str(firstStop)] in historyInfo):
				scenarioRecreated_toi = 4
			else:
				scenarioRecreated_toi = 3


	if achieved_goal_toi: print '\n\nGoal Achieved.'
	print '\nHistory of the world: '
	print historyWorld_toi
	historyInfo.sort(key=lambda x:x[0],reverse=True)
	historyInfo.sort(key=lambda x:int(x[1]))

	historyInfo = [','.join(item)+')' for item in historyInfo]
	history_toi = historyInfo + [''] + activityInfo


	#Writing to txt
	textfile.write("$$$$$$$$$$$$$$$$$$$   Run number " + str(runCount) +"   $$$$$$$$$$$$$$$$$$$\n")
	textfile.write("Running Scenario "+str(scenarioRecreated_toi)+"\n")
	textfile.write("Goal: "+goal+"\n")
	textfile.write("Initial World State: "+str(dic_initial_condition)+"\n")
	textfile.write("Achieved goal ToI: "+ str(achieved_goal_toi)+"\n")
	textfile.write("\nHistory World: \n" + '\n'.join(historyWorld_toi) +"\n")
	textfile.write("\nHistory ToI: \n"+ '\n'.join(history_toi)+'\n')
	textfile.write("\nOther Relevant Information: \n" + '\n'.join(other_relevant_information) +"\n")

	if('Goal is futile' in history_toi):
		textfile.write("Goal is futile\n")

	elif('Goal holds' in history_toi):
		textfile.write("Goal holds\n")

	textfile.write('\n--------------------------------------------------------------\n\n')


def createConditionsAndRunAll():
	places = domain_info_formatting.get_all_basic_subsorts('#place')
	shelves = domain_info_formatting.get_all_basic_subsorts('#shelf')
	objects = domain_info_formatting.get_all_basic_subsorts('#object')
	corridors = domain_info_formatting.get_all_basic_subsorts('#corridor')
	objects_to_locate = objects
	dic_initial_condition = {}
	dic_initial_condition['loc(rob'] = random.choice(list(places))
	if random.choice([True,False]):
		object_in_hand =  random.choice(list(objects))
		objects_to_locate.remove(object_in_hand)
		dic_initial_condition['in_hand(rob'] = object_in_hand

	for o in objects_to_locate:
		on_shelf = random.choice([True,False])
		if on_shelf:
			shelf = random.choice(list(shelves))
			dic_initial_condition['on_shelf(' + o] = shelf
		else:
			place = random.choice(list(places))
			dic_initial_condition['loc('+o] = place

	if random.choice([True,False]):
		corridor = random.choice(list(corridors))
		dic_initial_condition['lift_door_open(lift'] = corridor
	initial_knowledge =  domain_info_formatting.dic_state_to_obs_list(dic_initial_condition,0)
	run_and_write(dic_initial_condition, initial_knowledge)



if __name__ == "__main__":
	global goal
	textfile = open('results/results_ToI_test.txt', 'w')
	domain_info_formatting = DomainInfoFormatting()


	goal = "holds(loc(book_1,library),I), holds(loc(book_2,library),I), -holds(in_hand(rob,book_1),I), -holds(in_hand(rob,book_2),I) ."
	'''
	dic_initial_condition = {}
	locked = True
	if locked: dic_initial_condition['lift_door_open(lift,corridor_1'] = None
	dic_initial_condition['loc(rob'] = 'kitchen'
	dic_initial_condition['loc(book_1'] = 'kitchen'
	dic_initial_condition['on_shelf(book_2'] = 'bookshelf_2'
	dic_initial_condition['in_hand(rob'] = 'book_1'
	dic_initial_condition['on_shelf(cup_1'] = 'cupboard'
	dic_initial_condition['on_shelf(cup_2'] = 'cupboard'
	initial_knowledge = ['obs(loc(rob,kitchen),true,0).','obs(loc(book_1,kitchen),true,0).','obs(in_hand(rob,book_1),true,0).']
	'''

	dic_initial_condition = {'loc(rob': 'office_1', 'on_shelf(book_2': 'bookshelf_1', 'in_hand(rob': 'book_1', 'loc(cup_1': 'office_1', 'on_shelf(cup_2': 'bookshelf_1'}
	#initial_knowledge =  domain_info_formatting.dic_state_to_obs_list(dic_initial_condition,0)
	initial_knowledge = ['obs(loc(rob,office_1),true,0).']
	run_and_write(dic_initial_condition,initial_knowledge)
	#for n in range(50):
		#createConditionsAndRunAll()

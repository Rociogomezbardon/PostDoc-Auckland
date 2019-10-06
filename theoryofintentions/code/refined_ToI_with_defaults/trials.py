from datetime import datetime

from simulation.realWorld import World
from controllerToI import ControllerToI
from simulation.executer import Executer
from sets import Set
import subprocess
import  csv
import random
import multiprocessing
import time
import global_variables
from simulation.domain_info import DomainInfo
import sys
import csv
from decimal import getcontext, Decimal
from collections import OrderedDict

global trialCount

def runAndWrite( goal, dic_initial_state):
	goal  = 'holds(loc(book4,library),I).'
	##TODO remove line below. it is just for testing
	dic_initial_state = {'loc(ref4_book1': 'c4','loc(ref2_book1': 'c4','loc(ref3_book1': 'c4','loc(ref1_book1': 'c4','loc(ref3_book2': 'c17','loc(ref2_book2': 'c17','loc(ref4_book2': 'c17','loc(ref1_book2': 'c17','loc(ref2_book3': 'c10','loc(ref3_book3': 'c10','loc(ref4_book3': 'c10','loc(ref1_book3': 'c10','loc(ref3_book4': 'c20','loc(ref2_book4': 'c20','loc(ref1_book4': 'c20','loc(ref4_book4': 'c20','loc(rob1': 'c4', 'in_hand(rob1':'ref1_book1'}
	print 'Trial Number: ' + str(trialCount)
	print 'Controler type: ' + str(global_variables.controller_type).upper()
	print 'Goal: ' + goal
	print ('Initial_state:')
	print(dic_initial_state.items())

	my_world = World(dic_initial_state,domain_info,global_variables.sparc_file)
	executer = Executer(my_world)
	dic_known_world = my_world.getAbstractState()
	initial_state = list(domain_info.dic_abstractStateToAbstractHoldsSet(dic_known_world,0))
	initial_knowledge = [v for v in initial_state if 'loc(rob' in v or 'in_hand' in v]
	robot_refined_location = my_world.getRobotRefinedLocation()
	print '\nInitial abstract state: ' + str(initial_state)
	print '\nInitial knowledge: ' + str(initial_knowledge) + ', ' + robot_refined_location

	results = open(global_variables.txt_results_file, 'a')
	results.write('\nTrial Number: ' + str(trialCount))
	results.write('\nControler type: ' + str(global_variables.controller_type).upper())
	results.write('\nGoal: ' + goal)
	results.write('\nInitial World State: '+ str(dic_initial_state))
	results.write('\nInitial Abstract State: ' + str(initial_state))
	results.write('\nInitial Knowledge: ' + str(initial_knowledge) +', '+ robot_refined_location )
	results.close()

	controllerToI = ControllerToI( domain_info, executer, robot_refined_location, initial_knowledge , goal)

	startTime = datetime.now()
	error, refinedPlanningTime, abstractPlanningTime, inferObsTime, diagnosingTime, execTime, numAbsPlans, numRefPlans, numAbsAct, numRefAct,completeRun = controllerToI.run()
	timeTaken = (datetime.now()-startTime).total_seconds()
	print '$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$: Total run time: ' + str(timeTaken) + ' seconds.'
	results = open(global_variables.txt_results_file, 'a')
	results.write('\nTotal trial time: ' + str(timeTaken) + ' seconds.')
	results.write('\nTime Refined planning: '+ str(refinedPlanningTime))
	results.write('\nTime Abstract planning: '+ str(abstractPlanningTime))
	results.write('\nTime Diagnosing: '+ str(diagnosingTime))
	results.write('\nTime Inferring coarse resolution obs: '+str(inferObsTime))
	results.write('\nTime Executing: ' + str(execTime))
	results.write('\nNumber of abstract plans: '  + str(numAbsPlans))
	results.write('\nNumber of abstract actions: ' + str(numAbsAct))
	results.write('\nNumber of refined plans: ' + str(numRefPlans))
	results.write('\nNumber of refined actions: ' + str(numRefAct))
	results.write('\nComplete run code: ' + str(completeRun))
	results.write('\n----------------------------------------------------------------------------\n\n\n')
	results.close()
	return [timeTaken,refinedPlanningTime,abstractPlanningTime,diagnosingTime, inferObsTime, numAbsPlans,numAbsAct,numRefPlans,numRefAct,completeRun]


def runPairwiseControllersAndWrite(dic_initial_state, goal):
	global_variables.controller_type = 'zooming'
	resultsListZooming = runAndWrite(goal, dic_initial_state)

	## TODO UNCOMMENT LINE BELOW AND COMMENT OUT THE FOLLWING TWO TO AVOID RUNNING NON-ZOOMING
	#resultsListNonZooming = resultsListZooming
	global_variables.controller_type = 'non_zooming'
	resultsListNonZooming = runAndWrite(goal, dic_initial_state)

	resultsList = [trialCount]
	for i in range(len(resultsListZooming)-1):
		if(i < 5 or i == 31):
			try: resultsList.append("{0:.2f}".format(resultsListZooming[i]))
			except: resultsList.append("")
			try: resultsList.append("{0:.2f}".format(resultsListNonZooming[i]))
			except: resultsList.append("")
		else:
			try: resultsList.append(int(resultsListZooming[i]))
			except: resultsList.append("")
			try: resultsList.append(int(resultsListNonZooming[i]))
			except: resultsList.append("")
		if resultsListNonZooming[-1] == "C" and resultsListZooming[-1] == "C":
			try: resultsList.append("{0:.2f}".format(resultsListNonZooming[i]/resultsListZooming[i]))
			except ZeroDivisionError: resultsList.append(float("inf"))
		else: resultsList.append("")
	resultsList.append(resultsListZooming[-1])
	resultsList.append(resultsListNonZooming[-1])
	with open(global_variables.csv_results_file, 'a') as writeFile:
		writer = csv.writer(writeFile)
		writer.writerow(resultsList)
	writeFile.close()

def createInitialConditionsAndGoal():
	dic_initial_state = OrderedDict()
	refined_objects = list(domain_info.refined_signature_dic['#object'])
	refined_locations = list(domain_info.refined_signature_dic['#place'])
	abstract_objects = list(domain_info.refined_signature_dic['#coarse_object'])
	for book in abstract_objects:
		chosen_location = random.choice(refined_locations)
		for ref_book in refined_objects:
			if book in ref_book: dic_initial_state['loc('+ref_book] = chosen_location
	if(random.uniform(0, 1) < 0.2):
		ref_object_holding = random.choice(refined_objects)
		dic_initial_state['in_hand(rob1'] = ref_object_holding
		dic_initial_state['loc(rob1'] = dic_initial_state['loc('+ref_object_holding]
	else: dic_initial_state['loc(rob1'] = random.choice(refined_locations)
	#creating gol
	book_choice = random.choice(abstract_objects)
	locations = list(domain_info.refined_signature_dic['#coarse_place'])
	chosen_book_location = dic_initial_state['loc(ref1_'+book_choice]
	chosen_book_abstract_location = domain_info.components_dic[chosen_book_location]
	locations.remove(chosen_book_abstract_location)
	location_choice = random.choice(locations)
	goal = 'holds(loc('+book_choice+','+location_choice+'),I).'
	return dic_initial_state, goal


def runGivenInitialState():
	goal = 'holds(loc(book3,office2),I).'
	dic_initial_state =  OrderedDict([('loc(ref4_book1', 'c10'), ('loc(ref2_book1', 'c10'), ('loc(ref3_book1', 'c10'), ('loc(ref1_book1', 'c10'), ('loc(ref3_book2', 'c16'), ('loc(ref2_book2', 'c16'), ('loc(ref4_book2', 'c16'), ('loc(ref1_book2', 'c16'), ('loc(ref2_book3', 'c5'), ('loc(ref3_book3', 'c5'), ('loc(ref4_book3', 'c5'), ('loc(ref1_book3', 'c5'), ('loc(ref3_book4', 'c9'), ('loc(ref2_book4', 'c9'), ('loc(ref1_book4', 'c9'), ('loc(ref4_book4', 'c9'), ('loc(rob1', 'c19')])
	runPairwiseControllersAndWrite(dic_initial_state, goal)


if __name__ == "__main__":
	global trialCount
	trialCount = 0
	singleRunTest = False
	number_runs = 1
	global_variables.init()
	global_variables.csv_results_file = 'simulation/results/experimental_results.csv'
	global_variables.txt_results_file = 'simulation/results/experimental_results.txt'
	domain_info = DomainInfo()
	## The next two files would normally be created already in other versions, but in this case we need to create them now as the constants of the domain change with each complexity level. These functions will use
	## the complexity level (initialised above) and the paths of the files with the pre ASP info, initialised in DomainInfo().
	with open(global_variables.csv_results_file, 'a') as writeFile:
		writer = csv.writer(writeFile)
		writer.writerow(['Trial Number', 'Run-time zooming','Run-time non_zooming','Run-time Ratio',  'Refined Planning Time - zooming','Refined Planning Time - non_zooming','Refined Planning Time - Ratio', 'Abstract Planning Time - zooming','Abstract Planning Time - non_zooming','Abstract Planning Time - Ratio','Diagnosing - zooming', 'Diagnosing - non_zooming', 'Diagnosing - Ratio', 'Inferring -zooming', ' Inferring - non_zooming', 'Inferring - Ratio', '# Abstract Plans - zooming', '# Abstract Plans - non_zooming','# Abstract Plans - Ratio','# Abstract Actions - zooming','# Abstract Actions - non_zooming','# Abstract Actions - Ratio','# Refined Plans - zooming','# Refined Plans - non_zooming','# Refined Plans - Ratio',  '# Refined Actions - zooming','# Refined Actions - non_zooming' ,'# Refined Actions - Ratio','Complete Run - zooming','Complete Run - non_zooming'])
	remaining_runs = number_runs - trialCount
	if(singleRunTest): remaining_runs = 1
	for x in range (0,remaining_runs):
		trialCount += 1
		if(singleRunTest): runGivenInitialState()
		else:
			dic_initial_state, goal = createInitialConditionsAndGoal()
			runPairwiseControllersAndWrite(dic_initial_state, goal)

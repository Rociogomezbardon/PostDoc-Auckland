# -*- coding: utf-8 -*-
'''
'''

from datetime import datetime
import random
import  csv
from Controller_ToA import Controller_ToA
from Controller_Traditional import Controller_Traditional

sparcPath = "$HOME/work/solverfiles/sparc.jar"
goal = "tidy_all(library)"
numberOfRuns = 3000
numberPossibleInitialConditions = 576

toa_asp = None
textfile = None
csvfile = None
writer = None
activities_list_split = None
locations = ['office1', 'office2', 'office3','office4', 'kitchen', 'library']
boolean = ['true', 'false']
runCount = None

results_file_name = "results"

def createRandomInitialConditions():
	initial_conditions = []
	initial_conditions_index = random.randrange(1,numberPossibleInitialConditions+1,1)
	#initial_conditions_index = 22
	current_index = 0
	
	initial_conditions = []
	#Cases when rob1 is holding book1
	for locked_or_not in boolean:
		for robot_location in locations:			
			for book2_location in locations:
				current_index +=1
				if(initial_conditions_index != current_index): continue	
                                book1_location = robot_location
                                in_handBook1 = 'true'
                                in_handBook2 = 'false'
				initial_conditions = [locked_or_not, robot_location , book1_location , book2_location, in_handBook1, in_handBook2]

	#Cases when rob1 is holding book2
	for locked_or_not in boolean:
		for robot_location in locations:
			for book1_location in locations:
				current_index +=1
				if(initial_conditions_index != current_index): continue	
                                book2_location = robot_location
                                in_handBook1 = 'false'
                                in_handBook2 = 'true'
  				initial_conditions = [locked_or_not, robot_location , book1_location , book2_location, in_handBook1, in_handBook2]

	#Cases when rob1 is not holding any book
	for locked_or_not in boolean:
		for robot_location in locations:
			for book1_location in locations:
			     	for book2_location in locations:
					current_index +=1
					if(initial_conditions_index != current_index): continue	
                                	in_handBook1 = 'false'
                                	in_handBook2 = 'false'
	  				initial_conditions = [locked_or_not, robot_location , book1_location , book2_location, in_handBook1, in_handBook2]
	print "Initial conditions index: " + str(initial_conditions_index)
	return initial_conditions_index, initial_conditions

def parseInitialConditions(initial_conditions):
	initial_conditions_string = ""
	if initial_conditions[0] == 'true':
		initial_conditions_string += 'holds(locked(library),0).\n'
	else:
		initial_conditions_string += '-holds(locked(library),0).\n'
	initial_conditions_string += 'holds(loc(rob1,'+initial_conditions[1]+'),0).\n'
	initial_conditions_string += 'holds(loc(book1,'+initial_conditions[2]+'),0).\n'
	initial_conditions_string += 'holds(loc(book2,'+initial_conditions[3]+'),0).\n'

	if initial_conditions[4] == 'true':
		initial_conditions_string += 'holds(in_hand(rob1,book1),0).\n'
	else:
		initial_conditions_string += '-holds(in_hand(rob1,book1),0).\n'
	if initial_conditions[5] == 'true':
		initial_conditions_string += 'holds(in_hand(rob1,book2),0).\n'
	else:
		initial_conditions_string += '-holds(in_hand(rob1,book2),0).\n'
	
	return initial_conditions_string



	
if __name__ == "__main__":

	textfile = open(results_file_name+'.txt', 'w')
	csvfile = open(results_file_name+'.csv', 'w')
	writer = csv.writer(csvfile)
	writer.writerow(['Run', ' Time Trad', ' Time ToA' , ' Time First ASP', ' Time Second ASP', ' Plan Length Trad', ' Activity Length ToA', ' New Activity' , ' Activity Name' , ' Number Activities', ' Conditions Index' , ' Goal', 'Goal Holds'])


	controller_toa = Controller_ToA(sparcPath)
	controller_traditional = Controller_Traditional(sparcPath)
	goal = 'tidy_all(library)'
	for run in xrange(numberOfRuns):
		print("Run number " + str(run+1))
		initial_conditions = createRandomInitialConditions()
		initial_conditions_index = initial_conditions[0]
		initial_conditions_string = parseInitialConditions(initial_conditions[1])

		time_toa = 0
		time_toa_first = 0
		time_toa_second = 0
		new_activity_toa = ''
		activity_name_toa = ''
		activity_toa = ''
		activity_length = 0
		activities_list_length = 0
		time_traditional = 0
		plan_traditional = ''
		
		time_toa, time_toa_first, time_toa_second, new_activity_toa, activity_name_toa, activity_toa, activity_length, activities_list_length  = controller_toa.getActivity(initial_conditions_string,goal)
		time_traditional, plan_traditional = controller_traditional.getPlan(initial_conditions_string,goal)

		length_traditional = len(plan_traditional)
		goal_holds = False
		if(activity_toa == ['Goal Holds']): 
			activity_length = 0
			length_traditional = 0
			goal_holds = True
		textfile.write("$$$$$$$$$$$$$$$$$$$   Run number " + str(run +1) +"   $$$$$$$$$$$$$$$$$$$\n")
		textfile.write("Goal: "+goal+"\n")
		textfile.write("Initial Conditions Index: "+str(initial_conditions_index)+"\n")
		textfile.write("Initial Conditions: "+str(initial_conditions_string)+"\n")
		textfile.write("\n\n")
		textfile.write("Traditional Planning:\n" + str(plan_traditional))
		textfile.write("\n\n")
		textfile.write("ToA Activity:\n" + str(activity_toa))
		textfile.write('\n--------------------------------------------------------------\n\n')

		writer.writerow([run+1, time_traditional, time_toa, time_toa_first, time_toa_second, length_traditional, activity_length, new_activity_toa, activity_name_toa, activities_list_length, initial_conditions_index, goal, goal_holds])
		csvfile.flush()

	
